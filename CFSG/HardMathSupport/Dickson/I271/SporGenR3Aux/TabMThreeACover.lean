module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

section Perfect

theorem commutator_eq_top_of_commutator_eq {G : Type*} [Group G] {P : Subgroup G}
    (h : ⁅P, P⁆ = P) : commutator ↥P = ⊤ :=
  Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 h)

end Perfect

section Kernel

variable {Y G J : Type*} [Group Y] [Group G] [Group J]

theorem mul_comm_of_card_le_three {K : Type*} [Group K] [Finite K] (h : Nat.card K ≤ 3)
    (a b : K) : a * b = b * a := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  have key : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 := by omega
  rcases key with h1 | h2 | h3
  · haveI : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · haveI := isCyclic_of_prime_card (p := 2) h2
    exact (IsCyclic.commGroup (α := K)).mul_comm a b
  · haveI := isCyclic_of_prime_card (p := 3) h3
    exact (IsCyclic.commGroup (α := K)).mul_comm a b

theorem ker_le_ker_of_isSimpleGroup (hY : commutator Y = ⊤) (Φ : Y →* G) (ψ : Y →* J)
    (hψ : Function.Surjective ψ) [IsSimpleGroup J] [Finite ψ.ker] (hk : Nat.card ψ.ker ≤ 3)
    (hΦ : Φ.range ≠ ⊥) : Φ.ker ≤ ψ.ker := by
  by_contra hle
  have htop : Φ.ker.map ψ = ⊤ := by
    haveI : (Φ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Φ.ker.map ψ)).resolve_left fun hbot => hle ?_
    intro x hx
    have h1 : ψ x ∈ Φ.ker.map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  have hrange : Φ.range ≤ ψ.ker.map Φ := by
    rintro _ ⟨y, rfl⟩
    have hy : ψ y ∈ Φ.ker.map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hkΦ, hkψ⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨k⁻¹ * y, ?_, ?_⟩
    · show ψ (k⁻¹ * y) = 1
      rw [map_mul, map_inv, hkψ, inv_mul_cancel]
    · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hkΦ, inv_one, one_mul]
  let f : ψ.ker → ψ.ker.map Φ := fun x => ⟨Φ x, Subgroup.mem_map_of_mem Φ x.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Finite (ψ.ker.map Φ) := Finite.of_surjective f hf
  have hA : Nat.card (ψ.ker.map Φ) ≤ 3 := (Nat.card_le_card_of_surjective f hf).trans hk
  have hcomm : ∀ u ∈ Φ.range, ∀ v ∈ Φ.range, v * u = u * v := fun u hu v hv =>
    congrArg Subtype.val (mul_comm_of_card_le_three hA ⟨v, hrange hv⟩ ⟨u, hrange hu⟩)
  have hperf : Φ.range = ⁅Φ.range, Φ.range⁆ := by
    have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup Y)) (H₂ := ⊤) Φ
    rw [← commutator_def, hY, Subgroup.map_top] at h1
    exact h1
  have hbot : ⁅Φ.range, Φ.range⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun v hv => hcomm u hu v hv
  exact hΦ (hperf.trans hbot)

end Kernel

section CoverHom

variable {Y G J : Type*} [Group Y] [Group G] [Group J]

@[expose] noncomputable def coverHom (Φ : Y →* G) (ψ : Y →* J) (h : Φ.ker ≤ ψ.ker) :
    ↥Φ.range →* J :=
  Φ.rangeRestrict.liftOfSurjective Φ.rangeRestrict_surjective
    ⟨ψ, by rwa [MonoidHom.ker_rangeRestrict]⟩

variable {Φ : Y →* G} {ψ : Y →* J}

theorem coverHom_rangeRestrict (h : Φ.ker ≤ ψ.ker) (y : Y) :
    coverHom Φ ψ h (Φ.rangeRestrict y) = ψ y :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y

theorem coverHom_surjective (h : Φ.ker ≤ ψ.ker) (hψ : Function.Surjective ψ) :
    Function.Surjective (coverHom Φ ψ h) := fun j => by
  obtain ⟨y, rfl⟩ := hψ j
  exact ⟨Φ.rangeRestrict y, coverHom_rangeRestrict h y⟩

theorem coverHom_eq_one_iff (h : Φ.ker ≤ ψ.ker) (d : ↥Φ.range) :
    coverHom Φ ψ h d = 1 ↔ ∃ y : Y, ψ y = 1 ∧ Φ y = (d : G) := by
  obtain ⟨y, rfl⟩ := Φ.rangeRestrict_surjective d
  rw [coverHom_rangeRestrict h]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', hΦ⟩
    have hΦ' : Φ y' = Φ y := hΦ
    have hmem : y'⁻¹ * y ∈ ψ.ker := h (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ', inv_mul_cancel])
    have hψ : ψ (y'⁻¹ * y) = 1 := hmem
    rwa [map_mul, map_inv, hy', inv_one, one_mul] at hψ

theorem card_ker_coverHom_le (h : Φ.ker ≤ ψ.ker) [Finite ψ.ker] :
    Finite (coverHom Φ ψ h).ker ∧ Nat.card (coverHom Φ ψ h).ker ≤ Nat.card ψ.ker := by
  let f : ψ.ker → (coverHom Φ ψ h).ker := fun x =>
    ⟨Φ.rangeRestrict x.1, by rw [MonoidHom.mem_ker, coverHom_rangeRestrict h]; exact x.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨d, hd⟩
    obtain ⟨y, hy, hyd⟩ := (coverHom_eq_one_iff h d).1 hd
    exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext hyd)⟩
  exact ⟨Finite.of_surjective f hf, Nat.card_le_card_of_surjective f hf⟩

end CoverHom

section Three

theorem kernel_cyclic_three {G : Type*} [Group G] {K : Subgroup G} [Finite K]
    (hK : Nat.card K ≤ 3) {c ζ : G} (hζK : ζ ∈ K) (hcK : ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hc : c * ζ ≠ ζ * c) :
    orderOf ζ = 3 ∧ c * ζ * c⁻¹ = ζ⁻¹ ∧ ∀ g : G, g ∈ K ↔ g ∈ Subgroup.zpowers ζ := by
  have hζ1 : ζ ≠ 1 := fun h => hc (by rw [h, mul_one, one_mul])
  have hζ' : c * ζ * c⁻¹ ∈ K := hcK ζ hζK
  have hne1 : c * ζ * c⁻¹ ≠ 1 := fun h => hζ1 (by
    calc ζ = c⁻¹ * (c * ζ * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group)
  have hneζ : c * ζ * c⁻¹ ≠ ζ := fun h => hc (by
    calc c * ζ = c * ζ * c⁻¹ * c := by group
      _ = ζ * c := by rw [h])
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hdvd : orderOf ζ ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨ζ, hζK⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  have hord0 : 0 < orderOf ζ := Nat.pos_of_dvd_of_pos hdvd hpos
  have hord1 : orderOf ζ ≠ 1 := fun h => hζ1 (orderOf_eq_one_iff.1 h)
  have hord : orderOf ζ ≤ 3 := (Nat.le_of_dvd hpos hdvd).trans hK
  have hn : orderOf ζ = Nat.card K := by
    rcases (by omega : orderOf ζ = 2 ∨ orderOf ζ = 3) with h | h <;> rw [h] at hdvd ⊢ <;> omega
  have hKeq : Subgroup.zpowers ζ = K :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζK) (by rw [Nat.card_zpowers, hn])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hKeq ▸ hζ')
  rw [← zpow_mod_orderOf] at hk
  have hζ3 : orderOf ζ = 3 := by
    rcases (by omega : orderOf ζ = 2 ∨ orderOf ζ = 3) with h | h
    · exfalso
      rw [h] at hk
      rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h0 | h0
      · rw [h0, zpow_zero] at hk
        exact hne1 hk.symm
      · rw [h0, zpow_one] at hk
        exact hneζ hk.symm
    · exact h
  refine ⟨hζ3, ?_, fun g => by rw [← hKeq]⟩
  rw [hζ3] at hk
  rcases (by omega : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2) with
    h0 | h0 | h0
  · rw [h0, zpow_zero] at hk
    exact absurd hk.symm hne1
  · rw [h0, zpow_one] at hk
    exact absurd hk.symm hneζ
  · rw [h0] at hk
    rw [← hk]
    have h3 : ζ ^ 3 = 1 := by
      have := pow_orderOf_eq_one ζ
      rwa [hζ3] at this
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    simpa using h3

end Three

section Centralizer

theorem mulAut_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (σ τ : MulAut C) :
    σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic τ.toMonoidHom
  ext g
  change σ (τ g) = τ (σ g)
  have h1 : σ (τ g) = (τ g) ^ m := hm (τ g)
  have h2 : τ (σ g) = (σ g) ^ n := hn (σ g)
  have h3 : τ g = g ^ n := hn g
  have h4 : σ g = g ^ m := hm g
  rw [h1, h2, h3, h4, ← zpow_mul, ← zpow_mul, mul_comm]

theorem le_centralizer_of_commutator_eq {G : Type*} [Group G] {D : Subgroup G} (hD : ⁅D, D⁆ = D)
    {ζ : G} (_hζ : orderOf ζ = 3) (hn : ∀ d ∈ D, d * ζ * d⁻¹ ∈ Subgroup.zpowers ζ) :
    D ≤ Subgroup.centralizer ({ζ} : Set G) := by
  set Z := Subgroup.zpowers ζ
  have hconj : ∀ d ∈ D, ∀ x ∈ Z, d * x * d⁻¹ ∈ Z := by
    intro d hd x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← conj_zpow]
    exact Z.zpow_mem (hn d hd) k
  have hnorm : D ≤ Subgroup.normalizer (Z : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj d hd x, fun hx => ?_⟩
    have := hconj d⁻¹ (D.inv_mem hd) _ hx
    simpa [mul_assoc] using this
  let φ : ↥D →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← commutator_eq_top_of_commutator_eq hD, commutator_def]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_comm_of_isCyclic _ _
  intro d hd
  have h1 : (⟨d, hd⟩ : ↥D) ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_top _
  have h2 : Subgroup.inclusion hnorm ⟨d, hd⟩ ∈ Z.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
  exact Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 h2 ζ (Subgroup.mem_zpowers ζ)).symm

end Centralizer

section Quasisimple

theorem isQuasisimple_transport {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple B) :
    CFSG.Open.IsQuasisimple A ∧ Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) := by
  let f := QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)
  haveI : Group.IsPerfect B := Group.isPerfect_def.2 h.1
  haveI : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨⟨Group.isPerfect_def.1 this, f.isSimpleGroup_congr.2 h.2⟩, ⟨f⟩⟩

theorem isQuasisimple_of_cover {D J : Type*} [Group D] [Group J] (hD : commutator D = ⊤)
    (ρ : D →* J) (hρ : Function.Surjective ρ) [IsSimpleGroup J] (hJ : ∃ x y : J, x * y ≠ y * x)
    (hker : ρ.ker ≤ Subgroup.center D) :
    CFSG.Open.IsQuasisimple D ∧ Nonempty (D ⧸ Subgroup.center D ≃* J) := by
  have hZJ : Subgroup.center J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hJ
      have hx : x ∈ Subgroup.center J := h ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.1 hx y).symm
  have hcen : Subgroup.center D ≤ ρ.ker := by
    intro x hx
    have hρx : ρ x ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨c, rfl⟩ := hρ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx c]
    rw [hZJ, Subgroup.mem_bot] at hρx
    exact hρx
  have heq : Subgroup.center D = ρ.ker := le_antisymm hcen hker
  let e : (D ⧸ Subgroup.center D) ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  exact ⟨⟨hD, e.isSimpleGroup_congr.2 inferInstance⟩, ⟨e⟩⟩

@[expose] def centralizerConjEquiv {G : Type*} [Group G] (c k : G) :
    ↥(Subgroup.centralizer ({k} : Set G)) ≃* ↥(Subgroup.centralizer ({c * k * c⁻¹} : Set G)) where
  toFun x := ⟨c * x * c⁻¹, by
    have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : c * (x : G) * c⁻¹ * (c * k * c⁻¹) = c * ((x : G) * k) * c⁻¹ := by group
    have e2 : c * k * c⁻¹ * (c * (x : G) * c⁻¹) = c * (k * (x : G)) * c⁻¹ := by group
    rw [e1, e2, hx]⟩
  invFun y := ⟨c⁻¹ * y * c, by
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : c⁻¹ * (y : G) * c * k = c⁻¹ * ((y : G) * (c * k * c⁻¹)) * c := by group
    have e2 : k * (c⁻¹ * (y : G) * c) = c⁻¹ * ((c * k * c⁻¹) * (y : G)) * c := by group
    rw [e1, e2, hy]⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem quasisimple_centralizer_of_isConj {G Q : Type*} [Group G] [Group Q] {D : Subgroup G}
    {ζ k : G} (hD : Subgroup.centralizer ({ζ} : Set G) = D) (hk : IsConj k ζ)
    (hq : CFSG.Open.IsQuasisimple ↥D ∧ Nonempty (↥D ⧸ Subgroup.center ↥D ≃* Q)) :
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set G)) ∧
      Nonempty (↥(Subgroup.centralizer ({k} : Set G)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({k} : Set G)) ≃* Q) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hk
  have e : ↥(Subgroup.centralizer ({k} : Set G)) ≃* ↥D :=
    (centralizerConjEquiv c k).trans (MulEquiv.subgroupCongr (by rw [hc, hD]))
  obtain ⟨hqs, ⟨g⟩⟩ := hq
  obtain ⟨h1, ⟨f⟩⟩ := isQuasisimple_transport e hqs
  exact ⟨h1, ⟨f.trans g⟩⟩

end Quasisimple

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
