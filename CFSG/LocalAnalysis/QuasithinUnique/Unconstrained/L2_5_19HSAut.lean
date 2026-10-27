module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutModel

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem centralizer_zpowers {G : Type*} [Group G] (t : G) :
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h t (Subgroup.mem_zpowers t)
  · intro h g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute t x from h) n)).eq

theorem mem_zpowers_of_sq {Γ : Type*} [Group Γ] {g : Γ} (hg1 : g ≠ 1) (hg2 : g * g = 1) {x : Γ}
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg2) hg1
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hord]
  have : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem mem_P_of_outer
    {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (hxP : x ∉ hsP)
    (hy : y ∈ hsR) (hyP : y ∉ hsP) : x * y⁻¹ ∈ hsP := by
  have hmem := hs_normalizing_model.2.2.2.2.2.1
  have hx' : x * hsU ∈ hsP := ((hmem x).1 hx).resolve_left hxP
  have hy' : y * hsU ∈ hsP := ((hmem y).1 hy).resolve_left hyP
  have := hsP.mul_mem hx' (hsP.inv_mem hy')
  simpa [mul_assoc] using this

theorem center_eq_bot_of_simple_card {Γ : Type*} [Group Γ] [IsSimpleGroup Γ]
    (h : ¬ (Nat.card Γ).Prime) : Subgroup.center Γ = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Γ) with h1 | h1
  · exact h1
  · exfalso
    have hcomm : IsMulCommutative Γ := Subgroup.center_eq_top_iff.mp h1
    exact h (IsSimpleGroup.prime_card (α := Γ))

theorem card_alt_six_hs : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem tabAutCentHS
    : TabAutCentHS := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc htY
  obtain ⟨hA6, ⟨e⟩, hind⟩ := hpat
  have hX : Group.IsPerfect ↥X := hXq.1
  let θ : (↥X ⧸ Subgroup.center ↥X) ≃* ↥hsP := e.trans hsPermEquiv
  let π : ↥X →* ↥hsP := Tab.quotProj θ
  have hπ : Function.Surjective π := Tab.quotProj_surjective θ
  have hker : π.ker = Subgroup.center ↥X := Tab.quotProj_ker θ
  obtain ⟨eR, heR, -, -, -⟩ := hs_full_automorphism_model
  let φ : ↥Y →* MulAut ↥hsP := Tab.actHom π hπ hker Y hYn
  let ν : ↥Y →* ↥hsR := eR.symm.toMonoidHom.comp φ
  have hνφ : ∀ (y : ↥Y) (p : ↥hsP), ((φ y p : ↥hsP) : Equiv.Perm (Fin 3850)) =
      (ν y : Equiv.Perm (Fin 3850)) * p * (ν y : Equiv.Perm (Fin 3850))⁻¹ := by
    intro y p
    have h1 : φ y = eR (ν y) := by simp [ν]
    rw [h1, heR]
    rfl
  have hνker : ∀ y : ↥Y, ν y = 1 ↔ (y : G) ∈ Y ⊓ Subgroup.centralizer (X : Set G) := by
    intro y
    have h1 : ν y = 1 ↔ φ y = 1 := by
      constructor
      · intro h
        have : eR (ν y) = 1 := by rw [h]; exact map_one _
        simpa [ν] using this
      · intro h
        simp [ν, h]
    rw [h1, ← MonoidHom.mem_ker, Tab.ker_actHom π hπ hker Y hYn hX, Subgroup.mem_subgroupOf]
  obtain ⟨l, hl, hlt⟩ := hind
  let lX : ↥X := ⟨l, hl⟩
  have hconj : ∀ x : ↥X, ((Tab.conjAut X t ht x : ↥X) : G) = (lX : G) * x * (lX : G)⁻¹ := by
    intro x
    rw [Tab.coe_conjAut X ht]
    have hx' : t * (x : G) * t⁻¹ ∈ X := by
      have := (Tab.conjAut X t ht x).2
      rwa [Tab.coe_conjAut X ht] at this
    have h1 := hlt _ hx'
    have h1' : (x : G) = l⁻¹ * (t * (x : G) * t⁻¹) * l := by
      have e1 : t⁻¹ * (t * (x : G) * t⁻¹) * t = x := by group
      rw [e1] at h1
      exact h1
    calc t * (x : G) * t⁻¹ = l * (l⁻¹ * (t * (x : G) * t⁻¹) * l) * l⁻¹ := by group
      _ = l * x * l⁻¹ := by rw [← h1']
  let tY : ↥Y := ⟨t, htY⟩
  have hαeq : Tab.quotAct π hπ hker ht = MulAut.conj (π lX) := by
    have hcj : Tab.conjAut X t ht = MulAut.conj lX :=
      MulEquiv.ext fun x => Subtype.ext (by rw [hconj]; simp [MulAut.conj_apply])
    show Tab.quotActHom π hπ hker (Tab.conjAut X t ht) = _
    rw [hcj, Tab.quotActHom_conj]
  have hφt : φ tY = MulAut.conj (π lX) := hαeq
  have hα1 : Tab.quotAct π hπ hker ht ≠ 1 := Tab.quotAct_ne_one π hπ hker ht hXq hcomm
  set ĥ : Equiv.Perm (Fin 3850) := ((π lX : ↥hsP) : Equiv.Perm (Fin 3850)) with hĥdef
  have hĥP : ĥ ∈ hsP := (π lX).2
  have hĥR : ĥ ∈ hsR := le_sup_left (a := hsP) (b := Subgroup.zpowers hsU) hĥP
  have hνt : ν tY = ⟨ĥ, hĥR⟩ := by
    apply eR.injective
    have h1 : eR (ν tY) = φ tY := by simp [ν]
    rw [h1, hφt]
    ext p
    rw [heR]
    simp [MulAut.conj_apply, hĥdef]
  have hĥ2 : ĥ * ĥ = 1 := by
    have h1 : tY * tY = 1 := Subtype.ext ht2
    have h2 : ν tY * ν tY = 1 := by rw [← map_mul, h1, map_one]
    rw [hνt] at h2
    exact congrArg Subtype.val h2
  have hĥ1 : ĥ ≠ 1 := by
    intro h1
    apply hα1
    rw [hαeq]
    have : π lX = 1 := Subtype.ext h1
    rw [this]
    ext p
    simp
  have ht1 : t ≠ 1 := by
    intro h1
    apply hα1
    have : tY = 1 := Subtype.ext h1
    have h2 : φ tY = 1 := by rw [this, map_one]
    exact h2
  have hWn : Subgroup.zpowers t ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.zpowers_le]; exact ht
  let Ft : Subgroup ↥hsP :=
    (hsP ⊓ Subgroup.centralizer ({ĥ} : Set (Equiv.Perm (Fin 3850)))).subgroupOf hsP
  have hFtmem : ∀ m : ↥hsP, m ∈ Ft ↔ MulAut.conj (π lX) m = m := by
    intro m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      change ĥ * (m : Equiv.Perm (Fin 3850)) * ĥ⁻¹ = m
      rw [← h1]
      group
    · intro h1
      refine ⟨m.2, ?_⟩
      have h2 := congrArg Subtype.val h1
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      change ĥ * (m : Equiv.Perm (Fin 3850)) * ĥ⁻¹ = m at h2
      calc (m : Equiv.Perm (Fin 3850)) * ĥ = (ĥ * (m : Equiv.Perm (Fin 3850)) * ĥ⁻¹) * ĥ := by
            rw [h2]
        _ = ĥ * m := by group
  have hactt : Tab.actHom π hπ hker (Subgroup.zpowers t) hWn ⟨t, Subgroup.mem_zpowers t⟩ =
      MulAut.conj (π lX) := hαeq
  have hFt : ∀ m : ↥hsP, m ∈ Ft ↔
      ∀ w : ↥(Subgroup.zpowers t), Tab.actHom π hπ hker (Subgroup.zpowers t) hWn w m = m := by
    intro m
    rw [hFtmem]
    constructor
    · intro hm w
      obtain ⟨w, hw⟩ := w
      rcases mem_zpowers_of_sq ht1 ht2 hw with h | h
      · have h1 : (⟨w, hw⟩ : ↥(Subgroup.zpowers t)) = 1 := Subtype.ext h
        rw [h1, map_one]
        rfl
      · have h1 : (⟨w, hw⟩ : ↥(Subgroup.zpowers t)) = ⟨t, Subgroup.mem_zpowers t⟩ :=
          Subtype.ext h
        rw [h1, hactt]
        exact hm
    · intro h
      have h1 := h ⟨t, Subgroup.mem_zpowers t⟩
      rw [hactt] at h1
      exact h1
  have himg := residual_centralizer_image π hπ hker (Subgroup.zpowers t) hWn Ft hFt
  rw [centralizer_zpowers, ← hK] at himg
  set Kb : Subgroup (Equiv.Perm (Fin 3850)) :=
    perfectResidualOf (hsP ⊓ Subgroup.centralizer ({ĥ} : Set (Equiv.Perm (Fin 3850)))) with hKbdef
  have hKbmap : (perfectResidualOf Ft).map hsP.subtype = Kb :=
    perfectResidualOf_subgroupOf inf_le_left
  have hKbX : ∀ k ∈ Kb, ∃ k₀ : ↥X, (k₀ : G) ∈ K ∧
      ((π k₀ : ↥hsP) : Equiv.Perm (Fin 3850)) = k := by
    intro k hk
    rw [← hKbmap] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [← himg] at hm
    obtain ⟨k₀, hk₀, rfl⟩ := hm
    exact ⟨k₀, hk₀, rfl⟩
  have hKP : Kb ≤ hsP := (perfectResidualOf_le' _).trans inf_le_left
  have hKcent : ∀ k ∈ Kb, k * ĥ = ĥ * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (((perfectResidualOf_le' _) hk).2)
  have hKn : ∀ c ∈ hsP, c * ĥ = ĥ * c → ∀ k ∈ Kb, c * k * c⁻¹ ∈ Kb := by
    intro c hc hcĥ k hk
    have hcD : c ∈ hsP ⊓ Subgroup.centralizer ({ĥ} : Set (Equiv.Perm (Fin 3850))) :=
      ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 hcĥ⟩
    have hnorm := perfectResidualOf_normalizer_contains
      (hsP ⊓ Subgroup.centralizer ({ĥ} : Set (Equiv.Perm (Fin 3850)))) (Subgroup.le_normalizer hcD)
    exact (Subgroup.mem_normalizer_iff.1 hnorm k).1 hk
  have hKX : K ≤ X := by
    rw [hK]; exact (perfectResidualOf_le' _).trans inf_le_left
  obtain ⟨e6⟩ := hA6
  have hKsimple : IsSimpleGroup ↥K :=
    (MulEquiv.isSimpleGroup_congr e6).2 (alternatingGroup.isSimpleGroup (by simp))
  have hcardK : Nat.card ↥K = 360 := by
    rw [Nat.card_congr e6.toEquiv]
    exact card_alt_six_hs
  have hKcen : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_simple_card (by rw [hcardK]; norm_num)
  have hKcard : Nat.card Kb = 360 := by
    have hinj : Function.Injective (π.comp (K.subgroupOf X).subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : (a : ↥X) ∈ Subgroup.center ↥X := by rw [← hker]; exact ha
      have h2 : (⟨((a : ↥X) : G), a.2⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have := Subgroup.mem_center_iff.1 h1 (Subgroup.inclusion hKX g)
        exact congrArg (Subtype.val : ↥X → G) this
      rw [hKcen, Subgroup.mem_bot] at h2
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥K → G) h2
    have hrange : (π.comp (K.subgroupOf X).subtype).range = (K.subgroupOf X).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have c1 : Nat.card Kb = Nat.card ↥(perfectResidualOf Ft) := by
      rw [← hKbmap]
      exact Subgroup.card_map_of_injective hsP.subtype_injective
    rw [c1, ← himg, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
    exact hcardK
  obtain ⟨hN1, r₁, hr₁R, hr₁P, hr₁2, hr₁c⟩ := hs_model hKP hKcard hĥP hĥ2 hĥ1 hKcent hKn
  have hνc : ∀ (y : ↥Y), ∀ k ∈ Kb,
      (ν y : Equiv.Perm (Fin 3850)) * k = k * (ν y : Equiv.Perm (Fin 3850)) := by
    intro y k hk
    obtain ⟨k₀, hk₀K, rfl⟩ := hKbX k hk
    have hfix : φ y (π k₀) = π k₀ := by
      apply Tab.actHom_fix π hπ hker Y hYn (y := y) (k := k₀)
      exact Subgroup.mem_centralizer_iff.1 (hYc y.2) (k₀ : G) hk₀K
    have h2 := hνφ y (π k₀)
    rw [hfix] at h2
    calc (ν y : Equiv.Perm (Fin 3850)) * ((π k₀ : ↥hsP) : Equiv.Perm (Fin 3850)) =
        ((ν y : Equiv.Perm (Fin 3850)) * ((π k₀ : ↥hsP) : Equiv.Perm (Fin 3850)) *
          (ν y : Equiv.Perm (Fin 3850))⁻¹) * (ν y : Equiv.Perm (Fin 3850)) := by group
      _ = ((π k₀ : ↥hsP) : Equiv.Perm (Fin 3850)) * (ν y : Equiv.Perm (Fin 3850)) := by
        rw [← h2]
  classical
  have hr₁1 : r₁ ≠ 1 := fun h => hr₁P (h ▸ hsP.one_mem)
  have hĥr₁R : ĥ * r₁ ∈ hsR := hsR.mul_mem hĥR hr₁R
  have hĥr₁P : ĥ * r₁ ∉ hsP := fun h => hr₁P (by simpa using hsP.mul_mem (hsP.inv_mem hĥP) h)
  let S4 : Finset (Equiv.Perm (Fin 3850)) := {1, ĥ, r₁, ĥ * r₁}
  have hS4card : S4.card = 4 := by
    have h1 : (1 : Equiv.Perm (Fin 3850)) ∉ ({ĥ, r₁, ĥ * r₁} : Finset (Equiv.Perm (Fin 3850))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hĥ1 h.symm, fun h => hr₁1 h.symm, fun h => hĥr₁P (h ▸ hsP.one_mem)⟩
    have h2 : ĥ ∉ ({r₁, ĥ * r₁} : Finset (Equiv.Perm (Fin 3850))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hr₁P (h ▸ hĥP), fun h => hr₁1 (by simpa using h)⟩
    have h3 : r₁ ∉ ({ĥ * r₁} : Finset (Equiv.Perm (Fin 3850))) := by
      simp only [Finset.mem_singleton]
      exact fun h => hĥ1 (by simpa using h.symm)
    simp only [S4]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have hνS : ∀ y : ↥Y, (ν y : Equiv.Perm (Fin 3850)) ∈ S4 := by
    intro y
    set b : Equiv.Perm (Fin 3850) := (ν y : Equiv.Perm (Fin 3850)) with hb
    have hbR : b ∈ hsR := (ν y).2
    by_cases hbP : b ∈ hsP
    · rcases hN1 b hbP (hνc y) with h | h
      · simp [S4, h]
      · simp [S4, h]
    · have hq : b * r₁⁻¹ ∈ hsP := mem_P_of_outer hbR hbP hr₁R hr₁P
      have hqc : ∀ k ∈ Kb, (b * r₁⁻¹) * k = k * (b * r₁⁻¹) := by
        intro k hk
        have h1 := hνc y k hk
        have h2 := hr₁c k hk
        have h2' : r₁⁻¹ * k = k * r₁⁻¹ := by
          calc r₁⁻¹ * k = r₁⁻¹ * (k * r₁) * r₁⁻¹ := by group
            _ = r₁⁻¹ * (r₁ * k) * r₁⁻¹ := by rw [h2]
            _ = k * r₁⁻¹ := by group
        calc b * r₁⁻¹ * k = b * (r₁⁻¹ * k) := by group
          _ = b * (k * r₁⁻¹) := by rw [h2']
          _ = (b * k) * r₁⁻¹ := by group
          _ = (k * b) * r₁⁻¹ := by rw [h1]
          _ = k * (b * r₁⁻¹) := by group
      rcases hN1 _ hq hqc with h | h
      · have : b = r₁ := by
          calc b = (b * r₁⁻¹) * r₁ := by group
            _ = r₁ := by rw [h]; group
        simp [S4, this]
      · have : b = ĥ * r₁ := by
          calc b = (b * r₁⁻¹) * r₁ := by group
            _ = ĥ * r₁ := by rw [h]
        simp [S4, this]
  let f : ↥ν.range → ↥S4 := fun b => ⟨((b : ↥hsR) : Equiv.Perm (Fin 3850)), by
    obtain ⟨y, hy⟩ := b.2
    rw [← hy]
    exact hνS y⟩
  have hfinj : Function.Injective f := by
    intro b b' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (Subtype.val : ↥S4 → Equiv.Perm (Fin 3850)) h
  have hcardS4 : Nat.card ↥S4 = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hS4card
  have hrel : (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y = Nat.card ν.range := by
    rw [Tab.relIndex_eq_card_range π hπ hker Y hYn hX]
    have hr : ν.range = φ.range.map eR.symm.toMonoidHom := MonoidHom.range_comp _ _
    rw [hr, Subgroup.card_map_of_injective eR.symm.injective]
  have hle4 : Nat.card ν.range ≤ 4 := by
    have := Nat.card_le_card_of_injective f hfinj
    rwa [hcardS4] at this
  rw [hrel]
  refine ⟨hle4, fun h4 => ?_⟩
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hfinj, by rw [h4, hcardS4]⟩
  have hrange_mem : ∀ b : ↥hsR, (b : Equiv.Perm (Fin 3850)) ∈ S4 → b ∈ ν.range := by
    intro b hb
    obtain ⟨b', hb'⟩ := hbij.2 ⟨(b : Equiv.Perm (Fin 3850)), hb⟩
    have : (b' : ↥hsR) = b := by
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥S4 → Equiv.Perm (Fin 3850)) hb'
    rw [← this]
    exact b'.2
  let r₁R : ↥hsR := ⟨r₁, hr₁R⟩
  let ĥR : ↥hsR := ⟨ĥ, hĥR⟩
  have hr₁range : r₁R ∈ ν.range := hrange_mem r₁R (by simp [S4, r₁R])
  have hr₁R1 : r₁R ≠ 1 := fun h => hr₁1 (congrArg Subtype.val h)
  have hr₁R2 : r₁R * r₁R = 1 := Subtype.ext hr₁2
  have hĥR1 : ĥR ≠ 1 := fun h => hĥ1 (congrArg Subtype.val h)
  have hĥRr : ĥR ∉ Subgroup.zpowers r₁R := by
    intro h
    rcases mem_zpowers_of_sq hr₁R1 hr₁R2 h with h1 | h1
    · exact hĥR1 h1
    · have h2 : ĥ = r₁ := congrArg Subtype.val h1
      exact hr₁P (h2 ▸ hĥP)
  have hB1 : Nat.card ↥(Subgroup.zpowers r₁R) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hr₁R2) hr₁R1
  have hsq : ∀ y ∈ Y, y * y ∈ Subgroup.centralizer (X : Set G) := by
    have hĥrange : ĥR ∈ ν.range := ⟨tY, hνt⟩
    have hcomm : IsMulCommutative ↥ν.range :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
    have hĥr : ĥR * r₁R = r₁R * ĥR := by
      have := hcomm.is_comm.comm ⟨ĥR, hĥrange⟩ ⟨r₁R, hr₁range⟩
      exact congrArg (fun z : ↥ν.range => (z : ↥hsR)) this
    have hĥĥ : ĥR * ĥR = 1 := Subtype.ext hĥ2
    intro y hy
    let yY : ↥Y := ⟨y, hy⟩
    set b : ↥hsR := ν yY with hbdef
    have hbS := hνS yY
    have hb2 : b * b = 1 := by
      simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hbS
      rcases hbS with h | h | h | h
      · have : b = 1 := Subtype.ext h
        rw [this, mul_one]
      · have : b = ĥR := Subtype.ext h
        rw [this]
        exact hĥĥ
      · have : b = r₁R := Subtype.ext h
        rw [this]
        exact hr₁R2
      · have : b = ĥR * r₁R := Subtype.ext h
        rw [this]
        calc ĥR * r₁R * (ĥR * r₁R) = ĥR * (r₁R * ĥR) * r₁R := by group
          _ = ĥR * (ĥR * r₁R) * r₁R := by rw [hĥr]
          _ = (ĥR * ĥR) * (r₁R * r₁R) := by group
          _ = 1 := by rw [hĥĥ, hr₁R2, mul_one]
    have hmem : ν (yY * yY) = 1 := by rw [map_mul]; exact hb2
    exact ((hνker (yY * yY)).1 hmem).2
  refine ⟨hsq, ?_, ?_⟩
  ·
    let S₁ : Subgroup ↥Y := (Subgroup.zpowers r₁R).comap ν
    refine ⟨S₁.map Y.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
    · intro x hx
      have hxY : x ∈ Y := hx.1
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      show ν ⟨x, hxY⟩ ∈ Subgroup.zpowers r₁R
      rw [(hνker ⟨x, hxY⟩).2 hx]
      exact Subgroup.one_mem _
    · have h1 : (S₁.map Y.subtype).subgroupOf Y = S₁ :=
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective S₁
      unfold Subgroup.relIndex
      rw [h1]
      show ((Subgroup.zpowers r₁R).comap ν).index = 2
      rw [Subgroup.index_comap]
      have h2 := Subgroup.card_mul_index ((Subgroup.zpowers r₁R).subgroupOf ν.range)
      have h3 : Nat.card ↥((Subgroup.zpowers r₁R).subgroupOf ν.range) = 2 := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).2 hr₁range)).toEquiv]
        exact hB1
      rw [h3, h4] at h2
      unfold Subgroup.relIndex
      omega
    · intro htm
      obtain ⟨s, hs, hst⟩ := htm
      have hs' : s = tY := Subtype.ext hst
      rw [hs'] at hs
      have h1 : ν tY ∈ Subgroup.zpowers r₁R := hs
      rw [hνt] at h1
      exact hĥRr h1
  ·
    intro Y₁ hker₁ hY₁Y hidx ht₁
    have hY₁n : Y₁ ≤ Subgroup.normalizer (X : Set G) := hY₁Y.trans hYn
    let S : Subgroup ↥Y := Y₁.subgroupOf Y
    have hkerS : ν.ker ≤ S := by
      intro y hy
      have : (y : G) ∈ Y ⊓ Subgroup.centralizer (X : Set G) := (hνker y).1 hy
      exact hker₁ this
    let B₁ : Subgroup ↥hsR := S.map ν
    have hcomap : B₁.comap ν = S := Subgroup.comap_map_eq_self hkerS
    have hidxS : S.index = 2 := hidx
    have hB₁le : B₁ ≤ ν.range := Subgroup.map_le_range _ _
    have hB₁idx : (B₁.subgroupOf ν.range).index = 2 := by
      have h1 := Subgroup.index_comap (H := B₁) ν
      rw [hcomap, hidxS] at h1
      exact h1.symm
    have hB₁card : Nat.card ↥B₁ = 2 := by
      have h2 := Subgroup.card_mul_index (B₁.subgroupOf ν.range)
      rw [hB₁idx, h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁le).toEquiv] at h2
      omega
    have hnt : Nontrivial ↥B₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hB₁card]; norm_num)
    obtain ⟨b, hb1⟩ : ∃ b : ↥B₁, b ≠ 1 := exists_ne 1
    have hb2 : b * b = 1 := by
      have := pow_card_eq_one' (G := ↥B₁) (x := b)
      rwa [hB₁card, sq] at this
    have hbz : ∀ x : ↥B₁, x = 1 ∨ x = b := by
      intro x
      have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hx : x ∈ Subgroup.zpowers b := mem_zpowers_of_prime_card hB₁card hb1
      exact mem_zpowers_of_sq hb1 hb2 hx
    set β : ↥hsR := (b : ↥hsR) with hβ
    have hβB₁ : β ∈ B₁ := b.2
    have hβ1 : β ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hβ2 : β * β = 1 := congrArg Subtype.val hb2
    have hβall : ∀ x ∈ B₁, x = 1 ∨ x = β := fun x hx => by
      rcases hbz ⟨x, hx⟩ with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    have hβB₁' : ∃ s ∈ S, ν s = β := hβB₁
    obtain ⟨s₀, hs₀S, hs₀⟩ := hβB₁'
    have hβrange : β ∈ ν.range := hB₁le hβB₁
    obtain ⟨yβ, hyβ⟩ := hβrange
    have hβS4 : (β : Equiv.Perm (Fin 3850)) ∈ S4 := by rw [← hyβ]; exact hνS yβ
    have hβĥ : β ≠ ĥR := by
      intro h
      apply ht₁
      have h1 : ν (s₀⁻¹ * tY) = 1 := by
        rw [map_mul, map_inv, hs₀, h, hνt, inv_mul_cancel]
      have h2 : s₀⁻¹ * tY ∈ S := hkerS h1
      have h3 : tY ∈ S := by
        have := S.mul_mem hs₀S h2
        simpa using this
      exact h3
    have hβ' : (β : Equiv.Perm (Fin 3850)) = r₁ ∨ (β : Equiv.Perm (Fin 3850)) = ĥ * r₁ := by
      simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hβS4
      rcases hβS4 with h | h | h | h
      · exact absurd (Subtype.ext h) hβ1
      · exact absurd (Subtype.ext h) hβĥ
      · exact Or.inl h
      · exact Or.inr h
    have hβP : (β : Equiv.Perm (Fin 3850)) ∉ hsP := by
      rcases hβ' with h | h
      · rw [h]; exact hr₁P
      · rw [h]; exact hĥr₁P
    have hβ2' : (β : Equiv.Perm (Fin 3850)) * (β : Equiv.Perm (Fin 3850)) = 1 :=
      congrArg Subtype.val hβ2
    have hβKc : ∀ k ∈ Kb, (β : Equiv.Perm (Fin 3850)) * k = k * (β : Equiv.Perm (Fin 3850)) := by
      intro k hk
      rw [← hyβ]
      exact hνc yβ k hk
    let Fm₁ : Subgroup ↥hsP :=
      (hsP ⊓ Subgroup.centralizer
        ({(β : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850)))).subgroupOf hsP
    have hFm₁ : ∀ m : ↥hsP, m ∈ Fm₁ ↔
        ∀ w : ↥Y₁, Tab.actHom π hπ hker Y₁ hY₁n w m = m := by
      intro m
      have hact : ∀ w : ↥Y₁, Tab.actHom π hπ hker Y₁ hY₁n w = φ ⟨(w : G), hY₁Y w.2⟩ :=
        fun w => rfl
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨-, hm⟩ w
        have hwS : (⟨(w : G), hY₁Y w.2⟩ : ↥Y) ∈ S := w.2
        have hνw : ν ⟨(w : G), hY₁Y w.2⟩ ∈ B₁ := ⟨_, hwS, rfl⟩
        apply Subtype.ext
        rw [hact, hνφ]
        rcases hβall _ hνw with h | h
        · rw [h]; simp
        · rw [h]
          calc (β : Equiv.Perm (Fin 3850)) * (m : Equiv.Perm (Fin 3850)) *
              (β : Equiv.Perm (Fin 3850))⁻¹ =
              ((m : Equiv.Perm (Fin 3850)) * (β : Equiv.Perm (Fin 3850))) *
                (β : Equiv.Perm (Fin 3850))⁻¹ := by rw [hm]
            _ = m := mul_inv_cancel_right _ _
      · intro h
        refine ⟨m.2, ?_⟩
        have hw := h ⟨(s₀ : G), hs₀S⟩
        have h1 := congrArg Subtype.val hw
        rw [hact, hνφ] at h1
        have hs₀' : (⟨(s₀ : G), hY₁Y hs₀S⟩ : ↥Y) = s₀ := Subtype.ext rfl
        rw [hs₀', hs₀] at h1
        calc (m : Equiv.Perm (Fin 3850)) * (β : Equiv.Perm (Fin 3850)) =
            ((β : Equiv.Perm (Fin 3850)) * m * (β : Equiv.Perm (Fin 3850))⁻¹) *
              (β : Equiv.Perm (Fin 3850)) := by rw [h1]
          _ = (β : Equiv.Perm (Fin 3850)) * m := by group
    have hS : IsSimpleGroup ↥(perfectResidualOf Fm₁) ∧
        Nat.card ↥(perfectResidualOf Fm₁) = 20160 := by
      obtain ⟨hs1, hs2⟩ := hs_outer_simple hKP hKcard β.2 hβP hβ2' hβKc
      have hmap : (perfectResidualOf Fm₁).map hsP.subtype = perfectResidualOf
          (hsP ⊓ Subgroup.centralizer
            ({(β : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850)))) :=
        perfectResidualOf_subgroupOf inf_le_left
      let e : ↥(perfectResidualOf Fm₁) ≃* ↥((perfectResidualOf Fm₁).map hsP.subtype) :=
        Subgroup.equivMapOfInjective _ _ hsP.subtype_injective
      rw [hmap] at e
      exact ⟨(MulEquiv.isSimpleGroup_congr e).2 hs1, by rw [Nat.card_congr e.toEquiv]; exact hs2⟩
    obtain ⟨hqs, hcardA⟩ := residual_centralizer π hπ hker Y₁ hY₁n Fm₁ hFm₁ hS.1
    refine ⟨perfectResidualOf (X ⊓ Subgroup.centralizer (Y₁ : Set G)), rfl, hqs, ?_⟩
    have hKle : K ≤ perfectResidualOf (X ⊓ Subgroup.centralizer (Y₁ : Set G)) := by
      have hKperf : Group.IsPerfect ↥K := by
        rw [hK]
        exact finite_perfectResidualOf_isPerfect _
      refine le_perfectResidualOf ?_ hKperf
      intro k hk
      refine ⟨hKX hk, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hYc (hY₁Y hy)) k hk).symm
    refine lt_of_le_of_ne hKle fun hEq => ?_
    rw [hS.2, ← hEq, hcardK] at hcardA
    omega

end CFSG.QuasithinUnique.Id2519.HSAut
