module

public import CFSG.GH74.GLS.IVK.Proofs2.PglKGamma
public import CFSG.GH74.GLS.IVK.Proofs2.PglKCoatom
public import CFSG.GH74.GLS.C3.Layer1.BkPglStmt
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

theorem mem_psl2Range_of_odd' {F : Type} [Field F] (t : PGL2 F) (ht : Odd (orderOf t)) :
    t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.mpr ht)
  rw [← hm]
  apply Subgroup.pow_mem
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  rw [← map_pow, pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_pow_eq_pow_val, Matrix.det_pow]
  exact ⟨_, sq _⟩

theorem pgl2_nine_no_order_six {F₀ : Type} [Field F₀] [Finite F₀] (h9 : Nat.card F₀ = 9)
    {t u : PGL2 F₀} (ht : orderOf t = 2) (hu : orderOf u = 3) (hc : t * u = u * t) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : IsOddPrimePower (Nat.card F₀) :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [h9]; norm_num⟩
  have huJ := mem_psl2Range_of_odd' u (by rw [hu]; decide)
  have h1 := CFSG.ABGDGroups.pgl2_eq_one_of_commute_of_orderOf_eq_prime_pow hodd
    (by rw [h9]; norm_num) (p := 3) (f := 2) (by rw [h9]; norm_num) (by norm_num) ht (k := 1)
    (by rw [hu]; norm_num) huJ hc
  rw [h1, orderOf_one] at hu
  omega

theorem exists_eps_eight {q : ℕ} (hq : q = 7 ∨ q = 9) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] ∧ ((8 : ℕ) : ℤ) = q - ε := by
  rcases hq with h | h
  · exact ⟨-1, Or.inr rfl, by rw [h]; unfold Int.ModEq; norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, Or.inl rfl, by rw [h]; unfold Int.ModEq; norm_num, by rw [h]; norm_num⟩

section Data

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem centralizer_dih_of_seven_nine (hF : L2Field F) (hq : Nat.card F = 7 ∨ Nat.card F = 9)
    (e : K ≃* L2 F) {u : K} (hu : orderOf u = 2) :
    Nonempty (↥(centralizer ({u} : Set K)) ≃* DihedralGroup 4) ∧
    Nonempty (↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓ innDiagSub e) ≃*
      DihedralGroup 8) := by
  obtain ⟨ε, hε1, hε, hd⟩ := exists_eps_eight hq
  obtain ⟨⟨k1, hk1, -, ⟨ψ1⟩⟩, ⟨k2, hk2, -, ⟨ψ2⟩⟩, -⟩ := ivk_1_3a F hF K e ε hε1 hε 8 hd u hu
  have e1 : k1 = 8 := by omega
  have e2 : k2 = 4 := by omega
  subst e1 e2
  exact ⟨⟨ψ2⟩, ⟨ψ1⟩⟩

omit [Finite K] in
theorem card_eq_of_seven_nine (hF : L2Field F) (hq : Nat.card F = 7 ∨ Nat.card F = 9)
    (e : K ≃* L2 F) : Nat.card K = 168 ∨ Nat.card K = 360 := by
  rw [card_eq_of_L2Field e hF]
  rcases hq with h | h
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

end Data

section GammaAut

variable {K : Type} [Group K]

theorem fixSub_conj (u : K) :
    CFSG.GH74.GLS.C3.Layer1.Bk.fixSub K (MulAut.conj u) = centralizer ({u} : Set K) :=
  Lemma118.fixedSubgroup_conj u

theorem centralizer_le_gammaAut {V : Subgroup (MulAut K)} {u : K} (hu : MulAut.conj u ∈ V)
    (hord : orderOf (MulAut.conj u) = 2) :
    centralizer ({u} : Set K) ≤ CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K V := by
  rw [← fixSub_conj]
  exact le_iSup_of_le (MulAut.conj u) (le_iSup_of_le hu (le_iSup_of_le hord le_rfl))

@[expose] def stabSub (X : Subgroup (MulAut K)) (Γ : Subgroup K) : Subgroup (MulAut K) where
  carrier := {ψ | ψ ∈ X ∧ (∀ k ∈ Γ, ψ k ∈ Γ) ∧ ∀ k ∈ Γ, ψ⁻¹ k ∈ Γ}
  one_mem' := ⟨X.one_mem, fun k hk => hk, fun k hk => hk⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨X.mul_mem ha.1 hb.1, fun k hk => ha.2.1 _ (hb.2.1 k hk), fun k hk => by
      have : (a * b)⁻¹ k = b⁻¹ (a⁻¹ k) := by simp [mul_inv_rev]
      rw [this]
      exact hb.2.2 _ (ha.2.2 k hk)⟩
  inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, ha.2.2, fun k hk => by simpa using ha.2.1 k hk⟩

theorem mem_stabSub {X : Subgroup (MulAut K)} {Γ : Subgroup K} {ψ : MulAut K} :
    ψ ∈ stabSub X Γ ↔ ψ ∈ X ∧ (∀ k ∈ Γ, ψ k ∈ Γ) ∧ ∀ k ∈ Γ, ψ⁻¹ k ∈ Γ := Iff.rfl

theorem inv_mem_of_forall_mem [Finite K] (Γ : Subgroup K) (ψ : MulAut K)
    (h : ∀ k ∈ Γ, ψ k ∈ Γ) : ∀ k ∈ Γ, ψ⁻¹ k ∈ Γ := by
  have hle : Γ.map (ψ : K ≃* K).toMonoidHom ≤ Γ := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have heq : Γ.map (ψ : K ≃* K).toMonoidHom = Γ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective ψ.injective])
  intro k hk
  have hk' : k ∈ Γ.map (ψ : K ≃* K).toMonoidHom := by
    rw [heq]
    exact hk
  obtain ⟨k', hk', hkk⟩ := hk'
  have : ψ⁻¹ k = k' := by
    rw [← hkk]
    simp
  rw [this]
  exact hk'

end GammaAut

section D8

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem eq_of_commute_of_d8 (e : K ≃* L2 F)
    (hQ8 : ∀ u : K, orderOf u = 2 → Nonempty (↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓
      innDiagSub e) ≃* DihedralGroup 8))
    {u₁ u₂ : K} (h₁ : orderOf u₁ = 2) (h₂ : orderOf u₂ = 2) (hne : u₁ ≠ u₂)
    (hcomm : u₁ * u₂ = u₂ * u₁) {g : MulAut K} (hgX : g ∈ innDiagSub e)
    (hg1 : g * MulAut.conj u₁ = MulAut.conj u₁ * g)
    (hg2 : g * MulAut.conj u₂ = MulAut.conj u₂ * g) :
    g = 1 ∨ g = MulAut.conj u₁ ∨ g = MulAut.conj u₂ ∨ g = MulAut.conj u₂ * MulAut.conj u₁ := by
  obtain ⟨θ⟩ := hQ8 u₁ h₁
  have hinj := conj_injective_of_L2 e
  have hu1 : u₁ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₁; omega
  have hu2 : u₂ ≠ 1 := fun h' => by rw [h', orderOf_one] at h₂; omega
  have hsq2 : u₂ * u₂ = 1 := by rw [← pow_two, ← h₂]; exact pow_orderOf_eq_one u₂
  have hX1 : MulAut.conj u₁ ∈ innDiagSub e := innAut_le_innDiagSub e ⟨u₁, rfl⟩
  have hX2 : MulAut.conj u₂ ∈ innDiagSub e := innAut_le_innDiagSub e ⟨u₂, rfl⟩
  have hc21 : MulAut.conj u₂ * MulAut.conj u₁ = MulAut.conj u₁ * MulAut.conj u₂ := by
    rw [← map_mul, ← map_mul, hcomm]
  have hm1 : MulAut.conj u₁ ∈
      centralizer ({MulAut.conj u₁} : Set (MulAut K)) ⊓ innDiagSub e :=
    ⟨mem_centralizer_singleton_iff.2 rfl, hX1⟩
  have hm2 : MulAut.conj u₂ ∈
      centralizer ({MulAut.conj u₁} : Set (MulAut K)) ⊓ innDiagSub e :=
    ⟨mem_centralizer_singleton_iff.2 hc21, hX2⟩
  have hmg : g ∈ centralizer ({MulAut.conj u₁} : Set (MulAut K)) ⊓ innDiagSub e :=
    ⟨mem_centralizer_singleton_iff.2 hg1, hgX⟩
  have key := dih8_centralizer θ (z := ⟨MulAut.conj u₁, hm1⟩) (a := ⟨MulAut.conj u₂, hm2⟩)
    (g := ⟨g, hmg⟩)
    (fun h' => hu1 (hinj (by simpa using congrArg Subtype.val h')))
    (fun c => Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1))
    (Subtype.ext (by simp [← map_mul, hsq2]))
    (fun h' => hu2 (hinj (by simpa using congrArg Subtype.val h')))
    (fun h' => hne.symm (hinj (congrArg Subtype.val h')))
    (Subtype.ext hg2)
  rcases key with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end D8

section Main

theorem b_pgl_K : CFSG.GH74.GLS.C3.Layer1.Bk.B_pgl_K := by
  intro K _ _ q hq79 hmodel y hyInn hy2 hPGL V hVInn hVel hV4
  have hfm : IsFM9 q := by
    rcases hq79 with rfl | rfl
    · exact Or.inr ⟨by norm_num, Or.inr ⟨3, by norm_num⟩⟩
    · exact Or.inl rfl
  obtain ⟨F, _, _, e0, hF, hFq⟩ := exists_l2Field_of_hasL2Model hfm hmodel
  have hq : Nat.card F = 7 ∨ Nat.card F = 9 := hFq ▸ hq79
  have hfmF : IsFM9 (Nat.card F) := hFq ▸ hfm
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists F hF K e0 (inferInstance : Nonempty (Sylow 2 (MulAut K))).some
  have hinj := conj_injective_of_L2 e
  have hyD : y ∈ innDiagSub e := by
    by_contra hyD
    obtain ⟨h9, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfmF e N hy2 hyD
    have hc3 : orderOf (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 3 :=
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      orderOf_eq_prime (by decide) (by decide)
    set c : ↥(fixedSubgroup K y) := ρ.symm (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) with hc
    have hk3 : orderOf (c : K) = 3 := by
      rw [Subgroup.orderOf_coe, hc, MulEquiv.orderOf_eq]
      exact hc3
    have hyk : y (c : K) = c := c.2
    obtain ⟨F₀, _, _, hF₀, ⟨ψ⟩⟩ := hPGL
    have hF₀9 : Nat.card F₀ = 9 := hF₀.trans (hFq.symm.trans h9)
    let tX : ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) :=
      ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩
    let uX : ↥((MulAut.conj : K →* MulAut K).range ⊔ zpowers y) :=
      ⟨MulAut.conj (c : K), Subgroup.mem_sup_left ⟨c, rfl⟩⟩
    have hyne : y ≠ 1 := fun h => hyInn (by rw [h]; exact one_mem _)
    have htX : orderOf tX = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hy2 hyne
    have huX : orderOf uX = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact (orderOf_injective _ hinj (c : K)).trans hk3
    have hcomm : tX * uX = uX * tX := by
      apply Subtype.ext
      have h1 : y * MulAut.conj (c : K) * y⁻¹ = MulAut.conj (c : K) := by
        rw [mul_conj_mul_inv, hyk]
      calc y * MulAut.conj (c : K) = (y * MulAut.conj (c : K) * y⁻¹) * y := by group
        _ = MulAut.conj (c : K) * y := by rw [h1]
    refine pgl2_nine_no_order_six hF₀9 (t := ψ tX) (u := ψ uX) ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq]
      exact htX
    · rw [MulEquiv.orderOf_eq]
      exact huX
    · rw [← map_mul, ← map_mul, hcomm]
  have hX : (MulAut.conj : K →* MulAut K).range ⊔ zpowers y = innDiagSub e :=
    innAut_sup_zpowers_eq e hF hyD hyInn
  rw [hX]
  have hD4 : HasD4Centralizers K := fun u hu => (centralizer_dih_of_seven_nine hF hq e hu).1
  have hQ8 : ∀ u : K, orderOf u = 2 → Nonempty (↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓
      innDiagSub e) ≃* DihedralGroup 8) := fun u hu => (centralizer_dih_of_seven_nine hF hq e hu).2
  have hs : IsSimpleGroup K := isSimpleGroup_of_l2 hF e
  have hKcard : Nat.card K = 168 ∨ Nat.card K = 360 := card_eq_of_seven_nine hF hq e
  have h16 : ¬ 16 ∣ Nat.card K := by
    rcases hKcard with h | h <;> rw [h] <;> norm_num
  set V₀ : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hV₀
  have hVmap : V₀.map (MulAut.conj : K →* MulAut K) = V := Subgroup.map_comap_eq_self hVInn
  have hV₀4 : Nat.card ↥V₀ = 4 := by
    rw [← Subgroup.card_map_of_injective hinj, hVmap]
    exact hV4
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hV₀comm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    hinj (by rw [map_mul, map_mul]; exact hVcomm _ ha _ hb)
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hVel
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian v hv
  have hV₀sq : ∀ u ∈ V₀, u ^ 2 = 1 := fun u hu => hinj (by rw [map_pow, hVsq _ hu, map_one])
  have hV₀ord : ∀ u ∈ V₀, u ≠ 1 → orderOf u = 2 := fun u hu hu1 =>
    orderOf_eq_prime (hV₀sq u hu) hu1
  have hmemV : ∀ u ∈ V₀, MulAut.conj u ∈ V := fun u hu => hVmap ▸ Subgroup.mem_map_of_mem _ hu
  have hordconj : ∀ u : K, orderOf (MulAut.conj u) = orderOf u := fun u =>
    orderOf_injective _ hinj u
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu₁₂⟩ :=
    CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hV₀4
  have h₁ := hV₀ord u₁ hu₁ hu₁1
  have h₂ := hV₀ord u₂ hu₂ hu₂1
  have hcomm12 := hV₀comm u₁ hu₁ u₂ hu₂
  have hΓ1 := centralizer_le_gammaAut (hmemV u₁ hu₁) (by rw [hordconj]; exact h₁)
  have hΓ2 := centralizer_le_gammaAut (hmemV u₂ hu₂) (by rw [hordconj]; exact h₂)
  have hΓN : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K V ≤ normalizer (V₀ : Set K) := by
    refine iSup_le fun w => iSup_le fun hw => iSup_le fun hord => ?_
    obtain ⟨u, hu, rfl⟩ : w ∈ V₀.map (MulAut.conj : K →* MulAut K) := hVmap ▸ hw
    rw [fixSub_conj]
    exact (le_centralizer_normalizer_of_d4 hD4 hV₀4 hV₀comm hu (by rw [← hordconj]; exact hord)).2
  have hΓ24 := card_gamma_eq_of_d4 hD4 hV₀4 hu₁ hu₂ h₁ h₂ hu₁₂ hcomm12 h16 hΓ1 hΓ2 hΓN
  refine ⟨isCoatom_of_card_24 hs hKcard _ hΓ24, ?_, ?_⟩
  ·
    intro φ hφX hφ
    set Γ := CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K V with hΓ
    set S : Subgroup (MulAut K) := stabSub (innDiagSub e) Γ with hS
    have hφS : φ ∈ S := ⟨hφX, hφ, inv_mem_of_forall_mem Γ φ hφ⟩
    have hV₀Γ : V₀ ≤ Γ :=
      (le_centralizer_normalizer_of_d4 hD4 hV₀4 hV₀comm hu₁ h₁).1.trans hΓ1
    have hconjS : ∀ γ ∈ Γ, MulAut.conj γ ∈ S := fun γ hγ =>
      ⟨innAut_le_innDiagSub e ⟨γ, rfl⟩,
        fun k hk => by
          rw [MulAut.conj_apply]
          exact Γ.mul_mem (Γ.mul_mem hγ hk) (Γ.inv_mem hγ),
        fun k hk => by
          rw [← map_inv, MulAut.conj_apply]
          simpa using Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hk) hγ⟩
    have hVS : V ≤ S := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ : v ∈ V₀.map (MulAut.conj : K →* MulAut K) := hVmap ▸ hv
      exact hconjS u (hV₀Γ hu)
    have hS24 : Nat.card ↥S ≤ 24 := by
      have hF4 : Nat.card ↥(V.subgroupOf S) = 4 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
        exact hV4
      have hFn : (V.subgroupOf S).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        obtain ⟨u, hu, hun⟩ : (n : MulAut K) ∈ V₀.map (MulAut.conj : K →* MulAut K) := hVmap ▸ hn
        have hgu : (g : MulAut K) u ∈ V₀ :=
          map_mem_of_d4 hD4 hV₀4 hV₀comm hu₁ hu₂ h₁ h₂ hu₁₂ hΓ1 hΓ2 hΓN hΓ24
            (mem_stabSub.1 g.2).2.1 u hu
        have hE : ((g * n * g⁻¹ : ↥S) : MulAut K) = MulAut.conj ((g : MulAut K) u) := by
          show (g : MulAut K) * (n : MulAut K) * (g : MulAut K)⁻¹ = _
          rw [← hun]
          exact mul_conj_mul_inv _ u
        rw [hE]
        exact hVmap ▸ Subgroup.mem_map_of_mem _ hgu⟩
      refine CFSG.QuasithinUnique.Unc25Small.card_le_24_of_klein (V.subgroupOf S) hF4 ?_
      intro g hg
      have hf1 : (⟨MulAut.conj u₁, hVS (hmemV u₁ hu₁)⟩ : ↥S) ∈ V.subgroupOf S := hmemV u₁ hu₁
      have hf2 : (⟨MulAut.conj u₂, hVS (hmemV u₂ hu₂)⟩ : ↥S) ∈ V.subgroupOf S := hmemV u₂ hu₂
      have hg1 : (g : MulAut K) * MulAut.conj u₁ = MulAut.conj u₁ * g :=
        congrArg Subtype.val (hg _ hf1)
      have hg2 : (g : MulAut K) * MulAut.conj u₂ = MulAut.conj u₂ * g :=
        congrArg Subtype.val (hg _ hf2)
      show (g : MulAut K) ∈ V
      rcases eq_of_commute_of_d8 e hQ8 h₁ h₂ hu₁₂ hcomm12 (mem_stabSub.1 g.2).1 hg1 hg2 with
        h | h | h | h
      · rw [h]; exact V.one_mem
      · rw [h]; exact hmemV u₁ hu₁
      · rw [h]; exact hmemV u₂ hu₂
      · rw [h]; exact V.mul_mem (hmemV u₂ hu₂) (hmemV u₁ hu₁)
    have hconjle : Γ.map (MulAut.conj : K →* MulAut K) ≤ S := by
      rintro _ ⟨γ, hγ, rfl⟩
      exact hconjS γ hγ
    have hcardconj : Nat.card ↥(Γ.map (MulAut.conj : K →* MulAut K)) = 24 := by
      rw [Subgroup.card_map_of_injective hinj]
      exact hΓ24
    have hSeq : Γ.map (MulAut.conj : K →* MulAut K) = S :=
      Subgroup.eq_of_le_of_card_ge hconjle (by rw [hcardconj]; exact hS24)
    have hφc : φ ∈ Γ.map (MulAut.conj : K →* MulAut K) := by
      rw [hSeq]
      exact hφS
    obtain ⟨γ, -, rfl⟩ := hφc
    exact ⟨γ, rfl⟩
  ·
    intro v hv hv1
    obtain ⟨u, hu, rfl⟩ : v ∈ V₀.map (MulAut.conj : K →* MulAut K) := hVmap ▸ hv
    have hu1 : u ≠ 1 := fun h => hv1 (by rw [h, map_one])
    have hu2 := hV₀ord u hu hu1
    obtain ⟨θ⟩ := hQ8 u hu2
    have hQ16 : Nat.card ↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓ innDiagSub e) = 16 := by
      rw [Nat.card_congr θ.toEquiv, DihedralGroup.nat_card]
    by_contra hcon
    have hle : centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓ innDiagSub e ≤
        (centralizer ({u} : Set K)).map (MulAut.conj : K →* MulAut K) := by
      intro φ hφ
      have hφC : φ * MulAut.conj u = MulAut.conj u * φ :=
        mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hφ).1
      by_cases hφI : φ ∈ (MulAut.conj : K →* MulAut K).range
      · obtain ⟨k, rfl⟩ := hφI
        exact ⟨k, mem_centralizer_singleton_iff.2
          (hinj (by rw [map_mul, map_mul]; exact hφC)), rfl⟩
      · exact absurd ⟨φ, (Subgroup.mem_inf.1 hφ).2, hφI, hφC⟩ hcon
    have hcard := Subgroup.card_le_of_le hle
    rw [hQ16, Subgroup.card_map_of_injective hinj, card_centralizer_of_d4 hD4 hu2] at hcard
    omega

end Main

end CFSG.GH74.GLS.IVK.Proofs2
