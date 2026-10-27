module

public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.CharacterTheory.Semidihedral.FixedFieldCentralizer

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pgl2FieldAut pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff)
open CFSG.Semidihedral.FixedFieldCentralizer (pglInclusion pgl_fixed_iff F0)

theorem mem_of_pow_two_pow_mem {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd N.index) {x : G} {j : ℕ} (hx : x ^ 2 ^ j ∈ N) : x ∈ N := by
  have : N.FiniteIndex := ⟨hN.pos.ne'⟩
  have h1 : (x : G ⧸ N) ^ 2 ^ j = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hx
  have h2 : orderOf (x : G ⧸ N) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ j) N.index := (Nat.coprime_two_left.mpr hN).pow_left j
  have h4 : orderOf (x : G ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hcop) h2
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4

theorem exists_zpow_odd_and_two_pow {G : Type*} [Group G] (σ : G) (hσ : IsOfFinOrder σ) :
    ∃ u : ℤ, Odd (orderOf (σ ^ u)) ∧ ∃ j : ℕ, (σ * (σ ^ u)⁻¹) ^ 2 ^ j = 1 := by
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos_iff.mpr hσ).ne'
  have hcop : Nat.Coprime (2 ^ j) m := (Nat.coprime_two_left.mpr hm).pow_left j
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hab' : a * 2 ^ j + b * m = 1 := by
    have := hab
    push_cast at this
    exact this
  have hn' : (orderOf σ : ℤ) = 2 ^ j * m := by rw [hn]; push_cast; ring
  refine ⟨a * 2 ^ j, ?_, j, ?_⟩
  · apply Odd.of_dvd_nat hm
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, show a * 2 ^ j * (m : ℤ) = (orderOf σ : ℤ) * a by
      rw [hn']; ring, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h1 : σ * (σ ^ (a * 2 ^ j))⁻¹ = σ ^ (b * (m : ℤ)) := by
      rw [← zpow_neg, ← zpow_one_add]
      congr 1
      linarith
    rw [h1, ← zpow_natCast, ← zpow_mul, show b * (m : ℤ) * ((2 ^ j : ℕ) : ℤ) =
      (orderOf σ : ℤ) * b by rw [hn']; push_cast; ring, zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, one_zpow]

section Complement

variable {F : Type} [Field F] [Finite F]

theorem mem_of_mem_pGLRange (hF : IsOddPrimePower (Nat.card F)) {A M : Subgroup (PGammaL2 F)}
    (hM : IsStandardLayer M) (hodd : Odd (M.relIndex A)) {x : PGammaL2 F} (hxA : x ∈ A)
    (hx : x ∈ pGammaL2PGLRange F) : x ∈ M := by
  rcases hM.eq_pGLRange_or_inf with hMP | hMP
  · rw [hMP]
    exact hx
  · have hx2 : x ^ 2 ^ 1 ∈ M := by
      obtain ⟨g, rfl⟩ := hx
      apply hM.pGammaL2PSLRange_le
      obtain ⟨y, hy⟩ := Subgroup.sq_mem_of_index_two
        (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF) g
      rw [← map_pow, pow_one, mem_pGammaL2PSLRange_iff]
      exact ⟨y, by rw [hy]⟩
    have := hM.normal hF
    have : (M.subgroupOf A).Normal := Subgroup.Normal.subgroupOf this A
    exact mem_of_pow_two_pow_mem (N := M.subgroupOf A) (x := ⟨x, hxA⟩) hodd hx2

theorem inr_right_mem (hF : IsOddPrimePower (Nat.card F)) {A M : Subgroup (PGammaL2 F)}
    (hM : IsStandardLayer M) (hMA : M ≤ A) (hodd : Odd (M.relIndex A)) {a : PGammaL2 F}
    (ha : a ∈ A) (hσ : Odd (orderOf a.right)) : SemidirectProduct.inr a.right ∈ A := by
  have hk : a ^ orderOf a.right ∈ pGammaL2PGLRange F := by
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_pow,
      SemidirectProduct.rightHom_eq_right, pow_orderOf_eq_one]
  have hkM : a ^ orderOf a.right ∈ M :=
    mem_of_mem_pGLRange hF hM hodd (A.pow_mem ha _) hk
  have hleft : SemidirectProduct.inl a.left ∈ A := by
    rcases hM.eq_pGLRange_or_inf with hMP | hMP
    · exact hMA (hMP ▸ ⟨a.left, rfl⟩)
    · apply hMA
      apply hM.pGammaL2PSLRange_le
      have hpsl : a ^ orderOf a.right ∈ pGammaL2PSLRange F := by
        rw [← hMP]
        exact ⟨hkM, hk⟩
      rw [pGammaL2PSLRange_eq_inf_ker hF, Subgroup.mem_inf, MonoidHom.mem_ker, map_pow] at hpsl
      have hΦ : pGammaL2DetClass F hF a = 1 := by
        obtain ⟨t, ht⟩ := hσ
        have h := hpsl.2
        rw [ht, pow_succ, pow_mul, squareClass_sq, one_pow, one_mul] at h
        exact h
      rw [← left_mem_range_toPGL_iff hF] at hΦ
      obtain ⟨y, hy⟩ := hΦ
      rw [mem_pGammaL2PSLRange_iff]
      exact ⟨y, by rw [hy]⟩
  have h : SemidirectProduct.inr a.right = (SemidirectProduct.inl a.left)⁻¹ * a := by
    rw [eq_inv_mul_iff_mul_eq, SemidirectProduct.inl_left_mul_inr_right]
  rw [h]
  exact A.mul_mem (A.inv_mem hleft) ha

theorem exists_mem_mul_mem_fieldRange (hF : IsOddPrimePower (Nat.card F))
    {A M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M) (hMA : M ≤ A)
    (hodd : Odd (M.relIndex A)) {a : PGammaL2 F} (ha : a ∈ A) :
    ∃ m ∈ M, ∃ e ∈ A ⊓ pGammaL2FieldRange F, a = m * e := by
  obtain ⟨u, hu, j, hj⟩ := exists_zpow_odd_and_two_pow a.right (isOfFinOrder_of_finite _)
  have hright : (a ^ u).right = a.right ^ u := by
    rw [← SemidirectProduct.rightHom_eq_right, map_zpow]
  have heA : SemidirectProduct.inr (a.right ^ u) ∈ A := by
    have h := inr_right_mem hF hM hMA hodd (A.zpow_mem ha u) (by rwa [hright])
    rwa [hright] at h
  have hmA : a * (SemidirectProduct.inr (a.right ^ u))⁻¹ ∈ A := A.mul_mem ha (A.inv_mem heA)
  refine ⟨a * (SemidirectProduct.inr (a.right ^ u))⁻¹, ?_, SemidirectProduct.inr (a.right ^ u),
    ⟨heA, ⟨_, rfl⟩⟩, by group⟩
  have hpow : (a * (SemidirectProduct.inr (a.right ^ u))⁻¹) ^ 2 ^ j ∈ pGammaL2PGLRange F := by
    rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
      map_pow, map_mul, map_inv, SemidirectProduct.rightHom_inr,
      SemidirectProduct.rightHom_eq_right, hj]
  have hM' := mem_of_mem_pGLRange hF hM hodd (A.pow_mem hmA _) hpow
  have := hM.normal hF
  have : (M.subgroupOf A).Normal := Subgroup.Normal.subgroupOf this A
  exact mem_of_pow_two_pow_mem (N := M.subgroupOf A) (x := ⟨_, hmA⟩) hodd hM'

end Complement

section Centralizer

variable {F : Type} [Field F] [Finite F]

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

omit [Finite F] in
theorem relIndex_pGLRange_eq_card_map (K : Subgroup (PGammaL2 F)) :
    (pGammaL2PGLRange F).relIndex K = Nat.card (K.map SemidirectProduct.rightHom) := by
  rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, ← MonoidHom.comap_bot,
    Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]

theorem relIndex_pGammaL2PSLRange_pGLStar_le_two :
    (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) ≤ 2 := by
  classical
  rw [← pGLStar_inf_pGLRange, Subgroup.inf_relIndex_left, relIndex_pGLRange_eq_card_map]
  have := isCyclic_ringEquiv F
  set K := (pGammaL2PGLStar F).map (SemidirectProduct.rightHom :
    PGammaL2 F →* (F ≃+* F))
  have : IsCyclic K := Subgroup.isCyclic K
  have : Fintype K := Fintype.ofFinite K
  have hle := IsCyclic.card_pow_eq_one_le (α := K) (n := 2) (by norm_num)
  have hall : (Finset.univ.filter fun a : K => a ^ 2 = 1) = Finset.univ := by
    ext ⟨σ, hσ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    obtain ⟨x, hx, rfl⟩ := hσ
    apply Subtype.ext
    change (SemidirectProduct.rightHom x) ^ 2 = 1
    rw [SemidirectProduct.rightHom_eq_right]
    exact hx.1
  rw [hall, Finset.card_univ] at hle
  rwa [Nat.card_eq_fintype_card]

theorem odd_index_range_pglInclusion (hF : IsOddPrimePower (Nat.card F))
    (Γ : Subgroup (F ≃+* F)) (hΓ : Odd (Nat.card Γ)) : Odd (pglInclusion F Γ).range.index := by
  obtain ⟨p, f, hp, hpodd, hf, hcard⟩ := hF
  obtain ⟨-, -, hq0, hqodd, -, hfixed, hpower, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.odd_fixed_field_data p f hp hpodd hf F hcard Γ hΓ
  obtain ⟨r, hr, hratio⟩ :=
    CFSG.Semidihedral.FixedFieldCentralizer.projective_card_odd_ratio hq0 hqodd hΓ
  have hinj : Function.Injective (pglInclusion F Γ) :=
    CFSG.Semidihedral.FixedFieldCentralizer.pgl_map_injective _
  have hcardC : Nat.card (pglInclusion F Γ).range =
      Nat.card (F0 F Γ) * (Nat.card (F0 F Γ) ^ 2 - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact CFSG.GorensteinWalter.pgl2_card_formula _
  have hi := (pglInclusion F Γ).range.index_mul_card
  rw [hcardC, CFSG.GorensteinWalter.pgl2_card_formula, hfixed, hpower] at hi
  have hbase : 0 < p ^ (f / Nat.card Γ) * ((p ^ (f / Nat.card Γ)) ^ 2 - 1) := by
    have h1 : 1 < (p ^ (f / Nat.card Γ)) ^ 2 := by nlinarith
    have h2 : 0 < p ^ (f / Nat.card Γ) := by omega
    exact Nat.mul_pos h2 (by omega)
  rw [Nat.eq_of_mul_eq_mul_right hbase (hi.trans hratio)]
  exact hr

omit [Finite F] in
theorem inr_mul_inl_comm {Γ : Subgroup (F ≃+* F)} {σ : F ≃+* F} (hσ : σ ∈ Γ) {g : PGL2 F}
    (hg : g ∈ (pglInclusion F Γ).range) :
    (SemidirectProduct.inr σ : PGammaL2 F) * SemidirectProduct.inl g =
      SemidirectProduct.inl g * SemidirectProduct.inr σ := by
  have hfix : pgl2FieldAut F σ g = g := (pgl_fixed_iff F Γ g).mpr hg ⟨σ, hσ⟩
  have h := SemidirectProduct.inl_aut (φ := pgl2FieldAut F) σ g
  rw [hfix] at h
  calc (SemidirectProduct.inr σ : PGammaL2 F) * SemidirectProduct.inl g =
        SemidirectProduct.inr σ * SemidirectProduct.inl g * SemidirectProduct.inr σ⁻¹ *
          SemidirectProduct.inr σ := by
          rw [map_inv]; group
    _ = SemidirectProduct.inl g * SemidirectProduct.inr σ := by rw [← h]

theorem odd_relIndex_inf_centralizer (hF : IsOddPrimePower (Nat.card F))
    {M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M) (Γ : Subgroup (F ≃+* F))
    (hΓ : Odd (Nat.card Γ)) :
    Odd ((M ⊓ Subgroup.centralizer
      ((Γ.map SemidirectProduct.inr : Subgroup (PGammaL2 F)) : Set (PGammaL2 F))).relIndex M) := by
  set Z := Subgroup.centralizer
    ((Γ.map SemidirectProduct.inr : Subgroup (PGammaL2 F)) : Set (PGammaL2 F))
  set C := (pglInclusion F Γ).range
  set C' := C.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hC'Z : C' ≤ Z := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    exact inr_mul_inl_comm hσ hg
  have hC'P : C' ≤ pGammaL2PGLRange F := Subgroup.map_le_range _ _
  have hCodd := odd_index_range_pglInclusion hF Γ hΓ
  have hC'odd : Odd (C'.relIndex (pGammaL2PGLRange F)) := by
    rw [pGammaL2PGLRange, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ SemidirectProduct.inl_injective,
      Subgroup.relIndex_top_right]
    exact hCodd
  have h2 : (pGammaL2PSLRange F).relIndex (pGammaL2PGLRange F) = 2 :=
    CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF
  have hX : Odd ((C' ⊓ pGammaL2PSLRange F).relIndex (pGammaL2PSLRange F)) := by
    have e1 := Subgroup.relIndex_mul_relIndex (C' ⊓ pGammaL2PSLRange F) C'
      (pGammaL2PGLRange F) inf_le_left hC'P
    have e2 := Subgroup.relIndex_mul_relIndex (C' ⊓ pGammaL2PSLRange F) (pGammaL2PSLRange F)
      (pGammaL2PGLRange F) inf_le_right pGammaL2PSLRange_le_pGLRange
    rw [h2] at e2
    rw [Subgroup.inf_relIndex_left] at e1
    have hale : (pGammaL2PSLRange F).relIndex C' ≤ 2 :=
      (Subgroup.relIndex_le_of_le_right hC'P (by rw [h2]; norm_num)).trans_eq h2
    have hane := relIndex_ne_zero_of_finite (pGammaL2PSLRange F) C'
    obtain ⟨k, hk⟩ := hC'odd
    rw [hk] at e1
    refine ⟨k, ?_⟩
    interval_cases h : (pGammaL2PSLRange F).relIndex C' <;> omega
  rcases hM with rfl | rfl | rfl
  · exact Odd.of_dvd_nat hX (Subgroup.relIndex_dvd_of_le_left _ (le_inf inf_le_right
      (inf_le_left.trans hC'Z)))
  · exact Odd.of_dvd_nat hC'odd (Subgroup.relIndex_dvd_of_le_left _ (le_inf hC'P hC'Z))
  · set Y := pGammaL2PGLStar F ⊓ Z
    have hW : Odd ((Y ⊓ pGammaL2PSLRange F).relIndex (pGammaL2PSLRange F)) :=
      Odd.of_dvd_nat hX (Subgroup.relIndex_dvd_of_le_left _ (le_inf (le_inf
        (inf_le_right.trans pGammaL2PSLRange_le_pGLStar) (inf_le_left.trans hC'Z)) inf_le_right))
    have e1 := Subgroup.relIndex_mul_relIndex (Y ⊓ pGammaL2PSLRange F) Y
      (pGammaL2PGLStar F) inf_le_left inf_le_left
    have e2 := Subgroup.relIndex_mul_relIndex (Y ⊓ pGammaL2PSLRange F) (pGammaL2PSLRange F)
      (pGammaL2PGLStar F) inf_le_right pGammaL2PSLRange_le_pGLStar
    rw [Subgroup.inf_relIndex_left] at e1
    have hs := relIndex_pGammaL2PSLRange_pGLStar_le_two (F := F)
    have hsne := relIndex_ne_zero_of_finite (pGammaL2PSLRange F) (pGammaL2PGLStar F)
    have hale : (pGammaL2PSLRange F).relIndex Y ≤
        (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) :=
      Subgroup.relIndex_le_of_le_right inf_le_left hsne
    have hane := relIndex_ne_zero_of_finite (pGammaL2PSLRange F) Y
    by_cases hs1 : (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) = 1
    · have ha1 : (pGammaL2PSLRange F).relIndex Y = 1 := by omega
      rw [ha1, one_mul] at e1
      rw [hs1, mul_one] at e2
      rw [e1, ← e2]
      exact hW
    ·
      have hs2 : (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) = 2 := by omega
      obtain ⟨y, hyS, hyP⟩ : ∃ y ∈ pGammaL2PGLStar F, y ∉ pGammaL2PSLRange F := by
        by_contra hcon
        push Not at hcon
        exact hs1 (Subgroup.relIndex_eq_one.mpr hcon)
      have hτ1 : y.right ≠ 1 := by
        intro h1
        apply hyP
        have hyL : y ∈ pGammaL2PGLRange F := by
          rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
            SemidirectProduct.rightHom_eq_right, h1]
        rw [← pGLStar_inf_pGLRange]
        exact ⟨hyS, hyL⟩
      obtain ⟨δ, hδC, hδR⟩ : ∃ δ ∈ C, δ ∉
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
        by_contra hcon
        push Not at hcon
        have h := Subgroup.relIndex_mul_index (H := C) hcon
        rw [CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF] at h
        rw [← h] at hCodd
        exact (Nat.not_even_iff_odd.mpr hCodd) (even_two.mul_left _)
      set x : PGammaL2 F := SemidirectProduct.inl δ * SemidirectProduct.inr y.right
      have hxS : x ∈ pGammaL2PGLStar F := by
        refine ⟨by simpa [x] using hyS.1, ?_⟩
        simp only [x, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
          SemidirectProduct.right_inr, map_one, mul_one, one_mul]
        exact ⟨fun h => absurd h hδR, fun h => absurd h hτ1⟩
      have hxZ : x ∈ Z := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨σ, hσ, rfl⟩
        simp only [x]
        rw [← mul_assoc, inr_mul_inl_comm hσ hδC, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
          ringEquiv_mul_comm]
      have hxP : x ∉ pGammaL2PSLRange F := by
        intro hx
        have h := pGammaL2PSLRange_le_pGLRange hx
        rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
          SemidirectProduct.rightHom_eq_right] at h
        simp [x] at h
        exact hτ1 h
      have ha2 : (pGammaL2PSLRange F).relIndex Y = 2 := by
        have hne : (pGammaL2PSLRange F).relIndex Y ≠ 1 := by
          rw [Ne, Subgroup.relIndex_eq_one]
          intro hle
          exact hxP (hle ⟨hxS, hxZ⟩)
        omega
      rw [ha2] at e1
      rw [hs2] at e2
      have : Y.relIndex (pGammaL2PGLStar F) =
          (Y ⊓ pGammaL2PSLRange F).relIndex (pGammaL2PSLRange F) := by omega
      rw [this]
      exact hW

end Centralizer

section Conj

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

theorem map_conj_eq_of_normal {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (x : G) :
    N.map (MulAut.conj x).toMonoidHom = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact hN.conj_mem n hn x
  · intro n hn
    refine ⟨x⁻¹ * n * x, ?_, ?_⟩
    · simpa using hN.conj_mem n hn x⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g y : G) :
    y ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * y * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv]

theorem IsLinearDecomposition.conj (hd : IsLinearDecomposition ι L E S) (g : H) :
    IsLinearDecomposition ((MulAut.conj (ι g)⁻¹).toMonoidHom.comp ι) L
      (E.map (MulAut.conj g).toMonoidHom) (g • S) where
  isOddPrimePower_card := hd.isOddPrimePower_card
  injective := (MulAut.conj (ι g)⁻¹).injective.comp hd.injective
  normal := hd.normal
  map_eq := by
    rw [← Subgroup.map_map, map_conj_eq_of_normal
      (hd.isStandardLayer.normal hd.isOddPrimePower_card)]
    exact hd.map_eq
  isCyclic := ((E.equivMapOfInjective _ (MulAut.conj g).injective).isCyclic).mp hd.isCyclic
  odd_card := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hd.odd_card
  inf_eq_bot := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, e, he, rfl⟩
    have heL : e ∈ L := by
      have h := hd.normal.conj_mem _ hxL g⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using h
    have he1 : e = 1 := by
      have h : e ∈ L ⊓ E := ⟨heL, he⟩
      rwa [hd.inf_eq_bot, Subgroup.mem_bot] at h
    simp [he1]
  sup_eq_top := by
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hd.sup_eq_top
    rwa [Subgroup.map_sup, map_conj_eq_of_normal hd.normal,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
  map_le_fieldRange := by
    rw [Subgroup.map_map]
    have hcomp : ((MulAut.conj (ι g)⁻¹).toMonoidHom.comp ι).comp
        (MulAut.conj g).toMonoidHom = ι := by
      refine MonoidHom.ext fun e => ?_
      change (ι g)⁻¹ * ι (g * e * g⁻¹) * (ι g)⁻¹⁻¹ = ι e
      rw [map_mul, map_mul, map_inv]
      group
    rw [hcomp]
    exact hd.map_le_fieldRange
  le_centralizer := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, mem_smul_sylow_iff] at hy
    have hcomm := Subgroup.mem_centralizer_iff.mp (hd.le_centralizer he) _ hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * (g * e * g⁻¹) = g * (g⁻¹ * y * g * e) * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = g * e * g⁻¹ * y := by group

end Conj

theorem exists_isLinearDecomposition_of_embedding {H : Type} [Group H] [Finite H]
    {F : Type} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    {ι : H →* PGammaL2 F} (hι : Function.Injective ι) {M : Subgroup (PGammaL2 F)}
    (hM : IsStandardLayer M) (hMle : M ≤ ι.range) (hodd : Odd (M.relIndex ι.range))
    (S : Sylow 2 H) :
    ∃ (ι' : H →* PGammaL2 F) (E : Subgroup H), IsLinearDecomposition ι' (M.comap ι) E S ∧
      (M.comap ι).map ι' = M := by
  set A := ι.range
  set Estd := A ⊓ pGammaL2FieldRange F
  set L := M.comap ι
  set E := Estd.comap ι
  have hLn : L.Normal := (hM.normal hF).comap ι
  have hLE : L ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxE⟩
    have h : ι x ∈ M ⊓ pGammaL2FieldRange F := ⟨hxL, hxE.2⟩
    rw [hM.inf_fieldRange, Subgroup.mem_bot] at h
    exact hι (h.trans (map_one ι).symm)
  have hLE' : L ⊔ E = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨m, hm, e, he, hme⟩ :=
      exists_mem_mul_mem_fieldRange hF hM hMle hodd (⟨h, rfl⟩ : ι h ∈ ι.range)
    obtain ⟨e₀, he₀⟩ := he.1
    have he₀E : e₀ ∈ E := by
      change ι e₀ ∈ Estd
      rw [he₀]
      exact he
    have hl : h * e₀⁻¹ ∈ L := by
      change ι (h * e₀⁻¹) ∈ M
      rw [map_mul, map_inv, he₀, hme, mul_inv_cancel_right]
      exact hm
    have : h = h * e₀⁻¹ * e₀ := by group
    rw [this]
    exact (L ⊔ E).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right he₀E)
  have hcompl : L.IsComplement' E := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hLE) ?_
    rw [← Subgroup.normal_mul, hLE', Subgroup.coe_top]
  have hLidx : L.index = M.relIndex A := Subgroup.index_comap M ι
  have hEcard : Nat.card E = M.relIndex A := by
    rw [← hLidx]
    exact hcompl.symm.index_eq_card.symm
  have hEmap : E.map ι = Estd := Subgroup.map_comap_eq_self inf_le_left
  set Γ := Estd.map (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))
  have hEstd : Estd = Γ.map SemidirectProduct.inr := by
    apply le_antisymm
    · intro x hx
      obtain ⟨σ, rfl⟩ := hx.2
      exact ⟨σ, ⟨_, hx, SemidirectProduct.rightHom_inr σ⟩, rfl⟩
    · rintro _ ⟨σ, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨τ, rfl⟩ := hy.2
      rw [SemidirectProduct.rightHom_inr]
      exact hy
  have hcardEstd : Nat.card Estd = Nat.card E := by
    rw [← hEmap, Subgroup.card_map_of_injective hι]
  have hΓcard : Nat.card Γ = Nat.card E := by
    rw [← hcardEstd, hEstd, Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
  have hΓodd : Odd (Nat.card Γ) := by
    rw [hΓcard, hEcard]
    exact hodd
  have hEcyc : IsCyclic E := by
    have := isCyclic_ringEquiv F
    have hΓcyc : IsCyclic Γ := Subgroup.isCyclic Γ
    have e1 : E ≃* Estd :=
      (E.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hEmap)
    have e2 : Γ ≃* Estd := (Γ.equivMapOfInjective _ SemidirectProduct.inr_injective).trans
      (MulEquiv.subgroupCongr hEstd.symm)
    exact (e1.trans e2.symm).isCyclic.mpr hΓcyc
  have hY := odd_relIndex_inf_centralizer hF hM Γ hΓodd
  set Z := Subgroup.centralizer
    ((Γ.map SemidirectProduct.inr : Subgroup (PGammaL2 F)) : Set (PGammaL2 F))
  set YH := (M ⊓ Z).comap ι
  have hYHL : YH ≤ L := Subgroup.comap_mono inf_le_left
  have hYHidx : Odd YH.index := by
    rw [← Subgroup.relIndex_mul_index hYHL, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self hMle, hLidx]
    exact hY.mul hodd
  obtain ⟨S₀, hS₀⟩ :=
    CFSG.Semidihedral.FixedFieldCentralizer.exists_sylow_le_of_odd_index YH hYHidx
  have hd₀ : IsLinearDecomposition ι L E S₀ :=
    { isOddPrimePower_card := hF
      injective := hι
      normal := hLn
      map_eq := by rw [Subgroup.map_comap_eq_self hMle]; exact hM
      isCyclic := hEcyc
      odd_card := by rw [hEcard]; exact hodd
      inf_eq_bot := hLE
      sup_eq_top := hLE'
      map_le_fieldRange := by rw [hEmap]; exact inf_le_right
      le_centralizer := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hsZ : ι s ∈ Z := (hS₀ hs).2
        have heZ : ι e ∈ Γ.map SemidirectProduct.inr := by rw [← hEstd]; exact he
        apply hι
        rw [map_mul, map_mul]
        exact (Subgroup.mem_centralizer_iff.mp hsZ _ heZ).symm }
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H S₀ S
  refine ⟨_, _, hd₀.conj g, ?_⟩
  rw [← Subgroup.map_map, Subgroup.map_comap_eq_self hMle, map_conj_eq_of_normal (hM.normal hF)]

theorem IsLinearDecomposition.relIndex_linearCore {H : Type} [Group H] {F : Type} [Field F]
    [Finite F] {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}
    (hd : IsLinearDecomposition ι L E S) :
    (linearCore ι).relIndex L = 1 ∨ (linearCore ι).relIndex L = 2 := by
  rw [linearCore, Subgroup.relIndex_comap]
  rcases hd.map_eq with h | h | h <;> rw [h]
  · exact Or.inl (Subgroup.relIndex_self _)
  · exact Or.inr (CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F
      hd.isOddPrimePower_card)
  · have h1 := relIndex_pGammaL2PSLRange_pGLStar_le_two (F := F)
    have h2 := relIndex_ne_zero_of_finite (pGammaL2PSLRange F) (pGammaL2PGLStar F)
    omega

end CFSG.ABGDGroups
