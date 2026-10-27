module

public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.Monster.B.GSide.Setup
public import CFSG.Monster.B.Recog.GenericIndexTwo
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuterFinal

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide

section Generic

variable {A B X : Type*} [Group A] [Group B] [Group X]

private theorem mul_self_eq_one_of_orderOf_eq_two {a : A} (h : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem congr_conj (ι : A ≃* B) (a : A) :
    MulAut.congr ι (MulAut.conj a) = MulAut.conj (ι a) := by
  ext b
  obtain ⟨a', rfl⟩ := ι.surjective b
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, map_mul, map_inv]

theorem congr_mem_range_conj_iff (ι : A ≃* B) (f : MulAut A) :
    MulAut.congr ι f ∈ (MulAut.conj : B →* MulAut B).range ↔
      f ∈ (MulAut.conj : A →* MulAut A).range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨ι.symm b, (MulAut.congr ι).injective ?_⟩
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨a, rfl⟩
    exact ⟨ι a, (congr_conj ι a).symm⟩

theorem mem_of_conjNormal_mem_range {L : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) ≤ L) {x : X}
    (hx : MulAut.conjNormal x ∈ (MulAut.conj : L →* MulAut L).range) : x ∈ L := by
  obtain ⟨l, hl⟩ := hx
  have key : ∀ m ∈ L, x * m * x⁻¹ = l * m * (l : X)⁻¹ := fun m hm => by
    have h := congrArg Subtype.val (DFunLike.congr_fun hl ⟨m, hm⟩)
    rw [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv] at h
    exact h.symm
  have hc : (l : X)⁻¹ * x ∈ centralizer (L : Set X) := by
    rw [mem_centralizer_iff]
    intro m hm
    calc m * ((l : X)⁻¹ * x) = (l : X)⁻¹ * (l * m * (l : X)⁻¹) * x := by group
      _ = (l : X)⁻¹ * x * m := by rw [← key m hm]; group
  simpa using L.mul_mem l.2 (hC hc)

theorem index_le_two_of_range_conj_index_le_two [Finite A]
    (hO : (MulAut.conj : A →* MulAut A).range.index ≤ 2) {L : Subgroup X} [L.Normal]
    (ι : L ≃* A) (hC : centralizer (L : Set X) ≤ L) : L.index ≤ 2 := by
  have hL : L = (MulAut.conj : A →* MulAut A).range.comap
      ((MulAut.congr ι).toMonoidHom.comp MulAut.conjNormal) := by
    ext x
    rw [mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, congr_mem_range_conj_iff]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, (MulAut.conjNormal_val (h := ⟨x, hx⟩)).symm⟩
    · exact mem_of_conjNormal_mem_range hC
  rw [hL, index_comap]
  calc _ ≤ (MulAut.conj : A →* MulAut A).range.relIndex ⊤ :=
        relIndex_le_of_le_right le_top (by rw [relIndex_top_right]; exact FiniteIndex.index_ne_zero)
    _ = _ := relIndex_top_right _
    _ ≤ 2 := hO

theorem centralizer_le_of_index_two {E : Type*} [Group E] {D : Subgroup E} (hD2 : D.index = 2)
    (hZ : center E ≤ D) : centralizer (D : Set E) ≤ D := by
  intro y hy
  by_contra hyD
  refine hyD (hZ (mem_center_iff.2 fun x => ?_))
  by_cases hx : x ∈ D
  · exact (mem_centralizer_iff.1 hy) x hx
  · have hxy : x * y⁻¹ ∈ D := by
      rw [mul_mem_iff_of_index_two hD2, inv_mem_iff]
      exact iff_of_false hx hyD
    have h1 := (mem_centralizer_iff.1 hy) _ hxy
    calc x * y = x * y⁻¹ * y * y := by group
      _ = y * (x * y⁻¹) * y := by rw [h1]
      _ = y * x := by group

theorem centralizer_eq_map_center {E : Type*} [Group E] {D : Subgroup E}
    (h : centralizer (D : Set E) ≤ D) : centralizer (D : Set E) = (center D).map D.subtype := by
  apply le_antisymm
  · intro y hy
    refine ⟨⟨y, h hy⟩, mem_center_iff.2 fun m => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.1 hy) m m.2
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro m hm
    exact congrArg Subtype.val ((mem_center_iff.1 hw) ⟨m, hm⟩)

theorem exists_involution_of_not_mem_range_conj {E : Type*} [Group E] [Finite E] {D : Subgroup E}
    (hD2 : D.index = 2) (hO : (MulAut.conj : D →* MulAut D).range.index ≤ 2)
    (hCD : centralizer (D : Set E) ≤ D)
    (hsq : ∀ y : E, y ∉ D → y * y ∈ centralizer (D : Set E) → y * y = 1) {σ : MulAut D}
    (hσ : σ ∉ (MulAut.conj : D →* MulAut D).range) (hσ2 : ∀ m, σ (σ m) = m) :
    ∃ s : E, s ∉ D ∧ s * s = 1 ∧ ∀ m : D, ((σ m : D) : E) = s * m * s⁻¹ := by
  have hDN : D.Normal := normal_of_index_eq_two hD2
  obtain ⟨b, hbD⟩ : ∃ b : E, b ∉ D := by
    by_contra! h
    rw [(eq_top_iff' D).2 h, index_top] at hD2
    exact absurd hD2 (by norm_num)
  have hσb : (MulAut.conjNormal b : MulAut D) ∉ (MulAut.conj : D →* MulAut D).range := fun h =>
    hbD (mem_of_conjNormal_mem_range hCD h)
  have hInn2 : (MulAut.conj : D →* MulAut D).range.index = 2 := by
    have h0 : (MulAut.conj : D →* MulAut D).range.index ≠ 0 := FiniteIndex.index_ne_zero
    have h1 : (MulAut.conj : D →* MulAut D).range.index ≠ 1 :=
      fun h => hσ ((index_eq_one.1 h) ▸ mem_top _)
    omega
  obtain ⟨e, he⟩ : σ * (MulAut.conjNormal b)⁻¹ ∈ (MulAut.conj : D →* MulAut D).range := by
    rw [mul_mem_iff_of_index_two hInn2, inv_mem_iff]
    exact iff_of_false hσ hσb
  have hσs : ∀ m : D, ((σ m : D) : E) = (e * b) * m * ((e : E) * b)⁻¹ := by
    intro m
    have h1 : σ = MulAut.conj e * MulAut.conjNormal b := by rw [he, inv_mul_cancel_right]
    rw [h1, MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv,
      MulAut.conjNormal_apply]
    group
  have hsD : (e : E) * b ∉ D := fun h =>
    hbD (by simpa using D.mul_mem (D.inv_mem e.2) h)
  refine ⟨e * b, hsD, hsq _ hsD ?_, hσs⟩
  rw [mem_centralizer_iff]
  intro m hm
  have h2 := hσs (σ ⟨m, hm⟩)
  rw [hσ2, hσs] at h2
  calc m * ((e : E) * b * ((e : E) * b)) =
      (e * b) * ((e * b) * m * ((e : E) * b)⁻¹) * ((e : E) * b)⁻¹ * ((e : E) * b * (e * b)) := by
        rw [← h2]
    _ = (e : E) * b * (e * b) * m := by group

theorem exists_mulEquiv_of_index_two_of_involution {E : Type*} [Group E] [Finite E]
    {D : Subgroup E} (hD2 : D.index = 2) (hO : (MulAut.conj : D →* MulAut D).range.index ≤ 2)
    (hCD : centralizer (D : Set E) ≤ D)
    (hsq : ∀ y : E, y ∉ D → y * y ∈ centralizer (D : Set E) → y * y = 1)
    {L : Subgroup X} (hL2 : L.index = 2) (ι : L ≃* D) (hC : centralizer (L : Set X) ≤ L)
    {s : X} (hsL : s ∉ L) (hs2 : s * s = 1) :
    ∃ e : X ≃* E, ∀ l : L, e l = (ι l : E) := by
  have hN : L.Normal := normal_of_index_eq_two hL2
  have hσ : MulAut.congr ι (MulAut.conjNormal s) ∉ (MulAut.conj : D →* MulAut D).range :=
    fun h => hsL (mem_of_conjNormal_mem_range hC ((congr_mem_range_conj_iff ι _).1 h))
  have hσι : ∀ l : L, MulAut.congr ι (MulAut.conjNormal s) (ι l) = ι (MulAut.conjNormal s l) :=
    fun l => by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
  have hσ2 : ∀ m, MulAut.congr ι (MulAut.conjNormal s) (MulAut.congr ι (MulAut.conjNormal s) m) =
      m := by
    intro m
    obtain ⟨l, rfl⟩ := ι.surjective m
    rw [hσι, hσι]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    calc s * (s * l * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
      _ = l := by rw [hs2]; group
  obtain ⟨s', hs'D, hs'2, hs'⟩ := exists_involution_of_not_mem_range_conj hD2 hO hCD hsq hσ hσ2
  have hrange : (D.subtype.comp ι.toMonoidHom).range = D := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact (ι l).2
    · intro hy
      exact ⟨ι.symm ⟨y, hy⟩, by simp⟩
  obtain ⟨φ, hφ, -⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq L.subtype
    (D.subtype.comp ι.toMonoidHom) L.subtype_injective (D.subtype_injective.comp ι.injective)
    (by rw [L.range_subtype]; exact hL2) (by rw [hrange]; exact hD2)
    (by rw [L.range_subtype]; exact hsL) (by rw [hrange]; exact hs'D)
    (fun l => MulAut.conjNormal s l) 1 (fun l => (MulAut.conjNormal_apply s l).symm)
    (fun l => by
      show s' * ((ι l : D) : E) * s'⁻¹ = ((ι (MulAut.conjNormal s l) : D) : E)
      rw [← hσι, hs'])
    (by rw [map_one]; exact hs2) (by rw [map_one]; exact hs'2)
  exact ⟨φ, fun l => hφ l⟩

end Generic

theorem map_commutator_vStabEam
 :
    (commutator (vStab cv0)).map vStabEam.toMonoidHom = commutator Eam := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ vStabEam.surjective]

theorem mul_self_ne_cE'_of_not_mem_commutator
    {y : ↥Eam} (_hy : y ∉ commutator ↥Eam) :
    y * y ≠ cE' := fun h =>
  native_inner_square_fusion.2.1 (vStabEam.symm y) (by
    rw [← map_mul, h, ← vStabEam_cV0, MulEquiv.symm_apply_apply])

theorem exists_mul_self_eq_one_not_mem_commutator :
    ∃ b : ↥Eam, b ∉ commutator ↥Eam ∧ b * b = 1 := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨u, -, b, -, hvu, -, -, hbu, -, -, -, -, -, -, -, -, -, -, hb, -⟩ :=
    CFSG.Monster.B.CTIB.native_H_outer_involution_classes hρ
  have hbE := (native_distance_three_label_is_outer_local_involution_final
    (mem_sphereDistThree.2 hvu)).2.1 b hbu
  refine ⟨vStabEam b, fun h => hbE ?_, ?_⟩
  · rw [← map_commutator_vStabEam, mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  · rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two hb, map_one]

theorem centralizer_commutator_Eam :
    centralizer ((commutator ↥Eam : Subgroup ↥Eam) : Set ↥Eam) = Subgroup.zpowers cE' := by
  obtain ⟨hidx, -, hZE, hZE', -⟩ := short_F4_derived_standard_perfect_cover
  have hZ : center Eam ≤ commutator Eam := by
    rw [hZE]
    exact zpowers_le.2 cE'_mem_commutator
  rw [centralizer_eq_map_center (centralizer_le_of_index_two hidx hZ), hZE']

theorem nonempty_mulEquiv_Eam_of_outer_involution
    (hO : (MulAut.conj : ↥(commutator ↥Eam) →* MulAut ↥(commutator ↥Eam)).range.index ≤ 2)
    {X : Type} [Group X] [Finite X] (L : Subgroup X) (hL2 : L.index = 2)
    (ι : ↥L ≃* ↥(commutator ↥Eam)) (hC : centralizer (L : Set X) ≤ L)
    {s : X} (hsL : s ∉ L) (hs2 : s * s = 1) :
    ∃ e : X ≃* ↥Eam, ∀ l : ↥L, (e l : ↥Eam) = (ι l : ↥Eam) := by
  have hCD : centralizer ((commutator Eam : Subgroup Eam) : Set Eam) ≤ commutator Eam := by
    rw [centralizer_commutator_Eam]
    exact zpowers_le.2 cE'_mem_commutator
  refine exists_mulEquiv_of_index_two_of_involution short_F4_derived_standard_perfect_cover.1 hO
    hCD (fun y hy hyc => ?_) hL2 ι hC hsL hs2
  rw [centralizer_commutator_Eam] at hyc
  rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers
    short_F4_central_extension_nonsplit.2.2.2.2.2.1 hyc with h | h
  · exact h
  · exact absurd h (mul_self_ne_cE'_of_not_mem_commutator hy)

end CFSG.EvenSmallLie.TwoE6
