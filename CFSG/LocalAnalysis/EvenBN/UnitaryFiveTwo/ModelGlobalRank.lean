module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut
public import CFSG.RankThree.PartOne.U5K.Hyp.Coord
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem mat_ρ_apply (g : SU52) (i j : Fin 5) :
    CFSG.RankThree.PartOne.U5K.Hyp.mat (ρ g) (yIdx i) (yIdx j) = mat g i j := by
  change (ρGL (g : GL (Fin 5) F4) : Matrix (HypIndex 2 1) (HypIndex 2 1) F4) (yIdx i) (yIdx j) =
    _
  rw [coe_ρGL, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem mem_Ssub_iff_ρ {g : SU52} : g ∈ Ssub ↔ ρ g ∈ hypUnitriangular hF4 2 1 := by
  rw [Ssub_eq_LTsub, LTsub, Subgroup.mem_map_equiv, MulEquiv.symm_symm]

theorem comap_Vsub_le_Fsub :
    (CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4).comap ρ.toMonoidHom ≤ Fsub := by
  intro g hg
  obtain ⟨hU, Y, hY⟩ := hg
  have e : ∀ i j : Fin 5, mat g i j =
      oddUni hF4 (0 : Fin 2 → F4) Y (yIdx i) (yIdx j) := fun i j => by
    rw [← mat_ρ_apply]
    exact congrFun (congrFun hY _) _
  refine mem_Fsub.2 ⟨mem_Ssub_iff_ρ.2 hU, ?_, ?_, ?_⟩
  · rw [e]
    change oddUni hF4 (0 : Fin 2 → F4) Y (.inr (.inl 0)) (.inr (.inr 1)) = 0
    simp [oddUni]
  · rw [e]
    change oddUni hF4 (0 : Fin 2 → F4) Y (.inr (.inr 1)) (.inr (.inr 0)) = 0
    simp [oddUni, blk3]
  · rw [e]
    change oddUni hF4 (0 : Fin 2 → F4) Y (.inr (.inl 0)) (.inr (.inr 0)) = 0
    simp [oddUni]

theorem Fsub_eq_comap_Vsub :
    Fsub = (CFSG.RankThree.PartOne.U5K.Hyp.Vsub hF4).comap ρ.toMonoidHom := by
  refine (Subgroup.eq_of_le_of_card_ge comap_Vsub_le_Fsub ?_).symm
  rw [card_Fsub, comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ρ.symm.injective,
    CFSG.RankThree.PartOne.U5K.Hyp.card_Vsub]
  norm_num

theorem Fsub_comm {x y : SU52} (hx : x ∈ Fsub) (hy : y ∈ Fsub) : x * y = y * x := by
  rw [Fsub_eq_comap_Vsub] at hx hy
  exact ρ.injective (by
    rw [map_mul, map_mul]
    exact CFSG.RankThree.PartOne.U5K.Hyp.Vsub_comm hx hy)

theorem Fsub_sq {x : SU52} (hx : x ∈ Fsub) : x * x = 1 := by
  rw [Fsub_eq_comap_Vsub] at hx
  exact ρ.injective (by
    rw [map_mul, map_one]
    exact CFSG.RankThree.PartOne.U5K.Hyp.Vsub_sq hx)

theorem elemAb_le_Fsub_or_card_le {E : Subgroup SU52} (hES : E ≤ Ssub)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    E ≤ Fsub ∨ Nat.card E ≤ 8 := by
  have hU : E.map ρ.toMonoidHom ≤ hypUnitriangular hF4 2 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_Ssub_iff_ρ.1 (hES hx)
  have hc' : ∀ x ∈ E.map ρ.toMonoidHom, ∀ y ∈ E.map ρ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hs' : ∀ x ∈ E.map ρ.toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change ρ x * ρ x = 1
    rw [← map_mul, hs x hx, map_one]
  rcases CFSG.RankThree.PartOne.U5K.Hyp.elemAb_le_Vsub_or_card_le hU hc' hs' with h | h
  · left
    intro x hx
    rw [Fsub_eq_comap_Vsub]
    exact h ⟨x, hx, rfl⟩
  · right
    rw [Subgroup.card_map_of_injective ρ.injective] at h
    simpa using h

theorem card_le_of_elemAb_Ssub {E : Subgroup SU52} (hES : E ≤ Ssub)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  rcases elemAb_le_Fsub_or_card_le hES hc hs with h | h
  · exact (Subgroup.card_le_of_le h).trans card_Fsub.le
  · omega

theorem eq_Fsub_of_elemAb_Ssub {E : Subgroup SU52} (hES : E ≤ Ssub)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1)
    (hcard : 16 ≤ Nat.card E) : E = Fsub := by
  rcases elemAb_le_Fsub_or_card_le hES hc hs with h | h
  · exact Subgroup.eq_of_le_of_card_ge h (by rw [card_Fsub]; exact hcard)
  · omega

theorem exists_conj_le_Ssub {E : Subgroup SU52} (hE : IsPGroup 2 E) :
    ∃ g : SU52, E.map (MulAut.conj g).toMonoidHom ≤ Ssub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_Ssub
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SU52 P P₀
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hP₀, ← hg, Sylow.coe_subgroup_smul]
  exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hP hx, rfl⟩

theorem isPGroup_two_of_sq {X : Type*} [Group X] {E : Subgroup X} (hs : ∀ x ∈ E, x * x = 1) :
    IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by rw [pow_one, coe_pow, sq, hs x x.2, coe_one])⟩

theorem card_le_of_elemAb_SU52 {E : Subgroup SU52} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hs : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 16 ∧ (16 ≤ Nat.card E → ∃ g : SU52, E.map (MulAut.conj g).toMonoidHom = Fsub) := by
  obtain ⟨g, hg⟩ := exists_conj_le_Ssub (isPGroup_two_of_sq hs)
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc' : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change MulAut.conj g x * MulAut.conj g y = MulAut.conj g y * MulAut.conj g x
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have hs' : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change MulAut.conj g x * MulAut.conj g x = 1
    rw [← map_mul, hs x hx, map_one]
  refine ⟨hcard ▸ card_le_of_elemAb_Ssub hg hc' hs', fun h16 => ⟨g, ?_⟩⟩
  exact eq_Fsub_of_elemAb_Ssub hg hc' hs' (by rw [hcard]; exact h16)

theorem x₄SU_zero_one_mem_Fsub (h : (0 : F4) * bar 0 = 1 + bar 1) : x₄SU 0 1 h ∈ Fsub :=
  mem_sup_right ⟨0, 1, rfl, rfl⟩

theorem x₃SU_mem_Fsub (a : F4) : x₃SU a ∈ Fsub := mem_sup_left (mem_sup_right (x₃SU_mem a))

theorem zero_one_rel : (0 : F4) * bar 0 = 1 + bar 1 := by
  rw [bar_apply, bar_apply]
  decide

theorem F4_ω_add_one_mul {m : F4} (h : (F4.ω + 1) * m = F4.ω * m) : m = 0 := by
  linear_combination h

theorem fieldFactor_eq_one_of_fix_Fsub {α : MulAut SU52} (hα : ∀ y ∈ Fsub, α y = y) :
    fieldFactor α = 1 := by
  by_contra hne
  obtain ⟨s, rfl⟩ := exists_eq_conj_mul_fld hne
  have key : ∀ y ∈ Fsub, mat s * mat (fld y) = mat y * mat s := fun y hy => by
    have h1 := hα y hy
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [← mat_mul, ← mat_mul]
    congr 1
    calc s * fld y = s * fld y * s⁻¹ * s := by group
      _ = y * s := by rw [h1]
  have hb := key _ (x₄SU_zero_one_mem_Fsub zero_one_rel)
  have hc := key _ (x₃SU_mem_Fsub 1)
  have hd := key _ (x₃SU_mem_Fsub F4.ω)
  rw [fld_x₄SU, mat_x₄SU, mat_x₄SU] at hb
  rw [fld_x₃SU, mat_x₃SU, mat_x₃SU] at hc hd
  have hc' := congrFun (congrFun hc 3) 0
  have hd' := congrFun (congrFun hd 3) 0
  simp [x₃Mat, bar_apply, Matrix.mul_apply, Fin.sum_univ_five] at hc' hd'
  have h00 : mat s 0 0 = 0 := by
    have hω : bar F4.ω = F4.ω + 1 := bar_ω
    rw [bar_apply] at hω
    rw [hω] at hd'
    apply F4_ω_add_one_mul
    linear_combination hd' - (F4.ω + 1) * hc'
  have hrow : ∀ j : Fin 5, mat s 0 j = 0 := by
    intro j
    have h1 := congrFun (congrFun hb 4) j
    fin_cases j
    · exact h00
    all_goals
      simp [x₄Mat, bar_apply, Matrix.mul_apply, Fin.sum_univ_five] at h1
      simpa using h1
  have hdet := (mem_SU52.1 s.2).2
  rw [Matrix.det_eq_zero_of_row_eq_zero 0 hrow] at hdet
  exact zero_ne_one hdet

theorem mul_conj_mul_inv (α : MulAut SU52) (s : SU52) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem card_le_of_elemAb_mulAut {E : Subgroup (MulAut SU52)}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  set E₁ : Subgroup SU52 := E.comap MulAut.conj with hE₁
  have hE₁c : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy =>
    conj_injective (by rw [map_mul, map_mul]; exact hc _ hx _ hy)
  have hE₁s : ∀ x ∈ E₁, x * x = 1 := fun x hx =>
    conj_injective (by rw [map_mul, map_one]; exact hs _ hx)
  obtain ⟨h16, hF⟩ := card_le_of_elemAb_SU52 hE₁c hE₁s
  have hmap : E₁.map MulAut.conj = E ⊓ fieldFactor.ker := by
    ext α
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, fieldFactor_conj s⟩
    · rintro ⟨hαE, hα⟩
      obtain ⟨s, rfl⟩ := (fieldFactor_eq_one_iff α).1 hα
      exact ⟨s, hαE, rfl⟩
  have hcard₁ : Nat.card (E ⊓ fieldFactor.ker : Subgroup (MulAut SU52)) = Nat.card E₁ := by
    rw [← hmap, Subgroup.card_map_of_injective conj_injective]
  set f' : E →* (F4 ≃+* F4) := fieldFactor.comp E.subtype with hf'
  have hE : Nat.card E ≤ 2 * Nat.card E₁ := by
    have h := Subgroup.card_ker_mul_card_range f'
    have hk : Nat.card f'.ker = Nat.card E₁ := by
      rw [← hcard₁]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hr : Nat.card f'.range ≤ 2 :=
      (Subgroup.card_le_card_group _).trans card_ringEquiv_F4.le
    rw [hk] at h
    calc Nat.card E = Nat.card E₁ * Nat.card f'.range := h.symm
      _ ≤ Nat.card E₁ * 2 := Nat.mul_le_mul_left _ hr
      _ = 2 * Nat.card E₁ := mul_comm _ _
  by_cases h8 : Nat.card E₁ ≤ 8
  · omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_two_of_sq hE₁s).exists_card_eq
  have hk4 : k = 4 := by
    rw [hk] at h16 h8
    have h1 : k ≤ 4 := by
      by_contra h
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 4 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  obtain ⟨g, hg⟩ := hF (by rw [hk, hk4]; norm_num)
  have hker : ∀ α ∈ E, fieldFactor α = 1 := by
    intro α hαE
    have hfix : ∀ x ∈ E₁, α x = x := by
      intro x hx
      apply conj_injective
      rw [← mul_conj_mul_inv, hc α hαE _ hx, mul_inv_cancel_right]
    have hβ : ∀ y ∈ Fsub, (MulAut.conj g * α * (MulAut.conj g)⁻¹) y = y := by
      intro y hy
      rw [← hg] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change (MulAut.conj g * α * (MulAut.conj g)⁻¹) (MulAut.conj g x) = MulAut.conj g x
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix x hx]
    have h1 := fieldFactor_eq_one_of_fix_Fsub hβ
    rwa [map_mul, map_mul, map_inv, fieldFactor_conj, one_mul, inv_one, mul_one] at h1
  have hEle : E ≤ fieldFactor.ker := fun α hα => hker α hα
  rw [inf_eq_left.2 hEle] at hcard₁
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
