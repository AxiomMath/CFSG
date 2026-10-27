module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardColumnCoordinates

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LieType.Chevalley (SL2)
open CFSG.ComponentClassification.GS79bSec5

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

variable {G : Type*} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem ker_le_ker_proj_of_le_center (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) :
    ρ.ker ≤ (proj 3 K).ker := by
  rw [ker_proj, scalars_eq_center]
  exact hker

private theorem injective_comp_of_ker_le {H P M : Type*} [Group H] [Group P] [Group M]
    {ρ : H →* G} {π : H →* P} (hker : ρ.ker ≤ π.ker) {f : M →* H}
    (hf : Function.Injective (π.comp f)) : Function.Injective (ρ.comp f) := by
  intro a b hab
  apply hf
  have hab' : ρ (f a) = ρ (f b) := hab
  have hmem : f a * (f b)⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  have hπ : π (f a) * (π (f b))⁻¹ = 1 := by
    have h := hker hmem
    rwa [MonoidHom.mem_ker, map_mul, map_inv] at h
  exact mul_inv_eq_one.mp hπ

private theorem conjugate_mem_map_of_mem_normalizer {H P : Type*} [Group H] [Group P]
    {ρ : H →* G} {π : H →* P} (hker : ρ.ker ≤ π.ker) {R : Subgroup H} {y : H}
    (hy : ρ y ∈ normalizer ((R.map ρ : Subgroup G) : Set G)) {u : H} (hu : u ∈ R) :
    π (y * u * y⁻¹) ∈ R.map π := by
  have hρ : ρ (y * u * y⁻¹) ∈ R.map ρ := by
    have h := ((Subgroup.mem_normalizer_iff.mp hy) (ρ u)).mp (Subgroup.mem_map_of_mem ρ hu)
    simpa only [map_mul, map_inv] using h
  obtain ⟨u', hu', hueq⟩ := Subgroup.mem_map.mp hρ
  have hmem : (y * u * y⁻¹) * u'⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hueq, mul_inv_cancel]
  have hπ : (y * u * y⁻¹) * u'⁻¹ ∈ π.ker := hker hmem
  have heq : π (y * u * y⁻¹) = π u' := by
    have h := hπ
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  rw [heq]
  exact Subgroup.mem_map_of_mem π hu'

private theorem mem_normalizer_map_of_ker_le {H P : Type*} [Group H] [Group P]
    {ρ : H →* G} {π : H →* P} (hker : ρ.ker ≤ π.ker) {R : Subgroup H} {y : H}
    (hy : ρ y ∈ normalizer ((R.map ρ : Subgroup G) : Set G)) :
    π y ∈ normalizer ((R.map π : Subgroup P) : Set P) := by
  have hyinv : ρ y⁻¹ ∈ normalizer ((R.map ρ : Subgroup G) : Set G) := by
    rw [map_inv]
    exact (Subgroup.normalizer (R.map ρ : Set G)).inv_mem hy
  refine mem_normalizer_of_conj_mem ?_ ?_
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_inv, ← map_mul, ← map_mul]
    exact conjugate_mem_map_of_mem_normalizer hker hy hu
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_inv, ← map_mul, ← map_mul]
    simpa only [inv_inv] using conjugate_mem_map_of_mem_normalizer hker hyinv hu

omit [Finite K] [CharP K 2] in
private theorem radSLHom_mem_normalizer_unip (i : Fin 2) (w : Multiplicative (Fin 2 → K)) :
    radSLHom K i w ∈ normalizer ((![unipOne K, unipTwo K] i) :
      Set (SpecialLinearGroup (Fin 3) K)) :=
  Subgroup.le_normalizer (by rw [← range_radSLHom]; exact ⟨w, rfl⟩)

omit [Finite K] [CharP K 2] in
private theorem torSL_mem_normalizer_unip (i : Fin 2) (l : Kˣ) :
    torSL K i l ∈ normalizer ((![unipOne K, unipTwo K] i) :
      Set (SpecialLinearGroup (Fin 3) K)) := by
  refine mem_normalizer_of_conj_mem ?_ ?_
  · intro z hz
    rw [← range_radSLHom] at hz ⊢
    obtain ⟨v, rfl⟩ := hz
    exact ⟨_, (torSL_conj_radSLHom i l v).symm⟩
  · intro z hz
    rw [← range_radSLHom] at hz ⊢
    obtain ⟨v, rfl⟩ := hz
    have h := (torSL_conj_radSLHom i l⁻¹ v).symm
    have hgoal : ((torSL K i) l)⁻¹ * (radSLHom K i) v * (torSL K i) l =
        (torSL K i) l⁻¹ * (radSLHom K i) v * ((torSL K i) l⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
    rw [hgoal, ← h]
    exact ⟨_, rfl⟩

omit [Finite K] [CharP K 2] in
private theorem levi_mem_normalizer_unip (i : Fin 2) (B : SL2 K) :
    levi K i B ∈ normalizer ((![unipOne K, unipTwo K] i) :
      Set (SpecialLinearGroup (Fin 3) K)) := by
  refine mem_normalizer_of_conj_mem ?_ ?_
  · intro z hz
    rw [← range_radSLHom] at hz ⊢
    obtain ⟨v, rfl⟩ := hz
    exact ⟨_, (levi_conj_radSLHom i B v).symm⟩
  · intro z hz
    rw [← range_radSLHom] at hz ⊢
    obtain ⟨v, rfl⟩ := hz
    have h := (levi_conj_radSLHom i B⁻¹ v).symm
    have hgoal : ((levi K i) B)⁻¹ * (radSLHom K i) v * (levi K i) B =
        (levi K i) B⁻¹ * (radSLHom K i) v * ((levi K i) B⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
    rw [hgoal, ← h]
    exact ⟨_, rfl⟩

omit [Finite K] [CharP K 2] in
private theorem mul_mem_normalizer_cover (ρ : SpecialLinearGroup (Fin 3) K →* G) (i : Fin 2)
    (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K) :
    (ρ.comp (radSLHom K i)) w * (ρ.comp (torSL K i)) l * (ρ.comp (levi K i)) B ∈
      normalizer (((![unipOne K, unipTwo K] i).map ρ : Subgroup G) : Set G) :=
  mul_mem
    (mul_mem
      (Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ
        (radSLHom_mem_normalizer_unip i w)))
      (Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ
        (torSL_mem_normalizer_unip i l))))
    (Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem ρ
      (levi_mem_normalizer_unip i B)))

private theorem exists_eq_radSLHom_mul_of_mem_normalizer (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2)
    {y : SpecialLinearGroup (Fin 3) K}
    (hy : ρ y ∈ normalizer (((![unipOne K, unipTwo K] i).map ρ : Subgroup G) : Set G)) :
    ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K),
      y = radSLHom K i w * torSL K i l * levi K i B := by
  have hproj := mem_normalizer_map_of_ker_le (ker_le_ker_proj_of_le_center ρ hker) hy
  fin_cases i
  · obtain ⟨h10, h20⟩ := col_zero_of_mem_normalizer three_ne_zero_of_charTwo
      (by simpa [projRad_zero] using hproj)
    obtain ⟨l, a, c, B, hy_eq⟩ := exists_eq_torSL_zero_mul h10 h20
    refine ⟨Multiplicative.ofAdd ![(l : K) ^ 3 * c, -((l : K) ^ 3 * a)], l, B, ?_⟩
    have hdecomp : y = radSLHom K 0
        (Multiplicative.ofAdd ![(l : K) ^ 3 * c, -((l : K) ^ 3 * a)]) *
        torSL K 0 l * levi K 0 B := by
      rw [hy_eq, torSL_zero_mul_unipU, levi_zero]
      simp [radSLHom, rowSLHom]
    simpa only [Fin.zero_eta] using hdecomp
  · obtain ⟨h20, h21⟩ := row_two_of_mem_normalizer three_ne_zero_of_charTwo
      (by simpa [projRad_one] using hproj)
    obtain ⟨l, b, c, B, hy_eq⟩ := exists_eq_torSL_one_mul h20 h21
    refine ⟨Multiplicative.ofAdd ![(l : K) ^ 3 * c, (l : K) ^ 3 * b], l, B, ?_⟩
    have hdecomp : y = radSLHom K 1
        (Multiplicative.ofAdd ![(l : K) ^ 3 * c, (l : K) ^ 3 * b]) *
        torSL K 1 l * levi K 1 B := by
      rw [hy_eq, torSL_one_mul_unipU, levi_one]
      rfl
    simpa only [Fin.mk_one] using hdecomp

omit [Finite K] [CharP K 2] in
private theorem exists_eq_radSLHom_of_mem_map (ρ : SpecialLinearGroup (Fin 3) K →* G) (i : Fin 2)
    {v : G} (hv : v ∈ (![unipOne K, unipTwo K] i).map ρ) :
    ∃ r, (ρ.comp (radSLHom K i)) r = v := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  rw [← range_radSLHom] at hu
  obtain ⟨r, rfl⟩ := hu
  exact ⟨r, rfl⟩

omit [Finite K] [CharP K 2] in
private theorem radCoord_mem_projRad (i : Fin 2) (r : Multiplicative (Fin 2 → K)) :
    radCoord K i r ∈ projRad K i := by
  rw [← range_radCoord]
  exact ⟨r, rfl⟩

omit [Finite K] [CharP K 2] in
private theorem radCoord_ne_one (i : Fin 2) {r : Multiplicative (Fin 2 → K)} (hr : r ≠ 1) :
    radCoord K i r ≠ 1 :=
  fun h => hr (radCoord_injective i (by rw [h, map_one]))

omit [Finite K] [CharP K 2] in
private theorem coord_eq_of_leviProj_conj (i : Fin 2) (B : SL2 K)
    {r s : Multiplicative (Fin 2 → K)}
    (hB : leviProj K i B * radCoord K i r * (leviProj K i B)⁻¹ = radCoord K i s) :
    (B : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd r = Multiplicative.toAdd s := by
  have h1 : radCoord K i (Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd r)) = radCoord K i s := by
    rw [← leviProj_conj_radCoord i B r, hB]
  simpa using congrArg Multiplicative.toAdd (radCoord_injective i h1)

omit [Finite K] [CharP K 2] in
private theorem levi_map_conj_eq_of_coord_eq (ρ : SpecialLinearGroup (Fin 3) K →* G) (i : Fin 2)
    (B : SL2 K) {r s : Multiplicative (Fin 2 → K)}
    (h : (B : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd r =
      Multiplicative.toAdd s) :
    (ρ.comp (levi K i)) B * (ρ.comp (radSLHom K i)) r * ((ρ.comp (levi K i)) B)⁻¹ =
      (ρ.comp (radSLHom K i)) s := by
  have hw : Multiplicative.ofAdd ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Multiplicative.toAdd r) = s := by
    simpa using congrArg Multiplicative.ofAdd h
  have h' := congrArg ρ (levi_conj_radSLHom i B r)
  rw [hw] at h'
  simpa only [MonoidHom.comp_apply, map_mul, map_inv] using h'

omit [Finite K] [CharP K 2] in
theorem injective_comp_radSLHom_of_ker_le_center (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2) :
    Function.Injective (ρ.comp (radSLHom K i)) :=
  injective_comp_of_ker_le (ker_le_ker_proj_of_le_center ρ hker)
    (by rw [proj_comp_radSLHom]; exact radCoord_injective i)

omit [Finite K] [CharP K 2] in
theorem injective_comp_levi_of_ker_le_center (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2) :
    Function.Injective (ρ.comp (levi K i)) :=
  injective_comp_of_ker_le (ker_le_ker_proj_of_le_center ρ hker)
    (by
      show Function.Injective ((proj 3 K).comp (levi K i))
      exact leviProj_injective i)

theorem mem_normalizer_map_unip_iff (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2)
    (y : SpecialLinearGroup (Fin 3) K) :
    ρ y ∈ normalizer (((![unipOne K, unipTwo K] i).map ρ : Subgroup G) : Set G) ↔
      ∃ (w : Multiplicative (Fin 2 → K)) (l : Kˣ) (B : SL2 K),
        ρ y = ρ (radSLHom K i w) * ρ (torSL K i l) * ρ (levi K i B) := by
  constructor
  · intro hy
    obtain ⟨w, l, B, hy_eq⟩ := exists_eq_radSLHom_mul_of_mem_normalizer ρ hker i hy
    refine ⟨w, l, B, ?_⟩
    have hmap := congrArg ρ hy_eq
    simpa only [map_mul, mul_assoc] using hmap
  · rintro ⟨w, l, B, hxeq⟩
    rw [hxeq]
    simpa only [MonoidHom.comp_apply] using mul_mem_normalizer_cover ρ i w l B

omit [Finite K] [CharP K 2] in
theorem exists_levi_conj_eq_of_mem_map_unip (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (i : Fin 2) {v w : G}
    (hv : v ∈ (![unipOne K, unipTwo K] i).map ρ)
    (hw : w ∈ (![unipOne K, unipTwo K] i).map ρ) (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ B : SL2 K, ρ (levi K i B) * v * (ρ (levi K i B))⁻¹ = w := by
  obtain ⟨r, rfl⟩ := exists_eq_radSLHom_of_mem_map ρ i hv
  obtain ⟨s, rfl⟩ := exists_eq_radSLHom_of_mem_map ρ i hw
  have hr1 : r ≠ 1 := fun h => hv1 (by rw [h, map_one])
  have hs1 : s ≠ 1 := fun h => hw1 (by rw [h, map_one])
  have key : ∃ B : SL2 K,
      leviProj K i B * radCoord K i r * (leviProj K i B)⁻¹ = radCoord K i s := by
    fin_cases i
    · exact projRad_zero_transitive (radCoord_mem_projRad 0 r) (radCoord_mem_projRad 0 s)
        (radCoord_ne_one 0 hr1) (radCoord_ne_one 0 hs1)
    · exact projRad_one_transitive (radCoord_mem_projRad 1 r) (radCoord_mem_projRad 1 s)
        (radCoord_ne_one 1 hr1) (radCoord_ne_one 1 hs1)
  obtain ⟨B, hB⟩ := key
  exact ⟨B, levi_map_conj_eq_of_coord_eq ρ i B (coord_eq_of_leviProj_conj i B hB)⟩

@[expose] noncomputable def LeviData.ofCover {A : Subgroup G}
    (ρ : SpecialLinearGroup (Fin 3) K →* G) (hρ : ρ.range = A)
    (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2) :
    LeviData A ((![unipOne K, unipTwo K] i).map ρ) K where
  ι := ρ.comp (radSLHom K i)
  ι_injective := injective_comp_radSLHom_of_ker_le_center ρ hker i
  range_ι := by rw [MonoidHom.range_comp, range_radSLHom]
  ι_mem := fun w => by
    show ρ (radSLHom K i w) ∈ A
    rw [← hρ]
    exact ⟨radSLHom K i w, rfl⟩
  lev := ρ.comp (levi K i)
  lev_injective := injective_comp_levi_of_ker_le_center ρ hker i
  lev_mem := fun B => by
    show ρ (levi K i B) ∈ A
    rw [← hρ]
    exact ⟨levi K i B, rfl⟩
  lev_conj := fun B w => by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, levi_conj_radSLHom]
  tor := ρ.comp (torSL K i)
  tor_mem := fun l => by
    show ρ (torSL K i l) ∈ A
    rw [← hρ]
    exact ⟨torSL K i l, rfl⟩
  tor_conj := fun l w => by
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, torSL_conj_radSLHom]
  tor_comm := fun l B => by
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, torSL_mul_levi]
  mem_normalizer_iff := fun x hx => by
    have hxr : x ∈ ρ.range := by rwa [hρ]
    obtain ⟨y, rfl⟩ := hxr
    exact mem_normalizer_map_unip_iff ρ hker i y
  transitive := fun v hv w hw hv1 hw1 =>
    exists_levi_conj_eq_of_mem_map_unip ρ i hv hw hv1 hw1

theorem LeviData.ofCover_lev {A : Subgroup G} (ρ : SpecialLinearGroup (Fin 3) K →* G)
    (hρ : ρ.range = A) (hker : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)) (i : Fin 2) :
    (LeviData.ofCover ρ hρ hker i).lev = ρ.comp (levi K i) :=
  rfl

end CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

variable {G : Type*} [Group G]

theorem ker_subtype_comp_le_center {F : Type} [Field F] {A : Subgroup G}
    (e : (A ⧸ center A) ≃* projectiveSL 3 F) (φ : SpecialLinearGroup (Fin 3) F →* A)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (center A))).comp φ = proj 3 F) :
    (A.subtype.comp φ).ker ≤ center (SpecialLinearGroup (Fin 3) F) := by
  intro x hx
  have hφx : φ x = 1 := by
    apply Subgroup.subtype_injective A
    simpa using (MonoidHom.mem_ker.mp hx : A.subtype (φ x) = 1)
  have hproj : proj 3 F x = 1 := by
    have h := DFunLike.congr_fun hφproj x
    simp only [MonoidHom.comp_apply] at h
    rw [hφx, map_one] at h
    simpa using h.symm
  rw [← scalars_eq_center, ← ker_proj]
  exact MonoidHom.mem_ker.mpr hproj

end CFSG.ComponentClassification.GS79bSec5

end
