module

public import CFSG.CharacterTheory.Wreathed.CyclicOddScalarQuotient
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.CharacterTheory.Semidihedral.OddLinearNormals

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

universe u v w

theorem perfect_homs_eq_of_central_displacement
    {P : Type u} {B : Type v} [Group P] [Group B] [Group.IsPerfect P]
    (alpha beta : P →* B)
    (hc : ∀ x : P, (beta x)⁻¹ * alpha x ∈ Subgroup.center B) : alpha = beta := by
  let delta : P →* Subgroup.center B :=
    { toFun := fun x => ⟨(beta x)⁻¹ * alpha x, hc x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (beta (x * y))⁻¹ * alpha (x * y) =
          ((beta x)⁻¹ * alpha x) * ((beta y)⁻¹ * alpha y)
        have hcomm := (Subgroup.mem_center_iff.mp (hc x)) (beta y)⁻¹
        calc
          (beta (x * y))⁻¹ * alpha (x * y) =
              (beta y)⁻¹ * ((beta x)⁻¹ * alpha x) * alpha y := by
            rw [map_mul, map_mul]
            group
          _ = ((beta x)⁻¹ * alpha x) * (beta y)⁻¹ * alpha y := by rw [hcomm]
          _ = ((beta x)⁻¹ * alpha x) * ((beta y)⁻¹ * alpha y) := mul_assoc _ _ _ }
  have hd := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative delta
  ext x
  have hx : (beta x)⁻¹ * alpha x = 1 :=
    congrArg Subtype.val (congrArg (fun f : P →* Subgroup.center B => f x) hd)
  exact (inv_mul_eq_one.mp hx).symm

theorem centralizes_perfect_image_of_quotient
    {P : Type u} {B : Type v} {H : Type w}
    [Group P] [Group B] [Group H] [Group.IsPerfect P]
    (i : P →* B) (phi : B →* H) (hk : phi.ker ≤ Subgroup.center B)
    (g : B) (hg : ∀ x : P, Commute (phi g) (phi (i x))) :
    ∀ x : P, Commute g (i x) := by
  let alpha := (MulAut.conj g).toMonoidHom.comp i
  have hc : ∀ x : P, (i x)⁻¹ * alpha x ∈ Subgroup.center B := by
    intro x
    apply hk
    rw [MonoidHom.mem_ker]
    change phi ((i x)⁻¹ * (g * i x * g⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, (hg x).eq]
    group
  have he := perfect_homs_eq_of_central_displacement alpha i hc
  intro x
  have hx : g * i x * g⁻¹ = i x := congrArg (fun f : P →* B => f x) he
  have hy := congrArg (fun y : B => y * g) hx
  change g * i x = i x * g
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hy

theorem center_comap_eq_of_perfect_image
    {P : Type u} {B : Type v} {H : Type w}
    [Group P] [Group B] [Group H] [Group.IsPerfect P]
    (i : P →* B) (phi : B →* H) (hphi : Function.Surjective phi)
    (hk : phi.ker ≤ Subgroup.center B) (Z : Subgroup B)
    (hZ : Z ≤ Subgroup.center B)
    (hscalar : ∀ g : B, (∀ x : P, Commute g (i x)) → g ∈ Z) :
    (Subgroup.center H).comap phi = Z := by
  apply le_antisymm
  · intro g hg
    apply hscalar
    exact centralizes_perfect_image_of_quotient i phi hk g
      (fun x => (Subgroup.mem_center_iff.mp hg (phi (i x))).symm)
  · intro g hg
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨b, rfl⟩ := hphi h
    exact (map_mul phi b g).symm.trans
      ((congrArg phi (Subgroup.mem_center_iff.mp (hZ hg) b)).trans (map_mul phi g b))

theorem center_eq_map_of_perfect_image
    {P : Type u} {B : Type v} {H : Type w}
    [Group P] [Group B] [Group H] [Group.IsPerfect P]
    (i : P →* B) (phi : B →* H) (hphi : Function.Surjective phi)
    (hk : phi.ker ≤ Subgroup.center B) (Z : Subgroup B)
    (hZ : Z ≤ Subgroup.center B)
    (hscalar : ∀ g : B, (∀ x : P, Commute g (i x)) → g ∈ Z) :
    Subgroup.center H = Z.map phi := by
  rw [← center_comap_eq_of_perfect_image i phi hphi hk Z hZ hscalar]
  exact (Subgroup.map_comap_eq_self_of_surjective hphi _).symm

@[expose] def fullCenterQuotientEquiv
    {B : Type u} {H : Type v} [Group B] [Group H]
    (phi : B →* H) (hphi : Function.Surjective phi) (Z : Subgroup B) [Z.Normal]
    (hc : (Subgroup.center H).comap phi = Z) :
    B ⧸ Z ≃* H ⧸ Subgroup.center H := by
  let psi := (QuotientGroup.mk' (Subgroup.center H)).comp phi
  refine QuotientGroup.liftEquiv Z (φ := psi)
    ((QuotientGroup.mk'_surjective (Subgroup.center H)).comp hphi) ?_
  rw [← hc]
  ext b
  change phi b ∈ Subgroup.center H ↔
    (QuotientGroup.mk' (Subgroup.center H)) (phi b) = 1
  exact (QuotientGroup.eq_one_iff (N := Subgroup.center H) (phi b)).symm

theorem fullCenterQuotientEquiv_mk
    {B : Type u} {H : Type v} [Group B] [Group H]
    (phi : B →* H) (hphi : Function.Surjective phi) (Z : Subgroup B) [Z.Normal]
    (hc : (Subgroup.center H).comap phi = Z) (b : B) :
    fullCenterQuotientEquiv phi hphi Z hc (QuotientGroup.mk' Z b) =
      QuotientGroup.mk' (Subgroup.center H) (phi b) := by
  unfold fullCenterQuotientEquiv
  exact QuotientGroup.liftEquiv_mk Z _ _ b


theorem centralizer_range_eq_bot_of_perfect_image
    {P : Type u} {B : Type v} {H : Type w}
    [Group P] [Group B] [Group H] [Group.IsPerfect P]
    (i : P →* B) (phi : B →* H) (hphi : Function.Surjective phi)
    (hk : phi.ker ≤ Subgroup.center B)
    (hscalar : ∀ g : B, (∀ x : P, Commute g (i x)) → g ∈ phi.ker) :
    Subgroup.centralizer ((phi.comp i).range : Set H) = ⊥ := by
  apply le_antisymm
  · intro h hh
    obtain ⟨g, rfl⟩ := hphi h
    have hg : ∀ x : P, Commute (phi g) (phi (i x)) := by
      intro x
      change phi g * phi (i x) = phi (i x) * phi g
      exact (Subgroup.mem_centralizer_iff.mp hh _
        (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).symm
    exact hscalar g (centralizes_perfect_image_of_quotient i phi hk g hg)
  · exact bot_le

theorem center_comap_eq_of_bijective
    {B : Type u} {H : Type v} [Group B] [Group H]
    (phi : B →* H) (hphi : Function.Bijective phi) :
    (Subgroup.center H).comap phi = Subgroup.center B := by
  ext g
  constructor
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply hphi.1
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hg (phi b)
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨b, rfl⟩ := hphi.2 h
    simpa only [map_mul] using congrArg phi (Subgroup.mem_center_iff.mp hg b)

section MatrixOvergroup

open Matrix
open CFSG.Semidihedral.OddLinearNormals

variable {F : Type u} {E : Type v} [Field F] [Finite F] [Field E]

@[expose] def scalarSubgroup (B : Subgroup (GeneralLinearGroup (Fin 2) E)) : Subgroup B :=
  (Subgroup.center (GeneralLinearGroup (Fin 2) E)).subgroupOf B

theorem scalarSubgroup_le_center (B : Subgroup (GeneralLinearGroup (Fin 2) E)) :
    scalarSubgroup B ≤ Subgroup.center B := by
  intro g hg
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hg b.val

@[expose] def specialInclusion (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    SpecialLinearGroup (Fin 2) F →* B :=
  (conjugatedEntrywiseSL i b).codRestrict B (by
    intro x
    apply hSB
    rw [conjugatedImageSL_eq_range]
    exact ⟨x, rfl⟩)

omit [Finite F] in
theorem specialInclusion_coe (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    (x : SpecialLinearGroup (Fin 2) F) :
    (specialInclusion i b B hSB x : GeneralLinearGroup (Fin 2) E) =
      conjugatedEntrywiseSL i b x := rfl

omit [Finite F] in
theorem centralizes_specialInclusion_scalar (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) (g : B)
    (hg : ∀ x : SpecialLinearGroup (Fin 2) F, Commute g (specialInclusion i b B hSB x)) :
    g ∈ scalarSubgroup B := by
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  exact scalar_of_centralizes_conjugatedEntrywiseSL i b g.val
    (fun x => (hg x).map B.subtype)

omit [Finite F] in
theorem matrix_overgroup_center_eq_scalars (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) : Subgroup.center B = scalarSubgroup B := by
  apply le_antisymm
  · intro g hg
    exact centralizes_specialInclusion_scalar i b B hSB g
      (fun x => (Subgroup.mem_center_iff.mp hg _).symm)
  · exact scalarSubgroup_le_center B

theorem matrix_overgroup_center_comap (hF : 4 ≤ Nat.card F) (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) {H : Type w} [Group H]
    (phi : B →* H) (hphi : Function.Surjective phi)
    (hk : phi.ker ≤ scalarSubgroup B) :
    (Subgroup.center H).comap phi = scalarSubgroup B := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  exact center_comap_eq_of_perfect_image (specialInclusion i b B hSB) phi hphi
    (hk.trans (scalarSubgroup_le_center B)) (scalarSubgroup B)
    (scalarSubgroup_le_center B) (centralizes_specialInclusion_scalar i b B hSB)

theorem matrix_overgroup_center_image (hF : 4 ≤ Nat.card F) (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) {H : Type w} [Group H]
    (phi : B →* H) (hphi : Function.Surjective phi)
    (hk : phi.ker ≤ scalarSubgroup B) :
    Subgroup.center H = (scalarSubgroup B).map phi := by
  rw [← matrix_overgroup_center_comap hF i b B hSB phi hphi hk]
  exact (Subgroup.map_comap_eq_self_of_surjective hphi _).symm

instance scalarSubgroup_isMulCommutative
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) : IsMulCommutative (scalarSubgroup B) := by
  apply isMulCommutative_iff.mpr
  intro x y
  exact Subtype.ext (Subgroup.mem_center_iff.mp
    (scalarSubgroup_le_center B x.property) y.val).symm

@[expose] def oddScalarSubgroup (B : Subgroup (GeneralLinearGroup (Fin 2) E)) : Subgroup B :=
  (CyclicOddScalarQuotient.oddElements (scalarSubgroup B)).map (scalarSubgroup B).subtype

theorem oddScalarSubgroup_le_scalars (B : Subgroup (GeneralLinearGroup (Fin 2) E)) :
    oddScalarSubgroup B ≤ scalarSubgroup B := Subgroup.map_subtype_le _

instance oddScalarSubgroup_normal (B : Subgroup (GeneralLinearGroup (Fin 2) E)) :
    (oddScalarSubgroup B).Normal := Subgroup.normal_of_le_center
  ((oddScalarSubgroup_le_scalars B).trans (scalarSubgroup_le_center B))

theorem oddScalarSubgroup_eq_bot_of_two_power
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) [Finite (scalarSubgroup B)]
    (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k) : oddScalarSubgroup B = ⊥ := by
  have hu := CyclicOddScalarQuotient.oddElements_odd_card (scalarSubgroup B)
  have hd := Subgroup.card_subgroup_dvd_card
    (CyclicOddScalarQuotient.oddElements (scalarSubgroup B))
  rw [hZ] at hd
  have hcard : Nat.card (CyclicOddScalarQuotient.oddElements (scalarSubgroup B)) = 1 :=
    ((Nat.coprime_two_right.mpr hu).pow_right k).eq_one_of_dvd hd
  rw [oddScalarSubgroup, (Subgroup.eq_bot_iff_card _).mpr hcard, Subgroup.map_bot]

theorem matrix_overgroup_oddScalar_center_image (hF : 4 ≤ Nat.card F) (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) :
    Subgroup.center (B ⧸ oddScalarSubgroup B) =
      (scalarSubgroup B).map (QuotientGroup.mk' (oddScalarSubgroup B)) :=
  matrix_overgroup_center_image hF i b B hSB _ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact oddScalarSubgroup_le_scalars B)

instance scalarSubgroup_normal (B : Subgroup (GeneralLinearGroup (Fin 2) E)) :
    (scalarSubgroup B).Normal := Subgroup.normal_of_le_center (scalarSubgroup_le_center B)

@[expose] def matrixOvergroupFullCenterQuotientEquiv (hF : 4 ≤ Nat.card F) (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) :
    B ⧸ scalarSubgroup B ≃*
      (B ⧸ oddScalarSubgroup B) ⧸ Subgroup.center (B ⧸ oddScalarSubgroup B) := by
  exact fullCenterQuotientEquiv (QuotientGroup.mk' (oddScalarSubgroup B))
    (QuotientGroup.mk'_surjective _) (scalarSubgroup B)
    (matrix_overgroup_center_comap hF i b B hSB _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact oddScalarSubgroup_le_scalars B))


theorem matrixOvergroupFullCenterQuotientEquiv_mk (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    (g : B) :
    matrixOvergroupFullCenterQuotientEquiv hF i b B hSB
      (QuotientGroup.mk' (scalarSubgroup B) g) =
        QuotientGroup.mk' (Subgroup.center (B ⧸ oddScalarSubgroup B))
          (QuotientGroup.mk' (oddScalarSubgroup B) g) := by
  unfold matrixOvergroupFullCenterQuotientEquiv
  exact fullCenterQuotientEquiv_mk _ _ _ _ g

omit [Finite F] in
theorem matrix_overgroup_center_comap_of_ker_bot (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) {H : Type w} [Group H]
    (phi : B →* H) (hphi : Function.Surjective phi) (hk : phi.ker = ⊥) :
    (Subgroup.center H).comap phi = scalarSubgroup B := by
  rw [center_comap_eq_of_bijective phi ⟨(MonoidHom.ker_eq_bot_iff phi).mp hk, hphi⟩]
  exact matrix_overgroup_center_eq_scalars i b B hSB

omit [Finite F] in
theorem matrix_overgroup_oddScalar_center_comap_of_two_power (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) [Finite (scalarSubgroup B)]
    (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k) :
    (Subgroup.center (B ⧸ oddScalarSubgroup B)).comap
      (QuotientGroup.mk' (oddScalarSubgroup B)) = scalarSubgroup B := by
  exact matrix_overgroup_center_comap_of_ker_bot i b B hSB _
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk', oddScalarSubgroup_eq_bot_of_two_power B k hZ])

omit [Finite F] in
theorem matrix_overgroup_oddScalar_center_image_of_two_power (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) [Finite (scalarSubgroup B)]
    (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k) :
    Subgroup.center (B ⧸ oddScalarSubgroup B) =
      (scalarSubgroup B).map (QuotientGroup.mk' (oddScalarSubgroup B)) := by
  rw [← matrix_overgroup_oddScalar_center_comap_of_two_power i b B hSB k hZ]
  exact (Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) _).symm

theorem matrix_overgroup_projective_special_centralizer (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    Subgroup.centralizer
      (((QuotientGroup.mk' (scalarSubgroup B)).comp
        (specialInclusion i b B hSB)).range : Set (B ⧸ scalarSubgroup B)) = ⊥ := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  apply centralizer_range_eq_bot_of_perfect_image (specialInclusion i b B hSB)
    (QuotientGroup.mk' (scalarSubgroup B)) (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact scalarSubgroup_le_center B
  · intro g hg
    rw [QuotientGroup.ker_mk']
    exact centralizes_specialInclusion_scalar i b B hSB g hg


@[expose] def matrixOvergroupFullCenterQuotientEquivOfTwoPower
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    [Finite (scalarSubgroup B)] (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k) :
    B ⧸ scalarSubgroup B ≃*
      (B ⧸ oddScalarSubgroup B) ⧸ Subgroup.center (B ⧸ oddScalarSubgroup B) :=
  fullCenterQuotientEquiv (QuotientGroup.mk' (oddScalarSubgroup B))
    (QuotientGroup.mk'_surjective _) (scalarSubgroup B)
    (matrix_overgroup_oddScalar_center_comap_of_two_power i b B hSB k hZ)

omit [Finite F] in
theorem matrixOvergroupFullCenterQuotientEquivOfTwoPower_mk
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    [Finite (scalarSubgroup B)] (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k)
    (g : B) :
    matrixOvergroupFullCenterQuotientEquivOfTwoPower i b B hSB k hZ
      (QuotientGroup.mk' (scalarSubgroup B) g) =
        QuotientGroup.mk' (Subgroup.center (B ⧸ oddScalarSubgroup B))
          (QuotientGroup.mk' (oddScalarSubgroup B) g) := by
  unfold matrixOvergroupFullCenterQuotientEquivOfTwoPower
  exact fullCenterQuotientEquiv_mk _ _ _ _ g

end MatrixOvergroup

end CFSG.Wreathed.DegreeThreeModelFullCenter
