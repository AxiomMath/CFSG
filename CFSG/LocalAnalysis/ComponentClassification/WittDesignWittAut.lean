module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittUnique
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2028
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2195
public import Certificates.Certificate2031
public import Certificates.Certificate2033
public import Certificates.Certificate2034
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAutInputs
public import Certificates.Certificate2039
public import Certificates.Certificate2030
public import Certificates.Certificate2040
public import Certificates.Certificate2035
public import Certificates.Certificate3029

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Monster.B.Classical.Plane
open scoped Pointwise

theorem phi_facts : (∀ y, psiFun y ≠ 0 ∧ phiFun (psiFun y) = y) ∧
    (∀ x, x ≠ 0 → psiFun (phiFun x) = x) ∧ (∀ x, sigmaFun (sigmaFun x) = x) ∧
    hexadList.all (fun B => !(decide ((0 : Fin 22) ∈ B)) ||
      ((B.erase 0).image phiFun ∈ Finset.univ.image projLine)) = true ∧
    hexadList.all (fun B => decide ((0 : Fin 22) ∈ B) ||
      hyperClass0.contains (B.image phiFun)) = true ∧
    (∀ a : Fin 21, hexadList.any fun B =>
      decide ((0 : Fin 22) ∈ B) && ((B.erase 0).image phiFun == projLine a)) ∧
    hyperClass0.all (fun X => hexadList.any fun B =>
      !(decide ((0 : Fin 22) ∈ B)) && (B.image phiFun == X)) = true ∧
    hexadList.all (fun B => hexadMasks.contains (mask (B.image sigmaFun))) = true :=
  Certificates.certificate2039.1

theorem count_sigma : m22Count (fun g => ∀ x, g x = sigmaFun x) = 0 :=
  Certificates.certificate2039.2.1

theorem class_images : (hyperClass0.toFinset.image fun X => X.image (ofTable21 deltaTab)) =
      hyperClass1.toFinset ∧
    (hyperClass1.toFinset.image fun X => X.image (ofTable21 deltaTab)) = hyperClass2.toFinset ∧
    hyperClass0.toFinset ≠ hyperClass1.toFinset ∧ hyperClass0.toFinset ≠ hyperClass2.toFinset ∧
    hyperClass1.toFinset ≠ hyperClass2.toFinset :=
  Certificates.certificate2039.2.2.1

theorem psiFun_ne (y : Fin 21) : psiFun y ≠ 0 := (phi_facts.1 y).1

theorem phi_psi (y : Fin 21) : phiFun (psiFun y) = y := (phi_facts.1 y).2

theorem psi_phi {x : Fin 22} (hx : x ≠ 0) : psiFun (phiFun x) = x := phi_facts.2.1 x hx

abbrev hexadAut : Subgroup (Equiv.Perm (Fin 22)) := blockAut hexads

theorem mem_hexadAut_of {σ : Equiv.Perm (Fin 22)} (h : ∀ B ∈ hexads, B.map σ.toEmbedding ∈ hexads) :
    σ ∈ hexadAut := by
  rw [mem_blockAut]
  intro B
  refine ⟨fun hB => ?_, h B⟩
  have himg : hexads.image (fun B => B.map σ.toEmbedding) = hexads := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro C hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
      exact h B hB
    · rw [Finset.card_image_of_injective _ (Finset.map_injective _)]
  rw [← himg] at hB
  obtain ⟨B', hB', e⟩ := Finset.mem_image.1 hB
  rwa [← Finset.map_injective _ e]

theorem M22_le_hexadAut : M22 ≤ hexadAut := by
  intro g hg
  refine mem_hexadAut_of fun B hB => ?_
  have := smul_mem_hexads ⟨g, hg⟩ hB
  rwa [Subgroup.smul_def, smul_finset_eq_map] at this

@[expose] def sigmaPerm : Equiv.Perm (Fin 22) where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv := phi_facts.2.2.1
  right_inv := phi_facts.2.2.1

theorem sigmaPerm_mem : sigmaPerm ∈ hexadAut := by
  refine mem_hexadAut_of fun B hB => ?_
  have h := List.all_eq_true.1 phi_facts.2.2.2.2.2.2.2 B (mem_hexads.1 hB)
  rw [List.contains_iff_mem] at h
  obtain ⟨C, hC, e⟩ := List.mem_map.1 h
  rw [Finset.map_eq_image]
  change B.image sigmaFun ∈ hexads
  rw [← mask_injective e]
  exact mem_hexads.2 hC

theorem sigmaPerm_not_mem : sigmaPerm ∉ M22 := by
  intro h
  have h0 := card_m22_subtype (fun g => ∀ x, g x = sigmaFun x)
  rw [count_sigma] at h0
  have : Nonempty {x : M22 // ∀ y, (x : Equiv.Perm (Fin 22)) y = sigmaFun y} :=
    ⟨⟨⟨sigmaPerm, h⟩, fun _ => rfl⟩⟩
  exact absurd h0 (Nat.card_pos_iff.2 ⟨this, inferInstance⟩).ne'

variable (g : stabilizer hexadAut (0 : Fin 22))

theorem stab_zero : ((g : hexadAut) : Equiv.Perm (Fin 22)) 0 = 0 := g.2

theorem stab_ne_zero {x : Fin 22} (hx : x ≠ 0) : ((g : hexadAut) : Equiv.Perm (Fin 22)) x ≠ 0 :=
  fun e => hx (((g : hexadAut) : Equiv.Perm (Fin 22)).injective (e.trans (stab_zero g).symm))

@[expose] def inducedFun (y : Fin 21) : Fin 21 :=
  phiFun (((g : hexadAut) : Equiv.Perm (Fin 22)) (psiFun y))

theorem inducedFun_inv (y : Fin 21) : inducedFun g⁻¹ (inducedFun g y) = y := by
  simp only [inducedFun]
  rw [psi_phi (stab_ne_zero g (psiFun_ne y))]
  change phiFun (((g : hexadAut) : Equiv.Perm (Fin 22))⁻¹
    (((g : hexadAut) : Equiv.Perm (Fin 22)) (psiFun y))) = y
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply, phi_psi]

@[expose] def stabilizerToPlane : stabilizer hexadAut (0 : Fin 22) →* Equiv.Perm (Fin 21) where
  toFun g :=
    { toFun := inducedFun g
      invFun := inducedFun g⁻¹
      left_inv := inducedFun_inv g
      right_inv := fun y => by simpa using inducedFun_inv g⁻¹ y }
  map_one' := by
    ext y
    exact congrArg Fin.val (phi_psi y)
  map_mul' g h := by
    ext y
    change (phiFun ((((g * h : stabilizer hexadAut (0 : Fin 22)) : hexadAut) :
      Equiv.Perm (Fin 22)) (psiFun y)) : ℕ) = (phiFun (((g : hexadAut) : Equiv.Perm (Fin 22))
        (psiFun (phiFun (((h : hexadAut) : Equiv.Perm (Fin 22)) (psiFun y))))) : ℕ)
    rw [psi_phi (stab_ne_zero h (psiFun_ne y))]
    rfl

theorem stabilizerToPlane_apply (y : Fin 21) :
    stabilizerToPlane g y = phiFun (((g : hexadAut) : Equiv.Perm (Fin 22)) (psiFun y)) := rfl

theorem stabilizerToPlane_injective : Function.Injective stabilizerToPlane := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
  by_cases hx : x = 0
  · subst hx
    exact stab_zero g
  · have := congrArg (fun τ : Equiv.Perm (Fin 21) => τ (phiFun x)) hg
    simp only [stabilizerToPlane_apply, Equiv.Perm.one_apply, psi_phi hx] at this
    have e := congrArg psiFun this
    rwa [psi_phi (stab_ne_zero g hx), psi_phi hx] at e

@[expose] def planeImage (B : Finset (Fin 22)) : Finset (Fin 21) := (B.erase 0).image phiFun

theorem map_planeImage (B : Finset (Fin 22)) :
    (planeImage B).map (stabilizerToPlane g).toEmbedding =
      planeImage (B.map ((g : hexadAut) : Equiv.Perm (Fin 22)).toEmbedding) := by
  have herase : (B.erase 0).map ((g : hexadAut) : Equiv.Perm (Fin 22)).toEmbedding =
      (B.map ((g : hexadAut) : Equiv.Perm (Fin 22)).toEmbedding).erase 0 := by
    rw [Finset.map_erase]
    simp [stab_zero g]
  rw [planeImage, planeImage, ← herase, Finset.map_eq_image, Finset.image_image,
    Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun x hx => ?_
  have hx0 : x ≠ 0 := (Finset.mem_erase.1 hx).1
  simp only [Function.comp, Equiv.coe_toEmbedding, stabilizerToPlane_apply, psi_phi hx0]

theorem planeImage_of_not_mem {B : Finset (Fin 22)} (h0 : (0 : Fin 22) ∉ B) :
    planeImage B = B.image phiFun := by
  rw [planeImage, Finset.erase_eq_of_notMem h0]

theorem mem_map_hexadAut (g : hexadAut) {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    B.map (g : Equiv.Perm (Fin 22)).toEmbedding ∈ hexads :=
  (mem_blockAut.1 g.2 B).2 hB

theorem stabilizerToPlane_mem_lineAut : stabilizerToPlane g ∈ lineAut := by
  rw [mem_lineAut]
  intro a
  obtain ⟨B, hB, hB0⟩ : ∃ B ∈ hexadList, 0 ∈ B ∧ planeImage B = projLine a := by
    have := phi_facts.2.2.2.2.2.1 a
    rw [List.any_eq_true] at this
    obtain ⟨B, hB, h⟩ := this
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨B, hB, by simpa using h.1, h.2⟩
  have hB' := mem_map_hexadAut g (mem_hexads.2 hB)
  have h0 : (0 : Fin 22) ∈ B.map ((g : hexadAut) : Equiv.Perm (Fin 22)).toEmbedding := by
    rw [Finset.mem_map_equiv]
    have : ((g : hexadAut) : Equiv.Perm (Fin 22)).symm 0 = 0 := by
      rw [Equiv.symm_apply_eq, stab_zero g]
    rw [this]
    exact hB0.1
  have hline := List.all_eq_true.1 phi_facts.2.2.2.1 _ (mem_hexads.1 hB')
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hline
  rcases hline with h | h
  · simp only [decide_eq_false_iff_not] at h
    exact absurd h0 h
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h
    refine ⟨b, ?_⟩
    rw [← hB0.2, map_planeImage]
    exact hb.symm

@[expose] def class0 : Finset (Finset (Fin 21)) := hyperClass0.toFinset

theorem stabilizerToPlane_smul_class0 : stabilizerToPlane g • class0 = class0 := by
  have hsub : ∀ X ∈ class0, X.map (stabilizerToPlane g).toEmbedding ∈ class0 := by
    intro X hX
    obtain ⟨B, hB, hB0⟩ : ∃ B ∈ hexadList, 0 ∉ B ∧ B.image phiFun = X := by
      have := List.all_eq_true.1 phi_facts.2.2.2.2.2.2.1 X (List.mem_toFinset.1 hX)
      rw [List.any_eq_true] at this
      obtain ⟨B, hB, h⟩ := this
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_false_iff_not] at h
      exact ⟨B, hB, h.1, h.2⟩
    have hB' := mem_map_hexadAut g (mem_hexads.2 hB)
    have h0 : (0 : Fin 22) ∉ B.map ((g : hexadAut) : Equiv.Perm (Fin 22)).toEmbedding := by
      rw [Finset.mem_map_equiv]
      have : ((g : hexadAut) : Equiv.Perm (Fin 22)).symm 0 = 0 := by
        rw [Equiv.symm_apply_eq, stab_zero g]
      rw [this]
      exact hB0.1
    have hcls := List.all_eq_true.1 phi_facts.2.2.2.2.1 _ (mem_hexads.1 hB')
    simp only [Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hcls
    rcases hcls with h | h
    · exact absurd h h0
    · rw [← hB0.2, ← planeImage_of_not_mem hB0.1, map_planeImage, planeImage_of_not_mem h0]
      exact List.mem_toFinset.2 h
  have hsm : ∀ X : Finset (Fin 21),
      stabilizerToPlane g • X = X.map (stabilizerToPlane g).toEmbedding := fun X => by
    rw [Finset.smul_finset_def, Finset.map_eq_image]
    rfl
  rw [Finset.smul_finset_def]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro Y hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
    rw [hsm]
    exact hsub X hX
  · rw [Finset.card_image_of_injective _ (MulAction.injective _)]

@[expose] def classStabilizer : Subgroup (Equiv.Perm (Fin 21)) :=
  lineAut ⊓ stabilizer (Equiv.Perm (Fin 21)) class0

theorem range_stabilizerToPlane_le : stabilizerToPlane.range ≤ classStabilizer := by
  rintro _ ⟨g, rfl⟩
  exact ⟨stabilizerToPlane_mem_lineAut g, stabilizerToPlane_smul_class0 g⟩

theorem card_classStabilizer_le : Nat.card classStabilizer ≤ 40320 := by
  have hfun : (fun X : Finset (Fin 21) => deltaPerm • X) =
      fun X => X.image (ofTable21 deltaTab) := funext fun X => by
    rw [Finset.smul_finset_def]
    rfl
  have hδ : deltaPerm • class0 = hyperClass1.toFinset := by
    rw [Finset.smul_finset_def, class0, hfun]
    exact class_images.1
  have hδ2 : deltaPerm • hyperClass1.toFinset = hyperClass2.toFinset := by
    rw [Finset.smul_finset_def, hfun]
    exact class_images.2.1
  set δ' : lineAut := ⟨deltaPerm, deltaPerm_mem_lineAut⟩
  have horb : ({class0, hyperClass1.toFinset, hyperClass2.toFinset} : Set _) ⊆
      orbit lineAut class0 := by
    intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl | rfl
    · exact mem_orbit_self _
    · exact ⟨δ', hδ⟩
    · refine ⟨δ' * δ', ?_⟩
      show (δ' * δ') • class0 = hyperClass2.toFinset
      rw [mul_smul]
      change deltaPerm • deltaPerm • class0 = _
      rw [hδ, hδ2]
  have h3 : 3 ≤ (orbit lineAut class0).ncard := by
    obtain ⟨-, -, h01, h02, h12⟩ := class_images
    have := Set.ncard_le_ncard horb (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [class0, h01, h02]), Set.ncard_pair h12] at this
    exact this
  have hcard := natCard_orbit_mul_card_stabilizer lineAut class0
  have hle := card_lineAut_le
  have heq : Nat.card classStabilizer = Nat.card (stabilizer lineAut class0) :=
    Nat.card_congr ⟨fun τ => ⟨⟨τ.1, τ.2.1⟩, τ.2.2⟩, fun τ => ⟨τ.1.1, τ.1.2, τ.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [heq]
  rw [Nat.card_coe_set_eq] at hcard
  nlinarith

theorem card_stabilizer_hexadAut_le : Nat.card (stabilizer hexadAut (0 : Fin 22)) ≤ 40320 := by
  have h := Subgroup.card_le_of_le range_stabilizerToPlane_le
  rw [← Nat.card_congr (MonoidHom.ofInjective stabilizerToPlane_injective).toEquiv] at h
  exact h.trans card_classStabilizer_le

theorem card_hexadAut : Nat.card hexadAut = 887040 ∧ M22.relIndex hexadAut = 2 := by
  have hle := M22_le_hexadAut
  have hidx := Subgroup.card_mul_index (M22.subgroupOf hexadAut)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_M22'] at hidx
  have hne1 : (M22.subgroupOf hexadAut).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact sigmaPerm_not_mem (h1 sigmaPerm_mem)
  have hne0 : (M22.subgroupOf hexadAut).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have htrans : orbit hexadAut (0 : Fin 22) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨g, hg⟩ := exists_smul_eq M22 (0 : Fin 22) x
    exact ⟨⟨g, hle g.2⟩, hg⟩
  have hcard := natCard_orbit_mul_card_stabilizer hexadAut (0 : Fin 22)
  rw [htrans, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin 22),
    Fintype.card_fin] at hcard
  have hub := card_stabilizer_hexadAut_le
  have h1 : Nat.card hexadAut ≤ 887040 := by omega
  have h2 : 887040 ≤ Nat.card hexadAut := by
    rw [← hidx]
    have : 2 ≤ (M22.subgroupOf hexadAut).index := by omega
    nlinarith
  refine ⟨le_antisymm h1 h2, ?_⟩
  rw [Subgroup.relIndex]
  have : Nat.card hexadAut = 887040 := le_antisymm h1 h2
  rw [this] at hidx
  omega

universe u v

theorem eq_hexads_of_orbit {𝓑 : Finset (Finset (Fin 22))} {X : Finset (Fin 22)} (hX : X.card = 6)
    (h𝓑 : (𝓑 : Set (Finset (Fin 22))) = orbit M22 X) (hS : IsSteinerTriple 𝓑) : 𝓑 = hexads := by
  have h77 : Nat.card (orbit M22 X) = 77 := by
    rw [← h𝓑, Nat.card_coe_set_eq, Set.ncard_coe_finset, hS.card_blocks]
  obtain ⟨g, rfl⟩ := mem_hexads_iff.1 (mem_hexads_of_card_orbit hX h77)
  rw [orbit_smul, orbit_hexad0] at h𝓑
  exact Finset.coe_injective h𝓑

theorem witt_S3622_uniqueness_and_automorphism_group :
    (∀ {Ω : Type u} {Ω' : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
      (𝓑 : Finset (Finset Ω)) (𝓑' : Finset (Finset Ω')), IsSteinerTriple 𝓑 →
        IsSteinerTriple 𝓑' → ∃ e : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑') ∧
    (∃ 𝓑 : Finset (Finset (Fin 22)), (∃ X : Finset (Fin 22), X.card = 6 ∧
      (𝓑 : Set (Finset (Fin 22))) = MulAction.orbit M22 X) ∧ IsSteinerTriple 𝓑) ∧
    ∀ 𝓑 : Finset (Finset (Fin 22)), (∃ X : Finset (Fin 22), X.card = 6 ∧
      (𝓑 : Set (Finset (Fin 22))) = MulAction.orbit M22 X) → IsSteinerTriple 𝓑 →
        Nat.card (blockAut 𝓑) = 887040 ∧ (887040 : ℕ) = 2 * 443520 ∧ M22 ≤ blockAut 𝓑 ∧
          M22.relIndex (blockAut 𝓑) = 2 ∧ (M22.subgroupOf (blockAut 𝓑)).Normal := by
  refine ⟨fun 𝓑 𝓑' h h' => steinerTriple_iso h h', ⟨hexads, ⟨hexad0, Certificates.certificate2039.2.2.2,
    orbit_hexad0.symm⟩, isSteinerTriple_hexads⟩, ?_⟩
  rintro 𝓑 ⟨X, hX, h𝓑⟩ hS
  obtain rfl := eq_hexads_of_orbit hX h𝓑 hS
  obtain ⟨hcard, hidx⟩ := card_hexadAut
  exact ⟨hcard, by norm_num, M22_le_hexadAut, hidx, Subgroup.normal_of_index_eq_two hidx⟩

end CFSG.ComponentClassification.WittDesign
