module

public import CFSG.ClassicalInvolution.Q3.TL4VtxOrb

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Vtx

section Img

variable {Q : Type} [Group Q] {L : Subgroup Q}

theorem conjSub_inducedImage (n : ↥(Subgroup.normalizer (L : Set Q))) (M : Subgroup Q) :
    conjSub (toInducedAutOn L n) (inducedImage L M) = inducedImage L (conjSub (n : Q) M) := by
  unfold inducedImage
  rw [← AscQuot.map_conjSub, conjSub_subgroupOf]

@[expose] noncomputable def psiL (L X : Subgroup Q)
    (hXN : X ≤ Subgroup.normalizer (L : Set Q)) : ↥X →* ↥(inducedAutOn L) :=
  (toInducedAutOn L).comp (Subgroup.inclusion hXN)

theorem map_psiL {X : Subgroup Q} (hXN : X ≤ Subgroup.normalizer (L : Set Q)) {M : Subgroup Q}
    (hMX : M ≤ X) : (M.subgroupOf X).map (psiL L X hXN) = inducedImage L M := by
  unfold psiL inducedImage
  rw [← Subgroup.map_map]
  congr 1
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf]
    have e : (x : Q) = y := congrArg Subtype.val hxy
    show y ∈ M
    rw [← e]
    exact Subgroup.mem_subgroupOf.mp hx
  · intro hyM
    exact ⟨⟨y, hMX (Subgroup.mem_subgroupOf.mp hyM)⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hyM), rfl⟩

theorem mem_ker_psiL_iff {X : Subgroup Q} (hXN : X ≤ Subgroup.normalizer (L : Set Q)) (x : ↥X) :
    x ∈ (psiL L X hXN).ker ↔ ∀ l ∈ L, (x : Q) * l = l * x := by
  rw [MonoidHom.mem_ker]
  exact ⟨Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hXN x.2),
    Lemma52Proof.toInducedAutOn_eq_one_of_commute L (hXN x.2)⟩

theorem ker_psiL {X : Subgroup Q} (hXN : X ≤ Subgroup.normalizer (L : Set Q)) (hLX : L ≤ X) :
    (psiL L X hXN).ker = Subgroup.centralizer ((L.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  ext x
  rw [mem_ker_psiL_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    exact Subtype.ext (h l (Subgroup.mem_subgroupOf.mp hl)).symm
  · intro h l hl
    exact (congrArg Subtype.val (h ⟨l, hLX hl⟩ (Subgroup.mem_subgroupOf.mpr hl))).symm

theorem commute_conj_of_mem_normalizer {g w : Q} (hg : g ∈ Subgroup.normalizer (L : Set Q))
    (hw : ∀ l ∈ L, w * l = l * w) : ∀ l ∈ L, g * w * g⁻¹ * l = l * (g * w * g⁻¹) := by
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    refine (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_
    rwa [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
  have h1 := hw _ hl'
  calc g * w * g⁻¹ * l = g * (w * (g⁻¹ * l * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * l * g) * w) * g⁻¹ := by rw [h1]
    _ = l * (g * w * g⁻¹) := by group

theorem conj_ne_conj {g a b : Q} (hne : a * b ≠ b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) ≠ (g * b * g⁻¹) * (g * a * g⁻¹) := by
  intro h
  apply hne
  have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  simpa using h1

end Img

section Fam

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

@[expose] def TwinFreeAt (Φ : Set (Subgroup Q)) (K : Subgroup Q) (z : Q) (L : Subgroup Q) :
    Prop :=
  ∀ h ∈ orbGrp Φ K, (∀ l ∈ L, h * z * h⁻¹ * z⁻¹ * l = l * (h * z * h⁻¹ * z⁻¹)) →
    h * z * h⁻¹ = z

@[expose] noncomputable def imgFam (Φ : Set (Subgroup Q)) (K L : Subgroup Q)
    (hXN : orbGrp Φ K ≤ Subgroup.normalizer (L : Set Q)) : Set (Subgroup ↥(inducedAutOn L)) :=
  (fun M => M.map (psiL L (orbGrp Φ K) hXN)) ''
    CoreAssembly.conjClass (K.subgroupOf (orbGrp Φ K))

omit [Finite Q] in
theorem mem_imgFam_iff (hcl : ConjInvariant Φ) {K L : Subgroup Q} (hK : K ∈ Φ)
    (hXN : orbGrp Φ K ≤ Subgroup.normalizer (L : Set Q)) {M : Subgroup ↥(inducedAutOn L)} :
    M ∈ imgFam Φ K L hXN ↔ ∃ x ∈ orbGrp Φ K, inducedImage L (conjSub x K) = M := by
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, x.2, ?_⟩
    dsimp only
    rw [conjSub_subgroupOf, map_psiL hXN (conjSub_le_orbGrp K ⟨x, orbGrp_le hcl hK x.2⟩)]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨_, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    dsimp only
    rw [conjSub_subgroupOf, map_psiL hXN (conjSub_le_orbGrp K ⟨x, orbGrp_le hcl hK hx⟩)]

end Fam

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
