module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Field
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {H : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf p H ↔ ∃ h ∈ GLAPPrimeCore p ↥H, (h : G) = g := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem glaPPrimeCoreOf_normalized {p : ℕ} (X : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {n : G} (hn : n ∈ GLAPPrimeCoreOf p X) :
    g * n * g⁻¹ ∈ GLAPPrimeCoreOf p X := by
  have hgi : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
  obtain ⟨h, hh, hhn⟩ := (mem_glaPPrimeCoreOf_iff (p := p) (H := X) (g := n)).1 hn
  have hmap : (GLAPPrimeCore p ↥X).map (conjAutOf X g⁻¹ hgi).toMonoidHom = GLAPPrimeCore p ↥X :=
    pPrimeCore_map_iso p (conjAutOf X g⁻¹ hgi)
  have hmem : conjAutOf X g⁻¹ hgi h ∈ (GLAPPrimeCore p ↥X).map (conjAutOf X g⁻¹ hgi).toMonoidHom :=
    ⟨h, hh, rfl⟩
  rw [hmap] at hmem
  refine (mem_glaPPrimeCoreOf_iff (p := p) (H := X) (g := g * n * g⁻¹)).2 ⟨conjAutOf X g⁻¹ hgi h, hmem, ?_⟩
  rw [conjAutOf_apply, ← hhn]
  simp

theorem mem_glaPPrimeCore_of_coe {p : ℕ} {L : Subgroup G} {z : ↥L} (hz : (z : G) ∈ GLAPPrimeCoreOf p L) :
    z ∈ GLAPPrimeCore p ↥L := by
  obtain ⟨w, hw, hwe⟩ := (mem_glaPPrimeCoreOf_iff (p := p) (H := L) (g := (z : G))).1 hz
  have : w = z := Subtype.ext hwe
  rw [← this]
  exact hw

theorem trivAut_conjAutOf_iff {p : ℕ} (L : Subgroup G) {d : G} (hd : d ∈ Subgroup.normalizer (L : Set G)) :
    TrivAut p ↥L (conjAutOf L d hd) ↔ ∀ l ∈ L, ⁅l, d⁆ ∈ GLAPPrimeCoreOf p L := by
  have hdi : d⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hd
  constructor
  · intro h l hl
    have h1 := h ⟨l, hl⟩
    have h2 : (d⁻¹ * l * d * l⁻¹ : G) ∈ GLAPPrimeCoreOf p L := by
      refine (mem_glaPPrimeCoreOf_iff (p := p) (H := L)).2 ⟨_, h1, ?_⟩
      simp [conjAutOf_apply]
    have h3 := glaPPrimeCoreOf_normalized L hd h2
    have h4 : d * (d⁻¹ * l * d * l⁻¹) * d⁻¹ = ⁅l, d⁆ := by
      rw [commutatorElement_def]
      group
    rw [← h4]
    exact h3
  · intro h y
    apply mem_glaPPrimeCore_of_coe
    have h5 := glaPPrimeCoreOf_normalized L hdi (h y.1 y.2)
    have h6 : (d⁻¹)⁻¹ = d := inv_inv d
    rw [h6] at h5
    have h7 : (((conjAutOf L d hd) y * y⁻¹ : ↥L) : G) = d⁻¹ * ⁅(y : G), d⁆ * d⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAutOf_apply, inv_inv, commutatorElement_def]
      group
    rw [h7]
    simpa [h6] using h5

@[expose] noncomputable def conjHom (L B : Subgroup G) (hB : B ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) : ↥B →* MulAut ↥L where
  toFun g := conjAutOf L g.1 (hB g.2)
  map_one' := by
    ext x
    simp [conjAutOf_apply]
  map_mul' g h := by
    ext x
    have hc : g.1 * h.1 = h.1 * g.1 := hcomm g.1 g.2 h.1 h.2
    simp only [MulAut.mul_apply, conjAutOf_apply, Subgroup.coe_mul]
    rw [hc, mul_inv_rev]
    group

theorem conjHom_apply (L B : Subgroup G) (hB : B ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) (g : ↥B) :
    conjHom L B hB hcomm g = conjAutOf L g.1 (hB g.2) :=
  rfl

theorem card_trivAut_eq {p : ℕ} (L B : Subgroup G) (hB : B ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) :
    Nat.card {g : ↥B // TrivAut p ↥L (conjHom L B hB hcomm g)} = Nat.card ↥(B ⊓ centModSubgroup p L) := by
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨g.1.1, Subgroup.mem_inf.2
        ⟨g.1.2, ⟨hB g.1.2, (trivAut_conjAutOf_iff L (hB g.1.2)).1 g.2⟩⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩,
        (trivAut_conjAutOf_iff L (hB (Subgroup.mem_inf.1 x.2).1)).2
          (fun l hl => (Subgroup.mem_inf.1 x.2).2.2 l hl)⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
