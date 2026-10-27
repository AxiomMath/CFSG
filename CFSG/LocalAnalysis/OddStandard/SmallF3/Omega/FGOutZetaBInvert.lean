module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open scoped commutatorElement

private theorem zetaBInvert_coe_comm {G : Type*} [Group G] (L : Subgroup G) (u v : ↥L) :
    ((⁅u, v⁆ : ↥L) : G) = ⁅(u : G), (v : G)⁆ := rfl

private theorem zetaBInvert_commute_coe {G : Type*} [Group G] {L : Subgroup G} {a b : ↥L}
    (h : Commute a b) : (a : G) * (b : G) = (b : G) * (a : G) :=
  congrArg Subtype.val h

theorem zetaInvert_holds : ZetaInvert := by
  intro G H _ _ L φ hker w' hw' g hg u v hcomm hgu hgv
  have hmem : ∀ x : ↥L, w' * (x : G) * w'⁻¹ ∈ L := fun x =>
    (Subgroup.mem_set_normalizer_iff.mp hw' (x : G)).mp x.2
  let wu : ↥L := ⟨w' * (u : G) * w'⁻¹, hmem u⟩
  let wv : ↥L := ⟨w' * (v : G) * w'⁻¹, hmem v⟩
  have hφwu : φ wu = g * φ u * g⁻¹ := hg u wu rfl
  have hφwv : φ wv = g * φ v * g⁻¹ := hg v wv rfl
  have hφwu' : φ wu = φ u := by rw [hφwu, hgu]
  have hφwv' : φ wv = (φ v)⁻¹ := by rw [hφwv, hgv]
  let z₁ : ↥L := u⁻¹ * wu
  let z₂ : ↥L := v * wv
  let c : ↥L := ⁅u, v⁆
  have hz₁ker : z₁ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφwu', inv_mul_cancel]
  have hz₂ker : z₂ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hφwv', mul_inv_cancel]
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hcomm]
  have hz₁c : z₁ ∈ Subgroup.center ↥L := hker hz₁ker
  have hz₂c : z₂ ∈ Subgroup.center ↥L := hker hz₂ker
  have hcc : c ∈ Subgroup.center ↥L := hker hcker
  have hcv : Commute ⁅(u : G), (v : G)⁆ (v : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hcc v).symm
  have hz₁u : Commute (z₁ : G) (u : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hz₁c u).symm
  have hz₁v : Commute (z₁ : G) (v : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hz₁c v).symm
  have hz₁z₂ : Commute (z₁ : G) (z₂ : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hz₁c z₂).symm
  have hz₂u : Commute (z₂ : G) (u : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hz₂c u).symm
  have hz₂v : Commute (z₂ : G) (v : G) :=
    zetaBInvert_commute_coe (Subgroup.mem_center_iff.mp hz₂c v).symm
  have hu : w' * (u : G) * w'⁻¹ = (u : G) * (z₁ : G) := by
    rw [show (z₁ : G) = (u : G)⁻¹ * (w' * (u : G) * w'⁻¹) from rfl]
    group
  have hv : w' * (v : G) * w'⁻¹ = (v : G)⁻¹ * (z₂ : G) := by
    rw [show (z₂ : G) = (v : G) * (w' * (v : G) * w'⁻¹) from rfl]
    group
  have hmain := fg_oz_comm_inv hcv hz₁u hz₁v hz₁z₂ hz₂u hz₂v hu hv
  exact ⟨hcker, by simpa [zetaBInvert_coe_comm] using hmain⟩

end CFSG.OddStandard.SmallF3.Omega
