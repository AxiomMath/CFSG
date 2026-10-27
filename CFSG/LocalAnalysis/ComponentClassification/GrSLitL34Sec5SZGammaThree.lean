module

public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G]

@[expose] def zGammaThree (D : Subgroup G) : Subgroup G :=
  ⁅⁅D, D⁆, D⁆ ⊓ centralizer ((⁅⁅D, D⁆, D⁆ : Subgroup G) : Set G)

theorem zGammaThree_le (D : Subgroup G) : zGammaThree D ≤ D :=
  inf_le_left.trans (commutator_le_of_le (commutator_le_of_le le_rfl le_rfl) le_rfl)

theorem zGammaThree_comm (D : Subgroup G) :
    ∀ x ∈ zGammaThree D, ∀ y ∈ zGammaThree D, x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.mp hy.2 x hx.1

theorem zGammaThree_map_conj (g : G) (D : Subgroup G) :
    zGammaThree (D.map (MulAut.conj g).toMonoidHom) =
      (zGammaThree D).map (MulAut.conj g).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have h3 : (⁅⁅D, D⁆, D⁆).map (MulAut.conj g).toMonoidHom =
      ⁅⁅D.map (MulAut.conj g).toMonoidHom, D.map (MulAut.conj g).toMonoidHom⁆,
        D.map (MulAut.conj g).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
  rw [zGammaThree, zGammaThree, Subgroup.map_inf_eq _ _ _ hinj, ← CFSG.GroupTheory.centralizer_map_conj,
    h3]

theorem mem_normalizer_zGammaThree {D : Subgroup G} {g : G} (hg : g ∈ normalizer (D : Set G)) :
    g ∈ normalizer (zGammaThree D : Set G) := by
  have hD : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (zGammaThree D).map (MulAut.conj g).toMonoidHom = zGammaThree D
  rw [← zGammaThree_map_conj, hD]

variable [Finite G]

theorem wGroup_eq_wGroup_zGammaThree (hB : GWTwoBalanced G) {t : G} (ht : orderOf t = 2)
    {D X : Subgroup G} (hD : IsPGroup 2 D) (hDt : D ≤ centralizer ({t} : Set G))
    (hX : IsPGroup 2 X) (htX : t ∈ X) (hXt : X ≤ centralizer ({t} : Set G))
    (hXD : X ≤ normalizer (D : Set G)) (hA : IsElemTwo (zGammaThree D))
    (hA8 : 8 ≤ Nat.card (zGammaThree D)) (h32 : 32 ≤ Nat.card ↥(zGammaThree D ⊔ zpowers t))
    {B : Subgroup G} (hBT : B ≤ D ⊔ X) (hB3 : IsAbelianTwoOfRank 3 B) :
    wGroup B = wGroup (zGammaThree D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  set A := zGammaThree D with hAdef
  set F := A ⊔ zpowers t with hFdef
  have htA : ∀ y ∈ A, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hDt (zGammaThree_le D hy))).symm
  have hF : IsElemTwo F := by
    refine hA.sup (isElemTwo_zpowers htt) fun x hx y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (htA x hx).symm k).eq
  have hS : IsPGroup 2 ↥(D ⊔ X) := by
    rw [sup_comm]
    exact hX.to_sup_of_normal_right' hD hXD
  have hFS : F ≤ D ⊔ X := sup_le ((zGammaThree_le D).trans le_sup_left)
    (zpowers_le.mpr (mem_sup_right htX))
  have hNF : ∀ g : G, g ∈ normalizer (D : Set G) → g ∈ centralizer ({t} : Set G) →
      g ∈ normalizer (F : Set G) := by
    intro g hgD hgt
    have h1 : A.map (MulAut.conj g) = A :=
      mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_zGammaThree hgD)
    have h2 : (zpowers t).map (MulAut.conj g) = zpowers t := by
      rw [MonoidHom.map_zpowers]
      congr 1
      simp only [MonoidHom.coe_coe, MulAut.conj_apply]
      rw [mem_centralizer_singleton_iff.mp hgt, mul_inv_cancel_right]
    exact mem_normalizer_iff_map_conj_eq.mpr (by rw [hFdef, Subgroup.map_sup, h1, h2])
  have hSF : D ⊔ X ≤ normalizer (F : Set G) :=
    sup_le (fun d hd => hNF d (le_normalizer hd) (hDt hd)) fun x hx => hNF x (hXD hx) (hXt hx)
  have hconn := abelianConnectedIn_of_normal_elementary hS hFS hSF hF h32 hBT hB3
  rw [wGroup_eq_of_abelianConnected hB hconn.abelianConnected]
  exact wGroup_eq_of_commute hB (hF.isAbelianTwoOfRank (by omega)) (hA.isAbelianTwoOfRank hA8)
    fun x hx y hy => hF.1 x hx y (mem_sup_left hy)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
