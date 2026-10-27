module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LieType.OutStructure

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]

theorem mem_sup_centralizer_of_mem_inner {x : X}
    (h : MulAut.conjNormal (H := L) x ∈ inner ↥L) :
    x ∈ L ⊔ centralizer (L : Set X) :=
  CFSG.Quasithin.H13.NQCore.mem_sup_centralizer_of_conjNormal_inner h

@[expose] noncomputable def conjToOuter : X →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp (MulAut.conjNormal (H := L))

theorem conjToOuter_apply (x : X) :
    conjToOuter (L := L) x =
      (QuotientGroup.mk' (inner ↥L)) (MulAut.conjNormal (H := L) x) := rfl

theorem conjToOuter_ne_one {x : X} (hx : x ∉ L ⊔ centralizer (L : Set X)) :
    conjToOuter (L := L) x ≠ 1 := by
  intro h
  apply hx
  rw [conjToOuter_apply] at h
  exact mem_sup_centralizer_of_mem_inner
    ((QuotientGroup.eq_one_iff (MulAut.conjNormal (H := L) x)).mp h)

theorem sup_centralizer_le_ker_conjToOuter :
    L ⊔ centralizer (L : Set X) ≤ (conjToOuter (L := L)).ker := by
  refine sup_le ?_ ?_
  · intro l hl
    rw [MonoidHom.mem_ker, conjToOuter_apply]
    exact (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := L) l)).mpr
      ⟨⟨l, hl⟩, by ext y; simp [MulAut.conjNormal_apply]⟩
  · intro c hc
    rw [MonoidHom.mem_ker, conjToOuter_apply]
    have h1 : MulAut.conjNormal (H := L) c = 1 := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have hcomm : (y : X) * c = c * (y : X) :=
        Subgroup.mem_centralizer_iff.mp hc (y : X) y.2
      calc c * (y : X) * c⁻¹ = (y : X) * c * c⁻¹ := by rw [hcomm]
        _ = (y : X) := by group
    rw [h1, map_one]

theorem three_dvd_outer_centerQuotient_of_three_dvd_index (hL : CFSG.IsComponent L)
    (hdiv : 3 ∣ (L ⊔ centralizer (L : Set X)).index) :
    3 ∣ Nat.card (Outer (↥L ⧸ center ↥L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U : Subgroup X := L ⊔ centralizer (L : Set X)
  have hUidx : U.index = Nat.card (X ⧸ U) := Subgroup.index_eq_card (H := U)
  have h3q : 3 ∣ Nat.card (X ⧸ U) := by rw [← hUidx]; exact hdiv
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X ⧸ U) 3 h3q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective U g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    norm_num at hg
  have hxU : x ∉ U := by
    intro hxU
    apply hg1
    rw [← hx]
    exact (QuotientGroup.eq_one_iff x).mpr hxU
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hx3 : x ^ 3 ∈ U := by
    have h1 : (QuotientGroup.mk' U) (x ^ 3) = 1 := by
      rw [map_pow, hx, hg3]
    exact (QuotientGroup.eq_one_iff (x ^ 3)).mp h1
  let y : Outer ↥L := conjToOuter (L := L) x
  have hy1 : y ≠ 1 := conjToOuter_ne_one (by simpa [U] using hxU)
  have hy3 : y ^ 3 = 1 := by
    have hker := sup_centralizer_le_ker_conjToOuter (L := L)
    have hx3ker : x ^ 3 ∈ (conjToOuter (L := L)).ker := hker (by simpa [U] using hx3)
    have h1 : (conjToOuter (L := L)) (x ^ 3) = 1 := MonoidHom.mem_ker.mp hx3ker
    simpa [y, map_pow] using h1
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have h3OutL : 3 ∣ Nat.card (Outer ↥L) := by
    have := orderOf_dvd_natCard y
    rwa [hyord] at this
  haveI : Group.IsPerfect ↥L := hL.1.1
  let f : Outer ↥L →* Outer (↥L ⧸ center ↥L) := centerQuotientOuterHom ↥L
  have hf : Function.Injective f := centerQuotient_outer_injective ↥L
  have hcard : Nat.card (Outer ↥L) = Nat.card (f.range : Subgroup (Outer (↥L ⧸ center ↥L))) :=
    Nat.card_congr (Equiv.ofInjective f hf)
  have h3range : 3 ∣ Nat.card (f.range : Subgroup (Outer (↥L ⧸ center ↥L))) := by
    rw [← hcard]
    exact h3OutL
  exact h3range.trans (Subgroup.card_subgroup_dvd_card f.range)

end CFSG.LieType.OutStructure
