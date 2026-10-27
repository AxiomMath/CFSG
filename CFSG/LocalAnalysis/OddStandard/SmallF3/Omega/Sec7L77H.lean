module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77Case
import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicSolv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l77_centralizer_L_solvable [Finite G] (h72 : Asc82Lemma72) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) :
    Group.IsSolvable ↥(centralizer (L : Set G)) := by
  classical
  let C : Subgroup G := centralizer (L : Set G)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  haveI : IsCyclic ↥((P : Subgroup ↥C).map C.subtype) :=
    h72 G t L hctx.toSec3SettingLB hctx.omega6 _ (isSylow2Of_map_sylow P)
  have hcyc : IsCyclic ↥(P : Subgroup ↥C) :=
    isCyclic_of_injective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥C) C.subtype C.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥C) C.subtype C.subtype_injective).injective
  exact CFSG.OddStandard.Solomon75.isSolvable_of_cyclic_sylow ⟨P, hcyc⟩

theorem sec7l77_eq_one_of_mem_centralizer [Finite G] (hP : Asc82Tab6P) {L : Subgroup G}
    (hL : IsOm6P L) {w : G} (hw : w ∈ L) (hwc : w ∈ centralizer (L : Set G)) : w = 1 := by
  have hz : w ∈ centerIn L := by
    refine Subgroup.mem_map.mpr ⟨⟨w, hw⟩, Subgroup.mem_center_iff.mpr fun a => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwc (a : G) a.2)
  rw [hP.center_triv G L hL] at hz
  exact Subgroup.mem_bot.mp hz

theorem sec7l77_inner_le [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {h : G}
    (hM : h ∈ MSub S B) (ht : h ∈ centralizer ({t} : Set G))
    (hs : h ∈ centralizer ({g⁻¹ * t * g} : Set G)) (hin : h ∈ L ⊔ centralizer (L : Set G)) :
    h ∈ (L ⊓ normalizer (B : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊔
      centralizer (L : Set G) := by
  have hctx := hc.ctx
  have hL := hctx.isOm6P
  have hhN : h ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 h ht
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    hctx.cent_le_normalizer h36 _ (hctx.sylow.1 hc.s_mem)
  have hAL := sec7l77_A_inf_L h36 hP hc
  have hBL : B ≤ L := sec7l77_B_le_L hc
  obtain ⟨l, hl, c, hcC, rfl⟩ := innerOn_decompose (L := L) (s := h) hin
  have hcL : ∀ x ∈ L, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hcC x hx
  have hconj : ∀ x ∈ L, (l * c) * x * (l * c)⁻¹ = l * x * l⁻¹ := by
    intro x hx
    have h1 : c * x * c⁻¹ = x := by rw [← hcL x hx]; group
    calc (l * c) * x * (l * c)⁻¹ = l * (c * x * c⁻¹) * l⁻¹ := by group
      _ = l * x * l⁻¹ := by rw [h1]
  have hmemB : ∀ y, y ∈ B ↔ y ∈ ASub S B ⊓ L := fun y => by rw [hAL]
  have hlB : l ∈ normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxA := (hmemB x).mp hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hM x).mp hxA.1
      have h2 := (Subgroup.mem_normalizer_iff.mp hhN x).mp hxA.2
      have h3 : (l * c) * x * (l * c)⁻¹ ∈ B := (hmemB _).mpr ⟨h1, h2⟩
      rwa [hconj x hxA.2] at h3
    · intro hx
      have hxL' : l * x * l⁻¹ ∈ L := hBL hx
      have hxL : x ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL') hl
        simpa [mul_assoc] using this
      have h3 : (l * c) * x * (l * c)⁻¹ ∈ B := by rwa [hconj x hxL]
      have h4 := (hmemB _).mp h3
      have h5 : x ∈ ASub S B := (Subgroup.mem_normalizer_iff.mp hM x).mpr h4.1
      exact (hmemB x).mpr ⟨h5, hxL⟩
  have hs' : (l * c) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (l * c) :=
    Subgroup.mem_centralizer_singleton_iff.mp hs
  have hls : l * (g⁻¹ * t * g) = (g⁻¹ * t * g) * l := by
    set s := g⁻¹ * t * g with hs_def
    have hsL : ∀ x ∈ L, s * x * s⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
    have hsiL : s⁻¹ * l * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hsN) l).mp hl
      simpa using this
    have hE : ∀ x ∈ L, l * s * x * s⁻¹ * l⁻¹ = s * l * x * l⁻¹ * s⁻¹ := by
      intro x hx
      have e1 := hconj (s * x * s⁻¹) (hsL x hx)
      have e2 := hconj x hx
      calc l * s * x * s⁻¹ * l⁻¹ = l * (s * x * s⁻¹) * l⁻¹ := by group
        _ = (l * c) * (s * x * s⁻¹) * (l * c)⁻¹ := e1.symm
        _ = ((l * c) * s) * x * ((l * c) * s)⁻¹ := by group
        _ = (s * (l * c)) * x * (s * (l * c))⁻¹ := by rw [hs']
        _ = s * ((l * c) * x * (l * c)⁻¹) * s⁻¹ := by group
        _ = s * (l * x * l⁻¹) * s⁻¹ := by rw [e2]
        _ = s * l * x * l⁻¹ * s⁻¹ := by group
    have hyL : l⁻¹ * s⁻¹ * l * s ∈ L := by
      have := L.mul_mem (L.inv_mem hl) hsiL
      simpa [mul_assoc] using this
    have hyC : l⁻¹ * s⁻¹ * l * s ∈ centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      calc x * (l⁻¹ * s⁻¹ * l * s)
          = ((l⁻¹ * s⁻¹) * (s * l * x * l⁻¹ * s⁻¹) * (l * s))⁻¹⁻¹ := by group
        _ = ((l⁻¹ * s⁻¹) * (l * s * x * s⁻¹ * l⁻¹) * (l * s))⁻¹⁻¹ := by rw [hE x hx]
        _ = (l⁻¹ * s⁻¹ * l * s) * x := by group
    have hy1 : l⁻¹ * s⁻¹ * l * s = 1 := sec7l77_eq_one_of_mem_centralizer hP hL hyL hyC
    have hsl : s⁻¹ * l * s = l :=
      calc s⁻¹ * l * s = l * (l⁻¹ * s⁻¹ * l * s) := by group
        _ = l := by rw [hy1, mul_one]
    calc l * s = s * (s⁻¹ * l * s) := by group
      _ = s * l := by rw [hsl]
  have hlD : l ∈ L ⊓ normalizer (B : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) :=
    ⟨⟨hl, hlB⟩, Subgroup.mem_centralizer_singleton_iff.mpr hls⟩
  exact Subgroup.mul_mem_sup hlD hcC

theorem sec7l77_H_solvable [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    Group.IsSolvable
      ↥(MSub S B ⊓ centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
  classical
  have hctx := hc.ctx
  have hL := hctx.isOm6P
  set Hs := MSub S B ⊓ centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) with hHs
  set C := centralizer (L : Set G) with hC
  set D := L ⊓ normalizer (B : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) with hD
  have hCsol : Group.IsSolvable ↥C := sec7l77_centralizer_L_solvable h72 hctx
  have hDsol : Group.IsSolvable ↥D := sec7l77_cent_s_solvable h36 hP hc
  have hDC : D ≤ centralizer (C : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun c hcC =>
      (Subgroup.mem_centralizer_iff.mp hcC d hd.1.1).symm
  have hDCsol := sec7l77_solvable_sup hDC hDsol hCsol
  set X := Hs ⊓ (L ⊔ C) with hX
  have hXle : X ≤ D ⊔ C := fun h hh =>
    sec7l77_inner_le h36 hP hc hh.1.1.1 hh.1.1.2 hh.1.2 hh.2
  have hXsol : Group.IsSolvable ↥X :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hXle)
  have hXHs : X ≤ Hs := inf_le_left
  haveI hnorm : (X.subgroupOf Hs).Normal := by
    refine ⟨fun n hn k => ?_⟩
    have hnX : (n : G) ∈ X := hn
    obtain ⟨l, hl, c, hcC, hnlc⟩ := innerOn_decompose (L := L) (s := (n : G)) hnX.2
    have hkN : (k : G) ∈ normalizer (L : Set G) :=
      hctx.cent_le_normalizer h36 _ k.2.1.2
    have hklk : (k : G) * l * (k : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hkN l).mp hl
    have hkck : (k : G) * c * (k : G)⁻¹ ∈ C := by
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hx' : (k : G)⁻¹ * x * (k : G) ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hkN) x).mp hx
        simpa using this
      have hcomm : ((k : G)⁻¹ * x * (k : G)) * c = c * ((k : G)⁻¹ * x * (k : G)) :=
        Subgroup.mem_centralizer_iff.mp hcC _ hx'
      calc x * ((k : G) * c * (k : G)⁻¹)
          = (k : G) * (((k : G)⁻¹ * x * (k : G)) * c) * (k : G)⁻¹ := by group
        _ = (k : G) * (c * ((k : G)⁻¹ * x * (k : G))) * (k : G)⁻¹ := by rw [hcomm]
        _ = ((k : G) * c * (k : G)⁻¹) * x := by group
    change ((k * n * k⁻¹ : ↥Hs) : G) ∈ X
    refine ⟨(Hs.mul_mem (Hs.mul_mem k.2 n.2) (Hs.inv_mem k.2)), ?_⟩
    have hval : ((k * n * k⁻¹ : ↥Hs) : G) =
        ((k : G) * l * (k : G)⁻¹) * ((k : G) * c * (k : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnlc]
      group
    rw [hval]
    exact Subgroup.mul_mem_sup hklk hkck
  have hNsol : Group.IsSolvable ↥(X.subgroupOf Hs) :=
    solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hXHs).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXHs).injective
  refine sec7l77_solvable_of_odd_le (X.subgroupOf Hs) hNsol fun x hx => ?_
  have hxN : (x : G) ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 _ x.2.1.2
  have hxodd : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
  exact ⟨x.2, hP.out_two G L hL (x : G) hxN hxodd⟩

end CFSG.OddStandard.SmallF3.Omega
