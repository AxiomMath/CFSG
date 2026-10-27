module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem z4o_eq_of_orderOf_eq_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  haveI : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient (α := A) (d := 2) hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

theorem z4o_isCyclic_of_le_centralizer [Finite G] {I X : Subgroup G}
    (hcyc : ∀ P : Sylow 2 (centralizer (I : Set G)),
      IsCyclic (P : Subgroup (centralizer (I : Set G))))
    (hX : X ≤ centralizer (I : Set G)) (hX2 : IsPGroup 2 X) : IsCyclic ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX'2 : IsPGroup 2 (X.subgroupOf (centralizer (I : Set G))) :=
    hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm
  obtain ⟨Q, hQle⟩ := hX'2.exists_le_sylow
  haveI : IsCyclic ↥(Q : Subgroup (centralizer (I : Set G))) := hcyc Q
  haveI : IsCyclic ↥(X.subgroupOf (centralizer (I : Set G))) := Subgroup.isCyclic_of_le hQle
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX)
    (Subgroup.subgroupOfEquivOfLe hX).surjective

theorem sec123z4_false_of_cyclic [Finite G] (hAut : Asc82FactAutAb) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E)
    (F : Sec12Frame t L S)
    (hZ : IsZ4Pow4 (secV t S L E)) {s : G} (hs : orderOf s = 2) (hsS : s ∈ S)
    (hsL : s ∉ L ⊔ centralizer (L : Set G))
    (h64 : Nat.card (secV t S L E ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 ^ 6)
    {I : Subgroup G} (hI : IsComponentIn I (centralizer ({s} : Set G)))
    (hN : centralizer ({s} : Set G) ≤ normalizer (I : Set G))
    (h5 : IsOmega5 I ∨ IsL281 I)
    (hcyc : ∀ P : Sylow 2 (centralizer (I : Set G)),
      IsCyclic (P : Subgroup (centralizer (I : Set G)))) : False := by
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hctx.sylowE
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => sec12E_B_sq F hb
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hsV : s ∉ secV t S L E := fun h =>
    hsL (Subgroup.mem_sup_left (F.bdata.1 (sec124_z4_mem_of_sq hZ hBV F.bdata.2.1 hB2 s h hss)))
  have hsI : s ∈ centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hI.le hx)
  have hDC : secV t S L E ⊓ centralizer ({s} : Set G) ⊓ centralizer (I : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨⟨hxV, hxs⟩, hxI⟩ := hx
    by_contra hx1
    have key : ∃ y, y ∈ secV t S L E ∧ y ∈ centralizer ({s} : Set G) ∧
        y ∈ centralizer (I : Set G) ∧ orderOf y = 2 := by
      by_cases hxx : x * x = 1
      · exact ⟨x, hxV, hxs, hxI, orderOf_eq_prime (by rw [sq]; exact hxx) hx1⟩
      · refine ⟨x * x, mul_mem hxV hxV, mul_mem hxs hxs, mul_mem hxI hxI,
          orderOf_eq_prime ?_ hxx⟩
        have h4 := sec124_z4_pow_four hZ x hxV
        calc (x * x) ^ 2 = x ^ 4 := by rw [← pow_two, ← pow_mul]
          _ = 1 := h4
    obtain ⟨y, hyV, hys, hyI, hy2⟩ := key
    have hy2' : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
    have hs2' : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    have hcomm : ∀ a ∈ zpowers y, ∀ b ∈ zpowers s, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow
        (show Commute y s from Subgroup.mem_centralizer_singleton_iff.mp hys) i j).eq
    have hPel : CFSG.Open.IsElemAbelian 2 (zpowers y ⊔ zpowers s) :=
      CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hy2')
        (CFSG.Open.isElemAbelian_zpowers hs2') hcomm
    have hPC : zpowers y ⊔ zpowers s ≤ centralizer (I : Set G) :=
      sup_le (zpowers_le.mpr hyI) (zpowers_le.mpr hsI)
    haveI : IsCyclic ↥(zpowers y ⊔ zpowers s) :=
      z4o_isCyclic_of_le_centralizer hcyc hPC hPel.isPGroup
    have hyP : y ∈ zpowers y ⊔ zpowers s := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
    have hsP : s ∈ zpowers y ⊔ zpowers s := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    have heq := z4o_eq_of_orderOf_eq_two (A := ↥(zpowers y ⊔ zpowers s))
      (x := ⟨y, hyP⟩) (y := ⟨s, hsP⟩) (by rw [Subgroup.orderOf_mk]; exact hy2)
      (by rw [Subgroup.orderOf_mk]; exact hs)
    have hys' : y = s := congrArg Subtype.val heq
    exact hsV (hys' ▸ hyV)
  have hDN : secV t S L E ⊓ centralizer ({s} : Set G) ≤ normalizer (I : Set G) :=
    inf_le_right.trans hN
  have hD2 : IsPGroup 2 ↥(secV t S L E ⊓ centralizer ({s} : Set G)) := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    have := sec124_z4_pow_four hZ (g : G) g.2.1
    simpa using this
  have hDc : IsMulCommutative ↥(secV t S L E ⊓ centralizer ({s} : Set G)) :=
    ⟨⟨fun a b => Subtype.ext (sec124_z4_comm hZ a a.2.1 b b.2.1)⟩⟩
  have hle := hAut G I hI.isQuasisimple h5 _ hDN hDC hD2 hDc
  rw [h64] at hle
  norm_num at hle

end CFSG.OddStandard.SmallF3.Omega
