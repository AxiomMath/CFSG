module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0b

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem oddCoreIn_le_aux (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem odd_card_oddCoreIn_aux [Finite G] (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) :=
  CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X

theorem sec10K0_pockets_sup [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    K1 ⊔ K2 = oTwoRes (L ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨K1', K2', _, _, _, huniq, _, hsup', _, _⟩ :=
    hP5 G L hpsp z hctx.toSec10Z.pocket
  rcases huniq K1 hctx.pocket1 with h1 | h1 <;> rcases huniq K2 hctx.pocket2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hctx.ne
  · rw [h1, h2]
    exact hsup'.symm
  · rw [h1, h2, sup_comm]
    exact hsup'.symm
  · exact absurd (h1.trans h2.symm) hctx.ne

theorem sec10K0_ge [Finite G] (h36 : Asc82Lemma36) (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 ≤ secK0 t z := by
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hK : K1 ⊔ K2 ≤ secK0 t z := by
    rw [sec10K0_pockets_sup hP5 hpsp hctx]
    unfold secK0 oTwoRes
    exact Subgroup.closure_mono (by
      rintro x ⟨hx, hodd⟩
      exact ⟨⟨hLt hx.1, hx.2⟩, hodd⟩)
  refine sup_le (sup_le ?_ (le_trans le_sup_left hK)) (le_trans le_sup_right hK)
  intro o ho
  have hoC : o ∈ centralizer ({t} : Set G) := oddCoreIn_le_aux _ ho
  have hoL : o ∈ centralizer (L : Set G) :=
    sec10K0_oddCore_le_centralizer hpsp hzL hz2 hLt hN ho
  have hoZ : o ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hoL z hzL).symm
  have hdvd : orderOf o ∣ Nat.card (oddCoreIn (centralizer ({t} : Set G))) :=
    (oddCoreIn (centralizer ({t} : Set G))).orderOf_dvd_natCard ho
  have hodd : Odd (orderOf o) := (odd_card_oddCoreIn_aux _).of_dvd_nat hdvd
  unfold secK0 oTwoRes
  exact Subgroup.subset_closure ⟨⟨hoC, hoZ⟩, hodd⟩

theorem sec10K0_le [Finite G] (h36 : Asc82Lemma36) (h102 : Asc82Lemma102)
    (hP5 : Asc82FactPockets5) (hO5 : Asc82FactOut5) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    secK0 t z ≤ oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 := by
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hsup := sec10K0_pockets_sup hP5 hpsp hctx
  unfold secK0 oTwoRes
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨⟨hxt, hxz⟩, hodd⟩
  have hxN : x ∈ normalizer (L : Set G) := hN hxt
  have hxz' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxz
  obtain ⟨l, hlL, c, hc, hxc, hlz, hlodd, hcodd⟩ :=
    sec10K0_decomp hLC hzL hxN hxz' hodd (hO5 G L hpsp)
  have hct : c ∈ centralizer ({t} : Set G) := by
    have hcx : c = l⁻¹ * x := by rw [hxc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hcx]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLt hlL)) hxt
  have hcO : c ∈ oddCoreIn (centralizer ({t} : Set G)) :=
    sec10K0_mem_oddCoreIn (h102 G t L hctx.toSec10Z.toSec10Setting) hN hc hct hcodd
  have hl : l ∈ oTwoRes (L ⊓ centralizer ({z} : Set G)) :=
    Subgroup.subset_closure
      ⟨⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr hlz⟩, hlodd⟩
  have hlK : l ∈ K1 ⊔ K2 := by rw [hsup]; exact hl
  have hle : K1 ⊔ K2 ≤ (oddCoreIn (centralizer ({t} : Set G)) ⊔ K1) ⊔ K2 :=
    sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  have hl' : l ∈ (oddCoreIn (centralizer ({t} : Set G)) ⊔ K1) ⊔ K2 := hle hlK
  have hOle : oddCoreIn (centralizer ({t} : Set G)) ≤
      (oddCoreIn (centralizer ({t} : Set G)) ⊔ K1) ⊔ K2 :=
    le_trans le_sup_left le_sup_left
  have hcO' : c ∈ (oddCoreIn (centralizer ({t} : Set G)) ⊔ K1) ⊔ K2 := hOle hcO
  simpa [hxc] using Subgroup.mul_mem _ hl' hcO'

theorem asc82Lemma10K0_of (h36 : Asc82Lemma36) (h102 : Asc82Lemma102) (hb : Asc82Basic10)
    (hP5 : Asc82FactPockets5) (hO5 : Asc82FactOut5) : Asc82Lemma10K0 := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨hpsp, -, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  refine ⟨le_antisymm (sec10K0_le h36 h102 hP5 hO5 hpsp hctx)
    (sec10K0_ge h36 hP5 hpsp hctx), ?_⟩
  have hset : centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) =
      centralizer ({z, t} : Set G) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨ht, hz⟩ y hy
      rw [Set.mem_insert_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact hz z (Set.mem_singleton z)
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ht t (Set.mem_singleton t)
    · intro h
      exact ⟨fun y hy => h y (by rw [Set.mem_insert_iff]; exact Or.inr hy),
        fun y hy => h y (by rw [Set.mem_insert_iff]; exact Or.inl hy)⟩
  unfold secK0
  rw [hset]

end CFSG.OddStandard.SmallF3.Omega
