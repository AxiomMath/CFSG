module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSection
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
import CFSG.LocalAnalysis.AGLEmbedding.ConjPowInjective

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_three_blocks_scalar (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) (hOp : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hB : CFSG.Open.pRank p (barM M (H ⊓ M)) ≤ 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G} (htK : t ∈ H ⊓ M)
    (ht1 : t ∉ Subgroup.normalizer (L : Set G)) (ht2 : t ^ 2 ∉ Subgroup.normalizer (L : Set G))
    (ht3 : t ^ 3 ∈ Subgroup.normalizer (L : Set G))
    {X : Subgroup G} (hXK : X ≤ H ⊓ M) (hXel : IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    (hXL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      X ≤ Subgroup.normalizer (L' : Set G))
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : z ^ p = 1) (hzX : z ∉ X)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    (hzL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      z ∈ Subgroup.normalizer (L' : Set G))
    (htz : t * z = z * t) {l : ℕ} (hl : Nat.Coprime (l - 1) p) (hl0 : 1 ≤ l)
    (htl : ∀ x ∈ X, t ^ 3 * x * (t ^ 3)⁻¹ = x ^ l)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D) (hDK : D ≤ barM M (H ⊓ M))
    (hDL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      D ≤ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hzD : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩ ∈ D)
    (hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      W = ⊥) :
    False := by
  have hp := h3.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := h3.ne_two
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have htM : t ∈ M := htK.2
  have htS : t ∈ Subgroup.normalizer (S : Set G) := (hKeq ▸ htK).2
  have hzM : z ∈ M := hzK.2
  set zb := mk ⟨z, hzM⟩ with hzb
  set B := barM M (H ⊓ M) with hBdef
  let Lg : Fin 3 → Subgroup G := fun i => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom
  have hLg : ∀ i, IsWeakSBlock M S (Lg i) := fun i =>
    hL.map_conj (M.pow_mem htM _) (Subgroup.pow_mem _ htS _)
  let Lb : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun i => barM M (Lg i)
  have hLbC : ∀ i, IsComponentOf (Lb i) ⊤ := fun i => (hLg i).component
  have hmm : ∀ (a b : G) (Y : Subgroup G), Y.map (MulAut.conj (a * b)).toMonoidHom =
      (Y.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b Y
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hLne : ∀ i j : Fin 3, i ≠ j → Lb i ≠ Lb j := fun i j hij he =>
    hij (injective_map_conj_pow_of_forall_lt (m := 3) (fun a ha0 ha3 hmem => by
        interval_cases a
        · rw [pow_one] at hmem
          exact ht1 hmem
        · exact ht2 hmem)
      ((hLg i).toIsTwoPrimeComponent.eq_of_barM_eq (hLg j).toIsTwoPrimeComponent he))
  have hZc : ∀ i, ∀ w ∈ Lb i, w ∈ Subgroup.centralizer (Lb i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      w ^ p = 1 → w = 1 := fun i w hw hwC hwp =>
    eq_one_of_mem_center_component_of_pCore hOp (hLbC i) hw hwC hwp
  set Xb := barM M X with hXb
  have hXM : X ≤ M := hXK.trans inf_le_right
  have hXbel : IsElemAbelian p Xb := isElemAbelian_barM_of hXel
  have hXbcard : Nat.card Xb = p ^ 2 := (card_barM_of_elem hp hp2 hXM hXel).trans hXcard
  have hzbp : zb ^ p = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this, map_one]
  have hXbz : Xb ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hXz (Subgroup.mem_subgroupOf.mp hxX)))
  have hzbC : zb ∈ Subgroup.centralizer (Xb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.LocalAnalysis.ComponentInitial.mem_centralizer_of_le_centralizer_singleton hXbz
  have hzbX : zb ∉ Xb := mk_not_mem_barM_of_commute hp hp2 hXel.2 hzM hzp hzX hXz
  have hzb1 : zb ≠ 1 := fun h => hzbX (h ▸ Xb.one_mem)
  have hzbord : orderOf zb = p := orderOf_eq_prime hzbp hzb1
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Xb ⊔ Subgroup.zpowers zb with hE
  have hEel : IsElemAbelian p E := isElemAbelian_sup_zpowers_of_le_centralizer hXbel hXbz hzbp
  have hEz : ∀ e ∈ E, ∃ x ∈ Xb, ∃ m : ℕ, e = x * zb ^ m := fun e he =>
    exists_mul_pow_of_le_centralizer hXbz he
  have hEp : IsPGroup p E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 e e.2)⟩
  have hX2 : 2 ≤ CFSG.Open.pRank p Xb :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp Xb)
      ⟨Xb, le_rfl, hXbel, hXbcard⟩
  have hE3 : 3 ≤ CFSG.Open.pRank p E :=
    hX2.trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers Xb hzbp hzb1 hzbC
        (zpowers_inf_eq_bot_of_not_mem' hp hzbord hzbX)))
  have hEB : E ≤ B := sup_le (barM_mono hXK)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzK)))
  have hEL : ∀ i, E ≤ Subgroup.normalizer (Lb i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun i =>
    sup_le (barM_le_normalizer_barM (hXL _ (hLg i)))
      (Subgroup.zpowers_le.mpr (mem_normalizer_barM hzM (hzL _ (hLg i))))
  have hzLb : ∀ i, zb ∉ Subgroup.centralizer (Lb i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun i =>
    not_mem_centralizer_of_perfect hZ (hLbC i)
  have hy : ∀ i, ∃ y ∈ E, y ∈ Lb i ∧ y ≠ 1 ∧ y ^ p = 1 := by
    intro i
    obtain ⟨j, hjLB, hjc⟩ :=
      h3.exists_inner_mem_barM h84 h86 hD2 hSch (hLg i) hDp hDK (hDL _ (hLg i)) hzD
    exact exists_pElem_inf_component hEp hEel.1 hE3 hB hEB (hEL i)
      (fun w hw hwC hwp => hZc i w hw.1 hwC hwp)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers zb)) hzbp (hzLb i) hjLB hjc
  set u := mk ⟨t ^ 3, M.pow_mem htM 3⟩ with hu
  have huL : ∀ i, u ∈ Subgroup.normalizer (Lb i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro i
    refine mem_normalizer_barM (M.pow_mem htM 3) ?_
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom).map (MulAut.conj (t ^ 3)).toMonoidHom =
      L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom
    have h3' : L.map (MulAut.conj (t ^ 3)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht3
    rw [← hmm, ← pow_add, add_comm, pow_add, hmm, h3']
  have huz : u * zb = zb * u := by
    rw [hu, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Commute.pow_left htz 3).eq)
  have hux : ∀ x ∈ Xb, u * x * u⁻¹ = x ^ l := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    rw [hu, ← map_pow, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using htl x (Subgroup.mem_subgroupOf.mp hxX))
  exact false_of_three_components_scalar (L := Lb) hLbC hLne hZc hEel.1 le_sup_left hXbcard
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers zb)) hEz hzbp hzLb huL huz hux hl hl0 hy

end CFSG.AGLEmbedding
