module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74L38Spin

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
open CFSG.OddStandard.Solomon75
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem connected_of_normalizes {T P : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
    (hP : IsPGroup 2 P) (hTP : T ≤ P) (hnorm : ∀ x ∈ P, ∀ y ∈ T, x * y * x⁻¹ ∈ T) :
    ∀ U V : FourSub P, Relation.ReflTransGen (FourAdj P) U V := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  obtain ⟨hzT, htT⟩ := spinZ_mem_of_isSylowIn hp hp2 hK hT
  have hztne : spinZ K ≠ tSeven K := fun h => htc (h ▸ hzc)
  have hcz : ∀ g : spinGroup (quadOdd 3 K), Commute (spinZ K) g := fun g =>
    (mem_center_iff.mp hzc g).symm
  let mk : ∀ v : spinGroup (quadOdd 3 K), v ∈ P → v * v = 1 → v ≠ 1 → v ≠ spinZ K →
      FourSub P := fun v hvP hvv hv1 hvz =>
    ⟨four (spinZ K) v hzz hvv (hcz v), four_le (hTP hzT) hvP,
      isElemAbelian_four _ _ hzz hvv (hcz v), card_four hzz hvv (hcz v) hz1 hv1 (Ne.symm hvz)⟩
  let H : FourSub P := mk (tSeven K) (hTP htT) htt ht1 (Ne.symm hztne)
  have hadj : ∀ (v : spinGroup (quadOdd 3 K)) (hvP : v ∈ P) (hvv : v * v = 1) (hv1 : v ≠ 1)
      (hvz : v ≠ spinZ K) (w : spinGroup (quadOdd 3 K)) (hwP : w ∈ P) (hww : w * w = 1)
      (hw1 : w ≠ 1) (hwz : w ≠ spinZ K), Commute v w →
      w ∉ four (spinZ K) v hzz hvv (hcz v) →
      FourAdj P (mk v hvP hvv hv1 hvz) (mk w hwP hww hw1 hwz) := by
    intro v hvP hvv hv1 hvz w hwP hww hw1 hwz hvw hwV
    have hcomm : ∀ c ∈ four (spinZ K) v hzz hvv (hcz v), Commute c w := fun c hc =>
      (commute_of_mem_four (hcz w).symm hvw.symm hc).symm
    obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers (isElemAbelian_four _ _ hzz hvv (hcz v))
      hww hwV hcomm
    refine ⟨four (spinZ K) v hzz hvv (hcz v) ⊔ zpowers w,
      sup_le (four_le (hTP hzT) hvP) (zpowers_le.mpr hwP), hE, ?_, le_sup_left,
      four_le (ha := hzz) (hb := hww) (hab := hcz w) (mem_sup_left left_mem_four)
        (mem_sup_right (mem_zpowers w))⟩
    rw [hEcard, card_four hzz hvv (hcz v) hz1 hv1 (Ne.symm hvz)]
  have hinT : ∀ (v : spinGroup (quadOdd 3 K)) (hvP : v ∈ P) (hvv : v * v = 1) (hv1 : v ≠ 1)
      (hvz : v ≠ spinZ K), v ∈ T →
      Relation.ReflTransGen (FourAdj P) (mk v hvP hvv hv1 hvz) H := by
    intro v hvP hvv hv1 hvz hvT
    by_cases hvt : v = tSeven K
    · subst hvt
      exact Relation.ReflTransGen.refl
    by_cases hvzt : v = spinZ K * tSeven K
    · have heq : mk v hvP hvv hv1 hvz = H := by
        apply Subtype.ext
        ext g
        change g ∈ four (spinZ K) v hzz hvv (hcz v) ↔
          g ∈ four (spinZ K) (tSeven K) hzz htt (hcz (tSeven K))
        rw [mem_four, mem_four, hvzt, ← mul_assoc, hzz, one_mul]
        tauto
      rw [heq]
    · refine Relation.ReflTransGen.single (hadj v hvP hvv hv1 hvz _ (hTP htT) htt ht1
        (Ne.symm hztne) ?_ ?_)
      · exact (mem_centralizer_singleton_iff.mp (hT.1 hvT))
      · intro h
        rcases mem_four.mp h with h | h | h | h
        · apply hvzt
          rw [h, ← mul_assoc, hzz, one_mul]
        · exact hztne h.symm
        · exact hvt h.symm
        · exact ht1 h
  have hall : ∀ (v : spinGroup (quadOdd 3 K)) (hvP : v ∈ P) (hvv : v * v = 1) (hv1 : v ≠ 1)
      (hvz : v ≠ spinZ K), Relation.ReflTransGen (FourAdj P) (mk v hvP hvv hv1 hvz) H := by
    intro v hvP hvv hv1 hvz
    by_cases hvT : v ∈ T
    · exact hinT v hvP hvv hv1 hvz hvT
    have hxt := conj_tSeven_eq hp hp2 hK h5 hT hP hTP hnorm hvP hvT
    obtain ⟨w, hwT, hww, hwv, hw1, hwz, -, -⟩ := exists_spinW hp hp2 hK h5 hT hvv hxt
      (hnorm v hvP)
    refine Relation.ReflTransGen.head (hadj v hvP hvv hv1 hvz w (hTP hwT) hww hw1 hwz
      hwv.symm ?_) (hinT w (hTP hwT) hww hw1 hwz hwT)
    intro h
    rcases mem_four.mp h with h | h | h | h
    · apply hvT
      have hv' : v = spinZ K * w := by rw [h, ← mul_assoc, hzz, one_mul]
      rw [hv']
      exact mul_mem hzT hwT
    · exact hwz h
    · exact hvT (h ▸ hwT)
    · exact hw1 h
  refine connected_of_hub H fun U => ?_
  obtain ⟨U, hUP, hUab, hU4⟩ := U
  by_cases hzU : spinZ K ∈ U
  · obtain ⟨v, hvU, hv1, hvz⟩ : ∃ v ∈ U, v ≠ 1 ∧ v ≠ spinZ K := by
      by_contra hcon
      push Not at hcon
      have hle : U ≤ zpowers (spinZ K) := fun g hg => by
        by_cases hg1 : g = 1
        · rw [hg1]
          exact one_mem _
        · rw [hcon g hg hg1]
          exact mem_zpowers _
      have h := Subgroup.card_le_of_le hle
      rw [hU4, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1] at h
      omega
    have hUeq := eq_four hUab hU4 hzU hvU hz1 hv1 (Ne.symm hvz)
    have heq : (⟨U, hUP, hUab, hU4⟩ : FourSub P) =
        mk v (hUP hvU) (mul_self_eq_one_of_isElemAbelian hUab hvU) hv1 hvz := Subtype.ext hUeq
    rw [heq]
    exact hall v (hUP hvU) (mul_self_eq_one_of_isElemAbelian hUab hvU) hv1 hvz
  · obtain ⟨v, hvU, hv1⟩ : ∃ v ∈ U, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hle : U ≤ ⊥ := fun g hg => (mem_bot).mpr (hcon g hg)
      have h := Subgroup.card_le_of_le hle
      rw [hU4, Subgroup.card_bot] at h
      omega
    have hvz : v ≠ spinZ K := fun h => hzU (h ▸ hvU)
    have hvv := mul_self_eq_one_of_isElemAbelian hUab hvU
    obtain ⟨hE, hEcard⟩ := isElemAbelian_sup_zpowers hUab hzz hzU fun c _ => (hcz c).symm
    refine Relation.ReflTransGen.head ⟨U ⊔ zpowers (spinZ K),
      sup_le hUP (zpowers_le.mpr (hTP hzT)), hE, ?_, le_sup_left,
      four_le (ha := hzz) (hb := hvv) (hab := hcz v) (mem_sup_right (mem_zpowers _))
        (mem_sup_left hvU)⟩ (hall v (hUP hvU) hvv hv1 hvz)
    rw [hEcard, hU4]

theorem spin_sylow_connected [Finite (spinGroup (quadOdd 3 K))]
    (hX : Nat.card (spinGroup (quadOdd 3 K)) =
      Nat.card K ^ 9 * ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1))))
    (P : Sylow 2 (spinGroup (quadOdd 3 K))) :
    (∀ U V : FourSub (P : Subgroup (spinGroup (quadOdd 3 K))),
      Relation.ReflTransGen (FourAdj (P : Subgroup (spinGroup (quadOdd 3 K)))) U V) ∧
      3 ≤ Open.pRank 2 (P : Subgroup (spinGroup (quadOdd 3 K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁⟩ := (inferInstance :
    Nonempty (Sylow 2 (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))))
  have hTsub : ((T₁ : Subgroup _).map (centralizer ({tSeven K} :
      Set (spinGroup (quadOdd 3 K)))).subtype).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) = T₁ :=
    comap_map_eq_self_of_injective (subtype_injective _) _
  have hT : IsSylowIn 2 ((T₁ : Subgroup _).map (centralizer ({tSeven K} :
      Set (spinGroup (quadOdd 3 K)))).subtype)
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) := by
    refine ⟨map_subtype_le _, T₁.isPGroup'.map _, ?_⟩
    change ¬ 2 ∣ (Subgroup.subgroupOf _ _).index
    rw [hTsub]
    exact Sylow.not_dvd_index T₁
  obtain ⟨P₀, hTP₀⟩ := hT.2.1.exists_le_sylow
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := id hodd
  have hcard : Nat.card (spinGroup (quadOdd 3 K)) =
      Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) *
        (2 * (Nat.card K ^ 6 * (2 * r * r + 2 * r + 1) *
          (Nat.card K ^ 4 + Nat.card K ^ 2 + 1))) := by
    rw [hX, card_centralizer_tSeven hp hp2 hK h5, hr]
    have h2' : 1 ≤ (2 * r + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4' : 1 ≤ (2 * r + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h6' : 1 ≤ (2 * r + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h2', h4', h6']
    ring
  have ho : Odd (Nat.card K ^ 6 * (2 * r * r + 2 * r + 1) *
      (Nat.card K ^ 4 + Nat.card K ^ 2 + 1)) :=
    (hodd.pow.mul ⟨r * r + r, by ring⟩).mul (hodd.pow.add_odd hodd.pow).add_one
  have hconn := connected_of_normalizes hp hp2 hK h5 hT P₀.isPGroup' hTP₀
    fun x hx y hy => conj_mem_of_card_sylow hT P₀ hTP₀ ho hcard hx hy
  obtain ⟨E, hET, hE, hE8⟩ := exists_eight_le hp hp2 hK h5 hT
  have hrank : 3 ≤ Open.pRank 2 (P₀ : Subgroup (spinGroup (quadOdd 3 K))) :=
    le_pRank_of_le (hET.trans hTP₀) hE hE8
  refine ⟨connected_of_mulEquiv (Sylow.equiv P₀ P) hconn, ?_⟩
  rw [← CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 2 Nat.prime_two _ _
    (Sylow.equiv P₀ P)]
  exact hrank

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
