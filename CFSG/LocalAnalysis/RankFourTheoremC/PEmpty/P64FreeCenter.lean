module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem mem_of_central_of_pRank_le_two (hp : p.Prime) {Q B : Subgroup A}
    (hQ : Open.pRank p Q ≤ 2) (hBQ : B ≤ Q) (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    {w : A} (hwQ : w ∈ Q) (hwp : w ^ p = 1) (hw : ∀ q ∈ Q, q * w = w * q) : w ∈ B := by
  by_contra hwB
  have hcomm : ∀ a ∈ B, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a w from hw a (hBQ ha)) k).eq
  have hel := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hB
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hwp) hcomm
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hel
  have hlt : B < B ⊔ zpowers w := by
    refine lt_of_le_of_ne le_sup_left fun h => hwB ?_
    rw [h]
    exact mem_sup_right (mem_zpowers w)
  have hcard := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [hBcard, hk] at hcard
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
    omega
  have hle : k ≤ Open.pRank p Q :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt
      (sup_le hBQ (zpowers_le.mpr hwQ)) hel hk
  omega

theorem pCore_le_sylow {X : Type*} [Group X] [Fact p.Prime] (S : Sylow p X) :
    CFSG.pCore p X ≤ S := by
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hsup : IsPGroup p ↥(CFSG.pCore p X ⊔ (S : Subgroup X)) :=
    (CFSG.pCore_isPGroup (p := p) (G := X)).to_sup_of_normal_left S.isPGroup'
  have h := S.is_maximal' hsup le_sup_right
  rw [← h]
  exact le_sup_left

theorem mem_pCoreOf_of_central (hp : p.Prime) {X Q : Subgroup A} (hQX : Q ≤ X)
    (hQ : IsPGroup p Q) (hQsyl : ¬ p ∣ (Q.subgroupOf X).index) (hZ : IsCyclic (center Q))
    (hO : pCoreOf p X ≠ ⊥) {w : A} (hwQ : w ∈ Q) (hwp : orderOf w = p)
    (hw : ∀ q ∈ Q, q * w = w * q) : w ∈ pCoreOf p X := by
  have : Fact p.Prime := ⟨hp⟩
  set S : Sylow p X := (hQ.comap_subtype (K := X)).toSylow hQsyl
  have hOQ : pCoreOf p X ≤ Q := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : u ∈ (S : Subgroup X) := pCore_le_sylow S hu
    simpa [S, mem_subgroupOf] using h1
  have hnorm : ∀ g ∈ Q, ∀ u ∈ pCoreOf p X, g * u * g⁻¹ ∈ pCoreOf p X := by
    rintro g hg _ ⟨u, hu, rfl⟩
    have hN : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
    exact ⟨⟨g, hQX hg⟩ * u * ⟨g, hQX hg⟩⁻¹, hN.conj_mem u hu _, rfl⟩
  obtain ⟨z, hzO, hz1, hzc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal hp hQ hOQ hnorm hO
  have hzQ : z ∈ Q := hOQ hzO
  obtain ⟨n, hn⟩ : ∃ n, orderOf (⟨z, hzQ⟩ : Q) = p ^ n := IsPGroup.iff_orderOf.mp hQ ⟨z, hzQ⟩
  rw [Subgroup.orderOf_mk] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hz1 hn
  have hpd : p ∣ orderOf z := hn ▸ dvd_pow_self p hn0
  have hz0 : orderOf z ≠ 0 := by rw [hn]; exact pow_ne_zero _ hp.ne_zero
  set z' := z ^ (orderOf z / p)
  have hz'o : orderOf z' = p := orderOf_pow_orderOf_div hz0 hpd
  have hz'O : z' ∈ pCoreOf p X := (pCoreOf p X).pow_mem hzO _
  have hz'Q : z' ∈ Q := hOQ hz'O
  have hz'c : ∀ g ∈ Q, g * z' = z' * g := fun g hg =>
    (Commute.pow_right (show Commute g z from hzc g hg) _).eq
  have hwZ : (⟨w, hwQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g =>
    Subtype.ext (hw g g.2)
  have hz'Z : (⟨z', hz'Q⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g =>
    Subtype.ext (hz'c g g.2)
  set w₀ : center Q := ⟨⟨w, hwQ⟩, hwZ⟩
  set z₀ : center Q := ⟨⟨z', hz'Q⟩, hz'Z⟩
  have hord : ∀ {y : A} (hy : y ∈ Q) (hyZ : (⟨y, hy⟩ : Q) ∈ center Q),
      orderOf (⟨⟨y, hy⟩, hyZ⟩ : center Q) = orderOf y := by
    intro y hy hyZ
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  have heq : zpowers w₀ = zpowers z₀ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hord, hord, hwp,
      hz'o]
  have hmem : w₀ ∈ zpowers z₀ := heq ▸ mem_zpowers w₀
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : z' ^ k = w := by
    have := congrArg (fun y : center Q => ((y : Q) : A)) hk
    simpa [w₀, z₀] using this
  rw [← hk']
  exact (pCoreOf p X).zpow_mem hz'O k

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
