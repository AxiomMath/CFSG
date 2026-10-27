module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace Hyp5_0_1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L : Subgroup G} {n : ℕ}

theorem lemma_5_1_5_two_F4 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hE : E22MSolvableFact) {H D : Subgroup G} (hH : IsHStar T M H)
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hq : ∃ K ∈ cComp H, E2.HasE22LieQuot K) :
    Group.IsSolvable ↥(H ⊓ M) ∧ ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
      B ≤ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmp, -⟩ := h.minParabolic_of_isHStar_F4 h331 hH
  obtain ⟨hnsolv, hsqtk⟩ := h.not_isSolvable_and_sqtk_of_lie hH hq
  have hsolv : Group.IsSolvable ↥(H ⊓ M) := hE G H T (H ⊓ M) hmp hsqtk hnsolv hq
  refine ⟨hsolv, ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = T ⊓ L := ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl : Subgroup G, Bl = borelL T L := ⟨_, rfl⟩
  have hSB : IsSylowTwoOf P Bl := by
    rw [hP, hBl]
    exact h.isSylowTwoOf_borel
  have hP2 : IsPGroup 2 P := hSB.2.1
  have hPB : P ≤ Bl := hSB.1
  have hBN : Bl ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP, hBl]
    exact inf_le_right
  have hHMP : H ⊓ M ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact h.inf_le_normalizer_inf_F4 h331 hR hH
  have hHMB : H ⊓ M ≤ Subgroup.normalizer (Bl : Set G) := by
    rw [hBl]
    exact h.inf_le_normalizer_borel_F4 h331 hR hH
  have hTHM : T ≤ H ⊓ M := le_inf hH.1.1 h.T_le
  have hPHM : P ≤ H ⊓ M := by
    rw [hP]
    exact inf_le_left.trans hTHM
  have hD' : Lin2.IsHallTwoPrimeOf D Bl := by
    rw [hBl]
    exact hD
  obtain ⟨U, hU⟩ := exists_isHallTwoPrimeOf_of_isSolvable hsolv
  have hUHM : U ≤ H ⊓ M := hU.1
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = U ⊔ Bl := ⟨_, rfl⟩
  have hUY : U ≤ Y := by
    rw [hY]
    exact le_sup_left
  have hBY : Bl ≤ Y := by
    rw [hY]
    exact le_sup_right
  have hPY : P ≤ Y := hPB.trans hBY
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := by
    rw [hY]
    exact sup_le (hUHM.trans hHMP) hBN
  have hYB : Y ≤ Subgroup.normalizer (Bl : Set G) := by
    rw [hY]
    exact sup_le (hUHM.trans hHMB) Subgroup.le_normalizer
  have hoddB : Odd (P.relIndex Bl) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSB.2.2)
  have hoddBY : Odd (Bl.relIndex Y) := by
    have hnorm : (Bl.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYB
    have h1 := Subgroup.relIndex_sup_right (H := U.subgroupOf Y) (K := Bl.subgroupOf Y)
    have hsup : U.subgroupOf Y ⊔ Bl.subgroupOf Y = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hUY hBY, ← hY, Subgroup.subgroupOf_self]
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hUY] at h1
    have h2 := Subgroup.relIndex_mul_card Bl U
    have hdvd : Bl.relIndex U ∣ Nat.card U := Dvd.intro _ h2
    show Odd (Bl.subgroupOf Y).index
    rw [h1]
    exact hU.2.1.of_dvd_nat hdvd
  have hoddY : Odd (P.relIndex Y) := by
    rw [← Subgroup.relIndex_mul_relIndex P Bl Y hPB hBY]
    exact hoddB.mul hoddBY
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP2
  have hcopY : Nat.Coprime (Nat.card P) (P.relIndex Y) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddY)
  obtain ⟨E, hEY, hEP, hEs, -, -⟩ := exists_complement_of_coprime hPY hYP hcopY
  have hEN : E ≤ Subgroup.normalizer (P : Set G) := hEY.trans hYP
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = P ⊔ U := ⟨_, rfl⟩
  have hPW : P ≤ W := by
    rw [hW]
    exact le_sup_left
  have hUW : U ≤ W := by
    rw [hW]
    exact le_sup_right
  have hWY : W ≤ Y := by
    rw [hW]
    exact sup_le hPY hUY
  have hPU : P ⊓ U = ⊥ := inf_eq_bot_of_odd_of_isPGroup hP2 hU.2.1
  have hoddW : Odd (P.relIndex W) := by
    have := Subgroup.relIndex_mul_relIndex P W Y hPW hWY
    exact hoddY.of_dvd_nat (Dvd.intro _ this)
  have hWE : P ⊔ (W ⊓ E) = W := by
    apply le_antisymm (sup_le hPW inf_le_left)
    calc W = W ⊓ (P ⊔ E) := by rw [hEs]; exact (inf_eq_left.mpr hWY).symm
      _ ≤ P ⊔ (W ⊓ E) := inf_sup_le_sup_inf hPW hEN
  have hWEP : P ⊓ (W ⊓ E) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left P inf_le_right).trans hEP.le)
  obtain ⟨x, hxP, hUx⟩ := exists_mem_conj_of_complements hPW (hWY.trans hYP) hP2 hoddW
    inf_le_left hWEP hWE hUW hPU hW.symm
  have hxY : x ∈ Y := hPY hxP
  have hinj : ∀ z : G, Function.Injective (MulAut.conj z).toMonoidHom :=
    fun z => (MulAut.conj z).injective
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup G, E' = E.map (MulAut.conj x).toMonoidHom := ⟨_, rfl⟩
  have hUE' : U ≤ E' := by
    rw [hUx, hE']
    exact Subgroup.map_mono inf_le_right
  have hPx : P.map (MulAut.conj x).toMonoidHom = P := map_conj_eq_of_mem_normalizer (hYP hxY)
  have hYx : Y.map (MulAut.conj x).toMonoidHom = Y :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hxY)
  have hE'Y : E' ≤ Y := by
    rw [← hYx, hE']
    exact Subgroup.map_mono hEY
  have hE'P : P ⊓ E' = ⊥ := by
    rw [← hPx, hE', ← Subgroup.map_inf _ _ _ (hinj x), hEP, Subgroup.map_bot]
  have hE's : P ⊔ E' = Y := by
    rw [← hPx, hE', ← Subgroup.map_sup, hEs, hYx]
  have hE'N : E' ≤ Subgroup.normalizer (P : Set G) := hE'Y.trans hYP
  have hBE : P ⊔ (Bl ⊓ E') = Bl := by
    apply le_antisymm (sup_le hPB inf_le_left)
    calc Bl = Bl ⊓ (P ⊔ E') := by rw [hE's]; exact (inf_eq_left.mpr hBY).symm
      _ ≤ P ⊔ (Bl ⊓ E') := inf_sup_le_sup_inf hPB hE'N
  have hBEP : P ⊓ (Bl ⊓ E') = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left P inf_le_right).trans hE'P.le)
  have hDP : P ⊓ D = ⊥ := by
    rw [inf_comm, hP]
    exact Hyp5_0_1.inf_eq_bot_of_isHall hD (h.sylow.1.to_le inf_le_left)
  have hDs : P ⊔ D = Bl := by
    rw [sup_comm, hP, hBl]
    exact h.borelL_eq_sup hD
  obtain ⟨y, hyP, hDy⟩ := exists_mem_conj_of_complements hPB hBN hP2 hoddB inf_le_left hBEP hBE
    hD'.1 hDP hDs
  have hyHM : y ∈ H ⊓ M := hPHM hyP
  refine ⟨U.map (MulAut.conj y).toMonoidHom, isHallTwoPrimeOf_map_conj hU hyHM, ?_⟩
  obtain ⟨E'', hE''⟩ : ∃ E'' : Subgroup G, E'' = E'.map (MulAut.conj y).toMonoidHom := ⟨_, rfl⟩
  have hBy : Bl.map (MulAut.conj y).toMonoidHom = Bl :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hPB hyP))
  have hYy : Y.map (MulAut.conj y).toMonoidHom = Y :=
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hPY hyP))
  have hD'' : D = Bl ⊓ E'' := by
    rw [hDy, Subgroup.map_inf _ _ _ (hinj y), hBy, hE'']
  have hE''Y : E'' ≤ Y := by
    rw [← hYy, hE'']
    exact Subgroup.map_mono hE'Y
  have hE''N : E'' ≤ Subgroup.normalizer ((Bl ⊓ E'' : Subgroup G) : Set G) :=
    (le_inf (hE''Y.trans hYB) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [hD'']
  have hUE'' : U.map (MulAut.conj y).toMonoidHom ≤ E'' := by
    rw [hE'']
    exact Subgroup.map_mono hUE'
  exact hUE''.trans hE''N

end Hyp5_0_1

theorem stmt5_1_5_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hE : E22MSolvableFact) :
    Stmt5_1_5_F4 := by
  intro G _ _ T M L H D n h hH hD
  obtain ⟨h1, h2⟩ := h.lemma_5_1_5_one_F4 h331 hR hH hD
  exact ⟨h1, h2, fun hq => h.lemma_5_1_5_two_F4 h331 hR hE hH hD hq⟩

end CFSG.Quasithin.H13
