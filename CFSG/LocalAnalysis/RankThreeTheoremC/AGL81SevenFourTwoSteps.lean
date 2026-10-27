module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoBase
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
import CFSG.RankThree.GroupTheory.SteinbergCEPlaneNormalizerCentralizes
import CFSG.GroupTheory.PGroupNormalCommutator

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (SevenOneThree IsPClosedMod)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

private theorem exists_mul_ne_mul {D : Subgroup X} (hD : IsExtraspecialExpP p D) :
    ∃ a b : D, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact hD.1 ⟨⟨h⟩⟩

private theorem card_center_of_isExtraspecialExpP [Fact p.Prime] {D : Subgroup X}
    (hD : IsExtraspecialExpP p D) : Nat.card (Subgroup.center D) = p :=
  (center_structure_of_card_eq_pow_three hD.2.1 (exists_mul_ne_mul hD)).1

private theorem pRank_le_one_of_card_dvd {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    {H : Subgroup G} (hH : Nat.card H ∣ p) : Open.pRank p H ≤ 1 := by
  obtain ⟨E, hEH, -, hEc⟩ := pRank_attained p hp H
  have h : p ^ Open.pRank p H ∣ p ^ 1 := by
    rw [pow_one, ← hEc]
    exact (Subgroup.card_dvd_of_le hEH).trans hH
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h

theorem le_normalizer_map_subtype {N : Subgroup X} {K : Subgroup N} (hK : K.Normal) :
    N ≤ Subgroup.normalizer ((K.map N.subtype : Subgroup X) : Set X) := by
  intro n hn
  apply Subgroup.le_normalizer_map N.subtype (H := K)
  refine ⟨⟨n, hn⟩, ?_, rfl⟩
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top _

theorem exists_extraspecial_of_not_normalizer_le (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p X)
    {Y Q : Subgroup X} (hPY : (P : Subgroup X) ≤ Y) (hW : GLBWeakCore p (P : Subgroup X) ≤ Y)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup X)) (hQP : Q ≤ P)
    (hPQ : (P : Subgroup X) ≤ Subgroup.normalizer (Q : Set X)) (hQ2 : Open.pRank p Q = 2)
    (hQY : ¬ Subgroup.normalizer (Q : Set X) ≤ Y) :
    ∃ D : Subgroup X, D ≤ Q ∧
      Subgroup.normalizer (Q : Set X) ≤ Subgroup.normalizer (D : Set X) ∧
        IsExtraspecialExpP p D := by
  obtain ⟨D, hDQ, hND, -, hD⟩ :=
    pGroupRankTwoCharSubgroup p hp hp2 Q (P.isPGroup'.to_le hQP) hQ2
  rcases hD with ⟨hDe, hDc⟩ | hD
  · exact absurd (hND.trans (normalizer_le_of_normal_elemAbelian_sq hp P hPY hW h3 hDe hDc
      (hDQ.trans hQP) (hPQ.trans hND))) hQY
  · exact ⟨D, hDQ, hND, hD⟩

theorem exists_normal_elemAbelian_sq_le [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p X)
    {D : Subgroup X} (hDP : D ≤ P) (hPD : (P : Subgroup X) ≤ Subgroup.normalizer (D : Set X))
    (hD : IsExtraspecialExpP p D) :
    ∃ E : Subgroup X, E ≤ D ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (Subgroup.center D).map D.subtype ≤ E ∧
      (P : Subgroup X) ≤ Subgroup.normalizer (E : Set X) := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hED, hEc, hEn⟩ := CFSG.GroupTheory.exists_le_normal_card_eq
    (S := (P : Subgroup X)) (Y := D) P.isPGroup' hDP
    (fun s hs y hy => (Subgroup.mem_normalizer_iff.mp (hPD hs) y).mp hy) (k := 2)
    (by rw [hD.2.1]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
  have hPE : (P : Subgroup X) ≤ Subgroup.normalizer (E : Set X) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hEn s hs y, fun hy => ?_⟩
    have := hEn s⁻¹ (inv_mem hs) _ hy
    simpa [mul_assoc] using this
  refine ⟨E, hED, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hEc,
    fun x hx => hD.2.2 x (hED hx)⟩, hEc, ?_, hPE⟩
  have : (E.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hED).mpr (hDP.trans hPE)
  have hcard : Nat.card (E.subgroupOf D) = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
  have hne : E.subgroupOf D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have : Group.IsNilpotent D := (IsPGroup.of_card hD.2.1).isNilpotent
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hZ := card_center_of_isExtraspecialExpP hD
  have hdvd : Nat.card (E.subgroupOf D ⊓ Subgroup.center D : Subgroup D) ∣ p :=
    hZ ▸ Subgroup.card_dvd_of_le inf_le_right
  have hp' : Nat.card (E.subgroupOf D ⊓ Subgroup.center D : Subgroup D) = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hmeet
    · exact h
  have heq : E.subgroupOf D ⊓ Subgroup.center D = Subgroup.center D :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hZ, hp'])
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ E.subgroupOf D ⊓ Subgroup.center D := by
    rw [heq]
    exact hz
  exact Subgroup.mem_subgroupOf.mp hz'.1

theorem isCyclic_inf_centralizer_of_not_le (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p X)
    {Y D : Subgroup X} (hW : GLBWeakCore p (P : Subgroup X) ≤ Y) (hDP : D ≤ P)
    (hD : IsExtraspecialExpP p D) (hDY : ¬ Subgroup.normalizer (D : Set X) ≤ Y) :
    IsCyclic ((P : Subgroup X) ⊓ Subgroup.centralizer (D : Set X) : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  apply hDY
  obtain ⟨A, hAD, hA, hAc⟩ := exists_isElemAbelian_card_sq_of_card_cube hD.2.1 hD.2.2
  have h2 : 2 ≤ Open.pRank p D := le_csSup (pRank_bddAbove p hp D) ⟨A, hAD, hA, hAc⟩
  obtain ⟨F, hFC, hF, hFc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp
    (two_le_pRank_of_isPGroup_not_isCyclic hp hp2 (P.isPGroup'.to_le inf_le_left) hnc)
  obtain ⟨t, htF, htD⟩ : ∃ t ∈ F, t ∉ D := by
    by_contra h
    push Not at h
    have hFZ : F.subgroupOf D ≤ Subgroup.center D := fun f hf =>
      Subgroup.mem_center_iff.mpr fun d => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hFC hf).2 d d.2)
    have hle := Subgroup.card_le_of_le hFZ
    rw [card_center_of_isExtraspecialExpP hD,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, hFc] at hle
    have : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have htp : orderOf t = p := orderOf_eq_prime (hF.2 t htF) fun h => htD (h ▸ D.one_mem)
  have h3 : 3 ≤ Open.pRank p (D ⊔ ((P : Subgroup X) ⊓ Subgroup.centralizer (D : Set X))) :=
    three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hA hAc htp (fun h => htD (hAD h))
      (Subgroup.centralizer_le hAD (hFC htF).2) (hAD.trans le_sup_left)
      (Subgroup.mem_sup_right (hFC htF))
  exact (normalizer_le_weakCore p hDP h2 h3).trans hW

theorem exists_coords [Fact p.Prime] {D : Subgroup X} (hD : IsExtraspecialExpP p D) :
    Nonempty (D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p)) :=
  (center_structure_of_card_eq_pow_three hD.2.1 (exists_mul_ne_mul hD)).2.2

theorem pRank_le_three_of_not_le [Fact p.Prime] (P : Sylow p X) {Y D : Subgroup X}
    (e : D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p))
    (hPD : (P : Subgroup X) ≤ Subgroup.normalizer (D : Set X))
    (hW : GLBWeakCore p (P : Subgroup X) ≤ Y)
    (hker : (centerQuotientAction D e).ker.map (Subgroup.normalizer (D : Set X)).subtype ≤ Y)
    (hDY : ¬ Subgroup.normalizer (D : Set X) ≤ Y) : Open.pRank p (P : Subgroup X) ≤ 3 := by
  have hp : p.Prime := Fact.out
  set N := Subgroup.normalizer (D : Set X) with hN
  set ψ := centerQuotientAction D e with hψ
  have hK2 : Open.pRank p ((P : Subgroup X) ⊓ ψ.ker.map N.subtype) ≤ 2 := by
    by_contra h
    refine hDY (le_of_frattini P hPD (Subgroup.map_subtype_le _)
      (le_normalizer_map_subtype ψ.normal_ker) hker ?_)
    exact (normalizer_le_weakCore p inf_le_left (by omega)
      ((by omega : 3 ≤ _).trans (pRank_mono p hp le_sup_left))).trans hW
  set P' : Subgroup N := (P : Subgroup X).subgroupOf N with hP'
  have hP'map : P'.map N.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPD
  have hinf : (P' ⊓ ψ.ker).map N.subtype = (P : Subgroup X) ⊓ ψ.ker.map N.subtype := by
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hP'map]
  have h1 := pRank_le_pRank_inf_ker_add_pRank_map hp ψ P'
  have h2 : Open.pRank p (P'.map ψ) ≤ 1 := by
    have hpg : IsPGroup p P' := P.isPGroup'.comap_subtype
    exact pRank_le_one_of_card_dvd hp
      (CFSG.RankThree.GroupTheory.card_dvd_prime_of_isPGroup_GL_two (Nat.card_zmod p) (hpg.map ψ))
  rw [← pRank_map_of_injective p hp N.subtype N.subtype_injective P', hP'map,
    ← pRank_map_of_injective p hp N.subtype N.subtype_injective (P' ⊓ ψ.ker), hinf] at h1
  omega

@[expose] def SevenOneThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X, CFSG.IsComponent L →
    L.Normal → Open.pRank 3 L = 2 → Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
      IsPClosedMod 3 (L ⊔ Subgroup.centralizer (L : Set X))

theorem sevenOneThreeRankTwo_of (h : SevenOneThree) : SevenOneThreeRankTwo :=
  fun X _ _ hK L hL hLn _ h3 => h X hK 3 Nat.prime_three (by norm_num) L hL hLn (Or.inr (Or.inr h3))

theorem top_le_of_three (h713 : SevenOneThreeRankTwo) (hX : CatalogSimpleSections X)
    (P : Sylow 3 X) {Y L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hL3 : Open.pRank 3 L = 2) (hLY : L ≤ Y) (hCY : Subgroup.centralizer (L : Set X) ≤ Y)
    (hW : GLBWeakCore 3 (P : Subgroup X) ≤ Y) (h3 : 3 ≤ Open.pRank 3 (P : Subgroup X))
    (h3' : Open.pRank 3 (P : Subgroup X) ≤ 3) : ⊤ ≤ Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : Open.pRank 3 (⊤ : Subgroup X) ≤ 3 := by
    rw [← pRank_sylow_eq_globalRank 3 Nat.prime_three P]
    exact h3'
  have htop := (h713 X (catalogSimpleSections_iff_isKGroup.mp hX) L hL hLn hL3
    hr).sup_normalizer_eq_top P
  have hN : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤ Y :=
    (normalizer_le_weakCore_of_rank 3 Nat.prime_three (P : Subgroup X) h3).trans hW
  calc (⊤ : Subgroup X) = L ⊔ Subgroup.centralizer (L : Set X) ⊔
        Subgroup.normalizer ((P : Subgroup X) : Set X) := htop.symm
    _ ≤ Y := sup_le (sup_le hLY hCY) hN

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
