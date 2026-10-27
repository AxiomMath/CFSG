module

public import CFSG.GH74.Generic.BProg.B2.TwoA7Term
public import CFSG.GH74.Generic.BProg.B2.TwoA7Geo
import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.T1Basic
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.GH74.Uniqueness CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B2.SD.TwoA7Geo CFSG.GH74.Generic.BProg.B2.SD.TwoA7Term
open CFSG.GH74.Generic.BProg.B2

variable {G : Type} [Group G] [Finite G]

section Stage2

variable {x : G} {K A M P Q : Subgroup G}

theorem A_le_centralizer_u (hs : Stage2Setup G x K A M P Q) {u : G} (hu : u ∈ Q) :
    A ≤ centralizer ({u} : Set G) := by
  have hux : u ∈ centralizer ({x} : Set G) := (hs.Q_eq ▸ hu : u ∈ P ⊓ CxK x K).2.1
  obtain ⟨-, -, -, hcase⟩ := hs.src
  rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -, -, -, -⟩
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_Q_inf hs u hu a ⟨ha, hAK ha⟩).symm
  · have hEA : E ≤ A := hAE ▸ le_sup_left
    rw [hAE]
    refine sup_le (fun e he => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_Q_inf hs u hu e ⟨hEA he, hEK he⟩).symm
    · exact mem_centralizer_symm hux

theorem normalizer_inf_K_le_M (hs : Stage2Setup G x K A M P Q) :
    normalizer ((A ⊓ K : Subgroup G) : Set G) ≤ M := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have hAe3 : IsE 3 ⊤ A := ⟨le_top, hAel, hr3.ge⟩
  have hbal := hs.reg.1
  have hE : IsE 2 A (A ⊓ K) := isE_inf_K hs
  have h2 : normalizer ((A ⊓ K : Subgroup G) : Set G) ≤ gammaK 2 A 2 :=
    le_iSup₂_of_le (A ⊓ K) inf_le_left (le_iSup_of_le hE.2.2 le_rfl)
  exact fun g hg => hs.le_M ((gammaK_le_normalizer_thetaHalf_one hAe3 hbal.1 hbal.2) (h2 hg))

theorem exists_twoA7_pair {H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) {J : Subgroup (Mbar M)} (hJ : IsComponent J)
    (hdc : IsDoubleCoverOfAlt ↥J 7)
    (hJK : ∀ j ∈ J, ∀ k ∈ (barIn M K : Subgroup (Mbar M)), j * k = k * j)
    {u : G} (huQ : u ∈ Q) (hu2 : orderOf u = 2) (huM : u ∈ M)
    (huJ : (QuotientGroup.mk (⟨u, huM⟩ : ↥M) : Mbar M) ∈ J)
    (huJc : ∀ j ∈ J, (QuotientGroup.mk (⟨u, huM⟩ : ↥M) : Mbar M) * j =
      j * (QuotientGroup.mk (⟨u, huM⟩ : ↥M) : Mbar M)) :
    ∃ I : Subgroup G, IsILo 2 u I ∧ u ∈ I ∧
      IsDoubleCoverOfAlt (↥I ⧸ pPrimeCore 2 ↥I) 7 := by
  have hP2 : IsPGroup 2 ↥P := hs.sylowP.isPGroup
  have huPC : u ∈ P ⊓ CxK x K := hs.Q_eq ▸ huQ
  have huP : u ∈ P := huPC.1
  have hux : u ∈ centralizer ({x} : Set G) := huPC.2.1
  have huK : u ∈ centralizerSection K (pPrimeCoreOf 2 K) := huPC.2.2
  set E : Subgroup G := A ⊓ K with hE
  have hEP : E ≤ P := (inf_le_left : E ≤ A).trans hs.A_le
  have hE2 : IsPGroup 2 ↥E := hP2.to_le hEP
  have hcomE : ∀ a ∈ E, u * a = a * u := fun a ha => commute_Q_inf hs u huQ a ha
  set Hu : Subgroup G := centralizer ({u} : Set G) with hHu
  have hEHu : E ≤ Hu := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomE a ha).symm
  have hAHu : A ≤ Hu := A_le_centralizer_u hs huQ
  have hrank : oBound 2 ≤ pRank 2 ↥Hu := by
    obtain ⟨-, hAel, hAcard, -⟩ := hs.src
    have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
    have : oBound 2 = 3 := by simp [oBound]
    rw [this, ← hr3]
    exact CFSG.RankThree.PartOne.OddCore37.pRank_le_of_le Nat.prime_two hAHu
  have hterm : IsTwoTerminal x K := hs.pair.1.2.2
  obtain ⟨Λ, hΛX, hΛK, h2el, hL⟩ := pumpup_component_of_terminal hterm hu2 hux huK hrank
  have hEK : E ≤ K := inf_le_right
  have hKM : K ≤ M := h1.K_le
  have hYM : Hu ⊓ centralizer (E : Set G) ≤ M :=
    inf_le_right.trans ((Subgroup.centralizer_le_normalizer (E : Set G)).trans
      (normalizer_inf_K_le_M hs))
  set T : Subgroup G := E ⊔ zpowers u with hT
  have hTP : T ≤ P := sup_le hEP (Subgroup.zpowers_le.mpr huP)
  have hT2 : IsPGroup 2 ↥T := hP2.to_le hTP
  have hTM : T ≤ M := sup_le (hEK.trans hKM) (Subgroup.zpowers_le.mpr huM)
  have hJT : ∀ (t : G) (ht : t ∈ T), ∀ j ∈ J,
      barMk ↥M ⟨t, hTM ht⟩ * j = j * barMk ↥M ⟨t, hTM ht⟩ := by
    set C : Subgroup G := ((centralizer (J : Set (barQ ↥M))).comap (barMk ↥M)).map M.subtype
      with hC
    have hmemC : ∀ (t : G) (ht : t ∈ M),
        barMk ↥M ⟨t, ht⟩ ∈ centralizer (J : Set (barQ ↥M)) → t ∈ C :=
      fun t ht h => ⟨⟨t, ht⟩, h, rfl⟩
    have hCmem : ∀ t ∈ C, ∃ ht : t ∈ M, barMk ↥M ⟨t, ht⟩ ∈ centralizer (J : Set (barQ ↥M)) := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    have hEC : E ≤ C := fun e he => hmemC e (hKM (hEK he)) (by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact hJK j hj _ ⟨⟨e, hKM (hEK he)⟩, Subgroup.mem_subgroupOf.mpr (hEK he), rfl⟩)
    have huC : zpowers u ≤ C := Subgroup.zpowers_le.mpr (hmemC u huM (by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (huJc j hj).symm))
    intro t ht j hj
    obtain ⟨htM, hcen⟩ := hCmem t (sup_le hEC huC ht)
    exact (Subgroup.mem_centralizer_iff.mp hcen j hj).symm
  have huT : u ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hJY : ∀ j ∈ J, ∃ (y : G) (hy : y ∈ Hu ⊓ centralizer (E : Set G)),
      barMk ↥M ⟨y, hYM hy⟩ = j := by
    intro j hj
    obtain ⟨y, hy, hyj⟩ := le_image_centralizer_of_comm hTM hT2 hJT j hj
    have hyu : y ∈ centralizer ({u} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huT) hy.2
    have hyE : y ∈ centralizer (E : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_sup_left : E ≤ T)) hy.2
    exact ⟨y, Subgroup.mem_inf.mpr ⟨hyu, hyE⟩, hyj⟩
  obtain ⟨J₂, hJ₂c, hJ₂J, hJ₂2el, ⟨eJ₂⟩⟩ := exists_J₂ hYM hJ hJY
  have hJ₂Y : J₂ ≤ Hu ⊓ centralizer (E : Set G) := hJ₂c.1
  have hJ₂Hu : J₂ ≤ Hu := hJ₂Y.trans inf_le_left
  have hJ₂M : J₂ ≤ M := hJ₂Y.trans hYM
  have hΛM : Λ ≤ M := hΛK.trans hKM
  have hcommM : ∀ (j : G) (hj : j ∈ M), j ∈ J₂ → ∀ (l : G) (hl : l ∈ M), l ∈ Λ →
      barMk ↥M ⟨j, hj⟩ * barMk ↥M ⟨l, hl⟩ = barMk ↥M ⟨l, hl⟩ * barMk ↥M ⟨j, hj⟩ := by
    intro j hj hjJ l hl hlΛ
    exact hJK _ (hJ₂J j hj hjJ) _ ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.mpr (hΛK hlΛ), rfl⟩
  obtain ⟨N, hNodd, hNL, hNcomm⟩ := exists_odd_normalized (H := Hu) hΛM hcommM hJ₂M
  have hEL : ∀ (e : G) (he : e ∈ E), barMk ↥Hu ⟨e, hEHu he⟩ ∈
      (Λ.subgroupOf Hu).map (barMk ↥Hu) := by
    intro e he
    obtain ⟨n, hn⟩ := hE2 ⟨e, he⟩
    have hn' : e ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨⟨e, hEHu he⟩, h2el e (Subgroup.mem_inf.mpr ⟨he.2, hEHu he⟩) ⟨n, hn'⟩, rfl⟩
  obtain ⟨hDcomp, -⟩ := geo_component hE2 hEHu hJ₂c hL hEL hNodd hNL hNcomm
  have huHu : u ∈ Hu := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have huY : u ∈ Hu ⊓ centralizer (E : Set G) :=
    Subgroup.mem_inf.mpr ⟨huHu, Subgroup.mem_centralizer_iff.mpr fun a ha => (hcomE a ha).symm⟩
  have hu2el : ∃ n : ℕ, u ^ 2 ^ n = 1 := ⟨1, by
    have := pow_orderOf_eq_one u
    rwa [hu2] at this⟩
  have huJ₂ : u ∈ J₂ := hJ₂2el u huY huJ hu2el
  have huD : barMk ↥Hu ⟨u, huHu⟩ ∈ (J₂.subgroupOf Hu).map (barMk ↥Hu) := ⟨⟨u, huHu⟩, huJ₂, rfl⟩
  obtain ⟨I, hIc, huI, ⟨eI⟩⟩ := exists_lift_component hDcomp huHu hu2el huD
  obtain ⟨eD⟩ := equiv_image_of_equiv hJ₂Hu hDcomp eJ₂
  exact ⟨I, ⟨hu2, hrank, hIc⟩, huI,
    CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr (eI.trans eD).symm hdc⟩

end Stage2

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7

