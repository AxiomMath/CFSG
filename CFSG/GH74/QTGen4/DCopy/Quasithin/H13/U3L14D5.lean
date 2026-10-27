module

public import CFSG.Quasithin.H13.U3L14D5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem comm_U_P_F4 (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {p : ℕ} {P : Subgroup G} {x : G} (hD : DData T V Lp p P x) :
    ⁅conjClosure V₃ (A6.g1 T V), P⁆ ≠ ⊥ := by
  intro h
  have : Fact p.Prime := ⟨hD.prime⟩
  obtain ⟨-, hm⟩ := S.stepB_F4 h1336 h37 h38 h39
  have hPC : P ≤ centralizer (conjClosure V₃ (A6.g1 T V) : Set G) := by
    rw [commutator_eq_bot_iff_le_centralizer] at h
    exact le_centralizer_iff.1 h
  have hPY : P ≤ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) := by
    rw [hD.xi.1]
    exact oTwoUpper_mono hPC
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hD.prime.one_lt P
  have h1 := hm p hD.prime hD.odd E (hEP.trans hPY) hE
  rw [hEc] at h1
  have h2 : p ^ 2 ≤ p ^ CFSG.Open.pRank p P := Nat.pow_le_pow_right hD.prime.pos hD.rank
  have h3 : p < p ^ 2 := by
    have := hD.prime.two_le
    nlinarith
  omega

theorem isXf_P_F4 (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G))
    (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {p : ℕ} {P : Subgroup G} {x : G} (hD : DData T V Lp p P x) : IsXf P := by
  have : Fact p.Prime := ⟨hD.prime⟩
  have hPne : P ≠ ⊥ := by
    intro hb
    have h1 : (pCoreOf 2 P).relIndex P = 1 := by
      rw [hb]
      exact relIndex_bot_right _
    rcases hD.index with h | ⟨h, -⟩ <;> rw [h] at h1 <;>
      exact absurd h1 (Nat.one_lt_pow (by norm_num) hD.prime.one_lt).ne'
  have hPsub := isSubnormal_P hD
  have hX : IsXClass P := ⟨hPne, hD.xi.1, charTwo_of_isSubnormal' S.charTwo_G1 hPsub⟩
  refine ⟨hX, (a4_9 hX hPsub).1 fun h => ?_⟩
  apply S.comm_U_P_F4 h1336 h37 h38 h39 hD
  exact le_bot_iff.1 (h ▸ commutator_mono (S.U_omega hQ) le_rfl)

theorem isXiStarF_P_F4
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) (h1332 : Stmt13_3_2_F4)
    (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h139 : NQCore.Lemma139Two) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (h36c : Vol2Native.A36CoreForSQTKCat) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {p : ℕ} {P : Subgroup G} {x : G}
    (hD : DData T V Lp p P x) : IsXiStarF T P := by
  have : Fact p.Prime := ⟨hD.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := S.h13.simple
  have hXf := S.isXf_P_F4 hQ h1336 h37 h38 h39 hD
  have hXiF : IsXiF T P := ⟨hD.xi, hXf⟩
  refine ⟨⟨hD.xi, fun L' hL' hq hle => ?_⟩, hXf⟩

  have hPK : P ≤ conjClosure L' T := by
    rw [hD.xi.1]
    exact (oTwoUpper_mono (le_sup_left.trans hle)).trans (oTwoUpper_sup_le_conjClosure S.isP_T)
  have hfL := (h139 G S.h13.qtke S.h13.simple S.h13.nonabelian T P L' S.h13.sylow hXiF hL'
    hPK).2
  obtain ⟨hQ5, ⟨hTL, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 L' hfL
  have hKL : conjClosure L' T = L' :=
    le_antisymm (conjClosure_le fun t ht l hl => (mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L' T)
  have hPL : P ≤ L' := hKL ▸ hPK

  have hH : CFSG.SectionRank.IsSQTKCat ↥(L' ⊔ T) :=
    (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1 _ hL'.2.2.2
  have hS : IsSylowTwoOf T (L' ⊔ T) := S.syl le_sup_right
  have hPH : P ≤ L' ⊔ T := hPL.trans le_sup_left
  have hidx : ∃ k, (pCoreOf 2 P).relIndex P = p ^ k := by
    rcases hD.index with h | ⟨h, -⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨k, hk⟩ := hidx
  obtain ⟨R, hRP, hRp, hRc⟩ := exists_pSub_card_eq_relIndex hD.odd hk
  have key : L' ⊔ T ≤ normalizer (P : Set G) ∨
      ∃ K ∈ cComp (L' ⊔ T), P ≤ conjClosure K T ∧
        (¬ QT13Five (↥K ⧸ CFSG.pCore 2 ↥K) ∨ ¬ T ≤ normalizer (K : Set G)) := by
    have hp35 : p = 3 ∨ 5 ≤ p := by
      have h2 := hD.prime.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · have h34 : p = 3 ∨ p = 4 := by have := hD.odd; omega
        rcases h34 with h3 | h4
        · exact Or.inl h3
        · exfalso
          have := hD.prime
          rw [h4] at this
          norm_num at this
      · exact Or.inr h
    rcases hp35 with hp3 | hp5
    · subst hp3
      have h9 : (pCoreOf 2 P).relIndex P = 9 := hD.e9 rfl
      rcases h134 G (L' ⊔ T) T P R hH hL'.2.2.2 hS hPH hD.xi h9 hRP hRp (hRc.trans h9) with
        h | ⟨K, hK, -, hPK', hcases⟩
      · exact Or.inl h
      refine Or.inr ⟨K, hK, hPK', ?_⟩
      rcases hcases with ⟨⟨t, ht, htK, -⟩, -⟩ | ⟨-, h2⟩ | ⟨-, ⟨n, hn, h3⟩, -⟩ | ⟨-, h4⟩ |
          ⟨-, h5⟩
      · exact Or.inr fun hTK => htK (hTK (mem_inf.1 ht).1)
      · rcases h2 with h2 | h2
        · exact Or.inl (not_qt13Five_of_psl3 (by norm_num) h2)
        · exact Or.inl (not_qt13Five_of_sl3 (by norm_num) h2)
      · exact Or.inl (not_qt13Five_of_psp hn h3)
      · rcases h4 with h4 | h4 | h4
        · exact Or.inl (not_qt13Five_of_m11 h4)
        · exact Or.inl (not_qt13Five_of_psl_two (Or.inl rfl) h4)
        · exact Or.inl (not_qt13Five_of_psl_two (Or.inr rfl) h4)
      · exact Or.inl (not_qt13Five_of_he h5)
    · rcases NQCore.prop134_odd_case h36c h37c h38c NQCore.facts134Odd_proved hp5 hH hS hPH hD.xi
        hRP hRp hRc with
        h | ⟨K, hK, -, hPK', hcases⟩
      · exact Or.inl h
      refine Or.inr ⟨K, hK, hPK', ?_⟩
      rcases hcases with ⟨⟨t, ht, htK, -⟩, -⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, ⟨n, hn, -, h3⟩, -⟩ |
          ⟨-, h4, -⟩
      · exact Or.inr fun hTK => htK (hTK (mem_inf.1 ht).1)
      · rcases h2 with h2 | h2
        · exact Or.inl (not_qt13Five_of_psl3 hD.odd h2)
        · exact Or.inl (not_qt13Five_of_sl3 hD.odd h2)
      · exact Or.inl (not_qt13Five_of_psp hn h3)
      · omega
  rcases key with hN | ⟨K, hK, hPK', hbad⟩
  ·
    have hq' : CFSG.IsQuasisimple (↥L' ⧸ CFSG.pCore 2 ↥L') := hq
    set π' := QuotientGroup.mk' (CFSG.pCore 2 ↥L') with hπ'
    set Pb : Subgroup (↥L' ⧸ CFSG.pCore 2 ↥L') := (P.subgroupOf L').map π' with hPb
    have hPn : (P.subgroupOf L').Normal :=
      (normal_subgroupOf_iff_le_normalizer hPL).2 (le_sup_left.trans hN)
    have hPbn : Pb.Normal := hPn.map π' (QuotientGroup.mk'_surjective _)
    have hO2 : P ⊓ pCoreOf 2 L' = pCoreOf 2 P := by
      apply le_antisymm
      · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun y hy => mem_normalizer_inf (le_normalizer hy)
            (LieType.BorelTits.le_normalizer_pCoreOf 2 L' (hPL hy)))
          ((LieType.BorelTits.pCoreOf_isPGroup 2 L').to_le inf_le_right)
      · refine le_inf (LieType.BorelTits.pCoreOf_le 2 P) ?_
        exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((LieType.BorelTits.pCoreOf_le 2 P).trans hPL)
          ((le_sup_left.trans hN).trans
            (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P))
          (LieType.BorelTits.pCoreOf_isPGroup 2 P)
    set f : ↥P →* (↥L' ⧸ CFSG.pCore 2 ↥L') := π'.comp (inclusion hPL) with hf
    have hfrange : f.range = Pb := by
      ext γ
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨inclusion hPL y, mem_subgroupOf.2 y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
    have hfker : f.ker = (pCoreOf 2 P).subgroupOf P := by
      ext y
      rw [MonoidHom.mem_ker, mem_subgroupOf, ← hO2]
      show π' (inclusion hPL y) = 1 ↔ _
      rw [hπ', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← coe_mem_pCoreOf_iff]
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    have hcardPb : Nat.card Pb = (pCoreOf 2 P).relIndex P := by
      rw [← hfrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfker,
        relIndex, index_eq_card]
    have hp3 : 3 ≤ p := by have := hD.prime.two_le; have := hD.odd; omega
    have hp9 : 9 ≤ (pCoreOf 2 P).relIndex P := by
      have h9 : 9 ≤ p ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      rcases hD.index with h | ⟨h, -⟩
      · omega
      · have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq' hPbn with htop | hcen
    · have hc : Nat.card (↥L' ⧸ CFSG.pCore 2 ↥L') = p ^ k := by
        rw [← hk, ← hcardPb, htop, card_top]
      have hodd : Odd (p ^ k) := (hD.prime.odd_of_ne_two hD.odd).pow
      rw [← hc] at hodd
      rcases card_of_qt13Five hQ5 with h | h | h | h | h <;> rw [h] at hodd <;>
        exact absurd hodd (by decide)
    · have h1 := card_center_le_three_of_qt13Five hQ5
      have h2 : Nat.card Pb ≤ Nat.card (center (↥L' ⧸ CFSG.pCore 2 ↥L')) :=
        Subgroup.card_le_of_le hcen
      omega
  · have hKl := S.isLocal_of_mem_cComp hL' hK
    have hfK := (h139 G S.h13.qtke S.h13.simple S.h13.nonabelian T P K S.h13.sylow hXiF hKl
      hPK').2
    obtain ⟨hQ5K, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hfK
    rcases hbad with h | h
    · exact h hQ5K
    · exact h hTK

end Set14

end CFSG.Quasithin.H13.U3
