module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem528

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four
open CFSG.Quasithin.Vol2.Ch11.SecA CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt5_2_8_special_of_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h526 : Stmt5_2_6_F4)
    (h312 : A312ForSQTK) (hExc : FactExcParabolicO2Ne) (hG24 : FactG24ParabolicCenter)
    (hXG : FactX3ParabolicG2) (hAut : AutA7Fact) : Stmt5_2_8_special_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp Kh hlt hKh hc
  have h := hyp.toHyp5_0_1
  have hn : 2 ≤ n := h.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL₂K, hcore, -, -, -, hKT, halt⟩ := h526 G T M L V H B D L₂ n hyp
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  have hKloc : quasithinIsLocal T K := hyp.isLocal_oTwoUpper hL₂K
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have e : Emb528 T K Kh := ⟨h.qtke, h.simple, h.nonabelian, h.sylow, hKloc, hKh.1, hlt.le, hTN⟩
  have hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh :=
    e.charTwo_Kh h37
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hQKh : Q ≤ Kh := hQK.trans hlt.le
  have hST : sec52S M H ≤ T := h.pCoreOf_inf_le hyp.hStar.1.1

  have hcardK_of : ∀ {f : ℕ}, Nat.card (GaloisField 2 f) = 2 ^ f →
      (ModO2 K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) →
        Nat.card K = 2 ^ f * oSL2 f * Nat.card Q := by
    intro f hFc eK
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    congr 1
    · rw [show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card (ModO2 K) from rfl,
        Nat.card_congr eK.toEquiv, card_SL_two hFc]
    · try with_reducible rfl
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm

  have hG₂Q : sec52G2 M H D L₂ ≤ Subgroup.normalizer (Q : Set G) := by
    have h1 : sec52G2 M H D L₂ ≤ Subgroup.normalizer (K : Set G) := by
      rw [hcore]
      exact Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
    exact h1.trans (normalizer_le_normalizer_pCoreOf 2 K)

  have hRKS : pCoreOf 2 Kh ≤ pCoreOf 2 (K ⊔ sec52S M H) := by
    have h1 := e.pCoreOf_le_pCoreOf_KT h37
    rwa [hKT] at h1

  have hq4 : ∀ (hsp4 : IsSpecialPow 2 4 2 ↥Q),
      (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .G2 0 2) ∨
        IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSU 4 2) ∨
        IsU4ExtTwo 2 (sec52Alpha M L H B D L₂)) →
      Q ≤ pCoreOf 2 Kh → Kh ≤ Subgroup.normalizer (Q : Set G) →
      Nat.card (pCoreOf 2 Kh) ≤ 2 ^ 11 →
      (ModO2 K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) →
      (IsAlt 7 ↥(modO2Image (Kh ⊔ T) Kh) ∨
        IsHat ↥(modO2Image (Kh ⊔ T) Kh) (alternatingGroup (Fin 7)) ∨
        IsPSL 2 5 2 ↥(modO2Image (Kh ⊔ T) Kh) ∨
        (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          IsPSL 2 p 1 ↥(modO2Image (Kh ⊔ T) Kh)) ∨
        IsSporadic .J1 ↥(modO2Image (Kh ⊔ T) Kh) ∨ IsSporadic .J4 ↥(modO2Image (Kh ⊔ T) Kh)) →
      False := by
    intro hsp4 hα4 hQR hKhQ hR11 eK hL
    obtain ⟨hQQ, hZ4⟩ := commutator_eq_centerOf_of_isSpecialPow (by norm_num) (by norm_num) hsp4
    have hsp4' : IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
      rw [← hcore]
      exact hsp4
    obtain ⟨x, hxG₂, hx3, hxk⟩ :=
      exists_x3_of_amalgam hXG U4Par.factX3ParabolicU4_holds hα4 hsp4'
    rw [← hcore] at hxk
    have hcardK : Nat.card K = 60 * Nat.card Q := by
      rw [hcardK_of (GaloisField.card 2 2 (by norm_num)) eK]
      rfl
    exact false_of_q4 h37 h38 h39 hAut e hKh hQR hKhQ hR11 hQQ hZ4 hcardK hx3 (hG₂Q hxG₂) hxk hL
  rcases hc with ⟨hα, -, hKq, hsp, -⟩ | ⟨hα, -, -, hKq, hsp⟩ |
      ⟨⟨m, hnm, h2n, hαU, -, hKq, hsp⟩, hKhQ⟩
  ·
    obtain ⟨eK⟩ := exists_sl2_of_isL2Quot hKq
    have hFc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hsp' : IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
      rw [← hcore]
      exact hsp
    obtain ⟨hQQ, -⟩ := commutator_eq_centerOf_of_isSpecialPow (by norm_num)
      (Nat.le_self_pow (by omega) 2) hsp
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    ·
      obtain ⟨hcent, hctr⟩ := center_of_amalgam hG24 hα hsp'
      rw [← hcore] at hcent hctr
      have hRQ : pCoreOf 2 Kh ≤ Q := by
        rcases halt with ⟨-, -, -, hKS⟩ | ⟨m, -, h2n, -⟩
        · rw [hKS] at hRKS
          exact hRKS
        · omega
      have hRZ : ¬ pCoreOf 2 Kh ≤ centerOf Q := by
        intro hle
        have hKcR : K ≤ Subgroup.centralizer (pCoreOf 2 Kh : Set G) :=
          hcent.trans (Subgroup.centralizer_le hle)
        have hKR : K ≤ pCoreOf 2 Kh := fun k hk =>
          hchar (Subgroup.mem_inf.mpr ⟨e.le hk, hKcR hk⟩)
        exact e.not_isPGroup ((pCoreOf_isPGroup 2 Kh).to_le hKR)
      have hZR := hctr _ hRQ (e.le.trans (le_normalizer_pCoreOf 2 Kh)) hRZ
      have hQR : Q ≤ pCoreOf 2 Kh := by
        refine le_of_stabilizes hchar hQKh ?_ ?_
        · intro q hq
          refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZR hc)).2 q hq).symm
        · intro q hq r hr
          have hrQ : r ∈ Q := hRQ hr
          have hc1 : q * r * q⁻¹ * r⁻¹ ∈ centerOf Q := by
            rw [← hQQ]
            exact Subgroup.commutator_mem_commutator hq hrQ
          have hc2 : q * r * q⁻¹ * r⁻¹ ∈ pCoreOf 2 Kh := by
            rw [show q * r * q⁻¹ * r⁻¹ = (q * r * q⁻¹) * r⁻¹ from rfl]
            exact mul_mem ((Subgroup.mem_normalizer_iff.mp
              (le_normalizer_pCoreOf 2 Kh (hQKh hq)) r).mp hr) (inv_mem hr)
          refine Subgroup.mem_inf.mpr ⟨hc2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
          exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc1).2 s (hRQ hs)
      have hReq : pCoreOf 2 Kh = Q := le_antisymm hRQ hQR
      obtain ⟨-, hL⟩ := a312_list_of_le h37 h312 hExc e hlt hKh hQR le_rfl hFc eK
      have hR11 : Nat.card (pCoreOf 2 Kh) ≤ 2 ^ 11 := by
        rw [hReq, hsp.2.1]
        norm_num
      exact hq4 hsp (Or.inl hα) hQR (hReq ▸ le_normalizer_pCoreOf 2 Kh) hR11 eK hL
    ·
      obtain ⟨hcent, hirr⟩ := irred_of_amalgam NQCat.D4Irred.factG2D4ParabolicIrred_holds
        (Or.inl ⟨h3, hα, hsp'⟩)
      rw [← hcore] at hcent hirr
      have hQR := e.le_pCoreOf_of_irred h37 hQQ hcent hirr
      obtain ⟨hn2, -⟩ := a312_list_of_le h37 h312 hExc e hlt hKh hQR hn hFc eK
      omega
  ·
    obtain ⟨eK⟩ := exists_sl2_of_isL2Quot hKq
    have hFc : Nat.card (GaloisField 2 (3 * n)) = 2 ^ (3 * n) :=
      GaloisField.card 2 (3 * n) (by omega)
    have hsp' : IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
      rw [← hcore]
      exact hsp
    obtain ⟨hQQ, -⟩ := commutator_eq_centerOf_of_isSpecialPow (by norm_num)
      (Nat.le_self_pow (by omega) 2) hsp
    obtain ⟨hcent, hirr⟩ := irred_of_amalgam NQCat.D4Irred.factG2D4ParabolicIrred_holds
      (Or.inr ⟨by omega, hα, hsp'⟩)
    rw [← hcore] at hcent hirr
    have hQR := e.le_pCoreOf_of_irred h37 hQQ hcent hirr
    obtain ⟨h32, -⟩ := a312_list_of_le h37 h312 hExc e hlt hKh hQR (by omega) hFc eK
    omega
  ·
    have hQR : Q ≤ pCoreOf 2 Kh :=
      le_pCoreOf_of_le_normalizer 2 hQKh hKhQ (pCoreOf_isPGroup 2 K)
    obtain ⟨eK⟩ := exists_sl2_of_isL2Quot hKq
    have hFc : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
    obtain ⟨hm2, hL⟩ := a312_list_of_le h37 h312 hExc e hlt hKh hQR (by omega) hFc eK
    subst hm2

    have hQcard : Nat.card Q = 2 ^ 10 := by
      rw [hsp.2.1]
      norm_num
    have hR11 : Nat.card (pCoreOf 2 Kh) ≤ 2 ^ 11 := by
      refine (Subgroup.card_le_of_le hRKS).trans ?_
      rcases halt with ⟨-, -, -, hKS⟩ | ⟨m', hnm', -, -, t, ht2, -, hKS, -⟩
      · rw [hKS, hQcard]
        norm_num
      · rw [hKS, sup_comm]
        have htN : Subgroup.zpowers t ≤ Subgroup.normalizer (Q : Set G) := by
          rw [Subgroup.zpowers_le]
          have htKS : t ∈ K ⊔ sec52S M H :=
            (pCoreOf_le 2 _) (hKS ▸ (le_sup_right : Subgroup.zpowers t ≤ Q ⊔ _)
              (Subgroup.mem_zpowers t))
          exact (sup_le (le_normalizer_pCoreOf 2 K)
            ((hST.trans hTN).trans (normalizer_le_normalizer_pCoreOf 2 K))) htKS
        refine (card_sup_le_mul_of_normalizes htN).trans ?_
        rw [Nat.card_zpowers, ht2, hQcard]
        norm_num
    exact hq4 hsp (Or.inr hαU) hQR hKhQ hR11 eK hL

end CFSG.Quasithin.H13
