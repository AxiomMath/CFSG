module

public import CFSG.Quasithin.H13.A7Nat1233LinB51
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1233K

public section

namespace CFSG.Quasithin.H13.A7.Lin

open CFSG.Open CFSG.Quasithin Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem lin_alt8_F4 (h1222 : Stmt12_2_2_F4)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) (h51 : AsB51)
    {T L V : Subgroup G} (hyp : Hyp1223 G T L V) (hS : Setting1233Four hyp) {z : G}
    (hzV : z ∈ V) (hz1 : z ≠ 1) (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hC28 : HypC28 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V) {K : Subgroup G}
    (hK : K ∈ cComp (hyp.Gv z)) (hlt : Kv hyp z < K) (hTK : T ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ hyp.Mv z) (hVK : V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), K⁆)
    (h4 : C41Case4 (hyp.Gv z) hyp.Q (hyp.Mv z) (Kv hyp z) V K) {W : Subgroup G}
    (hW : W = omegaOneCenterOf (pCoreOf 2 (K ⊔ hyp.Q))) [IsMulCommutative ↥W] :
    K ≤ normalizer (W : Set G) ∧ V ≤ ⁅W, K⁆ ∧ IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) ∧
      commV (autOn K W) ∈ IrrPlus (autOn K W) ⊤ ∧
      AlternatingNatural (autOn K W) (commV (autOn K W))
        (fixV (autOn K W) ⊓ commV (autOn K W)) 8 ∧
      Nat.card ↥(autOn K W) = 20160 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := hyp.Q with hQ

  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).1
  have hTz : T ≤ hyp.Gv z := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hzZ) t ht))
  have hQT : Q ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_le hyp.sylow le_sup_right)
  have hTQ : T ≤ normalizer (Q : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQK : Q ≤ normalizer (K : Set G) := hQT.trans hTK
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _

  obtain ⟨hsimp, hcardK⟩ := simple_of_isPSL_four_five h4.1
  have hnaK := nonabelian_of_card (X := ↥K ⧸ CFSG.pCore 2 ↥K) hcardK
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := isQuasisimple_of_simple hnaK

  have hz2 : orderOf z = 2 := orderOf_eq_prime (hC28.V_elem.2 z hzV) hz1
  have hKH : K ≤ hyp.Gv z := le_of_mem_cComp hK
  have hlocK : quasithinIsLocal T K :=
    ⟨hyp.sylow.1, cComp_subset_lFamily hTz hK, (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2,
      pCoreOf_ne_bot_of_le_centralizer hz2 ((le_sup_right : T ≤ K ⊔ T) (hZT hzZ))
        (sup_le hKH hTz)⟩
  have hcK : QuasithinUnique.CharTwo K := charTwo_of_isLocal hyp.qtke hyp.sylow hlocK

  obtain ⟨⟨-, -, hred⟩, ⟨-, hWe, -, A, hAQ, hAoff⟩, -⟩ :=
    hC27 G (hyp.Gv z) Q (hyp.Mv z) K W (c2_10_four hC28) hK hq hcK hKM hQK hW
  have hKQW : K ⊔ Q ≤ normalizer (W : Set G) := hred.2.1
  have hKW : K ≤ normalizer (W : Set G) := le_sup_left.trans hKQW

  obtain ⟨-, -, -, -, -, -, hVc⟩ := autOn_Kv_four_F4 h1222 hyp hS hzV hz1 hzZ
  have hVW : V ≤ W := hVK.trans (hW ▸ commutator_omegaOneCenter_le hQT hTK hTQ)
  have hVKW : V ≤ ⁅W, K⁆ := hVc.le.trans (commutator_mono hVW hlt.le)
  refine ⟨hKW, hVKW, ?_⟩

  have hnt : ¬ K ≤ centralizer (W : Set G) := by
    intro hc
    have hbot : ⁅W, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hc)
    have := hVKW hzV
    rw [hbot, mem_bot] at this
    exact hz1 this
  have hO2 : pCoreOf 2 (autOn (K ⊔ Q) W) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hYK : K ⊔ Q ≤ normalizer (K : Set G) := sup_le le_normalizer hQK
  have hO2L : pCoreOf 2 (autOn K W) = ⊥ := pCoreOf_autOn_eq_bot_of_le le_sup_left hYK hO2
  have hqa : CFSG.IsQuasisimple ↥(autOn K W) := InternalSec.isQuasisimple_autOn hKW hq hO2L hnt
  have hker : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) :=
    InternalSec.isPGroup_ker_of_simple hKW hsimp hO2L hnt
  have hSQK : SQTKGroup ↥K := B5.sqtk_of_le hC28.sqtk hKH
  have hSQa : SQTKGroup ↥(autOn K W) := InternalSec.sqtkGroup_autOn hKW hSQK hker
  have h2 : ∀ y ∈ K ⊔ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K ⊔ centralizer (W : Set G) := fun y hy => by
    obtain ⟨e, he⟩ := InternalSec.two_of_sup hQ2 hQK y hy
    exact ⟨e, mem_sup_left he⟩

  have hle := InternalSec.pCore_le_ker_autOnHom hKW hO2L
  set ρ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K W) :=
    QuotientGroup.lift _ (InternalSec.autOnHom hKW) hle with hρ
  have hρs : Function.Surjective ρ := fun y => by
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hKW y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hρker : ρ.ker ≠ ⊤ := by
    intro h
    apply InternalSec.ker_autOnHom_ne_top hKW hnt
    rw [eq_top_iff]
    intro l _
    have : (QuotientGroup.mk l : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ ρ.ker := by rw [h]; trivial
    exact this
  have hρi : Function.Injective ρ := by
    have := hsimp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ).1 h
    · exact absurd h hρker
  set e := MulEquiv.ofBijective ρ ⟨hρi, hρs⟩ with he
  have hcard : Nat.card ↥(autOn K W) = 20160 ∨ Nat.card ↥(autOn K W) = 9999360 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcardK
  have hsa : IsSimpleGroup ↥(autOn K W) := by
    have := hsimp
    exact e.symm.isSimpleGroup
  have hna := nonabelian_of_card (X := ↥(autOn K W)) hcard

  have hLA := commutator_autOn_eq hKQW le_sup_left hYK h2 hO2 hsa hna
    (hAQ.trans (InternalSec.autOn_le_autOn_of_le le_sup_right)) hAoff.2.1
  obtain ⟨hB51, -⟩ := InternalSec.b51Hyp_ffJ_autOn hKQW le_sup_left hYK h2 hO2 hqa hSQa hAoff hLA
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hWe.2 w w.2)
  obtain ⟨-, hp2, -⟩ := h51 ↥W hW2 _ _ hB51

  have hzW : z ∈ W := hVW hzV
  have hzfix : (⟨z, hzW⟩ : ↥W) ∈ fixV (autOn K W) := by
    intro x hx
    obtain ⟨g, hgK, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [QuasithinUnique.Setup.coe_conjAct_apply]
    have hgz : (g : G) * z = z * g := mem_centralizer_singleton_iff.1 (hKH hgK)
    show (g : G) * z * (g : G)⁻¹ = z
    rw [hgz, mul_inv_cancel_right]
  have hzcomm : (⟨z, hzW⟩ : ↥W) ∈ commV (autOn K W) := by
    have h1 : z ∈ (commV (autOn K W)).map W.subtype := by
      rw [NQRigid.commV_autOn_map hKW]
      exact hVKW hzV
    obtain ⟨w, hw, hwz⟩ := mem_map.1 h1
    have : w = ⟨z, hzW⟩ := Subtype.ext hwz
    rwa [← this]
  have hne : fixV (autOn K W) ⊓ commV (autOn K W) ≠ ⊥ := by
    intro hb
    have : (⟨z, hzW⟩ : ↥W) ∈ fixV (autOn K W) ⊓ commV (autOn K W) := ⟨hzfix, hzcomm⟩
    rw [hb, mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  obtain ⟨hirr, hlist⟩ := hp2.2 (hp2.1.2 (Or.inl hne))
  refine ⟨hker, hirr, ?_⟩
  rcases hlist with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | hn | hn | hn | hn
  · exact (not_binaryNaturalSL_two1527d hcard hn).elim
  · exact (not_binaryNaturalSp4_1527d hcard hn).elim
  · exact (not_g2Natural1527d hcard hn).elim
  · refine (not_alternatingNatural1527d (n := 6) (by norm_num) ?_ hn).elim
    rcases hcard with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  · refine ⟨hn, ?_⟩
    rcases hcard with h | h
    · exact h
    · exact (not_alternatingNatural1527d (n := 8) (by norm_num)
        (by rw [h]; norm_num [Nat.factorial]) hn).elim
  · exact (not_g2NaturalDerived_one1527d hcard hn).elim
  · exact (not_binaryNaturalSL_three1527d hcard hn).elim

end CFSG.Quasithin.H13.A7.Lin
