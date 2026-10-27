module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Six
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3029
public import Certificates.Certificate17037
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9V
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action
  CFSG.QuasithinUnique.A5.Split

theorem exists_u9data
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) {z u : G} (s7 : A5Step7 T M H S L z u) :
    ∃ A V : Subgroup G, U9Data T M H S L z u A V := by
  have h27 : Lemma2_4_27Concl T H S L :=
    h247 G T M H S L cfg.cs (Or.inl ⟨cfg.alt5, cfg.single⟩)
  have hRx : ∀ x ∈ T, x ∉ S → baum S = blockU L ⊔ conjR (blockU L) x := by
    intro x hx hxS
    have h4 := (h27.2.2.2 x hx hxS).1
    rwa [s7.TC_one, bot_sup_eq, blockU0_eq_blockU cfg.single] at h4
  have key : ∀ (C : StdCfg T M H S L), Sec C → u = C.u0 →
      ∃ A V : Subgroup G, U9Data T M H S L z u A V := by
    intro C X hu0
    have hzz : z = C.zU := X.z_eq s7.z_gen
    refine ⟨X.A4W, X.V4W, ?_⟩
    exact
      { s7 := s7
        U_comm := fun a ha b hb => C.U_comm ha hb
        U_sq := fun a ha => cfg.cs.block.1.1.2.2.1.2 a ha
        A_eq := by rw [hu0]; exact X.pResidual_Hu.symm
        hA := X.isA4Block_A4W
        V_le := X.V4W_le_U
        uz_mem := by rw [hu0, hzz]; exact X.uz_mem_V4W
        R_eq := hRx
        Tu_card := by
          have h := X.card_Tu (hu0 ▸ s7.u_mem)
          rw [hu0]
          exact h
        U_card := C.card_U }
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  rcases X.exists_w_of_Z s7.u_mem s7.u_not with h | h
  · exact key C X h
  · let C' : StdCfg T M H S L :=
      C.relabel rho13 (fun σ hσ => rho13_conj_E σ hσ) (fun σ hσ => rho13_conj_E' σ hσ)
    obtain ⟨X'⟩ := exists_sec C' s7.TC_one
    have hu' : u = C'.u0 := by
      rw [h]
      show _ = ((C.iV (vact rho13⁻¹ g1w) : ↥H) : G)
      rw [rho13_inv, vact_rho13_g1w]
    exact key C' X' hu'

namespace U9Data

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V : Subgroup G}
  (D : U9Data T M H S L z u A V)

include D

theorem false_of_cover {K : Subgroup G} (hKG : K ≤ centralizerElem u)
    (hcov : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      Subgroup.center ↥K ≠ ⊥) : False := by
  have h8 := two_pow_eight_dvd_cover hcov
  have hKdvd : Nat.card ↥K ∣ Nat.card ↥(centralizerElem u) := Subgroup.card_dvd_of_le hKG
  have hsyl := D.s7.Tu_sylow
  have hcard := C5.card_eq_card_mul_relIndex hsyl.1
  rw [D.Tu_card] at hcard
  have hodd : ¬ 2 ∣ (T ⊓ centralizerElem u).relIndex (centralizerElem u) := hsyl.2.2
  have h256 : 128 * 2 ∣ 128 * (T ⊓ centralizerElem u).relIndex (centralizerElem u) := by
    rw [← hcard]
    exact (by norm_num : 128 * 2 = 2 ^ 8) ▸ h8.trans hKdvd
  exact hodd (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h256)

end U9Data

theorem step9_of_inspection
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) (hP : Prop121Three) (hIns : Lemma2_4_29_9_K) {G : Type} [Group G]
    [Finite G] {T M H S L : Subgroup G} (cfg : A5Cfg G T M H S L) {z u : G}
    (s7 : A5Step7 T M H S L z u) (hodd : oddCoreIn (centralizerElem u) = ⊥) {K : Subgroup G}
    (hK : IsComponentIn K (centralizerElem u)) (hzN : z ∈ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅K, Subgroup.zpowers z⁆ = K) (hKM : ¬ K ≤ M)
    (hinn : (¬ CentralQuotientAlt K 6 ∧ ¬ CentralQuotientAlt K 7) → Ch1.InducesInner z K)
    (hlist : IsListedComponentW M (T ⊓ centralizerElem u) K z) :
    centralizerElem u ≤ Subgroup.normalizer (K : Set G) ∧ IsSylowTwoOf (baum S ⊓ K) K ∧
      centralizerElem u ⊓ Subgroup.centralizer (K : Set G) =
        baum S ⊓ Subgroup.centralizer (K : Set G) ∧
      ∃ e : ↥K ≃* alternatingGroup (Fin 6),
        (∃ v ∈ baum S, v ∈ blockU L ∧ v ∉ Subgroup.zpowers u ∧
          ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧ InducesPerm e v τ) ∧
        ∀ r ∈ baum S, ∃ σ : Equiv.Perm (Fin 6), InducesPerm e r σ := by
  obtain ⟨A, V, D⟩ := exists_u9data h247 h245_4 hC54 h314 cfg s7
  rcases hlist.old_or_cover with hold | hcov
  · obtain ⟨hty, huzK⟩ := hIns G T M H S L cfg z u s7 hodd K hK hzN hcomm hKM hinn hold
    obtain ⟨hAK', hnorm, hsyl, hB, e, v, hvC, hv1, hvu, τ, hτ, hvτ⟩ :=
      step9_facts hP cfg D hK hty huzK
    refine ⟨hnorm, hsyl, hB, e, ⟨v, D.U_le_R hvC.1, hvC.1, ?_, τ, hτ, hvτ⟩, ?_⟩
    · intro hmem
      rcases (mem_zpowers_iff_of_sq_eq_one (by rw [pow_two]; exact D.u_sq')).mp hmem with h | h
      · exact hv1 h
      · exact hvu h
    · exact D.R_induces_perm hK.1 hnorm hAK' e hvC hv1 hvu hvτ
  · exact (D.false_of_cover hK.1 hcov).elim

end CFSG.QuasithinUnique.A5
