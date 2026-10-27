module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
import CFSG.Sporadic.Recognition.JankoWongSylow
import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Toolkit

variable {X : Type} [Group X] [Finite X]

private theorem l66_isPCompIn {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsPCompIn 2 H J := by
  rcases h with ⟨⟨u, -, -, hpc, -⟩, -⟩ | ⟨⟨hpc, -⟩, -⟩
  · exact hpc
  · exact hpc

private theorem l66_isTwoGenQuasi {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsTwoGenQuasi ↥J :=
  (isTwoGenQuasi_subgroupOf_iff (l66_isPCompIn h).1).1
    (isPComponent_two_iff.1 (l66_isPCompIn h).2).2

private theorem l66_sq_eq_one {g : X} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

private theorem l66_mem_oTwoPrimeOf {A : Subgroup X} {x : X} (hx : x ∈ A) (h2 : x ^ 2 = 1) :
    x ∈ oTwoPrimeOf A :=
  mem_oTwoPrimeOf hx 1 (by simpa using h2)

private theorem l66_conj_mem {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M) {x : X}
    (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem l66_mem_normalizer {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨l66_conj_mem h, fun hx => ?_⟩
  have := l66_conj_mem h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private theorem l66_commutatorElement_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    ⁅m, j⁆ ∈ pPrimeCoreOf 2 M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne' : M.subgroupOf H ≠ J.subgroupOf H := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hM.1, inf_of_le_left hJ.1] at h
    exact h
  obtain ⟨-, -, hcore, -⟩ :=
    (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hM.2 hJ.2).2 hne'
  have hc : ⁅(⟨m, hM.1 hm⟩ : ↥H), (⟨j, hJ.1 hj⟩ : ↥H)⁆ ∈
      (pPrimeCore 2 ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype :=
    (hcore.trans inf_le_left) (Subgroup.commutator_mem_commutator hm hj)
  obtain ⟨y, hy, hyeq⟩ := hc
  let e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hM.1
  have hey : e y ∈ pPrimeCore 2 ↥M := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨y, hy, rfl⟩
  refine ⟨e y, hey, ?_⟩
  change ((y : ↥H) : X) = ⁅m, j⁆
  exact congrArg Subtype.val hyeq

private theorem l66_commute_of_ne {H F G : Subgroup X} (hF : IsPCompIn 2 H F)
    (hG : IsPCompIn 2 H G) (hne : F ≠ G) (hFO : oddCoreOf F = ⊥) {f g : X} (hf : f ∈ F)
    (hg : g ∈ G) : f * g = g * f := by
  have h : ⁅f, g⁆ ∈ oddCoreOf F := l66_commutatorElement_mem hF hG hne hf hg
  rw [hFO, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem l66_sSup_le_normalizer {H M : Subgroup X} {S : Set (Subgroup X)}
    (hM : IsPCompIn 2 H M) (hS : ∀ J ∈ S, IsPCompIn 2 H J) :
    sSup S ≤ normalizer (M : Set X) := by
  refine sSup_le fun J hJ => ?_
  by_cases hne : M = J
  · rw [← hne]
    exact Subgroup.le_normalizer
  intro j hj
  have hOMM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ pPrimeCoreOf 2 M := fun g hg m hm =>
    l66_commutatorElement_mem hM (hS J hJ) hne hm hg
  exact l66_mem_normalizer (fun m hm => hOMM (hc j hj m hm))
    (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm))

private theorem l66_le_QOf_of_ne {H L J : Subgroup X} (hL : IsPCompIn 2 H L)
    (hJ : IsPCompIn 2 H J) (hne : L ≠ J) : J ≤ QOf L := by
  intro j hj
  have hOLL : pPrimeCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hc : ∀ g ∈ J, ∀ m ∈ L, ⁅m, g⁆ ∈ pPrimeCoreOf 2 L := fun g hg m hm =>
    l66_commutatorElement_mem hL hJ hne hm hg
  exact mem_QOf_iff.2 ⟨l66_mem_normalizer (fun m hm => hOLL (hc j hj m hm))
    (fun m hm => hOLL (hc j⁻¹ (J.inv_mem hj) m hm)), fun m hm => hc j hj m hm⟩

private theorem l66_exists_involution {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
    ∃ v ∈ L, orderOf v = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := primeResidual_eq_bot_of_coprime_card (G := ↥L) 2 hcop
    rw [hq.1] at h1
    have hnt : Nontrivial ↥L := by
      by_contra hnot
      rw [not_nontrivial_iff_subsingleton] at hnot
      obtain ⟨a, b, hab⟩ := hq.2.2.2
      exact hab (Subsingleton.elim (a * b) (b * a))
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

private theorem l66_le_of_normalizes {L A : Subgroup X} (hq : IsTwoGenQuasi ↥L)
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) (hLA : L ≤ normalizer (A : Set X)) {v : X}
    (hvL : v ∈ L) (hv : orderOf v = 2) (hvA : v ∈ A) : L ≤ A := by
  haveI hn : (A.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.1 (hLA g.2) x).1 hx
    simpa using h1
  have hv' : orderOf (⟨v, hvL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hv
  have htop := eq_top_of_normal_of_involution hq hZ (A := A.subgroupOf L) (s := ⟨v, hvL⟩)
    (by rw [Subgroup.mem_subgroupOf]; exact hvA) hv'
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ A.subgroupOf L := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this

private theorem l66_exists_mul_of_mem_sup {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) {x : X} (hx : x ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ k ∈ N, x = h * k := by
  set D : Subgroup X := normalizer (N : Set X)
  have hND : N ≤ D := Subgroup.le_normalizer
  haveI hMn : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).2 le_rfl
  have hxD : x ∈ D := (sup_le hHN hND) hx
  have hxHN : (⟨x, hxD⟩ : D) ∈ H.subgroupOf D ⊔ N.subgroupOf D := by
    rw [← Subgroup.subgroupOf_sup hHN hND]
    exact hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hxHN
  exact ⟨y, hy, z, hz, (congrArg Subtype.val hyz).symm⟩

private theorem l66_mem_normalizer_of_map_le {V : Subgroup X} {b : X}
    (h : V.map (MulAut.conj b).toMonoidHom ≤ V) : b ∈ normalizer (V : Set X) :=
  mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]))

private theorem l66_mem_normalizer_oTwoPrimeOf {A : Subgroup X} {g : X}
    (hg : g ∈ normalizer (A : Set X)) : g ∈ normalizer (oTwoPrimeOf A : Set X) := by
  apply l66_mem_normalizer_of_map_le
  have := map_oTwoPrimeOf_le A (MulAut.conj g).toMonoidHom
  rwa [map_conj_eq_of_mem_normalizer hg] at this

private theorem l66_oddCoreOf_le_of_normal {K C : Subgroup X} (hKC : K ≤ C)
    (hn : C ≤ normalizer (K : Set X)) : oddCoreOf K ≤ oddCoreOf C :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le K).trans hKC)
    (fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (hn hc)) (odd_card_oddCoreOf K)

private theorem l66_oddCoreOf_eq_bot {H F : Subgroup X} (hF : IsPCompIn 2 H F)
    (hH : oddCoreOf H = ⊥) : oddCoreOf F = ⊥ := by
  have h : oddCoreOf F ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hF.1 (isPComponent_two_iff.1 hF.2).1
  rw [hH] at h
  exact le_bot_iff.1 h

private theorem l66_K_le (n : ℕ) (t : X) : Sec6K X n (cen t) ≤ cen t :=
  sSup_le fun _ hL => (l66_isPCompIn hL).1

private theorem l66_M_le_K (n : ℕ) (H : Subgroup X) : Sec6M X n H ≤ Sec6K X n H := by
  rw [sec6K_eq]
  exact le_sup_right

private theorem l66_oddCoreOf_K_eq_bot {n : ℕ} {b : X} (hb : oddCoreOf (cen b) = ⊥) :
    oddCoreOf (Sec6K X n (cen b)) = ⊥ := by
  have h := l66_oddCoreOf_le_of_normal (l66_K_le n b) (Sec6K_cen_normal n b)
  rw [hb] at h
  exact le_bot_iff.1 h

private theorem l66_card_lt
    {n : ℕ} {Q K : Type} [Group Q] [Group K] (hT : IsSec6MType n Q)
    (hK : IsDoubleCoverOfAlt K n) : Nat.card K < Nat.card Q := by
  have hcardK : Nat.card K ≤ 2 * Nat.factorial n := by
    obtain ⟨-, hc, ⟨e⟩⟩ := hK
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [Nat.card_congr e.toEquiv, hc] at h1
    have h2 : Nat.card (alternatingGroup (Fin n)) ≤ Nat.factorial n := by
      calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
            Subgroup.card_le_card_group _
        _ = Nat.factorial n := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    omega
  rcases hT with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]
    have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ly.card_Ly']
    have h11 : Nat.factorial 11 = 39916800 := by norm_num [Nat.factorial]
    omega

private theorem l66_ne_of_A_M
    {n : ℕ} {H L J : Subgroup X} (hL : Sec5Comp X n H L) (hJ : Sec6MComp X n H J) : L ≠ J := by
  rintro rfl
  exact lt_irrefl _ (l66_card_lt hJ.2 hL.2)

private theorem l66_M_le_QOf_A
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec5Comp X n (cen t) L) :
    Sec6M X n (cen t) ≤ QOf L :=
  sSup_le fun J hJ => l66_le_QOf_of_ne (l66_isPCompIn (Or.inl hL)) (l66_isPCompIn (Or.inr hJ))
    (l66_ne_of_A_M hL hJ)

private theorem l66_center_quot_eq_bot
    {n : ℕ} {H L : Subgroup X} (hL : Sec6MComp X n H L) :
    center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ :=
  mcLLyCenterFree _ hL.1.2.1

end Toolkit

section Setting

variable {X : Type} [Group X] [Finite X]

private theorem l66_M_le_base (n : ℕ) (t : X) : Sec6M X n (cen t) ≤ Sec6Base X n t := by
  unfold Sec6Base
  exact le_sup_left

private theorem l66_core_bot {n : ℕ} {t b : X} (h65 : Sec6L65 X n t)
    (hb : b ∈ Sec6M X n (cen t)) (hb2 : orderOf b = 2) : oddCoreOf (cen b) = ⊥ :=
  h65 b (l66_M_le_base n t hb) hb2

private theorem l66_K_le_V {n : ℕ} {t x : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) :
    Sec6K X n (cen x) ≤ sec6V X n t := by
  unfold sec6V
  exact le_iSup₂_of_le x hx (le_iSup_of_le hx2 le_rfl)

private theorem l66_exists_involution_M {n : ℕ} {t : X} (hS : Sec6Setting X n t) :
    ∃ x ∈ Sec6M X n (cen t), orderOf x = 2 := by
  obtain ⟨M, hM⟩ := hS.choice.hasM
  obtain ⟨x, hxM, hx2⟩ := l66_exists_involution (l66_isTwoGenQuasi (Or.inr hM))
  exact ⟨x, le_sSup (s := {M | Sec6MComp X n (cen t) M}) hM hxM, hx2⟩

theorem sec6_oddCoreOf_cen_eq_bot {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (h65 : Sec6L65 X n t) (hA : K0 X n (cen t) ≠ ⊥) : oddCoreOf (cen t) = ⊥ := by
  have htA : t ∈ K0 X n (cen t) := hS.central hA
  have htt : t ∈ cen t := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have htN : t ∈ normalizer (K0 X n (cen t) : Set X) := K0_cen_normal n t htt
  have htZ : t ∈ zStar (K0 X n (cen t)) := by
    unfold zStar
    refine Subgroup.mem_inf.2 ⟨htA, htN, normalizer_le_normalizer_pPrimeCoreOf _ htN,
      fun k hk => ?_⟩
    have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.1 (K0_le n (cen t) hk)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hkt]
    exact one_mem _
  exact h65 t (by unfold Sec6Base; exact Subgroup.mem_sup_right htZ) hS.choice.inv

theorem sec6V_le_K_of_not_atAhat {n : ℕ} {t : X} (h61 : Sec6L61 X n t) (h65 : Sec6L65 X n t)
    (hA : ¬ Sec6AtAhat X n t) : sec6V X n t ≤ Sec6K X n (cen t) := by
  unfold sec6V
  refine iSup₂_le fun x hx => iSup_le fun hx2 => ?_
  have hcov := h61.b hA x hx hx2
  unfold Sec6Covers at hcov
  rw [l66_oddCoreOf_K_eq_bot (l66_core_bot h65 hx hx2), bot_sup_eq] at hcov
  exact hcov.le.trans inf_le_right

private theorem l66_piece_le_V {n : ℕ} {t x : X} (hC : Sec6CtrlAt X n t)
    (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : sec6Piece L x ≤ sec6V X n t := by
  obtain ⟨F, hF, hPF⟩ := hC.land x (Subgroup.mem_sup_left hx) hx2 L hL
  exact hPF.trans ((le_sSup (s := {L | Sec6KComp X n (cen x) L}) hF).trans (l66_K_le_V hx hx2))

theorem sec6K_le_V {n : ℕ}
    {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t) :
    Sec6K X n (cen t) ≤ sec6V X n t := by
  refine sSup_le fun L hL => ?_
  have hLV : L ≤ normalizer (sec6V X n t : Set X) :=
    (l66_isPCompIn hL).1.trans (cen_le_normalizer_sec6V n t)
  have hq := l66_isTwoGenQuasi hL
  rcases hL with hA | hM
  · obtain ⟨x, hx, hx2⟩ := l66_exists_involution_M hS
    have hxL : x ∈ centralizerSection L (pPrimeCoreOf 2 L) := l66_M_le_QOf_A hA hx
    obtain ⟨-, hcov⟩ := isPCompIn_restrict (l66_isPCompIn (Or.inl hA)) (l66_sq_eq_one hx2) hxL
    exact le_of_covers_of_normalized ((oTwoPrimeOf_le _).trans inf_le_left) hcov hq.1
      (l66_piece_le_V hC hx hx2 (Or.inl hA)) fun c hc => hLV hc
  · obtain ⟨v, hvL, hv2⟩ := l66_exists_involution hq
    have hvM : v ∈ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hM hvL
    have hvP : v ∈ sec6Piece L v :=
      l66_mem_oTwoPrimeOf ⟨hvL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
        (l66_sq_eq_one hv2)
    exact l66_le_of_normalizes hq (l66_center_quot_eq_bot hM) hLV hvL hv2
      (l66_piece_le_V hC hvM hv2 (Or.inr hM) hvP)

theorem sec6V_eq_K_of_not_atAhat
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t)
    (h65 : Sec6L65 X n t) (hA : ¬ Sec6AtAhat X n t) : sec6V X n t = Sec6K X n (cen t) :=
  le_antisymm (sec6V_le_K_of_not_atAhat h61 h65 hA) (sec6K_le_V hS hC)

end Setting

private abbrev L66HU (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
    Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x

section AtAhat

variable {X : Type} [Group X] [Finite X]

private theorem l66_piece_mem {n : ℕ} {t x : X} (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) : Sec6KComp X n (cen x) (sec6Piece L x) := by
  obtain ⟨F, hF, hPF⟩ := hC.land x (Subgroup.mem_sup_left hx) hx2 L (Or.inr hL)
  have hFeq := hU x hx hx2 L F hL hF hPF
  rw [l66_oddCoreOf_eq_bot (l66_isPCompIn hF) (l66_core_bot h65 hx hx2), bot_sup_eq] at hFeq
  rwa [← hFeq]

private theorem l66_K0_ne_bot_of_atAhat {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t) :
    K0 X n (cen t) ≠ ⊥ := by
  intro h
  set A := K0 X n (cen t) with hAdef
  have hc : Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) = 2 := hAt.2.1
  have h1 : Nat.card ↥A = 1 := by rw [h]; exact Subgroup.card_bot
  have h2 := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥A)
  have h3 := Subgroup.card_le_card_group (center (↥A ⧸ pPrimeCore 2 ↥A))
  rw [h1] at h2
  have h4 := Nat.le_of_dvd one_pos h2
  omega

private theorem l66_pPrimeCore_eq_bot {L : Subgroup X} (hL : oddCoreOf L = ⊥) :
    pPrimeCore 2 ↥L = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hL

private theorem l66_eq_one_of_central {L : Subgroup X} (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥)
    (hO : oddCoreOf L = ⊥) {z : X} (hzL : z ∈ L) (hz : ∀ l ∈ L, l * z = z * l) : z = 1 := by
  let π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' _
  have hc : π ⟨z, hzL⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz l l.2)
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : (⟨z, hzL⟩ : ↥L) ∈ π.ker := hc
  rw [QuotientGroup.ker_mk', l66_pPrimeCore_eq_bot hO, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

private theorem l66_exists_ne_comm {E : Subgroup X} (hq : IsTwoGenQuasi ↥E) :
    ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  by_contra h
  push_neg at h
  refine not_commutator_le_of_odd hq (R := ⊥) (by simp) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact h a ha b hb

private theorem l66_eq_of_le {H F G A : Subgroup X} (hF : IsPCompIn 2 H F)
    (hG : IsPCompIn 2 H G) (hFO : oddCoreOf F = ⊥) (hAF : A ≤ F) (hAG : A ≤ G)
    (hnc : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) : F = G := by
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact hab (l66_commute_of_ne hF hG hne hFO (hAF ha) (hAG hb))

private theorem l66_K0_oddCore {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥) :
    oddCoreOf (K0 X n (cen t)) = ⊥ := by
  have h := l66_oddCoreOf_le_of_normal (K0_le n (cen t)) (K0_cen_normal n t)
  rw [hcore] at h
  exact le_bot_iff.1 h

private theorem l66_eq_K0 {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) {A : Subgroup X} (hA : Sec5Comp X n (cen t) A) :
    A = K0 X n (cen t) := by
  set K := K0 X n (cen t) with hKdef
  have hAK : A ≤ K := by
    rw [hKdef, K0_eq_sSup_sec5Comp]
    exact le_sSup (s := {A | Sec5Comp X n (cen t) A}) hA
  have hKN : K ≤ normalizer (A : Set X) := by
    rw [hKdef, K0_eq_sSup_sec5Comp]
    exact l66_sSup_le_normalizer (l66_isPCompIn (Or.inl hA)) fun J hJ => l66_isPCompIn (Or.inl hJ)
  haveI hAn : (A.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).2 hKN
  have hO : pPrimeCore 2 ↥K = ⊥ := l66_pPrimeCore_eq_bot (l66_K0_oddCore hcore)
  let π : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = ⊥ := by rw [QuotientGroup.ker_mk', hO]
  have hN : ((A.subgroupOf K).map π).Normal := Subgroup.Normal.map hAn π hπ
  rcases LocalCores.quasisimple_normal_subgroups hAt.1 hN with htop | hcen
  · refine le_antisymm hAK fun x hx => ?_
    have h2 := Subgroup.comap_map_eq π (A.subgroupOf K)
    rw [htop, Subgroup.comap_top, hker, sup_bot_eq] at h2
    have h1 : (⟨x, hx⟩ : ↥K) ∈ A.subgroupOf K := by
      rw [← h2]
      exact Subgroup.mem_top _
    exact h1
  · exfalso
    refine not_commutator_le_of_odd (l66_isTwoGenQuasi (Or.inl hA)) (R := ⊥) (by simp) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haK : a ∈ K := hAK ha
    have hbK : b ∈ K := hAK hb
    have hac : π ⟨a, haK⟩ ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := hcen ⟨⟨a, haK⟩, ha, rfl⟩
    have h1 : π ⁅(⟨a, haK⟩ : ↥K), ⟨b, hbK⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hac (π ⟨b, hbK⟩)).symm
    have h2 : ⁅(⟨a, haK⟩ : ↥K), ⟨b, hbK⟩⁆ ∈ π.ker := h1
    rw [hker, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    have h3 := congrArg Subtype.val h2
    simpa [commutatorElement_def] using h3

private theorem l66_sec5Comp_K0 {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) : Sec5Comp X n (cen t) (K0 X n (cen t)) := by
  have hne := l66_K0_ne_bot_of_atAhat hAt
  obtain ⟨A, hA⟩ : ∃ A, Sec5Comp X n (cen t) A := by
    by_contra hno
    push_neg at hno
    apply hne
    rw [K0_eq_sSup_sec5Comp]
    exact sSup_eq_bot.2 fun A hA => absurd hA (hno A)
  rwa [← l66_eq_K0 hAt hcore hA]

private theorem l66_M_le_centralizer_K0
    {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) :
    Sec6M X n (cen t) ≤ centralizer (K0 X n (cen t) : Set X) := by
  have hA := l66_sec5Comp_K0 hAt hcore
  refine sSup_le fun M hM => ?_
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (l66_commute_of_ne (l66_isPCompIn (Or.inr hM)) (l66_isPCompIn (Or.inl hA))
    (l66_ne_of_A_M hA hM).symm (l66_oddCoreOf_eq_bot (l66_isPCompIn (Or.inr hM)) hcore) hm
      ha).symm

private theorem l66_piece_K0
    {n : ℕ} {t x : X} (hAt : Sec6AtAhat X n t) (hcore : oddCoreOf (cen t) = ⊥)
    (hx : x ∈ Sec6M X n (cen t)) : sec6Piece (K0 X n (cen t)) x = K0 X n (cen t) := by
  have hAx : K0 X n (cen t) ≤ cen x := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (l66_M_le_centralizer_K0 hAt hcore hx)) a ha)
  unfold sec6Piece
  rw [inf_of_le_left hAx]
  exact oTwoPrimeOf_eq_self_of_primeResidual
    (l66_isTwoGenQuasi (Or.inl (l66_sec5Comp_K0 hAt hcore))).1

private theorem l66_exists_F
    {n : ℕ} {t x : X} (hAt : Sec6AtAhat X n t) (hcore : oddCoreOf (cen t) = ⊥)
    (hC : Sec6CtrlAt X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) :
    ∃ F, Sec6KComp X n (cen x) F ∧ K0 X n (cen t) ≤ F := by
  obtain ⟨F, hF, hPF⟩ :=
    hC.land x (Subgroup.mem_sup_left hx) hx2 _ (Or.inl (l66_sec5Comp_K0 hAt hcore))
  rw [l66_piece_K0 hAt hcore hx] at hPF
  exact ⟨F, hF, hPF⟩

private theorem l66_K0_noncomm {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) :
    ∃ a ∈ K0 X n (cen t), ∃ b ∈ K0 X n (cen t), a * b ≠ b * a :=
  l66_exists_ne_comm (l66_isTwoGenQuasi (Or.inl (l66_sec5Comp_K0 hAt hcore)))

private theorem l66_mem_cases
    {n : ℕ} {t x : X} (hAt : Sec6AtAhat X n t) (hcore : oddCoreOf (cen t) = ⊥)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t)
    (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {G : Subgroup X}
    (hG : Sec6KComp X n (cen x) G) :
    K0 X n (cen t) ≤ G ∨ ∃ M, Sec6MComp X n (cen t) M ∧ G = sec6Piece M x := by
  obtain ⟨L, hL, hPG⟩ := hC.piece x (Subgroup.mem_sup_left hx) hx2 G hG
  rcases hL with hA | hM
  · left
    rw [l66_eq_K0 hAt hcore hA, l66_piece_K0 hAt hcore hx] at hPG
    exact hPG
  · right
    refine ⟨L, hM, ?_⟩
    have hGeq := hU x hx hx2 L G hM hG hPG
    rwa [l66_oddCoreOf_eq_bot (l66_isPCompIn hG) (l66_core_bot h65 hx hx2), bot_sup_eq] at hGeq

private theorem l66_K_le_F_sup
    {n : ℕ} {t x : X} (hAt : Sec6AtAhat X n t) (hcore : oddCoreOf (cen t) = ⊥)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t)
    (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen x) F) (hAF : K0 X n (cen t) ≤ F) :
    Sec6K X n (cen x) ≤ F ⊔ Sec6M X n (cen t) := by
  refine sSup_le fun G hG => ?_
  rcases l66_mem_cases hAt hcore hC hU h65 hx hx2 hG with hAG | ⟨M, hM, rfl⟩
  · rw [l66_eq_of_le (l66_isPCompIn hG) (l66_isPCompIn hF)
      (l66_oddCoreOf_eq_bot (l66_isPCompIn hG) (l66_core_bot h65 hx hx2)) hAG hAF
      (l66_K0_noncomm hAt hcore)]
    exact le_sup_left
  · exact ((oTwoPrimeOf_le _).trans inf_le_left).trans
      ((le_sSup (s := {M | Sec6MComp X n (cen t) M}) hM).trans le_sup_right)

private theorem l66_piece_le_centralizer
    {n : ℕ} {t x : X} (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen x) F) (hAF : K0 X n (cen t) ≤ F) {M : Subgroup X}
    (hM : Sec6MComp X n (cen t) M) : sec6Piece M x ≤ centralizer (F : Set X) := by
  have hP := l66_piece_mem hC hU h65 hx hx2 hM
  have hne : sec6Piece M x ≠ F := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := l66_K0_noncomm hAt hcore
    have hbP : b ∈ sec6Piece M x := by
      rw [h]
      exact hAF hb
    have hbM : b ∈ Sec6M X n (cen t) :=
      le_sSup (s := {M | Sec6MComp X n (cen t) M}) hM (((oTwoPrimeOf_le _).trans inf_le_left) hbP)
    exact hab ((Subgroup.mem_centralizer_iff.1 (l66_M_le_centralizer_K0 hAt hcore hbM)) a ha)
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact (l66_commute_of_ne (l66_isPCompIn hP) (l66_isPCompIn hF) hne
    (l66_oddCoreOf_eq_bot (l66_isPCompIn hP) (l66_core_bot h65 hx hx2)) hp hf).symm

private theorem l66_F_eq_of_mem {n : ℕ} {t x y : X} (hxO : oddCoreOf (cen x) = ⊥)
    {F G : Subgroup X} (hF : Sec6KComp X n (cen x) F) (hG : Sec6KComp X n (cen y) G)
    (hAF : K0 X n (cen t) ≤ F) (hAG : K0 X n (cen t) ≤ G) (hyF : y ∈ centralizer (F : Set X))
    (hxG : x ∈ centralizer (G : Set X))
    (hnc : ∃ a ∈ K0 X n (cen t), ∃ b ∈ K0 X n (cen t), a * b ≠ b * a) : F = G := by
  have hFy : F ≤ cen y := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hyF) f hf)
  have hGx : G ≤ cen x := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hxG) g hg)
  have hFH : F ≤ cen x ⊓ cen y := le_inf (l66_isPCompIn hF).1 hFy
  have hGH : G ≤ cen x ⊓ cen y := le_inf hGx (l66_isPCompIn hG).1
  have hF' : IsPCompIn 2 (cen x ⊓ cen y) F :=
    ⟨hFH, isPComponent_subgroupOf_mono hFH inf_le_left (l66_isPCompIn hF).2⟩
  have hG' : IsPCompIn 2 (cen x ⊓ cen y) G :=
    ⟨hGH, isPComponent_subgroupOf_mono hGH inf_le_right (l66_isPCompIn hG).2⟩
  exact l66_eq_of_le hF' hG' (l66_oddCoreOf_eq_bot (l66_isPCompIn hF) hxO) hAF hAG hnc

private theorem l66_M_le_sup_N {n : ℕ} {t : X} (L : Subgroup X) :
    Sec6M X n (cen t) ≤ L ⊔ sSup {M | Sec6MComp X n (cen t) M ∧ M ≠ L} := by
  refine sSup_le fun M hM => ?_
  by_cases h : M = L
  · rw [h]
    exact le_sup_left
  · exact (le_sSup (s := {M | Sec6MComp X n (cen t) M ∧ M ≠ L}) ⟨hM, h⟩).trans le_sup_right

private theorem l66_N_le_centralizer {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥)
    {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) :
    sSup {M | Sec6MComp X n (cen t) M ∧ M ≠ L} ≤ centralizer (L : Set X) := by
  refine sSup_le fun M ⟨hM, hne⟩ => ?_
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (l66_commute_of_ne (l66_isPCompIn (Or.inr hM)) (l66_isPCompIn (Or.inr hL)) hne
    (l66_oddCoreOf_eq_bot (l66_isPCompIn (Or.inr hM)) hcore) hm hl).symm

private theorem l66_mem_normalizer_centralizer {F : Subgroup X} {g : X}
    (hg : g ∈ normalizer (F : Set X)) : g ∈ normalizer (centralizer (F : Set X) : Set X) := by
  have key : ∀ g ∈ normalizer (F : Set X), ∀ c ∈ centralizer (F : Set X),
      g * c * g⁻¹ ∈ centralizer (F : Set X) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro f hf
    have hf' : g⁻¹ * f * g ∈ F := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) f).1 hf
      simpa using this
    have h1 := hc _ hf'
    calc f * (g * c * g⁻¹) = g * ((g⁻¹ * f * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * f := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have h2 := key g⁻¹ (inv_mem hg) _ h
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h2

private theorem l66_decomp
    {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {x : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) :
    ∃ m ∈ L, ∃ k ∈ centralizer (L : Set X), k ∈ sSup {M | Sec6MComp X n (cen t) M ∧ M ≠ L} ∧
      x = m * k ∧ m ^ 2 = 1 := by
  have hNC := l66_N_le_centralizer hcore hL
  have hLN : L ≤ normalizer
      ((sSup {M | Sec6MComp X n (cen t) M ∧ M ≠ L} : Subgroup X) : Set X) :=
    (Subgroup.le_centralizer_iff.1 hNC).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨m, hm, k, hk, rfl⟩ := l66_exists_mul_of_mem_sup hLN (l66_M_le_sup_N L hx)
  have hkC := hNC hk
  refine ⟨m, hm, k, hkC, hk, rfl, ?_⟩
  have hmk : Commute m k := (Subgroup.mem_centralizer_iff.1 hkC) m hm
  have hx2' : (m * k) ^ 2 = 1 := l66_sq_eq_one hx2
  rw [hmk.mul_pow] at hx2'
  have hm2 : m ^ 2 = (k ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hx2'
  have hk2C : (k ^ 2)⁻¹ ∈ centralizer (L : Set X) := inv_mem (pow_mem hkC 2)
  refine l66_eq_one_of_central (l66_center_quot_eq_bot hL)
    (l66_oddCoreOf_eq_bot (l66_isPCompIn (Or.inr hL)) hcore) (pow_mem hm 2) fun l hl => ?_
  rw [hm2]
  exact (Subgroup.mem_centralizer_iff.1 hk2C) l hl

private theorem l66_N_le_P {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {y : X} (hyL : y ∈ L) :
    sSup {M | Sec6MComp X n (cen t) M ∧ M ≠ L} ≤
      ⨆ (M : Subgroup X) (_ : Sec6MComp X n (cen t) M), sec6Piece M y := by
  refine sSup_le fun M ⟨hM, hne⟩ => ?_
  have hMy : M ≤ cen y := fun m hm => Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 (l66_N_le_centralizer hcore hL
      (le_sSup (s := {M | Sec6MComp X n (cen t) M ∧ M ≠ L}) ⟨hM, hne⟩ hm))) y hyL).symm
  have hP : sec6Piece M y = M := by
    unfold sec6Piece
    rw [inf_of_le_left hMy]
    exact oTwoPrimeOf_eq_self_of_primeResidual (l66_isTwoGenQuasi (Or.inr hM)).1
  rw [← hP]
  exact le_iSup₂ (f := fun M (_ : Sec6MComp X n (cen t) M) => sec6Piece M y) M hM

private theorem l66_mem_P
    {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {x y : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2)
    (hyL : y ∈ L) (hxy : x * y = y * x) :
    x ∈ ⨆ (M : Subgroup X) (_ : Sec6MComp X n (cen t) M), sec6Piece M y := by
  obtain ⟨m, hm, k, hkC, hkN, rfl, hm2⟩ := l66_decomp hcore hL hx hx2
  have hky : k * y = y * k := ((Subgroup.mem_centralizer_iff.1 hkC) y hyL).symm
  have hmy : m * y = y * m := by
    have h1 : m * y * k = y * m * k := by
      calc m * y * k = m * (k * y) := by rw [mul_assoc, hky]
        _ = m * k * y := by rw [mul_assoc]
        _ = y * (m * k) := hxy
        _ = y * m * k := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hmP : m ∈ sec6Piece L y :=
    l66_mem_oTwoPrimeOf ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 hmy⟩ hm2
  exact mul_mem (le_iSup₂ (f := fun M (_ : Sec6MComp X n (cen t) M) => sec6Piece M y) L hL hmP)
    (l66_N_le_P hcore hL hyL hkN)

private theorem l66_exists_commuting
    {n : ℕ} {t : X} (hcore : oddCoreOf (cen t) = ⊥) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {x : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) :
    ∃ y ∈ L, orderOf y = 2 ∧ x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, k, hkC, -, rfl, hm2⟩ := l66_decomp hcore hL hx hx2
  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨y, hyL, hy2⟩ := l66_exists_involution (l66_isTwoGenQuasi (Or.inr hL))
    refine ⟨y, hyL, hy2, ?_⟩
    rw [one_mul]
    exact ((Subgroup.mem_centralizer_iff.1 hkC) y hyL).symm
  · refine ⟨m, hm, orderOf_eq_prime hm2 hm1, ?_⟩
    have hmk : m * k = k * m := (Subgroup.mem_centralizer_iff.1 hkC) m hm
    rw [mul_assoc, ← hmk]

private theorem l66_F_step
    {n : ℕ} {t : X} (hAt : Sec6AtAhat X n t) (hcore : oddCoreOf (cen t) = ⊥)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {v y : X} (hv : v ∈ Sec6M X n (cen t)) (hv2 : orderOf v = 2)
    (hyL : y ∈ L) (hy2 : orderOf y = 2) (hvy : v * y = y * v) {G G' : Subgroup X}
    (hG : Sec6KComp X n (cen v) G) (hAG : K0 X n (cen t) ≤ G) (hG' : Sec6KComp X n (cen y) G')
    (hAG' : K0 X n (cen t) ≤ G') : G = G' := by
  have hyM : y ∈ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL hyL
  have hyG : y ∈ centralizer (G : Set X) := by
    have hyP : y ∈ sec6Piece L v :=
      l66_mem_oTwoPrimeOf ⟨hyL, Subgroup.mem_centralizer_singleton_iff.2 hvy.symm⟩
        (l66_sq_eq_one hy2)
    exact l66_piece_le_centralizer hAt hcore hC hU h65 hv hv2 hG hAG hL hyP
  have hPle : (⨆ (M : Subgroup X) (_ : Sec6MComp X n (cen t) M), sec6Piece M y) ≤
      centralizer (G' : Set X) :=
    iSup₂_le fun M hM => l66_piece_le_centralizer hAt hcore hC hU h65 hyM hy2 hG' hAG' hM
  have hvG' : v ∈ centralizer (G' : Set X) := hPle (l66_mem_P hcore hL hv hv2 hyL hvy)
  exact l66_F_eq_of_mem (l66_core_bot h65 hv hv2) hG hG' hAG hAG' hyG hvG'
    (l66_K0_noncomm hAt hcore)

private theorem l66_induct {L : Subgroup X}
    (hconn : (CFSG.Open.disconnectedInvolutionCommutingGraph ↥L).Preconnected) (P : X → Prop)
    (hstep : ∀ a ∈ L, ∀ b ∈ L, orderOf a = 2 → orderOf b = 2 → a * b = b * a → P a → P b)
    {y y' : X} (hy : y ∈ L) (hy' : y' ∈ L) (hy2 : orderOf y = 2) (hy2' : orderOf y' = 2)
    (hPy : P y) : P y' := by
  have hstep' : ∀ a b : {g : ↥L // orderOf g = 2}, (a : ↥L) * b = b * a →
      P ((a : ↥L) : X) → P ((b : ↥L) : X) := fun a b hab =>
    hstep _ a.1.2 _ b.1.2 (by rw [Subgroup.orderOf_coe]; exact a.2)
      (by rw [Subgroup.orderOf_coe]; exact b.2) (congrArg Subtype.val hab)
  let u : {g : ↥L // orderOf g = 2} := ⟨⟨y, hy⟩, by rw [Subgroup.orderOf_mk]; exact hy2⟩
  let u' : {g : ↥L // orderOf g = 2} := ⟨⟨y', hy'⟩, by rw [Subgroup.orderOf_mk]; exact hy2'⟩
  have hr := (SimpleGraph.reachable_iff_reflTransGen u u').1 (hconn u u')
  suffices h : ∀ v, Relation.ReflTransGen
      (CFSG.Open.disconnectedInvolutionCommutingGraph ↥L).Adj u v → P ((v : ↥L) : X) from h u' hr
  intro v hv
  induction hv with
  | refl => exact hPy
  | tail _ hbc ih =>
    exact hstep' _ _
      ((CFSG.DisconnectedInvolutionGraph.Helpers.involutionGraph_adj_iff _ _).1 hbc).2 ih

private theorem l66_F_const
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hAt : Sec6AtAhat X n t)
    (hcore : oddCoreOf (cen t) = ⊥) (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t)
    (hconn : ∀ L, Sec6MComp X n (cen t) L →
      (CFSG.Open.disconnectedInvolutionCommutingGraph ↥L).Preconnected)
    {x x' : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) (hx' : x' ∈ Sec6M X n (cen t))
    (hx2' : orderOf x' = 2) {F F' : Subgroup X} (hF : Sec6KComp X n (cen x) F)
    (hAF : K0 X n (cen t) ≤ F) (hF' : Sec6KComp X n (cen x') F') (hAF' : K0 X n (cen t) ≤ F') :
    F = F' := by
  obtain ⟨L, hL⟩ := hS.choice.hasM
  have hLM : L ≤ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL
  obtain ⟨y, hyL, hy2, hxy⟩ := l66_exists_commuting hcore hL hx hx2
  obtain ⟨y', hyL', hy2', hxy'⟩ := l66_exists_commuting hcore hL hx' hx2'
  obtain ⟨G, hG, hAG⟩ := l66_exists_F hAt hcore hC (hLM hyL) hy2
  have hFG := l66_F_step hAt hcore hC hU h65 hL hx hx2 hyL hy2 hxy hF hAF hG hAG
  have hP : ∀ H, Sec6KComp X n (cen y') H → K0 X n (cen t) ≤ H → H = G := by
    refine l66_induct (hconn L hL)
      (fun v => ∀ H, Sec6KComp X n (cen v) H → K0 X n (cen t) ≤ H → H = G)
      (fun a ha b hb ha2 hb2 hab hPa H hH hAH => ?_) hyL hyL' hy2 hy2' ?_
    · obtain ⟨Ha, hHa, hAHa⟩ := l66_exists_F hAt hcore hC (hLM ha) ha2
      rw [← hPa Ha hHa hAHa]
      exact (l66_F_step hAt hcore hC hU h65 hL (hLM ha) ha2 hb hb2 hab hHa hAHa hH hAH).symm
    · intro H hH hAH
      exact l66_eq_of_le (l66_isPCompIn hH) (l66_isPCompIn hG)
        (l66_oddCoreOf_eq_bot (l66_isPCompIn hH) (l66_core_bot h65 (hLM hyL) hy2)) hAH hAG
        (l66_K0_noncomm hAt hcore)
  obtain ⟨G', hG', hAG'⟩ := l66_exists_F hAt hcore hC (hLM hyL') hy2'
  have hF'G' := l66_F_step hAt hcore hC hU h65 hL hx' hx2' hyL' hy2' hxy' hF' hAF' hG' hAG'
  rw [hFG, hF'G', hP G' hG' hAG']

private theorem l66_sec6KComp_map {n : ℕ} (φ : X ≃* X) {H F : Subgroup X}
    (h : Sec6KComp X n H F) : Sec6KComp X n (H.map φ.toMonoidHom) (F.map φ.toMonoidHom) := by
  rcases h with ⟨⟨u, hu⟩, hn⟩ | hM
  · obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv
      (Subgroup.equivMapOfInjective F φ.toMonoidHom φ.injective)
    exact Or.inl ⟨⟨φ u, hu.map_mulEquiv φ⟩, isDoubleCoverOfAlt_congr' f hn⟩
  · exact Or.inr (hM.map_mulEquiv φ)

private theorem l66_V_of_atAhat_of_conn
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t) (hAt : Sec6AtAhat X n t)
    (hconn : ∀ L, Sec6MComp X n (cen t) L →
      (CFSG.Open.disconnectedInvolutionCommutingGraph ↥L).Preconnected) :
    sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
        sec6V X n t = M0 ⊔ Sec6M X n (cen t) := by
  have hcore := sec6_oddCoreOf_cen_eq_bot hS h65 (l66_K0_ne_bot_of_atAhat hAt)
  have hA := l66_sec5Comp_K0 hAt hcore
  obtain ⟨x₀, hx₀, hx₀2⟩ := l66_exists_involution_M hS
  obtain ⟨F₀, hF₀, hAF₀⟩ := l66_exists_F hAt hcore hC hx₀ hx₀2
  have hconst : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ F, Sec6KComp X n (cen x) F →
      K0 X n (cen t) ≤ F → F = F₀ := fun x hx hx2 F hF hAF =>
    l66_F_const hS hAt hcore hC hU h65 hconn hx hx2 hx₀ hx₀2 hF hAF hF₀ hAF₀
  have hVle : sec6V X n t ≤ F₀ ⊔ Sec6M X n (cen t) := by
    unfold sec6V
    refine iSup₂_le fun x hx => iSup_le fun hx2 => ?_
    obtain ⟨F, hF, hAF⟩ := l66_exists_F hAt hcore hC hx hx2
    have h := l66_K_le_F_sup hAt hcore hC hU h65 hx hx2 hF hAF
    rwa [hconst x hx hx2 F hF hAF] at h
  have hKV := sec6K_le_V hS hC
  have hMV : Sec6M X n (cen t) ≤ sec6V X n t := (l66_M_le_K n (cen t)).trans hKV
  by_cases hF₀A : F₀ = K0 X n (cen t)
  · left
    refine le_antisymm ?_ hKV
    rw [sec6K_eq, ← hF₀A]
    exact hVle
  · right
    have hF₀O : oddCoreOf F₀ = ⊥ :=
      l66_oddCoreOf_eq_bot (l66_isPCompIn hF₀) (l66_core_bot h65 hx₀ hx₀2)
    have hF₀M : Sec6MComp X n (cen x₀) F₀ := by
      have hP : sec6Piece (K0 X n (cen t)) x₀ ≤ F₀ := by
        rw [l66_piece_K0 hAt hcore hx₀]
        exact hAF₀
      rcases (hC.dich x₀ (Subgroup.mem_sup_left hx₀) hx₀2 _ F₀ (Or.inl hA) hF₀ hP).2 with h | h
      · exfalso
        rw [hF₀O, bot_sup_eq, l66_piece_K0 hAt hcore hx₀] at h
        exact hF₀A h
      · exact h.1
    have hMC : Sec6M X n (cen t) ≤ centralizer (F₀ : Set X) := by
      refine sSup_le fun L hL => ?_
      have hLM : L ≤ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL
      have hLN : L ≤ normalizer (centralizer (F₀ : Set X) : Set X) := by
        intro g hg
        refine l66_mem_normalizer_centralizer (mem_normalizer_of_map_conj_eq ?_)
        have hgt : g ∈ cen t := (l66_isPCompIn (Or.inr hL)).1 hg
        have hgA : g ∈ normalizer (K0 X n (cen t) : Set X) :=
          Subgroup.centralizer_le_normalizer _ (l66_M_le_centralizer_K0 hAt hcore (hLM hg))
        have hφA : (K0 X n (cen t)).map (MulAut.conj g).toMonoidHom = K0 X n (cen t) :=
          map_conj_eq_of_mem_normalizer hgA
        have hφx : MulAut.conj g x₀ ∈ Sec6M X n (cen t) := by
          rw [MulAut.conj_apply]
          exact (Subgroup.mem_normalizer_iff.1 (Sec6M_cen_normal n t hgt) x₀).1 hx₀
        have hφx2 : orderOf (MulAut.conj g x₀) = 2 := by
          rw [MulEquiv.orderOf_eq]
          exact hx₀2
        have hFm : Sec6KComp X n (cen (MulAut.conj g x₀))
            (F₀.map (MulAut.conj g).toMonoidHom) := by
          have h := l66_sec6KComp_map (MulAut.conj g) hF₀
          rwa [cen_map] at h
        have hAFm : K0 X n (cen t) ≤ F₀.map (MulAut.conj g).toMonoidHom := by
          rw [← hφA]
          exact Subgroup.map_mono hAF₀
        exact hconst _ hφx hφx2 _ hFm hAFm
      obtain ⟨v, hvL, hv2⟩ := l66_exists_involution (l66_isTwoGenQuasi (Or.inr hL))
      obtain ⟨Fv, hFv, hAFv⟩ := l66_exists_F hAt hcore hC (hLM hvL) hv2
      have hvC : v ∈ centralizer (F₀ : Set X) := by
        rw [← hconst v (hLM hvL) hv2 Fv hFv hAFv]
        exact l66_piece_le_centralizer hAt hcore hC hU h65 (hLM hvL) hv2 hFv hAFv hL
          (l66_mem_oTwoPrimeOf ⟨hvL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
            (l66_sq_eq_one hv2))
      exact l66_le_of_normalizes (l66_isTwoGenQuasi (Or.inr hL)) (l66_center_quot_eq_bot hL)
        hLN hvL hv2 hvC
    refine ⟨F₀, ?_, ?_, Subgroup.le_centralizer_iff.1 hMC, le_antisymm hVle (sup_le ?_ hMV)⟩
    · exact hF₀M.2.congr ((QuotientGroup.quotientMulEquivOfEq (l66_pPrimeCore_eq_bot hF₀O)).trans
        QuotientGroup.quotientBot)
    · rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact l66_eq_one_of_central (l66_center_quot_eq_bot hF₀M) hF₀O hz.1
        fun f hf => (Subgroup.mem_centralizer_iff.1 (hMC hz.2)) f hf
    · exact (le_sSup (s := {L | Sec6KComp X n (cen x₀) L}) hF₀).trans (l66_K_le_V hx₀ hx₀2)

end AtAhat

section Conn

private theorem l66_isSimpleGroup
    {n : ℕ} {Q : Type} [Group Q] (hQ : IsSec6MType n Q) : IsSimpleGroup Q := by
  rcases hQ with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e
  · exact @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.isSimpleGroup_Ly e

private theorem l66_exists_noncomm
    {n : ℕ} {Q : Type} [Group Q] (hQ : IsSec6MType n Q) : ∃ a b : Q, a * b ≠ b * a := by
  haveI := l66_isSimpleGroup hQ
  have hZ : center Q = ⊥ := mcLLyCenterFree Q (hQ.imp And.right And.right)
  by_contra h
  push_neg at h
  obtain ⟨g, hg⟩ := exists_ne (1 : Q)
  have hgZ : g ∈ center Q := Subgroup.mem_center_iff.2 fun y => h y g
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact hg hgZ

private theorem l66_oneClass_mcl
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.McL) :
    GH74.GLS.Stage12.OneClassDoubleCover Q 8 := by
  have hQ : IsSec6MType 8 Q := Or.inl ⟨rfl, ⟨e⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card Q := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]
    norm_num
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcov : IsDoubleCoverOfAlt ↥(centralizer ({z} : Set Q)) 8 := by
    obtain ⟨h1, h2, h3⟩ :=
      Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hz
    exact isDoubleCoverOfAlt_of_cover hz (by norm_num) h1 h2 h3
  obtain ⟨hc, hconj⟩ :=
    Sporadic.Recognition.JankoWong.isCentralInvolution_and_oneClass_of_doubleCover
      (l66_isSimpleGroup hQ) (l66_exists_noncomm hQ) hz hcov
  exact ⟨z, hc, hconj, hcov⟩

private theorem l66_preconnected
    {n : ℕ} {Q : Type} [Group Q] [Finite Q] (hQ : IsSec6MType n Q) :
    (CFSG.Open.disconnectedInvolutionCommutingGraph Q).Preconnected := by
  have hs := l66_isSimpleGroup hQ
  obtain ⟨m, c, hF, hG⟩ : ∃ m c, GH74.GLS.Stage12.McLRec.CoverFacts m c ∧
      GH74.GLS.Stage12.OneClassDoubleCover Q m := by
    rcases hQ with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact ⟨8, 40320, GH74.GLS.Stage12.McLRec.coverFacts_eight, l66_oneClass_mcl e⟩
    · exact ⟨11, 39916800, Sporadic.Recognition.LyonsSims.coverFacts_eleven,
        GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly ⟨e⟩⟩
  by_contra hdisc
  obtain ⟨z, hz, -, -⟩ := id hG
  let u : {g : Q // orderOf g = 2} := ⟨z, hz.1⟩
  obtain ⟨h1, h2, h3⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer_stronglyEmbedded u hdisc
  refine GH74.GLS.Stage12.McLRec.no_strongly_embedded_of_coverFacts hs hF hG
    (CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer u) ⟨h1, h2, fun g hg => ?_⟩ ?_
  · have hg' : g⁻¹ ∉ CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer u :=
      fun h => hg (by simpa using inv_mem h)
    have e : CFSG.conjugate (CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer u) g =
        CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup
          (CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer u) g⁻¹ := by
      ext x
      simp only [CFSG.conjugate, CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup,
        Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]
      constructor
      · rintro ⟨y, hy, rfl⟩
        convert hy using 1
        group
      · intro hx
        exact ⟨g * x * g⁻¹, hx, by group⟩
    rw [e]
    exact h3 g⁻¹ hg'
  · intro w hw hw2 g hgw
    have hr := (CFSG.DisconnectedInvolutionGraph.Helpers.componentStabilizer_involution_iff u
      ⟨w, hw2⟩).1 hw
    rw [CFSG.DisconnectedInvolutionGraph.Helpers.mem_componentStabilizer_iff]
    have h4 := CFSG.DisconnectedInvolutionGraph.Helpers.reachable_conjugate hr g
    have h5 : CFSG.DisconnectedInvolutionGraph.Helpers.conjugateInvolution g ⟨w, hw2⟩ =
        ⟨w, hw2⟩ := by
      apply Subtype.ext
      simp only [CFSG.DisconnectedInvolutionGraph.Helpers.conjugateInvolution, MulAut.conj_apply]
      rw [Subgroup.mem_centralizer_singleton_iff.1 hgw, mul_inv_cancel_right]
    rw [h5] at h4
    exact hr.trans h4.symm

end Conn

section MainV

variable {X : Type} [Group X] [Finite X]

private theorem l66_isSec6MType_of_core {n : ℕ} {H L : Subgroup X} (hL : Sec6MComp X n H L)
    (hO : oddCoreOf L = ⊥) : IsSec6MType n ↥L :=
  hL.2.congr ((QuotientGroup.quotientMulEquivOfEq (l66_pPrimeCore_eq_bot hO)).trans
    QuotientGroup.quotientBot)

theorem sec6V_of_atAhat
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X,
      Sec6MComp X n (cen t) L → Sec6KComp X n (cen x) F → sec6Piece L x ≤ F →
        F = oddCoreOf F ⊔ sec6Piece L x)
    (h65 : Sec6L65 X n t) (hAt : Sec6AtAhat X n t) :
    sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
        sec6V X n t = M0 ⊔ Sec6M X n (cen t) := by
  have hcore := sec6_oddCoreOf_cen_eq_bot hS h65 (l66_K0_ne_bot_of_atAhat hAt)
  exact l66_V_of_atAhat_of_conn hS hC hU h65 hAt fun L hL => l66_preconnected
    (l66_isSec6MType_of_core hL (l66_oddCoreOf_eq_bot (l66_isPCompIn (Or.inr hL)) hcore))

theorem sec6L66_V
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h61 : Sec6L61 X n t) (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X,
      Sec6MComp X n (cen t) L → Sec6KComp X n (cen x) F → sec6Piece L x ≤ F →
        F = oddCoreOf F ⊔ sec6Piece L x)
    (h65 : Sec6L65 X n t) :
    sec6V X n t = Sec6K X n (cen t) ∨ ∃ M0 : Subgroup X, IsSec6MType n ↥M0 ∧
      M0 ⊓ Sec6M X n (cen t) = ⊥ ∧ M0 ≤ centralizer (Sec6M X n (cen t) : Set X) ∧
        sec6V X n t = M0 ⊔ Sec6M X n (cen t) := by
  by_cases hAt : Sec6AtAhat X n t
  · exact sec6V_of_atAhat hS hC hU h65 hAt
  · exact Or.inl (sec6V_eq_K_of_not_atAhat hS h61 hC h65 hAt)

end MainV

section Central

variable {X : Type} [Group X] [Finite X]

private theorem l66_isElemAbelian_pair {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({a, b} : Set X)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set X)) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]; exact hb
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b} : Set X)) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [(show Commute y z from hc).mul_pow, hy, hz, one_mul]
  | inv y hy' hy => rw [inv_pow, hy, inv_one]

private theorem l66_cen_le_normalizer_W (n : ℕ) (t : X) :
    cen t ≤ normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
  fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6M_cen_normal n t hc)

private theorem l66_M_le_cen (n : ℕ) (t : X) : Sec6M X n (cen t) ≤ cen t :=
  (l66_M_le_K n (cen t)).trans (l66_K_le n t)

private theorem l66_cW_comm {n : ℕ} {t e : X} (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) (he : e ∈ Sec6M X n (cen t)) (he2 : orderOf e = 2) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {c p : X} (hc : c ∈ oddCoreOf (Sec6M X n (cen t)))
    (hce : c ∈ cen e) (hp : p ∈ sec6Piece L e) : c * p = p * c := by
  have hPL : sec6Piece L e ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPt : sec6Piece L e ≤ cen t := hPL.trans (l66_isPCompIn (Or.inr hL)).1
  have hWO : oddCoreOf (Sec6M X n (cen t)) ≤ oddCoreOf (cen t) :=
    l66_oddCoreOf_le_of_normal (l66_M_le_cen n t) (Sec6M_cen_normal n t)
  have hcL : c ∈ normalizer (L : Set X) :=
    pPrimeCoreOf_le_normalizer_of_isPCompIn (l66_isPCompIn (Or.inr hL)) (hWO hc)
  have hcP : c ∈ normalizer (sec6Piece L e : Set X) :=
    l66_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf hcL (Subgroup.le_normalizer hce))
  have hpW : p ∈ normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
    l66_cen_le_normalizer_W n t (hPt hp)
  have hcomP : ⁅c, p⁆ ∈ sec6Piece L e := by
    rw [commutatorElement_def]
    exact (sec6Piece L e).mul_mem ((Subgroup.mem_normalizer_iff.1 hcP p).1 hp)
      ((sec6Piece L e).inv_mem hp)
  have hcomW : ⁅c, p⁆ ∈ oddCoreOf (Sec6M X n (cen t)) := by
    have h1 : ⁅c, p⁆ = c * (p * c⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact (oddCoreOf (Sec6M X n (cen t))).mul_mem hc
      ((Subgroup.mem_normalizer_iff.1 hpW c⁻¹).1 ((oddCoreOf (Sec6M X n (cen t))).inv_mem hc))
  have hPO : oddCoreOf (sec6Piece L e) = ⊥ :=
    l66_oddCoreOf_eq_bot (l66_isPCompIn (l66_piece_mem hC hU h65 he he2 hL))
      (l66_core_bot h65 he he2)
  have hle : sec6Piece L e ⊓ oddCoreOf (Sec6M X n (cen t)) ≤ oddCoreOf (sec6Piece L e) :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
        (l66_cen_le_normalizer_W n t (hPt hg)))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  have h := hle ⟨hcomP, hcomW⟩
  rw [hPO, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem l66_W_le_cen
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) {x : X} (hxL : x ∈ L)
    (hx2 : orderOf x = 2) : oddCoreOf (Sec6M X n (cen t)) ≤ cen x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL
  have hxM := hLM hxL
  have hPmem := l66_piece_mem hC hU h65 hxM hx2 hL
  have hPO : oddCoreOf (sec6Piece L x) = ⊥ :=
    l66_oddCoreOf_eq_bot (l66_isPCompIn hPmem) (l66_core_bot h65 hxM hx2)
  have hPL : sec6Piece L x ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPx : sec6Piece L x ≤ cen x := (oTwoPrimeOf_le _).trans inf_le_right
  have hxP : x ∈ sec6Piece L x :=
    l66_mem_oTwoPrimeOf ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ (l66_sq_eq_one hx2)
  have hPn : IsDoubleCoverOfAlt ↥(sec6Piece L x) n := by
    rcases hPmem with hA | hM
    · exact isDoubleCoverOfAlt_congr' ((QuotientGroup.quotientMulEquivOfEq
        (l66_pPrimeCore_eq_bot hPO)).trans QuotientGroup.quotientBot) hA.2
    · exfalso
      have h1 := l66_eq_one_of_central (l66_center_quot_eq_bot hM) hPO hxP
        fun p hp => Subgroup.mem_centralizer_singleton_iff.1 (hPx hp)
      rw [h1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
  obtain ⟨u, hu2, hunc⟩ : ∃ u : ↥(sec6Piece L x), u ^ 2 = 1 ∧ u ∉ center ↥(sec6Piece L x) := by
    rcases hS.deg with h8 | h11
    · rw [h8] at hPn
      exact GH74.GLS.Stage12.McLRec.coverFacts_eight.exists_noncentral _ hPn
    · rw [h11] at hPn
      exact Sporadic.Recognition.LyonsSims.coverFacts_eleven.exists_noncentral _ hPn
  have hu1 : (u : X) ≠ 1 := fun h => hunc (by rw [show u = 1 from Subtype.ext h]; exact one_mem _)
  have hux' : (u : X) ≠ x := by
    intro h
    apply hunc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hPx g.2)
  have hu2' : (u : X) ^ 2 = 1 := by
    have := congrArg Subtype.val hu2
    simpa using this
  have hux : (u : X) * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 (hPx u.2)
  have hEab := l66_isElemAbelian_pair (l66_sq_eq_one hx2) hu2' hux.symm
  have hEcard : 2 ^ 2 ≤ Nat.card (Subgroup.closure ({x, (u : X)} : Set X)) := by
    obtain ⟨V, hVE, -, hV4⟩ :=
      LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hx2
        (orderOf_eq_prime hu2' hu1) hux.symm (Ne.symm hux')
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV4]
    exact Subgroup.card_le_of_le hVE
  have hEM : Subgroup.closure ({x, (u : X)} : Set X) ≤ Sec6M X n (cen t) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact hxM
    · rw [Set.mem_singleton_iff.mp h]
      exact hLM (hPL u.2)
  have hEx : Subgroup.closure ({x, (u : X)} : Set X) ≤ cen x := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · rw [Set.mem_singleton_iff.mp h]
      exact hPx u.2
  have hEN : Subgroup.closure ({x, (u : X)} : Set X) ≤
      normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
    hEM.trans ((l66_M_le_cen n t).trans (l66_cen_le_normalizer_W n t))
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreOf (Sec6M X n (cen t)))) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf _)
  rw [← SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hEab hEcard
    hEN hcop]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  have hao : orderOf a = 2 := orderOf_eq_prime (hEab.2 a haE) ha1
  have hxPa : x ∈ sec6Piece L a :=
    l66_mem_oTwoPrimeOf ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEx haE)).symm⟩ (l66_sq_eq_one hx2)
  intro c hc
  exact Subgroup.mem_centralizer_singleton_iff.2
    (l66_cW_comm hC hU h65 (hEM haE) hao hL hc.1 hc.2 hxPa)

private theorem l66_M_le_centralizer_W
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t) :
    Sec6M X n (cen t) ≤ centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) := by
  refine sSup_le fun L hL => ?_
  have hq := l66_isTwoGenQuasi (Or.inr hL)
  have hLN : L ≤ normalizer (centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) : Set X) :=
    fun g hg => l66_mem_normalizer_centralizer
      (l66_cen_le_normalizer_W n t ((l66_isPCompIn (Or.inr hL)).1 hg))
  obtain ⟨v, hvL, hv2⟩ := l66_exists_involution hq
  have hvC : v ∈ centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (l66_W_le_cen hS hC hU h65 hL hvL hv2 hw)
  exact l66_le_of_normalizes hq (l66_center_quot_eq_bot hL) hLN hvL hv2 hvC

end Central

end CFSG.OddStandard.Solomon75
