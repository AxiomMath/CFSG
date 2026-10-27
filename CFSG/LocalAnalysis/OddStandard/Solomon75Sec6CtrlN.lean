module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlNDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma51B
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyAllInnerThm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section CtrlN

variable {X : Type} [Group X] [Finite X]

private theorem cn_conj_mem {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M) {x : X}
    (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem cn_mem_normalizer {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨cn_conj_mem h, fun hx => ?_⟩
  have := cn_conj_mem h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private theorem cn_commutatorElement_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
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

private theorem cn_isPCompIn {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsPCompIn 2 H J := by
  rcases h with ⟨⟨u, -, -, hpc, -⟩, -⟩ | ⟨⟨hpc, -⟩, -⟩
  · exact hpc
  · exact hpc

private theorem cn_isTwoGenQuasi {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsTwoGenQuasi ↥J :=
  (isTwoGenQuasi_subgroupOf_iff (cn_isPCompIn h).1).1
    (isPComponent_two_iff.1 (cn_isPCompIn h).2).2

private theorem cn_exists_involution {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
    ∃ v ∈ L, orderOf v = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥L := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨a, b, hab⟩ := hq.2.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hdvd : 2 ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := primeResidual_eq_bot_of_coprime_card (G := ↥L) 2 hcop
    rw [hq.1] at h1
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

private theorem cn_eq_top_of_isPComponent {G : Type} [Group G] [Finite G] (hG : IsQuasisimple G)
    {K : Subgroup G} (hK : IsPComponent 2 K) : K = ⊤ := by
  obtain ⟨hsub, hq⟩ := isPComponent_two_iff.1 hK
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hG hsub with h | h
  · exact h
  · exfalso
    refine not_commutator_le_of_odd hq (R := ⊥) (by simp) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (h ha) b).symm

private theorem cn_isSubnormal_inf {K D D' H : Subgroup X} (hHD : H ≤ D) (hHD' : H ≤ D')
    (hK : (K.subgroupOf D).IsSubnormal) : ((K ⊓ D').subgroupOf H).IsSubnormal := by
  have h1 : (K ⊓ D').subgroupOf H = (K.subgroupOf D).comap (Subgroup.inclusion hHD) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hHD' x.2⟩⟩
  rw [h1]
  exact hK.comap _

private theorem cn_isPCompIn_oTwoPrimeOf {H A : Subgroup X} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).IsSubnormal) (hq : IsTwoGenQuasi ↥(oTwoPrimeOf A)) :
    IsPCompIn 2 H (oTwoPrimeOf A) := by
  have hEH : oTwoPrimeOf A ≤ H := (oTwoPrimeOf_le A).trans hAH
  refine ⟨hEH, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hEH).2 hq⟩⟩
  exact isSubnormal_subgroupOf_of_normal_of_subnormal hAH (oTwoPrimeOf_le A) hA
    (normal_subgroupOf_oTwoPrimeOf A)

private theorem cn_exists_mul_of_mem_sup {H N : Subgroup X}
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

private theorem cn_inf_le_oddCoreOf {L N : Subgroup X} (hLN : L ≤ normalizer (N : Set X))
    (hN : Odd (Nat.card N)) : L ⊓ N ≤ oddCoreOf L :=
  le_oddCoreOf_of_normalized inf_le_left
    (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg) (hLN hg))
    (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

private theorem cn_degree
    {n : ℕ} {L J : Subgroup X}
    {v : X} (hT : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L)) (hvL : v ∈ L) (hv : orderOf v = 2)
    (hJ : IsAhatIntr X v J) (hJcov : J ≤ (L ⊓ cen v) ⊔ oddCoreOf (cen v)) :
    IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, -, hJpc, -⟩ := hJ
  obtain ⟨J', hJ'CL, hJ'pc, -, -, ⟨q₁⟩⟩ := exists_isPComponent_inf_of_covered
    (C := cen v) (H := L) (O := oddCoreOf (cen v)) (E := L ⊓ cen v) (J := J)
    (oddCoreOf_le _) (le_normalizer_oddCoreOf _) (odd_card_oddCoreOf _) inf_le_right inf_le_left
    hJC hJpc hJcov
  have hJ'C : J' ≤ cen v := hJ'CL.trans inf_le_left
  have hJ'L : J' ≤ L := hJ'CL.trans inf_le_right
  set v' : ↥L := ⟨v, hvL⟩ with hv'def
  have hY : centralizer ({v'} : Set ↥L) = (cen v).subgroupOf L :=
    centralizer_singleton_subgroup hvL
  have hJ''Y : J'.subgroupOf L ≤ centralizer ({v'} : Set ↥L) := by
    rw [hY]
    exact Subgroup.subgroupOf_mono L hJ'C
  have hJ''pc : IsPComponent 2 ((J'.subgroupOf L).subgroupOf (centralizer ({v'} : Set ↥L))) := by
    rw [hY]
    exact (isPComponent_subgroupOf_subgroupOf_iff hJ'C hJ'L).2 hJ'pc
  set π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' (pPrimeCore 2 ↥L)
  have hker : ¬ 2 ∣ Nat.card π.ker :=
    CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker
  have hv'2 : v' * v' = 1 := by
    apply Subtype.ext
    show v * v = 1
    rw [← sq, ← hv]
    exact pow_orderOf_eq_one v
  have hCeq : centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L)) =
      (centralizer ({v'} : Set ↥L)).map π :=
    CFSG.ComponentClassification.GSThmB.OddQuot.centralizer_singleton_map_eq hv'2
  have hK := CFSG.ComponentClassification.GSThmB.OddQuot.isPComponent_map π hker hJ''Y hJ''pc
  rw [← hCeq] at hK
  have hπv : orderOf (π v') = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, hv'2, map_one]
    · intro h1
      have hmem : v' ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff v').1 h1
      have h3 := Subgroup.orderOf_dvd_natCard _ hmem
      have h4 : orderOf v' = 2 := by
        rw [hv'def, Subgroup.orderOf_mk]
        exact hv
      rw [h4] at h3
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
        Nat.coprime_two_left.1 pPrimeCore_coprime_card
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) n := by
    rcases hT with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
          he hπv
      exact isDoubleCoverOfAlt_of_cover hπv (by norm_num) h1 h2 h3
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple he (π v') hπv
      exact ⟨h1, h2, h3⟩
  have htop : ((J'.subgroupOf L).map π).subgroupOf
      (centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) = ⊤ :=
    cn_eq_top_of_isPComponent hC.1 hK
  have hmapC : (J'.subgroupOf L).map π = centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L)) := by
    refine le_antisymm ?_ (Subgroup.subgroupOf_eq_top.1 htop)
    rw [hCeq]
    exact Subgroup.map_mono hJ''Y
  obtain ⟨q₂⟩ :=
    CFSG.ComponentClassification.GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π hker
      (J'.subgroupOf L)
  obtain ⟨q₃⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr hmapC)
  obtain ⟨q₅⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ'L)
  have hbot := pPrimeCore_eq_bot_of_doubleCover hC
  let q₄ : ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ⧸
      pPrimeCore 2 ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ≃*
      ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact isDoubleCoverOfAlt_congr' (q₁.symm.trans (q₅.symm.trans (q₂.trans (q₃.trans q₄)))).symm hC

private theorem cn_card_lt
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

private theorem cn_mem_normalizer_of_map_le {V : Subgroup X} {b : X}
    (h : V.map (MulAut.conj b).toMonoidHom ≤ V) : b ∈ normalizer (V : Set X) :=
  mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]))

private theorem cn_mem_normalizer_oTwoPrimeOf {A : Subgroup X} {g : X}
    (hg : g ∈ normalizer (A : Set X)) : g ∈ normalizer (oTwoPrimeOf A : Set X) := by
  apply cn_mem_normalizer_of_map_le
  have := map_oTwoPrimeOf_le A (MulAut.conj g).toMonoidHom
  rwa [map_conj_eq_of_mem_normalizer hg] at this

private theorem cn_odd_card_sup {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup X)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

private theorem cn_oddCoreOf_le_of_normal {K C : Subgroup X} (hKC : K ≤ C)
    (hn : C ≤ normalizer (K : Set X)) : oddCoreOf K ≤ oddCoreOf C :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le K).trans hKC)
    (fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (hn hc)) (odd_card_oddCoreOf K)

private theorem cn_conj_mem_cs {K M : Subgroup X} {c x : X}
    (hcK : c ∈ normalizer (K : Set X)) (hcM : c ∈ normalizer (M : Set X))
    (hx : x ∈ centralizerSection K M) : c * x * c⁻¹ ∈ centralizerSection K M := by
  obtain ⟨hxK, hxM, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem hcK hxK) (inv_mem hcK), mul_mem (mul_mem hcM hxM) (inv_mem hcM),
    fun k hk => ?_⟩
  have hk' : c⁻¹ * k * c⁻¹⁻¹ ∈ K := (mem_normalizer_iff.1 (inv_mem hcK) k).1 hk
  have h2 : c * ⁅c⁻¹ * k * c⁻¹⁻¹, x⁆ * c⁻¹ ∈ M := (mem_normalizer_iff.1 hcM _).1 (hxc _ hk')
  have h3 : ⁅k, c * x * c⁻¹⁆ = c * ⁅c⁻¹ * k * c⁻¹⁻¹, x⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h3]
  exact h2

private theorem cn_le_normalizer_QOf (L : Subgroup X) : L ≤ normalizer (QOf L : Set X) := by
  intro m hm
  have hmL : m ∈ normalizer (L : Set X) := Subgroup.le_normalizer hm
  have hmO : m ∈ normalizer (pPrimeCoreOf 2 L : Set X) := mem_normalizer_pPrimeCoreOf_of_mem hm
  rw [mem_normalizer_iff]
  intro x
  refine ⟨cn_conj_mem_cs hmL hmO, fun hx => ?_⟩
  have h1 := cn_conj_mem_cs (inv_mem hmL) (inv_mem hmO) hx
  have h2 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [h2] at h1

private theorem cn_exists_inner {L : Subgroup X} {x : X} (hx : x ∈ L ⊔ QOf L) :
    ∃ m ∈ L, m⁻¹ * x ∈ QOf L := by
  obtain ⟨m, hm, k, hk, rfl⟩ := cn_exists_mul_of_mem_sup (cn_le_normalizer_QOf L) hx
  exact ⟨m, hm, by rwa [inv_mul_cancel_left]⟩

private theorem cn_oddCoreOf_le_QOf (L : Subgroup X) : oddCoreOf L ≤ QOf L := by
  intro o ho
  have hoL : o ∈ L := oddCoreOf_le L ho
  refine mem_QOf_iff.2 ⟨Subgroup.le_normalizer hoL, fun l hl => ?_⟩
  have h1 : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by rw [commutatorElement_def]
  rw [h1]
  exact (oddCoreOf L).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf L hl) o).1 ho)
    ((oddCoreOf L).inv_mem ho)

private theorem cn_QOf_le_normalizer (L : Subgroup X) : QOf L ≤ normalizer (L : Set X) :=
  fun _ hc => (mem_QOf_iff.1 hc).1

private theorem cn_sup_QOf_le_normalizer (L : Subgroup X) :
    L ⊔ QOf L ≤ normalizer (L : Set X) :=
  sup_le Subgroup.le_normalizer (cn_QOf_le_normalizer L)

private theorem cn_K_le (n : ℕ) (t : X) : Sec6K X n (cen t) ≤ cen t :=
  sSup_le fun _ hL => (cn_isPCompIn hL).1

private theorem cn_le_QOf_of_ne {H L J : Subgroup X} (hL : IsPCompIn 2 H L)
    (hJ : IsPCompIn 2 H J) (hne : L ≠ J) : J ≤ QOf L := by
  intro j hj
  have hOLL : pPrimeCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hc : ∀ g ∈ J, ∀ m ∈ L, ⁅m, g⁆ ∈ pPrimeCoreOf 2 L := fun g hg m hm =>
    cn_commutatorElement_mem hL hJ hne hm hg
  exact mem_QOf_iff.2 ⟨cn_mem_normalizer (fun m hm => hOLL (hc j hj m hm))
    (fun m hm => hOLL (hc j⁻¹ (J.inv_mem hj) m hm)), fun m hm => hc j hj m hm⟩

private theorem cn_comm_mul (p o y : X) : ⁅p * o, y⁆ = p * ⁅o, y⁆ * p⁻¹ * ⁅p, y⁆ := by
  simp only [commutatorElement_def]
  group

private theorem cn_isPCompIn_piece {H L : Subgroup X} {c : X} (hL : IsPCompIn 2 H L)
    (hq : IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ cen c))) :
    IsPCompIn 2 (H ⊓ cen c) (oTwoPrimeOf (L ⊓ cen c)) :=
  cn_isPCompIn_oTwoPrimeOf (inf_le_inf_right _ hL.1)
    (cn_isSubnormal_inf inf_le_left inf_le_right (isPComponent_two_iff.1 hL.2).1) hq

private theorem cn_card_of_dc {K : Type} [Group K] {m : ℕ} (hm : 2 ≤ m)
    (h : IsDoubleCoverOfAlt K m) : Nat.card K = m.factorial := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [h1, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) hm)

private theorem cn_two_le {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) : 2 ≤ n := by
  rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

private theorem cn_cent_dc
    {n : ℕ} {Q : Type} [Group Q]
    (hT : IsSec6MType n Q) {c : Q} (hc : orderOf c = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({c} : Set Q)) n := by
  rcases hT with ⟨rfl, he⟩ | ⟨rfl, he⟩
  · obtain ⟨h1, h2, h3⟩ :=
      CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
        he hc
    exact isDoubleCoverOfAlt_of_cover hc (by norm_num) h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple he c hc
    exact ⟨h1, h2, h3⟩

private theorem cn_orderOf_mk {M : Subgroup X} {s : X} (hsM : s ∈ M) (hs : orderOf s = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨s, hsM⟩ : ↥M)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs' : orderOf (⟨s, hsM⟩ : ↥M) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hs', pow_orderOf_eq_one, map_one]
  · intro h1
    have hmem : (⟨s, hsM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h1
    have h3 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hs'] at h3
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) :=
      Nat.coprime_two_left.1 pPrimeCore_coprime_card
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

private theorem cn_card_quot_le_of_cen
    {n : ℕ} {M W : Subgroup X} {s : X} (hT : IsSec6MType n (↥M ⧸ pPrimeCore 2 ↥M)) (hsM : s ∈ M)
    (hs : orderOf s = 2) (hWM : W ≤ M) (hWs : ∀ w ∈ W, ⁅w, s⁆ ∈ pPrimeCoreOf 2 M) :
    Nat.card (↥W ⧸ pPrimeCore 2 ↥W) ≤ n.factorial := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥M →* ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set f : ↥W →* ↥M ⧸ pPrimeCore 2 ↥M := π.comp (Subgroup.inclusion hWM) with hf
  have hC := cn_cent_dc hT (cn_orderOf_mk hsM hs)
  have hrange : f.range ≤ centralizer ({π ⟨s, hsM⟩} : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨y, hy, hye⟩ := hWs w w.2
    have hy' : y = ⁅Subgroup.inclusion hWM w, (⟨s, hsM⟩ : ↥M)⁆ := Subtype.ext hye
    have h1 : π ⁅Subgroup.inclusion hWM w, (⟨s, hsM⟩ : ↥M)⁆ = 1 := by
      rw [← hy']
      exact (QuotientGroup.eq_one_iff y).2 hy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hker : f.ker ≤ pPrimeCore 2 ↥W := by
    intro w hw
    have h1 : Subgroup.inclusion hWM w ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hw
    have h2 : (w : X) ∈ W ⊓ pPrimeCoreOf 2 M := ⟨w.2, ⟨_, h1, rfl⟩⟩
    obtain ⟨w', hw', hww'⟩ := cn_inf_le_oddCoreOf
      (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hWM hx)) (odd_card_oddCoreOf M) h2
    have : w' = w := Subtype.ext hww'
    rwa [← this]
  calc Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = (pPrimeCore 2 ↥W).index := (Subgroup.index_eq_card _).symm
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card f.range := Subgroup.index_ker f
    _ ≤ Nat.card ↥(centralizer ({π ⟨s, hsM⟩} : Set (↥M ⧸ pPrimeCore 2 ↥M))) :=
        Subgroup.card_le_of_le hrange
    _ = n.factorial := cn_card_of_dc (cn_two_le hT) hC

private theorem cn_mem_normalizer_sup_of_mem {A B C : Subgroup X} (hAC : A ≤ C)
    (hBn : C ≤ normalizer (B : Set X)) {o : X} (ho : o ∈ B) :
    o ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  apply cn_mem_normalizer_of_map_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a⁻¹ * o * a ∈ B := by
      have := (mem_normalizer_iff.1 (hBn (C.inv_mem (hAC ha))) o).1 ho
      rwa [inv_inv] at this
    have h2 : (MulAut.conj o).toMonoidHom a = a * ((a⁻¹ * o * a) * o⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2]
    exact Subgroup.mul_mem_sup ha (B.mul_mem h1 (B.inv_mem ho))
  · rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact le_sup_right (a := A) (B.mul_mem (B.mul_mem ho hb) (B.inv_mem ho))

private theorem cn_transfer
    {n : ℕ} {M J : Subgroup X}
    {s c : X} (hT : IsSec6MType n (↥M ⧸ pPrimeCore 2 ↥M)) (hsM : s ∈ M) (hs : orderOf s = 2)
    (hc2 : c ^ 2 = 1) (hcs : c ∈ cen s) (hcM : c ∈ normalizer (M : Set X))
    (hcen : ∀ y ∈ M ⊓ cen s, ⁅y, c⁆ ∈ pPrimeCoreOf 2 M)
    (hJ : IsAhatIntr X s J) (hJcov : J ≤ (M ⊓ cen s) ⊔ oddCoreOf (cen s)) :
    oTwoPrimeOf (M ⊓ cen s ⊓ cen c) ≤ J ∧
      J = pPrimeCoreOf 2 J ⊔ oTwoPrimeOf (M ⊓ cen s ⊓ cen c) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := oTwoPrimeOf (M ⊓ cen s) with hR
  set W : Subgroup X := oTwoPrimeOf (M ⊓ cen s ⊓ cen c) with hW
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := cn_degree hT hsM hs hJ hJcov
  obtain ⟨hJC, -, hJpc, -⟩ := hJ
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJC).1 (isPComponent_two_iff.1 hJpc).2
  have hRM : R ≤ M ⊓ cen s := oTwoPrimeOf_le _
  have hWR : W ≤ R := oTwoPrimeOf_mono inf_le_left
  have hRgen : primeResidual 2 ↥R = ⊤ := primeResidual_oTwoPrimeOf _
  have hWgen : primeResidual 2 ↥W = ⊤ := primeResidual_oTwoPrimeOf _
  have hcR : c ∈ normalizer (R : Set X) :=
    cn_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf hcM (Subgroup.le_normalizer hcs))
  have hcomm : ∀ r ∈ R, ⁅r, c⁆ ∈ pPrimeCoreOf 2 R := by
    intro r hr
    have h1 : ⁅r, c⁆ ∈ pPrimeCoreOf 2 M := hcen r (hRM hr)
    have h2 : ⁅r, c⁆ ∈ R := by
      have h3 : ⁅r, c⁆ = r * (c * r⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact R.mul_mem hr ((mem_normalizer_iff.1 hcR r⁻¹).1 (R.inv_mem hr))
    exact cn_inf_le_oddCoreOf (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hRM hx).1)
      (odd_card_oddCoreOf M) ⟨h2, h1⟩
  have hcRc : c ∈ centralizerSection R (pPrimeCoreOf 2 R) :=
    ⟨hcR, mem_normalizer_oddCoreOf_of_mem_normalizer hcR, hcomm⟩
  have hcovR := oTwoPrimeOf_inf_centralizer_covers hc2 hRgen hcRc
  have hRW : R ≤ pPrimeCoreOf 2 R ⊔ W := by
    have h1 := (covers_subgroupOf_iff ((oTwoPrimeOf_le _).trans inf_le_left)).1 hcovR
    exact h1.symm.le.trans
      (sup_le (le_sup_of_le_right (oTwoPrimeOf_mono (inf_le_inf_right _ hRM))) le_sup_left)
  set Z : Subgroup X := R ⊔ oddCoreOf (cen s) with hZ
  have hJZ : J ≤ Z := by
    have hJself : oTwoPrimeOf J = J := oTwoPrimeOf_eq_self_of_primeResidual hJq.1
    rw [← hJself, oTwoPrimeOf_le_iff]
    rintro x hx ⟨k, hk⟩
    obtain ⟨o, ho, a, ha, hak, rfl⟩ := exists_conj_twoElt_of_mem_sup_odd_X
      (A := M ⊓ cen s) (N := oddCoreOf (cen s))
      (fun y hy => le_normalizer_oddCoreOf (cen s) (Subgroup.mem_inf.1 hy).2)
      (odd_card_oddCoreOf (cen s)) (hJcov hx) hk
    have haR : a ∈ R := mem_oTwoPrimeOf ha k hak
    have hoZ : o ∈ Z := le_sup_right (a := R) ho
    exact Z.mul_mem (Z.mul_mem hoZ (le_sup_left (b := oddCoreOf (cen s)) haR)) (Z.inv_mem hoZ)
  have hZs : Z ≤ cen s := sup_le (hRM.trans inf_le_right) (oddCoreOf_le _)
  have hJZpc : IsPCompIn 2 Z J := by
    refine ⟨hJZ, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hJZ).2 hJq⟩⟩
    have h1 : J.subgroupOf Z = (J.subgroupOf (cen s)).comap (Subgroup.inclusion hZs) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
    rw [h1]
    exact (isPComponent_two_iff.1 hJpc).1.comap _
  have hWZ : W ≤ Z := hWR.trans le_sup_left
  set N : Subgroup X := oddCoreOf R ⊔ oddCoreOf (cen s) with hN
  have hNodd : Odd (Nat.card N) :=
    cn_odd_card_sup (fun x hx => le_normalizer_oddCoreOf (cen s) ((hRM ((oddCoreOf_le R) hx)).2))
      (odd_card_oddCoreOf R) (odd_card_oddCoreOf _)
  have hNZ : N ≤ Z := sup_le ((oddCoreOf_le R).trans le_sup_left) le_sup_right
  have hZN : Z ≤ normalizer (N : Set X) := by
    refine sup_le (fun r hr => ?_) (fun o ho => ?_)
    · exact mem_normalizer_sup (le_normalizer_oddCoreOf R hr)
        (le_normalizer_oddCoreOf (cen s) (hRM hr).2)
    · exact cn_mem_normalizer_sup_of_mem (C := cen s)
        (fun x hx => ((hRM ((oddCoreOf_le R) hx)).2)) (le_normalizer_oddCoreOf (cen s)) ho
  have hNO : N ≤ oddCoreOf Z := le_oddCoreOf_of_normalized hNZ hZN hNodd
  have hWcovZ : W.subgroupOf Z ⊔ pPrimeCore 2 ↥Z = ⊤ := by
    rw [covers_subgroupOf_iff hWZ]
    refine le_antisymm (sup_le hWZ (Subgroup.map_subtype_le _)) ?_
    have h1 : Z ≤ W ⊔ N := by
      refine sup_le (hRW.trans (sup_le ?_ le_sup_left)) ?_
      · exact le_sup_left.trans le_sup_right
      · exact le_sup_right.trans le_sup_right
    exact h1.trans (sup_le_sup_left hNO _)
  have hZW : Nat.card (↥Z ⧸ pPrimeCore 2 ↥Z) ≤ Nat.card (↥W ⧸ pPrimeCore 2 ↥W) :=
    card_quot_pPrimeCore_le_of_covers hWZ le_rfl hWcovZ
  have hWn : Nat.card (↥W ⧸ pPrimeCore 2 ↥W) ≤ n.factorial :=
    cn_card_quot_le_of_cen hT hsM hs (hWR.trans (hRM.trans inf_le_left)) fun w hw => by
      have hws : w * s = s * w :=
        Subgroup.mem_centralizer_singleton_iff.1 ((hWR.trans (hRM.trans inf_le_right)) hw)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hws]
      exact one_mem _
  have hJcard : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = n.factorial :=
    cn_card_of_dc (cn_two_le hT) hJn
  have hJcovZ : J.subgroupOf Z ⊔ pPrimeCore 2 ↥Z = ⊤ :=
    covers_of_card_le hJZ (hZW.trans (hWn.trans hJcard.ge))
  have hWJ : W ≤ J := by
    refine le_of_le_sup_pPrimeCoreOf hJZpc hWZ hWgen ?_
    rw [(covers_subgroupOf_iff hJZ).1 hJcovZ]
    exact hWZ
  have hJZc : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) ≤ Nat.card (↥Z ⧸ pPrimeCore 2 ↥Z) :=
    card_quot_pPrimeCore_le_of_covers le_rfl hJZ (by rw [Subgroup.subgroupOf_self, top_sup_eq])
  have hWcovJ : W.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := covers_of_card_le hWJ (hJZc.trans hZW)
  refine ⟨hWJ, ?_⟩
  rw [sup_comm]
  exact ((covers_subgroupOf_iff hWJ).1 hWcovJ).symm

private theorem cn_mem_of_central {L : Subgroup X} (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥)
    {g : X} (hgL : g ∈ L) (hg : ∀ l ∈ L, ⁅l, g⁆ ∈ pPrimeCoreOf 2 L) : g ∈ pPrimeCoreOf 2 L := by
  set π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hcen : π ⟨g, hgL⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) x
    obtain ⟨y, hy, hye⟩ := hg l l.2
    have hy' : y = ⁅l, (⟨g, hgL⟩ : ↥L)⁆ := Subtype.ext hye
    have h1 : π ⁅l, (⟨g, hgL⟩ : ↥L)⁆ = 1 := by
      rw [← hy']
      exact (QuotientGroup.eq_one_iff y).2 hy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  rw [hZ, Subgroup.mem_bot] at hcen
  exact ⟨⟨g, hgL⟩, (QuotientGroup.eq_one_iff _).1 hcen, rfl⟩

private theorem cn_comm_mem {L : Subgroup X} {a b x : X} (hxL : x ∈ L) (hab : a⁻¹ * b ∈ QOf L)
    (hxa : x * a = a * x) (haN : a ∈ normalizer (pPrimeCoreOf 2 L : Set X)) :
    ⁅x, b⁆ ∈ pPrimeCoreOf 2 L := by
  have h1 : ⁅x, a⁻¹ * b⁆ ∈ pPrimeCoreOf 2 L := (mem_QOf_iff.1 hab).2 x hxL
  have h2 : ⁅x, b⁆ = a * ⁅x, a⁻¹ * b⁆ * a⁻¹ := by
    have hx' : a * x * a⁻¹ = x := by rw [← hxa, mul_inv_cancel_right]
    calc ⁅x, b⁆ = (a * x * a⁻¹) * b * x⁻¹ * b⁻¹ := by rw [hx', commutatorElement_def]
      _ = a * ⁅x, a⁻¹ * b⁆ * a⁻¹ := by rw [commutatorElement_def]; group
  rw [h2]
  exact (mem_normalizer_iff.1 haN _).1 h1

private theorem cn_exists_inv_inner {L : Subgroup X} {c : X}
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) (hc2 : c ^ 2 = 1) (hcL : c ∈ L ⊔ QOf L)
    (hc : c ∉ QOf L) : ∃ v ∈ L ⊓ cen c, orderOf v = 2 ∧ v⁻¹ * c ∈ QOf L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmL, hmq⟩ := cn_exists_inner hcL
  set q : X := m⁻¹ * c with hq
  have hcmq : c = m * q := by rw [hq, mul_inv_cancel_left]
  have hcN : c ∈ normalizer (L : Set X) := cn_sup_QOf_le_normalizer L hcL
  have hcO : c ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hcN
  have hOQ : pPrimeCoreOf 2 L ≤ QOf L := cn_oddCoreOf_le_QOf L
  have hm2Q : m ^ 2 ∈ QOf L := by
    have h3 : m * (q * m * q) = 1 := by
      rw [← hc2, hcmq, pow_two]
      group
    have h4 : q * m * q = m⁻¹ := eq_inv_of_mul_eq_one_right h3
    have key : m ^ 2 = q⁻¹ * (m⁻¹ * q⁻¹ * m⁻¹⁻¹) := by
      rw [pow_two, inv_inv, ← h4]
      group
    rw [key]
    refine (QOf L).mul_mem ((QOf L).inv_mem hmq) ?_
    exact (mem_normalizer_iff.1 (cn_le_normalizer_QOf L (L.inv_mem hmL)) _).1
      ((QOf L).inv_mem hmq)
  have hm2O : m ^ (2 ^ 1) ∈ pPrimeCoreOf 2 L := by
    rw [pow_one]
    exact cn_mem_of_central hZ (L.pow_mem hmL 2) fun l hl => (mem_QOf_iff.1 hm2Q).2 l hl
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 L)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf L)
  obtain ⟨k, hk2, hmk⟩ := exists_zpow_twoElt_of_pow_mem hOcop hm2O
  set y : X := m ^ k with hy
  have hyL : y ∈ L := L.zpow_mem hmL k
  have hyc : y⁻¹ * c ∈ QOf L := by
    have h1 : y⁻¹ * c = (m⁻¹ * y)⁻¹ * q := by rw [hq]; group
    rw [h1]
    exact (QOf L).mul_mem (hOQ ((pPrimeCoreOf 2 L).inv_mem hmk)) hmq
  have hyt : ⁅y, c⁆ ∈ pPrimeCoreOf 2 L :=
    cn_comm_mem hyL hyc rfl (mem_normalizer_pPrimeCoreOf_of_mem hyL)
  obtain ⟨v, hv, hv2, hvy⟩ := exists_twoElt_centralizer_of_comm_mem hc2 hcO hyL hyt hk2
  refine ⟨v, hv, orderOf_eq_prime (by simpa using hv2) ?_, ?_⟩
  · rintro rfl
    apply hc
    have hyO : y ∈ pPrimeCoreOf 2 L := by simpa using hvy
    have hmO : m ∈ pPrimeCoreOf 2 L := by
      have h1 : m = y * (m⁻¹ * y)⁻¹ := by group
      rw [h1]
      exact (pPrimeCoreOf 2 L).mul_mem hyO ((pPrimeCoreOf 2 L).inv_mem hmk)
    rw [hcmq]
    exact (QOf L).mul_mem (hOQ hmO) hmq
  · have h1 : v⁻¹ * c = (v⁻¹ * y) * (y⁻¹ * c) := by group
    rw [h1]
    exact (QOf L).mul_mem (hOQ hvy) hyc

private theorem cn_piece_M_inner
    {n : ℕ} {H : Subgroup X} {c : X}
    {L : Subgroup X} (hc2 : orderOf c = 2) (hL : Sec6MComp X n H L)
    (hcL : c ∈ L ⊔ QOf L) (hc : c ∉ QOf L) :
    Sec5Comp X n (H ⊓ cen c) (oTwoPrimeOf (L ⊓ cen c)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hLpc, htype, hLJ⟩, hT⟩ := hL
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := mcLLyCenterFree _ htype
  have hc2' : c ^ 2 = 1 := by
    rw [← hc2]
    exact pow_orderOf_eq_one c
  obtain ⟨v, ⟨hvL, hvc⟩, hv, hvq⟩ := cn_exists_inv_inner hZ hc2' hcL hc
  set P : Subgroup X := oTwoPrimeOf (L ⊓ cen c) with hP
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPc : P ≤ cen c := (oTwoPrimeOf_le _).trans inf_le_right
  have hv2 : v ^ 2 = 1 := by
    rw [← hv]
    exact pow_orderOf_eq_one v
  have hvP : v ∈ P := mem_oTwoPrimeOf ⟨hvL, hvc⟩ 1 (by simpa using hv2)
  have hcN : c ∈ normalizer (L : Set X) := cn_sup_QOf_le_normalizer L hcL
  have hcO : c ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hcN
  have hcv : c ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvc).symm
  obtain ⟨J, hJ, hJcov⟩ := hLJ v hvL hv
  obtain ⟨hWJ, hJeq⟩ := cn_transfer hT hvL hv hc2' hcv hcN
    (fun y hy => cn_comm_mem hy.1 hvq (Subgroup.mem_centralizer_singleton_iff.1 hy.2)
      (mem_normalizer_pPrimeCoreOf_of_mem hvL)) hJ hJcov
  set W : Subgroup X := oTwoPrimeOf (L ⊓ cen v ⊓ cen c) with hW
  have hWP : W = oTwoPrimeOf (P ⊓ cen v) := by
    refine le_antisymm ?_ (oTwoPrimeOf_mono fun x hx => ⟨⟨hPL hx.1, hx.2⟩, hPc hx.1⟩)
    rw [oTwoPrimeOf_le_iff]
    intro x hx h2
    exact mem_oTwoPrimeOf_of_twoElt ⟨mem_oTwoPrimeOf_of_twoElt ⟨hx.1.1, hx.2⟩ h2, hx.1.2⟩ h2
  have hWcovJ : W.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
    rw [covers_subgroupOf_iff hWJ, sup_comm]
    exact hJeq.symm
  obtain ⟨eWJ⟩ := nonempty_quot_mulEquiv_of_covers hWJ hWcovJ
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := cn_degree hT hvL hv hJ hJcov
  have hWPle : W ≤ P := by
    rw [hWP]
    exact (oTwoPrimeOf_le _).trans inf_le_left
  have hcv' : c⁻¹ * v ∈ QOf L := by
    have h1 : c⁻¹ * v = (v⁻¹ * c)⁻¹ := by group
    rw [h1]
    exact (QOf L).inv_mem hvq
  have hPcard : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) ≤ n.factorial :=
    cn_card_quot_le_of_cen hT hvL hv hPL fun p hp =>
      cn_comm_mem (hPL hp) hcv' (Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)) hcO
  have hWcard : Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = n.factorial := by
    rw [Nat.card_congr eWJ.toEquiv]
    exact cn_card_of_dc (cn_two_le hT) hJn
  have hWcovP : W.subgroupOf P ⊔ pPrimeCore 2 ↥P = ⊤ :=
    covers_of_card_le hWPle (hPcard.trans hWcard.ge)
  obtain ⟨eWP⟩ := nonempty_quot_mulEquiv_of_covers hWPle hWcovP
  have hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n :=
    isDoubleCoverOfAlt_congr' (eWJ.symm.trans eWP) hJn
  have hPq : IsTwoGenQuasi ↥P := ⟨primeResidual_oTwoPrimeOf _, hPn.1⟩
  have hPpc : IsPCompIn 2 (H ⊓ cen c) P := cn_isPCompIn_piece hLpc hPq
  refine ⟨⟨v, hv, hvP, hPpc, ?_, J, hJ, ?_⟩, hPn⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, ← hWP, sup_comm]
    exact ((covers_subgroupOf_iff hWPle).1 hWcovP).symm
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, ← hWP]
    exact hJeq

private theorem cn_card_quot_le_range {M W : Subgroup X} (hWM : W ≤ M) :
    Nat.card (↥W ⧸ pPrimeCore 2 ↥W) ≤
      Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hWM)).range := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥W →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hWM) with hf
  have hker : f.ker ≤ pPrimeCore 2 ↥W := by
    intro w hw
    have h1 : Subgroup.inclusion hWM w ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hw
    have h2 : (w : X) ∈ W ⊓ pPrimeCoreOf 2 M := ⟨w.2, ⟨_, h1, rfl⟩⟩
    obtain ⟨w', hw', hww'⟩ := cn_inf_le_oddCoreOf
      (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hWM hx)) (odd_card_oddCoreOf M) h2
    have : w' = w := Subtype.ext hww'
    rwa [← this]
  calc Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = (pPrimeCore 2 ↥W).index := (Subgroup.index_eq_card _).symm
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card f.range := Subgroup.index_ker f

private theorem cn_quotConj_mk {A : Subgroup X} {c : X} (hc : c ∈ normalizer (A : Set X))
    (a : ↥A) : quotConj hc (QuotientGroup.mk a) = QuotientGroup.mk (conjAut hc a) := rfl

private theorem cn_inner_of_conj {F : Subgroup X} {t : X} (htN : t ∈ normalizer (F : Set X))
    {g : ↥F ⧸ pPrimeCore 2 ↥F} (hα : quotConj htN = MulAut.conj g) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(g₀ : X)⁻¹, F.inv_mem g₀.2, fun a ha => ?_⟩
  set a' : ↥F := ⟨a⁻¹, F.inv_mem ha⟩ with ha'
  have h1 : (QuotientGroup.mk (g₀ * a' * g₀⁻¹) : ↥F ⧸ pPrimeCore 2 ↥F) =
      QuotientGroup.mk (conjAut htN a') := by
    rw [← cn_quotConj_mk, hα, MulAut.conj_apply]
    rfl
  rw [QuotientGroup.eq] at h1
  have h2 : (g₀ : X) * a * (g₀ : X)⁻¹ * (t * a⁻¹ * t⁻¹) ∈ pPrimeCoreOf 2 F := by
    refine ⟨_, h1, ?_⟩
    show (((g₀ * a' * g₀⁻¹)⁻¹ * conjAut htN a' : ↥F) : X) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, ha']
    group
  have h3 : ⁅a, (g₀ : X)⁻¹ * t⁆ =
      (g₀ : X)⁻¹ * ((g₀ : X) * a * (g₀ : X)⁻¹ * (t * a⁻¹ * t⁻¹)) * (g₀ : X)⁻¹⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h3]
  exact (mem_normalizer_iff.1 (mem_normalizer_pPrimeCoreOf_of_mem (F.inv_mem g₀.2)) _).1 h2

private theorem cn_inner_ly
    {F : Subgroup X} {t : X} (htN : t ∈ normalizer (F : Set X))
    (he : Nonempty (↥F ⧸ pPrimeCore 2 ↥F ≃* Blueprint.NativeSporadic.Ly)) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨g, hg⟩ :=
    GH74.GLS.Stage2.Bender.Thm1.LyOut.lyAllInner_thm (↥F ⧸ pPrimeCore 2 ↥F) he (quotConj htN)
  exact cn_inner_of_conj htN hg

private theorem cn_mem_fixedSubgroup {G : Type} [Group G] (σ : MulAut G) (x : G) :
    x ∈ CFSG.Sporadic.Recognition.McLAS.fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem cn_mem_mclFixed (σ : MulAut Blueprint.NativeSporadic.McL)
    (x : Blueprint.NativeSporadic.McL) :
    x ∈ CFSG.Sporadic.Recognition.McLAS.mclFixed σ ↔ σ x = x := Iff.rfl

private theorem cn_fixed_iff {Q G : Type} [Group Q] [Mul G] (e : Q ≃* G) (α : MulAut Q)
    (σ : MulAut G) (h : ∀ y, σ (e y) = e (α y)) (y : Q) : α y = y ↔ σ (e y) = e y := by
  rw [h]
  exact ⟨fun h' => by rw [h'], fun h' => e.injective h'⟩

private theorem cn_quotConj_sq {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
    (htN : t ∈ normalizer (F : Set X)) (y : ↥F ⧸ pPrimeCore 2 ↥F) :
    quotConj htN (quotConj htN y) = y := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  rw [cn_quotConj_mk, cn_quotConj_mk]
  congr 1
  apply Subtype.ext
  simp only [coe_conjAut]
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
  rw [hti, ← mul_assoc, ← mul_assoc, ht', one_mul, mul_assoc, ht', mul_one]

private theorem cn_inner_mcl
    {F P : Subgroup X} {t : X}
    (ht2 : t ^ 2 = 1) (htN : t ∈ normalizer (F : Set X))
    (he : Nonempty (↥F ⧸ pPrimeCore 2 ↥F ≃* Blueprint.NativeSporadic.McL)) (hPF : P ≤ F)
    (hPt : P ≤ cen t) (hPcard : 7920 < Nat.card (↥P ⧸ pPrimeCore 2 ↥P)) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨e⟩ := he
  set σ : MulAut Blueprint.NativeSporadic.McL := (e.symm.trans (quotConj htN)).trans e with hσ
  have hσapp : ∀ y, σ (e y) = e (quotConj htN y) := fun y => by
    rw [hσ]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  by_cases hin : σ ∈ ComponentClassification.OuterAutomorphisms.inner Blueprint.NativeSporadic.McL
  · obtain ⟨g, hg⟩ := hin
    refine cn_inner_of_conj htN (g := e.symm g) ?_
    ext y
    have h1 := congrArg (fun φ : MulAut Blueprint.NativeSporadic.McL => φ (e y)) hg
    simp only [MulAut.conj_apply] at h1
    rw [hσapp] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · exfalso
    have hσ2 : orderOf σ = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · ext x
        obtain ⟨y, rfl⟩ := e.surjective x
        rw [pow_two, MulAut.mul_apply, hσapp, hσapp, cn_quotConj_sq ht2 htN, MulAut.one_apply]
      · intro h
        apply hin
        rw [h]
        exact one_mem _
    obtain ⟨eM⟩ :=
      (CFSG.Sporadic.Recognition.McLAS.mcl_outer_involutions_of_certificate).2.2 σ hσ2 hin
    have hfix : Nat.card ↥(CFSG.Sporadic.Recognition.McLAS.mclFixed σ) = 7920 := by
      rw [Nat.card_congr eM.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M11
    have hfixF : Nat.card ↥(CFSG.Sporadic.Recognition.McLAS.fixedSubgroup (quotConj htN)) =
        7920 := by
      rw [← hfix]
      exact Nat.card_congr (e.toEquiv.subtypeEquiv fun y =>
        (cn_mem_fixedSubgroup _ y).trans ((cn_fixed_iff e (quotConj htN) σ hσapp y).trans
          (cn_mem_mclFixed σ (e y)).symm))
    have hrange : ((QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)).range ≤
        CFSG.Sporadic.Recognition.McLAS.fixedSubgroup (quotConj htN) := by
      rintro _ ⟨p, rfl⟩
      rw [cn_mem_fixedSubgroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply, cn_quotConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_conjAut]
      have hp : (p : X) * t = t * p := Subgroup.mem_centralizer_singleton_iff.1 (hPt p.2)
      simp only [Subgroup.coe_inclusion]
      rw [← hp, mul_inv_cancel_right]
    have h1 := Subgroup.card_le_of_le hrange
    have h2 := cn_card_quot_le_range hPF
    omega

private theorem cn_factorial_lt
    {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) : n.factorial < Nat.card Q := by
  rcases hT with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]
    have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ly.card_Ly']
    have h11 : Nat.factorial 11 = 39916800 := by norm_num [Nat.factorial]
    omega

private theorem cn_card_ge
    {n : ℕ} (hn : 2 ≤ n) {H P : Subgroup X} (hP : Sec6KComp X n H P) :
    n.factorial ≤ Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := by
  rcases hP with h5 | h6
  · exact (cn_card_of_dc hn h5.2).ge
  · exact (cn_factorial_lt h6.2).le

private theorem cn_isPCompIn_conj {H F : Subgroup X} {g : X} (hF : IsPCompIn 2 H F)
    (hg : g ∈ normalizer (H : Set X)) : IsPCompIn 2 H (F.map (MulAut.conj g).toMonoidHom) := by
  have h := (isPComponent_subgroupOf_map_iff 2 (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective hF.1).2 hF.2
  rw [map_conj_eq_of_mem_normalizer hg] at h
  refine ⟨?_, h⟩
  rw [← map_conj_eq_of_mem_normalizer hg]
  exact Subgroup.map_mono hF.1

private theorem cn_oddCoreOf_le_of_covers {E F : Subgroup X} (hEF : E ≤ F)
    (hcov : E.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤) : oddCoreOf E ≤ oddCoreOf F := by
  have hEFeq : E ⊔ pPrimeCoreOf 2 F = F := (covers_subgroupOf_iff hEF).1 hcov
  set N : Subgroup X := oddCoreOf E ⊔ oddCoreOf F with hN
  have hNodd : Odd (Nat.card N) :=
    cn_odd_card_sup (fun x hx => le_normalizer_oddCoreOf F (hEF ((oddCoreOf_le E) hx)))
      (odd_card_oddCoreOf E) (odd_card_oddCoreOf F)
  have hNF : N ≤ F := sup_le ((oddCoreOf_le E).trans hEF) (oddCoreOf_le F)
  have hFN : F ≤ normalizer (N : Set X) := by
    refine hEFeq.symm.le.trans (sup_le (fun e he => ?_) (fun o ho => ?_))
    · exact mem_normalizer_sup (le_normalizer_oddCoreOf E he) (le_normalizer_oddCoreOf F (hEF he))
    · exact cn_mem_normalizer_sup_of_mem (C := F) ((oddCoreOf_le E).trans hEF)
        (le_normalizer_oddCoreOf F) ho
  exact le_sup_left.trans (le_oddCoreOf_of_normalized hNF hFN hNodd)

private theorem cn_step1 {n : ℕ} {t v : X} (hvt : v ∈ cen t) (hcov : Sec6Covers X n t v) :
    t ∈ QOf (Sec6K X n (cen v)) := by
  set Kv : Subgroup X := Sec6K X n (cen v) with hKv
  have hc : Kv = oddCoreOf Kv ⊔ (Kv ⊓ Sec6K X n (cen t)) := hcov
  have htv : t ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvt).symm
  have htN : t ∈ normalizer (Kv : Set X) := Sec6K_cen_normal n v htv
  refine mem_QOf_iff.2 ⟨htN, fun k hk => ?_⟩
  have hk' : k ∈ (Kv ⊓ Sec6K X n (cen t)) ⊔ oddCoreOf Kv := by
    rw [sup_comm, ← hc]
    exact hk
  obtain ⟨h, hh, o, ho, rfl⟩ :=
    cn_exists_mul_of_mem_sup (H := Kv ⊓ Sec6K X n (cen t)) (N := oddCoreOf Kv)
      (fun x hx => le_normalizer_oddCoreOf Kv (Subgroup.mem_inf.1 hx).1) hk'
  have htO : t ∈ normalizer (oddCoreOf Kv : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  have h1 : ⁅o, t⁆ ∈ oddCoreOf Kv := by
    have h3 : ⁅o, t⁆ = o * (t * o⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (oddCoreOf Kv).mul_mem ho ((mem_normalizer_iff.1 htO o⁻¹).1 ((oddCoreOf Kv).inv_mem ho))
  have hht : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.1 (cn_K_le n t hh.2)
  have hti : t⁻¹ * h⁻¹ = h⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hht]
  have h2 : ⁅h * o, t⁆ = h * ⁅o, t⁆ * h⁻¹ := by
    calc ⁅h * o, t⁆ = h * o * t * o⁻¹ * (h⁻¹ * t⁻¹) := by
          rw [commutatorElement_def]
          group
      _ = h * o * t * o⁻¹ * (t⁻¹ * h⁻¹) := by rw [hti]
      _ = h * ⁅o, t⁆ * h⁻¹ := by
          rw [commutatorElement_def]
          group
  rw [h2]
  exact (mem_normalizer_iff.1 (le_normalizer_oddCoreOf Kv hh.1) _).1 h1

private theorem cn_induces_one_eq {n : ℕ} {K : Type} [Group K] {C : AhatData.CoverSetup n K}
    {α : MulAut K} (h : C.Induces α 1) : α = 1 := by
  have hz : ∀ x : K, x⁻¹ * α x ∈ center K := by
    intro x
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, h.map_ρ x]
    simp
  have hcomm : ∀ x y : K, α ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    set c₁ := x⁻¹ * α x with hc₁
    set c₂ := y⁻¹ * α y with hc₂
    have e1 : α x = x * c₁ := by rw [hc₁, mul_inv_cancel_left]
    have e2 : α y = y * c₂ := by rw [hc₂, mul_inv_cancel_left]
    have k1 : c₁ * (y * c₂) * c₁⁻¹ = y * c₂ := by
      rw [← (Subgroup.mem_center_iff.1 (hz x) (y * c₂)), mul_inv_cancel_right]
    have k2 : c₂ * x⁻¹ * c₂⁻¹ = x⁻¹ := by
      rw [← (Subgroup.mem_center_iff.1 (hz y) x⁻¹), mul_inv_cancel_right]
    rw [map_commutatorElement, e1, e2]
    simp only [commutatorElement_def, mul_inv_rev]
    calc x * c₁ * (y * c₂) * (c₁⁻¹ * x⁻¹) * (c₂⁻¹ * y⁻¹)
        = x * (c₁ * (y * c₂) * c₁⁻¹) * x⁻¹ * (c₂⁻¹ * y⁻¹) := by group
      _ = x * (y * c₂) * x⁻¹ * (c₂⁻¹ * y⁻¹) := by rw [k1]
      _ = x * y * (c₂ * x⁻¹ * c₂⁻¹) * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [k2]
  have htop : (⊤ : Subgroup K) ≤ AhatData.fixSub α := by
    rw [← Group.isPerfect_def.1 C.hX.1.1, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  ext x
  exact htop (Subgroup.mem_top x)

private theorem cn_sqrt_center {n : ℕ} (hn : 8 ≤ n) {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
    (htN : t ∈ normalizer (F : Set X)) (hFn : IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n)
    (hcent : ¬ CentModOdd F t) :
    ∃ f ∈ F ⊓ cen t, f ^ (2 ^ 2) = 1 ∧ f ^ 2 ∉ pPrimeCoreOf 2 F ∧
      ∀ a ∈ F, ⁅a, f ^ 2⁆ ∈ pPrimeCoreOf 2 F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : AhatData.CoverSetup n (↥F ⧸ pPrimeCore 2 ↥F) := AhatData.CoverSetup.ofCover hFn with hC
  set α : MulAut (↥F ⧸ pPrimeCore 2 ↥F) := quotConj htN with hα
  obtain ⟨σ, hσ⟩ := exists_induces_perm (by omega) (by omega) C α
  have hα2 : α * α = 1 := MulEquiv.ext fun y => cn_quotConj_sq ht2 htN y
  have hσ2 : σ * σ = 1 := by
    have h1 := hσ.mul' hσ
    rw [hα2] at h1
    exact induces_unique (by omega) h1 C.induces_one'
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hcent
    have h1 := cn_induces_one_eq hσ
    intro a ha
    have h2 : α (QuotientGroup.mk ⟨a⁻¹, F.inv_mem ha⟩) = QuotientGroup.mk ⟨a⁻¹, F.inv_mem ha⟩ := by
      rw [h1]
      rfl
    rw [hα, cn_quotConj_mk] at h2
    have h3 := QuotientGroup.eq.1 h2.symm
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut,
      Subgroup.coe_mk, commutatorElement_def, inv_inv]
    group
  obtain ⟨k, hk⟩ := Equiv.Perm.two_dvd_card_support (by rw [pow_two]; exact hσ2)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hσ1
      rw [h0, mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hk
      exact hk
    · exact h0
  obtain ⟨x, hxfix, hx1, hxz⟩ := hσ.exists_mem_fixSub_sq_ne_one hn hσ2 hk hk1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have hx4 : (QuotientGroup.mk a : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ 2) = 1 := by
    have h1 := orderOf_dvd_natCard (⟨_, hxz⟩ : ↥(center (↥F ⧸ pPrimeCore 2 ↥F)))
    rw [hFn.2.1] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    calc (QuotientGroup.mk a : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ 2)
        = (QuotientGroup.mk a * QuotientGroup.mk a) ^ 2 := by
          rw [← pow_two, ← pow_mul]
          norm_num
      _ = 1 := h3
  have ha4 : (a : X) ^ (2 ^ 2) ∈ pPrimeCoreOf 2 F := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx4
    exact ⟨_, hx4, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 F)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf F)
  obtain ⟨m, hm4, ham⟩ := exists_zpow_twoElt_of_pow_mem hOcop ha4
  set y : X := (a : X) ^ m with hy
  have hyF : y ∈ F := F.zpow_mem a.2 m
  have hya : (QuotientGroup.mk (⟨y, hyF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = QuotientGroup.mk a := by
    rw [QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := ham
    have : (⟨y, hyF⟩ : ↥F)⁻¹ * a = w⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      rw [show (w : X) = (a : X)⁻¹ * y from hwe]
      group
    rw [this]
    exact (pPrimeCore 2 ↥F).inv_mem hw
  have htO : t ∈ normalizer (pPrimeCoreOf 2 F : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  have hyt : ⁅y, t⁆ ∈ pPrimeCoreOf 2 F := by
    have h1 : α (QuotientGroup.mk ((⟨y, hyF⟩ : ↥F)⁻¹)) =
        QuotientGroup.mk ((⟨y, hyF⟩ : ↥F)⁻¹) := by
      rw [QuotientGroup.mk_inv, map_inv, hya]
      exact congrArg (·⁻¹) (hxfix : α (QuotientGroup.mk a) = QuotientGroup.mk a)
    rw [hα, cn_quotConj_mk] at h1
    have h3 := QuotientGroup.eq.1 h1.symm
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut,
      Subgroup.coe_mk, commutatorElement_def, inv_inv]
    group
  obtain ⟨c, hc, hc4, hcy⟩ := exists_twoElt_centralizer_of_comm_mem ht2 htO hyF hyt hm4
  have hcF : c ∈ F := hc.1
  have hcx : (QuotientGroup.mk (⟨c, hcF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = QuotientGroup.mk a := by
    rw [← hya, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := hcy
    have : (⟨c, hcF⟩ : ↥F)⁻¹ * ⟨y, hyF⟩ = w := Subtype.ext (by simpa using hwe.symm)
    rw [this]
    exact hw
  refine ⟨c, hc, hc4, ?_, fun a' ha' => ?_⟩
  · rintro ⟨w, hw, hwe⟩
    apply hx1
    rw [← hcx, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have : (⟨c, hcF⟩ : ↥F) * ⟨c, hcF⟩ = w :=
      Subtype.ext (by rw [show (w : X) = c ^ 2 from hwe, pow_two]; rfl)
    rw [this]
    exact hw
  · have hz := Subgroup.mem_center_iff.1 hxz (QuotientGroup.mk ⟨a', ha'⟩)
    rw [← hcx] at hz
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥F) ⁅(⟨a', ha'⟩ : ↥F), ⟨c, hcF⟩ ^ 2⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_pow,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, pow_two]
      exact hz
    refine ⟨_, (QuotientGroup.eq_one_iff _).1 h1, ?_⟩
    show ((⁅(⟨a', ha'⟩ : ↥F), ⟨c, hcF⟩ ^ 2⁆ : ↥F) : X) = _
    simp [commutatorElement_def]

private theorem cn_lift_fixed {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
    (htN : t ∈ normalizer (F : Set X)) (a : ↥F) {j : ℕ}
    (hfix : quotConj htN (QuotientGroup.mk a) = QuotientGroup.mk a)
    (hj : (QuotientGroup.mk a : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ j) = 1) :
    ∃ c ∈ F ⊓ cen t, c ^ (2 ^ j) = 1 ∧ ∃ hcF : c ∈ F,
      (QuotientGroup.mk (⟨c, hcF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = QuotientGroup.mk a := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haj : (a : X) ^ (2 ^ j) ∈ pPrimeCoreOf 2 F := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
    exact ⟨_, hj, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 F)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf F)
  obtain ⟨m, hmj, ham⟩ := exists_zpow_twoElt_of_pow_mem hOcop haj
  set y : X := (a : X) ^ m with hy
  have hyF : y ∈ F := F.zpow_mem a.2 m
  have hya : (QuotientGroup.mk (⟨y, hyF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = QuotientGroup.mk a := by
    rw [QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := ham
    have : (⟨y, hyF⟩ : ↥F)⁻¹ * a = w⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      rw [show (w : X) = (a : X)⁻¹ * y from hwe]
      group
    rw [this]
    exact (pPrimeCore 2 ↥F).inv_mem hw
  have htO : t ∈ normalizer (pPrimeCoreOf 2 F : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  have hyt : ⁅y, t⁆ ∈ pPrimeCoreOf 2 F := by
    have h1 : quotConj htN (QuotientGroup.mk ((⟨y, hyF⟩ : ↥F)⁻¹)) =
        QuotientGroup.mk ((⟨y, hyF⟩ : ↥F)⁻¹) := by
      rw [QuotientGroup.mk_inv, map_inv, hya, hfix]
    rw [cn_quotConj_mk] at h1
    have h3 := QuotientGroup.eq.1 h1.symm
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut,
      Subgroup.coe_mk, commutatorElement_def, inv_inv]
    group
  obtain ⟨c, hc, hcj, hcy⟩ := exists_twoElt_centralizer_of_comm_mem ht2 htO hyF hyt hmj
  refine ⟨c, hc, hcj, hc.1, ?_⟩
  rw [← hya, QuotientGroup.eq]
  obtain ⟨w, hw, hwe⟩ := hcy
  have : (⟨c, hc.1⟩ : ↥F)⁻¹ * ⟨y, hyF⟩ = w := Subtype.ext (by simpa using hwe.symm)
  rw [this]
  exact hw

private theorem cn_fixed_M11
    {Q : Type} [Group Q]
    (e : Q ≃* Blueprint.NativeSporadic.McL) (α : MulAut Q) (hα2 : α * α = 1)
    (hout : ¬ ∃ g : Q, α = MulAut.conj g) :
    Nonempty (↥(CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α) ≃*
      ↥Blueprint.NativeSporadic.M11) := by
  set σ : MulAut Blueprint.NativeSporadic.McL := (e.symm.trans α).trans e with hσ
  have hσapp : ∀ y, σ (e y) = e (α y) := fun y => by
    rw [hσ]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hin : σ ∉ ComponentClassification.OuterAutomorphisms.inner Blueprint.NativeSporadic.McL := by
    rintro ⟨g, hg⟩
    apply hout
    refine ⟨e.symm g, ?_⟩
    ext y
    have h1 := congrArg (fun φ : MulAut Blueprint.NativeSporadic.McL => φ (e y)) hg
    simp only [MulAut.conj_apply] at h1
    rw [hσapp] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hσ2 : orderOf σ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : α (α y) = y := by
        rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
      rw [pow_two, MulAut.mul_apply, hσapp, hσapp, h1, MulAut.one_apply]
    · intro h
      apply hin
      rw [h]
      exact one_mem _
  obtain ⟨eM⟩ :=
    (CFSG.Sporadic.Recognition.McLAS.mcl_outer_involutions_of_certificate).2.2 σ hσ2 hin
  have hiff : ∀ y : Q, y ∈ CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α ↔
      e y ∈ CFSG.Sporadic.Recognition.McLAS.mclFixed σ := fun y =>
    (cn_mem_fixedSubgroup _ y).trans ((cn_fixed_iff e α σ hσapp y).trans
      (cn_mem_mclFixed σ (e y)).symm)
  refine ⟨MulEquiv.trans (MulEquiv.mk' (e.toEquiv.subtypeEquiv hiff) fun x y => ?_) eM⟩
  apply Subtype.ext
  simp only [Equiv.subtypeEquiv_apply, MulEquiv.coe_toEquiv, Subgroup.coe_mul]
  exact map_mul e _ _

private theorem cn_step1_comp {n : ℕ} {t v : X} (htv : t ∈ cen v)
    (htK : t ∈ QOf (Sec6K X n (cen v))) {J : Subgroup X} (hJ : IsPCompIn 2 (cen v) J)
    (hJK : J ≤ Sec6K X n (cen v)) : t ∈ QOf J := by
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJ.1).1 (isPComponent_two_iff.1 hJ.2).2
  have hOK : oddCoreOf (Sec6K X n (cen v)) ≤ oddCoreOf (cen v) :=
    cn_oddCoreOf_le_of_normal (cn_K_le n v) (Sec6K_cen_normal n v)
  obtain ⟨-, -, htc⟩ := htK
  have hJt : J.map (MulAut.conj t).toMonoidHom ≤ J := by
    refine le_of_le_sup_pPrimeCoreOf hJ ?_ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact (cen v).mul_mem ((cen v).mul_mem htv (hJ.1 hj)) ((cen v).inv_mem htv)
    · exact primeResidual_eq_top_of_equiv 2 (J.equivMapOfInjective _ (MulAut.conj t).injective)
        hJq.1
    · rintro _ ⟨j, hj, rfl⟩
      have h1 : ⁅j⁻¹, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htc _ (hJK (J.inv_mem hj))
      have h2 : (MulAut.conj t).toMonoidHom j = j * ⁅j⁻¹, t⁆ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [h2]
      exact Subgroup.mul_mem_sup hj (hOK h1)
  have htJ : t ∈ normalizer (J : Set X) := cn_mem_normalizer_of_map_le hJt
  refine mem_QOf_iff.2 ⟨htJ, fun j hj => ?_⟩
  have h1 : ⁅j, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htc j (hJK hj)
  have h2 : ⁅j, t⁆ ∈ J := by
    have h3 : ⁅j, t⁆ = j * (t * j⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact J.mul_mem hj ((mem_normalizer_iff.1 htJ j⁻¹).1 (J.inv_mem hj))
  exact cn_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf _ (hJK hx))
    (odd_card_oddCoreOf _) ⟨h2, h1⟩

private theorem cn_caseB_core
    {n : ℕ} {M J : Subgroup X}
    {v t : X} (hT : IsSec6MType n (↥M ⧸ pPrimeCore 2 ↥M)) (hvM : v ∈ M) (hv : orderOf v = 2)
    (htv : t ∈ cen v) (htN : t ∈ normalizer (M : Set X)) (hJ : IsAhatIntr X v J)
    (hJcov : J ≤ (M ⊓ cen v) ⊔ oddCoreOf (cen v)) (htJ : t ∈ QOf J) :
    ∀ x : ↥M ⧸ pPrimeCore 2 ↥M, x * QuotientGroup.mk ⟨v, hvM⟩ = QuotientGroup.mk ⟨v, hvM⟩ * x →
      quotConj htN x = x := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := oTwoPrimeOf (M ⊓ cen v) with hR
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := cn_degree hT hvM hv hJ hJcov
  obtain ⟨hJC, -, hJpc, -⟩ := hJ
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJC).1 (isPComponent_two_iff.1 hJpc).2
  have hRM : R ≤ M ⊓ cen v := oTwoPrimeOf_le _
  have hRM' : R ≤ M := hRM.trans inf_le_left
  set Z : Subgroup X := R ⊔ oddCoreOf (cen v) with hZ
  have hJZ : J ≤ Z := by
    have hJself : oTwoPrimeOf J = J := oTwoPrimeOf_eq_self_of_primeResidual hJq.1
    rw [← hJself, oTwoPrimeOf_le_iff]
    rintro x hx ⟨k, hk⟩
    obtain ⟨o, ho, a, ha, hak, rfl⟩ := exists_conj_twoElt_of_mem_sup_odd_X
      (A := M ⊓ cen v) (N := oddCoreOf (cen v))
      (fun y hy => le_normalizer_oddCoreOf (cen v) (Subgroup.mem_inf.1 hy).2)
      (odd_card_oddCoreOf (cen v)) (hJcov hx) hk
    have haR : a ∈ R := mem_oTwoPrimeOf ha k hak
    have hoZ : o ∈ Z := le_sup_right (a := R) ho
    exact Z.mul_mem (Z.mul_mem hoZ (le_sup_left (b := oddCoreOf (cen v)) haR)) (Z.inv_mem hoZ)
  have hZv : Z ≤ cen v := sup_le (hRM.trans inf_le_right) (oddCoreOf_le _)
  have hJZpc : IsPCompIn 2 Z J := by
    refine ⟨hJZ, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hJZ).2 hJq⟩⟩
    have h1 : J.subgroupOf Z = (J.subgroupOf (cen v)).comap (Subgroup.inclusion hZv) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
    rw [h1]
    exact (isPComponent_two_iff.1 hJpc).1.comap _
  have hRZ : R ≤ Z := le_sup_left
  have hOvZ : oddCoreOf (cen v) ≤ oddCoreOf Z :=
    le_oddCoreOf_of_normalized le_sup_right
      (fun z hz => le_normalizer_oddCoreOf (cen v) (hZv hz)) (odd_card_oddCoreOf _)
  have hRcovZ : R.subgroupOf Z ⊔ pPrimeCore 2 ↥Z = ⊤ := by
    rw [covers_subgroupOf_iff hRZ]
    exact le_antisymm (sup_le hRZ (Subgroup.map_subtype_le _))
      (sup_le le_sup_left (hOvZ.trans le_sup_right))
  have hZR : Nat.card (↥Z ⧸ pPrimeCore 2 ↥Z) ≤ Nat.card (↥R ⧸ pPrimeCore 2 ↥R) :=
    card_quot_pPrimeCore_le_of_covers hRZ le_rfl hRcovZ
  have hRv : ∀ r ∈ R, ⁅r, v⁆ ∈ pPrimeCoreOf 2 M := by
    intro r hr
    have hrv : r * v = v * r := Subgroup.mem_centralizer_singleton_iff.1 (hRM hr).2
    rw [commutatorElement_eq_one_iff_mul_comm.2 hrv]
    exact one_mem _
  have hRn : Nat.card (↥R ⧸ pPrimeCore 2 ↥R) ≤ n.factorial :=
    cn_card_quot_le_of_cen hT hvM hv hRM' hRv
  have hJcard : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = n.factorial :=
    cn_card_of_dc (cn_two_le hT) hJn
  have hJcovZ : J.subgroupOf Z ⊔ pPrimeCore 2 ↥Z = ⊤ :=
    covers_of_card_le hJZ (hZR.trans (hRn.trans hJcard.ge))
  have htR : t ∈ normalizer (R : Set X) :=
    cn_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf htN (Subgroup.le_normalizer htv))
  have htZ : t ∈ normalizer (Z : Set X) :=
    mem_normalizer_sup htR (le_normalizer_oddCoreOf (cen v) htv)
  have htOZ : t ∈ normalizer (oddCoreOf Z : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htZ
  have hOJZ : pPrimeCoreOf 2 J ≤ oddCoreOf Z :=
    pPrimeCoreOf_le_oddCoreOf hJZ (isPComponent_two_iff.1 hJZpc.2).1
  have htZc : ∀ z ∈ Z, ⁅z, t⁆ ∈ oddCoreOf Z := by
    intro z hz
    have hJZeq : J ⊔ pPrimeCoreOf 2 Z = Z := (covers_subgroupOf_iff hJZ).1 hJcovZ
    have hz' : z ∈ J ⊔ oddCoreOf Z := hJZeq.symm ▸ hz
    obtain ⟨j, hj, o, ho, rfl⟩ :=
      cn_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf Z (hJZ hx)) hz'
    rw [cn_comm_mul]
    have h1 : ⁅o, t⁆ ∈ oddCoreOf Z := by
      have h3 : ⁅o, t⁆ = o * (t * o⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact (oddCoreOf Z).mul_mem ho ((mem_normalizer_iff.1 htOZ o⁻¹).1 ((oddCoreOf Z).inv_mem ho))
    have h2 : ⁅j, t⁆ ∈ oddCoreOf Z := hOJZ ((mem_QOf_iff.1 htJ).2 j hj)
    exact (oddCoreOf Z).mul_mem
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf Z (hJZ hj)) _).1 h1) h2
  have htRc : ∀ r ∈ R, ⁅r, t⁆ ∈ pPrimeCoreOf 2 R := by
    intro r hr
    have h1 := htZc r (hRZ hr)
    have h2 : ⁅r, t⁆ ∈ R := by
      have h3 : ⁅r, t⁆ = r * (t * r⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact R.mul_mem hr ((mem_normalizer_iff.1 htR r⁻¹).1 (R.inv_mem hr))
    exact cn_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf Z (hRZ hx))
      (odd_card_oddCoreOf Z) ⟨h2, h1⟩
  set π : ↥M →* ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set fR : ↥R →* ↥M ⧸ pPrimeCore 2 ↥M := π.comp (Subgroup.inclusion hRM') with hfR
  set C : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) :=
    centralizer ({π ⟨v, hvM⟩} : Set (↥M ⧸ pPrimeCore 2 ↥M)) with hC
  have hfRC : fR.range ≤ C := by
    rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨w, hw, hwe⟩ := hRv r r.2
    have hw' : w = ⁅Subgroup.inclusion hRM' r, (⟨v, hvM⟩ : ↥M)⁆ := Subtype.ext hwe
    have h1 : π ⁅Subgroup.inclusion hRM' r, (⟨v, hvM⟩ : ↥M)⁆ = 1 := by
      rw [← hw']
      exact (QuotientGroup.eq_one_iff w).2 hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hJZc : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) ≤ Nat.card (↥Z ⧸ pPrimeCore 2 ↥Z) :=
    card_quot_pPrimeCore_le_of_covers le_rfl hJZ (by rw [Subgroup.subgroupOf_self, top_sup_eq])
  have hRr : Nat.card (↥R ⧸ pPrimeCore 2 ↥R) ≤ Nat.card fR.range := cn_card_quot_le_range hRM'
  have hCcard : Nat.card C = n.factorial :=
    cn_card_of_dc (cn_two_le hT) (cn_cent_dc hT (cn_orderOf_mk hvM hv))
  have hfReq : fR.range = C := Subgroup.eq_of_le_of_card_ge hfRC (by omega)
  have hker : fR.ker ≤ pPrimeCore 2 ↥R := by
    intro w hw
    have h1 : Subgroup.inclusion hRM' w ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hw
    have h2 : (w : X) ∈ R ⊓ pPrimeCoreOf 2 M := ⟨w.2, ⟨_, h1, rfl⟩⟩
    obtain ⟨w', hw', hww'⟩ := cn_inf_le_oddCoreOf
      (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hRM' hx)) (odd_card_oddCoreOf M) h2
    have : w' = w := Subtype.ext hww'
    rwa [← this]
  have hkerEq : pPrimeCore 2 ↥R ≤ fR.ker := by
    have h1 : fR.ker.index = (pPrimeCore 2 ↥R).index := by
      rw [Subgroup.index_ker, Subgroup.index_eq_card (pPrimeCore 2 ↥R), hfReq, hCcard]
      omega
    have e1 := Subgroup.card_mul_index fR.ker
    have e2 := Subgroup.card_mul_index (pPrimeCore 2 ↥R)
    rw [h1] at e1
    have h3 : Nat.card fR.ker = Nat.card (pPrimeCore 2 ↥R) :=
      Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (e1.trans e2.symm)
    exact (Subgroup.eq_of_le_of_card_ge hker h3.ge).ge
  intro x hx
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hx
  rw [← hfReq] at hxC
  obtain ⟨r, rfl⟩ := hxC
  obtain ⟨w', hw', hw'e⟩ := htRc r r.2
  have hw'ker : Subgroup.inclusion hRM' w' ∈ pPrimeCore 2 ↥M :=
    (QuotientGroup.eq_one_iff _).1 (hkerEq hw')
  show quotConj htN (QuotientGroup.mk (Subgroup.inclusion hRM' r)) =
    QuotientGroup.mk (Subgroup.inclusion hRM' r)
  rw [cn_quotConj_mk, QuotientGroup.eq]
  have h1 : (conjAut htN (Subgroup.inclusion hRM' r))⁻¹ * Subgroup.inclusion hRM' r =
      (Subgroup.inclusion hRM' r)⁻¹ * Subgroup.inclusion hRM' w' *
        (Subgroup.inclusion hRM' r)⁻¹⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, Subgroup.coe_inclusion, inv_inv]
    rw [show (w' : X) = ⁅(r : X), t⁆ from hw'e, commutatorElement_def]
    group
  rw [h1]
  exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem _ hw'ker _

private theorem cn_M11_ord4 :
    ∃ g ∈ Blueprint.NativeSporadic.M11, orderOf g = 4 := by
  refine ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (by simp), ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

private theorem cn_not_mem_of_odd {H : Subgroup X} {u : X} (hu : orderOf u = 2)
    (hH : Odd (Nat.card H)) : u ∉ H := by
  intro huH
  have h1 := Subgroup.orderOf_dvd_natCard H huH
  rw [hu] at h1
  exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 h1)

private theorem cn_land
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) {N : Subgroup X} (hN : N ≠ ⊤) (hCN : cen t ≤ N)
    {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    ∃ J : Subgroup X, Sec6KComp X n N J ∧ L ≤ J := by
  rcases hL with h5 | h6
  · exact Sec6L51B.exists_sec6KComp_of_sec5Comp hS.cex.toSolMinCEx hS.maxdeg.1 hN hCN h5
  · obtain ⟨J, hJ, hLJ⟩ :=
      Sec6L51B.exists_sec6MComp_of_sec6MComp hS.cex.toSolMinCEx hS.maxdeg hN hCN h6
    exact ⟨J, Or.inr hJ, hLJ⟩

private def cnComm (N L : Subgroup X) : Subgroup X where
  carrier := {y | y ∈ N ∧ ∀ l ∈ L, ⁅l, y⁆ ∈ oddCoreOf N}
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨N.mul_mem haN hbN, fun l hl => ?_⟩
    have h1 : ⁅l, a * b⁆ = ⁅l, a⁆ * (a * ⁅l, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (oddCoreOf N).mul_mem (ha l hl)
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf N haN) _).1 (hb l hl))
  one_mem' := ⟨N.one_mem, fun l _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨N.inv_mem haN, fun l hl => ?_⟩
    have h1 : ⁅l, a⁻¹⁆ = a⁻¹ * ⁅l, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (mem_normalizer_iff.1 (le_normalizer_oddCoreOf N (N.inv_mem haN)) _).1
      ((oddCoreOf N).inv_mem (ha l hl))

private theorem mem_cnComm {N L : Subgroup X} {y : X} :
    y ∈ cnComm N L ↔ y ∈ N ∧ ∀ l ∈ L, ⁅l, y⁆ ∈ oddCoreOf N := Iff.rfl

private theorem cn_le_cnComm {N F J L : Subgroup X} (hF : IsPCompIn 2 N F)
    (hJ : IsPCompIn 2 N J) (hne : J ≠ F) (hLJ : L ≤ J) : F ≤ cnComm N L := fun f hf =>
  mem_cnComm.2 ⟨hF.1 hf, fun l hl => pPrimeCoreOf_le_oddCoreOf hJ.1
    (isPComponent_two_iff.1 hJ.2).1 (cn_commutatorElement_mem hJ hF hne (hLJ hl) hf)⟩

private theorem cn_memQ {n : ℕ} {t c : X} {N : Subgroup X} (hCN : cen t ≤ N) (hct : c ∈ cen t)
    (hc : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → c ∈ cnComm N L) :
    c ∈ Sec6Q X n (cen t) := by
  set K : Subgroup X := Sec6K X n (cen t)
  have hcN : c ∈ normalizer (K : Set X) := Sec6K_cen_normal n t hct
  have hOK : K ⊓ oddCoreOf N ≤ oddCoreOf K :=
    cn_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf N (hCN (cn_K_le n t hx)))
      (odd_card_oddCoreOf N)
  let T : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ⁅k, c⁆ ∈ oddCoreOf K}
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, ?_⟩
        rw [cn_comm_mul]
        exact (oddCoreOf K).mul_mem
          ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf K haK) _).1 hb) ha
      one_mem' := ⟨K.one_mem, by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, ?_⟩
        have h1 : ⁅a⁻¹, c⁆ = a⁻¹ * ⁅a, c⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact (mem_normalizer_iff.1 (le_normalizer_oddCoreOf K (K.inv_mem haK)) _).1
          ((oddCoreOf K).inv_mem ha) }
  have hKT : K ≤ T := by
    refine sSup_le fun L hL l hl => ⟨le_sSup hL hl, hOK ⟨?_, (mem_cnComm.1 (hc L hL)).2 l hl⟩⟩
    have h3 : ⁅l, c⁆ = l * (c * l⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact K.mul_mem (le_sSup hL hl) ((mem_normalizer_iff.1 hcN l⁻¹).1 (K.inv_mem (le_sSup hL hl)))
  show c ∈ cen t ⊓ QOf (Sec6K X n (cen t))
  exact ⟨hct, mem_QOf_iff.2 ⟨hcN, fun k hk => (hKT hk).2⟩⟩

private theorem cn_S1 {n : ℕ} {t : X} (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x)
    {N : Subgroup X} (htN : t ∈ N) {v : X} (hv : v ∈ Sec6Q X n (cen t)) (hv2 : orderOf v = 2)
    {E F : Subgroup X} (hE : Sec6KComp X n (N ⊓ cen v) E) (hF : IsPCompIn 2 N F)
    (hEF : E ≤ F) : t ∈ normalizer (F : Set X) ∧ t ∈ QOf E := by
  have hvt : v ∈ cen t := hv.1
  have htv : t ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvt).symm
  have hEpc := cn_isPCompIn hE
  have hEq := cn_isTwoGenQuasi hE
  have hEK' : E ≤ Sec6K X n (cen v) :=
    (le_sSup hE : E ≤ Sec6K X n (N ⊓ cen v)).trans (h51.sub v hv2 _ inf_le_right).1
  obtain ⟨-, -, htKc⟩ := cn_step1 hvt (h61a v hv hv2)
  set D : Subgroup X := N ⊓ cen v
  have htD : t ∈ D := ⟨htN, htv⟩
  have hOD : oddCoreOf (Sec6K X n (cen v)) ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun d hd => mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n v hd.2))
        (Subgroup.le_normalizer hd))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hEt : E.map (MulAut.conj t).toMonoidHom ≤ E := by
    refine le_of_le_sup_pPrimeCoreOf hEpc ?_ ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact D.mul_mem (D.mul_mem htD (hEpc.1 he)) (D.inv_mem htD)
    · exact primeResidual_eq_top_of_equiv 2 (E.equivMapOfInjective _ (MulAut.conj t).injective)
        hEq.1
    · rintro _ ⟨e, he, rfl⟩
      have h1 : ⁅e⁻¹, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htKc _ (hEK' (E.inv_mem he))
      have h1D : ⁅e⁻¹, t⁆ ∈ D := by
        rw [commutatorElement_def, inv_inv]
        exact D.mul_mem (D.mul_mem (D.mul_mem (D.inv_mem (hEpc.1 he)) htD) (hEpc.1 he))
          (D.inv_mem htD)
      have h2 : (MulAut.conj t).toMonoidHom e = e * ⁅e⁻¹, t⁆ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [h2]
      exact Subgroup.mul_mem_sup he (hOD ⟨h1, h1D⟩)
  have htE : t ∈ normalizer (E : Set X) := cn_mem_normalizer_of_map_le hEt
  have hFt := cn_isPCompIn_conj hF (Subgroup.le_normalizer htN)
  have hEFt : E ≤ F.map (MulAut.conj t).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer htE]
    exact Subgroup.map_mono hEF
  refine ⟨mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hF hFt hEF hEFt hEq).symm,
    mem_QOf_iff.2 ⟨htE, fun e he => ?_⟩⟩
  have h1 : ⁅e, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htKc e (hEK' he)
  have h2 : ⁅e, t⁆ ∈ E := by
    have h3 : ⁅e, t⁆ = e * (t * e⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact E.mul_mem he ((mem_normalizer_iff.1 htE e⁻¹).1 (E.inv_mem he))
  exact cn_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf _ (hEK' hx))
    (odd_card_oddCoreOf _) ⟨h2, h1⟩

private theorem cn_cent_of_covers {F E : Subgroup X} {t : X} (htN : t ∈ normalizer (F : Set X))
    (hEF : E ≤ F) (hcov : E.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤)
    (htE : ∀ e ∈ E, ⁅e, t⁆ ∈ oddCoreOf E) : CentModOdd F t := by
  have hFE : E ⊔ pPrimeCoreOf 2 F = F := (covers_subgroupOf_iff hEF).1 hcov
  have hOEF : oddCoreOf E ≤ oddCoreOf F := cn_oddCoreOf_le_of_covers hEF hcov
  have htO : t ∈ normalizer (oddCoreOf F : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer htN
  intro f hf
  have hf' : f ∈ E ⊔ oddCoreOf F := by
    rw [show E ⊔ oddCoreOf F = F from hFE]
    exact hf
  obtain ⟨e, he, o, ho, rfl⟩ :=
    cn_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf F (hEF hx)) hf'
  rw [cn_comm_mul]
  have h1 : ⁅o, t⁆ ∈ oddCoreOf F := by
    have h3 : ⁅o, t⁆ = o * (t * o⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (oddCoreOf F).mul_mem ho ((mem_normalizer_iff.1 htO o⁻¹).1 ((oddCoreOf F).inv_mem ho))
  exact (oddCoreOf F).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf F (hEF he)) _).1 h1)
    (hOEF (htE e he))

private theorem cn_comm_of_le_cen {E : Subgroup X} {t : X} (hEt : E ≤ cen t) :
    ∀ e ∈ E, ⁅e, t⁆ ∈ oddCoreOf E := fun e he => by
  rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hEt he))]
  exact one_mem _

private theorem cn_witness_mem_QOf {H F : Subgroup X} {u : X} (hu : IsIntrinsicIn X H F u) :
    u ∈ QOf F := by
  obtain ⟨-, huF, -, hFeq, -⟩ := hu
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hFeq
  have hEF : oTwoPrimeOf (F ⊓ cen u) ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hcov : (oTwoPrimeOf (F ⊓ cen u)).subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ := by
    rw [covers_subgroupOf_iff hEF, sup_comm]
    exact hFeq.symm
  have huN : u ∈ normalizer (F : Set X) := Subgroup.le_normalizer huF
  exact mem_QOf_iff.2 ⟨huN, cn_cent_of_covers huN hEF hcov
    (cn_comm_of_le_cen ((oTwoPrimeOf_le _).trans inf_le_right))⟩

private theorem cn_card_eq_of_type {n : ℕ} {Q Q' : Type} [Group Q] [Group Q']
    (hQ : IsSec6MType n Q) (hQ' : IsSec6MType n Q') : Nat.card Q = Nat.card Q' := by
  rcases hQ with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩ <;> rcases hQ' with ⟨h, ⟨e'⟩⟩ | ⟨h, ⟨e'⟩⟩
  · exact Nat.card_congr (e.trans e'.symm).toEquiv
  · norm_num at h
  · norm_num at h
  · exact Nat.card_congr (e.trans e'.symm).toEquiv

private theorem cn_comm_comm {w t : X} (ht : t * t = 1) : ⁅⁅w, t⁆, t⁆ = ⁅w, t⁆ ^ 2 := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e : t * ⁅w, t⁆⁻¹ * t⁻¹ = ⁅w, t⁆ := by
    calc t * ⁅w, t⁆⁻¹ * t⁻¹ = t * t * w * t⁻¹ * w⁻¹ * t⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = w * t * w⁻¹ * t⁻¹ := by rw [ht, one_mul, ht']
      _ = ⁅w, t⁆ := (commutatorElement_def w t).symm
  calc ⁅⁅w, t⁆, t⁆ = ⁅w, t⁆ * (t * ⁅w, t⁆⁻¹ * t⁻¹) := by
        rw [commutatorElement_def ⁅w, t⁆ t]
        group
    _ = ⁅w, t⁆ ^ 2 := by rw [e, pow_two]

private theorem cn_sq_comm {w t : X} (hw : w * w = 1) :
    ⁅w, t⁆ ^ 2 = ⁅w, t * w⁻¹ * t⁻¹⁆ := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [pow_two]
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hw']
  group

private theorem cn_lift_inv {P : Subgroup X} {t a : X} (ht2 : t ^ 2 = 1)
    (htP : t ∈ normalizer (P : Set X)) (haP : a ∈ P) (ha2 : a ^ 2 ∈ oddCoreOf P)
    (hat : ⁅a, t⁆ ∈ oddCoreOf P) : ∃ c ∈ P ⊓ cen t, c ^ 2 = 1 ∧ a⁻¹ * c ∈ oddCoreOf P := by
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 P)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf P)
  have ha2' : a ^ (2 ^ 1) ∈ pPrimeCoreOf 2 P := by
    rw [pow_one]
    exact ha2
  obtain ⟨m, hm2, ham⟩ := exists_zpow_twoElt_of_pow_mem hOcop ha2'
  have hyP : a ^ m ∈ P := P.zpow_mem haP m
  have htO : t ∈ normalizer (pPrimeCoreOf 2 P : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htP
  have hyt : ⁅a ^ m, t⁆ ∈ pPrimeCoreOf 2 P := by
    have e : a ^ m = a * (a⁻¹ * a ^ m) := by group
    rw [e, cn_comm_mul]
    have h1 : ⁅a⁻¹ * a ^ m, t⁆ ∈ oddCoreOf P := by
      have h3 : ⁅a⁻¹ * a ^ m, t⁆ = (a⁻¹ * a ^ m) * (t * (a⁻¹ * a ^ m)⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact (oddCoreOf P).mul_mem ham ((mem_normalizer_iff.1 htO _).1 ((oddCoreOf P).inv_mem ham))
    exact (oddCoreOf P).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf P haP) _).1 h1)
      hat
  obtain ⟨c, hc, hc2, hcy⟩ := exists_twoElt_centralizer_of_comm_mem ht2 htO hyP hyt hm2
  refine ⟨c, hc, by rw [pow_one] at hc2; exact hc2, ?_⟩
  have e : a⁻¹ * c = (a⁻¹ * a ^ m) * (c⁻¹ * a ^ m)⁻¹ := by group
  rw [e]
  exact (oddCoreOf P).mul_mem ham ((oddCoreOf P).inv_mem hcy)

private theorem cn_norm
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) {F : Subgroup X} (hF : Sec6KComp X n N F) :
    t ∈ normalizer (F : Set X) := by
  by_contra htF
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htNN : t ∈ N := hCN (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hFpc := cn_isPCompIn hF
  set Ft : Subgroup X := F.map (MulAut.conj t).toMonoidHom
  have hFtpc : IsPCompIn 2 N Ft := cn_isPCompIn_conj hFpc (Subgroup.le_normalizer htNN)
  have hne : F ≠ Ft := fun h => htF (mem_normalizer_of_map_conj_eq h.symm)
  have hmemFt : ∀ x ∈ F, t * x * t⁻¹ ∈ Ft := fun x hx => ⟨x, hx, rfl⟩
  have hFtF : ∀ y ∈ Ft, t * y * t⁻¹ ∈ F := by
    rintro _ ⟨x, hx, rfl⟩
    have e : t * ((MulAut.conj t).toMonoidHom x) * t⁻¹ = x := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hti]
      calc t * (t * x * t) * t = t * t * x * (t * t) := by group
        _ = x := by rw [htt, one_mul, mul_one]
    rw [e]
    exact hx
  have hcen_conj : ∀ l ∈ cen t, t * l * t⁻¹ = l := fun l hl => by
    rw [← Subgroup.mem_centralizer_singleton_iff.1 hl, mul_inv_cancel_right]
  have hcomm : ∀ x ∈ F, ∀ y ∈ Ft, ⁅x, y⁆ ∈ oddCoreOf F := fun x hx y hy =>
    cn_commutatorElement_mem hFpc hFtpc hne hx hy
  have hnotF : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → ¬ L ≤ F := by
    intro L hL hLF
    have hLt : L ≤ cen t := (cn_isPCompIn hL).1
    have hLFt : L ≤ Ft := fun l hl => by
      have h1 := hmemFt l (hLF hl)
      rwa [hcen_conj l (hLt hl)] at h1
    refine not_commutator_le_of_odd (cn_isTwoGenQuasi hL) (odd_card_oddCoreOf F) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hLF ha) b (hLFt hb)
  have hnotFt : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → ¬ L ≤ Ft := by
    intro L hL hLFt
    have hLt : L ≤ cen t := (cn_isPCompIn hL).1
    refine hnotF L hL fun l hl => ?_
    have h1 := hFtF l (hLFt hl)
    rwa [hcen_conj l (hLt hl)] at h1
  set P : Subgroup X := F ⊔ Ft
  have hPcomm : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → P ≤ cnComm N L := by
    intro L hL
    obtain ⟨J, hJ, hLJ⟩ := cn_land hS hN hCN hL
    have hJpc := cn_isPCompIn hJ
    exact sup_le (cn_le_cnComm hFpc hJpc (fun h => hnotF L hL (h ▸ hLJ)) hLJ)
      (cn_le_cnComm hFtpc hJpc (fun h => hnotFt L hL (h ▸ hLJ)) hLJ)
  have hPQ : ∀ c ∈ P, c ∈ cen t → c ∈ Sec6Q X n (cen t) := fun c hc hct =>
    cn_memQ hCN hct fun L hL => hPcomm L hL hc
  have htP : t ∈ normalizer (P : Set X) := by
    apply cn_mem_normalizer_of_map_le
    rw [Subgroup.map_sup]
    refine sup_le le_sup_right ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_sup_left (hFtF y hy)
  have hPF : P ≤ normalizer (F : Set X) :=
    sup_le Subgroup.le_normalizer fun y hy =>
      cn_QOf_le_normalizer F (cn_le_QOf_of_ne hFpc hFtpc hne hy)
  have hOFP : oddCoreOf F ≤ oddCoreOf P :=
    le_oddCoreOf_of_normalized ((oddCoreOf_le F).trans le_sup_left)
      (fun p hp => mem_normalizer_oddCoreOf_of_mem_normalizer (hPF hp)) (odd_card_oddCoreOf F)
  have hFOP : F ⊓ oddCoreOf P ≤ oddCoreOf F :=
    cn_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf P (Subgroup.mem_sup_left hx))
      (odd_card_oddCoreOf P)
  have hOPQ : oddCoreOf P ≤ QOf F := by
    intro o ho
    have hoP : o ∈ P := oddCoreOf_le P ho
    refine mem_QOf_iff.2 ⟨hPF hoP, fun f hf => hFOP ⟨?_, ?_⟩⟩
    · have h3 : ⁅f, o⁆ = f * (o * f⁻¹ * o⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact F.mul_mem hf ((mem_normalizer_iff.1 (hPF hoP) f⁻¹).1 (F.inv_mem hf))
    · rw [commutatorElement_def]
      exact (oddCoreOf P).mul_mem ((mem_normalizer_iff.1
        (le_normalizer_oddCoreOf P (Subgroup.mem_sup_left hf)) o).1 ho) ((oddCoreOf P).inv_mem ho)
  have hFtQ : Ft ≤ QOf F := cn_le_QOf_of_ne hFpc hFtpc hne
  have hcomt : ∀ w ∈ F, w * w = 1 → ⁅w, t⁆ ∈ P ∧ ⁅w, t⁆ ^ 2 ∈ oddCoreOf P ∧
      ⁅⁅w, t⁆, t⁆ ∈ oddCoreOf P ∧ w⁻¹ * ⁅w, t⁆ ∈ QOf F := by
    intro w hwF hww
    have hyFt : t * w⁻¹ * t⁻¹ ∈ Ft := hmemFt _ (F.inv_mem hwF)
    have e : ⁅w, t⁆ = w * (t * w⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    have ha2 : ⁅w, t⁆ ^ 2 ∈ oddCoreOf P := by
      rw [cn_sq_comm hww]
      exact hOFP (hcomm w hwF _ hyFt)
    refine ⟨?_, ha2, by rw [cn_comm_comm htt]; exact ha2, ?_⟩
    · rw [e]
      exact P.mul_mem (Subgroup.mem_sup_left hwF) (Subgroup.mem_sup_right hyFt)
    · rw [e, inv_mul_cancel_left]
      exact hFtQ hyFt
  rcases hF with h5 | h6
  ·
    obtain ⟨⟨u, hu⟩, hFn⟩ := h5
    have huF : u ∈ F := hu.2.1
    have hu2 : orderOf u = 2 := hu.1
    have huu : u * u = 1 := by
      rw [← pow_two, ← hu2]
      exact pow_orderOf_eq_one u
    have huQ : u ∈ QOf F := cn_witness_mem_QOf hu
    have hcex : ∃ c ∈ P ⊓ cen t, c ^ 2 = 1 ∧ c ∈ QOf F ∧ c ≠ 1 := by
      by_cases hut : ⁅u, t⁆ ∈ oddCoreOf P
      · obtain ⟨c, hc, hc2, huc⟩ := cn_lift_inv ht2 htP (Subgroup.mem_sup_left huF)
          (by rw [pow_two, huu]; exact one_mem _) hut
        refine ⟨c, hc, hc2, ?_, ?_⟩
        · have e : c = u * (u⁻¹ * c) := by group
          rw [e]
          exact (QOf F).mul_mem huQ (hOPQ huc)
        · rintro rfl
          rw [mul_one] at huc
          have huO : u ∈ oddCoreOf P := inv_mem_iff.1 huc
          exact cn_not_mem_of_odd hu2 (odd_card_oddCoreOf F) (hFOP (Subgroup.mem_inf.2 ⟨huF, huO⟩))
      · obtain ⟨haP, ha2, hat, hwa⟩ := hcomt u huF huu
        obtain ⟨c, hc, hc2, hac⟩ := cn_lift_inv ht2 htP haP ha2 hat
        refine ⟨c, hc, hc2, ?_, ?_⟩
        · have e : c = u * (u⁻¹ * ⁅u, t⁆) * (⁅u, t⁆⁻¹ * c) := by group
          rw [e]
          exact (QOf F).mul_mem ((QOf F).mul_mem huQ hwa) (hOPQ hac)
        · rintro rfl
          rw [mul_one] at hac
          exact hut (inv_mem_iff.1 hac)
    obtain ⟨c, ⟨hcP, hct⟩, hc2, hcQ, hc1⟩ := hcex
    have hc2' : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hE := sec6KComp_restrict (Or.inl ⟨⟨u, hu⟩, hFn⟩ : Sec6KComp X n N F) hc2 hcQ
    exact htF (cn_S1 h51 h61a htNN (hPQ c hcP hct) hc2' hE hFpc
      ((oTwoPrimeOf_le _).trans inf_le_left)).1
  ·
    have hFq := cn_isTwoGenQuasi (Or.inr h6 : Sec6KComp X n N F)
    have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ := mcLLyCenterFree _ h6.1.2.1
    obtain ⟨w, hwF, hw⟩ := cn_exists_involution hFq
    have hww : w * w = 1 := by
      rw [← pow_two, ← hw]
      exact pow_orderOf_eq_one w
    have hwQ : w ∉ QOf F := fun h => cn_not_mem_of_odd hw (odd_card_oddCoreOf F)
      (cn_mem_of_central hZ hwF fun l hl => (mem_QOf_iff.1 h).2 l hl)
    obtain ⟨haP, ha2, hat, hwa⟩ := hcomt w hwF hww
    obtain ⟨c, ⟨hcP, hct⟩, hc2, hac⟩ := cn_lift_inv ht2 htP haP ha2 hat
    have hwc : w⁻¹ * c ∈ QOf F := by
      have e : w⁻¹ * c = (w⁻¹ * ⁅w, t⁆) * (⁅w, t⁆⁻¹ * c) := by group
      rw [e]
      exact (QOf F).mul_mem hwa (hOPQ hac)
    have hcL : c ∈ F ⊔ QOf F := by
      have e : c = w * (w⁻¹ * c) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hwF hwc
    have hcnQ : c ∉ QOf F := fun h => hwQ (by
      have e : w = c * (w⁻¹ * c)⁻¹ := by group
      rw [e]
      exact (QOf F).mul_mem h ((QOf F).inv_mem hwc))
    have hc1 : c ≠ 1 := fun h => hcnQ (h ▸ (QOf F).one_mem)
    have hc2' : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have hE : Sec5Comp X n (N ⊓ cen c) (oTwoPrimeOf (F ⊓ cen c)) :=
      cn_piece_M_inner hc2' h6 hcL hcnQ
    exact htF (cn_S1 h51 h61a htNN (hPQ c hcP hct) hc2' (Or.inl hE) hFpc
      ((oTwoPrimeOf_le _).trans inf_le_left)).1

private theorem cn_caseA
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) {F : Subgroup X} (hF : Sec5Comp X n N F)
    (htN : t ∈ normalizer (F : Set X)) : CentModOdd F t := by
  by_contra hcent
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have htNN : t ∈ N := hCN (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hFK : Sec6KComp X n N F := Or.inl hF
  have hFpc := cn_isPCompIn hFK
  have hn2 : 2 ≤ n := by have := hS.maxdeg.1; omega
  have hnoL : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → F ≤ cnComm N L := by
    intro L hL
    obtain ⟨J, hJ, hLJ⟩ := cn_land hS hN hCN hL
    refine cn_le_cnComm hFpc (cn_isPCompIn hJ) ?_ hLJ
    rintro rfl
    rcases hL with hL5 | hL6
    · apply hcent
      have hcov : L.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := covers_of_card_le hLJ (by
        rw [cn_card_of_dc hn2 hF.2, cn_card_of_dc hn2 hL5.2])
      exact cn_cent_of_covers htN hLJ hcov (cn_comm_of_le_cen (cn_isPCompIn (Or.inl hL5)).1)
    · have h1 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ≤ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) :=
        modOddCard_le_of_le hLJ
      have h2 := cn_card_lt hL6.2 hF.2
      omega
  obtain ⟨f, ⟨hfF, hft⟩, hf4, hfO, hfz⟩ := cn_sqrt_center hS.maxdeg.1 ht2 htN hF.2 hcent
  have hfQ : f ∈ Sec6Q X n (cen t) := cn_memQ hCN hft fun L hL => hnoL L hL hfF
  have hvQ : f ^ 2 ∈ Sec6Q X n (cen t) := (Sec6Q X n (cen t)).pow_mem hfQ 2
  have hv2' : (f ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hf4
  have hv2 : orderOf (f ^ 2) = 2 := orderOf_eq_prime hv2' fun h1 => hfO (h1 ▸ one_mem _)
  have hvF : f ^ 2 ∈ QOf F :=
    mem_QOf_iff.2 ⟨Subgroup.le_normalizer (F.pow_mem hfF 2), fun a ha => hfz a ha⟩
  have hE := sec6KComp_restrict hFK hv2' hvF
  obtain ⟨-, hcovE⟩ := isPCompIn_restrict hFpc hv2' hvF
  have hEF : oTwoPrimeOf (F ⊓ cen (f ^ 2)) ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨-, htE⟩ := cn_S1 h51 h61a htNN hvQ hv2 hE hFpc hEF
  exact hcent (cn_cent_of_covers htN hEF hcovE (mem_QOf_iff.1 htE).2)

private theorem cn_caseB
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) {F : Subgroup X} (hF : Sec6MComp X n N F)
    (htN : t ∈ normalizer (F : Set X)) : ∃ f ∈ F, CentModOdd F (f * t) := by
  by_contra hinner
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hFK : Sec6KComp X n N F := Or.inr hF
  have hFpc := cn_isPCompIn hFK
  rcases hF.2 with ⟨hn8, he⟩ | ⟨-, he⟩
  swap
  · exact hinner (cn_inner_ly htN he)
  have hnoL : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → F ≤ cnComm N L := by
    intro L hL
    obtain ⟨J, hJ, hLJ⟩ := cn_land hS hN hCN hL
    refine cn_le_cnComm hFpc (cn_isPCompIn hJ) ?_ hLJ
    rintro rfl
    apply hinner
    refine cn_inner_mcl ht2 htN he hLJ (cn_isPCompIn hL).1 ?_
    have h1 := cn_card_ge (by omega : 2 ≤ n) hL
    rw [hn8] at h1
    have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
    omega
  obtain ⟨e⟩ := he
  set α : MulAut (↥F ⧸ pPrimeCore 2 ↥F) := quotConj htN
  have hα2 : α * α = 1 := MulEquiv.ext fun y => cn_quotConj_sq ht2 htN y
  have hout : ¬ ∃ g, α = MulAut.conj g := fun ⟨g, hg⟩ => hinner (cn_inner_of_conj htN hg)
  obtain ⟨Φ⟩ := cn_fixed_M11 e α hα2 hout
  obtain ⟨g0, hg0, hg0ord⟩ := cn_M11_ord4
  set xs : ↥(CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α) := Φ.symm ⟨g0, hg0⟩ with hxs
  have hxfix : α (xs : ↥F ⧸ pPrimeCore 2 ↥F) = xs := (cn_mem_fixedSubgroup α _).1 xs.2
  have hxord : orderOf (xs : ↥F ⧸ pPrimeCore 2 ↥F) = 4 := by
    rw [Subgroup.orderOf_coe, hxs, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hg0ord]
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (xs : ↥F ⧸ pPrimeCore 2 ↥F)
  have hfixa : quotConj htN (QuotientGroup.mk a) = QuotientGroup.mk a := by
    rw [ha]
    exact hxfix
  have h4 : (QuotientGroup.mk a : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ 2) = 1 := by
    rw [ha, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hxord]
    exact pow_orderOf_eq_one _
  obtain ⟨f, ⟨hfF, hft⟩, hf4, hfF', hfa⟩ := cn_lift_fixed ht2 htN a hfixa h4
  have hvQ : f ^ 2 ∈ Sec6Q X n (cen t) :=
    (Sec6Q X n (cen t)).pow_mem (cn_memQ hCN hft fun L hL => hnoL L hL hfF) 2
  have hv1 : f ^ 2 ≠ 1 := by
    intro h1
    have h2 : (xs : ↥F ⧸ pPrimeCore 2 ↥F) ^ 2 = 1 := by
      rw [← ha, ← hfa, ← QuotientGroup.mk_pow]
      have : (⟨f, hfF'⟩ : ↥F) ^ 2 = 1 := Subtype.ext (by simpa using h1)
      rw [this, QuotientGroup.mk_one]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hxord] at h3
    norm_num at h3
  have hv2 : orderOf (f ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hf4) hv1
  have hvF : f ^ 2 ∈ F := F.pow_mem hfF 2
  have htv : t ∈ cen (f ^ 2) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvQ.1).symm
  have htK := cn_step1 hvQ.1 (h61a _ hvQ hv2)
  obtain ⟨J, hJ, hJcov⟩ := hF.1.2.2 (f ^ 2) hvF hv2
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := cn_degree hF.2 hvF hv2 hJ hJcov
  have hJK : J ≤ Sec6K X n (cen (f ^ 2)) :=
    le_sSup (Or.inl ⟨⟨f ^ 2, hJ.isIntrinsicIn hv2⟩, hJn⟩)
  have htJ : t ∈ QOf J := cn_step1_comp htv htK ⟨hJ.1, hJ.2.2.1⟩ hJK
  have hcore := cn_caseB_core hF.2 hvF hv2 htv htN hJ hJcov htJ
  have hle : centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥F) ⟨f ^ 2, hvF⟩} :
      Set (↥F ⧸ pPrimeCore 2 ↥F)) ≤
      CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α := fun x hx =>
    (cn_mem_fixedSubgroup α x).2 (hcore x (Subgroup.mem_centralizer_singleton_iff.1 hx))
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_congr Φ.toEquiv, CFSG.Sporadic.Mathieu.card_M11,
    cn_card_of_dc (cn_two_le hF.2) (cn_cent_dc hF.2 (cn_orderOf_mk hvF hv2)), hn8] at h1
  norm_num [Nat.factorial] at h1

private theorem cn_piece
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) {F : Subgroup X} (hF : Sec6KComp X n N F) :
    ∃ L : Subgroup X, Sec6KComp X n (cen t) L ∧ L ≤ F := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have htN := cn_norm hS h51 h61a hN hCN hF
  have htO : t ∈ normalizer (pPrimeCoreOf 2 F : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  by_cases hcent : CentModOdd F t
  · have hE := sec6KComp_restrict hF ht2 ⟨htN, htO, hcent⟩
    rw [inf_of_le_right hCN] at hE
    exact ⟨_, hE, (oTwoPrimeOf_le _).trans inf_le_left⟩
  · rcases hF with h5 | h6
    · exact absurd (cn_caseA hS h51 h61a hN hCN h5 htN) hcent
    · obtain ⟨f, hfF, hft⟩ := cn_caseB hS h51 h61a hN hCN h6 htN
      have hftQ : f * t ∈ QOf F :=
        mem_QOf_iff.2 ⟨mul_mem (Subgroup.le_normalizer hfF) htN, hft⟩
      have htL : t ∈ F ⊔ QOf F := by
        have e : t = f⁻¹ * (f * t) := by group
        rw [e]
        exact Subgroup.mul_mem_sup (F.inv_mem hfF) hftQ
      have htnQ : t ∉ QOf F := fun h => hcent (mem_QOf_iff.1 h).2
      have hE := cn_piece_M_inner hS.choice.inv h6 htL htnQ
      rw [inf_of_le_right hCN] at hE
      exact ⟨_, Or.inl hE, (oTwoPrimeOf_le _).trans inf_le_left⟩

private theorem cn_dich
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) {L F : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    (hF : Sec6KComp X n N F) (hLF : L ≤ F) :
    F = oddCoreOf F ⊔ L ∨
      (Sec6MComp X n N F ∧ Sec5Comp X n (cen t) L ∧ ¬ CentModOdd F t ∧
        ∃ f ∈ F, CentModOdd F (f * t)) := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have htN := cn_norm hS h51 h61a hN hCN hF
  have htO : t ∈ normalizer (pPrimeCoreOf 2 F : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  have hLpc := cn_isPCompIn hL
  have hLq := cn_isTwoGenQuasi hL
  by_cases hcent : CentModOdd F t
  · left
    have hE := sec6KComp_restrict hF ht2 ⟨htN, htO, hcent⟩
    rw [inf_of_le_right hCN] at hE
    obtain ⟨-, hcovE⟩ := isPCompIn_restrict (cn_isPCompIn hF) ht2 ⟨htN, htO, hcent⟩
    set E : Subgroup X := oTwoPrimeOf (F ⊓ cen t)
    have hEF : E ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
    have hFE : E ⊔ pPrimeCoreOf 2 F = F := (covers_subgroupOf_iff hEF).1 hcovE
    by_cases hLE : L = E
    · rw [hLE, sup_comm]
      exact hFE.symm
    · exfalso
      have hEpc := cn_isPCompIn hE
      have hodd : Odd (Nat.card (oddCoreOf L ⊔ oddCoreOf F : Subgroup X)) :=
        cn_odd_card_sup (fun x hx => le_normalizer_oddCoreOf F (hLF (oddCoreOf_le L hx)))
          (odd_card_oddCoreOf L) (odd_card_oddCoreOf F)
      refine not_commutator_le_of_odd hLq hodd ?_
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hb' : b ∈ E ⊔ oddCoreOf F := by
        rw [show E ⊔ oddCoreOf F = F from hFE]
        exact hLF hb
      obtain ⟨e, he, o, ho, rfl⟩ :=
        cn_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf F (hEF hx)) hb'
      have h1 : ⁅a, e⁆ ∈ oddCoreOf L := cn_commutatorElement_mem hLpc hEpc hLE ha he
      have h2 : ⁅a, o⁆ ∈ oddCoreOf F := by
        rw [commutatorElement_def]
        exact (oddCoreOf F).mul_mem ((mem_normalizer_iff.1
          (le_normalizer_oddCoreOf F (hLF ha)) o).1 ho) ((oddCoreOf F).inv_mem ho)
      have h3 : e * ⁅a, o⁆ * e⁻¹ ∈ oddCoreOf F :=
        (mem_normalizer_iff.1 (le_normalizer_oddCoreOf F (hEF he)) _).1 h2
      have e4 : ⁅a, e * o⁆ = ⁅a, e⁆ * (e * ⁅a, o⁆ * e⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e4]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h3)
  · right
    rcases hF with h5 | h6
    · exact absurd (cn_caseA hS h51 h61a hN hCN h5 htN) hcent
    · refine ⟨h6, ?_, hcent, cn_caseB hS h51 h61a hN hCN h6 htN⟩
      rcases hL with hL5 | hL6
      · exact hL5
      · exfalso
        apply hcent
        have hcov : L.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ :=
          covers_of_card_le hLF (cn_card_eq_of_type h6.2 hL6.2).le
        exact cn_cent_of_covers htN hLF hcov (cn_comm_of_le_cen hLpc.1)

end CtrlN

theorem sec6CtrlNAt
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {N : Subgroup X}
    (hN : N ≠ ⊤) (hCN : cen t ≤ N) : Sec6CtrlNAt X n t N where
  norm _ hF := cn_norm hS h51 h61a hN hCN hF
  piece _ hF := cn_piece hS h51 h61a hN hCN hF
  dich _ _ hL hF hLF := cn_dich hS h51 h61a hN hCN hL hF hLF

theorem sec6CtrlNHolds
    :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), Sec6Setting X n t → Sec6Lemma51 X n →
      (∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) → Sec6CtrlAt X n t →
        ∀ N : Subgroup X, N ≠ ⊤ → cen t ≤ N → Sec6CtrlNAt X n t N :=
  fun _ _ _ _ _ hS h51 h61a _ _ hN hCN => sec6CtrlNAt hS h51 h61a hN hCN

end CFSG.OddStandard.Solomon75
