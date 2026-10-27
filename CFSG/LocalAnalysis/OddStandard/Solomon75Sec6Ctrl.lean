module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyAllInnerThm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Toolkit

variable {X : Type} [Group X] [Finite X]

private theorem ctl_conj_mem {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M) {x : X}
    (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem ctl_mem_normalizer {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨ctl_conj_mem h, fun hx => ?_⟩
  have := ctl_conj_mem h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private theorem ctl_commutatorElement_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
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

private theorem ctl_mem_of_le_sSup {H M E : Subgroup X} {S : Set (Subgroup X)}
    (hM : IsPCompIn 2 H M) (hS : ∀ J ∈ S, IsPCompIn 2 H J) (hEM : E ≤ M) (hES : E ≤ sSup S)
    (hEq : IsTwoGenQuasi ↥E) : M ∈ S := by
  by_contra hMS
  have hOM : pPrimeCoreOf 2 M ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hM.1 (isPComponent_two_iff.1 hM.2).1
  have hOMM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hle : sSup S ≤ centralizerSection M (oddCoreOf H) := by
    refine sSup_le fun J hJ => ?_
    intro j hj
    have hne : M ≠ J := fun h => hMS (by rw [h]; exact hJ)
    have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ pPrimeCoreOf 2 M := fun g hg m hm =>
      ctl_commutatorElement_mem hM (hS J hJ) hne hm hg
    exact ⟨ctl_mem_normalizer (fun m hm => hOMM (hc j hj m hm))
        (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm)),
      le_normalizer_oddCoreOf H ((hS J hJ).1 hj), fun m hm => hOM (hc j hj m hm)⟩
  refine not_commutator_le_of_odd hEq (odd_card_oddCoreOf H) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨-, -, hab⟩ := hle (hES hb)
  exact hab a (hEM ha)

private theorem ctl_sSup_le_normalizer {H M : Subgroup X} {S : Set (Subgroup X)}
    (hM : IsPCompIn 2 H M) (hS : ∀ J ∈ S, IsPCompIn 2 H J) :
    sSup S ≤ normalizer (M : Set X) := by
  refine sSup_le fun J hJ => ?_
  by_cases hne : M = J
  · rw [← hne]
    exact Subgroup.le_normalizer
  intro j hj
  have hOMM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ pPrimeCoreOf 2 M := fun g hg m hm =>
    ctl_commutatorElement_mem hM (hS J hJ) hne hm hg
  exact ctl_mem_normalizer (fun m hm => hOMM (hc j hj m hm))
    (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm))

private theorem ctl_isPCompIn {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsPCompIn 2 H J := by
  rcases h with ⟨⟨u, -, -, hpc, -⟩, -⟩ | ⟨⟨hpc, -⟩, -⟩
  · exact hpc
  · exact hpc

private theorem ctl_isTwoGenQuasi {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsTwoGenQuasi ↥J :=
  (isTwoGenQuasi_subgroupOf_iff (ctl_isPCompIn h).1).1
    (isPComponent_two_iff.1 (ctl_isPCompIn h).2).2

private theorem ctl_K_le_normalizer {n : ℕ} {H J : Subgroup X} (hJ : Sec6KComp X n H J) :
    Sec6K X n H ≤ normalizer (J : Set X) :=
  ctl_sSup_le_normalizer (S := {L | Sec6KComp X n H L}) (ctl_isPCompIn hJ)
    (fun _ hL => ctl_isPCompIn hL)

private theorem ctl_exists_involution {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
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

private theorem ctl_le_of_normalizes {L A : Subgroup X} (hq : IsTwoGenQuasi ↥L)
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

private theorem ctl_eq_top_of_isPComponent {G : Type} [Group G] [Finite G] (hG : IsQuasisimple G)
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

private theorem ctl_isSubnormal_inf {K D D' H : Subgroup X} (hHD : H ≤ D) (hHD' : H ≤ D')
    (hK : (K.subgroupOf D).IsSubnormal) : ((K ⊓ D').subgroupOf H).IsSubnormal := by
  have h1 : (K ⊓ D').subgroupOf H = (K.subgroupOf D).comap (Subgroup.inclusion hHD) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hHD' x.2⟩⟩
  rw [h1]
  exact hK.comap _

private theorem ctl_isPCompIn_oTwoPrimeOf {H A : Subgroup X} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).IsSubnormal) (hq : IsTwoGenQuasi ↥(oTwoPrimeOf A)) :
    IsPCompIn 2 H (oTwoPrimeOf A) := by
  have hEH : oTwoPrimeOf A ≤ H := (oTwoPrimeOf_le A).trans hAH
  refine ⟨hEH, isPComponent_two_iff.2 ⟨?_, (isTwoGenQuasi_subgroupOf_iff hEH).2 hq⟩⟩
  exact isSubnormal_subgroupOf_of_normal_of_subnormal hAH (oTwoPrimeOf_le A) hA
    (normal_subgroupOf_oTwoPrimeOf A)

private theorem ctl_isPCompIn_piece {r c : X} {L : Subgroup X} (hL : IsPCompIn 2 (cen r) L)
    (hq : IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ cen c))) :
    IsPCompIn 2 (cen c ⊓ cen r) (oTwoPrimeOf (L ⊓ cen c)) :=
  ctl_isPCompIn_oTwoPrimeOf (le_inf inf_le_right (inf_le_left.trans hL.1))
    (ctl_isSubnormal_inf inf_le_right inf_le_left (isPComponent_two_iff.1 hL.2).1) hq

private theorem ctl_exists_mul_of_mem_sup {H N : Subgroup X}
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

private theorem ctl_inf_le_oddCoreOf {L N : Subgroup X} (hLN : L ≤ normalizer (N : Set X))
    (hN : Odd (Nat.card N)) : L ⊓ N ≤ oddCoreOf L :=
  le_oddCoreOf_of_normalized inf_le_left
    (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg) (hLN hg))
    (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))

private theorem ctl_exists_mem {n : ℕ} (hc : SolCEx X)
    (hb : ∀ H : Subgroup X, H ≠ ⊤ → ∀ t ∈ H, orderOf t = 2 →
      Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H)
    {s u : X} (hs : orderOf s = 2) (hu : orderOf u = 2) (hus : s * u = u * s) {Lu E : Subgroup X}
    (hLu : IsAhatIntr X u Lu) (hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n)
    (hEL : E ≤ Lu) (hEs : E ≤ cen s) (hEgen : primeResidual 2 ↥E = ⊤) (huE : u ∈ E)
    (hcov : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤) :
    ∃ J : Subgroup X, Sec6KComp X n (cen s) J ∧ E ≤ J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne s u with rfl | -
  · exact ⟨Lu, Or.inl ⟨⟨s, hLu.isIntrinsicIn hu⟩, hLun⟩, hEL⟩
  have hLuCu : IsPCompIn 2 (centralizer ({u} : Set X)) Lu := ⟨hLu.1, hLu.2.2.1⟩
  obtain ⟨hE'pc, M, hMpc, hE'M⟩ := exists_isPCompIn_above hu hus hLuCu hEL hEs hEgen huE hcov
  set E' : Subgroup X := oTwoPrimeOf (Lu ⊓ centralizer ({s} : Set X))
  have hEself : oTwoPrimeOf E = E := oTwoPrimeOf_eq_self_of_primeResidual hEgen
  have hEE' : E ≤ E' := by
    have := oTwoPrimeOf_mono (le_inf hEL hEs : E ≤ Lu ⊓ centralizer ({s} : Set X))
    rwa [hEself] at this
  have hE'Lu : E' ≤ Lu := (oTwoPrimeOf_le _).trans inf_le_left
  have hE'Cu : E' ≤ centralizer ({u} : Set X) := hE'Lu.trans hLu.1
  have hcov' : E'.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [eq_top_iff, ← hcov]
    exact sup_le_sup_right (Subgroup.subgroupOf_mono Lu hEE') _
  have hE'gen : primeResidual 2 ↥E' = ⊤ := primeResidual_oTwoPrimeOf _
  have hE'self : oTwoPrimeOf E' = E' := oTwoPrimeOf_eq_self_of_primeResidual hE'gen
  have hE'pc' : IsPCompIn 2 (cen s ⊓ cen u) E' := by
    rw [inf_comm]
    exact hE'pc
  have hE'int : IsIntrinsicIn X (cen s ⊓ cen u) E' u := by
    refine ⟨hu, hEE' huE, hE'pc', ?_, Lu, hLu, ?_⟩
    · rw [inf_of_le_left hE'Cu, oPrimeResidualOf_two_eq_oTwoPrimeOf, hE'self]
      exact (sup_eq_right.2 (Subgroup.map_subtype_le _)).symm
    · rw [inf_of_le_left hE'Cu, oPrimeResidualOf_two_eq_oTwoPrimeOf, hE'self]
      refine le_antisymm ?_ (sup_le (Subgroup.map_subtype_le _) hE'Lu)
      have h1 := (covers_subgroupOf_iff hEL).1 hcov
      calc Lu = E ⊔ pPrimeCoreOf 2 Lu := h1.symm
        _ ≤ pPrimeCoreOf 2 Lu ⊔ E' := sup_le (hEE'.trans le_sup_right) le_sup_left
  have hE'n : IsDoubleCoverOfAlt (↥E' ⧸ pPrimeCore 2 ↥E') n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hE'Lu hcov' n).2 hLun
  have hCs : cen s ≠ ⊤ := by
    haveI := hc.simple
    exact centralizer_ne_top_of_involution hc.nonabelian hs
  have huCs : u ∈ cen s := Subgroup.mem_centralizer_singleton_iff.2 hus.symm
  have hE'K : E' ≤ Sec6K X n (cen s) := by
    have h1 : E' ≤ Sec6K X n (cen s ⊓ cen u) := le_sSup (Or.inl ⟨⟨u, hE'int⟩, hE'n⟩)
    exact h1.trans (hb (cen s) hCs u huCs hu).1
  have hE'q : IsTwoGenQuasi ↥E' :=
    (isTwoGenQuasi_subgroupOf_iff hE'pc.1).1 (isPComponent_two_iff.1 hE'pc.2).2
  have hMK : Sec6KComp X n (cen s) M :=
    ctl_mem_of_le_sSup (S := {J | Sec6KComp X n (cen s) J}) hMpc
      (fun J hJ => ctl_isPCompIn hJ) hE'M hE'K hE'q
  exact ⟨M, hMK, hEE'.trans hE'M⟩

private theorem ctl_degree
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
    ctl_eq_top_of_isPComponent hC.1 hK
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

private theorem ctl_covers {L J D : Subgroup X} {v : X} (hLD : L ≤ D)
    (hJC : J ≤ cen v) (hJpc : IsPComponent 2 (J.subgroupOf (cen v)))
    (hJcov : J ≤ (L ⊓ cen v) ⊔ oddCoreOf (cen v)) :
    (oTwoPrimeOf (J ⊓ D)).subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEJ : oTwoPrimeOf (J ⊓ D) ≤ J := (oTwoPrimeOf_le _).trans inf_le_left
  rw [covers_subgroupOf_iff hEJ]
  refine le_antisymm (sup_le hEJ (Subgroup.map_subtype_le _)) ?_
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJC).1 (isPComponent_two_iff.1 hJpc).2
  have hJself : oTwoPrimeOf J = J := oTwoPrimeOf_eq_self_of_primeResidual hJq.1
  have hsub : J.subgroupOf (cen v) ≤
      (L ⊓ cen v).subgroupOf (cen v) ⊔ pPrimeCore 2 ↥(cen v) := by
    have h1 := Subgroup.subgroupOf_mono (cen v) hJcov
    rwa [Subgroup.subgroupOf_sup inf_le_right (oddCoreOf_le _), oddCoreOf_subgroupOf] at h1
  have hnorm := pPrimeCore_le_normalizer_of_isPComponent hJpc
  have hJO : J ⊓ oddCoreOf (cen v) ≤ oddCoreOf J :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
        (le_normalizer_oddCoreOf _ (hJC hg)))
      ((odd_card_oddCoreOf (cen v)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  refine (le_of_eq hJself.symm).trans (oTwoPrimeOf_le_iff.2 fun x hx hx2 => ?_)
  obtain ⟨j, hj⟩ := hx2
  have hxC : x ∈ cen v := hJC hx
  set x' : ↥(cen v) := ⟨x, hxC⟩
  have hx' : x' ∈ (L ⊓ cen v).subgroupOf (cen v) ⊔ pPrimeCore 2 ↥(cen v) := hsub hx
  have hx'j : x' ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
  obtain ⟨o, ho, a, ha, haj, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hx' hx'j
  have haL : (a : X) ∈ L := (Subgroup.mem_subgroupOf.1 ha).1
  have haJ : (a : X) ∈ J := by
    have hoN := hnorm (inv_mem ho)
    have h1 : o⁻¹ * x' * o⁻¹⁻¹ ∈ J.subgroupOf (cen v) :=
      (Subgroup.mem_normalizer_iff.1 hoN x').1 hx
    have h2 : o⁻¹ * x' * o⁻¹⁻¹ = a := by
      rw [hxa]
      group
    rw [h2] at h1
    exact h1
  have haE : (a : X) ∈ oTwoPrimeOf (J ⊓ D) :=
    mem_oTwoPrimeOf ⟨haJ, hLD haL⟩ j (by simpa using congrArg Subtype.val haj)
  have hxaO : x * (a : X)⁻¹ ∈ pPrimeCoreOf 2 J := by
    refine hJO ⟨J.mul_mem hx (J.inv_mem haJ), ?_⟩
    have h1 : x' * a⁻¹ ∈ pPrimeCore 2 ↥(cen v) := by
      rw [hxa]
      have h2 : o * a * o⁻¹ * a⁻¹ = o * (a * o⁻¹ * a⁻¹) := by group
      rw [h2]
      exact mul_mem ho
        ((inferInstance : (pPrimeCore 2 ↥(cen v)).Normal).conj_mem _ (inv_mem ho) a)
    exact ⟨x' * a⁻¹, h1, rfl⟩
  have hx_eq : x = (x * (a : X)⁻¹) * a := by group
  rw [hx_eq, sup_comm]
  exact Subgroup.mul_mem_sup hxaO haE

private theorem ctl_card_lt
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

private theorem ctl_broad
    {n : ℕ} (hc : SolCEx X)
    (hb : ∀ H : Subgroup X, H ≠ ⊤ → ∀ t ∈ H, orderOf t = 2 →
      Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H)
    {s : X} (hs : orderOf s = 2) {H L : Subgroup X} (hHs : H ≤ cen s) (hL : Sec6MComp X n H L) :
    ∃ J₀ : Subgroup X, Sec6MComp X n (cen s) J₀ ∧ L ≤ J₀ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨⟨hLH, hLpc⟩, htype, hLJ⟩, hT⟩ := hL
  have hLD : L ≤ cen s := hLH.trans hHs
  have hq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLH).1 (isPComponent_two_iff.1 hLpc).2
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := mcLLyCenterFree _ htype
  obtain ⟨v, hvL, hv⟩ := ctl_exists_involution hq
  obtain ⟨J, hJ, hJcov⟩ := hLJ v hvL hv
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := ctl_degree hT hvL hv hJ hJcov
  set E : Subgroup X := oTwoPrimeOf (J ⊓ cen s)
  have hEJ : E ≤ J := (oTwoPrimeOf_le _).trans inf_le_left
  have hEs : E ≤ cen s := (oTwoPrimeOf_le _).trans inf_le_right
  have hEgen : primeResidual 2 ↥E = ⊤ := primeResidual_oTwoPrimeOf _
  have hv2 : v ^ 2 = 1 := by
    rw [← hv]
    exact pow_orderOf_eq_one v
  have hvE : v ∈ E := mem_oTwoPrimeOf ⟨hJ.2.1, hLD hvL⟩ 1 (by simpa using hv2)
  have hcov : E.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := ctl_covers hLD hJ.1 hJ.2.2.1 hJcov
  have hvs : s * v = v * s := (Subgroup.mem_centralizer_singleton_iff.1 (hLD hvL)).symm
  obtain ⟨J₀, hJ₀, hEJ₀⟩ := ctl_exists_mem hc hb hs hv hvs hJ hJn hEJ hEs hEgen hvE hcov
  have hvJ₀ : v ∈ J₀ := hEJ₀ hvE
  have hJ₀pc : IsPCompIn 2 (cen s) J₀ := ctl_isPCompIn hJ₀
  have hLK : L ≤ Sec6K X n (cen s) :=
    ctl_le_of_normalizes hq hZ (fun x hx => Sec6K_cen_normal n s (hLD hx)) hvL hv
      ((le_sSup hJ₀ : J₀ ≤ Sec6K X n (cen s)) hvJ₀)
  have hKN : Sec6K X n (cen s) ≤ normalizer (J₀ : Set X) :=
    ctl_sSup_le_normalizer (S := {J | Sec6KComp X n (cen s) J}) hJ₀pc
      (fun J hJ => ctl_isPCompIn hJ)
  have hLN : L ≤ normalizer ((J₀ ⊔ oddCoreOf (cen s) : Subgroup X) : Set X) := fun x hx =>
    mem_normalizer_sup (hKN (hLK hx)) (le_normalizer_oddCoreOf _ (hLD hx))
  have hLJO : L ≤ J₀ ⊔ oddCoreOf (cen s) :=
    ctl_le_of_normalizes hq hZ hLN hvL hv (le_sup_left (b := oddCoreOf (cen s)) hvJ₀)
  have hLJ₀ : L ≤ J₀ := by
    have h1 : L.subgroupOf (cen s) ≤ J₀.subgroupOf (cen s) ⊔ pPrimeCore 2 ↥(cen s) := by
      have := Subgroup.subgroupOf_mono (cen s) hLJO
      rwa [Subgroup.subgroupOf_sup hJ₀pc.1 (oddCoreOf_le _), oddCoreOf_subgroupOf] at this
    have hgen : primeResidual 2 ↥(L.subgroupOf (cen s)) = ⊤ :=
      ((isTwoGenQuasi_subgroupOf_iff hLD).2 hq).1
    have h2 := le_of_le_sup_pPrimeCore hJ₀pc.2 hgen h1
    intro x hx
    exact h2 (show (⟨x, hLD hx⟩ : ↥(cen s)) ∈ L.subgroupOf (cen s) from hx)
  rcases hJ₀ with h5 | h6
  · exfalso
    have hcard := card_quot_pPrimeCore_le_of_covers (le_refl L) hLJ₀
      (by rw [Subgroup.subgroupOf_self, top_sup_eq])
    have hlt := ctl_card_lt hT h5.2
    omega
  · exact ⟨J₀, h6, hLJ₀⟩


private theorem ctl_twist {s t u : X} {K : Subgroup X}
    (hK : IsIntrinsicIn X (cen s) K u)
    (hcovE : (oTwoPrimeOf (K ⊓ cen t)).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤)
    (hEpc : IsPCompIn 2 (cen t ⊓ cen s) (oTwoPrimeOf (K ⊓ cen t))) :
    ∃ v, IsIntrinsicIn X (cen t ⊓ cen s) (oTwoPrimeOf (K ⊓ cen t)) v := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup X := oTwoPrimeOf (K ⊓ cen t) with hEdef
  have hKs : K ≤ cen s := hK.2.2.1.1
  have hKq : IsTwoGenQuasi ↥K :=
    (isTwoGenQuasi_subgroupOf_iff hKs).1 (isPComponent_two_iff.1 hK.2.2.1.2).2
  have hEK : E ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hu2 : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hK.1] at this
  have hu2' : (⟨u, hK.2.1⟩ : ↥K) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hu2)
  have hmem : (⟨u, hK.2.1⟩ : ↥K) ∈ E.subgroupOf K ⊔ pPrimeCore 2 ↥K := by
    rw [hcovE]
    exact Subgroup.mem_top _
  obtain ⟨o, -, a, ha, -, hua⟩ := exists_conj_twoElt_of_mem_sup_odd
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hmem hu2'
  have hua' : u = (o : X) * (a : X) * (o : X)⁻¹ := by
    simpa using congrArg Subtype.val hua
  obtain ⟨φ, hφ⟩ : ∃ φ : X ≃* X, φ = MulAut.conj (o : X)⁻¹ := ⟨_, rfl⟩
  have hφS : (cen s).map φ.toMonoidHom = cen s := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ((cen s).inv_mem (hKs o.2)))
  have hφK : K.map φ.toMonoidHom = K := by
    rw [hφ]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (K.inv_mem o.2))
  have hφu : φ u = (a : X) := by
    rw [hφ, MulAut.conj_apply, hua']
    group
  have hK' := hK.map_mulEquiv φ
  rw [hφS, hφK, hφu] at hK'
  have haE : (a : X) ∈ E := ha
  obtain ⟨hv, hvK, -, hKeq, Lv, hLv, hLveq⟩ := hK'
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hKeq hLveq
  have hGK : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ K := (oTwoPrimeOf_le _).trans inf_le_left
  have hGv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ cen (a : X) := (oTwoPrimeOf_le _).trans inf_le_right
  have hcovG : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
    rw [covers_subgroupOf_iff hGK, sup_comm]
    exact hKeq.symm
  have hGq : IsTwoGenQuasi ↥(oTwoPrimeOf (K ⊓ cen (a : X))) :=
    isTwoGenQuasi_of_covers hGK hcovG (primeResidual_oTwoPrimeOf _) hKq
  have hGLv : oTwoPrimeOf (K ⊓ cen (a : X)) ≤ Lv := le_sup_right.trans hLveq.ge
  have hcovGL : (oTwoPrimeOf (K ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ := by
    rw [covers_subgroupOf_iff hGLv, sup_comm]
    exact hLveq.symm
  have hvs : (a : X) * s = s * (a : X) := Subgroup.mem_centralizer_singleton_iff.1 (hKs hvK)
  have hvK' : (a : X) ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    mem_centralizerSection_of_covers hvs hK.2.2.1 hGK hGv hGq hcovG
  have hEO : E ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 E :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun e he => mem_normalizer_inf (Subgroup.le_normalizer he)
        (mem_normalizer_pPrimeCoreOf_of_mem (hEK he)))
      ((odd_card_oddCoreOf K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  have hvE : (a : X) ∈ centralizerSection E (pPrimeCoreOf 2 E) := by
    refine ⟨Subgroup.le_normalizer haE, mem_normalizer_pPrimeCoreOf_of_mem haE,
      fun e he => hEO ⟨?_, hvK'.2.2 e (hEK he)⟩⟩
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem he haE) (E.inv_mem he)) (E.inv_mem haE)
  have hv2 : (a : X) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (a : X)
    rwa [hv] at this
  have hFE : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ E := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovF : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf E ⊔ pPrimeCore 2 ↥E = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hv2 (primeResidual_oTwoPrimeOf _) hvE
  have hFLv : oTwoPrimeOf (E ⊓ cen (a : X)) ≤ Lv :=
    (oTwoPrimeOf_mono (inf_le_inf_right _ hEK)).trans hGLv
  have hc1 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hFE hcovF).some.toEquiv
  have hc2 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hEK hcovE).some.toEquiv
  have hc3 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGK hcovG).some.toEquiv
  have hc4 := Nat.card_congr (nonempty_quot_mulEquiv_of_covers hGLv hcovGL).some.toEquiv
  have hcovFL : (oTwoPrimeOf (E ⊓ cen (a : X))).subgroupOf Lv ⊔ pPrimeCore 2 ↥Lv = ⊤ :=
    covers_of_card_le hFLv (by omega)
  refine ⟨(a : X), hv, haE, hEpc, ?_, Lv, hLv, ?_⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFE).1 hcovF).symm.trans (sup_comm _ _)
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    exact ((covers_subgroupOf_iff hFLv).1 hcovFL).symm.trans (sup_comm _ _)

private theorem ctl_lift_narrow {n : ℕ} (hc : SolCEx X)
    (hb : ∀ H : Subgroup X, H ≠ ⊤ → ∀ t ∈ H, orderOf t = 2 →
      Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H)
    {s : X} (hs : orderOf s = 2) {H L : Subgroup X} (hHs : H ≤ cen s) (hL : Sec5Comp X n H L) :
    ∃ J : Subgroup X, Sec6KComp X n (cen s) J ∧ L ≤ J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨u, hu, huL, ⟨hLH, hLpc⟩, hLeq, Lu, hLuI, hLuEq⟩, hLn⟩ := hL
  set E : Subgroup X := oTwoPrimeOf (L ⊓ centralizer ({u} : Set X))
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq hLuEq
  have hEL : E ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hELu : E ≤ Lu := by
    rw [hLuEq]
    exact le_sup_right
  have hLs : L ≤ cen s := hLH.trans hHs
  have hEs : E ≤ cen s := hEL.trans hLs
  have hEgen : primeResidual 2 ↥E = ⊤ := primeResidual_oTwoPrimeOf _
  have hu2 : u ^ 2 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have huE : u ∈ E :=
    mem_oTwoPrimeOf ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ 1 (by simpa using hu2)
  have hcovL : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    exact hLeq.symm
  have hcovLu : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [covers_subgroupOf_iff hELu, sup_comm]
    exact hLuEq.symm
  have hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hELu hcovLu n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEL hcovL n).2 hLn)
  have hus : s * u = u * s :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hLs huL)).symm
  obtain ⟨J, hJ, hEJ⟩ := ctl_exists_mem hc hb hs hu hus hLuI hLun hELu hEs hEgen huE hcovLu
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLH).1 (isPComponent_two_iff.1 hLpc).2
  have hJpc : IsPCompIn 2 (cen s) J := ctl_isPCompIn hJ
  have hLK : L ≤ Sec6K X n (cen s) :=
    le_of_covers_of_normalized hEL hcovL hLq.1 (hEJ.trans (le_sSup hJ)) fun c hc' =>
      Sec6K_cen_normal n s (hLs hc')
  have hLN : ∀ c ∈ L, c ∈ normalizer ((J ⊔ oddCoreOf (cen s) : Subgroup X) : Set X) :=
    fun x hx =>
      mem_normalizer_sup (ctl_K_le_normalizer hJ (hLK hx)) (le_normalizer_oddCoreOf _ (hLs hx))
  have hLJO : L ≤ J ⊔ oddCoreOf (cen s) :=
    le_of_covers_of_normalized hEL hcovL hLq.1 (hEJ.trans le_sup_left) hLN
  exact ⟨J, hJ, le_of_le_sup_pPrimeCoreOf hJpc hLs hLq.1 hLJO⟩

private theorem ctl_lift
    {n : ℕ} (hc : SolCEx X)
    (hb : ∀ H : Subgroup X, H ≠ ⊤ → ∀ t ∈ H, orderOf t = 2 →
      Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H)
    {s : X} (hs : orderOf s = 2) {H L : Subgroup X} (hHs : H ≤ cen s) (hL : Sec6KComp X n H L) :
    ∃ J : Subgroup X, Sec6KComp X n (cen s) J ∧ L ≤ J := by
  rcases hL with h5 | h6
  · exact ctl_lift_narrow hc hb hs hHs h5
  · obtain ⟨J, hJ, hLJ⟩ := ctl_broad hc hb hs hHs h6
    exact ⟨J, Or.inr hJ, hLJ⟩

end Toolkit

section Pieces

variable {X : Type} [Group X] [Finite X]

private theorem ctl_mem_normalizer_of_map_le {V : Subgroup X} {b : X}
    (h : V.map (MulAut.conj b).toMonoidHom ≤ V) : b ∈ normalizer (V : Set X) :=
  mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]))

private theorem ctl_mem_normalizer_oTwoPrimeOf {A : Subgroup X} {g : X}
    (hg : g ∈ normalizer (A : Set X)) : g ∈ normalizer (oTwoPrimeOf A : Set X) := by
  apply ctl_mem_normalizer_of_map_le
  have := map_oTwoPrimeOf_le A (MulAut.conj g).toMonoidHom
  rwa [map_conj_eq_of_mem_normalizer hg] at this

private theorem ctl_odd_card_sup {H N : Subgroup X}
    (hHN : H ≤ normalizer (N : Set X)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup X)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

private theorem ctl_oddCoreOf_le_of_normal {K C : Subgroup X} (hKC : K ≤ C)
    (hn : C ≤ normalizer (K : Set X)) : oddCoreOf K ≤ oddCoreOf C :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le K).trans hKC)
    (fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (hn hc)) (odd_card_oddCoreOf K)

private theorem ctl_conj_mem_cs {K M : Subgroup X} {c x : X}
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

private theorem ctl_le_normalizer_QOf (L : Subgroup X) : L ≤ normalizer (QOf L : Set X) := by
  intro m hm
  have hmL : m ∈ normalizer (L : Set X) := Subgroup.le_normalizer hm
  have hmO : m ∈ normalizer (pPrimeCoreOf 2 L : Set X) := mem_normalizer_pPrimeCoreOf_of_mem hm
  rw [mem_normalizer_iff]
  intro x
  refine ⟨ctl_conj_mem_cs hmL hmO, fun hx => ?_⟩
  have h1 := ctl_conj_mem_cs (inv_mem hmL) (inv_mem hmO) hx
  have h2 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [h2] at h1

private theorem ctl_exists_inner {L : Subgroup X} {x : X} (hx : x ∈ L ⊔ QOf L) :
    ∃ m ∈ L, m⁻¹ * x ∈ QOf L := by
  obtain ⟨m, hm, k, hk, rfl⟩ := ctl_exists_mul_of_mem_sup (ctl_le_normalizer_QOf L) hx
  exact ⟨m, hm, by rwa [inv_mul_cancel_left]⟩

private theorem ctl_oddCoreOf_le_QOf (L : Subgroup X) : oddCoreOf L ≤ QOf L := by
  intro o ho
  have hoL : o ∈ L := oddCoreOf_le L ho
  refine mem_QOf_iff.2 ⟨Subgroup.le_normalizer hoL, fun l hl => ?_⟩
  have h1 : ⁅l, o⁆ = (l * o * l⁻¹) * o⁻¹ := by rw [commutatorElement_def]
  rw [h1]
  exact (oddCoreOf L).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf L hl) o).1 ho)
    ((oddCoreOf L).inv_mem ho)

private theorem ctl_QOf_le_normalizer (L : Subgroup X) : QOf L ≤ normalizer (L : Set X) :=
  fun _ hc => (mem_QOf_iff.1 hc).1

private theorem ctl_sup_QOf_le_normalizer (L : Subgroup X) :
    L ⊔ QOf L ≤ normalizer (L : Set X) :=
  sup_le Subgroup.le_normalizer (ctl_QOf_le_normalizer L)

private theorem ctl_K_le (n : ℕ) (t : X) : Sec6K X n (cen t) ≤ cen t :=
  sSup_le fun _ hL => (ctl_isPCompIn hL).1

private theorem ctl_M_le_K (n : ℕ) (H : Subgroup X) : Sec6M X n H ≤ Sec6K X n H := by
  rw [sec6K_eq]
  exact le_sup_right

private theorem ctl_MQ_le_cen (n : ℕ) (t : X) :
    Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) ≤ cen t :=
  sup_le ((ctl_M_le_K n _).trans (ctl_K_le n t)) inf_le_left

private theorem ctl_Q_le_QOf {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    Sec6Q X n (cen t) ≤ QOf L := by
  intro q hq
  obtain ⟨hqt, hqK, -, hqc⟩ := hq
  set K : Subgroup X := Sec6K X n (cen t) with hKdef
  have hLpc := ctl_isPCompIn hL
  have hLK : L ≤ K := le_sSup hL
  have hOK : oddCoreOf K ≤ oddCoreOf (cen t) :=
    ctl_oddCoreOf_le_of_normal (ctl_K_le n t) (Sec6K_cen_normal n t)
  have hmap : L.map (MulAut.conj q).toMonoidHom ≤ L := by
    have hED : L.map (MulAut.conj q).toMonoidHom ≤ cen t := by
      rintro _ ⟨l, hl, rfl⟩
      exact (cen t).mul_mem ((cen t).mul_mem hqt (hLpc.1 hl)) ((cen t).inv_mem hqt)
    have hgen : primeResidual 2 ↥(L.map (MulAut.conj q).toMonoidHom) = ⊤ :=
      primeResidual_eq_top_of_equiv 2 (L.equivMapOfInjective _ (MulAut.conj q).injective)
        (ctl_isTwoGenQuasi hL).1
    refine le_of_le_sup_pPrimeCoreOf hLpc hED hgen ?_
    rintro _ ⟨l, hl, rfl⟩
    have h1 : ⁅l⁻¹, q⁆ ∈ oddCoreOf K := hqc _ (hLK (L.inv_mem hl))
    have h2 : (MulAut.conj q).toMonoidHom l = l * ⁅l⁻¹, q⁆ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [h2]
    exact Subgroup.mul_mem_sup hl (hOK h1)
  have hqN : q ∈ normalizer (L : Set X) := ctl_mem_normalizer_of_map_le hmap
  refine mem_QOf_iff.2 ⟨hqN, fun l hl => ?_⟩
  have hcK : ⁅l, q⁆ ∈ oddCoreOf K := hqc l (hLK hl)
  have hcL : ⁅l, q⁆ ∈ L := by
    have h1 : ⁅l, q⁆ = l * (q * l⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact L.mul_mem hl ((mem_normalizer_iff.1 hqN l⁻¹).1 (L.inv_mem hl))
  exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf K (hLK hx))
    (odd_card_oddCoreOf K) ⟨hcL, hcK⟩

private theorem ctl_le_QOf_of_ne {H L J : Subgroup X} (hL : IsPCompIn 2 H L)
    (hJ : IsPCompIn 2 H J) (hne : L ≠ J) : J ≤ QOf L := by
  intro j hj
  have hOLL : pPrimeCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hc : ∀ g ∈ J, ∀ m ∈ L, ⁅m, g⁆ ∈ pPrimeCoreOf 2 L := fun g hg m hm =>
    ctl_commutatorElement_mem hL hJ hne hm hg
  exact mem_QOf_iff.2 ⟨ctl_mem_normalizer (fun m hm => hOLL (hc j hj m hm))
    (fun m hm => hOLL (hc j⁻¹ (J.inv_mem hj) m hm)), fun m hm => hc j hj m hm⟩

private theorem ctl_ne_of_A_M
    {n : ℕ} {H L J : Subgroup X} (hL : Sec5Comp X n H L) (hJ : Sec6MComp X n H J) : L ≠ J := by
  rintro rfl
  exact lt_irrefl _ (ctl_card_lt hJ.2 hL.2)

private theorem ctl_MQ_le_QOf_A
    {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec5Comp X n (cen t) L) :
    Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) ≤ QOf L := by
  refine sup_le (sSup_le fun J hJ => ?_) (ctl_Q_le_QOf (Or.inl hL))
  exact ctl_le_QOf_of_ne (ctl_isPCompIn (Or.inl hL)) (ctl_isPCompIn (Or.inr hJ))
    (ctl_ne_of_A_M hL hJ)

private theorem ctl_MQ_le_sup_M {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) :
    Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) ≤ L ⊔ QOf L := by
  refine sup_le (sSup_le fun J hJ => ?_) ((ctl_Q_le_QOf (Or.inr hL)).trans le_sup_right)
  by_cases h : L = J
  · rw [← h]
    exact le_sup_left
  · exact (ctl_le_QOf_of_ne (ctl_isPCompIn (Or.inr hL)) (ctl_isPCompIn (Or.inr hJ)) h).trans
      le_sup_right

end Pieces

section Transfer

variable {X : Type} [Group X] [Finite X]

private theorem ctl_card_of_dc {K : Type} [Group K] {m : ℕ} (hm : 2 ≤ m)
    (h : IsDoubleCoverOfAlt K m) : Nat.card K = m.factorial := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [h1, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) hm)

private theorem ctl_two_le {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) : 2 ≤ n := by
  rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

private theorem ctl_cent_dc
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

private theorem ctl_orderOf_mk {M : Subgroup X} {s : X} (hsM : s ∈ M) (hs : orderOf s = 2) :
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

private theorem ctl_card_quot_le_of_cen
    {n : ℕ} {M W : Subgroup X} {s : X} (hT : IsSec6MType n (↥M ⧸ pPrimeCore 2 ↥M)) (hsM : s ∈ M)
    (hs : orderOf s = 2) (hWM : W ≤ M) (hWs : ∀ w ∈ W, ⁅w, s⁆ ∈ pPrimeCoreOf 2 M) :
    Nat.card (↥W ⧸ pPrimeCore 2 ↥W) ≤ n.factorial := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥M →* ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set f : ↥W →* ↥M ⧸ pPrimeCore 2 ↥M := π.comp (Subgroup.inclusion hWM) with hf
  have hC := ctl_cent_dc hT (ctl_orderOf_mk hsM hs)
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
    obtain ⟨w', hw', hww'⟩ := ctl_inf_le_oddCoreOf
      (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hWM hx)) (odd_card_oddCoreOf M) h2
    have : w' = w := Subtype.ext hww'
    rwa [← this]
  calc Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = (pPrimeCore 2 ↥W).index := (Subgroup.index_eq_card _).symm
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card f.range := Subgroup.index_ker f
    _ ≤ Nat.card ↥(centralizer ({π ⟨s, hsM⟩} : Set (↥M ⧸ pPrimeCore 2 ↥M))) :=
        Subgroup.card_le_of_le hrange
    _ = n.factorial := ctl_card_of_dc (ctl_two_le hT) hC

private theorem ctl_mem_normalizer_sup_of_mem {A B C : Subgroup X} (hAC : A ≤ C)
    (hBn : C ≤ normalizer (B : Set X)) {o : X} (ho : o ∈ B) :
    o ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  apply ctl_mem_normalizer_of_map_le
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

private theorem ctl_transfer
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
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := ctl_degree hT hsM hs hJ hJcov
  obtain ⟨hJC, -, hJpc, -⟩ := hJ
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJC).1 (isPComponent_two_iff.1 hJpc).2
  have hRM : R ≤ M ⊓ cen s := oTwoPrimeOf_le _
  have hWR : W ≤ R := oTwoPrimeOf_mono inf_le_left
  have hRgen : primeResidual 2 ↥R = ⊤ := primeResidual_oTwoPrimeOf _
  have hWgen : primeResidual 2 ↥W = ⊤ := primeResidual_oTwoPrimeOf _
  have hcR : c ∈ normalizer (R : Set X) :=
    ctl_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf hcM (Subgroup.le_normalizer hcs))
  have hcomm : ∀ r ∈ R, ⁅r, c⁆ ∈ pPrimeCoreOf 2 R := by
    intro r hr
    have h1 : ⁅r, c⁆ ∈ pPrimeCoreOf 2 M := hcen r (hRM hr)
    have h2 : ⁅r, c⁆ ∈ R := by
      have h3 : ⁅r, c⁆ = r * (c * r⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact R.mul_mem hr ((mem_normalizer_iff.1 hcR r⁻¹).1 (R.inv_mem hr))
    exact ctl_inf_le_oddCoreOf (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hRM hx).1)
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
    ctl_odd_card_sup (fun x hx => le_normalizer_oddCoreOf (cen s) ((hRM ((oddCoreOf_le R) hx)).2))
      (odd_card_oddCoreOf R) (odd_card_oddCoreOf _)
  have hNZ : N ≤ Z := sup_le ((oddCoreOf_le R).trans le_sup_left) le_sup_right
  have hZN : Z ≤ normalizer (N : Set X) := by
    refine sup_le (fun r hr => ?_) (fun o ho => ?_)
    · exact mem_normalizer_sup (le_normalizer_oddCoreOf R hr)
        (le_normalizer_oddCoreOf (cen s) (hRM hr).2)
    · exact ctl_mem_normalizer_sup_of_mem (C := cen s)
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
    ctl_card_quot_le_of_cen hT hsM hs (hWR.trans (hRM.trans inf_le_left)) fun w hw => by
      have hws : w * s = s * w :=
        Subgroup.mem_centralizer_singleton_iff.1 ((hWR.trans (hRM.trans inf_le_right)) hw)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hws]
      exact one_mem _
  have hJcard : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = n.factorial :=
    ctl_card_of_dc (ctl_two_le hT) hJn
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

end Transfer

section PieceStructure

variable {X : Type} [Group X] [Finite X]

private theorem ctl_mem_of_central {L : Subgroup X} (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥)
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

private theorem ctl_comm_mem {L : Subgroup X} {a b x : X} (hxL : x ∈ L) (hab : a⁻¹ * b ∈ QOf L)
    (hxa : x * a = a * x) (haN : a ∈ normalizer (pPrimeCoreOf 2 L : Set X)) :
    ⁅x, b⁆ ∈ pPrimeCoreOf 2 L := by
  have h1 : ⁅x, a⁻¹ * b⁆ ∈ pPrimeCoreOf 2 L := (mem_QOf_iff.1 hab).2 x hxL
  have h2 : ⁅x, b⁆ = a * ⁅x, a⁻¹ * b⁆ * a⁻¹ := by
    have hx' : a * x * a⁻¹ = x := by rw [← hxa, mul_inv_cancel_right]
    calc ⁅x, b⁆ = (a * x * a⁻¹) * b * x⁻¹ * b⁻¹ := by rw [hx', commutatorElement_def]
      _ = a * ⁅x, a⁻¹ * b⁆ * a⁻¹ := by rw [commutatorElement_def]; group
  rw [h2]
  exact (mem_normalizer_iff.1 haN _).1 h1

private theorem ctl_exists_inv_inner {L : Subgroup X} {c : X}
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) (hc2 : c ^ 2 = 1) (hcL : c ∈ L ⊔ QOf L)
    (hc : c ∉ QOf L) : ∃ v ∈ L ⊓ cen c, orderOf v = 2 ∧ v⁻¹ * c ∈ QOf L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmL, hmq⟩ := ctl_exists_inner hcL
  set q : X := m⁻¹ * c with hq
  have hcmq : c = m * q := by rw [hq, mul_inv_cancel_left]
  have hcN : c ∈ normalizer (L : Set X) := ctl_sup_QOf_le_normalizer L hcL
  have hcO : c ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hcN
  have hOQ : pPrimeCoreOf 2 L ≤ QOf L := ctl_oddCoreOf_le_QOf L
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
    exact (mem_normalizer_iff.1 (ctl_le_normalizer_QOf L (L.inv_mem hmL)) _).1
      ((QOf L).inv_mem hmq)
  have hm2O : m ^ (2 ^ 1) ∈ pPrimeCoreOf 2 L := by
    rw [pow_one]
    exact ctl_mem_of_central hZ (L.pow_mem hmL 2) fun l hl => (mem_QOf_iff.1 hm2Q).2 l hl
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
    ctl_comm_mem hyL hyc rfl (mem_normalizer_pPrimeCoreOf_of_mem hyL)
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

private theorem ctl_piece_A {n : ℕ} {r c : X} {L : Subgroup X} (hc2 : orderOf c = 2)
    (hL : Sec5Comp X n (cen r) L) (hc : c ∈ QOf L) :
    Sec5Comp X n (cen c ⊓ cen r) (sec6Piece L c) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨u, hu⟩, hLn⟩ := hL
  have hLpc : IsPCompIn 2 (cen r) L := hu.2.2.1
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLpc.1).1 (isPComponent_two_iff.1 hLpc.2).2
  have hc2' : c ^ 2 = 1 := by
    rw [← hc2]
    exact pow_orderOf_eq_one c
  have hPL : oTwoPrimeOf (L ⊓ cen c) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hcov : (oTwoPrimeOf (L ⊓ cen c)).subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hc2' hLq.1 hc
  have hPq : IsTwoGenQuasi ↥(oTwoPrimeOf (L ⊓ cen c)) :=
    isTwoGenQuasi_of_covers hPL hcov (primeResidual_oTwoPrimeOf _) hLq
  obtain ⟨v, hv⟩ := ctl_twist hu hcov (ctl_isPCompIn_piece hLpc hPq)
  exact ⟨⟨v, hv⟩, (isDoubleCoverOfAlt_quot_iff_of_covers hPL hcov n).2 hLn⟩

private theorem ctl_piece_M_cent
    {n : ℕ} {r c : X}
    {L : Subgroup X} (hc2 : orderOf c = 2) (hL : Sec6MComp X n (cen r) L) (hc : c ∈ QOf L) :
    Sec6MComp X n (cen c ⊓ cen r) (sec6Piece L c) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hLpc, htype, hLJ⟩, hT⟩ := hL
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLpc.1).1 (isPComponent_two_iff.1 hLpc.2).2
  have hc2' : c ^ 2 = 1 := by
    rw [← hc2]
    exact pow_orderOf_eq_one c
  set P : Subgroup X := oTwoPrimeOf (L ⊓ cen c) with hP
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPc : P ≤ cen c := (oTwoPrimeOf_le _).trans inf_le_right
  have hcov : P.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hc2' hLq.1 hc
  have hPq : IsTwoGenQuasi ↥P :=
    isTwoGenQuasi_of_covers hPL hcov (primeResidual_oTwoPrimeOf _) hLq
  have hPpc : IsPCompIn 2 (cen c ⊓ cen r) P := ctl_isPCompIn_piece hLpc hPq
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_covers hPL hcov
  obtain ⟨hcN, hcC⟩ := mem_QOf_iff.1 hc
  refine ⟨⟨hPpc, htype.imp (Nonempty.map e.trans) (Nonempty.map e.trans),
    fun s hsP hs => ?_⟩, hT.congr e.symm⟩
  obtain ⟨J, hJ, hJcov⟩ := hLJ s (hPL hsP) hs
  have hcs : c ∈ cen s :=
    Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (hPc hsP)).symm
  obtain ⟨hWJ, hJeq⟩ :=
    ctl_transfer hT (hPL hsP) hs hc2' hcs hcN (fun y hy => hcC y hy.1) hJ hJcov
  refine ⟨J, hJ, ?_⟩
  rw [hJeq]
  refine sup_le ((pPrimeCoreOf_le_oddCoreOf hJ.1 (isPComponent_two_iff.1 hJ.2.2.1).1).trans
    le_sup_right) (le_sup_of_le_left (le_inf (oTwoPrimeOf_mono ?_)
      ((oTwoPrimeOf_le _).trans (inf_le_left.trans inf_le_right))))
  exact inf_le_inf_right _ inf_le_left

private theorem ctl_piece_M_inner
    {n : ℕ} {r c : X}
    {L : Subgroup X} (hc2 : orderOf c = 2) (hL : Sec6MComp X n (cen r) L)
    (hcL : c ∈ L ⊔ QOf L) (hc : c ∉ QOf L) :
    Sec5Comp X n (cen c ⊓ cen r) (sec6Piece L c) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hLpc, htype, hLJ⟩, hT⟩ := hL
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := mcLLyCenterFree _ htype
  have hc2' : c ^ 2 = 1 := by
    rw [← hc2]
    exact pow_orderOf_eq_one c
  obtain ⟨v, ⟨hvL, hvc⟩, hv, hvq⟩ := ctl_exists_inv_inner hZ hc2' hcL hc
  unfold sec6Piece
  set P : Subgroup X := oTwoPrimeOf (L ⊓ cen c) with hP
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPc : P ≤ cen c := (oTwoPrimeOf_le _).trans inf_le_right
  have hv2 : v ^ 2 = 1 := by
    rw [← hv]
    exact pow_orderOf_eq_one v
  have hvP : v ∈ P := mem_oTwoPrimeOf ⟨hvL, hvc⟩ 1 (by simpa using hv2)
  have hcN : c ∈ normalizer (L : Set X) := ctl_sup_QOf_le_normalizer L hcL
  have hcO : c ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hcN
  have hcv : c ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvc).symm
  obtain ⟨J, hJ, hJcov⟩ := hLJ v hvL hv
  obtain ⟨hWJ, hJeq⟩ := ctl_transfer hT hvL hv hc2' hcv hcN
    (fun y hy => ctl_comm_mem hy.1 hvq (Subgroup.mem_centralizer_singleton_iff.1 hy.2)
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
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := ctl_degree hT hvL hv hJ hJcov
  have hWPle : W ≤ P := by
    rw [hWP]
    exact (oTwoPrimeOf_le _).trans inf_le_left
  have hcv' : c⁻¹ * v ∈ QOf L := by
    have h1 : c⁻¹ * v = (v⁻¹ * c)⁻¹ := by group
    rw [h1]
    exact (QOf L).inv_mem hvq
  have hPcard : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) ≤ n.factorial :=
    ctl_card_quot_le_of_cen hT hvL hv hPL fun p hp =>
      ctl_comm_mem (hPL hp) hcv' (Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)) hcO
  have hWcard : Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = n.factorial := by
    rw [Nat.card_congr eWJ.toEquiv]
    exact ctl_card_of_dc (ctl_two_le hT) hJn
  have hWcovP : W.subgroupOf P ⊔ pPrimeCore 2 ↥P = ⊤ :=
    covers_of_card_le hWPle (hPcard.trans hWcard.ge)
  obtain ⟨eWP⟩ := nonempty_quot_mulEquiv_of_covers hWPle hWcovP
  have hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n :=
    isDoubleCoverOfAlt_congr' (eWJ.symm.trans eWP) hJn
  have hPq : IsTwoGenQuasi ↥P := ⟨primeResidual_oTwoPrimeOf _, hPn.1⟩
  have hPpc : IsPCompIn 2 (cen c ⊓ cen r) P := ctl_isPCompIn_piece hLpc hPq
  refine ⟨⟨v, hv, hvP, hPpc, ?_, J, hJ, ?_⟩, hPn⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, ← hWP, sup_comm]
    exact ((covers_subgroupOf_iff hWPle).1 hWcovP).symm
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, ← hWP]
    exact hJeq

private theorem ctl_piece_K
    {n : ℕ} {r c : X}
    {L : Subgroup X} (hc2 : orderOf c = 2) (hL : Sec6KComp X n (cen r) L)
    (hcA : Sec5Comp X n (cen r) L → c ∈ QOf L) (hcM : Sec6MComp X n (cen r) L → c ∈ L ⊔ QOf L) :
    Sec6KComp X n (cen c ⊓ cen r) (sec6Piece L c) := by
  rcases hL with h5 | h6
  · exact Or.inl (ctl_piece_A hc2 h5 (hcA h5))
  · by_cases hq : c ∈ QOf L
    · exact Or.inr (ctl_piece_M_cent hc2 h6 hq)
    · exact Or.inl (ctl_piece_M_inner hc2 h6 (hcM h6) hq)

end PieceStructure

theorem sec6Piece_mem
    {X : Type} [Group X] [Finite X]
    {n : ℕ} {t b : X} (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2)
    {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    Sec6KComp X n (cen b ⊓ cen t) (sec6Piece L b) :=
  ctl_piece_K hb2 hL (fun h5 => ctl_MQ_le_QOf_A h5 hb) (fun h6 => ctl_MQ_le_sup_M h6 hb)

theorem sec6Ctrl_land
    {X : Type} [Group X] [Finite X]
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n) {b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2) {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) :
    ∃ F : Subgroup X, Sec6KComp X n (cen b) F ∧ sec6Piece L b ≤ F :=
  ctl_lift hS.cex h51.b hb2 inf_le_left (sec6Piece_mem hb hb2 hL)

section Dich

variable {X : Type} [Group X] [Finite X]

private theorem ctl_card_quot_le_range {M W : Subgroup X} (hWM : W ≤ M) :
    Nat.card (↥W ⧸ pPrimeCore 2 ↥W) ≤
      Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hWM)).range := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥W →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hWM) with hf
  have hker : f.ker ≤ pPrimeCore 2 ↥W := by
    intro w hw
    have h1 : Subgroup.inclusion hWM w ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hw
    have h2 : (w : X) ∈ W ⊓ pPrimeCoreOf 2 M := ⟨w.2, ⟨_, h1, rfl⟩⟩
    obtain ⟨w', hw', hww'⟩ := ctl_inf_le_oddCoreOf
      (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hWM hx)) (odd_card_oddCoreOf M) h2
    have : w' = w := Subtype.ext hww'
    rwa [← this]
  calc Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = (pPrimeCore 2 ↥W).index := (Subgroup.index_eq_card _).symm
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hker)
    _ = Nat.card f.range := Subgroup.index_ker f

private theorem ctl_quotConj_mk {A : Subgroup X} {c : X} (hc : c ∈ normalizer (A : Set X))
    (a : ↥A) : quotConj hc (QuotientGroup.mk a) = QuotientGroup.mk (conjAut hc a) := rfl

private theorem ctl_inner_of_conj {F : Subgroup X} {t : X} (htN : t ∈ normalizer (F : Set X))
    {g : ↥F ⧸ pPrimeCore 2 ↥F} (hα : quotConj htN = MulAut.conj g) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(g₀ : X)⁻¹, F.inv_mem g₀.2, fun a ha => ?_⟩
  set a' : ↥F := ⟨a⁻¹, F.inv_mem ha⟩ with ha'
  have h1 : (QuotientGroup.mk (g₀ * a' * g₀⁻¹) : ↥F ⧸ pPrimeCore 2 ↥F) =
      QuotientGroup.mk (conjAut htN a') := by
    rw [← ctl_quotConj_mk, hα, MulAut.conj_apply]
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

private theorem ctl_inner_ly
    {F : Subgroup X} {t : X} (htN : t ∈ normalizer (F : Set X))
    (he : Nonempty (↥F ⧸ pPrimeCore 2 ↥F ≃* Blueprint.NativeSporadic.Ly)) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨g, hg⟩ :=
    GH74.GLS.Stage2.Bender.Thm1.LyOut.lyAllInner_thm (↥F ⧸ pPrimeCore 2 ↥F) he (quotConj htN)
  exact ctl_inner_of_conj htN hg

private theorem ctl_mem_fixedSubgroup {G : Type} [Group G] (σ : MulAut G) (x : G) :
    x ∈ CFSG.Sporadic.Recognition.McLAS.fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem ctl_mem_mclFixed (σ : MulAut Blueprint.NativeSporadic.McL)
    (x : Blueprint.NativeSporadic.McL) :
    x ∈ CFSG.Sporadic.Recognition.McLAS.mclFixed σ ↔ σ x = x := Iff.rfl

private theorem ctl_fixed_iff {Q G : Type} [Group Q] [Mul G] (e : Q ≃* G) (α : MulAut Q)
    (σ : MulAut G) (h : ∀ y, σ (e y) = e (α y)) (y : Q) : α y = y ↔ σ (e y) = e y := by
  rw [h]
  exact ⟨fun h' => by rw [h'], fun h' => e.injective h'⟩

private theorem ctl_quotConj_sq {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
    (htN : t ∈ normalizer (F : Set X)) (y : ↥F ⧸ pPrimeCore 2 ↥F) :
    quotConj htN (quotConj htN y) = y := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  rw [ctl_quotConj_mk, ctl_quotConj_mk]
  congr 1
  apply Subtype.ext
  simp only [coe_conjAut]
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
  rw [hti, ← mul_assoc, ← mul_assoc, ht', one_mul, mul_assoc, ht', mul_one]

private theorem ctl_inner_mcl
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
    refine ctl_inner_of_conj htN (g := e.symm g) ?_
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
        rw [pow_two, MulAut.mul_apply, hσapp, hσapp, ctl_quotConj_sq ht2 htN, MulAut.one_apply]
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
        (ctl_mem_fixedSubgroup _ y).trans ((ctl_fixed_iff e (quotConj htN) σ hσapp y).trans
          (ctl_mem_mclFixed σ (e y)).symm))
    have hrange : ((QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)).range ≤
        CFSG.Sporadic.Recognition.McLAS.fixedSubgroup (quotConj htN) := by
      rintro _ ⟨p, rfl⟩
      rw [ctl_mem_fixedSubgroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ctl_quotConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_conjAut]
      have hp : (p : X) * t = t * p := Subgroup.mem_centralizer_singleton_iff.1 (hPt p.2)
      simp only [Subgroup.coe_inclusion]
      rw [← hp, mul_inv_cancel_right]
    have h1 := Subgroup.card_le_of_le hrange
    have h2 := ctl_card_quot_le_range hPF
    omega

private theorem ctl_factorial_lt
    {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) : n.factorial < Nat.card Q := by
  rcases hT with ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]
    have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ly.card_Ly']
    have h11 : Nat.factorial 11 = 39916800 := by norm_num [Nat.factorial]
    omega

private theorem ctl_card_ge
    {n : ℕ} (hn : 2 ≤ n) {H P : Subgroup X} (hP : Sec6KComp X n H P) :
    n.factorial ≤ Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := by
  rcases hP with h5 | h6
  · exact (ctl_card_of_dc hn h5.2).ge
  · exact (ctl_factorial_lt h6.2).le

private theorem ctl_isPCompIn_conj {H F : Subgroup X} {g : X} (hF : IsPCompIn 2 H F)
    (hg : g ∈ normalizer (H : Set X)) : IsPCompIn 2 H (F.map (MulAut.conj g).toMonoidHom) := by
  have h := (isPComponent_subgroupOf_map_iff 2 (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective hF.1).2 hF.2
  rw [map_conj_eq_of_mem_normalizer hg] at h
  refine ⟨?_, h⟩
  rw [← map_conj_eq_of_mem_normalizer hg]
  exact Subgroup.map_mono hF.1

private theorem ctl_normalizes {b t : X} {F P : Subgroup X} (hbt : b ∈ cen t)
    (hF : IsPCompIn 2 (cen b) F) (hPF : P ≤ F) (hPt : P ≤ cen t) (hPq : IsTwoGenQuasi ↥P) :
    t ∈ normalizer (F : Set X) := by
  have htb : t ∈ cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  have hF' := ctl_isPCompIn_conj hF (Subgroup.le_normalizer htb)
  have hPF' : P ≤ F.map (MulAut.conj t).toMonoidHom := by
    intro p hp
    refine ⟨p, hPF hp, ?_⟩
    have hpt : p * t = t * p := Subgroup.mem_centralizer_singleton_iff.1 (hPt hp)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hpt, mul_inv_cancel_right]
  exact mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hF hF' hPF hPF' hPq).symm

private theorem ctl_dich_cent {b t : X} {F P : Subgroup X} (ht2 : t ^ 2 = 1)
    (hF : IsPCompIn 2 (cen b) F) (hP : IsPCompIn 2 (cen t ⊓ cen b) P) (hPF : P ≤ F)
    (hPt : P ≤ cen t) (htN : t ∈ normalizer (F : Set X)) (hcent : CentModOdd F t) :
    F = oddCoreOf F ⊔ P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFq : IsTwoGenQuasi ↥F :=
    (isTwoGenQuasi_subgroupOf_iff hF.1).1 (isPComponent_two_iff.1 hF.2).2
  have hPq : IsTwoGenQuasi ↥P :=
    (isTwoGenQuasi_subgroupOf_iff hP.1).1 (isPComponent_two_iff.1 hP.2).2
  have htQ : t ∈ QOf F := mem_QOf_iff.2 ⟨htN, hcent⟩
  have hEF : oTwoPrimeOf (F ⊓ cen t) ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hcov := oTwoPrimeOf_inf_centralizer_covers ht2 hFq.1 htQ
  have hEq : IsTwoGenQuasi ↥(oTwoPrimeOf (F ⊓ cen t)) :=
    isTwoGenQuasi_of_covers hEF hcov (primeResidual_oTwoPrimeOf _) hFq
  have hEpc : IsPCompIn 2 (cen t ⊓ cen b) (oTwoPrimeOf (F ⊓ cen t)) := ctl_isPCompIn_piece hF hEq
  have hPE : P ≤ oTwoPrimeOf (F ⊓ cen t) := by
    have := oTwoPrimeOf_mono (le_inf hPF hPt : P ≤ F ⊓ cen t)
    rwa [oTwoPrimeOf_eq_self_of_primeResidual hPq.1] at this
  have hEP : oTwoPrimeOf (F ⊓ cen t) = P := eq_of_isPCompIn_of_le hEpc hP hPE le_rfl hPq
  rw [← hEP, sup_comm]
  exact ((covers_subgroupOf_iff hEF).1 hcov).symm

theorem sec6Ctrl_dich
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) {b : X} (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t))
    (hb2 : orderOf b = 2) {L F : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    (hF : Sec6KComp X n (cen b) F) (hPF : sec6Piece L b ≤ F) :
    t ∈ normalizer (F : Set X) ∧
      (F = oddCoreOf F ⊔ sec6Piece L b ∨
        (Sec6MComp X n (cen b) F ∧ ¬ CentModOdd F t ∧ ∃ f ∈ F, CentModOdd F (f * t))) := by
  have hn : 2 ≤ n := by rcases hS.deg with h | h <;> omega
  have hPK := sec6Piece_mem hb hb2 hL
  have hPpc : IsPCompIn 2 (cen b ⊓ cen t) (sec6Piece L b) := ctl_isPCompIn hPK
  have hPq : IsTwoGenQuasi ↥(sec6Piece L b) := ctl_isTwoGenQuasi hPK
  have hPt : sec6Piece L b ≤ cen t := hPpc.1.trans inf_le_right
  have hbt : b ∈ cen t := ctl_MQ_le_cen n t hb
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hFpc := ctl_isPCompIn hF
  have htN := ctl_normalizes hbt hFpc hPF hPt hPq
  refine ⟨htN, ?_⟩
  by_cases hcent : CentModOdd F t
  · left
    exact ctl_dich_cent ht2 hFpc (by rw [inf_comm]; exact hPpc) hPF hPt htN hcent
  · right
    have hPcard := ctl_card_ge hn hPK
    rcases hF with h5 | h6
    · exfalso
      have hcov : (sec6Piece L b).subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ :=
        covers_of_card_le hPF ((ctl_card_of_dc hn h5.2).le.trans hPcard)
      have htb : t * b = b * t := (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
      exact hcent (mem_QOf_iff.1 (mem_centralizerSection_of_covers htb hFpc hPF hPt hPq hcov)).2
    · refine ⟨h6, hcent, ?_⟩
      rcases h6.2 with ⟨rfl, he⟩ | ⟨rfl, he⟩
      · refine ctl_inner_mcl ht2 htN he hPF hPt (lt_of_lt_of_le ?_ hPcard)
        have h8 : Nat.factorial 8 = 40320 := by norm_num [Nat.factorial]
        omega
      · exact ctl_inner_ly htN he

end Dich

section Piece

variable {X : Type} [Group X] [Finite X]

private theorem ctl_piece_ctrl
    {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n) {b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen b) F) (htN : t ∈ normalizer (F : Set X))
    (hctl : CentModOdd F t ∨ (Sec6MComp X n (cen b) F ∧ ∃ f ∈ F, CentModOdd F (f * t))) :
    ∃ L : Subgroup X, Sec6KComp X n (cen t) L ∧ sec6Piece L b ≤ F := by
  have ht2 : orderOf t = 2 := hS.choice.inv
  have hEK : Sec6KComp X n (cen t ⊓ cen b) (sec6Piece F t) := by
    refine ctl_piece_K ht2 hF (fun h5 => ?_) (fun h6 => ?_)
    · rcases hctl with h | ⟨h6, -⟩
      · exact mem_QOf_iff.2 ⟨htN, h⟩
      · exact absurd rfl (ctl_ne_of_A_M h5 h6)
    · rcases hctl with h | ⟨-, f, hf, hft⟩
      · exact le_sup_right (a := F) (mem_QOf_iff.2 ⟨htN, h⟩)
      · have hftQ : f * t ∈ QOf F :=
          mem_QOf_iff.2 ⟨mul_mem (Subgroup.le_normalizer hf) htN, hft⟩
        have h1 : t = f⁻¹ * (f * t) := by group
        rw [h1]
        exact Subgroup.mul_mem_sup (F.inv_mem hf) hftQ
  obtain ⟨L, hL, hEL⟩ := ctl_lift hS.cex h51.b ht2 inf_le_left hEK
  have hPK := sec6Piece_mem hb hb2 hL
  have hEq := ctl_isTwoGenQuasi hEK
  have hEpc : IsPCompIn 2 (cen b ⊓ cen t) (sec6Piece F t) := by
    rw [inf_comm]
    exact ctl_isPCompIn hEK
  have hEP : sec6Piece F t ≤ sec6Piece L b := by
    have hEb : sec6Piece F t ≤ cen b := (ctl_isPCompIn hEK).1.trans inf_le_right
    have := oTwoPrimeOf_mono (le_inf hEL hEb : sec6Piece F t ≤ L ⊓ cen b)
    rwa [oTwoPrimeOf_eq_self_of_primeResidual hEq.1] at this
  refine ⟨L, hL, ?_⟩
  rw [← eq_of_isPCompIn_of_le hEpc (ctl_isPCompIn hPK) le_rfl hEP hEq]
  exact (oTwoPrimeOf_le _).trans inf_le_left

end Piece

section Step1

variable {X : Type} [Group X] [Finite X]

private theorem ctl_oddCoreOf_le_of_covers {E F : Subgroup X} (hEF : E ≤ F)
    (hcov : E.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤) : oddCoreOf E ≤ oddCoreOf F := by
  have hEFeq : E ⊔ pPrimeCoreOf 2 F = F := (covers_subgroupOf_iff hEF).1 hcov
  set N : Subgroup X := oddCoreOf E ⊔ oddCoreOf F with hN
  have hNodd : Odd (Nat.card N) :=
    ctl_odd_card_sup (fun x hx => le_normalizer_oddCoreOf F (hEF ((oddCoreOf_le E) hx)))
      (odd_card_oddCoreOf E) (odd_card_oddCoreOf F)
  have hNF : N ≤ F := sup_le ((oddCoreOf_le E).trans hEF) (oddCoreOf_le F)
  have hFN : F ≤ normalizer (N : Set X) := by
    refine hEFeq.symm.le.trans (sup_le (fun e he => ?_) (fun o ho => ?_))
    · exact mem_normalizer_sup (le_normalizer_oddCoreOf E he) (le_normalizer_oddCoreOf F (hEF he))
    · exact ctl_mem_normalizer_sup_of_mem (C := F) ((oddCoreOf_le E).trans hEF)
        (le_normalizer_oddCoreOf F) ho
  exact le_sup_left.trans (le_oddCoreOf_of_normalized hNF hFN hNodd)

private theorem ctl_step1 {n : ℕ} {t v : X} (hvt : v ∈ cen t) (hcov : Sec6Covers X n t v) :
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
    ctl_exists_mul_of_mem_sup (H := Kv ⊓ Sec6K X n (cen t)) (N := oddCoreOf Kv)
      (fun x hx => le_normalizer_oddCoreOf Kv (Subgroup.mem_inf.1 hx).1) hk'
  have htO : t ∈ normalizer (oddCoreOf Kv : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htN
  have h1 : ⁅o, t⁆ ∈ oddCoreOf Kv := by
    have h3 : ⁅o, t⁆ = o * (t * o⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (oddCoreOf Kv).mul_mem ho ((mem_normalizer_iff.1 htO o⁻¹).1 ((oddCoreOf Kv).inv_mem ho))
  have hht : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.1 (ctl_K_le n t hh.2)
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

private theorem ctl_S1C
    {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n) {b v : X} (hbt : b ∈ cen t)
    {F : Subgroup X} (hF : Sec6KComp X n (cen b) F) (hv : v ∈ Sec6Q X n (cen t))
    (hv2 : orderOf v = 2) (hcov : Sec6Covers X n t v) (hvb : v ∈ cen b) (hvF : v ∈ QOf F) :
    t ∈ normalizer (F : Set X) ∧ CentModOdd F t := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvt : v ∈ cen t := hv.1
  have htv : t ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvt).symm
  have htb : t ∈ cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]
    exact pow_orderOf_eq_one v
  have hFpc := ctl_isPCompIn hF
  have hFq := ctl_isTwoGenQuasi hF
  have hEK : Sec6KComp X n (cen v ⊓ cen b) (sec6Piece F v) :=
    ctl_piece_K hv2 hF (fun _ => hvF) (fun _ => le_sup_right (a := F) hvF)
  set E : Subgroup X := sec6Piece F v with hE
  have hEpc := ctl_isPCompIn hEK
  have hEq := ctl_isTwoGenQuasi hEK
  have hEF : E ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovE : E.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hv2' hFq.1 hvF
  have hEK1 : E ≤ Sec6K X n (cen v ⊓ cen b) := le_sSup hEK
  have hEK' : E ≤ Sec6K X n (cen v) := hEK1.trans (h51.sub v hv2 _ inf_le_left).1
  obtain ⟨htKN, -, htKc⟩ := ctl_step1 hvt hcov
  set D : Subgroup X := cen v ⊓ cen b with hD
  have htD : t ∈ D := ⟨htv, htb⟩
  have hOD : oddCoreOf (Sec6K X n (cen v)) ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun d hd => mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n v hd.1))
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
  have htE : t ∈ normalizer (E : Set X) := ctl_mem_normalizer_of_map_le hEt
  have hFt := ctl_isPCompIn_conj hFpc (Subgroup.le_normalizer htb)
  have hEFt : E ≤ F.map (MulAut.conj t).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer htE]
    exact Subgroup.map_mono hEF
  have htF : t ∈ normalizer (F : Set X) :=
    mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hFpc hFt hEF hEFt hEq).symm
  refine ⟨htF, ?_⟩
  have htQE : t ∈ QOf E := by
    refine mem_QOf_iff.2 ⟨htE, fun e he => ?_⟩
    have h1 : ⁅e, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htKc e (hEK' he)
    have h2 : ⁅e, t⁆ ∈ E := by
      have h3 : ⁅e, t⁆ = e * (t * e⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact E.mul_mem he ((mem_normalizer_iff.1 htE e⁻¹).1 (E.inv_mem he))
    exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf _ (hEK' hx))
      (odd_card_oddCoreOf _) ⟨h2, h1⟩
  have hE'E : sec6Piece E t ≤ E := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovE' : (sec6Piece E t).subgroupOf E ⊔ pPrimeCore 2 ↥E = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers ht2 hEq.1 htQE
  have hE'q : IsTwoGenQuasi ↥(sec6Piece E t) :=
    isTwoGenQuasi_of_covers hE'E hcovE' (primeResidual_oTwoPrimeOf _) hEq
  have hcovE'F : (sec6Piece E t).subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ := by
    rw [covers_subgroupOf_iff (hE'E.trans hEF)]
    have h1 := (covers_subgroupOf_iff hE'E).1 hcovE'
    have h2 := (covers_subgroupOf_iff hEF).1 hcovE
    have h3 := ctl_oddCoreOf_le_of_covers hEF hcovE
    refine le_antisymm (sup_le (hE'E.trans hEF) (Subgroup.map_subtype_le _)) ?_
    calc F = E ⊔ pPrimeCoreOf 2 F := h2.symm
      _ ≤ sec6Piece E t ⊔ pPrimeCoreOf 2 F :=
          sup_le (h1.symm.le.trans (sup_le le_sup_left (h3.trans le_sup_right))) le_sup_right
  have htb' : t * b = b * t := (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  exact (mem_QOf_iff.1 (mem_centralizerSection_of_covers htb' hFpc (hE'E.trans hEF)
    ((oTwoPrimeOf_le _).trans inf_le_right) hE'q hcovE'F)).2

end Step1

@[expose] def Sec6ActsThrough (X : Type) [Group X] (n : ℕ) (t b : X) : Prop :=
  (∀ L : Subgroup X, Sec5Comp X n (cen t) L → b ∈ QOf L) ∧
    ∀ L : Subgroup X, Sec6MComp X n (cen t) L → b ∈ L ⊔ QOf L

private theorem ctl_actsThrough_of_mem
    {X : Type} [Group X] [Finite X] {n : ℕ} {t b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) : Sec6ActsThrough X n t b :=
  ⟨fun _ h5 => ctl_MQ_le_QOf_A h5 hb, fun _ h6 => ctl_MQ_le_sup_M h6 hb⟩

@[expose] def McLCentAutSq : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* Blueprint.NativeSporadic.McL) →
    ∀ (ψ : MulAut Q) (v : Q), orderOf v = 2 → (∀ x : Q, x * v = v * x → ψ x = x) → ψ * ψ = 1

section Step0

variable {X : Type} [Group X] [Finite X]

private theorem ctl_oddCoreOf_le_K {n : ℕ} {t : X} {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : pPrimeCoreOf 2 L ≤ oddCoreOf (Sec6K X n (cen t)) := by
  have hLpc := ctl_isPCompIn hL
  have hLK : L ≤ Sec6K X n (cen t) := le_sSup hL
  have hKt : Sec6K X n (cen t) ≤ cen t := ctl_K_le n t
  refine pPrimeCoreOf_le_oddCoreOf hLK ?_
  have h1 : L.subgroupOf (Sec6K X n (cen t)) =
      (L.subgroupOf (cen t)).comap (Subgroup.inclusion hKt) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
  rw [h1]
  exact (isPComponent_two_iff.1 hLpc.2).1.comap _

private theorem ctl_mem_QOf_K {n : ℕ} {t c : X} (hct : c ∈ cen t)
    (hc : ∀ L : Subgroup X, Sec6KComp X n (cen t) L → CentModOdd L c) :
    c ∈ QOf (Sec6K X n (cen t)) := by
  set K : Subgroup X := Sec6K X n (cen t) with hK
  have hcN : c ∈ normalizer (K : Set X) := Sec6K_cen_normal n t hct
  have hcO : c ∈ normalizer (oddCoreOf K : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hcN
  let T : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ⁅k, c⁆ ∈ oddCoreOf K}
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, ?_⟩
        have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1]
        exact (oddCoreOf K).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf K haK) _).1 hb)
          ha
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
  have hKT : K ≤ T := sSup_le fun L hL l hl =>
    ⟨le_sSup hL hl, ctl_oddCoreOf_le_K hL (hc L hL l hl)⟩
  exact mem_QOf_iff.2 ⟨hcN, fun k hk => (hKT hk).2⟩

private theorem ctl_s0_norm
    {n : ℕ} {t b y : X}
    (hbA : Sec6ActsThrough X n t b) (hb2 : orderOf b = 2) (hyt : y ∈ cen t)
    (hyb : y ∈ cen b) {L : Subgroup X} (hL : Sec6KComp X n (cen t) L)
    (hy : ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b)) :
    y ∈ normalizer (sec6Piece L b : Set X) ∧ y ∈ normalizer (L : Set X) := by
  have hPK := ctl_piece_K hb2 hL (hbA.1 L) (hbA.2 L)
  have hPpc := ctl_isPCompIn hPK
  have hPq := ctl_isTwoGenQuasi hPK
  set P : Subgroup X := sec6Piece L b with hP
  set D : Subgroup X := cen b ⊓ cen t with hD
  have hyD : y ∈ D := ⟨hyb, hyt⟩
  have hOD : oddCoreOf (cen b) ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun d hd => mem_normalizer_inf (le_normalizer_oddCoreOf (cen b) hd.1)
        (Subgroup.le_normalizer hd))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hPy : P.map (MulAut.conj y).toMonoidHom ≤ P := by
    refine le_of_le_sup_pPrimeCoreOf hPpc ?_ ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact D.mul_mem (D.mul_mem hyD (hPpc.1 hp)) (D.inv_mem hyD)
    · exact primeResidual_eq_top_of_equiv 2 (P.equivMapOfInjective _ (MulAut.conj y).injective)
        hPq.1
    · rintro _ ⟨p, hp, rfl⟩
      have h1 : ⁅p⁻¹, y⁆ ∈ oddCoreOf (cen b) := hy _ (P.inv_mem hp)
      have h1D : ⁅p⁻¹, y⁆ ∈ D := by
        rw [commutatorElement_def, inv_inv]
        exact D.mul_mem (D.mul_mem (D.mul_mem (D.inv_mem (hPpc.1 hp)) hyD) (hPpc.1 hp))
          (D.inv_mem hyD)
      have h2 : (MulAut.conj y).toMonoidHom p = p * ⁅p⁻¹, y⁆ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [h2]
      exact Subgroup.mul_mem_sup hp (hOD ⟨h1, h1D⟩)
  have hyP : y ∈ normalizer (P : Set X) := ctl_mem_normalizer_of_map_le hPy
  refine ⟨hyP, ?_⟩
  have hLpc := ctl_isPCompIn hL
  have hLy := ctl_isPCompIn_conj hLpc (Subgroup.le_normalizer hyt)
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPLy : P ≤ L.map (MulAut.conj y).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer hyP]
    exact Subgroup.map_mono hPL
  exact mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hLpc hLy hPL hPLy hPq).symm

private theorem ctl_comm_mul (p o y : X) : ⁅p * o, y⁆ = p * ⁅o, y⁆ * p⁻¹ * ⁅p, y⁆ := by
  simp only [commutatorElement_def]
  group

private theorem ctl_s0_cov {t b y : X} {L : Subgroup X} (hb2 : b ^ 2 = 1)
    (hLq : IsTwoGenQuasi ↥L) (hLt : L ≤ cen t) (hbL : b ∈ QOf L) (hyt : y ∈ cen t)
    (hyN : y ∈ normalizer (L : Set X))
    (hy : ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b)) : y ∈ QOf L := by
  set P : Subgroup X := sec6Piece L b with hP
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPb : P ≤ cen b := (oTwoPrimeOf_le _).trans inf_le_right
  have hcov : P.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hb2 hLq.1 hbL
  have hLeq : P ⊔ pPrimeCoreOf 2 L = L := (covers_subgroupOf_iff hPL).1 hcov
  set R : Subgroup X := L ⊓ (oddCoreOf (cen b) ⊓ cen t) with hR
  have hRodd : Odd (Nat.card R) :=
    (odd_card_oddCoreOf (cen b)).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_right.trans inf_le_left))
  have hRO : R ≤ oddCoreOf L := by
    set N' : Subgroup X := R ⊔ oddCoreOf L with hN'
    have hN'odd : Odd (Nat.card N') :=
      ctl_odd_card_sup (fun x hx => le_normalizer_oddCoreOf L hx.1) hRodd (odd_card_oddCoreOf L)
    have hN'L : N' ≤ L := sup_le inf_le_left (oddCoreOf_le L)
    have hLN' : L ≤ normalizer (N' : Set X) := by
      refine hLeq.symm.le.trans (sup_le (fun p hp => ?_) (fun o ho => ?_))
      · refine mem_normalizer_sup (mem_normalizer_inf (Subgroup.le_normalizer (hPL hp))
          (mem_normalizer_inf (le_normalizer_oddCoreOf (cen b) (hPb hp))
            (Subgroup.le_normalizer (hLt (hPL hp))))) (le_normalizer_oddCoreOf L (hPL hp))
      · exact ctl_mem_normalizer_sup_of_mem (C := L) inf_le_left (le_normalizer_oddCoreOf L) ho
    exact le_sup_left.trans (le_oddCoreOf_of_normalized hN'L hLN' hN'odd)
  have hcomm : ∀ p ∈ P, ⁅p, y⁆ ∈ oddCoreOf L := by
    intro p hp
    have h1 : ⁅p, y⁆ ∈ L := by
      have h3 : ⁅p, y⁆ = p * (y * p⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact L.mul_mem (hPL hp) ((mem_normalizer_iff.1 hyN p⁻¹).1 (L.inv_mem (hPL hp)))
    have h2 : ⁅p, y⁆ ∈ cen t := by
      rw [commutatorElement_def]
      exact (cen t).mul_mem ((cen t).mul_mem ((cen t).mul_mem (hLt (hPL hp)) hyt)
        ((cen t).inv_mem (hLt (hPL hp)))) ((cen t).inv_mem hyt)
    exact hRO ⟨h1, hy p hp, h2⟩
  have hyO : y ∈ normalizer (oddCoreOf L : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hyN
  refine mem_QOf_iff.2 ⟨hyN, fun l hl => ?_⟩
  have hl' : l ∈ P ⊔ oddCoreOf L := hLeq.symm ▸ hl
  obtain ⟨p, hp, o, ho, rfl⟩ :=
    ctl_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf L (hPL hx)) hl'
  rw [ctl_comm_mul]
  have h1 : ⁅o, y⁆ ∈ oddCoreOf L := by
    have h3 : ⁅o, y⁆ = o * (y * o⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (oddCoreOf L).mul_mem ho ((mem_normalizer_iff.1 hyO o⁻¹).1 ((oddCoreOf L).inv_mem ho))
  exact (oddCoreOf L).mul_mem
    ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf L (hPL hp)) _).1 h1) (hcomm p hp)

private theorem ctl_s0_inner
    (hM : McLCentAutSq) {n : ℕ} {t b y : X} (hb2 : orderOf b = 2) (hyt : y ∈ cen t)
    {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) (hbL : b ∈ L ⊔ QOf L) (hbQ : b ∉ QOf L)
    (hyN : y ∈ normalizer (L : Set X))
    (hy : ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b)) : y ^ 2 ∈ QOf L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP5 : Sec5Comp X n (cen b ⊓ cen t) (sec6Piece L b) := ctl_piece_M_inner hb2 hL hbL hbQ
  obtain ⟨⟨hLpc, htype, -⟩, hT⟩ := hL
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := mcLLyCenterFree _ htype
  have hb2' : b ^ 2 = 1 := by
    rw [← hb2]
    exact pow_orderOf_eq_one b
  obtain ⟨v, ⟨hvL, hvb⟩, hv, hvq⟩ := ctl_exists_inv_inner hZ hb2' hbL hbQ
  set P : Subgroup X := sec6Piece L b with hP
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPb : P ≤ cen b := (oTwoPrimeOf_le _).trans inf_le_right
  have hLt : L ≤ cen t := hLpc.1
  set π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set v' : ↥L := ⟨v, hvL⟩ with hv'
  set C : Subgroup (↥L ⧸ pPrimeCore 2 ↥L) := centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))
    with hC
  have hCdc : IsDoubleCoverOfAlt ↥C n := ctl_cent_dc hT (ctl_orderOf_mk hvL hv)
  have hn : 2 ≤ n := ctl_two_le hT
  have hCcard : Nat.card C = n.factorial := ctl_card_of_dc hn hCdc
  have hbN : b ∈ normalizer (L : Set X) := ctl_sup_QOf_le_normalizer L hbL
  have hbO : b ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hbN
  have hcb : b⁻¹ * v ∈ QOf L := by
    have h1 : b⁻¹ * v = (v⁻¹ * b)⁻¹ := by group
    rw [h1]
    exact (QOf L).inv_mem hvq
  have himg : ∀ (x : X) (hx : x ∈ L), x ∈ cen b → π ⟨x, hx⟩ ∈ C := by
    intro x hx hxb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅x, v⁆ ∈ pPrimeCoreOf 2 L :=
      ctl_comm_mem hx hcb (Subgroup.mem_centralizer_singleton_iff.1 hxb) hbO
    obtain ⟨w, hw, hwe⟩ := h1
    have hw' : w = ⁅(⟨x, hx⟩ : ↥L), v'⁆ := Subtype.ext hwe
    have h2 : π ⁅(⟨x, hx⟩ : ↥L), v'⁆ = 1 := by
      rw [← hw']
      exact (QuotientGroup.eq_one_iff w).2 hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  set f : ↥P →* ↥L ⧸ pPrimeCore 2 ↥L := π.comp (Subgroup.inclusion hPL) with hf
  have hfC : f.range ≤ C := by
    rintro _ ⟨p, rfl⟩
    exact himg p (hPL p.2) (hPb p.2)
  have hPcard : n.factorial ≤ Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := (ctl_card_of_dc hn hP5.2).ge
  have hfr : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) ≤ Nat.card f.range := ctl_card_quot_le_range hPL
  have hfeq : f.range = C := Subgroup.eq_of_le_of_card_ge hfC (by omega)
  set R : Subgroup X := L ⊓ (oddCoreOf (cen b) ⊓ cen t) with hR
  have hRodd : Odd (Nat.card R) :=
    (odd_card_oddCoreOf (cen b)).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_right.trans inf_le_left))
  set Rb : Subgroup (↥L ⧸ pPrimeCore 2 ↥L) := (R.subgroupOf L).map π with hRb
  have hRbC : Rb ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    exact himg r r.2 (oddCoreOf_le _ (Subgroup.mem_subgroupOf.1 hr).2.1)
  have hRbodd : Odd (Nat.card Rb) := by
    refine hRodd.of_dvd_nat (((R.subgroupOf L).card_map_dvd π).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : R ≤ L)).toEquiv]
  have hCRb : C ≤ normalizer (Rb : Set (↥L ⧸ pPrimeCore 2 ↥L)) := by
    rw [← hfeq]
    rintro _ ⟨p, rfl⟩
    apply ctl_mem_normalizer_of_map_le
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hrR : (r : X) ∈ R := Subgroup.mem_subgroupOf.1 hr
    have hpR : (p : X) * r * (p : X)⁻¹ ∈ R := by
      have hpN : (p : X) ∈ normalizer (R : Set X) :=
        mem_normalizer_inf (Subgroup.le_normalizer (hPL p.2))
          (mem_normalizer_inf (le_normalizer_oddCoreOf (cen b) (hPb p.2))
            (Subgroup.le_normalizer (hLt (hPL p.2))))
      exact (mem_normalizer_iff.1 hpN r).1 hrR
    refine ⟨⟨(p : X) * r * (p : X)⁻¹, hpR.1⟩, hpR, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hf, MonoidHom.coe_comp,
      Function.comp_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  have hRbbot : Rb = ⊥ := by
    have h1 := le_oddCoreOf_of_normalized hRbC hCRb hRbodd
    have h2 : pPrimeCore 2 ↥C = ⊥ := pPrimeCore_eq_bot_of_doubleCover hCdc
    have h3 : oddCoreOf C = ⊥ := by
      rw [oddCoreOf, h2, Subgroup.map_bot]
    rwa [h3, le_bot_iff] at h1
  have hRO : ∀ r ∈ R, r ∈ pPrimeCoreOf 2 L := by
    intro r hr
    have h1 : π ⟨r, hr.1⟩ ∈ Rb := ⟨⟨r, hr.1⟩, hr, rfl⟩
    rw [hRbbot, Subgroup.mem_bot] at h1
    exact ⟨⟨r, hr.1⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  set ψ : MulAut (↥L ⧸ pPrimeCore 2 ↥L) := quotConj hyN with hψ
  have hfix : ∀ x, x * π v' = π v' * x → ψ x = x := by
    intro x hx
    have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hx
    rw [← hfeq] at hxC
    obtain ⟨p, rfl⟩ := hxC
    have hpL : (p : X) ∈ L := hPL p.2
    have h1 : ⁅(p : X)⁻¹, y⁆ ∈ R := by
      have hc : ⁅(p : X)⁻¹, y⁆ = (p : X)⁻¹ * (y * p * y⁻¹) := by
        rw [commutatorElement_def, inv_inv]
        group
      refine ⟨?_, hy _ (P.inv_mem p.2), ?_⟩
      · rw [hc]
        exact L.mul_mem (L.inv_mem hpL) ((mem_normalizer_iff.1 hyN _).1 hpL)
      · rw [commutatorElement_def, inv_inv]
        exact (cen t).mul_mem ((cen t).mul_mem ((cen t).mul_mem
          ((cen t).inv_mem (hLt hpL)) hyt) (hLt hpL)) ((cen t).inv_mem hyt)
    obtain ⟨w, hw, hwe⟩ := hRO _ h1
    have hgoal : (Subgroup.inclusion hPL p)⁻¹ * conjAut hyN (Subgroup.inclusion hPL p) ∈
        pPrimeCore 2 ↥L := by
      have h2 : (Subgroup.inclusion hPL p)⁻¹ * conjAut hyN (Subgroup.inclusion hPL p) = w := by
        apply Subtype.ext
        rw [show (w : X) = ⁅(p : X)⁻¹, y⁆ from hwe]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, Subgroup.coe_inclusion,
          commutatorElement_def]
        group
      rw [h2]
      exact hw
    show quotConj hyN (QuotientGroup.mk (Subgroup.inclusion hPL p)) =
      QuotientGroup.mk (Subgroup.inclusion hPL p)
    rw [ctl_quotConj_mk]
    exact (QuotientGroup.eq.2 hgoal).symm
  have hψ2 : ψ * ψ = 1 := by
    rcases hT with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · exact hM _ he ψ (π v') (ctl_orderOf_mk hvL hv) hfix
    · obtain ⟨g, hg⟩ :=
        GH74.GLS.Stage2.Bender.Thm1.LyOut.lyAllInner_thm (↥L ⧸ pPrimeCore 2 ↥L) he ψ
      have hgC : ∀ x ∈ C, g * x = x * g := by
        intro x hxC
        have h1 := hfix x (Subgroup.mem_centralizer_singleton_iff.1 hxC)
        rw [hg, MulAut.conj_apply] at h1
        calc g * x = g * x * g⁻¹ * g := by group
          _ = x * g := by rw [h1]
      have hgmem : g ∈ C := Subgroup.mem_centralizer_singleton_iff.2
          (hgC _ (Subgroup.mem_centralizer_singleton_iff.2 rfl))
      have hgZ : (⟨g, hgmem⟩ : ↥C) ∈ center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact Subtype.ext (hgC x x.2).symm
      have hg2 : g * g = 1 := by
        have h1 := orderOf_dvd_natCard (⟨⟨g, hgmem⟩, hgZ⟩ : ↥(center ↥C))
        rw [hCdc.2.1] at h1
        have h2 : (⟨⟨g, hgmem⟩, hgZ⟩ : ↥(center ↥C)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
        have h3 := congrArg (fun z : ↥(center ↥C) => ((z : ↥C) : ↥L ⧸ pPrimeCore 2 ↥L)) h2
        simpa [pow_two] using h3
      rw [hg, ← map_mul, hg2, map_one]
  refine mem_QOf_iff.2 ⟨pow_mem hyN 2, fun a ha => ?_⟩
  have h1 := congrArg (fun φ : MulAut (↥L ⧸ pPrimeCore 2 ↥L) => φ (π ⟨a⁻¹, L.inv_mem ha⟩)) hψ2
  simp only [MulAut.mul_apply, MulAut.one_apply] at h1
  rw [hψ, hπ, QuotientGroup.mk'_apply, ctl_quotConj_mk, ctl_quotConj_mk] at h1
  have h2 : ((⟨a⁻¹, L.inv_mem ha⟩ : ↥L)⁻¹ *
      conjAut hyN (conjAut hyN ⟨a⁻¹, L.inv_mem ha⟩)) ∈ pPrimeCore 2 ↥L :=
    QuotientGroup.eq.1 h1.symm
  have h3 : ⁅a, y ^ 2⁆ = (((⟨a⁻¹, L.inv_mem ha⟩ : ↥L)⁻¹ *
      conjAut hyN (conjAut hyN ⟨a⁻¹, L.inv_mem ha⟩) : ↥L) : X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, commutatorElement_def,
      Subgroup.coe_mk, pow_two]
    group
  rw [h3]
  exact ⟨_, h2, rfl⟩

private theorem ctl_step0
    (hM : McLCentAutSq) {n : ℕ} {t b : X}
    (hbA : Sec6ActsThrough X n t b) (hb2 : orderOf b = 2) {y : X}
    (hyt : y ∈ cen t) (hyb : y ∈ cen b)
    (hy : ∀ L : Subgroup X, Sec6KComp X n (cen t) L →
      ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b)) :
    y ^ 2 ∈ Sec6Q X n (cen t) := by
  refine ⟨pow_mem hyt 2, ctl_mem_QOf_K (pow_mem hyt 2) fun L hL => ?_⟩
  have hyN := (ctl_s0_norm hbA hb2 hyt hyb hL (hy L hL)).2
  have hb2' : b ^ 2 = 1 := by
    rw [← hb2]
    exact pow_orderOf_eq_one b
  by_cases hbQ : b ∈ QOf L
  · have hyQ := ctl_s0_cov hb2' (ctl_isTwoGenQuasi hL) (ctl_isPCompIn hL).1 hbQ hyt hyN (hy L hL)
    exact (mem_QOf_iff.1 (pow_mem hyQ 2)).2
  · rcases hL with h5 | h6
    · exact absurd (hbA.1 L h5) hbQ
    · exact (mem_QOf_iff.1 (ctl_s0_inner hM hb2 hyt h6 (hbA.2 L h6) hbQ hyN
        (hy L (Or.inr h6)))).2

end Step0

section CaseA

variable {X : Type} [Group X] [Finite X]

private theorem ctl_induces_one_eq {n : ℕ} {K : Type} [Group K] {C : AhatData.CoverSetup n K}
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

private theorem ctl_sqrt_center {n : ℕ} (hn : 8 ≤ n) {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
    (htN : t ∈ normalizer (F : Set X)) (hFn : IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n)
    (hcent : ¬ CentModOdd F t) :
    ∃ f ∈ F ⊓ cen t, f ^ (2 ^ 2) = 1 ∧ f ^ 2 ∉ pPrimeCoreOf 2 F ∧
      ∀ a ∈ F, ⁅a, f ^ 2⁆ ∈ pPrimeCoreOf 2 F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : AhatData.CoverSetup n (↥F ⧸ pPrimeCore 2 ↥F) := AhatData.CoverSetup.ofCover hFn with hC
  set α : MulAut (↥F ⧸ pPrimeCore 2 ↥F) := quotConj htN with hα
  obtain ⟨σ, hσ⟩ := exists_induces_perm (by omega) (by omega) C α
  have hα2 : α * α = 1 := MulEquiv.ext fun y => ctl_quotConj_sq ht2 htN y
  have hσ2 : σ * σ = 1 := by
    have h1 := hσ.mul' hσ
    rw [hα2] at h1
    exact induces_unique (by omega) h1 C.induces_one'
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hcent
    have h1 := ctl_induces_one_eq hσ
    intro a ha
    have h2 : α (QuotientGroup.mk ⟨a⁻¹, F.inv_mem ha⟩) = QuotientGroup.mk ⟨a⁻¹, F.inv_mem ha⟩ := by
      rw [h1]
      rfl
    rw [hα, ctl_quotConj_mk] at h2
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
    rw [hα, ctl_quotConj_mk] at h1
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

private theorem ctl_cent_of_eq {b t : X} {F P : Subgroup X} (hbt : b ∈ cen t)
    (hF : IsPCompIn 2 (cen b) F) (hPF : P ≤ F) (hPt : P ≤ cen t) (hPq : IsTwoGenQuasi ↥P)
    (heq : F = oddCoreOf F ⊔ P) : CentModOdd F t := by
  have hcov : P.subgroupOf F ⊔ pPrimeCore 2 ↥F = ⊤ := by
    rw [covers_subgroupOf_iff hPF, sup_comm]
    exact heq.symm
  have htb : t * b = b * t := (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  exact (mem_QOf_iff.1 (mem_centralizerSection_of_covers htb hF hPF hPt hPq hcov)).2

private theorem ctl_comm_pieces
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (h51 : Sec6Lemma51 X n) {b : X} (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t))
    (hb2 : orderOf b = 2) {F : Subgroup X} (hF : Sec6KComp X n (cen b) F)
    (hcent : ¬ CentModOdd F t)
    (hno : ¬ (Sec6MComp X n (cen b) F ∧ ∃ f ∈ F, CentModOdd F (f * t))) :
    ∀ f ∈ F, ∀ L : Subgroup X, Sec6KComp X n (cen t) L →
      ∀ p ∈ sec6Piece L b, ⁅p, f⁆ ∈ oddCoreOf (cen b) := by
  have hbt := ctl_MQ_le_cen n t hb
  have hFpc := ctl_isPCompIn hF
  intro f hf L hL p hp
  obtain ⟨J, hJ, hPJ⟩ := sec6Ctrl_land hS h51 hb hb2 hL
  have hne : J ≠ F := by
    rintro rfl
    rcases (sec6Ctrl_dich hS hb hb2 hL hJ hPJ).2 with heq | ⟨h6, -, hin⟩
    · have hPK := sec6Piece_mem hb hb2 hL
      exact hcent (ctl_cent_of_eq hbt hFpc hPJ ((ctl_isPCompIn hPK).1.trans inf_le_right)
        (ctl_isTwoGenQuasi hPK) heq)
    · exact hno ⟨h6, hin⟩
  have hJpc := ctl_isPCompIn hJ
  exact pPrimeCoreOf_le_oddCoreOf hJpc.1 (isPComponent_two_iff.1 hJpc.2).1
    (ctl_commutatorElement_mem hJpc hFpc hne (hPJ hp) hf)

private theorem ctl_caseA
    (hM : McLCentAutSq) {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2) {F : Subgroup X}
    (hF : Sec5Comp X n (cen b) F) (htN : t ∈ normalizer (F : Set X)) : CentModOdd F t := by
  by_contra hcent
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbt := ctl_MQ_le_cen n t hb
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hFK : Sec6KComp X n (cen b) F := Or.inl hF
  have hFpc := ctl_isPCompIn hFK
  have hcomm := ctl_comm_pieces hS h51 hb hb2 hFK hcent
    (fun h => ctl_ne_of_A_M hF h.1 rfl)
  obtain ⟨f, ⟨hfF, hft⟩, hf4, hfO, hfz⟩ := ctl_sqrt_center hS.maxdeg.1 ht2 htN hF.2 hcent
  have hfb : f ∈ cen b := hFpc.1 hfF
  have hv : f ^ 2 ∈ Sec6Q X n (cen t) :=
    ctl_step0 hM (ctl_actsThrough_of_mem hb) hb2 hft hfb fun L hL p hp => hcomm f hfF L hL p hp
  have hv2 : orderOf (f ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul]
      exact hf4
    · intro h1
      exact hfO (h1 ▸ one_mem _)
  have hvF : f ^ 2 ∈ QOf F :=
    mem_QOf_iff.2 ⟨Subgroup.le_normalizer (F.pow_mem hfF 2), fun a ha => hfz a ha⟩
  exact hcent (ctl_S1C hS h51 hbt hFK hv hv2 (h61a _ hv hv2) (hFpc.1 (F.pow_mem hfF 2)) hvF).2

end CaseA

section CaseB

variable {X : Type} [Group X] [Finite X]

private theorem ctl_lift_fixed {F : Subgroup X} {t : X} (ht2 : t ^ 2 = 1)
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
    rw [ctl_quotConj_mk] at h1
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

private theorem ctl_fixed_M11
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
    (ctl_mem_fixedSubgroup _ y).trans ((ctl_fixed_iff e α σ hσapp y).trans
      (ctl_mem_mclFixed σ (e y)).symm)
  refine ⟨MulEquiv.trans (MulEquiv.mk' (e.toEquiv.subtypeEquiv hiff) fun x y => ?_) eM⟩
  apply Subtype.ext
  simp only [Equiv.subtypeEquiv_apply, MulEquiv.coe_toEquiv, Subgroup.coe_mul]
  exact map_mul e _ _

private theorem ctl_step1_comp {n : ℕ} {t v : X} (htv : t ∈ cen v)
    (htK : t ∈ QOf (Sec6K X n (cen v))) {J : Subgroup X} (hJ : IsPCompIn 2 (cen v) J)
    (hJK : J ≤ Sec6K X n (cen v)) : t ∈ QOf J := by
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJ.1).1 (isPComponent_two_iff.1 hJ.2).2
  have hOK : oddCoreOf (Sec6K X n (cen v)) ≤ oddCoreOf (cen v) :=
    ctl_oddCoreOf_le_of_normal (ctl_K_le n v) (Sec6K_cen_normal n v)
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
  have htJ : t ∈ normalizer (J : Set X) := ctl_mem_normalizer_of_map_le hJt
  refine mem_QOf_iff.2 ⟨htJ, fun j hj => ?_⟩
  have h1 : ⁅j, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := htc j (hJK hj)
  have h2 : ⁅j, t⁆ ∈ J := by
    have h3 : ⁅j, t⁆ = j * (t * j⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact J.mul_mem hj ((mem_normalizer_iff.1 htJ j⁻¹).1 (J.inv_mem hj))
  exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf _ (hJK hx))
    (odd_card_oddCoreOf _) ⟨h2, h1⟩

private theorem ctl_caseB_core
    {n : ℕ} {M J : Subgroup X}
    {v t : X} (hT : IsSec6MType n (↥M ⧸ pPrimeCore 2 ↥M)) (hvM : v ∈ M) (hv : orderOf v = 2)
    (htv : t ∈ cen v) (htN : t ∈ normalizer (M : Set X)) (hJ : IsAhatIntr X v J)
    (hJcov : J ≤ (M ⊓ cen v) ⊔ oddCoreOf (cen v)) (htJ : t ∈ QOf J) :
    ∀ x : ↥M ⧸ pPrimeCore 2 ↥M, x * QuotientGroup.mk ⟨v, hvM⟩ = QuotientGroup.mk ⟨v, hvM⟩ * x →
      quotConj htN x = x := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := oTwoPrimeOf (M ⊓ cen v) with hR
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := ctl_degree hT hvM hv hJ hJcov
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
    ctl_card_quot_le_of_cen hT hvM hv hRM' hRv
  have hJcard : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = n.factorial :=
    ctl_card_of_dc (ctl_two_le hT) hJn
  have hJcovZ : J.subgroupOf Z ⊔ pPrimeCore 2 ↥Z = ⊤ :=
    covers_of_card_le hJZ (hZR.trans (hRn.trans hJcard.ge))
  have htR : t ∈ normalizer (R : Set X) :=
    ctl_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf htN (Subgroup.le_normalizer htv))
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
      ctl_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf Z (hJZ hx)) hz'
    rw [ctl_comm_mul]
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
    exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf Z (hRZ hx))
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
  have hRr : Nat.card (↥R ⧸ pPrimeCore 2 ↥R) ≤ Nat.card fR.range := ctl_card_quot_le_range hRM'
  have hCcard : Nat.card C = n.factorial :=
    ctl_card_of_dc (ctl_two_le hT) (ctl_cent_dc hT (ctl_orderOf_mk hvM hv))
  have hfReq : fR.range = C := Subgroup.eq_of_le_of_card_ge hfRC (by omega)
  have hker : fR.ker ≤ pPrimeCore 2 ↥R := by
    intro w hw
    have h1 : Subgroup.inclusion hRM' w ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 hw
    have h2 : (w : X) ∈ R ⊓ pPrimeCoreOf 2 M := ⟨w.2, ⟨_, h1, rfl⟩⟩
    obtain ⟨w', hw', hww'⟩ := ctl_inf_le_oddCoreOf
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
  rw [ctl_quotConj_mk, QuotientGroup.eq]
  have h1 : (conjAut htN (Subgroup.inclusion hRM' r))⁻¹ * Subgroup.inclusion hRM' r =
      (Subgroup.inclusion hRM' r)⁻¹ * Subgroup.inclusion hRM' w' *
        (Subgroup.inclusion hRM' r)⁻¹⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, Subgroup.coe_inclusion, inv_inv]
    rw [show (w' : X) = ⁅(r : X), t⁆ from hw'e, commutatorElement_def]
    group
  rw [h1]
  exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem _ hw'ker _

private theorem ctl_M11_ord4 :
    ∃ g ∈ Blueprint.NativeSporadic.M11, orderOf g = 4 := by
  refine ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (by simp), ?_⟩
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

private theorem ctl_caseB
    (hM : McLCentAutSq) {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) {b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2) {F : Subgroup X}
    (hF : Sec6MComp X n (cen b) F) (htN : t ∈ normalizer (F : Set X)) :
    ∃ f ∈ F, CentModOdd F (f * t) := by
  by_contra hinner
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hcent : ¬ CentModOdd F t := fun h => hinner ⟨1, F.one_mem, by rwa [one_mul]⟩
  have hFK : Sec6KComp X n (cen b) F := Or.inr hF
  have hFpc := ctl_isPCompIn hFK
  have hcomm := ctl_comm_pieces hS h51 hb hb2 hFK hcent (fun h => hinner h.2)
  rcases hF.2 with ⟨hn8, he⟩ | ⟨-, he⟩
  swap
  · exact hinner (ctl_inner_ly htN he)
  obtain ⟨e⟩ := he
  set α : MulAut (↥F ⧸ pPrimeCore 2 ↥F) := quotConj htN with hα
  have hα2 : α * α = 1 := MulEquiv.ext fun y => ctl_quotConj_sq ht2 htN y
  have hout : ¬ ∃ g, α = MulAut.conj g := fun ⟨g, hg⟩ => hinner (ctl_inner_of_conj htN hg)
  obtain ⟨Φ⟩ := ctl_fixed_M11 e α hα2 hout
  obtain ⟨g0, hg0, hg0ord⟩ := ctl_M11_ord4
  set xs : ↥(CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α) := Φ.symm ⟨g0, hg0⟩ with hxs
  have hxfix : α (xs : ↥F ⧸ pPrimeCore 2 ↥F) = xs := (ctl_mem_fixedSubgroup α _).1 xs.2
  have hxord : orderOf (xs : ↥F ⧸ pPrimeCore 2 ↥F) = 4 := by
    rw [Subgroup.orderOf_coe, hxs, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hg0ord]
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (xs : ↥F ⧸ pPrimeCore 2 ↥F)
  have hfixa : quotConj htN (QuotientGroup.mk a) = QuotientGroup.mk a := by
    rw [ha]
    exact hxfix
  have h4 : (QuotientGroup.mk a : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ 2) = 1 := by
    rw [ha, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hxord]
    exact pow_orderOf_eq_one _
  obtain ⟨f, ⟨hfF, hft⟩, hf4, hfF', hfa⟩ := ctl_lift_fixed ht2 htN a hfixa h4
  have hfb : f ∈ cen b := hFpc.1 hfF
  have hvQ : f ^ 2 ∈ Sec6Q X n (cen t) :=
    ctl_step0 hM (ctl_actsThrough_of_mem hb) hb2 hft hfb fun L hL p hp => hcomm f hfF L hL p hp
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
  have htK := ctl_step1 hvQ.1 (h61a _ hvQ hv2)
  obtain ⟨J, hJ, hJcov⟩ := hF.1.2.2 (f ^ 2) hvF hv2
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := ctl_degree hF.2 hvF hv2 hJ hJcov
  have hJK : J ≤ Sec6K X n (cen (f ^ 2)) :=
    le_sSup (Or.inl ⟨⟨f ^ 2, hJ.isIntrinsicIn hv2⟩, hJn⟩)
  have htJ : t ∈ QOf J := ctl_step1_comp htv htK ⟨hJ.1, hJ.2.2.1⟩ hJK
  have hcore := ctl_caseB_core hF.2 hvF hv2 htv htN hJ hJcov htJ
  have hle : centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥F) ⟨f ^ 2, hvF⟩} :
      Set (↥F ⧸ pPrimeCore 2 ↥F)) ≤
      CFSG.Sporadic.Recognition.McLAS.fixedSubgroup α := fun x hx =>
    (ctl_mem_fixedSubgroup α x).2 (hcore x (Subgroup.mem_centralizer_singleton_iff.1 hx))
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_congr Φ.toEquiv, CFSG.Sporadic.Mathieu.card_M11,
    ctl_card_of_dc (ctl_two_le hF.2) (ctl_cent_dc hF.2 (ctl_orderOf_mk hvF hv2)), hn8] at h1
  norm_num [Nat.factorial] at h1

end CaseB

@[expose] def Sec6CtrlCaseC (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ F : Subgroup X, Sec6KComp X n (cen b) F → t ∈ normalizer (F : Set X)

section CaseC

variable {X : Type} [Group X] [Finite X]

private theorem ctl_dc_sqrt_center {K : Type} [Group K] {n : ℕ} (hn : 8 ≤ n)
    (hK : IsDoubleCoverOfAlt K n) : ∃ k : K, k * k ≠ 1 ∧ k * k ∈ center K := by
  set C : AhatData.CoverSetup n K := AhatData.CoverSetup.ofCover hK with hC
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  set d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have had : a ≠ d := by simp [a, d, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hbd : b ≠ d := by simp [b, d, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hsign : Equiv.Perm.sign (Equiv.swap a b * Equiv.swap c d) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
    decide
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
  exact ⟨x, C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hx,
    C.sq_mem_center (by rw [hx]; exact dbl_mul_self hab hac had hbc hbd hcd)⟩

private theorem ctl_KComp_conj {n : ℕ} {H F : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) (hF : Sec6KComp X n H F) :
    Sec6KComp X n H (F.map (MulAut.conj g).toMonoidHom) := by
  have hH := map_conj_eq_of_mem_normalizer hg
  rcases hF with ⟨⟨u, hu⟩, hdc⟩ | h6
  · left
    refine ⟨⟨_, hH ▸ hu.map_mulEquiv (MulAut.conj g)⟩, ?_⟩
    let ψ : ↥F ≃* ↥(F.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective F _ (MulAut.conj g).injective
    exact isDoubleCoverOfAlt_congr' (QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)) hdc
  · right
    have := h6.map_mulEquiv (MulAut.conj g)
    rwa [hH] at this

private theorem ctl_S1N {n : ℕ} {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    {b v : X} (hbt : b ∈ cen t) {F : Subgroup X} (hF : Sec6KComp X n (cen b) F)
    (hv : v ∈ Sec6Q X n (cen t)) (hv2 : orderOf v = 2) (hcov : Sec6Covers X n t v)
    (hEK : Sec6KComp X n (cen v ⊓ cen b) (sec6Piece F v)) : t ∈ normalizer (F : Set X) := by
  have hvt : v ∈ cen t := hv.1
  have htv : t ∈ cen v :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvt).symm
  have htb : t ∈ cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  have hFpc := ctl_isPCompIn hF
  set E : Subgroup X := sec6Piece F v with hE
  have hEpc := ctl_isPCompIn hEK
  have hEq := ctl_isTwoGenQuasi hEK
  have hEF : E ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hEK1 : E ≤ Sec6K X n (cen v ⊓ cen b) := le_sSup hEK
  have hEK' : E ≤ Sec6K X n (cen v) := hEK1.trans (h51.sub v hv2 _ inf_le_left).1
  obtain ⟨-, -, htKc⟩ := ctl_step1 hvt hcov
  set D : Subgroup X := cen v ⊓ cen b with hD
  have htD : t ∈ D := ⟨htv, htb⟩
  have hOD : oddCoreOf (Sec6K X n (cen v)) ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun d hd => mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n v hd.1))
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
  have htE : t ∈ normalizer (E : Set X) := ctl_mem_normalizer_of_map_le hEt
  have hFt := ctl_isPCompIn_conj hFpc (Subgroup.le_normalizer htb)
  have hEFt : E ≤ F.map (MulAut.conj t).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer htE]
    exact Subgroup.map_mono hEF
  exact mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hFpc hFt hEF hEFt hEq).symm

private theorem ctl_lift_ord4 {F : Subgroup X} {k : ↥F ⧸ pPrimeCore 2 ↥F} (hk2 : k * k ≠ 1)
    (hk4 : k * k * (k * k) = 1) :
    ∃ x ∈ F, x ^ (2 ^ 2) = 1 ∧ ∃ hxF : x ∈ F,
      (QuotientGroup.mk (⟨x, hxF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = k := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective k
  have ha4 : (a : X) ^ (2 ^ 2) ∈ pPrimeCoreOf 2 F := by
    have h1 : (QuotientGroup.mk (a ^ (2 ^ 2)) : ↥F ⧸ pPrimeCore 2 ↥F) = 1 := by
      rw [QuotientGroup.mk_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, pow_succ, pow_succ, pow_succ,
        pow_one]
      simpa [mul_assoc] using hk4
    rw [QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 F)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf F)
  obtain ⟨m, hm4, ham⟩ := exists_zpow_twoElt_of_pow_mem hOcop ha4
  refine ⟨(a : X) ^ m, F.zpow_mem a.2 m, hm4, F.zpow_mem a.2 m, ?_⟩
  rw [QuotientGroup.eq]
  obtain ⟨w, hw, hwe⟩ := ham
  have : (⟨(a : X) ^ m, F.zpow_mem a.2 m⟩ : ↥F)⁻¹ * a = w⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    rw [show (w : X) = (a : X)⁻¹ * (a : X) ^ m from hwe]
    group
  rw [← QuotientGroup.eq] at *
  rw [QuotientGroup.eq, this]
  exact (pPrimeCore 2 ↥F).inv_mem hw

omit [Finite X] in
private theorem ctl_mem_normalizer_of_subgroupOf {H J : Subgroup X} (hJH : J ≤ H) {c : ↥H}
    (hc : c ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    (c : X) ∈ normalizer (J : Set X) := by
  rw [mem_normalizer_iff] at hc ⊢
  intro x
  constructor
  · intro hx
    exact (hc ⟨x, hJH hx⟩).1 hx
  · intro hx
    have hxH : x ∈ H := by
      have h1 : (c : X) * x * (c : X)⁻¹ ∈ H := hJH hx
      have h2 : x = (c : X)⁻¹ * ((c : X) * x * (c : X)⁻¹) * (c : X) := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (H.inv_mem c.2) h1) c.2
    exact (hc ⟨x, hxH⟩).2 hx

private theorem ctl_map_conj_conj {t : X} (ht2 : t ^ 2 = 1) (F : Subgroup X) :
    (F.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = F := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id X := by
    ext y
    have ht' : t * t = 1 := by rw [← pow_two]; exact ht2
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply, hti]
    rw [← mul_assoc, ← mul_assoc, ht', one_mul, mul_assoc, ht', mul_one]
  rw [h, Subgroup.map_id]

private theorem ctl_diag {b t : X} (ht2 : t ^ 2 = 1) (htb : t ∈ cen b) {F : Subgroup X}
    (hF : IsPCompIn 2 (cen b) F) (hne : F ≠ F.map (MulAut.conj t).toMonoidHom)
    {x : X} (hxF : x ∈ F) (hx4 : x ^ (2 ^ 2) = 1) :
    ∃ d ∈ (F ⊔ F.map (MulAut.conj t).toMonoidHom) ⊓ cen t, d ^ (2 ^ 2) = 1 ∧
      (x ^ 2)⁻¹ * d ^ 2 ∈ QOf F ∧
      (d ^ 2 = 1 → x ^ 2 * (t * x ^ 2 * t⁻¹) ∈
        oddCoreOf (F ⊔ F.map (MulAut.conj t).toMonoidHom)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F' : Subgroup X := F.map (MulAut.conj t).toMonoidHom with hF'
  have hF'pc : IsPCompIn 2 (cen b) F' := ctl_isPCompIn_conj hF (Subgroup.le_normalizer htb)
  set Y : Subgroup X := F ⊔ F' with hY
  have hYb : Y ≤ cen b := sup_le hF.1 hF'pc.1
  have hF'Q : F' ≤ QOf F := ctl_le_QOf_of_ne hF hF'pc hne
  have hFQ' : F ≤ QOf F' := ctl_le_QOf_of_ne hF'pc hF (Ne.symm hne)
  have hFq : IsTwoGenQuasi ↥F :=
    (isTwoGenQuasi_subgroupOf_iff hF.1).1 (isPComponent_two_iff.1 hF.2).2
  have hFsub : (F.subgroupOf Y).IsSubnormal := by
    have h1 : F.subgroupOf Y = (F.subgroupOf (cen b)).comap (Subgroup.inclusion hYb) := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
    rw [h1]
    exact (isPComponent_two_iff.1 hF.2).1.comap _
  have hFY : IsPCompIn 2 Y F :=
    ⟨le_sup_left, isPComponent_two_iff.2 ⟨hFsub, (isTwoGenQuasi_subgroupOf_iff le_sup_left).2 hFq⟩⟩
  have hOFY : pPrimeCoreOf 2 F ≤ oddCoreOf Y := pPrimeCoreOf_le_oddCoreOf le_sup_left hFsub
  have hOYQ : oddCoreOf Y ≤ QOf F := by
    intro o ho
    have hoN : o ∈ normalizer (F : Set X) := by
      obtain ⟨o', ho', rfl⟩ := ho
      exact ctl_mem_normalizer_of_subgroupOf le_sup_left
        (pPrimeCore_le_normalizer_of_isPComponent hFY.2 ho')
    refine mem_QOf_iff.2 ⟨hoN, fun f hf => ?_⟩
    have h1 : ⁅f, o⁆ ∈ F := by
      have h3 : ⁅f, o⁆ = f * (o * f⁻¹ * o⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact F.mul_mem hf ((mem_normalizer_iff.1 hoN f⁻¹).1 (F.inv_mem hf))
    have h2 : ⁅f, o⁆ ∈ oddCoreOf Y := by
      have h3 : ⁅f, o⁆ = (f * o * f⁻¹) * o⁻¹ := by rw [commutatorElement_def]
      rw [h3]
      exact (oddCoreOf Y).mul_mem
        ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y (le_sup_left (b := F') hf)) o).1 ho)
        ((oddCoreOf Y).inv_mem ho)
    exact ctl_inf_le_oddCoreOf (fun y hy => le_normalizer_oddCoreOf Y (le_sup_left (b := F') hy))
      (odd_card_oddCoreOf Y) ⟨h1, h2⟩
  have htY : t ∈ normalizer (Y : Set X) := by
    apply ctl_mem_normalizer_of_map_le
    rw [hY, Subgroup.map_sup, hF', ctl_map_conj_conj ht2, sup_comm]
  have htOY : t ∈ normalizer (pPrimeCoreOf 2 Y : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htY
  set xt : X := t * x * t⁻¹ with hxt
  have hxtF' : xt ∈ F' := ⟨x, hxF, rfl⟩
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
  have hcxx : ⁅x, xt⁆ ∈ oddCoreOf Y := hOFY (ctl_commutatorElement_mem hF hF'pc hne hxF hxtF')
  set z : X := x * xt with hz
  have hzY : z ∈ Y := Y.mul_mem (le_sup_left (b := F') hxF) (le_sup_right (a := F) hxtF')
  have hzt : ⁅z, t⁆ ∈ oddCoreOf Y := by
    have hφ : ∀ y : X, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
      rw [hti]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [ht']; group
    have h1 : ⁅z, t⁆ = ⁅x, xt⁆ := by
      have h2 : t * z * t⁻¹ = xt * x := by
        rw [hz, show t * (x * xt) * t⁻¹ = (t * x * t⁻¹) * (t * xt * t⁻¹) by group, hxt, hφ x]
      calc ⁅z, t⁆ = z * (t * z * t⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        _ = z * (xt * x)⁻¹ := by rw [h2]
        _ = ⁅x, xt⁆ := by rw [hz, commutatorElement_def]; group
    rw [h1]
    exact hcxx
  set π : ↥Y →* ↥Y ⧸ pPrimeCore 2 ↥Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  have hxY : x ∈ Y := le_sup_left (b := F') hxF
  have hxtY : xt ∈ Y := le_sup_right (a := F) hxtF'
  have hcomm : Commute (π ⟨x, hxY⟩) (π ⟨xt, hxtY⟩) := by
    obtain ⟨w, hw, hwe⟩ := hcxx
    have hw' : w = ⁅(⟨x, hxY⟩ : ↥Y), ⟨xt, hxtY⟩⁆ := Subtype.ext hwe
    have h1 : π ⁅(⟨x, hxY⟩ : ↥Y), ⟨xt, hxtY⟩⁆ = 1 := by
      rw [← hw']
      exact (QuotientGroup.eq_one_iff w).2 hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hxt4 : xt ^ (2 ^ 2) = 1 := by
    rw [hxt, conj_pow, hx4, mul_one, mul_inv_cancel]
  have hz4 : z ^ (2 ^ 2) ∈ pPrimeCoreOf 2 Y := by
    have h1 : π ⟨z, hzY⟩ ^ (2 ^ 2) = 1 := by
      have h2 : π ⟨z, hzY⟩ = π ⟨x, hxY⟩ * π ⟨xt, hxtY⟩ := by
        rw [← map_mul]
        rfl
      rw [h2, hcomm.mul_pow, ← map_pow, ← map_pow]
      have h3 : (⟨x, hxY⟩ : ↥Y) ^ (2 ^ 2) = 1 := Subtype.ext (by simpa using hx4)
      have h4 : (⟨xt, hxtY⟩ : ↥Y) ^ (2 ^ 2) = 1 := Subtype.ext (by simpa using hxt4)
      rw [h3, h4, map_one, one_mul]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 Y)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf Y)
  clear_value z
  obtain ⟨m, hm4, hzm⟩ := exists_zpow_twoElt_of_pow_mem hOcop hz4
  set z' : X := z ^ m with hz'
  have hz'Y : z' ∈ Y := Y.zpow_mem hzY m
  have hz't : ⁅z', t⁆ ∈ pPrimeCoreOf 2 Y := by
    have h1 : z' = z * (z⁻¹ * z') := by group
    rw [h1, ctl_comm_mul]
    have h2 : ⁅z⁻¹ * z', t⁆ ∈ oddCoreOf Y := by
      have h3 : ⁅z⁻¹ * z', t⁆ = (z⁻¹ * z') * (t * (z⁻¹ * z')⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact (oddCoreOf Y).mul_mem hzm ((mem_normalizer_iff.1 htOY _).1 ((oddCoreOf Y).inv_mem hzm))
    exact (oddCoreOf Y).mul_mem
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y hzY) _).1 h2) hzt
  obtain ⟨d, hd, hd4, hdz⟩ := exists_twoElt_centralizer_of_comm_mem ht2 htOY hz'Y hz't hm4
  refine ⟨d, hd, hd4, ?_, ?_⟩
  ·
    set o₂ : X := z⁻¹ * d with ho₂
    have ho₂Y : o₂ ∈ oddCoreOf Y := by
      have h1 : z⁻¹ * d = (z⁻¹ * z') * (d⁻¹ * z')⁻¹ := by group
      rw [ho₂, h1]
      exact (oddCoreOf Y).mul_mem hzm ((oddCoreOf Y).inv_mem hdz)
    have hzo : z⁻¹ * o₂ * z ∈ oddCoreOf Y := by
      have := (mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y (Y.inv_mem hzY)) o₂).1 ho₂Y
      rwa [inv_inv] at this
    have hxxt : x⁻¹ * xt * x ∈ F' := by
      have := (mem_normalizer_iff.1 ((mem_QOf_iff.1 (hFQ' (F.inv_mem hxF))).1) xt).1 hxtF'
      rwa [inv_inv] at this
    have h1 : (x ^ 2)⁻¹ * d ^ 2 = (x⁻¹ * xt * x) * xt * (z⁻¹ * o₂ * z) * o₂ := by
      rw [ho₂, hz]
      simp only [pow_two]
      group
    rw [h1]
    exact (QOf F).mul_mem ((QOf F).mul_mem ((QOf F).mul_mem (hF'Q hxxt) (hF'Q hxtF'))
      (hOYQ hzo)) (hOYQ ho₂Y)
  ·
    intro hd1
    set o₂ : X := z⁻¹ * d with ho₂
    have ho₂Y : o₂ ∈ oddCoreOf Y := by
      have h1 : z⁻¹ * d = (z⁻¹ * z') * (d⁻¹ * z')⁻¹ := by group
      rw [ho₂, h1]
      exact (oddCoreOf Y).mul_mem hzm ((oddCoreOf Y).inv_mem hdz)
    have hzo : z⁻¹ * o₂ * z ∈ oddCoreOf Y := by
      have := (mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y (Y.inv_mem hzY)) o₂).1 ho₂Y
      rwa [inv_inv] at this
    have hz2 : z ^ 2 ∈ oddCoreOf Y := by
      have hd : d = z * o₂ := by rw [ho₂, mul_inv_cancel_left]
      have h1 : d ^ 2 = z ^ 2 * ((z⁻¹ * o₂ * z) * o₂) := by
        rw [hd, pow_two, pow_two]
        group
      rw [hd1] at h1
      have h2 : z ^ 2 = ((z⁻¹ * o₂ * z) * o₂)⁻¹ := (eq_inv_of_mul_eq_one_left h1.symm)
      rw [h2]
      exact (oddCoreOf Y).inv_mem ((oddCoreOf Y).mul_mem hzo ho₂Y)
    have hc' : ⁅x⁻¹, xt⁻¹⁆ ∈ oddCoreOf Y :=
      hOFY (ctl_commutatorElement_mem hF hF'pc hne (F.inv_mem hxF) (F'.inv_mem hxtF'))
    have hcw : xt⁻¹ * ⁅x⁻¹, xt⁻¹⁆ * xt ∈ oddCoreOf Y := by
      have := (mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y (Y.inv_mem hxtY)) _).1 hc'
      rwa [inv_inv] at this
    have h1 : x ^ 2 * (t * x ^ 2 * t⁻¹) = z ^ 2 * (xt⁻¹ * ⁅x⁻¹, xt⁻¹⁆ * xt) := by
      have h2 : t * x ^ 2 * t⁻¹ = xt ^ 2 := by rw [hxt, conj_pow]
      rw [h2, hz, commutatorElement_def]
      simp only [pow_two]
      group
    rw [h1]
    exact (oddCoreOf Y).mul_mem hz2 hcw

private theorem ctl_sq_sq_of_center {K : Type} [Group K] (hZ : Nat.card (center K) = 2) {k : K}
    (hk : k * k ∈ center K) : k * k * (k * k) = 1 := by
  have h1 := orderOf_dvd_natCard (⟨k * k, hk⟩ : ↥(center K))
  rw [hZ] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
  have h3 := congrArg Subtype.val h2
  simpa [pow_two] using h3

private theorem ctl_mem_of_sq_mem {N H : Subgroup X} (hN : Odd (Nat.card N)) {o : X}
    (ho : o ∈ N) (h2 : o ^ 2 ∈ H) : o ∈ H := by
  obtain ⟨k, hk⟩ : Odd (orderOf o) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N ho)
  have h1 : o = (o ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact H.pow_mem h2 _

private theorem ctl_eq_one_of_twoElt {N : Subgroup X} (hN : Odd (Nat.card N)) {g : X}
    (hg : g ∈ N) {j : ℕ} (hgj : g ^ (2 ^ j) = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hgj
  have h2 : orderOf g ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hg
  have hcop : Nat.Coprime (2 ^ j) (Nat.card N) := (Nat.coprime_two_left.2 hN).pow_left j
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)

omit [Finite X] in
private theorem ctl_comm_mul_right (a g h : X) : ⁅a, g * h⁆ = ⁅a, g⁆ * (g * ⁅a, h⁆ * g⁻¹) := by
  simp only [commutatorElement_def]
  group

omit [Finite X] in
private theorem ctl_sq_mem {N : Subgroup X} {a b c : X} (ha : a ∈ normalizer (N : Set X))
    (hb : b ∈ normalizer (N : Set X)) (hab : ⁅a, b⁆ ∈ N) (hc : (a * b)⁻¹ * c ∈ N) :
    (a ^ 2 * b ^ 2)⁻¹ * c ^ 2 ∈ N := by
  have key : ∀ g ∈ normalizer (N : Set X), ∀ m ∈ N, g * m * g⁻¹ ∈ N :=
    fun g hg m hm => (mem_normalizer_iff.1 hg m).1 hm
  have h1 : (a ^ 2 * b ^ 2)⁻¹ * c ^ 2 =
      ((b ^ 2)⁻¹ * (a⁻¹ * ⁅a, b⁆⁻¹ * a⁻¹⁻¹) * (b ^ 2)⁻¹⁻¹) *
        ((a * b)⁻¹ * ((a * b)⁻¹ * c) * (a * b)⁻¹⁻¹) * ((a * b)⁻¹ * c) := by
    rw [commutatorElement_def]
    simp only [pow_two]
    group
  rw [h1]
  exact N.mul_mem (N.mul_mem (key _ (inv_mem (pow_mem hb 2)) _
    (key _ (inv_mem ha) _ (N.inv_mem hab))) (key _ (inv_mem (mul_mem ha hb)) _ hc)) hc

private theorem ctl_pair {H F F' : Subgroup X} (hF : IsPCompIn 2 H F) (hF' : IsPCompIn 2 H F') :
    IsPCompIn 2 (F ⊔ F') F ∧ pPrimeCoreOf 2 F ≤ oddCoreOf (F ⊔ F') ∧
      oddCoreOf (F ⊔ F') ≤ QOf F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup X := F ⊔ F' with hY
  have hYH : Y ≤ H := sup_le hF.1 hF'.1
  have hFq : IsTwoGenQuasi ↥F :=
    (isTwoGenQuasi_subgroupOf_iff hF.1).1 (isPComponent_two_iff.1 hF.2).2
  have hFsub : (F.subgroupOf Y).IsSubnormal := by
    have h1 : F.subgroupOf Y = (F.subgroupOf H).comap (Subgroup.inclusion hYH) := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion]
    rw [h1]
    exact (isPComponent_two_iff.1 hF.2).1.comap _
  have hFY : IsPCompIn 2 Y F :=
    ⟨le_sup_left, isPComponent_two_iff.2 ⟨hFsub, (isTwoGenQuasi_subgroupOf_iff le_sup_left).2 hFq⟩⟩
  have hOFY : pPrimeCoreOf 2 F ≤ oddCoreOf Y := pPrimeCoreOf_le_oddCoreOf le_sup_left hFsub
  refine ⟨hFY, hOFY, fun o ho => ?_⟩
  have hoN : o ∈ normalizer (F : Set X) := by
    obtain ⟨o', ho', rfl⟩ := ho
    exact ctl_mem_normalizer_of_subgroupOf le_sup_left
      (pPrimeCore_le_normalizer_of_isPComponent hFY.2 ho')
  refine mem_QOf_iff.2 ⟨hoN, fun f hf => ?_⟩
  have h1 : ⁅f, o⁆ ∈ F := by
    have h3 : ⁅f, o⁆ = f * (o * f⁻¹ * o⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact F.mul_mem hf ((mem_normalizer_iff.1 hoN f⁻¹).1 (F.inv_mem hf))
  have h2 : ⁅f, o⁆ ∈ oddCoreOf Y := by
    have h3 : ⁅f, o⁆ = (f * o * f⁻¹) * o⁻¹ := by rw [commutatorElement_def]
    rw [h3]
    exact (oddCoreOf Y).mul_mem
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y (le_sup_left (b := F') hf)) o).1 ho)
      ((oddCoreOf Y).inv_mem ho)
  exact ctl_inf_le_oddCoreOf (fun y hy => le_normalizer_oddCoreOf Y (le_sup_left (b := F') hy))
    (odd_card_oddCoreOf Y) ⟨h1, h2⟩

private theorem ctl_comm_sup {H J F F' : Subgroup X} (hJ : IsPCompIn 2 H J)
    (hF : IsPCompIn 2 H F) (hF' : IsPCompIn 2 H F') (hJF : J ≠ F) (hJF' : J ≠ F')
    (hFF' : F ≤ normalizer (F' : Set X)) {p g : X} (hp : p ∈ J) (hg : g ∈ F ⊔ F') :
    ⁅p, g⁆ ∈ oddCoreOf H := by
  have hOJ : pPrimeCoreOf 2 J ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hJ.1 (isPComponent_two_iff.1 hJ.2).1
  obtain ⟨f, hf, f', hf', rfl⟩ := ctl_exists_mul_of_mem_sup hFF' hg
  rw [ctl_comm_mul_right]
  exact (oddCoreOf H).mul_mem (hOJ (ctl_commutatorElement_mem hJ hF hJF hp hf))
    ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf H (hF.1 hf)) _).1
      (hOJ (ctl_commutatorElement_mem hJ hF' hJF' hp hf')))

private theorem ctl_diag_basic {b t : X} (ht2 : t ^ 2 = 1) (htb : t ∈ cen b) {F : Subgroup X}
    (hF : IsPCompIn 2 (cen b) F) (hne : F ≠ F.map (MulAut.conj t).toMonoidHom)
    {y : X} (hyF : y ∈ F) {j : ℕ} (hyj : y ^ (2 ^ j) = 1) :
    ∃ d ∈ (F ⊔ F.map (MulAut.conj t).toMonoidHom) ⊓ cen t, d ^ (2 ^ j) = 1 ∧
      (y * (t * y * t⁻¹))⁻¹ * d ∈ oddCoreOf (F ⊔ F.map (MulAut.conj t).toMonoidHom) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F' : Subgroup X := F.map (MulAut.conj t).toMonoidHom with hF'
  have hF'pc : IsPCompIn 2 (cen b) F' := ctl_isPCompIn_conj hF (Subgroup.le_normalizer htb)
  set Y : Subgroup X := F ⊔ F' with hY
  obtain ⟨-, hOFY, -⟩ := ctl_pair hF hF'pc
  have htY : t ∈ normalizer (Y : Set X) := by
    apply ctl_mem_normalizer_of_map_le
    rw [hY, Subgroup.map_sup, hF', ctl_map_conj_conj ht2, sup_comm]
  have htOY : t ∈ normalizer (pPrimeCoreOf 2 Y : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htY
  set yt : X := t * y * t⁻¹ with hyt
  have hytF' : yt ∈ F' := ⟨y, hyF, rfl⟩
  have ht' : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht'
  have hcyy : ⁅y, yt⁆ ∈ oddCoreOf Y := hOFY (ctl_commutatorElement_mem hF hF'pc hne hyF hytF')
  set z : X := y * yt with hz
  have hzY : z ∈ Y := Y.mul_mem (le_sup_left (b := F') hyF) (le_sup_right (a := F) hytF')
  have hzt : ⁅z, t⁆ ∈ oddCoreOf Y := by
    have hφ : ∀ w : X, t * (t * w * t⁻¹) * t⁻¹ = w := fun w => by
      rw [hti]
      calc t * (t * w * t) * t = (t * t) * w * (t * t) := by group
        _ = w := by rw [ht']; group
    have h1 : ⁅z, t⁆ = ⁅y, yt⁆ := by
      have h2 : t * z * t⁻¹ = yt * y := by
        rw [hz, show t * (y * yt) * t⁻¹ = (t * y * t⁻¹) * (t * yt * t⁻¹) by group, hyt, hφ y]
      calc ⁅z, t⁆ = z * (t * z * t⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        _ = z * (yt * y)⁻¹ := by rw [h2]
        _ = ⁅y, yt⁆ := by rw [hz, commutatorElement_def]; group
    rw [h1]
    exact hcyy
  set π : ↥Y →* ↥Y ⧸ pPrimeCore 2 ↥Y := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  have hyY : y ∈ Y := le_sup_left (b := F') hyF
  have hytY : yt ∈ Y := le_sup_right (a := F) hytF'
  have hcomm : Commute (π ⟨y, hyY⟩) (π ⟨yt, hytY⟩) := by
    obtain ⟨w, hw, hwe⟩ := hcyy
    have hw' : w = ⁅(⟨y, hyY⟩ : ↥Y), ⟨yt, hytY⟩⁆ := Subtype.ext hwe
    have h1 : π ⁅(⟨y, hyY⟩ : ↥Y), ⟨yt, hytY⟩⁆ = 1 := by
      rw [← hw']
      exact (QuotientGroup.eq_one_iff w).2 hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hytj : yt ^ (2 ^ j) = 1 := by
    rw [hyt, conj_pow, hyj, mul_one, mul_inv_cancel]
  have hzj : z ^ (2 ^ j) ∈ pPrimeCoreOf 2 Y := by
    have h1 : π ⟨z, hzY⟩ ^ (2 ^ j) = 1 := by
      have h2 : π ⟨z, hzY⟩ = π ⟨y, hyY⟩ * π ⟨yt, hytY⟩ := by
        rw [← map_mul]
        rfl
      rw [h2, hcomm.mul_pow, ← map_pow, ← map_pow]
      have h3 : (⟨y, hyY⟩ : ↥Y) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hyj)
      have h4 : (⟨yt, hytY⟩ : ↥Y) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hytj)
      rw [h3, h4, map_one, one_mul]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 Y)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf Y)
  clear_value z
  obtain ⟨m, hmj, hzm⟩ := exists_zpow_twoElt_of_pow_mem hOcop hzj
  set z' : X := z ^ m with hz'
  have hz'Y : z' ∈ Y := Y.zpow_mem hzY m
  have hz't : ⁅z', t⁆ ∈ pPrimeCoreOf 2 Y := by
    have h1 : z' = z * (z⁻¹ * z') := by group
    rw [h1, ctl_comm_mul]
    have h2 : ⁅z⁻¹ * z', t⁆ ∈ oddCoreOf Y := by
      have h3 : ⁅z⁻¹ * z', t⁆ = (z⁻¹ * z') * (t * (z⁻¹ * z')⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact (oddCoreOf Y).mul_mem hzm ((mem_normalizer_iff.1 htOY _).1 ((oddCoreOf Y).inv_mem hzm))
    exact (oddCoreOf Y).mul_mem
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf Y hzY) _).1 h2) hzt
  obtain ⟨d, hd, hdj, hdz⟩ := exists_twoElt_centralizer_of_comm_mem ht2 htOY hz'Y hz't hmj
  refine ⟨d, hd, hdj, ?_⟩
  have h1 : z⁻¹ * d = (z⁻¹ * z') * (d⁻¹ * z')⁻¹ := by group
  rw [h1]
  exact (oddCoreOf Y).mul_mem hzm ((oddCoreOf Y).inv_mem hdz)

private theorem ctl_sq_mem_of_QOf {F : Subgroup X} {n : ℕ}
    (hF : IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n) {x : X} (hxF : x ∈ F) (hxQ : x ∈ QOf F) :
    x ^ 2 ∈ oddCoreOf F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥F →* ↥F ⧸ pPrimeCore 2 ↥F := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  have hcen : π ⟨x, hxF⟩ ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) g
    obtain ⟨w, hw, hwe⟩ := (mem_QOf_iff.1 hxQ).2 l l.2
    have hw' : w = ⁅l, (⟨x, hxF⟩ : ↥F)⁆ := Subtype.ext hwe
    have h1 : π ⁅l, (⟨x, hxF⟩ : ↥F)⁆ = 1 := by
      rw [← hw']
      exact (QuotientGroup.eq_one_iff w).2 hw
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have h2 : π ⟨x, hxF⟩ ^ 2 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨π ⟨x, hxF⟩, hcen⟩ : ↥(center (↥F ⧸ pPrimeCore 2 ↥F)))
    rw [hF.2.1] at h1
    have h3 := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h1)
    simpa using h3
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, by simp⟩

private theorem ctl_perm_sq {n : ℕ} {a b c d e f : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hbf : b ≠ f) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f)
    (hef : e ≠ f) :
    (Equiv.swap a b * (Equiv.swap a c * Equiv.swap b d) * Equiv.swap e f) *
      (Equiv.swap a b * (Equiv.swap a c * Equiv.swap b d) * Equiv.swap e f) =
      Equiv.swap a b * Equiv.swap c d := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hae.symm
  have := haf.symm
  have := hbc.symm
  have := hbd.symm
  have := hbe.symm
  have := hbf.symm
  have := hcd.symm
  have := hce.symm
  have := hcf.symm
  have := hde.symm
  have := hdf.symm
  have := hef.symm
  ext x
  by_cases hx1 : x = a
  · subst hx1
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  by_cases hx5 : x = e
  · subst hx5
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  by_cases hx6 : x = f
  · subst hx6
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, *]

private theorem ctl_dc_fourth_root {K : Type} [Group K] {n : ℕ} (hn : 8 ≤ n)
    (hK : IsDoubleCoverOfAlt K n) : ∃ k : K, k ^ 4 ≠ 1 ∧ k ^ 4 ∈ center K := by
  set C : AhatData.CoverSetup n K := AhatData.CoverSetup.ofCover hK with hC
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  set d : Fin n := ⟨3, by omega⟩
  set e : Fin n := ⟨4, by omega⟩
  set f : Fin n := ⟨5, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have had : a ≠ d := by simp [a, d, Fin.ext_iff]
  have hae : a ≠ e := by simp [a, e, Fin.ext_iff]
  have haf : a ≠ f := by simp [a, f, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hbd : b ≠ d := by simp [b, d, Fin.ext_iff]
  have hbe : b ≠ e := by simp [b, e, Fin.ext_iff]
  have hbf : b ≠ f := by simp [b, f, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hce : c ≠ e := by simp [c, e, Fin.ext_iff]
  have hcf : c ≠ f := by simp [c, f, Fin.ext_iff]
  have hde : d ≠ e := by simp [d, e, Fin.ext_iff]
  have hdf : d ≠ f := by simp [d, f, Fin.ext_iff]
  have hef : e ≠ f := by simp [e, f, Fin.ext_iff]
  have hsign : Equiv.Perm.sign
      (Equiv.swap a b * (Equiv.swap a c * Equiv.swap b d) * Equiv.swap e f) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hac, Equiv.Perm.sign_swap hbd, Equiv.Perm.sign_swap hef]
    decide
  obtain ⟨k, hk⟩ := C.exists_ρ_eq hsign
  have hk2 : C.ρ (k * k) = Equiv.swap a b * Equiv.swap c d := by
    rw [map_mul, hk]
    exact ctl_perm_sq hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  have h4 : k ^ 4 = k * k * (k * k) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨k, ?_, ?_⟩
  · rw [h4]
    exact C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hk2
  · rw [h4]
    exact C.sq_mem_center (by rw [hk2]; exact dbl_mul_self hab hac had hbc hbd hcd)

private theorem ctl_lift_pow {F : Subgroup X} (k : ↥F ⧸ pPrimeCore 2 ↥F) {j : ℕ}
    (hk : k ^ (2 ^ j) = 1) :
    ∃ x ∈ F, x ^ (2 ^ j) = 1 ∧ ∃ hxF : x ∈ F,
      (QuotientGroup.mk (⟨x, hxF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = k := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective k
  have haj : (a : X) ^ (2 ^ j) ∈ pPrimeCoreOf 2 F := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact ⟨_, hk, by simp⟩
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCoreOf 2 F)) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf F)
  obtain ⟨m, hmj, ham⟩ := exists_zpow_twoElt_of_pow_mem hOcop haj
  refine ⟨(a : X) ^ m, F.zpow_mem a.2 m, hmj, F.zpow_mem a.2 m, ?_⟩
  rw [QuotientGroup.eq]
  obtain ⟨w, hw, hwe⟩ := ham
  have : (⟨(a : X) ^ m, F.zpow_mem a.2 m⟩ : ↥F)⁻¹ * a = w⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    rw [show (w : X) = (a : X)⁻¹ * (a : X) ^ m from hwe]
    group
  rw [this]
  exact (pPrimeCore 2 ↥F).inv_mem hw

private theorem ctl_exists_root {F : Subgroup X} {n : ℕ} (hn : 8 ≤ n)
    (hF : IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) n) :
    ∃ y ∈ F, y ^ (2 ^ 3) = 1 ∧ (y ^ 2) ^ 2 ∉ oddCoreOf F ∧ (y ^ 2) ^ 2 ∈ QOf F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk4, hkz⟩ := ctl_dc_fourth_root hn hF
  have hk8 : k ^ (2 ^ 3) = 1 := by
    have h0 : k ^ 2 * k ^ 2 = k ^ 4 := by group
    have h1 := ctl_sq_sq_of_center hF.2.1 (k := k ^ 2) (by rw [h0]; exact hkz)
    calc k ^ (2 ^ 3) = k ^ 2 * k ^ 2 * (k ^ 2 * k ^ 2) := by group
      _ = 1 := h1
  obtain ⟨y, hyF, hy8, hyF', hyk⟩ := ctl_lift_pow k hk8
  have hy4F : (y ^ 2) ^ 2 ∈ F := F.pow_mem (F.pow_mem hyF 2) 2
  have hy4k : (QuotientGroup.mk (⟨(y ^ 2) ^ 2, hy4F⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) = k ^ 4 := by
    rw [← hyk, ← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_mk]
    group
  refine ⟨y, hyF, hy8, ?_, ?_⟩
  · rintro ⟨w, hw, hwe⟩
    apply hk4
    rw [← hy4k, QuotientGroup.eq_one_iff]
    have : (⟨(y ^ 2) ^ 2, hy4F⟩ : ↥F) = w := Subtype.ext hwe.symm
    rw [this]
    exact hw
  · refine mem_QOf_iff.2 ⟨Subgroup.le_normalizer hy4F, fun a ha => ?_⟩
    have hz := Subgroup.mem_center_iff.1 hkz (QuotientGroup.mk ⟨a, ha⟩)
    rw [← hy4k] at hz
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥F)
        ⁅(⟨a, ha⟩ : ↥F), ⟨(y ^ 2) ^ 2, hy4F⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hz
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

private theorem ctl_QOf_piece {L : Subgroup X} {c d : X} (hcd : c ∈ cen d) (hc : c ∈ QOf L) :
    c ∈ QOf (sec6Piece L d) := by
  obtain ⟨hcN, hcC⟩ := mem_QOf_iff.1 hc
  have hPL : sec6Piece L d ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hcP : c ∈ normalizer (sec6Piece L d : Set X) :=
    ctl_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf hcN (Subgroup.le_normalizer hcd))
  refine mem_QOf_iff.2 ⟨hcP, fun p hp => ?_⟩
  have h1 : ⁅p, c⁆ ∈ sec6Piece L d := by
    have h3 : ⁅p, c⁆ = p * (c * p⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (sec6Piece L d).mul_mem hp
      ((mem_normalizer_iff.1 hcP p⁻¹).1 ((sec6Piece L d).inv_mem hp))
  exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf L (hPL hx))
    (odd_card_oddCoreOf L) ⟨h1, hcC p (hPL hp)⟩

private theorem ctl_QOf_of_covers {L P : Subgroup X} {c d : X} (hL : IsPCompIn 2 (cen d) L)
    (hPL : P ≤ L) (hPq : IsTwoGenQuasi ↥P) (hcov : P.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤)
    (hcd : c ∈ cen d) (hc : c ∈ QOf P) : c ∈ QOf L := by
  obtain ⟨hcP, hcC⟩ := mem_QOf_iff.1 hc
  have hLc := ctl_isPCompIn_conj hL (Subgroup.le_normalizer hcd)
  have hPLc : P ≤ L.map (MulAut.conj c).toMonoidHom := by
    rw [← map_conj_eq_of_mem_normalizer hcP]
    exact Subgroup.map_mono hPL
  have hcL : c ∈ normalizer (L : Set X) :=
    mem_normalizer_of_map_conj_eq (eq_of_isPCompIn_of_le hL hLc hPL hPLc hPq).symm
  have hcO : c ∈ normalizer (oddCoreOf L : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hcL
  have hLeq : P ⊔ pPrimeCoreOf 2 L = L := (covers_subgroupOf_iff hPL).1 hcov
  have hOPL := ctl_oddCoreOf_le_of_covers hPL hcov
  refine mem_QOf_iff.2 ⟨hcL, fun l hl => ?_⟩
  have hl' : l ∈ P ⊔ oddCoreOf L := hLeq.symm ▸ hl
  obtain ⟨p, hp, o, ho, rfl⟩ :=
    ctl_exists_mul_of_mem_sup (fun x hx => le_normalizer_oddCoreOf L (hPL hx)) hl'
  rw [ctl_comm_mul]
  have h1 : ⁅o, c⁆ ∈ oddCoreOf L := by
    have h3 : ⁅o, c⁆ = o * (c * o⁻¹ * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (oddCoreOf L).mul_mem ho ((mem_normalizer_iff.1 hcO o⁻¹).1 ((oddCoreOf L).inv_mem ho))
  exact (oddCoreOf L).mul_mem ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf L (hPL hp)) _).1 h1)
    (hOPL (hcC p hp))

private theorem ctl_mem_of_le_sSup_sup {H M : Subgroup X} {S : Set (Subgroup X)}
    (hM : IsPCompIn 2 H M) (hS : ∀ J ∈ S, IsPCompIn 2 H J) (hMS : M ≤ sSup S ⊔ oddCoreOf H) :
    M ∈ S := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hMS'
  have hMq : IsTwoGenQuasi ↥M :=
    (isTwoGenQuasi_subgroupOf_iff hM.1).1 (isPComponent_two_iff.1 hM.2).2
  have hOM : pPrimeCoreOf 2 M ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hM.1 (isPComponent_two_iff.1 hM.2).1
  have hOMM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hle : sSup S ≤ centralizerSection M (oddCoreOf H) := by
    refine sSup_le fun J hJ => ?_
    intro j hj
    have hne : M ≠ J := fun h => hMS' (by rw [h]; exact hJ)
    have hc : ∀ g ∈ J, ∀ m ∈ M, ⁅m, g⁆ ∈ pPrimeCoreOf 2 M := fun g hg m hm =>
      ctl_commutatorElement_mem hM (hS J hJ) hne hm hg
    exact ⟨ctl_mem_normalizer (fun m hm => hOMM (hc j hj m hm))
        (fun m hm => hOMM (hc j⁻¹ (J.inv_mem hj) m hm)),
      le_normalizer_oddCoreOf H ((hS J hJ).1 hj), fun m hm => hOM (hc j hj m hm)⟩
  have hle' : oddCoreOf H ≤ centralizerSection M (oddCoreOf H) := by
    intro o ho
    refine ⟨?_, le_normalizer_oddCoreOf H (oddCoreOf_le H ho), fun m hm => ?_⟩
    · obtain ⟨o', ho', rfl⟩ := ho
      exact ctl_mem_normalizer_of_subgroupOf hM.1
        (pPrimeCore_le_normalizer_of_isPComponent hM.2 ho')
    · have h3 : ⁅m, o⁆ = (m * o * m⁻¹) * o⁻¹ := by rw [commutatorElement_def]
      rw [h3]
      exact (oddCoreOf H).mul_mem
        ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf H (hM.1 hm)) o).1 ho)
        ((oddCoreOf H).inv_mem ho)
  refine not_commutator_le_of_odd hMq (odd_card_oddCoreOf H) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨-, -, hab⟩ := (sup_le hle hle') (hMS hb)
  exact hab a ha

private theorem ctl_match
    {n : ℕ} {t d : X}
    (hd2 : orderOf d = 2) (hdQ : d ∈ Sec6Q X n (cen t)) (hcov : Sec6Covers X n t d)
    {L : Subgroup X} (hL : Sec6KComp X n (cen d) L) :
    ∃ L' : Subgroup X, Sec6KComp X n (cen t) L' ∧ sec6Piece L' d ≤ L ∧
      (sec6Piece L' d).subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd2' : d ^ 2 = 1 := by
    rw [← hd2]
    exact pow_orderOf_eq_one d
  have hLpc := ctl_isPCompIn hL
  have hLq := ctl_isTwoGenQuasi hL
  set Kt : Subgroup X := Sec6K X n (cen t) with hKt
  set Kd : Subgroup X := Sec6K X n (cen d) with hKd
  have hLKd : L ≤ Kd := le_sSup hL
  have hOKd : oddCoreOf Kd ≤ oddCoreOf (cen d) :=
    ctl_oddCoreOf_le_of_normal (ctl_K_le n d) (Sec6K_cen_normal n d)
  have hLcov : L ≤ (Kt ⊓ cen d) ⊔ oddCoreOf (cen d) := by
    have h1 : Kd = oddCoreOf Kd ⊔ (Kd ⊓ Kt) := hcov
    refine hLKd.trans (h1.le.trans (sup_le (hOKd.trans le_sup_right) (le_sup_of_le_left ?_)))
    exact le_inf inf_le_right (inf_le_left.trans (ctl_K_le n d))
  set E : Subgroup X := oTwoPrimeOf (L ⊓ Kt) with hE
  have hEL : E ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovE : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    ctl_covers (L := Kt) (D := Kt) le_rfl hLpc.1 hLpc.2 hLcov
  have hEq : IsTwoGenQuasi ↥E :=
    isTwoGenQuasi_of_covers hEL hcovE (primeResidual_oTwoPrimeOf _) hLq
  set D : Subgroup X := cen d ⊓ cen t with hD
  have hAD : L ⊓ Kt ≤ D := le_inf (inf_le_left.trans hLpc.1) (inf_le_right.trans (ctl_K_le n t))
  have hA1 : ((L ⊓ cen t).subgroupOf D).IsSubnormal :=
    ctl_isSubnormal_inf inf_le_left inf_le_right (isPComponent_two_iff.1 hLpc.2).1
  have hAsub : ((L ⊓ Kt).subgroupOf D).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_normal_of_subnormal
      (le_inf (inf_le_left.trans hLpc.1) inf_le_right) (inf_le_inf_left L (ctl_K_le n t)) hA1 ?_
    refine (normal_subgroupOf_iff_le_normalizer (inf_le_inf_left L (ctl_K_le n t))).2 ?_
    intro g hg
    exact mem_normalizer_inf (Subgroup.le_normalizer hg.1) (Sec6K_cen_normal n t hg.2)
  have hEpc : IsPCompIn 2 D E := ctl_isPCompIn_oTwoPrimeOf hAD hAsub hEq
  set S : Set (Subgroup X) :=
    {P | ∃ L' : Subgroup X, Sec6KComp X n (cen t) L' ∧ P = sec6Piece L' d} with hSdef
  have hS : ∀ J ∈ S, IsPCompIn 2 D J := by
    rintro _ ⟨L', hL', rfl⟩
    have hdL' : d ∈ QOf L' := ctl_Q_le_QOf hL' hdQ
    exact ctl_isPCompIn (ctl_piece_K hd2 hL' (fun _ => hdL') (fun _ => le_sup_right (a := L') hdL'))
  have hKtS : Kt ≤ sSup S ⊔ oddCoreOf Kt := by
    refine sSup_le fun L' hL' => ?_
    have hdL' : d ∈ QOf L' := ctl_Q_le_QOf hL' hdQ
    have hP'L' : sec6Piece L' d ≤ L' := (oTwoPrimeOf_le _).trans inf_le_left
    have hcov' : (sec6Piece L' d).subgroupOf L' ⊔ pPrimeCore 2 ↥L' = ⊤ :=
      oTwoPrimeOf_inf_centralizer_covers hd2' (ctl_isTwoGenQuasi hL').1 hdL'
    refine ((covers_subgroupOf_iff hP'L').1 hcov').symm.le.trans (sup_le ?_ ?_)
    · exact le_sup_of_le_left (le_sSup (show sec6Piece L' d ∈ S from ⟨L', hL', rfl⟩))
    · exact (ctl_oddCoreOf_le_K hL').trans le_sup_right
  have hOD : oddCoreOf Kt ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun g hg => mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n t hg.2))
        (Subgroup.le_normalizer hg))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hSKt : sSup S ≤ normalizer (oddCoreOf Kt : Set X) := by
    refine sSup_le ?_
    rintro _ ⟨L', hL', rfl⟩ p hp
    exact le_normalizer_oddCoreOf Kt
      ((show L' ≤ Kt from le_sSup hL') (((oTwoPrimeOf_le _).trans inf_le_left) hp))
  have hSD : sSup S ≤ D := sSup_le fun J hJ => (hS J hJ).1
  have hED : E ≤ sSup S ⊔ oddCoreOf D := by
    intro e he
    have heKt : e ∈ Kt := ((oTwoPrimeOf_le _).trans inf_le_right) he
    have heD : e ∈ D := hEpc.1 he
    obtain ⟨s, hs, o, ho, rfl⟩ := ctl_exists_mul_of_mem_sup hSKt (hKtS heKt)
    have hoD : o ∈ D := by
      have h1 : o = s⁻¹ * (s * o) := by group
      rw [h1]
      exact D.mul_mem (D.inv_mem (hSD hs)) heD
    exact Subgroup.mul_mem_sup hs (hOD ⟨ho, hoD⟩)
  obtain ⟨L', hL', hEeq⟩ := ctl_mem_of_le_sSup_sup hEpc hS hED
  refine ⟨L', hL', ?_, ?_⟩
  · rw [← hEeq]
    exact hEL
  · rw [← hEeq]
    exact hcovE

private theorem ctl_actsThrough_of_Q
    {n : ℕ} {t d b : X}
    (hd2 : orderOf d = 2) (hdQ : d ∈ Sec6Q X n (cen t)) (hcov : Sec6Covers X n t d)
    (hbd : b ∈ cen d) (hbA : Sec6ActsThrough X n t b) : Sec6ActsThrough X n d b := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd2' : d ^ 2 = 1 := by
    rw [← hd2]
    exact pow_orderOf_eq_one d
  have key : ∀ L : Subgroup X, Sec6KComp X n (cen d) L → ∃ L' : Subgroup X,
      Sec6KComp X n (cen t) L' ∧ sec6Piece L' d ≤ L ∧
      sec6Piece L' d ⊔ pPrimeCoreOf 2 L' = L' ∧
      Nonempty ((↥L' ⧸ pPrimeCore 2 ↥L') ≃* (↥L ⧸ pPrimeCore 2 ↥L)) ∧
      ∀ c ∈ cen d, c ∈ QOf L' → c ∈ QOf L := by
    intro L hL
    obtain ⟨L', hL', hPL, hcovPL⟩ := ctl_match hd2 hdQ hcov hL
    have hdL' : d ∈ QOf L' := ctl_Q_le_QOf hL' hdQ
    have hPL' : sec6Piece L' d ≤ L' := (oTwoPrimeOf_le _).trans inf_le_left
    have hcovPL' : (sec6Piece L' d).subgroupOf L' ⊔ pPrimeCore 2 ↥L' = ⊤ :=
      oTwoPrimeOf_inf_centralizer_covers hd2' (ctl_isTwoGenQuasi hL').1 hdL'
    have hPq : IsTwoGenQuasi ↥(sec6Piece L' d) :=
      isTwoGenQuasi_of_covers hPL' hcovPL' (primeResidual_oTwoPrimeOf _) (ctl_isTwoGenQuasi hL')
    obtain ⟨e1⟩ := nonempty_quot_mulEquiv_of_covers hPL' hcovPL'
    obtain ⟨e2⟩ := nonempty_quot_mulEquiv_of_covers hPL hcovPL
    exact ⟨L', hL', hPL, (covers_subgroupOf_iff hPL').1 hcovPL', ⟨e1.symm.trans e2⟩,
      fun c hcd hc => ctl_QOf_of_covers (ctl_isPCompIn hL) hPL hPq hcovPL hcd
        (ctl_QOf_piece hcd hc)⟩
  refine ⟨fun L hL => ?_, fun L hL => ?_⟩
  · obtain ⟨L', hL', -, -, ⟨e⟩, htr⟩ := key L (Or.inl hL)
    rcases hL' with h5 | h6
    · exact htr b hbd (hbA.1 L' h5)
    · exfalso
      have h1 := ctl_card_lt h6.2 hL.2
      rw [Nat.card_congr e.toEquiv] at h1
      exact lt_irrefl _ h1
  · obtain ⟨L', hL', hPL, hPL'eq, -, htr⟩ := key L (Or.inr hL)
    have hbL' : b ∈ L' ⊔ QOf L' := by
      rcases hL' with h5 | h6
      · exact le_sup_right (a := L') (hbA.1 L' h5)
      · exact hbA.2 L' h6
    obtain ⟨m, hmL', hmq⟩ := ctl_exists_inner hbL'
    have hm' : m ∈ sec6Piece L' d ⊔ oddCoreOf L' := hPL'eq.symm ▸ hmL'
    obtain ⟨p, hp, o, ho, rfl⟩ := ctl_exists_mul_of_mem_sup
      (fun z hz => le_normalizer_oddCoreOf L' (((oTwoPrimeOf_le _).trans inf_le_left) hz)) hm'
    have hpd : p ∈ cen d := ((oTwoPrimeOf_le _).trans inf_le_right) hp
    have h1 : p⁻¹ * b ∈ QOf L' := by
      have h2 : p⁻¹ * b = o * ((p * o)⁻¹ * b) := by group
      rw [h2]
      exact (QOf L').mul_mem (ctl_oddCoreOf_le_QOf L' ho) hmq
    have h3 : p⁻¹ * b ∈ QOf L := htr _ ((cen d).mul_mem ((cen d).inv_mem hpd) hbd) h1
    have h4 : b = p * (p⁻¹ * b) := by group
    rw [h4]
    exact Subgroup.mul_mem_sup (hPL hp) h3

private theorem ctl_QOf_of_Qd
    {n : ℕ} {t d u : X}
    (h51 : Sec6Lemma51 X n) (hd2 : orderOf d = 2) (hdQ : d ∈ Sec6Q X n (cen t))
    (hu : u ∈ Sec6Q X n (cen d)) (hut : u ∈ cen t) (hu2 : u ^ 2 = 1) {L : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) : u ∈ QOf L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd2' : d ^ 2 = 1 := by
    rw [← hd2]
    exact pow_orderOf_eq_one d
  have hdL : d ∈ QOf L := ctl_Q_le_QOf hL hdQ
  have hLpc := ctl_isPCompIn hL
  have hLq := ctl_isTwoGenQuasi hL
  have hPK : Sec6KComp X n (cen d ⊓ cen t) (sec6Piece L d) :=
    ctl_piece_K hd2 hL (fun _ => hdL) (fun _ => le_sup_right (a := L) hdL)
  have hPKd : sec6Piece L d ≤ Sec6K X n (cen d) :=
    (show sec6Piece L d ≤ Sec6K X n (cen d ⊓ cen t) from le_sSup hPK).trans
      (h51.sub d hd2 _ inf_le_left).1
  set P : Subgroup X := sec6Piece L d with hP
  have hPpc := ctl_isPCompIn hPK
  have hPq := ctl_isTwoGenQuasi hPK
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hcovPL : P.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hd2' hLq.1 hdL
  set D : Subgroup X := cen d ⊓ cen t with hD
  have huD : u ∈ D := ⟨hu.1, hut⟩
  have hOD : oddCoreOf (Sec6K X n (cen d)) ⊓ D ≤ oddCoreOf D :=
    le_oddCoreOf_of_normalized inf_le_right
      (fun g hg => mem_normalizer_inf
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n d hg.1))
        (Subgroup.le_normalizer hg))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨-, -, huc⟩ := hu.2
  have hPu : P.map (MulAut.conj u).toMonoidHom ≤ P := by
    refine le_of_le_sup_pPrimeCoreOf hPpc ?_ ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact D.mul_mem (D.mul_mem huD (hPpc.1 hp)) (D.inv_mem huD)
    · exact primeResidual_eq_top_of_equiv 2 (P.equivMapOfInjective _ (MulAut.conj u).injective)
        hPq.1
    · rintro _ ⟨p, hp, rfl⟩
      have h1 : ⁅p⁻¹, u⁆ ∈ oddCoreOf (Sec6K X n (cen d)) := huc _ (hPKd (P.inv_mem hp))
      have h1D : ⁅p⁻¹, u⁆ ∈ D := by
        rw [commutatorElement_def, inv_inv]
        exact D.mul_mem (D.mul_mem (D.mul_mem (D.inv_mem (hPpc.1 hp)) huD) (hPpc.1 hp))
          (D.inv_mem huD)
      have h2 : (MulAut.conj u).toMonoidHom p = p * ⁅p⁻¹, u⁆ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [h2]
      exact Subgroup.mul_mem_sup hp (hOD ⟨h1, h1D⟩)
  have huP : u ∈ normalizer (P : Set X) := ctl_mem_normalizer_of_map_le hPu
  have huQP : u ∈ QOf P := by
    refine mem_QOf_iff.2 ⟨huP, fun p hp => ?_⟩
    have h1 : ⁅p, u⁆ ∈ P := by
      have h3 : ⁅p, u⁆ = p * (u * p⁻¹ * u⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact P.mul_mem hp ((mem_normalizer_iff.1 huP p⁻¹).1 (P.inv_mem hp))
    have h2 : ⁅p, u⁆ ∈ D := by
      rw [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem (hPpc.1 hp) huD) (D.inv_mem (hPpc.1 hp)))
        (D.inv_mem huD)
    exact ctl_inf_le_oddCoreOf (fun x hx => le_normalizer_oddCoreOf D (hPpc.1 hx))
      (odd_card_oddCoreOf D) ⟨h1, hOD ⟨huc p (hPKd hp), h2⟩⟩
  set E : Subgroup X := oTwoPrimeOf (P ⊓ cen u) with hE
  have hEP : E ≤ P := (oTwoPrimeOf_le _).trans inf_le_left
  have hEu : E ≤ cen u := (oTwoPrimeOf_le _).trans inf_le_right
  have hcovEP : E.subgroupOf P ⊔ pPrimeCore 2 ↥P = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hu2 hPq.1 huQP
  have hcovEL : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff (hEP.trans hPL)]
    have h1 := (covers_subgroupOf_iff hPL).1 hcovPL
    have h2 := (covers_subgroupOf_iff hEP).1 hcovEP
    have h3 := ctl_oddCoreOf_le_of_covers hPL hcovPL
    refine le_antisymm (sup_le (hEP.trans hPL) (Subgroup.map_subtype_le _)) ?_
    calc L = P ⊔ pPrimeCoreOf 2 L := h1.symm
      _ ≤ E ⊔ pPrimeCoreOf 2 L :=
          sup_le (h2.symm.le.trans (sup_le le_sup_left (h3.trans le_sup_right))) le_sup_right
  have hEq : IsTwoGenQuasi ↥E :=
    isTwoGenQuasi_of_covers (hEP.trans hPL) hcovEL (primeResidual_oTwoPrimeOf _) hLq
  exact mem_centralizerSection_of_covers (Subgroup.mem_centralizer_singleton_iff.1 hut) hLpc
    (hEP.trans hPL) hEu hEq hcovEL

private theorem ctl_caseC2
    (hM : McLCentAutSq) {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x)
    {b : X} (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2)
    {F : Subgroup X} (hF : Sec5Comp X n (cen b) F) (htN : t ∉ normalizer (F : Set X))
    (hcommY : ∀ y ∈ F ⊔ F.map (MulAut.conj t).toMonoidHom, ∀ L : Subgroup X,
      Sec6KComp X n (cen t) L → ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b))
    {y : X} (hyF : y ∈ F) (hy8 : y ^ (2 ^ 3) = 1) (hx2O : (y ^ 2) ^ 2 ∉ oddCoreOf F)
    (hx2Q : (y ^ 2) ^ 2 ∈ QOf F)
    (hid : (y ^ 2) ^ 2 * (t * (y ^ 2) ^ 2 * t⁻¹) ∈
      oddCoreOf (F ⊔ F.map (MulAut.conj t).toMonoidHom)) : False := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn8 : 8 ≤ n := hS.maxdeg.1
  have hbt := ctl_MQ_le_cen n t hb
  have htb : t ∈ cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hFK : Sec6KComp X n (cen b) F := Or.inl hF
  have hFpc := ctl_isPCompIn hFK
  have hne : F ≠ F.map (MulAut.conj t).toMonoidHom :=
    fun h => htN (mem_normalizer_of_map_conj_eq h.symm)
  obtain ⟨d₁, ⟨hd₁Y, hd₁t⟩, hd₁8, hd₁z⟩ := ctl_diag_basic ht2 htb hFpc hne hyF hy8
  have hF'pc : IsPCompIn 2 (cen b) (F.map (MulAut.conj t).toMonoidHom) :=
    ctl_isPCompIn_conj hFpc (Subgroup.le_normalizer htb)
  obtain ⟨-, hOFY, hOYQ⟩ := ctl_pair hFpc hF'pc
  have hOYQ' : oddCoreOf (F ⊔ F.map (MulAut.conj t).toMonoidHom) ≤
      QOf (F.map (MulAut.conj t).toMonoidHom) := by
    have h1 := (ctl_pair hF'pc hFpc).2.2
    rwa [sup_comm] at h1
  set F' : Subgroup X := F.map (MulAut.conj t).toMonoidHom with hF'
  set Y : Subgroup X := F ⊔ F' with hY
  have hYb : Y ≤ cen b := sup_le hFpc.1 hF'pc.1
  have hF'Q : F' ≤ QOf F := ctl_le_QOf_of_ne hFpc hF'pc hne
  have hFF' : F ≤ normalizer (F' : Set X) := fun f hf =>
    (mem_QOf_iff.1 (ctl_le_QOf_of_ne hF'pc hFpc (Ne.symm hne) hf)).1
  have hNY : ∀ g ∈ Y, g ∈ normalizer (oddCoreOf Y : Set X) :=
    fun g hg => le_normalizer_oddCoreOf Y hg
  have hyY : y ∈ Y := le_sup_left (b := F') hyF
  have hytF' : t * y * t⁻¹ ∈ F' := ⟨y, hyF, rfl⟩
  have hytY : t * y * t⁻¹ ∈ Y := le_sup_right (a := F) hytF'
  set x : X := y ^ 2 with hx
  have hxF : x ∈ F := F.pow_mem hyF 2
  have hxY : x ∈ Y := le_sup_left (b := F') hxF
  have hxtF' : t * x * t⁻¹ ∈ F' := ⟨x, hxF, rfl⟩
  have hxtY : t * x * t⁻¹ ∈ Y := le_sup_right (a := F) hxtF'
  have hx4 : x ^ 2 * x ^ 2 = 1 := by
    calc x ^ 2 * x ^ 2 = y ^ (2 ^ 3) := by rw [hx]; group
      _ = 1 := hy8
  set d : X := d₁ ^ 2 with hd
  have hdQ : d ∈ Sec6Q X n (cen t) :=
    ctl_step0 hM (ctl_actsThrough_of_mem hb) hb2 hd₁t (hYb hd₁Y) (hcommY d₁ hd₁Y)
  have hdY : d ∈ Y := Y.pow_mem hd₁Y 2
  have hdt : d ∈ cen t := hdQ.1
  have hdx : (x * (t * x * t⁻¹))⁻¹ * d ∈ oddCoreOf Y := by
    have h1 := ctl_sq_mem (hNY y hyY) (hNY _ hytY)
      (hOFY (ctl_commutatorElement_mem hFpc hF'pc hne hyF hytF')) hd₁z
    rwa [conj_pow] at h1
  have hd2O : d ^ 2 ∈ oddCoreOf Y := by
    have h1 := ctl_sq_mem (hNY x hxY) (hNY _ hxtY)
      (hOFY (ctl_commutatorElement_mem hFpc hF'pc hne hxF hxtF')) hdx
    rw [conj_pow] at h1
    have h2 : d ^ 2 = (x ^ 2 * (t * x ^ 2 * t⁻¹)) * ((x ^ 2 * (t * x ^ 2 * t⁻¹))⁻¹ * d ^ 2) := by
      group
    rw [h2]
    exact (oddCoreOf Y).mul_mem hid h1
  have hd4 : (d ^ 2) ^ (2 ^ 1) = 1 := by
    calc (d ^ 2) ^ (2 ^ 1) = d₁ ^ (2 ^ 3) := by rw [hd]; group
      _ = 1 := hd₁8
  have hd2 : d ^ 2 = 1 := ctl_eq_one_of_twoElt (odd_card_oddCoreOf Y) hd2O hd4
  have hxd : x⁻¹ * d ∈ QOf F := by
    have h1 : x⁻¹ * d = (t * x * t⁻¹) * ((x * (t * x * t⁻¹))⁻¹ * d) := by group
    rw [h1]
    exact (QOf F).mul_mem (hF'Q hxtF') (hOYQ hdx)
  have hd1 : d ≠ 1 := by
    intro h
    have hxQ : x⁻¹ ∈ QOf F := by
      have h1 := hxd
      rwa [h, mul_one] at h1
    have hxQ' : x ∈ QOf F := by
      have h1 := (QOf F).inv_mem hxQ
      rwa [inv_inv] at h1
    exact hx2O (ctl_sq_mem_of_QOf hF.2 hxF hxQ')
  have hdo : orderOf d = 2 := orderOf_eq_prime hd2 hd1
  have hdN : d ∈ normalizer (F : Set X) := by
    have h1 := mul_mem (Subgroup.le_normalizer hxF) (ctl_QOf_le_normalizer F hxd)
    rwa [mul_inv_cancel_left] at h1
  have hdNO : d ∈ normalizer (pPrimeCoreOf 2 F : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hdN
  have hdb : d ∈ cen b := hYb hdY
  have hbd : b ∈ cen d :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hdb).symm
  have hbAd : Sec6ActsThrough X n d b :=
    ctl_actsThrough_of_Q hdo hdQ (h61a d hdQ hdo) hbd (ctl_actsThrough_of_mem hb)
  have hlandd : ∀ L : Subgroup X, Sec6KComp X n (cen d) L →
      ∃ J : Subgroup X, Sec6KComp X n (cen b) J ∧ sec6Piece L b ≤ J ∧ J ≠ F := by
    intro L hL
    have hPK : Sec6KComp X n (cen b ⊓ cen d) (sec6Piece L b) :=
      ctl_piece_K hb2 hL (hbAd.1 L) (hbAd.2 L)
    obtain ⟨J, hJ, hPJ⟩ := ctl_lift hS.cex h51.b hb2 inf_le_left hPK
    refine ⟨J, hJ, hPJ, fun hJF => ?_⟩
    have hPF : sec6Piece L b ≤ F := hJF ▸ hPJ
    have hPd : sec6Piece L b ≤ cen d :=
      (oTwoPrimeOf_le _).trans (inf_le_left.trans (ctl_isPCompIn hL).1)
    have hcard : Nat.card (↥F ⧸ pPrimeCore 2 ↥F) ≤
        Nat.card (↥(sec6Piece L b) ⧸ pPrimeCore 2 ↥(sec6Piece L b)) := by
      rcases hPK with h5 | h6
      · exact le_of_eq ((ctl_card_of_dc (by omega) hF.2).trans
          (ctl_card_of_dc (by omega) h5.2).symm)
      · exact (ctl_card_lt h6.2 hF.2).le
    have hFeq : sec6Piece L b ⊔ pPrimeCoreOf 2 F = F :=
      (covers_subgroupOf_iff hPF).1 (covers_of_card_le hPF hcard)
    have hdx' : d⁻¹ * x ∈ QOf F := by
      have h3 : d⁻¹ * x = (x⁻¹ * d)⁻¹ := by group
      rw [h3]
      exact (QOf F).inv_mem hxd
    have hxQ : x ∈ QOf F := by
      refine mem_QOf_iff.2 ⟨Subgroup.le_normalizer hxF, fun f hf => ?_⟩
      have hf' : f ∈ sec6Piece L b ⊔ oddCoreOf F := hFeq.symm ▸ hf
      obtain ⟨p, hp, o, ho, rfl⟩ :=
        ctl_exists_mul_of_mem_sup (fun z hz => le_normalizer_oddCoreOf F (hPF hz)) hf'
      rw [ctl_comm_mul]
      have h1 : ⁅o, x⁆ ∈ oddCoreOf F := by
        have h3 : ⁅o, x⁆ = o * (x * o⁻¹ * x⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h3]
        exact (oddCoreOf F).mul_mem ho
          ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf F hxF) o⁻¹).1
            ((oddCoreOf F).inv_mem ho))
      have h2 : ⁅p, x⁆ ∈ oddCoreOf F :=
        ctl_comm_mem (hPF hp) hdx' (Subgroup.mem_centralizer_singleton_iff.1 (hPd hp)) hdNO
      exact (oddCoreOf F).mul_mem
        ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf F (hPF hp)) _).1 h1) h2
    exact hx2O (ctl_sq_mem_of_QOf hF.2 hxF hxQ)
  have hcommF : ∀ L : Subgroup X, Sec6KComp X n (cen d) L → ∀ p ∈ sec6Piece L b, ∀ f ∈ F,
      ⁅p, f⁆ ∈ oddCoreOf (cen b) := by
    intro L hL p hp f hf
    obtain ⟨J, hJ, hPJ, hJF⟩ := hlandd L hL
    have hJpc := ctl_isPCompIn hJ
    exact pPrimeCoreOf_le_oddCoreOf hJpc.1 (isPComponent_two_iff.1 hJpc.2).1
      (ctl_commutatorElement_mem hJpc hFpc hJF (hPJ hp) hf)
  have hxfix : quotConj hdN (QuotientGroup.mk (⟨x, hxF⟩ : ↥F)) =
      QuotientGroup.mk (⟨x, hxF⟩ : ↥F) := by
    rw [ctl_quotConj_mk, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ : ⁅x, x⁻¹ * d⁆ ∈ pPrimeCoreOf 2 F := (mem_QOf_iff.1 hxd).2 x hxF
    have h1 : (conjAut hdN ⟨x, hxF⟩)⁻¹ * ⟨x, hxF⟩ = w := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut, Subgroup.coe_mk]
      rw [show (w : X) = ⁅x, x⁻¹ * d⁆ from hwe, commutatorElement_def]
      group
    rw [h1]
    exact hw
  have hxj : (QuotientGroup.mk (⟨x, hxF⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) ^ (2 ^ 2) = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h1 : (⟨x, hxF⟩ : ↥F) ^ (2 ^ 2) = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one]
      calc x ^ (2 ^ 2) = x ^ 2 * x ^ 2 := by group
        _ = 1 := hx4
    rw [h1, QuotientGroup.mk_one]
  obtain ⟨x', ⟨hx'F, hx'd⟩, -, hx'F2, hx'x⟩ := ctl_lift_fixed hd2 hdN ⟨x, hxF⟩ hxfix hxj
  have hx'xO : (x' ^ 2)⁻¹ * x ^ 2 ∈ oddCoreOf F := by
    have h1 : (QuotientGroup.mk ((⟨x', hx'F2⟩ : ↥F) ^ 2) : ↥F ⧸ pPrimeCore 2 ↥F) =
        QuotientGroup.mk ((⟨x, hxF⟩ : ↥F) ^ 2) := by
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, hx'x]
    rw [QuotientGroup.eq] at h1
    exact ⟨_, h1, by simp⟩
  have hx'2Q : x' ^ 2 ∈ Sec6Q X n (cen d) :=
    ctl_step0 hM hbAd hb2 hx'd (hFpc.1 hx'F) (fun L hL p hp => hcommF L hL p hp x' hx'F)
  set T : Subgroup X := Subgroup.zpowers t ⊔ Subgroup.zpowers d with hT
  have hTp : IsPGroup 2 ↥T := by
    have h1 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hS.choice.inv, pow_one])
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers d) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdo, pow_one])
    refine h1.to_sup_of_normal_right' h2 ?_
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_map_conj_eq
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      ← Subgroup.mem_centralizer_singleton_iff.1 hdt, mul_inv_cancel_right]
  have htY : t ∈ normalizer (Y : Set X) := by
    apply ctl_mem_normalizer_of_map_le
    rw [hY, Subgroup.map_sup, hF', ctl_map_conj_conj ht2, sup_comm]
  have hTN : T ≤ normalizer (pPrimeCoreOf 2 Y : Set X) :=
    sup_le (Subgroup.zpowers_le.2 (mem_normalizer_oddCoreOf_of_mem_normalizer htY))
      (Subgroup.zpowers_le.2 (le_normalizer_oddCoreOf Y hdY))
  have hxT : ∀ g ∈ T, ⁅x ^ 2, g⁆ ∈ pPrimeCoreOf 2 Y := by
    let S : Subgroup X :=
      { carrier := {g | g ∈ normalizer (pPrimeCoreOf 2 Y : Set X) ∧ ⁅x ^ 2, g⁆ ∈ pPrimeCoreOf 2 Y}
        mul_mem' := by
          rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
          refine ⟨mul_mem hgN hhN, ?_⟩
          rw [ctl_comm_mul_right]
          exact (pPrimeCoreOf 2 Y).mul_mem hg ((mem_normalizer_iff.1 hgN _).1 hh)
        one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
        inv_mem' := by
          rintro g ⟨hgN, hg⟩
          refine ⟨inv_mem hgN, ?_⟩
          have h1 : ⁅x ^ 2, g⁻¹⁆ = g⁻¹ * ⁅x ^ 2, g⁆⁻¹ * g⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [h1]
          exact (mem_normalizer_iff.1 (inv_mem hgN) _).1 ((pPrimeCoreOf 2 Y).inv_mem hg) }
    have htS : t ∈ S := by
      refine ⟨hTN (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)), ?_⟩
      have hxi : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right hx4
      have h1 : ⁅x ^ 2, t⁆ = x ^ 2 * (t * x ^ 2 * t⁻¹) := by
        rw [commutatorElement_def, hxi]
        group
      rw [h1]
      exact hid
    have hdS : d ∈ S := by
      refine ⟨hTN (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)), ?_⟩
      have hd' : d = x * ((t * x * t⁻¹) * ((x * (t * x * t⁻¹))⁻¹ * d)) := by group
      have hxx : ⁅x ^ 2, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        group
      have h1 : ⁅x ^ 2, t * x * t⁻¹⁆ ∈ oddCoreOf Y :=
        hOFY (ctl_commutatorElement_mem hFpc hF'pc hne (F.pow_mem hxF 2) hxtF')
      have h2 : ⁅x ^ 2, (x * (t * x * t⁻¹))⁻¹ * d⁆ ∈ oddCoreOf Y := by
        have h3 : ⁅x ^ 2, (x * (t * x * t⁻¹))⁻¹ * d⁆ =
            (x ^ 2 * ((x * (t * x * t⁻¹))⁻¹ * d) * (x ^ 2)⁻¹) *
              ((x * (t * x * t⁻¹))⁻¹ * d)⁻¹ := by
          rw [commutatorElement_def]
        rw [h3]
        exact (oddCoreOf Y).mul_mem ((mem_normalizer_iff.1 (hNY _ (Y.pow_mem hxY 2)) _).1 hdx)
          ((oddCoreOf Y).inv_mem hdx)
      rw [hd', ctl_comm_mul_right, hxx, one_mul, ctl_comm_mul_right]
      exact (mem_normalizer_iff.1 (hNY x hxY) _).1 ((oddCoreOf Y).mul_mem h1
        ((mem_normalizer_iff.1 (hNY _ hxtY) _).1 h2))
    have hTS : T ≤ S := sup_le (Subgroup.zpowers_le.2 htS) (Subgroup.zpowers_le.2 hdS)
    exact fun g hg => (hTS hg).2
  have hx2j : (x ^ 2) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact hx4
  obtain ⟨u, ⟨huY, huT⟩, hu2, hux⟩ :=
    exists_twoElt_centralizer_of_comm_mem_pgroup hTp hTN (Y.pow_mem hxY 2) hxT hx2j
  have hut : u ∈ cen t := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 huT) t
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))).symm
  have hud : u ∈ cen d := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 huT) d
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))).symm
  have hu2' : u ^ 2 = 1 := by
    rw [← pow_one 2]
    exact hu2
  have hoY : (x' ^ 2)⁻¹ * u ∈ oddCoreOf Y := by
    have h1 : (x' ^ 2)⁻¹ * u = ((x' ^ 2)⁻¹ * x ^ 2) * (u⁻¹ * x ^ 2)⁻¹ := by group
    rw [h1]
    exact (oddCoreOf Y).mul_mem (hOFY hx'xO) ((oddCoreOf Y).inv_mem hux)
  have hod : (x' ^ 2)⁻¹ * u ∈ cen d :=
    (cen d).mul_mem ((cen d).inv_mem ((cen d).pow_mem hx'd 2)) hud
  have hob : (x' ^ 2)⁻¹ * u ∈ cen b := hYb (oddCoreOf_le Y hoY)
  have ho2Q : ((x' ^ 2)⁻¹ * u) ^ 2 ∈ Sec6Q X n (cen d) := by
    refine ctl_step0 hM hbAd hb2 hod hob (fun L hL p hp => ?_)
    obtain ⟨J, hJ, hPJ, hJF⟩ := hlandd L hL
    have hJpc := ctl_isPCompIn hJ
    by_cases hJF' : J = F'
    · have hpF' : p ∈ F' := hJF' ▸ hPJ hp
      exact pPrimeCoreOf_le_oddCoreOf hF'pc.1 (isPComponent_two_iff.1 hF'pc.2).1
        ((mem_QOf_iff.1 (hOYQ' hoY)).2 p hpF')
    · exact ctl_comm_sup hJpc hFpc hF'pc hJF hJF' hFF' (hPJ hp) (oddCoreOf_le Y hoY)
  have hoQ : (x' ^ 2)⁻¹ * u ∈ Sec6Q X n (cen d) :=
    ctl_mem_of_sq_mem (odd_card_oddCoreOf Y) hoY ho2Q
  have huQd : u ∈ Sec6Q X n (cen d) := by
    have h1 := (Sec6Q X n (cen d)).mul_mem hx'2Q hoQ
    rwa [mul_inv_cancel_left] at h1
  have huQt : u ∈ Sec6Q X n (cen t) :=
    ⟨hut, ctl_mem_QOf_K hut fun L hL =>
      (mem_QOf_iff.1 (ctl_QOf_of_Qd h51 hdo hdQ huQd hut hu2' hL)).2⟩
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, inv_one, one_mul] at hux
    exact hx2O (ctl_inf_le_oddCoreOf
      (fun f hf => le_normalizer_oddCoreOf Y (le_sup_left (b := F') hf))
      (odd_card_oddCoreOf Y) ⟨F.pow_mem hxF 2, hux⟩)
  have huo : orderOf u = 2 := orderOf_eq_prime hu2' hu1
  have huF : u ∈ QOf F := by
    have h1 : u = x ^ 2 * (u⁻¹ * x ^ 2)⁻¹ := by group
    rw [h1]
    exact (QOf F).mul_mem hx2Q ((QOf F).inv_mem (hOYQ hux))
  exact htN (ctl_S1C hS h51 hbt hFK huQt huo (h61a u huQt huo) (hYb huY) huF).1

private theorem ctl_caseC
    (hM : McLCentAutSq) {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) :
    Sec6CtrlCaseC X n t := by
  intro b hb hb2 F hF
  by_contra htN
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn8 : 8 ≤ n := hS.maxdeg.1
  have hbt := ctl_MQ_le_cen n t hb
  have htb : t ∈ cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm
  have ht2 : t ^ 2 = 1 := by
    rw [← hS.choice.inv]
    exact pow_orderOf_eq_one t
  have hFpc := ctl_isPCompIn hF
  set F' : Subgroup X := F.map (MulAut.conj t).toMonoidHom with hF'
  have hne : F ≠ F' := fun h => htN (mem_normalizer_of_map_conj_eq h.symm)
  have hF'K : Sec6KComp X n (cen b) F' := ctl_KComp_conj (Subgroup.le_normalizer htb) hF
  have hF'pc := ctl_isPCompIn hF'K
  have hnoF : ∀ L, Sec6KComp X n (cen t) L → ¬ sec6Piece L b ≤ F := fun L hL hP =>
    htN (sec6Ctrl_dich hS hb hb2 hL hF hP).1
  have hnoF' : ∀ L, Sec6KComp X n (cen t) L → ¬ sec6Piece L b ≤ F' := by
    intro L hL hP
    have h1 := map_conj_eq_of_mem_normalizer (sec6Ctrl_dich hS hb hb2 hL hF'K hP).1
    rw [hF', ctl_map_conj_conj ht2] at h1
    exact hne h1
  have hFF' : F ≤ normalizer (F' : Set X) := fun f hf =>
    (mem_QOf_iff.1 (ctl_le_QOf_of_ne hF'pc hFpc (Ne.symm hne) hf)).1
  have hcommY : ∀ y ∈ F ⊔ F', ∀ L, Sec6KComp X n (cen t) L →
      ∀ p ∈ sec6Piece L b, ⁅p, y⁆ ∈ oddCoreOf (cen b) := by
    intro y hy L hL p hp
    obtain ⟨J, hJ, hPJ⟩ := sec6Ctrl_land hS h51 hb hb2 hL
    have hJF : J ≠ F := fun h => hnoF L hL (h ▸ hPJ)
    have hJF' : J ≠ F' := fun h => hnoF' L hL (h ▸ hPJ)
    have hJpc := ctl_isPCompIn hJ
    have hOJ : pPrimeCoreOf 2 J ≤ oddCoreOf (cen b) :=
      pPrimeCoreOf_le_oddCoreOf hJpc.1 (isPComponent_two_iff.1 hJpc.2).1
    obtain ⟨f, hf, f', hf', rfl⟩ := ctl_exists_mul_of_mem_sup hFF' hy
    have h1 : ⁅p, f * f'⁆ = ⁅p, f⁆ * (f * ⁅p, f'⁆ * f⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (oddCoreOf (cen b)).mul_mem (hOJ (ctl_commutatorElement_mem hJpc hFpc hJF (hPJ hp) hf))
      ((mem_normalizer_iff.1 (le_normalizer_oddCoreOf (cen b) (hFpc.1 hf)) _).1
        (hOJ (ctl_commutatorElement_mem hJpc hF'pc hJF' (hPJ hp) hf')))
  have hYb : F ⊔ F' ≤ cen b := sup_le hFpc.1 hF'pc.1
  rcases hF with h5 | h6
  ·
    obtain ⟨y, hyF, hy8, hx2O, hx2Q⟩ := ctl_exists_root hn8 h5.2
    set x : X := y ^ 2 with hx
    have hxF : x ∈ F := F.pow_mem hyF 2
    have hx4 : x ^ (2 ^ 2) = 1 := by
      calc x ^ (2 ^ 2) = y ^ (2 ^ 3) := by rw [hx]; group
        _ = 1 := hy8
    obtain ⟨d, ⟨hdY, hdt⟩, hd4, hdQ, hd1⟩ := ctl_diag ht2 htb hFpc hne hxF hx4
    by_cases hv1 : d ^ 2 = 1
    · exact ctl_caseC2 hM hS h51 h61a hb hb2 h5 htN hcommY hyF hy8 hx2O hx2Q (hd1 hv1)
    · have hvQt : d ^ 2 ∈ Sec6Q X n (cen t) :=
        ctl_step0 hM (ctl_actsThrough_of_mem hb) hb2 hdt (hYb hdY) (hcommY d hdY)
      have hv2 : orderOf (d ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hd4) hv1
      have hvF : d ^ 2 ∈ QOf F := by
        have h1 : d ^ 2 = x ^ 2 * ((x ^ 2)⁻¹ * d ^ 2) := by group
        rw [h1]
        exact (QOf F).mul_mem hx2Q hdQ
      exact htN (ctl_S1C hS h51 hbt (Or.inl h5) hvQt hv2 (h61a _ hvQt hv2)
        (hYb ((F ⊔ F').pow_mem hdY 2)) hvF).1
  ·
    have hFq := ctl_isTwoGenQuasi (Or.inr h6 : Sec6KComp X n (cen b) F)
    have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ := mcLLyCenterFree _ h6.1.2.1
    obtain ⟨w, hwF, hw⟩ := ctl_exists_involution hFq
    have hCdc := ctl_cent_dc h6.2 (ctl_orderOf_mk hwF hw)
    obtain ⟨k₀, hk2, hkz⟩ := ctl_dc_sqrt_center hn8 hCdc
    have hk4 := ctl_sq_sq_of_center hCdc.2.1 hkz
    obtain ⟨k, hk2', hk4'⟩ : ∃ k : ↥F ⧸ pPrimeCore 2 ↥F, k * k ≠ 1 ∧ k * k * (k * k) = 1 :=
      ⟨k₀, fun h => hk2 (Subtype.ext (by rw [Subgroup.coe_mul, h, Subgroup.coe_one])),
        by
          have := congrArg Subtype.val hk4
          simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
          exact this⟩
    obtain ⟨x, hxF, hx4, hxF', hxk⟩ := ctl_lift_ord4 hk2' hk4'
    have hx2k : (QuotientGroup.mk (⟨x ^ 2, F.pow_mem hxF 2⟩ : ↥F) : ↥F ⧸ pPrimeCore 2 ↥F) =
        k * k := by
      rw [← hxk, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (pow_two x)
    have hx2Q : x ^ 2 ∉ QOf F := by
      intro h
      apply hk2'
      rw [← hx2k, QuotientGroup.eq_one_iff]
      have h1 := ctl_mem_of_central hZ (F.pow_mem hxF 2) (mem_QOf_iff.1 h).2
      obtain ⟨w', hw', hw'e⟩ := h1
      have : (⟨x ^ 2, F.pow_mem hxF 2⟩ : ↥F) = w' := Subtype.ext hw'e.symm
      rw [this]
      exact hw'
    obtain ⟨d, ⟨hdY, hdt⟩, hd4, hdQ, -⟩ := ctl_diag ht2 htb hFpc hne hxF hx4
    have hvQt : d ^ 2 ∈ Sec6Q X n (cen t) := ctl_step0 hM (ctl_actsThrough_of_mem hb) hb2 hdt
        (hYb hdY) (hcommY d hdY)
    have hvnQ : d ^ 2 ∉ QOf F := by
      intro h
      apply hx2Q
      have h1 : x ^ 2 = d ^ 2 * ((x ^ 2)⁻¹ * d ^ 2)⁻¹ := by group
      rw [h1]
      exact (QOf F).mul_mem h ((QOf F).inv_mem hdQ)
    have hv1 : d ^ 2 ≠ 1 := fun h => hvnQ (h ▸ one_mem _)
    have hv2 : orderOf (d ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hd4) hv1
    have hvFQ : d ^ 2 ∈ F ⊔ QOf F :=
      (sup_le_sup_left (ctl_le_QOf_of_ne hFpc hF'pc hne) F) ((F ⊔ F').pow_mem hdY 2)
    have hEK : Sec6KComp X n (cen (d ^ 2) ⊓ cen b) (sec6Piece F (d ^ 2)) :=
      Or.inl (ctl_piece_M_inner hv2 h6 hvFQ hvnQ)
    exact htN (ctl_S1N hS h51 hbt (Or.inr h6) hvQt hv2 (h61a _ hvQt hv2) hEK)

end CaseC

section McLFact

private theorem ctl_dvd_of_index_le_two {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : H.index ≤ 2) {m : ℕ} (hm : 2 * m ∣ Nat.card G) : m ∣ Nat.card H := by
  have h1 := H.card_mul_index
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨j, hj⟩ := hm
  rcases (by omega : H.index = 1 ∨ H.index = 2) with hi | hi
  · rw [hi, mul_one] at h1
    exact ⟨2 * j, by rw [h1, hj]; ring⟩
  · rw [hi] at h1
    exact ⟨j, by rw [hj] at h1; linarith⟩

private theorem ctl_index_ker_le_two {G G' : Type} [Group G] [Group G'] [Finite G']
    (f : G →* G') (hG' : Nat.card G' ≤ 2) : f.ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  exact (Subgroup.card_le_card_group _).trans hG'

private theorem ctl_card_cent_s8 :
    Nat.card ↥(centralizer ({Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3} :
      Set (Equiv.Perm (Fin 8)))) = 192 := by
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 8) 1) (Equiv.swap 2 3) :=
    Equiv.Perm.disjoint_swap_swap (by decide)
  have hct : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3).cycleType = {2, 2} := by
    rw [hdisj.cycleType_mul, (Equiv.Perm.isCycle_swap (by decide)).cycleType,
      (Equiv.Perm.isCycle_swap (by decide)).cycleType, Equiv.Perm.card_support_swap (by decide),
      Equiv.Perm.card_support_swap (by decide)]
    rfl
  rw [Equiv.Perm.nat_card_centralizer, hct]
  decide

private theorem ctl_card_cent_a8 :
    32 ∣ Nat.card ↥(centralizer ({Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3} :
      Set (Equiv.Perm (Fin 8))) ⊓ alternatingGroup (Fin 8)) := by
  set C : Subgroup (Equiv.Perm (Fin 8)) :=
    centralizer ({Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3} : Set (Equiv.Perm (Fin 8))) with hC
  set f : ↥C →* ℤˣ := Equiv.Perm.sign.comp C.subtype with hf
  have hker : f.ker.map C.subtype = C ⊓ alternatingGroup (Fin 8) := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, hf, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxC, hx⟩
      exact ⟨⟨x, hxC⟩, hx, rfl⟩
  have h1 : 32 ∣ Nat.card f.ker := by
    refine ctl_dvd_of_index_le_two f.ker (ctl_index_ker_le_two f ?_) ?_
    · rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    · rw [ctl_card_cent_s8]
      norm_num
  rw [← hker, Subgroup.card_map_of_injective C.subtype_injective]
  exact h1

private theorem ctl_dc8_sqrt {K : Type} [Group K] [Finite K] (hK : IsDoubleCoverOfAlt K 8) :
    ∃ k : K, k * k ≠ 1 ∧ k * k ∈ center K ∧ 32 ∣ Nat.card ↥(centralizer ({k} : Set K)) := by
  set C : AhatData.CoverSetup 8 K := AhatData.CoverSetup.ofCover hK with hCdef
  set σ : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3 with hσ
  have hsign : Equiv.Perm.sign σ = 1 := by decide
  obtain ⟨k, hk⟩ := C.exists_ρ_eq hsign
  have hk2 : k * k ≠ 1 := C.sq_dbl_ne_one (by norm_num)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hk
  have hσ2 : σ * σ = 1 := by decide
  have hkz : k * k ∈ center K := C.sq_mem_center (by rw [hk]; exact hσ2)
  refine ⟨k, hk2, hkz, ?_⟩
  set T : Subgroup K := (centralizer ({σ} : Set (Equiv.Perm (Fin 8)))).comap C.ρ with hT
  set g : ↥T →* Equiv.Perm (Fin 8) := C.ρ.comp T.subtype with hg
  have hrange :
      g.range = centralizer ({σ} : Set (Equiv.Perm (Fin 8))) ⊓ alternatingGroup (Fin 8) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.2, Equiv.Perm.mem_alternatingGroup.2 (C.sign_ρ y)⟩
    · rintro ⟨hxC, hxA⟩
      obtain ⟨y, hy⟩ := C.exists_ρ_eq (Equiv.Perm.mem_alternatingGroup.1 hxA)
      have hyT : y ∈ T := by
        show C.ρ y ∈ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))
        rw [hy]
        exact hxC
      exact ⟨⟨y, hyT⟩, hy⟩
  have hkerc : Nat.card g.ker = 2 := by
    have hk' : g.ker.map T.subtype = center K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact C.ρ_eq_one_iff.1 hy
      · intro hx
        have hxT : x ∈ T := by
          show C.ρ x ∈ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))
          rw [C.ρ_eq_one_iff.2 hx]
          exact one_mem _
        exact ⟨⟨x, hxT⟩, C.ρ_eq_one_iff.2 hx, rfl⟩
    rw [← Subgroup.card_map_of_injective T.subtype_injective, hk']
    exact hK.2.1
  have hT64 : 2 * 32 ∣ Nat.card T := by
    have h1 := g.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hkerc] at h1
    rw [← h1]
    exact Nat.mul_dvd_mul_left 2 ctl_card_cent_a8
  have hCT : centralizer ({k} : Set K) ≤ T := by
    intro x hx
    show C.ρ x ∈ centralizer ({σ} : Set (Equiv.Perm (Fin 8)))
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← hk, ← map_mul, ← map_mul, hx]
  have hcz : ∀ y : ↥T, ⁅(y : K), k⁆ ∈ center K := by
    intro y
    rw [← C.ρ_eq_one_iff, map_commutatorElement, hk, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  let φ : ↥T →* ↥(center K) :=
    { toFun := fun y => ⟨⁅(y : K), k⁆, hcz y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 : ⁅(a : K) * b, k⁆ = (a : K) * ⁅(b : K), k⁆ * (a : K)⁻¹ * ⁅(a : K), k⁆ := by
          simp only [commutatorElement_def]
          group
        have hb' : (a : K) * ⁅(b : K), k⁆ * (a : K)⁻¹ = ⁅(b : K), k⁆ := by
          rw [Subgroup.mem_center_iff.1 (hcz b) (a : K), mul_inv_cancel_right]
        rw [h1, hb']
        exact Subgroup.mem_center_iff.1 (hcz a) _ }
  have hφker : φ.ker.map T.subtype = centralizer ({k} : Set K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : ⁅(y : K), k⁆ = 1 := congrArg Subtype.val hy
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact Subgroup.mem_centralizer_singleton_iff.2 h1
    · intro hx
      refine ⟨⟨x, hCT hx⟩, ?_, rfl⟩
      apply Subtype.ext
      show ⁅x, k⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.1 hx
  have h2 : 32 ∣ Nat.card φ.ker := by
    refine ctl_dvd_of_index_le_two φ.ker (ctl_index_ker_le_two φ ?_) hT64
    rw [hK.2.1]
  rw [← hφker, Subgroup.card_map_of_injective T.subtype_injective]
  exact h2

private theorem ctl_zpowers_inv {G : Type} [Group G] {v g : G} (hv : v * v = 1)
    (hg : g ∈ Subgroup.zpowers v) : g = 1 ∨ g = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  rw [zpow_eq_zpow_emod k hv2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem mclCentAutSq :
    McLCentAutSq := by
  intro Q _ he ψ v hv hfix
  obtain ⟨e⟩ := he
  have hQcard : Nat.card Q = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
  obtain ⟨hperf, hZ, hq⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
      ⟨e⟩ hv
  have hKdc : IsDoubleCoverOfAlt ↥(centralizer ({v} : Set Q)) 8 :=
    isDoubleCoverOfAlt_of_cover hv (by norm_num) hperf hZ hq
  have hcentK : ∀ g : Q, (∀ x : Q, x * v = v * x → g * x * g⁻¹ = x) → g = 1 ∨ g = v := by
    intro g hg
    have hgv : g ∈ centralizer ({v} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hg v rfl
      calc g * v = g * v * g⁻¹ * g := by group
        _ = v * g := by rw [h1]
    have hgZ : (⟨g, hgv⟩ : ↥(centralizer ({v} : Set Q))) ∈ center ↥(centralizer ({v} : Set Q)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := hg y (Subgroup.mem_centralizer_singleton_iff.1 y.2)
      show (y : Q) * g = g * y
      calc (y : Q) * g = g * y * g⁻¹ * g := by rw [h1]
        _ = g * y := by group
    rw [hZ] at hgZ
    have hv2' : (⟨v, self_mem_centralizer v⟩ : ↥(centralizer ({v} : Set Q))) *
        ⟨v, self_mem_centralizer v⟩ = 1 := Subtype.ext hv2
    rcases ctl_zpowers_inv hv2' hgZ with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h
  by_cases hin : ψ ∈ ComponentClassification.OuterAutomorphisms.inner Q
  · obtain ⟨g, rfl⟩ := hin
    have hg : ∀ x : Q, x * v = v * x → g * x * g⁻¹ = x := fun x hx => hfix x hx
    rcases hcentK g hg with h | h
    · rw [h, map_one, one_mul]
    · rw [h, ← map_mul, hv2, map_one]
  · exfalso
    have hOut : Nat.card (ComponentClassification.OuterAutomorphisms.Outer Q) = 2 := by
      rw [Nat.card_congr (@ComponentClassification.OuterAutomorphisms.equivalence Q
        Blueprint.NativeSporadic.McL _ inferInstance e).toEquiv]
      exact CFSG.Sporadic.Recognition.McLAS.card_outer_mcl
    have hsq : ψ * ψ ∈ ComponentClassification.OuterAutomorphisms.inner Q := by
      have h1 := orderOf_dvd_natCard
        (QuotientGroup.mk ψ : ComponentClassification.OuterAutomorphisms.Outer Q)
      rw [hOut] at h1
      have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two] at h2
      exact h2
    obtain ⟨g, hg⟩ := hsq
    have hgfix : ∀ x : Q, x * v = v * x → g * x * g⁻¹ = x := by
      intro x hx
      have h1 := congrArg (fun φ : MulAut Q => φ x) hg
      simp only [MulAut.conj_apply, MulAut.mul_apply] at h1
      rw [h1, hfix x hx, hfix x hx]
    rcases hcentK g hgfix with hg1 | hgv
    ·
      have hψ2 : ψ * ψ = 1 := by rw [← hg, hg1, map_one]
      have hout : ¬ ∃ g' : Q, ψ = MulAut.conj g' := fun ⟨g', hg'⟩ => hin ⟨g', hg'.symm⟩
      obtain ⟨Φ⟩ := ctl_fixed_M11 e ψ hψ2 hout
      have hle : centralizer ({v} : Set Q) ≤ CFSG.Sporadic.Recognition.McLAS.fixedSubgroup ψ :=
        fun x hx => (ctl_mem_fixedSubgroup ψ x).2
            (hfix x (Subgroup.mem_centralizer_singleton_iff.1 hx))
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Nat.card_congr Φ.toEquiv, CFSG.Sporadic.Mathieu.card_M11,
        ctl_card_of_dc (by norm_num) hKdc] at h1
      norm_num [Nat.factorial] at h1
    ·
      obtain ⟨k₀, hk2, hkz, hk32⟩ := ctl_dc8_sqrt hKdc
      have hkv : (k₀ : Q) * k₀ = v := by
        rw [hZ] at hkz
        have hv2' : (⟨v, self_mem_centralizer v⟩ : ↥(centralizer ({v} : Set Q))) *
            ⟨v, self_mem_centralizer v⟩ = 1 := Subtype.ext hv2
        rcases ctl_zpowers_inv hv2' hkz with h | h
        · exact absurd h hk2
        · exact congrArg Subtype.val h
      set k : Q := (k₀ : Q) with hk
      have hψk : ψ k = k := hfix k (Subgroup.mem_centralizer_singleton_iff.1 k₀.2)
      set τ : MulAut Q := ψ * (MulAut.conj k)⁻¹ with hτ
      have hτapp : ∀ x, τ x = ψ (k⁻¹ * x * k) := by
        intro x
        rw [hτ, MulAut.mul_apply, MulAut.conj_inv_apply]
      have hψψ : ∀ x, ψ (ψ x) = v * x * v⁻¹ := by
        intro x
        have h1 := congrArg (fun φ : MulAut Q => φ x) hg
        rw [hgv] at h1
        simp only [MulAut.conj_apply, MulAut.mul_apply] at h1
        exact h1.symm
      have hτ2 : τ * τ = 1 := by
        ext x
        rw [MulAut.mul_apply, hτapp, hτapp, MulAut.one_apply, map_mul, map_mul, map_inv,
          hψk, hψψ, ← hkv]
        group
      have hτout : ¬ ∃ g' : Q, τ = MulAut.conj g' := by
        rintro ⟨g', hg'⟩
        apply hin
        refine ⟨g' * k, ?_⟩
        rw [map_mul, ← hg', hτ, inv_mul_cancel_right]
      obtain ⟨Φ⟩ := ctl_fixed_M11 e τ hτ2 hτout
      have hle : (centralizer ({k₀} : Set ↥(centralizer ({v} : Set Q)))).map
          (centralizer ({v} : Set Q)).subtype ≤
          CFSG.Sporadic.Recognition.McLAS.fixedSubgroup τ := by
        rintro _ ⟨y, hy, rfl⟩
        rw [ctl_mem_fixedSubgroup, hτapp]
        have hyk : (y : Q) * k = k * y :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
        have h1 : k⁻¹ * (y : Q) * k = y := by
          rw [mul_assoc, hyk, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [Subgroup.coe_subtype, h1]
        exact hfix y (Subgroup.mem_centralizer_singleton_iff.1 y.2)
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective (centralizer ({v} : Set Q)).subtype_injective,
        Nat.card_congr Φ.toEquiv, CFSG.Sporadic.Mathieu.card_M11] at h1
      have h2 := hk32.trans h1
      norm_num at h2

end McLFact

structure Sec6CtrlCases (X : Type) [Group X] (n : ℕ) (t : X) : Prop where
  caseC : ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ F : Subgroup X, Sec6KComp X n (cen b) F → t ∈ normalizer (F : Set X)
  caseA : ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ F : Subgroup X, Sec5Comp X n (cen b) F → t ∈ normalizer (F : Set X) → CentModOdd F t
  caseB : n = 8 → ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ F : Subgroup X, Sec6MComp X n (cen b) F → t ∈ normalizer (F : Set X) →
      ∃ f ∈ F, CentModOdd F (f * t)

theorem sec6Ctrl_piece_of_cases
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (h51 : Sec6Lemma51 X n) (hC : Sec6CtrlCases X n t) {b : X}
    (hb : b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hb2 : orderOf b = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen b) F) :
    ∃ L : Subgroup X, Sec6KComp X n (cen t) L ∧ sec6Piece L b ≤ F := by
  have htN := hC.caseC b hb hb2 F hF
  refine ctl_piece_ctrl hS h51 hb hb2 hF htN ?_
  by_cases hcent : CentModOdd F t
  · exact Or.inl hcent
  · right
    rcases hF with h5 | h6
    · exact absurd (hC.caseA b hb hb2 F h5 htN) hcent
    · refine ⟨h6, ?_⟩
      rcases h6.2 with ⟨hn, -⟩ | ⟨-, he⟩
      · exact hC.caseB hn b hb hb2 F h6 htN
      · exact ctl_inner_ly htN he

theorem sec6CtrlAt_of_cases
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n) (hC : Sec6CtrlCases X n t) :
    Sec6CtrlAt X n t where
  land b hb hb2 L hL := sec6Ctrl_land hS h51 hb hb2 hL
  piece b hb hb2 F hF := sec6Ctrl_piece_of_cases hS h51 hC hb hb2 hF
  dich b hb hb2 L F hL hF hPF := sec6Ctrl_dich hS hb hb2 hL hF hPF

theorem sec6CtrlHolds_of_cases
    (h : ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), Sec6Setting X n t → Sec6Lemma51 X n → (∀
        x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) → Sec6CtrlCases X n
        t) : Sec6CtrlHolds :=
  fun X _ _ n t hS h51 h61a => sec6CtrlAt_of_cases hS h51 (h X n t hS h51 h61a)


theorem sec6CtrlCases_of_caseC
    (hM : McLCentAutSq) {X : Type} [Group X] [Finite X] {n : ℕ}
    {t : X} (hS : Sec6Setting X n t) (h51 : Sec6Lemma51 X n)
    (h61a : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x)
    (hC : Sec6CtrlCaseC X n t) : Sec6CtrlCases X n t where
  caseC := hC
  caseA b hb hb2 F hF htN := ctl_caseA hM hS h51 h61a hb hb2 hF htN
  caseB _ b hb hb2 F hF htN := ctl_caseB hM hS h51 h61a hb hb2 hF htN

theorem sec6CtrlHolds_of_caseC
    (hM : McLCentAutSq) (hC : ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), Sec6Setting X n t →
        Sec6Lemma51 X n → (∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) →
        Sec6CtrlCaseC X n t) :
    Sec6CtrlHolds :=
  sec6CtrlHolds_of_cases fun X _ _ n t hS h51 h61a =>
    sec6CtrlCases_of_caseC hM hS h51 h61a (hC X n t hS h51 h61a)

theorem sec6CtrlHolds :
    Sec6CtrlHolds :=
  sec6CtrlHolds_of_caseC mclCentAutSq fun _ _ _ _ _ hS h51 h61a =>
    ctl_caseC mclCentAutSq hS h51 h61a

end CFSG.OddStandard.Solomon75
