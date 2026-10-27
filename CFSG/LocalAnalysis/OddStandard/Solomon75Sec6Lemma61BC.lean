module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Count
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Restrict
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Toolkit

variable {X : Type} [Group X] [Finite X]

private theorem bc_sq {g : X} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

private theorem bc_mul_self {g : X} (hg : orderOf g = 2) : g * g = 1 := by
  rw [← sq]
  exact bc_sq hg

private theorem bc_comm_of_mem_cen {a b : X} (h : a ∈ cen b) : a * b = b * a :=
  Subgroup.mem_centralizer_singleton_iff.1 h

private theorem bc_mem_cen_symm {a b : X} (h : a ∈ cen b) : b ∈ cen a :=
  Subgroup.mem_centralizer_singleton_iff.2 (bc_comm_of_mem_cen h).symm

private theorem bc_conj_mem {S : Subgroup X} {c h : X} (hc : c ∈ normalizer (S : Set X))
    (hh : h ∈ S) : c * h * c⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 hc h).1 hh

private theorem bc_comm_mem_of_mem {O : Subgroup X} {o g : X} (ho : o ∈ O)
    (hg : g ∈ normalizer (O : Set X)) : ⁅o, g⁆ ∈ O := by
  have : ⁅o, g⁆ = o * (g * o⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [this]
  exact O.mul_mem ho (bc_conj_mem hg (O.inv_mem ho))

private theorem bc_not_mem_of_odd {Y : Type*} [Group Y] {O : Subgroup Y} (hO : Odd (Nat.card O))
    {g : Y} (hg : orderOf g = 2) : g ∉ O := by
  intro hgO
  have h1 : orderOf (⟨g, hgO⟩ : ↥O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hg] at h1
  exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h1)

private def bcComm (N : Subgroup X) (g : X) : Subgroup X where
  carrier := {k | k ∈ normalizer (N : Set X) ∧ ⁅k, g⁆ ∈ N}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h : ⁅a * b, g⁆ = a * ⁅b, g⁆ * a⁻¹ * ⁅a, g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact N.mul_mem (bc_conj_mem ha hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have h : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact bc_conj_mem (inv_mem ha) (N.inv_mem ha')

private theorem bc_mem_bcComm {N : Subgroup X} {g k : X} (hk : k ∈ normalizer (N : Set X))
    (hkg : ⁅k, g⁆ ∈ N) : k ∈ bcComm N g :=
  ⟨hk, hkg⟩

private theorem bc_centModOdd_of_cover {F R : Subgroup X} {g : X} (hRF : R ≤ F)
    (hcov : F = oddCoreOf F ⊔ R) (hgO : g ∈ normalizer (oddCoreOf F : Set X))
    (hR : ∀ r ∈ R, ⁅r, g⁆ ∈ oddCoreOf F) : CentModOdd F g := by
  have hle : oddCoreOf F ⊔ R ≤ bcComm (oddCoreOf F) g := by
    refine sup_le (fun o ho => bc_mem_bcComm (le_normalizer ho) (bc_comm_mem_of_mem ho hgO))
      (fun r hr => bc_mem_bcComm (le_normalizer_oddCoreOf F (hRF hr)) (hR r hr))
  intro a ha
  have ha' : a ∈ oddCoreOf F ⊔ R := by
    rw [← hcov]
    exact ha
  exact (hle ha').2

private theorem bc_cov {E K : Subgroup X} (hEK : E ≤ K)
    (hcov : E.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) : K = oddCoreOf K ⊔ E :=
  ((covers_subgroupOf_iff hEK).1 hcov).symm.trans (sup_comm _ _)

private theorem bc_oddCoreOf_le_of_cov {F K : Subgroup X} (hFK : F ≤ K)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) : oddCoreOf F ≤ oddCoreOf K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hN : ((pPrimeCore 2 ↥F).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hcard : Nat.card ((pPrimeCore 2 ↥F).map φ) ∣ Nat.card (pPrimeCore 2 ↥F) :=
    Subgroup.card_map_dvd _ _
  have hle : (pPrimeCore 2 ↥F).map φ ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
    le_sSup ⟨hN, Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card⟩
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
  rintro _ ⟨a, ha, rfl⟩
  have h2 : φ a = 1 := Subgroup.mem_bot.1 (hle ⟨a, ha, rfl⟩)
  exact ⟨Subgroup.inclusion hFK a, (QuotientGroup.eq_one_iff (Subgroup.inclusion hFK a)).1 h2,
    rfl⟩

private theorem bc_isPCompIn {n : ℕ} {H L : Subgroup X} (hL : Sec6KComp X n H L) :
    IsPCompIn 2 H L := by
  rcases hL with ⟨⟨u, hu⟩, -⟩ | ⟨hM, -⟩
  · exact hu.2.2.1
  · exact hM.1

private theorem bc_isTwoGenQuasi {H L : Subgroup X} (hL : IsPCompIn 2 H L) :
    IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff hL.1).1 (isPComponent_two_iff.1 hL.2).2

private theorem bc_le_sec6K {n : ℕ} {H L : Subgroup X} (hL : Sec6KComp X n H L) :
    L ≤ Sec6K X n H :=
  le_sSup (s := {L | Sec6KComp X n H L}) hL

private theorem bc_le_sec6M {n : ℕ} {H M : Subgroup X} (hM : Sec6MComp X n H M) :
    M ≤ Sec6M X n H :=
  le_sSup (s := {M | Sec6MComp X n H M}) hM

private theorem bc_sec6K_le {n : ℕ} {H : Subgroup X} : Sec6K X n H ≤ H := by
  unfold Sec6K
  exact sSup_le fun L hL => (bc_isPCompIn hL).1

private theorem bc_sec6M_le {n : ℕ} {H : Subgroup X} : Sec6M X n H ≤ H := by
  unfold Sec6M
  exact sSup_le fun L hL => hL.1.1.1

private theorem bc_conj_mem' {M : Subgroup X} {g : X} (hg : ∀ m ∈ M, ⁅m, g⁆ ∈ M) {x : X}
    (hx : x ∈ M) : g * x * g⁻¹ ∈ M := by
  have h1 := M.mul_mem hx (hg x⁻¹ (M.inv_mem hx))
  have h2 : x * ⁅x⁻¹, g⁆ = g * x * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rwa [h2] at h1

private theorem bc_mem_normalizer {M : Subgroup X} {j : X} (h : ∀ m ∈ M, ⁅m, j⁆ ∈ M)
    (h' : ∀ m ∈ M, ⁅m, j⁻¹⁆ ∈ M) : j ∈ normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨bc_conj_mem' h, fun hx => ?_⟩
  have := bc_conj_mem' h' hx
  rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at this

private theorem bc_comm_mem {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {m j : X} (hm : m ∈ M) (hj : j ∈ J) :
    ⁅m, j⁆ ∈ oddCoreOf M := by
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

private theorem bc_mem_normalizer_of_isPCompIn {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) {j : X} (hj : j ∈ J) : j ∈ normalizer (M : Set X) := by
  by_cases hMJ : M = J
  · subst hMJ
    exact le_normalizer hj
  · exact bc_mem_normalizer (fun m hm => oddCoreOf_le M (bc_comm_mem hM hJ hMJ hm hj))
      (fun m hm => oddCoreOf_le M (bc_comm_mem hM hJ hMJ hm (J.inv_mem hj)))

private theorem bc_mem_centralizerSection {H M J : Subgroup X} (hM : IsPCompIn 2 H M)
    (hJ : IsPCompIn 2 H J) (hne : M ≠ J) {j : X} (hj : j ∈ J) :
    j ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
  ⟨bc_mem_normalizer_of_isPCompIn hM hJ hj,
    mem_normalizer_oddCoreOf_of_mem_normalizer (bc_mem_normalizer_of_isPCompIn hM hJ hj),
    fun _ hm => bc_comm_mem hM hJ hne hm hj⟩

private theorem bc_sec6K_le_normalizer {n : ℕ} {H G : Subgroup X} (hG : Sec6KComp X n H G) :
    Sec6K X n H ≤ normalizer (G : Set X) := by
  unfold Sec6K
  exact sSup_le fun J hJ _ hj =>
    bc_mem_normalizer_of_isPCompIn (bc_isPCompIn hG) (bc_isPCompIn hJ) hj

private theorem bc_oddCoreOf_le_oddCoreOf_sec6K {n : ℕ} {b : X} {F : Subgroup X}
    (hF : Sec6KComp X n (cen b) F) : oddCoreOf F ≤ oddCoreOf (Sec6K X n (cen b)) := by
  have hFK : F ≤ Sec6K X n (cen b) := bc_le_sec6K hF
  have hpc := bc_isPCompIn hF
  have h1 : oddCoreOf F ≤ oddCoreOf (cen b) :=
    pPrimeCoreOf_le_oddCoreOf hpc.1 (isPComponent_two_iff.1 hpc.2).1
  have h2 : oddCoreOf (cen b) ⊓ Sec6K X n (cen b) ≤ oddCoreOf (Sec6K X n (cen b)) := by
    refine le_oddCoreOf_of_normalized inf_le_right (fun k hk => ?_)
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    exact mem_normalizer_inf (le_normalizer_oddCoreOf _ (bc_sec6K_le hk)) (le_normalizer hk)
  exact (le_inf h1 ((oddCoreOf_le F).trans hFK)).trans h2

private theorem bc_mem_normalizer_oTwoPrimeOf {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : g ∈ normalizer (oTwoPrimeOf H : Set X) :=
  oTwoPrimeOf_normalizes ((Subgroup.zpowers_le).2 hg) (Subgroup.mem_zpowers g)

end Toolkit

theorem sec6Covers_of_forall_centModOdd {X : Type} [Group X] [Finite X] {n : ℕ} {t x : X}
    (hC : Sec6CtrlAt X n t) (hx : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t))
    (hx2 : orderOf x = 2) (h : ∀ F, Sec6KComp X n (cen x) F → CentModOdd F t) :
    Sec6Covers X n t x := by
  unfold Sec6Covers
  refine le_antisymm ?_ (sup_le (oddCoreOf_le _) inf_le_left)
  have hK : Sec6K X n (cen x) = sSup {L | Sec6KComp X n (cen x) L} := rfl
  calc Sec6K X n (cen x) = sSup {L | Sec6KComp X n (cen x) L} := hK
    _ ≤ _ := by
      refine sSup_le fun F hF => ?_
      obtain ⟨L, hL, hLF⟩ := hC.piece x hx hx2 F hF
      obtain ⟨-, hd⟩ := hC.dich x hx hx2 L F hL hF hLF
      rcases hd with heq | ⟨-, hnt, -⟩
      · refine heq.le.trans (sup_le ((bc_oddCoreOf_le_oddCoreOf_sec6K hF).trans le_sup_left)
          (le_sup_of_le_right (le_inf (hLF.trans (bc_le_sec6K hF)) ?_)))
        exact ((oTwoPrimeOf_le _).trans inf_le_left).trans (bc_le_sec6K hL)
      · exact absurd (h F hF) hnt

section Pieces

variable {X : Type} [Group X] [Finite X]

private theorem bc_card_lt
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

private theorem bc_modOddCard_le
    {n : ℕ} {H G L : Subgroup X} (hL : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L))
    (hG : Sec6KComp X n H G) : modOddCard G ≤ modOddCard L := by
  rcases hG with ⟨-, hGn⟩ | hGM
  · exact (bc_card_lt hL hGn).le
  · exact (modOddCard_eq_of_sec6MComp hL hGM).le

private theorem bc_centModOdd_of_mpiece
    {n : ℕ} {t b : X} (hb2 : orderOf b = 2) {L G : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) (hbL : b ∈ centralizerSection L (pPrimeCoreOf 2 L))
    (hG : Sec6KComp X n (cen b) G) (hLG : sec6Piece L b ≤ G)
    (htG : t ∈ normalizer (G : Set X)) : CentModOdd G t := by
  have hPL : sec6Piece L b ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨-, hcov⟩ := isPCompIn_restrict hL.1.1 (bc_sq hb2) hbL
  have hPcard : modOddCard (sec6Piece L b) = modOddCard L :=
    modOddCard_eq_of_covers hPL (bc_cov hPL hcov)
  have hcovG := covers_of_card_le hLG ((bc_modOddCard_le hL.2 hG).trans hPcard.ge)
  refine bc_centModOdd_of_cover hLG (bc_cov hLG hcovG)
    (mem_normalizer_oddCoreOf_of_mem_normalizer htG) fun p hp => ?_
  rw [commutatorElement_eq_one_iff_mul_comm.2 (bc_comm_of_mem_cen (hL.1.1.1 (hPL hp)))]
  exact one_mem _

private theorem bc_centModOdd_of_Q {n : ℕ} {t x v : X} (hK : Sec6Lemma51 X n)
    (hLa : ∀ y ∈ Sec6Q X n (cen t), orderOf y = 2 → Sec6Covers X n t y)
    {F : Subgroup X} (hF : Sec6KComp X n (cen x) F) (htF : t ∈ normalizer (F : Set X))
    (hvQ : v ∈ Sec6Q X n (cen t)) (hv2 : orderOf v = 2)
    (hvF : v ∈ centralizerSection F (pPrimeCoreOf 2 F)) : CentModOdd F t := by
  set R : Subgroup X := oTwoPrimeOf (F ⊓ cen v) with hRdef
  have hRF : R ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨-, hRcov⟩ := isPCompIn_restrict (bc_isPCompIn hF) (bc_sq hv2) hvF
  have hRK : Sec6KComp X n (cen x ⊓ cen v) R := sec6KComp_restrict hF (bc_sq hv2) hvF
  have hRKv : R ≤ Sec6K X n (cen v) := (bc_le_sec6K hRK).trans (hK.sub v hv2 _ inf_le_right).1
  have hcv := hLa v hvQ hv2
  have hvt : v ∈ cen t := (Subgroup.mem_inf.1 hvQ).1
  have htv : t ∈ cen v := bc_mem_cen_symm hvt
  have htKv : t ∈ normalizer (Sec6K X n (cen v) : Set X) := Sec6K_cen_normal n v htv
  have htOKv : t ∈ normalizer (oddCoreOf (Sec6K X n (cen v)) : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer htKv
  have hKvt : ∀ k ∈ Sec6K X n (cen v), ⁅k, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := by
    intro k hk
    have hk' : k ∈ oddCoreOf (Sec6K X n (cen v)) ⊔
        (Sec6K X n (cen v) ⊓ Sec6K X n (cen t)) := by
      rw [← hcv]
      exact hk
    have hle : oddCoreOf (Sec6K X n (cen v)) ⊔ (Sec6K X n (cen v) ⊓ Sec6K X n (cen t)) ≤
        bcComm (oddCoreOf (Sec6K X n (cen v))) t := by
      refine sup_le (fun o ho => bc_mem_bcComm (le_normalizer ho) (bc_comm_mem_of_mem ho htOKv))
        (fun k hk => bc_mem_bcComm (le_normalizer_oddCoreOf _ hk.1) ?_)
      rw [commutatorElement_eq_one_iff_mul_comm.2 (bc_comm_of_mem_cen (bc_sec6K_le hk.2))]
      exact one_mem _
    exact (hle hk').2
  have htR : t ∈ normalizer (R : Set X) :=
    bc_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf htF (le_normalizer htv))
  have hRO : ∀ r ∈ R, ⁅r, t⁆ ∈ oddCoreOf F := by
    intro r hr
    have h1 : ⁅r, t⁆ ∈ R := by
      have : ⁅r, t⁆ = r * (t * r⁻¹ * t⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact R.mul_mem hr (bc_conj_mem htR (R.inv_mem hr))
    have h2 : ⁅r, t⁆ ∈ oddCoreOf (Sec6K X n (cen v)) := hKvt r (hRKv hr)
    exact bc_oddCoreOf_le_of_cov hRF hRcov (inf_pPrimeCoreOf_le_pPrimeCoreOf hRKv ⟨h1, h2⟩)
  exact bc_centModOdd_of_cover hRF (bc_cov hRF hRcov)
    (mem_normalizer_oddCoreOf_of_mem_normalizer htF) hRO

end Pieces

section Pump

variable {X : Type} [Group X] [Finite X]

private theorem bc_mem_pPrimeCore_iff {F : Subgroup X} (y : ↥F) :
    y ∈ pPrimeCore 2 ↥F ↔ (y : X) ∈ oddCoreOf F :=
  ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, hzy⟩ => by rwa [← Subtype.ext hzy]⟩

private theorem bc_pi_eq_one_iff {F : Subgroup X} (y : ↥F) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) y = 1 ↔ (y : X) ∈ oddCoreOf F := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, bc_mem_pPrimeCore_iff]

private theorem bc_centModOdd_iff {F : Subgroup X} {c : X} (hcF : c ∈ normalizer (F : Set X)) :
    CentModOdd F c ↔ ∀ a (ha : a ∈ F),
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨c * a * c⁻¹, bc_conj_mem hcF ha⟩ : ↥F) =
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨a, ha⟩ : ↥F) := by
  constructor
  · intro h a ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, bc_mem_pPrimeCore_iff]
    show (c * a * c⁻¹)⁻¹ * a ∈ oddCoreOf F
    have h1 := h a⁻¹ (F.inv_mem ha)
    have e : (c * a * c⁻¹)⁻¹ * a = ⁅a⁻¹, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  · intro h a ha
    have h1 := h a ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      bc_mem_pPrimeCore_iff] at h1
    change (c * a * c⁻¹)⁻¹ * a ∈ oddCoreOf F at h1
    have e : ⁅a, c⁆ = a * ((c * a * c⁻¹)⁻¹ * a) * a⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact bc_conj_mem (le_normalizer_oddCoreOf F ha) h1

private theorem bc_pump_act {F : Subgroup X} {t f : X} (htF : t ∈ normalizer (F : Set X))
    (hfF : f ∈ F) (hft : CentModOdd F (f * t)) {a : X} (ha : a ∈ F) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨t * a * t⁻¹, bc_conj_mem htF ha⟩ : ↥F) =
      (QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F))⁻¹ *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨a, ha⟩ : ↥F) *
          QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) := by
  have hftN : f * t ∈ normalizer (F : Set X) := mul_mem (le_normalizer hfF) htF
  have h := (bc_centModOdd_iff hftN).1 hft a ha
  have he : (⟨f * t * a * (f * t)⁻¹, bc_conj_mem hftN ha⟩ : ↥F) =
      (⟨f, hfF⟩ : ↥F) * ⟨t * a * t⁻¹, bc_conj_mem htF ha⟩ * (⟨f, hfF⟩ : ↥F)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he, map_mul, map_mul, map_inv] at h
  rw [← h]
  group

private theorem bc_centModOdd_of_pi_eq {F : Subgroup X} {t f z : X}
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t)) (hzF : z ∈ F)
    (hzf : QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨z, hzF⟩ : ↥F) =
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)) : CentModOdd F (t * z) := by
  have htzN : t * z ∈ normalizer (F : Set X) := mul_mem htF (le_normalizer hzF)
  rw [bc_centModOdd_iff htzN]
  intro a ha
  have hza : z * a * z⁻¹ ∈ F := bc_conj_mem (le_normalizer hzF) ha
  have h1 := bc_pump_act htF hfF hft hza
  have he1 : (⟨t * z * a * (t * z)⁻¹, bc_conj_mem htzN ha⟩ : ↥F) =
      ⟨t * (z * a * z⁻¹) * t⁻¹, bc_conj_mem htF hza⟩ := by
    apply Subtype.ext
    show t * z * a * (t * z)⁻¹ = t * (z * a * z⁻¹) * t⁻¹
    group
  have he2 : (⟨z * a * z⁻¹, hza⟩ : ↥F) = ⟨z, hzF⟩ * ⟨a, ha⟩ * (⟨z, hzF⟩ : ↥F)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he1, h1, he2, map_mul, map_mul, map_inv, hzf]
  group

private theorem bc_comm_mem_of_pi {F : Subgroup X} {c a : X} (hcF : c ∈ normalizer (F : Set X))
    (ha : a ∈ F)
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨c * a * c⁻¹, bc_conj_mem hcF ha⟩ : ↥F) =
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨a, ha⟩ : ↥F)) : ⁅a, c⁆ ∈ oddCoreOf F := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    bc_mem_pPrimeCore_iff] at h
  change (c * a * c⁻¹)⁻¹ * a ∈ oddCoreOf F at h
  have e : ⁅a, c⁆ = a * ((c * a * c⁻¹)⁻¹ * a) * a⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact bc_conj_mem (le_normalizer_oddCoreOf F ha) h

private theorem bc_pump_orderOf {F : Subgroup X} {t f : X} (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) with hgdef
  refine orderOf_eq_prime ?_ ?_
  · rw [sq]
    have hc : g * g ∈ center (↥F ⧸ pPrimeCore 2 ↥F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥F) y
      have hb : ((b : X)) ∈ F := b.2
      have h1 := bc_pump_act htF hfF hft hb
      have h2 := bc_pump_act htF hfF hft (bc_conj_mem htF hb)
      have he : (⟨t * (t * (b : X) * t⁻¹) * t⁻¹, bc_conj_mem htF (bc_conj_mem htF hb)⟩ : ↥F) =
          b := by
        apply Subtype.ext
        show t * (t * (b : X) * t⁻¹) * t⁻¹ = (b : X)
        rw [show t * (t * (b : X) * t⁻¹) * t⁻¹ = (t * t) * (b : X) * (t * t)⁻¹ by group, ht2]
        group
      rw [he, h1] at h2
      have hb' : (⟨(b : X), hb⟩ : ↥F) = b := Subtype.coe_eta b hb
      rw [hb', ← hgdef] at h2
      have h3 : g * g * QuotientGroup.mk' (pPrimeCore 2 ↥F) b =
          QuotientGroup.mk' (pPrimeCore 2 ↥F) b * (g * g) := by
        conv_lhs => rw [h2]
        group
      exact h3.symm
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  · intro hg1
    apply hnt
    rw [bc_centModOdd_iff htF]
    intro a ha
    rw [bc_pump_act htF hfF hft ha, ← hgdef, hg1]
    group

private theorem bc_center_eq_bot
    {n : ℕ} {Q : Type} [Group Q] (hT : IsSec6MType n Q) : center Q = ⊥ :=
  mcLLyCenterFree Q (hT.imp (fun h => h.2) (fun h => h.2))

private theorem bc_cent_doubleCover
    {n : ℕ} {Q : Type} [Group Q]
    (hT : IsSec6MType n Q) {q : Q} (hq : orderOf q = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({q} : Set Q)) n := by
  rcases hT with ⟨rfl, he⟩ | ⟨rfl, he⟩
  · obtain ⟨h1, h2, h3⟩ :=
      CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
        he hq
    exact isDoubleCoverOfAlt_of_cover hq (by norm_num) h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple he q hq
    exact ⟨h1, h2, h3⟩

private theorem bc_card_eq {A B : Type} [Group A] [Group B] {n : ℕ}
    (hA : IsDoubleCoverOfAlt A n) (hB : IsDoubleCoverOfAlt B n) : Nat.card A = Nat.card B := by
  obtain ⟨-, hA2, ⟨eA⟩⟩ := hA
  obtain ⟨-, hB2, ⟨eB⟩⟩ := hB
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center A),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center B), hA2, hB2,
    Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv]

private theorem bc_pump_comm {F : Subgroup X} {t f : X} (htF : t ∈ normalizer (F : Set X))
    (hfF : f ∈ F) (hft : CentModOdd F (f * t)) {p : X} (hpF : p ∈ F) (hpt : p ∈ cen t) :
    QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) =
      QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) *
        QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) := by
  have h := bc_pump_act htF hfF hft hpF
  have he : (⟨t * p * t⁻¹, bc_conj_mem htF hpF⟩ : ↥F) = ⟨p, hpF⟩ := by
    apply Subtype.ext
    show t * p * t⁻¹ = p
    rw [← bc_comm_of_mem_cen hpt]
    group
  rw [he] at h
  calc _ = QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) *
        ((QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F))⁻¹ *
          QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hpF⟩ : ↥F) *
            QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)) := by group
    _ = _ := by rw [← h]

private theorem bc_ker_le {F P : Subgroup X} (hPF : P ≤ F) :
    ((QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)).ker ≤
      pPrimeCore 2 ↥P := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF)
  have hodd : Nat.Coprime 2 (Nat.card φ.ker) := by
    let g : φ.ker →* pPrimeCore 2 ↥F :=
      { toFun := fun a => ⟨Subgroup.inclusion hPF (a : ↥P), by
          have h := a.2
          rw [MonoidHom.mem_ker] at h
          exact (QuotientGroup.eq_one_iff _).1 h⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun y : pPrimeCore 2 ↥F => ((y : ↥F) : X)) hab
      exact this
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
      pPrimeCore_coprime_card
  exact le_sSup ⟨inferInstance, hodd⟩

private theorem bc_pump_img
    {n : ℕ} {F P : Subgroup X}
    {t f : X} (hT : IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F)) (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hPF : P ≤ F) (hPt : P ≤ cen t)
    (hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n) :
    (∀ c ∈ centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F)} :
        Set (↥F ⧸ pPrimeCore 2 ↥F)),
      ∃ p, ∃ hp : p ∈ P, QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨p, hPF hp⟩ : ↥F) = c) ∧
    oddCoreOf P ≤ oddCoreOf F := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) with hgdef
  have hg2 : orderOf g = 2 := bc_pump_orderOf ht2 htF hfF hft hnt (bc_center_eq_bot hT)
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F))) n :=
    bc_cent_doubleCover hT hg2
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 ↥F)).comp (Subgroup.inclusion hPF) with hψ
  have hle : ψ.range ≤ centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F)) := by
    rintro _ ⟨p, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact bc_pump_comm htF hfF hft (hPF p.2) (hPt p.2)
  have hker := bc_ker_le hPF
  have h1 : Nat.card ↥P = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have h2 : Nat.card ↥P = Nat.card (↥P ⧸ pPrimeCore 2 ↥P) * Nat.card (pPrimeCore 2 ↥P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ψ.ker ≤ Nat.card (pPrimeCore 2 ↥P) := Subgroup.card_le_of_le hker
  have h4 : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) =
      Nat.card ↥(centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F))) := bc_card_eq hPn hC
  have hkpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hOpos : 0 < Nat.card (pPrimeCore 2 ↥P) := Nat.card_pos
  have h5 : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) ≤ Nat.card ψ.range := by
    by_contra hlt
    rw [not_le] at hlt
    have e1 : Nat.card ψ.range * Nat.card ψ.ker <
        Nat.card (↥P ⧸ pPrimeCore 2 ↥P) * Nat.card (pPrimeCore 2 ↥P) :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt hkpos) (Nat.mul_le_mul_left _ h3)
    rw [← h1, ← h2] at e1
    exact lt_irrefl _ e1
  have hrange : ψ.range = centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F)) :=
    Subgroup.eq_of_le_of_card_ge hle (h4 ▸ h5)
  refine ⟨fun c hc => ?_, ?_⟩
  · rw [← hrange] at hc
    obtain ⟨p, rfl⟩ := hc
    exact ⟨(p : X), p.2, rfl⟩
  ·
    have h6 : Nat.card ψ.range = Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := by
      rw [hrange, h4]
    have h7 : Nat.card ψ.ker = Nat.card (pPrimeCore 2 ↥P) := by
      have hrpos : 0 < Nat.card ψ.range := Nat.card_pos
      rw [h6] at h1
      rw [h1] at h2
      exact Nat.eq_of_mul_eq_mul_left (h6 ▸ hrpos) h2
    have hkerEq : ψ.ker = pPrimeCore 2 ↥P := Subgroup.eq_of_le_of_card_ge hker h7.ge
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ψ.ker := by
      rw [hkerEq]
      exact hy
    rw [MonoidHom.mem_ker] at hy'
    exact (bc_pi_eq_one_iff (Subgroup.inclusion hPF y)).1 hy'

private theorem bc_pump_two
    {n : ℕ} {F P P' : Subgroup X}
    {t f : X} (hT : IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F)) (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hPF : P ≤ F) (hPt : P ≤ cen t)
    (hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n) (hP'F : P' ≤ F) (hP't : P' ≤ cen t)
    (hP'n : IsDoubleCoverOfAlt (↥P' ⧸ pPrimeCore 2 ↥P') n)
    (hcomm : ∀ p ∈ P, ∀ p' ∈ P', ⁅p, p'⁆ ∈ oddCoreOf P) : False := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨himg, hO⟩ := bc_pump_img hT ht2 htF hfF hft hnt hPF hPt hPn
  obtain ⟨himg', -⟩ := bc_pump_img hT ht2 htF hfF hft hnt hP'F hP't hP'n
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥F) (⟨f, hfF⟩ : ↥F) with hgdef
  have hg2 : orderOf g = 2 := bc_pump_orderOf ht2 htF hfF hft hnt (bc_center_eq_bot hT)
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F))) n :=
    bc_cent_doubleCover hT hg2
  obtain ⟨a, b, hab⟩ := hC.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hab' : a * b = b * a := by
    apply Subtype.ext
    obtain ⟨p, hp, hpa⟩ := himg a.1 a.2
    obtain ⟨p', hp', hpb⟩ := himg' b.1 b.2
    show (a : ↥F ⧸ pPrimeCore 2 ↥F) * b = b * a
    rw [← hpa, ← hpb, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      bc_pi_eq_one_iff]
    exact hO (hcomm p hp p' hp')
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']

private theorem bc_pump_center
    {n : ℕ} {F P : Subgroup X}
    {t f : X} (hT : IsSec6MType n (↥F ⧸ pPrimeCore 2 ↥F)) (ht2 : t * t = 1)
    (htF : t ∈ normalizer (F : Set X)) (hfF : f ∈ F) (hft : CentModOdd F (f * t))
    (hnt : ¬ CentModOdd F t) (hPF : P ≤ F) (hPt : P ≤ cen t)
    (hPn : IsDoubleCoverOfAlt (↥P ⧸ pPrimeCore 2 ↥P) n) {z : X} (hzP : z ∈ P)
    (hz : ∀ p ∈ P, ⁅p, z⁆ ∈ oddCoreOf P) (hzO : z ∉ oddCoreOf F) : CentModOdd F (t * z) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨himg, hO⟩ := bc_pump_img hT ht2 htF hfF hft hnt hPF hPt hPn
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥F) with hπ
  set g := π (⟨f, hfF⟩ : ↥F) with hgdef
  set w := π (⟨z, hPF hzP⟩ : ↥F) with hwdef
  have hg2 : orderOf g = 2 := bc_pump_orderOf ht2 htF hfF hft hnt (bc_center_eq_bot hT)
  set C := centralizer ({g} : Set (↥F ⧸ pPrimeCore 2 ↥F)) with hCdef
  have hC : IsDoubleCoverOfAlt ↥C n := bc_cent_doubleCover hT hg2
  have hwC : w ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact bc_pump_comm htF hfF hft (hPF hzP) (hPt hzP)
  have hgC : g ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have hwZ : (⟨w, hwC⟩ : ↥C) ∈ center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    obtain ⟨p, hp, hpc⟩ := himg c c.2
    show (c : ↥F ⧸ pPrimeCore 2 ↥F) * w = w * c
    rw [← hpc, ← commutatorElement_eq_one_iff_mul_comm, hwdef, ← map_commutatorElement,
      bc_pi_eq_one_iff]
    exact hO (hz p hp)
  have hgZ : (⟨g, hgC⟩ : ↥C) ∈ center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 c.2
  have hw1 : (⟨⟨w, hwC⟩, hwZ⟩ : ↥(center ↥C)) ≠ 1 := by
    intro h
    have h1 : w = 1 := congrArg (fun y : ↥(center ↥C) => ((y : ↥C) : ↥F ⧸ pPrimeCore 2 ↥F)) h
    exact hzO ((bc_pi_eq_one_iff _).1 h1)
  have hg1 : (⟨⟨g, hgC⟩, hgZ⟩ : ↥(center ↥C)) ≠ 1 := by
    intro h
    have h1 : g = 1 := congrArg (fun y : ↥(center ↥C) => ((y : ↥C) : ↥F ⧸ pPrimeCore 2 ↥F)) h
    rw [h1, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(center ↥C))).1 hC.2.1
  have hwg : w = g := by
    have e1 := hy _ hw1
    have e2 := hy _ hg1
    have e3 := e1.trans e2.symm
    exact congrArg (fun y : ↥(center ↥C) => ((y : ↥C) : ↥F ⧸ pPrimeCore 2 ↥F)) e3
  exact bc_centModOdd_of_pi_eq htF hfF hft (hPF hzP) hwg

end Pump

section Inner

variable {X : Type} [Group X] [Finite X]

private theorem bc_centModOdd_mul {L : Subgroup X} {c d : X} (hc : c ∈ normalizer (L : Set X))
    (hcm : CentModOdd L c) (hdm : CentModOdd L d) : CentModOdd L (c * d) := by
  intro a ha
  have e : ⁅a, c * d⁆ = ⁅a, c⁆ * (c * ⁅a, d⁆ * c⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (oddCoreOf L).mul_mem (hcm a ha)
    (bc_conj_mem (mem_normalizer_oddCoreOf_of_mem_normalizer hc) (hdm a ha))

private theorem bc_centModOdd_inv {L : Subgroup X} {c : X} (hc : c ∈ normalizer (L : Set X))
    (hcm : CentModOdd L c) : CentModOdd L c⁻¹ := by
  intro a ha
  have hb : c⁻¹ * a * c⁻¹⁻¹ ∈ L := bc_conj_mem (inv_mem hc) ha
  have e : ⁅a, c⁻¹⁆ = ⁅c⁻¹ * a * c⁻¹⁻¹, c⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact inv_mem (hcm _ hb)

private theorem bc_centModOdd_mul_right {F : Subgroup X} {c y : X} (hc : CentModOdd F c)
    (hy : ∀ a ∈ F, a * y = y * a) : CentModOdd F (c * y) := by
  intro a ha
  have hya : y * a⁻¹ = a⁻¹ * y := by
    have := hy a⁻¹ (F.inv_mem ha)
    exact this.symm
  have e : ⁅a, c * y⁆ = ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    calc a * (c * y) * a⁻¹ * (c * y)⁻¹ = a * c * (y * a⁻¹) * y⁻¹ * c⁻¹ := by group
      _ = a * c * (a⁻¹ * y) * y⁻¹ * c⁻¹ := by rw [hya]
      _ = a * c * a⁻¹ * c⁻¹ := by group
  rw [e]
  exact hc a ha

private theorem bc_centModOdd_mul_left {L : Subgroup X} {c y : X} (hc : CentModOdd L c)
    (hcL : c ∈ normalizer (L : Set X)) (hy : ∀ a ∈ L, y * a = a * y) :
    CentModOdd L (y * c) := by
  intro a ha
  have hb : c * a⁻¹ * c⁻¹ ∈ L := bc_conj_mem hcL (L.inv_mem ha)
  have e : ⁅a, y * c⁆ = ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    calc a * (y * c) * a⁻¹ * (y * c)⁻¹ = a * (y * (c * a⁻¹ * c⁻¹)) * y⁻¹ := by group
      _ = a * ((c * a⁻¹ * c⁻¹) * y) * y⁻¹ := by rw [hy _ hb]
      _ = a * c * a⁻¹ * c⁻¹ := by group
  rw [e]
  exact hc a ha

private theorem bc_mem_normalizer_of_comm {F : Subgroup X} {y : X}
    (hy : ∀ a ∈ F, a * y = y * a) : y ∈ normalizer (F : Set X) := by
  refine bc_mem_normalizer (fun m hm => ?_) (fun m hm => ?_)
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (hy m hm)]
    exact one_mem _
  · rw [commutatorElement_eq_one_iff_mul_comm.2 ((Commute.inv_right (hy m hm)).eq)]
    exact one_mem _

private def bcInner (L : Subgroup X) : Subgroup X where
  carrier := {g | g ∈ normalizer (L : Set X) ∧ ∃ m ∈ L, CentModOdd L (m * g)}
  one_mem' := ⟨one_mem _, 1, one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁, m₁, hm₁, c₁⟩ ⟨h₂, m₂, hm₂, c₂⟩
    refine ⟨mul_mem h₁ h₂, m₁ * (g₁ * m₂ * g₁⁻¹), L.mul_mem hm₁ (bc_conj_mem h₁ hm₂), ?_⟩
    have e : m₁ * (g₁ * m₂ * g₁⁻¹) * (g₁ * g₂) = (m₁ * g₁) * (m₂ * g₂) := by group
    rw [e]
    exact bc_centModOdd_mul (mul_mem (le_normalizer hm₁) h₁) c₁ c₂
  inv_mem' := by
    rintro g ⟨h, m, hm, c⟩
    refine ⟨inv_mem h, g⁻¹ * m⁻¹ * g⁻¹⁻¹, bc_conj_mem (inv_mem h) (L.inv_mem hm), ?_⟩
    have e : g⁻¹ * m⁻¹ * g⁻¹⁻¹ * g⁻¹ = (m * g)⁻¹ := by group
    rw [e]
    exact bc_centModOdd_inv (mul_mem (le_normalizer hm) h) c

private theorem bc_le_bcInner {n : ℕ} {t : X} {L : Subgroup X} (hL : Sec6KComp X n (cen t) L) :
    Sec6M X n (cen t) ≤ bcInner L := by
  unfold Sec6M
  refine sSup_le fun M hM g hg => ?_
  have hMpc : IsPCompIn 2 (cen t) M := hM.1.1
  have hLpc := bc_isPCompIn hL
  by_cases hLM : L = M
  · subst hLM
    refine ⟨le_normalizer hg, g⁻¹, L.inv_mem hg, ?_⟩
    rw [inv_mul_cancel]
    intro a _
    simp
  · refine ⟨bc_mem_normalizer_of_isPCompIn hLpc hMpc hg, 1, one_mem _, ?_⟩
    rw [one_mul]
    intro a ha
    exact bc_comm_mem hLpc hMpc hLM ha hg

private theorem bc_primeResidual_top {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hm : 4 ≤ m)
    (hQ : IsDoubleCoverOfAlt Q m) : primeResidual 2 Q = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : (primeResidual 2 Q).Characteristic := primeResidual_characteristic 2 Q
  have hN : (primeResidual 2 Q).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ.1 hN with h | h
  · exact h
  · exfalso
    have h1 : (center Q).index ∣ (primeResidual 2 Q).index := Subgroup.index_dvd_of_le h
    obtain ⟨e⟩ := hQ.2.2
    have h2 : (center Q).index = Nat.card (alternatingGroup (Fin m)) := by
      rw [Subgroup.index, Nat.card_congr e.toEquiv]
    have h3 : 2 ∣ Nat.card (alternatingGroup (Fin m)) := by
      have hnt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h4 := two_mul_card_alternatingGroup (α := Fin m)
      rw [Fintype.card_perm, Fintype.card_fin] at h4
      have h5 : Nat.factorial 4 ∣ Nat.factorial m := Nat.factorial_dvd_factorial hm
      have h6 : Nat.factorial 4 = 24 := by norm_num [Nat.factorial]
      rw [h6] at h5
      rw [Nat.card_eq_fintype_card]
      omega
    have h4 : 2 ∣ (primeResidual 2 Q).index := (h2 ▸ h3).trans h1
    have h5 := primeResidual_coprime_index 2 Q
    exact absurd (Nat.dvd_gcd (dvd_refl 2) h4) (by rw [h5]; decide)

private theorem bc_inner_piece
    {n : ℕ} {L : Subgroup X}
    {x m : X} (hT : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L)) (hxx : x * x = 1)
    (hxL : x ∈ normalizer (L : Set X)) (hmL : m ∈ L) (hmx : CentModOdd L (m * x))
    (hnx : ¬ CentModOdd L x) :
    IsDoubleCoverOfAlt
      (↥(oTwoPrimeOf (L ⊓ cen x)) ⧸ pPrimeCore 2 ↥(oTwoPrimeOf (L ⊓ cen x))) n := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := oTwoPrimeOf (L ⊓ cen x) with hPdef
  have hPL : P ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPx : P ≤ cen x := (oTwoPrimeOf_le _).trans inf_le_right
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hxx
  have hxO : x ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hxL
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨m, hmL⟩ : ↥L) with hgdef
  have hg2 : orderOf g = 2 := bc_pump_orderOf hxx hxL hmL hmx hnx (bc_center_eq_bot hT)
  have hC := bc_cent_doubleCover hT hg2
  have hn4 : 4 ≤ n := by
    rcases hT with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have himg : (P.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) =
      centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L)) := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact bc_pump_comm hxL hmL hmx p.2 (hPx hp)
    · intro c hc
      have htop := bc_primeResidual_top hn4 hC
      have hmem : (⟨c, hc⟩ : ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L)))) ∈
          primeResidual 2 ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))) := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [primeResidual_eq_closure] at hmem
      have hcl : Subgroup.closure {y : ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))) |
          ∃ k : ℕ, orderOf y = 2 ^ k} ≤
          ((P.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L))).comap
            (centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))).subtype := by
        rw [Subgroup.closure_le]
        rintro y ⟨k, hk⟩
        have hyk : (y : ↥L ⧸ pPrimeCore 2 ↥L) ^ (2 ^ k) = 1 := by
          have := pow_orderOf_eq_one y
          rw [hk] at this
          exact congrArg Subtype.val this
        have hyg : (y : ↥L ⧸ pPrimeCore 2 ↥L) * g = g * y :=
          Subgroup.mem_centralizer_singleton_iff.1 y.2
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L)
          (y : ↥L ⧸ pPrimeCore 2 ↥L)
        have haO : (a : X) ^ (2 ^ k) ∈ oddCoreOf L := by
          have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) (a ^ (2 ^ k)) = 1 := by
            rw [map_pow, ha, hyk]
          have h2 := (bc_pi_eq_one_iff _).1 h1
          simpa using h2
        obtain ⟨e, he1, he2⟩ := exists_zpow_twoElt_of_pow_mem
          (Nat.coprime_two_left.2 (odd_card_oddCoreOf L)) haO
        have ha'L : (a : X) ^ e ∈ L := zpow_mem a.2 e
        have hpa : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨(a : X) ^ e, ha'L⟩ : ↥L) =
            (y : ↥L ⧸ pPrimeCore 2 ↥L) := by
          rw [← ha, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq,
            bc_mem_pPrimeCore_iff]
          exact he2
        have hcomm : ⁅(a : X) ^ e, x⁆ ∈ pPrimeCoreOf 2 L := by
          refine bc_comm_mem_of_pi hxL ha'L ?_
          rw [bc_pump_act hxL hmL hmx ha'L, hpa, ← hgdef, mul_assoc, hyg]
          group
        obtain ⟨c', hc', hc'k, hc'a⟩ :=
          exists_twoElt_centralizer_of_comm_mem hx2 hxO ha'L hcomm he1
        have hc'P : c' ∈ P := mem_oTwoPrimeOf hc' k hc'k
        refine ⟨⟨c', (Subgroup.mem_inf.1 hc').1⟩, Subgroup.mem_subgroupOf.2 hc'P, ?_⟩
        show _ = (y : ↥L ⧸ pPrimeCore 2 ↥L)
        rw [← hpa, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          bc_mem_pPrimeCore_iff]
        exact hc'a
      exact hcl hmem
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥L)).ker :=
    CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker
  obtain ⟨q₂⟩ := CFSG.ComponentClassification.GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥L)) hker (P.subgroupOf L)
  obtain ⟨q₃⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr himg)
  obtain ⟨q₅⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hPL)
  have hbot := pPrimeCore_eq_bot_of_doubleCover hC
  let q₄ : ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ⧸
      pPrimeCore 2 ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ≃*
      ↥(centralizer ({g} : Set (↥L ⧸ pPrimeCore 2 ↥L))) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact isDoubleCoverOfAlt_congr' (q₅.symm.trans (q₂.trans (q₃.trans q₄))).symm hC

private theorem bc_inner_center
    {n : ℕ} {L : Subgroup X} {x m : X} (hT : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L))
    (hxx : x * x = 1) (hxL : x ∈ normalizer (L : Set X)) (hmL : m ∈ L)
    (hmx : CentModOdd L (m * x)) (hnx : ¬ CentModOdd L x) :
    ∃ z ∈ oTwoPrimeOf (L ⊓ cen x), orderOf z = 2 ∧
      (∀ p ∈ oTwoPrimeOf (L ⊓ cen x), ⁅p, z⁆ ∈ oddCoreOf (oTwoPrimeOf (L ⊓ cen x))) ∧
      CentModOdd L (x * z) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : oTwoPrimeOf (L ⊓ cen x) ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPx : oTwoPrimeOf (L ⊓ cen x) ≤ cen x := (oTwoPrimeOf_le _).trans inf_le_right
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hxx
  have hxO : x ∈ normalizer (pPrimeCoreOf 2 L : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hxL
  set g := QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨m, hmL⟩ : ↥L) with hgdef
  have hg2 : orderOf g = 2 := bc_pump_orderOf hxx hxL hmL hmx hnx (bc_center_eq_bot hT)
  have hgg : g ^ 2 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg2] at this
  have hm2 : m ^ (2 ^ 1) ∈ oddCoreOf L := by
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ((⟨m, hmL⟩ : ↥L) ^ 2) = 1 := by
      rw [map_pow, ← hgdef, hgg]
    have h2 := (bc_pi_eq_one_iff _).1 h1
    simpa using h2
  obtain ⟨e, he1, he2⟩ := exists_zpow_twoElt_of_pow_mem
    (Nat.coprime_two_left.2 (odd_card_oddCoreOf L)) hm2
  have hyL : m ^ e ∈ L := zpow_mem hmL e
  have hpy : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨m ^ e, hyL⟩ : ↥L) = g := by
    rw [hgdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq,
      bc_mem_pPrimeCore_iff]
    exact he2
  have hcomm : ⁅m ^ e, x⁆ ∈ pPrimeCoreOf 2 L := by
    refine bc_comm_mem_of_pi hxL hyL ?_
    rw [bc_pump_act hxL hmL hmx hyL, hpy, ← hgdef]
    group
  obtain ⟨z, hz, hz2, hzy⟩ := exists_twoElt_centralizer_of_comm_mem hx2 hxO hyL hcomm he1
  have hzL : z ∈ L := hz.1
  have hpz : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨z, hzL⟩ : ↥L) = g := by
    rw [← hpy, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      bc_mem_pPrimeCore_iff]
    exact hzy
  have hzP : z ∈ oTwoPrimeOf (L ⊓ cen x) := mem_oTwoPrimeOf hz 1 hz2
  refine ⟨z, hzP, ?_, fun p hp => ?_, bc_centModOdd_of_pi_eq hxL hmL hmx hzL hpz⟩
  · refine orderOf_eq_prime (by simpa using hz2) ?_
    rintro rfl
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥L) (⟨1, hzL⟩ : ↥L) = 1 := map_one _
    rw [hpz] at h1
    rw [h1, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  · have h1 : ⁅p, z⁆ ∈ oTwoPrimeOf (L ⊓ cen x) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hp hzP) (inv_mem hp)) (inv_mem hzP)
    have h2 : ⁅p, z⁆ ∈ oddCoreOf L := by
      have hc := bc_pump_comm hxL hmL hmx (hPL hp) (hPx hp)
      have h3 : QuotientGroup.mk' (pPrimeCore 2 ↥L)
          ⁅(⟨p, hPL hp⟩ : ↥L), (⟨z, hzL⟩ : ↥L)⁆ = 1 := by
        rw [map_commutatorElement, hpz, commutatorElement_eq_one_iff_mul_comm]
        exact hc
      exact (bc_pi_eq_one_iff _).1 h3
    exact inf_pPrimeCoreOf_le_pPrimeCoreOf hPL ⟨h1, h2⟩

private theorem bc_iSup_subgroupOf_eq {H : Subgroup X} (S : Finset (Subgroup X))
    (hle : ∀ L ∈ S, L ≤ H) : ⨆ L ∈ S, L.subgroupOf H = (⨆ L ∈ S, L).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup₂_le hle)]
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun L => iSup_congr fun hL => Subgroup.map_subgroupOf_eq_of_le (hle L hL)

private theorem bc_not_mem_sec6M
    {n : ℕ} {t : X} (ht : orderOf t = 2) : t ∉ Sec6M X n (cen t) := by
  classical
  intro htM
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hMS, -⟩ := modOddCard_Sec6M_eq_prod_of_centerFree (n := n) mcLLyCenterFree (cen t)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(cen t)) with hπ
  have hpc : ∀ L ∈ S, IsPComponent 2 (L.subgroupOf (cen t)) := fun L hL => ((hS L).1 hL).1.1.2
  have hLC : ∀ L ∈ S, L ≤ cen t := fun L hL => ((hS L).1 hL).1.1.1
  have hT1 : ∀ L ∈ S, ∀ L' ∈ S, L ≠ L' → ∀ a ∈ (L.subgroupOf (cen t)).map π,
      ∀ b ∈ (L'.subgroupOf (cen t)).map π, a * b = b * a := by
    intro L hL L' hL' hne a ha b hb
    have hne' : L.subgroupOf (cen t) ≠ L'.subgroupOf (cen t) := by
      intro h
      apply hne
      rw [Subgroup.subgroupOf_inj, inf_of_le_left (hLC L hL), inf_of_le_left (hLC L' hL')] at h
      exact h
    exact (commute_of_mem_map_of_isPComponent (hpc L hL) (hpc L' hL') hne' ha hb).eq
  have hT2 : ∀ L ∈ S, ∀ a ∈ (L.subgroupOf (cen t)).map π,
      (∀ b ∈ (L.subgroupOf (cen t)).map π, a * b = b * a) → a = 1 := by
    intro L hL a ha hab
    have hsub : (L.subgroupOf (cen t)).IsSubnormal := (isPComponent_two_iff.1 (hpc L hL)).1
    obtain ⟨e₁⟩ := nonempty_quot_pPrimeCore_mulEquiv_map hsub
    obtain ⟨e₂⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe (hLC L hL))
    have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := bc_center_eq_bot ((hS L).1 hL).2
    have hZ' : center ↥((L.subgroupOf (cen t)).map π) = ⊥ := by
      rw [← Subgroup.map_center_eq (e₂.symm.trans e₁), hZ, Subgroup.map_bot]
    have hmem : (⟨a, ha⟩ : ↥((L.subgroupOf (cen t)).map π)) ∈
        center ↥((L.subgroupOf (cen t)).map π) := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hab b b.2).symm
    rw [hZ'] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  set t' : ↥(cen t) := ⟨t, self_mem_centralizer t⟩ with ht'
  have hT3 : ∀ y, y * π t' = π t' * y := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(cen t)) y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact bc_comm_of_mem_cen y.2
  have hT4 : ∀ S' : Finset (Subgroup X), S' ⊆ S →
      π t' ∈ ⨆ L ∈ S', (L.subgroupOf (cen t)).map π → π t' = 1 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      intro _ h
      simpa using h
    | insert L S' hLS' ih =>
      intro hsub hmem
      rw [Finset.iSup_insert] at hmem
      have hLS : L ∈ S := hsub (Finset.mem_insert_self L S')
      have hS'S : S' ⊆ S := (Finset.subset_insert L S').trans hsub
      have hcomm : ∀ a ∈ (L.subgroupOf (cen t)).map π,
          ∀ b ∈ ⨆ L' ∈ S', (L'.subgroupOf (cen t)).map π, a * b = b * a := by
        intro a ha b hb
        have hle : ⨆ L' ∈ S', (L'.subgroupOf (cen t)).map π ≤
            centralizer (((L.subgroupOf (cen t)).map π : Subgroup _) : Set _) := by
          refine iSup₂_le fun L' hL' => ?_
          intro c hc
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          exact hT1 L hLS L' (hS'S hL') (fun h => hLS' (h ▸ hL')) d hd c hc
        exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hcomm hmem
      have ha1 : a = 1 := by
        refine hT2 L hLS a ha fun c hc => ?_
        have hbc : Commute b c := (hcomm c hc b hb).symm
        have hbc' : b⁻¹ * c = c * b⁻¹ := hbc.inv_left.eq
        have ha' : a = π t' * b⁻¹ := by rw [← hab]; group
        rw [ha']
        calc π t' * b⁻¹ * c = π t' * (b⁻¹ * c) := mul_assoc _ _ _
          _ = π t' * (c * b⁻¹) := by rw [hbc']
          _ = (π t' * c) * b⁻¹ := (mul_assoc _ _ _).symm
          _ = (c * π t') * b⁻¹ := by rw [← hT3 c]
          _ = c * (π t' * b⁻¹) := mul_assoc _ _ _
      rw [ha1, one_mul] at hab
      exact ih hS'S (hab ▸ hb)
  have ht'M : t' ∈ (⨆ L ∈ S, L).subgroupOf (cen t) := by
    rw [Subgroup.mem_subgroupOf, ← hMS]
    exact htM
  rw [← bc_iSup_subgroupOf_eq S hLC] at ht'M
  have hmem : π t' ∈ ⨆ L ∈ S, (L.subgroupOf (cen t)).map π := by
    have h1 : π t' ∈ (⨆ L ∈ S, L.subgroupOf (cen t)).map π := ⟨t', ht'M, rfl⟩
    simpa only [Subgroup.map_iSup] using h1
  have h1 := hT4 S (subset_refl S) hmem
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(cen t))) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have ht'2 : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_mk]
    exact ht
  exact bc_not_mem_of_odd hodd ht'2 h1

private theorem bc_t_mem_Q {n : ℕ} {t : X} : t ∈ Sec6Q X n (cen t) := by
  refine Subgroup.mem_inf.2 ⟨self_mem_centralizer t, mem_QOf_iff.2
    ⟨Sec6K_cen_normal n t (self_mem_centralizer t), fun k hk => ?_⟩⟩
  rw [commutatorElement_eq_one_iff_mul_comm.2 (bc_comm_of_mem_cen (bc_sec6K_le hk))]
  exact one_mem _

private theorem bc_cover_of_normalized {D G W : Subgroup X} (hDq : IsTwoGenQuasi ↥D)
    (hDG : D ≤ normalizer (G : Set X)) (hWD : W ≤ D) (hWG : W ≤ G) (hWq : IsTwoGenQuasi ↥W) :
    D = oddCoreOf D ⊔ (D ⊓ G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : ((D ⊓ G).subgroupOf D).Normal := by
    refine ⟨fun a ha d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact ⟨(d * a * d⁻¹).2, bc_conj_mem (hDG d.2) ha.2⟩
  have hNm : (((D ⊓ G).subgroupOf D).map (QuotientGroup.mk' (pPrimeCore 2 ↥D))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hDq.2 hNm with htop | hcen
  · have h1 : (D ⊓ G).subgroupOf D ⊔ pPrimeCore 2 ↥D = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore 2 ↥D)) ((D ⊓ G).subgroupOf D)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    exact bc_cov inf_le_left h1
  · exfalso
    refine not_commutator_le_of_odd hWq (odd_card_oddCoreOf D) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haN : QuotientGroup.mk' (pPrimeCore 2 ↥D) (⟨a, hWD ha⟩ : ↥D) ∈
        center (↥D ⧸ pPrimeCore 2 ↥D) :=
      hcen ⟨⟨a, hWD ha⟩, Subgroup.mem_subgroupOf.2 ⟨hWD ha, hWG ha⟩, rfl⟩
    have hc : QuotientGroup.mk' (pPrimeCore 2 ↥D) ⁅(⟨a, hWD ha⟩ : ↥D), (⟨b, hWD hb⟩ : ↥D)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 haN _).symm
    exact (bc_pi_eq_one_iff _).1 hc

end Inner

theorem sec6_mpiece_unpumped
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hC : Sec6CtrlAt X n t)
    {x : X} (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2)
    {L F : Subgroup X} (hL : Sec6MComp X n (cen t) L) (hF : Sec6KComp X n (cen x) F)
    (hLF : sec6Piece L x ≤ F) : F = oddCoreOf F ⊔ sec6Piece L x := by
  have hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  obtain ⟨htF, hd⟩ := hC.dich x hxMQ hx2 L F (Or.inr hL) hF hLF
  rcases hd with h | ⟨hFM, hnt, f, hfF, hft⟩
  · exact h
  exfalso
  have ht2 : orderOf t = 2 := hS.choice.inv
  have htt : t * t = 1 := bc_mul_self ht2
  have hxx : x * x = 1 := bc_mul_self hx2
  have hLt : L ≤ cen t := hL.1.1.1
  have hxt : x ∈ cen t := bc_sec6M_le hx
  obtain ⟨hxL, m, hmL, hmx⟩ := bc_le_bcInner (Or.inr hL) hx
  by_cases hxc : CentModOdd L x
  · exact hnt (bc_centModOdd_of_mpiece hx2 hL
      ⟨hxL, mem_normalizer_oddCoreOf_of_mem_normalizer hxL, hxc⟩ hF hLF htF)
  have hPL : sec6Piece L x ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPx : sec6Piece L x ≤ cen x := (oTwoPrimeOf_le _).trans inf_le_right
  have hPt : sec6Piece L x ≤ cen t := hPL.trans hLt
  have hPn : IsDoubleCoverOfAlt (↥(sec6Piece L x) ⧸ pPrimeCore 2 ↥(sec6Piece L x)) n :=
    bc_inner_piece hL.2 hxx hxL hmL hmx hxc
  obtain ⟨z, hzP, hz2, hzc, hxz⟩ := bc_inner_center hL.2 hxx hxL hmL hmx hxc
  have hzO : z ∉ oddCoreOf F := bc_not_mem_of_odd (odd_card_oddCoreOf F) hz2
  have htz : CentModOdd F (t * z) :=
    bc_pump_center hFM.2 htt htF hfF hft hnt hLF hPt hPn hzP hzc hzO
  have hzx : z ∈ cen x := hPx hzP
  have hzt : z ∈ cen t := hPt hzP
  have hzL : z ∈ L := hPL hzP
  have cxt : x * t = t * x := bc_comm_of_mem_cen hxt
  have czx : z * x = x * z := bc_comm_of_mem_cen hzx
  have czt : z * t = t * z := bc_comm_of_mem_cen hzt
  have hzz : z * z = 1 := bc_mul_self hz2
  have hu2 : t * x * z * (t * x * z) = 1 := by
    calc t * x * z * (t * x * z) = t * x * (z * t) * x * z := by group
      _ = t * x * (t * z) * x * z := by rw [czt]
      _ = t * (x * t) * z * x * z := by group
      _ = t * (t * x) * z * x * z := by rw [cxt]
      _ = (t * t) * x * (z * x) * z := by group
      _ = (t * t) * x * (x * z) * z := by rw [czx]
      _ = (t * t) * (x * x) * (z * z) := by group
      _ = 1 := by rw [htt, hxx, hzz, one_mul, one_mul]
  have hxzM : x * z ∈ Sec6M X n (cen t) := mul_mem hx (bc_le_sec6M hL hzL)
  have hu1 : t * x * z ≠ 1 := by
    intro h
    apply bc_not_mem_sec6M (n := n) ht2
    have e : t = (x * z)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact h
    have h' : (x * z)⁻¹ ∈ Sec6M X n (cen t) := inv_mem hxzM
    rwa [← e] at h'
  have hu : orderOf (t * x * z) = 2 := by
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have husq : (t * x * z) ^ 2 = 1 := by rw [sq]; exact hu2
  have huMQ : t * x * z ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := by
    rw [mul_assoc]
    exact mul_mem (Subgroup.mem_sup_right bc_t_mem_Q) (Subgroup.mem_sup_left hxzM)
  have hux : t * x * z ∈ cen x :=
    mul_mem (mul_mem (bc_mem_cen_symm hxt) (self_mem_centralizer x)) hzx
  have hut : t * x * z ∈ cen t := mul_mem (mul_mem (self_mem_centralizer t) hxt) hzt
  have hxF : x ∈ normalizer (F : Set X) := bc_mem_normalizer_of_comm fun a ha =>
    bc_comm_of_mem_cen ((bc_isPCompIn hF).1 ha)
  have huNF : t * x * z ∈ normalizer (F : Set X) :=
    mul_mem (mul_mem htF hxF) (le_normalizer (hLF hzP))
  have huF : t * x * z ∈ centralizerSection F (pPrimeCoreOf 2 F) := by
    refine ⟨huNF, mem_normalizer_oddCoreOf_of_mem_normalizer huNF, ?_⟩
    have e : t * x * z = t * z * x := by rw [mul_assoc, ← czx, ← mul_assoc]
    rw [e]
    exact bc_centModOdd_mul_right htz fun a ha => bc_comm_of_mem_cen ((bc_isPCompIn hF).1 ha)
  have htL : t ∈ normalizer (L : Set X) :=
    bc_mem_normalizer_of_comm fun a ha => bc_comm_of_mem_cen (hLt ha)
  have huNL : t * x * z ∈ normalizer (L : Set X) := mul_mem (mul_mem htL hxL) (le_normalizer hzL)
  have huL : t * x * z ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
    refine ⟨huNL, mem_normalizer_oddCoreOf_of_mem_normalizer huNL, ?_⟩
    rw [mul_assoc]
    exact bc_centModOdd_mul_left hxz (mul_mem hxL (le_normalizer hzL))
      fun a ha => (bc_comm_of_mem_cen (hLt ha)).symm
  obtain ⟨hDpc, hDcov⟩ := isPCompIn_restrict (bc_isPCompIn hF) husq huF
  have hDF : oTwoPrimeOf (F ⊓ cen (t * x * z)) ≤ F := (oTwoPrimeOf_le _).trans inf_le_left
  have hDK : oTwoPrimeOf (F ⊓ cen (t * x * z)) ≤ Sec6K X n (cen (t * x * z)) :=
    (bc_le_sec6K (sec6KComp_restrict hF husq huF)).trans (hK.sub _ hu _ inf_le_right).1
  obtain ⟨G, hG, hP'G⟩ := hC.land _ huMQ hu L (Or.inr hL)
  obtain ⟨htG, -⟩ := hC.dich _ huMQ hu L G (Or.inr hL) hG hP'G
  have hGt : CentModOdd G t := bc_centModOdd_of_mpiece hu hL huL hG hP'G htG
  have huNP : t * x * z ∈ normalizer (sec6Piece L x : Set X) :=
    bc_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf huNL (le_normalizer hux))
  have huP : t * x * z ∈ centralizerSection (sec6Piece L x) (pPrimeCoreOf 2 (sec6Piece L x)) := by
    refine ⟨huNP, mem_normalizer_oddCoreOf_of_mem_normalizer huNP, fun p hp => ?_⟩
    have h1 : ⁅p, t * x * z⁆ ∈ sec6Piece L x := by
      have e : ⁅p, t * x * z⁆ = p * ((t * x * z) * p⁻¹ * (t * x * z)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hp (bc_conj_mem huNP (inv_mem hp))
    exact inf_pPrimeCoreOf_le_pPrimeCoreOf hPL ⟨h1, huL.2.2 p (hPL hp)⟩
  have hPq : IsTwoGenQuasi ↥(sec6Piece L x) := ⟨primeResidual_oTwoPrimeOf _, hPn.1⟩
  have hWP : oTwoPrimeOf (sec6Piece L x ⊓ cen (t * x * z)) ≤ sec6Piece L x :=
    (oTwoPrimeOf_le _).trans inf_le_left
  have hWcov := oTwoPrimeOf_inf_centralizer_covers husq hPq.1 huP
  have hWq : IsTwoGenQuasi ↥(oTwoPrimeOf (sec6Piece L x ⊓ cen (t * x * z))) :=
    isTwoGenQuasi_of_covers hWP hWcov (primeResidual_oTwoPrimeOf _) hPq
  have hWD : oTwoPrimeOf (sec6Piece L x ⊓ cen (t * x * z)) ≤ oTwoPrimeOf (F ⊓ cen (t * x * z)) :=
    oTwoPrimeOf_mono (inf_le_inf_right _ hLF)
  have hWG : oTwoPrimeOf (sec6Piece L x ⊓ cen (t * x * z)) ≤ G :=
    (oTwoPrimeOf_mono (inf_le_inf_right _ hPL)).trans hP'G
  have hDq : IsTwoGenQuasi ↥(oTwoPrimeOf (F ⊓ cen (t * x * z))) := bc_isTwoGenQuasi hDpc
  have hDG : oTwoPrimeOf (F ⊓ cen (t * x * z)) ≤ normalizer (G : Set X) :=
    hDK.trans (bc_sec6K_le_normalizer hG)
  have hDcov' := bc_cover_of_normalized hDq hDG hWD hWG hWq
  have htD : t ∈ normalizer (oTwoPrimeOf (F ⊓ cen (t * x * z)) : Set X) :=
    bc_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf htF (le_normalizer (bc_mem_cen_symm hut)))
  have hDt : ∀ d ∈ oTwoPrimeOf (F ⊓ cen (t * x * z)),
      ⁅d, t⁆ ∈ oddCoreOf (oTwoPrimeOf (F ⊓ cen (t * x * z))) := by
    have hle : oddCoreOf (oTwoPrimeOf (F ⊓ cen (t * x * z))) ⊔
        (oTwoPrimeOf (F ⊓ cen (t * x * z)) ⊓ G) ≤
        bcComm (oddCoreOf (oTwoPrimeOf (F ⊓ cen (t * x * z)))) t := by
      refine sup_le (fun o ho => bc_mem_bcComm (le_normalizer ho)
        (bc_comm_mem_of_mem ho (mem_normalizer_oddCoreOf_of_mem_normalizer htD)))
        (fun d hd => bc_mem_bcComm (le_normalizer_oddCoreOf _ hd.1) ?_)
      have h1 : ⁅d, t⁆ ∈ oTwoPrimeOf (F ⊓ cen (t * x * z)) := by
        have e : ⁅d, t⁆ = d * (t * d⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem hd.1 (bc_conj_mem htD (inv_mem hd.1))
      have h2 : ⁅d, t⁆ ∈ oddCoreOf G := hGt d hd.2
      refine le_oddCoreOf_of_normalized
        (N := oTwoPrimeOf (F ⊓ cen (t * x * z)) ⊓ oddCoreOf G) inf_le_left
        (fun k hk => mem_normalizer_inf (le_normalizer hk)
          (mem_normalizer_oddCoreOf_of_mem_normalizer (hDG hk)))
        ((odd_card_oddCoreOf G).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)) ⟨h1, h2⟩
    intro d hd
    have hd' : d ∈ oddCoreOf (oTwoPrimeOf (F ⊓ cen (t * x * z))) ⊔
        (oTwoPrimeOf (F ⊓ cen (t * x * z)) ⊓ G) := by
      rw [← hDcov']
      exact hd
    exact (hle hd').2
  apply hnt
  exact bc_centModOdd_of_cover hDF (bc_cov hDF hDcov)
    (mem_normalizer_oddCoreOf_of_mem_normalizer htF)
    fun d hd => bc_oddCoreOf_le_of_cov hDF hDcov (hDt d hd)

section APieces

variable {X : Type} [Group X] [Finite X]

private theorem bc_sec6M_le_centralizerSection
    {n : ℕ} {t : X} {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) :
    Sec6M X n (cen t) ≤ centralizerSection A (pPrimeCoreOf 2 A) := by
  unfold Sec6M
  refine sSup_le fun M hM => ?_
  have hApc : IsPCompIn 2 (cen t) A := bc_isPCompIn (Or.inl hA)
  have hne : A ≠ M := by
    rintro rfl
    have hZ := bc_center_eq_bot hM.2
    have h2 := hA.2.2.1
    rw [hZ] at h2
    simp at h2
  intro g hg
  exact bc_mem_centralizerSection hApc hM.1.1 hne hg

private theorem bc_witness_mem_Q {n : ℕ} {t x v : X} {A : Subgroup X}
    (hA : Sec5Comp X n (cen t) A) (hx2 : orderOf x = 2)
    (hxA : x ∈ centralizerSection A (pPrimeCoreOf 2 A))
    (hv : IsIntrinsicIn X (cen t ⊓ cen x) (sec6Piece A x) v) : v ∈ Sec6Q X n (cen t) := by
  have hApc : IsPCompIn 2 (cen t) A := bc_isPCompIn (Or.inl hA)
  have hPA : sec6Piece A x ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
  obtain ⟨-, hcovA⟩ := isPCompIn_restrict hApc (bc_sq hx2) hxA
  obtain ⟨-, hvP, -, hPeq, -⟩ := hv
  have hvA : v ∈ A := hPA hvP
  have hvt : v ∈ cen t := hApc.1 hvA
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hPeq
  have hvP' : CentModOdd (sec6Piece A x) v := by
    refine bc_centModOdd_of_cover ((oTwoPrimeOf_le _).trans inf_le_left) hPeq
      (mem_normalizer_oddCoreOf_of_mem_normalizer (le_normalizer hvP)) fun e he => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (bc_comm_of_mem_cen (((oTwoPrimeOf_le _).trans inf_le_right) he))]
    exact one_mem _
  have hvA' : CentModOdd A v :=
    bc_centModOdd_of_cover hPA (bc_cov hPA hcovA)
      (mem_normalizer_oddCoreOf_of_mem_normalizer (le_normalizer hvA))
      fun p hp => bc_oddCoreOf_le_of_cov hPA hcovA (hvP' p hp)
  have hKt : CentModOdd (Sec6K X n (cen t)) v := by
    intro k hk
    have hle : sSup {L | Sec6KComp X n (cen t) L} ≤
        bcComm (oddCoreOf (Sec6K X n (cen t))) v := by
      refine sSup_le fun L hL l hl =>
        bc_mem_bcComm (le_normalizer_oddCoreOf _ (bc_le_sec6K hL hl)) ?_
      by_cases hLA : L = A
      · rw [hLA] at hl
        exact bc_oddCoreOf_le_oddCoreOf_sec6K (Or.inl hA) (hvA' l hl)
      · exact bc_oddCoreOf_le_oddCoreOf_sec6K hL
          (bc_comm_mem (bc_isPCompIn hL) hApc hLA hl hvA)
    exact (hle hk).2
  exact Subgroup.mem_inf.2 ⟨hvt, mem_QOf_iff.2 ⟨Sec6K_cen_normal n t hvt, hKt⟩⟩

private theorem bc_centModOdd_of_eq_piece {n : ℕ} {t x : X} {L F : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) (hLF : sec6Piece L x ≤ F) (htF : t ∈ normalizer (F : Set X))
    (heq : F = oddCoreOf F ⊔ sec6Piece L x) : CentModOdd F t := by
  refine bc_centModOdd_of_cover hLF heq (mem_normalizer_oddCoreOf_of_mem_normalizer htF)
    fun p hp => ?_
  rw [commutatorElement_eq_one_iff_mul_comm.2
    (bc_comm_of_mem_cen ((bc_isPCompIn hL).1 (((oTwoPrimeOf_le _).trans inf_le_left) hp)))]
  exact one_mem _

private theorem bc_pump_data {n : ℕ} {t x : X} (hC : Sec6CtrlAt X n t)
    (hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t)) (hx2 : orderOf x = 2) {L F : Subgroup X}
    (hL : Sec6KComp X n (cen t) L) (hF : Sec6KComp X n (cen x) F) (hLF : sec6Piece L x ≤ F)
    (hnt : ¬ CentModOdd F t) :
    t ∈ normalizer (F : Set X) ∧ Sec6MComp X n (cen x) F ∧ ∃ f ∈ F, CentModOdd F (f * t) := by
  obtain ⟨htF, hd⟩ := hC.dich x hxMQ hx2 L F hL hF hLF
  rcases hd with heq | ⟨hFM, -, f, hfF, hft⟩
  · exact absurd (bc_centModOdd_of_eq_piece hL hLF htF heq) hnt
  · exact ⟨htF, hFM, f, hfF, hft⟩

private theorem bc_apiece_le
    {n : ℕ} {t x : X} (hK : Sec6Lemma51 X n)
    (hLa : ∀ y ∈ Sec6Q X n (cen t), orderOf y = 2 → Sec6Covers X n t y)
    (hC : Sec6CtrlAt X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2)
    {F : Subgroup X} (hF : Sec6KComp X n (cen x) F) (hnt : ¬ CentModOdd F t)
    {A : Subgroup X} (hA : Sec5Comp X n (cen t) A) : sec6Piece A x ≤ F := by
  have hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  have hxA := bc_sec6M_le_centralizerSection hA hx
  obtain ⟨⟨v, hv⟩, -⟩ := sec5Comp_restrict hA (bc_sq hx2) hxA
  have hvQ := bc_witness_mem_Q hA hx2 hxA hv
  obtain ⟨G, hG, hPG⟩ := hC.land x hxMQ hx2 A (Or.inl hA)
  by_contra hPF
  have hGF : G ≠ F := fun h => hPF (h ▸ hPG)
  obtain ⟨L, hL, hLF⟩ := hC.piece x hxMQ hx2 F hF
  obtain ⟨htF, -⟩ := hC.dich x hxMQ hx2 L F hL hF hLF
  have hvF : v ∈ centralizerSection F (pPrimeCoreOf 2 F) :=
    bc_mem_centralizerSection (bc_isPCompIn hF) (bc_isPCompIn hG) (Ne.symm hGF) (hPG hv.2.1)
  exact hnt (bc_centModOdd_of_Q hK hLa hF htF hvQ hv.1 hvF)

private theorem bc_pumped_apiece
    {n : ℕ} {t x : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hC : Sec6CtrlAt X n t)
    (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {F : Subgroup X}
    (hF : Sec6KComp X n (cen x) F) (hnt : ¬ CentModOdd F t) :
    ∃ A, Sec5Comp X n (cen t) A ∧ sec6Piece A x ≤ F := by
  have hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  obtain ⟨L, hL, hLF⟩ := hC.piece x hxMQ hx2 F hF
  rcases hL with hA | hM
  · exact ⟨L, hA, hLF⟩
  · obtain ⟨htF, -⟩ := hC.dich x hxMQ hx2 L F (Or.inr hM) hF hLF
    exact absurd (bc_centModOdd_of_eq_piece (Or.inr hM) hLF htF
      (sec6_mpiece_unpumped hS hK hC hx hx2 hM hF hLF)) hnt

private theorem bc_unique_A
    {n : ℕ} {t x : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n)
    (hLa : ∀ y ∈ Sec6Q X n (cen t), orderOf y = 2 → Sec6Covers X n t y)
    (hC : Sec6CtrlAt X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2)
    {F : Subgroup X} (hF : Sec6KComp X n (cen x) F) (hnt : ¬ CentModOdd F t)
    {A A' : Subgroup X} (hA : Sec5Comp X n (cen t) A) (hA' : Sec5Comp X n (cen t) A') :
    A = A' := by
  by_contra hne
  have hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  have hPA := bc_apiece_le hK hLa hC hx hx2 hF hnt hA
  have hPA' := bc_apiece_le hK hLa hC hx hx2 hF hnt hA'
  obtain ⟨htF, hFM, f, hfF, hft⟩ := bc_pump_data hC hxMQ hx2 (Or.inl hA) hF hPA hnt
  have hxA := bc_sec6M_le_centralizerSection hA hx
  have hxA' := bc_sec6M_le_centralizerSection hA' hx
  have hApc : IsPCompIn 2 (cen t) A := bc_isPCompIn (Or.inl hA)
  have hA'pc : IsPCompIn 2 (cen t) A' := bc_isPCompIn (Or.inl hA')
  obtain ⟨hPApc, -⟩ := isPCompIn_restrict hApc (bc_sq hx2) hxA
  obtain ⟨hPA'pc, -⟩ := isPCompIn_restrict hA'pc (bc_sq hx2) hxA'
  obtain ⟨-, hPAn⟩ := sec5Comp_restrict hA (bc_sq hx2) hxA
  obtain ⟨-, hPA'n⟩ := sec5Comp_restrict hA' (bc_sq hx2) hxA'
  have hPAA : sec6Piece A x ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
  have hPA'A' : sec6Piece A' x ≤ A' := (oTwoPrimeOf_le _).trans inf_le_left
  have hneP : sec6Piece A x ≠ sec6Piece A' x := by
    intro h
    exact hne (eq_of_isPCompIn_of_le hApc hA'pc hPAA ((le_of_eq h).trans hPA'A')
      (bc_isTwoGenQuasi hPApc))
  exact bc_pump_two hFM.2 (bc_mul_self hS.choice.inv) htF hfF hft hnt hPA
    (hPAA.trans hApc.1) hPAn hPA' (hPA'A'.trans hA'pc.1) hPA'n
    fun p hp p' hp' => bc_comm_mem hPApc hPA'pc hneP hp hp'

private theorem bc_K0_eq {n : ℕ} {H A : Subgroup X} (hA : Sec5Comp X n H A)
    (huniq : ∀ A', Sec5Comp X n H A' → A' = A) : K0 X n H = A := by
  rw [K0_eq_sSup_sec5Comp]
  have h : {A' | Sec5Comp X n H A'} = {A} := by
    ext A'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨huniq A', fun h => h ▸ hA⟩
  rw [h, sSup_singleton]

private theorem bc_isPCompIn_of_le {H H' E : Subgroup X} (hE : IsPCompIn 2 H E)
    (hEH' : E ≤ H') (hH'H : H' ≤ H) : IsPCompIn 2 H' E := by
  refine ⟨hEH', isPComponent_two_iff.2 ⟨?_,
    (isTwoGenQuasi_subgroupOf_iff hEH').2 (bc_isTwoGenQuasi hE)⟩⟩
  have h1 : E.subgroupOf H' = (E.subgroupOf H).comap (Subgroup.inclusion hH'H) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  rw [h1]
  exact (isPComponent_two_iff.1 hE.2).1.comap _

private theorem bc_exists_pumped {n : ℕ} {t x : X} (hC : Sec6CtrlAt X n t)
    (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) (h : ¬ Sec6Covers X n t x) :
    ∃ F, Sec6KComp X n (cen x) F ∧ ¬ CentModOdd F t := by
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  exact h (sec6Covers_of_forall_centModOdd hC (Subgroup.mem_sup_left hx) hx2 hno)

end APieces

theorem sec6L61_bc
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hK : Sec6Lemma51 X n) (hLa : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x)
    (hC : Sec6CtrlAt X n t) :
    (¬ Sec6AtAhat X n t → ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → Sec6Covers X n t x) ∧
    (Sec6AtAhat X n t → ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ¬ Sec6Covers X n t x →
      ∃ M0 : Subgroup X, M0 ≤ Sec6K X n (cen x) ∧
        Sec6K X n (cen x) = M0 ⊔ (Sec6M X n (cen t) ⊓ Sec6K X n (cen x)) ∧
        IsSec6MType n (↥M0 ⧸ pPrimeCore 2 ↥M0) ∧
        Sec6K X n (M0 ⊓ cen t) ≤ oddCoreOf (Sec6K X n (cen t)) ⊔ K0 X n (cen t)) := by
  refine ⟨fun hAt x hx hx2 => ?_, fun _ x hx hx2 hncov => ?_⟩
  · by_contra hncov
    obtain ⟨F, hF, hnt⟩ := bc_exists_pumped hC hx hx2 hncov
    obtain ⟨A, hA, -⟩ := bc_pumped_apiece hS hK hC hx hx2 hF hnt
    apply hAt
    have hK0 : K0 X n (cen t) = A :=
      bc_K0_eq hA fun A' hA' => (bc_unique_A hS hK hLa hC hx hx2 hF hnt hA hA').symm
    subst hK0
    exact hA.2
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxMQ : x ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t) := Subgroup.mem_sup_left hx
  have htt : t * t = 1 := bc_mul_self hS.choice.inv
  have hxt : x ∈ cen t := bc_sec6M_le hx
  obtain ⟨F, hF, hnt⟩ := bc_exists_pumped hC hx hx2 hncov
  obtain ⟨A, hA, hPA⟩ := bc_pumped_apiece hS hK hC hx hx2 hF hnt
  have huniq : ∀ A', Sec5Comp X n (cen t) A' → A' = A :=
    fun A' hA' => (bc_unique_A hS hK hLa hC hx hx2 hF hnt hA hA').symm
  obtain ⟨htF, hFM, f, hfF, hft⟩ := bc_pump_data hC hxMQ hx2 (Or.inl hA) hF hPA hnt
  have hApc : IsPCompIn 2 (cen t) A := bc_isPCompIn (Or.inl hA)
  have hxA := bc_sec6M_le_centralizerSection hA hx
  obtain ⟨hPApc, -⟩ := isPCompIn_restrict hApc (bc_sq hx2) hxA
  obtain ⟨-, hPAn⟩ := sec5Comp_restrict hA (bc_sq hx2) hxA
  have hPAq := bc_isTwoGenQuasi hPApc
  have hPAA : sec6Piece A x ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
  have hPAt : sec6Piece A x ≤ cen t := hPAA.trans hApc.1
  set Kx := Sec6K X n (cen x) with hKx
  have hFK : F ≤ Kx := bc_le_sec6K hF
  have hKxx : Kx ≤ cen x := bc_sec6K_le
  have hM0K : oddCoreOf Kx ⊔ F ≤ Kx := sup_le (oddCoreOf_le _) hFK
  have hOFK : oddCoreOf F ≤ oddCoreOf Kx := bc_oddCoreOf_le_oddCoreOf_sec6K hF
  have hOKM0 : oddCoreOf Kx ≤ oddCoreOf (oddCoreOf Kx ⊔ F) :=
    le_oddCoreOf_of_normalized le_sup_left (fun k hk => le_normalizer_oddCoreOf Kx (hM0K hk))
      (odd_card_oddCoreOf _)
  have hFM0 : F ≤ oddCoreOf Kx ⊔ F := le_sup_right
  have hM0cov : oddCoreOf Kx ⊔ F = oddCoreOf (oddCoreOf Kx ⊔ F) ⊔ F :=
    le_antisymm (sup_le (hOKM0.trans le_sup_left) le_sup_right)
      (sup_le (oddCoreOf_le _) le_sup_right)
  have hcovT : F.subgroupOf (oddCoreOf Kx ⊔ F) ⊔ pPrimeCore 2 ↥(oddCoreOf Kx ⊔ F) = ⊤ :=
    (covers_subgroupOf_iff hFM0).2 ((sup_comm _ _).trans hM0cov.symm)
  have hM0T : IsSec6MType n (↥(oddCoreOf Kx ⊔ F) ⧸ pPrimeCore 2 ↥(oddCoreOf Kx ⊔ F)) :=
    hFM.2.congr (nonempty_quot_mulEquiv_of_covers hFM0 hcovT).some
  refine ⟨oddCoreOf Kx ⊔ F, hM0K, ?_, hM0T, ?_⟩
  ·
    refine le_antisymm ?_ (sup_le hM0K inf_le_right)
    show sSup {G | Sec6KComp X n (cen x) G} ≤ _
    refine sSup_le fun G hG => ?_
    by_cases hGF : G = F
    · rw [hGF]
      exact le_sup_of_le_left hFM0
    · obtain ⟨L, hL, hLG⟩ := hC.piece x hxMQ hx2 G hG
      rcases hL with hA' | hM
      · exfalso
        rw [huniq L hA'] at hLG
        exact hGF (eq_of_isPCompIn_of_le (bc_isPCompIn hG) (bc_isPCompIn hF) hLG hPA hPAq)
      · have heq := sec6_mpiece_unpumped hS hK hC hx hx2 hM hG hLG
        refine heq.le.trans (sup_le ?_ ?_)
        · exact (bc_oddCoreOf_le_oddCoreOf_sec6K hG).trans (le_sup_left.trans le_sup_left)
        · exact le_sup_of_le_right (le_inf
            (((oTwoPrimeOf_le _).trans inf_le_left).trans (bc_le_sec6M hM))
            (hLG.trans (bc_le_sec6K hG)))
  ·
    have htM0 : t ∈ normalizer ((oddCoreOf Kx ⊔ F : Subgroup X) : Set X) :=
      mem_normalizer_sup
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6K_cen_normal n x (bc_mem_cen_symm hxt)))
        htF
    have hfM0 : f ∈ oddCoreOf Kx ⊔ F := hFM0 hfF
    have hftM0 : CentModOdd (oddCoreOf Kx ⊔ F) (f * t) :=
      bc_centModOdd_of_cover hFM0 hM0cov
        (mem_normalizer_oddCoreOf_of_mem_normalizer (mul_mem (le_normalizer hfM0) htM0))
        fun r hr => (hOFK.trans hOKM0) (hft r hr)
    have hntM0 : ¬ CentModOdd (oddCoreOf Kx ⊔ F) t := by
      intro h
      apply hnt
      intro a ha
      have h1 : ⁅a, t⁆ ∈ F := by
        have e : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact F.mul_mem ha (bc_conj_mem htF (F.inv_mem ha))
      exact inf_pPrimeCoreOf_le_pPrimeCoreOf hFM0 ⟨h1, h a (hFM0 ha)⟩
    have hPApc' : IsPCompIn 2 ((oddCoreOf Kx ⊔ F) ⊓ cen t) (sec6Piece A x) :=
      bc_isPCompIn_of_le hPApc (le_inf (hPA.trans hFM0) hPAt)
        (le_inf inf_le_right (inf_le_left.trans (hM0K.trans hKxx)))
    show sSup {E | Sec6KComp X n ((oddCoreOf Kx ⊔ F) ⊓ cen t) E} ≤ _
    refine sSup_le fun E hE => ?_
    have hEpc := bc_isPCompIn hE
    have hEM0 : E ≤ oddCoreOf Kx ⊔ F := hEpc.1.trans inf_le_left
    have hEt : E ≤ cen t := hEpc.1.trans inf_le_right
    rcases hE with ⟨-, hEn⟩ | hEM
    · by_cases hEP : E = sec6Piece A x
      · rw [hEP]
        exact le_sup_of_le_right (hPAA.trans (le_sSup (s := {A | Sec5Comp X n (cen t) A}) hA))
      · exact absurd (bc_pump_two hM0T htt htM0 hfM0 hftM0 hntM0 hEM0 hEt hEn
          (hPA.trans hFM0) hPAt hPAn fun p hp p' hp' => bc_comm_mem hEpc hPApc' hEP hp hp')
          id
    · exfalso
      have hcovE := covers_of_card_le hEM0 (modOddCard_eq_of_sec6MComp hM0T hEM).symm.le
      apply hntM0
      refine bc_centModOdd_of_cover hEM0 (bc_cov hEM0 hcovE)
        (mem_normalizer_oddCoreOf_of_mem_normalizer htM0) fun e he => ?_
      rw [commutatorElement_eq_one_iff_mul_comm.2 (bc_comm_of_mem_cen (hEt he))]
      exact one_mem _

theorem sec6L61_of
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hK : Sec6Lemma51 X n) (hLa : ∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x)
    (hC : Sec6CtrlAt X n t) : Sec6L61 X n t :=
  ⟨hLa, (sec6L61_bc hS hK hLa hC).1, (sec6L61_bc hS hK hLa hC).2⟩

end CFSG.OddStandard.Solomon75
