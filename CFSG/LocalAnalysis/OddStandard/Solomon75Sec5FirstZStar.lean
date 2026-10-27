module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoNtwo
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Simple
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ly.Primitive

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.Sec5Two
  CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem exists_pComp_ge_comp (h : Sec5Data X n z (zpowers z) S) {M A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hAM : A ≤ M) :
    ∃ J : Subgroup X, IsPCompIn 2 M J ∧ A ≤ J := by
  have hzA : z ∈ A := z_mem_comp h hA
  have hzM : z ∈ M := hAM hzA
  have hAC : A ≤ centralizer ({z} : Set X) := comp_le hA
  set zM : ↥M := ⟨z, hzM⟩ with hzMdef
  have hz2 : zM ^ 2 = 1 := by
    apply Subtype.ext
    show z ^ 2 = 1
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have hcen : centralizer ({zM} : Set ↥M) = (centralizer ({z} : Set X)).subgroupOf M :=
    centralizer_singleton_subgroup hzM
  have hEC : A.subgroupOf M ≤ centralizer ({zM} : Set ↥M) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono M hAC
  have huE : zM ∈ A.subgroupOf M := hzA
  have hE : IsPComponent 2 ((A.subgroupOf M).subgroupOf (centralizer ({zM} : Set ↥M))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hAC hAM).2
      (isPComponent_subgroupOf_mono (le_inf hAC hAM) inf_le_left hA.isPCompIn.2)
  have hEL : A.subgroupOf M ≤ pLayer ↥M 2 := by
    have hB : IsPGroup 2 (Subgroup.zpowers zM) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using orderOf_dvd_of_pow_eq_one hz2 : orderOf zM ∣ 2 ^ 1)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hbal := layer_balance (Subgroup.zpowers zM) hB
    have hcz : centralizer ((Subgroup.zpowers zM : Subgroup ↥M) : Set ↥M) =
        centralizer ({zM} : Set ↥M) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hEC' : A.subgroupOf M ≤ centralizer ((Subgroup.zpowers zM : Subgroup ↥M) : Set ↥M) := by
      rw [hcz]
      exact hEC
    have hE' : IsPComponent 2 ((A.subgroupOf M).subgroupOf
        (centralizer ((Subgroup.zpowers zM : Subgroup ↥M) : Set ↥M))) := by
      rw [hcz]
      exact hE
    have h1 := le_sSup (s := {L | IsPComponent 2 L}) hE'
    have h2 := Subgroup.map_mono (f := (centralizer ((Subgroup.zpowers zM : Subgroup ↥M) :
      Set ↥M)).subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le hEC'] at h2
    exact h2.trans hbal
  obtain ⟨M_D, hM_D, hEM_D⟩ := exists_isPComponent_le_of_mem_pLayer hEC huE hz2 hE hEL
  refine ⟨M_D.map M.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have h := Subgroup.comap_map_eq_self_of_injective M.subtype_injective M_D
    change IsPComponent 2 ((M_D.map M.subtype).comap M.subtype)
    rw [h]
    exact hM_D
  · have h1 := Subgroup.map_mono (f := M.subtype) hEM_D
    rwa [Subgroup.map_subgroupOf_eq_of_le hAM] at h1

theorem mem_centralizerSection_of_mem_pComp {M J J' : Subgroup X} (hJ : IsPCompIn 2 M J)
    (hJ' : IsPCompIn 2 M J') (hJJ' : J ≠ J') (hzJ' : z ∈ J') :
    z ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  refine normalizes_isPCompIn_of_comm_mem hJ (Subgroup.le_normalizer (hJ'.1 hzJ')) ?_
  intro l hl
  have h1 : ⁅l, z⁆ ∈ pPrimeCoreOf 2 M := commutator_mem_oddCoreOf_of_ne hJ hJ' hJJ' hl hzJ'
  exact h1

private theorem isAhatIntr_of_sec5Comp (h : Sec5Data X n z (zpowers z) S) {A : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) : IsAhatIntr X z A :=
  ⟨comp_le hA, z_mem_comp h hA, hA.isPCompIn.2, n, h.maxdeg.1, hA.2⟩

private theorem oTwoPrimeOf_inf_centralizer_eq (h : Sec5Data X n z (zpowers z) S)
    {M A J : Subgroup X} (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hAM : A ≤ M)
    (hJ : IsPCompIn 2 M J) (hAJ : A ≤ J) (hz : z ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    oTwoPrimeOf (J ⊓ centralizer ({z} : Set X)) = A ∧ A ⊔ pPrimeCoreOf 2 J = J := by
  set C : Subgroup X := centralizer ({z} : Set X)
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJ.1).1 (isPComponent_two_iff.1 hJ.2).2
  have hAq : IsTwoGenQuasi ↥A :=
    (isTwoGenQuasi_subgroupOf_iff (comp_le hA)).1 (isPComponent_two_iff.1 hA.isPCompIn.2).2
  have hAC : A ≤ C := comp_le hA
  have hT : IsPGroup 2 ↥(Subgroup.zpowers z) := aux_isPGroup_zpowers_of_sq hz2
  have hTc : Subgroup.zpowers z ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Subgroup.zpowers_le.2 hz
  have hcov0 := oTwoPrimeOf_inf_centralizer_covers_pgroup hT hJq.1
    (fun t ht => (hTc ht).2.1) (fun k hk t ht => (hTc ht).2.2 k hk)
  rw [aux_centralizer_zpowers] at hcov0
  set E : Subgroup X := oTwoPrimeOf (J ⊓ C) with hE
  have hEJC : E ≤ J ⊓ C := oTwoPrimeOf_le _
  have hEJ : E ≤ J := hEJC.trans inf_le_left
  have hcovE : E ⊔ pPrimeCoreOf 2 J = J := (covers_subgroupOf_iff hEJ).1 hcov0
  set H : Subgroup X := M ⊓ C with hH
  have hHM : H ≤ M := inf_le_left
  have hEH : E ≤ H := le_inf (hEJ.trans hJ.1) (hEJC.trans inf_le_right)
  have hEq : IsTwoGenQuasi ↥E :=
    isTwoGenQuasi_of_covers hEJ hcov0 (primeResidual_oTwoPrimeOf _) hJq
  have hJsub : (J.subgroupOf M).IsSubnormal := (isPComponent_two_iff.1 hJ.2).1
  have hJH : (J.subgroupOf H).IsSubnormal := by
    have := hJsub.comap (Subgroup.inclusion hHM)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hAeq : J ⊓ C = J ⊓ H := by
    ext x
    simp only [Subgroup.mem_inf, hH]
    constructor
    · rintro ⟨hxJ, hxC⟩
      exact ⟨hxJ, hJ.1 hxJ, hxC⟩
    · rintro ⟨hxJ, -, hxC⟩
      exact ⟨hxJ, hxC⟩
  have hJCsub : ((J ⊓ C).subgroupOf H).IsSubnormal := by
    rw [hAeq, Subgroup.inf_subgroupOf_right]
    exact hJH
  have hEsub : (E.subgroupOf H).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_of_subnormal (A := J ⊓ C) (H := H) (B := E)
      (by rw [hAeq]; exact inf_le_right) hEJC hJCsub (normal_subgroupOf_oTwoPrimeOf _)
  have hEpc : IsPCompIn 2 H E :=
    ⟨hEH, isPComponent_two_iff.2 ⟨hEsub, (isTwoGenQuasi_subgroupOf_iff hEH).2 hEq⟩⟩
  have hAH : A ≤ H := le_inf hAM hAC
  have hApc : IsPCompIn 2 H A :=
    ⟨hAH, isPComponent_subgroupOf_mono hAH inf_le_right hA.isPCompIn.2⟩
  have hAE : A ≤ E := by
    have h1 : oTwoPrimeOf A = A := oTwoPrimeOf_eq_self_of_primeResidual hAq.1
    have h2 := oTwoPrimeOf_mono (le_inf hAJ hAC : A ≤ J ⊓ C)
    rwa [h1] at h2
  have hAEeq : A = E := eq_of_isPCompIn_of_le hApc hEpc le_rfl hAE hAq
  refine ⟨hAEeq.symm, ?_⟩
  rw [hAEeq]
  exact hcovE

theorem isIntrinsicIn_of_pComp (h : Sec5Data X n z (zpowers z) S) {M A J : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hAM : A ≤ M) (hJ : IsPCompIn 2 M J)
    (hAJ : A ≤ J) (hz : z ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    IsIntrinsicIn X M J z ∧ IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := by
  obtain ⟨hE, hcov⟩ := oTwoPrimeOf_inf_centralizer_eq h hA hAM hJ hAJ hz
  have hcov' : A.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := (covers_subgroupOf_iff hAJ).2 hcov
  refine ⟨⟨h.orderOf_z, hAJ (z_mem_comp h hA), hJ, ?_, A, isAhatIntr_of_sec5Comp h hA, ?_⟩,
    (isDoubleCoverOfAlt_quot_iff_of_covers hAJ hcov' n).1 hA.2⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, hE, sup_comm]
    exact hcov.symm
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, hE]
    exact (sup_eq_right.2 (oddCoreOf_le A)).symm

theorem isSylowTwoIn_zStar_K0_of_mem (h : Sec5Data X n z (zpowers z) S) {M : Subgroup X}
    (hzK : z ∈ zStar (K0 X n M)) : IsSylowTwoIn (zStar (K0 X n M)) (zpowers z) := by
  have hz_sq : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_z] at this
  set K := K0 X n M with hK
  have hW : ∀ L : Subgroup X, (∃ u, IsIntrinsicIn X M L u) →
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n →
        ∃ u ∈ ({z} : Set X), IsIntrinsicIn X M L u := by
    rintro L ⟨u₀, hu₀⟩ hLn
    have hLK : L ≤ K := le_sSup ⟨⟨u₀, hu₀⟩, hLn⟩
    have hzc : z ∈ centralizerSection L (pPrimeCoreOf 2 L) :=
      normalizes_isPCompIn_of_comm_mem (hu₀.isPCompIn_K0 hLn) (Subgroup.le_normalizer hzK.1)
        fun l hl => hzK.2.2.2 l (hLK hl)
    obtain ⟨u, hu, huz⟩ := hu₀.exists_witness_centralizer_singleton hz_sq hzc
    obtain ⟨h1, h2, -⟩ := hu.descend_singleton hLn hz_sq hzc huz
    have hB : oTwoPrimeOf (L ⊓ centralizer ({z} : Set X)) ≤ K0 X n (centralizer ({z} : Set X)) :=
      (le_sSup ⟨⟨u, h1⟩, h2⟩ : _ ≤ K0 X n (M ⊓ centralizer ({z} : Set X))).trans
        (K0_le_K0_centralizer h.hypA h.maxdeg h.orderOf_z inf_le_right)
    have huz' : u = z := eq_z_of_mem_zStar h hB h2 h1.mem_zStar h1.1 huz
    exact ⟨u, by rw [huz']; exact Set.mem_singleton z, hu⟩
  have hZK := zStar_K0_le_sup_witnesses n M {z} hW
  have hZK' : zStar K ≤ pPrimeCoreOf 2 K ⊔ zpowers z :=
    hZK.trans (sup_le_sup_left ((Subgroup.closure_le _).2 fun u hu =>
      (Set.mem_singleton_iff.1 hu.1) ▸ Subgroup.mem_zpowers z) _)
  exact isSylowTwoIn_of_le_sup_odd (Subgroup.zpowers_le.2 hzK) h.isPGroup_Z
    (odd_card_oddCoreOf K) (Subgroup.zpowers_le.2 (mem_normalizer_pPrimeCoreOf_of_mem hzK.1))
    hZK'

theorem comm_mem_oddCore_of_isSylowTwoIn (h : Sec5Data X n z (zpowers z) S) {M : Subgroup X}
    (hsyl : IsSylowTwoIn (zStar (K0 X n M)) (zpowers z)) :
    ∀ m ∈ M, ⁅m, z⁆ ∈ oddCoreOf M := by
  set K := K0 X n M with hK
  have hKM : K ≤ M := K0_le n M
  have hCn : ∀ c ∈ M, c ∈ normalizer (K : Set X) := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_mem_K0 n (Subgroup.le_normalizer hc) hy
    · intro hy
      have := conj_mem_K0 n (Subgroup.le_normalizer (M.inv_mem hc)) hy
      simpa [mul_assoc] using this
  have hAC : zStar K ≤ M := inf_le_left.trans hKM
  have hAn : ∀ c ∈ M, ∀ a ∈ zStar K, c * a * c⁻¹ ∈ zStar K := fun c hc a ha =>
    conj_mem_zStar (hCn c hc) ha
  have hzM : z ∈ M := hAC (hsyl.1 (Subgroup.mem_zpowers z))
  have hKsub : (K.subgroupOf M).IsSubnormal := (K0_subgroupOf_normal n M).isSubnormal
  have hPO : pPrimeCoreOf 2 K ≤ oddCoreOf M := pPrimeCoreOf_le_oddCoreOf hKM hKsub
  have hOn : ∀ x ∈ M, ∀ o ∈ oddCoreOf M, x * o * x⁻¹ ∈ oddCoreOf M := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf M hx) o).1 ho
  have hcz : ∀ w ∈ zpowers z, w * z = z * w := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_left (Commute.refl z) k).eq
  have hcomm : ∀ a ∈ oddCoreOf M ⊔ zpowers z, ⁅a, z⁆ ∈ oddCoreOf M := by
    intro a ha
    have hzn : zpowers z ≤ normalizer (oddCoreOf M : Set X) :=
      Subgroup.zpowers_le.2 (le_normalizer_oddCoreOf M hzM)
    rw [sup_comm] at ha
    obtain ⟨w, hw, o, ho, rfl⟩ := exists_mul_of_mem_sup hzn ha
    have hwM : w ∈ M := (Subgroup.zpowers_le.2 hzM) hw
    have hwz : ⁅w, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcz w hw)
    have hoz : ⁅o, z⁆ ∈ oddCoreOf M := by
      have e : ⁅o, z⁆ = o * (z * o⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (oddCoreOf M).mul_mem ho (hOn z hzM _ ((oddCoreOf M).inv_mem ho))
    have e : ⁅w * o, z⁆ = w * ⁅o, z⁆ * w⁻¹ * ⁅w, z⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hwz, mul_one]
    exact hOn w hwM _ hoz
  intro m hm
  obtain ⟨a, ha, m', hm', rfl⟩ := exists_mul_mem_normalizer_of_isSylowTwoIn hAC hAn hsyl hm
  have haO : a ∈ oddCoreOf M ⊔ zpowers z :=
    (sup_le_sup hPO le_rfl) (zStar_le_pPrimeCoreOf_sup hsyl ha)
  have hm'z : ⁅m', z⁆ = 1 := by
    rw [normalizer_zpowers_eq_centralizer h.orderOf_z] at hm'
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 hm'.1)
  have haM : a ∈ M := hAC ha
  have e : ⁅a * m', z⁆ = a * ⁅m', z⁆ * a⁻¹ * ⁅a, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, hm'z]
  simpa using hcomm a haO

section Counting

variable {G : Type} [Group G] [Finite G]

private theorem eq_one_of_mem_pgroup_inf_odd {T O : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hO : Odd (Nat.card O)) {x : G} (hxT : x ∈ T) (hxO : x ∈ O) : x = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨x, hxT⟩
  have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hd : orderOf x ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) := (Nat.coprime_two_left.2 hO).pow_left k
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop (hk' ▸ dvd_rfl) hd
  exact orderOf_eq_one_iff.1 h1

private theorem card_mul_dvd_two_mul_card {T₁ T₂ O : Subgroup G}
    (hT₁ : IsPGroup 2 ↥T₁) (hT₂ : IsPGroup 2 ↥T₂) (hO : Odd (Nat.card O))
    (h₁ : T₁ ≤ normalizer (O : Set G)) (h₂ : T₂ ≤ normalizer (O : Set G))
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, ⁅a, b⁆ ∈ O)
    (hZ : Nat.card ↥(T₁ ⊓ (T₂ ⊔ O)) ≤ 2) :
    Nat.card T₁ * Nat.card T₂ ∣ 2 * Nat.card G := by
  set N : Subgroup G := normalizer (O : Set G)
  have hON : O ≤ N := Subgroup.le_normalizer
  set O' : Subgroup ↥N := O.subgroupOf N
  haveI : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hON).2 le_rfl
  set q : ↥N →* ↥N ⧸ O' := QuotientGroup.mk' O'
  set ι₁ : ↥T₁ →* ↥N ⧸ O' := q.comp (Subgroup.inclusion h₁)
  set ι₂ : ↥T₂ →* ↥N ⧸ O' := q.comp (Subgroup.inclusion h₂)
  have hc : ∀ (a : ↥T₁) (b : ↥T₂), Commute (ι₁ a) (ι₂ b) := by
    intro a b
    have h1 : ⁅(Subgroup.inclusion h₁ a : ↥N), Subgroup.inclusion h₂ b⁆ ∈ O' :=
      hcomm a a.2 b b.2
    have h2 : q ⁅(Subgroup.inclusion h₁ a : ↥N), Subgroup.inclusion h₂ b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  set φ : ↥T₁ × ↥T₂ →* ↥N ⧸ O' := MonoidHom.noncommCoprod ι₁ ι₂ hc with hφ
  have hker_mem : ∀ p ∈ φ.ker, ((p.1 : G) * (p.2 : G)) ∈ O := by
    intro p hp
    have h1 : ι₁ p.1 * ι₂ p.2 = 1 := by
      have := MonoidHom.mem_ker.1 hp
      rwa [hφ, MonoidHom.noncommCoprod_apply] at this
    have h2 : q ((Subgroup.inclusion h₁ p.1 : ↥N) * Subgroup.inclusion h₂ p.2) = 1 := by
      rw [map_mul]; exact h1
    exact (QuotientGroup.eq_one_iff (N := O') _).1 h2
  have hmem : ∀ p ∈ φ.ker, (p.1 : G) ∈ T₂ ⊔ O := by
    intro p hp
    have hab := hker_mem p hp
    have h1 : (p.1 : G) * (p.2 : G) * (p.2 : G)⁻¹ ∈ O ⊔ T₂ :=
      Subgroup.mul_mem_sup hab (T₂.inv_mem p.2.2)
    rw [mul_inv_cancel_right, sup_comm] at h1
    exact h1
  let g : ↥φ.ker → ↥(T₁ ⊓ (T₂ ⊔ O)) := fun p => ⟨(p.1.1 : G), p.1.1.2, hmem p.1 p.2⟩
  have hg : Function.Injective g := by
    intro p p' hpp
    have ha : (p.1.1 : G) = (p'.1.1 : G) :=
      congrArg (fun x : ↥(T₁ ⊓ (T₂ ⊔ O)) => (x : G)) hpp
    have hab := hker_mem p.1 p.2
    have hab' := hker_mem p'.1 p'.2
    rw [← ha] at hab'
    have hbb : (p.1.2 : G)⁻¹ * (p'.1.2 : G) ∈ O := by
      have e : ((p.1.1 : G) * (p.1.2 : G))⁻¹ * ((p.1.1 : G) * (p'.1.2 : G)) =
          (p.1.2 : G)⁻¹ * (p'.1.2 : G) := by group
      rw [← e]
      exact O.mul_mem (O.inv_mem hab) hab'
    have hb1 : (p.1.2 : G)⁻¹ * (p'.1.2 : G) = 1 :=
      eq_one_of_mem_pgroup_inf_odd hT₂ hO (T₂.mul_mem (T₂.inv_mem p.1.2.2) p'.1.2.2) hbb
    have hb : p.1.2 = p'.1.2 := Subtype.ext (inv_mul_eq_one.1 hb1)
    exact Subtype.ext (Prod.ext (Subtype.ext ha) hb)
  have hker : Nat.card φ.ker ≤ 2 := (Nat.card_le_card_of_injective g hg).trans hZ
  have hrange_dvd : Nat.card φ.range ∣ Nat.card G := by
    have h1 : Nat.card φ.range ∣ Nat.card (↥N ⧸ O') := Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (↥N ⧸ O') ∣ Nat.card ↥N :=
      Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup O').symm
    exact h1.trans (h2.trans (Subgroup.card_subgroup_dvd_card N))
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [Nat.card_prod] at hcard
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hkd : Nat.card φ.ker ∣ 2 := by
    rcases (by omega : Nat.card φ.ker = 1 ∨ Nat.card φ.ker = 2) with h | h
    · rw [h]; exact one_dvd 2
    · rw [h]
  rw [← hcard]
  exact Nat.mul_dvd_mul hkd hrange_dvd

private theorem card_inf_sup_le_two {L T₁ T₂ O : Subgroup G} {m : ℕ}
    (hdc : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) m) (hT₁L : T₁ ≤ L) (hT₁ : IsPGroup 2 ↥T₁)
    (hO : Odd (Nat.card O)) (hLO : L ≤ normalizer (O : Set G))
    (hT₂O : T₂ ≤ normalizer (O : Set G)) (hcomm : ∀ a ∈ L, ∀ b ∈ T₂, ⁅a, b⁆ ∈ O) :
    Nat.card ↥(T₁ ⊓ (T₂ ⊔ O)) ≤ 2 := by
  have hLOle : L ⊓ O ≤ oddCoreOf L :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun a ha => mem_normalizer_inf (Subgroup.le_normalizer ha) (hLO ha))
      (Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le inf_le_right))
  have hx : ∀ x ∈ T₁ ⊓ (T₂ ⊔ O), ∀ a ∈ L, ⁅a, x⁆ ∈ O := by
    rintro x ⟨-, hxs⟩ a ha
    obtain ⟨b, hb, o, ho, rfl⟩ := exists_mul_of_mem_sup hT₂O hxs
    have e : ⁅a, b * o⁆ = ⁅a, b⁆ * (b * ⁅a, o⁆ * b⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hao : ⁅a, o⁆ ∈ O := by
      have e2 : ⁅a, o⁆ = (a * o * a⁻¹) * o⁻¹ := by simp only [commutatorElement_def]
      rw [e2]
      exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hLO ha) o).1 ho) (O.inv_mem ho)
    exact O.mul_mem (hcomm a ha b hb) ((Subgroup.mem_normalizer_iff.1 (hT₂O hb) _).1 hao)
  have hxL : ∀ x : ↥(T₁ ⊓ (T₂ ⊔ O)), (x : G) ∈ L := fun x => hT₁L x.2.1
  let f : ↥(T₁ ⊓ (T₂ ⊔ O)) → center (↥L ⧸ pPrimeCore 2 ↥L) := fun x =>
    ⟨QuotientGroup.mk ⟨(x : G), hxL x⟩, by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hyx : ⁅(y : G), (x : G)⁆ ∈ L ⊓ O :=
        ⟨by simp only [commutatorElement_def]
            exact L.mul_mem (L.mul_mem (L.mul_mem y.2 (hxL x)) (L.inv_mem y.2)) (L.inv_mem (hxL x)),
          hx x x.2 y y.2⟩
      obtain ⟨hmL, hmP⟩ := mem_oddCoreOf_iff.1 (hLOle hyx)
      have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥L)) ⁅y, (⟨(x : G), hxL x⟩ : ↥L)⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 hmP
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1⟩
  have hf : Function.Injective f := by
    intro x x' hxx
    have h1 : (QuotientGroup.mk ⟨(x : G), hxL x⟩ : ↥L ⧸ pPrimeCore 2 ↥L) =
        QuotientGroup.mk ⟨(x' : G), hxL x'⟩ := congrArg Subtype.val hxx
    rw [QuotientGroup.eq] at h1
    have h2 : ((x : G)⁻¹ * (x' : G)) ∈ oddCoreOf L :=
      mem_oddCoreOf_iff.2 ⟨L.mul_mem (L.inv_mem (hxL x)) (hxL x'), h1⟩
    have h3 : ((x : G)⁻¹ * (x' : G)) ∈ T₁ := T₁.mul_mem (T₁.inv_mem x.2.1) x'.2.1
    have h4 := eq_one_of_mem_pgroup_inf_odd hT₁ (odd_card_oddCoreOf L) h3 h2
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  calc Nat.card ↥(T₁ ⊓ (T₂ ⊔ O)) ≤ Nat.card (center (↥L ⧸ pPrimeCore 2 ↥L)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 := hdc.2.1

private theorem two_pow_thirteen_dvd {L L' O : Subgroup G}
    (hdc : ∃ m, 8 ≤ m ∧ IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) m)
    (hdc' : ∃ m, 8 ≤ m ∧ IsDoubleCoverOfAlt (↥L' ⧸ pPrimeCore 2 ↥L') m)
    (hO : Odd (Nat.card O)) (hLO : L ≤ normalizer (O : Set G))
    (hL'O : L' ≤ normalizer (O : Set G)) (hcomm : ∀ a ∈ L, ∀ b ∈ L', ⁅a, b⁆ ∈ O) :
    2 ^ 13 ∣ Nat.card G := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : ∀ K : Subgroup G, (∃ m, 8 ≤ m ∧ IsDoubleCoverOfAlt (↥K ⧸ pPrimeCore 2 ↥K) m) →
      2 ^ 7 ∣ Nat.card K := by
    rintro K ⟨m, hm, hK⟩
    have hcardK : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = m.factorial :=
      natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hK
    have h2 : 2 ^ 7 ∣ m.factorial :=
      (show 2 ^ 7 ∣ Nat.factorial 8 by decide).trans (Nat.factorial_dvd_factorial hm)
    have h3 : Nat.card K = Nat.card (↥K ⧸ pPrimeCore 2 ↥K) * Nat.card (pPrimeCore 2 ↥K) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [h3, hcardK]
    exact h2.trans (Dvd.intro _ rfl)
  obtain ⟨K₁, hK₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 2 (h7 L hdc)
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L') 2 (h7 L' hdc')
  set T₁ : Subgroup G := K₁.map L.subtype with hT₁
  set T₂ : Subgroup G := K₂.map L'.subtype with hT₂
  have hT₁card : Nat.card T₁ = 2 ^ 7 := by
    rw [hT₁, Subgroup.card_map_of_injective L.subtype_injective]; exact hK₁
  have hT₂card : Nat.card T₂ = 2 ^ 7 := by
    rw [hT₂, Subgroup.card_map_of_injective L'.subtype_injective]; exact hK₂
  have hT₁p : IsPGroup 2 ↥T₁ := IsPGroup.of_card hT₁card
  have hT₂p : IsPGroup 2 ↥T₂ := IsPGroup.of_card hT₂card
  have hT₁L : T₁ ≤ L := Subgroup.map_subtype_le K₁
  have hT₂L' : T₂ ≤ L' := Subgroup.map_subtype_le K₂
  obtain ⟨m, -, hdcm⟩ := hdc
  have hZ := card_inf_sup_le_two hdcm hT₁L hT₁p hO hLO (hT₂L'.trans hL'O)
    (fun a ha b hb => hcomm a ha b (hT₂L' hb))
  have hmain := card_mul_dvd_two_mul_card hT₁p hT₂p hO (hT₁L.trans hLO) (hT₂L'.trans hL'O)
    (fun a ha b hb => hcomm a (hT₁L ha) b (hT₂L' hb)) hZ
  rw [hT₁card, hT₂card] at hmain
  have h14 : 2 * 2 ^ 13 ∣ 2 * Nat.card G := by
    have e : (2 : ℕ) ^ 7 * 2 ^ 7 = 2 * 2 ^ 13 := by norm_num
    rwa [e] at hmain
  exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 h14

private theorem not_two_pow_nine_dvd_card
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) (hne : KProd G ≠ ⊥) : ¬ 2 ^ 9 ∣ Nat.card G := by
  rcases nonempty_equiv_of_ne_bot_KProd hnonab ht hne with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
    norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
    norm_num

private theorem mem_normalizer_map_subgroup {Y : Type} [Group Y] (ψ : Y →* G) {K : Subgroup Y}
    {g : Y} (hg : g ∈ normalizer (K : Set Y)) :
    ψ g ∈ normalizer ((K.map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg s).1 hs, by simp [map_mul, map_inv]⟩
  · rintro ⟨s, hs, hsy⟩
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 ((normalizer (K : Set Y)).inv_mem hg) s).1 hs
      simpa using h1
    · have h2 : ψ g * y * (ψ g)⁻¹ = ψ s := hsy.symm
      have h3 : y = (ψ g)⁻¹ * ψ s * ψ g := by rw [← h2]; group
      rw [h3]
      simp [map_mul, map_inv]

end Counting

private abbrev OQ (J : Subgroup X) : Type := ↥J ⧸ pPrimeCore 2 ↥J

private abbrev CQ (J : Subgroup X) : Type := OQ J ⧸ center (OQ J)

private noncomputable def psiQ (J : Subgroup X) : ↥J →* CQ J :=
  (QuotientGroup.mk' (center (OQ J))).comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))

private theorem card_comap_subtype_dvd {Y : Type} [Group Y] (R J : Subgroup Y) :
    Nat.card (R.comap J.subtype) ∣ Nat.card R := by
  have h1 : Nat.card ((R.comap J.subtype).map J.subtype) = Nat.card (R.comap J.subtype) :=
    Subgroup.card_map_of_injective J.subtype_injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)

private theorem not_mem_center_of_not_mem_centralizerSection {J : Subgroup X} (hzJ : z ∈ J)
    (hzc : z ∉ centralizerSection J (pPrimeCoreOf 2 J)) :
    QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨z, hzJ⟩ : ↥J) ∉ center (OQ J) := by
  intro hcen
  apply hzc
  refine ⟨Subgroup.le_normalizer hzJ, mem_normalizer_pPrimeCoreOf_of_mem hzJ, fun k hk => ?_⟩
  have h1 : ⁅(QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨k, hk⟩ : ↥J)),
      (QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨z, hzJ⟩ : ↥J))⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hcen _)
  rw [← map_commutatorElement] at h1
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

private theorem isAhatIntr_psiQ (h : Sec5Data X n z (zpowers z) S) {A J : Subgroup X}
    (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hAJ : A ≤ J) (hzJ : z ∈ J)
    (hzc : z ∉ centralizerSection J (pPrimeCoreOf 2 J)) :
    IsAhatIntr (CQ J) (psiQ J ⟨z, hzJ⟩) ((A.subgroupOf J).map (psiQ J)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIAJ : IsAhatIntr ↥J ⟨z, hzJ⟩ (A.subgroupOf J) :=
    (isAhatIntr_of_sec5Comp h hA).subgroupOf hzJ hAJ
  have hz2J : orderOf (⟨z, hzJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_z
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hbar := hIAJ.map_odd hNodd hz2J
  have hzbar2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨z, hzJ⟩ : ↥J)) = 2 :=
    ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two hNodd hz2J
  have hzbar := not_mem_center_of_not_mem_centralizerSection hzJ hzc
  have := hbar.map_center hzbar2 hzbar
  rw [psiQ, ← Subgroup.map_map]
  exact this

private theorem false_of_noncentral_comps
    (h : Sec5Data X n z (zpowers z) S) {M A A' J : Subgroup X}
    (hM : M ≠ ⊤) (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') (hAA' : A ≠ A')
    (hJ : IsPCompIn 2 M J) (hAJ : A ≤ J) (hA'J : A' ≤ J)
    (hzc : z ∉ centralizerSection J (pPrimeCoreOf 2 J)) : False := by
  have hzJ : z ∈ J := hAJ (z_mem_comp h hA)
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJ.1).1 (isPComponent_two_iff.1 hJ.2).2
  have hQ : IsQuasisimple (OQ J) := hJq.2
  haveI : IsSimpleGroup (CQ J) := hQ.2.1
  have hnonab : ∃ a b : CQ J, a * b ≠ b * a := hQ.2.2
  have hψsurj : Function.Surjective (psiQ J) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hIA := isAhatIntr_psiQ h hA hAJ hzJ hzc
  have hIA' := isAhatIntr_psiQ h hA' hA'J hzJ hzc
  have hzbar := not_mem_center_of_not_mem_centralizerSection hzJ hzc
  have hz2 : orderOf (psiQ J ⟨z, hzJ⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨z, hzJ⟩ : ↥J) ^ 2 = 1 := by
        apply Subtype.ext
        show z ^ 2 = 1
        rw [← h.orderOf_z]
        exact pow_orderOf_eq_one z
      rw [this, map_one]
    · intro h1
      exact hzbar ((QuotientGroup.eq_one_iff _).1 h1)
  have hlt : Nat.card (CQ J) < Nat.card X := by
    have h1 : Nat.card (CQ J) ≤ Nat.card ↥J := Nat.card_le_card_of_surjective _ hψsurj
    have h2 : Nat.card ↥J ≤ Nat.card ↥M := Subgroup.card_le_of_le hJ.1
    have h3 : Nat.card ↥M < Nat.card X := by
      have hdvd : Nat.card M ∣ Nat.card X := Subgroup.card_subgroup_dvd_card M
      exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) fun heq =>
        hM ((Subgroup.card_eq_iff_eq_top M).1 heq)
    omega
  have hKP := h.cex.ih (CQ J) hlt (psiQ J ⟨z, hzJ⟩) hz2 _ (Or.inl hIA)
  have hne : KProd (CQ J) ≠ ⊥ := by
    intro hbot
    have hmem : psiQ J ⟨z, hzJ⟩ ∈ (A.subgroupOf J).map (psiQ J) := hIA.2.1
    have h1 := hKP hmem
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have h9 := not_two_pow_nine_dvd_card hnonab hz2 hne
  set OD : Subgroup X := pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X)))
  set Ot : Subgroup (CQ J) := (OD.comap J.subtype).map (psiQ J)
  have hOdd : Odd (Nat.card Ot) := by
    have h1 : Nat.card Ot ∣ Nat.card (OD.comap J.subtype) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (OD.comap J.subtype) ∣ Nat.card OD := card_comap_subtype_dvd OD J
    exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (h1.trans h2)
  have hLO : ∀ {B : Subgroup X}, Sec5Comp X n (centralizer ({z} : Set X)) B →
      (B.subgroupOf J).map (psiQ J) ≤ normalizer (Ot : Set (CQ J)) := by
    intro B hB y hy
    obtain ⟨g, hg, rfl⟩ := hy
    refine mem_normalizer_map_subgroup (psiQ J) ?_
    have hgB : (g : X) ∈ B := hg
    have hgOD : (g : X) ∈ normalizer (OD : Set X) :=
      mem_normalizer_pPrimeCoreOf_of_mem (comp_le_K0 hB hgB)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.1 hgOD (x : X)
  have hcomm : ∀ a ∈ (A.subgroupOf J).map (psiQ J), ∀ b ∈ (A'.subgroupOf J).map (psiQ J),
      ⁅a, b⁆ ∈ Ot := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_commutatorElement]
    refine Subgroup.mem_map_of_mem _ ?_
    exact comm_mem_of_ne hA hA' hAA' (a : X) ha (b : X) hb
  have h13 : 2 ^ 13 ∣ Nat.card (CQ J) :=
    two_pow_thirteen_dvd hIA.2.2.2 hIA'.2.2.2 hOdd (hLO hA) (hLO hA') hcomm
  exact h9 ((pow_dvd_pow 2 (by norm_num : 9 ≤ 13)).trans h13)

theorem false_of_two_comps_le_pComp
    (h : Sec5Data X n z (zpowers z) S) {M A A' J : Subgroup X}
    (hM : M ≠ ⊤) (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') (hAA' : A ≠ A')
    (hJ : IsPCompIn 2 M J) (hAJ : A ≤ J) (hA'J : A' ≤ J) : False := by
  have hAM : A ≤ M := hAJ.trans hJ.1
  by_cases hzc : z ∈ centralizerSection J (pPrimeCoreOf 2 J)
  · obtain ⟨hE, -⟩ := oTwoPrimeOf_inf_centralizer_eq h hA hAM hJ hAJ hzc
    obtain ⟨hE', -⟩ := oTwoPrimeOf_inf_centralizer_eq h hA' (hA'J.trans hJ.1) hJ hA'J hzc
    exact hAA' (hE.symm.trans hE')
  · exact false_of_noncentral_comps h hM hA hA' hAA' hJ hAJ hA'J hzc

theorem zStar_of_two_comps
    (h : Sec5Data X n z (zpowers z) S) {M A A' : Subgroup X}
    (hM : M ≠ ⊤) (hA : Sec5Comp X n (centralizer ({z} : Set X)) A)
    (hA' : Sec5Comp X n (centralizer ({z} : Set X)) A') (hAA' : A ≠ A') (hAM : A ≤ M)
    (hA'M : A' ≤ M) : ∀ m ∈ M, ⁅m, z⁆ ∈ oddCoreOf M := by
  obtain ⟨J, hJ, hAJ⟩ := exists_pComp_ge_comp h hA hAM
  obtain ⟨J', hJ', hA'J'⟩ := exists_pComp_ge_comp h hA' hA'M
  have hzc : z ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
    by_cases hJJ : J = J'
    · subst hJJ
      exact (false_of_two_comps_le_pComp h hM hA hA' hAA' hJ hAJ hA'J').elim
    · exact mem_centralizerSection_of_mem_pComp hJ hJ' hJJ (hA'J' (z_mem_comp h hA'))
  obtain ⟨hJi, hJn⟩ := isIntrinsicIn_of_pComp h hA hAM hJ hAJ hzc
  exact comm_mem_oddCore_of_isSylowTwoIn h (isSylowTwoIn_zStar_K0_of_mem h (hJi.mem_zStar_K0 hJn))

end CFSG.OddStandard.Solomon75
