module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTwoC
public import CFSG.ClassicalInvolution.Q3.TL3T26

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

@[expose] def ThmD1TwAt (r : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ Δ : Set (Subgroup G), HypOmegaGen Δ → (∀ J ∈ Δ, IsPGroup 2 J) →
    (∀ J ∈ Δ, Nat.card J = 2 ^ r) → (∀ J ∈ Δ, AEmpty Δ J) →
    classicalInvolutionOddCore G = ⊥ →
    (∀ L ∈ Δ, ∀ u : G, IsUniqueInvolution L u → TightInO2 u) →
    ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : G, conjSub g J = L) → Commutes J L

theorem thmD1GenBelow_of_twAt {r n : ℕ}
    (h : ∀ (H : Type) [Group H] [Finite H], Nat.card H < n → ThmD1TwAt r H) :
    ThmD1GenBelow r n := by
  intro G _ _ Ω hΩ h2 h8 hA P hPΩ hcard hinv hodd hE2 L hL L' hL' hnc a ha b hb
  set X := pSpan P with hX
  have hLX : ∀ M ∈ P, M ≤ X := fun M hM => le_pSpan hM
  have hΩ' : HypOmegaGen (restrictFamily P X) := by
    refine TL4.hypOmegaGen_restrict_of X hLX (fun n hn M hM => hinv M hM n hn)
      (fun K hK => hΩ.omega1 K (hPΩ hK)) (fun K hK => ?_)
      (fun K hK J hJ => hΩ.omega3 K (hPΩ hK) J (hPΩ hJ))
      (fun K hK J hJ hne => hΩ.omega4 K (hPΩ hK) J (hPΩ hJ) hne)
      (fun K hK J hJ hne => hΩ.omega5 K (hPΩ hK) J (hPΩ hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (h2 K (hPΩ hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  have h2' : ∀ J ∈ restrictFamily P X, IsPGroup 2 J := by
    rintro _ ⟨J, hJ, -, rfl⟩
    exact (h2 J (hPΩ hJ)).comap_subtype
  have h8' : ∀ J ∈ restrictFamily P X, Nat.card J = 2 ^ r := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJX).toEquiv]
    exact h8 J (hPΩ hJ)
  have hA' : ∀ J ∈ restrictFamily P X, AEmpty (restrictFamily P X) J := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    exact aEmpty_restrictFamily hΩ h2 hPΩ hJX (hA J (hPΩ hJ))
  have hall : ∀ M ∈ restrictFamily P X, ∀ u : ↥X, IsUniqueInvolution M u → TightInO2 u := by
    rintro _ ⟨M, hM, hMX, rfl⟩ u hu
    obtain ⟨Q, -, hQn, hQ2, huQ⟩ := hE2 M hM (u : G) (isUniqueInvolution_of_subgroupOf hu hMX)
    refine ⟨Q.subgroupOf X, ⟨fun q hq g => ?_⟩, hQ2.comap_subtype,
      Subgroup.mem_subgroupOf.mpr huQ⟩
    exact Subgroup.mem_subgroupOf.mpr (hQn g g.2 q (Subgroup.mem_subgroupOf.mp hq))
  have hnc' : ¬ ∃ g : ↥X, conjSub g (L.subgroupOf X) = L'.subgroupOf X := by
    rintro ⟨g, hg⟩
    apply hnc
    refine ⟨g, g.2, ?_⟩
    rw [conjSub_subgroupOf] at hg
    have hgX : conjSub (g : G) L ≤ X := by
      have := conjSub_mono (n := (g : G)) (hLX L hL)
      rwa [conjSub_eq_self_of_mem g.2] at this
    have h1 := Subgroup.subgroupOf_inj.mp hg
    rwa [inf_eq_left.mpr hgX, inf_eq_left.mpr (hLX L' hL')] at h1
  have hc := h ↥X hcard (restrictFamily P X) hΩ' h2' h8' hA' hodd hall
    (L.subgroupOf X) ⟨L, hL, hLX L hL, rfl⟩ (L'.subgroupOf X) ⟨L', hL', hLX L' hL', rfl⟩ hnc'
    ⟨a, hLX L hL ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨b, hLX L' hL' hb⟩
    (Subgroup.mem_subgroupOf.mpr hb)
  exact congrArg Subtype.val hc

variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin in
theorem twinT4Hyp_of {r : ℕ} {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 2 ^ r) (hA : ∀ J ∈ Δ, AEmpty Δ J)
    (hodd : classicalInvolutionOddCore G = ⊥) : TwinT4Hyp r G Δ where
  hyp := hΩ
  twoGroup := fun J hJ => (h2 J hJ).to_quotient _
  quat := fun J hJ P hP => by
    have hPJ : J = P := hP.2.2 J le_rfl (h2 J hJ) hP.1
    subst hPJ
    obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hJ (h2 J hJ))
    have hc : 2 ^ (k + 2) = 2 ^ r := by
      rw [← h8 J hJ, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      ring
    have hkr : k = r - 2 := by
      have := Nat.pow_right_injective (le_refl 2) hc
      omega
    rw [← hkr]
    exact ⟨e⟩
  aEmpty := hA
  odd := hodd

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin in
theorem not_mem_normalizer_of_not_commutes {r : ℕ} {Δ : Set (Subgroup G)} (h : TwinT4Hyp r G Δ)
    {J L : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ) (hnc : ¬ ∃ g : G, conjSub g J = L)
    (hncomm : ¬ Commutes J L) {u v : G} (hu : IsUniqueInvolution J u)
    (hv : IsUniqueInvolution L v) (hinu : TightInO2 u) (hinv : TightInO2 v) :
    v ∉ Subgroup.normalizer (J : Set G) := by
  intro hvJ
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJ2 := h.isPGroup_of_inO2 hJ hu ⟨_, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hL hv ⟨_, hQn, hQ2, hvQ⟩
  have hJR := TL4.mem_RSet_self hJ hJ2
  have hLR := TL4.mem_RSet_self hL hL2
  have hJL : J ≠ L := fun e => hnc ⟨1, by rw [conjSub_one, e]⟩
  by_cases huv : u = v
  · subst huv
    have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := isUniqueInvolution_le_centralizer hv
    have hLN : L ≤ Subgroup.normalizer (J : Set G) :=
      h.le_normalizer_of_le_centralizer hJ hL hJL hu hLu
    exact hncomm (TL4.commutes_of_le_normalizer h.hyp hJR hLR hJ2 hL2 hJL hLN)
  obtain ⟨X, hXC, hX2, hX4⟩ := h.exists_le_centralizer hJ hL hu hv hQn hQ2 huQ hvQ hvJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXC
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV4
    omega
  have huV : u ∈ V := TL4.mem_of_isPGroup_of_ne_bot hu (hV.1.trans inf_le_left) hV.2.1 hVne
  have hJtw : J ∉ twinSet Δ L := by
    rintro ⟨-, z, hzL, hzJ⟩
    exact huv ((hzJ.eq hu).symm.trans (hzL.eq hv))
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one
  have hRJ : ∀ R ∈ RSet Δ, R ≤ J → R = J := fun R hR hRJ =>
    ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hJ hR hRJ).eq_of_le hJ2 le_rfl hRJ).symm
  rcases Sec6Gen.l6_2Gen G Δ h.hyp L hL v hv J hJ hJtw u hu V hV huV with
    ⟨hVu, -⟩ | ⟨hVu, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVL⟩
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · have hJstar : J ∈ omegaStarNbr Δ L :=
      ⟨hJ, hJL, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hJn : J ∈ omegaNbr Δ L
    · obtain ⟨-, -, R, hR, hRJ', hRN⟩ := hJn
      rw [hRJ R hR hRJ'] at hRN
      exact hncomm
        (TL4.commutes_of_le_normalizer h.hyp hLR hJR hL2 hJ2 hJL.symm hRN).symm
    · obtain ⟨g, -, hg⟩ := h.aEmpty L hL J hJstar hJn v u hv hu
      exact hnc ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  · rw [hRJ V hVR (hV.1.trans inf_le_left), TL4.oddCoreOf_eq_bot_of_isPGroup hL2] at hVL
    refine hncomm fun x hx y hy => ?_
    have hc := hVL (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

theorem not_le_of_not_mem_normalizer {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) {J L : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ) {v : G}
    (hv : IsUniqueInvolution L v) (hvJ : v ∉ Subgroup.normalizer (J : Set G))
    {Q : Subgroup G} (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) {U : Subgroup G} (hU : U ∈ USet Δ)
    (hUJ : U ≤ J) : ¬ U ≤ Q := by
  intro hUQ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right (h2 L hL) hQ2).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hη : η ∈ etaG Δ := ⟨S, hηS, hinv⟩
  set W := etaSpan η with hW
  have hW2 : IsPGroup 2 W := etaSpan_isPGroup hη
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := etaSpan_comm hΩ hη
  have hLS : L ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hL8 := (Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hL (h2 L hL))).eight_le
  have hLW : L ⊓ W ∈ η := Sec6Gen.l6_11Gen G Δ hΩ S η hη (fun V hV => (hηS.1 hV).2) L hL
    (by rw [inf_eq_left.mpr hLS]; omega)
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hLW).1
  have hvW : v ∈ W := (hv.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)).2
  have hP : TC.IsNormalTwoIn Q 1 := ⟨fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr
    (by simp), hQ2, fun c _ p hp => hQn.conj_mem p hp c⟩
  have hact := (TC.normalizes_w_of_le_twoNormal hΩ h2 hη
    (fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)) hJ hU hUJ hP hUQ).1
  have hJN : J ≤ Subgroup.normalizer (W : Set G) := by
    intro j hj
    rw [mem_normalizer_iff_conjSub_eq]
    exact TC.conjSub_etaSpan_eq (hact j hj) (hact j⁻¹ (J.inv_mem hj))
  obtain ⟨S', hS'⟩ := ((h2 J hJ).to_sup_of_normal_right' hW2 hJN).exists_le_sylow
  have hJS' : J ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hJ8 := (Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hJ (h2 J hJ))).eight_le
  have hJW : J ⊓ W ∈ η := Sec6Gen.l6_11Gen G Δ hΩ S' η hη
    (fun V hV => (le_etaSpan hV).trans (le_sup_right.trans hS')) J hJ
    (by rw [inf_eq_left.mpr hJS']; omega)
  obtain ⟨-, -, -, -, -, -, -, -, h4J⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hJW).1
  have hJv : conjSub v J ≠ J := fun h => hvJ (mem_normalizer_iff_conjSub_eq.mpr h)
  have hle : J ⊓ W ≤ J ⊓ conjSub v J := by
    intro y hy
    refine ⟨hy.1, mem_conjSub_iff.mpr ?_⟩
    have hyv : y * v = v * y := hWcomm y hy.2 v hvW
    have : v⁻¹ * y * v = y := by rw [mul_assoc, hyv, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact hy.1
  have h1 := (hΩ.omega4 J hJ (conjSub v J) (hΩ.conjInvariant v J hJ) hJv.symm).1
  have hJJ2 : IsPGroup 2 ↥(J ⊓ conjSub v J) := (h2 J hJ).to_le inf_le_left
  obtain ⟨k, hk⟩ := hJJ2.exists_card_eq
  rw [hk, padicValNat.prime_pow] at h1
  have hc := Subgroup.card_le_of_le hle
  rw [hk] at hc
  have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
  omega

omit [Finite G] in
theorem not_mem_normalizer_conj {J : Subgroup G} {v : G}
    (hvJ : v ∉ Subgroup.normalizer (J : Set G)) (g : G) :
    g * v * g⁻¹ ∉ Subgroup.normalizer ((conjSub g J : Subgroup G) : Set G) := by
  intro h
  apply hvJ
  rw [mem_normalizer_iff_conjSub_eq] at h ⊢
  have h1 : conjSub g⁻¹ (conjSub (g * v * g⁻¹) (conjSub g J)) = conjSub g⁻¹ (conjSub g J) := by
    rw [h]
  rwa [← conjSub_mul, ← conjSub_mul, conjSub_inv_conjSub,
    show g⁻¹ * (g * v * g⁻¹) * g = v by group] at h1

theorem le_normalizer_of_e8Struct {r : ℕ} {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 2 ^ r) {P : Set (Subgroup G)}
    (hPΔ : P ⊆ Δ) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hE2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {E : Subgroup G} (hE : E8Struct (pSpan P) E) {K : Subgroup G} (hK : K ∈ P) :
    E ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan P with hX
  have hKX : K ≤ X := le_pSpan hK
  have hKΔ : K ∈ Δ := hPΔ hK
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hKΔ
  have hzE : z ∈ E := by
    obtain ⟨Q, hQX, hQn, hQ2, hzQ⟩ := hE2 K hK z hz
    exact hE.core Q hQX hQn hQ2 hzQ
  have hXN : X ≤ Subgroup.normalizer (E : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨hE.normal x hx e, fun h => ?_⟩
    have := hE.normal x⁻¹ (X.inv_mem hx) _ h
    simpa [mul_assoc] using this
  have hKNE : K ≤ Subgroup.normalizer (E : Set G) := hKX.trans hXN
  have hKEc : Nat.card ↥(K ⊓ E) = 2 := by
    have hset : ((K ⊓ E : Subgroup G) : Set G) = {1, z} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxK, hxE⟩
        exact hz.unique x hxK (hE.sq x hxE)
      · rintro (rfl | rfl)
        · exact ⟨K.one_mem, E.one_mem⟩
        · exact ⟨hz.mem, hzE⟩
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hz.ne_one.symm]
  have hKE := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := E) hKNE
  rw [hKEc, hE.card] at hKE
  intro e he
  by_contra hne
  have hJK : conjSub e K ≠ K := fun h => hne (mem_normalizer_iff_conjSub_eq.mpr h)
  have hJ : conjSub e K ∈ Δ := hPΔ (hinv K hK e (hE.le he))
  have hE2' : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hE.card]; norm_num)
  have hKE2 : IsPGroup 2 ↥(K ⊔ E) := (h2 K hKΔ).to_sup_of_normal_right' hE2' hKNE
  have hJKE : conjSub e K ≤ K ⊔ E := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have : x = e * (e⁻¹ * x * e) * e⁻¹ := by group
    rw [this]
    exact (K ⊔ E).mul_mem ((K ⊔ E).mul_mem (Subgroup.mem_sup_right he)
      (Subgroup.mem_sup_left hx)) ((K ⊔ E).inv_mem (Subgroup.mem_sup_right he))
  obtain ⟨S, hS⟩ := hKE2.exists_le_sylow
  have hcomm : ∀ x ∈ K, ∀ y ∈ conjSub e K, x * y = y * x :=
    Q3CP.l67Gen G Δ hΩ S K (TC.mem_RSet_of_isPGroup hKΔ (h2 K hKΔ)) (conjSub e K)
      (TC.mem_RSet_of_isPGroup hJ (h2 _ hJ)) (le_sup_left.trans hS) (hJKE.trans hS) hJK.symm
  have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (TC.mem_RSet_of_isPGroup hKΔ (h2 K hKΔ))
  have hinf : Nat.card ↥(K ⊓ conjSub e K) ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    refine hz.unique x hx.1 (hq.sq_eq_one_of_central hx.1 fun w hw => ?_)
    exact (hcomm w hw x hx.2).symm
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := conjSub e K)
    (le_normalizer_of_comm hcomm)
  have hcardJ : Nat.card ↥(conjSub e K) = Nat.card K := by rw [h8 _ hJ, h8 K hKΔ]
  have hle : Nat.card ↥(K ⊔ conjSub e K) ≤ Nat.card ↥(K ⊔ E) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hJKE)
  have h8' := hq.eight_le
  have hinf1 : 1 ≤ Nat.card ↥(K ⊓ conjSub e K) := Nat.card_pos
  rw [hcardJ] at hprod
  have hge : Nat.card ↥(K ⊔ E) ≤ Nat.card ↥(K ⊔ conjSub e K) := by nlinarith
  have heq : K ⊔ conjSub e K = K ⊔ E :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hJKE) hge
  have heN : e ∈ K ⊔ conjSub e K := heq ▸ Subgroup.mem_sup_right he
  exact hne ((sup_le (Subgroup.le_normalizer) (le_normalizer_of_comm fun x hx y hy =>
    (hcomm y hy x hx).symm)) heN)

end CFSG.ClassicalInvolution.Q3.TC.Thin
