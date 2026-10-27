module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpA3
import CFSG.ClassicalInvolution.Q3.TL3T26
public import CFSG.ClassicalInvolution.Q3.Sec13PerpD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def vW (Ω : Set (Subgroup G)) (W : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ R ∈ DSet Ω W, ∃ R' ∈ DSet Ω W, R' ∈ KPerp Ω R ∧
    ∃ u u' : G, IsUniqueInvolution R u ∧ IsUniqueInvolution R' u' ∧ x = u * u'}

private theorem perpA_self_mem (K : Subgroup G) : K ∈ KPerp Ω K := Set.mem_insert _ _

private theorem perpA_isSylow_self (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    IsSylow2In K K :=
  ⟨le_rfl, h.thmD.two K hK, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩

private theorem perpA_involution_mem (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {K : Subgroup G} (hK : K ∈ DSet Ω W) {z : G} (hz : IsUniqueInvolution K z) : z ∈ W := by
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hK).1
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.thmD.hyp hW hK hKΩ
    (perpA_isSylow_self h hKΩ)
  exact (hz.mem_of_le inf_le_left ((h.thmD.two K hKΩ).to_le inf_le_left) (by omega)).2

private theorem perpA_card_inf (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {T : Subgroup G} (hT : T ∈ DSet Ω W) : Nat.card ↥(T ⊓ W) = 4 := by
  have hTΩ : T ∈ Ω := (h.mem_dSet_iff.mp hT).1
  obtain ⟨-, -, -, -, hTW⟩ := Q3CL.Thompson.inf_W_of_mem_D h.thmD.hyp hW hT hTΩ
    (perpA_isSylow_self h hTΩ)
  have hT8 : Nat.card T = 8 := h.card_eq_eight hTΩ
  omega

private theorem perpA_kperp_symm (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) :
    K ∈ KPerp Ω J ↔ J ∈ KPerp Ω K := by
  by_cases hKJ : K = J
  · subst hKJ
    exact Iff.rfl
  have hsym : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → B ∈ omegaNbr Ω A → A ∈ omegaNbr Ω B :=
    fun hA hB hBA => Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.thmD.hyp hA hB hBA
  rw [KPerp, KPerp, Set.mem_insert_iff, Set.mem_insert_iff]
  constructor
  · rintro (e | hm)
    · exact absurd e hKJ
    · exact Or.inr (hsym hJ hK hm)
  · rintro (e | hm)
    · exact absurd e.symm hKJ
    · exact Or.inr (hsym hK hJ hm)

private theorem perpA_inv_comm (h : EndHyp Ω) {R J : Subgroup G} (hR : R ∈ Ω) {u : G}
    (hu : IsUniqueInvolution R u) (hJ : J ∈ KPerp Ω R) : ∀ y ∈ J, u * y = y * u := by
  rw [KPerp, Set.mem_insert_iff] at hJ
  rcases hJ with rfl | hJ
  · intro y hy
    have hc : y * u * y⁻¹ = u := hu.conj_eq (conjSub_eq_self_of_mem hy)
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · exact fun y hy => comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two hR hJ u hu.mem y hy

private theorem perpA_comm_of_mem_kperp (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' T : Subgroup G} (hR : R ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRR' : R' ∈ KPerp Ω R) (hTR : T ∈ KPerp Ω R) {u u' : G}
    (hu : IsUniqueInvolution R u) (hu' : IsUniqueInvolution R' u') :
    ∀ t ∈ T, u * u' * t = t * (u * u') := by
  have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hR).1
  have hR'Ω : R' ∈ Ω := (h.mem_dSet_iff.mp hR').1
  have hTΩ : T ∈ Ω := (h.mem_dSet_iff.mp hT).1
  have h1 : R' ∈ KPerp Ω T :=
    dSet_comm_trans h hW hT hR hR' ((perpA_kperp_symm h hRΩ hTΩ).mpr hTR) hRR'
  have hTR' : T ∈ KPerp Ω R' := (perpA_kperp_symm h hTΩ hR'Ω).mpr h1
  have hcu := perpA_inv_comm h hRΩ hu hTR
  have hcu' := perpA_inv_comm h hR'Ω hu' hTR'
  intro t ht
  rw [mul_assoc, hcu' t ht, ← mul_assoc, hcu t ht, mul_assoc]

private theorem perpA_comm_of_notW (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' T : Subgroup G} (hR : R ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ∉ KPerp Ω R) (hTR' : T ∉ KPerp Ω R') {u u' : G}
    (hu : IsUniqueInvolution R u) (hu' : IsUniqueInvolution R' u') {t : G} (ht : t ∈ T)
    (htW : t ∉ W) : u * u' * t = t * (u * u') := by
  have hΩ := h.thmD.hyp
  have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hR).1
  have hR'Ω : R' ∈ Ω := (h.mem_dSet_iff.mp hR').1
  have hTΩ : T ∈ Ω := (h.mem_dSet_iff.mp hT).1
  have hRT : R ≠ T := by
    rintro rfl
    exact hTR (perpA_self_mem _)
  have hR'T : R' ≠ T := by
    rintro rfl
    exact hTR' (perpA_self_mem _)
  have hTn : T ∉ omegaNbr Ω R := fun hc => hTR (Set.mem_insert_of_mem _ hc)
  have hTn' : T ∉ omegaNbr Ω R' := fun hc => hTR' (Set.mem_insert_of_mem _ hc)
  have hTst : T ∈ omegaStarNbr Ω R :=
    (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW hRΩ hTΩ hRT hR hT
      (perpA_isSylow_self h hRΩ) (perpA_isSylow_self h hTΩ)).1
  have hTst' : T ∈ omegaStarNbr Ω R' :=
    (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW hR'Ω hTΩ hR'T hR' hT
      (perpA_isSylow_self h hR'Ω) (perpA_isSylow_self h hTΩ)).1
  have hHN : T ⊓ W ≤ Subgroup.normalizer (R : Set G) :=
    (Q3CL.Thompson.inf_W_le_normalizer_of_ne hΩ hW hRΩ hTΩ hRT hR hT
      (perpA_isSylow_self h hRΩ) (perpA_isSylow_self h hTΩ)).2
  have hHN' : T ⊓ W ≤ Subgroup.normalizer (R' : Set G) :=
    (Q3CL.Thompson.inf_W_le_normalizer_of_ne hΩ hW hR'Ω hTΩ hR'T hR' hT
      (perpA_isSylow_self h hR'Ω) (perpA_isSylow_self h hTΩ)).2
  have hHc : Nat.card ↥(T ⊓ W) = 4 := perpA_card_inf h hW hT
  obtain ⟨-, -, -, hTN, -, -⟩ := pair_structure h hRΩ hTst hTn
  obtain ⟨-, -, -, hTN', -, -⟩ := pair_structure h hR'Ω hTst' hTn'
  have hEq : T ⊓ W = T ⊓ Subgroup.normalizer (R : Set G) :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hHN) (by omega)
  have hEq' : T ⊓ W = T ⊓ Subgroup.normalizer (R' : Set G) :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hHN') (by omega)
  have htN : t ∉ Subgroup.normalizer (R : Set G) := fun htn => htW (by
    have hm : t ∈ T ⊓ Subgroup.normalizer (R : Set G) := Subgroup.mem_inf.mpr ⟨ht, htn⟩
    rw [← hEq] at hm
    exact (Subgroup.mem_inf.mp hm).2)
  have htN' : t ∉ Subgroup.normalizer (R' : Set G) := fun htn => htW (by
    have hm : t ∈ T ⊓ Subgroup.normalizer (R' : Set G) := Subgroup.mem_inf.mpr ⟨ht, htn⟩
    rw [← hEq'] at hm
    exact (Subgroup.mem_inf.mp hm).2)
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ hTΩ
  have hc1 := conj_involution_eq_mul h hRΩ hTst hTn hu hv ht htN
  have hc2 := conj_involution_eq_mul h hR'Ω hTst' hTn' hu' hv ht htN'
  have hu'W : u' ∈ W := perpA_involution_mem h hW hR' hu'
  have huW : u ∈ W := perpA_involution_mem h hW hR hu
  have hvW : v ∈ W := perpA_involution_mem h hW hT hv
  have hvu : v * u' = u' * v := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW v hvW u' hu'W
  have hv2 : v * v = 1 := hv.sq
  have hc1' : t * u = u * v * t := mul_inv_eq_iff_eq_mul.mp hc1
  have hc2' : t * u' = u' * v * t := mul_inv_eq_iff_eq_mul.mp hc2
  have key : t * (u * u') = u * u' * t := by
    calc t * (u * u') = (t * u) * u' := (mul_assoc _ _ _).symm
      _ = (u * v * t) * u' := by rw [hc1']
      _ = u * v * (t * u') := by simp only [mul_assoc]
      _ = u * v * (u' * v * t) := by rw [hc2']
      _ = u * (v * u') * (v * t) := by simp only [mul_assoc]
      _ = u * (u' * v) * (v * t) := by rw [hvu]
      _ = u * u' * (v * v) * t := by simp only [mul_assoc]
      _ = u * u' * t := by rw [hv2, mul_one]
  exact key.symm

private theorem perpA_comm_of_not_mem_kperp (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' T : Subgroup G} (hR : R ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hTR : T ∉ KPerp Ω R) (hTR' : T ∉ KPerp Ω R') {u u' : G}
    (hu : IsUniqueInvolution R u) (hu' : IsUniqueInvolution R' u') :
    ∀ t ∈ T, u * u' * t = t * (u * u') := by
  have hΩ := h.thmD.hyp
  have hTΩ : T ∈ Ω := (h.mem_dSet_iff.mp hT).1
  have huW : u ∈ W := perpA_involution_mem h hW hR hu
  have hu'W : u' ∈ W := perpA_involution_mem h hW hR' hu'
  have hHc : Nat.card ↥(T ⊓ W) = 4 := perpA_card_inf h hW hT
  have hT8 : Nat.card T = 8 := h.card_eq_eight hTΩ
  set C : Subgroup G := Subgroup.centralizer ({u * u'} : Set G) with hC
  have hHC : T ⊓ W ≤ T ⊓ C := by
    intro s hs
    have hsW : s ∈ W := (Subgroup.mem_inf.mp hs).2
    have h1 := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW s hsW u huW
    have h2 := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW s hsW u' hu'W
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hs).1, ?_⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    calc s * (u * u') = (s * u) * u' := (mul_assoc _ _ _).symm
      _ = (u * s) * u' := by rw [h1]
      _ = u * (s * u') := mul_assoc _ _ _
      _ = u * (u' * s) := by rw [h2]
      _ = (u * u') * s := (mul_assoc _ _ _).symm
  obtain ⟨t0, ht0T, ht0⟩ : ∃ t0 ∈ T, t0 ∉ T ⊓ W := by
    by_contra hcon
    push_neg at hcon
    have hle : T ≤ T ⊓ W := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  have ht0W : t0 ∉ W := fun hw => ht0 (Subgroup.mem_inf.mpr ⟨ht0T, hw⟩)
  have hx0 := perpA_comm_of_notW h hW hR hR' hT hTR hTR' hu hu' ht0T ht0W
  have ht0C : t0 ∈ T ⊓ C :=
    Subgroup.mem_inf.mpr ⟨ht0T, by rw [hC, Subgroup.mem_centralizer_singleton_iff]; exact hx0.symm⟩
  have hcardK : 4 < Nat.card ↥(T ⊓ C) := by
    by_contra hle
    push_neg at hle
    have heq : T ⊓ W = T ⊓ C := Subgroup.eq_of_le_of_card_ge hHC (by omega)
    exact ht0 (heq ▸ ht0C)
  have hdvd : Nat.card ↥(T ⊓ C) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
  have hcard8 : Nat.card ↥(T ⊓ C) = 8 := by
    rw [hT8] at hdvd
    have hlt : Nat.card ↥(T ⊓ C) < 9 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)
    have key : ∀ n, n < 9 → n ∣ 8 → 4 < n → n = 8 := by decide
    exact key _ hlt hdvd hcardK
  have hTC : T ⊓ C = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  intro t ht
  have htC : t ∈ T ⊓ C := by rw [hTC]; exact ht
  have htC' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp htC).2
  exact htC'.symm

private theorem perpA_mem_kperp_iff (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) :
    J ∈ KPerp Ω K ↔ J = K ∨ Commutes K J := by
  constructor
  · intro hJK
    rw [KPerp, Set.mem_insert_iff] at hJK
    rcases hJK with e | hm
    · exact Or.inl e
    · exact Or.inr (comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two hK hm)
  · rintro (e | hc)
    · rw [e]
      exact perpA_self_mem K
    · by_cases hJK : J = K
      · rw [hJK]
        exact perpA_self_mem K
      · apply Set.mem_insert_of_mem
        exact (TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two).mpr
          ⟨hJ, hJK, AscL62.le_normalizer_of_commutes hc.symm⟩

private theorem perpA_commutes_conjSub {K L : Subgroup G} (n : G) (hKL : Commutes K L) :
    Commutes (conjSub n K) (conjSub n L) := by
  intro x hx y hy
  rw [mem_conjSub_iff] at hx hy
  have hk := hKL (n⁻¹ * x * n) hx (n⁻¹ * y * n) hy
  calc x * y = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [hk]
    _ = y * x := by group

private theorem perpA_conj_kperp (h : EndHyp Ω) {K J : Subgroup G} (n : G) (hK : K ∈ Ω)
    (hJ : J ∈ Ω) : J ∈ KPerp Ω K ↔ conjSub n J ∈ KPerp Ω (conjSub n K) := by
  rw [perpA_mem_kperp_iff h hK hJ,
    perpA_mem_kperp_iff h (h.thmD.hyp.conjInvariant n K hK) (h.thmD.hyp.conjInvariant n J hJ)]
  constructor
  · rintro (e | hc)
    · exact Or.inl (by rw [e])
    · exact Or.inr (perpA_commutes_conjSub n hc)
  · rintro (e | hc)
    · left
      have := congrArg (conjSub n⁻¹) e
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    · right
      have := perpA_commutes_conjSub n⁻¹ hc
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

private theorem perpA_kperp_subset_dSet (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {L : Subgroup G} (hL : L ∈ DSet Ω W) :
    KPerp Ω L ⊆ DSet Ω W := by
  have hLΩ : L ∈ Ω := (h.mem_dSet_iff.mp hL).1
  have hKΩ : ∀ K ∈ KPerp Ω L, K ∈ Ω := by
    intro K hK
    rw [KPerp, Set.mem_insert_iff] at hK
    rcases hK with e | hm
    · rw [e]
      exact hLΩ
    · exact hm.1
  have hpair : ∀ J ∈ KPerp Ω L, ∀ J' ∈ KPerp Ω L, J' ∈ KPerp Ω J := by
    intro J hJ J' hJ'
    by_cases hJL : J = L
    · rw [hJL]
      exact hJ'
    · have hJω : J ∈ omegaNbr Ω L := by
        rw [KPerp, Set.mem_insert_iff] at hJ
        exact hJ.resolve_left hJL
      rw [hA L hLΩ J hJω]
      exact hJ'
  have hcomm : ∀ R ∈ KPerp Ω L, ∀ T ∈ KPerp Ω L, R ≠ T →
      ∀ x ∈ R, ∀ y ∈ T, x * y = y * x := by
    intro R hR T hT hRT x hx y hy
    rcases (perpA_mem_kperp_iff h (hKΩ R hR) (hKΩ T hT)).mp (hpair R hR T hT) with e | c
    · exact absurd e.symm hRT
    · exact c x hx y hy
  have hle := clique_ncard_le h hKΩ hcomm hW hL
  have h2 : KPerp Ω L ∩ DSet Ω W = KPerp Ω L :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_left hle (Set.toFinite _)
  intro K hK
  have hKI : K ∈ KPerp Ω L ∩ DSet Ω W := by
    rw [h2]
    exact hK
  exact hKI.2

private theorem perpA_exists_not_mem (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {A : Subgroup G} (hA : A ∈ DSet Ω W) : ∃ r ∈ A, r ∉ W := by
  by_contra hcon
  push_neg at hcon
  have hle : A ≤ W := fun r hr => hcon r hr
  have hAΩ : A ∈ Ω := (h.mem_dSet_iff.mp hA).1
  have hA8 : Nat.card A = 8 := h.card_eq_eight hAΩ
  have h2 := perpA_card_inf h hW hA
  rw [inf_eq_left.mpr hle] at h2
  omega

private theorem perpA_inv_mul_mem_W (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {A : Subgroup G} (hA : A ∈ DSet Ω W) {r : G} (hr : r ∈ A) (hrW : r ∉ W)
    {x : G} (hx : x ∈ A) (hxW : x ∉ W) : r⁻¹ * x ∈ W := by
  have hAΩ : A ∈ Ω := (h.mem_dSet_iff.mp hA).1
  have hA8 : Nat.card A = 8 := h.card_eq_eight hAΩ
  have hH4 : Nat.card ↥(A ⊓ W) = 4 := perpA_card_inf h hW hA
  have hHA : ((A ⊓ W : Subgroup G) : Set G) ⊆ (A : Set G) := fun y hy => (Subgroup.mem_inf.mp hy).1
  have hHc : ((A ⊓ W : Subgroup G) : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hH4
  have hAc : ((A : Subgroup G) : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hA8
  have hrH : (fun w => r * w) '' ((A ⊓ W : Subgroup G) : Set G) ⊆
      ((A : Subgroup G) : Set G) \ ((A ⊓ W : Subgroup G) : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨A.mul_mem hr (hHA hw), fun hm => ?_⟩
    apply hrW
    have hwW : w ∈ W := (Subgroup.mem_inf.mp hw).2
    have hmW : r * w ∈ W := (Subgroup.mem_inf.mp hm).2
    simpa using W.mul_mem hmW (W.inv_mem hwW)
  have hcard1 : ((fun w => r * w) '' ((A ⊓ W : Subgroup G) : Set G)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective r), hHc]
  have hcard2 : (((A : Subgroup G) : Set G) \ ((A ⊓ W : Subgroup G) : Set G)).ncard = 4 := by
    rw [Set.ncard_diff hHA (Set.toFinite _), hAc, hHc]
  have heq : (fun w => r * w) '' ((A ⊓ W : Subgroup G) : Set G) =
      ((A : Subgroup G) : Set G) \ ((A ⊓ W : Subgroup G) : Set G) :=
    Set.eq_of_subset_of_ncard_le hrH (by omega) (Set.toFinite _)
  have hxmem : x ∈ ((A : Subgroup G) : Set G) \ ((A ⊓ W : Subgroup G) : Set G) :=
    ⟨hx, fun hxH => hxW (Subgroup.mem_inf.mp hxH).2⟩
  rw [← heq] at hxmem
  obtain ⟨w, hw, hrw⟩ := hxmem
  have hri : r⁻¹ * x = w := by
    rw [← hrw]
    group
  rw [hri]
  exact (Subgroup.mem_inf.mp hw).2

private theorem perpA_cube_conj {Q : Type*} [Group Q] (a b : Q) :
    (b * a) ^ 3 = b * (a * b) ^ 3 * b⁻¹ := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel, mul_one]

private theorem perpA_conj_ab {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hc : (a * b) ^ 3 = 1) : a * b * a * (a * b)⁻¹ = b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h5 : a * b * a * b * a = b := by
    calc a * b * a * b * a = a * b * a * b * a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) ^ 3 * b := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = b := by rw [hc, one_mul]
  rw [mul_inv_rev, ha', hb']
  simpa only [mul_assoc] using h5

private theorem perpA_conjSub_le (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {A B : Subgroup G} (hA : A ∈ DSet Ω W) (hB : B ∈ DSet Ω W)
    {r₀ l₀ : G} (hr₀ : r₀ ∈ A) (hr₀W : r₀ ∉ W) (hl₀ : l₀ ∈ B) (hl₀W : l₀ ∉ W)
    (hcube : (Asc77.Thompson.piG W r₀ * Asc77.Thompson.piG W l₀) ^ 3 = 1)
    (hr2 : Asc77.Thompson.piG W r₀ * Asc77.Thompson.piG W r₀ = 1)
    (hl2 : Asc77.Thompson.piG W l₀ * Asc77.Thompson.piG W l₀ = 1) :
    conjSub (r₀ * l₀) A ≤ B ⊔ W ⊔ OCW W := by
  have hAN : A ≤ Subgroup.normalizer (W : Set G) := hA.2
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hB.2
  have hr₀N : r₀ ∈ Subgroup.normalizer (W : Set G) := hAN hr₀
  have hl₀N : l₀ ∈ Subgroup.normalizer (W : Set G) := hBN hl₀
  have hnN : r₀ * l₀ ∈ Subgroup.normalizer (W : Set G) := Subgroup.mul_mem _ hr₀N hl₀N
  have himg : ∀ x ∈ A, Asc77.Thompson.piG W x = 1 ∨
      Asc77.Thompson.piG W x = Asc77.Thompson.piG W r₀ := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl (Asc77.Thompson.piG_of_mem_sup (Subgroup.mem_sup_left hxW))
    · right
      have hm := perpA_inv_mul_mem_W h hW hA hr₀ hr₀W hx hxW
      have hmN : r₀⁻¹ * x ∈ Subgroup.normalizer (W : Set G) :=
        hAN (A.mul_mem (A.inv_mem hr₀) hx)
      calc Asc77.Thompson.piG W x = Asc77.Thompson.piG W (r₀ * (r₀⁻¹ * x)) := by
            rw [mul_inv_cancel_left]
        _ = Asc77.Thompson.piG W r₀ * Asc77.Thompson.piG W (r₀⁻¹ * x) :=
            Asc77.Thompson.piG_mul hr₀N hmN
        _ = Asc77.Thompson.piG W r₀ := by
            rw [Asc77.Thompson.piG_of_mem_sup (Subgroup.mem_sup_left hm), mul_one]
  have hconj : ∀ x ∈ A, Asc77.Thompson.piG W (r₀ * l₀ * x * (r₀ * l₀)⁻¹) = 1 ∨
      Asc77.Thompson.piG W (r₀ * l₀ * x * (r₀ * l₀)⁻¹) = Asc77.Thompson.piG W l₀ := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (W : Set G) := hAN hx
    rw [Asc77.Thompson.piG_mul (Subgroup.mul_mem _ hnN hxN) (Subgroup.inv_mem _ hnN),
      Asc77.Thompson.piG_mul hnN hxN, Asc77.Thompson.piG_inv hnN,
      Asc77.Thompson.piG_mul hr₀N hl₀N]
    rcases himg x hx with hx1 | hxa
    · left
      rw [hx1, mul_one, mul_inv_cancel]
    · right
      rw [hxa]
      exact perpA_conj_ab hr2 hl2 hcube
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hyv : r₀ * l₀ * (((r₀ * l₀)⁻¹ * y * (r₀ * l₀))) * (r₀ * l₀)⁻¹ = y := by group
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [← hyv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hAN hy)) (Subgroup.inv_mem _ hnN)
  have hc := hconj _ hy
  rw [hyv] at hc
  have hBX : B ≤ B ⊔ W ⊔ OCW W := le_sup_left.trans le_sup_left
  have hXX : W ⊔ OCW W ≤ B ⊔ W ⊔ OCW W := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  rcases hc with hc | hc
  · exact hXX ((Asc77.Thompson.piG_eq_one_iff hyN).mp hc)
  · have hyl : l₀⁻¹ * y ∈ W ⊔ OCW W := by
      have h1 := (Asc77.Thompson.piG_eq_iff hyN hl₀N).mp hc
      have h2 := (W ⊔ OCW W).inv_mem h1
      simpa using h2
    have hyeq : y = l₀ * (l₀⁻¹ * y) := by group
    rw [hyeq]
    exact Subgroup.mul_mem _ (hBX hl₀) (hXX hyl)

private theorem perpA_exists_conj (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ DSet Ω W) (hR₂ : R₂ ∈ DSet Ω W)
    (hnc : R₂ ∉ KPerp Ω R₁) : ∃ r ∈ R₁, ∃ l ∈ R₂, conjSub (r * l) R₁ = R₂ := by
  have hΩ := h.thmD.hyp
  have hR₁Ω : R₁ ∈ Ω := (h.mem_dSet_iff.mp hR₁).1
  have hR₂Ω : R₂ ∈ Ω := (h.mem_dSet_iff.mp hR₂).1
  have hne : R₁ ≠ R₂ := by
    rintro rfl
    exact hnc (perpA_self_mem R₁)
  have hnot : R₂ ∉ omegaNbr Ω R₁ := fun hm => hnc (Set.mem_insert_of_mem _ hm)
  obtain ⟨r, hr, hrW⟩ := perpA_exists_not_mem h hW hR₁
  obtain ⟨l, hl, hlW⟩ := perpA_exists_not_mem h hW hR₂
  have hP : Q3CL.PartIHypG Ω := ⟨hΩ, h.cls, h.thmD.aEmpty⟩
  have c := Q3CL.T8.ctxOf hP hW
  have hcube : (Asc77.Thompson.piG W r * Asc77.Thompson.piG W l) ^ 3 = 1 :=
    Q3CL.Thompson.piG_cube_of_key Sec6Gen.l6_2Gen c.hΩ c.hW c.hkey (c.hA R₁ hR₁Ω) hR₁Ω hR₂Ω
      hne hR₁ hR₂ (perpA_isSylow_self h hR₁Ω) (perpA_isSylow_self h hR₂Ω) hnot hr hl hrW hlW
  have hr2 : Asc77.Thompson.piG W r * Asc77.Thompson.piG W r = 1 :=
    Q3CL.Thompson.piG_mul_self_of_mem_D hΩ hW hR₁ hr
  have hl2 : Asc77.Thompson.piG W l * Asc77.Thompson.piG W l = 1 :=
    Q3CL.Thompson.piG_mul_self_of_mem_D hΩ hW hR₂ hl
  have h12 := perpA_conjSub_le h hW hR₁ hR₂ hr hrW hl hlW hcube hr2 hl2
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR₁.2 hr
  have hlN : l ∈ Subgroup.normalizer (W : Set G) := hR₂.2 hl
  have hli : Asc77.Thompson.piG W l⁻¹ = Asc77.Thompson.piG W l := by
    rw [Asc77.Thompson.piG_inv hlN, inv_eq_of_mul_eq_one_right hl2]
  have hri : Asc77.Thompson.piG W r⁻¹ = Asc77.Thompson.piG W r := by
    rw [Asc77.Thompson.piG_inv hrN, inv_eq_of_mul_eq_one_right hr2]
  have hcube' : (Asc77.Thompson.piG W l * Asc77.Thompson.piG W r) ^ 3 = 1 := by
    rw [perpA_cube_conj, hcube, mul_one, mul_inv_cancel]
  have hlinv : l⁻¹ ∉ W := fun hw => hlW (by simpa using W.inv_mem hw)
  have hrinv : r⁻¹ ∉ W := fun hw => hrW (by simpa using W.inv_mem hw)
  have h21 := perpA_conjSub_le h hW hR₂ hR₁ (R₂.inv_mem hl) hlinv (R₁.inv_mem hr) hrinv
    (by rw [hli, hri]; exact hcube') (by rw [hli]; exact hl2) (by rw [hri]; exact hr2)
  have hnN : r * l ∈ Subgroup.normalizer (W : Set G) := Subgroup.mul_mem _ hrN hlN
  have hinvn : l⁻¹ * r⁻¹ = (r * l)⁻¹ := by rw [mul_inv_rev]
  rw [hinvn] at h21
  have hWn : conjSub (r * l) W = W := mem_normalizer_iff_conjSub_eq.mp hnN
  have hOn : conjSub (r * l) (OCW W) = OCW W :=
    mem_normalizer_iff_conjSub_eq.mp (Asc77.Thompson.normalizer_le_normalizer_OCW W hnN)
  have hsupn : conjSub (r * l) (R₁ ⊔ W ⊔ OCW W) ≤ conjSub (r * l) R₁ ⊔ W ⊔ OCW W := by
    rw [conjSub_sup, conjSub_sup, hWn, hOn]
  have hjoin : conjSub (r * l) R₁ ⊔ W ⊔ OCW W = R₂ ⊔ W ⊔ OCW W := by
    apply le_antisymm
    · exact sup_le (sup_le h12 (le_sup_right.trans le_sup_left)) le_sup_right
    · refine sup_le (sup_le ?_ (le_sup_right.trans le_sup_left)) le_sup_right
      intro y hy
      have hw : (r * l)⁻¹ * y * (r * l) ∈ R₁ ⊔ W ⊔ OCW W :=
        h21 (by
          have := conj_mem_conjSub (n := (r * l)⁻¹) hy
          rwa [inv_inv] at this)
      have hmem := hsupn (conj_mem_conjSub hw)
      have hyeq : r * l * ((r * l)⁻¹ * y * (r * l)) * (r * l)⁻¹ = y := by group
      rw [hyeq] at hmem
      exact hmem
  have hRn : conjSub (r * l) R₁ ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hR₁ hnN
  exact ⟨r, hr, l, hl, dSet_bar_injective h hW hRn hR₂ hjoin⟩

theorem dSet_le_centralizer_vW (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {T : Subgroup G} (hT : T ∈ DSet Ω W) :
    T ≤ Subgroup.centralizer (vW Ω W : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  have hle : vW Ω W ≤ Subgroup.centralizer ({t} : Set G) := by
    unfold vW
    rw [Subgroup.closure_le]
    rintro x ⟨R, hR, R', hR', hRR', u, u', hu, hu', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    by_cases hTR : T ∈ KPerp Ω R
    · exact perpA_comm_of_mem_kperp h hW hR hR' hT hRR' hTR hu hu' t ht
    · by_cases hTR' : T ∈ KPerp Ω R'
      · exact absurd (dSet_comm_trans h hW hR hR' hT hRR' hTR') hTR
      · exact perpA_comm_of_not_mem_kperp h hW hR hR' hT hTR hTR' hu hu' t ht
  intro v hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

@[expose] def perpAV (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ J ∈ KPerp Ω K, ∃ u u' : G, IsUniqueInvolution K u ∧
    IsUniqueInvolution J u' ∧ x = u * u'}

private theorem perpAV_gen {Ω : Set (Subgroup G)} {K J : Subgroup G} (hJ : J ∈ KPerp Ω K)
    {u u' : G} (hu : IsUniqueInvolution K u) (hu' : IsUniqueInvolution J u') :
    u * u' ∈ perpAV Ω K :=
  Subgroup.subset_closure ⟨J, hJ, u, u', hu, hu', rfl⟩

private theorem perpA_exists_wSet_pair (h : EndHyp Ω) {L J : Subgroup G} (hL : L ∈ Ω)
    (hJ : J ∈ Ω) (hLJ : J ∈ KPerp Ω L) : ∃ W ∈ WSet Ω, L ∈ DSet Ω W ∧ J ∈ DSet Ω W := by
  have hC : ({L, J} : Set (Subgroup G)) ⊆ Ω := by
    intro K hK
    rcases hK with rfl | rfl
    · exact hL
    · exact hJ
  have hcomm : ∀ R ∈ ({L, J} : Set (Subgroup G)), ∀ T ∈ ({L, J} : Set (Subgroup G)), R ≠ T →
      ∀ x ∈ R, ∀ y ∈ T, x * y = y * x := by
    intro R hR T hT hRT x hx y hy
    rcases hR with rfl | rfl <;> rcases hT with rfl | rfl
    · exact absurd rfl hRT
    · rcases (perpA_mem_kperp_iff h hL hJ).mp hLJ with e | c
      · exact absurd e.symm hRT
      · exact c x hx y hy
    · rcases (perpA_mem_kperp_iff h hL hJ).mp hLJ with e | c
      · exact absurd e hRT
      · exact c.symm x hx y hy
    · exact absurd rfl hRT
  obtain ⟨W, hW, hsub⟩ := exists_wSet_of_clique h hC hcomm
  exact ⟨W, hW, hsub (Set.mem_insert _ _), hsub (Set.mem_insert_of_mem _ rfl)⟩

private theorem perpAV_le_of_kperp (h : EndHyp Ω) {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ Ω)
    (hR₂ : R₂ ∈ Ω) (hK : KPerp Ω R₂ = KPerp Ω R₁) (hc : R₂ ∈ KPerp Ω R₁) :
    perpAV Ω R₁ ≤ perpAV Ω R₂ := by
  have hc' : R₁ ∈ KPerp Ω R₂ := (perpA_kperp_symm h hR₁ hR₂).mpr hc
  obtain ⟨u₂, hu₂⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hR₂
  unfold perpAV
  rw [Subgroup.closure_le]
  rintro x ⟨J, hJ, u₁, u', hu₁, hu', rfl⟩
  have hJ' : J ∈ KPerp Ω R₂ := by
    rw [hK]
    exact hJ
  have e1 : u₁ * u₂ ∈ perpAV Ω R₂ := by
    have h21 : u₂ * u₁ ∈ perpAV Ω R₂ := perpAV_gen hc' hu₂ hu₁
    have hi := (perpAV Ω R₂).inv_mem h21
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hu₁.sq,
      inv_eq_of_mul_eq_one_right hu₂.sq] at hi
  have e2 : u₂ * u' ∈ perpAV Ω R₂ := perpAV_gen hJ' hu₂ hu'
  have hfac : u₁ * u' = (u₁ * u₂) * (u₂ * u') := by
    calc u₁ * u' = u₁ * (u₂ * u₂) * u' := by rw [hu₂.sq, mul_one]
      _ = (u₁ * u₂) * (u₂ * u') := by simp only [mul_assoc]
  rw [hfac]
  exact (perpAV Ω R₂).mul_mem e1 e2

private theorem perpAV_eq_of_mem_kperp (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L) {R₁ R₂ : Subgroup G}
    (hR₁ : R₁ ∈ Ω) (hR₂ : R₂ ∈ Ω) (hc : R₂ ∈ KPerp Ω R₁) :
    perpAV Ω R₁ = perpAV Ω R₂ := by
  have hK : KPerp Ω R₂ = KPerp Ω R₁ := by
    by_cases e : R₂ = R₁
    · rw [e]
    · have hm : R₂ ∈ omegaNbr Ω R₁ := by
        rw [KPerp, Set.mem_insert_iff] at hc
        exact hc.resolve_left e
      exact hA R₁ hR₁ R₂ hm
  exact le_antisymm (perpAV_le_of_kperp h hR₁ hR₂ hK hc)
    (perpAV_le_of_kperp h hR₂ hR₁ hK.symm ((perpA_kperp_symm h hR₁ hR₂).mpr hc))

private theorem perpAV_conj_le (h : EndHyp Ω) {R : Subgroup G} (hR : R ∈ Ω) {n : G}
    (hn : ∀ y ∈ perpAV Ω R, n * y = y * n) : perpAV Ω (conjSub n R) ≤ perpAV Ω R := by
  unfold perpAV
  rw [Subgroup.closure_le]
  rintro x ⟨J', hJ', u', u'', hu', hu'', rfl⟩
  have hJ'Ω : J' ∈ Ω := by
    rw [KPerp, Set.mem_insert_iff] at hJ'
    rcases hJ' with e | hm
    · rw [e]
      exact h.thmD.hyp.conjInvariant n R hR
    · exact hm.1
  have hJ : conjSub n⁻¹ J' ∈ KPerp Ω R := by
    refine (perpA_conj_kperp h n hR (h.thmD.hyp.conjInvariant n⁻¹ J' hJ'Ω)).mpr ?_
    rw [conjSub_conjSub_inv]
    exact hJ'
  obtain ⟨u₁, hu₁⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hR
  obtain ⟨uJ, huJ⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp
    (h.thmD.hyp.conjInvariant n⁻¹ J' hJ'Ω)
  have hJ'eq : conjSub n (conjSub n⁻¹ J') = J' := conjSub_conjSub_inv n J'
  have hcu' : IsUniqueInvolution (conjSub n R) (n * u₁ * n⁻¹) := hu₁.conj n
  have hu'eq : u' = n * u₁ * n⁻¹ := hu'.eq hcu'
  have hcu'' : IsUniqueInvolution J' (n * uJ * n⁻¹) := by
    have := huJ.conj n
    rwa [hJ'eq] at this
  have hu''eq : u'' = n * uJ * n⁻¹ := hu''.eq hcu''
  have hgen : u₁ * uJ ∈ perpAV Ω R := perpAV_gen hJ hu₁ huJ
  have hcomm := hn _ hgen
  have key : n * u₁ * n⁻¹ * (n * uJ * n⁻¹) = u₁ * uJ := by
    calc n * u₁ * n⁻¹ * (n * uJ * n⁻¹) = n * (u₁ * uJ) * n⁻¹ := by group
      _ = (u₁ * uJ * n) * n⁻¹ := by rw [hcomm]
      _ = u₁ * uJ := by group
  rw [hu'eq, hu''eq, key]
  exact hgen

private theorem perpAV_le_vW (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    perpAV Ω R ≤ vW Ω W := by
  unfold perpAV
  rw [Subgroup.closure_le]
  rintro x ⟨J, hJ, u, u', hu, hu', rfl⟩
  unfold vW
  exact Subgroup.subset_closure
    ⟨R, hR, J, perpA_kperp_subset_dSet h hA hW hR hJ, hJ, u, u', hu, hu', rfl⟩

private theorem perpAV_eq (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ DSet Ω W)
    (hR₂ : R₂ ∈ DSet Ω W) : perpAV Ω R₁ = perpAV Ω R₂ := by
  have hR₁Ω : R₁ ∈ Ω := (h.mem_dSet_iff.mp hR₁).1
  have hR₂Ω : R₂ ∈ Ω := (h.mem_dSet_iff.mp hR₂).1
  by_cases hc : R₂ ∈ KPerp Ω R₁
  · exact perpAV_eq_of_mem_kperp h hA hR₁Ω hR₂Ω hc
  · obtain ⟨r, hr, l, hl, hrl⟩ := perpA_exists_conj h hW hR₁ hR₂ hc
    have hcen : ∀ g ∈ Subgroup.centralizer (vW Ω W : Set G), ∀ y ∈ vW Ω W, g * y = y * g :=
      fun g hg y hy => (Subgroup.mem_centralizer_iff.mp hg y hy).symm
    have hrC := dSet_le_centralizer_vW h hW hR₁ hr
    have hlC := dSet_le_centralizer_vW h hW hR₂ hl
    have hnC : r * l ∈ Subgroup.centralizer (vW Ω W : Set G) := Subgroup.mul_mem _ hrC hlC
    have hninvC : (r * l)⁻¹ ∈ Subgroup.centralizer (vW Ω W : Set G) :=
      Subgroup.inv_mem _ hnC
    have hV1 : ∀ y ∈ perpAV Ω R₁, y ∈ vW Ω W := fun y hy => perpAV_le_vW h hA hW hR₁ hy
    have hV2 : ∀ y ∈ perpAV Ω R₂, y ∈ vW Ω W := fun y hy => perpAV_le_vW h hA hW hR₂ hy
    have hA1 := perpAV_conj_le h hR₁Ω (n := r * l) (fun y hy => hcen _ hnC y (hV1 y hy))
    have hA2 := perpAV_conj_le h hR₂Ω (n := (r * l)⁻¹)
      (fun y hy => hcen _ hninvC y (hV2 y hy))
    have hinv : conjSub (r * l)⁻¹ R₂ = R₁ := by
      rw [← hrl, conjSub_inv_conjSub]
    rw [hrl] at hA1
    rw [hinv] at hA2
    exact le_antisymm hA2 hA1

private theorem perpAV_eq_vW (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    perpAV Ω R = vW Ω W := by
  refine le_antisymm (perpAV_le_vW h hA hW hR) ?_
  unfold vW
  rw [Subgroup.closure_le]
  rintro x ⟨R₁, hR₁, J, hJ, hRJ, u, u', hu, hu', rfl⟩
  rw [← perpAV_eq h hA hW hR₁ hR]
  exact perpAV_gen hRJ hu hu'

private theorem perpAV_dstarAdj (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L) {L J : Subgroup G}
    (hLΩ : L ∈ Ω) (hadj : dstarAdj Ω L J) : perpAV Ω L = perpAV Ω J := by
  obtain ⟨hJΩ, hstar⟩ := hadj
  rcases hstar with hJs | hLs
  · by_cases hJn : J ∈ omegaNbr Ω L
    · obtain ⟨W, hW, hLD, hJD⟩ :=
        perpA_exists_wSet_pair h hLΩ hJΩ (Set.mem_insert_of_mem _ hJn)
      exact perpAV_eq h hA hW hLD hJD
    · obtain ⟨W, hW, hLD, hJD, -⟩ := exists_wSet_of_omegaStar h hLΩ hJs hJn
      exact perpAV_eq h hA hW hLD hJD
  · have hLΩ' : L ∈ Ω := hLs.1
    by_cases hLn : L ∈ omegaNbr Ω J
    · obtain ⟨W, hW, hJD, hLD⟩ :=
        perpA_exists_wSet_pair h hJΩ hLΩ' (Set.mem_insert_of_mem _ hLn)
      exact perpAV_eq h hA hW hLD hJD
    · obtain ⟨W, hW, hJD, hLD, -⟩ := exists_wSet_of_omegaStar h hJΩ hLs hLn
      exact perpAV_eq h hA hW hLD hJD

private theorem perpAV_const_of_star (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ Ω) {J : Subgroup G} (hJ : J ∈ dstarComp Ω K₀) :
    perpAV Ω J = perpAV Ω K₀ := by
  have key : ∀ b, Relation.ReflTransGen (dstarAdj Ω) K₀ b →
      b ∈ Ω ∧ perpAV Ω b = perpAV Ω K₀ := by
    intro b hb
    induction hb with
    | refl => exact ⟨hK₀, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨hbΩ, hbV⟩ := ih
      exact ⟨hbc.1, (perpAV_dstarAdj h hA hbΩ hbc).symm.trans hbV⟩
  exact (key J hJ).2

theorem kPerp_eq_twinSet_of_caseA (h : EndHyp Ω)
    (hA : ∀ L ∈ Ω, ∀ J ∈ omegaNbr Ω L, KPerp Ω J = KPerp Ω L) :
    ∀ K ∈ Ω, KPerp Ω K = twinSet Ω K := by
  obtain ⟨K₀, hK₀, -, -, -⟩ := h.exists_ne
  have hV : ∀ M ∈ Ω, perpAV Ω M = perpAV Ω K₀ := fun M hM =>
    perpAV_const_of_star h hA hK₀ (h.star K₀ hK₀ M hM)
  have hcen : ∀ M ∈ Ω, ∀ y ∈ perpAV Ω K₀, ∀ m ∈ M, m * y = y * m := by
    intro M hM y hy m hm
    obtain ⟨W, hW, hMD, -⟩ := perpA_exists_wSet_pair h hM hM (perpA_self_mem M)
    have hVW : perpAV Ω K₀ = vW Ω W := by
      rw [← hV M hM]
      exact perpAV_eq_vW h hA hW hMD
    have hmC := Subgroup.mem_centralizer_iff.mp (dSet_le_centralizer_vW h hW hMD hm) y
      (hVW ▸ hy)
    exact hmC.symm
  have hV0 : ∀ y ∈ perpAV Ω K₀, y ∈ Subgroup.center G := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ pSpan Ω := by
      rw [h.thmD.gen]
      exact Subgroup.mem_top g
    have hle : pSpan Ω ≤ Subgroup.centralizer ({y} : Set G) := by
      unfold pSpan
      refine iSup₂_le fun M hM => ?_
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcen M hM y hy m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hV00 : ∀ y ∈ perpAV Ω K₀, y = 1 := fun y hy => by
    have hc := hV0 y hy
    rw [h.center] at hc
    exact Subgroup.mem_bot.mp hc
  intro K hK
  apply Set.Subset.antisymm
  · intro J hJ
    have hJΩ : J ∈ Ω := by
      rw [KPerp, Set.mem_insert_iff] at hJ
      rcases hJ with e | hm
      · rw [e]
        exact hK
      · exact hm.1
    obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
    obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJΩ
    have hgen : zK * zJ ∈ perpAV Ω K := perpAV_gen hJ hzK hzJ
    rw [hV K hK] at hgen
    have h1 := hV00 _ hgen
    have hinv : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
    have hzeq : zJ = zK := by
      calc zJ = zK⁻¹ * (zK * zJ) := by group
        _ = zK := by rw [h1, mul_one, hinv]
    exact ⟨hJΩ, zK, hzK, hzeq ▸ hzJ⟩
  · rintro J ⟨hJΩ, z, hzK, hzJ⟩
    by_cases hJK : J = K
    · rw [hJK]
      exact perpA_self_mem K
    · exact Set.mem_insert_of_mem _ (Q3CL.T3.twin_mem_omegaNbr h.thmD.hyp hK hJΩ hJK hzK hzJ)

end CFSG.ClassicalInvolution.Q3.Sec13
