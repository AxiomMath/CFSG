module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3Swap
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem perm_sq_eq_one_of_two_pow {A : Type} [Group A] [Finite A] (hc : Nat.card (Idx2 A) = 3)
    (σ : Equiv.Perm (Idx2 A)) {k : ℕ} (hk : σ ^ (2 ^ k) = 1) : σ * σ = 1 := by
  classical
  have hf : Fintype.card (Idx2 A) = 3 := by rw [← Nat.card_eq_fintype_card]; exact hc
  have h6 : Fintype.card (Equiv.Perm (Idx2 A)) = 6 := by
    rw [Fintype.card_perm, hf]; rfl
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf σ ∣ 6 := h6 ▸ orderOf_dvd_card
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hne
    push Not at hne
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hne).trans (hjo ▸ h2)
    norm_num at this
  have h3 : orderOf σ ∣ 2 := by
    rw [hjo]
    exact (pow_dvd_pow 2 hj1).trans (by norm_num)
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem innerOn_comm_invol {L : Subgroup G} (eL : Kbar L ≃* Q8) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (h2 : ⁅x, y⁆ * ⁅x, y⁆ = 1) : InnerOn L ⁅x, y⁆ := by
  set N := Subgroup.normalizer (L : Set G) with hN
  set a : ↥N := ⟨x, hx⟩ with ha
  set b : ↥N := ⟨y, hy⟩ with hb
  have hab : ((⁅a, b⁆ : ↥N) : G) = ⁅x, y⁆ := rfl
  have key : psiK L ⁅a, b⁆ = 1 := by
    set σ := psiK L ⁅a, b⁆ with hσ
    by_contra hne
    have hσ2 : σ * σ = 1 := by
      rw [hσ, ← map_mul]
      have : ⁅a, b⁆ * ⁅a, b⁆ = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, hab]; exact h2)
      rw [this, map_one]
    have hs := sign_eq_neg_one_of_invol (card_idx2_of_equiv_q8 eL) σ hne hσ2
    have hs1 : Equiv.Perm.sign σ = 1 := by
      rw [hσ, map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [hs1] at hs
    exact absurd hs (by decide)
  have := (psiK_eq_one_iff L eL _).mp key
  rwa [hab] at this

theorem inner_or_inner_mul {L : Subgroup G} (eL : Kbar L ≃* Q8) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (L : Set G)) {v g : G} (hvT : v ∈ T)
    (hv : ¬ InnerOn L v) (hgT : g ∈ T) : InnerOn L g ∨ InnerOn L (g * v⁻¹) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hc3 := card_idx2_of_equiv_q8 eL
  have hsq : ∀ x (hx : x ∈ T), psiK L ⟨x, hTN hx⟩ * psiK L ⟨x, hTN hx⟩ = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := by
      have := pow_orderOf_eq_one (⟨x, hx⟩ : ↥T)
      rw [hk] at this
      exact congrArg Subtype.val this
    refine perm_sq_eq_one_of_two_pow hc3 _ (k := k) ?_
    rw [← map_pow]
    have : (⟨x, hTN hx⟩ : ↥N) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hsign : ∀ x (hx : x ∈ T), psiK L ⟨x, hTN hx⟩ ≠ 1 →
      Equiv.Perm.sign (psiK L ⟨x, hTN hx⟩) = -1 := fun x hx hne =>
    sign_eq_neg_one_of_invol hc3 _ hne (hsq x hx)
  by_contra hcon
  push Not at hcon
  obtain ⟨hg1, hg2⟩ := hcon
  have hgv : g * v⁻¹ ∈ T := T.mul_mem hgT (T.inv_mem hvT)
  have ne1 : psiK L ⟨g, hTN hgT⟩ ≠ 1 := fun h => hg1 ((psiK_eq_one_iff L eL _).mp h)
  have ne2 : psiK L ⟨v, hTN hvT⟩ ≠ 1 := fun h => hv ((psiK_eq_one_iff L eL _).mp h)
  have ne3 : psiK L ⟨g * v⁻¹, hTN hgv⟩ ≠ 1 := fun h => hg2 ((psiK_eq_one_iff L eL _).mp h)
  have e : (⟨g * v⁻¹, hTN hgv⟩ : ↥N) = ⟨g, hTN hgT⟩ * (⟨v, hTN hvT⟩)⁻¹ := rfl
  have h3 := hsign _ hgv ne3
  rw [e, map_mul, map_inv, map_mul, map_inv, hsign _ hgT ne1, hsign _ hvT ne2] at h3
  exact absurd h3 (by decide)

end Generic


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section TX

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem cmo_K_le (c8 : Concl20_8 S K' R) {y : G}
    (hy : y ∈ centralizerModOdd (S : Subgroup G) K) : y ∈ R' := by
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  obtain ⟨hK'u, hRu, -, hSu⟩ := d.late_swap_data hu huK
  have h1 := late_cmo_conj_mem hy u⁻¹
  have hSi : conjSub u⁻¹ (S : Subgroup G) = S := conjSub_eq_self_of_mem (S.inv_mem hu)
  have hKi : conjSub u⁻¹ K = K' := by rw [← hK'u, conjSub_inv_conjSub]
  rw [hSi, hKi] at h1
  have c8' : centralizerModOdd (S : Subgroup G) K' = R := c8
  rw [c8'] at h1
  rw [← hRu, mem_conjSub_iff]
  simpa using h1

theorem mem_sup_of_innerOn (c8 : Concl20_8 S K' R) {y : G} (hyS : y ∈ (S : Subgroup G))
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hy : InnerOn K y) : y ∈ R ⊔ R' := by
  obtain ⟨k, hkK, hk⟩ := hy
  obtain ⟨r, hr, o, ho, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow d.twoGroup d.hR k hkK
  have hrK : r ∈ K := d.hR.1 hr
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hrK
  have hrS : r ∈ (S : Subgroup G) := d.hRS hr
  have hy' : r⁻¹ * y ∈ centralizerModOdd (S : Subgroup G) K := by
    have hN : r⁻¹ * y ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hrN) hyN
    refine ⟨S.mul_mem (S.inv_mem hrS) hyS, hN, mem_normalizer_oddCore_of_mem_normalizer hN,
      fun l hl => ?_⟩
    have h1 := hk l hl
    have hoK : o ∈ K := oddCoreOf_le_self K ho
    have h2 : ⁅o, l⁆ ∈ oddCoreOf K := by
      have e : ⁅o, l⁆ = o * (l * o⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (oddCoreOf K).mul_mem ho (mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer hl) ((oddCoreOf K).inv_mem ho))
    have e : ⁅r⁻¹ * y, l⁆ = r⁻¹ * ((y * l * y⁻¹) * (r * o * l * (r * o)⁻¹)⁻¹) * r⁻¹⁻¹ *
        ⁅o, l⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (oddCoreOf K).mul_mem (mem_normalizer_oddCoreOf_of_mem_normalizer
      (Subgroup.inv_mem _ hrN) h1) h2
  have hR' := cmo_K_le d c8 hy'
  have e : y = r * (r⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hR')

theorem frame_TX (c8 : Concl20_8 S K' R) {g : G} (hg : g ∈ (S : Subgroup G))
    (hgK : conjSub g K = K) : g ∈ R ⊔ R' ⊔ V := by
  obtain ⟨e⟩ := kbar_equiv_q8 d
  obtain ⟨v, hvV, -, hv1, -⟩ := exists_gen_V d
  have hXN := frameX_le_N d
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := hXN (tw.hVX hvV)
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 T := S.isPGroup'.to_le inf_le_left
  have hvT : v ∈ T := ⟨d.hVS hvV, hvN⟩
  have hgT : g ∈ T := ⟨hg, mem_normalizer_iff_conjSub_eq.mpr hgK⟩
  have hvout : ¬ InnerOn K v :=
    (frame203Outer G K K' J S R R' W V z t d v hvV hv1).1
  rcases inner_or_inner_mul e hT2 inf_le_right hvT hvout hgT with h | h
  · exact Subgroup.mem_sup_left (mem_sup_of_innerOn d c8 hg hgT.2 h)
  · have hgv : g * v⁻¹ ∈ T := T.mul_mem hgT (T.inv_mem hvT)
    have h1 := mem_sup_of_innerOn d c8 hgv.1 hgv.2 h
    have e1 : g = (g * v⁻¹) * v := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hvV)

theorem frame_SX (c8 : Concl20_8 S K' R) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' = R ⊔ R' ⊔ V := by
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  apply le_antisymm
  · rintro x ⟨hxS, hxX⟩
    exact frame_TX d c8 hxS (mem_normalizer_iff_conjSub_eq.mp (frameX_le_N d hxX))
  · exact le_inf (sup_le (sup_le d.hRS d.hR'S) d.hVS)
      (sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX)

end TX

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
