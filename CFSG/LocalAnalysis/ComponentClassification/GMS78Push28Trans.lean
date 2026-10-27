module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Frame
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G]

theorem card_eq_card_delta_mul [Finite G] {X Q₀ : Subgroup G} {Δ : Set (Subgroup G)}
    (hsub : ∀ x ∈ X, rightConjugate Q₀ x ∈ Δ) (hsurj : ∀ Q ∈ Δ, ∃ x ∈ X, rightConjugate Q₀ x = Q) :
    Nat.card X = Nat.card Δ * Nat.card (X ⊓ normalizer (Q₀ : Set G) : Subgroup G) := by
  classical
  let _ : MulAction X (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp X.subtype)
  have hsmul : ∀ (x : X) (H : Subgroup G), x • H = rightConjugate H (x : G)⁻¹ := by
    intro x H
    ext y
    rw [mem_rightConjugate_iff, inv_inv]
    change y ∈ (MulAut.conj (x : G)) • H ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_symm_apply, mul_assoc]
  have horbit : MulAction.orbit X Q₀ = Δ := by
    ext Q
    constructor
    · rintro ⟨x, rfl⟩
      change x • Q₀ ∈ Δ
      rw [hsmul]
      exact hsub _ (inv_mem x.2)
    · intro hQ
      obtain ⟨x, hx, rfl⟩ := hsurj Q hQ
      refine ⟨⟨x⁻¹, inv_mem hx⟩, ?_⟩
      change (⟨x⁻¹, inv_mem hx⟩ : X) • Q₀ = _
      rw [hsmul, inv_inv]
  have hstab : ∀ x : X, x ∈ MulAction.stabilizer X Q₀ ↔ (x : G) ∈ normalizer (Q₀ : Set G) := by
    intro x
    rw [MulAction.mem_stabilizer_iff, hsmul, rightConjugate_eq_self_iff, inv_mem_iff]
  have hcard : Nat.card (MulAction.stabilizer X Q₀) =
      Nat.card (X ⊓ normalizer (Q₀ : Set G) : Subgroup G) := by
    have heq : MulAction.stabilizer X Q₀ = (normalizer (Q₀ : Set G)).subgroupOf X := by
      ext x
      rw [hstab, mem_subgroupOf]
    rw [heq, ← inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : X ⊓ _ ≤ X)).toEquiv
  have h1 := (MulAction.stabilizer X Q₀).card_mul_index
  rw [MulAction.index_stabilizer, horbit, hcard, ← Nat.card_coe_set_eq] at h1
  rw [← h1, mul_comm]

theorem conj_eq_of_odd_of_eq_mul {x b a : G} (hx : Odd (orderOf x))
    (hxa : x * a = a * x) (ha : a * a = 1) (hxb : x * b * x⁻¹ = b * a) : x * b * x⁻¹ = b := by
  have hpow : ∀ k : ℕ, x ^ k * b * (x ^ k)⁻¹ = b * a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxak : x * a ^ k * x⁻¹ = a ^ k := by
        rw [(Commute.pow_right hxa k).eq]
        group
      calc x ^ (k + 1) * b * (x ^ (k + 1))⁻¹ = x * (x ^ k * b * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * b * x⁻¹ * (x * a ^ k * x⁻¹) := by rw [ih]; group
        _ = b * a ^ (k + 1) := by rw [hxb, hxak, pow_succ']; group
  obtain ⟨m, hm⟩ := hx
  have h1 := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hm] at h1
  have h2 : a ^ (2 * m + 1) = a := by
    rw [pow_succ, pow_mul, sq, ha, one_pow, one_mul]
  rw [h2] at h1
  rw [hxb]
  exact h1.symm

namespace Sec3

variable [Finite G] {L T : Subgroup G} {f : ℕ}

theorem gmsW_eq_of_psl2 (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : gmsW L T = gmsV L T := by
  show (T ⊓ L) ⊔ _ = gmsA L T ⊔ _
  rw [h.gmsA_eq_of_psl2 hf e]

theorem inf_centralizer_eq_of_psl2
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Facts L T (2 ^ f)) : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T := by
  rw [h.gmsW_eq_of_psl2 hf e]
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  have hVT : gmsV L T ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
  refine le_antisymm (fun x hx => ?_) (le_inf hVT (le_centralizer_iff_isMulCommutative.mpr hVel.1))
  obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
  exact h.mem_V_of_commute hf e hxT fun a ha =>
    (mem_centralizer_iff.mp hxC a (mem_sup_left ha)).symm

theorem commute_of_odd_of_mem_gmsTrans_of_psl2
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Facts L T (2 ^ f)) :
    ∀ x ∈ gmsTrans L T, x ∈ normalizer (gmsW L T : Set G) → Odd (orderOf x) →
      x ∈ centralizer (gmsW L T : Set G) := by
  intro x hx _ hxo
  rw [h.gmsW_eq_of_psl2 hf e]
  obtain ⟨-, hA₁sq, -⟩ := hX.sylow h
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  rw [mem_centralizer_iff]
  intro v hv
  have hav : x * v * x⁻¹ * v⁻¹ ∈ gmsA L T := conj_mul_inv_mem hx hv
  have hcomm : v * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * v :=
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨_, mem_sup_left hav⟩)
  have h1 := conj_eq_of_odd_of_eq_mul hxo (commute_of_mem_gmsTrans hx hav)
    (by rw [← pow_two]; exact hA₁sq _ hav) (b := v) (by rw [hcomm]; group)
  calc v * x = x * v * x⁻¹ * x := by rw [h1]
    _ = x * v := by group

theorem gmsV_inf_centralizer_eq (h : Sec3 G L T) (hX : Facts L T (2 ^ f)) :
    gmsV L T ⊓ centralizer (L : Set G) = T ⊓ centralizer (L : Set G) := by
  have hinf := h.inf_eq_bot_of_odd hX.oddCenter
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right inf_le_right)
  obtain ⟨hxV, hxC⟩ := mem_inf.mp hx
  obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_eq_of_mem_V hxV
  have haC : a ∈ centralizer (L : Set G) := by
    have := mul_mem hxC (inv_mem (mem_inf.mp ht).2)
    rwa [mul_inv_cancel_right] at this
  have haT : a ∈ T := (mem_inf.mp (mem_inf.mp ha).1).1
  have h1 : a ∈ (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) :=
    mem_inf.mpr ⟨(mem_inf.mp ha).1, mem_inf.mpr ⟨haT, haC⟩⟩
  rw [hinf, mem_bot] at h1
  rw [h1, one_mul]
  exact ht

namespace IsR

variable {R : Subgroup G}

theorem gmsV_le_of_psl2 (hR : IsR L T R) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : gmsV L T ≤ R :=
  h.gmsW_eq_of_psl2 hf e ▸ hR.gmsW_le

theorem mem_gmsV_of_psl2
    (hR : IsR L T R) (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Facts L T (2 ^ f))
    {r : G} (hr : r ∈ R) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T)
    (hrQ : r ∈ normalizer (Q : Set G)) : r ∈ gmsV L T := by
  rw [← h.gmsW_eq_of_psl2 hf e]
  exact hR.mem_gmsW_of_mem_normalizer h313 hX h hF (h.inf_centralizer_eq_of_psl2 hF hf e hX) hr
    hQ hrQ

theorem inf_normalizer_eq_of_psl2
    (hR : IsR L T R) (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Facts L T (2 ^ f)) :
    R ⊓ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) = gmsV L T := by
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  refine le_antisymm (fun r hr => hR.mem_gmsV_of_psl2 h313 h hF hf e hX (mem_inf.mp hr).1
    mem_delta_T₀ (mem_inf.mp hr).2) (le_inf (hR.gmsV_le_of_psl2 h hf e) fun v hv => ?_)
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht => ?_)
  exact congrArg Subtype.val (hVel.1.is_comm.comm ⟨t, mem_sup_right ht⟩ ⟨v, hv⟩)

theorem card_eq_of_psl2
    (hR : IsR L T R) (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q) :
    Nat.card R = 2 ^ f * Nat.card (gmsV L T) := by
  have h1 := card_eq_card_delta_mul (X := R) (Q₀ := T ⊓ centralizer (L : Set G))
    (Δ := gmsDelta L T) (fun x hx => rightConjugate_mem_delta mem_delta_T₀
      (hR.le_normalizer_gmsV hx)) (fun Q hQ => by
        obtain ⟨r, hr, hrQ⟩ := hR.exists_conj_eq hX h htr hQ
        exact ⟨r⁻¹, inv_mem hr, hrQ⟩)
  rw [h1, h313.card_eq, hR.inf_normalizer_eq_of_psl2 h313 h hF hf e hX]

theorem isSylowOf_sup_of_psl2
    (hR : IsR L T R) (h : Sec3 G L T) (hX : Facts L T (2 ^ f))
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q) :
    IsSylowOf 2 (R ⊔ T) (normalizer (gmsV L T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀
  have hle : R ⊔ T ≤ normalizer (gmsV L T : Set G) :=
    sup_le hR.le_normalizer_gmsV h.le_normalizer_gmsV
  have hp : IsPGroup 2 (R ⊔ T : Subgroup G) := by
    rw [sup_comm]
    exact h.sylow.isPGroup.to_sup_of_normal_right' hR.isPGroup hR.le_normalizer
  obtain ⟨S, hS, hRS⟩ := AS76b.exists_isSylowOf_le hle hp
  have hSle : S ≤ R ⊔ T := by
    intro s hs
    have hsV : s ∈ normalizer (gmsV L T : Set G) := hS.le hs
    obtain ⟨r, hr, hrs⟩ := hR.exists_conj_eq hX h htr
      (rightConjugate_mem_delta mem_delta_T₀ (inv_mem hsV))
    have hN : r⁻¹ * s ∈ normalizer (T₀ : Set G) := by
      have h1 : rightConjugate T₀ (s⁻¹ * r) = T₀ := by
        rw [← rightConjugate_mul, ← hrs, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
      have := inv_mem ((rightConjugate_eq_self_iff T₀ _).mp h1)
      rwa [mul_inv_rev, inv_inv] at this
    have hrsS : r⁻¹ * s ∈ S := mul_mem (inv_mem (hRS (mem_sup_left hr))) hs
    have hrsT : r⁻¹ * s ∈ T :=
      h.mem_of_mem_normalizer hS.isPGroup (le_sup_right.trans hRS) hrsS (h.normalizer_T₀_le hN)
    have : s = r * (r⁻¹ * s) := by group
    rw [this]
    exact mul_mem (mem_sup_left hr) (mem_sup_right hrsT)
  rwa [le_antisymm hSle hRS] at hS

theorem sec4Frame_of_psl2 (hR : IsR L T R) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : Sec4Frame L T R where
  V_le := hR.gmsV_le_of_psl2 h hf e
  comm_A := fun _ hw _ ha => commute_of_mem_gmsTrans (hR.le_gmsTrans hw) ha
  le_normalizer := hR.le_normalizer
  inf_T := by
    have hVT : gmsV L T ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
    refine le_antisymm (fun x hx => ?_) (le_inf (hR.gmsV_le_of_psl2 h hf e) hVT)
    obtain ⟨hxR, hxT⟩ := mem_inf.mp hx
    exact h.mem_V_of_commute hf e hxT fun a ha => commute_of_mem_gmsTrans (hR.le_gmsTrans hxR) ha

end IsR

end Sec3

end CFSG.ComponentClassification.GMS78
