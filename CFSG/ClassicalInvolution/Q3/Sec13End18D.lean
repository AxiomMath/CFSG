module

public import CFSG.ClassicalInvolution.Q3.Sec13End18B
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.Sec13End15A

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace End18

namespace Hyp

variable {Ω : Set (Subgroup G)}

private theorem e18d_zGroup_normal (H : Hyp Ω) : (zGroup Ω).Normal :=
  zGroup_normal_of_conjInvariant H.endHyp.thmD.hyp.conjInvariant

private theorem e18d_mem_zGroup {L : Subgroup G} {u : G} (hL : L ∈ Ω)
    (hu : IsUniqueInvolution L u) : u ∈ zGroup Ω :=
  Subgroup.subset_closure ⟨L, hL, hu⟩

private theorem e18d_conj_conj (H : Hyp Ω) {s : G} (hs : s ∈ zGroup Ω) (X : Subgroup G) :
    conjSub s (conjSub s X) = X := by
  rw [← conjSub_mul, H.endHyp.zGroup_mul_self H.perp9 s hs, conjSub_one]

private theorem e18d_conj_mem_twinSet (H : Hyp Ω) {M : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) {X : Subgroup G}
    (hX : X ∈ twinSet Ω M) : conjSub r X ∈ twinSet Ω M := by
  obtain ⟨hXΩ, z', hz'M, hz'X⟩ := hX
  have hzD : z' ∈ zGroup Ω := e18d_mem_zGroup hXΩ hz'X
  have hc : z' * r = r * z' := Subgroup.mem_centralizer_iff.mp hr z' hzD
  have e : r * z' * r⁻¹ = z' := by rw [← hc, mul_inv_cancel_right]
  have hconj := hz'X.conj r
  rw [e] at hconj
  exact ⟨H.endHyp.thmD.hyp.conjInvariant r X hXΩ, z', hz'M, hconj⟩

private theorem e18d_iter_conjSub (r : G) (n : ℕ) (X : Subgroup G) :
    (conjSub r)^[n] X = conjSub (r ^ n) X := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← conjSub_mul, pow_succ']

private theorem e18d_conjSub_sup (q : G) (A B : Subgroup G) :
    conjSub q (A ⊔ B) = conjSub q A ⊔ conjSub q B :=
  Subgroup.map_sup A B _

private theorem e18d_commutes_sup_right {A B C : Subgroup G} (h1 : Commutes A B)
    (h2 : Commutes A C) : Commutes A (B ⊔ C) := by
  intro x hx y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact h1 x hx y hy
    · exact h2 x hx y hy
  | one => simp
  | mul a b _ _ ha hb =>
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [ha]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hb]
      _ = a * b * x := by group
  | inv a _ ha =>
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * x := by group

private theorem e18d_le_normalizer {A B : Subgroup G} (h : Commutes B A) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : x * y * x⁻¹ = y := by
      rw [← h y hy x hx, mul_inv_cancel_right]
    rw [e]
    exact hy
  · intro hy
    have hc := h _ hy x⁻¹ (A.inv_mem hx)
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [hc]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

private theorem e18d_ncard_le_three {α : Type} (a b c : α) :
    ({a, b, c} : Set α).ncard ≤ 3 := by
  refine (Set.ncard_insert_le a {b, c}).trans ?_
  have := Set.ncard_insert_le b {c}
  rw [Set.ncard_singleton] at this
  omega

private theorem e18d_ncard_four_distinct {α : Type} {a b c d : α}
    (h : ({a, b, c, d} : Set α).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [Set.insert_eq_of_mem (show a ∈ ({b, c, d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three b c d
    omega
  · rw [Set.insert_eq_of_mem (show a ∈ ({b, c, d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three b c d
    omega
  · rw [Set.insert_eq_of_mem (show a ∈ ({b, c, d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three b c d
    omega
  · rw [Set.insert_eq_of_mem (show b ∈ ({c, d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three a c d
    omega
  · rw [Set.insert_eq_of_mem (show b ∈ ({c, d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three a c d
    omega
  · rw [Set.insert_eq_of_mem (show c ∈ ({d} : Set α) by simp [e])] at h
    have := e18d_ncard_le_three a b d
    omega

private theorem e18d_ncard_four_of_distinct {α : Type} {a b c d : α} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Set α).ncard = 4 := by
  have h1 : a ∉ ({b, c, d} : Set α) := by simp [hab, hac, had]
  have h2 : b ∉ ({c, d} : Set α) := by simp [hbc, hbd]
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hcd]

private theorem e18d_exists_two_pow {D : Subgroup G} {x : G} (hx : x ∈ D)
    (hodd : ∀ y ∈ D, Odd (orderOf y) → y = 1) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hym : (x ^ (2 ^ k)) ^ m = 1 := by
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  have hodd' : Odd (orderOf (x ^ (2 ^ k))) :=
    hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
  exact ⟨k, hodd _ (pow_mem hx _) hodd'⟩

private theorem e18d_center_le (H : Hyp Ω) {L : Subgroup G} (hL : L ∈ Ω) {u : G}
    (hu : IsUniqueInvolution L u) {c : G} (hc : c ∈ L) (hcc : ∀ y ∈ L, c * y = y * c) :
    c ∈ Subgroup.zpowers u := by
  have hq : IsQuatSub L :=
    Sec6Gen.isQuatSub_of_mem_RSet H.endHyp.thmD.hyp
      (TC.mem_RSet_of_isPGroup hL (H.endHyp.thmD.two L hL))
  rcases hu.unique c hc (IsQuatSub.sq_eq_one_of_central hq hc hcc) with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact Subgroup.mem_zpowers u

private theorem e18d_swap_conj {K : Subgroup G} {s k₁ : G} (hc : Commutes K (conjSub s K))
    (hk₁ : k₁ ∈ K) (k' : G) (hk' : k' ∈ K) :
    (s * k₁ * s⁻¹ * k₁⁻¹) * k' * (s * k₁ * s⁻¹ * k₁⁻¹)⁻¹ = k₁⁻¹ * k' * k₁ := by
  have hx : k₁⁻¹ * k' * k₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk₁) hk') hk₁
  have hκ : s * k₁ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub hk₁
  have hcm := hc _ hx _ hκ
  calc (s * k₁ * s⁻¹ * k₁⁻¹) * k' * (s * k₁ * s⁻¹ * k₁⁻¹)⁻¹
      = (s * k₁ * s⁻¹) * (k₁⁻¹ * k' * k₁) * (s * k₁ * s⁻¹)⁻¹ := by group
    _ = (k₁⁻¹ * k' * k₁) * (s * k₁ * s⁻¹) * (s * k₁ * s⁻¹)⁻¹ := by rw [← hcm]
    _ = k₁⁻¹ * k' * k₁ := by group

private theorem e18d_comm_mem (H : Hyp Ω) {s k₁ : G} (hs : s ∈ zGroup Ω) :
    s * k₁ * s⁻¹ * k₁⁻¹ ∈ zGroup Ω := by
  have hN := e18d_zGroup_normal H
  have h1 := hN.conj_mem s⁻¹ ((zGroup Ω).inv_mem hs) k₁
  have e : s * k₁ * s⁻¹ * k₁⁻¹ = s * (k₁ * s⁻¹ * k₁⁻¹) := by group
  rw [e]
  exact (zGroup Ω).mul_mem hs h1

private theorem e18d_fix_four {α : Type} {f g : α → α} {m : ℕ} (hm : Odd m)
    (hf : Function.Injective f) (hg : ∀ x, g (g x) = x) (hfg : ∀ x, f (g x) = g (f x))
    {a b : α} (hfm : f^[m] a = a) (h1 : a ≠ g a) (h2 : a ≠ b) (h3 : a ≠ g b) (h4 : g a ≠ b)
    (hfa : f a = a ∨ f a = g a ∨ f a = b ∨ f a = g b)
    (hfb : f b = a ∨ f b = g a ∨ f b = b ∨ f b = g b) : f a = a := by
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have per2 : f (f a) = a → f a = a := by
    intro h
    have hp : Function.IsPeriodicPt f 2 a := h
    have h1' := hp.iterate_mod_apply m
    rw [hfm, hm2, Function.iterate_one] at h1'
    exact h1'
  have per4 : f^[4] a = a → f a = a := by
    intro h
    have hp : Function.IsPeriodicPt f 4 a := h
    have h1' := hp.iterate_mod_apply m
    rw [hfm] at h1'
    rcases (show m % 4 = 1 ∨ m % 4 = 3 by omega) with h4' | h4'
    · rw [h4', Function.iterate_one] at h1'
      exact h1'
    · rw [h4'] at h1'
      calc f a = f (f^[3] a) := by rw [h1']
        _ = f^[3 + 1] a := (Function.iterate_succ_apply' f 3 a).symm
        _ = a := h
  rcases hfa with ha | ha | ha | ha
  · exact ha
  ·
    exfalso
    have hff : f (f a) = a := by
      rw [ha, hfg, ha]
      exact hg a
    exact h1 (by rw [← ha, per2 hff])
  ·
    exfalso
    rcases hfb with hb | hb | hb | hb
    · have hff : f (f a) = a := by
        rw [ha]
        exact hb
      exact h2 ((per2 hff).symm.trans ha)
    ·
      have hff4 : f^[4] a = a := by
        show f (f (f (f a))) = a
        rw [ha, hb, hfg, ha, hfg, hb, hg]
      exact h2 ((per4 hff4).symm.trans ha)
    · exact h2 (hf (ha.trans hb.symm))
    · have : f (g a) = f b := by rw [hfg, ha, hb]
      exact h4 (hf this)
  ·
    exfalso
    rcases hfb with hb | hb | hb | hb
    ·
      have hff4 : f^[4] a = a := by
        show f (f (f (f a))) = a
        rw [ha, hfg, hb, hfg, ha, hg]
        exact hb
      exact h3 ((per4 hff4).symm.trans ha)
    · have hff : f (f a) = a := by
        rw [ha, hfg, hb, hg]
      exact h3 ((per2 hff).symm.trans ha)
    · have : f (g a) = f b := by rw [hfg, ha, hg, hb]
      exact h4 (hf this)
    · exact h2 (hf (ha.trans hb.symm))

theorem exists_twin_frame (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) :
    ∃ K₃ : Subgroup G, K₃ ∈ twinSet Ω K ∧ K₃ ≠ K ∧ K₃ ≠ conjSub s K ∧ conjSub s K₃ ≠ K₃ ∧
      conjSub s K₃ ≠ K ∧ conjSub s K₃ ≠ conjSub s K ∧
      twinSet Ω K = {K, conjSub s K, K₃, conjSub s K₃} := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  obtain ⟨τ, hτfix, -, hact⟩ := H.exists_twin_involution hK
  have hsτ : ∀ L : ↥(twinSet Ω K),
      conjSub s (L : Subgroup G) = ((τ L : ↥(twinSet Ω K)) : Subgroup G) := by
    rcases hact s hs with h | h
    · exact absurd (h ⟨K, hKT⟩) hsK
    · exact h
  have hK'T : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hcard2 : ({K, conjSub s K} : Set (Subgroup G)).ncard = 2 :=
    Set.ncard_pair (Ne.symm hsK)
  obtain ⟨K₃, hK₃V, hK₃nt⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := ({K, conjSub s K} : Set (Subgroup G)))
      (t := twinSet Ω K) (by rw [hcard2, H.ncard_twinSet hK]; norm_num) (Set.toFinite _)
  have hK₃K : K₃ ≠ K := fun e => hK₃nt (by rw [e]; exact Set.mem_insert _ _)
  have hK₃K' : K₃ ≠ conjSub s K := fun e =>
    hK₃nt (by rw [e]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h1 : conjSub s K₃ = ((τ ⟨K₃, hK₃V⟩ : ↥(twinSet Ω K)) : Subgroup G) := hsτ ⟨K₃, hK₃V⟩
  have hK₃s : conjSub s K₃ ∈ twinSet Ω K := by
    rw [h1]
    exact (τ ⟨K₃, hK₃V⟩).2
  have hK₃fix : conjSub s K₃ ≠ K₃ := by
    intro e
    have h2 : τ ⟨K₃, hK₃V⟩ = ⟨K₃, hK₃V⟩ := Subtype.ext (h1.symm.trans e)
    exact hτfix _ h2
  have hK₃sK : conjSub s K₃ ≠ K := fun e =>
    hK₃K' ((e18d_conj_conj H hs K₃).symm.trans (congrArg (conjSub s) e))
  have hK₃sK' : conjSub s K₃ ≠ conjSub s K := fun e => hK₃K (conjSub_injective s e)
  have hne4 : K ≠ conjSub s K := Ne.symm hsK
  have hncard4 : ({K, conjSub s K, K₃, conjSub s K₃} : Set (Subgroup G)).ncard = 4 :=
    e18d_ncard_four_of_distinct hne4 hK₃K.symm hK₃sK.symm hK₃K'.symm hK₃sK'.symm
      (fun e => hK₃fix e.symm)
  have hsub : ({K, conjSub s K, K₃, conjSub s K₃} : Set (Subgroup G)) ⊆ twinSet Ω K := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> assumption
  have hV : twinSet Ω K = {K, conjSub s K, K₃, conjSub s K₃} :=
    (Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [H.ncard_twinSet hK, hncard4]))
      (Set.finite_of_ncard_ne_zero (by rw [H.ncard_twinSet hK]; norm_num))).symm
  exact ⟨K₃, hK₃V, hK₃K, hK₃K', hK₃fix, hK₃sK, hK₃sK', hV⟩

theorem sup_twin_inf_sup_twin (H : Hyp Ω) {K K₁ K₂ K₃ : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (h₁ : K₁ ∈ twinSet Ω K) (h₂ : K₂ ∈ twinSet Ω K)
    (h₃ : K₃ ∈ twinSet Ω K) (h4 : ({K, K₁, K₂, K₃} : Set (Subgroup G)).ncard = 4) :
    (K ⊔ K₁) ⊓ (K₂ ⊔ K₃) = Subgroup.zpowers z := by
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  obtain ⟨hKK₁, hKK₂, hKK₃, hK₁K₂, hK₁K₃, hK₂K₃⟩ := e18d_ncard_four_distinct h4
  have hA : Nat.card ↥(K ⊔ K₁) = 32 := (H.sup_twin hz hKT h₁ hKK₁).2.2
  have hB : Nat.card ↥(K₂ ⊔ K₃) = 32 := (H.sup_twin hz h₂ h₃ hK₂K₃).2.2
  have c1 : Commutes K (K₂ ⊔ K₃) :=
    e18d_commutes_sup_right (H.sup_twin hz hKT h₂ hKK₂).1 (H.sup_twin hz hKT h₃ hKK₃).1
  have c2 : Commutes K₁ (K₂ ⊔ K₃) :=
    e18d_commutes_sup_right (H.sup_twin hz h₁ h₂ hK₁K₂).1 (H.sup_twin hz h₁ h₃ hK₁K₃).1
  have hcAB : Commutes (K ⊔ K₁) (K₂ ⊔ K₃) :=
    (e18d_commutes_sup_right (A := K₂ ⊔ K₃) (B := K) (C := K₁) c1.symm c2.symm).symm
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (e18d_le_normalizer hcAB.symm)
  have hV : twinSet Ω K = {K, K₁, K₂, K₃} := by
    have hsub : ({K, K₁, K₂, K₃} : Set (Subgroup G)) ⊆ twinSet Ω K := by
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> assumption
    exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [H.ncard_twinSet hK, h4]))
      (Set.finite_of_ncard_ne_zero (by rw [H.ncard_twinSet hK]; norm_num))).symm
  have hspan : pSpan (twinSet Ω K) = (K ⊔ K₁) ⊔ (K₂ ⊔ K₃) := by
    rw [hV]
    simp only [pSpan, iSup_insert, iSup_singleton, sup_assoc]
  have hcard9 : Nat.card ↥((K ⊔ K₁) ⊔ (K₂ ⊔ K₃)) = 2 ^ 9 := by
    rw [← hspan]
    exact (H.card_span_twinSet hK hz).1
  have hinter : Nat.card ↥((K ⊔ K₁) ⊓ (K₂ ⊔ K₃)) = 2 := by
    rw [hcard9, hA, hB] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 9) (by rw [hprod]; norm_num)
  have hzK₂ : z ∈ K₂ := by
    obtain ⟨-, z₂, hz₂K, hz₂⟩ := h₂
    rw [hz.eq hz₂K]
    exact hz₂.mem
  have hle : Subgroup.zpowers z ≤ (K ⊔ K₁) ⊓ (K₂ ⊔ K₃) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨(le_sup_left : K ≤ K ⊔ K₁) hz.mem, (le_sup_left : K₂ ≤ K₂ ⊔ K₃) hzK₂⟩
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hinter, hzcard]))).symm

private theorem e18d_absurd_of_le (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) {K₃ : Subgroup G}
    (hV : twinSet Ω K = {K, conjSub s K, K₃, conjSub s K₃})
    (hle : zGroup Ω ⊓ (K ⊔ conjSub s K) ≤ K₃ ⊔ conjSub s K₃) : False := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hK'T : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hK₃T : K₃ ∈ twinSet Ω K := by
    rw [hV]
    simp
  have hK₃'T : conjSub s K₃ ∈ twinSet Ω K := by
    rw [hV]
    simp
  have hncard4 : ({K, conjSub s K, K₃, conjSub s K₃} : Set (Subgroup G)).ncard = 4 := by
    rw [← hV, H.ncard_twinSet hK]
  have hint := H.sup_twin_inf_sup_twin hK hz hK'T hK₃T hK₃'T hncard4
  have h8 := H.card_dZero hK hs hsK
  have hsub : zGroup Ω ⊓ (K ⊔ conjSub s K) ≤ Subgroup.zpowers z := by
    rw [← hint]
    exact le_inf inf_le_right hle
  have hle' := Subgroup.card_le_of_le hsub
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one]
  omega

theorem inf_centralizer_zGroup (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    K ⊓ Subgroup.centralizer (zGroup Ω : Set G) = Subgroup.zpowers z := by
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := e18d_mem_zGroup hJ hs
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hK' : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hsD
  have hc : Commutes K (conjSub s K) := (H.sup_twin hz hKT hK' hsK.symm).1
  apply le_antisymm
  · intro k hk
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    have hcK : ∀ k₁ ∈ K, k * k₁ = k₁ * k := by
      intro k₁ hk₁
      have hb := e18d_comm_mem H (k₁ := k₁) hsD
      have hbk : (s * k₁ * s⁻¹ * k₁⁻¹) * k = k * (s * k₁ * s⁻¹ * k₁⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hkC _ hb
      have h2 : (s * k₁ * s⁻¹ * k₁⁻¹) * k * (s * k₁ * s⁻¹ * k₁⁻¹)⁻¹ = k := by
        rw [hbk]
        group
      have h3 : k₁⁻¹ * k * k₁ = k := (e18d_swap_conj hc hk₁ k hkK).symm.trans h2
      calc k * k₁ = k₁ * (k₁⁻¹ * k * k₁) := by group
        _ = k₁ * k := by rw [h3]
    exact e18d_center_le H hK hz hkK hcK
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hz.mem, Subgroup.mem_centralizer_iff.mpr fun d hd =>
      H.endHyp.zGroup_comm H.perp9 d hd z (e18d_mem_zGroup hK hz)⟩

private theorem e18d_normalizes (H : Hyp Ω) {M : Subgroup G} (hM : M ∈ Ω) {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) (hodd : Odd (orderOf r)) :
    r ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hM
  have hMT : M ∈ twinSet Ω M := ⟨hM, z, hz, hz⟩
  obtain ⟨J, hJ, s, hs, hsM⟩ := H.exists_swap hM
  have hsD : s ∈ zGroup Ω := e18d_mem_zGroup hJ hs
  obtain ⟨K₃, hK₃T, hK₃M, hK₃sM, -, hsK₃M, -, hV⟩ := H.exists_twin_frame hM hsD hsM
  have hfa : conjSub r M ∈ twinSet Ω M := e18d_conj_mem_twinSet H hr hMT
  have hfb : conjSub r K₃ ∈ twinSet Ω M := e18d_conj_mem_twinSet H hr hK₃T
  rw [hV] at hfa hfb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfa hfb
  have hrs : r * s = s * r := (Subgroup.mem_centralizer_iff.mp hr s hsD).symm
  have hfix : conjSub r M = M :=
    e18d_fix_four hodd (conjSub_injective r) (e18d_conj_conj H hsD)
      (fun x => by rw [← conjSub_mul, ← conjSub_mul, hrs])
      (by rw [e18d_iter_conjSub, pow_orderOf_eq_one, conjSub_one])
      hsM.symm hK₃M.symm hsK₃M.symm hK₃sM.symm hfa hfb
  exact mem_normalizer_iff_conjSub_eq.mpr hfix

private theorem e18d_centralizes (H : Hyp Ω) {M : Subgroup G} (hM : M ∈ Ω) {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) (hodd : Odd (orderOf r))
    (hN : r ∈ Subgroup.normalizer (M : Set G)) : r ∈ Subgroup.centralizer (M : Set G) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hM
  have hzD : z ∈ zGroup Ω := e18d_mem_zGroup hM hz
  have hNz := e18d_zGroup_normal H
  have hrz : r * z = z * r := (Subgroup.mem_centralizer_iff.mp hr z hzD).symm
  have hrzp : ∀ c ∈ Subgroup.zpowers z, Commute r c := by
    intro c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (show Commute r z from hrz).zpow_right n
  have hsq : ∀ c ∈ Subgroup.zpowers z, c * c = 1 := by
    intro c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← zpow_add, show n + n = 2 * n by ring, zpow_mul, zpow_two, hz.sq, one_zpow]
  have hcomm : ∀ k ∈ M, k * r * k⁻¹ * r⁻¹ ∈ Subgroup.zpowers z := by
    intro k hk
    have hcM : k * r * k⁻¹ * r⁻¹ ∈ M := by
      have h1 : r * k⁻¹ * r⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp hN k⁻¹).mp (M.inv_mem hk)
      have e : k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) := by group
      rw [e]
      exact M.mul_mem hk h1
    have hcC : k * r * k⁻¹ * r⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hdr : d * r = r * d := Subgroup.mem_centralizer_iff.mp hr d hd
      have he : k⁻¹ * d * k ∈ zGroup Ω := by
        have h1 := hNz.conj_mem d hd k⁻¹
        rwa [inv_inv] at h1
      have hre : (k⁻¹ * d * k) * r = r * (k⁻¹ * d * k) :=
        Subgroup.mem_centralizer_iff.mp hr _ he
      have hdk : d * k = k * (k⁻¹ * d * k) := by group
      have hu : d * (k * r * k⁻¹) = (k * r * k⁻¹) * d := by
        calc d * (k * r * k⁻¹) = (d * k) * r * (d * k)⁻¹ * d := by group
          _ = (k * (k⁻¹ * d * k)) * r * (k * (k⁻¹ * d * k))⁻¹ * d := by rw [hdk]
          _ = k * ((k⁻¹ * d * k) * r * (k⁻¹ * d * k)⁻¹) * k⁻¹ * d := by group
          _ = k * r * k⁻¹ * d := by rw [hre]; group
      have hdr' : d * r⁻¹ = r⁻¹ * d := (show Commute d r from hdr).inv_right.eq
      calc d * (k * r * k⁻¹ * r⁻¹) = (d * (k * r * k⁻¹)) * r⁻¹ := by group
        _ = ((k * r * k⁻¹) * d) * r⁻¹ := by rw [hu]
        _ = (k * r * k⁻¹) * (d * r⁻¹) := by group
        _ = (k * r * k⁻¹) * (r⁻¹ * d) := by rw [hdr']
        _ = (k * r * k⁻¹ * r⁻¹) * d := by group
    have hint : k * r * k⁻¹ * r⁻¹ ∈ M ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcM, hcC⟩
    rw [H.inf_centralizer_zGroup hM hz] at hint
    exact hint
  have hr2 : ∀ k ∈ M, Commute (r * r) k := by
    intro k hk
    obtain ⟨c, hc_def⟩ : ∃ c, c = k * r * k⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have hcz : c ∈ Subgroup.zpowers z := by
      rw [hc_def]
      exact hcomm k hk
    have hcr : Commute r c := hrzp c hcz
    have hcc : c * c = 1 := hsq c hcz
    have hcc' : c⁻¹ * c⁻¹ = 1 := by rw [← mul_inv_rev, hcc, inv_one]
    have hk' : r * k * r⁻¹ = c⁻¹ * k := by
      rw [hc_def]
      group
    have hcinv : r * c⁻¹ * r⁻¹ = c⁻¹ := by
      rw [(hcr.inv_right).eq, mul_inv_cancel_right]
    have key : (r * r) * k * (r * r)⁻¹ = k := by
      calc (r * r) * k * (r * r)⁻¹ = r * (r * k * r⁻¹) * r⁻¹ := by group
        _ = r * (c⁻¹ * k) * r⁻¹ := by rw [hk']
        _ = (r * c⁻¹ * r⁻¹) * (r * k * r⁻¹) := by group
        _ = c⁻¹ * (c⁻¹ * k) := by rw [hcinv, hk']
        _ = (c⁻¹ * c⁻¹) * k := by group
        _ = k := by rw [hcc', one_mul]
    calc (r * r) * k = ((r * r) * k * (r * r)⁻¹) * (r * r) := by group
      _ = k * (r * r) := by rw [key]
  obtain ⟨t, ht⟩ := hodd
  have hpow : (r * r) ^ (t + 1) = r := by
    have h1 : (r * r) ^ (t + 1) = r ^ (orderOf r + 1) := by
      rw [← sq, ← pow_mul, ht]
      congr 1
    rw [h1, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hc : Commute ((r * r) ^ (t + 1)) k := (hr2 k hk).pow_left (t + 1)
  rw [hpow] at hc
  exact hc.eq.symm

theorem eq_one_of_odd_mem_centralizer_zGroup (H : Hyp Ω) {r : G}
    (hr : r ∈ Subgroup.centralizer (zGroup Ω : Set G)) (hodd : Odd (orderOf r)) : r = 1 := by
  have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [← H.endHyp.thmD.gen]
    refine pSpan_le fun M hM => ?_
    intro x hx
    have hC := e18d_centralizes H hM hr hodd (e18d_normalizes H hM hr hodd)
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.mp hC x hx).symm
  have hcenter : r ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_top g)) r
      (Set.mem_singleton r)).symm
  rw [H.endHyp.center] at hcenter
  exact Subgroup.mem_bot.mp hcenter

theorem centralizer_zGroup_eq_pCore (H : Hyp Ω) :
    Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G := by
  have hD := e18d_zGroup_normal H
  apply le_antisymm
  · haveI := hD
    have hpg : IsPGroup 2 ↥(Subgroup.centralizer (zGroup Ω : Set G)) := by
      intro g
      obtain ⟨k, hk⟩ := e18d_exists_two_pow g.2
        (fun y hy hodd => eq_one_of_odd_mem_centralizer_zGroup H hy hodd)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact (le_sSup ⟨inferInstance, hpg⟩ : Subgroup.centralizer (zGroup Ω : Set G) ≤ pCore 2 G)
  · exact H.endHyp.pCore_le_centralizer_zGroup H.perp9

private theorem e18d_le_of_conj {q : G} (hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G))
    {S T : Subgroup G} (hST : conjSub q S = T) : zGroup Ω ⊓ S ≤ T := by
  intro x hx
  obtain ⟨hxD, hxS⟩ := Subgroup.mem_inf.mp hx
  have hxq : q * x * q⁻¹ = x := by
    rw [← Subgroup.mem_centralizer_iff.mp hqC x hxD, mul_inv_cancel_right]
  have hmem := conj_mem_conjSub (n := q) hxS
  rwa [hxq, hST] at hmem

theorem inf_pCore_sup_twin (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) :
    (K ⊔ conjSub s K) ⊓ pCore 2 G = zGroup Ω ⊓ (K ⊔ conjSub s K) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hK' : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hc : Commutes K (conjSub s K) := (H.sup_twin hz hKT hK' hsK.symm).1
  have hzK' : IsUniqueInvolution (conjSub s K) z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'
    rw [hz.eq hz'K]
    exact hz'K'
  have hK'Ω : conjSub s K ∈ Ω := hK'.1
  have hinfK' : conjSub s K ⊓ pCore 2 G = Subgroup.zpowers z := H.inf_pCore hK'Ω hzK'
  have hD0 : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) = 8 := H.card_dZero hK hs hsK
  have hdle : zGroup Ω ⊓ (K ⊔ conjSub s K) ≤ (K ⊔ conjSub s K) ⊓ pCore 2 G :=
    le_inf inf_le_right (inf_le_left.trans H.endHyp.zGroup_le_pCore)
  have hSN : K ⊔ conjSub s K ≤ Subgroup.normalizer ((conjSub s K : Subgroup G) : Set G) :=
    sup_le (e18d_le_normalizer hc.symm) Subgroup.le_normalizer
  have hNK : (K ⊔ conjSub s K) ⊓ pCore 2 G ≤
      Subgroup.normalizer ((conjSub s K : Subgroup G) : Set G) :=
    inf_le_left.trans hSN
  have h1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hNK
  have h32 : Nat.card ↥(((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊔ conjSub s K) ≤ 32 := by
    have := Subgroup.card_le_of_le (sup_le inf_le_left le_sup_right :
      ((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊔ conjSub s K ≤ K ⊔ conjSub s K)
    rwa [(H.sup_twin hz hKT hK' hsK.symm).2.2] at this
  have h2 : Nat.card ↥(((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊓ conjSub s K) ≤ 2 := by
    have hle : ((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊓ conjSub s K ≤ Subgroup.zpowers z := by
      rw [← hinfK']
      exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one] at this
  have hK'8 : Nat.card ↥(conjSub s K) = 8 := H.endHyp.card_eq_eight hK'Ω
  have hle8 : Nat.card ↥((K ⊔ conjSub s K) ⊓ pCore 2 G) ≤ 8 := by
    have hm : Nat.card ↥((K ⊔ conjSub s K) ⊓ pCore 2 G) * 8 ≤ 64 := by
      calc Nat.card ↥((K ⊔ conjSub s K) ⊓ pCore 2 G) * 8
          = Nat.card ↥((K ⊔ conjSub s K) ⊓ pCore 2 G) * Nat.card ↥(conjSub s K) := by
            rw [hK'8]
        _ = Nat.card ↥(((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊔ conjSub s K) *
            Nat.card ↥(((K ⊔ conjSub s K) ⊓ pCore 2 G) ⊓ conjSub s K) := h1.symm
        _ ≤ 32 * 2 := Nat.mul_le_mul h32 h2
        _ = 64 := by norm_num
    omega
  have hcard : Nat.card ↥((K ⊔ conjSub s K) ⊓ pCore 2 G) ≤
      Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) := by
    rw [hD0]
    exact hle8
  exact (Subgroup.eq_of_le_of_card_ge hdle hcard).symm

theorem conjSub_pCore_mem_orbit (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G}
    (hs : s ∈ zGroup Ω) (hsK : conjSub s K ≠ K) {q : G} (hq : q ∈ pCore 2 G) :
    conjSub q K = K ∨ conjSub q K = conjSub s K := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    rw [H.centralizer_zGroup_eq_pCore]
    exact hq
  obtain ⟨K₃, -, -, -, -, -, -, hV⟩ := H.exists_twin_frame hK hs hsK
  have hqK : conjSub q K ∈ twinSet Ω K := e18d_conj_mem_twinSet H hqC hKT
  rw [hV] at hqK
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hqK
  have hqs : q * s = s * q := (Subgroup.mem_centralizer_iff.mp hqC s hs).symm
  have hqK's : conjSub q (conjSub s K) = conjSub s (conjSub q K) := by
    rw [← conjSub_mul, ← conjSub_mul, hqs]
  rcases hqK with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  ·
    exfalso
    have hA : conjSub q (K ⊔ conjSub s K) = K₃ ⊔ conjSub s K₃ := by
      rw [e18d_conjSub_sup, h, hqK's, h]
    exact e18d_absurd_of_le H hK hs hsK hV (e18d_le_of_conj hqC hA)
  ·
    exfalso
    have hA : conjSub q (K ⊔ conjSub s K) = K₃ ⊔ conjSub s K₃ := by
      rw [e18d_conjSub_sup, h, hqK's, h, e18d_conj_conj H hs K₃, sup_comm]
    exact e18d_absurd_of_le H hK hs hsK hV (e18d_le_of_conj hqC hA)

theorem commutator_pCore_mem_zGroup (H : Hyp Ω) {K : Subgroup G} (hK : K ∈ Ω) {q k : G}
    (hq : q ∈ pCore 2 G) (hk : k ∈ K) : k * q * k⁻¹ * q⁻¹ ∈ zGroup Ω := by
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := e18d_mem_zGroup hJ hs
  have horb := H.conjSub_pCore_mem_orbit hK hsD hsK hq
  have hKS : K ≤ K ⊔ conjSub s K := le_sup_left
  have hqK : conjSub q K ≤ K ⊔ conjSub s K := by
    rcases horb with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  have hmemS : k * q * k⁻¹ * q⁻¹ ∈ K ⊔ conjSub s K := by
    have h1 : q * k⁻¹ * q⁻¹ ∈ K ⊔ conjSub s K := hqK (conj_mem_conjSub (K.inv_mem hk))
    have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
    rw [e]
    exact (K ⊔ conjSub s K).mul_mem (hKS hk) h1
  have hmemQ : k * q * k⁻¹ * q⁻¹ ∈ pCore 2 G := by
    haveI : (pCore 2 G).Normal := CFSG.pCore_normal
    exact (pCore 2 G).mul_mem ((show (pCore 2 G).Normal from CFSG.pCore_normal).conj_mem q hq k)
      ((pCore 2 G).inv_mem hq)
  have hmem : k * q * k⁻¹ * q⁻¹ ∈ (K ⊔ conjSub s K) ⊓ pCore 2 G :=
    Subgroup.mem_inf.mpr ⟨hmemS, hmemQ⟩
  rw [H.inf_pCore_sup_twin hK hsD hsK] at hmem
  exact (Subgroup.mem_inf.mp hmem).1

theorem commutator_pCore_mem_zGroup_all (H : Hyp Ω) (g : G) {q : G} (hq : q ∈ pCore 2 G) :
    g * q * g⁻¹ * q⁻¹ ∈ zGroup Ω := by
  have hN := e18d_zGroup_normal H
  let T : Subgroup G :=
    { carrier := {x | x * q * x⁻¹ * q⁻¹ ∈ zGroup Ω}
      one_mem' := by
        show (1 : G) * q * (1 : G)⁻¹ * q⁻¹ ∈ zGroup Ω
        simpa using (zGroup Ω).one_mem
      mul_mem' := by
        intro a b ha hb
        show a * b * q * (a * b)⁻¹ * q⁻¹ ∈ zGroup Ω
        have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
            (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
        rw [e]
        exact (zGroup Ω).mul_mem (hN.conj_mem _ hb a) ha
      inv_mem' := by
        intro a ha
        show a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ ∈ zGroup Ω
        have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hN.conj_mem _ ((zGroup Ω).inv_mem ha) a⁻¹ }
  have hT : pSpan Ω ≤ T := by
    refine pSpan_le fun M hM => ?_
    intro k hk
    exact H.commutator_pCore_mem_zGroup hM hq hk
  rw [H.endHyp.thmD.gen] at hT
  exact hT (Subgroup.mem_top g)

end Hyp

end End18

end CFSG.ClassicalInvolution.Q3.Sec13
