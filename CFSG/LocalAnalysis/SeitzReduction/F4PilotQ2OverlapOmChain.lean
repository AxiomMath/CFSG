module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup

section Chain

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def omIsoGroup (Q : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := omIsoSet Q
  one_mem' := by intro v; simp
  mul_mem' := by
    intro a b ha hb v
    rw [Units.val_mul, ← mulVec_mulVec, ha, hb]
  inv_mem' := by
    intro a ha v
    rw [← ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v), mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mulVec]

theorem closure_omIsoSet (Q : (ι → K) → K) : closure (omIsoSet Q) = omIsoGroup Q :=
  closure_eq (omIsoGroup Q)

@[expose] def omFixSub (T : Finset ι) : Subgroup (GL ι K) where
  carrier := {g | ∀ m ∈ T, (g : Matrix ι ι K) *ᵥ Pi.single m 1 = Pi.single m 1}
  one_mem' := by
    intro m _
    rw [Units.val_one, one_mulVec]
  mul_mem' := by
    intro a b ha hb m hm
    rw [Units.val_mul, ← mulVec_mulVec, hb m hm, ha m hm]
  inv_mem' := by
    intro a ha m hm
    conv_lhs => rw [← ha m hm]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

@[expose] def omChain (Q : (ι → K) → K) (h : GL ι K) (T : Finset ι) : Subgroup (GL ι K) :=
  omIsoGroup Q ⊓ centralizer ({h} : Set (GL ι K)) ⊓ omFixSub T

theorem omChain_empty (Q : (ι → K) → K) (h : GL ι K) :
    omChain Q h ∅ = omIsoGroup Q ⊓ centralizer ({h} : Set (GL ι K)) := by
  rw [omChain, inf_eq_left]
  intro g _ m hm
  exact absurd hm (Finset.notMem_empty m)

theorem omChain_univ (Q : (ι → K) → K) (h : GL ι K) : omChain Q h Finset.univ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply Units.ext
  ext i j
  have := congrFun (hg.2 j (Finset.mem_univ j)) i
  rw [mulVec_single_one] at this
  rw [Units.val_one, Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using this

theorem card_omChain_step (Q : (ι → K) → K) (h : GL ι K) (T : Finset ι) (m : ι)
    (S : Finset (ι → K))
    (hup : ∀ g ∈ omChain Q h T, (g : Matrix ι ι K) *ᵥ Pi.single m 1 ∈ S)
    (hlow : ∀ s ∈ S, ∃ g ∈ omChain Q h T, (g : Matrix ι ι K) *ᵥ Pi.single m 1 = s) :
    Nat.card (omChain Q h T) = S.card * Nat.card (omChain Q h (insert m T)) := by
  set H := omChain Q h T with hHdef
  have horb : MulAction.orbit (↥H) (Pi.single m (1 : K) : ι → K) = (S : Set (ι → K)) := by
    ext s
    constructor
    · rintro ⟨g, rfl⟩
      exact hup g g.2
    · intro hs
      obtain ⟨g, hg, hgs⟩ := hlow s hs
      exact ⟨⟨g, hg⟩, hgs⟩
  have hstab : (MulAction.stabilizer (↥H) (Pi.single m (1 : K) : ι → K)).map H.subtype =
      omChain Q h (insert m T) := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      have hfix : ((g' : GL ι K) : Matrix ι ι K) *ᵥ Pi.single m 1 = Pi.single m 1 := hg'
      obtain ⟨⟨hgi, hgc⟩, hgT⟩ := g'.2
      refine ⟨⟨hgi, hgc⟩, ?_⟩
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hfix
      · exact hgT t ht
    · intro hg
      obtain ⟨⟨hgi, hgc⟩, hgT⟩ := hg
      refine ⟨⟨g, ⟨⟨hgi, hgc⟩, fun t ht => hgT t (Finset.mem_insert_of_mem ht)⟩⟩, ?_, rfl⟩
      exact hgT m (Finset.mem_insert_self m T)
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (↥H) (Pi.single m (1 : K) : ι → K))
  rw [MulAction.index_stabilizer, horb, Set.ncard_coe_finset] at h1
  rw [← h1, ← hstab, Subgroup.card_map_of_injective H.subtype_injective, mul_comm]

@[expose] def omPred (Q : (ι → K) → K) (hM : Matrix ι ι K) (T : Finset ι) (m : ι)
    (w : ι → K) : Prop :=
  Q w = Q (Pi.single m 1) ∧
    (∀ i ∈ T, Q (w + Pi.single i 1) = Q (Pi.single m 1 + Pi.single i 1)) ∧
    hM *ᵥ w = w + (hM *ᵥ Pi.single m 1 - Pi.single m 1) ∧
    (∃ i ∉ T, w i ≠ 0) ∧
    ((∃ y, hM *ᵥ y = y + Pi.single m 1) → ∃ y, hM *ᵥ y = y + w)

instance omPred.instDecidablePred [Fintype K] [DecidableEq K] (Q : (ι → K) → K)
    (hM : Matrix ι ι K) (T : Finset ι) (m : ι) : DecidablePred (omPred Q hM T m) := fun w =>
  inferInstanceAs (Decidable (Q w = Q (Pi.single m 1) ∧
    (∀ i ∈ T, Q (w + Pi.single i 1) = Q (Pi.single m 1 + Pi.single i 1)) ∧
    hM *ᵥ w = w + (hM *ᵥ Pi.single m 1 - Pi.single m 1) ∧
    (∃ i ∉ T, w i ≠ 0) ∧
    ((∃ y, hM *ᵥ y = y + Pi.single m 1) → ∃ y, hM *ᵥ y = y + w)))

omit [DecidableEq ι] in
theorem mulVec_eq_self_of_supp {g : Matrix ι ι K} [DecidableEq ι] {T : Finset ι}
    (hg : ∀ t ∈ T, g *ᵥ Pi.single t 1 = Pi.single t 1) {c : ι → K} (hc : ∀ i ∉ T, c i = 0) :
    g *ᵥ c = c := by
  have hc' : c = ∑ t ∈ T, c t • Pi.single t (1 : K) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq]
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [hi, hc i hi]
  rw [hc', mulVec_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mulVec_smul, hg t ht]

theorem omPred_of_mem {Q : (ι → K) → K} {h : GL ι K} {T : Finset ι} {m : ι} (hm : m ∉ T)
    (hc : ∀ i ∉ T, (((h : Matrix ι ι K) *ᵥ Pi.single m 1 - Pi.single m 1 : ι → K) i) = 0)
    {g : GL ι K} (hg : g ∈ omChain Q h T) :
    omPred Q (h : Matrix ι ι K) T m ((g : Matrix ι ι K) *ᵥ Pi.single m 1) := by
  obtain ⟨⟨hgi, hgc⟩, hgT⟩ := hg
  have hgc' : (g : Matrix ι ι K) * h = h * g := congrArg Units.val
    (mem_centralizer_singleton_iff.1 hgc)
  refine ⟨hgi _, fun i hi => ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← hgT i hi]
    rw [← mulVec_add, hgi]
  · rw [mulVec_mulVec, ← hgc', ← mulVec_mulVec, ← mulVec_eq_self_of_supp hgT hc, ← mulVec_add,
      add_sub_cancel]
  · by_contra hall
    push Not at hall
    have h1 : (g : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ Pi.single m 1) =
        (g : Matrix ι ι K) *ᵥ Pi.single m 1 := mulVec_eq_self_of_supp hgT hall
    have h2 : (g : Matrix ι ι K) *ᵥ Pi.single m 1 = Pi.single m 1 := by
      have := congrArg (fun v => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) h1
      simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left, inv_mul_cancel,
        Units.val_one, one_mulVec] at this
      exact this
    have := hall m hm
    rw [h2, Pi.single_eq_same] at this
    exact one_ne_zero this
  · rintro ⟨y, hy⟩
    refine ⟨(g : Matrix ι ι K) *ᵥ y, ?_⟩
    rw [mulVec_mulVec, ← hgc', ← mulVec_mulVec, hy, mulVec_add]

theorem omChain_low {Q : (ι → K) → K} {h : GL ι K} {T : Finset ι} {m : ι} {P : (ι → K) → Prop}
    {n : ℕ} (W Wi : Fin n → Matrix ι ι K) (hW : ∀ k, W k * Wi k = 1)
    (hiso : ∀ k v, Q (W k *ᵥ v) = Q v) (hcomm : ∀ k, W k * h = h * W k)
    (hfix : ∀ k, ∀ t ∈ T, W k *ᵥ Pi.single t 1 = Pi.single t 1)
    (hcov : ∀ s, P s → ∃ k, W k *ᵥ Pi.single m 1 = s) (s : ι → K) (hs : P s) :
    ∃ g ∈ omChain Q h T, (g : Matrix ι ι K) *ᵥ Pi.single m 1 = s := by
  obtain ⟨k, hk⟩ := hcov s hs
  refine ⟨⟨W k, Wi k, hW k, mul_eq_one_comm.1 (hW k)⟩, ⟨⟨hiso k, ?_⟩, hfix k⟩, hk⟩
  exact mem_centralizer_singleton_iff.2 (Units.ext (hcomm k))

theorem card_omChain_level [Fintype K] [DecidableEq K] {Q : (ι → K) → K} {h : GL ι K}
    {T : Finset ι} {m : ι} (n : ℕ) (W Wi : Fin n → Matrix ι ι K) (hm : m ∉ T)
    (hc : ∀ i ∉ T, (((h : Matrix ι ι K) *ᵥ Pi.single m 1 - Pi.single m 1 : ι → K) i) = 0)
    (hcard : (Finset.univ.filter (omPred Q (h : Matrix ι ι K) T m)).card = n)
    (hW : ∀ k, W k * Wi k = 1) (hiso : ∀ k v, Q (W k *ᵥ v) = Q v)
    (hcomm : ∀ k, W k * (h : Matrix ι ι K) = (h : Matrix ι ι K) * W k)
    (hfix : ∀ k, ∀ t ∈ T, W k *ᵥ Pi.single t 1 = Pi.single t 1)
    (hcov : ∀ s, omPred Q (h : Matrix ι ι K) T m s → ∃ k, W k *ᵥ Pi.single m 1 = s) :
    Nat.card (omChain Q h T) = n * Nat.card (omChain Q h (insert m T)) := by
  rw [← hcard]
  refine card_omChain_step Q h T m _ (fun g hg => ?_) (fun s hs => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, omPred_of_mem hm hc hg⟩
  · exact omChain_low W Wi hW hiso hcomm hfix hcov s (Finset.mem_filter.1 hs).2

@[expose] def omOfCode {ι : Type} {d : ℕ} (enc : ι → Fin d) (c : ℕ) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun i j => if c.testBit (d * (enc i : ℕ) + enc j) then 1 else 0

end Chain

section Two

theorem card_inf_mul_two {Γ : Type*} [Group Γ] [Finite Γ] {G₀ N H : Subgroup Γ}
    (hHG : H ≤ G₀) (hN : (N.subgroupOf G₀).index = 2) {r : Γ} (hr : r ∈ H) (hrN : r ∉ N) :
    Nat.card (H ⊓ N : Subgroup Γ) * 2 = Nat.card H := by
  set N' := N.subgroupOf G₀
  set H' := H.subgroupOf G₀
  have : N'.Normal := Subgroup.normal_of_index_eq_two hN
  have hdvd : N'.relIndex H' ∣ 2 := hN ▸ Subgroup.relIndex_dvd_index_of_normal N' H'
  have hne : N'.relIndex H' ≠ 1 := by
    intro h1
    have hle := Subgroup.relIndex_eq_one.1 h1
    have : (⟨r, hHG hr⟩ : G₀) ∈ N' := hle (Subgroup.mem_subgroupOf.2 hr)
    exact hrN (Subgroup.mem_subgroupOf.1 this)
  have h2 : N'.relIndex H' = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have key := Subgroup.relIndex_mul_card (H := N') (K := H')
  rw [h2] at key
  have e1 : Nat.card H' = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG).toEquiv
  have e2 : N' ⊓ H' = (H ⊓ N).subgroupOf G₀ := by
    ext x
    simp only [N', H', Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    exact and_comm
  have e3 : Nat.card ((H ⊓ N).subgroupOf G₀) = Nat.card (H ⊓ N : Subgroup Γ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hHG)).toEquiv
  rw [e2, e3, e1] at key
  rw [← key, mul_comm]

end Two

end CFSG.SeitzReduction.F4Pilot
