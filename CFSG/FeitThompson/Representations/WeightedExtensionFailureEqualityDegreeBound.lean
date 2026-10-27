module

public import CFSG.FeitThompson.Representations.WeightedFeitInequalityConjugatePairExtension
import CFSG.FeitThompson.Representations.EqualDegreeSubcoherenceExtendsToFamily
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder
open WeightedFeitExtension

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem IsSubcoherent.subfamily (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : T ⊆ S) (hTstar : ∀ γ ∈ T, star γ ∈ T) : IsSubcoherent T tau R := by
  have hspan : intSpanZeroAtOne (T : Set (L → ℂ)) ≤ intSpanZeroAtOne (S : Set (L → ℂ)) := by
    intro f hf
    exact mem_intSpanZeroAtOne.2 ⟨Submodule.span_mono (by exact_mod_cast hTS)
      (mem_intSpanZeroAtOne.1 hf).1, (mem_intSpanZeroAtOne.1 hf).2⟩
  exact
  { isCharacter := fun χ hχ => hc.isCharacter χ (hTS hχ)
    ne_zero := fun χ hχ => hc.ne_zero χ (hTS hχ)
    star_mem := hTstar
    star_ne := fun χ hχ => hc.star_ne χ (hTS hχ)
    charInner_eq_zero := fun χ hχ ψ hψ h => hc.charInner_eq_zero χ (hTS hχ) ψ (hTS hψ) h
    map_add := fun f hf h hh => hc.map_add f (hspan hf) h (hspan hh)
    tau_mem := fun f hf => hc.tau_mem f (hspan hf)
    charInner_tau_tau := fun f hf h hh => hc.charInner_tau_tau f (hspan hf) h (hspan hh)
    tau_apply_one := fun f hf => hc.tau_apply_one f (hspan hf)
    R_subset := fun χ hχ => hc.R_subset χ (hTS hχ)
    charInner_R_self := fun χ hχ => hc.charInner_R_self χ (hTS hχ)
    charInner_R_of_ne := fun χ hχ => hc.charInner_R_of_ne χ (hTS hχ)
    tau_sub_star := fun χ hχ => hc.tau_sub_star χ (hTS hχ)
    charInner_R_R := fun χ hχ ψ hψ => hc.charInner_R_R χ (hTS hχ) ψ (hTS hψ) }

namespace WeightedMinDegreeRigidity

def IsTauCoherent (tau : (L → ℂ) → (G → ℂ)) (T : Finset (L → ℂ)) : Prop :=
  ∃ τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G,
    (∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ)) ∧
      IsCoherent (T : Set (L → ℂ)) τT

theorem isCoherentWith_congr_baseline {U : Set (L → ℂ)}
    {τ τ' : charSpanZero U →+ virtualChars G} {ν : Submodule.span ℤ U →+ virtualChars G}
    (h : ∀ f : charSpanZero U, (τ f : G → ℂ) = (τ' f : G → ℂ)) (hν : IsCoherentWith U τ ν) :
    IsCoherentWith U τ' ν :=
  ⟨hν.inner_eq, fun f => (hν.eq_on_zero f).trans (Subtype.ext (h f))⟩

theorem isTauCoherent_iff (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : (T : Set (L → ℂ)) ⊆ (S : Set (L → ℂ))) :
    IsTauCoherent tau T ↔ IsCoherent (T : Set (L → ℂ)) (subTauHom hc hTS) := by
  refine ⟨fun h => ?_, fun h => ⟨subTauHom hc hTS, subTauHom_apply hc hTS, h⟩⟩
  obtain ⟨τT, hτT, hcoh⟩ := h
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
  exact isCoherent_iff.2 ⟨ν, isCoherentWith_congr_baseline
    (fun f => by rw [hτT f, subTauHom_apply hc hTS f]) hν⟩

theorem isTauCoherent_of_isCoherent (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    {U : Set (L → ℂ)} (hUT : U = (T : Set (L → ℂ))) (hUS : U ⊆ (S : Set (L → ℂ)))
    (h : IsCoherent U (subTauHom hc hUS)) : IsTauCoherent tau T := by
  subst hUT; exact (isTauCoherent_iff hc hUS).2 h

theorem isTauCoherent_of_uniform_degree (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : T ⊆ S) (hTstar : ∀ γ ∈ T, star γ ∈ T)
    (hdeg : ∀ χ ∈ T, ∀ ψ ∈ T, χ 1 = ψ 1) : IsTauCoherent tau T := by
  have hTS' : (T : Set (L → ℂ)) ⊆ (S : Set (L → ℂ)) := by exact_mod_cast hTS
  exact (isTauCoherent_iff hc hTS').2
    ((hc.subfamily hTS hTstar).isCoherent_of_uniform_degree (subTauHom hc hTS')
      (subTauHom_apply hc hTS') hdeg)

omit [Fintype L] [Group L] in
theorem coe_insert_insert_star [DecidableEq (L → ℂ)] [Star (L → ℂ)]
    (χ : L → ℂ) (T : Finset (L → ℂ)) :
    ((insert χ (insert (star χ) T) : Finset (L → ℂ)) : Set (L → ℂ)) = insertPair χ T := by
  ext f
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, mem_insertPair_iff]

theorem weight_pos (hc : IsSubcoherent S tau R) {γ : L → ℂ} (hγ : γ ∈ S) :
    (0 : ℂ) < γ 1 ^ 2 / cfInner γ γ := by
  obtain ⟨d, hd, hdd⟩ := (hc.isCharacter γ hγ).exists_pos_nat_apply_one (hc.ne_zero γ hγ)
  obtain ⟨n, hn, hnn⟩ := hc.exists_pos_nat_cfInner_self hγ
  rw [hdd, hnn,
    show ((d : ℂ)) ^ 2 / (n : ℂ) = ((((d : ℝ)) ^ 2 / (n : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.zero_lt_real]
  exact div_pos (pow_pos (by exact_mod_cast hd) 2) (by exact_mod_cast hn)

theorem exists_nonneg_real_sum_weight (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : T ⊆ S) :
    ∃ w : ℝ, 0 ≤ w ∧ ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ = ((w : ℝ) : ℂ) := by
  have h : (0 : ℂ) ≤ ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ :=
    Finset.sum_nonneg fun γ hγ => (weight_pos hc (hTS hγ)).le
  exact ⟨_, (Complex.le_def.1 h).1, Complex.eq_re_of_ofReal_le h⟩

theorem sum_weight_le_natCast_of_not_lt (hc : IsSubcoherent S tau R) {T : Finset (L → ℂ)}
    (hTS : T ⊆ S) {N : ℕ} (h : ¬ ((N : ℂ) < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ)) :
    ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ ≤ (N : ℂ) := by
  obtain ⟨w, -, hw⟩ := exists_nonneg_real_sum_weight hc hTS
  rw [hw] at h ⊢
  rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by push_cast; ring] at h ⊢
  rw [Complex.real_lt_real, not_lt] at h
  exact Complex.real_le_real.2 h

theorem sum_weight_le_of_subset (hc : IsSubcoherent S tau R) {T U : Finset (L → ℂ)}
    (hUT : U ⊆ T) (hTS : T ⊆ S) :
    ∑ γ ∈ U, γ 1 ^ 2 / cfInner γ γ ≤ ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ :=
  Finset.sum_le_sum_of_subset_of_nonneg hUT fun γ _ _ => (weight_pos hc (hTS ‹_›)).le

theorem eq_of_sum_weight_eq (hc : IsSubcoherent S tau R) {T U : Finset (L → ℂ)}
    (hUT : U ⊆ T) (hTS : T ⊆ S)
    (heq : ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ = ∑ γ ∈ U, γ 1 ^ 2 / cfInner γ γ) : T = U := by
  classical
  refine Finset.Subset.antisymm ?_ hUT
  rw [← Finset.sdiff_eq_empty_iff_subset]
  by_contra hne
  obtain ⟨γ, hγ⟩ := Finset.nonempty_of_ne_empty hne
  have hz : ∑ δ ∈ T \ U, δ 1 ^ 2 / cfInner δ δ = 0 := by
    rw [Finset.sum_sdiff_eq_sub hUT, heq, sub_self]
  have hzz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun δ hδ => (weight_pos hc (hTS (Finset.mem_sdiff.1 hδ).1)).le)).1 hz γ hγ
  exact (weight_pos hc (hTS (Finset.mem_sdiff.1 hγ).1)).ne' hzz

theorem sum_weight_eq_of_subset_Irr {Q S1 : Finset (L → ℂ)} {q a : ℕ}
    (hQS1 : Q ⊆ S1) (hQIrr : ∀ γ ∈ Q, γ ∈ Irr L)
    (hS1deg : ∀ γ ∈ S1, γ 1 = ((q * a : ℕ) : ℂ)) :
    ∑ γ ∈ Q, γ 1 ^ 2 / cfInner γ γ = ((Q.card * (q * a) ^ 2 : ℕ) : ℂ) := by
  rw [Finset.sum_congr rfl fun γ hγ => by
      rw [cfInner_self_of_mem_Irr (hQIrr γ hγ), div_one, hS1deg γ (hQS1 hγ)],
    Finset.sum_const, nsmul_eq_mul]
  push_cast; ring

theorem two_mul_le_sub_one {p a : ℕ} (hp : 3 ≤ p) (hpodd : Odd p) (haodd : Odd a)
    (hdvd : a ∣ p - 1) : 2 * a ≤ p - 1 := by
  obtain ⟨m, hm⟩ := hdvd
  have hpe : Even (p - 1) := Nat.Odd.sub_odd hpodd odd_one
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hme : Even m := by
    rcases Nat.even_or_odd m with h | h
    · exact h
    · exact absurd (hm ▸ hpe) (Nat.not_even_iff_odd.2 (haodd.mul h))
  obtain ⟨t, ht⟩ := hme
  have ht0 : 1 ≤ t := by omega
  rw [hm, ht]
  nlinarith

theorem numeric_chain {p q a u v r k N : ℕ} (hq : 1 ≤ q) (ha1 : 1 < a) (hu : 0 < u)
    (hP : 2 * a ≤ p - 1) (hak : a * k ≤ u) (huv : u ≤ v)
    (hrdef : r * a ^ 2 = (p - 1) * v) (hrN : r ≤ N)
    (hle : N * (q * a) ^ 2 ≤ 2 * q ^ 2 * a ^ 2 * k) :
    a * k = u ∧ 2 * a = p - 1 ∧ u = v ∧ r = N ∧ N * (q * a) ^ 2 = 2 * q ^ 2 * a ^ 2 * k := by
  have ha0 : 0 < a := by omega
  have hq0 : 0 < q := hq
  have hp0 : 0 < p - 1 := by omega
  have hB_C : 2 * q ^ 2 * a ^ 2 * k ≤ 2 * q ^ 2 * a * u := by
    calc 2 * q ^ 2 * a ^ 2 * k = (2 * q ^ 2 * a) * (a * k) := by ring
    _ ≤ (2 * q ^ 2 * a) * u := Nat.mul_le_mul_left _ hak
    _ = 2 * q ^ 2 * a * u := by ring
  have hC_D : 2 * q ^ 2 * a * u ≤ (p - 1) * q ^ 2 * u := by
    calc 2 * q ^ 2 * a * u = (2 * a) * (q ^ 2 * u) := by ring
    _ ≤ (p - 1) * (q ^ 2 * u) := Nat.mul_le_mul_right _ hP
    _ = (p - 1) * q ^ 2 * u := by ring
  have hD_E : (p - 1) * q ^ 2 * u ≤ (p - 1) * q ^ 2 * v := Nat.mul_le_mul_left _ huv
  have hE_Nq : (p - 1) * q ^ 2 * v ≤ N * (q * a) ^ 2 := by
    calc (p - 1) * q ^ 2 * v = q ^ 2 * (r * a ^ 2) := by rw [hrdef]; ring
    _ ≤ q ^ 2 * (N * a ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hrN)
    _ = N * (q * a) ^ 2 := by ring
  have e1 : 2 * q ^ 2 * a ^ 2 * k = 2 * q ^ 2 * a * u := by omega
  have e2 : 2 * q ^ 2 * a * u = (p - 1) * q ^ 2 * u := by omega
  have e3 : (p - 1) * q ^ 2 * u = (p - 1) * q ^ 2 * v := by omega
  have e4 : (p - 1) * q ^ 2 * v = N * (q * a) ^ 2 := by omega
  have e0 : N * (q * a) ^ 2 = 2 * q ^ 2 * a ^ 2 * k := by omega
  refine ⟨?_, ?_, ?_, ?_, e0⟩
  · refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * q ^ 2 * a by positivity) ?_
    calc (2 * q ^ 2 * a) * (a * k) = 2 * q ^ 2 * a ^ 2 * k := by ring
    _ = (2 * q ^ 2 * a) * u := e1
  · refine Nat.eq_of_mul_eq_mul_right (show 0 < q ^ 2 * u by positivity) ?_
    calc (2 * a) * (q ^ 2 * u) = 2 * q ^ 2 * a * u := by ring
    _ = (p - 1) * (q ^ 2 * u) := by rw [e2]; ring
  · exact Nat.eq_of_mul_eq_mul_left (show 0 < (p - 1) * q ^ 2 by positivity) e3
  · refine Nat.eq_of_mul_eq_mul_left (show 0 < q ^ 2 * a ^ 2 by positivity) ?_
    calc q ^ 2 * a ^ 2 * r = q ^ 2 * (r * a ^ 2) := by ring
    _ = (p - 1) * q ^ 2 * v := by rw [hrdef]; ring
    _ = N * (q * a) ^ 2 := e4
    _ = q ^ 2 * a ^ 2 * N := by ring

theorem exists_maximal_isTauCoherent {S1 : Finset (L → ℂ)} (hS1S : S1 ⊆ S)
    (hS1star : ∀ γ ∈ S1, star γ ∈ S1) (hS1coh : IsTauCoherent tau S1) :
    ∃ T : Finset (L → ℂ), T ⊆ S ∧ S1 ⊆ T ∧ (∀ γ ∈ T, star γ ∈ T) ∧ IsTauCoherent tau T ∧
      ∀ T' : Finset (L → ℂ), T' ⊆ S → S1 ⊆ T' → (∀ γ ∈ T', star γ ∈ T') →
        IsTauCoherent tau T' → T'.card ≤ T.card := by
  classical
  set P : Finset (L → ℂ) → Prop :=
    fun T => S1 ⊆ T ∧ (∀ γ ∈ T, star γ ∈ T) ∧ IsTauCoherent tau T with hP
  set cands := S.powerset.filter P with hcands
  have hmem : ∀ T : Finset (L → ℂ), T ∈ cands ↔ T ⊆ S ∧ P T := by
    intro T; rw [hcands, Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨T, hT, hTmax⟩ := Finset.exists_max_image cands Finset.card
    ⟨S1, (hmem S1).2 ⟨hS1S, Finset.Subset.refl _, hS1star, hS1coh⟩⟩
  obtain ⟨hTS, hTP⟩ := (hmem T).1 hT
  exact ⟨T, hTS, hTP.1, hTP.2.1, hTP.2.2, fun T' h1 h2 h3 h4 =>
    hTmax T' ((hmem T').2 ⟨h1, h2, h3, h4⟩)⟩

theorem not_lt_sum_weight_of_maximal (hc : IsSubcoherent S tau R) {T S1 : Finset (L → ℂ)}
    (hTS : T ⊆ S) (hS1T : S1 ⊆ T) (hTstar : ∀ γ ∈ T, star γ ∈ T)
    (hTcoh : IsTauCoherent tau T)
    (hTmax : ∀ T' : Finset (L → ℂ), T' ⊆ S → S1 ⊆ T' → (∀ γ ∈ T', star γ ∈ T') →
      IsTauCoherent tau T' → T'.card ≤ T.card)
    {ψ : L → ℂ} (hψT : ψ ∈ T) {χ : L → ℂ} (hχS : χ ∈ S) (hχT : χ ∉ T)
    {d : ℕ} (hd : 1 ≤ d) (hχd : χ 1 = (d : ℂ) * ψ 1) :
    ¬ (2 * χ 1 * ψ 1 < ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ) := by
  classical
  intro hlt
  obtain ⟨τT, hτT, hcoh⟩ := hTcoh
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
  have hbig := isCoherent_insertPair hc hTS ⟨ψ, hψT⟩ hTstar hν hτT hψT hχS hχT hd hχd hlt
  set T' : Finset (L → ℂ) := insert χ (insert (star χ) T) with hT'def
  have hT'coh : IsTauCoherent tau T' :=
    isTauCoherent_of_isCoherent hc (coe_insert_insert_star χ T).symm _ hbig
  have hT'S : T' ⊆ S := by
    intro f hf
    rw [hT'def, Finset.mem_insert, Finset.mem_insert] at hf
    rcases hf with rfl | rfl | hf
    · exact hχS
    · exact hc.star_mem _ hχS
    · exact hTS hf
  have hT'star : ∀ γ ∈ T', star γ ∈ T' := by
    intro γ hγ
    rw [hT'def, Finset.mem_insert, Finset.mem_insert] at hγ ⊢
    rcases hγ with rfl | rfl | hγ
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (star_star _)
    · exact Or.inr (Or.inr (hTstar γ hγ))
  have hTT' : T ⊆ T' := by
    rw [hT'def]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hcard := hTmax T' hT'S (hS1T.trans hTT') hT'star hT'coh
  have hχnot : χ ∉ insert (star χ) T := by
    rw [Finset.mem_insert]
    exact fun h => h.elim (fun he => hc.star_ne χ hχS he.symm) hχT
  have hlt' : T.card < T'.card := by
    rw [hT'def, Finset.card_insert_of_notMem hχnot]
    exact Nat.lt_succ_of_le (Finset.card_le_card (Finset.subset_insert _ _))
  omega

theorem rigidity (hc : IsSubcoherent S tau R)
    {p q a u v r : ℕ} (hp : 3 ≤ p) (hpodd : Odd p) (hq : 1 ≤ q)
    (ha1 : 1 < a) (haodd : Odd a) (hadvd : a ∣ p - 1) (hau : a ∣ u)
    (hu : 0 < u) (huv : u ≤ v)
    (hdeg : ∀ χ ∈ S, ∃ k : ℕ, 0 < k ∧ χ 1 = ((q * a * k : ℕ) : ℂ))
    (hdegle : ∀ χ ∈ S, χ 1 ≤ ((q * u : ℕ) : ℂ))
    {S1 : Finset (L → ℂ)} (hS1 : ∀ χ, χ ∈ S1 ↔ χ ∈ S ∧ χ 1 = ((q * a : ℕ) : ℂ))
    {Q : Finset (L → ℂ)} (hQS1 : Q ⊆ S1) (hQIrr : ∀ γ ∈ Q, γ ∈ Irr L)
    (hr : 0 < r) (hrdef : r * a ^ 2 = (p - 1) * v) (hQcard : r ≤ Q.card)
    (hSnc : ¬ IsTauCoherent tau S) :
    2 * a = p - 1 ∧ v = u ∧ a < u ∧ S1 = Q ∧ Q.card = r ∧ Q.card * a = 2 * u ∧
      (∀ χ ∈ S, χ ∉ S1 → χ 1 = ((q * u : ℕ) : ℂ)) ∧
      IsTauCoherent tau S1 ∧
      (∀ T : Finset (L → ℂ), S1 ⊆ T → T ⊆ S → (∀ γ ∈ T, star γ ∈ T) →
        IsTauCoherent tau T → T = S1) := by
  classical
  have hS1S : S1 ⊆ S := fun χ hχ => ((hS1 χ).1 hχ).1
  have hS1deg : ∀ γ ∈ S1, γ 1 = ((q * a : ℕ) : ℂ) := fun γ hγ => ((hS1 γ).1 hγ).2
  have hS1star : ∀ γ ∈ S1, star γ ∈ S1 := by
    intro γ hγ
    refine (hS1 _).2 ⟨hc.star_mem γ (hS1S hγ), ?_⟩
    rw [(hc.isCharacter γ (hS1S hγ)).star_apply_one, hS1deg γ hγ]
  have hS1coh : IsTauCoherent tau S1 :=
    isTauCoherent_of_uniform_degree hc hS1S hS1star
      (fun χ hχ ψ hψ => by rw [hS1deg χ hχ, hS1deg ψ hψ])
  obtain ⟨T, hTS, hS1T, hTstar, hTcoh, hTmax⟩ :=
    exists_maximal_isTauCoherent hS1S hS1star hS1coh
  have hTneS : T ≠ S := fun h => hSnc (h ▸ hTcoh)
  have hSTne : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun h => hTneS (Finset.Subset.antisymm hTS h)
  obtain ⟨χ₀, hχ₀ST, hχ₀min⟩ := Finset.exists_min_image (S \ T) (fun χ => (χ 1).re) hSTne
  obtain ⟨hχ₀S, hχ₀T⟩ := Finset.mem_sdiff.1 hχ₀ST
  obtain ⟨k, hk, hχ₀d⟩ := hdeg χ₀ hχ₀S
  obtain ⟨ψ, hψQ⟩ : Q.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le hr hQcard)
  have hψS1 : ψ ∈ S1 := hQS1 hψQ
  have hψT : ψ ∈ T := hS1T hψS1
  have hψd : ψ 1 = ((q * a : ℕ) : ℂ) := hS1deg ψ hψS1
  have hbound : ∑ γ ∈ T, γ 1 ^ 2 / cfInner γ γ ≤ ((2 * q ^ 2 * a ^ 2 * k : ℕ) : ℂ) := by
    have hcast : 2 * χ₀ 1 * ψ 1 = ((2 * q ^ 2 * a ^ 2 * k : ℕ) : ℂ) := by
      rw [hχ₀d, hψd]; push_cast; ring
    refine sum_weight_le_natCast_of_not_lt hc hTS ?_
    rw [← hcast]
    exact not_lt_sum_weight_of_maximal hc hTS hS1T hTstar hTcoh hTmax hψT hχ₀S hχ₀T hk
      (d := k) (by rw [hχ₀d, hψd]; push_cast; ring)
  have hWQ : ∑ γ ∈ Q, γ 1 ^ 2 / cfInner γ γ = ((Q.card * (q * a) ^ 2 : ℕ) : ℂ) :=
    sum_weight_eq_of_subset_Irr hQS1 hQIrr hS1deg
  have hQT : Q ⊆ T := hQS1.trans hS1T
  have hle : Q.card * (q * a) ^ 2 ≤ 2 * q ^ 2 * a ^ 2 * k := by
    have h : ((Q.card * (q * a) ^ 2 : ℕ) : ℂ) ≤ ((2 * q ^ 2 * a ^ 2 * k : ℕ) : ℂ) :=
      le_trans (hWQ ▸ sum_weight_le_of_subset hc hQT hTS) hbound
    exact_mod_cast h
  have hak : a * k ≤ u := by
    have h : ((q * a * k : ℕ) : ℂ) ≤ ((q * u : ℕ) : ℂ) := hχ₀d ▸ hdegle χ₀ hχ₀S
    have h' : q * a * k ≤ q * u := by exact_mod_cast h
    rw [mul_assoc] at h'
    exact Nat.le_of_mul_le_mul_left h' hq
  obtain ⟨heq_ak, heq_2a, heq_uv, heq_r, heq_W⟩ :=
    numeric_chain hq ha1 hu (two_mul_le_sub_one hp hpodd haodd hadvd) hak huv hrdef hQcard hle
  have hχ₀u : χ₀ 1 = ((q * u : ℕ) : ℂ) := by rw [hχ₀d, ← heq_ak, mul_assoc]
  have hTQ : T = Q := by
    refine eq_of_sum_weight_eq hc hQT hTS (le_antisymm ?_ (sum_weight_le_of_subset hc hQT hTS))
    rw [hWQ]
    refine le_trans hbound (le_of_eq ?_)
    exact_mod_cast congrArg (fun n : ℕ => ((n : ℕ) : ℂ)) heq_W.symm
  have hS1Q : S1 = Q := Finset.Subset.antisymm (hTQ ▸ hS1T) hQS1
  have hka : k ≠ 1 := by
    rintro rfl
    exact hχ₀T (hS1T ((hS1 χ₀).2 ⟨hχ₀S, by rw [hχ₀d, mul_one]⟩))
  have hau' : a < u := by
    have hle : a ≤ u := Nat.le_of_dvd hu hau
    have hk2 : 2 ≤ k := by omega
    have h2a : 2 * a ≤ u := by
      calc 2 * a ≤ a * k := by nlinarith
      _ = u := heq_ak
    omega
  have houtside : ∀ χ ∈ S, χ ∉ S1 → χ 1 = ((q * u : ℕ) : ℂ) := by
    intro χ hχS hχS1
    have hχT : χ ∉ T := by rw [hTQ, ← hS1Q]; exact hχS1
    obtain ⟨j, hj, hχd⟩ := hdeg χ hχS
    have h1 : (χ₀ 1).re ≤ (χ 1).re := hχ₀min χ (Finset.mem_sdiff.2 ⟨hχS, hχT⟩)
    rw [hχ₀u, hχd] at h1
    simp only [Complex.natCast_re] at h1
    have h1' : q * u ≤ q * a * j := by exact_mod_cast h1
    have h2 : ((q * a * j : ℕ) : ℂ) ≤ ((q * u : ℕ) : ℂ) := hχd ▸ hdegle χ hχS
    have h2' : q * a * j ≤ q * u := by exact_mod_cast h2
    rw [hχd]
    exact_mod_cast congrArg (fun n : ℕ => ((n : ℕ) : ℂ)) (le_antisymm h2' h1')
  refine ⟨heq_2a, heq_uv.symm, hau', hS1Q, heq_r.symm, ?_, houtside, hS1coh, ?_⟩
  ·
    refine Nat.eq_of_mul_eq_mul_left (show 0 < q ^ 2 * a by positivity) ?_
    calc q ^ 2 * a * (Q.card * a) = Q.card * (q * a) ^ 2 := by ring
    _ = 2 * q ^ 2 * a ^ 2 * k := heq_W
    _ = q ^ 2 * a * (2 * (a * k)) := by ring
    _ = q ^ 2 * a * (2 * u) := by rw [heq_ak]
  ·
    intro T' hS1T' hT'S hT'star hT'coh
    refine (Finset.eq_of_subset_of_card_le hS1T' ?_).symm
    have hcard := hTmax T' hT'S hS1T' hT'star hT'coh
    rw [hTQ, ← hS1Q] at hcard
    exact hcard

theorem rigidity_maximal (hc : IsSubcoherent S tau R)
    {p q a u v r : ℕ} (hp : 3 ≤ p) (hpodd : Odd p) (hq : 1 ≤ q)
    (ha1 : 1 < a) (haodd : Odd a) (hadvd : a ∣ p - 1) (hau : a ∣ u)
    (hu : 0 < u) (huv : u ≤ v)
    (hdeg : ∀ χ ∈ S, ∃ k : ℕ, 0 < k ∧ χ 1 = ((q * a * k : ℕ) : ℂ))
    (hdegle : ∀ χ ∈ S, χ 1 ≤ ((q * u : ℕ) : ℂ))
    {S1 : Finset (L → ℂ)} (hS1 : ∀ χ, χ ∈ S1 ↔ χ ∈ S ∧ χ 1 = ((q * a : ℕ) : ℂ))
    {Q : Finset (L → ℂ)} (hQS1 : Q ⊆ S1) (hQIrr : ∀ γ ∈ Q, γ ∈ Irr L)
    (hr : 0 < r) (hrdef : r * a ^ 2 = (p - 1) * v) (hQcard : r ≤ Q.card)
    (hSnc : ¬ IsTauCoherent tau S) :
    IsTauCoherent tau S1 ∧
      ∀ T : Finset (L → ℂ), S1 ⊂ T → T ⊆ S → (∀ γ ∈ T, star γ ∈ T) →
        ¬ IsTauCoherent tau T := by
  obtain ⟨-, -, -, -, -, -, -, hS1coh, hmax⟩ :=
    rigidity hc hp hpodd hq ha1 haodd hadvd hau hu huv hdeg hdegle hS1 hQS1 hQIrr hr hrdef
      hQcard hSnc
  refine ⟨hS1coh, fun T hST hTS hTstar hTcoh => ?_⟩
  exact hST.ne' (hmax T hST.subset hTS hTstar hTcoh)

end WeightedMinDegreeRigidity

end CFSG.FeitThompson
