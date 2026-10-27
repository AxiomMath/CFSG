module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltWeakBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakHolds
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceFromYS2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn SporadicOrdersTable LocalTwoBalanceDefCharThree
  LocalTwoBalanceDefCharFive)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs SporadicOuterLeTwo
  LocalThreeBalanceCrossChar)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo (LocalTwoBalanceSporadicGtFive IsLpEpsIndex
  LocalTwoBalanceCrossCharGtFive LocalTwoBalanceDefCharGtFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Equiv Equiv.Perm

theorem localDeltaTwoIn_commutator_eq_bot {M : Type*} [Group M] (H D : Subgroup M) :
    ⁅localDeltaTwoIn H D, D⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx d hd
  by_cases hd1 : d = 1
  · rw [hd1, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · have hx' : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set M)) := by
      unfold localDeltaTwoIn at hx
      simp only [Subgroup.mem_iInf] at hx
      exact hx d hd hd1
    have hxc : x ∈ Subgroup.centralizer ({d} : Set M) :=
      (Subgroup.mem_inf.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx')).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    rw [commutatorElement_eq_one_iff_mul_comm.2 hxc]
    exact Subgroup.one_mem _

@[expose] def Input19_16Lp : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    GLAPPrimeCore p K = ⊥ →
    (∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ 2 →
      ¬ IsLocallyOTwoBalanced p 2 B → Lemma129.Lie1916 p 2 B

theorem isWeaklyLocallyOTwoBalanced_of_weak {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut K)}
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.IsWeaklyLocallyBalanced p k A) :
    IsWeaklyLocallyOTwoBalanced p k A := by
  intro D hD H hH hAH
  exact le_bot_iff.1 ((Subgroup.commutator_mono (localDeltaTwoIn_le_localDeltaIn hp hp2 H D) le_rfl).trans
    (h D hD H hH hAH).le)

theorem weakLpEps_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (idx : TauCeti.ValidLieTypeIndex) (hidx : IsLpEpsIndex p idx.1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsWeaklyLocallyBalancedAbs p 2 S := by
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  change IsLpEpsIndex p d at hidx
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    exact CFSG.HardMathSupport.Solomon.Coordinator.isWeaklyLocallyBalancedAbs_of_mulEquiv
      (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)))
      (CFSG.HardMathSupport.Solomon.Coordinator.weakBalance_projectiveSL hp hp2
        (CFSG.HardMathSupport.Solomon.Coordinator.dvd_card_galoisField_sub_one hp.one_lt Q hQ))
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    obtain ⟨K, _, h, hne, ⟨e'⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.unitary_catalogue_model m Q hv e
    have hpq : m + 1 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    by_cases h8 : m + 1 = 3 ∧ Q.p ^ Q.exponent = 8
    · obtain ⟨h3, h8'⟩ := h8
      obtain ⟨hp2', he3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.w3_pp_eq_eight Q.prime_p h8'
      obtain rfl : m = 2 := by omega
      exact CFSG.HardMathSupport.Solomon.Coordinator.isWeaklyLocallyBalancedAbs_of_mulEquiv e'
        (CFSG.HardMathSupport.Solomon.Coordinator.i1910_weakAbs_of_abs
          (CFSG.HardMathSupport.Solomon.Coordinator.u38_isLocallyBalancedAbs' h hp2' he3))
    · exact CFSG.HardMathSupport.Solomon.Coordinator.isWeaklyLocallyBalancedAbs_of_mulEquiv e'
        (CFSG.HardMathSupport.Solomon.Coordinator.weakBalance_primeFormP h hp hp2 hne h8 hpq)

@[expose] def Input19_16LpC : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    GLAPPrimeCore p K = ⊥ →
    (∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ 2 →
      ¬ IsLocallyOTwoBalanced p 2 B →
        (∃ q : ℕ, p ∣ q - 1 ∧ IsLpType p q (K ⧸ Subgroup.center K)) ∧ B ≤ innerAut K

theorem input19_16Lp_of_C (h : Input19_16LpC) : Input19_16Lp := by
  intro p hp hp2 K _ _ hq hO hL B hB hBc hnb
  obtain ⟨hlin, hinn⟩ := h p hp hp2 K hq hO hL B hB hBc hnb
  refine ⟨rfl, hlin, hinn, fun B' hB' _ => ?_⟩
  obtain ⟨idx, hidx, he⟩ := hL
  have hw := weakLpEps_holds hp hp2 idx hidx he
  have hw2 : IsWeaklyLocallyOTwoBalancedWrtP p 2 (K ⧸ Subgroup.center K) := fun A hA =>
    isWeaklyLocallyOTwoBalanced_of_weak hp hp2 (hw A hA)
  exact Inputs123a.isWeaklyLocallyOTwoBalancedWrtP_of_quot hq.1 hw2 B' hB'

section AltPerm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem ncard_fix_eq (σ : Perm α) : {j | σ j = j}.ncard = Fintype.card {i // σ i = i} := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  rfl

theorem fix_of_fix {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Set (Perm α)}
    (hcomm : ∀ σ ∈ D, ∀ σ' ∈ D, σ * σ' = σ' * σ) (hexp : ∀ σ ∈ D, σ ^ p = 1) {τ : Perm α}
    (hτ : τ ≠ 1) (hτfix : ∀ σ ∈ D, σ ≠ 1 → ∀ j, τ j ≠ j → σ j = j)
    (hcard : ∀ σ ∈ D, σ ≠ 1 → Fintype.card {i // σ i = i} ≤ 4)
    {σ σ' : Perm α} (hσ : σ ∈ D) (hσ1 : σ ≠ 1) (hσ' : σ' ∈ D) {j : α} (hj : σ j = j) : σ' j = j := by
  by_contra hj'
  have hσ'1 : σ' ≠ 1 := fun h => hj' (by rw [h, Perm.one_apply])
  have hcyc : (σ'.cycleOf j).IsCycle := isCycle_cycleOf σ' hj'
  have hccard : (σ'.cycleOf j).support.card = p := by
    rw [← hcyc.orderOf]
    exact AltWeakBalance.orderOf_cycleOf_eq hp (hexp σ' hσ') hj'
  have hT : τ.support ⊆ Finset.univ.filter (fun i => σ i = i) := by
    intro y hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hτfix σ hσ hσ1 y (Perm.mem_support.1 hy)⟩
  have hC : (σ'.cycleOf j).support ⊆ Finset.univ.filter (fun i => σ i = i) := by
    intro y hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨⟨i, hi⟩, -⟩ := Perm.mem_support_cycleOf_iff.1 hy
    rw [← hi]
    have hcm : σ * σ' ^ i = σ' ^ i * σ := (Commute.zpow_right (hcomm σ hσ σ' hσ') i).eq
    rw [← Perm.mul_apply, hcm, Perm.mul_apply, hj]
  have hdisj : Disjoint τ.support (σ'.cycleOf j).support := by
    rw [Finset.disjoint_left]
    intro y hyτ hyc
    have h1 : σ' y ≠ y := Perm.mem_support.1 (Perm.support_cycleOf_le σ' j hyc)
    exact h1 (hτfix σ' hσ' hσ'1 y (Perm.mem_support.1 hyτ))
  have h2 : 2 ≤ τ.support.card := Perm.two_le_card_support_of_ne_one hτ
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hle : τ.support.card + (σ'.cycleOf j).support.card ≤
      (Finset.univ.filter (fun i => σ i = i)).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hT hC)
  have h4 := hcard σ hσ hσ1
  rw [Fintype.card_subtype] at h4
  omega

theorem exists_eq_of_fix_card {n : ℕ} {D : Subgroup (Perm (Fin n))} {r : ℕ}
    (hfix : ∀ σ ∈ D, σ ≠ 1 → Fintype.card {i // σ i = i} = r) :
    ∃ N : ℕ, n + (Nat.card D - 1) * r = N * Nat.card D := by
  classical
  have hcardfix : ∀ σ : ↥D, Fintype.card (MulAction.fixedBy (Fin n) σ) =
      Fintype.card {i // (σ : Perm (Fin n)) i = i} :=
    fun σ => Fintype.card_congr (Equiv.subtypeEquivRight fun i => Iff.rfl)
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥D (Fin n)
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (1 : ↥D))] at hB
  have h1 : Fintype.card (MulAction.fixedBy (Fin n) (1 : ↥D)) = n := by
    rw [hcardfix]
    simp
  have hrest : ∑ σ ∈ Finset.univ \ {(1 : ↥D)}, Fintype.card (MulAction.fixedBy (Fin n) σ) =
      (Fintype.card ↥D - 1) * r := by
    rw [Finset.sum_congr rfl fun σ hσ => (hcardfix σ).trans (hfix σ σ.2 fun h => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hσ
      exact hσ (Subtype.ext h)), Finset.sum_const, smul_eq_mul, Finset.card_sdiff, Finset.card_univ]
    simp
  rw [h1, hrest] at hB
  exact ⟨_, by rw [Nat.card_eq_fintype_card]; exact hB⟩

theorem eq_mul_add_of_sum {n N q r : ℕ} (hq : 0 < q) (hrn : r < n) (h : n + (q - 1) * r = N * q) :
    ∃ m, 0 < m ∧ n = m * q + r := by
  have h1 : (q - 1) * r + r = q * r := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
  have hNr : r < N := by
    by_contra hle
    push Not at hle
    have : N * q ≤ r * q := Nat.mul_le_mul_right q hle
    nlinarith
  refine ⟨N - r, Nat.sub_pos_of_lt hNr, ?_⟩
  have h2 : (N - r) * q + r * q = N * q := by rw [← Nat.add_mul, Nat.sub_add_cancel hNr.le]
  nlinarith

end AltPerm

section Alt

variable {S : Type} [Group S] [Finite S] {n : ℕ}

theorem alt_le_map (e : S ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) {H : Subgroup (MulAut S)}
    (hH : innerAut S ≤ H) :
    alternatingGroup (Fin n) ≤ H.map (AltWeakBalance.autPerm e h5 h6).toMonoidHom := by
  intro u hu
  exact ⟨(AltWeakBalance.autPerm e h5 h6).symm u,
    hH (AltWeakBalance.autPerm_symm_mem_innerAut e h5 h6 hu), by simp⟩

theorem pCoreOf_eq_bot_of_fix (e : S ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup (MulAut S)} (hH : innerAut S ≤ H) {b : MulAut S}
    (hb : b ^ p = 1) (h2 : Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} ≠ 2)
    (h4 : Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} ≠ 4) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({b} : Set (MulAut S))) = ⊥ := by
  have hσ : AltWeakBalance.autPerm e h5 h6 b ^ p = 1 := by rw [← map_pow, hb, map_one]
  have h0 := Inputs123a.pCoreOf_eq_bot_of_card_fix hp hp2 hσ (alt_le_map e h5 h6 hH) h2 h4
  have hmap : (H ⊓ Subgroup.centralizer ({b} : Set (MulAut S))).map
      (AltWeakBalance.autPerm e h5 h6).toMonoidHom =
      H.map (AltWeakBalance.autPerm e h5 h6).toMonoidHom ⊓
        Subgroup.centralizer ({AltWeakBalance.autPerm e h5 h6 b} : Set (Perm (Fin n))) :=
    Inputs123a.map_inf_centralizer _ (AltWeakBalance.autPerm e h5 h6).injective H b
  rw [← hmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (AltWeakBalance.autPerm e h5 h6)] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ (AltWeakBalance.autPerm e h5 h6).injective).1 h0

theorem alt_fix_eq (e : S ≃* alternatingGroup (Fin n)) (h5 : 5 ≤ n) (h6 : n ≠ 6) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B H : Subgroup (MulAut S)} (hB : IsElemAbelian p B)
    (hH : innerAut S ≤ H) (hne : localDeltaTwoIn H B ≠ ⊥) :
    (∀ b ∈ B, b ≠ 1 → Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} = 2 ∨
        Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} = 4) ∧
      ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, ∀ j, AltWeakBalance.autPerm e h5 h6 b j = j →
        AltWeakBalance.autPerm e h5 h6 b' j = j := by
  obtain ⟨⟨x, hxΔ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxb : ∀ b ∈ B, b ≠ 1 → x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({b} : Set (MulAut S))) := by
    intro b hb hb1
    unfold localDeltaTwoIn at hxΔ
    simp only [Subgroup.mem_iInf] at hxΔ
    exact hxΔ b hb hb1
  have hcard : ∀ b ∈ B, b ≠ 1 → Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} = 2 ∨
      Fintype.card {i // AltWeakBalance.autPerm e h5 h6 b i = i} = 4 := by
    intro b hb hb1
    by_contra hc
    push Not at hc
    have h0 := pCoreOf_eq_bot_of_fix e h5 h6 hp hp2 hH (hB.2 b hb) hc.1 hc.2
    have hxb' := hxb b hb hb1
    rw [h0] at hxb'
    exact hx1' (Subgroup.mem_bot.1 hxb')
  refine ⟨hcard, ?_⟩
  intro b hb hb1 b' hb' j hj
  have hτ : AltWeakBalance.autPerm e h5 h6 x ≠ 1 := fun h =>
    hx1' ((AltWeakBalance.autPerm e h5 h6).injective (by rw [h, map_one]))
  refine fix_of_fix hp hp2 (D := (AltWeakBalance.autPerm e h5 h6) '' (B : Set (MulAut S))) ?_ ?_ hτ ?_ ?_
    ⟨b, hb, rfl⟩ (fun h => hb1 ((AltWeakBalance.autPerm e h5 h6).injective (by rw [h, map_one])))
    ⟨b', hb', rfl⟩ hj
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨σ', hσ', rfl⟩
    rw [← map_mul, ← map_mul, CFSG.Open.IsElemAbelian.comm hB hσ hσ']
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [← map_pow, hB.2 σ hσ, map_one]
  · rintro _ ⟨σ, hσ, rfl⟩ hσ1 i hi
    have hσ1' : σ ≠ 1 := fun h => hσ1 (by rw [h, map_one])
    by_contra hci
    exact hi (AltWeakBalance.apply_eq_self_of_mem_pCoreOf e h5 h6 hp hp2 hH (hB.2 σ hσ) (hxb σ hσ hσ1') hci)
  · rintro _ ⟨σ, hσ, rfl⟩ hσ1
    have hσ1' : σ ≠ 1 := fun h => hσ1 (by rw [h, map_one])
    rcases hcard σ hσ hσ1' with h | h <;> omega

end Alt

@[expose] noncomputable def quotCenterEquiv {X : Type*} [Group X] (h : Subgroup.center X = ⊥) :
    X ≃* (X ⧸ Subgroup.center X) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center X))
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, h] at hx
      exact Subgroup.mem_bot.mp hx, QuotientGroup.mk'_surjective _⟩

theorem alt1916_of_fix {p k : ℕ} {K : Type} [Group K] (B : Subgroup (MulAut K)) {n : ℕ}
    (φ : K ≃* alternatingGroup (Fin n)) (ρ : ↥B →* Perm (Fin n)) (hρ : Lemma129.ActsAsPerm B φ ρ)
    (Ω₀ : Set (Fin n)) (hΩ : Lemma129.SemiregOutside ρ Ω₀) {m r : ℕ} (hm : 0 < m) (hr : r = 2 ∨ r = 4)
    (hΩc : Ω₀.ncard = r) (hn : n = m * p ^ k + r) : Lemma129.Alt1916 p k B := by
  subst hn
  exact ⟨m, r, hm, hr, φ, ρ, Ω₀, hρ, hΩc, hΩ⟩

theorem alt_case {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥) {n : ℕ} (hn : 5 ≤ n)
    (f : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n))
    (B : Subgroup (MulAut K)) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ k) :
    IsLocallyOTwoBalanced p k B ∨ Lemma129.Alt1916 p k B := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have htr : ∀ k', IsLocallyOTwoBalancedWrtP p k' (K ⧸ Subgroup.center K) → IsLocallyOTwoBalanced p k' B :=
    fun k' h => Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hq.1 h B hB
  by_cases h6 : n = 6
  · subst h6
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl (Lemma123.isLocallyOTwoBalanced_of_le Nat.prime_three le_rfl (by omega)
        (htr 1 ((Inputs123a.isLocallyOTwoBalancedWrtP_congr f).2 Inputs123a.balanced_alt6_three)))
    · exact (false_of_alt_quot hq.1 hp hp2 hk B hBc (Or.inr ⟨hp3, ⟨f⟩⟩)).elim
  by_cases hbal : IsLocallyOTwoBalanced p k B
  · exact Or.inl hbal
  right
  have hQinj : Function.Injective (Lemma123.autQ K) := Lemma123.autQ_injective hq.1
  have hbar : ¬ IsLocallyOTwoBalanced p k (B.map (Lemma123.autQ K)) := fun h =>
    hbal (Inputs123a.isLocallyOTwoBalanced_of_map (Lemma123.autQ K) hQinj
      (Inputs123a.innerAut_le_map_autQ K) h)
  have hBbar : IsElemAbelian p (B.map (Lemma123.autQ K)) :=
    CFSG.SectionRank.isElemAbelian_map hB (Lemma123.autQ K)
  have hBbarc : Nat.card (B.map (Lemma123.autQ K)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hQinj, hBc]
  unfold IsLocallyOTwoBalanced at hbar
  push Not at hbar
  obtain ⟨D, hD, H, hH, -, hΔ⟩ := hbar
  have hDeq : D = B.map (Lemma123.autQ K) :=
    Subgroup.eq_of_le_of_card_ge hD.1 (by rw [hBbarc, hD.2.2])
  subst hDeq
  obtain ⟨hcard, hfixeq⟩ := alt_fix_eq f hn h6 hp hp2 hBbar hH hΔ
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hBbar1 : B.map (Lemma123.autQ K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBbarc
    omega
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBbar1
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card {i // AltWeakBalance.autPerm f hn h6 b₀ i = i} = r := ⟨_, rfl⟩
  have hr24 : r = 2 ∨ r = 4 := hr ▸ hcard b₀ hb₀ hb₀1'
  have hfixr : ∀ σ ∈ (B.map (Lemma123.autQ K)).map (AltWeakBalance.autPerm f hn h6).toMonoidHom, σ ≠ 1 →
      Fintype.card {i // σ i = i} = r := by
    rintro _ ⟨b, hb, rfl⟩ hσ1
    have hb1 : b ≠ 1 := fun h => hσ1 (by rw [h, map_one])
    rw [← hr]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun h => hfixeq b hb hb1 b₀ hb₀ i h, fun h => hfixeq b₀ hb₀ hb₀1' b hb i h⟩)
  obtain ⟨N, hN⟩ := exists_eq_of_fix_card hfixr
  rw [Subgroup.card_map_of_injective (AltWeakBalance.autPerm f hn h6).injective, hBbarc] at hN
  obtain ⟨m, hm, hnm⟩ := eq_mul_add_of_sum (pow_pos hp.pos k) (by omega) hN
  have h9 : 9 ≤ p ^ k := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have h8 : 8 ≤ n := by rw [hnm]; nlinarith
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha⟩ := (AltFacts2.isPGroup_center_of_core_eq_bot hp hO).exists_card_eq
    rw [ha]
    exact (hp.odd_of_ne_two hp2).pow
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.center_eq_bot_of_odd h8 f hodd
  refine alt1916_of_fix B ((quotCenterEquiv hZ).trans f)
    ((AltWeakBalance.autPerm f hn h6).toMonoidHom.comp ((Lemma123.autQ K).comp B.subtype))
    (fun b x => AltWeakBalance.autPerm_spec f hn h6 (Lemma123.autQ K b) (x : K ⧸ Subgroup.center K))
    {j | AltWeakBalance.autPerm f hn h6 b₀ j = j} ⟨fun b j hj => ?_, fun b hb1 j hj h => ?_⟩ hm hr24
    ((ncard_fix_eq _).trans hr) hnm
  · exact hfixeq b₀ hb₀ hb₀1' _ ⟨b, b.2, rfl⟩ j hj
  · have hQb1 : Lemma123.autQ K b ≠ 1 := fun h' =>
      hb1 (Subtype.ext (hQinj (h'.trans (map_one (Lemma123.autQ K)).symm)))
    exact hj (hfixeq _ ⟨b, b.2, rfl⟩ hQb1 b₀ hb₀ j h)

theorem spor1916_fi22 (hout : SporadicOuterLeTwo) (hbr : SporadicBridges) (hord : SporadicOrdersTable)
    (hFi : CFSG.RankThree.PartOne.Mult.SporadicKernelTrivial .Fi22 5) {k : ℕ} (hk : 2 ≤ k)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 5 K = ⊥)
    (hs : IsSporType .Fi22 (K ⧸ Subgroup.center K))
    (B : Subgroup (MulAut K)) (hB : IsElemAbelian 5 B) (hBc : Nat.card B = 5 ^ k) :
    Lemma129.Spor1916 5 k B := by
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hZ : Subgroup.center K = ⊥ := by
    have h := hFi K (K ⧸ Subgroup.center K) (QuotientGroup.mk' (Subgroup.center K))
      ⟨hs.some.trans (hbr .Fi22).some.symm⟩ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
      (by rw [QuotientGroup.ker_mk']; exact AltFacts2.isPGroup_center_of_core_eq_bot Nat.prime_five hO)
    rwa [QuotientGroup.ker_mk'] at h
  have eK : K ≃* K ⧸ Subgroup.center K := quotCenterEquiv hZ
  haveI hKs : IsSimpleGroup K := eK.isSimpleGroup
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Prop1116Design.not_isCommutative_barQuot K hq
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have h' := congrArg eK h
    simpa [map_mul] using h'
  have hsK : IsSporType .Fi22 K := ⟨eK.trans hs.some⟩
  have houtK : Nat.card (Outer K) ≤ 2 := hout K hKs hnab .Fi22 hsK
  have hinn : ∀ x : MulAut K, x ^ 5 = 1 → x ∈ innerAut K := fun x hx =>
    mem_innerAut_of_pow_prime Nat.prime_five (by norm_num) houtK hx
  have hcardK : Nat.card K = 64561751654400 := by
    rw [Nat.card_congr hsK.some.toEquiv, hord .Fi22]
    rfl
  have hInn : Nat.card (innerAut K) ∣ Nat.card K := by
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : K →* MulAut K)).toEquiv
    show Nat.card (MulAut.conj : K →* MulAut K).range ∣ Nat.card K
    rw [← e]
    exact Subgroup.card_quotient_dvd_card _
  have hle : ∀ A : Subgroup (MulAut K), IsElemAbelian 5 A → Nat.card A ≤ 5 ^ 2 := by
    intro A hA
    have hAI : A ≤ innerAut K := fun a ha => hinn a (hA.2 a ha)
    have hdvd : Nat.card A ∣ 64561751654400 := hcardK ▸ (Subgroup.card_dvd_of_le hAI).trans hInn
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨j, hj⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
    rw [hj] at hdvd ⊢
    have hj2 : j ≤ 2 := by
      by_contra h
      push Not at h
      have h3 : 5 ^ 3 ∣ 64561751654400 := (pow_dvd_pow 5 h).trans hdvd
      norm_num at h3
    exact Nat.pow_le_pow_right (by norm_num) hj2
  have hk2 : k = 2 := by
    have h := hle B hB
    rw [hBc] at h
    have : k ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
    omega
  subst hk2
  refine ⟨rfl, rfl, hsK, fun b hb => hinn b (hB.2 b hb), ?_⟩
  intro B' hB' hB'c D hD H _ _
  have hB'25 : Nat.card B' = 5 ^ 2 := le_antisymm (hle B' hB') hB'c
  have hDB' : D = B' := Subgroup.eq_of_le_of_card_ge hD.1 (by rw [hB'25, hD.2.2])
  rw [← hDB']
  exact localDeltaTwoIn_commutator_eq_bot H D

theorem spor_case (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive)
    (h04s : LocalTwoBalanceSporadicGtFive) (hout : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hord : SporadicOrdersTable) (hFi : CFSG.RankThree.PartOne.Mult.SporadicKernelTrivial .Fi22 5)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥) {s : TauCeti.SporadicName}
    (hs : IsSporType s (K ⧸ Subgroup.center K))
    (B : Subgroup (MulAut K)) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ k) :
    IsLocallyOTwoBalanced p k B ∨ Lemma129.Spor1916 p k B := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot K hq
  by_cases hexc : p = 5 ∧ s = .Fi22
  · obtain ⟨rfl, rfl⟩ := hexc
    exact Or.inr (spor1916_fi22 hout hbr hord hFi hk hq hO hs B hB hBc)
  · have h2 : IsLocallyBalancedAbs p 2 (K ⧸ Subgroup.center K) := by
      rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
      · exact h03.sporadicThree s _ hq.2 hnab hs
      · exact h03.sporadicFive s (fun h => hexc ⟨rfl, h⟩) _ hq.2 hnab hs
      · exact h04s _ hq.2 hnab s hs p hp h5
    exact Or.inl (Lemma123.isLocallyOTwoBalanced_of_le hp (by norm_num) hk
      (Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hq.1 (isLocallyOTwoBalancedWrtP_of_abs hp hp2 h2) B hB))

theorem lie_case (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (hd3 : LocalTwoBalanceDefCharThree) (hd5 : LocalTwoBalanceDefCharFive) (hd7 : LocalTwoBalanceDefCharGtFive)
    (hLp : Input19_16Lp) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (B : Subgroup (MulAut K)) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ k) :
    IsLocallyOTwoBalanced p k B ∨ Lemma129.Lie1916 p k B := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot K hq
  have htr : ∀ k', IsLocallyOTwoBalancedWrtP p k' (K ⧸ Subgroup.center K) → IsLocallyOTwoBalanced p k' B :=
    fun k' h => Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hq.1 h B hB
  obtain ⟨h3, h2⟩ := lie_balance h02 h03 h04 hd3 hd5 hd7 hp hp2 hq.2 hnab idx he
  by_cases hch : idx.1.characteristic = p
  · exact Or.inl (Lemma123.isLocallyOTwoBalanced_of_le hp (by norm_num) hk (htr 2 (h2 (Or.inl hch))))
  by_cases hk3 : 3 ≤ k
  · exact Or.inl (Lemma123.isLocallyOTwoBalanced_of_le hp (by norm_num) hk3 (htr 3 (h3 hch)))
  have hk2 : k = 2 := by omega
  subst hk2
  by_cases hL : ∃ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie idx').Group)
  · by_cases hbal : IsLocallyOTwoBalanced p 2 B
    · exact Or.inl hbal
    · exact Or.inr (hLp p hp hp2 K hq hO hL B hB hBc hbal)
  · exact Or.inl (htr 2 (h2 (Or.inr fun idx' h => not_nonempty_iff.1 fun hn => hL ⟨idx', h, hn⟩)))

theorem input19_16Main_of_ys (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (h04s : LocalTwoBalanceSporadicGtFive) (hd3 : LocalTwoBalanceDefCharThree)
    (hd5 : LocalTwoBalanceDefCharFive) (hd7 : LocalTwoBalanceDefCharGtFive) (hout : SporadicOuterLeTwo)
    (hbr : SporadicBridges) (hord : SporadicOrdersTable)
    (hFi : CFSG.RankThree.PartOne.Mult.SporadicKernelTrivial .Fi22 5) (hLp : Input19_16Lp) :
    Lemma129.Input19_16Main := by
  intro p k hp hp2 hk K _ _ hKG hq hO B hB hBc
  obtain ⟨hnab, i, ⟨f⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.I1420.catalog_of_quasisimple hq hKG
  rcases i with ⟨p', hp'⟩ | ⟨n, hn⟩ | idx | s
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    apply hxy
    apply f.injective
    rw [map_mul, map_mul]
    have : ∀ x y : Multiplicative (ZMod p'), x * y = y * x := fun x y => mul_comm x y
    exact this _ _
  · rcases alt_case hp hp2 hk hq hO hn f B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases lie_case h02 h03 h04 hd3 hd5 hd7 hLp hp hp2 hk hq hO idx ⟨f⟩ B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases spor_case h03 h04s hout hbr hord hFi hp hp2 hk hq hO ⟨f⟩ B hB hBc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

section Closed

set_option linter.unusedSectionVars false

theorem input19_16Main_of_LpC
    (hC : Input19_16LpC) : Lemma129.Input19_16Main :=
  input19_16Main_of_ys crossCharBalance_holds.1 crossCharBalance_holds.2.1 crossCharBalance_holds.2.2
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.localTwoBalanceSporadicGtFive_of_open_rows
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.sporadicTwoPairHolds_Fi24Prime_seven
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.oPrimeCoreLeTwoAt_B_seven
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.sporadicTwoPairHolds_M_thirteen)
    CFSG.HardMathSupport.Solomon.Coordinator.localTwoBalanceDefCharThree_holds
    CFSG.HardMathSupport.Solomon.Coordinator.localTwoBalanceDefCharFive_holds
    (HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceDefCharGtFive_of_dFourImage
        HardMathSupport.Timmesfeld.DFour.dFourPrimeCentralizerInImage_holds)
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.sporadicKernelTrivial_fi22_five
    (input19_16Lp_of_C hC)

end Closed

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS
