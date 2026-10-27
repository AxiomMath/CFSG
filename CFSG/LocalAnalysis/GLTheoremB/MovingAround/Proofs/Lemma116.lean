module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop112

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups Pointwise

namespace Lemma116

@[expose] def Input23_6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p n : ℕ), p.Prime → p ≠ 2 → p < n → ¬ p ∣ n →
    ∀ (B K : Subgroup X), IsSCp p ⊤ B → 3 ≤ CFSG.Open.pRank p B →
      IsComponentOf K ⊤ → Nonempty (↥K ≃* ↥(alternatingGroup (Fin n))) →
      B ⊓ Subgroup.centralizer ((⨆ g ∈ B, GLBConj g K : Subgroup X) : Set X) ≠ ⊥ →
        K ≤ CFSG.Open.GLBCore p 2 B ∨
          ∃ r δ : ℕ, 2 ≤ r ∧ 1 ≤ δ ∧ δ < p ∧ n = p ^ r + δ ∧ CFSG.Open.pRank p B = r + 1 ∧
            (B ⊓ K) ⊓ (B ⊓ Subgroup.centralizer ((⨆ g ∈ B, GLBConj g K : Subgroup X) : Set X)) = ⊥ ∧
            ∃ e1 : ↥K, (e1 : X) ∈ B ∧ e1 ≠ 1 ∧
              ∃ ψ : ↥K ≃* ↥(alternatingGroup (Fin n)),
                (ψ e1).1.cycleType = Multiset.replicate (p ^ (r - 1)) p

@[expose] def Input23_6gt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p n : ℕ), p.Prime → p ≠ 2 → n < p →
    ∀ (B K : Subgroup X), IsSCp p ⊤ B → 3 ≤ CFSG.Open.pRank p B →
      IsComponentOf K ⊤ → Nonempty (↥K ≃* ↥(alternatingGroup (Fin n))) →
      B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ → K ≤ CFSG.Open.GLBCore p 2 B

section Perm

open Equiv Equiv.Perm Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

theorem card_support_of_mem {π : Perm α} {p s : ℕ} (h : π.cycleType = Multiset.replicate s p)
    {c : Perm α} (hc : c ∈ π.cycleFactorsFinset) : c.support.card = p := by
  have hmem : c.support.card ∈ π.cycleType := by
    rw [cycleType_def]
    exact Multiset.mem_map.2 ⟨c, by simpa using hc, rfl⟩
  rw [h] at hmem
  exact Multiset.eq_of_mem_replicate hmem

theorem card_cycleFactorsFinset_of {π : Perm α} {p s : ℕ}
    (h : π.cycleType = Multiset.replicate s p) :
    π.cycleFactorsFinset.card = s := by
  have h1 : π.cycleType.card = π.cycleFactorsFinset.card := by
    rw [cycleType_def, Multiset.card_map, Finset.card_val]
  rw [← h1, h, Multiset.card_replicate]

theorem card_support_eq_of {π : Perm α} {p s : ℕ} (h : π.cycleType = Multiset.replicate s p) :
    π.support.card = s * p := by
  rw [← sum_cycleType, h, Multiset.sum_replicate, smul_eq_mul, mul_comm]

theorem exists_fixed_of_card_lt {π : Perm α} {p s : ℕ} (h : π.cycleType = Multiset.replicate s p)
    (hlt : s * p < Fintype.card α) : ∃ w : α, π w = w := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset α) ⊆ π.support := fun x _ => by
    rw [mem_support]; exact hcon x
  have h2 := Finset.card_le_card hsub
  rw [card_support_eq_of h, Finset.card_univ] at h2
  omega

theorem card_closure_ge {p : ℕ} (hp : p.Prime) :
    ∀ C : Finset (Perm α), (∀ c ∈ C, IsCycle c ∧ c.support.card = p) →
      (C : Set (Perm α)).Pairwise Disjoint →
      p ^ C.card ≤ Nat.card (Subgroup.closure (C : Set (Perm α))) := by
  intro C
  induction C using Finset.induction_on with
  | empty => intro _ _; simp
  | insert c C hcC ih =>
    intro hC hdisj
    have hC' : ∀ d ∈ C, IsCycle d ∧ d.support.card = p :=
      fun d hd => hC d (Finset.mem_insert_of_mem hd)
    have hmemC : ∀ d ∈ C, d ∈ (↑(insert c C) : Set (Perm α)) := fun d hd => by simp [hd]
    have hmemc : c ∈ (↑(insert c C) : Set (Perm α)) := by simp
    have hdisj' : (C : Set (Perm α)).Pairwise Disjoint := by
      intro x hx y hy hxy
      exact hdisj (hmemC x hx) (hmemC y hy) hxy
    have hH := ih hC' hdisj'
    have hcyc : IsCycle c := (hC c (Finset.mem_insert_self _ _)).1
    have hcard : c.support.card = p := (hC c (Finset.mem_insert_self _ _)).2
    have hord : orderOf c = p := by rw [hcyc.orderOf, hcard]
    have hfix : ∀ g ∈ Subgroup.closure (C : Set (Perm α)), ∀ x ∈ c.support, g x = x := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => ∀ x ∈ c.support, g x = x) ?_ ?_ ?_ ?_ hg
      · intro d hd x hx
        have hdc : Disjoint c d := hdisj hmemc (hmemC d hd) (fun h => hcC (h ▸ hd))
        rcases hdc x with h1 | h1
        · exact absurd h1 (mem_support.1 hx)
        · exact h1
      · intro x _; rfl
      · intro a b _ _ ha hb x hx
        simp [ha x hx, hb x hx]
      · intro a _ ha x hx
        exact (Equiv.Perm.inv_eq_iff_eq).2 (ha x hx).symm
    obtain ⟨x0, hx0⟩ := hcyc.nonempty_support
    have hcp : c ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
    have hinj : Function.Injective (fun q : Subgroup.closure (C : Set (Perm α)) × Fin p =>
        (⟨(q.1 : Perm α) * c ^ (q.2 : ℕ), by
          apply Subgroup.mul_mem _ (Subgroup.closure_mono (Set.subset_insert _ _) q.1.2)
          exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _⟩ :
          Subgroup.closure (insert c C : Set (Perm α)))) := by
      rintro ⟨h, k⟩ ⟨h', k'⟩ heq
      have heq' : (h : Perm α) * c ^ (k : ℕ) = (h' : Perm α) * c ^ (k' : ℕ) :=
        congrArg Subtype.val heq
      have hk := k.2
      have hk' := k'.2
      have hinv : (c ^ (k : ℕ))⁻¹ = c ^ (p - (k : ℕ)) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hk), hcp]
      have hg0 : (h' : Perm α)⁻¹ * (h : Perm α) = c ^ (k' : ℕ) * (c ^ (k : ℕ))⁻¹ := by
        calc (h' : Perm α)⁻¹ * (h : Perm α)
            = (h' : Perm α)⁻¹ * ((h : Perm α) * c ^ (k : ℕ)) * (c ^ (k : ℕ))⁻¹ := by group
          _ = (h' : Perm α)⁻¹ * ((h' : Perm α) * c ^ (k' : ℕ)) * (c ^ (k : ℕ))⁻¹ := by
              rw [heq']
          _ = c ^ (k' : ℕ) * (c ^ (k : ℕ))⁻¹ := by group
      have hg : (h' : Perm α)⁻¹ * (h : Perm α) = c ^ ((k' : ℕ) + (p - (k : ℕ))) := by
        rw [hg0, hinv, pow_add]
      have hgfix : ∀ x ∈ c.support, (c ^ ((k' : ℕ) + (p - (k : ℕ)))) x = x := by
        intro x hx
        rw [← hg]
        exact hfix _ (mul_mem (inv_mem h'.2) h.2) x hx
      have hpow : c ^ ((k' : ℕ) + (p - (k : ℕ))) = 1 := by
        rw [IsCycle.pow_eq_one_iff hcyc]
        exact ⟨x0, mem_support.1 hx0, hgfix x0 hx0⟩
      have hkk : (k : ℕ) = (k' : ℕ) := by
        have hlt1 : (k' : ℕ) + (p - (k : ℕ)) < 2 * p := by omega
        have hdvd' : p ∣ (k' : ℕ) + (p - (k : ℕ)) := by
          have := orderOf_dvd_of_pow_eq_one hpow
          rwa [hord] at this
        obtain ⟨t, ht⟩ := hdvd'
        have ht2 : t < 2 := by
          by_contra hcon
          push_neg at hcon
          have : p * 2 ≤ p * t := Nat.mul_le_mul_left p hcon
          omega
        interval_cases t <;> omega
      have hkeq : k = k' := Fin.ext hkk
      subst hkeq
      have hone : (h' : Perm α)⁻¹ * (h : Perm α) = 1 := by
        rw [hg, Nat.add_sub_of_le (Nat.le_of_lt hk), hcp]
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.1 hone).symm) rfl
    have hcard_le := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_fin] at hcard_le
    rw [Finset.card_insert_of_notMem hcC, pow_succ, Finset.coe_insert]
    calc p ^ C.card * p ≤ Nat.card (Subgroup.closure (C : Set (Perm α))) * p :=
          Nat.mul_le_mul_right _ hH
      _ ≤ _ := hcard_le

theorem three_cycle_mem_closure (w : α) (g : Perm α) (hg : g.IsThreeCycle) :
    g ∈ Subgroup.closure {σ : Perm α | σ.IsThreeCycle ∧ w ∈ σ.support} := by
  by_cases hw : w ∈ g.support
  · exact Subgroup.subset_closure ⟨hg, hw⟩
  · obtain ⟨a, ha⟩ := hg.isCycle.nonempty_support
    have hdec := (hg.eq_swap_mul_swap_iff_mem_support).2 ha
    have hsupp := (hg.support_eq_iff_mem_support).2 ha
    have hnd := (hg.nodup_iff_mem_support (a := a)).2 ha
    obtain ⟨hA, hBC⟩ := List.nodup_cons.1 hnd
    obtain ⟨hB, -⟩ := List.nodup_cons.1 hBC
    have hab : a ≠ g a := fun h => hA (List.mem_cons.2 (Or.inl h))
    have hac : a ≠ g (g a) := fun h => hA (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h))))
    have hbc : g a ≠ g (g a) := fun h => hB (List.mem_singleton.2 h)
    rw [hsupp] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    obtain ⟨hwa, hwb, hwc⟩ := hw
    set b := g a with hb
    set c := g (g a) with hc
    have hA3 : (swap b a * swap b w).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same (Ne.symm hab) (Ne.symm hwb) (Ne.symm hwa)
    have hB3 : (swap b c * swap b w).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same hbc (Ne.symm hwb) (Ne.symm hwc)
    have wA : w ∈ (swap b a * swap b w).support := by
      rw [mem_support, mul_apply, swap_apply_right, swap_apply_left]
      exact fun h => hwa h.symm
    have wB : w ∈ (swap b c * swap b w).support := by
      rw [mem_support, mul_apply, swap_apply_right, swap_apply_left]
      exact fun h => hwc h.symm
    have hkey : g = (swap b a * swap b w) * (swap b c * swap b w)⁻¹ := by
      rw [mul_inv_rev, swap_inv, swap_inv]
      rw [← mul_assoc (swap b a * swap b w) (swap b w) (swap b c),
        mul_assoc (swap b a) (swap b w) (swap b w), swap_mul_self, mul_one, hdec, swap_comm a b]
    rw [hkey]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨hA3, wA⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨hB3, wB⟩))

theorem closure_threeCycles_through (w : α) :
    Subgroup.closure {σ : Perm α | σ.IsThreeCycle ∧ w ∈ σ.support} = alternatingGroup α := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro σ hσ
    exact IsThreeCycle.mem_alternatingGroup hσ.1
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    exact three_cycle_mem_closure w g hg

theorem exists_cycle_avoiding {C : Finset (Perm α)} (hdisj : (C : Set (Perm α)).Pairwise Disjoint)
    (hC3 : 3 ≤ C.card) (x y : α) : ∃ c ∈ C, x ∉ c.support ∧ y ∉ c.support := by
  classical
  have hAx : (C.filter (fun c => x ∈ c.support)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    by_contra hne
    have ha' := Finset.mem_filter.1 ha
    have hb' := Finset.mem_filter.1 hb
    rcases hdisj (Finset.mem_coe.2 ha'.1) (Finset.mem_coe.2 hb'.1) hne x with h1 | h1
    · exact (mem_support.1 ha'.2) h1
    · exact (mem_support.1 hb'.2) h1
  have hAy : (C.filter (fun c => y ∈ c.support)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    by_contra hne
    have ha' := Finset.mem_filter.1 ha
    have hb' := Finset.mem_filter.1 hb
    rcases hdisj (Finset.mem_coe.2 ha'.1) (Finset.mem_coe.2 hb'.1) hne y with h1 | h1
    · exact (mem_support.1 ha'.2) h1
    · exact (mem_support.1 hb'.2) h1
  set Ax := C.filter (fun c => x ∈ c.support) with hAxdef
  set Ay := C.filter (fun c => y ∈ c.support) with hAydef
  obtain ⟨c, hc1, hc2⟩ : ∃ c ∈ C, c ∉ Ax ∪ Ay := by
    by_contra hcon
    push_neg at hcon
    have h1 := Finset.card_le_card (show C ⊆ Ax ∪ Ay from fun c hc => hcon c hc)
    have h2 := Finset.card_union_le Ax Ay
    omega
  have hc : c ∈ C ∧ c ∉ Ax ∪ Ay := ⟨hc1, hc2⟩
  refine ⟨c, hc.1, fun hxc => hc.2 (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc.1, hxc⟩)),
    fun hyc => hc.2 (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hc.1, hyc⟩))⟩


end Perm

section Group

variable {G : Type} [Group G]

theorem isElemAbelian_le {p : ℕ} {X Z : Subgroup G} (hX : CFSG.Open.IsElemAbelian p X)
    (hZ : Z ≤ X) : CFSG.Open.IsElemAbelian p Z :=
  CFSG.Open.IsElemAbelian.mono hX hZ

theorem isElemAbelian_closure_of_comm {H : Type} [Group H] {p : ℕ} (S : Set H)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) (hp : ∀ s ∈ S, s ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.closure S) := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_centralizer_iff.2 (fun t ht => hS t ht s hs)
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set H) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_centralizer_iff.2
      (fun y hy => (Subgroup.mem_centralizer_iff.1 (h1 hy) s hs).symm)
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x ^ p = 1) ?_ ?_ ?_ ?_ hx
  · intro s hs
    exact hp s hs
  · simp
  · intro a b ha hb hpa hpb
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, hpa, hpb, one_mul]
  · intro a _ ha
    rw [inv_pow, ha, inv_one]

theorem exists_sub_card [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : CFSG.Open.IsElemAbelian p X) {j : ℕ} (hj : p ^ j ≤ Nat.card X) :
    ∃ Z : Subgroup G, Z ≤ X ∧ CFSG.Open.IsElemAbelian p Z ∧ Nat.card Z = p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian' hX).exists_card_eq
  have hjm : j ≤ m := by
    rw [hm] at hj
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hj
  obtain ⟨Z0, hZ0⟩ := Sylow.exists_subgroup_card_pow_prime p (n := j)
    (by rw [hm]; exact pow_dvd_pow p hjm)
  refine ⟨Z0.map X.subtype, Subgroup.map_subtype_le _, isElemAbelian_le hX (Subgroup.map_subtype_le _), ?_⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact hZ0

theorem exists_isSCp_above [Finite G] {p : ℕ} {Y : Subgroup G} (hY : CFSG.Open.IsElemAbelian p Y) :
    ∃ H : Subgroup G, IsSCp p ⊤ H ∧ Y ≤ H := by
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image
    {H : Subgroup G | Y ≤ H ∧ CFSG.Open.IsElemAbelian p H} (fun H => Nat.card H)
    (Set.toFinite _) ⟨Y, le_rfl, hY⟩
  refine ⟨H, ⟨le_top, hH.2, fun E _ hEab hHE => ?_⟩, hH.1⟩
  have hE : E ∈ {H : Subgroup G | Y ≤ H ∧ CFSG.Open.IsElemAbelian p H} := ⟨hH.1.trans hHE, hEab⟩
  exact (Subgroup.eq_of_le_of_card_ge hHE (hmax E hE)).symm

theorem glbCore_mono [Finite G] {p k : ℕ} {P P' : Subgroup G} (h : P ≤ P') :
    CFSG.Open.GLBCore p k P ≤ CFSG.Open.GLBCore p k P' := by
  unfold CFSG.Open.GLBCore
  apply sSup_le_sSup
  rintro N ⟨Q, hQP, hk, rfl⟩
  exact ⟨Q, hQP.trans h, hk, rfl⟩

theorem le_centralizer_of_le {A U W : Subgroup G} (hAU : A ≤ Subgroup.centralizer (U : Set G))
    (hWU : W ≤ U) : A ≤ Subgroup.centralizer (W : Set G) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
  exact (Subgroup.mem_centralizer_iff.1 (hAU hx)) y (hWU hy)

theorem le_centralizer_of_abelian {p : ℕ} {A Z : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A)
    (hZ : Z ≤ A) : A ≤ Subgroup.centralizer (Z : Set G) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
  exact elemAbelian_comm hA (hZ hy) hx

open Classical in
noncomputable def subRank [Finite G] (p k : ℕ) (U : Subgroup G) : Subgroup G :=
  if h : ∃ Z : Subgroup G, Z ≤ U ∧ CFSG.Open.IsElemAbelian p Z ∧ Nat.card Z = p ^ k then
    h.choose else ⊥

theorem subRank_spec [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hU : CFSG.Open.IsElemAbelian p U) {k : ℕ} (hk : p ^ k ≤ Nat.card U) :
    subRank p k U ≤ U ∧ CFSG.Open.IsElemAbelian p (subRank p k U) ∧
      Nat.card (subRank p k U) = p ^ k := by
  have h := exists_sub_card hp hU hk
  unfold subRank
  rw [dif_pos h]
  exact h.choose_spec

theorem isKConnectedIn_lower [Finite G] {p : ℕ} (hp : p.Prime) {j k : ℕ} (hkj : k ≤ j)
    {X A B : Subgroup G} (h : IsKConnectedIn p j X A B) : IsKConnectedIn p k X A B := by
  obtain ⟨hA, hAab, hAc, hB, hBab, hBc, hcase⟩ := h
  have hpk : p ^ k ≤ p ^ j := Nat.pow_le_pow_right hp.pos hkj
  refine ⟨hA, hAab, hpk.trans hAc, hB, hBab, hpk.trans hBc, ?_⟩
  rcases hcase with hAB | ⟨U, V, hU, hV, hAU, hrt, hVB⟩
  · exact Or.inl hAB
  · have hstep : ∀ W Y : Subgroup G, IsKConnStep p j X W Y →
        IsKConnStep p k X (subRank p k W) (subRank p k Y) := by
      rintro W Y ⟨hW, hY, hWY⟩
      have hkW : p ^ k ≤ Nat.card W := by rw [hW.2.2]; exact hpk
      have hkY : p ^ k ≤ Nat.card Y := by rw [hY.2.2]; exact hpk
      obtain ⟨hW1, hW2, hW3⟩ := subRank_spec hp hW.2.1 hkW
      obtain ⟨hY1, hY2, hY3⟩ := subRank_spec hp hY.2.1 hkY
      refine ⟨⟨hW1.trans hW.1, hW2, hW3⟩, ⟨hY1.trans hY.1, hY2, hY3⟩, ?_⟩
      exact le_centralizer_of_le ((hW1.trans hWY)) hY1
    have hkU : p ^ k ≤ Nat.card U := by rw [hU.2.2]; exact hpk
    have hkV : p ^ k ≤ Nat.card V := by rw [hV.2.2]; exact hpk
    obtain ⟨hU1, hU2, hU3⟩ := subRank_spec hp hU.2.1 hkU
    obtain ⟨hV1, hV2, hV3⟩ := subRank_spec hp hV.2.1 hkV
    refine Or.inr ⟨subRank p k U, subRank p k V, ⟨hU1.trans hU.1, hU2, hU3⟩,
      ⟨hV1.trans hV.1, hV2, hV3⟩, le_centralizer_of_le hAU hU1,
      Relation.ReflTransGen.lift (subRank p k) (fun _ _ hab => hstep _ _ hab) U V hrt, ?_⟩
    exact hV1.trans hVB

theorem isKConnStep_mono {p k : ℕ} {X X' W Y : Subgroup G} (hXX' : X ≤ X')
    (h : IsKConnStep p k X W Y) : IsKConnStep p k X' W Y :=
  ⟨⟨h.1.1.trans hXX', h.1.2.1, h.1.2.2⟩, ⟨h.2.1.1.trans hXX', h.2.1.2.1, h.2.1.2.2⟩, h.2.2⟩

theorem isKConnectedIn_extend [Finite G] {p : ℕ} (hp : p.Prime) {j : ℕ} {X X' A U A' U' : Subgroup G}
    (hXX' : X ≤ X') (hAch : IsKConnectedIn p j X A U) (hAA' : A ≤ A') (hUU' : U ≤ U')
    (hA' : CFSG.Open.IsElemAbelian p A') (hU' : CFSG.Open.IsElemAbelian p U')
    (hA'card : p ^ j ≤ Nat.card A') (hU'card : p ^ j ≤ Nat.card U')
    (hA'X : A' ≤ X') (hU'X : U' ≤ X') : IsKConnectedIn p j X' A' U' := by
  obtain ⟨hA, hAab, hAc, hU, hUab, hUc, hcase⟩ := hAch
  obtain ⟨hZA1, hZA2, hZA3⟩ := subRank_spec hp hAab hAc
  obtain ⟨hZU1, hZU2, hZU3⟩ := subRank_spec hp hUab hUc
  have hEkA : IsEkIn p j X' (subRank p j A) := ⟨hZA1.trans (hA.trans hXX'), hZA2, hZA3⟩
  have hEkU : IsEkIn p j X' (subRank p j U) := ⟨hZU1.trans (hU.trans hXX'), hZU2, hZU3⟩
  have hA'C : A' ≤ Subgroup.centralizer ((subRank p j A : Subgroup G) : Set G) :=
    le_centralizer_of_abelian hA' (hZA1.trans hAA')
  have hZUC : subRank p j U ≤ Subgroup.centralizer (U' : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.2
      (fun y hy => elemAbelian_comm hU' hy (hUU' (hZU1 hx)))
  refine ⟨hA'X, hA', hA'card, hU'X, hU', hU'card, Or.inr ⟨subRank p j A, subRank p j U, hEkA, hEkU,
    hA'C, ?_, hZUC⟩⟩
  rcases hcase with hAU | ⟨U1, V, hU1, hV, hAU1, hrt, hVU⟩
  · exact Relation.ReflTransGen.single
      ⟨hEkA, hEkU, le_centralizer_of_le (hZA1.trans hAU) hZU1⟩
  · have hU1' : IsEkIn p j X' U1 := ⟨hU1.1.trans hXX', hU1.2.1, hU1.2.2⟩
    have hV' : IsEkIn p j X' V := ⟨hV.1.trans hXX', hV.2.1, hV.2.2⟩
    have hstepA : IsKConnStep p j X' (subRank p j A) U1 :=
      ⟨hEkA, hU1', hZA1.trans hAU1⟩
    have hstepV : IsKConnStep p j X' V (subRank p j U) :=
      ⟨hV', hEkU, le_centralizer_of_le hVU hZU1⟩
    exact Relation.ReflTransGen.head hstepA
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.mono (r := IsKConnStep p j X) (p := IsKConnStep p j X')
          (fun (a b : Subgroup G) (h : IsKConnStep p j X a b) => isKConnStep_mono hXX' h) U1 V hrt)
        hstepV)

theorem two_le_pRank_pair {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {a b : H}
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hind : ∀ i j : ℕ, a ^ i = b ^ j → a ^ i = 1) :
    2 ≤ CFSG.Open.pRank p (Subgroup.closure ({a, b} : Set H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : ∀ x : H, x ^ p = 1 → x ≠ 1 → ∀ m : ℕ, x ^ m = 1 → p ∣ m := by
    intro x hx hx1 m hm
    rw [← orderOf_eq_prime hx hx1]
    exact orderOf_dvd_of_pow_eq_one hm
  have hnat : ∀ x y : ℕ, x < p → y < p → p ∣ (p - x) + y → x = y := by
    intro x y hx hy hdvd
    obtain ⟨t, ht⟩ := hdvd
    have ht2 : t < 2 := by
      by_contra hcon
      push_neg at hcon
      have : p * 2 ≤ p * t := Nat.mul_le_mul_left p hcon
      omega
    interval_cases t <;> omega
  have hS : ∀ s ∈ ({a, b} : Set H), ∀ t ∈ ({a, b} : Set H), s * t = t * s := by
    intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rfl
    · exact hab
    · exact hab.symm
    · rfl
  have hSp : ∀ s ∈ ({a, b} : Set H), s ^ p = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ha
    · exact hb
  have hQab := isElemAbelian_closure_of_comm ({a, b} : Set H) hS hSp
  set Q := Subgroup.closure ({a, b} : Set H) with hQ
  have hmemQ : ∀ x : H, x ∈ ({a, b} : Set H) → x ∈ Q := fun x hx => Subgroup.subset_closure hx
  let φ : Fin p × Fin p → Q := fun q =>
    ⟨a ^ (q.1 : ℕ) * b ^ (q.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (hmemQ a (by simp)) _)
        (Subgroup.pow_mem _ (hmemQ b (by simp)) _)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (i' : ℕ) * b ^ (j' : ℕ) := congrArg Subtype.val h
    have hi := i.2
    have hj := j.2
    have hi' := i'.2
    have hj' := j'.2
    have hA : (a ^ (i' : ℕ))⁻¹ = a ^ (p - (i' : ℕ)) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, Nat.add_sub_of_le hi'.le, ha]
    have hB : (b ^ (j : ℕ))⁻¹ = b ^ (p - (j : ℕ)) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, Nat.add_sub_of_le hj.le, hb]
    have hkey : (a ^ (i' : ℕ))⁻¹ * a ^ (i : ℕ) = b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹ := by
      calc (a ^ (i' : ℕ))⁻¹ * a ^ (i : ℕ)
          = (a ^ (i' : ℕ))⁻¹ * (a ^ (i : ℕ) * b ^ (j : ℕ)) * (b ^ (j : ℕ))⁻¹ := by group
        _ = (a ^ (i' : ℕ))⁻¹ * (a ^ (i' : ℕ) * b ^ (j' : ℕ)) * (b ^ (j : ℕ))⁻¹ := by rw [h']
        _ = b ^ (j' : ℕ) * (b ^ (j : ℕ))⁻¹ := by group
    have key : a ^ ((p - (i' : ℕ)) + (i : ℕ)) = b ^ ((j' : ℕ) + (p - (j : ℕ))) := by
      rw [pow_add, ← hA, pow_add, ← hB]
      exact hkey
    have h1 : a ^ ((p - (i' : ℕ)) + (i : ℕ)) = 1 := hind _ _ key
    have h2 : b ^ ((p - (j : ℕ)) + (j' : ℕ)) = 1 := by
      rw [Nat.add_comm]
      rw [← key, h1]
    have hia : (i' : ℕ) = (i : ℕ) := hnat _ _ hi' hi (hord a ha ha1 _ h1)
    have hjb : (j : ℕ) = (j' : ℕ) := hnat _ _ hj hj' (hord b hb hb1 _ h2)
    exact Prod.ext (Fin.ext hia.symm) (Fin.ext hjb)
  have hcard : p * p ≤ Nat.card Q := by
    have := Nat.card_le_card_of_injective φ hinj
    simpa [Nat.card_prod, Nat.card_fin] using this
  obtain ⟨Z, hZQ, hZab, hZcard⟩ := exists_sub_card hp hQab (j := 2) (by rw [pow_two]; exact hcard)
  exact CFSG.SectionRank.le_pRank hp.one_lt hZQ hZab hZcard

theorem le_twoLocalRank [Finite G] {p : ℕ} (hp : p.Prime) {M : Subgroup G} (hM : IsTwoLocal M)
    {S : Subgroup G} (hSM : S ≤ M) (hS : CFSG.Open.IsElemAbelian p S) {k : ℕ}
    (hk : Nat.card S = p ^ k) : k ≤ GLATwoLocalRank p G := by
  have h1 : k ≤ CFSG.Open.pRank p M := CFSG.SectionRank.le_pRank hp.one_lt hSM hS hk
  have hbdd : BddAbove {k' | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k'} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k' ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card G := by
      rw [← hE]
      exact Subgroup.card_le_card_group E
    exact (Nat.lt_pow_self hp.one_lt).le.trans h2
  have h2 : CFSG.Open.pRank p M ≤ CFSG.Open.twoLocalPrimeRank p G :=
    le_csSup hbdd ⟨M, hM, rfl⟩
  exact h1.trans h2

end Group

theorem mem_normalizer_closure_of_comm {H : Type} [Group H] (S : Set H) (x : H)
    (hx : ∀ s ∈ S, x * s = s * x) :
    x ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup H) : Set H) := by
  have hfix : ∀ y : H, (∀ s ∈ S, Commute y s) → ∀ h ∈ Subgroup.closure S, Commute y h := by
    intro y hy h hh
    refine Subgroup.closure_induction (p := fun h _ => Commute y h) ?_ ?_ ?_ ?_ hh
    · exact hy
    · exact Commute.one_right y
    · intro a b _ _ ha hb
      exact ha.mul_right hb
    · intro a _ ha
      exact ha.inv_right
  have hx' : ∀ s ∈ S, Commute x s := hx
  have hxinv : ∀ s ∈ S, Commute x⁻¹ s := fun s hs => (hx' s hs).inv_left
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e1 : x * h * x⁻¹ = h := by
      rw [(hfix x hx' h hh).eq, mul_inv_cancel_right]
    rw [e1]
    exact hh
  · intro hh
    have e2 : x⁻¹ * (x * h * x⁻¹) * x = x * h * x⁻¹ := by
      rw [(hfix x⁻¹ hxinv _ hh).eq]
      group
    rw [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at e2
    rw [e2]
    exact hh

theorem core_gamma {Cb : Type} [Group Cb] [Finite Cb] {p n s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Kb : Subgroup Cb) (ψ : ↥Kb ≃* ↥(alternatingGroup (Fin n)))
    (ē : Cb) (hēc : ∀ g : Cb, ē * g = g * ē) (hēo : ē ^ p = 1) (hē1 : ē ≠ 1)
    (hēK : ∀ i : ℕ, ∀ x : Cb, x ∈ Kb → ē ^ i = x → ē ^ i = 1)
    (e1 : ↥Kb) (hcyc : (ψ e1).1.cycleType = Multiset.replicate s p)
    (hs3 : 3 ≤ s) (hn : s * p < n) :
    ∃ P : Subgroup Cb, CFSG.Open.IsElemAbelian p P ∧ p ^ s ≤ Nat.card P ∧
      P ≤ Subgroup.centralizer ({(e1 : Cb)} : Set Cb) ∧ Kb ≤ CFSG.Open.GLBCore p 2 P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let ι : ↥Kb →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp ψ.toMonoidHom
  have hι_inj : Function.Injective ι := fun x y hxy =>
    ψ.injective (Subtype.ext (show ((ψ x : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) =
      ((ψ y : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) from hxy))
  have hι_mem : ∀ x : ↥Kb, ι x ∈ alternatingGroup (Fin n) := fun x => (ψ x).2
  have hι_surj : ∀ y ∈ alternatingGroup (Fin n), ∃ x : ↥Kb, ι x = y := by
    intro y hy
    exact ⟨ψ.symm ⟨y, hy⟩, by simp [ι]⟩
  set π : Equiv.Perm (Fin n) := ι e1 with hπ
  set C : Finset (Equiv.Perm (Fin n)) := π.cycleFactorsFinset with hC
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hCc : ∀ c ∈ C, c.IsCycle ∧ c.support.card = p := fun c hc =>
    ⟨(Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1, card_support_of_mem hcyc hc⟩
  have hCcard : C.card = s := card_cycleFactorsFinset_of hcyc
  have hCdisj : (C : Set (Equiv.Perm (Fin n))).Pairwise Equiv.Perm.Disjoint :=
    Equiv.Perm.cycleFactorsFinset_pairwise_disjoint π
  have hCalt : ∀ c ∈ C, c ∈ alternatingGroup (Fin n) := by
    intro c hc
    rw [Equiv.Perm.mem_alternatingGroup, (hCc c hc).1.sign, (hCc c hc).2, Odd.neg_one_pow hodd,
      neg_neg]
  have hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    by_cases h : c = c'
    · rw [h]
    · exact (hCdisj (Finset.mem_coe.2 hc) (Finset.mem_coe.2 hc') h).commute
  have hCpow : ∀ c ∈ C, c ^ p = 1 := by
    intro c hc
    rw [← (hCc c hc).2, ← (hCc c hc).1.orderOf]
    exact pow_orderOf_eq_one c
  have hCne : ∀ c ∈ C, c ≠ 1 := by
    intro c hc h1
    have := (hCc c hc).2
    rw [h1] at this
    simp at this
    exact hp.ne_zero this.symm
  set Kc : Set ↥Kb := {x | ι x ∈ C} with hKc
  have hKc_surj : ∀ c ∈ C, ∃ x ∈ Kc, ι x = c := by
    intro c hc
    obtain ⟨x, hx⟩ := hι_surj c (hCalt c hc)
    exact ⟨x, by simp [hKc, hx, hc], hx⟩
  have hKc_image : ι '' Kc = (C : Set (Equiv.Perm (Fin n))) := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Finset.mem_coe.2 hx
    · intro hc
      obtain ⟨x, hx, hxc⟩ := hKc_surj c (Finset.mem_coe.1 hc)
      exact ⟨x, hx, hxc⟩
  have hKc_comm : ∀ x ∈ Kc, ∀ y ∈ Kc, x * y = y * x := by
    intro x hx y hy
    apply hι_inj
    rw [map_mul, map_mul]
    exact hCcomm _ hx _ hy
  have hKc_pow : ∀ x ∈ Kc, x ^ p = 1 := by
    intro x hx
    apply hι_inj
    rw [map_pow, map_one]
    exact hCpow _ hx
  have hKc_ne : ∀ x ∈ Kc, x ≠ 1 := by
    intro x hx h1
    apply hCne (ι x) hx
    rw [h1, map_one]
  set Kset : Set Cb := (Kb.subtype) '' Kc with hKset
  set P : Subgroup Cb := Subgroup.closure (insert ē Kset) with hP
  have hPab : CFSG.Open.IsElemAbelian p P := by
    apply isElemAbelian_closure_of_comm
    · intro u hu v hv
      rcases hu with rfl | ⟨x, hx, rfl⟩ <;> rcases hv with rfl | ⟨y, hy, rfl⟩
      · rfl
      · exact hēc _
      · exact (hēc _).symm
      · have := hKc_comm x hx y hy
        exact congrArg Subtype.val this
    · intro u hu
      rcases hu with rfl | ⟨x, hx, rfl⟩
      · exact hēo
      · have := hKc_pow x hx
        rw [← map_pow, this, map_one]
  have hPK_card : p ^ s ≤ Nat.card (Subgroup.closure Kc) := by
    have hinj : Function.Injective ι := hι_inj
    have h1 : Nat.card ((Subgroup.closure Kc).map ι) = Nat.card (Subgroup.closure Kc) :=
      Subgroup.card_map_of_injective hι_inj
    rw [← h1, MonoidHom.map_closure, hKc_image]
    have := card_closure_ge hp C hCc hCdisj
    rw [hCcard] at this
    exact this
  have hPK_P : Nat.card (Subgroup.closure Kc) ≤ Nat.card P := by
    have hle : (Subgroup.closure Kc).map Kb.subtype ≤ P := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono (Set.subset_insert _ _)
    have h1 : Nat.card ((Subgroup.closure Kc).map Kb.subtype) = Nat.card (Subgroup.closure Kc) :=
      Subgroup.card_map_of_injective Kb.subtype_injective
    rw [← h1]
    exact Subgroup.card_le_of_le hle
  have hPcent : P ≤ Subgroup.centralizer ({(e1 : Cb)} : Set Cb) := by
    rw [hP, Subgroup.closure_le]
    rintro u (rfl | ⟨x, hx, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hēc _
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hcomm : Commute (ι x) π :=
        Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute (ι x) π
          (fun c' hc' => hCcomm (ι x) hx c' hc')
      have h2 : x * e1 = e1 * x := by
        apply hι_inj
        rw [map_mul, map_mul]
        exact hcomm.eq
      exact congrArg Subtype.val h2
  obtain ⟨w, hw⟩ := exists_fixed_of_card_lt hcyc (by simpa using hn)
  have hwπ : w ∉ π.support := by
    rw [Equiv.Perm.mem_support, not_not]
    exact hw
  have hwC : ∀ c ∈ C, w ∉ c.support := fun c hc hwc =>
    hwπ (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hwc)
  set Tset : Set (Equiv.Perm (Fin n)) := {τ | τ.IsThreeCycle ∧ w ∈ τ.support} with hTset
  have hT_gen : Subgroup.closure Tset = alternatingGroup (Fin n) :=
    closure_threeCycles_through w
  set Tk : Set ↥Kb := {x | ι x ∈ Tset} with hTk
  have hTset_alt : ∀ τ ∈ Tset, τ ∈ alternatingGroup (Fin n) :=
    fun τ hτ => hτ.1.mem_alternatingGroup
  have hTk_image : ι '' Tk = Tset := by
    ext τ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hτ
      obtain ⟨x, hx⟩ := hι_surj τ (hTset_alt τ hτ)
      exact ⟨x, show ι x ∈ Tset from by rw [hx]; exact hτ, hx⟩
  have hmap : (Subgroup.closure Tk).map ι = Subgroup.closure Tset := by
    rw [MonoidHom.map_closure, hTk_image]
  have hall : ∀ x : ↥Kb, x ∈ Subgroup.closure Tk := by
    intro x
    have h1 : ι x ∈ (Subgroup.closure Tk).map ι := by
      rw [hmap, hT_gen]
      exact hι_mem x
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 h1
    have hzx' : z = x := hι_inj hzx
    rw [← hzx']
    exact hz
  have claim1 : ∀ x ∈ Tk, ((x : ↥Kb) : Cb) ∈ CFSG.Open.GLBCore p 2 P := by
    intro x hx
    have hx' : ι x ∈ Tset := hx
    obtain ⟨h3, hwτ⟩ := hx'
    have hE : ((ι x).support.erase w).card = 2 := by
      rw [Finset.card_erase_of_mem hwτ, h3.card_support]
    obtain ⟨a, b, hab, hEq⟩ := Finset.card_eq_two.1 hE
    have hmemτ : ∀ y, y ∈ (ι x).support → y = w ∨ y = a ∨ y = b := by
      intro y hy
      by_cases hyw : y = w
      · exact Or.inl hyw
      · have hy2 : y ∈ (ι x).support.erase w := Finset.mem_erase.2 ⟨hyw, hy⟩
        rw [hEq] at hy2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy2
        exact Or.inr hy2
    have ha : a ∈ (ι x).support.erase w := by rw [hEq]; simp
    have hb : b ∈ (ι x).support.erase w := by rw [hEq]; simp
    obtain ⟨c, hc, hac, hbc⟩ := exists_cycle_avoiding hCdisj (by rw [hCcard]; exact hs3) a b
    obtain ⟨xc, hxc, hιxc⟩ := hKc_surj c hc
    have hdisj : Equiv.Perm.Disjoint c (ι x) := by
      intro y
      by_cases hy : y ∈ c.support
      · right
        by_contra hne
        have hyτ : y ∈ (ι x).support := Equiv.Perm.mem_support.2 hne
        rcases hmemτ y hyτ with h | h | h
        · exact hwC c hc (h ▸ hy)
        · exact hac (h ▸ hy)
        · exact hbc (h ▸ hy)
      · left
        by_contra hne
        exact hy (Equiv.Perm.mem_support.2 hne)
    have hcommτ : Commute c (ι x) := hdisj.commute
    have hxcx : xc * x = x * xc := by
      apply hι_inj
      rw [map_mul, map_mul, hιxc]
      exact hcommτ.eq
    have hxcb_pow : (xc : Cb) ^ p = 1 := by
      have h := congrArg (fun z : ↥Kb => (z : Cb)) (hKc_pow xc hxc)
      simpa using h
    have hxcb_ne : (xc : Cb) ≠ 1 := fun h => hKc_ne xc hxc (Subtype.ext h)
    have hind : ∀ i j : ℕ, ē ^ i = (xc : Cb) ^ j → ē ^ i = 1 := by
      intro i j hij
      exact hēK i ((xc : Cb) ^ j) (Subgroup.pow_mem Kb xc.2 j) hij
    have hQrank : 2 ≤ CFSG.Open.pRank p (Subgroup.closure ({ē, (xc : Cb)} : Set Cb)) :=
      two_le_pRank_pair hp (hēc _) hēo hxcb_pow hē1 hxcb_ne hind
    have hQP : Subgroup.closure ({ē, (xc : Cb)} : Set Cb) ≤ P := by
      rw [hP]
      apply Subgroup.closure_mono
      intro u hu
      rcases hu with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ ⟨xc, hxc, rfl⟩
    have hxnorm : ((x : ↥Kb) : Cb) ∈
        Subgroup.normalizer ((Subgroup.closure ({ē, (xc : Cb)} : Set Cb) : Subgroup Cb) : Set Cb) := by
      apply mem_normalizer_closure_of_comm
      intro s hs
      rcases hs with h | h
      · rw [h]
        exact (hēc _).symm
      · rw [h]
        exact (congrArg Subtype.val hxcx).symm
    exact normalizer_le_glbCore hQP hQrank hxnorm
  have hKb : Kb ≤ CFSG.Open.GLBCore p 2 P := by
    intro g hg
    have hmem := hall ⟨g, hg⟩
    have hle : Subgroup.closure Tk ≤ (CFSG.Open.GLBCore p 2 P).comap Kb.subtype := by
      rw [Subgroup.closure_le]
      intro x hx
      exact claim1 x hx
    exact hle hmem
  exact ⟨P, hPab, le_trans hPK_card hPK_P, hPcent, hKb⟩

section Lift

variable {G : Type} [Group G]

theorem exists_lift [Finite G] {p : ℕ} (hp : p.Prime) {C T : Subgroup G} (hTC : T ≤ C)
    {Q : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hQ : Q ≤ barX p C T) (hQp : IsPGroup p Q) :
    ∃ S : Subgroup G, S ≤ T ∧ IsPGroup p S ∧ barX p C S = Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Γ : Subgroup ↥C := T.subgroupOf C
  let f : ↥Γ →* (↥C ⧸ GLAPPrimeCore p ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp Γ.subtype
  have hrange : f.range = barX p C T := by
    simp only [f, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hQf : Q ≤ f.range := hrange ▸ hQ
  let W : Subgroup ↥Γ := Q.comap f
  have hWQ : W.map f = Q := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hQf]
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  let φ : ↥W →* ↥Q := (f.comp W.subtype).codRestrict Q (fun w => w.2)
  have hφ : Function.Surjective φ := by
    intro q
    have hq : (q : (↥C ⧸ GLAPPrimeCore p ↥C)) ∈ W.map f := by
      rw [hWQ]; exact q.2
    obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨w, hw⟩, Subtype.ext hwq⟩
  have hdvd : Nat.card Q ∣ Nat.card ↥W := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
    exact Dvd.intro _ rfl
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p (n := k) (hk ▸ hdvd)
  let H : Subgroup ↥Γ := K.map W.subtype
  have hHcard : Nat.card ↥H = p ^ k := by
    rw [← hK, Subgroup.card_map_of_injective W.subtype_injective]
  have hcop : Nat.Coprime (p ^ k) (Nat.card (GLAPPrimeCore p ↥C)) :=
    Nat.Coprime.pow_left k (coprime_card_glaPPrimeCore C)
  have hHW : ∀ h ∈ H, h ∈ W := by
    intro h hh
    obtain ⟨w, _, rfl⟩ := Subgroup.mem_map.1 hh
    exact w.2
  have hHinj : ∀ h : ↥H, f h.1 = 1 → h = 1 := by
    intro h hfh
    have hy : Γ.subtype h.1 ∈ GLAPPrimeCore p ↥C := (QuotientGroup.eq_one_iff _).1 hfh
    have hpow : h.1 ^ (p ^ k) = 1 := by
      rw [← hHcard]
      have h3 : h ^ Nat.card ↥H = 1 := pow_card_eq_one'
      have h4 := congrArg Subtype.val h3
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h4
    have hpowC : (Γ.subtype h.1) ^ (p ^ k) = 1 := by
      rw [← map_pow, hpow, map_one]
    let z : ↥(GLAPPrimeCore p ↥C) := ⟨Γ.subtype h.1, hy⟩
    have hz1 : z ^ (p ^ k) = 1 := by
      apply Subtype.ext
      simpa [z] using hpowC
    have hz0 : z = 1 := by
      have hz2 : z ^ Nat.card ↥(GLAPPrimeCore p ↥C) = 1 := pow_card_eq_one'
      have := (pow_gcd_eq_one (a := z) (m := p ^ k) (n := Nat.card ↥(GLAPPrimeCore p ↥C))).2
        ⟨hz1, hz2⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    have hy1 : Γ.subtype h.1 = 1 := by
      have := congrArg Subtype.val hz0
      simpa [z] using this
    apply Subtype.ext
    apply Subtype.ext
    exact hy1
  have hfinj : Function.Injective (f.comp H.subtype) :=
    (injective_iff_map_eq_one (f.comp H.subtype)).2 (fun a ha => hHinj a ha)
  have hle : H.map f ≤ Q := by
    intro q hq
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hq
    exact (Subgroup.mem_comap).1 (hHW h hh)
  have hHQ : H.map f = Q := by
    have hr : H.map f = (f.comp H.subtype).range := by
      ext x
      constructor
      · intro hx
        obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hx
        exact ⟨⟨h, hh⟩, rfl⟩
      · rintro ⟨h, rfl⟩
        exact Subgroup.mem_map.2 ⟨h.1, h.2, rfl⟩
    have hcardmap : Nat.card (H.map f) = Nat.card ↥H := by
      rw [hr, Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardmap, hHcard, hk])
  let ιG : ↥Γ →* G := C.subtype.comp Γ.subtype
  have hιinj : Function.Injective ιG := C.subtype_injective.comp Γ.subtype_injective
  refine ⟨H.map ιG, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨h, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_subgroupOf.1 h.2
  · apply IsPGroup.of_card
    rw [Subgroup.card_map_of_injective hιinj, hHcard]
  · ext z
    rw [CFSG.HardMathSupport.Timmesfeld.Balance.mem_barX_iff p C (H.map ιG) z]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, hιh⟩ := Subgroup.mem_map.1 hx
      have hxh : x = Γ.subtype h := Subtype.ext hιh.symm
      rw [hxh]
      show f h ∈ Q
      rw [← hHQ]
      exact Subgroup.mem_map_of_mem f hh
    · intro hz
      rw [← hHQ] at hz
      obtain ⟨h, hh, hfh⟩ := Subgroup.mem_map.1 hz
      exact ⟨Γ.subtype h, Subgroup.mem_map.2 ⟨h, hh, rfl⟩, hfh⟩

end Lift

section Sylow

variable {G : Type} [Group G]

theorem exists_sylow_cover [Finite G] {p : ℕ} (hp : p.Prime) {M S B : Subgroup G}
    (hSM : S ≤ M) (hBM : B ≤ M) (hSp : IsPGroup p S) (hBp : IsPGroup p B) :
    ∃ y ∈ M, ∃ R : Subgroup G, S ≤ R ∧ GLBConj y B ≤ R ∧ IsPGroup p R := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS'p : IsPGroup p ↥(S.subgroupOf M) := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  have hB'p : IsPGroup p ↥(B.subgroupOf M) := hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm
  obtain ⟨QS, hQS⟩ := IsPGroup.exists_le_sylow hS'p
  obtain ⟨QB, hQB⟩ := IsPGroup.exists_le_sylow hB'p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M QB QS
  let R : Subgroup G := (QS : Subgroup ↥M).map M.subtype
  have hRp : IsPGroup p R := by
    obtain ⟨n, hn⟩ := (QS.isPGroup').exists_card_eq
    apply IsPGroup.of_card (n := n)
    rw [Subgroup.card_map_of_injective M.subtype_injective, hn]
  have hcoe : MulAut.conj g • (QB : Set ↥M) = (QS : Set ↥M) := by
    rw [← Sylow.coe_smul, hg]
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, R, ?_, ?_, hRp⟩
  · intro x hx
    have hxM : x ∈ M := hSM hx
    exact Subgroup.mem_map.2 ⟨⟨x, hxM⟩, hQS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · intro z hz
    simp only [GLBConj, inv_inv] at hz
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hz
    have hbQB : (⟨b, hBM hb⟩ : ↥M) ∈ (QB : Set ↥M) :=
      hQB (Subgroup.mem_subgroupOf.2 hb)
    have h2 : MulAut.conj g ⟨b, hBM hb⟩ ∈ (QS : Set ↥M) := by
      rw [← hcoe]
      exact Set.smul_mem_smul_set hbQB
    refine Subgroup.mem_map.2 ⟨MulAut.conj g ⟨b, hBM hb⟩, h2, ?_⟩
    simp

end Sylow

section Helpers

variable {G : Type} [Group G]

theorem card_eq_pow_pRank [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian' hE).exists_card_eq
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card hp hE hm, hm]

theorem succ_le_pow_pred {p r : ℕ} (hp3 : 3 ≤ p) (hr : 2 ≤ r) : r + 1 ≤ p ^ (r - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
  have key : ∀ t : ℕ, t + 3 ≤ p ^ (t + 1) := by
    intro t
    induction t with
    | zero => simpa using hp3
    | succ t ih =>
      rw [pow_succ]
      nlinarith
  have e : t + 2 - 1 = t + 1 := by omega
  rw [e]
  exact key t

theorem elemAbelian_of_barX_elemAbelian [Finite G] {p : ℕ} (hp : p.Prime) {C S : Subgroup G}
    (hSC : S ≤ C) (hS : IsPGroup p S) (hbar : CFSG.Open.IsElemAbelian p (barX p C S)) :
    CFSG.Open.IsElemAbelian p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := injective_barX_comp hp hS hSC
  have hmem : ∀ x (hx : x ∈ S),
      (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨x, hSC hx⟩ : ↥C)) ∈ barX p C S := fun x hx =>
    (CFSG.HardMathSupport.Timmesfeld.Balance.mem_barX_iff p C S _).2 ⟨⟨x, hSC hx⟩, hx, rfl⟩
  have hcomm : ∀ x (hx : x ∈ S) y (hy : y ∈ S), x * y = y * x := by
    intro x hx y hy
    let a : ↥(S.subgroupOf C) := ⟨⟨x, hSC hx⟩, Subgroup.mem_subgroupOf.2 hx⟩
    let b : ↥(S.subgroupOf C) := ⟨⟨y, hSC hy⟩, Subgroup.mem_subgroupOf.2 hy⟩
    have hc := elemAbelian_comm hbar (hmem x hx) (hmem y hy)
    have h2 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (S.subgroupOf C).subtype) (a * b) =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (S.subgroupOf C).subtype) (b * a) := by
      rw [map_mul, map_mul]
      exact hc
    have h3 := hinj h2
    have h4 := congrArg (fun z : ↥(S.subgroupOf C) => (z : ↥C).1) h3
    simpa using h4
  have hpow : ∀ x (hx : x ∈ S), x ^ p = 1 := by
    intro x hx
    let a : ↥(S.subgroupOf C) := ⟨⟨x, hSC hx⟩, Subgroup.mem_subgroupOf.2 hx⟩
    have h1 := hbar.2 _ (hmem x hx)
    have h2 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (S.subgroupOf C).subtype) (a ^ p) =
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (S.subgroupOf C).subtype) 1 := by
      rw [map_pow, map_one]
      exact h1
    have h3 := hinj h2
    have h4 := congrArg (fun z : ↥(S.subgroupOf C) => (z : ↥C).1) h3
    simpa using h4
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hpow x hx⟩

end Helpers

end Lemma116

section Main

open Lemma116 in
theorem lemma116_of_inputs (hI236 : Lemma116.Input23_6) (hI236gt : Lemma116.Input23_6gt)
    (hI319 : Input31_9) : Lemma116Statement := by
  intro G _ _ m p B M E A h a e ha ha1 he he1 K hK n hn hpn
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotK, hnotD⟩ := hcon
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hE𝒟 : inD p M E := h.pair.1.1
  have hA𝒟 : inDp p M A := h.pair.1.2.1
  obtain ⟨hEsc, hAsc⟩ := lemma104_ii_holds h.toSec10Fails h.pair
  have hEel : CFSG.Open.IsElemAbelian p E := hEsc.2.1
  have hAel : CFSG.Open.IsElemAbelian p A := hAsc.2.1
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian' hEel
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian' hAel
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have hEC : E ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hEel heE hx
  have hAC : A ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hAel heA hx
  have hE3 : 3 ≤ CFSG.Open.pRank p E := h.pair.1.1.1.2
  have hO : GLAPPrimeCoreOf p (Cg e) ≤ M := le_trans le_sup_left (h.pair.1.1.2.clause_a e heE he1)
  have hEM : GLBCore p 2 E ≤ M := hE𝒟.2.clause_d
  have hEM2 : IsTwoLocal M := hE𝒟.2.maxTwoLocal.1
  have hNC : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥(Cg e)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_glaPPrimeCore (Cg e))
  have he_Cg : e ∈ Cg e := Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
  have hebar_ne : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ≠ 1 := by
    intro h1
    have heO : e ∈ GLAPPrimeCoreOf p (Cg e) := (mem_glaPPrimeCoreOf_iff he_Cg).2 h1
    have hmem : e ∈ E ⊓ GLAPPrimeCoreOf p (Cg e) := ⟨heE, heO⟩
    rw [inf_O_eq_bot (C := Cg e) hEp] at hmem
    exact he1 (Subgroup.mem_bot.1 hmem)
  have hebar_central : ∀ g : (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)),
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) * g =
        g * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥(Cg e)) g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 x.2 e (Set.mem_singleton e)
  have hebar_pow : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ p = 1 := by
    have h1 : (⟨e, he_Cg⟩ : ↥(Cg e)) ^ p = 1 := Subtype.ext (by simpa using hEel.2 e heE)
    rw [← map_pow, h1, map_one]
  have hebar_mem : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
      barX p (Cg e) E :=
    (CFSG.HardMathSupport.Timmesfeld.Balance.mem_barX_iff p (Cg e) E _).2 ⟨⟨e, he_Cg⟩, heE, rfl⟩
  have hEbar_sc : IsSCp p ⊤ (barX p (Cg e) E) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥(Cg e)) hNC (isSCp_subgroupOf hEsc hEC)
  have hEbar_rank : CFSG.Open.pRank p (barX p (Cg e) E) = CFSG.Open.pRank p E :=
    rank_barX_of_isPGroup hp hEp hEC
  have hKbar_comp : GLAPComponent p (⊤ : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)))
      (barX p (Cg e) K) := glaPComponent_barX_top hp hK
  have hKbar_quasi : CFSG.Open.IsQuasisimple ↥(barX p (Cg e) K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hK.1 hK.2.1) (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK)
  have hKbar_comp' : IsComponentOf (barX p (Cg e) K) ⊤ := ⟨le_top, hKbar_comp.2.1, hKbar_quasi⟩
  have hKbar_iso : Nonempty (↥(barX p (Cg e) K) ≃* ↥(alternatingGroup (Fin n))) := by
    obtain ⟨f⟩ := hn
    exact ⟨(quotEquivBarX hp hK.1 hK.2.1).symm.trans f⟩
  have hbarE3 : 3 ≤ CFSG.Open.pRank p (barX p (Cg e) E) := by
    rw [hEbar_rank]
    exact hE3
  have hcentral : barX p (Cg e) E ⊓ Subgroup.centralizer
      ((⨆ g ∈ barX p (Cg e) E, GLBConj g (barX p (Cg e) K) : Subgroup _) : Set _) ≠ ⊥ := by
    intro hbot
    have hm := (show QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        barX p (Cg e) E ⊓ Subgroup.centralizer
          ((⨆ g ∈ barX p (Cg e) E, GLBConj g (barX p (Cg e) K) : Subgroup _) : Set _) from
      ⟨hebar_mem, Subgroup.mem_centralizer_iff.2 (fun x _ => (hebar_central x).symm)⟩)
    rw [hbot] at hm
    exact hebar_ne (Subgroup.mem_bot.1 hm)
  have hcentral' : barX p (Cg e) E ⊓ Subgroup.centralizer ((barX p (Cg e) K : Subgroup _) : Set _) ≠ ⊥ := by
    intro hbot
    have hm := (show QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        barX p (Cg e) E ⊓ Subgroup.centralizer ((barX p (Cg e) K : Subgroup _) : Set _) from
      ⟨hebar_mem, Subgroup.mem_centralizer_iff.2 (fun x _ => (hebar_central x).symm)⟩)
    rw [hbot] at hm
    exact hebar_ne (Subgroup.mem_bot.1 hm)
  have hnp : p ≠ n := fun hpn' => hpn (hpn' ▸ dvd_refl p)
  have hcase_i : barX p (Cg e) K ≤ GLBCore p 2 (barX p (Cg e) E) → False := by
    intro hL
    exact hnotK (le_of_barX_le_glbCore hp 2 hEp hEC hK.1
      (fun E' hE' hr' => (normalizer_le_glbCore hE' hr').trans hEM) hO hL)
  rcases Nat.lt_or_gt_of_ne hnp with hlt | hgt
  · rcases hI236 _ p n hp hp2 hlt hpn (barX p (Cg e) E) (barX p (Cg e) K) hEbar_sc hbarE3 hKbar_comp'
      hKbar_iso hcentral with hi | ⟨r, δ, hr2, hδ1, hδp, hnr, hrank, hdisj, e1', he1B, he1ne, ψ, hcyc⟩
    · exact hcase_i hi
    ·
      have hp3 : 3 ≤ p := by
        have h2 := hp.two_le
        rcases Nat.lt_or_ge p 3 with h3 | h3
        · exfalso; apply hp2; omega
        · exact h3
      have hodd : Odd p := hp.odd_of_ne_two hp2
      have hs3 : 3 ≤ p ^ (r - 1) := le_trans hp3 (Nat.le_self_pow (by omega) p)
      have hsn : p ^ (r - 1) * p < n := by
        have : p ^ (r - 1) * p = p ^ r := by
          rw [← pow_succ]
          congr 1
          omega
        rw [this, hnr]
        omega
      have hebar_hom : ∀ i : ℕ, ∀ x : (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)),
          x ∈ barX p (Cg e) K → (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i = x →
            (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i = 1 := by
        intro i x hxK hx
        have hcomm_i : ∀ g : (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)),
            Commute ((QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i) g :=
          fun g => Commute.pow_left (hebar_central g) i
        have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i ∈
            barX p (Cg e) E ⊓ Subgroup.centralizer ((⨆ g ∈ barX p (Cg e) E,
              GLBConj g (barX p (Cg e) K) : Subgroup _) : Set _) := by
          refine ⟨Subgroup.pow_mem _ hebar_mem i, ?_⟩
          exact Subgroup.mem_centralizer_iff.2 (fun y _ => (hcomm_i y).eq.symm)
        have hmem' : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i ∈
            barX p (Cg e) K := by
          rw [hx]; exact hxK
        have hall : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i ∈
            (barX p (Cg e) E ⊓ barX p (Cg e) K) ⊓ (barX p (Cg e) E ⊓ Subgroup.centralizer
              ((⨆ g ∈ barX p (Cg e) E, GLBConj g (barX p (Cg e) K) : Subgroup _) : Set _)) :=
          ⟨⟨hmem.1, hmem'⟩, hmem⟩
        rw [hdisj] at hall
        exact Subgroup.mem_bot.1 hall
      obtain ⟨P, hPab, hPcard, hPcent, hKP⟩ := Lemma116.core_gamma hp hp2 (barX p (Cg e) K) ψ
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)))
        hebar_central hebar_pow hebar_ne (fun i x hx hi => hebar_hom i x hx hi) e1' hcyc hs3 hsn
      obtain ⟨e1g, he1gC, he1gE, hmk⟩ : ∃ e1g : G, ∃ hC : e1g ∈ Cg e, e1g ∈ E ∧
          QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e1g, hC⟩ : ↥(Cg e)) = e1' := by
        obtain ⟨xe, hxeE, hxe⟩ := (CFSG.HardMathSupport.Timmesfeld.Balance.mem_barX_iff p (Cg e) E e1').1
          he1B
        exact ⟨xe, xe.2, hxeE, hxe⟩
      have he1g_ne : e1g ≠ 1 := by
        intro h1
        apply he1ne
        apply Subtype.ext
        rw [← hmk, Subgroup.coe_one]
        subst h1
        exact map_one _
      have he1gp : e1g ^ p = 1 := hEel.2 e1g he1gE
      have hbarC : barX p (Cg e) (Cg e) = ⊤ := by
        ext z
        simp only [Subgroup.mem_top, iff_true]
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥(Cg e)) z
        exact (CFSG.HardMathSupport.Timmesfeld.Balance.mem_barX_iff p (Cg e) (Cg e) _).2
          ⟨x, x.2, rfl⟩
      have hPT : P ≤ barX p (Cg e) (Cg e ⊓ Subgroup.centralizer ({e1g} : Set G)) := by
        have hbar := barX_inf_centralizer hp he1gC (le_refl (Cg e))
          (Subgroup.le_normalizer he1gC) (isPGroup_of_isElemAbelian' (isElemAbelian_zpowers_of_mem hEel he1gE))
        rw [hbarC, top_inf_eq] at hbar
        rw [hbar]
        have hmk' : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e1g, he1gC⟩ : ↥(Cg e)) = e1' := hmk
        rw [hmk']
        exact hPcent
      obtain ⟨S, hST, hSp, hSbar⟩ := Lemma116.exists_lift hp (inf_le_left : Cg e ⊓ Subgroup.centralizer ({e1g} : Set G) ≤ Cg e) hPT (isPGroup_of_isElemAbelian' hPab)
      have hSC : S ≤ Cg e := hST.trans inf_le_left
      have hSab : CFSG.Open.IsElemAbelian p S :=
        Lemma116.elemAbelian_of_barX_elemAbelian hp hSC hSp (by rw [hSbar]; exact hPab)
      have hScard : p ^ (p ^ (r - 1)) ≤ Nat.card S := by
        rw [← card_barX_of_le hp hSC hSp, hSbar]
        exact hPcard
      have hS_comm_e : ∀ x ∈ S, x * e = e * x := fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hST hx).1 e (Set.mem_singleton e)).symm
      have hS_comm_e1 : ∀ x ∈ S, x * e1g = e1g * x := fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hST hx).2 e1g (Set.mem_singleton e1g)).symm
      have hepE : e ^ p = 1 := hEel.2 e heE
      have hcommEE : e * e1g = e1g * e := elemAbelian_comm hEel heE he1gE
      have hind : ∀ i j : ℕ, e ^ i = e1g ^ j → e ^ i = 1 := by
        intro i j hij
        have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e))) ^ i =
            (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e1g, he1gC⟩ : ↥(Cg e))) ^ j := by
          rw [← map_pow, ← map_pow]
          congr 1
          apply Subtype.ext
          simp only [Subgroup.coe_pow]
          exact hij
        rw [hmk] at h1
        have h2 := hebar_hom i ((e1' : (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) ^ j)
          (Subgroup.pow_mem _ e1'.2 j) h1
        have hei : e ^ i ∈ Cg e := Subgroup.pow_mem _ he_Cg i
        have h3 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e ^ i, hei⟩ : ↥(Cg e)) = 1 := by
          rw [← map_pow] at h2
          exact h2
        have h4 : e ^ i ∈ GLAPPrimeCoreOf p (Cg e) := (mem_glaPPrimeCoreOf_iff hei).2 h3
        have h5 : e ^ i ∈ E ⊓ GLAPPrimeCoreOf p (Cg e) := ⟨Subgroup.pow_mem _ heE i, h4⟩
        rw [inf_O_eq_bot (C := Cg e) hEp] at h5
        exact Subgroup.mem_bot.1 h5
      have hS_le_M : S ≤ M := by
        intro x hx
        have hxN : x ∈ Subgroup.normalizer ((Subgroup.closure ({e, e1g} : Set G) : Subgroup G) : Set G) := by
          apply Lemma116.mem_normalizer_closure_of_comm
          intro t ht
          rcases ht with h' | h'
          · rw [h']
            exact hS_comm_e x hx
          · rw [h']
            exact hS_comm_e1 x hx
        have hQE : Subgroup.closure ({e, e1g} : Set G) ≤ E := by
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with h' | h'
          · rw [h']
            exact heE
          · rw [h']
            exact he1gE
        have hQr : 2 ≤ CFSG.Open.pRank p (Subgroup.closure ({e, e1g} : Set G)) :=
          Lemma116.two_le_pRank_pair hp hcommEE hepE he1gp he1 he1g_ne hind
        exact hEM (normalizer_le_glbCore hQE hQr hxN)
      obtain ⟨F, hFS, hFab, hFcard⟩ := Lemma116.exists_sub_card hp hSab (j := p ^ (r - 1)) hScard
      have hFM : F ≤ M := hFS.trans hS_le_M
      have hsTLR : p ^ (r - 1) ≤ GLATwoLocalRank p G :=
        Lemma116.le_twoLocalRank hp hEM2 hFM hFab hFcard
      have hBD : inD p M B := lemma101_ii_holds h.toSec10Fails
      have hBM : B ≤ M := hBD.1.1.1
      obtain ⟨hBab, hBcard, -⟩ := h.bOne.1
      have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hBab
      obtain ⟨y, hyM, R, hSR, hBR, hRp⟩ := Lemma116.exists_sylow_cover hp hS_le_M hBM hSp hBp
      have hB'D : inD p M (GLBConj y B) :=
        (lemma101_i_holds h.toSec10Fails hyM hBD h.pair.1.2.1).1
      have hB'ab : CFSG.Open.IsElemAbelian p (GLBConj y B) := hB'D.1.1.2.1
      have hB'card : Nat.card (GLBConj y B) = p ^ GLATwoLocalRank p G := by
        rw [← hBcard]
        unfold GLBConj
        exact Subgroup.card_map_of_injective (MulAut.conj _).injective
      have hcardB' : p ^ (p ^ (r - 1)) ≤ Nat.card (GLBConj y B) := by
        rw [hB'card]
        exact Nat.pow_le_pow_right hp.pos hsTLR
      obtain ⟨U, hUB, hUab, hUcard⟩ := Lemma116.exists_sub_card hp hB'ab hcardB'
      have hnot : ¬ (p = 3 ∧ r = 2) := by
        rintro ⟨rfl, rfl⟩
        have h4 := lemma113_i_of_104v (lemma104_v_of_input31_8 input31_8_holds) h ha ha1 hnotD
        omega
      have hFek : IsEkIn p (p ^ (r - 1)) R F := ⟨hFS.trans hSR, hFab, hFcard⟩
      have hUek : IsEkIn p (p ^ (r - 1)) R U := ⟨hUB.trans hBR, hUab, hUcard⟩
      have hRconn : IsKConnectedIn p (r + 1) R F U :=
        hI319 G p r hp hp2 hr2 hnot R hRp F U hFek hUek
      have hk_le : CFSG.Open.pRank p (E ⊓ A) ≤ r := by
        by_contra hcon
        push_neg at hcon
        have hle : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p E :=
          CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left
        have hEr : CFSG.Open.pRank p E = r + 1 := by omega
        have hpr : CFSG.Open.pRank p (E ⊓ A) = r + 1 := by omega
        obtain ⟨Z, hZ, hZab, hZc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (E ⊓ A)
        rw [hpr] at hZc
        have hEc : Nat.card E = p ^ (r + 1) := by
          rw [Lemma116.card_eq_pow_pRank hp hEel, hEr]
        have hZE : Z = E := Subgroup.eq_of_le_of_card_ge (hZ.trans inf_le_left)
          (by rw [hEc, hZc])
        have hEA : E ≤ A := by
          have h6 := hZ.trans inf_le_right
          rw [hZE] at h6
          exact h6
        have hAE : A = E := hE𝒟.1.1.2.2 A hA𝒟.1.1.1 hAel hEA
        exact hA𝒟.2 (by rw [hAE]; exact hE𝒟.2)
      have hk1 : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ r + 1 := by omega
      have hconnk := Lemma116.isKConnectedIn_lower hp hk1 hRconn
      obtain ⟨Es, hEsSC, hS_Es⟩ := Lemma116.exists_isSCp_above hSab
      have hcardEs : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ Nat.card Es := by
        have h1 : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ p ^ (p ^ (r - 1)) :=
          Nat.pow_le_pow_right hp.pos (hk1.trans (Lemma116.succ_le_pow_pred hp3 hr2))
        exact h1.trans (hScard.trans (Subgroup.card_le_of_le hS_Es))
      have hcardB'' : p ^ (CFSG.Open.pRank p (E ⊓ A) + 1) ≤ Nat.card (GLBConj y B) := by
        refine le_trans ?_ hcardB'
        exact Nat.pow_le_pow_right hp.pos (hk1.trans (Lemma116.succ_le_pow_pred hp3 hr2))
      have hconnE : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ Es (GLBConj y B) :=
        Lemma116.isKConnectedIn_extend hp le_top hconnk (hFS.trans hS_Es) hUB hEsSC.2.1 hB'ab hcardEs
          hcardB'' le_top le_top
      have hEsD : inD p M Es := lemma104_iii_holds h.toSec10Fails h.pair hEsSC hB'D hconnE
      have hGS_M : GLBCore p 2 S ≤ M := (Lemma116.glbCore_mono hS_Es).trans hEsD.2.clause_d
      have hK' : barX p (Cg e) K ≤ GLBCore p 2 (barX p (Cg e) S) := by
        rw [hSbar]
        exact hKP
      have hK_le : K ≤ GLBCore p 2 S ⊔ GLAPPrimeCoreOf p (Cg e) :=
        le_of_barX_le_glbCore hp 2 hSp hSC hK.1
          (fun E' hE' hr' => (normalizer_le_glbCore hE' hr').trans le_sup_left) le_sup_right hK'
      exact hnotK (hK_le.trans (sup_le hGS_M hO))
  · have hi := hI236gt _ p n hp hp2 hgt (barX p (Cg e) E) (barX p (Cg e) K) hEbar_sc hbarE3 hKbar_comp'
      hKbar_iso hcentral'
    exact hcase_i hi

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
