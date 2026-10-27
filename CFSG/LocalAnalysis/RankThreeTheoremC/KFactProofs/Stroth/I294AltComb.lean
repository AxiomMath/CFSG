module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem altComb_pow_val_add {G : Type*} [Group G] {p : ℕ} [NeZero p] {g : G}
    (hg : g ^ p = 1) (a b : ZMod p) : g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

private theorem altComb_fix_left {α : Type*} {A B C : Equiv.Perm α} (h : A * B * C = 1) {b : α}
    (hB : B b = b) (hC : C b = b) : A b = b := by
  have h1 := congrArg (fun g : Equiv.Perm α => g b) h
  simpa [Equiv.Perm.mul_apply, hB, hC] using h1

private theorem altComb_fix_mid {α : Type*} {A B C : Equiv.Perm α} (h : A * B * C = 1) {b : α}
    (hA : A b = b) (hC : C b = b) : B b = b := by
  have h1 : A (B b) = b := by
    have := congrArg (fun g : Equiv.Perm α => g b) h
    simpa [Equiv.Perm.mul_apply, hC] using this
  exact A.injective (h1.trans hA.symm)

private theorem altComb_fix_right {α : Type*} {A B C : Equiv.Perm α} (h : A * B * C = 1) {b : α}
    (hA : A b = b) (hB : B b = b) : C b = b := by
  have h1 : A (B (C b)) = b := by
    have := congrArg (fun g : Equiv.Perm α => g b) h
    simpa [Equiv.Perm.mul_apply] using this
  have h2 : B (C b) = b := A.injective (h1.trans hA.symm)
  exact B.injective (h2.trans hB.symm)

private theorem altComb_eq_one_of_pow_val {G : Type*} [Group G] {p : ℕ} [NeZero p] {g : G}
    (hord : orderOf g = p) {y : Multiplicative (ZMod p)} (h : g ^ y.toAdd.val = 1) : y = 1 := by
  have hd : orderOf g ∣ y.toAdd.val := orderOf_dvd_of_pow_eq_one h
  rw [hord] at hd
  have h0 : y.toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h0
  exact toAdd_eq_zero.mp h0

private theorem altComb_exists_fun_three {n : ℕ} {P : Equiv.Perm (Fin n) → Prop}
    {u v w : Equiv.Perm (Fin n)} (hu : P u) (hv : P v) (hw : P w)
    (huv : Equiv.Perm.Disjoint u v) (huw : Equiv.Perm.Disjoint u w)
    (hvw : Equiv.Perm.Disjoint v w) :
    ∃ s : Fin 3 → Equiv.Perm (Fin n), (∀ i, P (s i)) ∧
      ∀ i j, i ≠ j → Equiv.Perm.Disjoint (s i) (s j) := by
  refine ⟨![u, v, w], fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    exacts [hu, hv, hw]
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact huv | exact huv.symm | exact huw | exact huw.symm | exact hvw | exact hvw.symm

private theorem altComb_exists_pcycle {n p : ℕ} (hp2 : 2 ≤ p) {S : Finset (Fin n)}
    (hS : p ≤ S.card) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ σ.support.card = p ∧ σ.support ⊆ S := by
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  have hl : T.toList.Nodup := Finset.nodup_toList T
  have hlen : T.toList.length = p := by rw [Finset.length_toList, hTcard]
  have hn : 2 ≤ T.toList.length := by omega
  have hnt : ∀ x : Fin n, T.toList ≠ [x] := by
    intro x h
    rw [h, List.length_singleton] at hlen
    omega
  have hsupp : (T.toList.formPerm).support = T := by
    rw [List.support_formPerm_of_nodup _ hl hnt, Finset.toList_toFinset]
  refine ⟨T.toList.formPerm, List.isCycle_formPerm hl hn, ?_, ?_⟩
  · rw [hsupp, hTcard]
  · rw [hsupp]
    exact hTS

private theorem altComb_exists_three_pcycles {n p : ℕ} (hp : p.Prime) (hn : 3 * p ≤ n)
    {x : Equiv.Perm (Fin n)} (hxo : orderOf x = p) (hx1 : x ≠ 1) :
    ∃ s : Fin 3 → Equiv.Perm (Fin n),
      (∀ i, (s i).IsCycle ∧ (s i).support.card = p ∧ Commute x (s i)) ∧
        ∀ i j, i ≠ j → Equiv.Perm.Disjoint (s i) (s j) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hCcard : ∀ c ∈ x.cycleFactorsFinset, c.support.card = p := by
    intro c hc
    have hmem : c.support.card ∈ x.cycleType := by
      rw [Equiv.Perm.cycleType_def]
      exact Multiset.mem_map_of_mem _ (Finset.mem_val.mpr hc)
    have hd := Equiv.Perm.dvd_of_mem_cycleType hmem
    rw [hxo] at hd
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hmem
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · exact h
  have hCsum : x.support.card = x.cycleFactorsFinset.card * p := by
    have hmap : x.cycleFactorsFinset.1.map (Finset.card ∘ Equiv.Perm.support)
        = x.cycleFactorsFinset.1.map (fun _ => p) :=
      Multiset.map_congr rfl (fun c hc => hCcard c (Finset.mem_val.mp hc))
    rw [← Equiv.Perm.sum_cycleType, Equiv.Perm.cycleType_def, hmap, Multiset.map_const',
      Multiset.sum_replicate, smul_eq_mul]
    rfl
  have hCpos : 0 < x.cycleFactorsFinset.card := by
    rcases Nat.eq_zero_or_pos x.cycleFactorsFinset.card with h | h
    · exfalso
      apply hx1
      have hsupp : x.support.card = 0 := by rw [hCsum, h, zero_mul]
      exact Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hsupp)
    · exact h
  have hCcyc : ∀ c ∈ x.cycleFactorsFinset, c.IsCycle := fun c hc =>
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  have hCcomm : ∀ c ∈ x.cycleFactorsFinset, Commute x c := fun c hc =>
    (Equiv.Perm.self_mem_cycle_factors_commute hc).symm
  have hCsub : ∀ c ∈ x.cycleFactorsFinset, c.support ⊆ x.support := fun c hc =>
    Equiv.Perm.mem_cycleFactorsFinset_support_le hc
  have hCdisj : ∀ c ∈ x.cycleFactorsFinset, ∀ c' ∈ x.cycleFactorsFinset, c ≠ c' →
      Equiv.Perm.Disjoint c c' := fun c hc c' hc' hne =>
    Equiv.Perm.cycleFactorsFinset_pairwise_disjoint x hc hc' hne
  have hFcard : x.supportᶜ.card = n - x.cycleFactorsFinset.card * p := by
    rw [Finset.card_compl, Fintype.card_fin, hCsum]
  have hFdisj : ∀ σ : Equiv.Perm (Fin n), σ.support ⊆ x.supportᶜ → Equiv.Perm.Disjoint x σ := by
    intro σ hσ
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro y
    by_cases hy : σ y = y
    · exact Or.inr hy
    · left
      have hy'' := hσ (Equiv.Perm.mem_support.mpr hy)
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy''
      exact hy''
  have hFcomm : ∀ σ : Equiv.Perm (Fin n), σ.support ⊆ x.supportᶜ → Commute x σ :=
    fun σ hσ => (hFdisj σ hσ).commute
  have hCFdisj : ∀ c ∈ x.cycleFactorsFinset, ∀ σ : Equiv.Perm (Fin n),
      σ.support ⊆ x.supportᶜ → Equiv.Perm.Disjoint c σ := by
    intro c hc σ hσ
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Finset.disjoint_of_subset_left (hCsub c hc)
      (Finset.disjoint_of_subset_right hσ _root_.disjoint_compl_right)
  rcases (show x.cycleFactorsFinset.card = 1 ∨ x.cycleFactorsFinset.card = 2 ∨
      3 ≤ x.cycleFactorsFinset.card by omega) with h1 | h2 | h3
  ·
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have haC : a ∈ x.cycleFactorsFinset := by rw [ha]; exact Finset.mem_singleton_self a
    obtain ⟨σ, hσc, hσcard, hσsub⟩ := altComb_exists_pcycle hp2
      (S := x.supportᶜ) (by rw [hFcard, h1]; omega)
    obtain ⟨τ, hτc, hτcard, hτsub⟩ := altComb_exists_pcycle hp2
      (S := x.supportᶜ \ σ.support)
      (by rw [Finset.card_sdiff_of_subset hσsub, hFcard, h1, hσcard]; omega)
    have hτsub' : τ.support ⊆ x.supportᶜ := hτsub.trans Finset.sdiff_subset
    refine altComb_exists_fun_three (P := fun σ : Equiv.Perm (Fin n) =>
      σ.IsCycle ∧ σ.support.card = p ∧ Commute x σ) (u := a) (v := σ) (w := τ)
      ⟨hCcyc a haC, hCcard a haC, hCcomm a haC⟩
      ⟨hσc, hσcard, hFcomm σ hσsub⟩ ⟨hτc, hτcard, hFcomm τ hτsub'⟩
      (hCFdisj a haC σ hσsub) (hCFdisj a haC τ hτsub') ?_
    exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Finset.disjoint_of_subset_right hτsub Finset.disjoint_sdiff)
  ·
    obtain ⟨a, b, hab, hC2⟩ := Finset.card_eq_two.mp h2
    have haC : a ∈ x.cycleFactorsFinset := by rw [hC2]; simp
    have hbC : b ∈ x.cycleFactorsFinset := by rw [hC2]; simp
    obtain ⟨σ, hσc, hσcard, hσsub⟩ := altComb_exists_pcycle hp2
      (S := x.supportᶜ) (by rw [hFcard, h2]; omega)
    exact altComb_exists_fun_three (P := fun σ : Equiv.Perm (Fin n) =>
      σ.IsCycle ∧ σ.support.card = p ∧ Commute x σ) (u := a) (v := b) (w := σ)
      ⟨hCcyc a haC, hCcard a haC, hCcomm a haC⟩
      ⟨hCcyc b hbC, hCcard b hbC, hCcomm b hbC⟩ ⟨hσc, hσcard, hFcomm σ hσsub⟩
      (hCdisj a haC b hbC hab) (hCFdisj a haC σ hσsub) (hCFdisj b hbC σ hσsub)
  ·
    have h3' : 2 < x.cycleFactorsFinset.card := by omega
    obtain ⟨a, haC, b, hbC, c, hcC, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3'
    exact altComb_exists_fun_three (P := fun σ : Equiv.Perm (Fin n) =>
      σ.IsCycle ∧ σ.support.card = p ∧ Commute x σ) (u := a) (v := b) (w := c)
      ⟨hCcyc a haC, hCcard a haC, hCcomm a haC⟩
      ⟨hCcyc b hbC, hCcard b hbC, hCcomm b hbC⟩
      ⟨hCcyc c hcC, hCcard c hcC, hCcomm c hcC⟩
      (hCdisj a haC b hbC hab) (hCdisj a haC c hcC hac) (hCdisj b hbC c hcC hbc)

private theorem altComb_exists_elemAbelian {n p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {x : Equiv.Perm (Fin n)} (s : Fin 3 → Equiv.Perm (Fin n))
    (hs : ∀ i, (s i).IsCycle ∧ (s i).support.card = p ∧ Commute x (s i))
    (hdisj : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (s i) (s j)) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)),
      E ≤ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ alternatingGroup (Fin n) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hodd' : Odd p := hp.odd_of_ne_two hodd
  have hord : ∀ i, orderOf (s i) = p := fun i => by
    rw [(hs i).1.orderOf, (hs i).2.1]
  have hpow : ∀ i, s i ^ p = 1 := fun i => by
    rw [← hord i]
    exact pow_orderOf_eq_one _
  let ϕ : ∀ i : Fin 3, Multiplicative (ZMod p) →* Equiv.Perm (Fin n) := fun i =>
    MonoidHom.mk' (fun a => s i ^ a.toAdd.val) (fun a b => by
      simp only [toAdd_mul]
      exact altComb_pow_val_add (hpow i) _ _)
  have hϕ : ∀ i a, ϕ i a = s i ^ a.toAdd.val := fun i a => rfl
  have hcomm : Pairwise fun i j => ∀ a b, Commute (ϕ i a) (ϕ j b) := by
    intro i j hij a b
    rw [hϕ, hϕ]
    exact Commute.pow_pow (hdisj i j hij).commute _ _
  have hΦf : ∀ a : ∀ i : Fin 3, Multiplicative (ZMod p),
      MonoidHom.noncommPiCoprod ϕ hcomm a = ϕ 0 (a 0) * ϕ 1 (a 1) * ϕ 2 (a 2) := by
    intro a
    have ha : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) * Pi.mulSingle 2 (a 2) :=
      (Finset.univ_prod_mulSingle a).symm.trans
        (Fin.prod_univ_three (fun i => Pi.mulSingle i (a i)))
    conv_lhs => rw [ha]
    simp only [map_mul, MonoidHom.noncommPiCoprod_mulSingle]
  have hxϕ : ∀ i (y : Multiplicative (ZMod p)), Commute x (ϕ i y) := fun i y => by
    rw [hϕ]
    exact (hs i).2.2.pow_right _
  have hcent : ∀ a, Commute x (MonoidHom.noncommPiCoprod ϕ hcomm a) := fun a => by
    rw [hΦf]
    exact ((hxϕ 0 _).mul_right (hxϕ 1 _)).mul_right (hxϕ 2 _)
  have hpowA : ∀ a : ∀ i : Fin 3, Multiplicative (ZMod p), a ^ p = 1 := by
    intro a
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hΦpow : ∀ a, MonoidHom.noncommPiCoprod ϕ hcomm a ^ p = 1 := fun a => by
    rw [← map_pow, hpowA a, map_one]
  have hsign : ∀ a, Equiv.Perm.sign (MonoidHom.noncommPiCoprod ϕ hcomm a) = 1 := fun a => by
    have h' : Equiv.Perm.sign (MonoidHom.noncommPiCoprod ϕ hcomm a) ^ p = 1 := by
      rw [← map_pow, hΦpow, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (MonoidHom.noncommPiCoprod ϕ hcomm a))
      with h1 | h1
    · exact h1
    · rw [h1, Odd.neg_one_pow hodd'] at h'
      exact absurd h' (by decide)
  have hsep : ∀ i j, i ≠ j → ∀ b, s i b ≠ b → s j b = b := fun i j hij b hb =>
    (Equiv.Perm.disjoint_iff_eq_or_eq.mp (hdisj i j hij) b).resolve_left hb
  have hinj : Function.Injective (MonoidHom.noncommPiCoprod ϕ hcomm) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hΦf] at ha
    simp only [hϕ] at ha
    have h0 : a 0 = 1 := by
      obtain ⟨b, hb⟩ := (hs 0).1.nonempty_support
      have hb' : s 0 b ≠ b := Equiv.Perm.mem_support.mp hb
      have hB : (s 1 ^ (a 1).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 0 1 (by decide) b hb') _
      have hC : (s 2 ^ (a 2).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 0 2 (by decide) b hb') _
      have hA := altComb_fix_left ha hB hC
      exact altComb_eq_one_of_pow_val (hord 0) (((hs 0).1.pow_eq_one_iff' hb').mpr hA)
    have h1 : a 1 = 1 := by
      obtain ⟨b, hb⟩ := (hs 1).1.nonempty_support
      have hb' : s 1 b ≠ b := Equiv.Perm.mem_support.mp hb
      have hA : (s 0 ^ (a 0).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 1 0 (by decide) b hb') _
      have hC : (s 2 ^ (a 2).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 1 2 (by decide) b hb') _
      have hB := altComb_fix_mid ha hA hC
      exact altComb_eq_one_of_pow_val (hord 1) (((hs 1).1.pow_eq_one_iff' hb').mpr hB)
    have h2 : a 2 = 1 := by
      obtain ⟨b, hb⟩ := (hs 2).1.nonempty_support
      have hb' : s 2 b ≠ b := Equiv.Perm.mem_support.mp hb
      have hA : (s 0 ^ (a 0).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 2 0 (by decide) b hb') _
      have hB : (s 1 ^ (a 1).toAdd.val) b = b :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hsep 2 1 (by decide) b hb') _
      have hC := altComb_fix_right ha hA hB
      exact altComb_eq_one_of_pow_val (hord 2) (((hs 2).1.pow_eq_one_iff' hb').mpr hC)
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨(MonoidHom.noncommPiCoprod ϕ hcomm).range, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent a).eq.symm
    · rw [Equiv.Perm.mem_alternatingGroup]
      exact hsign a
  · unfold CFSG.Open.IsElemAbelian
    refine ⟨⟨⟨fun g h => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp g.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      exact hΦpow a
  · have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
    have e : Nat.card (MonoidHom.noncommPiCoprod ϕ hcomm).range =
        Nat.card (∀ i : Fin 3, Multiplicative (ZMod p)) := by
      rw [← Nat.card_range_of_injective hinj]
      exact Nat.card_congr (Equiv.subtypeEquivRight
        fun y => MonoidHom.mem_range.trans Set.mem_range.symm)
    rw [e, Nat.card_pi]
    simp [hcardZ]

theorem exists_elemAbelian_three_of_pow_eq_one {n p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : 3 * p ≤ n) {x : Equiv.Perm (Fin n)} (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)),
      E ≤ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ alternatingGroup (Fin n) ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs, hdisj⟩ := altComb_exists_three_pcycles hp hn (orderOf_eq_prime hxp hx1) hx1
  exact altComb_exists_elemAbelian hp hodd s hs hdisj

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
