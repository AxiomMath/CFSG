module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Inputs
public import CFSG.Permutation.Embedding
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv Equiv.Perm

theorem IsZ3E9A4A5.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : IsZ3E9A4A5 K) : IsZ3E9A4A5 K' := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans f⟩))

theorem nonempty_mulEquiv_zmod_three {Γ : Type} [Group Γ] {A : Subgroup Γ}
    (hA : Nat.card ↥A = 3) : Nonempty (↥A ≃* Multiplicative (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥A := isCyclic_of_prime_card hA
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by omega)
  exact ⟨(zmodCyclicMulEquiv ‹IsCyclic ↥A›).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hA).toAddEquiv)⟩

theorem isZ3E9A4A5_of_commute {Γ : Type} [Group Γ] {A B : Subgroup Γ} (hA : Nat.card ↥A = 3)
    (hB : Nat.card ↥B = 3) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsZ3E9A4A5 ↥(A ⊔ B) := by
  by_cases hAB : A = B
  · subst hAB
    rw [sup_idem]
    exact Or.inl (nonempty_mulEquiv_zmod_three hA)
  · have hfinA : Finite ↥A := Nat.finite_of_card_ne_zero (by omega)
    have hfinB : Finite ↥B := Nat.finite_of_card_ne_zero (by omega)
    have hdisj : A ⊓ B = ⊥ := by
      have h1 : Nat.card ↥(A ⊓ B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exfalso
        have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hA])
        have hAle : A ≤ B := e1 ▸ inf_le_right
        exact hAB (Subgroup.eq_of_le_of_card_ge hAle (by rw [hA, hB]))
    let φ : ↥A × ↥B →* ↥(A ⊔ B) :=
      { toFun := fun p => ⟨(p.1 : Γ) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
        map_one' := by ext; simp
        map_mul' := by
          rintro ⟨a, b⟩ ⟨a', b'⟩
          apply Subtype.ext
          show ((a : Γ) * a') * ((b : Γ) * b') = ((a : Γ) * b) * ((a' : Γ) * b')
          have h := hcomm a' a'.2 b b.2
          calc ((a : Γ) * a') * ((b : Γ) * b') = (a : Γ) * ((a' : Γ) * b) * b' := by group
            _ = (a : Γ) * (b * a') * b' := by rw [h]
            _ = ((a : Γ) * b) * ((a' : Γ) * b') := by group }
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h
      have h1 : (a : Γ) * b = 1 := congrArg Subtype.val h
      have h2 : (a : Γ) = (b : Γ)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : (a : Γ) ∈ A ⊓ B := ⟨a.2, by rw [h2]; exact B.inv_mem b.2⟩
      rw [hdisj, Subgroup.mem_bot] at h3
      have h4 : (b : Γ) = 1 := by rw [h3] at h1; simpa using h1
      have ha : a = 1 := Subtype.ext h3
      have hb : b = 1 := Subtype.ext h4
      rw [ha, hb]; rfl
    have hsurj : Function.Surjective φ := by
      let P : Subgroup Γ :=
        { carrier := {z | ∃ a ∈ A, ∃ b ∈ B, z = a * b}
          one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
          mul_mem' := by
            rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
            refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
            have h := hcomm a' ha' b hb
            calc a * b * (a' * b') = a * (b * a') * b' := by group
              _ = a * (a' * b) * b' := by rw [← h]
              _ = a * a' * (b * b') := by group
          inv_mem' := by
            rintro _ ⟨a, ha, b, hb, rfl⟩
            refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
            have h := hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
            calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
              _ = a⁻¹ * b⁻¹ := h.symm }
      have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
        (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
      rintro ⟨z, hz⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hle hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    let e : (↥A × ↥B) ≃* ↥(A ⊔ B) := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
    obtain ⟨eA⟩ := nonempty_mulEquiv_zmod_three hA
    obtain ⟨eB⟩ := nonempty_mulEquiv_zmod_three hB
    let ep : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) ≃*
        Multiplicative (ZMod 3 × ZMod 3) :=
      { toFun := fun p => Multiplicative.ofAdd (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)
        invFun := fun x => (Multiplicative.ofAdd (Multiplicative.toAdd x).1,
          Multiplicative.ofAdd (Multiplicative.toAdd x).2)
        left_inv := fun p => rfl
        right_inv := fun x => rfl
        map_mul' := fun p q => rfl }
    exact Or.inr (Or.inl ⟨e.symm.trans ((MulEquiv.prodCongr eA eB).trans ep)⟩)

private def pairStepF {n : ℕ} (a b : Perm (Fin n)) (S : Finset (Perm (Fin n))) :
    Finset (Perm (Fin n)) :=
  S ∪ S.image (· * a) ∪ S.image (· * b)

private theorem pairStepF_iter_mem {n : ℕ} (a b : Perm (Fin n)) (K : Subgroup (Perm (Fin n)))
    (ha : a ∈ K) (hb : b ∈ K) : ∀ k : ℕ, ∀ σ ∈ (pairStepF a b)^[k] {1}, σ ∈ K := by
  intro k
  induction k with
  | zero =>
    intro σ hσ
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hσ
    subst hσ
    exact K.one_mem
  | succ k ih =>
    intro σ hσ
    rw [Function.iterate_succ_apply'] at hσ
    simp only [pairStepF, Finset.mem_union, Finset.mem_image] at hσ
    rcases hσ with (h | ⟨τ, hτ, rfl⟩) | ⟨τ, hτ, rfl⟩
    · exact ih σ h
    · exact K.mul_mem (ih τ hτ) ha
    · exact K.mul_mem (ih τ hτ) hb

set_option maxRecDepth 100000 in
private theorem std5_three_mem : ∀ σ : Perm (Fin 5), σ.support.card = 3 →
    σ ∈ (pairStepF (swap 0 1 * swap 1 2) (swap 0 3 * swap 3 4))^[6] {1} := by decide +kernel

set_option maxRecDepth 100000 in
private theorem std4_three_mem : ∀ σ : Perm (Fin 4), σ.support.card = 3 →
    σ ∈ (pairStepF (swap 0 1 * swap 1 2) (swap 0 1 * swap 1 3))^[6] {1} := by decide +kernel

private theorem sign_std5 : Perm.sign (swap (0 : Fin 5) 1 * swap 1 2) = 1 ∧
    Perm.sign (swap (0 : Fin 5) 3 * swap 3 4) = 1 := by decide

private theorem sign_std4 : Perm.sign (swap (0 : Fin 4) 1 * swap 1 2) = 1 ∧
    Perm.sign (swap (0 : Fin 4) 1 * swap 1 3) = 1 := by decide

theorem closure_std_five :
    Subgroup.closure {swap (0 : Fin 5) 1 * swap 1 2, swap (0 : Fin 5) 3 * swap 3 4} =
      alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Perm.mem_alternatingGroup.mpr sign_std5.1
    · exact Perm.mem_alternatingGroup.mpr sign_std5.2
  · rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    exact pairStepF_iter_mem _ _ _ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr rfl)) 6 σ
      (std5_three_mem σ (card_support_eq_three_iff.mpr hσ))

theorem closure_std_four :
    Subgroup.closure {swap (0 : Fin 4) 1 * swap 1 2, swap (0 : Fin 4) 1 * swap 1 3} =
      alternatingGroup (Fin 4) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Perm.mem_alternatingGroup.mpr sign_std4.1
    · exact Perm.mem_alternatingGroup.mpr sign_std4.2
  · rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    exact pairStepF_iter_mem _ _ _ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr rfl)) 6 σ
      (std4_three_mem σ (card_support_eq_three_iff.mpr hσ))

section Label

variable {α : Type} [Fintype α] [DecidableEq α]

export CFSG.Permutation (viaEmbeddingHom_swap)

theorem three_cycles_overlap_one {c₁ c₂ : Perm α} (h₁ : c₁.IsThreeCycle) (h₂ : c₂.IsThreeCycle)
    {r : α} (hr : c₁.support ∩ c₂.support = {r}) :
    ∃ ι : Fin 5 ↪ α, c₁ = viaEmbeddingHom ι (swap 0 1 * swap 1 2) ∧
      c₂ = viaEmbeddingHom ι (swap 0 3 * swap 3 4) := by
  have hr12 : r ∈ c₁.support ∩ c₂.support := by rw [hr]; exact Finset.mem_singleton_self r
  have hr1 : r ∈ c₁.support := (Finset.mem_inter.mp hr12).1
  have hr2 : r ∈ c₂.support := (Finset.mem_inter.mp hr12).2
  have nd1 := h₁.nodup_iff_mem_support.mpr hr1
  have nd2 := h₂.nodup_iff_mem_support.mpr hr2
  have sp1 := h₁.support_eq_iff_mem_support.mpr hr1
  have sp2 := h₂.support_eq_iff_mem_support.mpr hr2
  generalize hp : c₁ r = p at nd1 sp1
  generalize hq : c₁ p = q at nd1 sp1
  generalize hs : c₂ r = s at nd2 sp2
  generalize hu : c₂ s = u at nd2 sp2
  simp only [List.nodup_cons, List.mem_cons, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at nd1 nd2
  obtain ⟨⟨hrp, hrq⟩, hpq⟩ := nd1
  obtain ⟨⟨hrs, hru⟩, hsu⟩ := nd2
  replace hrp : r ≠ p := hrp
  replace hrq : r ≠ q := hrq
  replace hpq : p ≠ q := hpq
  replace hrs : r ≠ s := hrs
  replace hru : r ≠ u := hru
  replace hsu : s ≠ u := hsu
  have cross : ∀ x, x ∈ c₁.support → x ∈ c₂.support → x = r := by
    intro x hx1 hx2
    have : x ∈ c₁.support ∩ c₂.support := Finset.mem_inter.mpr ⟨hx1, hx2⟩
    rw [hr] at this
    exact Finset.mem_singleton.mp this
  have hp1 : p ∈ c₁.support := by rw [sp1]; simp
  have hq1 : q ∈ c₁.support := by rw [sp1]; simp
  have hs2 : s ∈ c₂.support := by rw [sp2]; simp
  have hu2 : u ∈ c₂.support := by rw [sp2]; simp
  have hps : p ≠ s := fun h => hrp (cross p hp1 (h ▸ hs2)).symm
  have hpu : p ≠ u := fun h => hrp (cross p hp1 (h ▸ hu2)).symm
  have hqs : q ≠ s := fun h => hrq (cross q hq1 (h ▸ hs2)).symm
  have hqu : q ≠ u := fun h => hrq (cross q hq1 (h ▸ hu2)).symm
  have hinj : Function.Injective (![r, p, q, s, u] : Fin 5 → α) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [hrp, hrq, hrs, hru, hpq, hps, hpu, hqs, hqu, hsu, hrp.symm, hrq.symm, hrs.symm,
        hru.symm, hpq.symm, hps.symm, hpu.symm, hqs.symm, hqu.symm, hsu.symm] at h ⊢
  refine ⟨⟨_, hinj⟩, ?_, ?_⟩
  · rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    have := h₁.eq_swap_mul_swap_iff_mem_support.mpr hr1
    rw [hp, hq] at this
    exact this
  · rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    have := h₂.eq_swap_mul_swap_iff_mem_support.mpr hr2
    rw [hs, hu] at this
    exact this

theorem exists_orientation {c : Perm α} (h : c.IsThreeCycle) {a b : α} (ha : a ∈ c.support)
    (hb : b ∈ c.support) (hab : a ≠ b) : ∃ d : Perm α, (d = c ∨ d = c⁻¹) ∧ d a = b := by
  have sp := h.support_eq_iff_mem_support.mpr ha
  rw [sp] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact ⟨c, Or.inl rfl, rfl⟩
  · refine ⟨c⁻¹, Or.inr rfl, ?_⟩
    have h3 : c ^ 3 = 1 := by rw [← h.orderOf]; exact pow_orderOf_eq_one c
    have h4 : c (c (c a)) = a := by
      have : (c ^ 3) a = a := by rw [h3]; rfl
      simpa [pow_succ, Perm.mul_apply] using this
    rw [Perm.inv_eq_iff_eq]
    exact h4.symm

theorem three_cycles_overlap_two {c₁ c₂ : Perm α} (h₁ : c₁.IsThreeCycle)
    (h₂ : c₂.IsThreeCycle) {a b : α} (hr : c₁.support ∩ c₂.support = {a, b})
    (h1 : c₁ a = b) (h2 : c₂ a = b) :
    ∃ ι : Fin 4 ↪ α, c₁ = viaEmbeddingHom ι (swap 0 1 * swap 1 2) ∧
      c₂ = viaEmbeddingHom ι (swap 0 1 * swap 1 3) := by
  have ha12 : a ∈ c₁.support ∩ c₂.support := by rw [hr]; simp
  have ha1 : a ∈ c₁.support := (Finset.mem_inter.mp ha12).1
  have ha2 : a ∈ c₂.support := (Finset.mem_inter.mp ha12).2
  have nd1 := h₁.nodup_iff_mem_support.mpr ha1
  have nd2 := h₂.nodup_iff_mem_support.mpr ha2
  have sp1 := h₁.support_eq_iff_mem_support.mpr ha1
  have sp2 := h₂.support_eq_iff_mem_support.mpr ha2
  rw [h1] at nd1 sp1
  rw [h2] at nd2 sp2
  generalize hc : c₁ b = c at nd1 sp1
  generalize hd : c₂ b = d at nd2 sp2
  simp only [List.nodup_cons, List.mem_cons, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at nd1 nd2
  obtain ⟨⟨hab, hac⟩, hbc⟩ := nd1
  obtain ⟨⟨-, had⟩, hbd⟩ := nd2
  replace hab : a ≠ b := hab
  replace hac : a ≠ c := hac
  replace hbc : b ≠ c := hbc
  replace had : a ≠ d := had
  replace hbd : b ≠ d := hbd
  have hc1 : c ∈ c₁.support := by rw [sp1]; simp
  have hcd : c ≠ d := by
    intro hcd
    have hc2 : c ∈ c₂.support := by rw [sp2, ← hcd]; simp
    have : c ∈ c₁.support ∩ c₂.support := Finset.mem_inter.mpr ⟨hc1, hc2⟩
    rw [hr] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hac h.symm
    · exact hbc h.symm
  have hinj : Function.Injective (![a, b, c, d] : Fin 4 → α) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
        hcd.symm] at h ⊢
  refine ⟨⟨_, hinj⟩, ?_, ?_⟩
  · rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    have := h₁.eq_swap_mul_swap_iff_mem_support.mpr ha1
    rw [h1, hc] at this
    exact this
  · rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    have := h₂.eq_swap_mul_swap_iff_mem_support.mpr ha2
    rw [h2, hd] at this
    exact this

omit [Fintype α] [DecidableEq α] in
theorem isZ3E9A4A5_of_std {m : ℕ} (hm : m = 4 ∨ m = 5) (ι : Fin m ↪ α) (a₀ b₀ : Perm (Fin m))
    {c₁ c₂ : Perm α} (hc₁ : c₁ = viaEmbeddingHom ι a₀) (hc₂ : c₂ = viaEmbeddingHom ι b₀)
    (hcl : Subgroup.closure ({a₀, b₀} : Set (Perm (Fin m))) = alternatingGroup (Fin m)) :
    IsZ3E9A4A5 ↥(Subgroup.closure ({c₁, c₂} : Set (Perm α))) := by
  have hinj := viaEmbeddingHom_injective ι
  have hmap : Subgroup.closure ({c₁, c₂} : Set (Perm α)) =
      (alternatingGroup (Fin m)).map (viaEmbeddingHom ι) := by
    rw [← hcl, MonoidHom.map_closure, Set.image_pair, hc₁, hc₂]
  have e : ↥(alternatingGroup (Fin m)) ≃* ↥(Subgroup.closure ({c₁, c₂} : Set (Perm α))) :=
    (Subgroup.equivMapOfInjective _ (viaEmbeddingHom ι) hinj).trans
      (MulEquiv.subgroupCongr hmap.symm)
  rcases hm with rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.symm⟩))

theorem three_cycle_eq_of_support_eq {c d : Perm α} (hc : c.IsThreeCycle) (hd : d.IsThreeCycle)
    (hs : c.support = d.support) {a : α} (ha : a ∈ c.support) (hcd : c a = d a) : c = d := by
  have had : a ∈ d.support := hs ▸ ha
  have hcsp := hc.support_eq_iff_mem_support.mpr ha
  have hdsp := hd.support_eq_iff_mem_support.mpr had
  have ndc := hc.nodup_iff_mem_support.mpr ha
  have e1 := hc.eq_swap_mul_swap_iff_mem_support.mpr ha
  have e2 := hd.eq_swap_mul_swap_iff_mem_support.mpr had
  rw [← hcd] at e2 hdsp
  have hmem : c (c a) ∈ d.support := by
    rw [← hs, hcsp]; simp
  rw [hdsp] at hmem
  simp only [List.nodup_cons, List.mem_cons, or_false, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at ndc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have h3 : c (c a) = d (c a) := by
    rcases hmem with h | h | h
    · exact absurd h.symm ndc.1.2
    · exact absurd h.symm ndc.2
    · exact h
  rw [e1, e2, h3]

theorem three_cycles_same_support_commute {c₁ c₂ : Perm α} (h₁ : c₁.IsThreeCycle)
    (h₂ : c₂.IsThreeCycle) (hs : c₁.support = c₂.support) : Commute c₁ c₂ := by
  have hne : c₁.support.Nonempty := by
    rw [← Finset.card_pos, h₁.card_support]; norm_num
  obtain ⟨a, ha1⟩ := hne
  have ha2 : a ∈ c₂.support := hs ▸ ha1
  have hb1 : c₁ a ∈ c₁.support := Perm.apply_mem_support.mpr ha1
  have hb2 : c₁ a ∈ c₂.support := hs ▸ hb1
  have hab : a ≠ c₁ a := fun h => (Perm.mem_support.mp ha1) h.symm
  obtain ⟨d, hd, hda⟩ := exists_orientation h₂ ha2 hb2 hab
  have hd3 : d.IsThreeCycle := by
    rcases hd with hd | hd
    · rw [hd]; exact h₂
    · rw [hd]; exact h₂.inv
  have hsd : c₁.support = d.support := by
    rcases hd with hd | hd
    · rw [hd]; exact hs
    · rw [hd, Perm.support_inv]; exact hs
  have hdc := three_cycle_eq_of_support_eq h₁ hd3 hsd ha1 hda.symm
  rcases hd with hd | hd
  · rw [hdc, hd]
  · rw [hdc, hd]
    exact (Commute.refl c₂).inv_left

theorem closure_pair_congr {Γ : Type*} [Group Γ] {c₁ c₂ d₁ d₂ : Γ} (h₁ : d₁ = c₁ ∨ d₁ = c₁⁻¹)
    (h₂ : d₂ = c₂ ∨ d₂ = c₂⁻¹) :
    Subgroup.closure ({d₁, d₂} : Set Γ) = Subgroup.closure ({c₁, c₂} : Set Γ) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rcases h₁ with rfl | rfl
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))
    · rcases h₂ with rfl | rfl
      · exact Subgroup.subset_closure (Or.inr rfl)
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rcases h₁ with h | h
      · rw [← h]; exact Subgroup.subset_closure (Or.inl rfl)
      · have : x = d₁⁻¹ := by rw [h]; simp
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))
    · rcases h₂ with h | h
      · rw [← h]; exact Subgroup.subset_closure (Or.inr rfl)
      · have : x = d₂⁻¹ := by rw [h]; simp
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))

theorem isZ3E9A4A5_closure_threeCycles {c₁ c₂ : Perm α} (h₁ : c₁.IsThreeCycle)
    (h₂ : c₂.IsThreeCycle) : IsZ3E9A4A5 ↥(Subgroup.closure ({c₁, c₂} : Set (Perm α))) := by
  have hcl : Subgroup.closure ({c₁, c₂} : Set (Perm α)) =
      Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hz1 : Nat.card ↥(Subgroup.zpowers c₁) = 3 := by rw [Nat.card_zpowers, h₁.orderOf]
  have hz2 : Nat.card ↥(Subgroup.zpowers c₂) = 3 := by rw [Nat.card_zpowers, h₂.orderOf]
  have hcommCase : Commute c₁ c₂ →
      IsZ3E9A4A5 ↥(Subgroup.closure ({c₁, c₂} : Set (Perm α))) := by
    intro hc
    rw [hcl]
    refine isZ3E9A4A5_of_commute hz1 hz2 ?_
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hc m n).eq
  have hk : (c₁.support ∩ c₂.support).card ≤ 3 :=
    (Finset.card_le_card Finset.inter_subset_left).trans h₁.card_support.le
  generalize hkd : (c₁.support ∩ c₂.support).card = k at hk
  interval_cases k
  · apply hcommCase
    have : Disjoint c₁.support c₂.support :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hkd)
    exact (Perm.disjoint_iff_disjoint_support.mpr this).commute
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hkd
    obtain ⟨ι, e1, e2⟩ := three_cycles_overlap_one h₁ h₂ hr
    exact isZ3E9A4A5_of_std (Or.inr rfl) ι _ _ e1 e2 closure_std_five
  · obtain ⟨a, b, hab, hr⟩ := Finset.card_eq_two.mp hkd
    have ha : a ∈ c₁.support ∩ c₂.support := by rw [hr]; simp
    have hb : b ∈ c₁.support ∩ c₂.support := by rw [hr]; simp
    obtain ⟨d₁, hd₁, hd₁a⟩ := exists_orientation h₁ (Finset.mem_inter.mp ha).1
      (Finset.mem_inter.mp hb).1 hab
    obtain ⟨d₂, hd₂, hd₂a⟩ := exists_orientation h₂ (Finset.mem_inter.mp ha).2
      (Finset.mem_inter.mp hb).2 hab
    have hd₁3 : d₁.IsThreeCycle := by
      rcases hd₁ with h | h
      · rw [h]; exact h₁
      · rw [h]; exact h₁.inv
    have hd₂3 : d₂.IsThreeCycle := by
      rcases hd₂ with h | h
      · rw [h]; exact h₂
      · rw [h]; exact h₂.inv
    have hsup₁ : d₁.support = c₁.support := by
      rcases hd₁ with h | h
      · rw [h]
      · rw [h, Perm.support_inv]
    have hsup₂ : d₂.support = c₂.support := by
      rcases hd₂ with h | h
      · rw [h]
      · rw [h, Perm.support_inv]
    have hr' : d₁.support ∩ d₂.support = {a, b} := by rw [hsup₁, hsup₂]; exact hr
    obtain ⟨ι, e1, e2⟩ := three_cycles_overlap_two hd₁3 hd₂3 hr' hd₁a hd₂a
    rw [← closure_pair_congr hd₁ hd₂]
    exact isZ3E9A4A5_of_std (Or.inl rfl) ι _ _ e1 e2 closure_std_four
  · apply hcommCase
    have hs : c₁.support = c₂.support := by
      have h1 : c₁.support ∩ c₂.support = c₁.support :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hkd, h₁.card_support])
      have h2 : c₁.support ∩ c₂.support = c₂.support :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hkd, h₂.card_support])
      rw [← h1, h2]
    exact three_cycles_same_support_commute h₁ h₂ hs

end Label

theorem isZ3E9A4A5_of_injective_threeCycles {Γ : Type} [Group Γ] {α : Type} [Fintype α]
    [DecidableEq α] (f : Γ →* Perm α) (hf : Function.Injective f) {X Y : Subgroup Γ}
    {c₁ c₂ : Perm α} (h₁ : c₁.IsThreeCycle) (h₂ : c₂.IsThreeCycle)
    (hX : X.map f = Subgroup.zpowers c₁) (hY : Y.map f = Subgroup.zpowers c₂) :
    IsZ3E9A4A5 ↥(X ⊔ Y) := by
  have hmap : (X ⊔ Y).map f = Subgroup.closure ({c₁, c₂} : Set (Perm α)) := by
    rw [Subgroup.map_sup, hX, hY, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  have e : ↥(X ⊔ Y) ≃* ↥(Subgroup.closure ({c₁, c₂} : Set (Perm α))) :=
    (Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr hmap)
  exact IsZ3E9A4A5.of_mulEquiv e.symm (isZ3E9A4A5_closure_threeCycles h₁ h₂)

end CFSG.CGT.PushingUpLit.CGT6
