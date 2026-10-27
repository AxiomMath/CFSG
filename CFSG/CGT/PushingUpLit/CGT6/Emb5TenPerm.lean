module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Equiv Equiv.Perm

theorem sign_viaEmbeddingHom {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ι : α ↪ β) (σ : Perm α) : sign (viaEmbeddingHom ι σ) = sign σ := by
  classical
  rw [viaEmbeddingHom_apply, viaEmbedding]
  convert sign_extendDomain σ (Equiv.ofInjective ι ι.injective)

theorem fin3_ne01 (k : ℕ) : (0 : Fin (k + 3)) ≠ 1 := by
  intro h; have := congrArg Fin.val h; simp at this

theorem fin3_ne02 (k : ℕ) : (0 : Fin (k + 3)) ≠ 2 := by
  intro h; have := congrArg Fin.val h; rw [Fin.val_two] at this; simp at this

theorem fin3_ne12 (k : ℕ) : (1 : Fin (k + 3)) ≠ 2 := by
  intro h; have := congrArg Fin.val h; rw [Fin.val_two] at this; simp at this

theorem exists_embedding_threeCycle {N k : ℕ} (hk : k + 3 ≤ N) {c : Perm (Fin N)}
    (hc : c.IsThreeCycle) :
    ∃ ι : Fin (k + 3) ↪ Fin N, c = viaEmbeddingHom ι (swap 0 1 * swap 1 2) := by
  set ι₀ : Fin (k + 3) ↪ Fin N := Fin.castLEEmb hk with hι₀
  set c₀ : Perm (Fin N) := viaEmbeddingHom ι₀ (swap 0 1 * swap 1 2) with hc₀
  have hc₀3 : c₀.IsThreeCycle := by
    rw [hc₀, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap, swap_comm (ι₀ 0) (ι₀ 1)]
    exact isThreeCycle_swap_mul_swap_same (ι₀.injective.ne (fin3_ne01 k).symm)
      (ι₀.injective.ne (fin3_ne12 k)) (ι₀.injective.ne (fin3_ne02 k))
  have hconj : IsConj c₀ c :=
    isConj_iff_cycleType_eq.mpr (hc₀3.cycleType.trans hc.cycleType.symm)
  obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
  refine ⟨ι₀.trans π.toEmbedding, ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap, ← hπ, hc₀, map_mul,
    viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [swap_apply_apply, swap_apply_apply]
  group

section Two

variable {α : Type*} (ιP ιQ : Fin 5 ↪ α)

theorem fix_four_of_eq {a a' : Perm (Fin 5)} (hP4 : ιP 4 ∉ Set.range ιQ)
    (h : viaEmbeddingHom ιP a = viaEmbeddingHom ιQ a') : a 4 = 4 := by
  have h1 := congrArg (fun f : Perm α => f (ιP 4)) h
  simp only [viaEmbeddingHom_apply, viaEmbedding_apply,
    viaEmbedding_apply_of_notMem _ _ _ hP4] at h1
  exact ιP.injective h1

theorem viaEmbeddingHom_eq_of_fix (hag : ∀ i : Fin 5, i ≠ 4 → ιP i = ιQ i)
    (hP4 : ιP 4 ∉ Set.range ιQ) (a : Perm (Fin 5)) (ha : a 4 = 4) :
    viaEmbeddingHom ιP a = viaEmbeddingHom ιQ a := by
  ext x
  rw [viaEmbeddingHom_apply, viaEmbeddingHom_apply]
  by_cases hx : x ∈ Set.range ιP
  · obtain ⟨i, rfl⟩ := hx
    rw [viaEmbedding_apply]
    by_cases hi : i = 4
    · subst hi
      rw [ha, viaEmbedding_apply_of_notMem _ _ _ hP4]
    · have hai : a i ≠ 4 := fun h => hi (a.injective (h.trans ha.symm))
      rw [hag i hi, viaEmbedding_apply, hag (a i) hai]
  · rw [viaEmbedding_apply_of_notMem _ _ _ hx]
    by_cases hxQ : x ∈ Set.range ιQ
    · obtain ⟨j, rfl⟩ := hxQ
      have hj : j = 4 := by
        by_contra hj
        exact hx ⟨j, hag j hj⟩
      subst hj
      rw [viaEmbedding_apply, ha]
    · rw [viaEmbedding_apply_of_notMem _ _ _ hxQ]

end Two

set_option maxRecDepth 100000 in
theorem tenF0 : ∀ σ : Perm (Fin 5), (∀ a : Perm (Fin 5), Perm.sign a = 1 → a 4 = 4 →
    (σ * a * σ⁻¹) 4 = 4) → σ 4 = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem tenF1 : ∀ σ : Perm (Fin 5), σ * (swap 0 1 * swap 1 2) * σ⁻¹ = swap 0 1 * swap 1 2 →
    σ 4 = 4 → (∀ a : Perm (Fin 5), Perm.sign a = 1 → σ * σ * a * (σ * σ)⁻¹ = a) → σ = 1 := by
  decide +kernel

section Core

theorem core_alpha {S : Type*} [Group S] {N : ℕ} (ε : S →* Perm (Fin N))
    (hε : Function.Injective ε) (α : S ≃* S) (hα2 : ∀ s, α (α s) = s)
    (ιP ιQ : Fin 5 ↪ Fin N) (hag : ∀ i : Fin 5, i ≠ 4 → ιP i = ιQ i)
    (hP4 : ιP 4 ∉ Set.range ιQ)
    (y : S) (hy : ε y = viaEmbeddingHom ιP (swap 0 1 * swap 1 2)) (hαy : α y = y)
    (hPs : ∀ a ∈ alternatingGroup (Fin 5), ∃ s, ε s = viaEmbeddingHom ιP a)
    (hQs : ∀ a ∈ alternatingGroup (Fin 5), ∃ s, ε s = viaEmbeddingHom ιQ a)
    (hPα : ∀ s : S, ε s ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιP) →
      ε (α s) ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιP))
    (hQα : ∀ s : S, ε s ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιQ) →
      ε (α s) ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιQ)) :
    ∀ s : S, ε s ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιP) → α s = s := by
  classical
  set A5 : Subgroup (Perm (Fin 5)) := alternatingGroup (Fin 5) with hA5
  let EP : ↥A5 →* Perm (Fin N) := (viaEmbeddingHom ιP).comp A5.subtype
  let EQ : ↥A5 →* Perm (Fin N) := (viaEmbeddingHom ιQ).comp A5.subtype
  have hEP : Function.Injective EP := (viaEmbeddingHom_injective ιP).comp A5.subtype_injective
  choose Φ0 hΦ0 using fun a : ↥A5 => hPs a a.2
  choose Ψ0 hΨ0 using fun a : ↥A5 => hQs a a.2
  have hΦ0' : ∀ a : ↥A5, ε (Φ0 a) = EP a := hΦ0
  have hΨ0' : ∀ a : ↥A5, ε (Ψ0 a) = EQ a := hΨ0
  have hΦinj : Function.Injective Φ0 := fun a b h => hEP (by rw [← hΦ0' a, ← hΦ0' b, h])
  have hΦmul : ∀ a b : ↥A5, Φ0 (a * b) = Φ0 a * Φ0 b := fun a b =>
    hε (by rw [map_mul, hΦ0', hΦ0', hΦ0', map_mul])
  have hβ : ∀ a : ↥A5, ∃ a' : ↥A5, ε (α (Φ0 a)) = EP a' := by
    intro a
    have h1 : ε (Φ0 a) ∈ A5.map (viaEmbeddingHom ιP) := ⟨a, a.2, by rw [hΦ0']; rfl⟩
    obtain ⟨x, hx, hxe⟩ := hPα _ h1
    exact ⟨⟨x, hx⟩, hxe.symm⟩
  choose β0 hβ0 using hβ
  have hαΦ : ∀ a : ↥A5, α (Φ0 a) = Φ0 (β0 a) := fun a =>
    hε (by rw [hβ0 a, hΦ0'])
  have hβmul : ∀ a b : ↥A5, β0 (a * b) = β0 a * β0 b := by
    intro a b
    apply hΦinj
    rw [← hαΦ, hΦmul, map_mul, hαΦ, hαΦ, hΦmul]
  have hββ : ∀ a : ↥A5, β0 (β0 a) = a := by
    intro a
    apply hΦinj
    rw [← hαΦ, ← hαΦ, hα2]
  let β : MulAut ↥A5 :=
    { toFun := β0
      invFun := β0
      left_inv := hββ
      right_inv := hββ
      map_mul' := hβmul }
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    le_rfl (by norm_num)).2 β
  have hconj : ∀ a : ↥A5, ((β0 a : ↥A5) : Perm (Fin 5)) = σ * a * σ⁻¹ := by
    intro a
    have h1 : ((β a : ↥A5) : Perm (Fin 5)) = σ * a * σ⁻¹ := by
      have := congrArg (fun f : MulAut ↥A5 => ((f a : ↥A5) : Perm (Fin 5))) hσ
      simpa [MulAut.conjNormal_apply] using this.symm
    exact h1
  have hc5 : (swap (0 : Fin 5) 1 * swap 1 2) ∈ A5 := by
    rw [hA5, Perm.mem_alternatingGroup]; decide
  have hyΦ : y = Φ0 ⟨_, hc5⟩ := hε (by rw [hy, hΦ0']; rfl)
  have hσ1 : σ * (swap (0 : Fin 5) 1 * swap 1 2) * σ⁻¹ = swap 0 1 * swap 1 2 := by
    have h1 : Φ0 (β0 ⟨_, hc5⟩) = Φ0 ⟨_, hc5⟩ := by rw [← hαΦ, ← hyΦ, hαy]
    have h2 := hΦinj h1
    have := congrArg (fun a : ↥A5 => (a : Perm (Fin 5))) h2
    simpa [hconj] using this
  have hσ2 : ∀ a : Perm (Fin 5), Perm.sign a = 1 → σ * σ * a * (σ * σ)⁻¹ = a := by
    intro a ha
    have h1 := hββ ⟨a, Perm.mem_alternatingGroup.mpr ha⟩
    have h2 := congrArg (fun b : ↥A5 => (b : Perm (Fin 5))) h1
    simp only [hconj] at h2
    calc σ * σ * a * (σ * σ)⁻¹ = σ * (σ * a * σ⁻¹) * σ⁻¹ := by group
      _ = a := h2
  have hσ3 : ∀ a : Perm (Fin 5), Perm.sign a = 1 → a 4 = 4 → (σ * a * σ⁻¹) 4 = 4 := by
    intro a ha ha4
    set a' : ↥A5 := ⟨a, Perm.mem_alternatingGroup.mpr ha⟩ with hdef
    have h1 : Ψ0 a' = Φ0 a' := by
      apply hε
      rw [hΨ0', hΦ0']
      exact (viaEmbeddingHom_eq_of_fix ιP ιQ hag hP4 a ha4).symm
    have h2 : ε (Ψ0 a') ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ιQ) :=
      ⟨a, a'.2, by rw [hΨ0']; rfl⟩
    obtain ⟨x, hx, hxe⟩ := hQα _ h2
    rw [h1, hαΦ, hΦ0'] at hxe
    have h3 : viaEmbeddingHom ιP ((β0 a' : ↥A5) : Perm (Fin 5)) = viaEmbeddingHom ιQ x :=
      hxe.symm
    have := fix_four_of_eq ιP ιQ hP4 h3
    simpa [hconj] using this
  have hσ4 : σ 4 = 4 := tenF0 σ hσ3
  have hσ5 : σ = 1 := tenF1 σ hσ1 hσ4 hσ2
  have hβid : ∀ a : ↥A5, β0 a = a := by
    intro a
    apply Subtype.ext
    rw [hconj, hσ5]
    simp
  intro s hs
  obtain ⟨x, hx, hxe⟩ := hs
  have hs' : s = Φ0 ⟨x, hx⟩ := hε (by rw [hΦ0', ← hxe]; rfl)
  rw [hs', hαΦ, hβid]

end Core

section Facts

theorem caseA_perm_facts :
    (swap (3 : Fin 8) 4 * swap 5 6) * (swap 0 1 * swap 1 2) =
        (swap 0 1 * swap 1 2) * (swap 3 4 * swap 5 6) ∧
      (swap (3 : Fin 8) 4 * swap 5 6) * (swap 2 7 * swap 3 4) =
        (swap 2 7 * swap 3 4) * (swap 3 4 * swap 5 6) ∧
      Perm.sign (swap (3 : Fin 8) 4 * swap 5 6) = 1 ∧
      Perm.sign (swap (2 : Fin 8) 7 * swap 3 4) = 1 ∧
      (swap (3 : Fin 8) 4 * swap 5 6) * (swap 3 4 * swap 5 6) = 1 ∧
      swap (3 : Fin 8) 4 * swap 5 6 ≠ 1 ∧
      ((swap (0 : Fin 8) 1 * swap 1 2) *
          ((swap 2 7 * swap 3 4) * (swap 0 1 * swap 1 2) * (swap 2 7 * swap 3 4)⁻¹)) *
        ((swap (0 : Fin 8) 1 * swap 1 2) *
          ((swap 2 7 * swap 3 4) * (swap 0 1 * swap 1 2) * (swap 2 7 * swap 3 4)⁻¹)) = 1 ∧
      (swap (0 : Fin 8) 1 * swap 1 2) *
          ((swap 2 7 * swap 3 4) * (swap 0 1 * swap 1 2) * (swap 2 7 * swap 3 4)⁻¹) ≠ 1 := by
  decide +kernel

theorem caseB_perm_facts :
    (swap (1 : Fin 5) 3 * swap 2 4) * (swap 0 1 * swap 1 2) * (swap 1 3 * swap 2 4)⁻¹ =
        swap 0 3 * swap 3 4 ∧ Perm.sign (swap (1 : Fin 5) 3 * swap 2 4) = 1 := by
  decide +kernel

theorem caseC_perm_facts :
    (swap (1 : Fin 6) 3 * swap 2 4) * (swap 0 1 * swap 1 2) * (swap 1 3 * swap 2 4)⁻¹ =
        swap 0 3 * swap 3 4 ∧
      (swap (1 : Fin 6) 3 * swap 2 5) * (swap 0 1 * swap 1 2) * (swap 1 3 * swap 2 5)⁻¹ =
        swap 0 3 * swap 3 5 ∧
      Perm.sign (swap (1 : Fin 6) 3 * swap 2 4) = 1 ∧
      Perm.sign (swap (1 : Fin 6) 3 * swap 2 5) = 1 ∧
      (swap (0 : Fin 6) 3 * swap 3 4) * (swap 0 1 * swap 1 2) ≠
        (swap 0 1 * swap 1 2) * (swap 0 3 * swap 3 4) ∧
      (swap (0 : Fin 6) 3 * swap 3 5) * (swap 0 1 * swap 1 2) ≠
        (swap 0 1 * swap 1 2) * (swap 0 3 * swap 3 5) := by
  decide +kernel

theorem two_embeddings {N : ℕ} (ι : Fin 6 ↪ Fin N) :
    ∃ ιP ιQ : Fin 5 ↪ Fin N, (∀ i : Fin 5, i ≠ 4 → ιP i = ιQ i) ∧ ιP 4 ∉ Set.range ιQ ∧
      viaEmbeddingHom ιP (swap 0 1 * swap 1 2) = viaEmbeddingHom ι (swap 0 1 * swap 1 2) ∧
      viaEmbeddingHom ιQ (swap 0 1 * swap 1 2) = viaEmbeddingHom ι (swap 0 1 * swap 1 2) ∧
      viaEmbeddingHom ιP (swap 0 3 * swap 3 4) = viaEmbeddingHom ι (swap 0 3 * swap 3 4) ∧
      viaEmbeddingHom ιQ (swap 0 3 * swap 3 4) = viaEmbeddingHom ι (swap 0 3 * swap 3 5) := by
  let fP : Fin 5 → Fin 6 := ![0, 1, 2, 3, 4]
  let fQ : Fin 5 → Fin 6 := ![0, 1, 2, 3, 5]
  have hfP : Function.Injective fP := by decide
  have hfQ : Function.Injective fQ := by decide
  have hne : ∀ j : Fin 5, fQ j ≠ fP 4 := by decide
  refine ⟨⟨ι ∘ fP, ι.injective.comp hfP⟩, ⟨ι ∘ fQ, ι.injective.comp hfQ⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : fP i = fQ i := by revert i; decide
    exact congrArg ι this
  · rintro ⟨j, hj⟩
    exact hne j (ι.injective hj)
  · simp only [map_mul, viaEmbeddingHom_swap]
    rfl
  · simp only [map_mul, viaEmbeddingHom_swap]
    rfl
  · simp only [map_mul, viaEmbeddingHom_swap]
    rfl
  · simp only [map_mul, viaEmbeddingHom_swap]
    rfl

theorem map_viaEmbeddingHom_eq_alt (ι : Fin 5 ↪ Fin 5) :
    (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι) = alternatingGroup (Fin 5) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ alternatingGroup (Fin 5) := ha
    rw [Perm.mem_alternatingGroup] at ha' ⊢
    rw [sign_viaEmbeddingHom, ha']
  · rw [Subgroup.card_map_of_injective (viaEmbeddingHom_injective ι)]

end Facts

end CFSG.CGT.PushingUpLit.CGT6
