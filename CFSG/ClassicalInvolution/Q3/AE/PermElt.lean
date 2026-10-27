module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem ofPerm_mul (σ τ : Equiv.Perm (Fin n)) : ofPerm σ * ofPerm τ = ofPerm (σ * τ) := by
  refine Wr.ext (funext fun i => ?_) rfl
  show (0 : ZMod 2) + 0 = 0
  rw [add_zero]

theorem ofPerm_one : ofPerm (1 : Equiv.Perm (Fin n)) = 1 := rfl

theorem ofPerm_pow (σ : Equiv.Perm (Fin n)) (k : ℕ) : ofPerm σ ^ k = ofPerm (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ofPerm_one]
  | succ k ih => rw [pow_succ, ih, ofPerm_mul, ← pow_succ]

theorem ofPerm_conj_vec (σ : Equiv.Perm (Fin n)) (a : Wr n) (x : Fin n) :
    (ofPerm σ * a * (ofPerm σ)⁻¹).vec x = a.vec (σ.symm x) := by
  rw [mul_vec, mul_vec]
  show (0 : ZMod 2) + a.vec (σ.symm x) + (ofPerm σ)⁻¹.vec ((σ * a.perm).symm x) = a.vec (σ.symm x)
  rw [inv_vec]
  show (0 : ZMod 2) + a.vec (σ.symm x) + 0 = a.vec (σ.symm x)
  rw [zero_add, add_zero]

theorem ofPerm_conj_perm (σ : Equiv.Perm (Fin n)) (a : Wr n) :
    (ofPerm σ * a * (ofPerm σ)⁻¹).perm = σ * a.perm * σ⁻¹ := rfl

theorem ofPerm_conj_embed {ι : Fin 4 ↪ Fin n} {σ : Equiv.Perm (Fin n)} {c : Equiv.Perm (Fin 4)}
    (hσ : ∀ i, σ (ι i) = ι (c i)) (a : Wr 4) :
    ofPerm σ * embed ι a * (ofPerm σ)⁻¹ = embed ι (ofPerm c * a * (ofPerm c)⁻¹) := by
  classical
  have hsymm : ∀ i, σ.symm (ι i) = ι (c.symm i) := by
    intro i
    apply σ.injective
    rw [Equiv.apply_symm_apply, hσ, Equiv.apply_symm_apply]
  have hout : ∀ x, x ∉ Set.range ι → σ.symm x ∉ Set.range ι := by
    rintro x hx ⟨i, hi⟩
    apply hx
    refine ⟨c i, ?_⟩
    rw [← hσ, hi, Equiv.apply_symm_apply]
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [ofPerm_conj_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [hsymm, embed_vec, embed_vec, embedVec_apply, embedVec_apply, ofPerm_conj_vec]
    · rw [embed_vec_of_not_mem ι _ (hout x hx), embed_vec_of_not_mem ι _ hx]
  · rw [ofPerm_conj_perm]
    show σ ((embed ι a).perm (σ⁻¹ x)) = (embed ι (ofPerm c * a * (ofPerm c)⁻¹)).perm x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [Equiv.Perm.inv_def, hsymm, embed_perm, embed_perm, embedPerm_apply, embedPerm_apply,
        hσ, ofPerm_conj_perm]
      rfl
    · rw [Equiv.Perm.inv_def, embed_perm_of_not_mem ι _ (hout x hx), Equiv.apply_symm_apply,
        embed_perm_of_not_mem ι _ hx]

@[expose] noncomputable def localPerm (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n))
    (hmap : ∀ i, σ (ι i) ∈ Set.range ι) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (fun i => (hmap i).choose) (Finite.injective_iff_bijective.mp fun i j hij => by
    have hi := (hmap i).choose_spec
    have hj := (hmap j).choose_spec
    have h1 : σ (ι i) = σ (ι j) := by rw [← hi, ← hj]; exact congrArg ι hij
    exact ι.injective (σ.injective h1))

theorem localPerm_spec (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n))
    (hmap : ∀ i, σ (ι i) ∈ Set.range ι) (i : Fin 4) :
    σ (ι i) = ι (localPerm ι σ hmap i) :=
  ((hmap i).choose_spec).symm

theorem three_cycle_kList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList := by
  decide +kernel

theorem three_cycle_kStarList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList := by
  decide +kernel

theorem three_cycle_not_comm_kList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∃ k ∈ kList, ofPerm c * k ≠ k * ofPerm c := by
  decide +kernel

theorem three_cycle_not_comm_kStarList : ∀ c : Equiv.Perm (Fin 4), c * c * c = 1 → c ≠ 1 →
    ∃ k ∈ kStarList, ofPerm c * k ≠ k * ofPerm c := by
  decide +kernel

theorem perm_conj_zQ : ∀ c : Equiv.Perm (Fin 4), ofPerm c * zQ * (ofPerm c)⁻¹ = zQ := by
  decide +kernel

theorem three_cycle_local (c : Equiv.Perm (Fin 4)) (hc3 : c * c * c = 1) (hc1 : c ≠ 1) :
    (∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∧
    (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) ∧
    (∃ k ∈ kList, ofPerm c * k ≠ k * ofPerm c) ∧
    (∃ k ∈ kStarList, ofPerm c * k ≠ k * ofPerm c) ∧
    ofPerm c * zQ * (ofPerm c)⁻¹ = zQ :=
  ⟨three_cycle_kList c hc3 hc1, three_cycle_kStarList c hc3 hc1,
    three_cycle_not_comm_kList c hc3 hc1, three_cycle_not_comm_kStarList c hc3 hc1,
    perm_conj_zQ c⟩

theorem yElt_of_perm (hn : 5 ≤ n) {α : Finset (Fin n)} (h : α.card = 4)
    {σ : Equiv.Perm (Fin n)} (hσα : ∀ x ∈ α, σ x ∈ α) (hσ3 : σ ^ 3 = 1)
    (hσ1 : ∃ x ∈ α, σ x ≠ x) :
    mkQ n (ofPerm σ) ^ 3 = 1 ∧ mkQ n (ofPerm σ) * zBar α h = zBar α h * mkQ n (ofPerm σ) ∧
    (∀ b, ∀ x ∈ memBar α h b, mkQ n (ofPerm σ) * x * (mkQ n (ofPerm σ))⁻¹ ∈ memBar α h b) ∧
    (∀ b, ∃ x ∈ memBar α h b, mkQ n (ofPerm σ) * x ≠ x * mkQ n (ofPerm σ)) := by
  classical
  set ι := emb α h with hι
  have hrange : Set.range ι = (α : Set (Fin n)) := range_emb α h
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := by
    intro i
    rw [hrange]
    have hi : ι i ∈ α := by
      have : ι i ∈ Set.range ι := Set.mem_range_self i
      rw [hrange] at this
      exact this
    exact hσα _ hi
  set c := localPerm ι σ hmap with hc
  have hspec : ∀ i, σ (ι i) = ι (c i) := localPerm_spec ι σ hmap
  have hc3 : c * c * c = 1 := by
    refine Equiv.ext fun i => ι.injective ?_
    have h1 : (σ ^ 3) (ι i) = ι i := by rw [hσ3]; rfl
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hspec, hspec, hspec] at h1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h1
  have hc1 : c ≠ 1 := by
    rintro hc1
    obtain ⟨x, hx, hσx⟩ := hσ1
    have hx' : x ∈ Set.range ι := by rw [hrange]; exact hx
    obtain ⟨i, rfl⟩ := hx'
    apply hσx
    rw [hspec, hc1]
    rfl
  obtain ⟨hK, hKS, ⟨k₁, hk₁, hk₁'⟩, ⟨k₂, hk₂, hk₂'⟩, hz⟩ := three_cycle_local c hc3 hc1
  have hconj := fun a => ofPerm_conj_embed (ι := ι) hspec a
  have hloc : ∀ b, ∀ k, (k ∈ (bif b then kList else kStarList)) →
      embed ι k ∈ memAt α h b := by
    intro b k hk
    cases b
    · exact ⟨k, hk, rfl⟩
    · exact ⟨k, hk, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ofPerm_pow, hσ3, ofPerm_one, map_one]
  · have h1 : ofPerm σ * zOf ι * (ofPerm σ)⁻¹ = zOf ι := by
      unfold zOf
      rw [hconj, hz]
    rw [zBar, ← hι, ← map_mul, ← map_mul]
    congr 1
    calc ofPerm σ * zOf ι = (ofPerm σ * zOf ι * (ofPerm σ)⁻¹) * ofPerm σ := by group
      _ = zOf ι * ofPerm σ := by rw [h1]
  · intro b x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨ofPerm σ * a * (ofPerm σ)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    cases b
    · obtain ⟨k, hk, rfl⟩ := ha
      rw [hconj]
      exact ⟨_, hKS k hk, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := ha
      rw [hconj]
      exact ⟨_, hK k hk, rfl⟩
  · intro b
    obtain ⟨k, hk, hk'⟩ : ∃ k ∈ (bif b then kList else kStarList),
        ofPerm c * k ≠ k * ofPerm c := by
      cases b
      · exact ⟨k₂, hk₂, hk₂'⟩
      · exact ⟨k₁, hk₁, hk₁'⟩
    refine ⟨mkQ n (embed ι k), ⟨_, hloc b k hk, rfl⟩, fun he => hk' ?_⟩
    have hsupp1 : SupportedOn (ofPerm σ * embed ι k * (ofPerm σ)⁻¹) (Set.range ι) := by
      rw [hconj]
      exact embed_supportedOn ι _
    have he' : mkQ n (ofPerm σ * embed ι k * (ofPerm σ)⁻¹) = mkQ n (embed ι k) := by
      rw [map_mul, map_mul, map_inv, he]
      group
    have h2 := mkQ_inj_of_supportedOn hn hsupp1 (embed_supportedOn ι k) he'
    rw [hconj] at h2
    have h3 := embed_injective ι h2
    calc ofPerm c * k = (ofPerm c * k * (ofPerm c)⁻¹) * ofPerm c := by group
      _ = k * ofPerm c := by rw [h3]

end CFSG.ClassicalInvolution.Q3.AE
