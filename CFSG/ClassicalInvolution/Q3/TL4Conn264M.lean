module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem local_swap_kStarList : ∀ i₁ i₂ : Fin 4, i₁ ≠ i₂ → ∀ w : Fin 4 → ZMod 2,
    (w i₁ + w i₂ = 1 ∧ ∀ i, i ≠ i₁ → i ≠ i₂ → w i = 0) →
    ∀ a ∈ kStarList, ofVec w * (ofPerm (Equiv.swap i₁ i₂) * a * (ofPerm (Equiv.swap i₁ i₂))⁻¹) *
      (ofVec w)⁻¹ ∈ kStarList := by
  decide +kernel

theorem kList_pairs : ∀ k ∈ kList, k * k ≠ 1 → ∀ i : Fin 4,
    k.perm (k.perm i) = i ∧ k.perm i ≠ i ∧ k.vec i + k.vec (k.perm i) = 1 := by
  decide +kernel

theorem normalizes_embed_of_swap (ι κ : Fin 4 ↪ Fin n) {k : Wr 4} (hk : k ∈ kList)
    (hkk : k * k ≠ 1) (j : Fin 4) (hpι : κ j ∈ Set.range ι)
    (hqι : κ (k.perm j) ∈ Set.range ι)
    (hinter : ∀ x ∈ Set.range ι, x ∈ Set.range κ → x = κ j ∨ x = κ (k.perm j)) :
    (∀ a ∈ memK ι, embed κ k * a * (embed κ k)⁻¹ ∈ memK ι) ∧
      (∀ a ∈ memKStar ι, embed κ k * a * (embed κ k)⁻¹ ∈ memKStar ι) := by
  classical
  obtain ⟨hk1, hk0, hkv⟩ := kList_pairs k hk hkk j
  obtain ⟨i₁, hi₁⟩ := hpι
  obtain ⟨i₂, hi₂⟩ := hqι
  have hj : k.perm j ≠ j := hk0
  have hi : i₁ ≠ i₂ := fun h => hj (κ.injective (by rw [← hi₂, ← hi₁, h]))
  set v := embed κ k with hv
  have hvp : v.perm = embedPerm κ k.perm := rfl
  have hvv : v.vec = embedVec κ k.vec := rfl
  have hout : ∀ i, i ≠ i₁ → i ≠ i₂ → ι i ∉ Set.range κ := fun i h1 h2 hκ => by
    rcases hinter _ ⟨i, rfl⟩ hκ with h | h
    · exact h1 (ι.injective (h.trans hi₁.symm))
    · exact h2 (ι.injective (h.trans hi₂.symm))
  have hτ1 : v.perm (ι i₁) = ι i₂ := by
    rw [hvp, hi₁, embedPerm_apply, hi₂]
  have hτ2 : v.perm (ι i₂) = ι i₁ := by
    rw [hvp, hi₂, embedPerm_apply, hk1, hi₁]
  have hτo : ∀ i, i ≠ i₁ → i ≠ i₂ → v.perm (ι i) = ι i := fun i h1 h2 => by
    rw [hvp, embedPerm_of_not_mem κ _ (hout i h1 h2)]
  have hmap : ∀ i, v.perm (ι i) ∈ Set.range ι := fun i => by
    by_cases h1 : i = i₁
    · rw [h1, hτ1]; exact ⟨i₂, rfl⟩
    · by_cases h2 : i = i₂
      · rw [h2, hτ2]; exact ⟨i₁, rfl⟩
      · rw [hτo i h1 h2]; exact ⟨i, rfl⟩
  have hc := localPerm_spec ι v.perm hmap
  have hc1 : localPerm ι v.perm hmap i₁ = i₂ := ι.injective (by rw [← hc, hτ1])
  have hc2 : localPerm ι v.perm hmap i₂ = i₁ := ι.injective (by rw [← hc, hτ2])
  have hc3 : ∀ i, i ≠ i₁ → i ≠ i₂ → localPerm ι v.perm hmap i = i := fun i h1 h2 =>
    ι.injective (by rw [← hc, hτo i h1 h2])
  have hcs : localPerm ι v.perm hmap = Equiv.swap i₁ i₂ := Equiv.ext fun i => by
    by_cases h1 : i = i₁
    · rw [h1, hc1, Equiv.swap_apply_left]
    · by_cases h2 : i = i₂
      · rw [h2, hc2, Equiv.swap_apply_right]
      · rw [hc3 i h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hw1 : (v.vec ∘ ι) i₁ + (v.vec ∘ ι) i₂ = 1 := by
    show v.vec (ι i₁) + v.vec (ι i₂) = 1
    rw [hvv, hi₁, hi₂, embedVec_apply, embedVec_apply, hkv]
  have hw0 : ∀ i, i ≠ i₁ → i ≠ i₂ → (v.vec ∘ ι) i = 0 := fun i h1 h2 => by
    show v.vec (ι i) = 0
    rw [hvv, embedVec_of_not_mem κ _ (hout i h1 h2)]
  have hconj : ∀ a : Wr 4, v * embed ι a * v⁻¹ = embed ι (ofVec (v.vec ∘ ι) *
      (ofPerm (Equiv.swap i₁ i₂) * a * (ofPerm (Equiv.swap i₁ i₂))⁻¹) *
        (ofVec (v.vec ∘ ι))⁻¹) := fun a => by
    rw [← ofVec_conj_embed, ← hcs, ← ofPerm_conj_embed hc]
    conv_lhs => rw [eq_ofVec_mul_ofPerm v]
    group
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, local_swap_kList i₁ i₂ hi _ ⟨hw1, hw0⟩ a ha, (hconj a).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, local_swap_kStarList i₁ i₂ hi _ ⟨hw1, hw0⟩ a ha, (hconj a).symm⟩

theorem not_mem_memBar_of_perm {γ : Finset (Fin n)} (hγ : γ.card = 4) (b : Bool) {w : Wr n}
    {x : Fin n} (hx : x ∉ γ) (hwx : w.perm x ≠ x) : mkQ n w ∉ memBar γ hγ b := by
  rintro ⟨a, ha, he⟩
  have hfix : a.perm x = x :=
    (supportedOn_of_mem_memAt ha x (by rw [range_emb]; exact_mod_cast hx)).2
  rcases mkQ_eq_iff.mp he with h1 | h1
  · rw [inv_mul_eq_one.mp h1] at hfix
    exact hwx hfix
  · have h2 : w = a * allOnes n := by
      rw [← h1]
      group
    apply hwx
    rw [h2, mul_perm]
    exact hfix

theorem exists_normalizing_memBar_pair (hn : 5 ≤ n) {β : Finset (Fin n)} (hβ : β.card = 4)
    {p q : Fin n} (hp : p ∈ β) (hq : q ∈ β) (hpq : p ≠ q) :
    ∃ v ∈ memBar β hβ true, v * v ≠ 1 ∧
      (∀ (γ : Finset (Fin n)) (hγ : γ.card = 4) (b : Bool), ¬ β ⊆ γ → v ∉ memBar γ hγ b) ∧
      ∀ (γ : Finset (Fin n)) (hγ : γ.card = 4), (γ ∩ β = {p, q} ∨ γ ∩ β = β \ {p, q}) →
        ∀ (b : Bool), ∀ a ∈ memBar γ hγ b, v * a * v⁻¹ ∈ memBar γ hγ b := by
  classical
  set κ := emb β hβ with hκdef
  have hκ : ∀ x, x ∈ Set.range κ ↔ x ∈ β := fun x => by rw [hκdef, range_emb]; rfl
  obtain ⟨j₁, hj₁⟩ := (hκ p).mpr hp
  obtain ⟨j₂, hj₂⟩ := (hκ q).mpr hq
  have hj : j₁ ≠ j₂ := fun h => hpq (by rw [← hj₁, ← hj₂, h])
  obtain ⟨k, hk, hk1, hk2, -, hkk⟩ := exists_kList_swap j₁ j₂ hj
  have hpairs := kList_pairs k hk hkk
  set w := embed κ k with hwdef
  have hwK : w ∈ memAt β hβ true := ⟨k, hk, rfl⟩
  have hws : SupportedOn w (Set.range κ) := supportedOn_of_mem_memAt (b := true) hwK
  refine ⟨mkQ n w, ⟨w, hwK, rfl⟩, fun h1 => hkk ?_, fun γ hγ b hβγ => ?_, fun γ hγ hcase b => ?_⟩
  ·
    rw [← map_mul, ← map_one (mkQ n)] at h1
    have h2 := mkQ_inj_of_supportedOn hn (hws.mul hws) (supportedOn_one _) h1
    apply embed_injective κ
    rw [map_mul, map_one]
    exact h2
  ·
    obtain ⟨x, hxβ, hxγ⟩ := Finset.not_subset.mp hβγ
    obtain ⟨i, rfl⟩ := (hκ x).mpr hxβ
    refine not_mem_memBar_of_perm hγ b hxγ ?_
    show embedPerm κ k.perm (κ i) ≠ κ i
    rw [embedPerm_apply]
    exact fun h => (hpairs i).2.1 (κ.injective h)
  ·
    have hγι : ∀ x, x ∈ Set.range (emb γ hγ) ↔ x ∈ γ := fun x => by rw [range_emb]; rfl
    obtain ⟨j, hjγ, hkjγ, hjint⟩ : ∃ j : Fin 4, κ j ∈ γ ∧ κ (k.perm j) ∈ γ ∧
        ∀ x ∈ γ, x ∈ β → x = κ j ∨ x = κ (k.perm j) := by
      rcases hcase with h | h
      · refine ⟨j₁, ?_, ?_, fun x hxγ hxβ => ?_⟩
        · have : p ∈ γ ∩ β := by rw [h]; simp
          rw [← hj₁] at this
          exact (Finset.mem_inter.mp this).1
        · have : q ∈ γ ∩ β := by rw [h]; simp
          rw [hk1, hj₂]
          exact (Finset.mem_inter.mp this).1
        · have : x ∈ γ ∩ β := Finset.mem_inter.mpr ⟨hxγ, hxβ⟩
          rw [h] at this
          rw [hk1, hj₁, hj₂]
          simpa using this
      ·
        have hsub : ({p, q} : Finset (Fin n)) ⊆ β := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hp
          · exact hq
        have hcard : (β \ {p, q}).card = 2 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hβ, Finset.card_pair hpq]
        obtain ⟨x₀, hx₀⟩ : (β \ {p, q}).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨hx₀β, hx₀pq⟩ := Finset.mem_sdiff.mp hx₀
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx₀pq
        obtain ⟨i, rfl⟩ := (hκ x₀).mpr hx₀β
        have hi1 : i ≠ j₁ := fun e => hx₀pq.1 (by rw [e, hj₁])
        have hi2 : i ≠ j₂ := fun e => hx₀pq.2 (by rw [e, hj₂])
        have hki1 : k.perm i ≠ j₁ := fun e => hi2 (by
          have := (hpairs i).1
          rw [e, hk1] at this
          exact this.symm)
        have hki2 : k.perm i ≠ j₂ := fun e => hi1 (by
          have := (hpairs i).1
          rw [e, hk2] at this
          exact this.symm)
        have hmem1 : κ i ∈ β \ {p, q} := hx₀
        have hmem2 : κ (k.perm i) ∈ β \ {p, q} := by
          refine Finset.mem_sdiff.mpr ⟨(hκ _).mp ⟨_, rfl⟩, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => hki1 (κ.injective (e.trans hj₁.symm)),
            fun e => hki2 (κ.injective (e.trans hj₂.symm))⟩
        have hne : κ i ≠ κ (k.perm i) := fun e => (hpairs i).2.1 (κ.injective e).symm
        have heq : β \ {p, q} = {κ i, κ (k.perm i)} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hmem1
            · exact hmem2
          · rw [hcard, Finset.card_pair hne]
        refine ⟨i, ?_, ?_, fun x hxγ hxβ => ?_⟩
        · have : κ i ∈ γ ∩ β := by rw [h]; exact hmem1
          exact (Finset.mem_inter.mp this).1
        · have : κ (k.perm i) ∈ γ ∩ β := by rw [h]; exact hmem2
          exact (Finset.mem_inter.mp this).1
        · have : x ∈ γ ∩ β := Finset.mem_inter.mpr ⟨hxγ, hxβ⟩
          rw [h, heq] at this
          simpa using this
    obtain ⟨hnK, hnK'⟩ := normalizes_embed_of_swap (emb γ hγ) κ hk hkk j ((hγι _).mpr hjγ)
      ((hγι _).mpr hkjγ) fun x hxι hxκ => hjint x ((hγι x).mp hxι) ((hκ x).mp hxκ)
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨w * a * w⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    cases b
    · exact hnK' a ha
    · exact hnK a ha

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
