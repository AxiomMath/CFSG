module

public import CFSG.ClassicalInvolution.Q3.AE.PermElt
public import CFSG.ClassicalInvolution.Q3.AE.Twins

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem eq_ofVec_mul_ofPerm (a : Wr n) : a = ofVec a.vec * ofPerm a.perm := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show a.vec i = a.vec i + 0
    rw [add_zero]
  · show a.perm = 1 * a.perm
    rw [one_mul]

theorem ofVec_conj_embed (ι : Fin 4 ↪ Fin n) (w : Fin n → ZMod 2) (a : Wr 4) :
    ofVec w * embed ι a * (ofVec w)⁻¹ = embed ι (ofVec (w ∘ ι) * a * (ofVec (w ∘ ι))⁻¹) := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · show w x + (embed ι a).vec x + w ((embed ι a).perm.symm x) =
      embedVec ι (fun i => w (ι i) + a.vec i + w (ι (a.perm.symm i))) x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, embed_vec, embedVec_apply, embed_perm, embedPerm_symm_apply]
    · rw [embedVec_of_not_mem ι _ hx, embed_vec, embedVec_of_not_mem ι _ hx, embed_perm,
        embedPerm_symm_of_not_mem ι _ hx, add_zero, zmod_two_add_self]
  · show 1 * embedPerm ι a.perm * 1⁻¹ = embedPerm ι (1 * a.perm * 1⁻¹)
    simp only [one_mul, inv_one, mul_one]

theorem local_swap_kList : ∀ i₁ i₂ : Fin 4, i₁ ≠ i₂ → ∀ w : Fin 4 → ZMod 2,
    (w i₁ + w i₂ = 1 ∧ ∀ i, i ≠ i₁ → i ≠ i₂ → w i = 0) →
    ∀ a ∈ kList, ofVec w * (ofPerm (Equiv.swap i₁ i₂) * a * (ofPerm (Equiv.swap i₁ i₂))⁻¹) *
      (ofVec w)⁻¹ ∈ kList := by
  decide +kernel

theorem exists_kList_swap : ∀ j₁ j₂ : Fin 4, j₁ ≠ j₂ → ∃ k ∈ kList, k.perm j₁ = j₂ ∧
    k.perm j₂ = j₁ ∧ k.vec j₁ + k.vec j₂ = 1 ∧ k * k ≠ 1 := by
  decide +kernel

theorem exists_normalizing_embed (ι κ : Fin 4 ↪ Fin n) {p q : Fin n} (hpq : p ≠ q)
    (hpι : p ∈ Set.range ι) (hqι : q ∈ Set.range ι) (hpκ : p ∈ Set.range κ)
    (hqκ : q ∈ Set.range κ)
    (hinter : ∀ x ∈ Set.range ι, x ∈ Set.range κ → x = p ∨ x = q) :
    ∃ v ∈ memK κ, v * v ≠ 1 ∧ ∀ a ∈ memK ι, v * a * v⁻¹ ∈ memK ι := by
  classical
  obtain ⟨i₁, hi₁⟩ := hpι
  obtain ⟨i₂, hi₂⟩ := hqι
  obtain ⟨j₁, hj₁⟩ := hpκ
  obtain ⟨j₂, hj₂⟩ := hqκ
  have hj : j₁ ≠ j₂ := fun h => hpq (by rw [← hj₁, ← hj₂, h])
  have hi : i₁ ≠ i₂ := fun h => hpq (by rw [← hi₁, ← hi₂, h])
  obtain ⟨k, hk, hk1, hk2, hkv, hkk⟩ := exists_kList_swap j₁ j₂ hj
  obtain ⟨v, hv⟩ : ∃ v, v = embed κ k := ⟨_, rfl⟩
  have hvp : v.perm = embedPerm κ k.perm := by rw [hv]; rfl
  have hvv : v.vec = embedVec κ k.vec := by rw [hv]; rfl
  have hout : ∀ i, i ≠ i₁ → i ≠ i₂ → ι i ∉ Set.range κ := fun i h1 h2 hκ => by
    rcases hinter _ ⟨i, rfl⟩ hκ with h | h
    · exact h1 (ι.injective (h.trans hi₁.symm))
    · exact h2 (ι.injective (h.trans hi₂.symm))
  have hτ1 : v.perm (ι i₁) = ι i₂ := by
    rw [hvp, hi₁, ← hj₁, embedPerm_apply, hk1, hj₂, hi₂]
  have hτ2 : v.perm (ι i₂) = ι i₁ := by
    rw [hvp, hi₂, ← hj₂, embedPerm_apply, hk2, hj₁, hi₁]
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
    rw [hvv, hi₁, hi₂, ← hj₁, ← hj₂, embedVec_apply, embedVec_apply, hkv]
  have hw0 : ∀ i, i ≠ i₁ → i ≠ i₂ → (v.vec ∘ ι) i = 0 := fun i h1 h2 => by
    show v.vec (ι i) = 0
    rw [hvv, embedVec_of_not_mem κ _ (hout i h1 h2)]
  refine ⟨v, ⟨k, hk, hv.symm⟩, fun h => hkk (embed_injective κ ?_), ?_⟩
  · rw [map_mul, map_one, ← hv]
    exact h
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨_, local_swap_kList i₁ i₂ hi _ ⟨hw1, hw0⟩ a ha, ?_⟩
    rw [← ofVec_conj_embed, ← hcs, ← ofPerm_conj_embed hc]
    conv_rhs => rw [eq_ofVec_mul_ofPerm v]
    group

theorem exists_normalizing_memBar (hn : 5 ≤ n) {α β : Finset (Fin n)} (h : α.card = 4)
    (h' : β.card = 4) (h2 : (α ∩ β).card = 2) :
    ∃ v ∈ memBar β h' true, v * v ≠ 1 ∧ ∀ a ∈ memBar α h true, v * a * v⁻¹ ∈ memBar α h true := by
  classical
  obtain ⟨p, q, hpq, hαβ⟩ := Finset.card_eq_two.mp h2
  have hp : p ∈ α ∩ β := by rw [hαβ]; simp
  have hq : q ∈ α ∩ β := by rw [hαβ]; simp
  have hι : ∀ x, x ∈ Set.range (emb α h) ↔ x ∈ α := fun x => by rw [range_emb]; rfl
  have hκ : ∀ x, x ∈ Set.range (emb β h') ↔ x ∈ β := fun x => by rw [range_emb]; rfl
  obtain ⟨v, hv, hvv, hvn⟩ := exists_normalizing_embed (emb α h) (emb β h') hpq
    ((hι p).mpr (Finset.mem_inter.mp hp).1) ((hι q).mpr (Finset.mem_inter.mp hq).1)
    ((hκ p).mpr (Finset.mem_inter.mp hp).2) ((hκ q).mpr (Finset.mem_inter.mp hq).2)
    (fun x hxα hxβ => by
      have hx : x ∈ α ∩ β := Finset.mem_inter.mpr ⟨(hι x).mp hxα, (hκ x).mp hxβ⟩
      rw [hαβ] at hx
      simpa using hx)
  have hvs : SupportedOn v (Set.range (emb β h')) := supportedOn_of_mem_memAt (b := true) hv
  refine ⟨mkQ n v, ⟨v, hv, rfl⟩, fun h1 => hvv ?_, ?_⟩
  · rw [← map_mul, ← map_one (mkQ n)] at h1
    exact mkQ_inj_of_supportedOn hn (hvs.mul hvs) (supportedOn_one _) h1
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨v * a * v⁻¹, hvn a ha, by rw [map_mul, map_mul, map_inv]⟩

theorem exists_mul_self_ne_one_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4)
    (b : Bool) : ∃ v ∈ memBar α h b, v * v ≠ 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_not_comm_memBar hn α h b
  refine ⟨x, hx, fun h2 => hxy ?_⟩
  rcases eq_of_mem_memBar_mul_self hn hx h2 with rfl | rfl
  · rw [one_mul, mul_one]
  · exact zBar_comm_memBar α h b y hy

theorem exists_normalizing_memBar_of_comm (hn : 5 ≤ n) {α β : Finset (Fin n)} {h : α.card = 4}
    {h' : β.card = 4} {b c : Bool}
    (hcomm : ∀ x ∈ memBar α h b, ∀ y ∈ memBar β h' c, x * y = y * x) :
    ∃ v ∈ memBar β h' c, v * v ≠ 1 ∧ ∀ a ∈ memBar α h b, v * a * v⁻¹ ∈ memBar α h b := by
  obtain ⟨v, hv, hvv⟩ := exists_mul_self_ne_one_memBar hn β h' c
  refine ⟨v, hv, hvv, fun a ha => ?_⟩
  rw [show v * a * v⁻¹ = a by rw [← hcomm a ha v hv]; group]
  exact ha

theorem comm_memBar_twin (α : Finset (Fin n)) (h : α.card = 4) :
    ∀ x ∈ memBar α h true, ∀ y ∈ memBar α h false, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
  rw [← map_mul, ← map_mul, comm_memK_memKStar (emb α h) a ha a' ha']

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
