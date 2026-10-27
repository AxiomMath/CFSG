module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Inv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma sec5b517_pair_compl :
    ∀ a : Fin 4, ∃ b c : Fin 4, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
  decide

private lemma sec5b517_conj_inf (H J : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊓ J) g = CFSG.conjugate H g ⊓ CFSG.conjugate J g := by
  unfold CFSG.conjugate
  exact Subgroup.map_inf H J _ (MulEquiv.injective (MulAut.conj g⁻¹))

private lemma sec5b517_map_injective {f : G →* G} (hf : Function.Injective f)
    {H J : Subgroup G} (h : H.map f = J.map f) : H = J := by
  apply le_antisymm
  · intro x hx
    have hx' : f x ∈ J.map f := by
      rw [← h]
      exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have hyx' : y = x := hf hyx
    rwa [hyx'] at hy
  · intro x hx
    have hx' : f x ∈ H.map f := by
      rw [h]
      exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have hyx' : y = x := hf hyx
    rwa [hyx'] at hy

private lemma sec5b517_conjugate_injective {g : G} {H J : Subgroup G}
    (h : CFSG.conjugate H g = CFSG.conjugate J g) : H = J := by
  unfold CFSG.conjugate at h
  exact sec5b517_map_injective (MulEquiv.injective (MulAut.conj g⁻¹)) h

private lemma sec5b517_conj_card (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H := by
  unfold CFSG.conjugate
  exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g⁻¹))

theorem Sec5B517Quad.mem_of_commute_pair (hq : Sec5B517Quad K z) {a b : Fin 4} (hab : a ≠ b)
    {x : G} (hx : x ∈ K a ⊔ K b) (h : ∀ v ∈ K a, x * v = v * x) : x ∈ K b := by
  obtain ⟨a', ha', b', hb', hx_eq⟩ := sec5b_mem_sup_of_comm (hq.comm a b hab) hx
  have hcomm : ∀ v ∈ K a, a' * v = v * a' := by
    intro v hv
    have hb'v : b' * v = v * b' := hq.comm b a hab.symm b' hb' v hv
    have h1 : x * v = v * x := h v hv
    rw [hx_eq] at h1
    have h2 : (a' * v) * b' = (v * a') * b' := by
      calc (a' * v) * b' = a' * (v * b') := by group
        _ = a' * (b' * v) := by rw [hb'v]
        _ = (a' * b') * v := by group
        _ = v * (a' * b') := h1
        _ = (v * a') * b' := by group
    exact mul_right_cancel h2
  rcases hq.eq_of_central ha' hcomm with h1 | hz
  · rw [hx_eq, h1, one_mul]
    exact hb'
  · rw [hx_eq, hz]
    exact (K b).mul_mem (hq.z_mem b) hb'

theorem Sec5B517Quad.pair_ne (hq : Sec5B517Quad K z) {a b c : Fin 4} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : K a ⊔ K b ≠ K a ⊔ K c := by
  intro heq
  obtain ⟨u, hu, hu2⟩ := hq.exists_sq b
  have hua : u ∈ K a ⊔ K c := by
    have h1 : u ∈ K a ⊔ K b := Subgroup.mem_sup_right hu
    rwa [heq] at h1
  have hcomm : ∀ v ∈ K b, u * v = v * u := by
    intro v hv
    have hle := Sec5B517Quad.le_centralizer_of_mem_pair hq (l := b) hab.symm hbc hua
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
  rcases hq.eq_of_central hu hcomm with h1 | hz
  · rw [h1, one_mul] at hu2
    exact hq.z_ne hu2.symm
  · rw [hz, hq.z_sq] at hu2
    exact hq.z_ne hu2.symm

theorem Sec5B517Quad.sup_inf_eq (hq : Sec5B517Quad K z) {a b c : Fin 4} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : (K a ⊔ K b) ⊓ (K a ⊔ K c) = K a := by
  apply le_antisymm
  · intro x hx
    have hxb : ∀ v ∈ K b, x * v = v * x := by
      intro v hv
      have hle := Sec5B517Quad.le_centralizer_of_mem_pair hq (l := b) hab.symm hbc hx.2
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
    have hx' : x ∈ K b ⊔ K a := by
      rw [sup_comm]
      exact hx.1
    exact Sec5B517Quad.mem_of_commute_pair hq hab.symm hx' hxb
  · intro x hx
    exact ⟨Subgroup.mem_sup_left hx, Subgroup.mem_sup_left hx⟩

theorem Sec5B517Quad.pair_inf_le (hq : Sec5B517Quad K z) {i j k l : Fin 4} (hij : i ≠ j)
    (hkl : k ≠ l) (hne : K i ⊔ K j ≠ K k ⊔ K l) :
    ∃ m : Fin 4, (K i ⊔ K j) ⊓ (K k ⊔ K l) ≤ K m := by
  have hnotboth : ¬ ((k = i ∨ k = j) ∧ (l = i ∨ l = j)) := by
    rintro ⟨hk, hl⟩
    rcases hk with hk | hk <;> rcases hl with hl | hl
    · exact hkl (hk.trans hl.symm)
    · apply hne
      rw [hk, hl]
    · apply hne
      rw [hk, hl, sup_comm]
    · exact hkl (hk.trans hl.symm)
  by_cases hk : k = i ∨ k = j
  · have hl : ¬ (l = i ∨ l = j) := fun hl => hnotboth ⟨hk, hl⟩
    have hli : l ≠ i := fun h => hl (Or.inl h)
    have hlj : l ≠ j := fun h => hl (Or.inr h)
    refine ⟨k, ?_⟩
    intro x hx
    have hxc : ∀ v ∈ K l, x * v = v * x := by
      intro v hv
      have hle := Sec5B517Quad.le_centralizer_of_mem_pair hq (l := l) hli hlj hx.1
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
    have hx2' : x ∈ K l ⊔ K k := by
      rw [sup_comm]
      exact hx.2
    exact Sec5B517Quad.mem_of_commute_pair hq hkl.symm hx2' hxc
  · have hki : k ≠ i := fun h => hk (Or.inl h)
    have hkj : k ≠ j := fun h => hk (Or.inr h)
    refine ⟨l, ?_⟩
    intro x hx
    have hxc : ∀ v ∈ K k, x * v = v * x := by
      intro v hv
      have hle := Sec5B517Quad.le_centralizer_of_mem_pair hq (l := k) hki hkj hx.1
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
    exact Sec5B517Quad.mem_of_commute_pair hq hkl hx.2 hxc

theorem Sec5B517Quad.conj_family [Finite G] (hq : Sec5B517Quad K z) {g : G}
    (hg : ∀ k l : Fin 4, k ≠ l →
      ∃ k' l' : Fin 4, k' ≠ l' ∧ CFSG.conjugate (K k ⊔ K l) g = K k' ⊔ K l')
    (a : Fin 4) : ∃ m : Fin 4, CFSG.conjugate (K a) g = K m := by
  obtain ⟨b, c, hba, hca, hbc⟩ := sec5b517_pair_compl a
  have hab : a ≠ b := fun h => hba h.symm
  have hac : a ≠ c := fun h => hca h.symm
  obtain ⟨k', l', hkl', hconj_ab⟩ := hg a b hab
  obtain ⟨k'', l'', hkl'', hconj_ac⟩ := hg a c hac
  have hne_conj : CFSG.conjugate (K a ⊔ K b) g ≠ CFSG.conjugate (K a ⊔ K c) g := by
    intro heq
    exact Sec5B517Quad.pair_ne hq hab hac hbc (sec5b517_conjugate_injective heq)
  have hne_kl : K k' ⊔ K l' ≠ K k'' ⊔ K l'' := by
    intro heq
    apply hne_conj
    rw [hconj_ab, hconj_ac, heq]
  obtain ⟨m, hm⟩ := Sec5B517Quad.pair_inf_le hq hkl' hkl'' hne_kl
  have hKa : CFSG.conjugate (K a) g = (K k' ⊔ K l') ⊓ (K k'' ⊔ K l'') := by
    rw [← Sec5B517Quad.sup_inf_eq hq hab hac hbc]
    rw [sec5b517_conj_inf, hconj_ab, hconj_ac]
  refine ⟨m, ?_⟩
  have hle : CFSG.conjugate (K a) g ≤ K m := by
    rw [hKa]
    exact hm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [sec5b517_conj_card, hq.card_eq a m]

end CFSG.OddStandard.SmallF3.Omega
