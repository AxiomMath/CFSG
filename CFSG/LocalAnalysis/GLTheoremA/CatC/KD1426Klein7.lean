module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Klein
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Orbit

public section

open Equiv CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Orbit CFSG.LocalAnalysis.GLTheoremA.KD264Rank

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Klein

theorem conj_mul_swap (δ : Perm (Fin 7)) (p q r s : Fin 7) :
    δ * (swap p q * swap r s) * δ⁻¹ = swap (δ p) (δ q) * swap (δ r) (δ s) := by
  calc δ * (swap p q * swap r s) * δ⁻¹ = (δ * swap p q * δ⁻¹) * (δ * swap r s * δ⁻¹) := by group
    _ = swap (δ p) (δ q) * swap (δ r) (δ s) := by rw [conj_swap, conj_swap]

theorem conj_mem_kleinSub {x y z f : Fin 7} (h : Distinct4 x y z f) {δ : Perm (Fin 7)}
    (hf : δ f = f) (hx : δ x = x ∨ δ x = y ∨ δ x = z) (hy : δ y = x ∨ δ y = y ∨ δ y = z)
    (hz : δ z = x ∨ δ z = y ∨ δ z = z) (hxy : δ x ≠ δ y) (hxz : δ x ≠ δ z) (hyz : δ y ≠ δ z)
    {τ : Perm (Fin 7)} (hτ : τ ∈ kleinSub h) : δ * τ * δ⁻¹ ∈ kleinSub h := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hd : Distinct4 x y z f := ⟨h1, h2, h3, h4, h5, h6⟩
  rw [mem_kleinSub] at hτ ⊢
  rcases hτ with rfl | rfl | rfl | rfl
  · left
    simp
  · have key : δ * kU1 x y z f * δ⁻¹ = swap (δ x) (δ y) * swap (δ z) f := by
      show δ * (swap x y * swap z f) * δ⁻¹ = _
      rw [conj_mul_swap, hf]
    rw [key]
    exact mem_kleinCarrier.1 (swap_mul_swap_mem_klein hd hx hy hz hxy hxz hyz)
  · have key : δ * kU2 x y z f * δ⁻¹ = swap (δ y) (δ z) * swap (δ x) f := by
      show δ * (swap y z * swap x f) * δ⁻¹ = _
      rw [conj_mul_swap, hf]
    rw [key]
    exact mem_kleinCarrier.1 (swap_mul_swap_mem_klein hd hy hz hx hyz hxy.symm hxz.symm)
  · have key : δ * kU3 x y z f * δ⁻¹ = swap (δ x) (δ z) * swap (δ y) f := by
      show δ * (swap x z * swap y f) * δ⁻¹ = _
      rw [conj_mul_swap, hf]
    rw [key]
    exact mem_kleinCarrier.1 (swap_mul_swap_mem_klein hd hx hz hy hxz hxy hyz.symm)

theorem conj_kU_case1 {σ : Perm (Fin 7)} {x y z f : Fin 7} (h1 : σ x = y) (h2 : σ y = z)
    (h3 : σ z = x) (hf : σ f = f) :
    σ * kU1 x y z f * σ⁻¹ = kU2 x y z f ∧ σ * kU2 x y z f * σ⁻¹ = kU3 x y z f ∧
      σ * kU3 x y z f * σ⁻¹ = kU1 x y z f := by
  refine ⟨?_, ?_, ?_⟩
  · show σ * (swap x y * swap z f) * σ⁻¹ = swap y z * swap x f
    rw [conj_mul_swap, h1, h2, h3, hf]
  · show σ * (swap y z * swap x f) * σ⁻¹ = swap x z * swap y f
    rw [conj_mul_swap, h2, h3, h1, hf, swap_comm z x]
  · show σ * (swap x z * swap y f) * σ⁻¹ = swap x y * swap z f
    rw [conj_mul_swap, h1, h3, h2, hf, swap_comm y x]

theorem conj_kU_case2 {σ : Perm (Fin 7)} {x y z f : Fin 7} (h1 : σ x = z) (h2 : σ y = x)
    (h3 : σ z = y) (hf : σ f = f) :
    σ * kU1 x y z f * σ⁻¹ = kU3 x y z f ∧ σ * kU2 x y z f * σ⁻¹ = kU1 x y z f ∧
      σ * kU3 x y z f * σ⁻¹ = kU2 x y z f := by
  refine ⟨?_, ?_, ?_⟩
  · show σ * (swap x y * swap z f) * σ⁻¹ = swap x z * swap y f
    rw [conj_mul_swap, h1, h2, h3, hf, swap_comm z x]
  · show σ * (swap y z * swap x f) * σ⁻¹ = swap x y * swap z f
    rw [conj_mul_swap, h2, h3, h1, hf]
  · show σ * (swap x z * swap y f) * σ⁻¹ = swap y z * swap x f
    rw [conj_mul_swap, h1, h3, h2, hf, swap_comm z y]

theorem comm_cover {σ : Perm (Fin 7)} {x y z f : Fin 7} (h : Distinct4 x y z f) (hf : σ f = f)
    (hor : (σ x = y ∧ σ y = z ∧ σ z = x) ∨ (σ x = z ∧ σ y = x ∧ σ z = y))
    {t : Perm (Fin 7)} (ht : t ∈ kleinSub h) :
    ∃ s ∈ kleinSub h, σ * s * σ⁻¹ * s⁻¹ = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hd : Distinct4 x y z f := ⟨h1, h2, h3, h4, h5, h6⟩
  rw [mem_kleinSub] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, (mem_kleinSub hd).2 (Or.inl rfl), by simp⟩
  · rcases hor with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case1 e1 e2 e3 hf
      refine ⟨kU2 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [c2, inv_eq_of_mul_eq_one_right (kU2_mul_kU2 hd), kU32 hd]
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case2 e1 e2 e3 hf
      refine ⟨kU3 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      rw [c3, inv_eq_of_mul_eq_one_right (kU3_mul_kU3 hd), kU23 hd]
  · rcases hor with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case1 e1 e2 e3 hf
      refine ⟨kU3 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      rw [c3, inv_eq_of_mul_eq_one_right (kU3_mul_kU3 hd), kU13 hd]
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case2 e1 e2 e3 hf
      refine ⟨kU1 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inl rfl)), ?_⟩
      rw [c1, inv_eq_of_mul_eq_one_right (kU1_mul_kU1 hd), kU31 hd]
  · rcases hor with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case1 e1 e2 e3 hf
      refine ⟨kU1 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inl rfl)), ?_⟩
      rw [c1, inv_eq_of_mul_eq_one_right (kU1_mul_kU1 hd), kU21 hd]
    · obtain ⟨c1, c2, c3⟩ := conj_kU_case2 e1 e2 e3 hf
      refine ⟨kU2 x y z f, (mem_kleinSub hd).2 (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [c2, inv_eq_of_mul_eq_one_right (kU2_mul_kU2 hd), kU12 hd]

theorem klein7 (D : Subgroup (alternatingGroup (Fin 7))) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 9) :
    ∃ T : Subgroup (alternatingGroup (Fin 7)), IsElemAbelian 2 T ∧ Nat.card T = 4 ∧
      (∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T) ∧
      (∀ t ∈ T, ∃ d ∈ D, ∃ s ∈ T, d * s * d⁻¹ * s⁻¹ = t) := by
  classical
  have hinj : Function.Injective (alternatingGroup (Fin 7)).subtype :=
    (alternatingGroup (Fin 7)).subtype_injective
  have hPel : IsElemAbelian 3 (D.map (alternatingGroup (Fin 7)).subtype) :=
    isElemAbelian_map hinj hD
  have hPcard : Nat.card (D.map (alternatingGroup (Fin 7)).subtype) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  obtain ⟨-, hex⟩ := orbit_pCycles (n := 7) Nat.prime_three (le_refl 3)
    (D.map (alternatingGroup (Fin 7)).subtype) hPel (by rw [hPcard]; norm_num)
  obtain ⟨a', b', ha', hb', A, B, hA, hB, hdisj, hAs, hBs⟩ := hex (by norm_num)
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hb'
  have hsA : ∀ t, (a : Perm (Fin 7)) t ≠ t ↔ t ∈ A := fun t => by
    simpa using hAs 1 (by norm_num) t
  have hsB : ∀ t, (b : Perm (Fin 7)) t ≠ t ↔ t ∈ B := fun t => by
    simpa using hBs 1 (by norm_num) t
  have hABc : (A ∪ B).card = 6 := by rw [Finset.card_union_of_disjoint hdisj, hA, hB]
  have hcompc : (A ∪ B)ᶜ.card = 1 := by rw [Finset.card_compl, hABc]; simp
  obtain ⟨f, hf⟩ := Finset.card_eq_one.1 hcompc
  have hfAB : f ∉ A ∪ B := by
    intro hm
    have : f ∈ (A ∪ B)ᶜ := by rw [hf]; exact Finset.mem_singleton_self f
    exact (Finset.mem_compl.1 this) hm
  obtain ⟨x, y, z, hxy, hxz, hyz, hAeq⟩ := Finset.card_eq_three.1 hA
  have hxA : x ∈ A := by rw [hAeq]; simp
  have hyA : y ∈ A := by rw [hAeq]; simp
  have hzA : z ∈ A := by rw [hAeq]; simp
  have hfA : f ∉ A := fun h => hfAB (Finset.mem_union_left _ h)
  have hfB : f ∉ B := fun h => hfAB (Finset.mem_union_right _ h)
  have hdist : Distinct4 x y z f := ⟨hxy, hxz, hyz,
    fun e => hfA (e ▸ hxA), fun e => hfA (e ▸ hyA), fun e => hfA (e ▸ hzA)⟩
  have hA' : ∀ t, (a : Perm (Fin 7)) t ≠ t ↔ (t = x ∨ t = y ∨ t = z) := by
    intro t; rw [hsA t, hAeq]; simp
  have horient := cycle_orientation hxy hxz hyz hA'
  have haf : (a : Perm (Fin 7)) f = f := by
    by_contra h; exact hfA ((hsA f).1 h)
  have hcomm : ∀ g ∈ D, ∀ d ∈ D, ∀ t, (g : Perm (Fin 7)) ((d : Perm (Fin 7)) t) =
      (d : Perm (Fin 7)) ((g : Perm (Fin 7)) t) := by
    intro g hg d hd t
    have h1 := hD.1.is_comm.comm (⟨g, hg⟩ : ↥D) ⟨d, hd⟩
    have h2 := congrArg (fun k : ↥D => ((k : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) t) h1
    simpa using h2
  have hpresA : ∀ d ∈ D, ∀ t, (d : Perm (Fin 7)) t ∈ A ↔ t ∈ A := by
    intro d hd t
    rw [← hsA ((d : Perm (Fin 7)) t), ← hsA t, hcomm a ha d hd t,
      (d : Perm (Fin 7)).injective.ne_iff]
  have hpresB : ∀ d ∈ D, ∀ t, (d : Perm (Fin 7)) t ∈ B ↔ t ∈ B := by
    intro d hd t
    rw [← hsB ((d : Perm (Fin 7)) t), ← hsB t, hcomm b hb d hd t,
      (d : Perm (Fin 7)).injective.ne_iff]
  have hfix : ∀ d ∈ D, (d : Perm (Fin 7)) f = f := by
    intro d hd
    have h1 : (d : Perm (Fin 7)) f ∉ A := fun h => hfA ((hpresA d hd f).1 h)
    have h2 : (d : Perm (Fin 7)) f ∉ B := fun h => hfB ((hpresB d hd f).1 h)
    have : (d : Perm (Fin 7)) f ∈ ({f} : Finset (Fin 7)) := by
      rw [← hf]
      simp [h1, h2]
    exact Finset.mem_singleton.1 this
  have hpt : ∀ d ∈ D, ∀ t : Fin 7, (d : Perm (Fin 7)) t ∈ ({x, y, z} : Finset (Fin 7)) ↔
      t ∈ ({x, y, z} : Finset (Fin 7)) := fun d hd t => by
    rw [← hAeq]; exact hpresA d hd t
  have hTmem : ∀ t : ↥(alternatingGroup (Fin 7)), t ∈ kleinA7 hdist ↔
      (t : Perm (Fin 7)) ∈ kleinSub hdist := fun t => Subgroup.mem_subgroupOf
  refine ⟨kleinA7 hdist, ⟨⟨⟨fun t s => ?_⟩⟩, ?_⟩, card_kleinA7 hdist, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have ht := (hTmem t).1 t.2
    have hs := (hTmem s).1 s.2
    simp only [Subgroup.coe_mul]
    rw [mem_kleinSub] at ht hs
    rcases ht with ht | ht | ht | ht <;> rcases hs with hs | hs | hs | hs <;> rw [ht, hs] <;>
      simp [kU12 hdist, kU21 hdist, kU13 hdist, kU31 hdist, kU23 hdist, kU32 hdist]
  · intro t ht
    apply Subtype.ext
    have ht' := (hTmem t).1 ht
    rw [mem_kleinSub] at ht'
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rcases ht' with h | h | h | h <;> rw [h] <;>
      simp [sq, kU1_mul_kU1 hdist, kU2_mul_kU2 hdist, kU3_mul_kU3 hdist]
  · intro d hd t ht
    rw [hTmem] at ht ⊢
    have hc : (((d * t * d⁻¹ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))) =
        (d : Perm (Fin 7)) * (t : Perm (Fin 7)) * (d : Perm (Fin 7))⁻¹ := by simp
    rw [hc]
    have hx := (hpt d hd x).2 (by simp)
    have hy := (hpt d hd y).2 (by simp)
    have hz := (hpt d hd z).2 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    exact conj_mem_kleinSub hdist (hfix d hd) hx hy hz
      ((d : Perm (Fin 7)).injective.ne hxy) ((d : Perm (Fin 7)).injective.ne hxz)
      ((d : Perm (Fin 7)).injective.ne hyz) ht
  · intro t ht
    have ht' := (hTmem t).1 ht
    obtain ⟨s0, hs0, hcomm0⟩ := comm_cover hdist haf horient ht'
    refine ⟨a, ha, ⟨s0, kU_mem_alt hdist s0 hs0⟩, (hTmem _).2 hs0, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcomm0

end CFSG.LocalAnalysis.GLTheoremA.KD1426Klein

end
