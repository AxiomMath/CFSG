module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Iso

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma sec5b517_prod_eq_one_or_z {z : G} {k : Fin 4 → G} (hz2 : z * z = 1)
    (hk : ∀ i, k i = 1 ∨ k i = z) : Sec5B517Prod k = 1 ∨ Sec5B517Prod k = z := by
  rcases hk 0 with h0 | h0 <;> rcases hk 1 with h1 | h1 <;>
    rcases hk 2 with h2 | h2 <;> rcases hk 3 with h3 | h3 <;>
    simp [Sec5B517Prod, h0, h1, h2, h3, hz2]

private lemma sec5b517_pattern {z : G} {s : Fin 4 → G} (hs : ∀ i, s i = 1 ∨ s i = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hprod : Sec5B517Prod s = 1) :
    (∀ i, s i = z) ∨ (∀ i, s i = 1) ∨
      ∃ i j : Fin 4, i ≠ j ∧ s i = z ∧ s j = z ∧ ∀ m, m ≠ i → m ≠ j → s m = 1 := by
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;>
    rcases hs 2 with h2 | h2 <;> rcases hs 3 with h3 | h3
  · exact Or.inr (Or.inl fun i => by fin_cases i <;> assumption)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exact Or.inr (Or.inr ⟨2, 3, by decide, h2, h3, fun m hm2 hm3 => by
      fin_cases m <;> simp_all⟩)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exact Or.inr (Or.inr ⟨1, 3, by decide, h1, h3, fun m hm1 hm3 => by
      fin_cases m <;> simp_all⟩)
  · exact Or.inr (Or.inr ⟨1, 2, by decide, h1, h2, fun m hm1 hm2 => by
      fin_cases m <;> simp_all⟩)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exact Or.inr (Or.inr ⟨0, 3, by decide, h0, h3, fun m hm0 hm3 => by
      fin_cases m <;> simp_all⟩)
  · exact Or.inr (Or.inr ⟨0, 2, by decide, h0, h2, fun m hm0 hm2 => by
      fin_cases m <;> simp_all⟩)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exact Or.inr (Or.inr ⟨0, 1, by decide, h0, h1, fun m hm0 hm1 => by
      fin_cases m <;> simp_all⟩)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exfalso
    exact hz1 (by simpa [Sec5B517Prod, h0, h1, h2, h3, hz2] using hprod)
  · exact Or.inl fun i => by fin_cases i <;> assumption

private lemma sec5b517_prod_mem_sup (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {k : Fin 4 → G} (hk : ∀ m, k m ∈ K m)
    (hkz : ∀ m, m ≠ i → m ≠ j → k m = 1 ∨ k m = z) :
    Sec5B517Prod k ∈ K i ⊔ K j := by
  have hmem : ∀ m, k m ∈ K i ⊔ K j := by
    intro m
    by_cases hmi : m = i
    · subst hmi; exact Subgroup.mem_sup_left (hk m)
    · by_cases hmj : m = j
      · subst hmj; exact Subgroup.mem_sup_right (hk m)
      · rcases hkz m hmi hmj with h | h
        · rw [h]; exact (K i ⊔ K j).one_mem
        · rw [h]; exact Subgroup.mem_sup_left (hq.z_mem i)
  rw [Sec5B517Prod]
  exact (K i ⊔ K j).mul_mem ((K i ⊔ K j).mul_mem
    ((K i ⊔ K j).mul_mem (hmem 0) (hmem 1)) (hmem 2)) (hmem 3)

private lemma sec5b517_not_mem_of_sq (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j)
    {a : G} (ha : a ∈ K i) (ha2 : a * a = z) (haj : a ∈ K j) : False := by
  have hcent : ∀ v ∈ K i, a * v = v * a := fun v hv => hq.comm j i hij.symm a haj v hv
  rcases hq.eq_of_central ha hcent with h | h
  · rw [h] at ha2
    exact hq.z_ne (by simpa using ha2.symm)
  · rw [h, hq.z_sq] at ha2
    exact hq.z_ne ha2.symm

private lemma sec5b517_exists_ne_ne : ∀ i j : Fin 4, ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by
  decide

theorem Sec5B517Quad.le_centralizer_of_mem_pair (hq : Sec5B517Quad K z) {i j l : Fin 4}
    (hli : l ≠ i) (hlj : l ≠ j) {d : G} (hd : d ∈ K i ⊔ K j) :
    K l ≤ centralizer ({d} : Set G) := by
  have hKi : K i ≤ centralizer (K l : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hq.comm i l (Ne.symm hli) v hv w hw).symm
  have hKj : K j ≤ centralizer (K l : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hq.comm j l (Ne.symm hlj) v hv w hw).symm
  have hdcl : d ∈ centralizer (K l : Set G) := (sup_le hKi hKj) hd
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hdcl) v hv

theorem Sec5B517Quad.pair_mem_Q8 (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {d : G}
    (hd : d ∈ K i ⊔ K j) (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z) :
    d ∈ Sec5B517Q8 hq := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hd_eq, ha2, hb2⟩ :=
    sec5b513_decomp (Classical.choice (hq.iso i)) (Classical.choice (hq.iso j))
      (hq.comm i j hij) (hq.z_mem i) (hq.z_mem j) hq.z_sq hq.z_ne hd hd2 hd1 hdz
  have ha4 : a₀ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ha2, hq.z_sq]
  have hb4 : b₀ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hb2, hq.z_sq]
  rw [hd_eq]
  exact (Sec5B517Q8 hq).mul_mem (Sec5B517Q8.mem_of_mem hq ha₀ ha4)
    (Sec5B517Q8.mem_of_mem hq hb₀ hb4)

theorem Sec5B517Quad.exists_pair_invol (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) :
    ∃ d : G, d ∈ K i ⊔ K j ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ z ∧
      ∀ l : Fin 4, l ≠ i → l ≠ j → K l ≤ centralizer ({d} : Set G) := by
  obtain ⟨a, ha, ha2⟩ := hq.exists_sq i
  obtain ⟨b, hb, hb2⟩ := hq.exists_sq j
  have hab : Commute a b := hq.comm i j hij a ha b hb
  have hsq : (a * b) * (a * b) = 1 := by
    rw [← pow_two (a * b), hab.mul_pow 2, pow_two a, pow_two b, ha2, hb2, hq.z_sq]
  have haKj : a ∉ K j := by
    intro haj
    exact sec5b517_not_mem_of_sq hq hij ha ha2 haj
  refine ⟨a * b, Subgroup.mul_mem_sup ha hb, hsq, ?_, ?_, ?_⟩
  · intro h
    exact haKj (by
      rw [show a = b⁻¹ from eq_inv_of_mul_eq_one_left h]
      exact (K j).inv_mem hb)
  · intro h
    exact haKj (by
      rw [show a = z * b⁻¹ from by rw [← h, mul_assoc, mul_inv_cancel, mul_one]]
      exact (K j).mul_mem (hq.z_mem j) ((K j).inv_mem hb))
  · intro l hli hlj
    exact Sec5B517Quad.le_centralizer_of_mem_pair hq hli hlj (Subgroup.mul_mem_sup ha hb)

theorem Sec5B517Quad.invol_cases (hq : Sec5B517Quad K z) {d : G} (hd : d ∈ Sec5B517Q8 hq)
    (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z) :
    (∃ k : Fin 4 → G, (∀ i, k i ∈ K i ∧ k i * k i = z) ∧ d = Sec5B517Prod k) ∨
      ∃ i j : Fin 4, i ≠ j ∧ d ∈ K i ⊔ K j := by
  obtain ⟨k, hk, hd_eq⟩ := (Sec5B517Q8.mem_iff hq).mp hd
  have hs : ∀ i, k i * k i = 1 ∨ k i * k i = z := fun i =>
    hq.sq_of_pow4 (hk i).1 (hk i).2
  have hprod : Sec5B517Prod (fun i => k i * k i) = 1 := by
    rw [← sec5b517_prod_mul hq (fun i => (hk i).1) (fun i => (hk i).1), ← hd_eq, hd2]
  rcases sec5b517_pattern hs hq.z_sq hq.z_ne hprod with
    hallz | hall1 | ⟨i, j, hij, hsi, hsj, hrest⟩
  · exact Or.inl ⟨k, fun i => ⟨(hk i).1, hallz i⟩, hd_eq⟩
  · exfalso
    have hkz : ∀ i, k i = 1 ∨ k i = z := fun i => hq.eq_of_sq (hk i).1 (hall1 i)
    rcases sec5b517_prod_eq_one_or_z hq.z_sq hkz with h | h
    · exact hd1 (by rw [hd_eq]; exact h)
    · exact hdz (by rw [hd_eq]; exact h)
  · exact Or.inr ⟨i, j, hij, by
      rw [hd_eq]
      exact sec5b517_prod_mem_sup hq hij (fun m => (hk m).1)
        (fun m hm1 hm2 => hq.eq_of_sq (hk m).1 (hrest m hm1 hm2))⟩

theorem Sec5B517Quad.type4_of_noncentral (hq : Sec5B517Quad K z) {d : G}
    (hd : d ∈ Sec5B517Q8 hq) (hd2 : d * d = 1) (hd1 : d ≠ 1) (hdz : d ≠ z)
    (hnc : ∀ i : Fin 4, ¬ K i ≤ centralizer ({d} : Set G)) :
    ∃ k : Fin 4 → G, (∀ i, k i ∈ K i ∧ k i * k i = z) ∧ d = Sec5B517Prod k := by
  rcases Sec5B517Quad.invol_cases hq hd hd2 hd1 hdz with h | ⟨i, j, hij, hdij⟩
  · exact h
  · exfalso
    obtain ⟨l, hli, hlj⟩ := sec5b517_exists_ne_ne i j
    exact hnc l (Sec5B517Quad.le_centralizer_of_mem_pair hq hli hlj hdij)

theorem Sec5B517Quad.type4_conj (hq : Sec5B517Quad K z) {k k' : Fin 4 → G}
    (hk : ∀ i, k i ∈ K i ∧ k i * k i = z) (hk' : ∀ i, k' i ∈ K i ∧ k' i * k' i = z) :
    ∃ y : G, y⁻¹ * Sec5B517Prod k * y = Sec5B517Prod k' := by
  choose u hu hconj using fun i =>
    sec5b513_conj_of_sq (Classical.choice (hq.iso i)) (hq.z_mem i) hq.z_sq hq.z_ne
      (hk i).1 (hk' i).1 (hk i).2 (hk' i).2
  refine ⟨Sec5B517Prod u, ?_⟩
  rw [sec5b517_prod_conj hq hu (fun i => (hk i).1),
    show (fun i => (u i)⁻¹ * k i * u i) = k' from funext fun i => hconj i]

end CFSG.OddStandard.SmallF3.Omega
