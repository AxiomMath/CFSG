module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888ParC

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

private lemma s888parD_mem_conjugate_iff {A : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma s888parD_conj_mem {l : Fin 4} {g x : G} (hgK : CFSG.conjugate (K l) g = K l)
    (hx : x ∈ K l) : g⁻¹ * x * g ∈ K l := by
  have h : g⁻¹ * x * g ∈ CFSG.conjugate (K l) g := by
    rw [s888parD_mem_conjugate_iff]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx
  rwa [hgK] at h

private lemma s888parD_mem_core [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) {q : G} :
    q ∈ twoCoreIn (K i) ↔ q ∈ K i ∧ q ^ 4 = 1 := by
  rw [twoCoreIn_eq_inf hq i, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, Sec5B517Q8.pow_four hq h1⟩
  · rintro ⟨h2, h4⟩
    exact ⟨Sec5B517Q8.mem_of_mem hq h2 h4, h2⟩

private lemma s888parD_fix_mul {g x y : G} (hgz : g⁻¹ * z * g = z) (hz2 : z * z = 1)
    (hzy : z * y = y * z) (hx : g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x * z)
    (hy : g⁻¹ * y * g = y ∨ g⁻¹ * y * g = y * z) :
    g⁻¹ * (x * y) * g = x * y ∨ g⁻¹ * (x * y) * g = x * y * z := by
  have e : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
  rw [e]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · exact Or.inl rfl
  · exact Or.inr (mul_assoc _ _ _).symm
  · right
    calc x * z * y = x * (z * y) := mul_assoc _ _ _
      _ = x * (y * z) := by rw [hzy]
      _ = x * y * z := (mul_assoc _ _ _).symm
  · left
    calc x * z * (y * z) = x * (z * y) * z := by group
      _ = x * (y * z) * z := by rw [hzy]
      _ = x * y * (z * z) := by group
      _ = x * y := by rw [hz2, mul_one]

private lemma s888parD_fix_mulz {g x : G} (hgz : g⁻¹ * z * g = z)
    (hx : g⁻¹ * x * g = x ∨ g⁻¹ * x * g = x * z) :
    g⁻¹ * (x * z) * g = x * z ∨ g⁻¹ * (x * z) * g = x * z * z := by
  have e : g⁻¹ * (x * z) * g = (g⁻¹ * x * g) * z := by
    calc g⁻¹ * (x * z) * g = (g⁻¹ * x * g) * (g⁻¹ * z * g) := by group
      _ = (g⁻¹ * x * g) * z := by rw [hgz]
  rw [e]
  rcases hx with hx | hx <;> rw [hx]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem par_plane_dich [Finite G] (hq : Sec5B517Quad K z) (l : Fin 4) {g a₀ a₁ : G}
    (ha₀ : a₀ ∈ K l) (ha₁ : a₁ ∈ K l) (h₀ : a₀ * a₀ = z) (h₁ : a₁ * a₁ = z) (hne : a₁ ≠ a₀)
    (hne' : a₁ ≠ a₀ * z) (hgz : g * z = z * g) (hgK : CFSG.conjugate (K l) g = K l)
    (hg0 : g⁻¹ * a₀ * g = a₀ ∨ g⁻¹ * a₀ * g = a₀ * z) :
    (¬ ParNt K z g l ∧ (g⁻¹ * a₁ * g = a₁ ∨ g⁻¹ * a₁ * g = a₁ * z)) ∨
      (ParNt K z g l ∧ (g⁻¹ * a₁ * g = a₀ * a₁ ∨ g⁻¹ * a₁ * g = a₀ * a₁ * z)) := by
  have hz2 : z * z = 1 := hq.z_sq
  have hzne : z ≠ 1 := hq.z_ne
  have hgzc : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  have hgzc' : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hgz]
      _ = z := by group
  have hpow4 : ∀ {a : G}, a * a = z → a ^ 4 = 1 := fun {a} h => by
    have e : a ^ 4 = (a * a) * (a * a) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [e, h, hz2]
  have ha₀1 : a₀ ≠ 1 := fun h => hzne (by rw [h, one_mul] at h₀; exact h₀.symm)
  have ha₀z : a₀ ≠ z := fun h => hzne (by rw [h] at h₀; exact h₀.symm.trans hz2)
  have hcK : g⁻¹ * a₁ * g ∈ K l := s888parD_conj_mem hgK ha₁
  have hcc : (g⁻¹ * a₁ * g) * (g⁻¹ * a₁ * g) = z := by
    calc (g⁻¹ * a₁ * g) * (g⁻¹ * a₁ * g) = g⁻¹ * (a₁ * a₁) * g := by group
      _ = g⁻¹ * z * g := by rw [h₁]
      _ = z := hgzc
  have hc4 : (g⁻¹ * a₁ * g) ^ 4 = 1 := hpow4 hcc
  have hg0' : g * a₀ * g⁻¹ = a₀ ∨ g * a₀ * g⁻¹ = a₀ * z := by
    rcases hg0 with h | h
    · left
      calc g * a₀ * g⁻¹ = g * (g⁻¹ * a₀ * g) * g⁻¹ := by rw [h]
        _ = a₀ := by group
    · right
      have e1 : g * (a₀ * z) * g⁻¹ = (g * a₀ * g⁻¹) * z := by
        calc g * (a₀ * z) * g⁻¹ = (g * a₀ * g⁻¹) * (g * z * g⁻¹) := by group
          _ = (g * a₀ * g⁻¹) * z := by rw [hgzc']
      have e2 : (g * a₀ * g⁻¹) * z = a₀ := by
        rw [← e1, ← h]
        group
      calc g * a₀ * g⁻¹ = (g * a₀ * g⁻¹) * (z * z) := by rw [hz2, mul_one]
        _ = ((g * a₀ * g⁻¹) * z) * z := (mul_assoc _ _ _).symm
        _ = a₀ * z := by rw [e2]
  have hcne : g⁻¹ * a₁ * g ≠ a₀ ∧ g⁻¹ * a₁ * g ≠ a₀ * z := by
    constructor
    · intro h
      have e : a₁ = g * a₀ * g⁻¹ := by
        rw [← h]
        group
      rcases hg0' with h' | h'
      · exact hne (e.trans h')
      · exact hne' (e.trans h')
    · intro h
      have e : a₁ = g * (a₀ * z) * g⁻¹ := by
        rw [← h]
        group
      have e1 : g * (a₀ * z) * g⁻¹ = (g * a₀ * g⁻¹) * z := by
        calc g * (a₀ * z) * g⁻¹ = (g * a₀ * g⁻¹) * (g * z * g⁻¹) := by group
          _ = (g * a₀ * g⁻¹) * z := by rw [hgzc']
      rw [e1] at e
      rcases hg0' with h' | h'
      · exact hne' (by rw [e, h'])
      · apply hne
        rw [e, h']
        calc a₀ * z * z = a₀ * (z * z) := mul_assoc _ _ _
          _ = a₀ := by rw [hz2, mul_one]
  have hc1 : g⁻¹ * a₁ * g ≠ 1 := fun h => hzne (by rw [h, one_mul] at hcc; exact hcc.symm)
  have hcz : g⁻¹ * a₁ * g ≠ z := fun h => hzne (by rw [h] at hcc; exact hcc.symm.trans hz2)
  have h4 : (g⁻¹ * a₁ * g = a₁ ∨ g⁻¹ * a₁ * g = a₁ * z) ∨
      (g⁻¹ * a₁ * g = a₀ * a₁ ∨ g⁻¹ * a₁ * g = a₀ * a₁ * z) := by
    rcases par_mem_q8_decomp hq l ha₀ ha₁ h₀ h₁ hne hne' hcK hc4 with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact absurd h hcz
    · exact absurd h hcne.1
    · exact absurd h hcne.2
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hzc : ∀ {x : G}, x ∈ K l → z * x = x * z := fun hx => hq.z_comm hx
  rcases h4 with hfix | hswap
  · left
    refine ⟨?_, hfix⟩
    unfold ParNt
    rintro ⟨q, hqc, h1, h2⟩
    obtain ⟨hqK, hq4⟩ := (s888parD_mem_core hq l).mp hqc
    have hfq : g⁻¹ * q * g = q ∨ g⁻¹ * q * g = q * z := by
      rcases par_mem_q8_decomp hq l ha₀ ha₁ h₀ h₁ hne hne' hqK hq4 with
        h | h | h | h | h | h | h | h <;> rw [h]
      · exact Or.inl (by group)
      · exact Or.inl hgzc
      · exact hg0
      · exact s888parD_fix_mulz hgzc hg0
      · exact hfix
      · exact s888parD_fix_mulz hgzc hfix
      · exact s888parD_fix_mul hgzc hz2 (hzc ha₁) hg0 hfix
      · exact s888parD_fix_mulz hgzc (s888parD_fix_mul hgzc hz2 (hzc ha₁) hg0 hfix)
    rcases hfq with e | e
    · exact h1 e
    · exact h2 e
  · right
    refine ⟨?_, hswap⟩
    unfold ParNt
    have hc1' : ∀ x : G, a₀ * x = x → False := fun x h =>
      ha₀1 (mul_right_cancel (a := a₀) (b := x) (c := 1) (by rw [one_mul]; exact h))
    have hc2' : ∀ x : G, x ∈ K l → a₀ * x = x * z → False := fun x hx h =>
      ha₀z (mul_right_cancel (a := a₀) (b := x) (c := z) (by rw [h, hzc hx]))
    have hc3' : ∀ x : G, x ∈ K l → a₀ * x * z = x → False := fun x hx h => by
      have e : a₀ * z * x = 1 * x := by
        calc a₀ * z * x = a₀ * (z * x) := mul_assoc _ _ _
          _ = a₀ * (x * z) := by rw [hzc hx]
          _ = a₀ * x * z := (mul_assoc _ _ _).symm
          _ = 1 * x := by rw [h, one_mul]
      have e2 : a₀ * z = 1 := mul_right_cancel e
      apply ha₀z
      calc a₀ = a₀ * (z * z) := by rw [hz2, mul_one]
        _ = (a₀ * z) * z := (mul_assoc _ _ _).symm
        _ = z := by rw [e2, one_mul]
    have hc4' : ∀ x : G, a₀ * x * z = x * z → False := fun x h =>
      hc1' x (mul_right_cancel h)
    refine ⟨a₁, (s888parD_mem_core hq l).mpr ⟨ha₁, hpow4 h₁⟩, ?_, ?_⟩
    · intro h
      rcases hswap with e | e
      · exact hc1' a₁ (e.symm.trans h)
      · exact hc3' a₁ ha₁ (e.symm.trans h)
    · intro h
      rcases hswap with e | e
      · exact hc2' a₁ ha₁ (e.symm.trans h)
      · exact hc4' a₁ (e.symm.trans h)

end CFSG.OddStandard.SmallF3.Omega
