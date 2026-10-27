module

public import CFSG.CGT.T75H.Klein
public import CFSG.CGT.T75H.NormD

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

structure OddCore (T T₁ N : Subgroup G) : Prop where
  le_hSub : N ≤ hSub T (normIn T₁ T)
  le_centralizer : N ≤ Subgroup.centralizer (T : Set G)
  odd : Odd (Nat.card N)
  inf_eq_bot : T ⊓ N = ⊥
  dec : ∀ c ∈ Subgroup.centralizer (T : Set G) ⊓ hSub T (normIn T₁ T),
    ∃ t ∈ T, ∃ n ∈ N, c = t * n
  norm : ∀ s ∈ Subgroup.normalizer (T : Set G), ∀ n ∈ N, s * n * s⁻¹ ∈ N

theorem not_cent_conj {w s : G} (hs : s ∈ Subgroup.normalizer (T : Set G))
    (hw : ¬ ∀ t ∈ T, w * t = t * w) : ¬ ∀ t ∈ T, (s * w * s⁻¹) * t = t * (s * w * s⁻¹) := by
  intro hcent
  apply hw
  intro t ht
  have h := hcent _ (conj_mem_of_mem_normalizer hs ht)
  calc w * t = s⁻¹ * ((s * w * s⁻¹) * (s * t * s⁻¹)) * s := by group
    _ = s⁻¹ * ((s * t * s⁻¹) * (s * w * s⁻¹)) * s := by rw [h]
    _ = t * w := by group

theorem mem_of_invol_cent {N : Subgroup G} (hN : OddCore T T₁ N)
    (htt : ∀ t ∈ T, t * t = 1) {c : G} (hcH : c ∈ hSub T (normIn T₁ T))
    (hcc : ∀ t ∈ T, t * c = c * t) (hc2 : c * c = 1) : c ∈ T := by
  obtain ⟨t, ht, n, hn, hcn⟩ := hN.dec c ⟨Subgroup.mem_centralizer_iff.2 hcc, hcH⟩
  have hnc : ∀ m ∈ N, ∀ s ∈ T, s * m = m * s := fun m hm s hs =>
    Subgroup.mem_centralizer_iff.1 (hN.le_centralizer hm) s hs
  have hnn : n * n = 1 := by
    have h1 : (t * n) * (t * n) = (t * t) * (n * n) := by
      calc (t * n) * (t * n) = t * (n * t) * n := by group
        _ = t * (t * n) * n := by rw [← hnc n hn t ht]
        _ = (t * t) * (n * n) := by group
    rw [← hcn, hc2, htt t ht, one_mul] at h1
    exact h1.symm
  have hn1 : n = 1 := eq_one_of_mul_self_eq_one_of_odd hN.odd hn hnn
  rw [hcn, hn1, mul_one]
  exact ht

theorem exists_cent_involution [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T)))
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {N : Subgroup G} (hN : OddCore T T₁ N)
    (hNℓ : ∀ n ∈ N, n * ℓ = ℓ * n) {S : Subgroup G}
    (hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G)) {α β : G}
    (hα : α ∈ Cbar T T₁ S) (hβ : β ∈ Cbar T T₁ S) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hne : α ≠ β)
    (hββ : β * β = 1) :
    ∃ γ ∈ Cbar T T₁ S, γ ≠ 1 ∧ ∀ h ∈ hSub T (normIn T₁ T), γ * h = h * γ := by
  classical
  set H := hSub T (normIn T₁ T) with hHdef
  have hHN : H ≤ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2)
  have hTab := hc.hy.pair.wc.1
  have htt : ∀ t ∈ T, t * t = 1 := fun t ht => elemAbelian_mul_self hTab ht
  have hℓH : ℓ ∈ H := le_hSub D.hℓ
  have hb1 : b ≠ 1 := fun h => D.hbL (h ▸ (normIn T T₁).one_mem)
  have hab : a ≠ b := fun h => D.hbL (h ▸ D.ha)
  have hNc : ∀ n ∈ N, ∀ t ∈ T, t * n = n * t := fun n hn t ht =>
    Subgroup.mem_centralizer_iff.1 (hN.le_centralizer hn) t ht
  have hℓnc : ¬ ∀ t ∈ T, ℓ * t = t * ℓ := by
    intro hcent
    apply D.ha1
    have h1 : ℓ * a = ℓ * 1 := by
      calc ℓ * a = b * ℓ * b := D.conj_ℓ_b.symm
        _ = ℓ * b * b := by rw [← hcent b D.hb]
        _ = ℓ * 1 := by rw [mul_assoc, D.bb]
    exact mul_left_cancel h1
  have hℓa : ℓ * a * ℓ = a := by
    calc ℓ * a * ℓ = a * ℓ * ℓ := by rw [← D.comm_aℓ]
      _ = a := by rw [mul_assoc, D.ℓℓ, mul_one]
  have hℓb : ℓ * b * ℓ = b * a := D.conj_b_ℓ
  have hℓba : ℓ * (b * a) * ℓ = b := by
    calc ℓ * (b * a) * ℓ = ℓ * b * (ℓ * ℓ) * a * ℓ := by rw [D.ℓℓ, mul_one]; group
      _ = (ℓ * b * ℓ) * (ℓ * a * ℓ) := by group
      _ = b := by rw [hℓb, hℓa, mul_assoc, D.aa, mul_one]
  obtain ⟨h₀, hh₀, hh₀e⟩ := h57 a D.haT D.ha1 b D.hb hb1
  set g₂ : G := h₀ * ℓ * h₀⁻¹ with hg₂def
  have hg₂H : g₂ ∈ H := H.mul_mem (H.mul_mem hh₀ hℓH) (H.inv_mem hh₀)
  have hg₂g₂ : g₂ * g₂ = 1 := by
    calc g₂ * g₂ = h₀ * (ℓ * ℓ) * h₀⁻¹ := by simp only [hg₂def]; group
      _ = 1 := by rw [D.ℓℓ]; group
  have hg₂inv : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right hg₂g₂
  have hg₂b : g₂ * b * g₂⁻¹ = b := by
    have hb' : h₀⁻¹ * b * h₀ = a := by rw [← hh₀e]; group
    have hℓa' : ℓ * a * ℓ⁻¹ = a := by rw [D.inv_ℓ]; exact hℓa
    calc g₂ * b * g₂⁻¹ = h₀ * (ℓ * (h₀⁻¹ * b * h₀) * ℓ⁻¹) * h₀⁻¹ := by
          simp only [hg₂def]; group
      _ = h₀ * (ℓ * a * ℓ⁻¹) * h₀⁻¹ := by rw [hb']
      _ = b := by rw [hℓa']; exact hh₀e
  have hg₂nc : ¬ ∀ t ∈ T, g₂ * t = t * g₂ := not_cent_conj (hHN hh₀) hℓnc
  have hNg₂ : ∀ n ∈ N, n * g₂ = g₂ * n := by
    intro n hn
    have hn' : h₀⁻¹ * n * h₀ ∈ N := by
      simpa using hN.norm h₀⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem (hHN hh₀)) n hn
    have := hNℓ _ hn'
    calc n * g₂ = h₀ * ((h₀⁻¹ * n * h₀) * ℓ) * h₀⁻¹ := by simp only [hg₂def]; group
      _ = h₀ * (ℓ * (h₀⁻¹ * n * h₀)) * h₀⁻¹ := by rw [this]
      _ = g₂ * n := by simp only [hg₂def]; group
  set g₃ : G := ℓ * g₂ * ℓ with hg₃def
  have hg₃H : g₃ ∈ H := H.mul_mem (H.mul_mem hℓH hg₂H) hℓH
  have hg₃g₃ : g₃ * g₃ = 1 := by
    calc g₃ * g₃ = ℓ * g₂ * (ℓ * ℓ) * g₂ * ℓ := by simp only [hg₃def]; group
      _ = ℓ * (g₂ * g₂) * ℓ := by rw [D.ℓℓ]; group
      _ = 1 := by rw [hg₂g₂, mul_one, D.ℓℓ]
  have hg₃inv : g₃⁻¹ = g₃ := inv_eq_of_mul_eq_one_right hg₃g₃
  have hg₃f : g₃ * (b * a) * g₃⁻¹ = b * a := by
    rw [hg₃inv]
    have hg₂b' : g₂ * b * g₂ = b := by
      have := hg₂b
      rwa [hg₂inv] at this
    calc g₃ * (b * a) * g₃ = ℓ * g₂ * (ℓ * (b * a) * ℓ) * g₂ * ℓ := by simp only [hg₃def]; group
      _ = ℓ * (g₂ * b * g₂) * ℓ := by rw [hℓba]; group
      _ = b * a := by rw [hg₂b']; exact hℓb
  have hg₃nc : ¬ ∀ t ∈ T, g₃ * t = t * g₃ := by
    have := not_cent_conj (T := T) (s := ℓ) D.hℓN hg₂nc
    simpa [hg₃def, D.inv_ℓ] using this
  have hNg₃ : ∀ n ∈ N, n * g₃ = g₃ * n := by
    intro n hn
    calc n * g₃ = (n * ℓ) * g₂ * ℓ := by simp only [hg₃def]; group
      _ = (ℓ * n) * g₂ * ℓ := by rw [hNℓ n hn]
      _ = ℓ * (n * g₂) * ℓ := by group
      _ = ℓ * (g₂ * n) * ℓ := by rw [hNg₂ n hn]
      _ = ℓ * g₂ * (n * ℓ) := by group
      _ = ℓ * g₂ * (ℓ * n) := by rw [hNℓ n hn]
      _ = g₃ * n := by simp only [hg₃def]; group
  have hQ3 : ∀ f ∈ T, f ≠ 1 → ∃ g : G, (g = ℓ ∨ g = g₂ ∨ g = g₃) ∧ g ∈ H ∧ g * g = 1 ∧
      g * f * g⁻¹ = f ∧ (¬ ∀ t ∈ T, g * t = t * g) ∧ (∀ n ∈ N, n * g = g * n) := by
    intro f hf hf1
    rcases D.hT f hf with h | h | h | h
    · exact absurd h hf1
    · refine ⟨ℓ, Or.inl rfl, hℓH, D.ℓℓ, ?_, hℓnc, hNℓ⟩
      rw [h, D.inv_ℓ]
      exact hℓa
    · exact ⟨g₂, Or.inr (Or.inl rfl), hg₂H, hg₂g₂, by rw [h]; exact hg₂b, hg₂nc, hNg₂⟩
    · exact ⟨g₃, Or.inr (Or.inr rfl), hg₃H, hg₃g₃, by rw [h]; exact hg₃f, hg₃nc, hNg₃⟩
  have hE1 : ∀ z ∈ H, z * z = 1 → z ∉ T →
      ∃ t ∈ T, ∃ g : G, (g = ℓ ∨ g = g₂ ∨ g = g₃) ∧ z = t * g := by
    intro z hzH hzz hzT
    have hznc : ¬ ∀ t ∈ T, z * t = t * z := fun hcent =>
      hzT (mem_of_invol_cent hN htt hzH (fun t ht => (hcent t ht).symm) hzz)
    have hzN : ∀ t ∈ T, z * t * z⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer (hHN hzH) ht
    obtain ⟨f, hfT, hf1, hzf⟩ := exists_fixed_of_invol D.hT D.haT D.hb D.comm_ab D.aa D.bb
      D.ha1 hb1 hab hzz hzN
    obtain ⟨g, hg, hgH, hgg, hgf, hgnc, hNg⟩ := hQ3 f hfT hf1
    obtain ⟨x, hxT, hx1, hxf, hbasis⟩ := exists_basis_of_ne_one D.hT D.haT D.hb D.comm_ab D.aa
      D.ha1 hb1 hab hfT hf1
    obtain ⟨t, ht, -, hzt⟩ := eq_mul_of_fixed hHN hN.odd hN.inf_eq_bot hN.le_centralizer hN.dec
      htt hxT hx1 hxf hbasis (htt f hfT) hgH hzH hgg hzz hNg hgf hzf hgnc hznc
    exact ⟨t, ht, g, hg, hzt⟩
  obtain ⟨x₂, hx₂T, hx₂1, hx₂f, hbasis₂⟩ := exists_basis_of_ne_one D.hT D.haT D.hb D.comm_ab D.aa
    D.ha1 hb1 hab D.hb hb1
  have hg₂x : g₂ * x₂ * g₂⁻¹ = x₂ * b := conj_eq_mul_of_fixed hx₂T hx₂1 hx₂f hbasis₂
    (fun t ht => conj_mem_of_mem_normalizer (hHN hg₂H) ht) hg₂b hg₂nc
  have hCcomm : ∀ γ ∈ Cbar T T₁ S, ∃ t ∈ T, (t = 1 ∨ t = b) ∧ γ * g₂ * γ⁻¹ = t * g₂ := by
    intro γ hγ
    obtain ⟨hγS, hγT, hγT₁⟩ := mem_Cbar_iff.1 hγ
    have hγN := hSN γ hγS
    have hqH : γ * g₂ * γ⁻¹ ∈ H := mul_mul_inv_mem_hSub hγN hg₂H
    have hqq : (γ * g₂ * γ⁻¹) * (γ * g₂ * γ⁻¹) = 1 := by
      calc (γ * g₂ * γ⁻¹) * (γ * g₂ * γ⁻¹) = γ * (g₂ * g₂) * γ⁻¹ := by group
        _ = 1 := by rw [hg₂g₂]; group
    have hγb' : γ * b * γ⁻¹ = b := by
      calc γ * b * γ⁻¹ = (b * γ) * γ⁻¹ := by rw [hγT b D.hb]
        _ = b := by group
    have hγb'' : γ⁻¹ * b * γ = b := by
      calc γ⁻¹ * b * γ = γ⁻¹ * (b * γ) := by group
        _ = γ⁻¹ * (γ * b) := by rw [hγT b D.hb]
        _ = b := by group
    have hqb : (γ * g₂ * γ⁻¹) * b * (γ * g₂ * γ⁻¹)⁻¹ = b := by
      calc (γ * g₂ * γ⁻¹) * b * (γ * g₂ * γ⁻¹)⁻¹
          = γ * (g₂ * (γ⁻¹ * b * γ) * g₂⁻¹) * γ⁻¹ := by group
        _ = γ * (g₂ * b * g₂⁻¹) * γ⁻¹ := by rw [hγb'']
        _ = γ * b * γ⁻¹ := by rw [hg₂b]
        _ = b := hγb'
    have hqnc : ¬ ∀ t ∈ T, (γ * g₂ * γ⁻¹) * t = t * (γ * g₂ * γ⁻¹) := not_cent_conj hγN hg₂nc
    obtain ⟨t, ht, hgt, hqt⟩ := eq_mul_of_fixed hHN hN.odd hN.inf_eq_bot hN.le_centralizer hN.dec
      htt hx₂T hx₂1 hx₂f hbasis₂ (htt b D.hb) hg₂H hqH hg₂g₂ hqq hNg₂ hg₂b hqb hg₂nc hqnc
    exact ⟨t, ht, eq_of_comm_of_conj hb1 hbasis₂ (htt b D.hb) hg₂b hg₂x ht hgt, hqt⟩
  obtain ⟨tα, htαT, htα, hqα⟩ := hCcomm α hα
  obtain ⟨tβ, htβT, htβ, hqβ⟩ := hCcomm β hβ
  have hγ₀ : ∃ γ ∈ Cbar T T₁ S, γ ≠ 1 ∧ γ * g₂ = g₂ * γ := by
    by_cases h1 : tα = 1
    · refine ⟨α, hα, hα1, ?_⟩
      rw [h1, one_mul] at hqα
      exact mul_inv_eq_iff_eq_mul.1 hqα
    · by_cases h2 : tβ = 1
      · refine ⟨β, hβ, hβ1, ?_⟩
        rw [h2, one_mul] at hqβ
        exact mul_inv_eq_iff_eq_mul.1 hqβ
      · have hα' : tα = b := htα.resolve_left h1
        have hβ' : tβ = b := htβ.resolve_left h2
        refine ⟨α * β, (Cbar T T₁ S).mul_mem hα hβ, ?_, ?_⟩
        · intro h
          apply hne
          have : α = β⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this, inv_eq_of_mul_eq_one_right hββ]
        · have hαb : α * b * α⁻¹ = b := by
            calc α * b * α⁻¹ = (b * α) * α⁻¹ := by rw [((mem_Cbar_iff.1 hα).2.1 b D.hb)]
              _ = b := by group
          have e : (α * β) * g₂ * (α * β)⁻¹ = g₂ := by
            calc (α * β) * g₂ * (α * β)⁻¹ = α * (β * g₂ * β⁻¹) * α⁻¹ := by group
              _ = α * (b * g₂) * α⁻¹ := by rw [hqβ, hβ']
              _ = (α * b * α⁻¹) * (α * g₂ * α⁻¹) := by group
              _ = b * (b * g₂) := by rw [hqα, hα', hαb]
              _ = g₂ := by rw [← mul_assoc, D.bb, one_mul]
          exact mul_inv_eq_iff_eq_mul.1 e
  obtain ⟨γ₀, hγ₀C, hγ₀1, hγ₀g₂⟩ := hγ₀
  obtain ⟨hγ₀S, hγ₀T, hγ₀T₁⟩ := mem_Cbar_iff.1 hγ₀C
  have hγ₀ℓ : γ₀ * ℓ = ℓ * γ₀ := (hγ₀T₁ ℓ D.hℓT₁).symm
  have hγ₀g₃ : γ₀ * g₃ = g₃ * γ₀ := by
    calc γ₀ * g₃ = (γ₀ * ℓ) * g₂ * ℓ := by simp only [hg₃def]; group
      _ = (ℓ * γ₀) * g₂ * ℓ := by rw [hγ₀ℓ]
      _ = ℓ * (γ₀ * g₂) * ℓ := by group
      _ = ℓ * (g₂ * γ₀) * ℓ := by rw [hγ₀g₂]
      _ = ℓ * g₂ * (γ₀ * ℓ) := by group
      _ = ℓ * g₂ * (ℓ * γ₀) := by rw [hγ₀ℓ]
      _ = g₃ * γ₀ := by simp only [hg₃def]; group
  refine ⟨γ₀, hγ₀C, hγ₀1, ?_⟩
  have hgen := hSub_le_closure_conj hc h48 h57 D
  have hle : Subgroup.closure {z | ∃ h ∈ H, z = h * ℓ * h⁻¹} ≤
      Subgroup.centralizer ({γ₀} : Set G) := by
    rw [Subgroup.closure_le]
    rintro z ⟨h, hhH, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hzH : h * ℓ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hℓH) (H.inv_mem hhH)
    have hzz : (h * ℓ * h⁻¹) * (h * ℓ * h⁻¹) = 1 := by
      calc (h * ℓ * h⁻¹) * (h * ℓ * h⁻¹) = h * (ℓ * ℓ) * h⁻¹ := by group
        _ = 1 := by rw [D.ℓℓ]; group
    have hzT : h * ℓ * h⁻¹ ∉ T := by
      intro hzT
      have h' := conj_mem_of_mem_normalizer
        ((Subgroup.normalizer (T : Set G)).inv_mem (hHN hhH)) hzT
      rw [show h⁻¹ * (h * ℓ * h⁻¹) * h⁻¹⁻¹ = ℓ by group] at h'
      exact D.ℓ_not_mem h'
    obtain ⟨t, ht, g, hg, hzt⟩ := hE1 _ hzH hzz hzT
    have hγg : γ₀ * g = g * γ₀ := by
      rcases hg with h' | h' | h'
      · rw [h']; exact hγ₀ℓ
      · rw [h']; exact hγ₀g₂
      · rw [h']; exact hγ₀g₃
    rw [hzt]
    calc (t * g) * γ₀ = t * (g * γ₀) := by group
      _ = t * (γ₀ * g) := by rw [hγg]
      _ = (t * γ₀) * g := by group
      _ = (γ₀ * t) * g := by rw [hγ₀T t ht]
      _ = γ₀ * (t * g) := by group
  intro x hx
  have := hle (hgen hx)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

end CFSG.CGT.T75H
