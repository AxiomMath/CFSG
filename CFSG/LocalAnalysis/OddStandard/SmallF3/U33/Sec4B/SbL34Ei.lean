module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ed

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

theorem crit_of_surj_core {Γ Λ : Type} [Group Γ] [Finite Γ] [Group Λ] [Finite Λ]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (π : Γ →* Λ) (hπ : Function.Surjective π) (P W : Subgroup Γ) [P.Normal]
    (hKP : π.ker ≤ P) (hKW : π.ker ≤ W)
    (ι : Λ →* (E ≃ₗ[ZMod 2] E)) (hι : Function.Injective ι)
    (hdim : Module.finrank (ZMod 2) E = 6) {ρ σ : Γ}
    (hρ3 : ρ * ρ * ρ = 1) (hρP : ρ ∉ P) (hσ2 : σ * σ = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hcard : Nat.card Γ = 6 * Nat.card P)
    (hfpf : ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ π.ker → p ∈ π.ker)
    (hW2 : IsPGroup 2 W) (hWi : ¬ 2 ∣ W.index) (hσW : σ ∈ W)
    (hD : Nat.card ↥(Subgroup.centralizer ({σ} : Set Γ) ⊓ W) = 2 ^ 7)
    (hDK : Nat.card ↥(Subgroup.centralizer ({σ} : Set Γ) ⊓ π.ker) = 2 ^ 5)
    (hcentW : ∀ w ∈ W, σ * w * σ⁻¹ * w⁻¹ ∈ π.ker →
      ∃ k ∈ π.ker, ∃ d ∈ Subgroup.centralizer ({σ} : Set Γ) ⊓ W, w = k * d) :
    Crit ι (P.map π) (W.map π) (π ρ) (π σ) := by
  have hρ3' : ρ ^ 3 = 1 := by
    rw [pow_succ, pow_succ, pow_one]
    exact hρ3
  refine ⟨hι, hdim, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← map_pow, hρ3', map_one]
  ·
    intro h
    exact hρP (hKP (MonoidHom.mem_ker.mpr h))
  ·
    rw [← map_mul, hσ2, map_one]
  ·
    rw [← map_mul, ← map_inv, ← map_mul, hσρ, map_inv]
  ·
    exact Subgroup.Normal.map (inferInstance : P.Normal) π hπ
  ·
    haveI : Nonempty ↥π.ker := ⟨1, π.ker.one_mem⟩
    have hker : Nat.card ↥(π.ker.subgroupOf P) = Nat.card π.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
    have h1 : Nat.card π.ker * Nat.card Λ = Nat.card Γ :=
      Subgroup.card_ker_mul_card_of_surjective hπ
    have h2 : Nat.card π.ker * Nat.card ↥(P.map π) = Nat.card P := by
      have h := Subgroup.card_ker_mul_card_range (π.domRestrict P)
      rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, hker] at h
      exact h
    have key : Nat.card π.ker * Nat.card Λ =
        Nat.card π.ker * (6 * Nat.card ↥(P.map π)) := by
      rw [h1, hcard, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  ·
    intro x hx hfix
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : ρ * p * ρ⁻¹ * p⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hπ : π (ρ * p * ρ⁻¹ * p⁻¹) = π ρ * π p * (π ρ)⁻¹ * (π p)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [hπ, hfix]
      group
    exact MonoidHom.mem_ker.mp (hfpf p hp hmem)
  ·
    exact hW2.map π
  ·
    rw [Subgroup.index_map_eq W hπ hKW]
    exact hWi
  ·
    exact Subgroup.mem_map_of_mem π hσW
  ·
    set D : Subgroup Γ := Subgroup.centralizer ({σ} : Set Γ) ⊓ W with hDdef
    let g : ↥D →* Λ := π.domRestrict D
    have hmemD : ∀ {x : Γ}, x ∈ D → x ∈ Subgroup.centralizer ({σ} : Set Γ) ∧ x ∈ W := by
      intro x hx
      simpa only [hDdef, Subgroup.mem_inf] using hx
    have hA : g.range = Subgroup.centralizer ({π σ} : Set Λ) ⊓ W.map π := by
      dsimp only [g]
      rw [MonoidHom.domRestrict_range]
      ext x
      constructor
      · rintro ⟨d, hd, rfl⟩
        obtain ⟨hdc, hdw⟩ := hmemD hd
        refine ⟨?_, Subgroup.mem_map_of_mem π hdw⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hdc])
      · rintro ⟨hx1, hx2⟩
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx2
        have hx1' : π w * π σ = π σ * π w :=
          Subgroup.mem_centralizer_singleton_iff.mp hx1
        have hmem : σ * w * σ⁻¹ * w⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker]
          simp only [map_mul, map_inv]
          rw [← hx1']
          group
        obtain ⟨k, hk, d, hd, hwd⟩ := hcentW w hw hmem
        refine Subgroup.mem_map.mpr ⟨d, hd, ?_⟩
        have hk1 : π k = 1 := MonoidHom.mem_ker.mp hk
        rw [hwd, map_mul, hk1, one_mul]
    have hHD : Subgroup.centralizer ({σ} : Set Γ) ⊓ π.ker ≤ D := by
      intro x hx
      rw [hDdef]
      exact Subgroup.mem_inf.mpr ⟨hx.1, hKW hx.2⟩
    have hB : g.ker = (Subgroup.centralizer ({σ} : Set Γ) ⊓ π.ker).subgroupOf D := by
      dsimp only [g]
      rw [MonoidHom.ker_domRestrict]
      ext d
      constructor
      · intro hd
        rw [Subgroup.mem_subgroupOf] at hd ⊢
        exact Subgroup.mem_inf.mpr ⟨(hmemD d.2).1, hd⟩
      · intro hd
        rw [Subgroup.mem_subgroupOf] at hd ⊢
        exact hd.2
    have hBcard : Nat.card g.ker =
        Nat.card ↥(Subgroup.centralizer ({σ} : Set Γ) ⊓ π.ker) := by
      rw [hB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHD).toEquiv
    have hcardg : Nat.card g.ker * Nat.card g.range = Nat.card ↥D :=
      Subgroup.card_ker_mul_card_range g
    have hD' : Nat.card ↥D = 2 ^ 7 := by rw [hDdef]; exact hD
    rw [hBcard, hA, hDK, hD'] at hcardg
    have h2 : 2 ^ 5 * Nat.card ↥(Subgroup.centralizer ({π σ} : Set Λ) ⊓ W.map π) =
        2 ^ 5 * 4 := by
      rw [hcardg]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
