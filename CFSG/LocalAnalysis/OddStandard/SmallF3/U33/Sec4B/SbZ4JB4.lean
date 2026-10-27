module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JB3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {H : Type} [Group H] [Finite H]
variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem no_order_four {g : H} (hg : g * ρ * g⁻¹ * ρ⁻¹ ∈ centralizer (Y : Set H))
    (h2 : g * g ∉ centralizer (Y : Set H))
    (h4 : g * g * (g * g) ∈ centralizer (Y : Set H)) : False := by
  classical
  haveI hY : Y.Normal := ⟨fun n hn k => h.normal_Y k n hn⟩
  let f : H →* MulAut ↥Y := zjAct Y
  have hfker : f.ker = centralizer (Y : Set H) := by
    rw [show f = zjAct Y from rfl]
    exact zjAct_ker Y
  have hcomm : f g * f ρ = f ρ * f g := by
    have h1 : f (g * ρ * g⁻¹ * ρ⁻¹) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact hg
    simp only [map_mul, map_inv] at h1
    have h2' : f g * f ρ * (f g)⁻¹ = f ρ := mul_inv_eq_one.mp h1
    calc f g * f ρ = (f g * f ρ * (f g)⁻¹) * f g := by group
      _ = f ρ * f g := by rw [h2']
  have hsq : f g * f g ≠ 1 := by
    intro h1
    apply h2
    rw [← hfker, MonoidHom.mem_ker, map_mul]
    exact h1
  have hfour : (f g) ^ 4 = 1 := by
    have h4' : (f g * f g) * (f g * f g) = 1 := by
      have h : f (g * g * (g * g)) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hfker]
        exact h4
      simpa only [map_mul] using h
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
    exact h4'
  have horder : orderOf (f g) = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfin : (f g) ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
      exact hfour
    have h := orderOf_eq_prime_pow (x := f g) (p := 2) (n := 1)
      (by simpa [pow_two] using hsq) hfin
    simpa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] using h
  let W : Subgroup (MulAut ↥Y) := Subgroup.zpowers (f g)
  have hWcard : Nat.card W = 4 := by
    show Nat.card (Subgroup.zpowers (f g)) = 4
    rw [Nat.card_zpowers, horder]
  have hW : IsPGroup 2 W := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hWcard]
    norm_num
  have hWS : W ≤ (zjAct Y).range := by
    change Subgroup.zpowers (f g) ≤ (zjAct Y).range
    exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  have hWc : W ≤ centralizer ({zjAct Y ρ} : Set (MulAut ↥Y)) := by
    change Subgroup.zpowers (f g) ≤ centralizer ({zjAct Y ρ} : Set (MulAut ↥Y))
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hres : Nat.card W ≤ 2 := h.range_cent_two_group W hWS hWc hW
  rw [hWcard] at hres
  omega

theorem no_klein {g g' : H} (hg : g * ρ * g⁻¹ * ρ⁻¹ ∈ centralizer (Y : Set H))
    (hg' : g' * ρ * g'⁻¹ * ρ⁻¹ ∈ centralizer (Y : Set H))
    (e : g * g ∈ centralizer (Y : Set H)) (e' : g' * g' ∈ centralizer (Y : Set H))
    (hgE : g ∉ centralizer (Y : Set H)) (hg'E : g' ∉ centralizer (Y : Set H))
    (hne : g⁻¹ * g' ∉ centralizer (Y : Set H))
    (hc : g * g' * g⁻¹ * g'⁻¹ ∈ centralizer (Y : Set H)) : False := by
  classical
  haveI hY : Y.Normal := ⟨fun n hn k => h.normal_Y k n hn⟩
  let f : H →* MulAut ↥Y := zjAct Y
  have hfker : f.ker = centralizer (Y : Set H) := by
    rw [show f = zjAct Y from rfl]
    exact zjAct_ker Y
  have haρ : f g * f ρ = f ρ * f g := by
    have h1 : f (g * ρ * g⁻¹ * ρ⁻¹) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact hg
    simp only [map_mul, map_inv] at h1
    have h2' : f g * f ρ * (f g)⁻¹ = f ρ := mul_inv_eq_one.mp h1
    calc f g * f ρ = (f g * f ρ * (f g)⁻¹) * f g := by group
      _ = f ρ * f g := by rw [h2']
  have hbρ : f g' * f ρ = f ρ * f g' := by
    have h1 : f (g' * ρ * g'⁻¹ * ρ⁻¹) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact hg'
    simp only [map_mul, map_inv] at h1
    have h2' : f g' * f ρ * (f g')⁻¹ = f ρ := mul_inv_eq_one.mp h1
    calc f g' * f ρ = (f g' * f ρ * (f g')⁻¹) * f g' := by group
      _ = f ρ * f g' := by rw [h2']
  have haa : f g * f g = 1 := by
    have h1 : f (g * g) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact e
    rwa [map_mul] at h1
  have hbb : f g' * f g' = 1 := by
    have h1 : f (g' * g') = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact e'
    rwa [map_mul] at h1
  have ha1 : f g ≠ 1 := by
    intro h1
    apply hgE
    rw [← hfker]
    exact MonoidHom.mem_ker.mpr h1
  have hb1 : f g' ≠ 1 := by
    intro h1
    apply hg'E
    rw [← hfker]
    exact MonoidHom.mem_ker.mpr h1
  have hab : f g ≠ f g' := by
    intro h1
    apply hne
    rw [← hfker]
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, h1]
    group
  have hab' : f g * f g' = f g' * f g := by
    have h1 : f (g * g' * g⁻¹ * g'⁻¹) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hfker]
      exact hc
    simp only [map_mul, map_inv] at h1
    have h2' : f g * f g' * (f g)⁻¹ = f g' := mul_inv_eq_one.mp h1
    calc f g * f g' = (f g * f g' * (f g)⁻¹) * f g := by group
      _ = f g' * f g := by rw [h2']
  have hab1 : f g * f g' ≠ 1 := by
    intro h1
    apply hab
    have h2 : f g' = f g := by
      calc f g' = (f g * f g) * f g' := by rw [haa, one_mul]
        _ = f g * (f g * f g') := by group
        _ = f g := by rw [h1, mul_one]
    exact h2.symm
  have hproda : f g * f g' ≠ f g := by
    intro h1
    apply hb1
    calc f g' = (f g)⁻¹ * (f g * f g') := by group
      _ = (f g)⁻¹ * f g := by rw [h1]
      _ = 1 := by group
  have hprodb : f g * f g' ≠ f g' := by
    intro h1
    apply ha1
    calc f g = (f g * f g') * (f g')⁻¹ := by group
      _ = f g' * (f g')⁻¹ := by rw [h1]
      _ = 1 := by group
  let W : Subgroup (MulAut ↥Y) := Subgroup.closure ({f g, f g'} : Set (MulAut ↥Y))
  have hWS : W ≤ (zjAct Y).range := by
    change Subgroup.closure ({f g, f g'} : Set (MulAut ↥Y)) ≤ (zjAct Y).range
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    · exact MonoidHom.mem_range.mpr ⟨g', rfl⟩
  have hWc : W ≤ centralizer ({zjAct Y ρ} : Set (MulAut ↥Y)) := by
    change Subgroup.closure ({f g, f g'} : Set (MulAut ↥Y)) ≤
      centralizer ({zjAct Y ρ} : Set (MulAut ↥Y))
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change f g ∈ centralizer ({(zjAct Y) ρ} : Set (MulAut ↥Y))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact haρ
    · change f g' ∈ centralizer ({(zjAct Y) ρ} : Set (MulAut ↥Y))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hbρ
  have hW : IsPGroup 2 W := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (x : MulAut ↥Y) ^ (2 ^ 1) = 1
    have hx := (mem_closure_pair_of_invol haa hbb hab').mp x.2
    rcases hx with hx | hx | hx | hx
    · rw [hx]; simp
    · rw [hx]; simpa [pow_two] using haa
    · rw [hx]; simpa [pow_two] using hbb
    · rw [hx]
      have h1 : (f g * f g') * (f g * f g') = 1 := by
        calc (f g * f g') * (f g * f g') = f g * (f g' * f g) * f g' := by group
          _ = f g * (f g * f g') * f g' := by rw [← hab']
          _ = (f g * f g) * (f g' * f g') := by group
          _ = 1 := by rw [haa, hbb, mul_one]
      simpa [pow_two] using h1
  have h4le : 4 ≤ Nat.card W := by
    let ψ : Fin 4 → W := fun i =>
      if i = 0 then ⟨1, one_mem W⟩
      else if i = 1 then ⟨f g, subset_closure (by simp)⟩
      else if i = 2 then ⟨f g', subset_closure (by simp)⟩
      else ⟨f g * f g', mul_mem (subset_closure (by simp)) (subset_closure (by simp))⟩
    have hψ : Function.Injective ψ := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [ψ, Subtype.ext_iff, ha1, hb1, hab, hab1, hproda, hprodb]
    have := Nat.card_le_card_of_injective ψ hψ
    simpa using this
  have hres : Nat.card W ≤ 2 := h.range_cent_two_group W hWS hWc hW
  omega

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
