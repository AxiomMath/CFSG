module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2IdCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2SL3
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Span

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

section Kr

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem tauW_tauW (he : matOfN e τW = tMN 9) : τW ∘ₗ τW = LinearMap.id := by
  apply matOfN_injective e
  rw [matOfN_comp, he, tMN_mul_tMN, matOfN_id]

theorem R3bHyp.τ_mem_ker (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9) {g : Γ}
    (hg : g ∈ π.ker) : τ g ∈ π.ker := by
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [h.πτ, hg, Module.End.one_eq_id, LinearMap.id_comp, tauW_tauW he]

theorem R3bHyp.τ_ker_inv [Finite Γ] (h : R3bHyp π θ τW ι D W₀ V τ)
    (he : matOfN e τW = tMN 9) : ∀ g ∈ π.ker, τ g = g⁻¹ :=
  inv_of_fixedPoints τ h.ττ (fun _ hg => h.τ_mem_ker he hg) (fun g hg hτ => h.Kr g hg hτ)

theorem R3bHyp.odd_card_ker [Finite Γ] (h : R3bHyp π θ τW ι D W₀ V τ)
    (he : matOfN e τW = tMN 9) : Odd (Nat.card π.ker) :=
  odd_card_of_fixedPoints τ h.ττ (fun _ hg => h.τ_mem_ker he hg) (fun g hg hτ => h.Kr g hg hτ)

theorem R3bHyp.comm_mem (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {j : ℕ} (hj : j < 4) {y : Γ} (hy : y ∈ D) :
    ⁅θ (gen3 (nuS j)), y⁆ ∈ D ∧ betaG e π ⁅θ (gen3 (nuS j)), y⁆ =
      n0M2 j * betaG e π y * n1M2 j + betaG e π y := by
  have h1 := h.ν_norm j hj y hy
  have h2 : ⁅θ (gen3 (nuS j)), y⁆ = θ (gen3 (nuS j)) * y * (θ (gen3 (nuS j)))⁻¹ * y⁻¹ := rfl
  rw [h2]
  refine ⟨mul_mem h1 (inv_mem hy), ?_⟩
  rw [h.beta_mul hK h1 (inv_mem hy), h.beta_ν hK hj hy, h.inv_eq hy]

theorem commDecCheck_spec {z : ℕ} (hz : z < 2) :
    candBlock z 1 = commBlk 3 (candBlock z 2) ∧
    candBlock z 0 = bxor 8 (commBlk 3 (candBlock z 2)) (commBlk 3 (candBlock z 3)) ∧
    candBlock z 3 = commBlk 1 (candBlock z 0) ∧
    candBlock z 2 = bxor 8 (commBlk 1 (candBlock z 0)) (commBlk 1 (candBlock z 1)) := by
  have h := commDecCheck_eq_true
  simp only [commDecCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h z hz
  exact ⟨h1, h2, h3, h4⟩

theorem toMat_commBlk (j : ℕ) (X : Array ℕ) :
    toMat 8 8 (commBlk j X) = n0M2 j * toMat 8 8 X * n1M2 j + toMat 8 8 X := by
  rw [commBlk, toMat_bxor, toMat_bmul, toMat_bmul]; rfl

theorem toMat_bxor8 (A B : Array ℕ) : toMat 8 8 (bxor 8 A B) = toMat 8 8 A + toMat 8 8 B :=
  toMat_bxor 8 8 A B

theorem R3bHyp.ker_central [Finite Γ]
    (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {z : ℕ} (hz : z < 2) {d : ℕ → Γ}
    (hd : ∀ n < 4, d n ∈ D) (hdτ : ∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n)))
    (hβ : ∀ n < 4, betaG e π (d n) = candM z n)
    (hspan : ∀ x ∈ D, ∃ μ < 16, ∃ ν < 16, x = dProd d ν * eProdG θ μ) :
    π.ker ≤ Subgroup.center Γ ∧ Odd (Nat.card π.ker) := by
  refine ⟨?_, h.odd_card_ker he⟩
  set C := Subgroup.centralizer (π.ker : Set Γ) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hinv := h.τ_ker_inv he
  have hE : ∀ m < 4, θ (gen3 (Fin.ofNat 12 m)) ∈ C := fun m hm => by
    have e1 : θ (gen3 (Fin.ofNat 12 m)) = (d m)⁻¹ * τ (d m) := by
      rw [h.inv_eq (hd m hm), hdτ m hm]
    rw [e1, hCdef, Subgroup.mem_centralizer_iff]
    intro n hn
    exact (commute_inv_mul_of_inv τ hinv (d m) hn).symm.eq
  have hθ : ∀ g, θ g ∈ C := by
    have hN : (C.comap θ).Normal := Subgroup.Normal.comap hCn θ
    have h01 : ∀ c, st3 0 1 c ∈ C.comap θ := st3_mem_of_gen (by decide)
      (by have := hE 0 (by norm_num); exact this) (by have := hE 1 (by norm_num); exact this)
    have h02 : ∀ c, st3 0 2 c ∈ C.comap θ := st3_mem_of_gen (by decide)
      (by have := hE 2 (by norm_num); exact this) (by have := hE 3 (by norm_num); exact this)
    have htop := eq_top_of_E h01 h02
    intro g
    have : g ∈ C.comap θ := by rw [htop]; exact Subgroup.mem_top g
    exact this
  have hν : ∀ j < 4, θ (gen3 (nuS j)) ∈ C := fun j _ => hθ _
  obtain ⟨c1, c0, c3, c2⟩ := commDecCheck_spec hz
  have hcomm : ∀ j < 4, ∀ n < 4, ⁅θ (gen3 (nuS j)), d n⁆ ∈ D ∧ ⁅θ (gen3 (nuS j)), d n⁆ ∈ C ∧
      betaG e π ⁅θ (gen3 (nuS j)), d n⁆ = n0M2 j * candM z n * n1M2 j + candM z n :=
    fun j hj n hn => by
      obtain ⟨h1, h2⟩ := h.comm_mem hK hj (hd n hn)
      exact ⟨h1, comm_mem_left (hν j hj) _, by rw [h2, hβ n hn]⟩
  have hβ0 : ∀ x ∈ D, betaG e π x = 0 → x = 1 := fun x hx h0 => h.beta_inj he hK hx h0
  have hmem : ∀ n < 4, ∀ (a b : Γ), a ∈ D → b ∈ D → a ∈ C → b ∈ C →
      candM z n = betaG e π a + betaG e π b → d n ∈ C := by
    intro n hn a b haD hbD haC hbC hsum
    have hx : d n * a * b ∈ D := mul_mem (mul_mem (hd n hn) haD) hbD
    have h0 : betaG e π (d n * a * b) = 0 := by
      rw [h.beta_mul hK (mul_mem (hd n hn) haD) hbD, h.beta_mul hK (hd n hn) haD, hβ n hn, hsum]
      rw [show ∀ A B : Mat8, A + B + A + B = 0 from fun A B => by
        rw [show A + B + A + B = (A + A) + (B + B) by abel, mat8_add_self', mat8_add_self',
          add_zero]]
    have h1 := hβ0 _ hx h0
    have : d n = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)
    rw [this]
    exact inv_mem (mul_mem haC hbC)
  have hd1 : d 1 ∈ C := hmem 1 (by norm_num) _ 1 (hcomm 3 (by norm_num) 2 (by norm_num)).1
    (one_mem _) (hcomm 3 (by norm_num) 2 (by norm_num)).2.1 (one_mem _) (by
      rw [(hcomm 3 (by norm_num) 2 (by norm_num)).2.2, betaG_one, add_zero, candM, c1,
        toMat_commBlk]; rfl)
  have hd0 : d 0 ∈ C := hmem 0 (by norm_num) _ _ (hcomm 3 (by norm_num) 2 (by norm_num)).1
    (hcomm 3 (by norm_num) 3 (by norm_num)).1 (hcomm 3 (by norm_num) 2 (by norm_num)).2.1
    (hcomm 3 (by norm_num) 3 (by norm_num)).2.1 (by
      rw [(hcomm 3 (by norm_num) 2 (by norm_num)).2.2, (hcomm 3 (by norm_num) 3 (by norm_num)).2.2,
        candM, c0, toMat_bxor8, toMat_commBlk, toMat_commBlk]; rfl)
  have hd3 : d 3 ∈ C := hmem 3 (by norm_num) _ 1 (hcomm 1 (by norm_num) 0 (by norm_num)).1
    (one_mem _) (hcomm 1 (by norm_num) 0 (by norm_num)).2.1 (one_mem _) (by
      rw [(hcomm 1 (by norm_num) 0 (by norm_num)).2.2, betaG_one, add_zero, candM, c3,
        toMat_commBlk]; rfl)
  have hd2 : d 2 ∈ C := hmem 2 (by norm_num) _ _ (hcomm 1 (by norm_num) 0 (by norm_num)).1
    (hcomm 1 (by norm_num) 1 (by norm_num)).1 (hcomm 1 (by norm_num) 0 (by norm_num)).2.1
    (hcomm 1 (by norm_num) 1 (by norm_num)).2.1 (by
      rw [(hcomm 1 (by norm_num) 0 (by norm_num)).2.2, (hcomm 1 (by norm_num) 1 (by norm_num)).2.2,
        candM, c2, toMat_bxor8, toMat_commBlk, toMat_commBlk]; rfl)
  have hdC : ∀ n < 4, d n ∈ C := fun n hn => by
    interval_cases n
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3
  have hDC : D ≤ C := fun x hx => by
    obtain ⟨μ, -, ν, -, rfl⟩ := hspan x hx
    refine mul_mem (Subgroup.list_prod_mem _ fun y hy => ?_)
      (Subgroup.list_prod_mem _ fun y hy => ?_)
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
      exact hdC n (bitList_lt hn)
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
      exact hθ _
  have htop : (⊤ : Subgroup Γ) ≤ C := by
    rw [← h.gen]
    exact sup_le (by rintro _ ⟨g, rfl⟩; exact hθ g) hDC
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have := htop (Subgroup.mem_top g)
  rw [hCdef, Subgroup.mem_centralizer_iff] at this
  exact (this k hk).symm

end Kr

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
