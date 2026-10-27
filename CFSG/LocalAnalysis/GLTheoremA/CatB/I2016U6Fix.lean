module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open scoped Pointwise

theorem exists_fixed_of_odd {G X : Type} [Group G] [MulAction G X] [Finite X]
    (hodd : Odd (Nat.card X)) (hle : Nat.card X ≤ 3) (N : Subgroup G)
    (hN : ∀ n ∈ N, ∀ x : X, n • x = x) (hidx : Nat.Coprime 3 N.index) :
    ∃ x : X, ∀ g : G, g • x = x := by
  classical
  let ρ : G →* Equiv.Perm X := MulAction.toPermHom G X
  have hNk : N ≤ ρ.ker := fun n hn => by
    rw [MonoidHom.mem_ker]
    ext x
    exact hN n hn x
  have hdvd1 : ρ.ker.index ∣ N.index := Subgroup.index_dvd_of_le hNk
  have hcop : Nat.Coprime 3 (Nat.card ρ.range) := by
    rw [← Subgroup.index_ker]
    exact Nat.Coprime.coprime_dvd_right hdvd1 hidx
  have hdvd6 : Nat.card ρ.range ∣ 6 := by
    have h1 : Nat.card ρ.range ∣ Nat.card (Equiv.Perm X) := Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (Equiv.Perm X) = (Nat.card X).factorial := by
      haveI := Fintype.ofFinite X
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
    rw [h2] at h1
    refine h1.trans ?_
    obtain ⟨k, hk⟩ : ∃ k, Nat.card X = k := ⟨_, rfl⟩
    rw [hk] at hle ⊢
    interval_cases k <;> decide
  have hdvd2 : Nat.card ρ.range ∣ 2 := by
    have h : Nat.card ρ.range ∣ 2 * 3 := hdvd6
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ρ.range := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  have hmod := hp.card_modEq_card_fixedPoints X
  have hfix : Nat.card (MulAction.fixedPoints ρ.range X) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h2 : 2 ∣ Nat.card X := Nat.modEq_zero_iff_dvd.1 hmod
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  haveI : Nonempty (MulAction.fixedPoints ρ.range X) :=
    Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hfix) |>.1
  obtain ⟨x⟩ := this
  refine ⟨x.1, fun g => ?_⟩
  have := x.2 ⟨ρ g, ⟨g, rfl⟩⟩
  exact this

section Involution

variable {M : Type} [Group M] [Finite M]

private noncomputable def conjHom (Y G : Subgroup M)
    (hGY : ∀ g ∈ G, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : ↥G →* MulAut ↥Y where
  toFun g :=
    { toFun := fun y => ⟨(g : M) * y * (g : M)⁻¹, hGY g g.2 y y.2⟩
      invFun := fun y => ⟨((g⁻¹ : ↥G) : M) * y * ((g⁻¹ : ↥G) : M)⁻¹, hGY _ (g⁻¹).2 y y.2⟩
      left_inv := fun y => Subtype.ext (by
        show ((g⁻¹ : ↥G) : M) * ((g : M) * y * (g : M)⁻¹) * ((g⁻¹ : ↥G) : M)⁻¹ = y
        simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by
        show (g : M) * (((g⁻¹ : ↥G) : M) * y * ((g⁻¹ : ↥G) : M)⁻¹) * (g : M)⁻¹ = y
        simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by
        show (g : M) * ((a : M) * b) * (g : M)⁻¹ =
          (g : M) * a * (g : M)⁻¹ * ((g : M) * b * (g : M)⁻¹)
        simp [mul_assoc]) }
  map_one' := by
    ext y
    show (1 : M) * y * (1 : M)⁻¹ = y
    simp
  map_mul' := fun a b => by
    ext y
    show ((a * b : ↥G) : M) * y * ((a * b : ↥G) : M)⁻¹ =
      (a : M) * ((b : M) * y * (b : M)⁻¹) * (a : M)⁻¹
    simp [mul_assoc]

theorem exists_fixed_involution (Y : Subgroup M) (hY : Nat.card Y = 6) (G : Subgroup M)
    (hGY : ∀ g ∈ G, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (N : Subgroup M) (hNG : N ≤ G)
    (hNY : ∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) (hidx : Nat.Coprime 3 (N.subgroupOf G).index) :
    ∃ t ∈ Y, t ≠ 1 ∧ t * t = 1 ∧ ∀ g ∈ G, g * t * g⁻¹ = t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulDistribMulAction ↥G ↥Y := MulDistribMulAction.compHom ↥Y (conjHom Y G hGY)
  have hsmul : ∀ (g : ↥G) (y : ↥Y), ((g • y : ↥Y) : M) = (g : M) * y * (g : M)⁻¹ :=
    fun g y => rfl
  have hcard : ∀ P : Sylow 2 ↥Y, Nat.card (P : Subgroup ↥Y) = 2 := by
    intro P
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
    have hdvd : Nat.card (P : Subgroup ↥Y) ∣ 6 := hY ▸ Subgroup.card_subgroup_dvd_card _
    have h2 : 2 ∣ Nat.card (P : Subgroup ↥Y) := P.dvd_card_of_dvd_card (by rw [hY]; norm_num)
    rw [hk] at hdvd h2 ⊢
    rcases k with _ | _ | k
    · simp at h2
    · rfl
    · exfalso
      have h4 : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
      have := h4.trans hdvd
      omega
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  have hindex : (P₀ : Subgroup ↥Y).index = 3 := by
    have h := Subgroup.card_mul_index (P₀ : Subgroup ↥Y)
    rw [hcard P₀, hY] at h
    omega
  have hle3 : Nat.card (Sylow 2 ↥Y) ≤ 3 := by
    have := Sylow.card_dvd_index P₀
    rw [hindex] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hodd : Odd (Nat.card (Sylow 2 ↥Y)) := by
    have := card_sylow_modEq_one 2 ↥Y
    exact Nat.odd_iff.2 (by simpa [Nat.ModEq] using this)
  have hN : ∀ n ∈ N.subgroupOf G, ∀ S : Sylow 2 ↥Y, n • S = S := by
    intro n hn S
    have hn' : (n : M) ∈ N := hn
    have htriv : ∀ y : ↥Y, n • y = y := fun y => Subtype.ext (by
      rw [hsmul, hNY n hn' y y.2]
      group)
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def]
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [htriv x]
      exact hx
    · intro hy
      exact ⟨y, hy, htriv y⟩
  obtain ⟨S, hS⟩ := exists_fixed_of_odd hodd hle3 (N.subgroupOf G) hN hidx
  obtain ⟨t₀, ht₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(S : Subgroup ↥Y))).1 (hcard S)
  refine ⟨((t₀ : ↥Y) : M), (t₀ : ↥Y).2, ?_, ?_, ?_⟩
  · intro h
    apply ht₀
    exact Subtype.ext (Subtype.ext h)
  · have h1 : t₀ ^ Nat.card (S : Subgroup ↥Y) = 1 := pow_card_eq_one'
    rw [hcard S] at h1
    have h2 := congrArg (fun z : ↥(S : Subgroup ↥Y) => (((z : ↥Y)) : M)) h1
    simpa [pow_two] using h2
  · intro g hg
    set g' : ↥G := ⟨g, hg⟩ with hg'
    have hmem : g' • (t₀ : ↥Y) ∈ (S : Subgroup ↥Y) := by
      have h1 : g' • (t₀ : ↥Y) ∈ g' • (S : Subgroup ↥Y) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ t₀.2
      have h2 : g' • (S : Subgroup ↥Y) = (S : Subgroup ↥Y) := by
        have := congrArg (fun T : Sylow 2 ↥Y => (T : Subgroup ↥Y)) (hS g')
        simpa [Sylow.pointwise_smul_def] using this
      rwa [h2] at h1
    have hne : (⟨g' • (t₀ : ↥Y), hmem⟩ : ↥(S : Subgroup ↥Y)) ≠ 1 := by
      intro h
      apply ht₀
      have h3 : g' • (t₀ : ↥Y) = 1 := congrArg Subtype.val h
      have h4 : (g : M) * ((t₀ : ↥Y) : M) * (g : M)⁻¹ = 1 := by
        have := congrArg Subtype.val h3
        simpa [hsmul] using this
      have h5 : ((t₀ : ↥Y) : M) = 1 := by
        have : ((t₀ : ↥Y) : M) = (g : M)⁻¹ * ((g : M) * ((t₀ : ↥Y) : M) * (g : M)⁻¹) * (g : M) := by
          group
        rw [this, h4]
        group
      exact Subtype.ext (Subtype.ext h5)
    have := congrArg (fun z : ↥(S : Subgroup ↥Y) => (((z : ↥Y)) : M)) (huniq _ hne)
    simpa [hsmul] using this

end Involution

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

end
