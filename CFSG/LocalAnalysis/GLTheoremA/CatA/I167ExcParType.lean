module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParTwoPart
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParTypeDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKind
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp



private theorem exc_surv_bound {n j N B : ℕ} (hj1 : 1 ≤ j) (hN : N = j * (n * (n - 1)))
    (hB : N < (B + 1) * B) : n ≤ B := by
  by_contra h
  push Not at h
  have h1 : (B + 1) * B ≤ n * (n - 1) := Nat.mul_le_mul h (by omega)
  have h2 : n * (n - 1) ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hj1
  omega

private theorem exc_surv_A {r n j : ℕ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8) (hn : Odd n) (hn3 : 3 ≤ n)
    (hj : Odd j) (hN : r * (r + 1) / 2 = j * (n * (n - 1))) : r = 3 ∧ n = 3 := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨l, hl⟩ := hj
  have hr72 : r * (r + 1) ≤ 8 * 9 := Nat.mul_le_mul hr8 (by omega)
  have hn6 : n ≤ 6 := exc_surv_bound (by omega) hN (B := 6) (by omega)
  interval_cases r <;> interval_cases n <;> omega

private theorem exc_surv_BC {r n j : ℕ} (hr2 : 2 ≤ r) (hr8 : r ≤ 8) (hn : Odd n) (hn3 : 3 ≤ n)
    (hj : Odd j) (hN : 2 * (r * r) / 2 = j * (n * (n - 1))) : False := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨l, hl⟩ := hj
  have hr64 : r * r ≤ 8 * 8 := Nat.mul_le_mul hr8 hr8
  have hn8 : n ≤ 8 := exc_surv_bound (by omega) hN (B := 8) (by omega)
  interval_cases r <;> interval_cases n <;> omega

private theorem exc_surv_D {r n j : ℕ} (hr4 : 4 ≤ r) (hr8 : r ≤ 8) (hn : Odd n) (hn3 : 3 ≤ n)
    (hj : Odd j) (hN : 2 * (r * (r - 1)) / 2 = j * (n * (n - 1))) :
    (r = 5 ∧ n = 5) ∨ (r = 6 ∧ n = 3) ∨ (r = 7 ∧ (n = 7 ∨ n = 3)) := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨l, hl⟩ := hj
  have hr56 : r * (r - 1) ≤ 8 * 7 := Nat.mul_le_mul hr8 (by omega)
  have hn8 : n ≤ 8 := exc_surv_bound (by omega) hN (B := 8) (by omega)
  interval_cases r <;> interval_cases n <;> omega

private theorem exc_surv_fixed {c n j : ℕ} (hc : c = 72 ∨ c = 126 ∨ c = 240 ∨ c = 48)
    (hn : Odd n) (hn3 : 3 ≤ n) (hj : Odd j) (hN : c / 2 = j * (n * (n - 1))) : False := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨l, hl⟩ := hj
  have hn11 : n ≤ 11 := exc_surv_bound (by omega) hN (B := 11) (by omega)
  rcases hc with rfl | rfl | rfl | rfl <;> interval_cases n <;> omega

theorem exc_survivors {r nc n j : ℕ} (hshape : ExcShape r nc) (hn : Odd n) (hn3 : 3 ≤ n)
    (hj : Odd j) (hN : nc / 2 = j * (n * (n - 1))) :
    (r = 3 ∧ nc = 12 ∧ n = 3) ∨ (r = 5 ∧ nc = 40 ∧ n = 5) ∨ (r = 6 ∧ nc = 60 ∧ n = 3) ∨
      (r = 7 ∧ nc = 84 ∧ (n = 7 ∨ n = 3)) := by
  rcases hshape with ⟨h1, h8, hnc⟩ | ⟨h2, h8, hnc⟩ | ⟨h4, h8, hnc⟩ | ⟨hr, hnc⟩ | ⟨hr, hnc⟩ |
    ⟨hr, hnc⟩ | ⟨hr, hnc⟩
  · subst hnc
    obtain ⟨rfl, rfl⟩ := exc_surv_A h1 h8 hn hn3 hj hN
    simp
  · subst hnc
    exact (exc_surv_BC h2 h8 hn hn3 hj hN).elim
  · subst hnc
    rcases exc_surv_D h4 h8 hn hn3 hj hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hn7⟩
    · simp
    · simp
    · rcases hn7 with rfl | rfl <;> simp
  · exact (exc_surv_fixed (Or.inl hnc) hn hn3 hj hN).elim
  · exact (exc_surv_fixed (Or.inr (Or.inl hnc)) hn hn3 hj hN).elim
  · exact (exc_surv_fixed (Or.inr (Or.inr (Or.inl hnc))) hn hn3 hj hN).elim
  · exact (exc_surv_fixed (Or.inr (Or.inr (Or.inr hnc))) hn hn3 hj hN).elim

theorem exc_finite_ratComp {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) :
    Finite ↥(excRatComp S a i) := by
  haveI := S.finite
  have hcomm : ∀ H : Subgroup (ModGL τ L), ⁅H, H⁆ ≤ H := fun H =>
    Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
      mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have h1 : excRatComp S a i ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := hcomm _
  have h2 : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.D.model :=
    inf_le_right.trans (hcomm S.D.model)
  exact Finite.of_injective _ (Subgroup.inclusion_injective (h1.trans h2))

theorem exc_odd_cofactor {p e j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpe : p ∣ 2 ^ e + 1)
    (hpk : p ∣ 2 ^ (e * j) + 1) : Odd j := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hj
  rw [Nat.not_odd_iff_even] at hj
  have h1 : (2 : ZMod p) ^ e = -1 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ e + 1) p).2 hpe
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 : (2 : ZMod p) ^ (e * j) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ (e * j) + 1) p).2 hpk
    push_cast at this
    exact this
  rw [pow_mul, h1, Even.neg_one_pow hj] at h2
  have h3 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [← h2]
    norm_num
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 h3))

theorem exc_orbitLength_one {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) (hst : ∀ γ ∈ Ψ, ρ γ ∈ Ψ) :
    componentOrbitLength ρ Ψ = 1 := by
  have himg : (ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    ((hfin.injOn_iff_bijOn_of_mapsTo fun γ hγ => hst γ hγ).1 ρ.injective.injOn).image_eq
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} :=
    ⟨one_pos, by simpa using himg⟩
  unfold componentOrbitLength
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

private theorem exc_rational_false_aux1 {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a)) {n k : ℕ}
    (hdet : ∀ {t : StatedLieTag} {ν g : ℕ},
      LieModel (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i)) t ν 2 g →
      (4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4))
    (h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn' : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) : False := by
  have hch : ringChar L = 2 := ringChar.eq L 2
  obtain ⟨m, e', -, hm⟩ :=
    KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG hp S hT hap ha1 i h5' hn' hout
      (fun r q => r = 2 ∨ 5 ≤ q)
      (CompsPTwoDRecog.twoDChainRecogAll_even_or_five L)
      (Or.inl hch)
  rw [hch] at hm
  rcases hdet hm with ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ <;> cases ht

private theorem exc_rational_false_aux2 {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a)) {n k : ℕ}
    (hdet : ∀ {t : StatedLieTag} {ν g : ℕ},
      LieModel (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i)) t ν 2 g →
      (4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i))
    (hA : 2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) : False := by
  obtain ⟨f, -, -, hm⟩ := excRec_typeA_suN S hp hT hap ha1 i hA hout hQ
  rcases hdet (excRec_lieModel_two (by simp [classicalTags]) hm) with
    ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ <;> cases ht

private theorem exc_rational_false_aux3 {p : ℕ} (hp : p.Prime) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e n k : ℕ} (he : 1 ≤ e) (hq : S.D.q = 2 ^ e)
    (hdet : ∀ {t : StatedLieTag} {ν g : ℕ},
      LieModel (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i)) t ν 2 g →
      (4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i)) (hn3 : n = 3)
    (h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn' : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1)) : False := by
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · have hrk := compRank_le_rank (componentRoots (rootCharHom a) i)
    have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with rfl | h | h | h
      · simp [Tag.rank] at hrk
        omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hm := excRec_dInner hτ' S hp hT hap ha1 i h5' hn' hin Nat.prime_two (by omega) hq hQ
    rcases hdet (Or.inl ⟨by simp [classicalTags], hm⟩) with ⟨h4, -, -⟩ | ⟨-, -, ht, -⟩
    · omega
    · cases ht
  · exact exc_rational_false_aux1 hp S hT hap ha1 i hdet h5' hn' hin

private theorem exc_rational_false_aux4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a)) {e : ℕ} (he : 1 ≤ e)
    (hq : S.D.q = 2 ^ e) (hqp : p ∣ S.D.q + 1)
    (hen : ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i)) {n k : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hk : 1 ≤ k) (hk1 : k = 1 → 5 ≤ n) (hpk : p ∣ 2 ^ k + 1) (hek : e ∣ k)
    (hJ : catalogIs (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i))
      (isOmPA n (2 ^ k))) :
    (compRank (componentRoots (rootCharHom a) i) = 3 ∧
        (componentRoots (rootCharHom a) i).ncard = 12 ∧ n = 3) ∨
      (compRank (componentRoots (rootCharHom a) i) = 5 ∧
        (componentRoots (rootCharHom a) i).ncard = 40 ∧ n = 5) ∨
      (compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 60 ∧ n = 3) ∨
      (compRank (componentRoots (rootCharHom a) i) = 7 ∧
        (componentRoots (rootCharHom a) i).ncard = 84 ∧ (n = 7 ∨ n = 3)) := by
  haveI := exc_finite_ratComp S a i
  have hq4 : 4 ≤ S.D.q := by
    rcases Nat.lt_or_ge e 2 with h | h
    · have he1 : e = 1 := by omega
      rw [he1] at hq
      rw [hq] at hqp
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hqp)) hp3
    · rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨u, huC, hu⟩ := hen
  have hst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => exc_rho_mem_component S i huC hu hγ
  have h1 := exc_rat_twoPart S hT i hq hq4 hst hp hap ha1 ⟨u, huC, hu⟩ hQ
  have h2 := exc_cat_twoPart hn hn3 hk hk1 hJ
  have h5 := exc_component_shape hτ a i
  obtain ⟨j, hj⟩ := hek
  have hpe : p ∣ 2 ^ e + 1 := by rwa [hq] at hqp
  have hjodd : Odd j := exc_odd_cofactor hp hp2 hpe (hj ▸ hpk)
  have hN : (componentRoots (rootCharHom a) i).ncard / 2 = j * (n * (n - 1)) := by
    have h6 : e * ((componentRoots (rootCharHom a) i).ncard / 2) = e * (j * (n * (n - 1))) := by
      rw [← h1, h2, hj, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h6
  exact exc_survivors h5 hn hn3 hjodd hN

private theorem exc_rational_false_aux5 {p : ℕ} (hp : p.Prime) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e n k : ℕ} (he : 1 ≤ e) (hq : S.D.q = 2 ^ e)
    (hdet : ∀ {t : StatedLieTag} {ν g : ℕ},
      LieModel (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i)) t ν 2 g →
      (4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i))
    (hout_of_odd : Odd (compRank (componentRoots (rootCharHom a) i) +
        (componentRoots (rootCharHom a) i).ncard / 2) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]))
    (hsurv : (compRank (componentRoots (rootCharHom a) i) = 3 ∧
        (componentRoots (rootCharHom a) i).ncard = 12 ∧ n = 3) ∨
      (compRank (componentRoots (rootCharHom a) i) = 5 ∧
        (componentRoots (rootCharHom a) i).ncard = 40 ∧ n = 5) ∨
      (compRank (componentRoots (rootCharHom a) i) = 6 ∧
        (componentRoots (rootCharHom a) i).ncard = 60 ∧ n = 3) ∨
      (compRank (componentRoots (rootCharHom a) i) = 7 ∧
        (componentRoots (rootCharHom a) i).ncard = 84 ∧ (n = 7 ∨ n = 3))) : False := by
  rcases hsurv with ⟨hr3, hnc12, -⟩ | ⟨hr5, hnc40, -⟩ | ⟨hr6, hnc60, hn3'⟩ | ⟨hr7, hnc84, -⟩
  · exact exc_rational_false_aux2 hp S hT hap ha1 i hdet
      (hout_of_odd (by rw [hr3, hnc12]; decide)) hQ ⟨by omega, by rw [hr3, hnc12]⟩
  · exact exc_rational_false_aux1 hp S hT hap ha1 i hdet (by omega) (by rw [hnc40, hr5])
      (hout_of_odd (by rw [hr5, hnc40]; decide))
  · exact exc_rational_false_aux3 hp hτ S hT hap ha1 i he hq hdet hQ hn3' (by omega)
      (by rw [hnc60, hr6])
  · exact exc_rational_false_aux1 hp S hT hap ha1 i hdet (by omega) (by rw [hnc84, hr7])
      (hout_of_odd (by rw [hr7, hnc84]; decide))

theorem exc_rational_false {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    {e : ℕ} (he : 1 ≤ e) (hq : S.D.q = 2 ^ e) (hqp : p ∣ S.D.q + 1)
    (hen : ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ}, ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ))
    (hQ : CFSG.IsQuasisimple ↥(excRatComp S a i)) {n k : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hk : 1 ≤ k) (hk1 : k = 1 → 5 ≤ n) (hpk : p ∣ 2 ^ k + 1) (hek : e ∣ k)
    (hJ : catalogIs (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i))
      (isOmPA n (2 ^ k))) : False := by
  have hdet : ∀ {t : StatedLieTag} {ν g : ℕ},
      LieModel (↥(excRatComp S a i) ⧸ Subgroup.center ↥(excRatComp S a i)) t ν 2 g →
      (4 ≤ n ∧ t = .POmegaPlus ∧ ν = n) ∨ (n = 3 ∧ 2 ≤ k ∧ t = .PSL ∧ ν = 4) :=
    fun hm => (exc_omPA_type_det hn3 hk hk1 hJ hm).2
  have hen' := hen
  obtain ⟨u, huC, hu⟩ := hen
  have hst : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => exc_rho_mem_component S i huC hu hγ
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    exc_orbitLength_one S.ρ (exc_component_finite hΨ) hst
  have hu1 : ∀ γ ∈ componentRoots (rootCharHom a) i, (S.ρ : (Fin τ.rank → ℤ) → _) γ = -(u • γ) :=
    hu
  have hout_of_odd : Odd (compRank (componentRoots (rootCharHom a) i) +
      (componentRoots (rootCharHom a) i).ncard / 2) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
    intro hodd
    rw [hs1, Function.iterate_one]
    exact exc_not_twistInner_of_odd hΨ huC hu1 hodd
  exact exc_rational_false_aux5 hp hτ S hT hap ha1 i he hq hdet hQ hout_of_odd
    (exc_rational_false_aux4 hp hp2 hp3 hτ S hT hap ha1 i he hq hqp hen' hQ hn hn3 hk hk1 hpk hek hJ)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
