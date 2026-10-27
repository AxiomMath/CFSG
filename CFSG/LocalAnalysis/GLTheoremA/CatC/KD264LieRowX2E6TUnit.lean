module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TLin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open scoped MatrixGroups Matrix

section GroupTheory

theorem three_dvd_quot_center_of_noncentral {J : Type*} [Group J] {z : J} (hz : z ^ 3 = 1)
    (hzc : z ∉ Subgroup.center J) : 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
  set q : J ⧸ Subgroup.center J := QuotientGroup.mk z with hq
  have hq1 : q ≠ 1 := fun h => hzc (QuotientGroup.eq_one_iff z |>.1 h)
  have hq3 : q ^ 3 = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, hz]; rfl
  have hord : orderOf q = 3 := by
    have hdvd : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hq1
    · exact h
  rw [← hord]
  exact orderOf_dvd_natCard q

theorem three_dvd_quot_center {J : Type*} [Group J] [Finite J]
    (hZ : Nat.card (Subgroup.center J) ≤ 3) {x y : J} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : y ≠ x) (hxy' : y ≠ x⁻¹) :
    3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
  classical
  have key : ∀ z : J, z ^ 3 = 1 → z ≠ 1 → z ∉ Subgroup.center J →
      3 ∣ Nat.card (J ⧸ Subgroup.center J) := fun z hz _ hzc =>
    three_dvd_quot_center_of_noncentral hz hzc
  haveI : Fintype (Subgroup.center J) := Fintype.ofFinite _
  haveI : Fintype (Subgroup.center J : Set J) := Fintype.ofFinite _
  by_cases hxc : x ∈ Subgroup.center J
  · by_cases hyc : y ∈ Subgroup.center J
    · exfalso
      have hx2 : x⁻¹ ≠ 1 := fun h => hx1 (inv_eq_one.1 h)
      have hxx : x⁻¹ ≠ x := by
        intro h
        have h2 : x ^ 2 = 1 := by
          have : x * x = 1 := by
            calc x * x = x * x⁻¹ := by rw [h]
              _ = 1 := mul_inv_cancel x
          simpa [pow_two] using this
        apply hx1
        calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
          _ = 1 := by rw [hx, h2]; simp
      have hsub : ({1, x, x⁻¹, y} : Finset J) ⊆
          (Subgroup.center J : Set J).toFinset := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · simp [Subgroup.one_mem]
        · simpa using hxc
        · simpa using inv_mem hxc
        · simpa using hyc
      have hcard4 : ({1, x, x⁻¹, y} : Finset J).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]
          exact hxy'.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hxx.symm, hxy.symm⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hx1.symm, hx2.symm, hy1.symm⟩
      have hle := Finset.card_le_card hsub
      rw [hcard4] at hle
      have : (Subgroup.center J : Set J).toFinset.card = Nat.card (Subgroup.center J) := by
        rw [Set.toFinset_card, Nat.card_eq_fintype_card]
        exact Fintype.card_congr (Equiv.refl _)
      omega
    · exact key y hy hy1 hyc
  · exact key x hx hx1 hxc

end GroupTheory

section Injective

variable
  {τ : CFSG.Blueprint.Chevalley.Tag}
  {L : Type} [Field L] {ν m : ℕ} {ρ : SL(ν, L) →* CFSG.Blueprint.Chevalley.ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GF2Type.SmithTypeE

theorem block_injective (h : IsSLFrame ρ σ) (hν : 3 ≤ ν) (e : Fin m → Fin ν)
    (he : Function.Injective e) {l : Fin ν} (hl : ∀ a, e a ≠ l) :
    Function.Injective (ρ.comp (slEmbed e he)) := by
  classical
  rw [injective_iff_map_eq_one]
  intro κ hκ
  have hker : slEmbed e he κ ∈ ρ.ker := hκ
  obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center hν h hker)
  have hX : ∀ k, k ∈ (Finset.univ.image e) ↔ ∃ a, e a = k := by
    intro k; simp
  have hrange := (mem_range_slEmbed_iff e he hX (slEmbed e he κ)).1 ⟨κ, rfl⟩
  have h1 := congrArg (fun A : Matrix (Fin ν) (Fin ν) L => A l l) hrange
  have hl' : l ∉ (Finset.univ.image e) := fun hh => by
    obtain ⟨a, ha⟩ := (hX l).1 hh
    exact hl a ha
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, projDiag, Matrix.mul_diagonal,
    Matrix.diagonal_mul, if_neg hl', mul_zero, zero_mul] at h1
  have hs1 : s = 1 := by
    have h2 := congrArg (fun A : Matrix (Fin ν) (Fin ν) L => A l l) hs
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
    rw [h2]
    linear_combination h1
  subst hs1
  have : (slEmbed e he κ : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [← hs]; simp
  have h3 : slEmbed e he κ = 1 := Subtype.ext this
  rw [← map_one (slEmbed e he)] at h3
  exact slEmbed_injective he h3

end Injective

section DiagConj

variable {L : Type} [Field L] {m : ℕ}

@[expose] def diagSLm (d : Fin m → L) (hprod : ∏ i, d i = 1) : SL(m, L) :=
  ⟨Matrix.diagonal d, by rw [Matrix.det_diagonal, hprod]⟩

@[expose] def conjDiagSL (H : SL(m, L)) (d : Fin m → L) (hprod : ∏ i, d i = 1) : SL(m, L) :=
  H * diagSLm d hprod * H⁻¹

theorem diagSLm_mul (d d' : Fin m → L) (hd : ∏ i, d i = 1) (hd' : ∏ i, d' i = 1)
    (hdd : ∏ i, (d i * d' i) = 1) :
    diagSLm d hd * diagSLm d' hd' = diagSLm (fun i => d i * d' i) hdd := by
  apply Subtype.ext
  change (Matrix.diagonal d * Matrix.diagonal d' : Matrix (Fin m) (Fin m) L) = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]

theorem conjDiagSL_mul (H : SL(m, L)) (d d' : Fin m → L) (hd : ∏ i, d i = 1)
    (hd' : ∏ i, d' i = 1) (hdd : ∏ i, (d i * d' i) = 1) :
    conjDiagSL H d hd * conjDiagSL H d' hd' = conjDiagSL H (fun i => d i * d' i) hdd := by
  unfold conjDiagSL
  rw [← diagSLm_mul d d' hd hd' hdd]
  group

theorem diagSLm_pow_three (d : Fin m → L) (hprod : ∏ i, d i = 1) (hd : ∀ i, d i ^ 3 = 1) :
    diagSLm d hprod ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  change (Matrix.diagonal d) ^ 3 = (1 : Matrix (Fin m) (Fin m) L)
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

theorem conjDiagSL_pow_three (H : SL(m, L)) (d : Fin m → L) (hprod : ∏ i, d i = 1)
    (hd : ∀ i, d i ^ 3 = 1) : conjDiagSL H d hprod ^ 3 = 1 := by
  unfold conjDiagSL
  rw [conj_pow, diagSLm_pow_three d hprod hd]
  group

theorem conjDiagSL_eq_one_iff (H : SL(m, L)) (d : Fin m → L) (hprod : ∏ i, d i = 1) :
    conjDiagSL H d hprod = 1 ↔ ∀ i, d i = 1 := by
  unfold conjDiagSL
  constructor
  · intro h i
    have h1 : diagSLm d hprod = 1 := by
      have := congrArg (fun A => H⁻¹ * A * H) h
      simpa [mul_assoc] using this
    have h2 := congrArg (fun A : SL(m, L) => (A : Matrix (Fin m) (Fin m) L) i i) h1
    simpa [diagSLm] using h2
  · intro h
    have h1 : diagSLm d hprod = 1 := by
      apply Subtype.ext
      simp only [diagSLm, Matrix.SpecialLinearGroup.coe_one]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact h i
    rw [h1]
    group

@[expose] def dpair (i j : Fin m) (u v : L) : Fin m → L :=
  fun k => if k = i then u else if k = j then v else 1

theorem prod_dpair {i j : Fin m} (hij : i ≠ j) (u v : L) : ∏ k, dpair i j u v k = u * v := by
  classical
  rw [Finset.prod_eq_mul i j hij]
  · simp [dpair, hij.symm]
  · intro k _ hk
    simp [dpair, hk.1, hk.2]
  · intro h
    exact absurd (Finset.mem_univ i) h
  · intro h
    exact absurd (Finset.mem_univ j) h

noncomputable abbrev blockFix {τ : CFSG.Blueprint.Chevalley.Tag} {ν : ℕ}
    (ρ : SL(ν, L) →* CFSG.Blueprint.Chevalley.ModGL τ L) (e : Fin m → Fin ν)
    (he : Function.Injective e) (Ψ : CFSG.Blueprint.Chevalley.ModGL τ L →*
      CFSG.Blueprint.Chevalley.ModGL τ L) : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L) :=
  (ρ.comp (CFSG.GF2Type.SmithTypeE.slEmbed e he)).range ⊓ Ψ.eqLocus (MonoidHom.id _)

end DiagConj

section Facts

variable
  {τ : CFSG.Blueprint.Chevalley.Tag}
  {L : Type} [Field L] {ν m : ℕ} {ρ : SL(ν, L) →* CFSG.Blueprint.Chevalley.ModGL τ L}
  {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GF2Type.SmithTypeE
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem block_unitary_facts (h : IsSLFrame ρ σ) (hν : 3 ≤ ν) (e : Fin m → Fin ν)
    (he : Function.Injective e) (hinj : Function.Injective (ρ.comp (slEmbed e he)))
    (hm : 4 ≤ m)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = 2 ^ 1)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ 1) (Ψ : ModGL τ L →* ModGL τ L)
    (hΨinj : Function.Injective Ψ)
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ (e i) (e j)) c) = pinnedX τ L (σ (e j) (e i)) ((b : L) * Fr c))
    {ω : L} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Finite ↥(blockFix ρ e he Ψ) ∧ CFSG.IsQuasisimple ↥(blockFix ρ e he Ψ) ∧
    Nat.card (Subgroup.center ↥(blockFix ρ e he Ψ)) = Nat.gcd m 3 ∧
    3 ∣ Nat.card (↥(blockFix ρ e he Ψ) ⧸ Subgroup.center ↥(blockFix ρ e he Ψ)) ∧
    ∃ x : ↥(blockFix ρ e he Ψ), x ≠ 1 ∧ x ^ 3 = 1 := by
  classical
  have hρe := isSLFrame_block h e he
  obtain ⟨⟨H, hH⟩, hfin, hq⟩ := hρe.fix_unitary hinj Nat.prime_two le_rfl hk (by omega) Fr hFr Ψ
    hΨinj (Equiv.refl (Fin m)) hΨ
  have hne : (m, 2 ^ 1) ≠ (3, 2) := by
    intro h'
    have := congrArg Prod.fst h'
    simp at this
    omega
  obtain ⟨hqs, hcard⟩ := hq hne
  haveI := hfin
  set J := blockFix ρ e he Ψ with hJdef
  have hω0 : ω ≠ 0 := by
    intro h0; rw [h0] at hω3; norm_num at hω3
  have hω2 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hprodω : ω * ω ^ 2 = 1 := by rw [← pow_succ']; exact hω3
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin m := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂, Fin.ext_iff]
  set d₁ := dpair i₀ i₁ ω (ω ^ 2) with hd₁
  set d₂ := dpair i₁ i₂ ω (ω ^ 2) with hd₂
  have hp₁ : ∏ k, d₁ k = 1 := by rw [hd₁, prod_dpair h01]; exact hprodω
  have hp₂ : ∏ k, d₂ k = 1 := by rw [hd₂, prod_dpair h12]; exact hprodω
  have hd₁3 : ∀ k, d₁ k ^ 3 = 1 := by
    intro k; simp only [hd₁, dpair]; split_ifs
    · exact hω3
    · exact hω2
    · exact one_pow _
  have hd₂3 : ∀ k, d₂ k ^ 3 = 1 := by
    intro k; simp only [hd₂, dpair]; split_ifs
    · exact hω3
    · exact hω2
    · exact one_pow _
  have hmem : ∀ (d : Fin m → L) (hp : ∏ k, d k = 1), (∀ k, d k ^ 3 = 1) →
      (ρ.comp (slEmbed e he)) (conjDiagSL H d hp) ∈ J := by
    intro d hp hd3
    refine ⟨⟨_, rfl⟩, ?_⟩
    have hdet : IsUnit (Matrix.diagonal d).det := by
      rw [Matrix.det_diagonal, hp]; exact isUnit_one
    have hY := CFSG.RankThree.Classical2.diagonal_mem_unitary (Ω := L) (q := 2 ^ 1) (n := m)
      (by norm_num) (d := d) (fun i => by simpa using hd3 i) hp hdet
    refine ((hH _).2 ⟨_, hY, ?_⟩)
    unfold conjDiagSL
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext rfl
  have hone : ∀ (d : Fin m → L) (hp : ∏ k, d k = 1),
      (ρ.comp (slEmbed e he)) (conjDiagSL H d hp) = 1 → ∀ i, d i = 1 := by
    intro d hp h1
    have : conjDiagSL H d hp = 1 := hinj (by rw [h1, map_one])
    exact (conjDiagSL_eq_one_iff H d hp).1 this
  set ρe := ρ.comp (slEmbed e he) with hρe'
  have hp21 : ∏ k, (d₂ k * d₁ k) = 1 := by rw [Finset.prod_mul_distrib, hp₂, hp₁, mul_one]
  have hp211 : ∏ k, ((d₂ k * d₁ k) * d₁ k) = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hp₂, hp₁, mul_one, mul_one]
  have hd21 : ∀ k, (d₂ k * d₁ k) ^ 3 = 1 := fun k => by rw [mul_pow, hd₂3, hd₁3, one_mul]
  let X₁ : J := ⟨ρe (conjDiagSL H d₁ hp₁), hmem d₁ hp₁ hd₁3⟩
  let X₂ : J := ⟨ρe (conjDiagSL H d₂ hp₂), hmem d₂ hp₂ hd₂3⟩
  have hX1 : X₁ ^ 3 = 1 := by
    apply Subtype.ext
    change (ρe (conjDiagSL H d₁ hp₁)) ^ 3 = 1
    rw [← map_pow, conjDiagSL_pow_three H d₁ hp₁ hd₁3, map_one]
  have hX2 : X₂ ^ 3 = 1 := by
    apply Subtype.ext
    change (ρe (conjDiagSL H d₂ hp₂)) ^ 3 = 1
    rw [← map_pow, conjDiagSL_pow_three H d₂ hp₂ hd₂3, map_one]
  have hi₀ω : d₁ i₀ = ω := by simp [hd₁, dpair]
  have hi₁ω : d₂ i₁ = ω := by simp [hd₂, dpair]
  have hi₀1 : d₂ i₀ = 1 := by simp [hd₂, dpair, h01, h02]
  have hZ : Nat.card (Subgroup.center ↥J) ≤ 3 := by
    rw [hcard]
    exact (Nat.gcd_le_right _ (by norm_num)).trans (by norm_num)
  have hX1ne : X₁ ≠ 1 := by
    intro h
    have h1 : ρe (conjDiagSL H d₁ hp₁) = 1 := congrArg Subtype.val h
    have := hone d₁ hp₁ h1 i₀
    rw [hi₀ω] at this
    exact hω1 this
  have hcard' : Nat.card (Subgroup.center ↥J) = Nat.gcd m 3 := by rw [hcard]; norm_num
  refine ⟨hfin, hqs, hcard', ?_, X₁, hX1ne, hX1⟩
  refine three_dvd_quot_center hZ hX1 hX2 hX1ne ?_ ?_ ?_
  · intro h
    have h1 : ρe (conjDiagSL H d₂ hp₂) = 1 := congrArg Subtype.val h
    have := hone d₂ hp₂ h1 i₁
    rw [hi₁ω] at this
    exact hω1 this
  · intro h
    have h1 : ρe (conjDiagSL H d₂ hp₂ * conjDiagSL H d₁ hp₁ * conjDiagSL H d₁ hp₁) = 1 := by
      have h2 : X₂ * X₁ * X₁ = 1 := by
        calc X₂ * X₁ * X₁ = X₁ * X₁ * X₁ := by rw [h]
          _ = X₁ ^ 3 := by rw [pow_three, mul_assoc]
          _ = 1 := hX1
      have h3 := congrArg Subtype.val h2
      simpa [map_mul] using h3
    rw [conjDiagSL_mul H d₂ d₁ hp₂ hp₁ hp21, conjDiagSL_mul H _ d₁ hp21 hp₁ hp211] at h1
    have := hone _ hp211 h1 i₀
    simp only [hi₀1, hi₀ω, one_mul] at this
    apply hω1
    have h5 : ω ^ 3 = 1 := hω3
    have h6 : ω * ω = 1 := this
    calc ω = ω * (ω * ω) := by rw [h6, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := h5
  · intro h
    have h1 : ρe (conjDiagSL H d₂ hp₂ * conjDiagSL H d₁ hp₁) = 1 := by
      have h2 : X₂ * X₁ = 1 := by
        rw [mul_eq_one_iff_eq_inv]; exact h
      have h3 := congrArg Subtype.val h2
      simpa [map_mul] using h3
    rw [conjDiagSL_mul H d₂ d₁ hp₂ hp₁ hp21] at h1
    have := hone _ hp21 h1 i₀
    simp only [hi₀1, hi₀ω, one_mul] at this
    exact hω1 this

end Facts

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
