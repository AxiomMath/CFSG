module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ10

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Reduce

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem conj_rootDiagUnit_mem_levi {J : Set (Fin Tag.D4.rank)} (a : Fin Tag.D4.rank → Kˣ)
    {u : ModGL Tag.D4 K} (hu : u ∈ parabolicLevi Tag.D4 K J) :
    rootDiagUnit Tag.D4 a * u * (rootDiagUnit Tag.D4 a)⁻¹ ∈ parabolicLevi Tag.D4 K J := by
  have h : parabolicLevi Tag.D4 K J ≤
      (parabolicLevi Tag.D4 K J).comap (MulAut.conj (rootDiagUnit Tag.D4 a)).toMonoidHom := by
    refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
    · intro t ht
      obtain ⟨b, rfl⟩ := torusGroup_le_range ht
      rw [Subgroup.mem_comap]
      change rootDiagUnit Tag.D4 a * rootDiagUnit Tag.D4 b * (rootDiagUnit Tag.D4 a)⁻¹ ∈
        parabolicLevi Tag.D4 K J
      rw [rootDiagUnit_comm a b, mul_inv_cancel_right]
      exact torusGroup_le_parabolicLevi J ht
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change rootDiagUnit Tag.D4 a * xUnit Tag.D4 K j c * (rootDiagUnit Tag.D4 a)⁻¹ ∈
          parabolicLevi Tag.D4 K J
        rw [(root_diagonal_conjugation Tag.D4 K a).1 j c]
        exact xUnit_mem_parabolicLevi hj _
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change rootDiagUnit Tag.D4 a * yUnit Tag.D4 K j c * (rootDiagUnit Tag.D4 a)⁻¹ ∈
          parabolicLevi Tag.D4 K J
        rw [(root_diagonal_conjugation Tag.D4 K a).2.1 j c]
        exact yUnit_mem_parabolicLevi hj _
  exact h hu

theorem rootDiagUnit_conj_radical {J : Set (Fin Tag.D4.rank)} (a : Fin Tag.D4.rank → Kˣ)
    {q : ModGL Tag.D4 K} (hq : q ∈ parabolicRadical Tag.D4 K J) :
    rootDiagUnit Tag.D4 a * q * (rootDiagUnit Tag.D4 a)⁻¹ ∈ parabolicRadical Tag.D4 K J := by
  have := (Subgroup.mem_normalizer_iff.1
    (rootDiagUnit_mem_normalizer_degSeries (τ := Tag.D4) (K := K) (J := J) a 1) q).1
  rw [degSeries_one] at this
  exact this hq

theorem sq_centralizes_levi {J : Set (Fin Tag.D4.rank)} {q₀ m : ModGL Tag.D4 K}
    (hq₀ : q₀ ∈ parabolicRadical Tag.D4 K J)
    (hmQ : ∀ q ∈ parabolicRadical Tag.D4 K J, m * q * m⁻¹ ∈ parabolicRadical Tag.D4 K J)
    (hmM : ∀ u ∈ parabolicLevi Tag.D4 K J, m * u * m⁻¹ ∈ parabolicLevi Tag.D4 K J)
    (hΓ2 : ∀ x ∈ parabolicLevi Tag.D4 K J, (q₀ * m) * (q₀ * m) * x * ((q₀ * m) * (q₀ * m))⁻¹ = x)
    {x : ModGL Tag.D4 K} (hx : x ∈ parabolicLevi Tag.D4 K J) : m * m * x * (m * m)⁻¹ = x := by
  obtain ⟨hQP, -, -, hMP, hQM, -⟩ := parabolic_root_radical_Levi_factors Tag.D4 K J
  have hxP : x ∈ parabolicSubgroup Tag.D4 K J := hMP hx
  set qs : ModGL Tag.D4 K := q₀ * (m * q₀ * m⁻¹) with hqs
  have hqsQ : qs ∈ parabolicRadical Tag.D4 K J := mul_mem hq₀ (hmQ q₀ hq₀)
  have e : (q₀ * m) * (q₀ * m) = qs * (m * m) := by rw [hqs]; group
  set x₂ : ModGL Tag.D4 K := m * m * x * (m * m)⁻¹ with hx₂
  have hx₂M : x₂ ∈ parabolicLevi Tag.D4 K J := by
    have h1 := hmM x hx
    have h2 := hmM _ h1
    have e2 : m * (m * x * m⁻¹) * m⁻¹ = x₂ := by rw [hx₂]; group
    rwa [e2] at h2
  have h := hΓ2 x hx
  rw [e] at h
  have h' : qs * x₂ * qs⁻¹ = x := by rw [hx₂]; simpa [mul_assoc] using h
  have hxx : x₂ * x⁻¹ ∈ parabolicRadical Tag.D4 K J := by
    have e3 : x₂ * x⁻¹ = qs⁻¹ * (x * qs * x⁻¹) := by
      have : x₂ = qs⁻¹ * x * qs := by
        rw [← h']; group
      rw [this]; group
    rw [e3]
    refine mul_mem (inv_mem hqsQ) ?_
    exact (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hxP) qs).1 hqsQ
  have hxxM : x₂ * x⁻¹ ∈ parabolicLevi Tag.D4 K J := mul_mem hx₂M (inv_mem hx)
  have h1 : x₂ * x⁻¹ ∈ parabolicRadical Tag.D4 K J ⊓ parabolicLevi Tag.D4 K J := ⟨hxx, hxxM⟩
  rw [hQM, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem gamma_conj {J : Set (Fin Tag.D4.rank)} {q₀ m y z : ModGL Tag.D4 K}
    (hq₀ : q₀ ∈ parabolicRadical Tag.D4 K J) (hy : NormAll J y) (hz : NormAll J z)
    (h : y * m * y⁻¹ = z * m) :
    ∃ q ∈ parabolicRadical Tag.D4 K J, y * (q₀ * m) * y⁻¹ = q * (z * (q₀ * m)) := by
  have hy1 : y ∈ Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
    have := hy 1
    rwa [degSeries_one] at this
  have hz1 : z ∈ Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
    have := hz 1
    rwa [degSeries_one] at this
  refine ⟨(y * q₀ * y⁻¹) * (z * q₀ * z⁻¹)⁻¹, mul_mem ((Subgroup.mem_normalizer_iff.1 hy1 q₀).1 hq₀)
    (inv_mem ((Subgroup.mem_normalizer_iff.1 hz1 q₀).1 hq₀)), ?_⟩
  calc y * (q₀ * m) * y⁻¹ = (y * q₀ * y⁻¹) * (y * m * y⁻¹) := by group
    _ = (y * q₀ * y⁻¹) * (z * m) := by rw [h]
    _ = ((y * q₀ * y⁻¹) * (z * q₀ * z⁻¹)⁻¹) * (z * (q₀ * m)) := by group

end Reduce

section Dichotomy

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem rho_mul_diag (a : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) (A : SL2 K) :
    ρ k A * rootDiagUnit Tag.D4 a = rootDiagUnit Tag.D4 a * ρ k (dconj ((a k)⁻¹) A) := by
  rw [← conj_inv_rho a k A]; group

theorem gamma_dichotomy_two (hK2 : ringChar K ≠ 2) {c : ModGL Tag.D4 K}
    (hc : c ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank))) (a : Fin Tag.D4.rank → Kˣ)
    (hΓ2 : ∀ x ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      (c * rootDiagUnit Tag.D4 a) * (c * rootDiagUnit Tag.D4 a) * x *
        ((c * rootDiagUnit Tag.D4 a) * (c * rootDiagUnit Tag.D4 a))⁻¹ = x) :
    (∃ y q : ModGL Tag.D4 K, NormAll ({2} : Set (Fin Tag.D4.rank)) y ∧
      q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) ∧
      y * (c * rootDiagUnit Tag.D4 a) * y⁻¹ = q * (rootDiagUnit Tag.D4
        (zetaDiag (K := K) ({2} : Set (Fin Tag.D4.rank))) * (c * rootDiagUnit Tag.D4 a))) ∨
    (∃ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)), ∃ b' : Fin Tag.D4.rank → Kˣ,
      b' 2 = 1 ∧ c * rootDiagUnit Tag.D4 a = q * rootDiagUnit Tag.D4 b') := by
  obtain ⟨hQP, -, -, hMP, hQM, -, hfact, -⟩ :=
    parabolic_root_radical_Levi_factors Tag.D4 K ({2} : Set (Fin Tag.D4.rank))
  obtain ⟨⟨q₀, m₀⟩, ⟨hq₀, hm₀, hcm⟩, -⟩ := hfact c hc
  simp only at hq₀ hm₀ hcm
  subst hcm
  obtain ⟨b₀, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm₀
  have hl' : l ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl
  obtain ⟨A, rfl⟩ := hl'
  set da : ModGL Tag.D4 K := rootDiagUnit Tag.D4 a with hda
  set m₀ : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b₀ * ρ 2 A with hm₀def
  have hmt : m₀ * da = rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A) := by
    rw [hm₀def, mul_assoc, rho_mul_diag, ← mul_assoc, ← rootDiagUnit_mul]
  have hmQ : ∀ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * q * (m₀ * da)⁻¹ ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) := by
    intro q hq
    have e : (m₀ * da) * q * (m₀ * da)⁻¹ = m₀ * (da * q * da⁻¹) * m₀⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical _ (hMP hm₀)) _).1
        (rootDiagUnit_conj_radical a hq)
  have hmM : ∀ u ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * u * (m₀ * da)⁻¹ ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) := by
    intro u hu
    have e : (m₀ * da) * u * (m₀ * da)⁻¹ = m₀ * (da * u * da⁻¹) * m₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hm₀ (conj_rootDiagUnit_mem_levi a hu)) (inv_mem hm₀)
  have hΓ2' : ∀ x ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      (q₀ * (m₀ * da)) * (q₀ * (m₀ * da)) * x * ((q₀ * (m₀ * da)) * (q₀ * (m₀ * da)))⁻¹ = x := by
    intro x hx
    simpa only [mul_assoc] using hΓ2 x hx
  have hsq : ∀ x ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * (m₀ * da) * x * ((m₀ * da) * (m₀ * da))⁻¹ = x :=
    fun x hx => sq_centralizes_levi hq₀ hmQ hmM hΓ2' hx
  have h2 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A)) *
      (rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A))) * ρ 2 X *
      ((rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A)) *
        (rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A)))⁻¹ = ρ 2 X := fun X => by
    rw [← hmt]
    exact hsq (ρ 2 X) (Lk_le_levi (Set.mem_singleton 2) ⟨X, rfl⟩)
  have hcd : q₀ * m₀ * da = q₀ * (rootDiagUnit Tag.D4 (b₀ * a) * ρ 2 (dconj ((a 2)⁻¹) A)) := by
    rw [mul_assoc, hmt]
  rw [hcd]
  rcases classify_two hK2 (b₀ * a) (dconj ((a 2)⁻¹) A) h2 with ⟨y, hy, hyeq⟩ | ⟨b', hb', hb'eq⟩
  · left
    obtain ⟨q, hq, hqeq⟩ := gamma_conj hq₀ hy (NormAll.of_rootDiagUnit _) hyeq
    exact ⟨y, q, hy, hq, hqeq⟩
  · right
    exact ⟨q₀, hq₀, b', hb', by rw [hb'eq]⟩

theorem outer_mul_diag (a : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K) :
    (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * rootDiagUnit Tag.D4 a =
      rootDiagUnit Tag.D4 a * (ρ 0 (dconj ((a 0)⁻¹) A₀) *
        (ρ 1 (dconj ((a 1)⁻¹) A₁) * ρ 3 (dconj ((a 3)⁻¹) A₃))) := by
  calc (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * rootDiagUnit Tag.D4 a
      = ρ 0 A₀ * (ρ 1 A₁ * (ρ 3 A₃ * rootDiagUnit Tag.D4 a)) := by group
    _ = ρ 0 A₀ * (ρ 1 A₁ * (rootDiagUnit Tag.D4 a * ρ 3 (dconj ((a 3)⁻¹) A₃))) := by
        rw [rho_mul_diag a 3]
    _ = ρ 0 A₀ * ((ρ 1 A₁ * rootDiagUnit Tag.D4 a) * ρ 3 (dconj ((a 3)⁻¹) A₃)) := by group
    _ = ρ 0 A₀ * ((rootDiagUnit Tag.D4 a * ρ 1 (dconj ((a 1)⁻¹) A₁)) *
          ρ 3 (dconj ((a 3)⁻¹) A₃)) := by rw [rho_mul_diag a 1]
    _ = (ρ 0 A₀ * rootDiagUnit Tag.D4 a) * (ρ 1 (dconj ((a 1)⁻¹) A₁) *
          ρ 3 (dconj ((a 3)⁻¹) A₃)) := by group
    _ = (rootDiagUnit Tag.D4 a * ρ 0 (dconj ((a 0)⁻¹) A₀)) * (ρ 1 (dconj ((a 1)⁻¹) A₁) *
          ρ 3 (dconj ((a 3)⁻¹) A₃)) := by rw [rho_mul_diag a 0]
    _ = _ := by group

theorem gamma_dichotomy_three (hK2 : ringChar K ≠ 2) {c : ModGL Tag.D4 K}
    (hc : c ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (a : Fin Tag.D4.rank → Kˣ)
    (hΓ2 : ∀ x ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (c * rootDiagUnit Tag.D4 a) * (c * rootDiagUnit Tag.D4 a) * x *
        ((c * rootDiagUnit Tag.D4 a) * (c * rootDiagUnit Tag.D4 a))⁻¹ = x) :
    (∃ y q : ModGL Tag.D4 K, NormAll ({0, 1, 3} : Set (Fin Tag.D4.rank)) y ∧
      q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∧
      y * (c * rootDiagUnit Tag.D4 a) * y⁻¹ = q * (rootDiagUnit Tag.D4
        (zetaDiag (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))) * (c * rootDiagUnit Tag.D4 a))) ∨
    (∃ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∃ b' : Fin Tag.D4.rank → Kˣ,
      b' 0 = 1 ∧ b' 1 = 1 ∧ b' 3 = 1 ∧ c * rootDiagUnit Tag.D4 a = q * rootDiagUnit Tag.D4 b') := by
  obtain ⟨hQP, -, -, hMP, hQM, -, hfact, -⟩ :=
    parabolic_root_radical_Levi_factors Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank))
  obtain ⟨⟨q₀, m₀⟩, ⟨hq₀, hm₀, hcm⟩, -⟩ := hfact c hc
  simp only at hq₀ hm₀ hcm
  subst hcm
  obtain ⟨b₀, A₀, A₁, A₃, rfl⟩ := levi_outer_decomp hm₀
  set da : ModGL Tag.D4 K := rootDiagUnit Tag.D4 a with hda
  set m₀ : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b₀ * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) with hm₀def
  have hmt : m₀ * da = mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁)
      (dconj ((a 3)⁻¹) A₃) := by
    rw [hm₀def, mul_assoc, hda, outer_mul_diag, ← mul_assoc, ← rootDiagUnit_mul]
    rfl
  have hmQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * q * (m₀ * da)⁻¹ ∈
        parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
    intro q hq
    have e : (m₀ * da) * q * (m₀ * da)⁻¹ = m₀ * (da * q * da⁻¹) * m₀⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical _ (hMP hm₀)) _).1
        (rootDiagUnit_conj_radical a hq)
  have hmM : ∀ u ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * u * (m₀ * da)⁻¹ ∈
        parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
    intro u hu
    have e : (m₀ * da) * u * (m₀ * da)⁻¹ = m₀ * (da * u * da⁻¹) * m₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hm₀ (conj_rootDiagUnit_mem_levi a hu)) (inv_mem hm₀)
  have hΓ2' : ∀ x ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (q₀ * (m₀ * da)) * (q₀ * (m₀ * da)) * x * ((q₀ * (m₀ * da)) * (q₀ * (m₀ * da)))⁻¹ = x := by
    intro x hx
    simpa only [mul_assoc] using hΓ2 x hx
  have hsq : ∀ x ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (m₀ * da) * (m₀ * da) * x * ((m₀ * da) * (m₀ * da))⁻¹ = x :=
    fun x hx => sq_centralizes_levi hq₀ hmQ hmM hΓ2' hx
  have h2 : ∀ k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∀ X : SL2 K,
      (mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁) (dconj ((a 3)⁻¹) A₃) *
        mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁) (dconj ((a 3)⁻¹) A₃)) * ρ k X *
        (mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁) (dconj ((a 3)⁻¹) A₃) *
          mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁) (dconj ((a 3)⁻¹) A₃))⁻¹ =
        ρ k X := fun k hk X => by
    rw [← hmt]
    exact hsq (ρ k X) (Lk_le_levi hk ⟨X, rfl⟩)
  have hcd : q₀ * m₀ * da = q₀ * mm013 (b₀ * a) (dconj ((a 0)⁻¹) A₀) (dconj ((a 1)⁻¹) A₁)
      (dconj ((a 3)⁻¹) A₃) := by
    rw [mul_assoc, hmt]
  rw [hcd]
  rcases classify_three hK2 (b₀ * a) _ _ _ h2 with ⟨y, hy, hyeq⟩ | ⟨b', hb0, hb1, hb3, hb'eq⟩
  · left
    obtain ⟨q, hq, hqeq⟩ := gamma_conj hq₀ hy (NormAll.of_rootDiagUnit _) hyeq
    exact ⟨y, q, hy, hq, hqeq⟩
  · right
    exact ⟨q₀, hq₀, b', hb0, hb1, hb3, by rw [hb'eq]⟩

end Dichotomy

end CFSG.LocalAnalysis.GLTheoremA
