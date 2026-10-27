module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ9
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL5

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even

section Ly

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem rootDiagUnit_comm (a a' : Fin Tag.D4.rank → Kˣ) :
    rootDiagUnit Tag.D4 (K := K) a * rootDiagUnit Tag.D4 a' =
      rootDiagUnit Tag.D4 a' * rootDiagUnit Tag.D4 a := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem y_conj_levi (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) (A Y₁ : SL2 K)
    (R : ModGL Tag.D4 K) (hR : ∀ Z : SL2 K, Commute R (ρ k Z))
    (hRu : Commute R (rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1))))
    (hmat : dconj (-1) (dconj ((b k)⁻¹) Y₁ * A * Y₁⁻¹) = HSL (-1) * A) :
    (rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1)) * ρ k Y₁) *
        (rootDiagUnit Tag.D4 b * (ρ k A * R)) *
        (rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1)) * ρ k Y₁)⁻¹ =
      ρ k (HSL (-1)) * (rootDiagUnit Tag.D4 b * (ρ k A * R)) := by
  set u : Fin Tag.D4.rank → Kˣ := Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1) with hu
  set du : ModGL Tag.D4 K := rootDiagUnit Tag.D4 u with hdu
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  have hu_k : u k = -1 := by rw [hu]; exact Function.update_self ..
  have hx : ρ k Y₁ * h = h * ρ k (dconj ((b k)⁻¹) Y₁) := by
    rw [← conj_inv_rho b k Y₁, ← hh]; group
  have hdh : du * h = h * du := rootDiagUnit_comm u b
  have hRx : R * (ρ k Y₁)⁻¹ = (ρ k Y₁)⁻¹ * R := (hR Y₁).inv_right.eq
  have hRdu : R * du⁻¹ = du⁻¹ * R := hRu.inv_right.eq
  have hconj : ∀ P : SL2 K, du * ρ k P * du⁻¹ = ρ k (dconj (-1) P) := fun P => by
    rw [hdu, torus_conj_rho u k P, hu_k]
  have hζ : ρ k (HSL (-1)) * h = h * ρ k (HSL (-1)) := by
    rw [simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, hh]
    exact rootDiagUnit_comm _ b
  calc (du * ρ k Y₁) * (h * (ρ k A * R)) * (du * ρ k Y₁)⁻¹
      = du * (ρ k Y₁ * h) * ρ k A * (R * (ρ k Y₁)⁻¹) * du⁻¹ := by group
    _ = du * (h * ρ k (dconj ((b k)⁻¹) Y₁)) * ρ k A * ((ρ k Y₁)⁻¹ * R) * du⁻¹ := by
        rw [hx, hRx]
    _ = (du * h) * ρ k (dconj ((b k)⁻¹) Y₁ * A * Y₁⁻¹) * (R * du⁻¹) := by
        rw [map_mul, map_mul, map_inv]; group
    _ = h * (du * ρ k (dconj ((b k)⁻¹) Y₁ * A * Y₁⁻¹) * du⁻¹) * R := by
        rw [hdh, hRdu]; group
    _ = h * ρ k (HSL (-1) * A) * R := by rw [hconj, hmat]
    _ = ρ k (HSL (-1)) * (h * (ρ k A * R)) := by
        rw [map_mul]
        calc h * (ρ k (HSL (-1)) * ρ k A) * R = (h * ρ k (HSL (-1))) * ρ k A * R := by group
          _ = (ρ k (HSL (-1)) * h) * ρ k A * R := by rw [hζ]
          _ = ρ k (HSL (-1)) * (h * (ρ k A * R)) := by group

end Ly

section Classify

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem conj_action (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) (A : SL2 K) (R : ModGL Tag.D4 K)
    (hR : ∀ Z : SL2 K, Commute R (ρ k Z)) (X : SL2 K) :
    (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k X * (rootDiagUnit Tag.D4 b * (ρ k A * R))⁻¹ =
      ρ k (dconj (b k) (A * X * A⁻¹)) := by
  have h1 : R * ρ k X * R⁻¹ = ρ k X := by rw [(hR X).eq, mul_inv_cancel_right]
  calc (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k X * (rootDiagUnit Tag.D4 b * (ρ k A * R))⁻¹
      = rootDiagUnit Tag.D4 b * (ρ k A * (R * ρ k X * R⁻¹) * (ρ k A)⁻¹) *
          (rootDiagUnit Tag.D4 b)⁻¹ := by group
    _ = rootDiagUnit Tag.D4 b * (ρ k A * ρ k X * (ρ k A)⁻¹) * (rootDiagUnit Tag.D4 b)⁻¹ := by
        rw [h1]
    _ = rootDiagUnit Tag.D4 b * ρ k (A * X * A⁻¹) * (rootDiagUnit Tag.D4 b)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
    _ = ρ k (dconj (b k) (A * X * A⁻¹)) := torus_conj_rho b k _

theorem psi_involutive (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank)
    (A : SL2 K) (R : ModGL Tag.D4 K) (hR : ∀ Z : SL2 K, Commute R (ρ k Z))
    (h2 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R))) *
      ρ k X * ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R)))⁻¹ =
        ρ k X) (X : SL2 K) :
    dconj (b k) (A * dconj (b k) (A * X * A⁻¹) * A⁻¹) = X := by
  apply simpleRootSL2_injective hK2 k
  have e : ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R))) *
      ρ k X * ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R)))⁻¹ =
      (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k X *
        (rootDiagUnit Tag.D4 b * (ρ k A * R))⁻¹) * (rootDiagUnit Tag.D4 b * (ρ k A * R))⁻¹ := by
    group
  have h2X := h2 X
  rw [e, conj_action b k A R hR X, conj_action b k A R hR] at h2X
  exact h2X

theorem node_dichotomy (hK2 : ringChar K ≠ 2) {J : Set (Fin Tag.D4.rank)} {k : Fin Tag.D4.rank}
    (hkJ : k ∈ J) (hζ : ρ k (HSL (-1)) = rootDiagUnit Tag.D4 (zetaDiag (K := K) J))
    (b : Fin Tag.D4.rank → Kˣ) (A : SL2 K) (R : ModGL Tag.D4 K) (hR : ∀ Z : SL2 K, Commute R (ρ k Z))
    (hRu : Commute R (rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1))))
    (h2 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R))) *
      ρ k X * ((rootDiagUnit Tag.D4 b * (ρ k A * R)) * (rootDiagUnit Tag.D4 b * (ρ k A * R)))⁻¹ =
        ρ k X) :
    (∃ y : ModGL Tag.D4 K, NormAll J y ∧ y * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * y⁻¹ =
      rootDiagUnit Tag.D4 (zetaDiag (K := K) J) * (rootDiagUnit Tag.D4 b * (ρ k A * R))) ∨
    (∃ u : Kˣ, A = HSL u ∧ ((u : Kˣ) : K) ^ 2 * ((b k : Kˣ) : K) = 1) := by
  have hψ := psi_involutive hK2 b k A R hR h2
  obtain ⟨l, hl⟩ := gm_sq_scalar (b k) A hψ
  by_cases hs : ∃ μ : K, gm ((b k : Kˣ) : K) (A : Matrix (Fin 2) (Fin 2) K) =
      μ • (1 : Matrix (Fin 2) (Fin 2) K)
  · obtain ⟨μ, hμ⟩ := hs
    exact Or.inr (eq_HSL_of_gm_scalar (b k) A μ hμ)
  · left
    obtain ⟨Y₁, hY₁⟩ := exists_dconj_neg (Ring.two_ne_zero hK2) (b k) A ⟨l, hl⟩ hs
    refine ⟨rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1)) * ρ k Y₁,
      (NormAll.of_rootDiagUnit _).mul (NormAll.of_parabolic
        (parabolicLevi_le_parabolicSubgroup J (Lk_le_levi hkJ ⟨Y₁, rfl⟩))), ?_⟩
    rw [y_conj_levi b k A Y₁ R hR hRu hY₁, hζ]

theorem rho_negOne_eq_zeta_two :
    ρ 2 (HSL (-1)) = rootDiagUnit Tag.D4 (zetaDiag (K := K) ({2} : Set (Fin Tag.D4.rank))) := by
  rw [simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  have hc : Tag.D4.cartan 2 j = if j = 2 then 2 else -1 := by revert j; decide
  rw [hc]
  by_cases hj : j = 2 <;> simp [zetaDiag, hj]

theorem rho_negOne_eq_zeta_three' {k : Fin Tag.D4.rank}
    (hk : k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    ρ k (HSL (-1)) =
      rootDiagUnit Tag.D4 (zetaDiag (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))) := by
  rw [simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  have hc : ∀ k : Fin Tag.D4.rank, k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) →
      ∀ j : Fin Tag.D4.rank, Tag.D4.cartan k j = if j = k then 2 else if j = 2 then -1 else 0 := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  rw [hc k hk j]
  have h4 : ∀ j : Fin Tag.D4.rank, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl <;> rcases h4 j with rfl | rfl | rfl | rfl <;> simp [zetaDiag]

theorem commute_rho_update {j k : Fin Tag.D4.rank} (hjk : j ≠ k) (X : SL2 K) :
    Commute (ρ j X) (rootDiagUnit Tag.D4 (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1))) := by
  have h := torus_conj_rho (Function.update (1 : Fin Tag.D4.rank → Kˣ) k (-1)) j X
  rw [Function.update_of_ne hjk, Pi.one_apply, dconj_one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem unit_pow_two_mul (u v : Kˣ) (h : ((u : Kˣ) : K) ^ 2 * ((v : Kˣ) : K) = 1) : u ^ 2 * v = 1 :=
  Units.ext (by simpa using h)

theorem classify_two (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (A : SL2 K)
    (h2 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * ρ 2 A) * (rootDiagUnit Tag.D4 b * ρ 2 A)) * ρ 2 X *
      ((rootDiagUnit Tag.D4 b * ρ 2 A) * (rootDiagUnit Tag.D4 b * ρ 2 A))⁻¹ = ρ 2 X) :
    (∃ y : ModGL Tag.D4 K, NormAll ({2} : Set (Fin Tag.D4.rank)) y ∧
        y * (rootDiagUnit Tag.D4 b * ρ 2 A) * y⁻¹ =
          rootDiagUnit Tag.D4 (zetaDiag (K := K) ({2} : Set (Fin Tag.D4.rank))) *
            (rootDiagUnit Tag.D4 b * ρ 2 A)) ∨
    (∃ b' : Fin Tag.D4.rank → Kˣ, b' 2 = 1 ∧ rootDiagUnit Tag.D4 b * ρ 2 A = rootDiagUnit Tag.D4 b') := by
  have h2' : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ 2 A * 1)) * (rootDiagUnit Tag.D4 b * (ρ 2 A * 1))) *
      ρ 2 X * ((rootDiagUnit Tag.D4 b * (ρ 2 A * 1)) * (rootDiagUnit Tag.D4 b * (ρ 2 A * 1)))⁻¹ =
        ρ 2 X := by simpa only [mul_one] using h2
  rcases node_dichotomy hK2 (Set.mem_singleton 2) rho_negOne_eq_zeta_two b A 1
      (fun Z => Commute.one_left _) (Commute.one_left _) h2' with h | ⟨u, hA, hu⟩
  · left; simpa only [mul_one] using h
  · right
    refine ⟨b * fun j => u ^ Tag.D4.cartan 2 j, ?_, ?_⟩
    · have hc : Tag.D4.cartan 2 2 = 2 := by decide
      simp only [Pi.mul_apply, hc]
      rw [mul_comm]
      exact unit_pow_two_mul u (b 2) hu
    · rw [hA, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, rootDiagUnit_mul]

@[expose] def mm013 (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K) : ModGL Tag.D4 K :=
  rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))

theorem mm013_eq_one (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K) :
    mm013 b A₀ A₁ A₃ = rootDiagUnit Tag.D4 b * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃)) := by
  unfold mm013
  congr 1
  rw [← mul_assoc, (comm01 A₀ A₁).eq, mul_assoc]

theorem mm013_eq_three (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K) :
    mm013 b A₀ A₁ A₃ = rootDiagUnit Tag.D4 b * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁)) := by
  unfold mm013
  congr 1
  have h : Commute (ρ 0 A₀ * ρ 1 A₁) (ρ 3 A₃) :=
    (comm03 A₀ A₃).mul_left (comm13 A₁ A₃)
  calc ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃) = (ρ 0 A₀ * ρ 1 A₁) * ρ 3 A₃ := (mul_assoc _ _ _).symm
    _ = ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁) := h.eq

theorem classify_three (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K)
    (h2 : ∀ k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∀ X : SL2 K,
      (mm013 b A₀ A₁ A₃ * mm013 b A₀ A₁ A₃) * ρ k X * (mm013 b A₀ A₁ A₃ * mm013 b A₀ A₁ A₃)⁻¹ = ρ k X) :
    (∃ y : ModGL Tag.D4 K, NormAll ({0, 1, 3} : Set (Fin Tag.D4.rank)) y ∧
        y * mm013 b A₀ A₁ A₃ * y⁻¹ =
          rootDiagUnit Tag.D4 (zetaDiag (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))) *
            mm013 b A₀ A₁ A₃) ∨
    (∃ b' : Fin Tag.D4.rank → Kˣ, b' 0 = 1 ∧ b' 1 = 1 ∧ b' 3 = 1 ∧
      mm013 b A₀ A₁ A₃ = rootDiagUnit Tag.D4 b') := by
  have hζ : ∀ k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      ρ k (HSL (-1)) = rootDiagUnit Tag.D4 (zetaDiag (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))) := by
    intro k hk
    exact rho_negOne_eq_zeta_three' hk
  have h20 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) *
      (rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)))) * ρ 0 X *
      ((rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) *
        (rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))))⁻¹ = ρ 0 X := fun X => h2 0 mem_outer0 X
  rcases node_dichotomy hK2 mem_outer0 (hζ 0 mem_outer0) b A₀ (ρ 1 A₁ * ρ 3 A₃)
      (fun Z => (comm01 Z A₁).symm.mul_left (comm03 Z A₃).symm)
      (((commute_rho_update (by decide) A₁).mul_left (commute_rho_update (by decide) A₃)))
      h20 with h | ⟨u₀, hA₀, hu₀⟩
  · exact Or.inl h
  have h21 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃))) *
      (rootDiagUnit Tag.D4 b * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃)))) * ρ 1 X *
      ((rootDiagUnit Tag.D4 b * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃))) *
        (rootDiagUnit Tag.D4 b * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃))))⁻¹ = ρ 1 X := fun X => by
    have := h2 1 mem_outer1 X
    rwa [mm013, ← mm013, mm013_eq_one] at this
  rcases node_dichotomy hK2 mem_outer1 (hζ 1 mem_outer1) b A₁ (ρ 0 A₀ * ρ 3 A₃)
      (fun Z => (comm01 A₀ Z).mul_left (comm13 Z A₃).symm)
      (((commute_rho_update (by decide) A₀).mul_left (commute_rho_update (by decide) A₃)))
      h21 with h | ⟨u₁, hA₁, hu₁⟩
  · left
    obtain ⟨y, hy, hyeq⟩ := h
    exact ⟨y, hy, by rw [mm013_eq_one]; exact hyeq⟩
  have h23 : ∀ X : SL2 K, ((rootDiagUnit Tag.D4 b * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁))) *
      (rootDiagUnit Tag.D4 b * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁)))) * ρ 3 X *
      ((rootDiagUnit Tag.D4 b * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁))) *
        (rootDiagUnit Tag.D4 b * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁))))⁻¹ = ρ 3 X := fun X => by
    have := h2 3 mem_outer3 X
    rwa [mm013, ← mm013, mm013_eq_three] at this
  rcases node_dichotomy hK2 mem_outer3 (hζ 3 mem_outer3) b A₃ (ρ 0 A₀ * ρ 1 A₁)
      (fun Z => (comm03 A₀ Z).mul_left (comm13 A₁ Z))
      (((commute_rho_update (by decide) A₀).mul_left (commute_rho_update (by decide) A₁)))
      h23 with h | ⟨u₃, hA₃, hu₃⟩
  · left
    obtain ⟨y, hy, hyeq⟩ := h
    exact ⟨y, hy, by rw [mm013_eq_three]; exact hyeq⟩
  right
  have c00 : Tag.D4.cartan 0 0 = 2 := by decide
  have c10 : Tag.D4.cartan 1 0 = 0 := by decide
  have c30 : Tag.D4.cartan 3 0 = 0 := by decide
  have c01 : Tag.D4.cartan 0 1 = 0 := by decide
  have c11 : Tag.D4.cartan 1 1 = 2 := by decide
  have c31 : Tag.D4.cartan 3 1 = 0 := by decide
  have c03 : Tag.D4.cartan 0 3 = 0 := by decide
  have c13 : Tag.D4.cartan 1 3 = 0 := by decide
  have c33 : Tag.D4.cartan 3 3 = 2 := by decide
  refine ⟨b * ((fun j => u₀ ^ Tag.D4.cartan 0 j) * ((fun j => u₁ ^ Tag.D4.cartan 1 j) *
    (fun j => u₃ ^ Tag.D4.cartan 3 j))), ?_, ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, c00, c10, c30, zpow_zero, mul_one]
    rw [mul_comm]; exact unit_pow_two_mul u₀ (b 0) hu₀
  · simp only [Pi.mul_apply, c01, c11, c31, zpow_zero, one_mul, mul_one]
    rw [mul_comm]; exact unit_pow_two_mul u₁ (b 1) hu₁
  · simp only [Pi.mul_apply, c03, c13, c33, zpow_zero, one_mul]
    rw [mul_comm]; exact unit_pow_two_mul u₃ (b 3) hu₃
  · unfold mm013
    rw [hA₀, hA₁, hA₃, simpleRootSL2_HSL, simpleRootSL2_HSL, simpleRootSL2_HSL,
      torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_mul]

end Classify

end CFSG.LocalAnalysis.GLTheoremA
