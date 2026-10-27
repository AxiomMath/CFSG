module

public import CFSG.ClassicalInvolution.Asc77.AscT8V11
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.Asc77.AscIHSectD

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace T8V

structure E4Pair {S X : Type} [Group S] [Group X] (ψ : S →* X) (R R' : Subgroup S) (y y' : S) :
    Prop where
  surj : Function.Surjective ψ
  ker : ψ.ker ≤ Subgroup.center S
  perf : Group.IsPerfect S
  perfR : R ≤ ⁅R, R⁆
  perfR' : R' ≤ ⁅R', R'⁆
  ne : R ≠ R'
  comm : Commutes R R'
  hy : y ∈ R
  hy2 : y * y = 1
  hy1 : y ≠ 1
  hy' : y' ∈ R'
  hy'2 : y' * y' = 1
  hy'1 : y' ≠ 1
  cen : y * y' ∈ Subgroup.center S
  nontwin : y * y' ∉ ψ.ker
  nc : ψ y ∉ Subgroup.center X

section Transfer

variable {p f : ℕ} [Fact p.Prime]

theorem not_mem_center_of_adj {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : HypOmegaMod p f Φ) (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x : X} (hx : IsUniqueInvolution A x) :
    x ∉ Subgroup.center X := by
  intro hc
  have hN : Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (A : Set X) :=
    T8.centralizer_le_normalizer_of_noTwins hΦ.conjInvariant hA (hnt _ hA) hx
  have hall : ∀ g : X, conjSub g A = A := fun g => by
    have : g ∈ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_center_iff.mp hc g
    exact mem_normalizer_iff_conjSub_eq.mp (hN this)
  obtain ⟨g, hg⟩ := htrans A hA B hB.1
  exact hB.2.1 (by rw [← hg, hall g])

end Transfer

section Assemble

variable {S X : Type} [Group S] [Group X]

theorem e4_assemble {ψ : S →* X} {R R' : Subgroup S} {y y' : S} (hP : E4Pair ψ R R' y y')
    (hσ1 : ∀ σ : MulAut X, (∀ r ∈ R, σ (ψ r) = ψ r) → (∀ r ∈ R', σ (ψ r) = ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1)
    (he1 : ∀ s : S, (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ ψ.ker, s * s ≠ y * y' * k)
    (hA0 : oddCoreOf (R.map ψ) = ⊥) (hB0 : oddCoreOf (R'.map ψ) = ⊥) :
    (∀ σ : MulAut X, (∀ k ∈ R.map ψ, σ k * k⁻¹ ∈ oddCoreOf (R.map ψ)) →
      (∀ k ∈ R'.map ψ, σ k * k⁻¹ ∈ oddCoreOf (R'.map ψ)) → σ * σ ≠ MulAut.conj (ψ y)) ∧
    (∀ e : X, (∀ k ∈ R.map ψ, ⁅e, k⁆ ∈ oddCoreOf (R.map ψ)) →
      (∀ k ∈ R'.map ψ, ⁅e, k⁆ ∈ oddCoreOf (R'.map ψ)) → e * e ≠ ψ y * ψ y') := by
  refine ⟨fun σ h1 h2 hsq => ?_, fun e h1 h2 hsq => ?_⟩
  · have hfixR : ∀ r ∈ R, σ (ψ r) = ψ r := by
      intro r hr
      have := h1 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have hfixR' : ∀ r ∈ R', σ (ψ r) = ψ r := by
      intro r hr
      have := h2 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hB0, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have hσ4 : σ * σ * (σ * σ) = 1 := by
      rw [hsq, ← map_mul, ← map_mul ψ y y, hP.hy2, map_one, map_one]
    have h3 := hσ1 σ hfixR hfixR' hσ4
    rw [hsq] at h3
    apply hP.nc
    rw [Subgroup.mem_center_iff]
    intro z
    have h4 := congrArg (fun τ : MulAut X => τ z) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at h4
    calc z * ψ y = (ψ y * z * (ψ y)⁻¹) * ψ y := by rw [h4]
      _ = ψ y * z := by group
  · obtain ⟨s, rfl⟩ := hP.surj e
    have hcR : ∀ r ∈ R, ψ s * ψ r = ψ r * ψ s := by
      intro r hr
      have := h1 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hA0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcR' : ∀ r ∈ R', ψ s * ψ r = ψ r * ψ s := by
      intro r hr
      have := h2 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hB0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hs1 := comm_of_map_comm ψ hP.ker hP.perfR hcR
    have hs2 := comm_of_map_comm ψ hP.ker hP.perfR' hcR'
    have hk : (y * y')⁻¹ * (s * s) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hsq]
      group
    exact he1 s hs1 hs2 _ hk (by group)

end Assemble

section Model

variable {p f : ℕ} [Fact p.Prime]


theorem e4_pair_of_model (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {t : StatedLieTag} {k e : ℕ}
    (M : Ih8Model p f Φ t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnpsl : ¬ (t = .PSL ∧ k = 2)) (hSperf : Group.IsPerfect (modelUniv t k p e Fact.out).K)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    ∃ (R R' : Subgroup (modelUniv t k p e Fact.out).K) (y y' : (modelUniv t k p e Fact.out).K),
      R ∈ M.cls ∧ R' ∈ M.cls ∧ A = R.map M.ψ ∧ B = R'.map M.ψ ∧ M.ψ y = x ∧ M.ψ y' = x' ∧
        E4Pair M.ψ R R' y y' := by
  obtain ⟨R, hR, hAR⟩ := (M.mem_iff A).mp hA
  obtain ⟨R', hR', hBR⟩ := (M.mem_iff B).mp hB.1
  have hcomm : Commutes R R' :=
    M.commutes_of_omegaNbr_sect hΦ hp2 hq hG2 hD4 hR hR' (by rw [← hAR, ← hBR]; exact hB)
  have hodd := M.natCard_galoisField_odd hp2
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eR'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR'
  have hinj : ∀ R₀ : Subgroup (modelUniv t k p e Fact.out).K, R₀ ∈ M.cls →
      ∀ a ∈ R₀, ∀ b ∈ R₀, M.ψ a = M.ψ b → a = b := by
    intro R₀ hR₀ a ha b hb hab
    have h1 : a * b⁻¹ = 1 := M.injOn_fund hnpsl (M.cls_sub hR₀) (a * b⁻¹)
      (R₀.mul_mem ha (R₀.inv_mem hb)) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  have hψy : M.ψ (sl2Inv eR) = x := by
    have hmem : M.ψ (sl2Inv eR) ∈ A := by
      rw [hAR]
      exact Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
    have hsq : M.ψ (sl2Inv eR) * M.ψ (sl2Inv eR) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR, map_one]
    rcases hxA.unique _ hmem hsq with h | h
    · exact absurd (hinj R hR _ (sl2Inv_mem eR) 1 R.one_mem (by rw [h, map_one]))
        (sl2Inv_ne_one hodd eR)
    · exact h
  have hψy' : M.ψ (sl2Inv eR') = x' := by
    have hmem : M.ψ (sl2Inv eR') ∈ B := by
      rw [hBR]
      exact Subgroup.mem_map_of_mem _ (sl2Inv_mem eR')
    have hsq : M.ψ (sl2Inv eR') * M.ψ (sl2Inv eR') = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR', map_one]
    rcases hxB.unique _ hmem hsq with h | h
    · exact absurd (hinj R' hR' _ (sl2Inv_mem eR') 1 R'.one_mem (by rw [h, map_one]))
        (sl2Inv_ne_one hodd eR')
    · exact h
  refine ⟨R, R', sl2Inv eR, sl2Inv eR', hR, hR', hAR, hBR, hψy, hψy', ?_⟩
  refine ⟨M.surj, M.ker_le_center, hSperf, M.cls_perfect hp2 hD4 hq hR,
    M.cls_perfect hp2 hD4 hq hR', ?_, hcomm, sl2Inv_mem eR, sl2Inv_mul_self hodd eR,
    sl2Inv_ne_one hodd eR, sl2Inv_mem eR', sl2Inv_mul_self hodd eR', sl2Inv_ne_one hodd eR', ?_,
    ?_, ?_⟩
  · intro h
    exact hB.2.1 (by rw [hBR, ← h, ← hAR])
  · exact mem_center_of_map_mem_center hSperf M.ψ M.ker_le_center
      (by rw [map_mul, hψy, hψy']; exact hcen)
  · intro h
    rw [MonoidHom.mem_ker, map_mul, hψy, hψy'] at h
    have hx' : x' = x := by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hxA.sq]
    exact hB.2.1 (hnt A hA B ⟨hB.1, x, hxA, hx' ▸ hxB⟩)
  · rw [hψy]
    exact not_mem_center_of_adj hΦ hnt htrans hA hB hxA

end Model

end T8V

end CFSG.ClassicalInvolution.Asc77
