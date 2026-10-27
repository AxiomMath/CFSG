module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Lemma136b

theorem commute_of_bar {G : Type} [Group G] [Finite G] {M H : Subgroup G} {x y : G}
    (hxM : x ∈ M) (hyM : y ∈ M) (hH : IsPGroup 3 ↥H) (hxH : x ∈ H) (hyH : y ∈ H)
    (hcomm : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨y, hyM⟩ : ↥M) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨y, hyM⟩ : ↥M) *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M)) :
    x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) with ha
  set b := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨y, hyM⟩ : ↥M) with hb
  set c : G := x⁻¹ * y⁻¹ * x * y with hc
  have hcM : c ∈ M := M.mul_mem (M.mul_mem (M.mul_mem (M.inv_mem hxM) (M.inv_mem hyM)) hxM) hyM
  have hcH : c ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hxH) (H.inv_mem hyH)) hxH) hyH
  have hbinv : b⁻¹ * a * b = a := by
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (b * a) := by rw [hcomm]
      _ = a := by group
  have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨c, hcM⟩ : ↥M) = 1 := by
    have e : (⟨c, hcM⟩ : ↥M) = (⟨x, hxM⟩ : ↥M)⁻¹ * (⟨y, hyM⟩ : ↥M)⁻¹ * (⟨x, hxM⟩ : ↥M) *
        (⟨y, hyM⟩ : ↥M) := Subtype.ext (by simp [hc])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← ha, ← hb]
    calc a⁻¹ * b⁻¹ * a * b = a⁻¹ * (b⁻¹ * a * b) := by group
      _ = 1 := by rw [hbinv]; group
  have hcO : (⟨c, hcM⟩ : ↥M) ∈ GLAPPrimeCore 3 ↥M := (QuotientGroup.eq_one_iff _).1 hmk
  have hord3 : ∃ k : ℕ, orderOf c = 3 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hH) ⟨c, hcH⟩
    exact ⟨k, (Subgroup.orderOf_coe (⟨c, hcH⟩ : ↥H)).trans hk⟩
  obtain ⟨k, hk⟩ := hord3
  have hdvd : orderOf c ∣ Nat.card ↥(GLAPPrimeCore 3 ↥M) := by
    have h1 := orderOf_dvd_natCard (⟨⟨c, hcM⟩, hcO⟩ : ↥(GLAPPrimeCore 3 ↥M))
    rw [← Subgroup.orderOf_coe] at h1
    simpa [Subgroup.orderOf_coe] using h1
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥M)) := by
    unfold GLAPPrimeCore
    exact pPrimeCore_coprime_card
  have hc1 : orderOf c = 1 := by
    rw [hk] at hdvd ⊢
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop) hdvd
  have hcone : c = 1 := orderOf_eq_one_iff.1 hc1
  calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
    _ = y * x := by rw [← hc, hcone, mul_one]

theorem barX_piOf_le_piStar {G : Type} [Group G] [Finite G] {M D : Subgroup G} {d : G}
    (hdD : d ∈ D) (hd1 : d ≠ 1) :
    barX 3 M (piOf 3 d) ≤ barX 3 M (piStar 3 D) :=
  barX_mono_of_le 3 (le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_sup_left)))

@[expose] def P1GLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (b : ↥M), (b : G) ∈ B →
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b ≠ 1 →
    (∀ y ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * y = y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b) →
    ∀ d : ↥M, (d : G) ∈ D → (d : G) ≠ 1 →
      (¬ (d : G) ∈ Subgroup.normalizer (L : Set G) ∨ (d : G) ∈ centBar 3 ⊤ L) →
      ∀ K : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
        GLAPComponent 3 (barX 3 M (Lstarsub D L) ⊓
          Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) d} :
            Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) K →
        ∃ J : Subgroup G, J ≤ Lstarsub D L ∧
          GLAPComponent 3 (Subgroup.centralizer ({(b : G), (d : G)} : Set G)) J ∧
          barX 3 M J = K

@[expose] def P1GCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (b : ↥M), (b : G) ∈ B →
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b ≠ 1 →
    (∀ y ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * y = y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b) →
    ∀ d : ↥M, (d : G) ∈ D → (d : G) ≠ 1 →
      (¬ (d : G) ∈ Subgroup.normalizer (L : Set G) ∨ (d : G) ∈ centBar 3 ⊤ L) →
      ∀ J : Subgroup G, J ≤ Lstarsub D L →
        GLAPComponent 3 (Subgroup.centralizer ({(b : G), (d : G)} : Set G)) J →
        J ≤ piOf 3 (d : G)

theorem p1BarInput_of_inputs (h135 : Lemma135_iStatement) (hLift : P1GLift) (hCore : P1GCore) :
    Lemma136.P1BarInput := by
  intro G _ _ m B M E A D T L h d hdD hd1 hJd K hK
  have hne := h135 h
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ barX 3 M B ⊓ Subgroup.centralizer
      ((barX 3 M D ⊔ barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)), y ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hne ((Subgroup.eq_bot_iff_forall _).2 hc)
  obtain ⟨hyB, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨b, hbB, rfl⟩ := (mem_barX_iff 3 y).1 hyB
  have hb1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b ≠ 1 := hy1
  have hbc : ∀ z ∈ barX 3 M D ⊔ barX 3 M (Lstarsub D L),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b * z =
        z * QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) b := fun z hz =>
    ((Subgroup.mem_centralizer_iff.1 hyC) z hz).symm
  obtain ⟨J, hJL, hJc, hJK⟩ := hLift G m h b hbB hb1 hbc d hdD hd1 hJd K hK
  have hJpi : J ≤ piOf 3 (d : G) := hCore G m h b hbB hb1 hbc d hdD hd1 hJd J hJL hJc
  rw [← hJK]
  exact (barX_mono_of_le 3 hJpi).trans (barX_piOf_le_piStar hdD hd1)

end Lemma136b

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
