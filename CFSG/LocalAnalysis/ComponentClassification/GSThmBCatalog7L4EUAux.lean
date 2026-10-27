module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EULift

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal)
open scoped commutatorElement

section Mat

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

variable {h} in
theorem eq_of_mul_swap {Y M₁ M₂ : Matrix (Fin 4) (Fin 4) K} (hYY : Y * Y.map h.bar = -1)
    (hM : M₁ * Y = M₂ * Y) : M₁ = M₂ := by
  have hYi : Y * (-(Y.map h.bar)) = 1 := by rw [Matrix.mul_neg, hYY, neg_neg]
  calc M₁ = M₁ * Y * (-(Y.map h.bar)) := by rw [Matrix.mul_assoc, hYi, Matrix.mul_one]
    _ = M₂ * Y * (-(Y.map h.bar)) := by rw [hM]
    _ = M₂ := by rw [Matrix.mul_assoc, hYi, Matrix.mul_one]

variable {h} in
theorem eq_of_mul_swap_swap {Y g g₁ g₂ : Matrix (Fin 4) (Fin 4) K} (hYY : Y * Y.map h.bar = -1)
    (h1 : g₁ * Y = Y * g.map h.bar) (h2 : g₂ * Y = Y * g₁.map h.bar) : g₂ = g := by
  have h1' : g₁.map h.bar * Y.map h.bar = Y.map h.bar * g := by
    have := congrArg (fun M => M.map h.bar) h1
    simp only [Matrix.map_mul] at this
    rwa [map_map_bar] at this
  have e : g₂ * (Y * Y.map h.bar) = Y * Y.map h.bar * g := by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, h1', ← Matrix.mul_assoc]
  rw [hYY, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul] at e
  exact neg_inj.mp e

variable {h} in
theorem eq_of_mul_swap_conj {Y g g₁ g₃ : Matrix (Fin 4) (Fin 4) K} {T : GL (Fin 4) K} {s : K}
    (hYY : Y * Y.map h.bar = -1)
    (hs : Y * (T : Matrix (Fin 4) (Fin 4) K).map h.bar = s • ((T : Matrix (Fin 4) (Fin 4) K) * Y))
    (h1 : g₁ * Y = Y * g.map h.bar)
    (h3 : g₃ * Y = Y * ((T : Matrix (Fin 4) (Fin 4) K) * g * (↑T⁻¹ : Matrix (Fin 4) (Fin 4) K)).map
      h.bar) :
    g₃ = (T : Matrix (Fin 4) (Fin 4) K) * g₁ * (↑T⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  set Tm : Matrix (Fin 4) (Fin 4) K := (T : Matrix (Fin 4) (Fin 4) K) with hTm
  set Ti : Matrix (Fin 4) (Fin 4) K := (↑T⁻¹ : Matrix (Fin 4) (Fin 4) K) with hTi
  have hTTi : Tm * Ti = 1 := by rw [hTm, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hTiT : Ti * Tm = 1 := by rw [hTm, hTi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbT : Tm.map h.bar * Ti.map h.bar = 1 := by
    rw [← Matrix.map_mul, hTTi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hs
    have e := congrArg (fun M => (-(Y.map h.bar)) * M * Ti.map h.bar) hs
    simp only [Matrix.mul_zero, Matrix.zero_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hbT, Matrix.mul_one, Matrix.neg_mul] at e
    have hYi : (Y.map h.bar) * Y = -1 := by
      have h1 : Y * (-(Y.map h.bar)) = 1 := by rw [Matrix.mul_neg, hYY, neg_neg]
      have h2 := mul_eq_one_comm.mp h1
      rw [Matrix.neg_mul] at h2
      rw [← neg_neg (Y.map h.bar * Y), h2]
    rw [hYi, neg_neg] at e
    exact one_ne_zero e
  have hsi : Y * Ti.map h.bar = s⁻¹ • (Ti * Y) := by
    have e : Ti * (Y * Tm.map h.bar) * Ti.map h.bar = Ti * (s • (Tm * Y)) * Ti.map h.bar := by
      rw [hs]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hbT, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc Ti Tm, hTiT, Matrix.one_mul, Matrix.smul_mul] at e
    rw [e, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  apply eq_of_mul_swap hYY
  rw [h3, Matrix.map_mul, Matrix.map_mul]
  calc Y * (Tm.map h.bar * g.map h.bar * Ti.map h.bar) =
      (Y * Tm.map h.bar) * g.map h.bar * Ti.map h.bar := by simp only [Matrix.mul_assoc]
    _ = s • (Tm * (Y * g.map h.bar) * Ti.map h.bar) := by
        rw [hs, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = s • (Tm * g₁ * (Y * Ti.map h.bar)) := by rw [← h1]; simp only [Matrix.mul_assoc]
    _ = Tm * g₁ * Ti * Y := by
        rw [hsi, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
        simp only [Matrix.mul_assoc]

theorem mul_swap_of_conj {A : GL (Fin 4) K} {Y : Matrix (Fin 4) (Fin 4) K}
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {R : unitarySU p f K 4}
    (hAR : (A : Matrix (Fin 4) (Fin 4) K) *
      ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = Y) (g : unitarySU p f K 4) :
    ((ψ (R * g * R⁻¹) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Y =
      Y * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar := by
  have hAiA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRiR : ((((R⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
      h.bar) * ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  rw [hψA, ← hAR, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    Matrix.map_mul, Matrix.map_mul]
  calc (A : Matrix (Fin 4) (Fin 4) K) *
        (((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((((R⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)) *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((A : Matrix (Fin 4) (Fin 4) K) *
          ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar) =
      (A : Matrix (Fin 4) (Fin 4) K) *
        ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (((((R⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar) *
          (((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * A) *
            ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAiA, Matrix.one_mul, hRiR, Matrix.mul_one]

end Mat

section Perfect

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_mem_commutator_centT {T : GL (Fin 4) K}
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψT : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (T : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (↑T⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {X : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hXp : ⁅X, X⁆ = X)
    (hXψ : ∀ g : unitarySU p f K 4, (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K)) ∈ X →
      (QuotientGroup.mk (ψ g) : StatedProj (StatedSU 4 (p ^ f) K)) = QuotientGroup.mk g) :
    ∀ y ∈ X, ∃ g ∈ ⁅centT p f T, centT p f T⁆, (QuotientGroup.mk g :
      StatedProj (StatedSU 4 (p ^ f) K)) = y := by
  classical
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) := QuotientGroup.mk' (scal p f K)
    with hθ
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ center (unitarySU p f K 4) := by
    rw [hθ, QuotientGroup.ker_mk']
    intro z hz
    exact CatFactsL4U4.StabU.mem_center_of_mem_scal hz
  obtain ⟨hNp, hNmap⟩ := commutator_comap_perfect θ hθs hker hXp
  set N := X.comap θ with hN
  have hZc : StatedScalars (Fin 4) K ≤ center (GL (Fin 4) K) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_center_iff]
    intro g
    exact (GeneralLinearGroup.scalar_commute c g).symm
  have hmod : ∀ g ∈ N, (g : GL (Fin 4) K) * T * (g : GL (Fin 4) K)⁻¹ * T⁻¹ ∈
      StatedScalars (Fin 4) K := by
    intro g hg
    have h1 := hXψ g hg
    rw [QuotientGroup.eq] at h1
    obtain ⟨c, hc⟩ := CatFactsL4U4.StabU.val_of_mem_scal h1
    set gm : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      with hgm
    set Tm : Matrix (Fin 4) (Fin 4) K := (T : Matrix (Fin 4) (Fin 4) K) with hTm
    set Ti : Matrix (Fin 4) (Fin 4) K := (↑T⁻¹ : Matrix (Fin 4) (Fin 4) K) with hTi
    set gi : Matrix (Fin 4) (Fin 4) K := (↑(g : GL (Fin 4) K)⁻¹ : Matrix (Fin 4) (Fin 4) K)
      with hgi
    have hTTi : Tm * Ti = 1 := by rw [hTm, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hTiT : Ti * Tm = 1 := by rw [hTm, hTi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hggi : gm * gi = 1 := by rw [hgm, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e1 : gm = (c : K) • ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have e : ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((((ψ g)⁻¹ * g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = gm := by
        rw [hgm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [hc, Matrix.mul_smul, Matrix.mul_one] at e
      exact e.symm
    have hψm : ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Tm * gm * Ti := hψT g
    have e3 : gm * Tm = (c : K) • (Tm * gm) := by
      calc gm * Tm = ((c : K) • (Tm * gm * Ti)) * Tm := by rw [← hψm, ← e1]
        _ = (c : K) • (Tm * gm) := by
            rw [Matrix.smul_mul, Matrix.mul_assoc (Tm * gm), hTiT, Matrix.mul_one]
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_mul, Units.val_mul, Units.val_mul, ← hgm, ← hTm,
      ← hTi, ← hgi, e3, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Tm gm gi, hggi,
      Matrix.mul_one, hTTi, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hNC : ⁅N, N⁆ ≤ centT p f T := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [mem_centT]
    have := CatFactsL4U4.commutator_comm_of_comm_mod hZc (hmod g₁ hg₁) (hmod g₂ hg₂)
    have e : ((⁅g₁, g₂⁆ : unitarySU p f K 4) : GL (Fin 4) K) =
        ⁅(g₁ : GL (Fin 4) K), (g₂ : GL (Fin 4) K)⁆ := by
      simp [commutatorElement_def]
    rw [e]
    exact this
  intro y hy
  rw [← hNmap] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨g, ?_, rfl⟩
  rw [← hNp] at hg
  exact Subgroup.commutator_mono hNC hNC hg

end Perfect

variable {H : Type} [Group H]

theorem mem_centralizer_of_kernel {J : Subgroup H} (hJp : Group.IsPerfect J)
    (hcore : pPrimeCore 2 J = center J) {b : H} (hb : b ∈ coreActionKernel J) :
    ∀ j ∈ J, b * j = j * b := by
  classical
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hb
  have hcJ : ∀ j : J, ∃ z ∈ center J, (b⁻¹ * (j : H) * b : H) = ((j * z : J) : H) := by
    intro j
    have h1 := hbc j j.2
    rw [hcore] at h1
    obtain ⟨z, hz, hzj⟩ := h1
    refine ⟨z, hz, ?_⟩
    rw [Subgroup.coe_mul]
    change _ = (j : H) * (Subgroup.subtype J z)
    rw [hzj]
    group
  have hbJ : ∀ j : J, b⁻¹ * (j : H) * b ∈ J := by
    intro j
    obtain ⟨z, -, hz⟩ := hcJ j
    rw [hz]
    exact (j * z).2
  have hcomm : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ⁅j₁, j₂⁆ ∈ J ⊓ centralizer ({b} : Set H) := by
    intro j₁ hj₁ j₂ hj₂
    refine ⟨Subgroup.commutator_mem_commutator hj₁ hj₂ |> fun h' =>
      Subgroup.commutator_le_self J h', ?_⟩
    obtain ⟨z₁, hz₁, he₁⟩ := hcJ ⟨j₁, hj₁⟩
    obtain ⟨z₂, hz₂, he₂⟩ := hcJ ⟨j₂, hj₂⟩
    have hJc : ⁅(⟨j₁, hj₁⟩ : J) * z₁, (⟨j₂, hj₂⟩ : J) * z₂⁆ = ⁅(⟨j₁, hj₁⟩ : J), ⟨j₂, hj₂⟩⁆ :=
      commutatorElement_mul_central hz₁ hz₂
    have hJc' := congrArg (fun x : J => (x : H)) hJc
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at hJc'
    have he₁' : j₁ * (z₁ : H) = b⁻¹ * j₁ * b := by rw [he₁, Subgroup.coe_mul]
    have he₂' : j₂ * (z₂ : H) = b⁻¹ * j₂ * b := by rw [he₂, Subgroup.coe_mul]
    rw [he₁', he₂'] at hJc'
    show ⁅j₁, j₂⁆ ∈ centralizer ({b} : Set H)
    rw [mem_centralizer_singleton_iff]
    have e : b⁻¹ * ⁅j₁, j₂⁆ * b = ⁅b⁻¹ * j₁ * b, b⁻¹ * j₂ * b⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : b⁻¹ * ⁅j₁, j₂⁆ * b = ⁅j₁, j₂⁆ := by
      rw [e, commutatorElement_def, commutatorElement_def]
      exact hJc'
    refine (?_ : b * ⁅j₁, j₂⁆ = ⁅j₁, j₂⁆ * b).symm
    calc b * ⁅j₁, j₂⁆ = b * (b⁻¹ * ⁅j₁, j₂⁆ * b) := by rw [e2]
      _ = ⁅j₁, j₂⁆ * b := by group
  have hle : ⁅J, J⁆ ≤ J ⊓ centralizer ({b} : Set H) := by
    rw [Subgroup.commutator_le]
    exact hcomm
  have hJJ : ⁅J, J⁆ = J := Subgroup.commutator_eq_self (H := J)
  intro j hj
  rw [← hJJ] at hj
  have h1 : j ∈ centralizer ({b} : Set H) := (hle hj).2
  exact (mem_centralizer_singleton_iff.mp h1).symm

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
