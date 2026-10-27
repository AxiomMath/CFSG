module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Eigen
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix

private theorem kd26h_lin_dvd_card_SL {E : Type} [Field E] [Finite E] {p m : ℕ}
    (hm : 2 ≤ m) (hpE : p ∣ Nat.card E - 1) :
    p ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega)]
  have h2 : (2 : ℕ) ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨le_rfl, hm⟩
  exact Dvd.dvd.mul_left ((hpE.trans (Nat.sub_one_dvd_pow_sub_one _ 2)).trans
    (Finset.dvd_prod_of_mem (fun j => Nat.card E ^ j - 1) h2)) _

private theorem kd26h_lin_natCast_ne_zero {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) : (p : F) ≠ 0 := by
  intro h
  haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h
  letI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  rw [Nat.card_eq_fintype_card, hn] at hpF
  have h1 : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
  have h2 : 1 ≤ p ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
  have h3 : p ∣ p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) := Nat.dvd_sub h1 hpF
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem exists_block_linear {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF4 : 4 ≤ Nat.card F) (hpF : p ∣ Nat.card F - 1)
    (d : SpecialLinearGroup (Fin p) F) (c : Fˣ)
    (hd : (SpecialLinearGroup.toGL d) ^ p = GeneralLinearGroup.scalar (Fin p) c) (hc : c ≠ 1) :
    ∃ L : Subgroup (SpecialLinearGroup (Fin p) F),
      L ≤ Subgroup.centralizer ({d} : Set (SpecialLinearGroup (Fin p) F)) ∧
      CFSG.IsQuasisimple ↥L ∧
      (∀ g ∈ Subgroup.centralizer ({d} : Set (SpecialLinearGroup (Fin p) F)), ∀ f ∈ L,
        g * f * g⁻¹ ∈ L) ∧ p ∣ Nat.card L := by
  open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell in
  classical
  have hpF0 : (p : F) ≠ 0 := kd26h_lin_natCast_ne_zero hp hpF
  set y : GL (Fin p) F := SpecialLinearGroup.toGL d with hy
  have hx : Squarefree (minpoly F (linEnd y)) := squarefree_minpoly_linEnd_of_pow_scalar hpF0 c hd
  have hM : (y : Matrix (Fin p) (Fin p) F) ^ p = Matrix.scalar (Fin p) (c : F) := by
    have := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) hd
    simpa using this
  have hdet : (y : Matrix (Fin p) (Fin p) F).det = 1 := d.2
  have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨a, ha⟩ := exists_primaryMultiplicity_ge_two hp hp2 hM hdet hc1 hx
  have hq : CFSG.IsQuasisimple (blockImage hx a) := isQuasisimple_blockImage hx hF4 a ha
  have hle := blockImage_le_range_toGL hx hF4 a ha
  have hcen : blockImage hx a ≤ Subgroup.centralizer ({y} : Set (GL (Fin p) F)) :=
    (blockImage_le_range hx a).trans (range_commutantUnitsToGL_eq_centralizer y rfl).le
  set B := blockImage hx a
  let toGL : SpecialLinearGroup (Fin p) F →* GL (Fin p) F := SpecialLinearGroup.toGL
  have hinj : Function.Injective toGL := SpecialLinearGroup.toGL_injective
  let L : Subgroup (SpecialLinearGroup (Fin p) F) := B.comap toGL
  have hLB : L.map toGL = B := Subgroup.map_comap_eq_self hle
  have hBL : L ≃* B :=
    (Subgroup.equivMapOfInjective L toGL hinj).trans (MulEquiv.subgroupCongr hLB)
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hinj
    have h1 : toGL g * y = y * toGL g := Subgroup.mem_centralizer_singleton_iff.1 (hcen hg)
    rw [map_mul, map_mul]
    exact h1
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv hBL.symm hq
  · intro g hg f hf
    show toGL (g * f * g⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    refine conj_mem_blockImage hx a ?_ hf
    rw [range_commutantUnitsToGL_eq_centralizer y rfl, Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have h2 : toGL g * y = y * toGL g := by
      rw [hy, ← map_mul, ← map_mul, h1]
    exact h2
  · have hBB : B ≃* blockSL (Efac (linEnd y)) (mult (linEnd y)) a :=
      (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx)).symm
    have hSL : blockSL (Efac (linEnd y)) (mult (linEnd y)) a ≃*
        SpecialLinearGroup (Fin (mult (linEnd y) a)) (Efac (linEnd y) a) :=
      (MonoidHom.ofInjective (blockEmbed_injective a)).symm
    rw [Nat.card_congr (hBL.trans (hBB.trans hSL)).toEquiv]
    have hFin : Finite (Efac (linEnd y) a) := finite_efac a
    have hinjE : Function.Injective (Units.map (algebraMap F (Efac (linEnd y) a)).toMonoidHom) :=
      Units.map_injective (algebraMap F (Efac (linEnd y) a)).injective
    have hdvd := Subgroup.card_dvd_of_injective _ hinjE
    rw [Nat.card_units, Nat.card_units] at hdvd
    exact kd26h_lin_dvd_card_SL ha (hpF.trans hdvd)

end CFSG.LocalAnalysis.GLTheoremA
