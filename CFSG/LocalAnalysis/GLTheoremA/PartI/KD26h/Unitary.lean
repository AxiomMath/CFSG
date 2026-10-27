module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Eigen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBlockOrder
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem kd26h_uni_dvd_sq_sub_one {p q k : ℕ} (hpq : p ∣ q + 1) :
    (p : ℤ) ∣ ((q ^ k : ℕ) : ℤ) ^ 2 - 1 := by
  have e : ((q ^ k : ℕ) : ℤ) ^ 2 - 1 = ((q : ℤ) ^ 2) ^ k - 1 := by push_cast; ring
  have h3 : ((q : ℤ) ^ 2 - 1) ∣ ((q : ℤ) ^ 2) ^ k - 1 := by
    simpa using sub_dvd_pow_sub_pow ((q : ℤ) ^ 2) 1 k
  have h4 : (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 := by
    have : (q : ℤ) ^ 2 - 1 = ((q : ℤ) - 1) * ((q : ℤ) + 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left (by exact_mod_cast hpq) _
  rw [e]
  exact h4.trans h3

section Block

variable {ℓ f n p : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

private theorem kd26h_uni_dvd_card_block (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    {y : primeFormUnitary h (idGram F n)}
    (hx : Squarefree (minpoly F ((toLinU h n y : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F))))
    (a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)))
    (ha : IsGoodBlock h (toLinU h n y) a) :
    p ∣ Nat.card (specialBlock (idForm h n) (toLinU h n y) (a : F[X])) := by
  have := h.finite
  have HU := primaryData_toLinU y hx
  by_cases hself : dualPoly h.bar (a : F[X]) = a
  · refine dvd_card_specialBlock_selfDual HU a hself le_rfl ha.1 ?_
    simpa using kd26h_uni_dvd_sq_sub_one (k := (a : F[X]).natDegree) hpq
  · refine dvd_card_specialBlock_paired a (pairedPrimaryBlock HU a (Ne.symm hself)) ha.1 hp ?_
    have : Fact (Irreducible (a : F[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    have hE : Nat.card (AdjoinRoot (a : F[X])) =
        ((ℓ ^ f) ^ (a : F[X]).natDegree) ^ 2 := by
      rw [natCard_adjoinRoot h, ← pow_mul, ← pow_mul]
      ring_nf
    rw [hE]
    have h1 : 1 ≤ ((ℓ ^ f) ^ (a : F[X]).natDegree) ^ 2 :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ (pow_ne_zero _ h.prime.ne_zero)))
    have h2 : (p : ℤ) ∣ ((((ℓ ^ f) ^ (a : F[X]).natDegree) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      simpa using kd26h_uni_dvd_sq_sub_one (k := (a : F[X]).natDegree) hpq
    exact Int.natCast_dvd_natCast.mp h2

open scoped Classical in
private theorem kd26h_uni_main (h : UnitaryFieldData ℓ f F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hq4 : 4 ≤ ℓ ^ f)
    (d : ↥(gramSU h (idGram F p))) (c : Fˣ)
    (hd : ((d : GL (Fin p) F)) ^ p = GeneralLinearGroup.scalar (Fin p) c) (hc : c ≠ 1) :
    ∃ L : Subgroup ↥(gramSU h (idGram F p)),
      L ≤ Subgroup.centralizer ({d} : Set ↥(gramSU h (idGram F p))) ∧ CFSG.IsQuasisimple ↥L ∧
      (∀ g ∈ Subgroup.centralizer ({d} : Set ↥(gramSU h (idGram F p))), ∀ f ∈ L,
        g * f * g⁻¹ ∈ L) ∧ p ∣ Nat.card L := by
  have hℓ := h.prime
  have : Finite F := h.finite
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hpF : (p : F) ≠ 0 := cast_ne_zero_of_ne_char h hp hpℓ
  set y : primeFormUnitary h (idGram F p) := ⟨(d : GL (Fin p) F), d.2.1⟩
  have hyp : (y : GL (Fin p) F) ^ p = GeneralLinearGroup.scalar (Fin p) c := hd
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y hpF hyp
  have hX : ((toLinU h p y : LinearMap.GeneralLinearGroup F (Fin p → F)) :
      Module.End F (Fin p → F)) = Matrix.toLin' ((y : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) :=
    (Matrix.toLin'_apply' _).symm
  have hM : ((y : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ^ p =
      Matrix.scalar (Fin p) (c : F) := by
    have h1 : (((y : GL (Fin p) F) ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        ((y : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hyp, GeneralLinearGroup.coe_scalar]
  have hdet : ((y : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).det = 1 := d.2.2
  have hex : ∃ a : primaryFactors ((toLinU h p y : LinearMap.GeneralLinearGroup F (Fin p → F)) :
      Module.End F (Fin p → F)), 2 ≤ primaryMultiplicity
        ((toLinU h p y : LinearMap.GeneralLinearGroup F (Fin p → F)) : Module.End F (Fin p → F))
        (a : F[X]) := by
    rw [hX]
    exact exists_primaryMultiplicity_ge_two hp hp2 hM hdet (fun h1 => hc (Units.ext h1))
      (hX ▸ hx)
  obtain ⟨a, ha2⟩ := hex
  have ha : IsGoodBlock h (toLinU h p y) a :=
    isGoodBlock_of_numeric a ha2 (fun _ => hq4) (fun _ => by omega)
  have HU := primaryData_toLinU y hx
  have hF := specialBlockFacts_of_good HU (two_le_pow h) a ha
  set Q := specialBlock (idForm h p) (toLinU h p y) (a : F[X])
  have hQc : Q ≤ unitaryCentralizer (idForm h p) (toLinU h p y) :=
    specialBlock_le_unitaryCentralizer
  have hQd : ∀ g ∈ Q, LinearMap.det (g : Module.End F (Fin p → F)) = 1 := hF.detK
  have hQq : CFSG.IsQuasisimple ↥Q := hF.quasisimple ha.1
  have hQp : p ∣ Nat.card Q := kd26h_uni_dvd_card_block hp hpq hx a ha
  have hrange : Q ≤ (phiS h (n := p)).range := by
    intro g hg
    exact mem_range_phiS (mem_sesqSpecialUnitaryGroup.mpr
      ⟨(mem_unitaryCentralizer.mp (hQc hg)).1, hQd g hg⟩)
  set Bq : Subgroup ↥(gramSU h (idGram F p)) := Q.comap (phiS h)
  have hmap : Bq.map (phiS h) = Q := Subgroup.map_comap_eq_self hrange
  have e : ↥Bq ≃* ↥Q := (Subgroup.equivMapOfInjective Bq (phiS h) phiS_injective).trans
    (MulEquiv.subgroupCongr hmap)
  refine ⟨Bq, ?_, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQq, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (mem_unitaryCentralizer.mp (hQc (show phiS h g ∈ Q from hg))).2
    have hc' : (g : GL (Fin p) F) * (y : GL (Fin p) F) =
        (y : GL (Fin p) F) * (g : GL (Fin p) F) := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      exact Units.ext hcomm.eq
    exact Subtype.ext hc'
  · intro g hg f hf
    show phiS h (g * f * g⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    refine conj_mem_specialBlock ?_ hf
    rw [mem_unitaryCentralizer]
    refine ⟨phiS_mem_unitary g, ?_⟩
    have h1 : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have h2 : phiS h g * phiS h d = phiS h d * phiS h g := by rw [← map_mul, ← map_mul, h1]
    have h3 : toLinU h p y = phiS h d := rfl
    rw [h3]
    exact congrArg (fun u : LinearMap.GeneralLinearGroup F (Fin p → F) =>
      (u : Module.End F (Fin p → F))) h2
  · rw [Nat.card_congr e.toEquiv]
    exact hQp

end Block

theorem exists_block_unitary {ℓ f : ℕ} {F : Type} [Field F]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hq4 : 4 ≤ ℓ ^ f)
    (d : ↥(StatedSU p (ℓ ^ f) F)) (c : Fˣ)
    (hd : ((d : GL (Fin p) F)) ^ p = GeneralLinearGroup.scalar (Fin p) c) (hc : c ≠ 1) :
    ∃ L : Subgroup ↥(StatedSU p (ℓ ^ f) F),
      L ≤ Subgroup.centralizer ({d} : Set ↥(StatedSU p (ℓ ^ f) F)) ∧ CFSG.IsQuasisimple ↥L ∧
      (∀ g ∈ Subgroup.centralizer ({d} : Set ↥(StatedSU p (ℓ ^ f) F)), ∀ f ∈ L,
        g * f * g⁻¹ ∈ L) ∧ p ∣ Nat.card L := by
  have key : ∀ S : Subgroup (GL (Fin p) F), S = gramSU h (idGram F p) → ∀ d : ↥S,
      ((d : GL (Fin p) F)) ^ p = GeneralLinearGroup.scalar (Fin p) c →
      ∃ L : Subgroup ↥S, L ≤ Subgroup.centralizer ({d} : Set ↥S) ∧ CFSG.IsQuasisimple ↥L ∧
        (∀ g ∈ Subgroup.centralizer ({d} : Set ↥S), ∀ f ∈ L, g * f * g⁻¹ ∈ L) ∧
        p ∣ Nat.card L := by
    intro S hS
    subst hS
    intro d hd
    exact kd26h_uni_main h hp hp2 hpq hq4 d c hd hc
  exact key _ (unitarySU_eq_gramSU h p) d hd

end CFSG.LocalAnalysis.GLTheoremA
