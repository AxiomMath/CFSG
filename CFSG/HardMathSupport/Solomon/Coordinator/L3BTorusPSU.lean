module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def normOneUnits (h : UnitaryFieldData p f K) : Subgroup Kˣ where
  carrier := {c | h.norm (c : K) = 1}
  one_mem' := by simp [UnitaryFieldData.norm]
  mul_mem' := fun {a b} ha hb => by
    show h.norm ((a * b : Kˣ) : K) = 1
    rw [Units.val_mul, norm_mul_eq h]
    exact (congrArg₂ (· * ·) ha hb).trans (one_mul 1)
  inv_mem' := fun {a} ha => by
    show h.norm (((a⁻¹ : Kˣ)) : K) = 1
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h]
    exact (congrArg (·⁻¹) ha).trans inv_one

theorem mem_normOneUnits {h : UnitaryFieldData p f K} {c : Kˣ} :
    c ∈ normOneUnits h ↔ h.norm (c : K) = 1 := Iff.rfl

theorem diagHom_mem_unitaryIsom3 (h : UnitaryFieldData p f K) {d : Fin 3 → Kˣ}
    (hd : ∀ i, d i ∈ normOneUnits h) : diagHom 3 K d ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagHom, Matrix.diagonal_map (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := hd i
  rw [mem_normOneUnits, UnitaryFieldData.norm] at this
  simpa [mul_comm] using this

@[expose] noncomputable def torusSU (p f : ℕ) (H : Subgroup Kˣ) : Subgroup (unitarySU p f K 3) :=
  (diagTorus H).comap (unitarySU p f K 3).subtype

@[expose] noncomputable def torusPSU (h : UnitaryFieldData p f K) (H : Subgroup Kˣ) :
    Subgroup (unitaryPSU h 3) :=
  (torusSU p f H).map (unitaryProj h 3)

theorem mem_torusSU {H : Subgroup Kˣ} {g : unitarySU p f K 3} :
    g ∈ torusSU p f H ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ H) ∧ diagHom 3 K d = (g : GL (Fin 3) K) :=
  mem_diagTorus

theorem coprime_card_torusPSU (h : UnitaryFieldData p f K) {H : Subgroup Kˣ}
    (hH : H ≤ coprimeThreeTorsion Kˣ) : Nat.Coprime 3 (Nat.card (torusPSU h H)) := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, hg, hgx⟩ := x.2
  obtain ⟨N, hN, hgN⟩ := exists_pow_eq_one_of_mem_diagTorus hH hg
  have hgN' : g ^ N = 1 := Subtype.ext hgN
  have h1 : (x : unitaryPSU h 3) ^ N = 1 := by
    rw [← hgx, ← map_pow, hgN', map_one]
  have h2 : orderOf x ∣ N := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using h1)
  rw [hx] at h2
  exact absurd (Nat.Coprime.eq_one_of_dvd hN h2) (by norm_num)

theorem torusPSU_ne_bot (h : UnitaryFieldData p f K) {H : Subgroup Kˣ} (hHN : H ≤ normOneUnits h)
    (hH : ∃ a ∈ H, a ≠ 1) : torusPSU h H ≠ ⊥ := by
  obtain ⟨a, haH, ha1⟩ := hH
  let d : Fin 3 → Kˣ := ![a, a⁻¹, 1]
  have hd : ∀ i, d i ∈ H := by
    intro i
    fin_cases i
    · exact haH
    · exact H.inv_mem haH
    · exact H.one_mem
  have hdet : ((diagHom 3 K d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [d]
  let g : unitarySU p f K 3 :=
    ⟨diagHom 3 K d, (mem_unitarySU_iff h).2 ⟨hdet, diagHom_mem_unitaryIsom3 h fun i => hHN (hd i)⟩⟩
  have hg : g ∈ torusSU p f H := mem_torusSU.2 ⟨d, hd, rfl⟩
  intro hbot
  have hmem : unitaryProj h 3 g ∈ torusPSU h H := Subgroup.mem_map_of_mem _ hg
  rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_unitaryProj, mem_unitaryScalars] at hmem
  obtain ⟨c, -, -, hc⟩ := hmem
  have h0 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hc
  have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hc
  simp [g, d, coe_diagHom] at h0 h2
  exact ha1 (Units.ext (by rw [h0, ← h2]; rfl))

theorem map_psuConj_torusPSU_le (h : UnitaryFieldData p f K) (H : Subgroup Kˣ)
    {A : unitaryIsom3 h}
    (hA : (A : GL (Fin 3) K) ∈ Subgroup.normalizer (diagTorus H : Set (GL (Fin 3) K))) :
    (torusPSU h H).map (psuConj h A).toMonoidHom ≤ torusPSU h H := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨suConj h A g, ?_, (psuConj_mk A g).symm⟩
  show _ ∈ (diagTorus H).comap _
  rw [Subgroup.mem_comap]
  show ((suConj h A g : unitarySU p f K 3) : GL (Fin 3) K) ∈ diagTorus H
  rw [coe_suConj]
  exact (Subgroup.mem_normalizer_iff.1 hA _).1 (Subgroup.mem_comap.1 hg)

theorem glAut_diagHom (σ : K ≃+* K) (d : Fin 3 → Kˣ) :
    glAut σ (diagHom 3 K d) = diagHom 3 K (fun i => Units.map (σ : K →* K) (d i)) := by
  apply Units.ext
  rw [coe_glAut, coe_diagHom, coe_diagHom, Matrix.diagonal_map (map_zero σ)]
  rfl

theorem map_psuField_torusPSU_le (h : UnitaryFieldData p f K) (H : Subgroup Kˣ)
    (hH : ∀ σ : K ≃+* K, ∀ a ∈ H, Units.map (σ : K →* K) a ∈ H) (σ : K ≃+* K) :
    (torusPSU h H).map (psuField h σ).toMonoidHom ≤ torusPSU h H := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨suField h σ g, ?_, (psuField_mk σ g).symm⟩
  obtain ⟨d, hd, hgd⟩ := mem_torusSU.1 hg
  refine mem_torusSU.2 ⟨fun i => Units.map (σ : K →* K) (d i), fun i => hH σ _ (hd i), ?_⟩
  rw [coe_suField, ← hgd, glAut_diagHom]

theorem map_psuFieldRange_torusPSU [Finite K] (h : UnitaryFieldData p f K) (H : Subgroup Kˣ)
    (hH : ∀ σ : K ≃+* K, ∀ a ∈ H, Units.map (σ : K →* K) a ∈ H)
    {r : MulAut (unitaryPSU h 3)} (hr : r ∈ (psuField h).range) :
    (torusPSU h H).map r.toMonoidHom = torusPSU h H := by
  obtain ⟨σ, rfl⟩ := hr
  exact map_eq_of_map_le _ _ (map_psuField_torusPSU_le h H hH σ)

theorem monomialGroup_le_unitaryIsom3 (h : UnitaryFieldData p f K) :
    monomialGroup (normOneUnits h) ≤ unitaryIsom3 h := by
  refine sup_le ?_ ?_
  · intro A hA
    obtain ⟨d, hd, rfl⟩ := mem_diagTorus.1 hA
    exact diagHom_mem_unitaryIsom3 h hd
  · rintro _ ⟨σ, rfl⟩
    rw [mem_unitaryIsom3, coe_permGL]
    have hmap : (σ⁻¹.permMatrix K).map h.bar = σ⁻¹.permMatrix K := by
      ext i j
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [hmap, transpose_permMatrix, inv_inv, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]

theorem toLin_mem_sesqUnitaryGroup_iff (h : UnitaryFieldData p f K) (g : GL (Fin 3) K) :
    Matrix.GeneralLinearGroup.toLin g ∈
        sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)) ↔ g ∈ unitaryIsom3 h := by
  rw [mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
  simp only [Matrix.toLin'_apply]
  rw [gramForm_isometry_iff, Matrix.mul_one, mem_unitaryIsom3]

theorem card_unitaryIsom3_normOne (h : UnitaryFieldData p f K) :
    Nat.card (unitaryIsom3 h) =
        (p ^ f) ^ 3 * (p ^ f + 1) * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) ∧
      Nat.card (normOneUnits h) = p ^ f + 1 := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  obtain ⟨hU, -, hrange, hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)
  have hcardU : Nat.card (unitaryIsom3 h) =
      Nat.card (sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) K))) :=
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
      (toLin_mem_sesqUnitaryGroup_iff h g).symm)
  refine ⟨?_, ?_⟩
  · have hprod : ∏ i ∈ Finset.Icc 1 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
        (((p ^ f : ℕ) : ℤ) + 1) * ((((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1)) := by
      rw [show Finset.Icc 1 3 = {1, 2, 3} by rfl, Finset.prod_insert (by decide),
        Finset.prod_pair (by norm_num)]
      ring
    rw [hprod] at hU
    have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
    rw [hcardU]
    zify [hq2]
    rw [hU]
    norm_num
    ring
  · have hN : (CFSG.LinearGroups.unitaryDet
        (gramForm h (1 : Matrix (Fin 3) (Fin 3) K))).range = normOneUnits h := by
      ext c
      rw [hrange c]
      rfl
    rw [← hN]
    exact hcard

theorem units_map_mem_normOneUnits (h : UnitaryFieldData p f K) (σ : K ≃+* K) {a : Kˣ}
    (ha : a ∈ normOneUnits h) : Units.map (σ : K →* K) a ∈ normOneUnits h := by
  rw [mem_normOneUnits] at ha ⊢
  have : h.norm (σ (a : K)) = σ (h.norm (a : K)) := by
    simp only [UnitaryFieldData.norm, map_mul, map_bar_comm h σ]
  show h.norm (σ (a : K)) = 1
  rw [this, ha, map_one]

theorem fixedTorus_unitaryPSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (hq3 : p ^ f % 3 = 2) (hq8 : p ^ f ≠ 8) : FixedTorus (unitaryPSU h 3) := by
  have := h.finite
  have hH : ∀ σ : K ≃+* K, ∀ a ∈ normOneUnits h ⊓ coprimeThreeTorsion Kˣ,
      Units.map (σ : K →* K) a ∈ normOneUnits h ⊓ coprimeThreeTorsion Kˣ := by
    rintro σ a ⟨ha, n, hn, han⟩
    exact ⟨units_map_mem_normOneUnits h σ ha, n, hn, by rw [← map_pow, han, map_one]⟩
  obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_ne_three_dvd_succ h.prime hq3 (by omega) hq8
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := normOneUnits h) r
    (by rw [(card_unitaryIsom3_normOne h).2]; exact hrd)
  have hxr : (x : Kˣ) ^ r = 1 := by
    have := congrArg (fun y : normOneUnits h => (y : Kˣ)) (hx ▸ pow_orderOf_eq_one x)
    simpa using this
  have hx1 : (x : Kˣ) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact hr.one_lt.ne hx
  have hne : ∃ a ∈ normOneUnits h ⊓ coprimeThreeTorsion Kˣ, a ≠ 1 :=
    ⟨x, ⟨x.2, r, (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3), hxr⟩, hx1⟩
  refine fixedTorus_of_decomposition (psuConj h) (psuField h).range
    ((monomialGroup (normOneUnits h)).subgroupOf (unitaryIsom3 h))
    (torusPSU h (normOneUnits h ⊓ coprimeThreeTorsion Kˣ)) ?_ ?_ ?_ ?_
    (torusPSU_ne_bot h inf_le_left hne) (coprime_card_torusPSU h inf_le_right)
  · intro α
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    exact ⟨A, psuField h σ, ⟨σ, rfl⟩, rfl⟩
  · intro r hr
    exact map_psuFieldRange_torusPSU h _ hH hr
  · intro A hA
    exact map_eq_of_map_le _ _ (map_psuConj_torusPSU_le h _
      (monomialGroup_le_normalizer (normOneUnits h) _ (Subgroup.mem_subgroupOf.1 hA)))
  · have hle := monomialGroup_le_unitaryIsom3 h
    have hcard := Subgroup.card_mul_index
      ((monomialGroup (normOneUnits h)).subgroupOf (unitaryIsom3 h))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_monomialGroup,
      (card_unitaryIsom3_normOne h).2, (card_unitaryIsom3_normOne h).1] at hcard
    rw [mul_comm] at hcard
    exact not_dvd_index_gu _ _ hq3 (by omega) hcard

theorem fixedTorus_statedProj_su [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hq3 : q % 3 = 2) (hq2 : q ≠ 2) (hq8 : q ≠ 8) :
    FixedTorus (StatedProj (StatedSU 3 q K)) := by
  obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
  have hq : 2 < p ^ f := by
    have : 2 ≤ p ^ f := le_trans hF.prime.two_le (Nat.le_self_pow (by have := hF.one_le; omega) p)
    omega
  exact FixedTorus.of_mulEquiv (unitaryPSUEquiv hF (by norm_num)).symm
    (fixedTorus_unitaryPSU hF hq hq3 hq8)

end CFSG.HardMathSupport.Solomon.Coordinator
