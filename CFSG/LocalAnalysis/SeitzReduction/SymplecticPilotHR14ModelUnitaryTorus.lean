module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore perfectCore_mono)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (coords mem_coords)

section Two

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')

theorem bar_eq_of_unitary_two [CharP K' 2] {x y z w : K'}
    (E1 : h.bar x * z + h.bar z * x = 0) (E2 : h.bar x * w + h.bar z * y = 1)
    (E3 : h.bar y * z + h.bar w * x = 1) (E4 : h.bar y * w + h.bar w * y = 0)
    (D : x * w + y * z = 1) :
    h.bar x = x ∧ h.bar y = y ∧ h.bar z = z ∧ h.bar w = w := by
  have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-h.bar x) * D + x * E2 + y * E1 - x * y * h.bar z * h2
  · linear_combination (-h.bar y) * D + x * E4 + y * E3 - x * y * h.bar w * h2
  · linear_combination (-h.bar z) * D + z * E2 - w * E1 + w * x * h.bar z * h2
  · linear_combination (-h.bar w) * D + w * E3 + z * E4 - w * z * h.bar y * h2

end Two

section Block

variable {f : ℕ} {K' : Type} [Field K'] {h : UnitaryFieldData 2 f K'} {n : ℕ}

theorem det_two_of_finset {m : ℕ} {a b : Fin m} (hab : a ≠ b) (A : Matrix
    ({a, b} : Finset (Fin m)) ({a, b} : Finset (Fin m)) K') :
    A.det = A ⟨a, Finset.mem_insert_self _ _⟩ ⟨a, Finset.mem_insert_self _ _⟩ *
        A ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
          ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ -
      A ⟨a, Finset.mem_insert_self _ _⟩
          ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ *
        A ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
          ⟨a, Finset.mem_insert_self _ _⟩ := by
  set u : ({a, b} : Finset (Fin m)) := ⟨a, Finset.mem_insert_self _ _⟩ with hu
  set v : ({a, b} : Finset (Fin m)) :=
    ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ with hv
  have huv : u ≠ v := fun e => hab (congrArg Subtype.val e)
  have hbij : Function.Bijective (![u, v] : Fin 2 → ({a, b} : Finset (Fin m))) := ⟨by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm], by
      rintro ⟨c, hc⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨0, rfl⟩
      · rw [Finset.mem_singleton] at hc
        subst hc
        exact ⟨1, rfl⟩⟩
  rw [← det_submatrix_equiv_self (Equiv.ofBijective _ hbij) A, det_fin_two]
  simp only [submatrix_apply, Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

variable [CharP K' 2]

theorem map_bar_eq_of_mem_gramSU_block (last : Fin n) {C₀ : GL (Fin (2 * n)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    {g : GL (Fin (2 * n)) K'} (hg : g ∈ gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
    (hI : ∀ i j, (i ∉ spModelPlane n last ∨ j ∉ spModelPlane n last) →
      (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i j =
        (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i j) :
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K').map h.bar = g := by
  set a := spModelIdx n (Sum.inl last) with ha
  set b := spModelIdx n (Sum.inr last) with hb
  have hab : a ≠ b := fun e => Sum.inl_ne_inr ((spModelIdx n).injective e)
  have hg1 := hg.1
  have hg2 : (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K').det = 1 := hg.2
  rw [hC₀] at hg1
  generalize (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = G at hg1 hg2 hI ⊢
  have hJa : ∀ i, (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i a =
      if i = b then 1 else 0 := blockSwapJ_apply_inl (F := K') last
  have hJb : ∀ i, (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i b =
      if i = a then 1 else 0 := blockSwapJ_apply_inr (F := K') last
  have hmemI : ∀ {i}, i ∈ spModelPlane n last ↔ i = a ∨ i = b := by
    intro i
    simp [spModelPlane, ha, hb]
  have hcol : ∀ {q l}, (q = a ∨ q = b) → ¬(l = a ∨ l = b) → G l q = 0 := by
    intro q l hq hl
    rw [hI l q (Or.inl (fun h' => hl (hmemI.1 h'))), one_apply_ne]
    rintro rfl
    exact hl hq
  have hrel : ∀ p q, (q = a ∨ q = b) →
      h.bar (G b p) * G a q + h.bar (G a p) * G b q =
        (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') p q := by
    intro p q hq
    have h1 := congrFun (congrFun hg1 p) q
    rw [← h1, mul_apply, Fintype.sum_eq_add a b hab (fun l hl => by
      rw [hcol hq (by tauto), mul_zero])]
    have hA : (((G.map h.bar)ᵀ * (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K')) p a = h.bar (G b p) := by
      rw [mul_apply, Finset.sum_eq_single b (fun k _ hk => by simp [hJa k, hk])
        (by simp)]
      simp [hJa b]
    have hB : (((G.map h.bar)ᵀ * (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K')) p b = h.bar (G a p) := by
      rw [mul_apply, Finset.sum_eq_single a (fun k _ hk => by simp [hJb k, hk])
        (by simp)]
      simp [hJb a]
    rw [hA, hB]
  have hJaa : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') a a = 0 := by
    simp [hJa a, hab]
  have hJbb : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') b b = 0 := by
    simp [hJb b, Ne.symm hab]
  have hJab : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') a b = 1 := by
    simp [hJb a]
  have hJba : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) K') b a = 1 := by
    simp [hJa b]
  have R1 := hrel a a (Or.inl rfl)
  have R2 := hrel a b (Or.inr rfl)
  have R3 := hrel b a (Or.inl rfl)
  have R4 := hrel b b (Or.inr rfl)
  rw [hJaa] at R1
  rw [hJab] at R2
  rw [hJba] at R3
  rw [hJbb] at R4
  have hblock : G = LinearPilot.blockMatrix (spModelPlane n last)
      (Matrix.of fun i j : spModelPlane n last => G i j) := by
    ext i j
    refine Eq.symm ((LinearPilot.blockMatrix_apply _ _ i j).trans ?_)
    split_ifs with hij
    · rfl
    · exact (hI i j (not_and_or.1 hij)).symm
  have hdet : (Matrix.of fun i j : spModelPlane n last => G i j).det = 1 := by
    rw [← LinearPilot.det_blockMatrix, ← hblock]
    exact hg2
  have hD : G a a * G b b + G a b * G b a = 1 := by
    have h1 := det_two_of_finset (K' := K') hab (Matrix.of fun i j : spModelPlane n last => G i j)
    have h2 : (1 : K') = G a a * G b b - G a b * G b a := hdet.symm.trans h1
    linear_combination -h2 + G a b * G b a * (CharTwo.two_eq_zero (R := K'))
  obtain ⟨hx, hy, hz, hw⟩ := bar_eq_of_unitary_two h (x := G a a) (y := G a b) (z := G b a)
    (w := G b b) (by linear_combination R1) (by linear_combination R2)
    (by linear_combination R3) (by linear_combination R4) hD
  ext i j
  rw [Matrix.map_apply]
  by_cases hij : i ∈ spModelPlane n last ∧ j ∈ spModelPlane n last
  · rcases hmemI.1 hij.1 with rfl | rfl <;> rcases hmemI.1 hij.2 with rfl | rfl
    · exact hx
    · exact hy
    · exact hz
    · exact hw
  · rw [hI i j (not_and_or.1 hij), one_apply]
    split_ifs <;> simp

end Block

section Core

variable {f : ℕ} {K' : Type} [Field K'] {h : UnitaryFieldData 2 f K'} {n : ℕ}
  [CharP h.fixedField 2] {C₀ : GL (Fin (2 * n)) K'}

theorem perfectCore_centralizer_map_uModelP_le (hn : 1 ≤ n)
    {last : Fin n} (hlast : last.val + 1 = n) (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (T : Subgroup (StatedSp n h.fixedField)) (hT : T ≤ leviTorusSp h.fixedField {last})
    {κ : h.fixedFieldˣ} (hκ : κ ≠ 1)
    (hTκ : ∀ i : Fin n, i.val + 1 < n → diagSp h.fixedField n (Pi.mulSingle i κ) ∈ T) :
    perfectCore (centralizer ((T.map (uModelP h hC₀) :
        Subgroup (primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K'))) :
          Set (primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')))) ≤
      fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
  classical
  have : CharP K' 2 := h.charP
  have : Finite K' := h.finite
  have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  set S := gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') with hS
  set Φ : S →* primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') :=
    QuotientGroup.mk' (normOneScalars h S (2 * n)) with hΦ
  set Tp := T.map (uModelP h hC₀) with hTp
  have hlift : ∀ d : Tp, ∃ x ∈ T, uModelP h hC₀ x = (d : primeFormP h _) :=
    fun d => Subgroup.mem_map.1 d.2
  choose ℓx hℓxT hℓx using hlift
  set α : Tp → MulAut S := fun d => MulAut.conj (uModelSU h hC₀ (ℓx d)) with hα
  have hαp : ∀ (d : Tp) (x : S), Φ (α d x) = (d : primeFormP h _) * Φ x * (d : primeFormP h _)⁻¹ := by
    intro d x
    simp only [hα, MulAut.conj_apply, map_mul, map_inv]
    rw [← hℓx d]
    rfl
  have hker : Φ.ker ≤ center S := by
    rw [hΦ, QuotientGroup.ker_mk']
    exact normOneScalars_le_center h S (2 * n)
  have hh := LinearPilot.perfectCore_range_inf_centralizer Φ hker α hαp
  rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), top_inf_eq] at hh
  rw [hh]
  rintro _ ⟨g, hg, rfl⟩
  set ι := F4Pilot.gramSUToSL h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') with hι
  set D : Set (SpecialLinearGroup (Fin (2 * n)) K') :=
    Set.range fun d : Tp => ι (uModelSU h hC₀ (ℓx d)) with hD
  have hfixι : (LinearPilot.fixAll α).map ι ≤
      blockSpecialLinear (K := K') Finset.univ ⊓ centralizer D := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun i j hij => by simp at hij, ?_⟩
    change ι y ∈ centralizer D
    rw [mem_centralizer_iff]
    rintro _ ⟨d, rfl⟩
    have h1 := LinearPilot.mem_fixAll.1 hy d
    simp only [hα, MulAut.conj_apply] at h1
    rw [← map_mul, ← map_mul]
    congr 1
    calc uModelSU h hC₀ (ℓx d) * y = uModelSU h hC₀ (ℓx d) * y * (uModelSU h hC₀ (ℓx d))⁻¹ *
        uModelSU h hC₀ (ℓx d) := by group
      _ = y * uModelSU h hC₀ (ℓx d) := by rw [h1]
  have hdiagD : ∀ d ∈ D, ∀ i j, i ≠ j →
      ((d : SpecialLinearGroup (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i j = 0 := by
    rintro _ ⟨d, rfl⟩ i j hij
    obtain ⟨t, -, ht⟩ := hT (hℓxT d)
    change (((uModelSU h hC₀ (ℓx d) : S) : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K') i j = 0
    rw [coe_uModelSU, ← ht, coe_spModelSL_diagSp, Matrix.map_apply, diagonal_apply_ne _ hij,
      map_zero]
  have hentry : ∀ (x : StatedSp n h.fixedField) (t : Fin n → h.fixedFieldˣ),
      diagSp h.fixedField n t = x → ∀ i,
      (((uModelSU h hC₀ x : S) : GL (Fin (2 * n)) K') :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i =
          ((diagSpEntry t ((spModelIdx n).symm i) : h.fixedField) : K') := by
    intro x t hxt i
    rw [coe_uModelSU, ← hxt, coe_spModelSL_diagSp, Matrix.map_apply, diagonal_apply_eq]
    rfl
  have hconstD : ∀ d ∈ D, ∀ i ∈ spModelPlane n last, ∀ j ∈ spModelPlane n last,
      ((d : SpecialLinearGroup (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i =
        ((d : SpecialLinearGroup (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') j j := by
    rintro _ ⟨d, rfl⟩ i hi j hj
    obtain ⟨t, ht, htx⟩ := hT (hℓxT d)
    have htl : t last = 1 := (ht last (Finset.mem_singleton_self _)).2 hlast
    have hval : ∀ s ∈ coords last, diagSpEntry t s = 1 := by
      intro s hs
      rcases mem_coords.1 hs with rfl | rfl <;> simp [htl]
    change (((uModelSU h hC₀ (ℓx d) : S) : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i = (((uModelSU h hC₀ (ℓx d) : S) :
        GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') j j
    rw [hentry _ t htx, hentry _ t htx, hval _ (mem_spModelPlane.1 hi),
      hval _ (mem_spModelPlane.1 hj)]
  have hsepD : ∀ i ∈ (Finset.univ : Finset (Fin (2 * n))), ∀ j ∈ (Finset.univ : Finset (Fin (2 * n))),
      i ≠ j → (i ∉ spModelPlane n last ∨ j ∉ spModelPlane n last) →
        ∃ d ∈ D, ((d : SpecialLinearGroup (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i ≠
            ((d : SpecialLinearGroup (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') j j := by
    intro i _ j _ hij hI
    obtain ⟨i₀, hi₀, hne⟩ := exists_diagSpEntry_mulSingle_ne hκ hlast
      ((spModelIdx n).symm.injective.ne hij)
      (hI.imp (fun h' h'' => h' (mem_spModelPlane.2 h'')) (fun h' h'' => h' (mem_spModelPlane.2 h'')))
    set x₀ := diagSp h.fixedField n (Pi.mulSingle i₀ κ) with hx₀
    set d : Tp := ⟨uModelP h hC₀ x₀, mem_map_of_mem _ (hTκ i₀ hi₀)⟩ with hd
    have hxd : ℓx d = x₀ := uModelP_injective hn hC₀ (hℓx d)
    refine ⟨_, ⟨d, rfl⟩, ?_⟩
    change (((uModelSU h hC₀ (ℓx d) : S) : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K') i i ≠ (((uModelSU h hC₀ (ℓx d) : S) :
        GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') j j
    rw [hentry _ _ hxd.symm, hentry _ _ hxd.symm]
    exact fun h' => hne (Subtype.val_injective h')
  have hK'4 : 4 ≤ Nat.card K' := by
    rw [h.card]
    have := h.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLevi := LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (Finset.subset_univ (spModelPlane n last)) D hdiagD hconstD hsepD
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by rw [card_spModelPlane]) hK'4)
  have hgI : ι g ∈ blockSpecialLinear (K := K') (spModelPlane n last) := by
    rw [← hLevi]
    refine perfectCore_mono hfixι ?_
    rw [← map_perfectCore]
    exact ⟨g, hg, rfl⟩
  have hbar := map_bar_eq_of_mem_gramSU_block (h := h) last hC₀ g.2
    (fun i j hij => mem_blockSpecialLinear.1 hgI i j hij)
  change primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h) (QuotientGroup.mk g) =
    QuotientGroup.mk g
  rw [primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU]
  exact hbar

theorem perfectCore_centralizer_conj_torus_le_unitary {K : Type} [Field K] (hn : 2 ≤ n)
    (hq : ¬(2 * n = 3 ∧ 2 ^ f = 2)) {last : Fin n} (hlast : last.val + 1 = n)
    (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (σ : K ≃+* h.fixedField) {κ₀ : Kˣ} (hκ₀ : κ₀ ≠ 1) (u : StatedSp n K) :
    perfectCore (centralizer ((((leviTorusSp K {last}).map (MulAut.conj u).toMonoidHom).map
        ((uModelP h hC₀).comp (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n)) :
          Subgroup (primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K'))) :
            Set (primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')))) ≤
      (uModelP h hC₀).range := by
  have : Finite K' := h.finite
  have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  set ρ := (uModelP h hC₀).comp (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n) with hρ
  set T := leviTorusSp K ({last} : Finset (Fin n)) with hT
  have hY : (T.map (MulAut.conj u).toMonoidHom).map ρ =
      ((T.map (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n)).map (uModelP h hC₀)).map
        (MulAut.conj (ρ u)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp [hρ, MulAut.conj_apply]
  rw [hY, centralizer_map_mulEquiv_toMonoidHom (MulAut.conj (ρ u)), ← map_perfectCore]
  have hTF : T.map (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n) ≤
      leviTorusSp h.fixedField ({last} : Finset (Fin n)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact statedSpMap_mem_leviTorusSp' _ hx
  have hκ : Units.map ((σ : K →+* h.fixedField) : K →* h.fixedField) κ₀ ≠ 1 := by
    intro h1
    apply hκ₀
    apply Units.ext
    have h2 := congrArg (fun v : h.fixedFieldˣ => (v : h.fixedField)) h1
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_one] at h2
    apply σ.injective
    rw [Units.val_one, map_one]
    exact h2
  have hTκ : ∀ i : Fin n, i.val + 1 < n →
      diagSp h.fixedField n (Pi.mulSingle i (Units.map ((σ : K →+* h.fixedField) :
        K →* h.fixedField) κ₀)) ∈ T.map (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n) := by
    intro i hi
    refine ⟨diagSp K n (Pi.mulSingle i κ₀), ?_, statedSpMap_diagSp_mulSingle _ i κ₀⟩
    refine diagSp_mem_leviTorusSp fun j hj => ⟨fun h' => ?_, fun h' => ?_⟩
    · rw [Finset.mem_singleton] at hj
      rw [hj] at h'
      omega
    · rw [Finset.mem_singleton] at hj
      rw [hj]
      have hil : i ≠ last := fun e => by rw [e] at hi; omega
      simp [Ne.symm hil]
  have hcore := perfectCore_centralizer_map_uModelP_le (by omega) hlast hC hC₀ _ hTF hκ hTκ
  rw [← range_uModelP hn hq hC hC₀] at hcore
  rintro _ ⟨_, hx, rfl⟩
  obtain ⟨x, rfl⟩ := hcore hx
  refine ⟨F4Pilot.statedSpMap (σ : K →+* h.fixedField) n u * x *
    (F4Pilot.statedSpMap (σ : K →+* h.fixedField) n u)⁻¹, ?_⟩
  simp [hρ, MulAut.conj_apply]

end Core

end CFSG.SeitzReduction.SymplecticPilot
