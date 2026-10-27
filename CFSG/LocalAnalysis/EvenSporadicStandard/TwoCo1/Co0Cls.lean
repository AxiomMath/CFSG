module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Iface
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsK
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsOct
public import CFSG.Monster.Existence.Compat.Co1Iso

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.Existence.Compat
  CFSG.Monster.B.TwoA.Census CFSG.Blueprint.NativeSporadic

namespace Co0Cls

abbrev piOLq : latticeO →* OLq := QuotientGroup.mk' (Subgroup.zpowers negOneO)

theorem orderOf_negOneO : orderOf negOneO = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact negOneO_mul_self) negOneO_ne_one

theorem piOLq_eq_one_iff {g : latticeO} : piOLq g = 1 ↔ g = 1 ∨ g = negOneO := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff]

theorem finite_latticeO :
    Finite latticeO := by
  have h2 : Nat.card (Subgroup.zpowers negOneO) = 2 := by
    rw [Nat.card_zpowers, orderOf_negOneO]
  refine Nat.finite_of_card_ne_zero ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers negOneO), h2,
    show Nat.card (latticeO ⧸ Subgroup.zpowers negOneO) = 4157776806543360000 from natCard_OLq]
  norm_num

theorem card_centralizer_O_of_fused
    {y c : latticeO} (hc : c * y * c⁻¹ = negOneO * y) :
    Nat.card (Subgroup.centralizer ({y} : Set latticeO)) =
      Nat.card (Subgroup.centralizer ({piOLq y} : Set OLq)) := by
  have := finite_latticeO
  exact card_centralizer_eq_of_fused piOLq (QuotientGroup.mk'_surjective _) negOneO
    (QuotientGroup.ker_mk' _) negOneO_mem_center orderOf_negOneO hc

theorem card_centralizer_O_of_not_fused
    {y : latticeO}
    (h : ∀ c : latticeO, c * y * c⁻¹ ≠ negOneO * y) :
    Nat.card (Subgroup.centralizer ({y} : Set latticeO)) =
      2 * Nat.card (Subgroup.centralizer ({piOLq y} : Set OLq)) := by
  have := finite_latticeO
  exact card_centralizer_eq_two_mul_of_not_fused piOLq (QuotientGroup.mk'_surjective _) negOneO
    (QuotientGroup.ker_mk' _) negOneO_mem_center orderOf_negOneO h

theorem orderOf_piOLq {y : latticeO} (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyn : y ≠ negOneO) :
    orderOf (piOLq y) = 2 :=
  orderOf_eq_prime (by rw [pow_two, ← map_mul, hy2, map_one])
    (fun h => (piOLq_eq_one_iff.1 h).elim hy1 hyn)

theorem isSporadic_OLq :
    IsSporadic OLq .Co1 :=
  ⟨monsterCo1EquivOLq.trans co1EquivMonsterCo1.symm⟩

theorem card_centralizer_O_cases
    {y : latticeO} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyn : y ≠ negOneO) :
    ∃ M : ℕ, (M = 89181388800 ∨ M = 389283840 ∨ M = 2012774400) ∧
      ((∃ c : latticeO, c * y * c⁻¹ = negOneO * y) ∧
          Nat.card (Subgroup.centralizer ({y} : Set latticeO)) = M ∨
        (∀ c : latticeO, c * y * c⁻¹ ≠ negOneO * y) ∧
          Nat.card (Subgroup.centralizer ({y} : Set latticeO)) = 2 * M) := by
  have hM := card_centralizer_involution_of_isSporadic_co1 isSporadic_OLq
    (orderOf_piOLq hy2 hy1 hyn)
  refine ⟨Nat.card (Subgroup.centralizer ({piOLq y} : Set OLq)), hM, ?_⟩
  by_cases hf : ∃ c : latticeO, c * y * c⁻¹ = negOneO * y
  · obtain ⟨c, hc⟩ := hf
    exact Or.inl ⟨⟨c, hc⟩, card_centralizer_O_of_fused hc⟩
  · exact Or.inr ⟨fun c hc => hf ⟨c, hc⟩,
      card_centralizer_O_of_not_fused fun c hc => hf ⟨c, hc⟩⟩

theorem monoAO_one :
    monoAO 1 = gO oct₁ := by
  have h : (⟨monoWord 1, monoWord_mem 1⟩ : C) = oct₁ := Subtype.ext rfl
  rw [monoAO, h]
  show gO oct₁ * PO (seedAut 0) = gO oct₁
  rw [seedAut_zero, PO_one, mul_one]

theorem monoAO_two :
    monoAO 2 = gO dod₂ := by
  have h : (⟨monoWord 2, monoWord_mem 2⟩ : C) = dod₂ := Subtype.ext rfl
  rw [monoAO, h]
  show gO dod₂ * PO (seedAut 0) = gO dod₂
  rw [seedAut_zero, PO_one, mul_one]

theorem monoAO_six_mul_self :
    monoAO 6 * monoAO 6 = negOneO := by
  apply mat_injective
  rw [mat_mul, mat_monoAO, mat_negOneO, monoA_eq]
  exact monoA_sq_check.2.2

theorem negOneO_mul_mul_self (x : latticeO) : negOneO * x * (negOneO * x) = x * x := by
  apply mat_injective
  simp only [mat_mul, mat_negOneO, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, neg_neg]

theorem conj_mul_self_of_mul_self_eq {k x : latticeO} (h : x * x = negOneO) :
    (k⁻¹ * x * k) * (k⁻¹ * x * k) = negOneO := by
  calc (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
    _ = negOneO := by rw [h, ← negOneO_mul_comm k⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_conj_monoAO
    {y : latticeO}
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyn : y ≠ negOneO) :
    ∃ c : latticeO, ∃ i ∈ ({1, 2} : Finset ℕ),
      y = c * monoAO i * c⁻¹ ∨ y = negOneO * (c * monoAO i * c⁻¹) := by
  have hu : modTwoUnit y ∈ OLvis := modTwoUnit_mem_OLvis y
  have huu : modTwoUnit y * modTwoUnit y = 1 := by
    rw [← modTwoUnit_mul, hy2, modTwoUnit_one]
  have hu1 : modTwoUnit y ≠ 1 := fun h => ((modTwoUnit_eq_one_iff y).1 h).elim hy1 hyn
  obtain ⟨i, hi, g, hg, hgi⟩ := exists_conj_three hu huu hu1
  obtain ⟨k, rfl⟩ := mem_OLvis.1 hg
  have e : modTwoUnit y = modTwoUnit (k⁻¹ * monoAO i * k) := by
    rw [modTwoUnit_mul, modTwoUnit_mul, modTwoUnit_inv, ← monoN, ← hgi]
    group
  have hy := (modTwoUnit_eq_modTwoUnit_iff y _).1 e
  have h6 : i ≠ 6 := by
    rintro rfl
    have hx := conj_mul_self_of_mul_self_eq (k := k) monoAO_six_mul_self
    refine negOneO_ne_one ?_
    rcases hy with h | h
    · rw [← hx, ← h, hy2]
    · rw [← hx, ← negOneO_mul_mul_self, ← h, hy2]
  refine ⟨k⁻¹, i, ?_, by rwa [inv_inv]⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
  omega

theorem gO_ne_one_of_ne {a : C} (h : a ≠ 0) : gO a ≠ 1 := fun h1 =>
  h (gO_injective (h1.trans gO_zero.symm))

theorem gO_ne_negOneO_of_ne {a : C} (h : a ≠ ΩC) : gO a ≠ negOneO := fun h1 =>
  h (gO_injective (h1.trans gO_ΩC.symm))

theorem oct₁_ne_zero : oct₁ ≠ 0 := fun h => by
  have := hammingNorm_oct₁
  rw [show (oct₁ : Fin 24 → ZMod 2) = 0 from congrArg Subtype.val h] at this
  simp at this

theorem oct₁_ne_ΩC : oct₁ ≠ ΩC := fun h => by
  have := congrArg (fun a : C => hammingNorm (a : Fin 24 → ZMod 2)) h
  simp only [hammingNorm_oct₁] at this
  revert this
  decide

theorem dod₂_ne_zero : dod₂ ≠ 0 := fun h => by
  have := hammingNorm_dod₂
  rw [show (dod₂ : Fin 24 → ZMod 2) = 0 from congrArg Subtype.val h] at this
  simp at this

theorem dod₂_ne_ΩC : dod₂ ≠ ΩC := fun h => by
  have := congrArg (fun a : C => hammingNorm (a : Fin 24 → ZMod 2)) h
  simp only [hammingNorm_dod₂] at this
  revert this
  decide

theorem card_centralizer_gO_oct :
    Nat.card (Subgroup.centralizer {gO oct₁}) = co0C2 := by
  obtain ⟨M, hM, h⟩ := card_centralizer_O_cases (gO_mul_self oct₁) (gO_ne_one_of_ne oct₁_ne_zero)
    (gO_ne_negOneO_of_ne oct₁_ne_ΩC)
  have h22 := two_pow_dvd_card_centralizer_oct
  unfold co0C2
  rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
  · rw [h1] at h22
    exfalso
    rcases hM with rfl | rfl | rfl <;> omega
  · rw [h1] at h22 ⊢
    rcases hM with rfl | rfl | rfl <;> omega

def tAut : AutPerm := ⟨tEl, tEl_mem⟩

def sAut : AutPerm := ⟨sigEl, sigEl_mem⟩

theorem permC_tAut_dod₂ : permC tAut dod₂ = dod₂ := Subtype.ext permWord_tEl_dod₂

theorem permC_sAut_dod₂ : permC sAut dod₂ = dod₂ + ΩC := Subtype.ext permWord_sigEl_dod₂

theorem tAut_pow_eleven : tAut ^ 11 = 1 := Subtype.ext tEl_pow_eleven

theorem orderOf_PO_tAut : orderOf (PO tAut) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun h => ?_
  · have e : PO tAut = permOHom tAut⁻¹ := by rw [permOHom_apply, inv_inv]
    rw [e, ← map_pow, inv_pow, tAut_pow_eleven, inv_one, map_one]
  · have h' := (gO_mul_PO_inj (a := 0) (b := 0) (p := tAut) (q := 1)
      (by rw [gO_zero, one_mul, one_mul, PO_one]; exact h)).2
    exact tEl_ne_one (congrArg Subtype.val h')

theorem PO_tAut_mem_centralizer : PO tAut ∈ Subgroup.centralizer {gO dod₂} := by
  have h := (mul_PO_mem_centralizer_gO_iff 0 tAut dod₂).2 permC_tAut_dod₂
  rwa [gO_zero, one_mul] at h

theorem eleven_dvd_card_centralizer_dod : 11 ∣ Nat.card (Subgroup.centralizer {gO dod₂}) := by
  rw [← orderOf_PO_tAut]
  exact Subgroup.orderOf_dvd_natCard _ PO_tAut_mem_centralizer

theorem symm_permC_sAut_dod₂ : (permC sAut).symm dod₂ = dod₂ + ΩC := by
  rw [LinearEquiv.symm_apply_eq, map_add, permC_sAut_dod₂, VisQuot.permC_ΩC, add_assoc,
    ZModModule.add_self, add_zero]

theorem fused_gO_dod₂ : ∃ c : latticeO, c * gO dod₂ * c⁻¹ = negOneO * gO dod₂ := by
  refine ⟨PO sAut, ?_⟩
  rw [PO_mul_gO', symm_permC_sAut_dod₂, gO_add, gO_ΩC, negOneO_mul_comm]

theorem card_centralizer_gO_dod :
    Nat.card (Subgroup.centralizer {gO dod₂}) = co0C3 := by
  obtain ⟨M, hM, h⟩ := card_centralizer_O_cases (gO_mul_self dod₂) (gO_ne_one_of_ne dod₂_ne_zero)
    (gO_ne_negOneO_of_ne dod₂_ne_ΩC)
  have h11 := eleven_dvd_card_centralizer_dod
  unfold co0C3
  rcases h with ⟨-, h1⟩ | ⟨hnf, -⟩
  · rw [h1] at h11 ⊢
    rcases hM with rfl | rfl | rfl <;> omega
  · obtain ⟨c, hc⟩ := fused_gO_dod₂
    exact absurd hc (hnf c)

theorem centralizer_negOneO_mul (x : latticeO) :
    Subgroup.centralizer ({negOneO * x} : Set latticeO) = Subgroup.centralizer {x} := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have h1 : z * (negOneO * x) = negOneO * (z * x) := by
    rw [← mul_assoc, ← negOneO_mul_comm z, mul_assoc]
  rw [h1, mul_assoc, mul_right_inj]

end Co0Cls

open Co0Cls

theorem co0ClassData :
    Co0ClassData where
  involution_classes y hy2 hy1 hyn := by
    obtain ⟨c, i, hi, h⟩ := exists_conj_monoAO hy2 hy1 hyn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨c, oct₁, Set.mem_insert _ _, by rwa [monoAO_one] at h⟩
    · exact ⟨c, dod₂, Set.mem_insert_of_mem _ (Set.mem_singleton _), by rwa [monoAO_two] at h⟩
  card_cent_oct := card_centralizer_gO_oct
  card_cent_dod := card_centralizer_gO_dod

theorem lat_classify :
    ∀ y ∈ (⊤ : Subgroup latticeO), orderOf y = 2 → y ≠ negOneO →
      Nat.card (centIn (⊤ : Subgroup latticeO) y) = co0C2 ∨
        Nat.card (centIn (⊤ : Subgroup latticeO) y) = co0C3 := by
  intro y _ hy2 hyn
  have hyy : y * y = 1 := by
    rw [← pow_two, ← hy2]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy2
    omega
  have hcl := co0ClassData
  obtain ⟨c, d, hd, h⟩ := hcl.involution_classes y hyy hy1 hyn
  have hy : Nat.card (centIn (⊤ : Subgroup latticeO) y) =
      Nat.card (Subgroup.centralizer ({gO d} : Set latticeO)) := by
    rw [centIn, top_inf_eq]
    rcases h with h | h
    · rw [h]
      exact (card_centralizer_eq_of_isConj (isConj_iff.2 ⟨c, rfl⟩)).symm
    · rw [h, centralizer_negOneO_mul]
      exact (card_centralizer_eq_of_isConj (isConj_iff.2 ⟨c, rfl⟩)).symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (hy.trans hcl.card_cent_oct)
  · exact Or.inr (hy.trans hcl.card_cent_dod)

end CFSG.EvenSporadicStandard.TwoCo1
