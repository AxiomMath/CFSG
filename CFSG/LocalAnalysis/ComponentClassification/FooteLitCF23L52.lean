module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23L4
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix Assembly.LowTwoRank LocalAnalysis.ComponentInitial.LinearFlag
open LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open scoped commutatorElement

@[expose] def l52MA : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

@[expose] def l52MB : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def l52MH : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 1, 1, 1, 0, 1; 0, 0, 0, 1, 1; 1, 0, 1, 0, 1]

@[expose] def l52MHi : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 0, 1, 0, 1; 0, 1, 0, 1, 0; 1, 1, 1, 0, 1; 1, 1, 1, 1, 1]

@[expose] def l52A : GL (Fin 5) (ZMod 2) := ⟨l52MA, l52MA, by decide, by decide⟩

@[expose] def l52B : GL (Fin 5) (ZMod 2) := ⟨l52MB, l52MB, by decide, by decide⟩

@[expose] def l52H : GL (Fin 5) (ZMod 2) := ⟨l52MH, l52MHi, by decide, by decide⟩

theorem l52_mat_facts : l52MAᵀ * l52MA = 1 ∧ l52MBᵀ * l52MB = 1 ∧
    l52MHi * l52MHiᵀ = l52MA * l52MB * l52MA * l52MB ∧
    (l52MB * l52MA * l52MB * l52MA)ᵀ = l52MA * l52MB * l52MA * l52MB ∧
    l52MA * l52MB * l52MA * l52MB * (l52MA * l52MB * l52MA * l52MB) = 1 ∧
    l52MA * l52MB * l52MA * l52MB ≠ 1 := by
  decide

theorem coe_l52_comm : ((⁅l52A, l52B⁆ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
    l52MA * l52MB * l52MA * l52MB := by
  rw [commutatorElement_def]
  rfl

theorem coe_l52_comm_inv :
    (((⁅l52A, l52B⁆)⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      l52MB * l52MA * l52MB * l52MA := by
  rw [commutatorElement_inv, commutatorElement_def]
  rfl

theorem l52_facts :
    (l52A : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ * (l52A : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 ∧
    (l52B : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ * (l52B : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 ∧
    l52H⁻¹ * GeneralLinearGroup.inverseTranspose l52H = ⁅l52A, l52B⁆ ∧
    GeneralLinearGroup.inverseTranspose ⁅l52A, l52B⁆ = ⁅l52A, l52B⁆ ∧
    ⁅l52A, l52B⁆ ^ 2 = 1 ∧ ⁅l52A, l52B⁆ ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := l52_mat_facts
  refine ⟨h1, h2, Units.ext ?_, Units.ext ?_, Units.ext ?_, fun h => h6 ?_⟩
  · rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, coe_l52_comm, ← h3]
    rfl
  · rw [GeneralLinearGroup.coe_inverseTranspose, coe_l52_comm_inv, coe_l52_comm, h4]
  · rw [pow_two, Units.val_mul, coe_l52_comm, h5, Units.val_one]
  · rw [← coe_l52_comm, h, Units.val_one]

theorem map_mem_matrixIsometryGroup_one {K : Type} [Field K] [CharP K 2]
    {g : GL (Fin 5) (ZMod 2)}
    (hg : (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ * (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1) :
    GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K) g ∈
      matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
  show ((GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K) g : Matrix (Fin 5) (Fin 5) K))ᵀ *
    ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      (GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K) g : Matrix (Fin 5) (Fin 5) K) =
    ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  rw [Units.val_one, mul_one]
  have e : ∀ x : GL (Fin 5) (ZMod 2),
      (GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) K) x : Matrix (Fin 5) (Fin 5) K) =
        (x : Matrix (Fin 5) (Fin 5) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) := fun _ => rfl
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_castHom_injective {K : Type} [Field K] [CharP K 2] :
    Function.Injective (GeneralLinearGroup.map (n := Fin 5) (ZMod.castHom (dvd_refl 2) K)) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : GL (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K)) hxy
  exact Matrix.map_injective (ZMod.castHom (dvd_refl 2) K).injective h

theorem card_of_lieModel_L52 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSL 5 2 1) :
    Nat.card Y = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two (h.statedClassicalModel (by decide))

theorem isEmpty_alt_of_card_L52 {Y : Type} [Group Y] (hY : Nat.card Y = 9999360) (m : ℕ)
    (hm : 5 ≤ m) : IsEmpty (Y ≃* alternatingGroup (Fin m)) := by
  refine ⟨fun e => ?_⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 := two_mul_card_alternatingGroup (α := Fin m)
  rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr e.toEquiv, hY] at h1
  rcases Nat.lt_or_ge m 11 with h11 | h11
  · have := Nat.factorial_le (Nat.le_of_lt_succ h11)
    rw [← h1] at this
    exact absurd this (by decide)
  · have := Nat.factorial_le h11
    rw [← h1] at this
    exact absurd this (by decide)

theorem eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) {x : K} (hx : x ≠ 0) :
    x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h

theorem l52 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 5 2 1 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := RestrictedStd.statedClassicalModel_of_lieModel_PSL hY
  have hK2 : Nat.card K = 2 := by rw [hK]; rfl
  have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hK
  let φ' : ↥N ≃* projectiveSL 5 K := φ.trans (SymmetricLocal.statedProjEquivProjectiveSL 5 K)
  have : IsSimpleGroup (projectiveSL 5 K) :=
    OutcomeLocal.isSimpleGroup_projectiveSL (k := K) (by norm_num)
  have hs : IsSimpleGroup ↥N := φ'.isSimpleGroup
  have hnab : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ :=
      exists_ne_comm_of_center_eq_bot (OddSelector.center_projectiveSL_eq_bot (k := K)
        (by norm_num : 3 ≤ 5))
    exact ⟨φ'.symm a, φ'.symm b, fun h => hab (by simpa using congrArg φ' h)⟩
  have hJc : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  have hWalt := isEmpty_alt_of_card_L52 (card_of_lieModel_L52 hY)
  obtain ⟨p', f', hp', hp'2, hf', hsrc⟩ : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 p f ∨
        Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2) := by
    rcases hsmall with ⟨p', f', hp', hp'2, hf', -, hm'⟩ | h7
    · exact ⟨p', f', hp', hp'2, hf',
        Or.inl (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm')⟩
    · exact ⟨3, 1, Nat.prime_three, by decide, le_rfl, Or.inr (Or.inl h7)⟩
  obtain ⟨ρ, hρinj, hρW, -, -, -, -, c, hrows⟩ :=
    OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector hs hnab hC hα
      hJN hJc hp' hp'2 hf' hsrc hWalt (by norm_num : 3 ≤ 5) (by norm_num : 1 ≤ 1) hK φ'
  rcases hrows with ⟨σ, hF, -⟩ | hG
  · exfalso
    rcases hF with ⟨hn3, -⟩ | ⟨hn3, -⟩ <;> omega
  obtain ⟨hρa, -, -, hOinj, -, -, hG59⟩ := hG
  rcases hG59 with ⟨hn3, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, hLmap, -⟩
  · omega
  obtain ⟨hA, hB, hH, hinv, hsq, hne⟩ := l52_facts
  set ψ := GeneralLinearGroup.map (n := Fin 5) (ZMod.castHom (dvd_refl 2) K) with hψdef
  set O := matrixIsometryGroup ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hOdef
  have hAO : ψ l52A ∈ O := map_mem_matrixIsometryGroup_one hA
  have hBO : ψ l52B ∈ O := map_mem_matrixIsometryGroup_one hB
  set g := ⁅ψ l52A, ψ l52B⁆ with hgdef
  have hgO : g ∈ O := O.mul_mem (O.mul_mem (O.mul_mem hAO hBO) (O.inv_mem hAO)) (O.inv_mem hBO)
  have hgψ : g = ψ ⁅l52A, l52B⁆ := (map_commutatorElement ψ l52A l52B).symm
  have hgT : GeneralLinearGroup.inverseTranspose g = g := by
    rw [hgψ, ← GeneralLinearGroup.map_inverseTranspose, hinv]
  have hhg : (ψ l52H)⁻¹ * GeneralLinearGroup.inverseTranspose (ψ l52H) = g := by
    rw [hgψ, ← GeneralLinearGroup.map_inverseTranspose, ← map_inv, ← map_mul, hH]
  have hg2 : orderOf g = 2 := by
    rw [hgψ, orderOf_injective ψ map_castHom_injective]
    exact orderOf_eq_prime hsq hne
  have key : (conjAut 5 K (ψ l52H))⁻¹ * dualAut 5 K * conjAut 5 K (ψ l52H) =
      dualAut 5 K * conjAut 5 K g := by
    rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, ← map_inv, ← map_mul, hhg,
      dualAut_mul_conjAut, hgT]
  set Cc := conjAut 5 K c with hCcdef
  have hgN' : conjAut 5 K g ∈ ⁅O.map (conjAut 5 K), O.map (conjAut 5 K)⁆ := by
    rw [hgdef, map_commutatorElement]
    exact commutator_mem_commutator (mem_map_of_mem _ hAO) (mem_map_of_mem _ hBO)
  have hz : Cc * conjAut 5 K g * Cc⁻¹ ∈ J.map ρ := by
    rw [hLmap]
    exact ⟨conjAut 5 K g, hgN', by simp [MulAut.conj_apply]⟩
  obtain ⟨z, hzJ, hρz⟩ := mem_map.mp hz
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective ρ hρinj, hρz, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have := orderOf_injective _ hOinj ⟨g, hgO⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype] at this
    rw [this, Subgroup.orderOf_mk, hg2]
  set X := c * ψ l52H * c⁻¹ with hXdef
  have hdet : (X : Matrix (Fin 5) (Fin 5) K).det = 1 :=
    eq_one_of_card_two hK2 (GeneralLinearGroup.det_ne_zero X)
  let sX : Matrix.SpecialLinearGroup (Fin 5) K := ⟨X, hdet⟩
  have hsX : Matrix.SpecialLinearGroup.toGL sX = X := Units.ext rfl
  set γ₀ : G := ((φ'.symm (proj 5 K sX) : N) : G) with hγ₀def
  have hργ₀ : ρ γ₀ = Cc * conjAut 5 K (ψ l52H) * Cc⁻¹ := by
    rw [hγ₀def, hρW, MulEquiv.apply_symm_apply, ← conjAut_toGL, hsX, hXdef, map_mul, map_mul,
      map_inv]
  refine concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hzJ hz2
    (φ'.symm (proj 5 K sX)).2 (hρinj ?_)
  rw [map_mul, map_mul, map_inv, hργ₀, hρa, map_mul, hρa, hρz]
  calc (Cc * conjAut 5 K (ψ l52H) * Cc⁻¹)⁻¹ * (Cc * dualAut 5 K * Cc⁻¹) *
        (Cc * conjAut 5 K (ψ l52H) * Cc⁻¹) =
        Cc * ((conjAut 5 K (ψ l52H))⁻¹ * dualAut 5 K * conjAut 5 K (ψ l52H)) * Cc⁻¹ := by group
    _ = Cc * (dualAut 5 K * conjAut 5 K g) * Cc⁻¹ := by rw [key]
    _ = Cc * dualAut 5 K * Cc⁻¹ * (Cc * conjAut 5 K g * Cc⁻¹) := by group

end CFSG.ComponentClassification.GSThmB.CF23I
