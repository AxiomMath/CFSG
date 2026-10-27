module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3U
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81InnD

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.CatFactsL4U4.DiagU
open CFSG.ComponentClassification.HarrisLit.C3 CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace Q81

section Linear

variable {k : Type} [Field k] [Finite k]

theorem rowS_of_eq_conjAut {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {φ : MulAut (projectiveSL 4 k)} (hφ2 : φ ^ 2 = 1) (hφ1 : φ ≠ 1)
    {J' : Subgroup (projectiveSL 4 k)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    {m : ℕ} (hJm : Blueprint.LieModel ↥J' .PSL 2 ℓ m) {B : GL (Fin 4) k}
    (hφB : φ = conjAut 4 k B) :
    m = 2 * e ∧
      SelectorRowS 4 k (MonoidHom.id (MulAut (projectiveSL 4 k)))
        (OuterAutomorphisms.inner (projectiveSL 4 k)) φ (J'.map MulAut.conj) := by
  classical
  set ρ := MonoidHom.id (MulAut (projectiveSL 4 k)) with hρ
  have hinj : Function.Injective ρ := Function.injective_id
  set L := J'.map (MulAut.conj : projectiveSL 4 k →* MulAut (projectiveSL 4 k)) with hL
  have ha : orderOf φ = 2 := orderOf_eq_prime hφ2 hφ1
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hJc : CFSG.Assembly.IsComponentOf J' (fixSub φ) :=
    (isComponentOf_iff_isComponent_subgroupOf hJφ).2 hJ
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ}) := by
    have h1 := isComponentOf_map_of_injective hJc MulAut.conj CSL.conj_injective
    rw [OIL.map_conj_fixSub] at h1
    rw [hρ, Subgroup.map_id]
    exact h1
  let eJL : ↥J' ≃* ↥L := J'.equivMapOfInjective _ CSL.conj_injective
  have hJq : IsQuasisimple ↥J' :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJφ) hJ.1
  have hJna := FooteLit.exists_mul_ne_mul_of_isQuasisimple hJq
  have : IsSimpleGroup ↥J' := FooteLit.isSimpleGroup_of_lieModel_psl_two hJm
  have : IsSimpleGroup ↥L := eJL.symm.isSimpleGroup
  have hLna : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJna
    exact ⟨eJL a, eJL b, fun h => hab (eJL.injective (by rw [map_mul, map_mul, h]))⟩
  have hLZ : center ↥L = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hZodd : Odd (Nat.card (center ↥L)) := by
    rw [hLZ, Subgroup.card_bot]
    exact odd_one
  let eLb : ↥L ⧸ center ↥L ≃* ↥J' :=
    (QuotientGroup.quotientMulEquivOfEq hLZ).trans (QuotientGroup.quotientBot.trans eJL.symm)
  have hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 ℓ m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eLb.symm hJm
  have hsrc : StatedClassicalModel (↥L ⧸ center ↥L) .PSL 2 ℓ m ∨
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 2 :=
    Or.inl (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hLm)
  have hCA : (centralizer {φ}).map ρ = ρ.range ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id, MonoidHom.range_eq_top.2 Function.surjective_id, top_inf_eq]
    rfl
  have hCW : (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {φ}).map ρ =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id]
    rfl
  have hbig : ∀ {E : Type} [Field E] [Finite E], Nat.card E = Nat.card k ^ 2 →
      Nonempty (↥L ≃* projectiveSL 2 E) → m = 2 * e := by
    intro E _ _ hE ⟨eX⟩
    have hEodd : Odd (Nat.card E) := by rw [hE]; exact hodd.pow
    let eX' : ↥L ≃* GorensteinWalter.PSL2 E :=
      eX.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm
    have hLm' : Blueprint.LieModel (↥L ⧸ (⊥ : Subgroup ↥L)) .PSL 2 ℓ m :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientBot.trans eJL.symm).symm) hJm
    have h := GSThmB.Catalog7L4M.eq_card_of_psl2 rfl hℓ hℓ2 hLm' hEodd eX'
    rw [hE, hk, ← pow_mul] at h
    have := Nat.pow_right_injective hℓ.two_le h
    omega
  obtain ⟨μ, hμ, hsq, -⟩ := inner_case_reduction ha le_rfl hℓ hℓ2 he hk hinj hL₁ hφB hℓ2
    hsrc (fun _ => Or.inr hZodd)
  obtain ⟨hrow, E, _, _, hE, hiso⟩ :=
    selectorRowS_of_inner htwo hinj hCA hCW hL₁ hφB hμ hsq
  exact ⟨hbig hE hiso, hrow⟩

end Linear

section Cover

variable {G : Type} [Group G] [Finite G]

theorem l4_inner_b (Q : Subgroup G) (x : G) (p kk m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ kk) (hQ : IsQuasisimple ↥Q) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ kk) (e₀ : ↥Q ⧸ center ↥Q ≃* projectiveSL 4 F)
    (hZ : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ kk - 1))
    (hxN : x ∈ normalizer (Q : Set G)) (hx2 : x * x = 1) (hxC : x ∉ centralizer (Q : Set G))
    (hLm : Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 p m)
    (hinn : phi hxN e₀ ∈ (conjAut 4 F).range) :
    m = 2 * kk ∧ ∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
      ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8 := by
  classical
  have hF2 : ringChar F ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have hφ2 := phi_sq hxN e₀ hx2
  have hφ1 := phi_ne_one hxN e₀ hQ.1 hxC
  obtain ⟨hLs, hLna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hLm
  have hLZ : center ↥(Lay Q x) = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hJφ := Jp_le_fixSub hxN e₀
  have hJ := isComponent_Jp hxN e₀ hLna
  have hJm : Blueprint.LieModel ↥(Jp e₀ x) .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (equivJp e₀ hLZ) hLm
  obtain ⟨B₀, hB₀⟩ := hinn
  obtain ⟨hm, hS⟩ := rowS_of_eq_conjAut hp hp2 hk hF hφ2 hφ1 hJφ hJ hJm hB₀.symm
  refine ⟨hm, ?_⟩
  have hZ' : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ Nat.card F - 1) := by
    rw [hF]
    exact hZ
  obtain ⟨θ, hθs, hθ, hθk, hθ1⟩ := exists_theta e₀ hQ hF2 hZ'
  obtain ⟨C, ν, Ψ, hφM, hκU, hcen, hnot, hE8⟩ := rowS_aut hF2 hS
  set sκ := CatalogueBHigherLinearAction.slConjugation 4 F C (kappaSL ν Ψ) with hsκ
  have hκGL : SpecialLinearGroup.toGL sκ = C * rowSKappa ν Ψ * C⁻¹ := by
    rw [hsκ, CatalogueBHigherLinearAction.toGL_slConjugation, toGL_kappaSL]
  have hconjκ : MulAut.conj (proj 4 F sκ) = conjAut 4 F (C * rowSKappa ν Ψ * C⁻¹) := by
    rw [← conjAut_toGL, hκGL]
  rw [← hconjκ] at hcen hnot hE8
  obtain ⟨hcenP, hnotP, hE8P⟩ := transfer_conj CSL.conj_injective hcen hnot hE8
  have hxκ : xAut hxN (θ sκ) = θ sκ := by
    rw [xAut_theta e₀ hxN hθ hφM sκ]
    have h1 : CatalogueBHigherLinearAction.slConjugation 4 F (C * rowSU ν Ψ * C⁻¹) sκ =
        negOne4 * sκ := by
      apply SpecialLinearGroup.toGL_injective
      rw [CatalogueBHigherLinearAction.toGL_slConjugation, hκGL, map_mul, toGL_negOne4, hκGL]
      exact conj_kappa hκU (rowSKappa_mul_self ν Ψ)
    rw [h1, map_mul, hθ1, one_mul]
  have hκ2 : θ sκ * θ sκ = 1 := by
    rw [← map_mul]
    have h1 : sκ * sκ = 1 := by
      apply SpecialLinearGroup.toGL_injective
      rw [map_mul, hκGL, map_one,
        show C * rowSKappa ν Ψ * C⁻¹ * (C * rowSKappa ν Ψ * C⁻¹) =
          C * (rowSKappa ν Ψ * rowSKappa ν Ψ) * C⁻¹ by group, rowSKappa_mul_self, mul_one,
        mul_inv_cancel]
    rw [h1, map_one]
  rw [← hθ sκ] at hcenP hnotP hE8P
  exact b_alternative e₀ hLZ ((xAut_eq_iff hxN _).mp hxκ) hκ2 hnotP hcenP hE8P

end Cover

section InnDiag

variable {G : Type} [Group G] [Finite G]

structure IsInnDiag (Q I : Subgroup G) : Prop where
  le : Q ≤ I
  centralizer_le : centralizer (Q : Set G) ≤ I
  le_normalizer : I ≤ normalizer (Q : Set G)
  mul_mem : ∀ x ∈ normalizer (Q : Set G), ∀ y ∈ normalizer (Q : Set G), x ∉ I → y ∉ I →
    x * y ∈ I
  inner_b : ∀ x ∈ I, x * x = 1 → x ∉ centralizer (Q : Set G) →
    Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 3 2 →
    ∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
      ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8

theorem isInnDiag_innDiagL {Q : Subgroup G} (hQ : IsQuasisimple ↥Q) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 3) (e : ↥Q ⧸ center ↥Q ≃* projectiveSL 4 F)
    (hZ : Nat.card ↥(center ↥Q) = 1) : IsInnDiag Q (innDiagL e) where
  le := le_innDiagL e
  centralizer_le := centralizer_le_innDiagL e
  le_normalizer := innDiagL_le_normalizer e
  mul_mem := fun _ hx _ hy hx' hy' => mul_mem_innDiagL e hF hx hy hx' hy'
  inner_b := by
    rintro x ⟨hxN, hinn⟩ hx2 hxC hLm
    exact (l4_inner_b Q x 3 1 2 Nat.prime_three (by norm_num) le_rfl hQ (by rw [hF, pow_one]) e
      (Or.inl hZ) hxN hx2 hxC hLm hinn).2

theorem isInnDiag_innDiagU {Q : Subgroup G} (hQ : IsQuasisimple ↥Q) {K : Type} [Field K]
    (hK9 : UnitaryFieldData 3 1 K) (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (3 ^ 1) K))
    (hZ : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ 3 ^ 1 + 1)) :
    IsInnDiag Q (innDiagU hK9 e) where
  le := le_innDiagU hK9 e
  centralizer_le := centralizer_le_innDiagU hK9 e
  le_normalizer := innDiagU_le_normalizer hK9 e
  mul_mem := fun _ hx _ hy hx' hy' => mul_mem_innDiagU hK9 e hx hy hx' hy'
  inner_b := by
    rintro x ⟨hxN, hinn⟩ hx2 hxC hlie
    have : Finite K := hK9.finite
    have hφ2 := phi_sq hxN e hx2
    have hφ1 := phi_ne_one hxN e hQ.1 hxC
    obtain ⟨hLs, hLna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hlie
    have hLZ : center ↥(Lay Q x) = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
    have hJφ := Jp_le_fixSub hxN e
    have hJc := isComponent_Jp hxN e hLna
    have hJm : Blueprint.LieModel ↥(Jp e x) .PSL 2 3 2 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (equivJp e hLZ) hlie
    obtain ⟨θ, -, hθ, -, hθ1⟩ := exists_thetaU hK9 (by norm_num) e hQ hZ
    obtain ⟨A, hA⟩ := (mem_InnU hK9).1 hinn
    exact (u4_inner_b hK9 (by norm_num) hxN e hθ hθ1 hφ1 hLZ hJφ hJc hJm hA hφ2).2

theorem exists_isInnDiag {Q : Subgroup G} (hQ : IsQuasisimple ↥Q)
    (hZc : (Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∧
        (Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ 3 ^ 1 - 1))) ∨
      (Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1 ∧
        (Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ 3 ^ 1 + 1)))) :
    ∃ I : Subgroup G, IsInnDiag Q I := by
  rcases hZc with ⟨hL, hZ⟩ | ⟨hU, hZ⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
    rw [pow_one] at hF
    have hZ1 : Nat.card ↥(center ↥Q) = 1 := by
      rcases hZ with hZ | ⟨-, h4⟩
      · exact hZ
      · norm_num at h4
    exact ⟨_, isInnDiag_innDiagL hQ hF e hZ1⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU
    have hK9 : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
    exact ⟨_, isInnDiag_innDiagU hQ hK9 e hZ⟩

end InnDiag

end Q81

end CFSG.ComponentClassification.HarrisLit
