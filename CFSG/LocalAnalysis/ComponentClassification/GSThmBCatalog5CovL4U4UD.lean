module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U4Split
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4O8
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U4Anti

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.LinearGroups CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.Catalog7L4EU
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)

section Anti

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem psu4_anti_of_noTightWitness [Finite K] (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {X' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hX' : CFSG.Assembly.IsComponentOf X' (fixedSubgroup β)) (hs : SmallSource X')
    (hnt : NoTightWitness X') {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {z : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      z • 1) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
      Nonempty (X' ⧸ center X' ≃* GorensteinWalter.PSL2 E') := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hτ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτB := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have he : ∀ y, ιU h (β y) = antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))
      hτ hτB (ιU h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, ιU_mk, ιU_mk, antiProjConj_mk]
    congr 1
    exact (toSesqUnitary_antiConj h hAu g (ψ g) (hψA g)).symm
  have key := isComponentOf_map_of_intertwine (ιU h) (ιU_injective h) (ιU_range_normal h) he hX'
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ := OddClassSelector.central_lift _ hZc _
    (map_scalars_unitaryConj h _ _ hτB)
    (unitaryConj_unitaryConj h _ _ hτB (Units.mk0 z hz0)
      (CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA)) key
  have eX : X' ≃* X'.map (ιU h) := X'.equivMapOfInjective _ (ιU_injective h)
  have hs₂ : SmallSource (X'.map (ιU h)) := OddClassSelector.smallSource_of_mulEquiv eX hs
  rcases CF23I.anti_witness h hp2 hAu hAA hY σY hσYs hσYk hs₂ with ⟨E', _, _, hE', ⟨eP⟩⟩ |
    ⟨Y₂, T, hY₂p, hTY₂, hcomm, hTT, hTZ⟩
  · exact ⟨E', inferInstance, inferInstance, hE', ⟨(centerQuotientCongr eX).trans eP⟩⟩
  · exfalso
    have hYX : Y.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) =
        X'.map (ιU h) := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hσYv ⟨y, hy⟩]
        exact (σY ⟨y, hy⟩).2
      · intro hw
        obtain ⟨y, hy⟩ := hσYs ⟨w, hw⟩
        refine ⟨y, y.2, ?_⟩
        rw [← hσYv y, hy]
    exact CF23I.u4_split_false h hp2
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mp hX'.2.2) hnt hYX hY₂p hTY₂ hcomm hTT
      hTZ

end Anti

theorem cf23L4U4O8Comp_psu4_holds {N : Type} [Group N] [Finite N] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hN : LieModel N .PSU 4 p f)
    (G : Subgroup (MulAut N)) (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) (α : G)
    (J : Subgroup G) (hα : orderOf α = 2)
    (hJN : J ≤ (MulAut.conj : N →* MulAut N).range.subgroupOf G)
    (hJc : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hstd : IsStandardSubgroup J) (hodd : Odd (Nat.card (center J)))
    (hsmall : Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨
      ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
        LieModel (J ⧸ center J) .PSL 2 s t) :
    LieModel (J ⧸ center J) .PSL 2 p (2 * f) := by
  classical
  have hM := statedClassicalModel_of_lieModel hN (by simp [chevalleyExceptionalTags])
    (by simp [reeTitsTags]) (by decide)
  have : IsSimpleGroup N := (ClassicalGroups.Unitary.fam_PSU_simplicity N 4 p f hM).2
  have hL : CFSG.Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hJc).2 hJ
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup (nonabelian_of_inn_component hJN hL)
  obtain ⟨-, hWnab⟩ := innIn_simple_nonabelian G hZ hInn
  have hCW := centralizer_innIn G hZ hInn
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := id hM
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let θ : innIn G ≃* StatedProj (StatedSU 4 (p ^ f) K) := (innInEquiv G hZ hInn).trans φ
  have : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ f) K)) := φ.symm.isSimpleGroup
  have hnabP : ∃ x y : StatedProj (StatedSU 4 (p ^ f) K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZP := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnabP
  have hLCW := isComponentOf_of_le hL (le_inf hJN hL.1) inf_le_right
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZP hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (OddClassSelector.conj_injective hZP)
    hstd hLX
  have hsX := smallSource_of_mulEquiv eLX (smallSource_of_small hodd hsmall)
  have hα' : ∀ y, ρ α (ρ α y) = y := by
    intro y
    have hαα : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, hαα, map_one, MulAut.one_apply]
  have hα1 : ρ α ≠ 1 := by
    intro h
    have h1 : orderOf (ρ α) = orderOf α := orderOf_injective ρ hinj α
    rw [h, orderOf_one, hα] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := Catalog7U4.exists_lift hud hp2 (ρ α) hα'
  let eJ : ↥J ⧸ center ↥J ≃* ↥X ⧸ center ↥X :=
    QuotientGroup.congr _ _ eLX (Subgroup.map_center_eq eLX)
  have h4 : 4 ≤ p ^ (2 * f) := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  have : Finite K := hud.finite
  rcases hcase with ⟨hψA, c₀, hAA⟩ | ⟨hψA, z, hAA⟩
  · obtain ⟨⟨eP⟩, -⟩ := psu4_inner_case hud hp2 hα1 hX hsX hAu hψ hψA hAA
    exact lieModel_psl2_of_card hp h4 hud.card (eJ.trans eP)
  · obtain ⟨E', _, _, hE', ⟨eP⟩⟩ :=
      psu4_anti_of_noTightWitness hud hp2 hX hsX hW hAu hψ hψA hAA
    exact lieModel_psl2_of_card hp h4
      (by rw [hE', hud.card_fixedField, ← pow_mul, mul_comm]) (eJ.trans eP)

end CFSG.ComponentClassification.GSThmB.Cov
