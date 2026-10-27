module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U4Split
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23Wit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U4Anti
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Module Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.Catalog7L4EU
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)

theorem lieModel_of_psl2_equiv {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ (2 * f))
    (e : Y ≃* GorensteinWalter.PSL2 F) : LieModel Y .PSL 2 p (2 * f) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h9 : 9 ≤ p ^ (2 * f) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  have hodd : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  have hm := OddSelector.statedClassicalModel_psl_two hp (by omega) hF
    (fun h2 => by rw [h2] at hodd; exact (Nat.not_odd_iff_even.mpr even_two) hodd) (by omega)
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)).symm (Or.inl ⟨by decide, hm⟩)

section Anti

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u4_anti_type [Finite K] (hp2 : p ≠ 2)
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
  rcases anti_witness h hp2 hAu hAA hY σY hσYs hσYk hs₂ with ⟨E', _, _, hE', ⟨eP⟩⟩ |
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
    exact u4_split_false h hp2 ((AssemblyBPredicates.isQuasisimple_iff_native _).mp hX'.2.2) hnt
      hYX hY₂p hTY₂ hcomm hTT hTZ

end Anti

theorem u4_socle_false {H : Type} [Group H] {W : Subgroup H} [W.Normal]
    (hCW : centralizer (W : Set H) = ⊥) {a : H} (ha : orderOf a = 2) {L : Subgroup H}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L)
    (hsm : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        LieModel (↥L ⧸ center ↥L) .PSL 2 p f) ∨
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)))
    (hZL : Odd (Nat.card (center ↥L))) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hexc : ¬ LieModel (↥L ⧸ center ↥L) .PSL 2 p (2 * f))
    (hM : LieModel W .PSU 4 p f) : False := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hM
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := hud.finite
  have : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 4 (by norm_num)
      (by simp)
  have hnab : ∃ x y : StatedProj (StatedSU 4 (p ^ f) K), x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have hWle : W ≤ centralizer (W : Set H) := by
      intro w hw
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := hc (φ ⟨v, hv⟩) (φ ⟨w, hw⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (φ.injective h1)
    rw [hCW] at hWle
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSU 4 (p ^ f) K))
    apply hx
    have hw := hWle (φ.symm x).2
    rw [mem_bot] at hw
    have h1 : φ.symm x = 1 := Subtype.ext hw
    rw [← φ.apply_symm_apply x, h1, map_one]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW φ hZ hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (conj_injective hZ) hstd hLX
  have hsX : SmallSource X := smallSource_of_mulEquiv eLX (smallSource_of_cf23 hsm hZL)
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hα : ∀ y, ρ a (ρ a y) = y := by
    intro y
    rw [← MulAut.mul_apply, ← map_mul, ← pow_two, ha2, map_one, MulAut.one_apply]
  have hα1 : ρ a ≠ 1 := by
    intro h1
    have h2 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h1, orderOf_one, ha] at h2
    exact absurd h2 (by norm_num)
  have hexcX : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ (2 * f) →
      Nonempty (↥X ⧸ center ↥X ≃* GorensteinWalter.PSL2 F) → False := by
    intro F _ _ hF ⟨eP⟩
    exact hexc (lieModel_of_psl2_equiv hp hp2 hf hF ((centerQuotientCongr eLX).trans eP))
  obtain ⟨B, ψ, hBu, hψ, hcase⟩ := Catalog7U4.exists_lift hud hp2 (ρ a) hα
  rcases hcase with ⟨hψB, c₀, hBB⟩ | ⟨hψB, z, hBB⟩
  · obtain ⟨⟨eP⟩, -⟩ := psu4_inner_case hud hp2 hα1 hX hsX hBu hψ hψB hBB
    exact hexcX K (by rw [hK, ← pow_mul, mul_comm f 2]) ⟨eP⟩
  · obtain ⟨E', _, _, hE', heP⟩ := u4_anti_type hud hp2 hX hsX hW hBu hψ hψB hBB
    exact hexcX E' (by rw [hE', hud.card_fixedField, ← pow_mul, mul_comm f 2]) heP

theorem cf23InnerFusionFor_PSU4 :
    CF23InnerFusionFor fun Y _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      LieModel Y .PSU 4 p f := by
  intro G _ _ N hN hC hτ α J hα hJN hJα hJ hstd hsm hZ hexc
  exfalso
  obtain ⟨p, f, hp, hp2, hf, hM⟩ := hτ
  have := hN
  exact u4_socle_false hC hα (isComponentOf_of_cf23 hJN hJα hJ) hstd hsm hZ hp hp2 hf
    (fun h => hexc (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h, Or.inr (Or.inl hM)⟩))) hM

end CFSG.ComponentClassification.GSThmB.CF23I
