module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcMain
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.StandardType.TableBExc

section Model


theorem mul_comm_of_smul_neg {τ : Tag} {w : WeylGroup τ} (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x)
    (q : WeylGroup τ) : w * q = q * w := by
  refine eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun x => ?_
  rw [mul_smul, mul_smul, hw (q • x), hw x, smul_neg]

theorem langTorus_le_model {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) : S.D.torus ≤ S.D.model := fun x hx => by
  obtain ⟨hxT, hxeq⟩ := mem_twistedTorusOf.1 hx
  exact ⟨torusGroup_le_adjointGroup' hxT, hxeq⟩

theorem canonicalRep_mem_model {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
    (S : LangSetup τ L p) (Fr : L →+* L) (w : WeylGroup τ)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x) (q : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) L q ∈ S.D.model := by
  refine (LangDatum.mem_model _).2 ⟨canonicalRep_mem_adjointGroup _ L q, ?_⟩
  rw [hn, hΦ, CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8Lift.units_map_entrywiseHom_canonicalRep,
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    mul_comm_of_smul_neg hw q, mul_assoc, mul_inv_cancel, mul_one]

theorem baseChange_monomial_mem_model {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup τ L 5) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2) (w : WeylGroup τ)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x) {K : Type} [Field K] (hK3 : ∀ a : Kˣ, a ^ 3 = 1)
    (ι : K →+* L) {x : ModGL τ K} (hx : x ∈ monomialSubgroup τ K) :
    baseChangeGL ι x ∈ S.D.model := by
  obtain ⟨w', k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets hx
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  rw [hgk, map_mul, baseChangeGL_rootDiagUnit,
    CFSG.RankThree.Chevalley.baseChangeGL_canonicalRep]
  refine mul_mem (langTorus_le_model S (rootDiagUnit_mem_langTorus S Fr hFr w hΦ hn hw
    (fun i => ?_))) (canonicalRep_mem_model S Fr w hΦ hn hw w')
  rw [← map_pow, hK3, map_one]

theorem exists_conj_le_of_not_dvd_index' {G : Type*} [Group G] {Γ P E : Subgroup G} [Finite Γ]
    (hidx : ¬ 3 ∣ (P.subgroupOf Γ).index) (hEΓ : E ≤ Γ) (hE : IsPGroup 3 E) :
    ∃ g ∈ Γ, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  have hE' : IsPGroup 3 (E.subgroupOf Γ) := hE.comap_subtype
  obtain ⟨g, hg⟩ := CFSG.StandardType.TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three
    hidx hE'
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h1 : (MulAut.conj g) (⟨e, hEΓ he⟩ : Γ) ∈ P.subgroupOf Γ := hg ⟨⟨e, hEΓ he⟩, he, rfl⟩
  have h2 := Subgroup.mem_subgroupOf.1 h1
  simpa [MulAut.conj_apply] using h2

theorem charP_two_of_card_two' {K : Type} [Field K] (hK : Nat.card K = 2) : CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime hK'

theorem exc_maxRank_of_data {τ : Tag} {w : WeylGroup τ}
    (hw : ∀ x : Fin τ.rank → ℤ, w • x = -x)
    (Q : Subgroup (WeylGroup τ)) (k : ℕ) (hQ : Nat.card Q = 3 ^ k)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3)) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hV : Nat.card (torusPow τ (GaloisField 2 2) 3) = 3 ^ τ.rank)
    (hH : Nat.card (torusGroup τ (GaloisField 2 2)) = 3 ^ τ.rank)
    (hoff : ∀ A : Subgroup (WeylGroup τ), A ≤ Q → IsElemAbelian 3 A → A ≠ ⊥ →
      Nat.card A * Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} <
        3 ^ τ.rank)
    (hord : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      ∃ m, ¬ 3 ∣ m ∧ Nat.card (adjointGroup τ K) = 3 ^ (τ.rank + k) * m) :
    ExcMaxRank τ w := by
  classical
  intro L _ _ S Fr K _ _ hK hφ hFr hq2 hΦ hn h3sub
  obtain ⟨φ⟩ := hφ
  have h2L : ((2 : ℕ) : L) = 0 := by
    have := S.hqpow.2
    rwa [hq2] at this
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2L
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK43 : ∀ a : (GaloisField 2 2)ˣ, a ^ 3 = 1 := fun a => by
    have h : a ^ Nat.card (GaloisField 2 2)ˣ = 1 := pow_card_eq_one'
    rwa [Nat.card_units, hK4] at h
  have h3K : 3 ∣ Nat.card (GaloisField 2 2) - 1 := by rw [hK4]
  let ι : GaloisField 2 2 →+* L := (IsAlgClosed.lift : GaloisField 2 2 →ₐ[ZMod 2] L)
  let φ₄ : adjointGroup τ (GaloisField 2 2) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ (GaloisField 2 2)).subtype
  have hφ₄inj : Function.Injective φ₄ :=
    (baseChangeGL_injective ι).comp (Subgroup.subtype_injective _)
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cube_root_unity L (natCast_three_ne_zero_of_q_two S hq2)
  haveI : Finite (torus3 τ L) :=
    Nat.finite_of_card_ne_zero (by rw [card_torus3 hζ hζ']; positivity)
  haveI : Finite (torusPow τ (GaloisField 2 2) 3) :=
    Nat.finite_of_card_ne_zero (by rw [hV]; positivity)
  have hT3 : torus3 τ L ≤ S.D.model := by
    rintro _ ⟨a, ha, rfl⟩
    exact langTorus_le_model S (rootDiagUnit_mem_langTorus S Fr hFr w hΦ hn hw ha)
  have hT3Γ : torus3 τ L ≤ S.Γ := h3sub _ hT3 (isPGroup_of_isElemAbelian' isElemAbelian_torus3)
  set X := weylX τ (GaloisField 2 2) Q with hXdef
  set P₁ : Subgroup (ModGL τ L) := X.map φ₄ with hP₁
  have hP₁model : P₁ ≤ S.D.model := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hg, -⟩ := mem_weylX.1 hx
    exact baseChange_monomial_mem_model S Fr hFr w hΦ hn hw hK43 ι hg
  have hP₁card : Nat.card P₁ = 3 ^ (τ.rank + k) := by
    rw [hP₁, Subgroup.card_map_of_injective hφ₄inj, hXdef, card_weylX, hQ, hH, pow_add, mul_comm]
  have hP₁Γ : P₁ ≤ S.Γ := h3sub P₁ hP₁model (IsPGroup.of_card hP₁card)
  obtain ⟨m, hm3, hΓcard⟩ := hord K hK
  have hΓcard' : Nat.card S.Γ = 3 ^ (τ.rank + k) * m := by
    rw [← Nat.card_congr φ.toEquiv]
    exact hΓcard
  have hm0 : m ≠ 0 := fun h => hm3 (h ▸ dvd_zero 3)
  haveI : Finite S.Γ := Nat.finite_of_card_ne_zero (by
    rw [hΓcard']
    exact mul_ne_zero (by positivity) hm0)
  have hidx : ¬ 3 ∣ (P₁.subgroupOf S.Γ).index := by
    have h1 := Subgroup.card_mul_index (P₁.subgroupOf S.Γ)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁Γ).toEquiv, hP₁card, hΓcard'] at h1
    have : (P₁.subgroupOf S.Γ).index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [this]
    exact hm3
  have hVmap : (torusPow τ (GaloisField 2 2) 3).map φ₄ = torus3 τ L := by
    have hle : (torusPow τ (GaloisField 2 2) 3).map φ₄ ≤ torus3 τ L := by
      rintro _ ⟨x, ⟨hxT, -⟩, rfl⟩
      obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
      refine ⟨fun i => Units.map ι.toMonoidHom (a i), fun i => ?_, ?_⟩
      · rw [← map_pow, hK43, map_one]
      · show baseChangeGL ι (x : ModGL τ (GaloisField 2 2)) = _
        rw [ha, baseChangeGL_rootDiagUnit]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective hφ₄inj, hV, card_torus3 hζ hζ']
  refine ⟨hT3Γ, fun E hEΓ hEel hEcard => ?_⟩
  obtain ⟨g, hgΓ, hg⟩ := exists_conj_le_of_not_dvd_index' hidx hEΓ (isPGroup_of_isElemAbelian' hEel)
  set E₁ := E.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁el : IsElemAbelian 3 E₁ := isElemAbelian_map' _ hEel
  have hE₁card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  set E₂ : Subgroup (adjointGroup τ (GaloisField 2 2)) := E₁.comap φ₄ with hE₂
  have hE₁range : E₁ ≤ φ₄.range := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hg hx
    exact ⟨y, rfl⟩
  have hE₂map : E₂.map φ₄ = E₁ := Subgroup.map_comap_eq_self hE₁range
  have hE₂X : E₂ ≤ X := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hg (show φ₄ x ∈ E₁ from hx)
    rw [← hφ₄inj hyx]
    exact hy
  have hE₂el : IsElemAbelian 3 E₂ := isElemAbelian_comap' hφ₄inj hE₁el
  have hE₂card : Nat.card E₂ = Nat.card E := by
    rw [← hE₁card, ← hE₂map, Subgroup.card_map_of_injective hφ₄inj]
  obtain ⟨A, hAQ, hA, hA1, hEA⟩ :=
    card_le_mul_card_fix_of_le_weylX Nat.prime_three h3K hdet hV hsymm hE₂el hE₂X
  have hE₂V : E₂ = torusPow τ (GaloisField 2 2) 3 := by
    by_cases hbot : A = ⊥
    · exact Subgroup.eq_of_le_of_card_ge (hA1 hbot) (by rw [hV, hE₂card]; exact hEcard)
    · have := hoff A hAQ hA hbot
      omega
  refine ⟨g, ?_, ?_⟩
  · exact Subgroup.commutator_le_self S.D.model (hgΓ : g ∈ S.D.Γ)
  · show E₁ = torus3 τ L
    rw [← hE₂map, hE₂V, hVmap]

theorem card_galoisField_two_two [Fact (Nat.Prime 2)] : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem exc_maxRank_E7 : ExcMaxRank Tag.E7 e7Neg := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exc_maxRank_of_data (w := e7Neg) e7Neg_smul
    CFSG.StandardType.TableBExc.Three.modelHomE7.range 4 ?_ ?_
    CFSG.StandardType.TableBExc.Three.cartan_symm_E7 ?_ ?_
    CFSG.StandardType.TableBExc.Three.noOffender_E7 ?_
  · rw [CFSG.StandardType.TableBExc.Three.card_range_modelHomE7]
    norm_num
  · exact isUnit_det_cartan_of_eq Nat.prime_three CFSG.LieType.Chevalley.det_cartan_E7
      (by norm_num)
  · exact card_torusPow_E7 Nat.prime_three (by rw [card_galoisField_two_two])
  · have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := GaloisField 2 2)
    rw [card_galoisField_two_two] at h
    norm_num at h
    exact h
  · intro K _ _ hK
    haveI := charP_two_of_card_two' hK
    have hH := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
    rw [hK] at hH
    norm_num at hH
    rw [card_adjointGroup_E7_eq, hK, hH, Subgroup.card_bot, one_mul]
    refine ⟨(2 ^ 63 * prodE7 2) / 3 ^ 11, by decide +kernel, ?_⟩
    show _ = 3 ^ (7 + 4) * _
    exact (Nat.mul_div_cancel' (by decide +kernel)).symm

theorem exc_maxRank_E8 : ExcMaxRank Tag.E8 e8Neg := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exc_maxRank_of_data (w := e8Neg) e8Neg_smul
    CFSG.StandardType.TableBExc.Three.modelHomE8.range 5 ?_ ?_
    CFSG.StandardType.TableBExc.Three.cartan_symm_E8 ?_ ?_
    CFSG.StandardType.TableBExc.Three.noOffender_E8 ?_
  · rw [CFSG.StandardType.TableBExc.Three.card_range_modelHomE8]
    norm_num
  · exact isUnit_det_cartan_of_eq Nat.prime_three CFSG.LieType.Chevalley.det_cartan_E8
      (by norm_num)
  · exact card_torusPow_E8 Nat.prime_three (by rw [card_galoisField_two_two])
  · have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8 (K := GaloisField 2 2)
    rw [card_galoisField_two_two] at h
    norm_num at h
    exact h
  · intro K _ _ hK
    have hH := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8 (K := K)
    rw [hK] at hH
    norm_num at hH
    rw [card_adjointGroup_E8_eq, hK, hH, Subgroup.card_bot, one_mul]
    refine ⟨(2 ^ 120 * prodE8 2) / 3 ^ 13, by decide +kernel, ?_⟩
    show _ = 3 ^ (8 + 5) * _
    exact (Nat.mul_div_cancel' (by decide +kernel)).symm

end Model

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
