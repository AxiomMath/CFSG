module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport
public import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Odd
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.Walter.Defs

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.GorensteinWalter CFSG.Walter CFSG.QuasithinUnique CFSG.QuasithinUnique.K1
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

section Fixed

variable {F : Type} [Field F]

@[expose] def fixedSubfieldOf (σ : F ≃+* F) : Subfield F := σ.toRingHom.eqLocusField (RingHom.id F)

theorem mem_fixedSubfieldOf {σ : F ≃+* F} {a : F} : a ∈ fixedSubfieldOf σ ↔ σ a = a := Iff.rfl

@[expose] noncomputable def psl2FixedRange (σ : F ≃+* F) : Subgroup PSL(2, F) :=
  (psl2Map (fixedSubfieldOf σ).subtype).range

theorem exists_sl2_map_of_fixed (σ : F ≃+* F) (M : SL(2, F))
    (h : Matrix.SpecialLinearGroup.map σ.toRingHom M = M) :
    ∃ M₀ : SL(2, fixedSubfieldOf σ),
      Matrix.SpecialLinearGroup.map (fixedSubfieldOf σ).subtype M₀ = M := by
  have hent : ∀ i j, σ (M i j) = M i j := fun i j => by
    have := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F) i j) h
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
  let M₀' : Matrix (Fin 2) (Fin 2) (fixedSubfieldOf σ) :=
    Matrix.of fun i j => ⟨M i j, mem_fixedSubfieldOf.mpr (hent i j)⟩
  have hmap : (fixedSubfieldOf σ).subtype.mapMatrix M₀' = (M : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    rfl
  have hdet : M₀'.det = 1 := by
    apply (fixedSubfieldOf σ).subtype.injective
    rw [RingHom.map_det, hmap, M.2, map_one]
  let M₀ : SL(2, fixedSubfieldOf σ) := ⟨M₀', hdet⟩
  refine ⟨M₀, Subtype.ext ?_⟩
  show (fixedSubfieldOf σ).subtype.mapMatrix M₀' = (M : Matrix (Fin 2) (Fin 2) F)
  exact hmap

theorem psl2FixedRange_le_fixedSubgroup (σ : F ≃+* F) :
    psl2FixedRange σ ≤ fixedSubgroup (psl2FieldAut F σ) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_fixedSubgroup, psl2FieldAut_eq_psl2Map]
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [psl2Map_mk]
  congr 1
  ext i j
  exact mem_fixedSubfieldOf.mp (A i j).2

theorem conj_mem_psl2FixedRange (σ : F ≃+* F) {y n : PSL(2, F)}
    (hy : psl2FieldAut F σ y = y) (hn : n ∈ psl2FixedRange σ) :
    y * n * y⁻¹ ∈ psl2FixedRange σ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hn
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psl2FieldAut_eq_psl2Map, psl2Map_mk] at hy
  have hc := (QuotientGroup.eq (s := Subgroup.center SL(2, F))).mp hy
  set c : SL(2, F) := (Matrix.SpecialLinearGroup.map σ.toRingHom A)⁻¹ * A with hcdef
  have hmapA : Matrix.SpecialLinearGroup.map σ.toRingHom A = A * c⁻¹ := by
    rw [hcdef]
    group
  set B' : SL(2, F) := Matrix.SpecialLinearGroup.map (fixedSubfieldOf σ).subtype B with hB'
  have hσB : Matrix.SpecialLinearGroup.map σ.toRingHom B' = B' := by
    rw [hB']
    apply Subtype.ext
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact mem_fixedSubfieldOf.mp (B i j).2
  have hcomm : c⁻¹ * B' = B' * c⁻¹ :=
    (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) B').symm
  have hM : Matrix.SpecialLinearGroup.map σ.toRingHom (A * B' * A⁻¹) = A * B' * A⁻¹ := by
    rw [map_mul, map_mul, map_inv, hmapA, hσB]
    calc A * c⁻¹ * B' * (A * c⁻¹)⁻¹ = A * (c⁻¹ * B' * c) * A⁻¹ := by group
      _ = A * B' * A⁻¹ := by rw [hcomm]; group
  obtain ⟨M₀, hM₀⟩ := exists_sl2_map_of_fixed σ _ hM
  refine ⟨QuotientGroup.mk M₀, ?_⟩
  rw [psl2Map_mk, hM₀, psl2Map_mk, ← hB']
  simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

variable [Finite F]

theorem isQuasisimple_psl2FixedRange (σ : F ≃+* F) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp5 : 5 ≤ p) : CFSG.IsQuasisimple (psl2FixedRange σ) := by
  classical
  have hinj : Function.Injective (psl2Map (fixedSubfieldOf σ).subtype) :=
    psl2Map_injective _
  let e : PSL(2, fixedSubfieldOf σ) ≃* psl2FixedRange σ :=
    MonoidHom.ofInjective hinj
  have : Fintype (fixedSubfieldOf σ) := Fintype.ofFinite _
  have hcharF₀ : CharP (fixedSubfieldOf σ) p :=
    (fixedSubfieldOf σ).subtype.charP (fixedSubfieldOf σ).subtype.injective p
  have hring : ringChar (fixedSubfieldOf σ) = p := ringChar.eq _ p
  have hodd : ringChar (fixedSubfieldOf σ) ≠ 2 := by rw [hring]; omega
  have hq5 : 5 ≤ Fintype.card (fixedSubfieldOf σ) := by
    obtain ⟨n, hn, hcard⟩ := FiniteField.card (fixedSubfieldOf σ) p
    rw [hcard]
    calc 5 ≤ p := hp5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right hn.pos n.pos
  have hcard5 : 5 ≤ Nat.card (fixedSubfieldOf σ) := by
    rw [Nat.card_eq_fintype_card]
    exact hq5
  have hsimple : IsSimpleGroup PSL(2, fixedSubfieldOf σ) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have h4 : 4 ∣ Nat.card PSL(2, fixedSubfieldOf σ) := psl2_four_dvd_card hodd hq5
  have hnonab : ∃ a b : PSL(2, fixedSubfieldOf σ), a * b ≠ b * a :=
    not_comm_of_simple_of_four_dvd h4
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1

theorem not_charTwo_fixedSubgroup_psl2FieldAut (σ : F ≃+* F) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp5 : 5 ≤ p) : ¬ CharTwo (fixedSubgroup (psl2FieldAut F σ)) := by
  intro hC
  have hle := psl2FixedRange_le_fixedSubgroup σ
  have hq := isQuasisimple_psl2FixedRange σ hp5
  have hnorm : ((psl2FixedRange σ).subgroupOf (fixedSubgroup (psl2FieldAut F σ))).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_psl2FixedRange σ c.2 hn
  have hcomp : IsComponentIn (psl2FixedRange σ) (fixedSubgroup (psl2FieldAut F σ)) :=
    ⟨hle, CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hle).symm hq, hnorm.isSubnormal⟩
  exact not_le_of_isComponentIn_of_charTwo hC le_rfl hcomp hle

end Fixed

section Assembly

theorem map_fixedSubgroup_conj {G : Type} [Group G] (a b : MulAut G) :
    (fixedSubgroup b).map (a⁻¹ : MulAut G).toMonoidHom = fixedSubgroup (a⁻¹ * b * a) := by
  ext y
  simp only [Subgroup.mem_map, mem_fixedSubgroup, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp [MulAut.mul_apply, hz]
  · intro hy
    refine ⟨a y, ?_, by simp⟩
    have := congrArg a hy
    simpa [MulAut.mul_apply] using this

theorem map_fixedSubgroup_transAut {K N : Type} [Group K] [Group N] (ψ : K ≃* N) (β : K ≃* K) :
    (fixedSubgroup β).map ψ.toMonoidHom = fixedSubgroup (transAut ψ β) := by
  ext y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  simp only [Subgroup.mem_map, mem_fixedSubgroup, MulEquiv.coe_toMonoidHom, transAut_apply]
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain rfl := ψ.injective hzx
    rw [hz]
  · intro h
    exact ⟨x, ψ.injective h, rfl⟩

variable {F : Type} [Field F] [Finite F]

theorem pGammaL2ToMulAutPSL2_eq_mul (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (x : PGammaL2 F) :
    pGammaL2ToMulAutPSL2 F hK hcard x =
      pgl2InnerAutPSL2 F hK hcard x.left * psl2FieldAut F x.right := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr]

theorem inner_of_field_part_trivial
    (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hdih : HasDihedralSylowTwo (PSL2 F)) (P : Sylow 2 (PSL2 F)) (β' : MulAut (PSL2 F))
    (hP : ∀ t ∈ (P : Subgroup (PSL2 F)), β' t = t) (g : PGL2 F)
    (hβ' : β' = pgl2InnerAutPSL2 F hK hcard g) : β' ∈ inner (PSL2 F) := by
  obtain ⟨m, hm, ⟨eP⟩⟩ := hdih P
  obtain ⟨V, hVP, hV⟩ :=
    exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (P : Subgroup (PSL2 F)) hm eP
  let toPGL : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP' : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 F hK hcard g v = v := by
      rw [← hβ']
      exact hP v (hVP hv)
    have h2 := toPGL_pgl2InnerAutPSL2_apply F hK hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self F hK _ hVP'] at hgC
  obtain ⟨g0, -, hg0⟩ := hgC
  refine ⟨g0, ?_⟩
  rw [hβ', ← hg0]
  exact (pgl2InnerAutPSL2_toPGL F hK hcard g0).symm

end Assembly

theorem oddAutInner_psl2
    {K : Type} [Group K] [Finite K] {p f : ℕ} (hp2 : p ≠ 2)
    (hf : f = 1 ∨ f = 2) (hmodel : StatedClassicalModel K .PSL 2 p f)
    (hno : ¬ Nonempty (K ≃* alternatingGroup (Fin 6))) (β : K ≃* K) (hβ : ∀ x, β (β x) = x)
    (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t)
    (hC : CharTwo (fixedSubgroup β)) : IsInnerAut β := by
  classical
  have hp : p.Prime := hmodel.1.1
  obtain ⟨F, _, _, _, e, hq, hF, hq5⟩ := psl2_model_data hp2 hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hf0 : 0 < f := by rcases hf with rfl | rfl <;> norm_num
  have hKcard : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card]; exact hq
  have hF' : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf0, hKcard⟩
  have hcard3 : 3 < Nat.card F := by rw [Nat.card_eq_fintype_card]; omega
  have hcharF : CharP F p := charP_of_card_eq_prime_pow (f := f) hq
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have hp3 : p = 3 := by
      have h2 := hp.two_le
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      omega
    subst hp3
    rcases hf with rfl | rfl
    · simp at hq
      omega
    · have hK9 : Fintype.card F = 9 := by rw [hq]; norm_num
      obtain ⟨e9⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
          F hK9
      exact hno ⟨e.trans e9⟩
  let ψ : K ≃* PSL2 F := e
  have hβ'2 : transAut ψ β * transAut ψ β = 1 := transAut_mul_self ψ β hβ
  obtain ⟨P, hP⟩ := hP
  obtain ⟨P', hP'coe⟩ : ∃ P' : Sylow 2 (PSL2 F),
      (P' : Subgroup (PSL2 F)) = (P : Subgroup K).map ψ.toMonoidHom :=
    ⟨P.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, rfl⟩
  have hP' : ∀ t ∈ (P' : Subgroup (PSL2 F)), transAut ψ β t = t := by
    intro t ht
    rw [hP'coe] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change transAut ψ β (ψ s) = ψ s
    rw [transAut_apply, hP s hs]
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hF' hcard3 (transAut ψ β)
  have hdih : HasDihedralSylowTwo (PSL2 F) := psl2_odd_hasDihedralSylowTwo_model F hF'
  by_cases hσ : x.right = 1
  · have hβx : transAut ψ β = pgl2InnerAutPSL2 F hF' hcard3 x.left := by
      rw [← hx, pGammaL2ToMulAutPSL2_eq_mul, hσ, map_one, mul_one]
    exact isInnerAut_of_transAut_mem_inner ψ β
      (inner_of_field_part_trivial hF' hcard3 hdih P' (transAut ψ β) hP' x.left hβx)
  · exfalso
    have hx2 : x * x = 1 := by
      apply pGammaL2ToMulAutPSL2_injective F hF' hcard3
      rw [map_mul, hx, hβ'2, map_one]
    have hxne : x ≠ 1 := fun h => hσ (by rw [h]; rfl)
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [sq]) hxne
    obtain ⟨C, hCx⟩ := pGammaL2_involution_conj_inr hF' x hord hσ
    have hconj : (pgl2InnerAutPSL2 F hF' hcard3 C)⁻¹ * transAut ψ β *
        pgl2InnerAutPSL2 F hF' hcard3 C = psl2FieldAut F x.right := by
      have := congrArg (pGammaL2ToMulAutPSL2 F hF' hcard3) hCx
      simpa [map_mul, map_inv, hx] using this
    have h1 : CharTwo (fixedSubgroup (transAut ψ β)) := by
      have := charTwo_map_mulEquiv ψ hC
      rwa [map_fixedSubgroup_transAut] at this
    have h2 : CharTwo (fixedSubgroup (psl2FieldAut F x.right)) := by
      have := charTwo_map_mulEquiv (pgl2InnerAutPSL2 F hF' hcard3 C)⁻¹ h1
      rwa [map_fixedSubgroup_conj, hconj] at this
    exact not_charTwo_fixedSubgroup_psl2FieldAut x.right hp5 h2

@[expose] def OddDegreeThreeAutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → p ≠ 2 →
    (StatedClassicalModel K .PSL 3 p 1 ∨ StatedClassicalModel K .PSU 3 p 1) →
    ∀ β : K ≃* K, (∀ x, β (β x) = x) → (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) →
      CharTwo (fixedSubgroup β) → IsInnerAut β

theorem oddAutInner_of
    (h : OddDegreeThreeAutInner) : OddAutInner := by
  intro K _ _ hK h6 β hβ hP hC
  obtain ⟨p, hp, hp2, hcases⟩ := hK
  rcases hcases with ⟨f, hf, hm⟩ | hm | hm
  · exact oddAutInner_psl2 hp2 hf hm h6 β hβ hP hC
  · exact h K p hp hp2 (Or.inl hm) β hβ hP hC
  · exact h K p hp hp2 (Or.inr hm) β hβ hP hC

end CFSG.QuasithinUnique.Ch1
