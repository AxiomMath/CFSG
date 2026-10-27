module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenCommon
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.RankThree.PartOne.N143.O7
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Blueprint.MatrixSeedIdentification
public import Certificates.Certificate9437
public import Certificates.Certificate9438

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.AGLEmbedding.R3.O73Three CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.Blueprint
open CFSG.LieType.Multipliers.O73 (Idx idx code dec tabOf)
open CFSG.RankThree.PartOne.N143.O7 (Om Iso gramM mem_iso_of_gram mem_om_of_inverted modelEquiv)
open Matrix

namespace O73

theorem matA_cube : matA * (matA * matA) = 1 := by decide +kernel

theorem matA_cube' : (matA * matA) * matA = 1 := by decide +kernel

theorem matB_cube : matB * (matB * matB) = 1 := by decide +kernel

theorem matB_cube' : (matB * matB) * matB = 1 := by decide +kernel

theorem matHA_inv : matHA * matHAinv = 1 := by decide +kernel

theorem matHA_inv' : matHAinv * matHA = 1 := by decide +kernel

theorem matHB_inv : matHB * matHBinv = 1 := by decide +kernel

theorem matHB_inv' : matHBinv * matHB = 1 := by decide +kernel

@[expose] def gA : GL Idx (ZMod 3) := ⟨matA, matA * matA, matA_cube, matA_cube'⟩

@[expose] def gB : GL Idx (ZMod 3) := ⟨matB, matB * matB, matB_cube, matB_cube'⟩

@[expose] def hA : GL Idx (ZMod 3) := ⟨matHA, matHAinv, matHA_inv, matHA_inv'⟩

@[expose] def hB : GL Idx (ZMod 3) := ⟨matHB, matHBinv, matHB_inv, matHB_inv'⟩

theorem gram_A : matAᵀ * gramM * matA = gramM := by decide +kernel

theorem gram_B : matBᵀ * gramM * matB = gramM := by decide +kernel

theorem gram_HA : matHAᵀ * gramM * matHA = gramM := by decide +kernel

theorem gram_HB : matHBᵀ * gramM * matHB = gramM := by decide +kernel

theorem inv_A : matHA * matA = matA * matA * matHA := by decide +kernel

theorem inv_B : matHB * matB = matB * matB * matHB := by decide +kernel

theorem gA_mem : gA ∈ Om :=
  mem_om_of_inverted (mem_iso_of_gram (A := gA) gram_A) (mem_iso_of_gram (A := hA) gram_HA)
    (Units.ext inv_A)

theorem gB_mem : gB ∈ Om :=
  mem_om_of_inverted (mem_iso_of_gram (A := gB) gram_B) (mem_iso_of_gram (A := hB) gram_HB)
    (Units.ext inv_B)

@[expose] def oA : ↥Om := ⟨gA, gA_mem⟩

@[expose] def oB : ↥Om := ⟨gB, gB_mem⟩

theorem code_lt (v : Idx → ZMod 3) : code v < 2187 := by
  have h : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt (v i)
  have := h (.inl 0); have := h (.inl 1); have := h (.inl 2)
  have := h (.inr (.inl 0)); have := h (.inr (.inl 1)); have := h (.inr (.inl 2))
  have := h (.inr (.inr ()))
  unfold code
  omega

theorem code_dec_all : ∀ x : Fin 2187, code (dec x) = x := by decide +kernel

theorem dec_injective : Function.Injective fun x : Fin 2187 => dec x := by
  intro x y h
  have hx := code_dec_all x
  have hy := code_dec_all y
  simp only at h
  rw [h] at hx
  exact Fin.ext (hx.symm.trans hy)

theorem dec_surjective : Function.Surjective fun x : Fin 2187 => dec x := by
  have hcard : Nat.card (Idx → ZMod 3) ≤ Nat.card (Fin 2187) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  exact (dec_injective.bijective_of_nat_card_le hcard).2

theorem dec_code (v : Idx → ZMod 3) : dec (code v) = v := by
  obtain ⟨x, rfl⟩ := dec_surjective v
  simp only
  rw [code_dec_all x]

@[expose] noncomputable def cE : (Idx → ZMod 3) ≃ Fin 2187 where
  toFun v := ⟨code v, code_lt v⟩
  invFun x := dec x
  left_inv v := dec_code v
  right_inv x := Fin.ext (code_dec_all x)

@[expose] noncomputable def psi : GL Idx (ZMod 3) →* Equiv.Perm (Fin 2187) :=
  (Equiv.permCongrHom cE).toMonoidHom.comp (MulAction.toPermHom (GL Idx (ZMod 3)) (Idx → ZMod 3))

theorem psi_apply (A : GL Idx (ZMod 3)) (x : Fin 2187) :
    ((psi A x : Fin 2187) : ℕ) = code ((A : Matrix Idx Idx (ZMod 3)) *ᵥ dec x) := rfl

theorem rep_tabOf {A : GL Idx (ZMod 3)} {M : Matrix Idx Idx (ZMod 3)}
    (hA : (A : Matrix Idx Idx (ZMod 3)) = M) : Rep 2187 (tabOf M) (psi A) := fun x => by
  rw [tabOf, getElem!_ofFn_nat _ x.2, psi_apply, hA]

noncomputable def chainQ : RawSchreierDatum 2187 :=
  RawSchreierDatum.ofArrays 2187 (by norm_num) chainS 2 (by decide +kernel) chainBase
    (by decide) chainW

theorem chain_check :
    rawChainOK 2187 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true :=
  Certificates.certificate9437.1

theorem chain_orbits :
    (rawOrbitSizes 2187 chainS (chainBase.map Fin.val).toArray).prod = 4585351680 :=
  Certificates.certificate9437.2.1

theorem eq_of_rep {n : ℕ} {t : Array ℕ} {g g' : Equiv.Perm (Fin n)}
    (h : Rep n t g) (h' : Rep n t g') : g = g' :=
  Equiv.ext fun i => Fin.ext (by rw [← h i, ← h' i])

theorem card_chainQ :
    Nat.card chainQ.originalSubgroup = 4585351680 := by
  rw [chainQ, card_originalSubgroup_of_chainOK
    (chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv) (by norm_num) chain_check,
    chain_orbits]

theorem chainQ_eq :
    chainQ.originalSubgroup = Subgroup.closure {psi gA, psi gB} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [chainQ, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have hS0 : chainS[0]! = tabA := by simp [chainS]
  have hS1 : chainS[1]! = tabB := by simp [chainS]
  rw [hS0] at h0
  rw [hS1] at h1
  have e0 : permOfArr 2187 chainS[0]! = psi gA := by
    rw [hS0]; exact eq_of_rep h0 (rep_tabOf (A := gA) (M := matA) rfl)
  have e1 : permOfArr 2187 chainS[1]! = psi gB := by
    rw [hS1]; exact eq_of_rep h1 (rep_tabOf (A := gB) (M := matB) rfl)
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem card_closure_psi :
    Nat.card (Subgroup.closure {psi gA, psi gB}) = 4585351680 := by
  rw [← chainQ_eq, card_chainQ]

theorem card_om : Nat.card ↥Om = 4585351680 := by
  have hK : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have h := CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC (K := ZMod 3)
    (p := 3) (f := 1) Nat.prime_three (by norm_num) (by rw [hK]; norm_num) (n := 3) le_rfl
  rw [Nat.card_congr (modelEquiv hK).toEquiv, pow_one] at h
  rw [h]
  decide

theorem closure_ab : Subgroup.closure ({oA, oB} : Set ↥Om) = ⊤ := by
  have : Finite ↥Om := Nat.finite_of_card_ne_zero (by rw [card_om]; norm_num)
  apply Subgroup.eq_top_of_le_card
  have hmap : (Subgroup.closure ({oA, oB} : Set ↥Om)).map (psi.comp Om.subtype) =
      Subgroup.closure {psi gA, psi gB} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [card_om, ← card_closure_psi, ← hmap]
  exact Nat.card_le_card_of_surjective _ ((psi.comp Om.subtype).subgroupMap_surjective _)

theorem closure_gAgB : Subgroup.closure {gA, gB} = Om := by
  have h := congrArg (Subgroup.map Om.subtype) closure_ab
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

@[expose] def e7 : Idx ≃ Fin 7 where
  toFun a := match a with
    | .inl k => ⟨k, by omega⟩
    | .inr (.inl k) => ⟨3 + k, by omega⟩
    | .inr (.inr _) => ⟨6, by omega⟩
  invFun := ![.inl 0, .inl 1, .inl 2, .inr (.inl 0), .inr (.inl 1), .inr (.inl 2), .inr (.inr ())]
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def rho : GL Idx (ZMod 3) ≃* GL (Fin 7) (ZMod 3) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 3) (ZMod 3) e7).toRingEquiv.toMulEquiv

theorem decode_seedA : NativeSporadic.decode 3 7 1 seedA = Matrix.reindex e7 e7 matA := by
  decide +kernel

theorem decode_seedB : NativeSporadic.decode 3 7 1 seedB = Matrix.reindex e7 e7 matB := by
  decide +kernel

theorem seedMonoid_eq_O73 :
    NativeSporadic.seedMonoid 3 7 1 seedA seedB =
      Submonoid.closure {((rho gA : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3)),
        ((rho gB : GL (Fin 7) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3))} := by
  unfold NativeSporadic.seedMonoid
  rw [decode_seedA, decode_seedB]
  rfl

theorem closure_rho :
    Subgroup.closure {rho gA, rho gB} = Om.map rho.toMonoidHom := by
  rw [← closure_gAgB, MonoidHom.map_closure, Set.image_pair]
  rfl

noncomputable def seedEquivO73 :
    (NativeSporadic.seedMonoid 3 7 1 seedA seedB)ˣ ≃* ↥Om := by
  rw [seedMonoid_eq_O73]
  exact (NativeSporadic.unitSeedEquiv (rho gA) (rho gB)).trans
    ((MulEquiv.subgroupCongr closure_rho).trans
      (Om.equivMapOfInjective rho.toMonoidHom rho.injective).symm)

end O73

theorem weakGenO73 : WeakGenO73 := by
  intro q hv hq
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  have hp2 : q.p ≠ 2 := by omega
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
    (G := (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) (MulEquiv.refl _)
  obtain ⟨-, K, _, _, hK3, ⟨eK⟩⟩ := hmodel
  have hK : Nat.card K = 3 := by rw [hK3, ← PrimePower.card_def]; exact hq
  have : Fact (Nat.Prime CFSG.AGLEmbedding.R3.O73Three.cpSpec.p) := ⟨by show Nat.Prime 3; norm_num⟩
  exact coverWeakGen_of_check (spec3 7) (D := CFSG.AGLEmbedding.R3.O73Three.cpSpec)
    (by show (3 : ℕ) ≠ 2; norm_num) Certificates.certificate9438.1
    Certificates.certificate9438.2 (O73.seedEquivO73.trans (eK.trans (modelEquiv hK)).symm)

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
