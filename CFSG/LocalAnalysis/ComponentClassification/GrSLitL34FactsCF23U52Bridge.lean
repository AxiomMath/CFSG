module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Action
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Certificates.Certificate22229
import all CFSG.Fischer.F4

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Fischer CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

theorem matA_unitary : (matA.map (· ^ 2))ᵀ * matA = 1 := by decide +kernel
theorem matB_unitary : (matB.map (· ^ 2))ᵀ * matB = 1 := by decide +kernel
theorem det_matA : matA.det = 1 := by decide +kernel
theorem det_matB : matB.det = 1 := by decide +kernel

noncomputable def suA : StatedSU 5 2 F4 :=
  ⟨GeneralLinearGroup.mk'' matA (by rw [det_matA]; exact isUnit_one),
    Subgroup.subset_closure ⟨det_matA, matA_unitary⟩⟩

noncomputable def suB : StatedSU 5 2 F4 :=
  ⟨GeneralLinearGroup.mk'' matB (by rw [det_matB]; exact isUnit_one),
    Subgroup.subset_closure ⟨det_matB, matB_unitary⟩⟩

noncomputable def xElt : X₀ := QuotientGroup.mk suA

noncomputable def yElt : X₀ := QuotientGroup.mk suB

theorem rep_tabA : Rep 341 tabA (psi xElt) := fun i => by
  rw [tabA, tabN_getElem!, xElt, psi_mk_apply]
  rfl

theorem rep_tabB : Rep 341 tabB (psi yElt) := fun i => by
  rw [tabB, tabN_getElem!, yElt, psi_mk_apply]
  rfl

noncomputable def chainQ : RawSchreierDatum 341 :=
  RawSchreierDatum.ofArrays 341 (by norm_num) chainS 2 (by decide) chainBase (by decide) chainW

theorem chain_check :
    rawChainOK 341 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true :=
  Certificates.certificate22229.1

theorem chain_orbits :
    (rawOrbitSizes 341 chainS (chainBase.map Fin.val).toArray).prod = 13685760 :=
  Certificates.certificate22229.2

private theorem eq_of_rep {n : ℕ} {t : Array ℕ} {g g' : Equiv.Perm (Fin n)}
    (h : Rep n t g) (h' : Rep n t g') : g = g' :=
  Equiv.ext fun i => Fin.ext (by rw [← h i, ← h' i])

theorem chainArrays_chainQ :
    ChainArrays chainQ (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW :=
  chainArrays_ofArrays (chainCheckFacts chain_check).strong_inv

theorem card_chainQ :
    Nat.card chainQ.originalSubgroup = 13685760 := by
  rw [card_originalSubgroup_of_chainOK chainArrays_chainQ (by norm_num) chain_check, chain_orbits]

noncomputable def u52P : Subgroup (Equiv.Perm (Fin 341)) := closure {psi xElt, psi yElt}

theorem chainQ_eq : chainQ.originalSubgroup = u52P := by
  rw [RawSchreierDatum.originalSubgroup, u52P]
  congr 1
  ext g
  simp only [chainQ, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have h0 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 0 (by decide))).1
  have h1 := (rep_permOfArr ((chainCheckFacts chain_check).strong_inv 1 (by decide))).1
  have hS0 : chainS[0]! = tabA := by
    simp only [chainS, List.getElem!_toArray, List.getElem!_cons_zero]
  have hS1 : chainS[1]! = tabB := by
    simp only [chainS, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
  rw [hS0] at h0
  rw [hS1] at h1
  have e0 : permOfArr 341 chainS[0]! = psi xElt := by rw [hS0]; exact eq_of_rep h0 rep_tabA
  have e1 : permOfArr 341 chainS[1]! = psi yElt := by rw [hS1]; exact eq_of_rep h1 rep_tabB
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem card_X₀ : Nat.card X₀ = 13685760 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F4) (p := 2) (f := 1)
    (n := 5) Nat.prime_two le_rfl (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num)
    (by norm_num)
  rw [pow_one] at h
  rw [X₀, h]
  decide

theorem card_u52P : Nat.card u52P = 13685760 := by
  rw [← chainQ_eq, card_chainQ]

instance : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)

theorem closure_xy :
    closure ({xElt, yElt} : Set X₀) = ⊤ := by
  apply Subgroup.eq_top_of_le_card
  have hmap : (closure ({xElt, yElt} : Set X₀)).map psi = u52P := by
    rw [MonoidHom.map_closure, Set.image_pair, u52P]
  rw [card_X₀, ← card_u52P, ← hmap]
  exact Nat.card_le_card_of_surjective _ (psi.subgroupMap_surjective _)

theorem range_psi : psi.range = u52P := by
  rw [MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair, u52P]

theorem psi_injective : Function.Injective psi := by
  have hle : Nat.card X₀ ≤ Nat.card psi.range := by
    rw [card_X₀, range_psi, card_u52P]
  have hb := psi.rangeRestrict_surjective.bijective_of_nat_card_le hle
  exact fun g h hgh => hb.1 (Subtype.ext hgh)

end CFSG.ComponentClassification.GSThmB.U52
