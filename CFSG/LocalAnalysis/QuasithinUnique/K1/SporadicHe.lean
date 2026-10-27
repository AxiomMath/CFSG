module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.Sporadic.He
public meta import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
public import Certificates.Certificate4141
public import Certificates.Certificate3168
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.Sporadic.He
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem he_eq_one_of_fix_base (g : J)
    (hg : ∀ i < Native.chainBase.size,
      CFSG.Sporadic.Th.idx 8330 g Native.chainBase[i]! = Native.chainBase[i]!) : g = 1 := by
  have key : ∀ i ≤ Native.chainBase.size, g ∈ lvl i := by
    intro i
    induction i with
    | zero => intro _; rw [lvl_zero]; exact Subgroup.mem_top g
    | succ i ih =>
      intro hi
      exact (chain_facts'.2.1 i (by omega) g (ih (by omega))).1 (hg i (by omega))
  have hcard : Nat.card (lvl Native.chainBase.size) = 1 := by
    rw [chain_facts'.2.2 Native.chainBase.size le_rfl]; simp
  have hbot : lvl Native.chainBase.size = ⊥ := Subgroup.card_eq_one.mp hcard
  have hg' := key Native.chainBase.size le_rfl
  rw [hbot] at hg'
  exact Subgroup.mem_bot.mp hg'

theorem he_base_lt : ∀ b ∈ Native.chainBase.toList, b < 8330 := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < Native.chainBase.size := by simpa using hi
  have := (chain_facts'.1 i hi').r_lt
  simpa [getElem!_pos Native.chainBase i hi'] using this

theorem he_base_property :
    ∀ g : J, (∀ b ∈ Native.chainBase.toList, act 8330 g b = b) → g = 1 := by
  intro g hg
  apply he_eq_one_of_fix_base
  intro i hi
  have hb : Native.chainBase[i]! < 8330 := (chain_facts'.1 i hi).r_lt
  have hmem : Native.chainBase[i]! ∈ Native.chainBase.toList := by
    rw [getElem!_pos Native.chainBase i hi]
    exact Array.getElem_mem_toList hi
  rw [CFSG.Sporadic.Th.idx_of_lt g hb]
  have h1 := hg _ hmem
  have h2 : act 8330 g Native.chainBase[i]! = (g • (⟨Native.chainBase[i]!, hb⟩ : Fin 8330)).val :=
    act_eq g ⟨Native.chainBase[i]!, hb⟩
  rw [h2] at h1
  exact h1

theorem he_valid : slpValidAux heProg 2 = true :=
  Certificates.certificate4141.1

theorem he_cert :
    BaseCertS 8330 heB heSLP heQp 170 249 253 251 255
      heEnum.1 heEnum.2.1 heEnum.2.2 10 :=
  Certificates.certificate4141.2

theorem he_group_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian J := by
  have ha : tab 8330 (a : J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (a : J) rep_alpha]
    simp [heTa, orb]
  have hb : tab 8330 (b : J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (b : J) rep_beta]
    simp [heTb, orb]
  refine noStronglyClosedElemAbelian_of_baseCertS (n := 8330) heB he_base_lt he_base_property
    (a : J) (b : J) heProg he_valid heQp 170 249 253 251 255 heEnum.1 heEnum.2.1
    heEnum.2.2 10 3935925 (by rw [card_J]; norm_num) (by decide) ?_
  rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
  exact he_cert

theorem he_noStronglyClosedElemAbelian : NoStronglyClosedElemAbelian (Carrier .He) := by
  have h : NoStronglyClosedElemAbelian CFSG.Blueprint.NativeSporadic.He :=
    NoStronglyClosedElemAbelian.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.He) (Y := ↥J)
      heEquivJ he_group_noStronglyClosedElemAbelian
  exact h

end CFSG.QuasithinUnique.K1.SporadicPerm
