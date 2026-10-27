module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOvoid
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_15
public import Certificates.Certificate43
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Omega" => {p : Projectivization K (Fin 4 → K) // p ∈ suzukiOvoidSet m}

local instance : MulAction SzG Omega := suzukiOvoidAction m

@[expose] def suzukiDerangement (g : SzG) : Prop := ∀ a : Omega, g • a ≠ a

theorem suzuki_derangement_ne_one (g : SzG) (hg : suzukiDerangement m g) : g ≠ 1 := by
  intro h
  apply hg (⟨suzukiOvoidInfinity m, Or.inl rfl⟩ : Omega)
  rw [h, one_smul]

theorem suzuki_derangement_conjugate (g : SzG) (hg : suzukiDerangement m g) (s : SzG) :
    suzukiDerangement m ((MulAut.conj s) g) := by
  intro a ha
  apply hg (s⁻¹ • a)
  have h := congrArg (fun b : Omega => s⁻¹ • b) ha
  simpa only [MulAut.conj_apply, mul_smul, inv_smul_smul] using h

theorem suzuki_derangement_order_dvd (hm : 0 < m) (g : SzG)
    (hg : suzukiDerangement m g) : orderOf g ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let x : Subgroup.centralizer ({g} : Set SzG) :=
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hx : orderOf g ∣ Nat.card (Subgroup.centralizer ({g} : Set SzG)) :=
    Subgroup.orderOf_coe x ▸ orderOf_dvd_natCard x
  exact hx.trans (suzuki_ovoid_derangement_full_centralizer_card_dvd m hm g hg)

theorem suzuki_derangement_centralizer_member (hm : 0 < m) (g : SzG)
    (hg : suzukiDerangement m g) (c : SzG)
    (hc : c ∈ Subgroup.centralizer ({g} : Set SzG)) (hc1 : c ≠ 1) :
    suzukiDerangement m c := by
  intro a ha
  have h := suzuki_ovoid_derangement_full_centralizer_free m hm g hg
    (⟨c, hc⟩ : Subgroup.centralizer ({g} : Set SzG)) a ha
  exact hc1 (congrArg Subtype.val h)

theorem suzuki_derangement_centralizer_exact (hm : 0 < m) (g : SzG)
    (hg : suzukiDerangement m g) (c : SzG)
    (hc : c ∈ Subgroup.centralizer ({g} : Set SzG)) (hc1 : c ≠ 1) :
    Subgroup.centralizer ({c} : Set SzG) = Subgroup.centralizer ({g} : Set SzG) := by
  have hcg : Commute c g := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcDer := suzuki_derangement_centralizer_member m hm g hg c hc hc1
  have comm (x : SzG) (hx : suzukiDerangement m x)
      (a b : SzG) (ha : a ∈ Subgroup.centralizer ({x} : Set SzG))
      (hb : b ∈ Subgroup.centralizer ({x} : Set SzG)) : Commute a b := by
    have H := suzuki_degree_divisor_centralizer_commutative m x
      (suzuki_derangement_ne_one m x hx) (suzuki_derangement_order_dvd m hm x hx)
    exact congrArg Subtype.val ((@IsMulCommutative.is_comm
      (Subgroup.centralizer ({x} : Set SzG)) _ H).comm
      (⟨a, ha⟩ : Subgroup.centralizer ({x} : Set SzG)) ⟨b, hb⟩)
  apply le_antisymm
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (comm c hcDer a g ha (Subgroup.mem_centralizer_singleton_iff.mpr hcg.symm))
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm g hg a c ha hc)

theorem suzuki_derangement_centralizer_hall (hm : 0 < m) (g : SzG)
    (hg : suzukiDerangement m g) :
    Nat.Coprime (Nat.card (Subgroup.centralizer ({g} : Set SzG)))
      (Subgroup.centralizer ({g} : Set SzG)).index :=
  xi1115_centralizer_card_coprime_index_core _
    (suzuki_derangement_centralizer_exact m hm g hg)

theorem suzuki_derangement_centralizer_TI (hm : 0 < m) (g : SzG)
    (hg : suzukiDerangement m g) (s : SzG)
    (hs : s ∉ Subgroup.normalizer (Subgroup.centralizer ({g} : Set SzG) : Set SzG)) :
    Subgroup.centralizer ({g} : Set SzG) ⊓
      (Subgroup.centralizer ({g} : Set SzG)).map (MulAut.conj s).toMonoidHom = ⊥ :=
  xi1115_centralizer_TI_core g (suzuki_derangement_centralizer_exact m hm g hg) s hs

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
