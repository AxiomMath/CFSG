module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6 CFSG
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.QuasithinUnique
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isNaturalAltModule_of_isNatAlt {F : Subgroup Γ} {m : ℕ} (hchar : CharTwo F)
    (hW : ∀ x ∈ pCoreOf 2 F, ∀ y ∈ pCoreOf 2 F, x * y = y * x)
    (hperf : ⁅pCoreOf 2 F, F⁆ = pCoreOf 2 F) (hnat : IsNatAlt F (pCoreOf 2 F) (2 * m + 1)) :
    IsNaturalAltModule ↥F m := by
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  let eU := shortUEquiv hperf
  have hpc : CFSG.pCore 2 ↥F = φ.ker := by
    rw [hφk]
    exact pCore_eq_inf_centralizer hchar hW
  let φ' : (↥F ⧸ CFSG.pCore 2 ↥F) ≃* alternatingGroup (Fin (2 * m + 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hφ' : ∀ l : ↥F, φ' (l : ↥F ⧸ CFSG.pCore 2 ↥F) = φ l := fun l => rfl
  let ψ' : ↥(shortU ↥F) →* Multiplicative (Fin (2 * m + 1) → ZMod 2) :=
    ((coreMod (2 * m + 1)).subtype).comp (ψ.comp eU.toMonoidHom)
  have hψ' : ∀ u : ↥(shortU ↥F), ψ' u = ((ψ (eU u) : ↥(coreMod (2 * m + 1))) :
      PermMod (2 * m + 1)) := fun u => rfl
  refine ⟨φ', ψ', fun u => ?_, fun v hv => ?_, ?_, ?_⟩
  · rw [hψ']
    exact (ψ (eU u)).2
  · obtain ⟨w, hw⟩ := hψs ⟨Multiplicative.ofAdd v, hv⟩
    refine ⟨eU.symm w, ?_⟩
    rw [hψ', MulEquiv.apply_symm_apply, hw]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ' u = 1 ↔ ψ (eU u) = 1 := by
      rw [hψ']
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    have h2 : ψ (eU u) = 1 ↔ eU u ∈ ψ.ker := MonoidHom.mem_ker.symm
    have hcoe : (((eU u : ↥(pCoreOf 2 F)) : Γ)) = (((u : ↥(shortU ↥F)) : ↥F) : Γ) :=
      shortUEquiv_coe hperf u
    rw [h1, h2, hψk, Subgroup.mem_subgroupOf, hcoe, mem_shortC_iff hperf]
  · intro l u hu hu'
    set uu : ↥(shortU ↥F) := ⟨u, hu⟩ with huu
    have hu1 : ((eU uu : ↥(pCoreOf 2 F)) : Γ) = (u : Γ) := shortUEquiv_coe hperf uu
    have hw : (l : Γ) * (eU uu : Γ) * (l : Γ)⁻¹ ∈ pCoreOf 2 F := by
      rw [hu1]
      have := (mem_shortU_iff hperf (l * u * l⁻¹)).1 hu'
      simpa using this
    have hsub : eU ⟨l * u * l⁻¹, hu'⟩ = ⟨(l : Γ) * (eU uu : Γ) * (l : Γ)⁻¹, hw⟩ := by
      apply Subtype.ext
      show ((l * u * l⁻¹ : ↥F) : Γ) = (l : Γ) * ((eU uu : ↥(pCoreOf 2 F)) : Γ) * (l : Γ)⁻¹
      rw [hu1]
      rfl
    rw [hψ' ⟨l * u * l⁻¹, hu'⟩, hsub, hψe l (eU uu) hw, hφ' l, hψ' uu]
    rfl

theorem oResidualTwo_eq_top_of_opResidual {F : Subgroup Γ} (h : opResidual 2 F = F) :
    oResidualTwo ↥F = ⊤ := by
  rw [oResidualTwo_eq_top_iff]
  intro N hN hpow
  have key : ∀ g : Γ, ∀ hg : g ∈ opResidual 2 F, (⟨g, opResidual_le 2 F hg⟩ : ↥F) ∈ N := by
    intro g hg
    unfold opResidual at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyF, hcop⟩ := hy
      obtain ⟨k, hk⟩ := hpow ⟨y, hyF⟩
      have hcop' : (2 ^ k).Coprime (orderOf (⟨y, hyF⟩ : ↥F)) := by
        rw [Subgroup.orderOf_mk]
        exact Nat.Coprime.pow_left k hcop.symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
      rw [← hm]
      exact N.pow_mem hk m
    | one => exact N.one_mem
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, opResidual_le 2 F (mul_mem hy hz)⟩ : ↥F) =
          ⟨y, opResidual_le 2 F hy⟩ * ⟨z, opResidual_le 2 F hz⟩ := rfl
      rw [e]
      exact N.mul_mem ihy ihz
    | inv y hy ihy =>
      have e : (⟨y⁻¹, opResidual_le 2 F (inv_mem hy)⟩ : ↥F) =
          (⟨y, opResidual_le 2 F hy⟩ : ↥F)⁻¹ := rfl
      rw [e]
      exact N.inv_mem ihy
  refine eq_top_iff.2 fun x _ => ?_
  exact key x (by rw [h]; exact x.2)

end CFSG.CGT.PushingUpLit.BHS6
