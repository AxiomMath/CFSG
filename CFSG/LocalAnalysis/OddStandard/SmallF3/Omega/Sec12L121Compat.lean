module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec121_f_inv (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    sec12f t p⁻¹ = (sec12f t p)⁻¹ := by
  have h1 : sec12f t (p⁻¹ * p) = sec12f t p⁻¹ * sec12f t p :=
    sec12E_f_mul F ((secCMB t S L).inv_mem hp) hp
  rw [inv_mul_cancel] at h1
  have h0 : sec12f t 1 = 1 := by simp [sec12f]
  exact eq_inv_of_mul_eq_one_left (h0 ▸ h1).symm

theorem sec121_prince_compat (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {φ φ' : (Fin 5 → ZMod 2) → G} (hφ'V : ∀ v, IsEvenVec v → φ' v ∈ secV t S L E)
    (hφ'f : ∀ v, IsEvenVec v → sec12f t (φ' v) = φ v) :
    ∀ h ∈ secM t S L ⊓ L, ∀ σ ∈ alternatingGroup (Fin 5),
      (∀ v, IsEvenVec v → (h * φ' v * h⁻¹)⁻¹ * φ' (permVec σ v) ∈ secB S L) →
        ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v) := by
  intro h hh σ _ hσ v hv
  have hVE := sec121_V_le_E F hE
  have hx : h * φ' v * h⁻¹ ∈ secV t S L E :=
    (Subgroup.mem_normalizer_iff.mp (sec121_Y_le_normalizer_V F hE hh) _).1 (hφ'V v hv)
  have hx' : φ' (permVec σ v) ∈ secV t S L E := hφ'V _ (isEvenVec_permVec σ hv)
  have hxE : h * φ' v * h⁻¹ ∈ E := hVE hx
  have hx'E : φ' (permVec σ v) ∈ E := hVE hx'
  have hbA : (h * φ' v * h⁻¹)⁻¹ * φ' (permVec σ v) ∈ secA t S L :=
    Subgroup.mem_sup_left (hσ v hv)
  have h1 : sec12f t ((h * φ' v * h⁻¹)⁻¹ * φ' (permVec σ v)) = 1 :=
    (sec120_f_eq_one_iff F hE (E.mul_mem (E.inv_mem hxE) hx'E)).2 hbA
  rw [sec12E_f_mul F (hE.1 (E.inv_mem hxE)) (hE.1 hx'E), sec121_f_inv F (hE.1 hxE)] at h1
  have h2 : sec12f t (h * φ' v * h⁻¹) = sec12f t (φ' (permVec σ v)) := inv_mul_eq_one.mp h1
  rw [sec12E_f_conj (Subgroup.mem_centralizer_iff.mp F.htC h hh.2), hφ'f v hv,
    hφ'f _ (isEvenVec_permVec σ hv)] at h2
  exact h2

end CFSG.OddStandard.SmallF3.Omega
