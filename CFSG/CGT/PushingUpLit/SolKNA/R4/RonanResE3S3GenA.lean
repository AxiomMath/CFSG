module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenL3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenU3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.ClassicalInvolution.Q3.TL4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem gen_l3_of_normal {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    (hL3 : CFSG.ClassicalInvolution.Q3.TA3.SmallL3 ↥T) {z s : A} (hzT : z ∈ T)
    (hz2 : orderOf z = 2) (hcomm : z * s = s * z) (hsz : s ≠ z) (hconj : ∃ g : A, s = g * z * g⁻¹) :
    Subgroup.centralizer ({z} : Set A) ⊔ Subgroup.centralizer ({s} : Set A) = ⊤ := by
  obtain ⟨p, f, hp, hp2, -, hm⟩ := hL3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
    (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel ↥T .PSL 3 p f)
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨g, hg⟩ := hconj
  have hsT : s ∈ T := by
    rw [hg]
    exact Subgroup.Normal.conj_mem inferInstance z hzT g
  have hs2 : orderOf s = 2 := by
    rw [hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz2
  exact E3S3Gen.sup_centralizer_eq_top_of_normal e
    (fun a b ha hb hab hab' => E3C269G.sup_centralizer_eq_top_psl3 hodd ha hb hab hab')
    (fun a b ha hb => E3S3Gen.exists_conj_psl3 hodd ha hb) hzT hsT hz2 hs2 hcomm hsz

theorem gen_u3_of_normal {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    (hU3 : CFSG.ClassicalInvolution.Q3.TA3.SmallU3 ↥T) {z s : A} (hzT : z ∈ T)
    (hz2 : orderOf z = 2) (hcomm : z * s = s * z) (hsz : s ≠ z) (hconj : ∃ g : A, s = g * z * g⁻¹) :
    Subgroup.centralizer ({z} : Set A) ⊔ Subgroup.centralizer ({s} : Set A) = ⊤ := by
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hU3
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨g, hg⟩ := hconj
  have hsT : s ∈ T := by
    rw [hg]
    exact Subgroup.Normal.conj_mem inferInstance z hzT g
  have hs2 : orderOf s = 2 := by
    rw [hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz2
  exact E3S3Gen.sup_centralizer_eq_top_of_normal e
    (fun a b ha hb hab hab' => E3C269G.sup_centralizer_eq_top_psu3 h hp2 ha hb hab hab')
    (fun a b ha hb => E3S3Gen.exists_conj_psu3 h hp2 ha hb) hzT hsT hz2 hs2 hcomm hsz

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
