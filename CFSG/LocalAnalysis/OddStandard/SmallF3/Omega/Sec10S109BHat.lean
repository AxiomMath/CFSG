module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JWb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}

theorem sec10B_hatCent_normalizes_W (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10Ctx G t L S z K1 K2) {c : G} (hc : c ∈ hatCent t z) :
    c ∈ normalizer ((secW t K1 K2 : Subgroup G) : Set G) := by
  obtain ⟨ht2, hz2, ht1, -, hne, htz⟩ := sec10D_basic hb hctx
  obtain ⟨hzW, -⟩ := sec10J_W_elem hf.pockets5 hf.centZ5 hb hctx
  have hK0 := sec10D_hatCent_normalizes_K0 h.lK0 hctx ht2 hz2 htz ht1 hne hc
  have hD := sec10A2_split h3 h hf hb hctx
  have hQ : ∀ x ∈ secQ K1 K2, c * x * c⁻¹ ∈ secQ K1 K2 := by
    intro x hx
    have hxK0 : x ∈ secK0 t z := hD.right_le (twoCoreIn_le_self _ hx)
    refine sec10T_two_elem_K0 h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb hctx (hK0 x hxK0) ?_
    obtain ⟨m, hm⟩ := isPGroup_twoCoreIn (K1 ⊔ K2) ⟨x, hx⟩
    refine ⟨m, ?_⟩
    have hm' : x ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    rw [conj_pow, hm']
    group
  have hct : c * t * c⁻¹ ∈ secW t K1 K2 := by
    have htW : t ∈ secW t K1 K2 := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rcases sec10D_hatCent_conj ht2 hz2 htz ht1 hne hc with h1 | h1
    · rw [h1]
      exact htW
    · rw [h1]
      exact (secW t K1 K2).mul_mem htW hzW
  refine sec10A2_mem_normalizer_of_map_le fun x hx => ?_
  refine sec10A2_conj_sup_le (fun q hq => Subgroup.mem_sup_left (hQ q hq)) (fun y hy => ?_) x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hct n

theorem sec10B_conjugate_eq_of_conj_t (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hb : Asc82Basic10) (hctx : Sec10Ctx G t L S z K1 K2) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hct : c * t * c⁻¹ = t ∨ c * t * c⁻¹ = t * z) :
    CFSG.conjugate (secW t K1 K2) c = secW t K1 K2 :=
  sec10B_conjugate_eq
    (sec10B_hatCent_normalizes_W h3 h hf hb hctx (sec10D_mem_hatCent hc hct))

end CFSG.OddStandard.SmallF3.Omega
