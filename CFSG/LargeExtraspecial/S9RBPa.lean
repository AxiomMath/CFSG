module

public import CFSG.LargeExtraspecial.S6Pkg
public import CFSG.LargeExtraspecial.S8Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_commSpace_le_two_mul {s : S.O} {P : Submodule (ZMod 2) S.Qt}
    (hsP : ∀ p ∈ P, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ P)
    (hP : LinearMap.BilinForm.orthogonal S.q.polarBilin P = P) :
    finrank (ZMod 2) (commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
      2 * finrank (ZMod 2) ↥(commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ P) := by
  set A := commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) with hA
  have hnd := S.q_nondegenerate
  have hfix : fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      LinearMap.BilinForm.orthogonal S.q.polarBilin A :=
    fixSpace_eq_orthogonal_commSpace_of_mem hnd s.2
  have hperp : ∀ X : Submodule (ZMod 2) S.Qt,
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin X) +
        finrank (ZMod 2) X = finrank (ZMod 2) S.Qt := by
    intro X
    have := LinearMap.BilinForm.finrank_orthogonal hnd X
    have := Submodule.finrank_le X
    omega
  have hsup : LinearMap.BilinForm.orthogonal S.q.polarBilin
      (P ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin A) = P ⊓ A := by
    have h1 := S8.perp_sup (q := S.q) P (LinearMap.BilinForm.orthogonal S.q.polarBilin A)
    have h2 := S8.perp_perp hnd A
    simp only [S2.perp] at h1 h2
    rw [h1, hP, h2]
  have d1 := hperp (P ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin A)
  rw [hsup] at d1
  have d2 := hperp A
  have d3 := Submodule.finrank_sup_add_finrank_inf_eq P
    (LinearMap.BilinForm.orthogonal S.q.polarBilin A)
  have d4 := S2.finrank_map_sub_one_add (s : S.Qt ≃ₗ[ZMod 2] S.Qt) P
  rw [hfix] at d4
  have hmap : P.map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤ A ⊓ P := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨sub_mem_commSpace _ p, sub_mem (hsP p hp) hp⟩
  have d5 := Submodule.finrank_mono hmap
  have e : finrank (ZMod 2) ↥(P ⊓ A) = finrank (ZMod 2) ↥(A ⊓ P) := by rw [inf_comm]
  omega

theorem two_le_finrank_commSpace_inf_clSub {g' : G} (H' : Hyp4 S g') (C' : Cons311 S g')
    {σ : S.O} (hσM : σ ∈ S.Mbar)
    (hfix : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g' * S.z * g'⁻¹)) = S.cl (g' * S.z * g'⁻¹))
    (h4 : finrank (ZMod 2) (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4) :
    2 ≤ finrank (ZMod 2)
      ↥(commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ S.clSub (S.QG ⊓ S.Qa g')) := by
  have := finrank_commSpace_le_two_mul (s := σ)
    (fun p hp => apply_mem_clSub_of_fix H'.conj_mem H'.conj_ne hσM hfix hp)
    (orthogonal_clSub_eq H'.conj_mem H'.conj_ne C'.card_QG_inf_Qa)
  omega

theorem four_mul_card_le {g' : G} (H' : Hyp4 S g') (C' : Cons311 S g') {t σ : S.O}
    (hA : Nat.card (S.Lbar g' ⊓ Nbar S g t : Subgroup S.O) * 8 = 2 ^ S.width)
    (hV3 : 3 ≤ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g') ⊓ Vt S g t))
    (hσ2 : 2 ≤ finrank (ZMod 2)
      ↥(commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ S.clSub (S.QG ⊓ S.Qa g')))
    (hinf : Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    4 * Nat.card ↥((S.Lbar g' ⊓ Nbar S g t) ⊓ (S2.fixGroup
      (commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ S.clSub (S.QG ⊓ S.Qa g'))).comap S.O.subtype) ≤
      Nat.card (S.Lbar g' ⊓ Nbar S g t : Subgroup S.O) := by
  set P := S.clSub (S.QG ⊓ S.Qa g') with hP
  set B := commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ P with hB
  set K := (S.Lbar g' ⊓ Nbar S g t) ⊓ (S2.fixGroup B).comap S.O.subtype with hK
  have h1 := card_mul_two_pow_finrank_fix H' C' (K := K) (inf_le_left.trans inf_le_left)
  have hle : (P ⊓ Vt S g t) ⊔ B ≤ P ⊓ fixSub S K := by
    refine sup_le (inf_le_inf_left _ fun v hv => (mem_fixSub S).mpr fun x hx =>
      (mem_Nbar.mp hx.1.2).2 v hv) (le_inf inf_le_right fun v hv => (mem_fixSub S).mpr
        fun x hx => S2.mem_fixGroup.mp hx.2 v hv)
  have hdisj : (P ⊓ Vt S g t) ⊓ B = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_left)
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ Vt S g t) B
  rw [hdisj, finrank_bot] at d1
  have d2 := Submodule.finrank_mono hle
  have h5 : 2 ^ 5 ≤ 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S K) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h6 : Nat.card K * 2 ^ 5 ≤ 2 ^ S.width := h1 ▸ Nat.mul_le_mul_left _ h5
  omega

theorem mem_zpowers_of_mem_Lbar_inf (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {x : S.O}
    (hx : x ∈ S.Lbar g) (hxb : x ∈ S.Lbar ((h : G) * g)) : x ∈ zpowers t := by
  have haQ := H.conj_mem
  set K : Subgroup S.O := S.Lbar g ⊓ S.Lbar ((h : G) * g) with hK
  have hth := mem_Lbar_of_pair H ht hh
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htK : zpowers t ≤ K := by rw [zpowers_le]; exact ⟨ht, hth⟩
  have h1 := card_mul_two_pow_finrank_fix H C (K := K) inf_le_left
  have h2 := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K := by
    refine le_inf inf_le_left fun v hv => (mem_fixSub S).mpr fun y hy => ?_
    have hspan := Lbar_apply_sub_mem_span' haQ hv.1 hy.1
    have hPb := apply_sub_mem_clSub_of_mem_Wt (C.mul h) (cl_mem_Vt hth)
      (conj_mem_QG' S h.2 haQ) hv.2 hy.2
    rcases mem_span_cl_iff.mp hspan with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (h0 ▸ hPb) (cl_a_not_mem H hb)
  have h3 := Submodule.finrank_mono hle
  have hcard : Nat.card K ≤ Nat.card (zpowers t) := by
    rw [Nat.card_zpowers, hto]
    have hp : 2 ^ (S.width - 1) ≤
        2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hw : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 2 ^ (S.width - 1) := by positivity
    have := Nat.mul_le_mul hlt hp
    rw [h1, hw] at this
    omega
  have heq := Subgroup.eq_of_le_of_card_ge htK hcard
  rw [heq]
  exact ⟨hx, hxb⟩

end CFSG.LargeExtraspecial.S9.RB
