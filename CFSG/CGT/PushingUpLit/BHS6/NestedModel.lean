module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbits

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem congr_apply_apply {V V' : Type*} [Group V] [Group V'] (e : V ≃* V') (x : MulAut V) (v : V) :
    (MulAut.congr e x) (e v) = e (x v) := by
  simp [MulAut.congr_apply]

section Transport

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

theorem fixV_map_congr (A : Subgroup (MulAut V)) :
    fixV (A.map (MulAut.congr e).toMonoidHom) = (fixV A).map e.toMonoidHom :=
  CFSG.Quasithin.fixV_map_congr_equiv e A

theorem commV_map_congr (A : Subgroup (MulAut V)) :
    commV (A.map (MulAut.congr e).toMonoidHom) = (commV A).map e.toMonoidHom :=
  CFSG.Quasithin.commV_map_congr_equiv e A

theorem isIrrSection_map_congr {A : Subgroup (MulAut V)} {P Z : Subgroup V}
    (h : IsIrrSection A P Z) :
    IsIrrSection (A.map (MulAut.congr e).toMonoidHom) (P.map e.toMonoidHom)
      (Z.map e.toMonoidHom) := by
  obtain ⟨hlt, hirr⟩ := h
  refine ⟨?_, fun U' hZU' hU'P hinv => ?_⟩
  · exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr hlt
  · set U : Subgroup V := U'.comap e.toMonoidHom with hU
    have hZU : Z ≤ U := by
      rw [hU, ← Subgroup.map_le_iff_le_comap]
      exact hZU'
    have hUP : U ≤ P := by
      intro u hu
      have := hU'P (show e u ∈ U' from hu)
      obtain ⟨p, hp, hpe⟩ := this
      have : p = u := e.injective hpe
      rwa [← this]
    have hUinv : ∀ x ∈ A, ∀ u ∈ U, x u ∈ U := by
      intro x hx u hu
      have := hinv (MulAut.congr e x) ⟨x, hx, rfl⟩ (e u) hu
      rw [congr_apply_apply] at this
      exact this
    have hmap : U.map e.toMonoidHom = U' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective U'
    rcases hirr U hZU hUP hUinv with h1 | h1
    · left
      rw [← hmap, h1]
    · right
      rw [← hmap, h1]

theorem commV_eq_map_congr {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut V')}
    (hA : A' = A.map (MulAut.congr e).toMonoidHom) : commV A' = (commV A).map e.toMonoidHom := by
  subst hA
  exact commV_map_congr e A

theorem mem_commV_eq_map_congr {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut V')}
    (hA : A' = A.map (MulAut.congr e).toMonoidHom) (v : V) : e v ∈ commV A' ↔ v ∈ commV A := by
  rw [commV_eq_map_congr e hA]
  constructor
  · rintro ⟨x, hx, hxv⟩
    have : x = v := e.injective hxv
    rwa [← this]
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem card_commV_eq_map_congr {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut V')}
    (hA : A' = A.map (MulAut.congr e).toMonoidHom) :
    Nat.card ↥(commV A') = Nat.card ↥(commV A) := by
  rw [commV_eq_map_congr e hA]
  exact Subgroup.card_map_of_injective e.injective

theorem isIrrSection_eq_map_congr {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut V')}
    (hA : A' = A.map (MulAut.congr e).toMonoidHom)
    (h : IsIrrSection A (commV A ⊔ fixV A) (fixV A)) :
    IsIrrSection A' (commV A' ⊔ fixV A') (fixV A') := by
  subst hA
  rw [commV_map_congr, fixV_map_congr, ← Subgroup.map_sup]
  exact isIrrSection_map_congr e h

theorem isNatSectionBy_map_congr {S M : Type*} [Group S] [Group M] {act : S → M → M}
    {X : Subgroup (MulAut V)} {P Z : Subgroup V} (h : IsNatSectionBy act X P Z) :
    IsNatSectionBy act (X.map (MulAut.congr e).toMonoidHom) (P.map e.toMonoidHom)
      (Z.map e.toMonoidHom) := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := h
  let jX := Subgroup.equivMapOfInjective X (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
  let jP := Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have hjP : ∀ p : ↥(P.map e.toMonoidHom), ((jP.symm p : ↥P) : V) = e.symm (p : V') := by
    intro p
    have h1 : ((jP (jP.symm p) : ↥(P.map e.toMonoidHom)) : V') = e ((jP.symm p : ↥P) : V) :=
      Subgroup.coe_equivMapOfInjective_apply P e.toMonoidHom e.injective _
    rw [jP.apply_symm_apply] at h1
    rw [h1, MulEquiv.symm_apply_apply]
  refine ⟨?_, jX.symm.trans θ, β.comp jP.symm.toMonoidHom, hβs.comp jP.symm.surjective, ?_, ?_⟩
  · rintro _ ⟨x₀, hx₀, rfl⟩ _ ⟨p₀, hp₀, rfl⟩
    refine ⟨x₀ p₀, hinv x₀ hx₀ p₀ hp₀, ?_⟩
    exact (congr_apply_apply e x₀ p₀).symm
  · ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
    have h1 : β (jP.symm p) = 1 ↔ jP.symm p ∈ β.ker := (MonoidHom.mem_ker).symm
    show β (jP.symm p) = 1 ↔ _
    rw [h1, hβk, Subgroup.mem_subgroupOf, hjP]
  · rintro x p hp
    obtain ⟨x₀, rfl⟩ := jX.surjective x
    obtain ⟨p₀, rfl⟩ := jP.surjective p
    have hq : (x₀ : MulAut V) (p₀ : V) ∈ P := hinv _ x₀.2 _ p₀.2
    have hcx : ((jX x₀ : ↥(X.map (MulAut.congr e).toMonoidHom)) : MulAut V') =
        MulAut.congr e (x₀ : MulAut V) :=
      Subgroup.coe_equivMapOfInjective_apply X _ (MulAut.congr e).injective _
    have hcp : ((jP p₀ : ↥(P.map e.toMonoidHom)) : V') = e (p₀ : V) :=
      Subgroup.coe_equivMapOfInjective_apply P e.toMonoidHom e.injective _
    have e1 : jP.symm ⟨((jX x₀ : ↥(X.map (MulAut.congr e).toMonoidHom)) : MulAut V')
        ((jP p₀ : ↥(P.map e.toMonoidHom)) : V'), hp⟩ = ⟨(x₀ : MulAut V) (p₀ : V), hq⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((jX x₀ : ↥(X.map (MulAut.congr e).toMonoidHom)) : MulAut V')
        ((jP p₀ : ↥(P.map e.toMonoidHom)) : V') =
        ((jP ⟨(x₀ : MulAut V) (p₀ : V), hq⟩ : ↥(P.map e.toMonoidHom)) : V')
      rw [hcx, hcp, Subgroup.coe_equivMapOfInjective_apply P e.toMonoidHom e.injective]
      exact congr_apply_apply e (x₀ : MulAut V) (p₀ : V)
    show β (jP.symm _) = act ((jX.symm.trans θ) (jX x₀)) (β (jP.symm (jP p₀)))
    rw [e1, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hβe x₀ p₀ hq

theorem isSLNatSection_eq_map_congr {k : ℕ} {A : Subgroup (MulAut V)} {A' : Subgroup (MulAut V')}
    (hA : A' = A.map (MulAut.congr e).toMonoidHom)
    (h : IsSLNatSection A (commV A) (commV A ⊓ fixV A) k) :
    IsSLNatSection A' (commV A') (fixV A' ⊓ commV A') k := by
  subst hA
  have h1 := isNatSectionBy_map_congr e (isSLNatSection_iff.mp h)
  have h2 : (commV A ⊓ fixV A).map e.toMonoidHom =
      fixV (A.map (MulAut.congr e).toMonoidHom) ⊓ commV (A.map (MulAut.congr e).toMonoidHom) := by
    rw [Subgroup.map_inf _ _ _ e.injective, commV_map_congr, fixV_map_congr, inf_comm]
  rw [h2, ← commV_map_congr] at h1
  exact isSLNatSection_iff.mpr h1

end Transport

theorem opResidual_range_of_eq {Γ Γ' : Type*} [Group Γ] [Group Γ'] {F : Subgroup Γ}
    (hF : opResidual 2 F = F) (Θ : ↥F →* Γ') : opResidual 2 Θ.range = Θ.range := by
  refine le_antisymm (opResidual_le 2 _) ?_
  rintro _ ⟨x, rfl⟩
  have key : ∀ g : Γ, ∀ hg : g ∈ opResidual 2 F, Θ ⟨g, opResidual_le 2 F hg⟩ ∈
      opResidual 2 Θ.range := by
    intro g hg
    unfold opResidual at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      refine mem_opResidual_of_coprime ⟨⟨y, hy.1⟩, rfl⟩ ?_
      refine Nat.Coprime.coprime_dvd_left ?_ hy.2
      have := orderOf_map_dvd Θ (⟨y, hy.1⟩ : ↥F)
      rwa [Subgroup.orderOf_mk] at this
    | one =>
      have e : (⟨1, opResidual_le 2 F (one_mem _)⟩ : ↥F) = 1 := rfl
      rw [e, map_one]
      exact (opResidual 2 Θ.range).one_mem
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, opResidual_le 2 F (mul_mem hy hz)⟩ : ↥F) =
          ⟨y, opResidual_le 2 F hy⟩ * ⟨z, opResidual_le 2 F hz⟩ := rfl
      rw [e, map_mul]
      exact (opResidual 2 Θ.range).mul_mem ihy ihz
    | inv y hy ihy =>
      have e : (⟨y⁻¹, opResidual_le 2 F (inv_mem hy)⟩ : ↥F) =
          (⟨y, opResidual_le 2 F hy⟩ : ↥F)⁻¹ := rfl
      rw [e, map_inv]
      exact (opResidual 2 Θ.range).inv_mem ihy
  exact key x (by rw [hF]; exact x.2)

end CFSG.CGT.PushingUpLit.BHS6
