module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
public import CFSG.CGT.PushingUpLit.A78.JStructure
import CFSG.CGT.PushingUpLit.A78One.Claim3
import CFSG.CGT.PushingUpLit.A78One.CjLemmas
import CFSG.CGT.PushingUpLit.A78One.CommGe
import CFSG.CGT.PushingUpLit.A78One.Dict
import CFSG.CGT.PushingUpLit.A78One.Star
import CFSG.CGT.PushingUpLit.A78One.QEq
import CFSG.CGT.PushingUpLit.T2K.FourSevenB

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.A78
open scoped commutatorElement

variable {G : Type} [Group G]

def sqClosure (A : Subgroup G) : Subgroup G := Subgroup.closure {z | ∃ g ∈ A, z = g * g}

theorem sq_mem_sqClosure {A : Subgroup G} {g : G} (hg : g ∈ A) : g * g ∈ sqClosure A :=
  Subgroup.subset_closure ⟨g, hg, rfl⟩

theorem sqClosure_le {A : Subgroup G} : sqClosure A ≤ A :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨g, hg, rfl⟩; exact A.mul_mem hg hg)

theorem sqClosure_le_of {A B : Subgroup G} (h : ∀ g ∈ A, ∃ f ∈ B, g * g = f * f) :
    sqClosure A ≤ sqClosure B := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨f, hf, he⟩ := h g hg
  rw [he]
  exact sq_mem_sqClosure hf

theorem cj_sqClosure_le {A : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    cj n (sqClosure A) ≤ sqClosure A := by
  refine Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨g, hg, rfl⟩
  have e : (MulAut.conj n).toMonoidHom (g * g) = (n * g * n⁻¹) * (n * g * n⁻¹) := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  show (MulAut.conj n).toMonoidHom (g * g) ∈ sqClosure A
  rw [e]
  exact sq_mem_sqClosure ((Subgroup.mem_normalizer_iff.1 hn g).1 hg)

theorem le_normalizer_sqClosure {A N : Subgroup G} (hN : N ≤ Subgroup.normalizer (A : Set G)) :
    N ≤ Subgroup.normalizer (sqClosure A : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_cj]
  refine le_antisymm (cj_sqClosure_le (hN hn)) ?_
  have h := cjx_mono n (cj_sqClosure_le (hN (N.inv_mem hn)))
  rwa [cjx_cj_inv] at h

theorem mul_self_mul_eq {u f : G} (hu : u * u = 1) (hc : u * f = f * u) :
    (u * f) * (u * f) = f * f := by
  calc (u * f) * (u * f) = u * (f * u) * f := by group
    _ = u * (u * f) * f := by rw [hc]
    _ = (u * u) * (f * f) := by group
    _ = f * f := by rw [hu, one_mul]

theorem comm_of_conj_comm {x a b : G}
    (h : (x * a * x⁻¹) * (x * b * x⁻¹) = (x * b * x⁻¹) * (x * a * x⁻¹)) : a * b = b * a := by
  calc a * b = x⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * b * x⁻¹) * (x * a * x⁻¹)) * x := by rw [h]
    _ = b * a := by group

theorem mul_self_of_conj {x a : G} (h : (x * a * x⁻¹) * (x * a * x⁻¹) = 1) : a * a = 1 := by
  calc a * a = x⁻¹ * ((x * a * x⁻¹) * (x * a * x⁻¹)) * x := by group
    _ = 1 := by rw [h]; group

namespace CexCtx

variable [Finite G] {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

theorem blockU_le_cexP (c : CexCtx L M n T T' x) : blockU L ≤ cexP L T :=
  le_inf (NatBlock.blockU_le_sylow c.hyp.le c.nM c.sylow) fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun w hw => c.hyp.natBlock.blockU_comm w hw v hv

theorem H_le_normalizer_P (c : CexCtx L M n T T' x) :
    L ⊔ T' ≤ Subgroup.normalizer (cexP L T : Set G) := by
  have := SixThree.le_normalizer_oTwoIn (L ⊔ T')
  rwa [c.oTwoIn_H] at this

theorem le_normalizer_Px (c : CexCtx L M n T T' x) :
    T' ≤ Subgroup.normalizer (cj x⁻¹ (cexP L T) : Set G) := by
  intro t ht
  have hxt : x * t * x⁻¹ ∈ T' := (Subgroup.mem_normalizer_iff.1 c.hx t).1 ht
  have e : t * x⁻¹ = x⁻¹ * (x * t * x⁻¹) := by group
  rw [mem_normalizer_iff_cj, cjx_cj, e, ← cjx_cj,
    mem_normalizer_iff_cj.1 (c.H_le_normalizer_P (Subgroup.mem_sup_right hxt))]

theorem Px_le (c : CexCtx L M n T T' x) : cj x⁻¹ (cexP L T) ≤ T' := by
  intro t ht
  have ht' : x * t * x⁻¹ ∈ cexP L T := by simpa using (cjx_mem _ _ _).1 ht
  exact ((Subgroup.mem_normalizer_iff.1 c.hx) t).2 (c.P_le ht')

theorem cj_T' (c : CexCtx L M n T T' x) : cj x⁻¹ T' = T' :=
  mem_normalizer_iff_cj.1 ((Subgroup.normalizer (T' : Set G)).inv_mem c.hx)

theorem mem_P_decomp (c : CexCtx L M n T T' x) {y : G} (hy : y ∈ cexP L T) :
    ∃ u ∈ blockU L, ∃ f ∈ cexP L T ⊓ cj x⁻¹ (cexP L T), y = u * f := by
  have hQ := c.inv.le_sylow
  have hQ0 := c.inv.sylow_eq_U1
  simp only [inv_inv] at hQ hQ0
  have h : cexP L T ≤ blockU L ⊔ cj x⁻¹ (cexP L T) := by
    have := cjx_mono x⁻¹ (hQ.trans hQ0.le)
    rwa [cjx_inv_cj, cjx_sup, cjx_inv_cj] at this
  have hUn : blockU L ≤ Subgroup.normalizer (cj x⁻¹ (cexP L T) : Set G) :=
    (c.blockU_le_cexP.trans c.P_le).trans c.le_normalizer_Px
  obtain ⟨u, hu, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hUn).1 (h hy)
  refine ⟨u, hu, p, ⟨?_, hp⟩, rfl⟩
  have := (cexP L T).mul_mem ((cexP L T).inv_mem (c.blockU_le_cexP hu)) hy
  simpa using this

theorem mem_Px_decomp (c : CexCtx L M n T T' x) {y : G} (hy : y ∈ cj x⁻¹ (cexP L T)) :
    ∃ u ∈ cj x⁻¹ (blockU L), ∃ f ∈ cexP L T ⊓ cj x⁻¹ (cexP L T), y = u * f := by
  have hQ := c.sylow_eq_U1
  have hy' : y ∈ T' ⊓ (L ⊔ cexP L T) := c.le_sylow hy
  rw [hQ] at hy'
  have hUxP : cj x⁻¹ (blockU L) ≤ cj x⁻¹ (cexP L T) := cjx_mono _ c.blockU_le_cexP
  have hUn : cj x⁻¹ (blockU L) ≤ Subgroup.normalizer (cexP L T : Set G) := fun u hu =>
    c.H_le_normalizer_P (Subgroup.mem_sup_right (c.Px_le (hUxP hu)))
  obtain ⟨u, hu, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hUn).1 hy'
  refine ⟨u, hu, p, ⟨hp, ?_⟩, rfl⟩
  have := (cj x⁻¹ (cexP L T)).mul_mem ((cj x⁻¹ (cexP L T)).inv_mem (hUxP hu)) hy
  simpa using this

theorem sylow_eq_sup (c : CexCtx L M n T T' x) :
    T' ⊓ (L ⊔ cexP L T) = cexP L T ⊔ cj x⁻¹ (cexP L T) := by
  refine le_antisymm ?_ (sup_le (le_inf c.P_le le_sup_right) c.le_sylow)
  rw [c.sylow_eq_U1]
  exact sup_le (le_sup_of_le_right (cjx_mono _ c.blockU_le_cexP)) le_sup_left

theorem sq_eq_of_mem_P (c : CexCtx L M n T T' x) {g : G} (hg : g ∈ cexP L T) :
    ∃ f ∈ cj x⁻¹ (cexP L T), g * g = f * f := by
  obtain ⟨u, hu, f, hf, rfl⟩ := c.mem_P_decomp hg
  have hu2 : u * u = 1 := by simpa [pow_two] using c.hyp.natBlock.sq_eq_one_of_mem_blockU hu
  have huc : u * f = f * u := Subgroup.mem_centralizer_iff.1 hf.1.2 u hu
  exact ⟨f, hf.2, mul_self_mul_eq hu2 huc⟩

theorem sq_eq_of_mem_Px (c : CexCtx L M n T T' x) {g : G} (hg : g ∈ cj x⁻¹ (cexP L T)) :
    ∃ f ∈ cexP L T, g * g = f * f := by
  obtain ⟨u, hu, f, hf, rfl⟩ := c.mem_Px_decomp hg
  have hu' : x * u * x⁻¹ ∈ blockU L := by simpa using (cjx_mem _ _ _).1 hu
  have hf' : x * f * x⁻¹ ∈ cexP L T := by simpa using (cjx_mem _ _ _).1 hf.2
  have hu2 : u * u = 1 := mul_self_of_conj (x := x) (by
    simpa [pow_two] using c.hyp.natBlock.sq_eq_one_of_mem_blockU hu')
  have huc : u * f = f * u :=
    comm_of_conj_comm (Subgroup.mem_centralizer_iff.1 hf'.2 _ hu')
  exact ⟨f, hf.1, mul_self_mul_eq hu2 huc⟩

theorem sqClosure_eq (c : CexCtx L M n T T' x) :
    sqClosure (cexP L T) = sqClosure (cj x⁻¹ (cexP L T)) :=
  le_antisymm (sqClosure_le_of fun _ hg => c.sq_eq_of_mem_P hg)
    (sqClosure_le_of fun _ hg => c.sq_eq_of_mem_Px hg)

theorem elem_P (c : CexCtx L M n T T' x) : CFSG.Open.IsElemAbelian 2 (cexP L T) := by
  have hPT : cexP L T ≤ T := inf_le_left
  have hD2 : IsPGroup 2 (sqClosure (cexP L T)) :=
    c.sylow.isPGroup.to_le (sqClosure_le.trans hPT)
  have hLP : L ≤ Subgroup.normalizer (cexP L T : Set G) :=
    le_sup_left.trans c.H_le_normalizer_P
  have hL : L ≤ Subgroup.normalizer (sqClosure (cexP L T) : Set G) :=
    le_normalizer_sqClosure hLP
  have hLg : cj x⁻¹ L ≤ Subgroup.normalizer (sqClosure (cexP L T) : Set G) := by
    rw [c.sqClosure_eq]
    exact le_normalizer_sqClosure (T2Hyp.normalizer_map_conj_of_le hLP)
  have hbot : sqClosure (cexP L T) = ⊥ := by
    by_contra hne
    have h := c.hyp.mem_of_normalized hne hD2 hL hLg
    exact c.hxM (by simpa using M.inv_mem h)
  have hsq : ∀ g ∈ cexP L T, g * g = 1 := fun g hg => by
    have := sq_mem_sqClosure hg
    rwa [hbot, Subgroup.mem_bot] at this
  refine isElemAbelian_of_forall' (fun a ha b hb => ?_)
    (fun a ha => by rw [pow_two]; exact hsq a ha)
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hab := hsq (a * b) ((cexP L T).mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, ha1, hb1]

theorem isMax_self_P (c : CexCtx L M n T T' x) : IsMaxElemAbelian (cexP L T) (cexP L T) :=
  ⟨le_rfl, c.elem_P, fun _ hB _ => Subgroup.card_le_of_le hB⟩

theorem P_isMax (c : CexCtx L M n T T' x) : IsMaxElemAbelian T' (cexP L T) :=
  c.isMax_of_isMax_P c.isMax_self_P

theorem Px_isMax (c : CexCtx L M n T T' x) : IsMaxElemAbelian T' (cj x⁻¹ (cexP L T)) := by
  have := cjx_isMax x⁻¹ c.P_isMax
  rwa [c.cj_T'] at this

theorem P_ne_Px (c : CexCtx L M n T T' x) : cexP L T ≠ cj x⁻¹ (cexP L T) := by
  intro h
  refine c.star c.isMax_self_P ?_
  rw [← h]
  exact c.isMax_self_P

theorem Px_not_le_centralizer (c : CexCtx L M n T T' x) :
    ¬ cj x⁻¹ (cexP L T) ≤ Subgroup.centralizer (blockU L : Set G) := by
  intro h
  have h1 : cj x⁻¹ (cexP L T) ≤ cexP L T := le_inf (c.Px_le.trans c.le) h
  have h2 : cj x⁻¹ (cexP L T) = cexP L T :=
    Subgroup.eq_of_le_of_card_ge h1 (cjx_card x⁻¹ _).ge
  exact c.P_ne_Px h2.symm

theorem hyp45_Px (c : CexCtx L M n T T' x) : Hyp45 L (L ⊔ T') T' (cj x⁻¹ (cexP L T)) n :=
  c.hyp45 c.Px_isMax c.Px_not_le_centralizer

theorem relIndex_Px (c : CexCtx L M n T T' x) :
    (cexP L T ⊓ cj x⁻¹ (cexP L T)).relIndex (cj x⁻¹ (cexP L T)) = 2 ^ n := by
  have h := c.hyp45_Px.index_centralizer
  have e : cj x⁻¹ (cexP L T) ⊓ Subgroup.centralizer (blockU L : Set G) =
      cexP L T ⊓ cj x⁻¹ (cexP L T) := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨⟨c.le (c.Px_le hy1), hy2⟩, hy1⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy2, hy1.2⟩
  rwa [e] at h

theorem relIndex_P (c : CexCtx L M n T T' x) :
    (cexP L T ⊓ cj x⁻¹ (cexP L T)).relIndex (cexP L T) = 2 ^ n := by
  have h := c.inv.relIndex_Px
  simp only [inv_inv] at h
  have h' := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (cexP L T ⊓ cj x (cexP L T)) (cj x (cexP L T)) (MulAut.conj x⁻¹).injective
  change (cj x⁻¹ (cexP L T ⊓ cj x (cexP L T))).relIndex (cj x⁻¹ (cj x (cexP L T))) = _ at h'
  rw [cjx_inf, cjx_inv_cj, h, inf_comm] at h'
  exact h'

theorem jStructure (c : CexCtx L M n T T' x) :
    JStructure G (cexP L T ⊔ cj x⁻¹ (cexP L T)) (cexP L T) (cj x⁻¹ (cexP L T)) n where
  two_le := c.hyp.two_le
  sup_eq := rfl
  conj_V := fun j hj y hy => by
    have hjT' : j ∈ T' := sup_le c.P_le c.Px_le hj
    exact (Subgroup.mem_normalizer_iff.1
      (c.H_le_normalizer_P (Subgroup.mem_sup_right hjT')) y).1 hy
  conj_V₂ := fun j hj y hy => by
    have hjT' : j ∈ T' := sup_le c.P_le c.Px_le hj
    exact (Subgroup.mem_normalizer_iff.1 (c.le_normalizer_Px hjT') y).1 hy
  abelian_V := fun a ha b hb => isElemAbelian_comm' c.elem_P ha hb
  sq_V := fun a ha => by simpa [pow_two] using c.elem_P.2 a ha
  abelian_V₂ := fun a ha b hb => isElemAbelian_comm' (cjx_isElemAbelian c.elem_P x⁻¹) ha hb
  sq_V₂ := fun a ha => by simpa [pow_two] using (cjx_isElemAbelian c.elem_P x⁻¹).2 a ha
  index_V := c.relIndex_P
  index_V₂ := c.relIndex_Px
  comm_ge := fun v hv hvP => by
    have hnt : v ∉ Subgroup.centralizer (blockU L : Set G) := fun h => hvP ⟨c.le (c.Px_le hv), h⟩
    exact (c.hyp45_Px.card_commutator_ge hv hnt).trans
      (Subgroup.card_le_of_le (Subgroup.commutator_mono c.blockU_le_cexP le_rfl))

theorem endData (c : CexCtx L M n T T' x) : EndData L M n T T' x where
  elem := c.elem_P
  maxElem := fun A => by
    constructor
    · intro hA
      by_cases hAP : A ≤ cexP L T
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge hAP (hA.2.2 _ c.P_le c.elem_P))
      · obtain ⟨hAL, -⟩ := c.offender_sylow hA hAP
        have hAJ : A ≤ cexP L T ⊔ cj x⁻¹ (cexP L T) := by
          rw [← c.sylow_eq_sup]
          exact le_inf hA.1 hAL
        have hcard : Nat.card A = Nat.card (cexP L T) :=
          le_antisymm (c.P_isMax.2.2 A hA.1 hA.2.1) (hA.2.2 _ c.P_le c.elem_P)
        exact c.jStructure.mem_of_card hAJ
          (fun y hy => by simpa [pow_two] using hA.2.1.2 y hy) hcard
    · rintro (rfl | rfl)
      · exact c.P_isMax
      · exact c.Px_isMax
  ne := c.P_ne_Px
  sylowJ := by
    rw [← c.sylow_eq_sup]
    have hsubn : L ⊔ T' ≤ Subgroup.normalizer ((L ⊔ cexP L T : Subgroup G) : Set G) := by
      intro h hh
      rw [mem_normalizer_iff_cj, cjx_sup, mem_normalizer_iff_cj.1 (c.H_le_normalizer hh),
        mem_normalizer_iff_cj.1 (c.H_le_normalizer_P hh)]
    exact c.sylow_H.inf_of_le_normalizer (sup_le_sup_left c.P_le L) hsubn

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
