module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NDefect
public import CFSG.Assembly.Subnormal
public import CFSG.Walter.Bender1970.S2.Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

section Iso

variable {G G' : Type*} [Group G] [Group G']

theorem isQuasisimple_of_mulEquiv' (e : G ≃* G') (h : CFSG.Open.IsQuasisimple G') : CFSG.Open.IsQuasisimple G := by
  refine isQuasisimple_of_surjective (e.symm : G' →* G) e.symm.surjective ?_ h
  intro g hg
  have : g = 1 := (MulEquiv.map_eq_one_iff e.symm).1 hg
  rw [this]
  exact Subgroup.one_mem _

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  obtain ⟨_, hs⟩ := hQ
  haveI := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩

theorem layer_map_ge_of_injOn (f : G →* G') {X : Subgroup G}
    (hinj : ∀ x ∈ X, f x = 1 → x = 1) : GLALayer (X.map f) ≤ (GLALayer X).map f := by
  refine GLALayer_le_of fun K hK => ?_
  have hsub : IsSubnormal (X ⊓ K.comap f) (X ⊓ (X.map f).comap f) :=
    isSubnormal_inf_comap f hK.2.1 X
  have hXeq : X ⊓ (X.map f).comap f = X :=
    inf_eq_left.2 (fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem f hx))
  rw [hXeq] at hsub
  have hmap : (X ⊓ K.comap f).map f = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.1 hx).2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hK.1 hy)
      exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_comap.2 hy⟩, rfl⟩
  let g : ↥(X ⊓ K.comap f) →* ↥K :=
    { toFun := fun x => ⟨f (x : G), Subgroup.mem_comap.1 (Subgroup.mem_inf.1 x.2).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (X ⊓ K.comap f).map f := by rw [hmap]; exact hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy'
    exact ⟨⟨x, hx⟩, rfl⟩
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj _ (Subgroup.mem_inf.1 x.2).1 (congrArg Subtype.val hx))
  have hq : CFSG.Open.IsQuasisimple ↥(X ⊓ K.comap f) :=
    isQuasisimple_of_mulEquiv' (MulEquiv.ofBijective g ⟨hginj, hg⟩) hK.2.2
  have hcomp : CFSG.Open.IsComponentOf (X ⊓ K.comap f) X := ⟨inf_le_left, hsub, hq⟩
  calc K = (X ⊓ K.comap f).map f := hmap.symm
    _ ≤ (GLALayer X).map f := Subgroup.map_mono (le_GLALayer hcomp)

end Iso

section Restrict

variable {A S : Type*} [Group A] [Group S]

@[expose] def restrictEquiv (e : MulAut S) (H : Subgroup S) (h : H.map e.toMonoidHom = H) :
    ↥H ≃* ↥H where
  toFun x := ⟨e x, by
    have hx : e (x : S) ∈ H.map e.toMonoidHom := Subgroup.mem_map_of_mem _ x.2
    rwa [h] at hx⟩
  invFun x := ⟨e.symm x, by
    have hx : (x : S) ∈ H.map e.toMonoidHom := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hyx' : e.symm (x : S) = y := by
      rw [← hyx]
      exact e.symm_apply_apply y
    rw [hyx']
    exact hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : S))
  right_inv x := Subtype.ext (e.apply_symm_apply (x : S))
  map_mul' x y := Subtype.ext (map_mul e (x : S) (y : S))

theorem restrictEquiv_apply (e : MulAut S) (H : Subgroup S) (h : H.map e.toMonoidHom = H)
    (x : ↥H) : ((restrictEquiv e H h x : ↥H) : S) = e (x : S) := rfl

@[expose] def restrictAct (ρ : A →* MulAut S) (H : Subgroup S)
    (hH : ∀ a, H.map (ρ a).toMonoidHom = H) : A →* MulAut ↥H :=
  MonoidHom.mk' (fun a => restrictEquiv (ρ a) H (hH a)) (fun a b => by
    ext x
    simp [restrictEquiv_apply, MulAut.mul_apply, map_mul])

theorem restrictAct_apply (ρ : A →* MulAut S) (H : Subgroup S)
    (hH : ∀ a, H.map (ρ a).toMonoidHom = H) (a : A) (x : ↥H) :
    ((restrictAct ρ H hH a x : ↥H) : S) = ρ a x := rfl

theorem map_fixA_restrict (ρ : A →* MulAut S) (H : Subgroup S)
    (hH : ∀ a, H.map (ρ a).toMonoidHom = H) :
    (fixA (restrictAct ρ H hH)).map H.subtype = fixA ρ ⊓ H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, y.2⟩
    rw [mem_fixA]
    intro a
    have := mem_fixA.1 hy a
    have h2 := congrArg Subtype.val this
    rw [restrictAct_apply] at h2
    exact h2
  · intro hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hx2⟩, ?_, rfl⟩
    show (⟨x, hx2⟩ : ↥H) ∈ fixA (restrictAct ρ H hH)
    rw [mem_fixA]
    intro a
    apply Subtype.ext
    rw [restrictAct_apply]
    exact (mem_fixA.1 hx1 a)

@[expose] def quotActFun (ρ : A →* MulAut S) (H : Subgroup S) (hH : ∀ a, H.map (ρ a).toMonoidHom = H)
    (a : A) : MulAut (↥H ⧸ Subgroup.center ↥H) :=
  QuotientGroup.congr (Subgroup.center ↥H) (Subgroup.center ↥H) (restrictEquiv (ρ a) H (hH a))
    (Subgroup.map_center_eq (restrictEquiv (ρ a) H (hH a)))

theorem quotActFun_mul (ρ : A →* MulAut S) (H : Subgroup S) (hH : ∀ a, H.map (ρ a).toMonoidHom = H)
    (a b : A) : quotActFun ρ H hH (a * b) = quotActFun ρ H hH a * quotActFun ρ H hH b := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [quotActFun, MulAut.mul_apply, QuotientGroup.congr_mk]
  congr 1
  apply Subtype.ext
  simp [restrictEquiv_apply, MulAut.mul_apply, map_mul]

@[expose] def quotAct (ρ : A →* MulAut S) (H : Subgroup S) (hH : ∀ a, H.map (ρ a).toMonoidHom = H) :
    A →* MulAut (↥H ⧸ Subgroup.center ↥H) :=
  MonoidHom.mk' (quotActFun ρ H hH) (quotActFun_mul ρ H hH)

theorem good_of_restrict (ρ : A →* MulAut S) {H : Subgroup S}
    (hH : ∀ a, H.map (ρ a).toMonoidHom = H)
    (hT : ∀ P' : Subgroup ↥H, P' ≤ fixA (restrictAct ρ H hH) → ⁅P', P'⁆ = P' →
      P' ≤ GLALayer (fixA (restrictAct ρ H hH))) :
    ∀ P : Subgroup S, P ≤ fixA ρ ⊓ H → ⁅P, P⁆ = P → P ≤ GLALayer (fixA ρ ⊓ H) := by
  intro P hP hPp
  have hPH : P ≤ H := fun x hx => (Subgroup.mem_inf.1 (hP hx)).2
  have hmapP : (P.subgroupOf H).map H.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH]
  have hP'fix : P.subgroupOf H ≤ fixA (restrictAct ρ H hH) := by
    intro y hy
    rw [mem_fixA]
    intro a
    apply Subtype.ext
    rw [restrictAct_apply]
    have hyP : (y : S) ∈ P := Subgroup.mem_subgroupOf.1 hy
    exact mem_fixA.1 (Subgroup.mem_inf.1 (hP hyP)).1 a
  have hP'perf : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hmapP, hPp]
  have hP'amb := hT _ hP'fix hP'perf
  calc P = (P.subgroupOf H).map H.subtype := hmapP.symm
    _ ≤ (GLALayer (fixA (restrictAct ρ H hH))).map H.subtype :=
        Subgroup.map_mono hP'amb
    _ ≤ GLALayer ((fixA (restrictAct ρ H hH)).map H.subtype) :=
        GLALayer_map_le H.subtype (fun g hg => by
          have h1 : (g : S) = 1 := hg
          have h2 : g = 1 := Subtype.ext h1
          rw [h2]
          exact Subgroup.one_mem _) _
    _ = GLALayer (fixA ρ ⊓ H) := by rw [map_fixA_restrict]

end Restrict

section Commute

variable {S : Type*} [Group S] [Finite S]

theorem gw_isComponentOf_of_open {X L : Subgroup S} (hL : CFSG.Open.IsComponentOf L X) :
    CFSG.GorensteinWalter.IsComponentOf L X := by
  refine ⟨hL.1, CFSG.Assembly.IsSubnormal.subgroupOf
    ((CFSG.Assembly.isSubnormal_iff_open).2 hL.2.1), ?_⟩
  obtain ⟨hc, hs⟩ := hL.2.2
  haveI := nontrivial_of_isQuasisimple hL.2.2
  exact ⟨inferInstance, hc, hs⟩

theorem isComponent_commute_or_eq {X K K' : Subgroup S}
    (hK : CFSG.Open.IsComponentOf K X) (hK' : CFSG.Open.IsComponentOf K' X) : K = K' ∨ ⁅K, K'⁆ = ⊥ :=
  CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot (gw_isComponentOf_of_open hK)
    (gw_isComponentOf_of_open hK')

end Commute

end CFSG.LocalAnalysis.GLTheoremA.I142N
