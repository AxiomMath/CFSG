module

public import CFSG.CGT.PushingUpLit.ThmOne.AmbKSharp
public import CFSG.CGT.PushingUpLit.BHS6.NestedModel

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {Γ G : Type} [Group Γ] [Group G] {f : Γ →* G}

theorem ThreeSix.map_inf_centralizer_eq_inf_centralizer_map (hf : Function.Injective f)
    (A B : Subgroup Γ) : (A ⊓ Subgroup.centralizer (B : Set Γ)).map f =
      A.map f ⊓ Subgroup.centralizer ((B.map f : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨⟨a, haA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp haC b hb]
  · intro hg
    obtain ⟨⟨a, haA, rfl⟩, hgC⟩ := Subgroup.mem_inf.mp hg
    refine ⟨a, Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_centralizer_iff.mpr fun b hb => hf ?_⟩,
      rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hgC (f b) ⟨b, hb, rfl⟩

theorem ThreeSix.map_mem_centralizer_map {B : Subgroup Γ} {c : Γ}
    (hc : c ∈ Subgroup.centralizer (B : Set Γ)) :
    f c ∈ Subgroup.centralizer ((B.map f : Subgroup G) : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc b hb]

theorem ThreeSix.isNatBy_map {S M : Type*} [Group S] [Group M] {act : S → M → M}
    (hf : Function.Injective f) {E W : Subgroup Γ} (h : IsNatBy act E W) :
    IsNatBy act (E.map f) (W.map f) := by
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, heq⟩ := h
  let eE := E.equivMapOfInjective f hf
  let eW := W.equivMapOfInjective f hf
  refine ⟨φ.comp eE.symm.toMonoidHom, ψ.comp eW.symm.toMonoidHom, hφs.comp eE.symm.surjective,
    ?_, hψs.comp eW.symm.surjective, ?_, ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := eE.surjective x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← ThreeSix.map_inf_centralizer_eq_inf_centralizer_map hf]
    exact (Subgroup.mem_map_iff_mem hf).symm
  · ext x
    obtain ⟨y, rfl⟩ := eW.surjective x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← ThreeSix.map_inf_centralizer_eq_inf_centralizer_map hf]
    exact (Subgroup.mem_map_iff_mem hf).symm
  · intro e w hw
    obtain ⟨e₀, rfl⟩ := eE.surjective e
    obtain ⟨w₀, rfl⟩ := eW.surjective w
    have hcoe : ((eE e₀ : ↥(E.map f)) : G) * ((eW w₀ : ↥(W.map f)) : G) *
        ((eE e₀ : ↥(E.map f)) : G)⁻¹ = f ((e₀ : Γ) * w₀ * (e₀ : Γ)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    have hw₀ : (e₀ : Γ) * w₀ * (e₀ : Γ)⁻¹ ∈ W := by
      rw [← Subgroup.mem_map_iff_mem hf, ← hcoe]
      exact hw
    have hpt : (⟨_, hw⟩ : ↥(W.map f)) = eW ⟨_, hw₀⟩ := Subtype.ext hcoe
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hpt, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact heq e₀ w₀ hw₀

theorem ThreeSix.isElemAbelian_of_map_of_injective (hf : Function.Injective f) {V : Subgroup Γ}
    (h : IsElemAbelian 2 (V.map f)) : IsElemAbelian 2 V := by
  obtain ⟨hc, h2⟩ := h
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have := congrArg Subtype.val (hc.is_comm.comm (⟨f a, a, a.2, rfl⟩ : ↥(V.map f))
      ⟨f b, b, b.2, rfl⟩)
    simpa [map_mul] using this
  · rw [map_pow, map_one]
    exact h2 _ ⟨x, hx, rfl⟩

theorem ThreeSix.map_mem_normalizer_map_iff (hf : Function.Injective f) (V : Subgroup Γ) (a : Γ) :
    f a ∈ Subgroup.normalizer ((V.map f : Subgroup G) : Set G) ↔
      a ∈ Subgroup.normalizer (V : Set Γ) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range f V)
  rw [Subgroup.comap_map_eq_self_of_injective hf] at h
  rw [← h]
  exact Subgroup.mem_comap.symm

theorem ThreeSix.coe_conjAct_apply_eq {Λ : Type} [Group Λ] (W : Subgroup Λ)
    (g : ↥(Subgroup.normalizer (W : Set Λ))) (w : ↥W) :
    ((conjAct W g w : ↥W) : Λ) = g * w * (g : Λ)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply W g w

theorem ThreeSix.autOn_map (hf : Function.Injective f) (A V : Subgroup Γ) :
    autOn (A.map f) (V.map f) =
      (autOn A V).map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom := by
  have hconj : ∀ (a : Γ) (ha : a ∈ Subgroup.normalizer (V : Set Γ)),
      conjAct (V.map f) ⟨f a, (ThreeSix.map_mem_normalizer_map_iff hf V a).mpr ha⟩ =
        MulAut.congr (V.equivMapOfInjective f hf) (conjAct V ⟨a, ha⟩) := by
    intro a ha
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := (V.equivMapOfInjective f hf).surjective w
    rw [congr_apply_apply]
    apply Subtype.ext
    rw [ThreeSix.coe_conjAct_apply_eq, Subgroup.coe_equivMapOfInjective_apply,
      Subgroup.coe_equivMapOfInjective_apply, ThreeSix.coe_conjAct_apply_eq, map_mul, map_mul,
      map_inv]
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, haA, hag⟩ := Subgroup.mem_subgroupOf.mp hg
    have ha : a ∈ Subgroup.normalizer (V : Set Γ) :=
      (ThreeSix.map_mem_normalizer_map_iff hf V a).mp (hag ▸ g.2)
    refine ⟨conjAct V ⟨a, ha⟩, ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← hconj a ha]
    congr 1
    exact Subtype.ext hag
  · rintro ⟨_, ⟨⟨a, ha⟩, haA, rfl⟩, rfl⟩
    exact ⟨⟨f a, (ThreeSix.map_mem_normalizer_map_iff hf V a).mpr ha⟩,
      Subgroup.mem_subgroupOf.mpr ⟨a, haA, rfl⟩, hconj a ha⟩

theorem ThreeSix.natOmega_map (hf : Function.Injective f) {V : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.map f)) {n : ℕ}
    {Xh : Subgroup (MulAut ↥V)} (h : NatOmega hV n Xh) :
    NatOmega hV' n (Xh.map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom) := by
  have hc := @commV_map_congr ↥V ↥(V.map f) (commGroupOfElemAbelian hV)
    (commGroupOfElemAbelian hV') (V.equivMapOfInjective f hf) Xh
  rcases h with h | h
  · left
    have h1 := @isNatSectionBy_map_congr ↥V ↥(V.map f) (commGroupOfElemAbelian hV)
      (commGroupOfElemAbelian hV') (V.equivMapOfInjective f hf) _ _ _ _ _ _ _ _ h
    rwa [← hc, Subgroup.map_bot] at h1
  · right
    have h1 := @isNatSectionBy_map_congr ↥V ↥(V.map f) (commGroupOfElemAbelian hV)
      (commGroupOfElemAbelian hV') (V.equivMapOfInjective f hf) _ _ _ _ _ _ _ _ h
    rwa [← hc, Subgroup.map_bot] at h1

theorem ThreeSix.omegaFourOutcomeSharp_map (hf : Function.Injective f) {V Y X : Subgroup Γ}
    (h : OmegaFourOutcomeSharp V Y X) :
    OmegaFourOutcomeSharp (V.map f) (Y.map f) (X.map f) := by
  obtain ⟨h1, h2, h3, h4, n, hn, hnat, hcap, hcen, hns, hΩ, hle, hne, hSL, hcard⟩ := h
  have hXV : ⁅X.map f, V.map f⁆ = ⁅X, V⁆.map f := (Subgroup.map_commutator _ _ _).symm
  have hYV : ⁅Y.map f, V.map f⁆ = ⁅Y, V⁆.map f := (Subgroup.map_commutator _ _ _).symm
  have hAut : ∀ A : Subgroup Γ, autOn (A.map f) (V.map f) =
      (autOn A V).map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom :=
    fun A => ThreeSix.autOn_map hf A V
  refine ⟨oResidualTwo_eq_top_of_mulEquiv (X.equivMapOfInjective f hf) h1,
    by rw [← Subgroup.map_commutator, h2],
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotPCoreEquiv (Y.equivMapOfInjective f hf)) h3,
    by rw [← Subgroup.map_commutator, h4], n, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hXV]
    exact hnat.imp (ThreeSix.isNatBy_map hf) (ThreeSix.isNatBy_map hf)
  · rw [hXV, ← ThreeSix.map_inf_centralizer_eq_inf_centralizer_map hf, hcap, Subgroup.map_bot]
  · rw [hXV, ← ThreeSix.map_inf_centralizer_eq_inf_centralizer_map hf]
    rintro _ ⟨x, hx, rfl⟩
    exact ThreeSix.map_mem_centralizer_map (hcen hx)
  · intro hsn
    apply hns
    have e1 : ((Y.map f).subgroupOf (X.map f)).comap
        (X.equivMapOfInjective f hf).toMonoidHom = Y.subgroupOf X := by
      ext z
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        MulEquiv.coe_toMonoidHom, Subgroup.coe_equivMapOfInjective_apply]
      exact Subgroup.mem_map_iff_mem hf
    rw [← e1]
    exact hsn.comap _
  · intro hV'
    rw [hAut X]
    exact ThreeSix.natOmega_map hf _ hV' (hΩ (ThreeSix.isElemAbelian_of_map_of_injective hf hV'))
  · rw [hAut Y, hAut X]
    exact Subgroup.map_mono hle
  · rw [hAut Y, hAut X]
    exact fun h' => hne (Subgroup.map_injective (MulAut.congr _).injective h')
  · rw [hAut Y]
    exact ⟨((autOn Y V).equivMapOfInjective _ (MulAut.congr _).injective).symm.trans hSL.some⟩
  · rw [hYV, Subgroup.card_map_of_injective hf]
    exact hcard

end CFSG.CGT.PushingUpLit.ThmOne
