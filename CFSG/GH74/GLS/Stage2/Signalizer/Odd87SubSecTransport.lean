module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Generic

variable {A A' : Type*} [Group A] [Group A'] (f : A ≃* A')

@[expose] def subEquiv {H : Subgroup A} {H' : Subgroup A'} (h : H.map f.toMonoidHom = H') :
    ↥H ≃* ↥H' :=
  (f.subgroupMap H).trans (MulEquiv.subgroupCongr h)

@[simp] theorem coe_subEquiv {H : Subgroup A} {H' : Subgroup A'} (h : H.map f.toMonoidHom = H')
    (x : ↥H) : ((subEquiv f h x : ↥H') : A') = f x := rfl

theorem map_map_subtype {H : Subgroup A} {H' : Subgroup A'} (h : H.map f.toMonoidHom = H')
    (K : Subgroup ↥H) :
    (K.map (subEquiv f h).toMonoidHom).map H'.subtype = (K.map H.subtype).map f.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_top : (⊤ : Subgroup A).map f.toMonoidHom = ⊤ :=
  Subgroup.map_top_of_surjective _ f.surjective

theorem map_sup (H K : Subgroup A) :
    (H ⊔ K).map f.toMonoidHom = H.map f.toMonoidHom ⊔ K.map f.toMonoidHom :=
  Subgroup.map_sup H K _

theorem map_inf (H K : Subgroup A) :
    (H ⊓ K).map f.toMonoidHom = H.map f.toMonoidHom ⊓ K.map f.toMonoidHom :=
  Subgroup.map_inf_eq H K _ f.injective

theorem map_centralizer_set (s : Set A) :
    (centralizer s).map f.toMonoidHom = centralizer (f '' s) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    have := congrArg f (h g₀ hg₀)
    simpa using this
  · intro h g hg
    have := congrArg f.symm (h (f g) ⟨g, hg, rfl⟩)
    simpa using this

theorem map_centralizer_singleton (z : A) :
    (centralizer ({z} : Set A)).map f.toMonoidHom = centralizer ({f z} : Set A') := by
  rw [map_centralizer_set, Set.image_singleton]

theorem map_centralizer (H : Subgroup A) :
    (centralizer (H : Set A)).map f.toMonoidHom =
      centralizer ((H.map f.toMonoidHom : Subgroup A') : Set A') := by
  rw [map_centralizer_set]
  rfl

theorem map_normalizer (H : Subgroup A) :
    (normalizer (H : Set A)).map f.toMonoidHom =
      normalizer ((H.map f.toMonoidHom : Subgroup A') : Set A') :=
  Subgroup.map_equiv_normalizer_eq H f

theorem map_commutator (H K : Subgroup A) :
    ⁅H, K⁆.map f.toMonoidHom = ⁅H.map f.toMonoidHom, K.map f.toMonoidHom⁆ :=
  Subgroup.map_commutator H K _

theorem map_zpowers (z : A) : (zpowers z).map f.toMonoidHom = zpowers (f z) :=
  MonoidHom.map_zpowers _ z

theorem map_center : (center A).map f.toMonoidHom = center A' :=
  Subgroup.map_center_eq f

theorem map_pCore (p : ℕ) : (pCore p A).map f.toMonoidHom = pCore p A' :=
  pCore_map_iso p f

theorem map_layer : (layer A).map f.toMonoidHom = layer A' := by
  obtain ⟨-, hbij⟩ := CFSG.LocalCores.component_isomorphism f
  let F : Subgroup A ≃o Subgroup A' := MulEquiv.mapSubgroup f
  have himage : F '' {K : Subgroup A | IsComponent K} = {L : Subgroup A' | IsComponent L} :=
    hbij.image_eq
  calc (layer A).map f.toMonoidHom = F (sSup {K : Subgroup A | IsComponent K}) := rfl
    _ = sSup (F '' {K : Subgroup A | IsComponent K}) := by
        rw [OrderIso.map_sSup]
        simp [sSup_image]
    _ = layer A' := by rw [himage]; rfl

theorem map_map_symm (H : Subgroup A) : (H.map f.toMonoidHom).map f.symm.toMonoidHom = H :=
  CFSG.LocalCores.map_map_symm f H

theorem map_symm_map (H : Subgroup A') : (H.map f.symm.toMonoidHom).map f.toMonoidHom = H :=
  CFSG.LocalCores.map_map_symm f.symm H

theorem isSylowOf_map (p : ℕ) {P K : Subgroup A} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f.toMonoidHom) (K.map f.toMonoidHom) := by
  obtain ⟨Q, rfl⟩ := h
  let g : ↥K ≃* ↥(K.map f.toMonoidHom) := subEquiv f rfl
  refine ⟨⟨(Q : Subgroup K).map g.toMonoidHom, Q.isPGroup'.map g.toMonoidHom, ?_⟩, ?_⟩
  · intro R hR hle
    have hR' : IsPGroup p ↥(R.map g.symm.toMonoidHom) := hR.map g.symm.toMonoidHom
    have hle' : (Q : Subgroup K) ≤ R.map g.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := g.symm.toMonoidHom) hle
      rwa [map_map_symm g] at this
    have hmax := Q.is_maximal' hR' hle'
    calc R = (R.map g.symm.toMonoidHom).map g.toMonoidHom := (map_symm_map g R).symm
      _ = (Q : Subgroup K).map g.toMonoidHom := by rw [hmax]
  · exact map_map_subtype f rfl _

end Generic

section Local

variable {A A' : Type} [Group A] [Group A'] (f : A ≃* A')

theorem map_Op (p : ℕ) (P : Subgroup A) :
    (Op p P).map f.toMonoidHom = Op p (P.map f.toMonoidHom) := by
  unfold Op inSubgroup
  rw [← map_map_subtype f rfl, pCore_map_iso p (subEquiv f rfl)]

theorem isParabolicP_map (p : ℕ) {K P : Subgroup A} (h : IsParabolicP p K P) :
    IsParabolicP p (K.map f.toMonoidHom) (P.map f.toMonoidHom) := by
  obtain ⟨hPK, U, hU, hle⟩ := h
  refine ⟨Subgroup.map_mono hPK, U.map f.toMonoidHom, isSylowOf_map f p hU, ?_⟩
  rw [← map_normalizer, ← map_inf]
  exact Subgroup.map_mono hle

theorem isMaxParabolicP_map (p : ℕ) {K P : Subgroup A} (h : IsMaxParabolicP p K P) :
    IsMaxParabolicP p (K.map f.toMonoidHom) (P.map f.toMonoidHom) := by
  obtain ⟨hP, hne, hmax⟩ := h
  refine ⟨isParabolicP_map f p hP, fun h' => hne (Subgroup.map_injective f.injective h'), ?_⟩
  intro Q hQ hQK hle
  have hQ' : IsParabolicP p K (Q.map f.symm.toMonoidHom) := by
    have := isParabolicP_map f.symm p hQ
    rwa [map_map_symm] at this
  have hQK' : Q.map f.symm.toMonoidHom ≠ K := by
    intro h'
    apply hQK
    rw [← map_symm_map f Q, h']
  have hle' : P ≤ Q.map f.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := f.symm.toMonoidHom) hle
    rwa [map_map_symm] at this
  have hQP := hmax _ hQ' hQK' hle'
  calc Q = (Q.map f.symm.toMonoidHom).map f.toMonoidHom := (map_symm_map f Q).symm
    _ = P.map f.toMonoidHom := by rw [hQP]

theorem sig4A_map {z : A} {H X : Subgroup A} {p : ℕ} (h : Sig4A z H p X) :
    Sig4A (f z) (H.map f.toMonoidHom) p (X.map f.toMonoidHom) where
  prime := h.prime
  odd := h.odd
  z_mem := Subgroup.mem_map_of_mem _ h.z_mem
  X_le := Subgroup.map_mono h.X_le
  pgroup := h.pgroup.map f.toMonoidHom
  ne_bot := fun hb => h.ne_bot ((Subgroup.map_eq_bot_iff_of_injective X f.injective).1 hb)
  inv := by
    intro c hc hcz
    obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.1 hc
    have hcz' : c₀ ∈ centralizer ({z} : Set A) := by
      have h1 : f c₀ ∈ (centralizer ({z} : Set A)).map f.toMonoidHom := by
        rw [map_centralizer_singleton]
        exact hcz
      obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 h1
      rwa [← f.injective hdc]
    have h2 : f c₀ ∈ (normalizer (X : Set A)).map f.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (h.inv c₀ hc₀ hcz')
    rwa [map_normalizer] at h2
  comm := by
    rw [← map_zpowers, ← map_commutator, h.comm]

theorem sig4A_top_map {z : A} {X : Subgroup A} {p : ℕ} (h : Sig4A z (⊤ : Subgroup A) p X) :
    Sig4A (f z) (⊤ : Subgroup A') p (X.map f.toMonoidHom) := by
  have := sig4A_map f h
  rwa [map_top] at this

include f in
theorem pCore_eq_bot_map (p : ℕ) (h : pCore p A = ⊥) : pCore p A' = ⊥ := by
  rw [← map_pCore f p, h, Subgroup.map_bot]

end Local

section TypeLevel

variable {K K' : Type} [Group K] [Group K']

theorem hasSL2Model_of_mulEquiv (e : K ≃* K') {P : ℕ → Prop} (h : HasSL2Model K P) :
    HasSL2Model K' P := by
  obtain ⟨F, x, hF, hP, ⟨e'⟩⟩ := h
  exact ⟨F, x, hF, hP, ⟨e.symm.trans e'⟩⟩

theorem lieModel_of_mulEquiv (e : K ≃* K') {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel K t n p f) : LieModel K' t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isPGL3Four_of_mulEquiv (e : K ≃* K') (h : IsPGL3Four K) : IsPGL3Four K' := by
  obtain ⟨F, x, hF, hc, ⟨e'⟩⟩ := h
  exact ⟨F, x, hF, hc, ⟨e.symm.trans e'⟩⟩

theorem isL2_of_mulEquiv (e : K ≃* K') {P : ℕ → Prop} (h : IVK.IsL2 K P) : IVK.IsL2 K' P := by
  obtain ⟨F, x, hF, hP, ⟨e'⟩⟩ := h
  exact ⟨F, x, hF, hP, ⟨e.symm.trans e'⟩⟩

theorem isElementaryAbelian_of_mulEquiv (e : K ≃* K') {p : ℕ} (h : IsElementaryAbelian p K) :
    IsElementaryAbelian p K' := by
  refine
    { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
      exponent_dvd_p := ?_ }
  · have := h.toIsMulCommutative.is_comm.comm (e.symm a) (e.symm b)
    simpa using congrArg e this
  · rw [← Monoid.exponent_eq_of_mulEquiv e]
    exact h.exponent_dvd_p

end TypeLevel

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport
