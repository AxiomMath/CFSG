module

public import CFSG.GH74.GLS.C3.Layer2.L5C2

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

noncomputable abbrev cardC {M : Type} [Group M] (u : M) : ℕ :=
  Nat.card (Subgroup.centralizer ({u} : Set M))

theorem exists_extremal {M : Type} [Group M] [Finite M] {E : M → M → Prop} (hE : Equivalence E)
    (t : M) : ∃ y, E t y ∧ ∀ z, E y z → cardC z ≤ cardC y := by
  classical
  have : Fintype M := Fintype.ofFinite M
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (E t)) cardC
    ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, hE.refl t⟩⟩
  refine ⟨y, (Finset.mem_filter.1 hy).2, fun z hz => hmax z ?_⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hE.trans (Finset.mem_filter.1 hy).2 hz⟩

end Fus

open Fus

namespace FusionHyp

variable {M : Type} [Group M] [Finite M] {emb : ↥T5 →* M} {E : M → M → Prop}

theorem inv_of_extremal
    (h : FusionHyp M emb E) {t y : M} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hty : E t y) (hy : ∀ z, E y z → cardC z ≤ cardC y) : y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨φ, hinj, hφ, -⟩ := h.scp t y ht hty hy
  set a : ↥(Subgroup.centralizer ({t} : Set M)) :=
    ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with ha
  have haa : a * a = 1 := Subtype.ext ht
  have h2 : φ a * φ a = 1 := by rw [← map_mul, haa, map_one]
  refine ⟨?_, ?_⟩
  · have := congrArg Subtype.val h2
    simpa [hφ] using this
  · intro hy1
    have h3 : φ a = 1 := Subtype.ext (hφ.trans hy1)
    have h4 : a = 1 := hinj (h3.trans (map_one φ).symm)
    exact ht1 (congrArg Subtype.val h4)

theorem extremal_of_max
    (h : FusionHyp M emb E) {u : M} (hu : u * u = 1) (hu1 : u ≠ 1)
    (hmax : ∀ i : M, i * i = 1 → i ≠ 1 → E u i → cardC i ≤ cardC u) :
    ∀ z, E u z → cardC z ≤ cardC u := by
  obtain ⟨y, huy, hy⟩ := exists_extremal h.equiv u
  obtain ⟨hy2, hy1⟩ := h.inv_of_extremal hu hu1 huy hy
  intro z hz
  calc cardC z ≤ cardC y := hy z (h.equiv.trans (h.equiv.symm huy) hz)
    _ ≤ cardC u := hmax y hy2 hy1 huy

theorem scp_inv
    (h : FusionHyp M emb E) {t t' : M} (ht : t * t = 1) (hE : E t t')
    (ht' : t' * t' = 1) (ht'1 : t' ≠ 1)
    (hmax : ∀ i : M, i * i = 1 → i ≠ 1 → E t' i → cardC i ≤ cardC t') :
    ∃ φ : ↥(Subgroup.centralizer ({t} : Set M)) →* ↥(Subgroup.centralizer ({t'} : Set M)),
      Function.Injective φ ∧
        (φ ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : M) = t' ∧
        ∀ s, E (φ s : M) (s : M) :=
  h.scp t t' ht hE (h.extremal_of_max ht' ht'1 hmax)

theorem thompson_inv
    (h : FusionHyp M emb E) (H : Subgroup M) (hH : H.index = 2) {u : M}
    (hu : u ∉ H) (hu2 : u * u = 1) :
    ∃ u' : M, u' ∈ H ∧ u' * u' = 1 ∧ u' ≠ 1 ∧ E u' u ∧
      ∀ i : M, i * i = 1 → i ≠ 1 → E u' i → cardC i ≤ cardC u' := by
  obtain ⟨u', hu'H, hE, hext⟩ := h.thompson H hH u hu hu2
  have hu1 : u ≠ 1 := fun e => hu (e ▸ H.one_mem)
  obtain ⟨h2, h1⟩ := h.inv_of_extremal hu2 hu1 (h.equiv.symm hE) hext
  exact ⟨u', hu'H, h2, h1, hE, fun i _ _ hi => hext i hi⟩

theorem eq_one_of_E_one
    (h : FusionHyp M emb E) {b : M} (hb : b * b = 1) (hE : E 1 b) :
    b = 1 := by
  by_contra hb1
  have hE' : E b 1 := h.equiv.symm hE
  have hext : ∀ z : M, E 1 z → cardC z ≤ cardC (1 : M) := by
    intro z _
    refine Nat.card_le_card_of_injective
      (fun a : ↥(Subgroup.centralizer ({z} : Set M)) =>
        (⟨a.1, by simp [Subgroup.mem_centralizer_singleton_iff]⟩ :
          ↥(Subgroup.centralizer ({(1 : M)} : Set M)))) ?_
    intro a a' haa'
    have h1 : a.1 = a'.1 :=
      congrArg (fun x : ↥(Subgroup.centralizer ({(1 : M)} : Set M)) => x.1) haa'
    exact Subtype.ext h1
  obtain ⟨φ, hinj, hφ, -⟩ := h.scp b 1 hb hE' hext
  set a : ↥(Subgroup.centralizer ({b} : Set M)) :=
    ⟨b, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with ha
  have h3 : φ a = 1 := Subtype.ext hφ
  have h4 : a = 1 := hinj (h3.trans (map_one φ).symm)
  exact hb1 (congrArg Subtype.val h4)

end FusionHyp

namespace Fus

@[expose] def centEquiv {M N : Type} [Group M] [Group N] (iso : M ≃* N) {x : M} {y : N}
    (hxy : iso x = y) :
    ↥(Subgroup.centralizer ({x} : Set M)) ≃* ↥(Subgroup.centralizer ({y} : Set N)) where
  toFun a := ⟨iso a.1, by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxy, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 a.2]⟩
  invFun b := ⟨iso.symm b.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply iso.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hxy]
    exact Subgroup.mem_centralizer_singleton_iff.1 b.2⟩
  left_inv a := Subtype.ext (iso.symm_apply_apply _)
  right_inv b := Subtype.ext (iso.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul iso _ _)

theorem cardC_equiv {M N : Type} [Group M] [Group N] (iso : M ≃* N) (x : M) :
    cardC (iso x) = cardC x :=
  Nat.card_congr (centEquiv iso (x := x) rfl).toEquiv.symm

end Fus

namespace FusionHyp

variable {M : Type} [Group M] [Finite M] {emb : ↥T5 →* M} {E : M → M → Prop}

theorem transport
    (h : FusionHyp M emb E) {N : Type} [Group N] [Finite N] (iso : M ≃* N) :
    FusionHyp N (iso.toMonoidHom.comp emb) (fun a b => E (iso.symm a) (iso.symm b)) where
  equiv := ⟨fun a => h.equiv.refl _, fun hab => h.equiv.symm hab,
    fun hab hbc => h.equiv.trans hab hbc⟩
  conj a s := by simpa [map_mul, map_inv] using h.conj (iso.symm a) (iso.symm s)
  f5 g hg t s hgts := by simpa using h.f5 g hg t s hgts
  nbar A hA i := by simpa using h.nbar A hA i
  xmax x' hx := by
    have h1 : cardC (iso.symm x') ≤ 32 := h.xmax (iso.symm x') (by simpa using hx)
    have h2 := cardC_equiv iso (iso.symm x')
    rw [MulEquiv.apply_symm_apply] at h2
    show cardC x' ≤ 32
    omega
  scp t t' ht hE hext := by
    have ht2 : iso.symm t * iso.symm t = 1 := by rw [← map_mul, ht, map_one]
    have hext' : ∀ z, E (iso.symm t') z → cardC z ≤ cardC (iso.symm t') := by
      intro z hz
      have h1 : cardC (iso z) ≤ cardC t' := hext (iso z) (by simpa using hz)
      have h2 := cardC_equiv iso (iso.symm t')
      have h3 := cardC_equiv iso z
      rw [MulEquiv.apply_symm_apply] at h2
      omega
    obtain ⟨φ, hinj, hφ, hφE⟩ := h.scp (iso.symm t) (iso.symm t') ht2 hE hext'
    let c1 := centEquiv iso (x := iso.symm t) (y := t) (MulEquiv.apply_symm_apply iso t)
    let c2 := centEquiv iso (x := iso.symm t') (y := t') (MulEquiv.apply_symm_apply iso t')
    refine ⟨c2.toMonoidHom.comp (φ.comp c1.symm.toMonoidHom), ?_, ?_, ?_⟩
    · intro a b hab
      exact c1.symm.injective (hinj (c2.injective hab))
    · have e1 : c1.symm ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ =
          ⟨iso.symm t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ := rfl
      show iso (φ (c1.symm ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) : M) = t'
      rw [e1, hφ, MulEquiv.apply_symm_apply]
    · intro s
      have := hφE (c1.symm s)
      simpa [c2, centEquiv, c1] using this
  thompson H hH u hu hu2 := by
    have hH' : (H.comap iso.toMonoidHom).index = 2 := by
      rw [Subgroup.index_comap_of_surjective _ iso.surjective, hH]
    have hu' : iso.symm u ∉ H.comap iso.toMonoidHom := by simpa using hu
    have hu2' : iso.symm u * iso.symm u = 1 := by rw [← map_mul, hu2, map_one]
    obtain ⟨u', hu'H, hE, hext⟩ := h.thompson _ hH' _ hu' hu2'
    refine ⟨iso u', hu'H, by simpa using hE, ?_⟩
    intro z hz
    have h1 : cardC (iso.symm z) ≤ cardC u' := hext (iso.symm z) (by simpa using hz)
    have h2 := cardC_equiv iso (iso.symm z)
    have h3 := cardC_equiv iso u'
    rw [MulEquiv.apply_symm_apply] at h2
    show cardC z ≤ cardC (iso u')
    omega

end FusionHyp

end CFSG.GH74.GLS.C3.Layer2.L5
