module

public import CFSG.Fischer.Uniq.MuSets

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

structure LocalModel (P : Type) where
  perp : P → P → Prop
  tv : P → Equiv.Perm P
  tv_tv : ∀ p q, tv p (tv p q) = q
  tv_self : ∀ p, tv p p = p

namespace LocalModel

variable {P : Type} (M : LocalModel P)

theorem tv_image_image (p : P) (O : Set P) : M.tv p '' (M.tv p '' O) = O := by
  rw [Set.image_image]
  simp only [M.tv_tv, Set.image_id']

theorem mem_tv_image (p : P) (O : Set P) : p ∈ M.tv p '' O ↔ p ∈ O := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    have := congrArg (M.tv p) hqp
    rw [M.tv_tv, M.tv_self] at this
    rwa [← this]
  · intro h
    exact ⟨p, h, M.tv_self p⟩

@[expose] def xi (𝒮 : Set (Set P)) : SimpleGraph 𝒮 where
  Adj O Q := O ≠ Q ∧ ∃ f, f ∉ (O : Set P) ∧ M.tv f '' (O : Set P) = Q
  symm := ⟨by
    rintro O Q ⟨hne, f, hf, hQ⟩
    refine ⟨hne.symm, f, ?_, ?_⟩
    · rw [← hQ, M.mem_tv_image]; exact hf
    · rw [← hQ, M.tv_image_image]⟩
  loopless := ⟨fun O h => h.1 rfl⟩

theorem xi_adj (𝒮 : Set (Set P)) (O Q : 𝒮) :
    (M.xi 𝒮).Adj O Q ↔ O ≠ Q ∧ ∃ f, f ∉ (O : Set P) ∧ M.tv f '' (O : Set P) = Q :=
  Iff.rfl

@[expose] def triRule (O Q R : Set P) : Prop :=
  ∃ f g, f ∉ O ∧ g ∉ O ∧ M.tv f '' O = Q ∧ M.tv g '' O = R ∧ M.perp f g

end LocalModel

variable {X : Type} [Group X] {E : Set X} {P : Type}

structure LocalPoints (M : LocalModel P) (E : Set X) (d : X) where
  χ : LocalClass E d ≃ P
  comm : ∀ f g : LocalClass E d, (f : X) * g = g * f ↔ M.perp (χ f) (χ g)
  tau : ∀ (f g : LocalClass E d) (h : (f : X) * g * f ∈ LocalClass E d),
    χ ⟨_, h⟩ = M.tv (χ f) (χ g)

namespace LocalPoints

variable {M : LocalModel P} {d : X} (L : LocalPoints M E d)

@[expose] def muImg (c : X) : Set P :=
  {p | ∃ s : LocalClass E d, (s : X) ∈ LocalClass E c ∧ L.χ s = p}

theorem mem_muImg {c : X} {p : P} :
    p ∈ L.muImg c ↔ (L.χ.symm p : X) ∈ LocalClass E c := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [Equiv.symm_apply_apply]
  · intro h
    exact ⟨L.χ.symm p, h, Equiv.apply_symm_apply _ _⟩

theorem χ_mem_muImg_iff {c : X} (f : LocalClass E d) :
    L.χ f ∈ L.muImg c ↔ (f : X) ∈ muSet E d c := by
  rw [mem_muImg, Equiv.symm_apply_apply]
  exact ⟨fun h => ⟨f.2, h⟩, fun h => h.2⟩

theorem muImg_eq_image (c : X) :
    L.muImg c = L.χ '' {s : LocalClass E d | (s : X) ∈ muSet E d c} := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨s.2, hs⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs.2, rfl⟩

theorem muImg_nonempty_iff (c : X) : (L.muImg c).Nonempty ↔ (muSet E d c).Nonempty := by
  constructor
  · rintro ⟨_, s, hs, rfl⟩
    exact ⟨s, s.2, hs⟩
  · rintro ⟨s, hs, hsc⟩
    exact ⟨_, ⟨s, hs⟩, hsc, rfl⟩

theorem ncard_muImg (c : X) : (L.muImg c).ncard = (muSet E d c).ncard := by
  rw [muImg_eq_image, Set.ncard_image_of_injective _ L.χ.injective]
  have : (Subtype.val '' {s : LocalClass E d | (s : X) ∈ muSet E d c}) = muSet E d c := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx, rfl⟩
  have h2 := Set.ncard_image_of_injective {s : LocalClass E d | (s : X) ∈ muSet E d c}
    Subtype.val_injective
  rw [this] at h2
  exact h2.symm

variable (hP : Pair X E) (hd : d ∈ E)
include hP hd

theorem muImg_conj {c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c) :
    L.muImg (d * c * d) = L.muImg c := by
  ext p
  rw [mem_muImg, mem_muImg]
  have h := Pair.muSet_eq_muSet_mul_mul hP hd hc hcd
  constructor
  · intro hp
    have : (L.χ.symm p : X) ∈ muSet E d (d * c * d) := ⟨(L.χ.symm p).2, hp⟩
    rw [← h] at this
    exact this.2
  · intro hp
    have : (L.χ.symm p : X) ∈ muSet E d c := ⟨(L.χ.symm p).2, hp⟩
    rw [h] at this
    exact this.2

omit hP hd in
theorem muImg_of_muSet (g : LocalClass E d) {c c' : X}
    (h : muSet E d c' = (fun s => (g : X) * s * g) '' muSet E d c) :
    L.muImg c' = M.tv (L.χ g) '' L.muImg c := by
  ext p
  constructor
  · intro hp
    rw [mem_muImg] at hp
    have : (L.χ.symm p : X) ∈ muSet E d c' := ⟨(L.χ.symm p).2, hp⟩
    rw [h] at this
    obtain ⟨s, hs, hsp⟩ := this
    simp only at hsp
    have hsd : s ∈ LocalClass E d := hs.1
    refine ⟨L.χ ⟨s, hsd⟩, (L.χ_mem_muImg_iff ⟨s, hsd⟩).2 hs, ?_⟩
    have hgs : (g : X) * s * g ∈ LocalClass E d := by rw [hsp]; exact (L.χ.symm p).2
    rw [← L.tau g ⟨s, hsd⟩ hgs]
    have : (⟨(g : X) * s * g, hgs⟩ : LocalClass E d) = L.χ.symm p := Subtype.ext hsp
    rw [this, Equiv.apply_symm_apply]
  · rintro ⟨q, hq, rfl⟩
    rw [mem_muImg] at hq
    set s := L.χ.symm q
    have hsmu : (s : X) ∈ muSet E d c := ⟨s.2, hq⟩
    have hmem : (g : X) * s * g ∈ muSet E d c' := by rw [h]; exact ⟨s, hsmu, rfl⟩
    have hq' : q = L.χ s := (Equiv.apply_symm_apply _ _).symm
    rw [hq', ← L.tau g s hmem.1]
    exact ⟨⟨_, hmem.1⟩, hmem.2, rfl⟩

theorem muImg_nu {c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c) (f : LocalClass E d)
    (hf : (f : X) ∉ muSet E d c) :
    L.muImg (d * c * f * c * d) = M.tv (L.χ f) '' L.muImg c :=
  L.muImg_of_muSet f (Pair.muSet_nu hP hd hc hcd f.2 hf)

omit hd in
theorem muImg_star_conj (f : LocalClass E d) (c : X) :
    L.muImg ((f : X) * c * f) = M.tv (L.χ f) '' L.muImg c := by
  have hfE : (f : X) ∈ E := f.2.1
  have hfi : (f : X)⁻¹ = f := Pair.inv_eq hP hfE
  have hfd : (f : X) * d * f = d := by
    rw [f.2.2.2, mul_assoc, Pair.mul_self hP hfE, mul_one]
  apply L.muImg_of_muSet f
  have h := Pair.image_conj_muSet hP f d c
  simp only [hfi, hfd] at h
  exact h.symm

omit hP hd

@[expose] def relabel (σ : P ≃ P) (hperp : ∀ p q, M.perp (σ p) (σ q) ↔ M.perp p q)
    (htv : ∀ p q, σ (M.tv p q) = M.tv (σ p) (σ q)) : LocalPoints M E d where
  χ := L.χ.trans σ
  comm f g := by rw [Equiv.trans_apply, Equiv.trans_apply, hperp]; exact L.comm f g
  tau f g h := by rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, L.tau f g h, htv]

theorem relabel_χ (σ : P ≃ P) (hperp : ∀ p q, M.perp (σ p) (σ q) ↔ M.perp p q)
    (htv : ∀ p q, σ (M.tv p q) = M.tv (σ p) (σ q)) (f : LocalClass E d) :
    (L.relabel σ hperp htv).χ f = σ (L.χ f) :=
  rfl

theorem muImg_relabel (σ : P ≃ P) (hperp : ∀ p q, M.perp (σ p) (σ q) ↔ M.perp p q)
    (htv : ∀ p q, σ (M.tv p q) = M.tv (σ p) (σ q)) (c : X) :
    (L.relabel σ hperp htv).muImg c = σ '' L.muImg c := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨L.χ s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

end LocalPoints

end CFSG.Fischer
