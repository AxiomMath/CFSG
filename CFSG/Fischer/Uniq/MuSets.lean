module

public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer SimpleGraph

variable {X : Type} [Group X] {E : Set X}

@[expose] def muSet (E : Set X) (d c : X) : Set X := LocalClass E d ∩ LocalClass E c

theorem mem_muSet {d c s : X} : s ∈ muSet E d c ↔ s ∈ LocalClass E d ∧ s ∈ LocalClass E c :=
  Iff.rfl

theorem muSet_comm (d c : X) : muSet E d c = muSet E c d :=
  Set.inter_comm _ _

theorem Pair.image_conj_muSet (hP : Pair X E) (g d c : X) :
    (fun s => g * s * g⁻¹) '' muSet E d c = muSet E (g * d * g⁻¹) (g * c * g⁻¹) := by
  rw [muSet, Set.image_inter (conj_injective g), Pair.image_conj_localClass hP,
    Pair.image_conj_localClass hP, muSet]

section Line

variable (hP : Pair X E) {d c : X} (hd : d ∈ E) (hc : c ∈ E) (hcd : c * d ≠ d * c)
include hP hd hc hcd

omit hc in
theorem Pair.mem_localClass_mul_mul {s : X} (hs : s ∈ LocalClass E d) (hsc : s * c = c * s) :
    s ∈ LocalClass E (d * c * d) := by
  have h1 : Commute s d := hs.2.2
  have h2 : Commute s c := hsc
  refine ⟨hs.1, ?_, (h1.mul_right h2).mul_right h1⟩
  rintro rfl
  exact Pair.mul_mul_not_commute_left hP hd (fun h => hcd h.symm) hs.2.2

theorem Pair.muSet_eq_muSet_mul_mul : muSet E d c = muSet E d (d * c * d) := by
  ext s
  constructor
  · rintro ⟨hs, hsc⟩
    exact ⟨hs, Pair.mem_localClass_mul_mul hP hd hcd hs hsc.2.2⟩
  · rintro ⟨hs, hs'⟩
    refine ⟨hs, hs.1, ?_, ?_⟩
    · rintro rfl
      exact hcd hs.2.2
    · have h1 : Commute s d := hs.2.2
      have h2 : Commute s (d * c * d) := hs'.2.2
      have h := (h1.mul_right h2).mul_right h1
      rwa [Pair.mul_mul_mul_mul hP hd] at h

theorem Pair.muSet_eq_inter : muSet E d c = LocalClass E c ∩ LocalClass E (d * c * d) := by
  ext s
  constructor
  · rintro ⟨hs, hsc⟩
    exact ⟨hsc, Pair.mem_localClass_mul_mul hP hd hcd hs hsc.2.2⟩
  · rintro ⟨hsc, hs'⟩
    refine ⟨⟨hsc.1, ?_, ?_⟩, hsc⟩
    · rintro rfl
      exact hcd hsc.2.2.symm
    · have h1 : Commute s c := hsc.2.2
      have h2 : Commute s (d * c * d) := hs'.2.2
      have h := (h1.mul_right h2).mul_right h1
      rwa [← Pair.mul_mul_eq hP hc hd hcd, Pair.mul_mul_mul_mul hP hc] at h

end Line

theorem Pair.mul_mul_mem_muSet (hP : Pair X E) {d c s s' : X} (hs : s ∈ muSet E d c)
    (hs' : s' ∈ muSet E d c) : s * s' * s ∈ muSet E d c := by
  have hmem : ∀ {e : X}, s ∈ LocalClass E e → s' ∈ LocalClass E e →
      s * s' * s ∈ LocalClass E e := fun {e} h h' => by
    have h1 : Commute s e := h.2.2
    have h2 : Commute s' e := h'.2.2
    refine ⟨Pair.mul_mul_mem hP h.1 h'.1, fun he => h'.2.1 ?_, (h1.mul_left h2).mul_left h1⟩
    rw [← Pair.mul_mul_mul_mul hP h.1 s', he]
    exact (Pair.mul_mul_eq_self_iff hP h.1 e).2 h.2.2
  exact ⟨hmem hs.1 hs'.1, hmem hs.2 hs'.2⟩

theorem nu_injective (d c : X) : Function.Injective fun f : X => d * c * f * c * d :=
  fun f f' h => by simpa using h

section Nu

variable (hP : Pair X E) {d c : X} (hd : d ∈ E) (hc : c ∈ E) (hcd : c * d ≠ d * c)
include hP hd hc hcd

omit hcd in
theorem Pair.nu_eq_conj (f : X) : d * c * f * c * d = d * c * f * (d * c)⁻¹ := by
  rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hc]
  group

theorem Pair.conj_mul_left : d * c * d * (d * c)⁻¹ = c := by
  rw [← Pair.nu_eq_conj hP hd hc]
  calc d * c * d * c * d = d * (c * d * c) * d := by group
    _ = d * (d * c * d) * d := by rw [Pair.mul_mul_eq hP hc hd hcd]
    _ = c := Pair.mul_mul_mul_mul hP hd c

theorem Pair.conj_mul_mul : d * c * (d * c * d) * (d * c)⁻¹ = d := by
  rw [← Pair.nu_eq_conj hP hd hc]
  calc d * c * (d * c * d) * c * d = d * (c * d * c) * (d * c * d) := by group
    _ = d * (d * c * d) * (d * c * d) := by rw [Pair.mul_mul_eq hP hc hd hcd]
    _ = d := by
      rw [show d * (d * c * d) * (d * c * d) = d * (d * (c * (d * d) * c) * d) by group,
        Pair.mul_self hP hd, mul_one, Pair.mul_self hP hc, mul_one, Pair.mul_self hP hd, mul_one]

theorem Pair.nu_mem_localClass {f : X} (hf : f ∈ LocalClass E d) :
    d * c * f * c * d ∈ LocalClass E c := by
  have h := (Pair.conj_mem_localClass_iff hP (d * c)).2 hf
  rwa [Pair.conj_mul_left hP hd hc hcd, ← Pair.nu_eq_conj hP hd hc] at h

omit hcd in
theorem Pair.nu_commute_iff (f f' : X) :
    d * c * f * c * d * (d * c * f' * c * d) = d * c * f' * c * d * (d * c * f * c * d) ↔
      f * f' = f' * f := by
  rw [Pair.nu_eq_conj hP hd hc, Pair.nu_eq_conj hP hd hc, conj_commute_iff]

theorem Pair.nu_commute_left_iff (f : X) :
    d * c * f * c * d * d = d * (d * c * f * c * d) ↔ f * (d * c * d) = d * c * d * f := by
  rw [← conj_commute_iff (d * c) f (d * c * d), Pair.conj_mul_mul hP hd hc hcd,
    ← Pair.nu_eq_conj hP hd hc]

theorem Pair.nu_not_commute {f : X} (hf : f ∈ LocalClass E d) (hfc : f ∉ muSet E d c) :
    d * c * f * c * d * d ≠ d * (d * c * f * c * d) := by
  rw [ne_eq, Pair.nu_commute_left_iff hP hd hc hcd]
  intro h
  apply hfc
  rw [Pair.muSet_eq_muSet_mul_mul hP hd hc hcd]
  refine ⟨hf, hf.1, ?_, h⟩
  rintro rfl
  exact Pair.mul_mul_not_commute_left hP hd (fun h => hcd h.symm) hf.2.2

theorem Pair.exists_nu {g : X} (hg : g ∈ LocalClass E c) (hgd : g * d ≠ d * g) :
    ∃ f ∈ LocalClass E d, f ∉ muSet E d c ∧ d * c * f * c * d = g := by
  have hfg : d * c * ((d * c)⁻¹ * g * (d * c)) * c * d = g := by
    rw [Pair.nu_eq_conj hP hd hc]
    group
  refine ⟨(d * c)⁻¹ * g * (d * c), ?_, fun hfm => hgd ?_, hfg⟩
  · rw [← Pair.conj_mem_localClass_iff hP (d * c), Pair.conj_mul_left hP hd hc hcd,
      ← Pair.nu_eq_conj hP hd hc, hfg]
    exact hg
  · rw [Pair.muSet_eq_muSet_mul_mul hP hd hc hcd] at hfm
    rw [← hfg]
    exact (Pair.nu_commute_left_iff hP hd hc hcd _).2 hfm.2.2.2

theorem Pair.nu_bijOn :
    Set.BijOn (fun f => d * c * f * c * d) (LocalClass E d \ muSet E d c)
      {g | g ∈ LocalClass E c ∧ g * d ≠ d * g} := by
  refine ⟨fun f hf => ⟨Pair.nu_mem_localClass hP hd hc hcd hf.1,
    Pair.nu_not_commute hP hd hc hcd hf.1 hf.2⟩, fun f _ f' _ h => ?_, fun g hg => ?_⟩
  · exact nu_injective d c h
  · obtain ⟨f, hf, hfm, rfl⟩ := Pair.exists_nu hP hd hc hcd hg.1 hg.2
    exact ⟨f, ⟨hf, hfm⟩, rfl⟩

theorem Pair.muSet_nu {f : X} (hf : f ∈ LocalClass E d) (hfc : f ∉ muSet E d c) :
    muSet E d (d * c * f * c * d) = (fun s => f * s * f) '' muSet E d c := by
  have hfE := hf.1
  have hcf : c * f ≠ f * c := by
    intro h
    refine hfc ⟨hf, hfE, ?_, h.symm⟩
    rintro rfl
    exact hcd hf.2.2
  have hw : d * c * f * c * d = d * (f * c * f) * d := by
    rw [← Pair.mul_mul_eq hP hc hfE hcf]
    group
  have hfd : f * d * f = d := (Pair.mul_mul_eq_self_iff hP hfE d).2 hf.2.2
  have hfcf : f * c * f * d ≠ d * (f * c * f) := by
    intro h
    apply hcd
    have h' := (conj_commute_iff f (f * c * f) d).2 h
    rwa [← Pair.mul_mul_eq_conj hP hfE, ← Pair.mul_mul_eq_conj hP hfE, Pair.mul_mul_mul_mul hP hfE,
      hfd] at h'
  have himage : (fun s => f * s * f) = fun s => f * s * f⁻¹ := by
    rw [Pair.inv_eq hP hfE]
  rw [hw, ← Pair.muSet_eq_muSet_mul_mul hP hd (Pair.mul_mul_mem hP hfE hc) hfcf, himage,
    Pair.image_conj_muSet hP, ← Pair.mul_mul_eq_conj hP hfE, ← Pair.mul_mul_eq_conj hP hfE, hfd]

end Nu

section Components

theorem reachable_induction {V : Type*} {G : SimpleGraph V} {p : V → Prop}
    (hp : ∀ a b, G.Adj a b → p a → p b) {a b : V} (h : G.Reachable a b) (ha : p a) : p b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hp _ _ hadj ha)

theorem Pair.muSet_eq_empty_of_adj (hP : Pair X E) {d c c' : X} (hd : d ∈ E) (hc : c ∈ E)
    (hcd : c * d ≠ d * c) (hmu : muSet E d c = ∅) (hc' : c' ∈ LocalClass E c) :
    c' * d ≠ d * c' ∧ muSet E d c' = ∅ := by
  have hc'd : c' * d ≠ d * c' := by
    intro h
    have hmem : c' ∈ muSet E d c := ⟨⟨hc'.1, ?_, h⟩, hc'⟩
    · rw [hmu] at hmem
      exact hmem
    · rintro rfl
      exact hcd hc'.2.2.symm
  refine ⟨hc'd, ?_⟩
  obtain ⟨f, hf, hfm, rfl⟩ := Pair.exists_nu hP hd hc hcd hc' hc'd
  rw [Pair.muSet_nu hP hd hc hcd hf hfm, hmu, Set.image_empty]

theorem Pair.reachable_iff_muSet_nonempty (hP : Pair X E) {d c : E}
    (hcd : (c : X) * d ≠ d * c) :
    (commGraph E).Reachable d c ↔ (muSet E d c).Nonempty := by
  constructor
  · intro h
    by_contra hmu
    rw [Set.not_nonempty_iff_eq_empty] at hmu
    have key := reachable_induction (G := commGraph E)
      (p := fun a : E => (a : X) * d ≠ d * a ∧ muSet E d a = ∅)
      (fun a b hab ha => Pair.muSet_eq_empty_of_adj hP d.2 a.2 ha.1 ha.2
        (mem_localClass_iff_adj.2 ((commGraph E).adj_symm hab))) h.symm ⟨hcd, hmu⟩
    exact key.1 rfl
  · rintro ⟨s, hsd, hsc⟩
    have h1 : (commGraph E).Adj d ⟨s, hsd.1⟩ :=
      (commGraph E).adj_symm (mem_localClass_iff_adj.1 hsd)
    have h2 : (commGraph E).Adj ⟨s, hsd.1⟩ c := mem_localClass_iff_adj.1 hsc
    exact h1.reachable.trans h2.reachable

theorem Pair.reachable_iff (hP : Pair X E) {d c : E} :
    (commGraph E).Reachable d c ↔
      c = d ∨ (c : X) ∈ LocalClass E d ∨ ((c : X) * d ≠ d * c ∧ (muSet E d c).Nonempty) := by
  constructor
  · intro h
    by_cases hcd : (c : X) * d = d * c
    · rcases commGraph_eq_or_adj hcd with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl (mem_localClass_iff_adj.2 hc))
    · exact Or.inr (Or.inr ⟨hcd, (Pair.reachable_iff_muSet_nonempty hP hcd).1 h⟩)
  · rintro (rfl | hc | ⟨hcd, hmu⟩)
    · rfl
    · exact ((commGraph E).adj_symm (mem_localClass_iff_adj.1 hc)).reachable
    · exact (Pair.reachable_iff_muSet_nonempty hP hcd).2 hmu

theorem Pair.muSet_nonempty (hP : Pair X E) (hconn : (commGraph E).Connected) {d c : X}
    (hd : d ∈ E) (hc : c ∈ E) (hcd : c * d ≠ d * c) : (muSet E d c).Nonempty :=
  (Pair.reachable_iff_muSet_nonempty hP (d := ⟨d, hd⟩) (c := ⟨c, hc⟩) hcd).1 (hconn _ _)

end Components

end CFSG.Fischer
