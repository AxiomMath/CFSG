module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoMainSylow
public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common

scoped notation:max A "ᵍ[" g "]" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (g)⁻¹)) A

section Generic

variable {G : Type*} [Group G]

@[expose] def oTwoPrimeRes (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

@[expose] def zc (X : Subgroup G) : Subgroup G :=
  X ⊓ centralizer (X : Set G)

@[expose] def centralizerMod (N B : Subgroup G) : Subgroup G :=
  NormalizerQuotient.lift (centralizer
    ((NormalizerQuotient.bar N B : Subgroup (NormalizerQuotient.Bar N)) :
      Set (NormalizerQuotient.Bar N)))

@[expose] def upperCenterMod (N A : Subgroup G) (i : ℕ) : Subgroup G :=
  NormalizerQuotient.lift ((Subgroup.upperCentralSeries ↥(NormalizerQuotient.bar N A) i).map
    (NormalizerQuotient.bar N A).subtype)

@[expose] def centerMod (N A : Subgroup G) : Subgroup G :=
  upperCenterMod N A 1

@[expose] def IsQuotientIso (X N : Subgroup G) (T : Type*) [Group T] : Prop :=
  ∃ φ : X →* T, Function.Surjective φ ∧ φ.ker = N.subgroupOf X

@[expose] def SectionIso (A B A' B' : Subgroup G) : Prop :=
  ∃ (_ : (B.subgroupOf A).Normal) (_ : (B'.subgroupOf A').Normal),
    Nonempty ((A ⧸ B.subgroupOf A) ≃* (A' ⧸ B'.subgroupOf A'))

@[expose] def IsFreeSection (t : G) (A B : Subgroup G) : Prop :=
  B.relIndex A = (B.relIndex (A ⊓ centralizerMod B (zpowers t))) ^ 2

theorem commutator_mem_iff_proj {N : Subgroup G} {g b : G} (hg : g ∈ normalizer (N : Set G))
    (hb : b ∈ normalizer (N : Set G)) :
    NormalizerQuotient.proj N ⟨b, hb⟩ * NormalizerQuotient.proj N ⟨g, hg⟩ =
        NormalizerQuotient.proj N ⟨g, hg⟩ * NormalizerQuotient.proj N ⟨b, hb⟩ ↔
      g * b * g⁻¹ * b⁻¹ ∈ N := by
  rw [← map_mul, ← map_mul, NormalizerQuotient.proj_eq_proj_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  constructor
  · intro h
    have h1 : g * (g⁻¹ * b⁻¹ * g * b) * g⁻¹ ∈ N := by
      have := (mem_normalizer_iff.1 hg (g⁻¹ * b⁻¹ * g * b)).1 (by simpa [mul_assoc] using h)
      simpa [mul_assoc] using this
    have h2 : b * (b⁻¹ * g * b * g⁻¹) * b⁻¹ ∈ N := by
      have hh : b⁻¹ * g * b * g⁻¹ ∈ N := by
        have e : g * (g⁻¹ * b⁻¹ * g * b) * g⁻¹ = b⁻¹ * g * b * g⁻¹ := by group
        rwa [e] at h1
      exact (mem_normalizer_iff.1 hb _).1 hh
    have e2 : b * (b⁻¹ * g * b * g⁻¹) * b⁻¹ = g * b * g⁻¹ * b⁻¹ := by group
    rwa [e2] at h2
  · intro h
    have h1 : b⁻¹ * (g * b * g⁻¹ * b⁻¹) * b ∈ N := by
      have := (mem_normalizer_iff.1 (inv_mem hb) _).1 h
      simpa [mul_assoc] using this
    have e : b⁻¹ * (g * b * g⁻¹ * b⁻¹) * b = b⁻¹ * g * b * g⁻¹ := by group
    rw [e] at h1
    have h2 : g⁻¹ * (b⁻¹ * g * b * g⁻¹) * g ∈ N := by
      have := (mem_normalizer_iff.1 (inv_mem hg) _).1 h1
      simpa [mul_assoc] using this
    have e2 : g⁻¹ * (b⁻¹ * g * b * g⁻¹) * g = g⁻¹ * b⁻¹ * g * b := by group
    rw [e2] at h2
    simpa [mul_assoc] using h2

theorem mem_centralizerMod_iff {N B : Subgroup G} {g : G} :
    g ∈ centralizerMod N B ↔ g ∈ normalizer (N : Set G) ∧
      ∀ b ∈ B, ∀ hb : b ∈ normalizer (N : Set G), g * b * g⁻¹ * b⁻¹ ∈ N := by
  unfold centralizerMod
  rw [NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, fun b hbB hb => ?_⟩
    have := mem_centralizer_iff.1 hc (NormalizerQuotient.proj N ⟨b, hb⟩)
      (NormalizerQuotient.proj_mem_bar hbB)
    exact (commutator_mem_iff_proj hg hb).1 this
  · rintro ⟨hg, hc⟩
    refine ⟨hg, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨⟨b, hb⟩, hbB, rfl⟩ := hy
    exact (commutator_mem_iff_proj hg hb).2 (hc b (mem_subgroupOf.1 hbB) hb)

theorem mem_centerMod_iff {N A : Subgroup G} (hNA : N ≤ A) {g : G} :
    g ∈ centerMod N A ↔ g ∈ A ∧ g ∈ normalizer (N : Set G) ∧
      ∀ a ∈ A, ∀ ha : a ∈ normalizer (N : Set G), g * a * g⁻¹ * a⁻¹ ∈ N := by
  unfold centerMod upperCenterMod
  rw [NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, hz⟩
    obtain ⟨z, hz1, hz2⟩ := hz
    have hzg : (z : NormalizerQuotient.Bar N) = NormalizerQuotient.proj N ⟨g, hg⟩ := hz2
    have hmem : NormalizerQuotient.proj N ⟨g, hg⟩ ∈ NormalizerQuotient.bar N A := by
      rw [← hzg]; exact z.2
    refine ⟨(NormalizerQuotient.mem_bar_iff hNA ⟨g, hg⟩).1 hmem, hg, fun a ha han => ?_⟩
    rw [Subgroup.upperCentralSeries_one] at hz1
    have := Subgroup.mem_center_iff.1 hz1 ⟨NormalizerQuotient.proj N ⟨a, han⟩,
      NormalizerQuotient.proj_mem_bar ha⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [hzg] at h2
    exact (commutator_mem_iff_proj hg han).1 h2
  · rintro ⟨hgA, hg, hc⟩
    refine ⟨hg, ⟨⟨NormalizerQuotient.proj N ⟨g, hg⟩,
      NormalizerQuotient.proj_mem_bar hgA⟩, ?_, rfl⟩⟩
    rw [Subgroup.upperCentralSeries_one]
    refine Subgroup.mem_center_iff.2 fun w => ?_
    obtain ⟨⟨a, han⟩, haA, hw⟩ := w.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hw]
    exact (commutator_mem_iff_proj hg han).2 (hc a (mem_subgroupOf.1 haA) han)


theorem map_conj_inv_map_conj_inv {g : G} (hg : g * g = 1) (A : Subgroup G) :
    (Aᵍ[g])ᵍ[g] = A := by
  have hcomp : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)).comp
      (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) = MonoidHom.id G := by
    ext x
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    have h1 : g * (g * x * g) * g = (g * g) * x * (g * g) := by group
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgi, inv_inv,
      MonoidHom.id_apply]
    rw [h1, hg]
    simp
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

@[expose] abbrev uG {q : ℕ} (d : TrialityD4Data L q) : G :=
  ((d.u : L) : G)

@[expose] abbrev vG {q : ℕ} (d : TrialityD4Data L q) : G :=
  ((d.v : L) : G)

@[expose] def jZeroCentralizer {q : ℕ} (d : TrialityD4Data L q) : Subgroup G :=
  centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)

@[expose] noncomputable def prodX {q : ℕ} (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaD₅ d t ⊓ jZeroCentralizer d

@[expose] def cLV {q : ℕ} (d : TrialityD4Data L q) : Subgroup G :=
  (centralizer (d.V : Set L)).map L.subtype

@[expose] def lvM {q : ℕ} (d : TrialityD4Data L q) : Subgroup G :=
  (d.leviLong ⊔ d.M).map L.subtype

structure ProductHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : Prop where
  two_le : 2 ≤ f
  layer : h.LayerHyp d
  not_field : ¬ ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
    CFSG.IsComponent Kc ∧
    Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
          ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
    CFSG.Blueprint.LieModel Kc .PSL 3 2 (2 * f)

structure IsLayerComponent {q : ℕ} (d : TrialityD4Data L q) (t : G) (K : Subgroup G) : Prop where
  le : K ≤ jZeroCentralizer d
  isComponent : CFSG.IsComponent (K.subgroupOf (jZeroCentralizer d))
  ne : Kᵍ[t] ≠ K
  comm : ⁅K, Kᵍ[t]⁆ = ⊥
  layer_eq : jZeroLayer d = K ⊔ Kᵍ[t]

end Setting

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
