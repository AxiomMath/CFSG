module

public import CFSG.Fischer.Classification.PartII.Twins.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

structure IsTwinSection (E μ : Set H) : Prop where
  subset : μ ⊆ E
  mul_mul_mem : ∀ s ∈ μ, ∀ t ∈ μ, s * t * s ∈ μ
  exists_isTwin : ∀ a ∈ E, ∃ s ∈ μ, IsTwin E a s
  eq_of_isTwin : ∀ s ∈ μ, ∀ t ∈ μ, IsTwin E s t → s = t

noncomputable def sec (E μ : Set H) (a : H) : H :=
  Classical.epsilon fun s => s ∈ μ ∧ IsTwin E a s

namespace IsTwinSection

variable (hμ : IsTwinSection E μ)
include hμ

theorem sec_spec {a : H} (ha : a ∈ E) : sec E μ a ∈ μ ∧ IsTwin E a (sec E μ a) :=
  Classical.epsilon_spec (hμ.exists_isTwin a ha)

theorem sec_mem {a : H} (ha : a ∈ E) : sec E μ a ∈ μ := (hμ.sec_spec ha).1

theorem isTwin_sec {a : H} (ha : a ∈ E) : IsTwin E a (sec E μ a) := (hμ.sec_spec ha).2

theorem eq_sec {a s : H} (hs : s ∈ μ) (h : IsTwin E a s) : s = sec E μ a :=
  hμ.eq_of_isTwin _ hs _ (hμ.sec_mem h.1) (isTwin_trans (isTwin_symm h) (hμ.isTwin_sec h.1))

theorem sec_eq_self {s : H} (hs : s ∈ μ) : sec E μ s = s :=
  (hμ.eq_sec hs (isTwin_refl (hμ.subset hs))).symm

theorem sec_eq_sec {a b : H} (h : IsTwin E a b) : sec E μ a = sec E μ b :=
  (hμ.eq_sec (hμ.sec_mem h.2.1) (isTwin_trans h (hμ.isTwin_sec h.2.1))).symm

theorem sec_ne {f : H} (hf : f ∉ μ) (hfE : f ∈ E) : sec E μ f ≠ f := fun e =>
  hf (e ▸ hμ.sec_mem hfE)

variable (hP : Pair H E)
include hP

theorem conj_notMem {s f : H} (hs : s ∈ μ) (hf : f ∉ μ) : s * f * s ∉ μ := fun h => hf (by
  rw [← Pair.mul_mul_mul_mul hP (hμ.subset hs) f]
  exact hμ.mul_mul_mem s hs _ h)

theorem sec_mul_mul {a b : H} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a) :
    sec E μ (a * b * a) = sec E μ a * sec E μ b * sec E μ a := by
  have hsa := hμ.isTwin_sec ha
  have hsb := hμ.isTwin_sec hb
  have h1 : IsTwin E (a * b * a) (sec E μ a * b * sec E μ a) :=
    Pair.isTwin_mul_mul hP hsa hb hab
  have h2 : IsTwin E (sec E μ a * b * sec E μ a) (sec E μ a * sec E μ b * sec E μ a) := by
    have := isTwin_conj hP (sec E μ a) hsb
    rwa [Pair.inv_eq hP (hμ.subset (hμ.sec_mem ha))] at this
  exact (hμ.eq_sec (hμ.mul_mul_mem _ (hμ.sec_mem ha) _ (hμ.sec_mem hb))
    (isTwin_trans h1 h2)).symm

theorem existsUnique_match {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E)
    (hfg : f * g ≠ g * f) :
    ∃! g', g' ∈ twinClass E g ∧ g' ∉ μ ∧ f * g' * f ∈ μ := by
  set r := f * g * f with hr
  have hrE : r ∈ E := Pair.mul_mul_mem hP hf hg
  set g' := f * sec E μ r * f with hg'
  have hsr := hμ.isTwin_sec hrE
  have hg'g : g' ∈ twinClass E g := by
    have h := isTwin_conj hP f hsr
    rwa [Pair.inv_eq hP hf, hr, Pair.mul_mul_mul_mul hP hf] at h
  have hfg'f : f * g' * f = sec E μ r := by
    rw [hg', Pair.mul_mul_mul_mul hP hf]
  refine ⟨g', ⟨hg'g, fun hg'μ => ?_, hfg'f ▸ hμ.sec_mem hrE⟩, ?_⟩
  ·
    have hg'sec : g' = sec E μ g := hμ.eq_sec hg'μ hg'g
    have hsf := hμ.isTwin_sec hf
    have hsfE := hμ.subset (hμ.sec_mem hf)
    have hsgE := hμ.subset (hμ.sec_mem hg)
    have hsec : sec E μ r = sec E μ f * sec E μ g * sec E μ f := hμ.sec_mul_mul hP hf hg hfg
    have hne : f ≠ sec E μ f := (hμ.sec_ne hfμ hf).symm
    have hfsg : f * sec E μ g ≠ sec E μ g * f := fun e =>
      (not_commute_of_isTwin (hμ.isTwin_sec hg) hf fun e' => hfg e'.symm) e.symm
    obtain ⟨-, hne'⟩ := Pair.isTwin_conj_mul_mul hP (isTwin_symm hsf) hne.symm hsgE
      (not_commute_of_isTwin hsf hsgE hfsg)
    apply hne'
    have e1 : f * sec E μ g * f = sec E μ f * sec E μ g * sec E μ f := by
      rw [← hsec, ← hfg'f, hg'sec]
    calc sec E μ f * f * sec E μ g * (sec E μ f * f)
        = sec E μ f * (f * sec E μ g * f) * sec E μ f := by
          rw [mul_mul_mul_mul_eq (isTwin_symm hsf).2.2.1]
      _ = sec E μ g := by rw [e1, Pair.mul_mul_mul_mul hP hsfE]
  · rintro y ⟨hyg, -, hyμ⟩
    have hyr : IsTwin E r (f * y * f) := by
      have h := isTwin_conj hP f (isTwin_of_mem (self_mem_twinClass hg) hyg)
      rwa [Pair.inv_eq hP hf] at h
    have h := hμ.eq_sec hyμ hyr
    rw [hg', ← h, Pair.mul_mul_mul_mul hP hf]

theorem isMatch_conj {s f : H} (hs : s ∈ μ) (hf : f ∈ E) (hfμ : f ∉ μ)
    (hsf : s * f ≠ f * s) : f ∈ E ∧ f ∉ μ ∧ (s * f * s) ∈ E ∧ (s * f * s) ∉ μ ∧ f * (s * f * s) ≠ (s * f * s) * f ∧ f * (s * f * s) * f ∈ μ := by
  have hsE := hμ.subset hs
  refine ⟨hf, hfμ, Pair.mul_mul_mem hP hsE hf, hμ.conj_notMem hP hs hfμ, ?_, ?_⟩
  · rw [Pair.mul_mul_eq hP hsE hf hsf]
    exact fun h => Pair.mul_mul_not_commute_left hP hf (fun e => hsf e.symm) h.symm
  · rw [Pair.mul_mul_eq hP hsE hf hsf, Pair.mul_mul_mul_mul hP hf]
    exact hs

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
