module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuJ

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

@[expose] def stabOf (t : Fin 8) : List Lin8 := glList.filter fun r => linApply r t == t

@[expose] def transCheck (t : Fin 8) : Bool :=
  let St := stabOf t
  ((ppOf t).all fun m₁ => (ppOf t).all fun m₂ => St.any fun r => maskApply (adMat r) m₁ == m₂) &&
  (all8.all fun s₁ => s₁ == 0 || s₁ == t || all8.all fun s₂ => s₂ == 0 || s₂ == t ||
     St.any fun r => linApply r s₁ == s₂) &&
  ((ppOf t).all fun m => all8.all fun s => all256.any fun n => bC n m == s) &&
  (all8.all fun s₁ => s₁ == 0 || s₁ == t ||
     (St.filter fun r => linApply r s₁ == s₁).length == 4)

theorem transCheck_eq : ∀ t : Fin 8, t ≠ 0 → transCheck t = true := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  all_goals decide +kernel

theorem mem_stabOf {t : Fin 8} {r : Lin8} : r ∈ stabOf t ↔ r ∈ glList ∧ linApply r t = t := by
  simp [stabOf]

theorem mem_all8 (s : Fin 8) : s ∈ all8 := by simp [all8]

theorem exists_stab_mask {t : Fin 8} (ht : t ≠ 0) {m₁ m₂ : Nat} (h₁ : m₁ ∈ ppOf t)
    (h₂ : m₂ ∈ ppOf t) : ∃ r ∈ glList, linApply r t = t ∧ maskApply (adMat r) m₁ = m₂ := by
  have h := transCheck_eq t ht
  simp only [transCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨r, hr, h1⟩ := h.1.1.1 m₁ h₁ m₂ h₂
  exact ⟨r, (mem_stabOf.mp hr).1, (mem_stabOf.mp hr).2, h1⟩

theorem exists_stab_code {t : Fin 8} (ht : t ≠ 0) {s₁ s₂ : Fin 8} (h₁ : s₁ ≠ 0) (h₁' : s₁ ≠ t)
    (h₂ : s₂ ≠ 0) (h₂' : s₂ ≠ t) : ∃ r ∈ glList, linApply r t = t ∧ linApply r s₁ = s₂ := by
  have h := transCheck_eq t ht
  simp only [transCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h.1.1.2 s₁ (mem_all8 _) with (h | h) | h
  · exact absurd h h₁
  · exact absurd h h₁'
  · rcases h s₂ (mem_all8 _) with (h | h) | ⟨r, hr, h1⟩
    · exact absurd h h₂
    · exact absurd h h₂'
    · exact ⟨r, (mem_stabOf.mp hr).1, (mem_stabOf.mp hr).2, h1⟩

theorem exists_bC_eq {t : Fin 8} (ht : t ≠ 0) {m : Nat} (hm : m ∈ ppOf t) (s : Fin 8) :
    ∃ n < 256, bC n m = s := by
  have h := transCheck_eq t ht
  simp only [transCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq, RuSimCode.mem_all256] at h
  exact h.1.2 m hm s (mem_all8 _)

theorem axis_length {t : Fin 8} (ht : t ≠ 0) {s₁ : Fin 8} (h₁ : s₁ ≠ 0) (h₁' : s₁ ≠ t) :
    ((stabOf t).filter fun r => linApply r s₁ == s₁).length = 4 := by
  have h := transCheck_eq t ht
  simp only [transCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h.2 s₁ (mem_all8 _) with (h | h) | h
  · exact absurd h h₁
  · exact absurd h h₁'
  · exact h

theorem pair_xor : ∀ t s : Fin 8, ∀ a ∈ [0, t, s, t ^^^ s], ∀ b ∈ [0, t, s, t ^^^ s],
    a ^^^ b ∈ [0, t, s, t ^^^ s] := by
  decide

theorem pair_nodup : ∀ t s : Fin 8, t ≠ 0 → s ≠ 0 → s ≠ t → [0, t, s, t ^^^ s].Nodup := by
  decide

end RuQCode

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem exists_conj_eq_mul {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) {x : G} (hx : x ∈ X)
    (hxA : x ∉ gmsA L T) {a : G} (ha : a ∈ gmsA L T) : ∃ w ∈ R, w * x * w⁻¹ = a * x := by
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  obtain ⟨hxR, hxm⟩ := (hX x).mp hx
  have hm : μ x ∈ RuQCode.ppOf (ν f) := by
    rcases List.mem_cons.mp hxm with h | h
    · exact absurd ((hM.ker x hxR).mp h) hxA
    · exact h
  obtain ⟨n, hn, hnm⟩ := RuQCode.exists_bC_eq ht hm (ν a)
  obtain ⟨w, hw, hwn⟩ := hM.surj n hn
  have hc := hM.comm hw hxR
  rw [hwn, hnm] at hc
  have h1 := hM.eq_of_ν_eq (hM.comm_mem _ hw _ hxR) ha hc
  refine ⟨w, hw, ?_⟩
  calc w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
    _ = a * x := by rw [h1]

theorem exists_conj_eq_of_not_mem
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {f : G} (hfA : f ∈ gmsA L T)
    (hf1 : f ≠ 1) {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {x x' : G} (hx : x ∈ X) (hxA : x ∉ gmsA L T) (hx' : x' ∈ X) (hx'A : x' ∉ gmsA L T) :
    ∃ g ∈ normalizer (R : Set G), g * f * g⁻¹ = f ∧ g * x * g⁻¹ = x' := by
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  obtain ⟨hxR, hxm⟩ := (hX x).mp hx
  obtain ⟨hx'R, hx'm⟩ := (hX x').mp hx'
  have hm : μ x ∈ RuQCode.ppOf (ν f) := by
    rcases List.mem_cons.mp hxm with h | h
    · exact absurd ((hM.ker x hxR).mp h) hxA
    · exact h
  have hm' : μ x' ∈ RuQCode.ppOf (ν f) := by
    rcases List.mem_cons.mp hx'm with h | h
    · exact absurd ((hM.ker x' hx'R).mp h) hx'A
    · exact h
  obtain ⟨r, hr, hrt, hrm⟩ := RuQCode.exists_stab_mask ht hm hm'
  obtain ⟨g, hgN, hgA, hgR⟩ := hM.exists_code_eq hNC hidx hr
  have hgf : g * f * g⁻¹ = f :=
    hM.eq_of_ν_eq (hM.normA g hgN f hfA) hfA (by rw [hgA f hfA, hrt])
  have hgxR : g * x * g⁻¹ ∈ R := (mem_normalizer_iff.mp hgN x).mp hxR
  have hμ : μ x' = μ (g * x * g⁻¹) := by rw [hgR x hxR, hrm]
  have ha := hM.mul_inv_mem_of_μ_eq hx'R hgxR hμ
  have hgxX : g * x * g⁻¹ ∈ X :=
    (mem_normalizer_iff.mp (hM.mem_normalizer_plane hX hgN hgf hfA) x).mp hx
  have hgxA : g * x * g⁻¹ ∉ gmsA L T := by
    intro h
    apply hxA
    have := hM.normA g⁻¹ (inv_mem hgN) _ h
    simpa [mul_assoc] using this
  obtain ⟨w, hw, hwx⟩ := hM.exists_conj_eq_mul hfA hf1 hX hgxX hgxA ha
  refine ⟨w * g, mul_mem (le_normalizer hw) hgN, ?_, ?_⟩
  · rw [show w * g * f * (w * g)⁻¹ = w * (g * f * g⁻¹) * w⁻¹ by group, hgf,
      hM.central w hw f hfA]
    group
  · rw [show w * g * x * (w * g)⁻¹ = w * (g * x * g⁻¹) * w⁻¹ by group, hwx]
    group

theorem exists_conj_eq_of_mem_gmsA
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {f : G} (hfA : f ∈ gmsA L T)
    (hf1 : f ≠ 1) {a a' : G} (ha : a ∈ gmsA L T) (ha1 : a ≠ 1) (haf : a ≠ f)
    (ha' : a' ∈ gmsA L T) (ha'1 : a' ≠ 1) (ha'f : a' ≠ f) :
    ∃ g ∈ normalizer (R : Set G), g * f * g⁻¹ = f ∧ g * a * g⁻¹ = a' := by
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  have hne : ∀ b ∈ gmsA L T, b ≠ 1 → b ≠ f → ν b ≠ 0 ∧ ν b ≠ ν f := fun b hb hb1 hbf =>
    ⟨fun h => hb1 (hM.ν_inj b hb h), fun h => hbf (hM.eq_of_ν_eq hb hfA h)⟩
  obtain ⟨h1, h1'⟩ := hne a ha ha1 haf
  obtain ⟨h2, h2'⟩ := hne a' ha' ha'1 ha'f
  obtain ⟨r, hr, hrt, hrs⟩ := RuQCode.exists_stab_code ht h1 h1' h2 h2'
  obtain ⟨g, hgN, hgA, -⟩ := hM.exists_code_eq hNC hidx hr
  exact ⟨g, hgN, hM.eq_of_ν_eq (hM.normA g hgN f hfA) hfA (by rw [hgA f hfA, hrt]),
    hM.eq_of_ν_eq (hM.normA g hgN a ha) ha' (by rw [hgA a ha, hrs])⟩

theorem exists_conj_eq_of_mem_plane
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {f : G} (hfA : f ∈ gmsA L T)
    (hf1 : f ≠ 1) {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) {x x' : G}
    (hx : x ∈ X) (hx1 : x ≠ 1) (hxf : x ≠ f) (hx' : x' ∈ X) (hx'1 : x' ≠ 1) (hx'f : x' ≠ f) :
    ∃ h ∈ centralizer ({f} : Set G), h * x * h⁻¹ = x' := by
  classical
  obtain ⟨h₀, hh₀, a₀, ha₀, hout⟩ : ∃ h₀ ∈ centralizer ({f} : Set G), ∃ a₀ ∈ gmsA L T,
      h₀ * a₀ * h₀⁻¹ ∉ gmsA L T := by
    by_contra hall
    push Not at hall
    exact hnot fun h hh => mem_normalizer_of_conj_mem_of_finite fun a ha => hall h hh a ha
  have hh₀f : h₀ * f * h₀⁻¹ = f := by
    rw [mem_centralizer_singleton_iff.mp hh₀]
    group
  have hAX : gmsA L T ≤ X := hM.gmsA_le_plane hX
  set x₀ := h₀ * a₀ * h₀⁻¹ with hx₀
  have hx₀X : x₀ ∈ X := (mem_normalizer_iff.mp (hXH hh₀) a₀).mp (hAX ha₀)
  have ha₀1 : a₀ ≠ 1 := fun h => hout (by rw [hx₀, h]; simp [one_mem])
  have ha₀f : a₀ ≠ f := fun h => hout (by rw [hx₀, h, hh₀f]; exact hfA)
  have key : ∀ y ∈ X, y ≠ 1 → y ≠ f → ∃ h ∈ centralizer ({f} : Set G), h * y * h⁻¹ = x₀ := by
    intro y hy hy1 hyf
    have hcen : ∀ g ∈ normalizer (R : Set G), g * f * g⁻¹ = f → g ∈ centralizer ({f} : Set G) :=
      fun g _ hgf => mem_centralizer_singleton_iff.mpr (by
        calc g * f = g * f * g⁻¹ * g := by group
          _ = f * g := by rw [hgf])
    by_cases hyA : y ∈ gmsA L T
    · obtain ⟨g, hgN, hgf, hgy⟩ :=
        hM.exists_conj_eq_of_mem_gmsA hNC hidx hfA hf1 hyA hy1 hyf ha₀ ha₀1 ha₀f
      refine ⟨h₀ * g, mul_mem hh₀ (hcen g hgN hgf), ?_⟩
      rw [show h₀ * g * y * (h₀ * g)⁻¹ = h₀ * (g * y * g⁻¹) * h₀⁻¹ by group, hgy]
    · obtain ⟨g, hgN, hgf, hgy⟩ :=
        hM.exists_conj_eq_of_not_mem hNC hidx hfA hf1 hX hy hyA hx₀X hout
      exact ⟨g, hcen g hgN hgf, hgy⟩
  obtain ⟨h₁, hh₁, h1⟩ := key x hx hx1 hxf
  obtain ⟨h₂, hh₂, h2⟩ := key x' hx' hx'1 hx'f
  refine ⟨h₂⁻¹ * h₁, mul_mem (inv_mem hh₂) hh₁, ?_⟩
  rw [show h₂⁻¹ * h₁ * x * (h₂⁻¹ * h₁)⁻¹ = h₂⁻¹ * (h₁ * x * h₁⁻¹) * h₂ by group, h1, ← h2]
  group


omit [Finite G] in
theorem card_R : Nat.card R = 2 ^ 11 := by
  classical
  have h := card_eq_length_mul_card hM.le μ (List.range 256) List.nodup_range
    (fun a ha => List.mem_range.mpr (hM.lt a ha))
    (fun c hc => by
      obtain ⟨x, hx, hxc⟩ := hM.surj c (List.mem_range.mp hc)
      exact ⟨x, hx, hxc⟩)
    (fun a ha b hb => by
      rw [← hM.ker _ (mul_mem (inv_mem ha) hb), hM.mul _ (inv_mem ha) _ hb, hM.μ_inv ha]
      exact ⟨fun h => by rw [h]; exact Nat.xor_self _, RuQCode.nat_eq_of_xor_eq_zero⟩)
  rw [List.length_range, hM.card_gmsA] at h
  rw [h]
  norm_num

theorem card_centralizer_inf_eq
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {f f₁ : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hf₁A : f₁ ∈ gmsA L T) (hf₁1 : f₁ ≠ 1)
    (hf₁f : f₁ ≠ f) :
    Nat.card (centralizer ({f} : Set G) ⊓ centralizer ({f₁} : Set G) : Subgroup G) =
      2 ^ 13 := by
  classical
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  have ht₁ : ν f₁ ≠ 0 := fun h => hf₁1 (hM.ν_inj f₁ hf₁A h)
  have ht₁' : ν f₁ ≠ ν f := fun h => hf₁f (hM.eq_of_ν_eq hf₁A hfA h)
  set l : List (Fin 8) := [0, ν f, ν f₁, ν f ^^^ ν f₁] with hl
  let F₁ : Subgroup G :=
    { carrier := {x | x ∈ gmsA L T ∧ ν x ∈ l}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        show ν (a * b) ∈ l
        rw [hM.ν_mul _ ha _ hb]
        exact RuQCode.pair_xor _ _ _ ha' _ hb'
      one_mem' := ⟨one_mem _, by show ν 1 ∈ l; rw [hM.ν_one]; exact List.mem_cons_self⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, by show ν a⁻¹ ∈ l; rw [hM.ν_inv ha]; exact ha'⟩ }
  have hF₁ : ∀ x, x ∈ F₁ ↔ x ∈ gmsA L T ∧ ν x ∈ l := fun x => Iff.rfl
  have hF₁A : F₁ ≤ gmsA L T := fun x hx => ((hF₁ x).mp hx).1
  have hF₁c : Nat.card F₁ = 4 := by
    have h := card_eq_length_mul_card (bot_le : (⊥ : Subgroup G) ≤ F₁) ν l
      (RuQCode.pair_nodup _ _ ht ht₁ ht₁') (fun a ha => ((hF₁ a).mp ha).2)
      (fun c hc => by
        obtain ⟨b, hb, hbc⟩ := hM.ν_surj c
        exact ⟨b, (hF₁ b).mpr ⟨hb, by rw [hbc]; exact hc⟩, hbc⟩)
      (fun a ha b hb => by
        rw [mem_bot, inv_mul_eq_one]
        exact ⟨fun h => hM.eq_of_ν_eq (hF₁A ha) (hF₁A hb) h, fun h => by rw [h]⟩)
    rw [card_bot, mul_one] at h
    rw [h]
    rfl
  set H' := centralizer ({f} : Set G) ⊓ centralizer ({f₁} : Set G) with hH'
  have hH'N : H' ≤ normalizer (R : Set G) := by
    refine le_trans ?_ (h216 F₁ hF₁A hF₁c)
    intro g hg
    obtain ⟨hgf, hgf₁⟩ := mem_inf.mp hg
    have hcf : g * f * g⁻¹ = f := by rw [mem_centralizer_singleton_iff.mp hgf]; group
    have hcf₁ : g * f₁ * g⁻¹ = f₁ := by rw [mem_centralizer_singleton_iff.mp hgf₁]; group
    refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    obtain ⟨hxA, hxl⟩ := (hF₁ x).mp hx
    have hcases : x = 1 ∨ x = f ∨ x = f₁ ∨ x = f * f₁ := by
      simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hxl
      rcases hxl with h | h | h | h
      · exact Or.inl (hM.ν_inj x hxA h)
      · exact Or.inr (Or.inl (hM.eq_of_ν_eq hxA hfA h))
      · exact Or.inr (Or.inr (Or.inl (hM.eq_of_ν_eq hxA hf₁A h)))
      · exact Or.inr (Or.inr (Or.inr (hM.eq_of_ν_eq hxA (mul_mem hfA hf₁A)
          (by rw [h, hM.ν_mul _ hfA _ hf₁A]))))
    have hgx : g * x * g⁻¹ = x := by
      rcases hcases with rfl | rfl | rfl | rfl
      · group
      · exact hcf
      · exact hcf₁
      · rw [show g * (f * f₁) * g⁻¹ = (g * f * g⁻¹) * (g * f₁ * g⁻¹) by group, hcf, hcf₁]
    rw [hgx]
    exact hx
  choose! rOf hrGL hrA hrR using hM.act
  have hRH' : R ≤ H' := fun w hw => mem_inf.mpr
    ⟨mem_centralizer_singleton_iff.mpr (hM.central w hw f hfA),
      mem_centralizer_singleton_iff.mpr (hM.central w hw f₁ hf₁A)⟩
  set lc := (RuQCode.stabOf (ν f)).filter fun r => linApply r (ν f₁) == ν f₁ with hlc
  have hlcn : lc.Nodup := List.Nodup.filter _ (List.Nodup.filter _ RuQCode.glList_nodup)
  have hfix : ∀ g ∈ H', linApply (rOf g) (ν f) = ν f ∧ linApply (rOf g) (ν f₁) = ν f₁ := by
    intro g hg
    obtain ⟨hgf, hgf₁⟩ := mem_inf.mp hg
    have hgN := hH'N hg
    constructor
    · rw [← hrA g hgN f hfA, mem_centralizer_singleton_iff.mp hgf]
      congr 1
      group
    · rw [← hrA g hgN f₁ hf₁A, mem_centralizer_singleton_iff.mp hgf₁]
      congr 1
      group
  have h := card_eq_length_mul_card hRH' rOf lc hlcn
    (fun g hg => by
      have hgN := hH'N hg
      obtain ⟨h1, h2⟩ := hfix g hg
      rw [hlc, List.mem_filter, RuQCode.mem_stabOf]
      exact ⟨⟨hrGL g hgN, h1⟩, by simp [h2]⟩)
    (fun c hc => by
      rw [hlc, List.mem_filter, RuQCode.mem_stabOf] at hc
      obtain ⟨⟨hcGL, hct⟩, hct₁⟩ := hc
      simp only [beq_iff_eq] at hct₁
      obtain ⟨g, hgN, hgA, -⟩ := hM.exists_code_eq hNC hidx hcGL
      have hgf : g * f * g⁻¹ = f :=
        hM.eq_of_ν_eq (hM.normA g hgN f hfA) hfA (by rw [hgA f hfA, hct])
      have hgf₁ : g * f₁ * g⁻¹ = f₁ :=
        hM.eq_of_ν_eq (hM.normA g hgN f₁ hf₁A) hf₁A (by rw [hgA f₁ hf₁A, hct₁])
      refine ⟨g, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
        mem_centralizer_singleton_iff.mpr ?_⟩, hM.code_unique (hrA g hgN) hgA⟩
      · calc g * f = g * f * g⁻¹ * g := by group
          _ = f * g := by rw [hgf]
      · calc g * f₁ = g * f₁ * g⁻¹ * g := by group
          _ = f₁ * g := by rw [hgf₁])
    (fun a ha b hb => by
      have haN := hH'N ha
      have hbN := hH'N hb
      constructor
      · intro hab
        rw [← hNC]
        refine mem_inf.mpr ⟨mul_mem (inv_mem haN) hbN, mem_centralizer_iff.mpr fun c hc => ?_⟩
        have h1 := hM.eq_of_ν_eq (hM.normA a haN c hc) (hM.normA b hbN c hc)
          (by rw [hrA a haN c hc, hrA b hbN c hc, hab])
        calc c * (a⁻¹ * b) = a⁻¹ * (a * c * a⁻¹) * b := by group
          _ = a⁻¹ * (b * c * b⁻¹) * b := by rw [h1]
          _ = a⁻¹ * b * c := by group
      · intro hw
        refine hM.code_unique (hrA a haN) fun c hc => ?_
        have e : a * c * a⁻¹ = b * ((a⁻¹ * b)⁻¹ * c * (a⁻¹ * b)) * b⁻¹ := by group
        rw [e, show (a⁻¹ * b)⁻¹ * c * (a⁻¹ * b) = c by
          rw [mul_assoc, ← hM.central _ hw c hc]; group, hrA b hbN c hc])
  rw [RuQCode.axis_length ht ht₁ ht₁', hM.card_R] at h
  rw [h]
  norm_num


theorem card_centralizer_eq
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) :
    Nat.card (centralizer ({f} : Set G)) = 30 * 2 ^ 13 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  obtain ⟨s, hs0, hst⟩ : ∃ s : Fin 8, s ≠ 0 ∧ s ≠ ν f := by
    have key : ∀ t : Fin 8, ∃ s : Fin 8, s ≠ 0 ∧ s ≠ t := by decide
    exact key _
  obtain ⟨f₁, hf₁A, hf₁s⟩ := hM.ν_surj s
  have hf₁1 : f₁ ≠ 1 := fun h => hs0 (by rw [← hf₁s, h, hM.ν_one])
  have hf₁f : f₁ ≠ f := fun h => hst (by rw [← hf₁s, h])
  have hAX : gmsA L T ≤ X := hM.gmsA_le_plane hX
  set l : List G := (((Finset.univ.filter (· ∈ X)).erase 1).erase f).toList with hl
  have hmem : ∀ c, c ∈ l ↔ c ∈ X ∧ c ≠ 1 ∧ c ≠ f := by
    intro c
    simp only [hl, Finset.mem_toList, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
      true_and]
    tauto
  have hlen : l.length = 30 := by
    have h1 : (Finset.univ.filter (· ∈ X)).card = 32 := by
      rw [← hM.card_plane hX hfA hf1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hl, Finset.length_toList, Finset.card_erase_of_mem, Finset.card_erase_of_mem, h1]
    · simp [one_mem]
    · simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Ne.symm hf1 |>.symm, hAX hfA⟩
  have hKH : centralizer ({f} : Set G) ⊓ centralizer ({f₁} : Set G) ≤
      centralizer ({f} : Set G) := inf_le_left
  have h := card_eq_length_mul_card hKH (fun h => h * f₁ * h⁻¹) l (Finset.nodup_toList _)
    (fun h hh => by
      have hhf : h * f * h⁻¹ = f := by rw [mem_centralizer_singleton_iff.mp hh]; group
      refine (hmem _).mpr ⟨(mem_normalizer_iff.mp (hXH hh) f₁).mp (hAX hf₁A), fun h1 => ?_,
        fun h1 => ?_⟩
      · apply hf₁1
        calc f₁ = h⁻¹ * (h * f₁ * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      · apply hf₁f
        calc f₁ = h⁻¹ * (h * f₁ * h⁻¹) * h := by group
          _ = h⁻¹ * (h * f * h⁻¹) * h := by rw [h1, hhf]
          _ = f := by group)
    (fun c hc => by
      obtain ⟨hcX, hc1, hcf⟩ := (hmem c).mp hc
      obtain ⟨h, hh, hhc⟩ := hM.exists_conj_eq_of_mem_plane hNC hidx hfA hf1 hX hXH hnot
        (hAX hf₁A) hf₁1 hf₁f hcX hc1 hcf
      exact ⟨h, hh, hhc⟩)
    (fun a ha b hb => by
      constructor
      · intro hab
        refine mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, mem_centralizer_singleton_iff.mpr ?_⟩
        calc a⁻¹ * b * f₁ = a⁻¹ * (b * f₁ * b⁻¹) * b := by group
          _ = a⁻¹ * (a * f₁ * a⁻¹) * b := by rw [hab]
          _ = f₁ * (a⁻¹ * b) := by group
      · intro hab
        have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hab).2
        calc a * f₁ * a⁻¹ = a * (a⁻¹ * b * f₁ * (a⁻¹ * b)⁻¹) * a⁻¹ := by
              rw [h1]; group
          _ = b * f₁ * b⁻¹ := by group)
  rw [hlen, hM.card_centralizer_inf_eq hNC hidx h216 hfA hf1 hf₁A hf₁1 hf₁f] at h
  exact h

theorem mem_J_iff_of_mem_centralizer
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G)) (hRp : IsPGroup 2 R)
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) (hRS : R ≤ S) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f) {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) {J : Subgroup G}
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f)
    (h : G) : h ∈ J ↔ h ∈ centralizer ({f} : Set G) ∧
      ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ = 1 ∨ h * x * h⁻¹ * x⁻¹ = f := by
  have hAX : gmsA L T ≤ X := hM.gmsA_le_plane hX
  constructor
  · intro hh
    obtain ⟨hhS, hc⟩ := (hJ h).mp hh
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, hc⟩
    calc h * f = h * f * h⁻¹ * h := by group
      _ = f * h := by rw [hfS h hhS]
  · rintro ⟨-, hc⟩
    refine (hJ h).mpr ⟨?_, hc⟩
    have hhA : h ∈ normalizer (gmsA L T : Set G) := by
      refine mem_normalizer_of_conj_mem_of_finite fun a ha => ?_
      rcases hc a (hAX ha) with h1 | h1
      · rw [show h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a by group, h1, one_mul]
        exact ha
      · rw [show h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a by group, h1]
        exact mul_mem hfA ha
    have hhN : h ∈ normalizer (R : Set G) := hNA ▸ hhA
    obtain ⟨r, hr, hrA, -⟩ := hM.act h hhN
    rcases List.mem_cons.mp (hM.code_mem_tvOf hr hrA (fun b hb => hc b (hAX hb))
      (hM.normA h hhN)) with h1 | h1
    · exact hRS (hM.mem_of_code_eq_linId hNC hhN (by rw [← h1]; exact hrA))
    · obtain ⟨g, hgS, hgA, -⟩ :=
        hM.exists_mem_sylow_code_eq hRp hNC hidx hSN hfA hf1 hfS h1
      have hgN := hSN.le hgS
      have hgh : g⁻¹ * h ∈ R := by
        rw [← hNC]
        refine mem_inf.mpr ⟨mul_mem (inv_mem hgN) hhN, mem_centralizer_iff.mpr fun c hc' => ?_⟩
        have e := hM.eq_of_ν_eq (hM.normA g hgN c hc') (hM.normA h hhN c hc')
          (by rw [hgA c hc', hrA c hc'])
        calc c * (g⁻¹ * h) = g⁻¹ * (g * c * g⁻¹) * h := by group
          _ = g⁻¹ * (h * c * h⁻¹) * h := by rw [e]
          _ = g⁻¹ * h * c := by group
      rw [show h = g * (g⁻¹ * h) by group]
      exact mul_mem hgS (hRS hgh)

theorem relIndex_J_eq (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) (hRS : R ≤ S) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f)
    (h210 : ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R)
    {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {J : Subgroup G} (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f)
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) :
    J.relIndex (centralizer ({f} : Set G)) = 120 := by
  obtain ⟨hcardJ, -, hJS, -⟩ := hM.J_props hRp hNC hidx hSN hRS hfA hf1 hfS h210 hX hJ
  have hJH : J ≤ centralizer ({f} : Set G) := fun v hv => mem_centralizer_singleton_iff.mpr (by
    calc v * f = v * f * v⁻¹ * v := by group
      _ = f * v := by rw [hfS v (hJS hv)])
  have h1 := Subgroup.relIndex_mul_card J (centralizer ({f} : Set G))
  rw [inf_eq_left.mpr hJH, hcardJ,
    hM.card_centralizer_eq hNC hidx h216 hfA hf1 hX hXH hnot] at h1
  omega

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
