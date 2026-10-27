module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step27
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step29

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Three

theorem le_normalizer_of_commutator_mem {P E C : Subgroup G}
    (hPE : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ E) (hEC : E ≤ C) (hCP : C ≤ P) :
    P ≤ normalizer (C : Set G) := fun p hp =>
  Sec2.mem_normalizer_of_forall_conj_mem fun c hc => by
    have h := hPE _ hp _ (hCP hc)
    have : p * c * p⁻¹ = (p * c * p⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact mul_mem (hEC h) hc

theorem forall_mem_of_three {P E C₁ C₂ C₃ : Subgroup G} {f : G}
    (hPE : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ E) (hEC₁ : E ≤ C₁) (hEC₃ : E ≤ C₃)
    (hC₁P : C₁ ≤ P) (hC₂P : C₂ ≤ P) (hC₃P : C₃ ≤ P) (h12 : C₁ ⊔ C₂ = P) (h13 : C₁ ⊔ C₃ = P)
    (h23 : C₂ ⊓ C₃ ≤ E) (hf2 : f ∈ normalizer (C₂ : Set G)) (hf3 : f ∈ normalizer (C₃ : Set G))
    (hf1 : ∀ c ∈ C₁, c⁻¹ * (f⁻¹ * c * f) ∈ E) : ∀ p ∈ P, p⁻¹ * (f⁻¹ * p * f) ∈ E := by
  have hEP : E ≤ P := hEC₁.trans hC₁P
  have hEn : ∀ b ∈ P, ∀ e ∈ E, b⁻¹ * e * b ∈ E := fun b hb e he => by
    have h := hPE _ (inv_mem hb) _ (hEP he)
    have : b⁻¹ * e * b = (b⁻¹ * e * b⁻¹⁻¹ * e⁻¹) * e := by group
    rw [this]
    exact mul_mem h he
  have hδ : ∀ a b : G, (a * b)⁻¹ * (f⁻¹ * (a * b) * f) =
      (b⁻¹ * (a⁻¹ * (f⁻¹ * a * f)) * b) * (b⁻¹ * (f⁻¹ * b * f)) := fun a b => by group
  have hδC : ∀ C : Subgroup G, f ∈ normalizer (C : Set G) → ∀ c ∈ C,
      c⁻¹ * (f⁻¹ * c * f) ∈ C := fun C hfC c hc => by
    have : f⁻¹ * c * f ∈ C := by
      have := (mem_normalizer_iff.mp (inv_mem hfC) c).mp hc
      simpa using this
    exact mul_mem (inv_mem hc) this
  have hC₂ : ∀ c ∈ C₂, c⁻¹ * (f⁻¹ * c * f) ∈ E := by
    intro c hc
    have hc' : c ∈ ((C₁ ⊔ C₃ : Subgroup G) : Set G) := by rw [h13]; exact hC₂P hc
    rw [coe_mul_of_right_le_normalizer_left C₁ C₃
      (hC₃P.trans (le_normalizer_of_commutator_mem hPE hEC₁ hC₁P))] at hc'
    obtain ⟨c₁, hc₁, c₃, hc₃, rfl⟩ := hc'
    have he := hEn _ (hC₃P hc₃) _ (hf1 c₁ hc₁)
    have hmem3 : (c₁ * c₃)⁻¹ * (f⁻¹ * (c₁ * c₃) * f) ∈ C₃ := by
      rw [hδ]
      exact mul_mem (hEC₃ he) (hδC C₃ hf3 c₃ hc₃)
    exact h23 ⟨hδC C₂ hf2 _ hc, hmem3⟩
  intro p hp
  have hp' : p ∈ ((C₁ ⊔ C₂ : Subgroup G) : Set G) := by rw [h12]; exact hp
  rw [coe_mul_of_right_le_normalizer_left C₁ C₂
    (hC₂P.trans (le_normalizer_of_commutator_mem hPE hEC₁ hC₁P))] at hp'
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hp'
  rw [hδ]
  exact mul_mem (hEn _ (hC₂P hc₂) _ (hf1 c₁ hc₁)) (hC₂ c₂ hc₂)

omit [Finite G] in
theorem rightConjugate_mem_planes_sec2P {E F V : Subgroup G} (hV : V ∈ planes E F)
    (hVP : V ≤ sec2P E) {n : G} (hn : n ∈ normalizer (sec2P E : Set G)) :
    rightConjugate V n ∈ planes E F ∧ rightConjugate V n ≤ sec2P E :=
  ⟨rightConjugate_mem_planes hV n, by
    rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVP n⟩

end Three

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

section Plane

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include hx hxS

theorem sup_rightConjugate_sec2F0_eq {m : G} (hm : m ∈ normalizer (E : Set G)) :
    E ⊔ rightConjugate (sec2F0 A E x) m =
      rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m := by
  rw [centralizerMod_eq_sup_sec2F0 h11 hE16 hF hL hodd hx hxS, rightConjugate_sup',
    (rightConjugate_eq_self_iff E m).mpr hm]

theorem inf_rightConjugate_sec2F0_eq {m : G} (hm : m ∈ normalizer (E : Set G)) :
    E ⊓ rightConjugate (sec2F0 A E x) m = E ⊓ A := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hEm := (rightConjugate_eq_self_iff E m).mpr hm
  have hEAm := (rightConjugate_eq_self_iff _ m).mpr (hD.normalizer_le_normalizer hm)
  calc E ⊓ rightConjugate (sec2F0 A E x) m
      = rightConjugate E m ⊓ rightConjugate (sec2F0 A E x) m := by rw [hEm]
    _ = rightConjugate (sec2F0 A E x ⊓ E) m := by
        rw [AschbacherTheorem3.rightConjugate_inf]
        exact inf_comm _ _
    _ = E ⊓ A := by rw [sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS, hEAm]

theorem exists_eq_of_mem_planes_ne {V : Subgroup G} (hV : V ∈ planes E F) (hVP : V ≤ sec2P E)
    (hVE : V ≠ E) : ∃ m ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      V = rightConjugate (sec2F0 A E x) m ∧
      E ⊔ V = rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m ∧
      E ⊓ V = E ⊓ A := by
  rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hV hVP with h | ⟨m, hm, rfl⟩
  · exact absurd h hVE
  obtain ⟨hmE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hm
  exact ⟨m, hm, rfl, sup_rightConjugate_sec2F0_eq h11 hE16 hF hL hodd hx hxS hmE,
    inf_rightConjugate_sec2F0_eq h11 hE16 hF hL hodd hx hxS hmE⟩

theorem eq_of_mem_sup_of_not_mem {V W : Subgroup G} (hV : V ∈ planes E F) (hVP : V ≤ sec2P E)
    (hVE : V ≠ E) (hW : W ∈ planes E F) (hWP : W ≤ sec2P E) (hWE : W ≠ E) {t : G}
    (htV : t ∈ E ⊔ V) (htW : t ∈ E ⊔ W) (htE : t ∉ E) : V = W := by
  obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  obtain ⟨-, hW64⟩ := isElemAbelian_and_card_of_mem_planes hF hW
  obtain ⟨m, hm, hVm, hVC, -⟩ :=
    exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS hV hVP hVE
  obtain ⟨m', hm', hWm, hWC, -⟩ :=
    exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS hW hWP hWE
  obtain ⟨hmE, hmR⟩ := mem_normalizer_of_mem_inf_normalizer hF hm
  obtain ⟨hm'E, hm'R⟩ := mem_normalizer_of_mem_inf_normalizer hF hm'
  have hCC := rightConjugate_centralizerMod_eq h11 hE16 hF hL hodd hmE hmR hm'E hm'R
    (hVC ▸ htV) (hWC ▸ htW) htE
  have hle : V ≤ rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m' := by
    rw [← hCC, ← hVC]
    exact le_sup_right
  rcases le_or_le_of_le_rightConjugate h11 hE16 hF hL hodd hx hxS hm'E hVe hle with h | h
  · exact absurd (eq_of_le_of_card_ge h (by rw [hV64, hF.cardE])) hVE
  · rw [← hWm] at h
    exact eq_of_le_of_card_ge h (by rw [hV64, hW64])

variable (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include h4

theorem exists_sec2P_eq_rightConjugate : ∃ j : G,
    (sec2F0 A E x = rightConjugate E j ∧ sec2P E = rightConjugate (sec2P E) j) ∨
      (sec2F0 A E x = rightConjugate F j ∧ sec2P E = rightConjugate (sec2P F) j) := by
  have hF0pl := sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4
  have hF0P := sec2F0_le_sec2P hF x
  have hEAF0 := inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd hF0pl hF0P
  have hP1024 := card_sec2P_of_frame h11 hE16 hF hL hodd
  have hPN := sec2P_le_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS
  obtain ⟨j, hj | hj⟩ := hF0pl
  · refine ⟨j, Or.inl ⟨hj, ?_⟩⟩
    obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
    have hEAj := rightConjugate_inf_eq_of_points h11 hE16 hF hL hodd hD
      (card_inf_left hF hodd) (hj ▸ hF0P) (hj ▸ hEAF0)
    have hle := sec2P_le_rightConjugate_of_points h11 hE16 hF hL hodd
      (fun hq hqC _ hm => mem_sec2P_of_pow_two h11 hE16 hF hL hodd hq hqC hm) hEAj (hj ▸ hPN)
    exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  · refine ⟨j, Or.inr ⟨hj, ?_⟩⟩
    obtain ⟨hDF, -⟩ := exists_pointsData h11 hE16 hF.symm hL hodd
    have hEAj := rightConjugate_inf_eq_of_points h11 hE16 hF hL hodd hDF
      (card_inf_left hF.symm hodd) (hj ▸ hF0P) (hj ▸ hEAF0)
    have hle := sec2P_le_rightConjugate_of_points h11 hE16 hF hL hodd
      (fun hq hqC _ hm => mem_sec2P_of_pow_two h11 hE16 hF.symm hL hodd hq hqC hm) hEAj
      (hj ▸ hPN)
    exact eq_of_le_of_card_ge hle (by
      rw [rightConjugate_card, card_sec2P_of_frame h11 hE16 hF.symm hL hodd, hP1024])

theorem sq_mem_and_commutator_mem_sec2F0 {a b : G} (ha : a ∈ sec2P E) (hb : b ∈ sec2P E) :
    a * a ∈ sec2F0 A E x ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2F0 A E x := by
  obtain ⟨j, ⟨hj, hP⟩ | ⟨hj, hP⟩⟩ :=
    exists_sec2P_eq_rightConjugate h11 hE16 hF hL hodd hx hxS h4
  · obtain ⟨-, -, hq⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
    have ha' : a ∈ rightConjugate (sec2P E) j := hP ▸ ha
    have hb' : b ∈ rightConjugate (sec2P E) j := hP ▸ hb
    rw [mem_rightConjugate_iff] at ha' hb'
    obtain ⟨h1, h2⟩ := hq _ ha' _ hb'
    rw [hj, mem_rightConjugate_iff, mem_rightConjugate_iff]
    exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩
  · obtain ⟨-, -, hq⟩ := isElemQuot_sec2P h11 hE16 hF.symm hL hodd
    have ha' : a ∈ rightConjugate (sec2P F) j := hP ▸ ha
    have hb' : b ∈ rightConjugate (sec2P F) j := hP ▸ hb
    rw [mem_rightConjugate_iff] at ha' hb'
    obtain ⟨h1, h2⟩ := hq _ ha' _ hb'
    rw [hj, mem_rightConjugate_iff, mem_rightConjugate_iff]
    exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩

theorem sq_mem_and_commutator_mem_inf {a b : G} (ha : a ∈ sec2P E) (hb : b ∈ sec2P E) :
    a * a ∈ E ⊓ A ∧ a * b * a⁻¹ * b⁻¹ ∈ E ⊓ A := by
  obtain ⟨-, -, hq⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  obtain ⟨h1, h2⟩ := hq a ha b hb
  obtain ⟨h3, h3'⟩ := sq_mem_and_commutator_mem_sec2F0 h11 hE16 hF hL hodd hx hxS h4 ha hb
  rw [← sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS]
  exact ⟨⟨h3, h1⟩, ⟨h3', h2⟩⟩

theorem normalizer_sec2P_le_normalizer_inf :
    normalizer (sec2P E : Set G) ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
  intro n hn
  refine Sec2.mem_normalizer_of_forall_conj_mem fun e he => ?_
  have hstab : ∀ V ∈ planes E F, V ≤ sec2P E → E ⊓ A ≤ rightConjugate V n := fun V hV hVP =>
    inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd (rightConjugate_mem_planes hV n) (by
      rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVP n)
  have h1 := (mem_rightConjugate_iff _ n e).mp
    (hstab E ⟨1, Or.inl (rightConjugate_one E).symm⟩ (le_sec2P_of_frame hF) he)
  have h2 := (mem_rightConjugate_iff _ n e).mp
    (hstab _ (sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4) (sec2F0_le_sec2P hF x) he)
  rw [← sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS]
  exact ⟨h2, h1⟩

theorem sec2P_le_normalizer_of_le {B : Subgroup G} (hEB : E ⊓ A ≤ B) (hBP : B ≤ sec2P E) :
    sec2P E ≤ normalizer (B : Set G) :=
  le_normalizer_of_commutator_mem
    (fun _ ha _ hb => (sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 ha hb).2)
    hEB hBP

theorem inf_sup_eq_of_mem_planes {V₁ V₂ V₃ : Subgroup G} (h₁ : V₁ ∈ planes E F)
    (h₁P : V₁ ≤ sec2P E) (h₂ : V₂ ∈ planes E F) (h₂P : V₂ ≤ sec2P E) (h₃ : V₃ ∈ planes E F)
    (h₃P : V₃ ≤ sec2P E) (h12 : V₁ ≠ V₂) (h13 : V₁ ≠ V₃) (h23 : V₂ ≠ V₃) :
    V₃ ⊓ (V₁ ⊔ V₂) = E ⊓ A := by
  have hNP := normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4
  have hEpl : E ∈ planes E F := ⟨1, Or.inl (rightConjugate_one E).symm⟩
  obtain ⟨n, hn, hVn⟩ := exists_mem_normalizer_rightConjugate_eq h11 hE16 hF hL hodd hx hxS h4
    h₃ h₃P hEpl (le_sec2P_of_frame hF)
  obtain ⟨hW₁, hW₁P⟩ := rightConjugate_mem_planes_sec2P h₁ h₁P hn
  obtain ⟨hW₂, hW₂P⟩ := rightConjugate_mem_planes_sec2P h₂ h₂P hn
  have hinj : ∀ {U U' : Subgroup G}, rightConjugate U n = rightConjugate U' n → U = U' :=
    fun h => by
      have := congrArg (fun U => rightConjugate U n⁻¹) h
      simpa only [rightConjugate_inv_rightConjugate] using this
  have hW₁E : rightConjugate V₁ n ≠ E := fun h => h13 (hinj (h.trans hVn.symm))
  have hW₂E : rightConjugate V₂ n ≠ E := fun h => h23 (hinj (h.trans hVn.symm))
  have hW12 : rightConjugate V₁ n ≠ rightConjugate V₂ n := fun h => h12 (hinj h)
  obtain ⟨-, -, -, -, hEW₁⟩ :=
    exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS hW₁ hW₁P hW₁E
  obtain ⟨-, -, -, -, hEW₂⟩ :=
    exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS hW₂ hW₂P hW₂E
  have hEAW₁ := inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd hW₁ hW₁P
  have hcore : E ⊓ (rightConjugate V₁ n ⊔ rightConjugate V₂ n) = E ⊓ A := by
    refine le_antisymm (fun e he => ?_) (le_inf inf_le_left (hEAW₁.trans le_sup_left))
    have he' : e ∈ ((rightConjugate V₁ n ⊔ rightConjugate V₂ n : Subgroup G) : Set G) := he.2
    rw [coe_mul_of_right_le_normalizer_left _ _
      (hW₂P.trans (sec2P_le_normalizer_of_le h11 hE16 hF hL hodd hx hxS h4 hEAW₁ hW₁P))] at he'
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := he'
    have hw₂E : w₂ ∈ E := by
      by_contra hw₂E
      refine hW12 (eq_of_mem_sup_of_not_mem h11 hE16 hF hL hodd hx hxS hW₁ hW₁P hW₁E hW₂
        hW₂P hW₂E (t := w₂) ?_ (mem_sup_right hw₂) hw₂E)
      have : w₂ = w₁⁻¹ * (w₁ * w₂) := by group
      rw [this]
      exact mul_mem (mem_sup_right (inv_mem hw₁)) (mem_sup_left he.1)
    have hw₁E : w₁ ∈ E := by
      have : w₁ = (w₁ * w₂) * w₂⁻¹ := by group
      rw [this]
      exact mul_mem he.1 (inv_mem hw₂E)
    have h1 : w₁ ∈ E ⊓ A := hEW₁ ▸ ⟨hw₁E, hw₁⟩
    have h2 : w₂ ∈ E ⊓ A := hEW₂ ▸ ⟨hw₂E, hw₂⟩
    exact mul_mem h1 h2
  have h1 : rightConjugate (V₃ ⊓ (V₁ ⊔ V₂)) n = E ⊓ A := by
    rw [AschbacherTheorem3.rightConjugate_inf, rightConjugate_sup', hVn, hcore]
  have h2 := congrArg (fun U => rightConjugate U n⁻¹) h1
  simp only [rightConjugate_inv_rightConjugate] at h2
  rw [h2]
  exact (rightConjugate_eq_self_iff _ n⁻¹).mpr (hNP (inv_mem hn))

theorem exists_not_mem_normalizer_of_mem_inf {f : G} (hf : f ∈ F ⊓ A) (hfZ : f ∉ sec2Z A E F) :
    ∃ V ∈ planes E F, V ≤ sec2P E ∧ f ∉ normalizer (V : Set G) := by
  by_contra hall
  push Not at hall
  have h5 := ncard_planes_ne h11 hE16 hF hL hodd hx hxS h4
  have hF0E : sec2F0 A E x ≠ E := by
    have h := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rwa [rightConjugate_one] at h
  have hF0pl := sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4
  have hF0P := sec2F0_le_sec2P hF x
  have hF0mem : sec2F0 A E x ∈ {V | V ∈ planes E F ∧ V ≤ sec2P E ∧ V ≠ E} := ⟨hF0pl, hF0P, hF0E⟩
  obtain ⟨V₂, ⟨hV₂, hV₂P, hV₂E⟩, hV₂ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by rw [h5]; norm_num) (sec2F0 A E x)
  have h4' : 1 < ({V | V ∈ planes E F ∧ V ≤ sec2P E ∧ V ≠ E} \ {sec2F0 A E x}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hF0mem, h5]
    norm_num
  obtain ⟨V₃, ⟨⟨hV₃, hV₃P, hV₃E⟩, hV₃F0⟩, hV₃ne⟩ := Set.exists_ne_of_one_lt_ncard h4' V₂
  rw [Set.mem_singleton_iff] at hV₃F0
  have hEP := le_sec2P_of_frame hF
  have hPcard := card_sec2P_of_frame h11 hE16 hF hL hodd
  have hCcard := card_centralizerMod_of_frame h11 hE16 hF hL hodd
  have hcard256 : ∀ {V : Subgroup G}, V ∈ planes E F → V ≤ sec2P E → V ≠ E →
      Nat.card (E ⊔ V : Subgroup G) = 256 := fun hV hVP hVE => by
    obtain ⟨m, -, -, hVC, -⟩ := exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS hV hVP hVE
    rw [hVC, rightConjugate_card, hCcard]
  have hdis : ∀ {V W : Subgroup G}, V ∈ planes E F → V ≤ sec2P E → V ≠ E → W ∈ planes E F →
      W ≤ sec2P E → W ≠ E → V ≠ W → (E ⊔ V) ⊓ (E ⊔ W) ≤ E :=
    fun hV hVP hVE hW hWP hWE hVW t ht => by
      by_contra htE
      exact hVW (eq_of_mem_sup_of_not_mem h11 hE16 hF hL hodd hx hxS hV hVP hVE hW hWP hWE
        ht.1 ht.2 htE)
  have hsup : ∀ {V W : Subgroup G}, V ∈ planes E F → V ≤ sec2P E → V ≠ E → W ∈ planes E F →
      W ≤ sec2P E → W ≠ E → V ≠ W → (E ⊔ V) ⊔ (E ⊔ W) = sec2P E := by
    intro V W hV hVP hVE hW hWP hWE hVW
    have hle : (E ⊔ V) ⊔ (E ⊔ W) ≤ sec2P E := sup_le (sup_le hEP hVP) (sup_le hEP hWP)
    have hinf : (E ⊔ V) ⊓ (E ⊔ W) = E :=
      le_antisymm (hdis hV hVP hVE hW hWP hWE hVW) (le_inf le_sup_left le_sup_left)
    have hN : E ⊔ W ≤ normalizer ((E ⊔ V : Subgroup G) : Set G) :=
      (sup_le hEP hWP).trans (sec2P_le_normalizer_of_le h11 hE16 hF hL hodd hx hxS h4
        (inf_le_left.trans le_sup_left) (sup_le hEP hVP))
    have hc := card_sup_mul_card_inf hN
    rw [hinf, hcard256 hV hVP hVE, hcard256 hW hWP hWE, hF.cardE] at hc
    exact eq_of_le_of_card_ge hle (by rw [hPcard]; omega)
  have hfF : f ∈ F := hf.1
  have hfE : f ∈ normalizer (E : Set G) := hF.F_le_normalizer hL hodd hfF
  have hnorm : ∀ {V : Subgroup G}, V ∈ planes E F → V ≤ sec2P E →
      f ∈ normalizer ((E ⊔ V : Subgroup G) : Set G) :=
    fun hV hVP => mem_normalizer_sup hfE (hall _ hV hVP)
  have hC := centralizerMod_eq_sup_sec2F0 h11 hE16 hF hL hodd hx hxS
  have hf1 : ∀ c ∈ E ⊔ sec2F0 A E x, c⁻¹ * (f⁻¹ * c * f) ∈ E := by
    intro c hc
    have hcS : c ∈ sec2S A R E F := by
      rw [← hC] at hc
      exact mem_sup_right hc
    have hfS : f ∈ sec2S A R E F := mem_sup_left hfF
    have h := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd (inv_mem hcS)
      (inv_mem hfS)).2
    have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
    have : c⁻¹ * (f⁻¹ * c * f) = c⁻¹ * f⁻¹ * c⁻¹⁻¹ * f⁻¹⁻¹ := by group
    rw [this]
    exact hZE h
  obtain ⟨-, -, hPq⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  have hcen := forall_mem_of_three (fun a ha b hb => (hPq a ha b hb).2) le_sup_left le_sup_left
    (sup_le hEP hF0P) (sup_le hEP hV₂P) (sup_le hEP hV₃P)
    (hsup hF0pl hF0P hF0E hV₂ hV₂P hV₂E hV₂ne.symm)
    (hsup hF0pl hF0P hF0E hV₃ hV₃P hV₃E (Ne.symm hV₃F0))
    (hdis hV₂ hV₂P hV₂E hV₃ hV₃P hV₃E hV₃ne.symm) (hnorm hV₂ hV₂P) (hnorm hV₃ hV₃P) hf1
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hfR : rightConjugate R f = R := (rightConjugate_eq_self_iff R f).mpr
    (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨r, hF.R_le_F hr⟩ ⟨f, hfF⟩)))
  have hpts : pointsAction R E ⟨f, hfE⟩ = 1 := by
    refine Equiv.ext fun Q => Subtype.ext ?_
    rw [coe_pointsAction_apply, Equiv.Perm.one_apply]
    obtain ⟨p, hp, hpQ⟩ := htr Q Q.2
    have hRpE : rightConjugate R p ≤ E := hpQ ▸ Q.2.1
    rw [← hpQ]
    apply (rightConjugate_eq_self_iff _ _).mpr
    refine inv_mem ((rightConjugate_eq_self_iff _ _).mp ?_)
    set e' := p⁻¹ * (f⁻¹ * p * f) with he'
    have he := hcen p hp
    have hpE : rightConjugate (rightConjugate R p) e' = rightConjugate R p :=
      (rightConjugate_eq_self_iff _ _).mpr (centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun q hq => hD.comm q (hRpE hq) e' he))
    rw [rightConjugate_mul R p f, show p * f = f * p * e' by rw [he']; group,
      ← rightConjugate_mul R (f * p) e', ← rightConjugate_mul R f p, hfR, hpE]
  have hfE' := hD.mem_of_pointsAction_eq_one hCE hpts (n := 1)
    (by rw [pow_one]; exact hF.elemF.2 f hfF)
  exact hfZ (by rw [hF.sec2Z_eq]; exact ⟨⟨hfE', hfF⟩, hf.2⟩)

theorem exists_not_mem_normalizer_of_sec2U {u : G}
    (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G)) (hu3 : orderOf u = 3)
    (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    ∃ V ∈ planes E F, V ≤ sec2P E ∧ u ∉ normalizer (V : Set G) := by
  by_contra hall
  push Not at hall
  obtain ⟨-, huF, huEF, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  have huA' : u ∈ A := (Subgroup.mem_inf.mp huA).1
  have hZ16 : Nat.card (sec2Z A E F) < Nat.card (F ⊓ A : Subgroup G) := by
    rw [hF.card_sec2Z hodd, card_inf_left hF.symm hodd]
    norm_num
  obtain ⟨f, hf, hfZ⟩ : ∃ f ∈ F ⊓ A, f ∉ sec2Z A E F := by
    by_contra h
    push Not at h
    exact absurd (card_le_of_le fun f hf => h f hf) (not_le.mpr hZ16)
  have huZ : u ∈ normalizer (sec2Z A E F : Set G) := by
    rw [hF.sec2Z_eq]
    exact inf_normalizer_le_normalizer_inf ⟨huEF, le_normalizer huA'⟩
  have huFA : u ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨huF, le_normalizer huA'⟩
  set f' := f⁻¹ * (u⁻¹ * f * u) with hf'
  have hf'FA : f' ∈ F ⊓ A := by
    have h1 : u⁻¹ * f * u ∈ F ⊓ A := by
      have := (mem_normalizer_iff.mp (inv_mem huFA) f).mp hf
      simpa using this
    exact mul_mem (inv_mem hf) h1
  have hf'Z : f' ∉ sec2Z A E F := by
    intro h
    refine hfZ ?_
    have hZF : sec2Z A E F ≤ F := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_right
    have hcomm : f * f' = f' * f :=
      congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨f, hf.1⟩ ⟨f', hZF h⟩)
    have h' : u⁻¹ * f * u⁻¹⁻¹ * f⁻¹ ∈ sec2Z A F E := by
      rw [sec2Z_comm]
      have : u⁻¹ * f * u⁻¹⁻¹ * f⁻¹ = f' := by
        calc u⁻¹ * f * u⁻¹⁻¹ * f⁻¹ = f * f' * f⁻¹ := by rw [hf']; group
          _ = f' := by rw [hcomm]; group
      rw [this]
      exact h
    have := mem_sec2Z_of_conj_mul_inv_mem hF.symm hL hodd (A.inv_mem huA')
      (by rw [sec2Z_comm]; exact inv_mem huZ)
      (fun w hw hw' => hufix w (by rwa [sec2Z_comm] at hw) (by
        calc u * w * u⁻¹ = u * (u⁻¹ * w * u⁻¹⁻¹) * u⁻¹ := by rw [hw']
          _ = w := by group)) hf h'
    rwa [sec2Z_comm] at this
  obtain ⟨V, hV, hVP, hf'V⟩ :=
    exists_not_mem_normalizer_of_mem_inf h11 hE16 hF hL hodd hx hxS h4 hf'FA hf'Z
  refine hf'V ((rightConjugate_eq_self_iff _ _).mp ?_)
  have hfP : f ∈ normalizer (sec2P E : Set G) :=
    Sec2.normalizer_le_normalizer_sec2P E (hF.F_le_normalizer hL hodd hf.1)
  obtain ⟨hW, hWP⟩ := rightConjugate_mem_planes_sec2P hV hVP (inv_mem hfP)
  have hWu : rightConjugate (rightConjugate V f⁻¹) u⁻¹ = rightConjugate V f⁻¹ :=
    (rightConjugate_eq_self_iff _ _).mpr (inv_mem (hall _ hW hWP))
  have hVu : rightConjugate V u = V := (rightConjugate_eq_self_iff _ _).mpr (hall V hV hVP)
  rw [hf', show f⁻¹ * (u⁻¹ * f * u) = f⁻¹ * u⁻¹ * f * u by group,
    ← rightConjugate_mul V (f⁻¹ * u⁻¹ * f) u, ← rightConjugate_mul V (f⁻¹ * u⁻¹) f,
    ← rightConjugate_mul V f⁻¹ u⁻¹, hWu, rightConjugate_rightConjugate_inv, hVu]

end Plane

end Frame

end CFSG.ComponentClassification.AS81
