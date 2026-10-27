module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveTThree
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoGF
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Helpers

variable {G : Type} [Group G]

theorem le_normalizer_of_forall_conj_mem {H S : Subgroup G}
    (h : ∀ s ∈ S, ∀ x ∈ H, s * x * s⁻¹ ∈ H) : S ≤ normalizer (H : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h s hs x, fun hx => ?_⟩
  have h1 := h s⁻¹ (inv_mem hs) _ hx
  rwa [inv_inv, show s⁻¹ * (s * x * s⁻¹) * s = x by group] at h1

theorem le_of_isPGroup_of_not_dvd_relIndex [Finite G] {p : ℕ} [Fact p.Prime] {P N W : Subgroup G}
    (hP : IsPGroup p P) (hPN : P ≤ N) (hidx : ¬ p ∣ P.relIndex N) (hW : IsPGroup p W)
    (hWN : W ≤ N) (hNW : N ≤ normalizer (W : Set G)) : W ≤ P := by
  have hWP : IsPGroup p (W ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hW hP (hPN.trans hNW)
  have hle : W ⊔ P ≤ N := sup_le hWN hPN
  have hmul := Subgroup.relIndex_mul_relIndex P (W ⊔ P) N le_sup_right hle
  obtain ⟨k, hk⟩ := hWP.index (P.subgroupOf (W ⊔ P))
  have h1 : P.relIndex (W ⊔ P) = p ^ k := hk
  have hk0 : k = 0 := by
    by_contra hk0
    apply hidx
    rw [← hmul, h1]
    exact Dvd.dvd.mul_right (dvd_pow_self p hk0) _
  rw [hk0, pow_zero] at h1
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 h1)

theorem card_inf_centralizer_sq_le_of_card_eq_four [Finite G] {Z : Subgroup G} {u : G}
    (hZ : Nat.card Z = 4) (huZ : u ∉ centralizer (Z : Set G)) :
    Nat.card (Z ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 ≤ Nat.card Z := by
  have hdvd : Nat.card (Z ⊓ centralizer ({u} : Set G) : Subgroup G) ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hZ]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (Z ⊓ centralizer ({u} : Set G) : Subgroup G) ≠ 4 := by
    intro h4
    apply huZ
    have heq : Z ⊓ centralizer ({u} : Set G) = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hZ])
    rw [mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Z ⊓ centralizer ({u} : Set G) := by rw [heq]; exact hz
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hz').2
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hZ, hm']
  interval_cases m
  · norm_num
  · norm_num
  · exact absurd hm' (by simpa using hne)

end Helpers

section Core

variable {G : Type} [Group G] [Finite G]

theorem twentySeven_dvd_card_centralizer_of_swap (hSL : SLThreeGraphFieldFixInput)
    {F : Type} [Field F] [CharP F 2] (hF : Nat.card F = 4) {W₁ W₂ X : Subgroup G}
    (φ : X →* Matrix.SpecialLinearGroup (Fin 3) F) (hφ : Function.Surjective φ)
    (hker : ∀ x : X, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₂) (hW₁X : W₁ ≤ X) (hW₂X : W₂ ≤ X)
    (hW₁2 : ∀ w ∈ W₁, w * w = 1) (hW₂2 : ∀ w ∈ W₂, w * w = 1)
    (hN : W₁ ≤ normalizer (W₂ : Set G)) (hZc : Nat.card (W₁ ⊓ W₂ : Subgroup G) = 4)
    {u : G} (hu2 : u * u = 1) (huX : ∀ x ∈ X, u * x * u⁻¹ ∈ X)
    (h12 : ∀ w ∈ W₁, u * w * u⁻¹ ∈ W₂) (h21 : ∀ w ∈ W₂, u * w * u⁻¹ ∈ W₁)
    (B : Matrix.SpecialLinearGroup (Fin 3) F)
    (hB : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ = B * graphFieldSL F (φ x) * B⁻¹)
    (huZ : u ∉ centralizer ((W₁ ⊓ W₂ : Subgroup G) : Set G)) :
    27 ∣ Nat.card (centralizer ({u} : Set G)) := by
  have hZ2 : ∀ z ∈ W₁ ⊓ W₂, z * z = 1 := fun z hz => hW₁2 z (mem_inf.1 hz).1
  have huZ' : ∀ z ∈ W₁ ⊓ W₂, u * z * u⁻¹ ∈ W₁ ⊓ W₂ := fun z hz =>
    mem_inf.2 ⟨h21 z (mem_inf.1 hz).2, h12 z (mem_inf.1 hz).1⟩
  have hH1Z : HOneTrivial u (W₁ ⊓ W₂) :=
    hOneTrivial_of_card_sq_le hu2 hZ2 huZ' (card_inf_centralizer_sq_le_of_card_eq_four hZc huZ)
  have hH1 : HOneTrivial u (W₁ ⊔ W₂) :=
    hOneTrivial_sup_of_swap hu2 (fun a ha b hb => mul_comm_of_mul_self_eq_one hW₁2 ha hb)
      (fun a ha b hb => mul_comm_of_mul_self_eq_one hW₂2 ha hb) hN h12 h21 hH1Z
  have hα : ∀ x : X, φ ⟨u * x * u⁻¹, huX x x.2⟩ =
      ((MulAut.conj B).toMonoidHom.comp (graphFieldSL F)) (φ x) := fun x => by
    rw [hB x]
    rfl
  have hdvd := card_eqLocus_dvd_card_centralizer φ hφ hker (sup_le hW₁X hW₂X) hu2 huX _ hα hH1
  have hinv : ∀ y, B * graphFieldSL F (B * graphFieldSL F y * B⁻¹) * B⁻¹ = y :=
    involutive_of_surjective_of_conj φ hφ hu2 huX (fun y => B * graphFieldSL F y * B⁻¹) hB
  exact (hSL F hF B hinv).trans hdvd

end Core

@[expose] def LFiveGraphXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧
      ∃ (F : Type) (_ : Field F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ (X : Subgroup G) (φ : X →* Matrix.SpecialLinearGroup (Fin 3) F)
        (A : Matrix.SpecialLinearGroup (Fin 3) F) (hd₁X : ∀ x ∈ X, d₁ * x * d₁⁻¹ ∈ X),
        Function.Surjective φ ∧
        (∀ x : X, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₁.map (MulAut.conj d).toMonoidHom) ∧
        S₀ ≤ X ∧
        (∀ x : X, φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ = A * graphFieldSL F (φ x) * A⁻¹) ∧
        Nat.card (W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) = 4 ∧
        S₀ ≤ centralizer ((W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) ∧
        d₁ ∉ centralizer ((W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G)

section Setting

variable {G : Type} [Group G] [Finite G]

theorem swap_facts_of_graphSylowData {L : Subgroup G} {t : G} {W₁ : Subgroup G}
    (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (htN : t ∈ normalizer (W₁ : Set G)) {Kc : Subgroup (seitzHat W₁)} {S₀ : Subgroup G} {d : G}
    (hdata : IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d) {d₁ : G}
    (hd₁ : d₁ = d ∨ d₁ = d * t) {s : G} (hs : s ∈ S₀) :
    W₁ ≤ S₀ ∧ W₁.map (MulAut.conj d).toMonoidHom ≤ S₀ ∧
      W₁ ≤ normalizer ((W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, w * w = 1) ∧
      (∀ w ∈ W₁, s * d₁ * w * (s * d₁)⁻¹ ∈ W₁.map (MulAut.conj d).toMonoidHom) ∧
      (∀ w ∈ W₁.map (MulAut.conj d).toMonoidHom, s * d₁ * w * (s * d₁)⁻¹ ∈ W₁) := by
  obtain ⟨hS₀p, hS₀N, hS₀syl, -, hdS₀, hdt, hd2, -⟩ := hdata
  set W₂ := W₁.map (MulAut.conj d).toMonoidHom with hW₂def
  have hmemW₂ : ∀ v ∈ W₁, d * v * d⁻¹ ∈ W₂ := fun v hv => ⟨v, hv, rfl⟩
  have hW₂mem : ∀ w ∈ W₂, ∃ v ∈ W₁, w = d * v * d⁻¹ := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have hW₁p : IsPGroup 2 W₁ := IsPGroup.of_card hW₁c
  have hW₁N : W₁ ≤ seitzTilde W₁ Kc := by
    intro w hw
    refine mem_seitzTilde_iff.2 ⟨Subgroup.le_normalizer hw, ?_⟩
    have h1 : QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G)))
        ⟨w, Subgroup.le_normalizer hw⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)
    rw [h1]
    exact one_mem _
  have hW₁S₀ : W₁ ≤ S₀ := le_of_isPGroup_of_not_dvd_relIndex hS₀p hS₀N hS₀syl hW₁p hW₁N
    (seitzTilde_le_normalizer W₁ Kc)
  have hS₀W₁ : S₀ ≤ normalizer (W₁ : Set G) := hS₀N.trans (seitzTilde_le_normalizer W₁ Kc)
  have hdconj : ∀ x ∈ S₀, d * x * d⁻¹ ∈ S₀ := fun x hx => (mem_normalizer_iff.1 hdS₀ x).1 hx
  have hdconj' : ∀ x ∈ S₀, d⁻¹ * x * d ∈ S₀ := fun x hx => by
    have h1 := (mem_normalizer_iff.1 (inv_mem hdS₀) x).1 hx
    rwa [inv_inv] at h1
  have hW₂S₀ : W₂ ≤ S₀ := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hW₂mem w hw
    exact hdconj v (hW₁S₀ hv)
  have hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg w hw => ?_
    obtain ⟨v, hv, rfl⟩ := hW₂mem w hw
    have h1 : (d⁻¹ * g * d) * v * (d⁻¹ * g * d)⁻¹ ∈ W₁ :=
      (mem_normalizer_iff.1 (hS₀W₁ (hdconj' g hg)) v).1 hv
    have h2 := hmemW₂ _ h1
    rwa [show d * ((d⁻¹ * g * d) * v * (d⁻¹ * g * d)⁻¹) * d⁻¹ = g * (d * v * d⁻¹) * g⁻¹ by
      group] at h2
  have hW₂2 : ∀ w ∈ W₂, w * w = 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hW₂mem w hw
    calc d * v * d⁻¹ * (d * v * d⁻¹) = d * (v * v) * d⁻¹ := by group
      _ = 1 := by rw [hW₁2 v hv]; group
  have htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => (mem_normalizer_iff.1 htN w).1 hw
  have hd₁W₁ : ∀ w ∈ W₁, d₁ * w * d₁⁻¹ ∈ W₂ := by
    intro w hw
    rcases hd₁ with rfl | rfl
    · exact hmemW₂ w hw
    · have h1 := hmemW₂ _ (htW₁ w hw)
      rwa [show d * (t * w * t⁻¹) * d⁻¹ = d * t * w * (d * t)⁻¹ by group] at h1
  have h12 : ∀ w ∈ W₁, s * d₁ * w * (s * d₁)⁻¹ ∈ W₂ := by
    intro w hw
    have h1 := (mem_normalizer_iff.1 (hS₀W₂ hs) _).1 (hd₁W₁ w hw)
    rwa [show s * (d₁ * w * d₁⁻¹) * s⁻¹ = s * d₁ * w * (s * d₁)⁻¹ by group] at h1
  have h21 : ∀ w ∈ W₂, s * d₁ * w * (s * d₁)⁻¹ ∈ W₁ := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hW₂mem w hw
    have hsd : s * (d * d) ∈ S₀ := mul_mem hs hd2
    have hud : (s * d₁ * d) * v * (s * d₁ * d)⁻¹ ∈ W₁ := by
      rcases hd₁ with h | h
      · rw [h]
        have h1 := (mem_normalizer_iff.1 (hS₀W₁ hsd) v).1 hv
        rwa [show s * (d * d) * v * (s * (d * d))⁻¹ = s * d * d * v * (s * d * d)⁻¹ by
          group] at h1
      · rw [h]
        have h1 := (mem_normalizer_iff.1 (hS₀W₁ hsd) _).1 (htW₁ v hv)
        have h2 : s * (d * t) * d = s * (d * d) * t := by
          calc s * (d * t) * d = s * d * (t * d) := by group
            _ = s * d * (d * t) := by rw [hdt]
            _ = s * (d * d) * t := by group
        rw [h2]
        rwa [show s * (d * d) * (t * v * t⁻¹) * (s * (d * d))⁻¹ =
          s * (d * d) * t * v * (s * (d * d) * t)⁻¹ by group] at h1
    rwa [show s * d₁ * d * v * (s * d₁ * d)⁻¹ = s * d₁ * (d * v * d⁻¹) * (s * d₁)⁻¹ by
      group] at hud
  exact ⟨hW₁S₀, hW₂S₀, hW₁S₀.trans hS₀W₂, hW₂2, h12, h21⟩

omit [Finite G] in
theorem conj_facts_of_X {F : Type} [Field F] [CharP F 2] {X : Subgroup G}
    (φ : X →* Matrix.SpecialLinearGroup (Fin 3) F) {d₁ s : G}
    (A : Matrix.SpecialLinearGroup (Fin 3) F) (hd₁X : ∀ x ∈ X, d₁ * x * d₁⁻¹ ∈ X)
    (hφd₁ : ∀ x : X, φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ = A * graphFieldSL F (φ x) * A⁻¹)
    (hsX : s ∈ X) :
    ∃ huX : ∀ x ∈ X, s * d₁ * x * (s * d₁)⁻¹ ∈ X,
      ∀ x : X, φ ⟨s * d₁ * x * (s * d₁)⁻¹, huX x x.2⟩ =
        (φ ⟨s, hsX⟩ * A) * graphFieldSL F (φ x) * (φ ⟨s, hsX⟩ * A)⁻¹ := by
  have huX : ∀ x ∈ X, s * d₁ * x * (s * d₁)⁻¹ ∈ X := by
    intro x hx
    have h1 := mul_mem (mul_mem hsX (hd₁X x hx)) (inv_mem hsX)
    rwa [show s * (d₁ * x * d₁⁻¹) * s⁻¹ = s * d₁ * x * (s * d₁)⁻¹ by group] at h1
  refine ⟨huX, fun x => ?_⟩
  have h1 : (⟨s * d₁ * x * (s * d₁)⁻¹, huX x x.2⟩ : X) =
      ⟨s, hsX⟩ * ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ * ⟨s, hsX⟩⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h1, map_mul, map_mul, map_inv, hφd₁]
  group

end Setting

theorem lFiveGraphCosetThreeInput_of_X (hX : LFiveGraphXInput)
    (hSL : SLThreeGraphFieldFixInput) : LFiveGraphCosetThreeInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨d₁, hd₁, F, _, _, hF, X, φ, A, hd₁X, hφ, hker, hS₀X, hφd₁, hZc, hS₀Z, hd₁Z⟩ :=
    hX G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  refine ⟨d₁, hd₁, fun s hs hinv => ?_⟩
  obtain ⟨hW₁S₀, hW₂S₀, hN, hW₂2, h12, h21⟩ :=
    swap_facts_of_graphSylowData hW₁c hW₁2 htN hdata hd₁ hs
  obtain ⟨huX, hB⟩ := conj_facts_of_X φ A hd₁X hφd₁ (hS₀X hs)
  have huZ : s * d₁ ∉ centralizer
      ((W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) := by
    intro hu
    apply hd₁Z
    rw [mem_centralizer_iff] at hu ⊢
    intro z hz
    have hsz := (mem_centralizer_iff.1 (hS₀Z hs)) z hz
    have h1 := hu z hz
    have h2 : s * (z * d₁) = s * (d₁ * z) := by
      calc s * (z * d₁) = (s * z) * d₁ := by group
        _ = (z * s) * d₁ := by rw [hsz]
        _ = z * (s * d₁) := by group
        _ = s * d₁ * z := h1
        _ = s * (d₁ * z) := by group
    exact mul_left_cancel h2
  exact twentySeven_dvd_card_centralizer_of_swap hSL hF φ hφ hker (hW₁S₀.trans hS₀X)
    (hW₂S₀.trans hS₀X) hW₁2 hW₂2 hN hZc hinv huX h12 h21 _ hB huZ

end CFSG.SeitzReduction.LinearPilot
