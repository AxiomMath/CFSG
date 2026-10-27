module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.RouteD.Sp3C4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem ncEdge_conj (hΩ : ConjInvariant Ω) (g x : G) {A B : Subgroup G}
    (h : NCEdge Ω x A B) : NCEdge Ω (g * x * g⁻¹) (conjSub g A) (conjSub g B) := by
  obtain ⟨hA, hB, hn⟩ := h
  refine ⟨?_, ?_, fun hc => hn ((commutes_conjSub_iff g).mp hc)⟩
  · rw [centralizingMembers_conj hΩ g x]
    exact ⟨A, hA, rfl⟩
  · rw [centralizingMembers_conj hΩ g x]
    exact ⟨B, hB, rfl⟩

theorem linked_conj (hΩ : ConjInvariant Ω) (g x : G) {A B : Subgroup G}
    (h : Linked Ω x A B) : Linked Ω (g * x * g⁻¹) (conjSub g A) (conjSub g B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (ncEdge_conj hΩ g x hbc)

theorem linked_conj_iff (hΩ : ConjInvariant Ω) (g x : G) {A B : Subgroup G} :
    Linked Ω (g * x * g⁻¹) (conjSub g A) (conjSub g B) ↔ Linked Ω x A B := by
  refine ⟨fun h => ?_, linked_conj hΩ g x⟩
  have h' := linked_conj hΩ g⁻¹ _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e, conjSub_inv_conjSub, conjSub_inv_conjSub] at h'

@[expose] def UnlinkedAt (Ω : Set (Subgroup G)) (A : Subgroup G) (a b : G) : Prop :=
  ∃ R ∈ centralizingMembers Ω {a * b, a}, ¬ Linked Ω (a * b) A R

@[expose] def CliqueAt (Ω : Set (Subgroup G)) (A B : Subgroup G) (a b : G) : Prop :=
  ∀ R ∈ centralizingMembers Ω {a * b, a}, ∀ L ∈ centralizingMembers Ω {a * b, a},
    R ≠ A → R ≠ B → L ≠ A → L ≠ B → Linked Ω (a * b) R L

private theorem pair_conj (hΩ : ConjInvariant Ω) (g a b : G) :
    centralizingMembers Ω {(g * a * g⁻¹) * (g * b * g⁻¹), g * a * g⁻¹} =
      conjSub g '' centralizingMembers Ω {a * b, a} := by
  have e : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  rw [e, centralizingMembers_pair_eq_inter, centralizingMembers_pair_eq_inter,
    centralizingMembers_conj hΩ g (a * b), centralizingMembers_conj hΩ g a,
    Set.image_inter (conjSub_injective g)]

theorem UnlinkedAt.conj (hΩ : ConjInvariant Ω) (g : G) {A : Subgroup G} {a b : G}
    (h : UnlinkedAt Ω A a b) :
    UnlinkedAt Ω (conjSub g A) (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨R, hR, hn⟩ := h
  refine ⟨conjSub g R, ?_, ?_⟩
  · rw [pair_conj hΩ]
    exact ⟨R, hR, rfl⟩
  · have e : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    rw [e, linked_conj_iff hΩ]
    exact hn

theorem CliqueAt.conj (hΩ : ConjInvariant Ω) (g : G) {A B : Subgroup G} {a b : G}
    (h : CliqueAt Ω A B a b) :
    CliqueAt Ω (conjSub g A) (conjSub g B) (g * a * g⁻¹) (g * b * g⁻¹) := by
  intro R hR L hL hRA hRB hLA hLB
  rw [pair_conj hΩ] at hR hL
  obtain ⟨R₀, hR₀, rfl⟩ := hR
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  have e : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  rw [e, linked_conj_iff hΩ]
  exact h R₀ hR₀ L₀ hL₀ (fun h' => hRA (by rw [h'])) (fun h' => hRB (by rw [h']))
    (fun h' => hLA (by rw [h'])) (fun h' => hLB (by rw [h']))

section Abstract

private theorem commutes_sSup_sSup {X : Type*} [Group X] {F₁ F₂ : Set (Subgroup X)}
    (h : ∀ N ∈ F₁, ∀ N' ∈ F₂, Commutes N N') : Commutes (sSup F₁) (sSup F₂) := by
  intro a ha b hb
  have key : ∀ N ∈ F₁, N ≤ Subgroup.centralizer ({b} : Set X) := by
    intro N hN n hn
    have hle : sSup F₂ ≤ Subgroup.centralizer (N : Set X) :=
      sSup_le fun N' hN' c hc =>
        Subgroup.mem_centralizer_iff.mpr fun n hn => h N hN N' hN' n hn c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hle hb) n hn)
  have hle : sSup F₁ ≤ Subgroup.centralizer ({b} : Set X) := sSup_le key
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

private theorem range_le_of_stable {K X : Type*} [Group K] [Group X]
    (hq : CFSG.Open.IsQuasisimple K) (φ : K →* X) (H : Subgroup X) (hHle : H ≤ φ.range)
    (hH : ∀ t ∈ φ.range, ∀ h ∈ H, t * h * t⁻¹ ∈ H)
    (hnc : ∃ a ∈ H, ∃ b ∈ φ.range, a * b ≠ b * a) : φ.range ≤ H := by
  have hN : (H.comap φ).Normal :=
    ⟨fun n hn g => by
      have := hH (φ g) ⟨g, rfl⟩ (φ n) hn
      simpa using this⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq (H.comap φ)
    with h | h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨k, rfl⟩ := hHle ha
    obtain ⟨g, rfl⟩ := hb
    have hk : k ∈ Subgroup.center K := h ha
    exact hab (by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hk g).symm])
  · rintro _ ⟨k, rfl⟩
    have : k ∈ H.comap φ := by rw [h]; trivial
    exact this

theorem family_split_empty {K X : Type*} [Group K] [Group X] (hq : CFSG.Open.IsQuasisimple K)
    (φ : K →* X) (F₁ F₂ : Set (Subgroup X)) (hle : ∀ N ∈ F₁ ∪ F₂, N ≤ φ.range)
    (hstab : ∀ t ∈ φ.range, ∀ N ∈ F₁ ∪ F₂, ∃ N' ∈ F₁ ∪ F₂, ∀ a ∈ N, t * a * t⁻¹ ∈ N')
    (hnc : ∀ N ∈ F₁ ∪ F₂, ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a)
    (hcomm : ∀ N ∈ F₁, ∀ N' ∈ F₂, Commutes N N') : F₁ = ∅ ∨ F₂ = ∅ := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := hne
  have hall₁ : ∀ N ∈ F₁, N ≤ sSup (F₁ ∪ F₂) := fun N hN => le_sSup (Or.inl hN)
  have hall₂ : ∀ N ∈ F₂, N ≤ sSup (F₁ ∪ F₂) := fun N hN => le_sSup (Or.inr hN)
  have hHallle : sSup (F₁ ∪ F₂) ≤ φ.range := sSup_le hle
  have hstabH : ∀ t ∈ φ.range, ∀ h ∈ sSup (F₁ ∪ F₂), t * h * t⁻¹ ∈ sSup (F₁ ∪ F₂) := by
    intro t ht
    have : sSup (F₁ ∪ F₂) ≤ (sSup (F₁ ∪ F₂)).comap (MulAut.conj t).toMonoidHom := by
      refine sSup_le fun N hN a ha => ?_
      obtain ⟨N', hN', hN'a⟩ := hstab t ht N hN
      exact le_sSup hN' (hN'a a ha)
    intro h hh
    exact this hh
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ := hnc N₁ (Or.inl hN₁)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂⟩ := hnc N₂ (Or.inr hN₂)
  have hTHall : φ.range ≤ sSup (F₁ ∪ F₂) :=
    range_le_of_stable hq φ _ hHallle hstabH
      ⟨a₁, hall₁ N₁ hN₁ ha₁, a₂, hle N₁ (Or.inl hN₁) ha₂, ha₁₂⟩
  have hsup : sSup (F₁ ∪ F₂) = sSup F₁ ⊔ sSup F₂ := sSup_union
  have hcomm' : Commutes (sSup F₁) (sSup F₂) := commutes_sSup_sSup hcomm
  have hH₁le : sSup F₁ ≤ φ.range := sSup_le fun N hN => hle N (Or.inl hN)
  have hH₂le : sSup F₂ ≤ φ.range := sSup_le fun N hN => hle N (Or.inr hN)
  have hstab₁ : ∀ t ∈ φ.range, ∀ h ∈ sSup F₁, t * h * t⁻¹ ∈ sSup F₁ := by
    intro t ht h hh
    have hnorm : sSup F₁ ⊔ sSup F₂ ≤ Subgroup.normalizer ((sSup F₁ : Subgroup X) : Set X) := by
      refine sup_le Subgroup.le_normalizer fun v hv => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have hc : ∀ w ∈ sSup F₂, ∀ y ∈ sSup F₁, w * y * w⁻¹ = y := fun w hw y hy => by
        have hyw : y * w = w * y := hcomm' y hy w hw
        calc w * y * w⁻¹ = (w * y) * w⁻¹ := rfl
          _ = (y * w) * w⁻¹ := by rw [hyw]
          _ = y := by group
      constructor
      · intro hu
        rw [hc v hv u hu]
        exact hu
      · intro hu
        have h1 := hc v⁻¹ ((sSup F₂).inv_mem hv) _ hu
        have e : v⁻¹ * (v * u * v⁻¹) * v⁻¹⁻¹ = u := by group
        rw [e] at h1
        rw [h1]
        exact hu
    have htsup : t ∈ sSup F₁ ⊔ sSup F₂ := hsup ▸ hTHall ht
    exact (Subgroup.mem_normalizer_iff.mp (hnorm htsup) h).mp hh
  have hT₁ : φ.range ≤ sSup F₁ :=
    range_le_of_stable hq φ _ hH₁le hstab₁
      ⟨a₁, le_sSup hN₁ ha₁, a₂, hle N₁ (Or.inl hN₁) ha₂, ha₁₂⟩
  exact hb₁₂ (hcomm' _ (hT₁ (hH₂le (le_sSup hN₂ hb₁))) _ (le_sSup hN₂ hb₂))

end Abstract

section Component

variable [Finite G]

theorem linked_of_le_range_of_quasisimple (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K) (φ : K →* locQuot Ω x)
    {A B : Subgroup G} (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    (hAc : locImg Ω x A ≤ φ.range) (hBc : locImg Ω x B ≤ φ.range) : Linked Ω x A B := by
  classical
  by_contra hAB
  obtain ⟨Fam, hFam⟩ : ∃ Fam : Set (Subgroup G), ∀ N, N ∈ Fam ↔
      N ∈ centralizingMembers Ω {x} ∧ locImg Ω x N ≤ φ.range := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : Set (Subgroup (locQuot Ω x)), F₁ =
      (locImg Ω x) '' {N | N ∈ Fam ∧ Linked Ω x A N} := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : Set (Subgroup (locQuot Ω x)), F₂ =
      (locImg Ω x) '' {N | N ∈ Fam ∧ ¬ Linked Ω x A N} := ⟨_, rfl⟩
  have hmem : ∀ N, N ∈ F₁ ∪ F₂ ↔ ∃ N₀ ∈ Fam, locImg Ω x N₀ = N := by
    intro N
    rw [Set.mem_union, hF₁, hF₂]
    constructor
    · rintro (⟨N₀, ⟨h, -⟩, rfl⟩ | ⟨N₀, ⟨h, -⟩, rfl⟩) <;> exact ⟨N₀, h, rfl⟩
    · rintro ⟨N₀, h, rfl⟩
      by_cases hl : Linked Ω x A N₀
      · exact Or.inl ⟨N₀, ⟨h, hl⟩, rfl⟩
      · exact Or.inr ⟨N₀, ⟨h, hl⟩, rfl⟩
  have hle : ∀ N ∈ F₁ ∪ F₂, N ≤ φ.range := by
    intro N hN
    obtain ⟨N₀, h, rfl⟩ := (hmem N).mp hN
    exact ((hFam N₀).mp h).2
  have hstab : ∀ t ∈ φ.range, ∀ N ∈ F₁ ∪ F₂, ∃ N' ∈ F₁ ∪ F₂, ∀ a ∈ N, t * a * t⁻¹ ∈ N' := by
    intro t ht N hN
    obtain ⟨N₀, h, rfl⟩ := (hmem N).mp hN
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨hNx, hNc⟩ := (hFam N₀).mp h
    have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      centralizingLayer_le_centralizer Ω {x} y.2
    have hN' : conjSub (y : G) N₀ ∈ Fam := by
      refine (hFam _).mpr ⟨⟨hΩ.conjInvariant _ _ hNx.1, fun a ha => ?_⟩, ?_⟩
      · rw [mem_conjSub_iff] at ha
        have hx' := hNx.2 ha
        have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
      · rw [locImg_conjSub_layer]
        rintro _ ⟨a, ha, rfl⟩
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
        exact φ.range.mul_mem (φ.range.mul_mem ht (hNc ha)) (φ.range.inv_mem ht)
    refine ⟨locImg Ω x (conjSub (y : G) N₀), (hmem _).mpr ⟨_, hN', rfl⟩, fun a ha => ?_⟩
    rw [locImg_conjSub_layer]
    exact ⟨a, ha, rfl⟩
  have hnc : ∀ N ∈ F₁ ∪ F₂, ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
    intro N hN
    obtain ⟨N₀, h, rfl⟩ := (hmem N).mp hN
    have := locImg_not_commutative hΩ hex ((hFam N₀).mp h).1
    push Not at this
    exact this
  have hcomm : ∀ N ∈ F₁, ∀ N' ∈ F₂, Commutes N N' := by
    rw [hF₁, hF₂]
    rintro _ ⟨N₁, ⟨h₁, hl₁⟩, rfl⟩ _ ⟨N₂, ⟨h₂, hl₂⟩, rfl⟩
    refine commutes_locImg_of_commutes ?_
    by_contra hn
    exact hl₂ (hl₁.trans (Linked.single ⟨((hFam N₁).mp h₁).1, ((hFam N₂).mp h₂).1, hn⟩))
  rcases family_split_empty hq φ F₁ F₂ hle hstab hnc hcomm with h | h
  · have : locImg Ω x A ∈ F₁ := by
      rw [hF₁]
      exact ⟨A, ⟨(hFam A).mpr ⟨hA, hAc⟩, Relation.ReflTransGen.refl⟩, rfl⟩
    rw [h] at this
    exact this
  · have : locImg Ω x B ∈ F₂ := by
      rw [hF₂]
      exact ⟨B, ⟨(hFam B).mpr ⟨hB, hBc⟩, hAB⟩, rfl⟩
    rw [h] at this
    exact this

theorem linked_of_le_range (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {c : Fin D.card} {A B : Subgroup G}
    (hA : A ∈ centralizingMembers Ω {x}) (hB : B ∈ centralizingMembers Ω {x})
    (hAc : locImg Ω x A ≤ (D.hom c).range) (hBc : locImg Ω x B ≤ (D.hom c).range) :
    Linked Ω x A B :=
  linked_of_le_range_of_quasisimple hΩ hex
    (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag c)
      (D.admissible c)).1 (D.hom c) hA hB hAc hBc

end Component

end CFSG.ClassicalInvolution.RouteD.Sp3C4
