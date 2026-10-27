module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FusionLift

public section

namespace CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7

open CFSG.RankThree.PartOne.CTP.Fus

section Assembly

variable {G : Type*} [Group G]

theorem exists_sylow_normalizer [Finite G] {p : ℕ} [Fact p.Prime] (W D : Subgroup G) (hDW : D ≤ W)
    (hDn : (D.subgroupOf W).Normal) (hD : p ∣ Nat.card D) :
    ∃ S : Subgroup G, S ≤ D ∧ IsPGroup p S ∧ S ≠ ⊥ ∧
      ∀ w ∈ W, ∃ n ∈ W, ∃ d ∈ D, (∀ s ∈ S, n * s * n⁻¹ ∈ S) ∧ w = n * d := by
  classical
  have hcardN : Nat.card (D.subgroupOf W) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDW).toEquiv
  obtain ⟨S₀⟩ : Nonempty (Sylow p (D.subgroupOf W)) := inferInstance
  have hfrat := Sylow.normalizer_sup_eq_top S₀
  have hS₀ : (S₀ : Subgroup (D.subgroupOf W)) ≠ ⊥ := by
    intro h
    have hc := S₀.card_eq_multiplicity
    rw [h, Subgroup.card_bot, hcardN] at hc
    have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card D).factorization p :=
      (Nat.Prime.factorization_pos_of_dvd Fact.out hD0 hD)
    have hp1 : 1 < p ^ (Nat.card D).factorization p :=
      Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    omega
  refine ⟨((S₀ : Subgroup (D.subgroupOf W)).map (D.subgroupOf W).subtype).map W.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, ⟨n, hn, rfl⟩, rfl⟩
    exact n.2
  · exact (S₀.isPGroup'.map _).map _
  · intro h
    apply hS₀
    rw [Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h
    exact h
  · intro w hw
    have hw' : (⟨w, hw⟩ : W) ∈ Subgroup.normalizer
        (((S₀ : Subgroup (D.subgroupOf W)).map (D.subgroupOf W).subtype : Subgroup W) : Set W) ⊔
          D.subgroupOf W := by
      rw [hfrat]; trivial
    have := hDn
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_right.mp hw'
    refine ⟨n, n.2, d, Subgroup.mem_subgroupOf.mp hd, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
      exact ⟨n * t * n⁻¹, this, by simp⟩
    · have := congrArg Subtype.val hnd
      simpa using this.symm

theorem fusionGenerationOf_of_sup_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (K W D : Subgroup G) (hDK : D ≤ K) (hDW : D ≤ W) (hDn : (D.subgroupOf W).Normal)
    (hKW : K ⊔ W = ⊤) (hD : p ∣ Nat.card D) (hK : FusionGenerationOf K p) :
    FusionGenerationOf G p := by
  classical
  obtain ⟨S, hSD, hSp, hS1, hfrat⟩ := exists_sylow_normalizer W D hDW hDn hD
  have hSpK : IsPGroup p (S.subgroupOf K) := hSp.comap_subtype
  obtain ⟨Q, hSQ⟩ := hSpK.exists_le_sylow
  obtain ⟨Γ, hΓ⟩ := exists_datum_sylow hK Q
  obtain ⟨-, -, hΓtop, hfus⟩ := hΓ
  have hSE : S ≤ (Q : Subgroup K).map K.subtype := by
    intro x hx
    have hxK : x ∈ K := hDK (hSD hx)
    exact ⟨⟨x, hxK⟩, hSQ (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  refine fusionGenerationOf_iff.mpr
    ⟨(Q : Subgroup K).map K.subtype,
      K.subtype '' Γ ∪ {n | n ∈ W ∧ ∀ s ∈ S, n * s * n⁻¹ ∈ S}, Q.isPGroup'.map _, ?_, ?_, ?_⟩
  · intro h
    exact hS1 (le_bot_iff.mp (h ▸ hSE))
  · have hKC : ∀ z : K, z ∈ Subgroup.closure Γ → (z : G) ∈
        Subgroup.closure (K.subtype '' Γ ∪ {n | n ∈ W ∧ ∀ s ∈ S, n * s * n⁻¹ ∈ S}) := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz => exact Subgroup.subset_closure (Or.inl ⟨z, hz, rfl⟩)
      | one => exact Subgroup.one_mem _
      | mul a b _ _ ha hb => exact Subgroup.mul_mem _ ha hb
      | inv a _ ha => exact Subgroup.inv_mem _ ha
    have hKC' : K ≤ Subgroup.closure
        (K.subtype '' Γ ∪ {n | n ∈ W ∧ ∀ s ∈ S, n * s * n⁻¹ ∈ S}) := fun x hx =>
      hKC ⟨x, hx⟩ (by rw [hΓtop]; trivial)
    have hWC : W ≤ Subgroup.closure
        (K.subtype '' Γ ∪ {n | n ∈ W ∧ ∀ s ∈ S, n * s * n⁻¹ ∈ S}) := by
      intro w hw
      obtain ⟨n, hnW, d, hd, hnS, rfl⟩ := hfrat w hw
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨hnW, hnS⟩)) (hKC' (hDK hd))
    exact eq_top_iff.mpr (hKW.symm.le.trans (sup_le hKC' hWC))
  · rintro g (⟨k, hk, rfl⟩ | ⟨hgW, hgS⟩)
    · obtain ⟨e, he, he1, hke⟩ := hfus k hk
      exact ⟨e.1, ⟨e, he, rfl⟩, fun h => he1 (Subtype.ext h), ⟨k * e * k⁻¹, hke, rfl⟩⟩
    · obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS1
      exact ⟨e, hSE e.2, fun h => he1 (Subtype.ext h), hSE (hgS e e.2)⟩

theorem inf_centralizer_le_of_edge {a y : G} (W : Subgroup G)
    (hW : ∀ g, g ∈ W ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤ W := by
  intro d hd
  obtain ⟨ha, hy⟩ := Subgroup.mem_inf.mp hd
  rw [hW]
  left
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hy
  constructor
  · rw [mul_inv_eq_iff_eq_mul]; exact ha
  · rw [mul_inv_eq_iff_eq_mul]; exact hy

theorem normal_inf_centralizer_of_edge {a y : G} (W : Subgroup G)
    (hW : ∀ g, g ∈ W ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    ((Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf W).Normal := by
  refine ⟨fun n hn w => ?_⟩
  have hn' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff] at hn'
  obtain ⟨hna, hny⟩ := hn'
  have hnc : ∀ c₀, (c₀ = a ∨ c₀ = y) → (n : G) * c₀ = c₀ * n := by
    rintro c₀ (rfl | rfl)
    · exact hna
    · exact hny
  have hw := (hW (w : G)).mp w.2
  have key : ∀ c, (c = a ∨ c = y) → ∃ c₀, (c₀ = a ∨ c₀ = y) ∧ (w : G) * c₀ * (w : G)⁻¹ = c := by
    intro c hc
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hc with rfl | rfl
      · exact ⟨c, Or.inl rfl, h1⟩
      · exact ⟨c, Or.inr rfl, h2⟩
    · rcases hc with rfl | rfl
      · exact ⟨y, Or.inr rfl, h2⟩
      · exact ⟨a, Or.inl rfl, h1⟩
  have hconj : ∀ c, (c = a ∨ c = y) → ((w * n * w⁻¹ : W) : G) * c = c * ((w * n * w⁻¹ : W) : G) := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := key c hc
    have h := hnc c₀ hc₀
    calc ((w * n * w⁻¹ : W) : G) * ((w : G) * c₀ * (w : G)⁻¹)
        = (w : G) * ((n : G) * c₀) * (w : G)⁻¹ := by simp [mul_assoc]
      _ = (w : G) * (c₀ * (n : G)) * (w : G)⁻¹ := by rw [h]
      _ = ((w : G) * c₀ * (w : G)⁻¹) * ((w * n * w⁻¹ : W) : G) := by simp [mul_assoc]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨hconj a (Or.inl rfl), hconj y (Or.inr rfl)⟩

end Assembly

end CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7
