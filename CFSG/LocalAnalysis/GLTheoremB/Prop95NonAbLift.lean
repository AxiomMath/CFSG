module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbFactors

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

open Subgroup
open scoped commutatorElement

section Lift

variable {A B : Type*} [Group A] [Group B]

theorem comm_le_of_le {G : Type*} [Group G] {X P R : Subgroup G} (hP : P ≤ X) (hR : R ≤ X) :
    ⁅P, R⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have := X.mul_mem (X.mul_mem (X.mul_mem (hP ha) (hR hb)) (X.inv_mem (hP ha))) (X.inv_mem (hR hb))
  simpa [commutatorElement_def] using this

theorem commutator_self_eq_of_simple (Sg : Subgroup B) [IsSimpleGroup Sg]
    (hnab : ∃ a b : Sg, a * b ≠ b * a) : ⁅Sg, Sg⁆ = Sg := by
  have hle : ⁅Sg, Sg⁆ ≤ Sg := comm_le_of_le le_rfl le_rfl
  have hn : Sg ≤ normalizer ((⁅Sg, Sg⁆ : Subgroup B) : Set B) := normalizer_commutator_ge_left Sg Sg
  rcases eq_bot_or_eq_of_simple (N := Sg) (T := Sg) (A := ⁅Sg, Sg⁆) hle le_rfl hn with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : ⁅(a : B), (b : B)⁆ ∈ ⁅Sg, Sg⁆ := Subgroup.commutator_mem_commutator a.2 b.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact Subtype.ext this
  · exact h

theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h]; trivial
    exact ((Subgroup.mem_center_iff.1 ha) b).symm

theorem mem_normalizer_commutator_self {G : Type*} [Group G] {g : G} {K : Subgroup G}
    (hg : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_cj_eq ?_
  unfold cj
  rw [Subgroup.map_commutator]
  have := cj_eq_of_mem_normalizer hg
  unfold cj at this
  rw [this]


end Lift

section LiftMain

variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]

theorem exists_component_lift (π : A →* B) (hπ : Function.Surjective π) (Γ : Subgroup A)
    (hΓker : ⁅Γ, π.ker⁆ = ⊥) (T Sg : Subgroup B) [T.Normal] [IsSimpleGroup Sg]
    (hnab : ∃ a b : Sg, a * b ≠ b * a) (hST : Sg ≤ T) (hSTn : T ≤ normalizer (Sg : Set B))
    (hΓn : Γ.map π ≤ normalizer (Sg : Set B)) (hΓS : ⁅Γ.map π, Sg⁆ ≠ ⊥) :
    ∃ K : Subgroup A, CFSG.Open.IsComponentOf K ⊤ ∧ ⁅Γ, K⁆ = K ∧
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* ↥Sg) := by
  classical
  set Z := π.ker with hZ
  set W₁ : Subgroup A := Sg.comap π with hW₁
  set W : Subgroup A := T.comap π with hW
  have hWn : W.Normal := Subgroup.Normal.comap inferInstance π
  have hπW₁ : W₁.map π = Sg := Subgroup.map_comap_eq_self_of_surjective hπ Sg
  have hΓW₁ : Γ ≤ normalizer (W₁ : Set A) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hW₁, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hΓn ⟨g, hg, rfl⟩) _
  set A₁ : Subgroup A := ⁅Γ, W₁⁆ with hA₁
  have hA₁W₁ : A₁ ≤ W₁ := by
    rw [hA₁, Subgroup.commutator_le]
    intro g hg x hx
    have h1 := (Subgroup.mem_normalizer_iff.1 (hΓW₁ hg) x).1 hx
    simpa [commutatorElement_def] using W₁.mul_mem h1 (W₁.inv_mem hx)
  have hA₁Z : ⁅A₁, Z⁆ = ⊥ := by
    have hZn : Z.Normal := MonoidHom.normal_ker π
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · refine le_bot_iff.1 ?_
      calc ⁅⁅W₁, Z⁆, Γ⁆ ≤ ⁅Z, Γ⁆ := Subgroup.commutator_mono_left (Subgroup.commutator_le_right W₁ Z)
        _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hΓker
    · rw [show ⁅Z, Γ⁆ = ⊥ by rw [Subgroup.commutator_comm]; exact hΓker]
      simp
  have hA₁cent : ∀ k ∈ A₁, ∀ z ∈ Z, k * z = z * k := by
    intro k hk z hz
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hA₁Z hk
    exact ((Subgroup.mem_centralizer_iff.1 this) z hz).symm
  have hE : ⁅Γ.map π, Sg⁆ = Sg := by
    have hle : ⁅Γ.map π, Sg⁆ ≤ Sg := by
      rw [Subgroup.commutator_le]
      intro g hg x hx
      have h1 := (Subgroup.mem_normalizer_iff.1 (hΓn hg) x).1 hx
      simpa [commutatorElement_def] using Sg.mul_mem h1 (Sg.inv_mem hx)
    have hn : Sg ≤ normalizer ((⁅Γ.map π, Sg⁆ : Subgroup B) : Set B) :=
      normalizer_commutator_ge_right _ _
    rcases eq_bot_or_eq_of_simple (N := Sg) (T := Sg) (A := ⁅Γ.map π, Sg⁆) hle le_rfl hn with h | h
    · exact absurd h hΓS
    · exact h
  have hSperf : ⁅Sg, Sg⁆ = Sg := commutator_self_eq_of_simple Sg hnab
  let P : Subgroup A → Prop := fun K =>
    K ≤ A₁ ∧ Γ ≤ normalizer (K : Set A) ∧ W₁ ≤ normalizer (K : Set A) ∧ K.map π = Sg
  have hP₀ : P A₁ := by
    refine ⟨le_rfl, normalizer_commutator_ge_left _ _, normalizer_commutator_ge_right _ _, ?_⟩
    rw [hA₁, Subgroup.map_commutator, hπW₁, hE]
  obtain ⟨K, ⟨hKA₁, hKΓ, hKW₁, hKπ⟩, hKmin⟩ := (Set.toFinite {K : Subgroup A | P K}).exists_minimal
    ⟨A₁, hP₀⟩
  have hKcent : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k := fun k hk z hz => hA₁cent k (hKA₁ hk) z hz
  have hKperf : ⁅K, K⁆ = K := by
    have hle : ⁅K, K⁆ ≤ K := comm_le_of_le le_rfl le_rfl
    refine le_antisymm hle (hKmin (y := ⁅K, K⁆) ⟨hle.trans hKA₁, ?_, ?_, ?_⟩ hle)
    · exact fun g hg => mem_normalizer_commutator_self (hKΓ hg)
    · exact fun g hg => mem_normalizer_commutator_self (hKW₁ hg)
    · rw [Subgroup.map_commutator, hKπ, hSperf]
  have hKΓK : ⁅Γ, K⁆ = K := by
    have hL : ⁅Γ, K⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_right.1 hKΓ
    refine le_antisymm hL ?_
    have hLπ : (⁅Γ, K⁆).map π = Sg := by rw [Subgroup.map_commutator, hKπ, hE]
    have hdecomp : ∀ k ∈ K, ∃ l ∈ ⁅Γ, K⁆, ∃ z ∈ Z, k = l * z := by
      intro k hk
      have hπk : π k ∈ (⁅Γ, K⁆).map π := by
        rw [hLπ, ← hKπ]; exact ⟨k, hk, rfl⟩
      obtain ⟨l, hl, hlk⟩ := hπk
      refine ⟨l, hl, l⁻¹ * k, ?_, by group⟩
      rw [hZ, MonoidHom.mem_ker, map_mul, map_inv, hlk, inv_mul_cancel]
    have hKK : ⁅K, K⁆ ≤ ⁅Γ, K⁆ := by
      refine (Subgroup.commutator_le).2 fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := hdecomp k₁ hk₁
      obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := hdecomp k₂ hk₂
      have hl₁K : l₁ ∈ K := hL hl₁
      have hl₂K : l₂ ∈ K := hL hl₂
      have hz₁K : z₁ ∈ K := by
        have : z₁ = l₁⁻¹ * (l₁ * z₁) := by group
        rw [this]; exact K.mul_mem (K.inv_mem hl₁K) hk₁
      have hz₂K : z₂ ∈ K := by
        have : z₂ = l₂⁻¹ * (l₂ * z₂) := by group
        rw [this]; exact K.mul_mem (K.inv_mem hl₂K) hk₂
      have e1 : z₁ * l₂ = l₂ * z₁ := hKcent l₂ hl₂K z₁ hz₁ |>.symm
      have e2 : z₂ * l₁ = l₁ * z₂ := hKcent l₁ hl₁K z₂ hz₂ |>.symm
      have e3 : z₁ * z₂ = z₂ * z₁ := hKcent z₂ hz₂K z₁ hz₁ |>.symm
      have : ⁅l₁ * z₁, l₂ * z₂⁆ = ⁅l₁, l₂⁆ := by
        simp only [commutatorElement_def, mul_inv_rev]
        calc l₁ * z₁ * (l₂ * z₂) * (z₁⁻¹ * l₁⁻¹) * (z₂⁻¹ * l₂⁻¹)
            = l₁ * (z₁ * l₂) * (z₂ * z₁⁻¹) * l₁⁻¹ * (z₂⁻¹ * l₂⁻¹) := by group
          _ = l₁ * (l₂ * z₁) * (z₂ * z₁⁻¹) * l₁⁻¹ * (z₂⁻¹ * l₂⁻¹) := by rw [e1]
          _ = l₁ * l₂ * (z₁ * z₂ * z₁⁻¹) * l₁⁻¹ * (z₂⁻¹ * l₂⁻¹) := by group
          _ = l₁ * l₂ * z₂ * l₁⁻¹ * (z₂⁻¹ * l₂⁻¹) := by rw [e3]; group
          _ = l₁ * l₂ * (z₂ * l₁⁻¹) * (z₂⁻¹ * l₂⁻¹) := by group
          _ = l₁ * l₂ * (l₁⁻¹ * z₂) * (z₂⁻¹ * l₂⁻¹) := by
            have : z₂ * l₁⁻¹ = l₁⁻¹ * z₂ := by
              calc z₂ * l₁⁻¹ = l₁⁻¹ * (l₁ * z₂) * l₁⁻¹ := by group
                _ = l₁⁻¹ * (z₂ * l₁) * l₁⁻¹ := by rw [← e2]
                _ = l₁⁻¹ * z₂ := by group
            rw [this]
          _ = ⁅l₁, l₂⁆ := by group
      rw [this]
      exact (comm_le_of_le (X := ⁅Γ, K⁆) le_rfl le_rfl) (Subgroup.commutator_mem_commutator hl₁ hl₂)
    rw [hKperf] at hKK
    exact hKK
  have hKW₁' : K ≤ W₁ := hKA₁.trans hA₁W₁
  have hsub : CFSG.Open.IsSubnormal K ⊤ := by
    have hW₁W : W₁ ≤ W := Subgroup.comap_mono hST
    have h1 : (K.subgroupOf W₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKW₁').2 hKW₁
    have h2 : (W₁.subgroupOf W).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hW₁W).2 fun w hw => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hW₁, Subgroup.mem_comap, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.1 (hSTn (Subgroup.mem_comap.1 hw)) _
    have h3 : (W.subgroupOf ⊤).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2
        (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hWn).symm)
    exact CFSG.Open.IsSubnormal.step hKW₁' h1 (CFSG.Open.IsSubnormal.step hW₁W h2
      (CFSG.Open.IsSubnormal.step le_top h3 (CFSG.Open.IsSubnormal.refl ⊤)))
  have hKπ' : ∀ k : ↥K, π k ∈ Sg := fun k => by rw [← hKπ]; exact ⟨k, k.2, rfl⟩
  let ρ : ↥K →* ↥Sg := (π.comp K.subtype).codRestrict Sg hKπ'
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨s, hs⟩
    rw [← hKπ] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  have hρker : ρ.ker = Subgroup.center ↥K := by
    ext k
    constructor
    · intro hk
      rw [Subgroup.mem_center_iff]
      intro k'
      have hπ1 : π k = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      exact Subtype.ext (hKcent k' k'.2 k (by rw [hZ, MonoidHom.mem_ker]; exact hπ1))
    · intro hk
      have hc : ρ k ∈ Subgroup.center ↥Sg := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨k', rfl⟩ := hρsurj s
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hk) k']
      rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hc
      exact hc
  let e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥Sg :=
    (QuotientGroup.quotientMulEquivOfEq hρker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj)
  refine ⟨K, ⟨le_top, hsub, ?_, ?_⟩, hKΓK, ⟨e⟩⟩
  · exact Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKperf)
  · exact MulEquiv.isSimpleGroup e

end LiftMain

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
