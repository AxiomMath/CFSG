module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmfHat
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmfGold

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section Conj

variable {G : Type} [Group G]

theorem gmf_conj_props {t : G} {X : Subgroup G}
    (hX : ∀ a ∈ X, a ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ a) {g' x : G} (hx : g' * x * g'⁻¹ ∈ X) :
    x ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ x := by
  obtain ⟨h1, h2⟩ := hX _ hx
  refine ⟨?_, fun g hg => h2 (g' * g) ?_⟩
  · have h3 : g' * x ^ 2 * g'⁻¹ = 1 := by
      rw [show g' * x ^ 2 * g'⁻¹ = (g' * x * g'⁻¹) ^ 2 by rw [sq, sq]; group, h1]
    calc x ^ 2 = g'⁻¹ * (g' * x ^ 2 * g'⁻¹) * g' := by group
      _ = 1 := by rw [h3]; group
  · rw [show g' * g * t * (g' * g)⁻¹ = g' * (g * t * g⁻¹) * g'⁻¹ by group, hg]

theorem gmf_comm_of_conj {X : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) {g' x y : G}
    (hx : g' * x * g'⁻¹ ∈ X) (hy : g' * y * g'⁻¹ ∈ X) : x * y = y * x := by
  have h1 := hX _ hx _ hy
  have h2 : g' * (x * y) * g'⁻¹ = g' * (y * x) * g'⁻¹ := by
    calc g' * (x * y) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * y * g'⁻¹) := by group
      _ = (g' * y * g'⁻¹) * (g' * x * g'⁻¹) := h1
      _ = g' * (y * x) * g'⁻¹ := by group
  calc x * y = g'⁻¹ * (g' * (x * y) * g'⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * (y * x) * g'⁻¹) * g' := by rw [h2]
    _ = y * x := by group

theorem gmf_conj_mem_of_mem_map {X : Subgroup G} {h x : G}
    (hx : x ∈ X.map (MulAut.conj h).toMonoidHom) : h⁻¹ * x * h⁻¹⁻¹ ∈ X := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [show h⁻¹ * (h * a * h⁻¹) * h = a by group]
  exact ha

end Conj

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gmf_card_le_two_mul_inf {X : Subgroup G} (hX : X ≤ swapS₂ P U T) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ (U ⊔ T) : Subgroup G) := by
  have h1 := relIndex_mul_card (H := U ⊔ T) (K := X)
  have h2 : (U ⊔ T).relIndex X ≤ 2 := by
    rw [← hW.relIndex_SU_S₂]
    exact relIndex_le_of_le_right hX (by rw [hW.relIndex_SU_S₂]; norm_num)
  rw [inf_comm] at h1
  calc Nat.card X = (U ⊔ T).relIndex X * Nat.card (X ⊓ (U ⊔ T) : Subgroup G) := h1.symm
    _ ≤ 2 * Nat.card (X ⊓ (U ⊔ T) : Subgroup G) := Nat.mul_le_mul_right _ h2

theorem gmf_inf_le_A {X : Subgroup G}
    (hX : X ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
    (hXt : ∀ x ∈ X, x ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ x) :
    X ⊓ (U ⊔ T) ≤ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) := by
  intro x hx
  obtain ⟨hxX, hxS⟩ := mem_inf.mp hx
  obtain ⟨hx2, hxt⟩ := hXt x hxX
  exact hW.gmf_mem_A_of_sq_eq_one hxS
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (hX hxX)).2) hx2 hxt

theorem gmf_mem_C₀ {y : G} (hy : y ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
    (hyF : ∀ e ∈ U₁ ⊓ centralizer ({t * w} : Set G), y * e = e * y) :
    y ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
      centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G) := by
  have hyv := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
  have hAy : (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤
      centralizer ({y} : Set G) :=
    sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hyF e he).symm)
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyv.symm))
  exact mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun a ha =>
    mem_centralizer_singleton_iff.mp (hAy ha)⟩

theorem gmf_exists_mem_C₀
    (hSyl : IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G)))
    (hcl : ¬ ∀ a ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w),
      ∀ g ∈ centralizer ({t * w} : Set G),
        g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
          g⁻¹ * a * g ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)) :
    ∃ y ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
      centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G), y ∉ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ∧ y ^ 2 = 1 := by
  set I := centralizer ({t * w} : Set G) with hIdef
  set S₀ := swapS₂ P U T ⊓ I with hS₀def
  set F := U₁ ⊓ I with hFdef
  set A := F ⊔ zpowers (t * w) with hAdef
  have hAS₀ : A ≤ S₀ := hW.gmf_A_le_S₀
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hW.gmf_A_comm ha hb
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hW.gmf_A_sq ha
  have hAp : ∀ a ∈ A, a ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ a := fun a ha =>
    ⟨hA2 a ha, fun g hg => hW.not_conj_mem_F_sup g (hg ▸ ha)⟩
  push Not at hcl
  obtain ⟨a, haA, g, hgI, hgS₀, hgA⟩ := hcl
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * a * g := ⟨_, rfl⟩
  rw [← hbdef] at hgS₀ hgA
  have hbconj : g * b * g⁻¹ ∈ A := by
    rw [hbdef, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact haA
  obtain ⟨hb2, hbt⟩ := gmf_conj_props hAp hbconj
  have hbv : b * (t * w) = (t * w) * b := mem_centralizer_singleton_iff.mp (mem_inf.mp hgS₀).2
  have hbS : b ∉ U ⊔ T := fun hbS => hgA (hW.gmf_mem_A_of_sq_eq_one hbS hbv hb2 hbt)
  by_cases hwc : ∀ h ∈ I, (∀ a ∈ A, h * a * h⁻¹ ∈ S₀) → ∀ a ∈ A, h * a * h⁻¹ ∈ A
  · rcases gmf_cor4_self_rel hSyl hAS₀ hwc hAab hA2 with hcl' | hB
    · have h1 := hcl' a haA g hgI (by rw [← hbdef]; exact hgS₀)
      rw [← hbdef] at h1
      exact absurd h1 hgA
    · obtain ⟨B, hBS₀, -, ⟨g', -, hg'⟩, hrel, -⟩ := hB b hgS₀ hgA ⟨g, hgI, hbconj⟩
      have hBA := hW.gmf_inf_le_A hBS₀ fun x hx => gmf_conj_props hAp (hg' x hx)
      have h1 := hW.gmf_card_le_two_mul_inf (hBS₀.trans inf_le_left)
      have h2 : Nat.card (B ⊓ (U ⊔ T) : Subgroup G) ≤
          Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le (le_inf inf_le_left fun x hx =>
          mem_centralizer_iff.mpr fun c hc => hAab c hc x (hBA hx))
      have hpos : 0 < Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
      have h3 : Nat.card A ≤ 2 * Nat.card (A ⊓ centralizer ({b} : Set G) : Subgroup G) := by
        have h4 : Nat.card A * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) ≤
            (2 * Nat.card (A ⊓ centralizer ({b} : Set G) : Subgroup G)) *
              Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) := by
          calc _ ≤ Nat.card B * Nat.card (A ⊓ centralizer ({b} : Set G) : Subgroup G) := hrel
            _ ≤ (2 * Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G)) *
                Nat.card (A ⊓ centralizer ({b} : Set G) : Subgroup G) :=
              Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_left 2 h2))
            _ = _ := by ring
        exact Nat.le_of_mul_le_mul_right h4 hpos
      have hbF := hW.gmf_comm_F (mem_inf.mp hgS₀).1 hbv hbS hb2
        (M := A ⊓ centralizer ({b} : Set G)) inf_le_left
        (fun m hm => (mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2).symm) h3
      exact ⟨b, hW.gmf_mem_C₀ hgS₀ hbF, hgA, hb2⟩
  · push Not at hwc
    obtain ⟨h, -, hhS₀, a₀, ha₀A, hha₀⟩ := hwc
    set X := A.map (MulAut.conj h).toMonoidHom with hXdef
    have hXmem : ∀ x ∈ X, h⁻¹ * x * h⁻¹⁻¹ ∈ A := fun x hx => gmf_conj_mem_of_mem_map hx
    have hXS₀ : X ≤ S₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hhS₀ x hx
    have hXA := hW.gmf_inf_le_A hXS₀ fun x hx => gmf_conj_props hAp (hXmem x hx)
    have hXcard : Nat.card X = Nat.card A := card_map_of_injective (MulAut.conj h).injective
    have h1 := hW.gmf_card_le_two_mul_inf (hXS₀.trans inf_le_left)
    have hyX : h * a₀ * h⁻¹ ∈ X := ⟨a₀, ha₀A, rfl⟩
    have hy2 := (gmf_conj_props hAp (hXmem _ hyX)).1
    have hyS₀ := hXS₀ hyX
    have hyS : h * a₀ * h⁻¹ ∉ U ⊔ T := fun hyS => hha₀ (hXA (mem_inf.mpr ⟨hyX, hyS⟩))
    have hyF := hW.gmf_comm_F (mem_inf.mp hyS₀).1
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hyS₀).2) hyS hy2 (M := X ⊓ (U ⊔ T)) hXA
      (fun m hm => gmf_comm_of_conj hAab (hXmem _ hyX) (hXmem m (mem_inf.mp hm).1))
      (by rw [← hXcard]; exact h1)
    exact ⟨h * a₀ * h⁻¹, hW.gmf_mem_C₀ hyS₀ hyF, hha₀, hy2⟩

theorem gmf_C₀_closed (hc : ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T)
    (hSyl : IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G)))
    {y : G} (hyC₀ : y ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
      centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
        Set G))
    (hyA : y ∉ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)) (hy2 : y ^ 2 = 1) :
    (∀ a ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
        centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
          Set G),
      ∀ b ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
        centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
          Set G), a * b = b * a) ∧
    ∀ a ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
        centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) : Subgroup G) :
          Set G),
      ∀ g ∈ centralizer ({t * w} : Set G),
        g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
          g⁻¹ * a * g ∈ (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
            centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :
              Subgroup G) : Set G) := by
  set I := centralizer ({t * w} : Set G) with hIdef
  set S₀ := swapS₂ P U T ⊓ I with hS₀def
  set F := U₁ ⊓ I with hFdef
  set A := F ⊔ zpowers (t * w) with hAdef
  set C₀ := S₀ ⊓ centralizer (A : Set G) with hC₀def
  have hAS₀ : A ≤ S₀ := hW.gmf_A_le_S₀
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hW.gmf_A_comm ha hb
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hW.gmf_A_sq ha
  have hyS₀ : y ∈ S₀ := (mem_inf.mp hyC₀).1
  have hyAC : ∀ a ∈ A, a * y = y * a := mem_centralizer_iff.mp (mem_inf.mp hyC₀).2
  have hC₀SU : ∀ c ∈ C₀, c ∈ U ⊔ T → c ∈ A := by
    intro c hc hcS
    obtain ⟨hcS₀, hcA⟩ := mem_inf.mp hc
    exact hW.gmf_mem_A_of_comm hcS (mem_centralizer_singleton_iff.mp (mem_inf.mp hcS₀).2)
      fun e he => ((mem_centralizer_iff.mp hcA) e (mem_sup_left he)).symm
  have hyS : y ∉ U ⊔ T := fun h => hyA (hC₀SU y hyC₀ h)
  have hC₀cases : ∀ c ∈ C₀, c ∈ A ∨ y⁻¹ * c ∈ A := by
    intro c hc
    by_cases hcS : c ∈ U ⊔ T
    · exact Or.inl (hC₀SU c hc hcS)
    · right
      have hy' := (hW.mem_or (mem_inf.mp hyS₀).1).resolve_left hyS
      have hc' := (hW.mem_or (mem_inf.mp (mem_inf.mp hc).1).1).resolve_left hcS
      have h2 : s * (y⁻¹ * c) * s⁻¹ ∈ U ⊔ T := by
        rw [show s * (y⁻¹ * c) * s⁻¹ = (y * s⁻¹)⁻¹ * (c * s⁻¹) by group]
        exact mul_mem (inv_mem hy') hc'
      have h3 := (mem_normalizer_iff.mp (inv_mem hW.s_mem_normalizer) _).mp h2
      rw [show s⁻¹ * (s * (y⁻¹ * c) * s⁻¹) * s⁻¹⁻¹ = y⁻¹ * c by group] at h3
      exact hC₀SU _ (mul_mem (inv_mem hyC₀) hc) h3
  have hAC₀ : A ≤ C₀ :=
    le_inf hAS₀ fun a ha => mem_centralizer_iff.mpr fun b hb => hAab b hb a ha
  have hC₀S₀ : C₀ ≤ S₀ := inf_le_left
  have hC₀ab : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a := by
    intro a ha b hb
    have haC := mem_centralizer_iff.mp (mem_inf.mp ha).2
    have hbC := mem_centralizer_iff.mp (mem_inf.mp hb).2
    rcases hC₀cases a ha with haA | haA
    · exact hbC a haA
    · rcases hC₀cases b hb with hbA | hbA
      · exact (haC b hbA).symm
      · obtain ⟨a', rfl⟩ : ∃ a', a = y * a' := ⟨y⁻¹ * a, by group⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = y * b' := ⟨y⁻¹ * b, by group⟩
        rw [inv_mul_cancel_left] at haA hbA
        have h1 : a' * y = y * a' := hyAC a' haA
        have h2 : b' * y = y * b' := hyAC b' hbA
        have h3 : a' * b' = b' * a' := hAab a' haA b' hbA
        calc y * a' * (y * b') = y * (a' * y) * b' := by group
          _ = y * (y * a') * b' := by rw [h1]
          _ = y * y * (a' * b') := by group
          _ = y * y * (b' * a') := by rw [h3]
          _ = y * (y * b') * a' := by group
          _ = y * (b' * y) * a' := by rw [h2]
          _ = y * b' * (y * a') := by group
  have hC₀sq : ∀ c ∈ C₀, c ^ 2 = 1 := by
    intro c hc
    rcases hC₀cases c hc with hcA | hcA
    · exact hA2 c hcA
    · obtain ⟨a', rfl⟩ : ∃ a', c = y * a' := ⟨y⁻¹ * c, by group⟩
      rw [inv_mul_cancel_left] at hcA
      have h1 : a' * y = y * a' := hyAC a' hcA
      calc (y * a') ^ 2 = y * (a' * y) * a' := by rw [sq]; group
        _ = y * (y * a') * a' := by rw [h1]
        _ = y ^ 2 * a' ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [hy2, hA2 a' hcA, one_mul]
  have hC₀p : ∀ c ∈ C₀, c ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ c := by
    intro c hcm
    refine ⟨hC₀sq c hcm, fun g hg => ?_⟩
    by_cases hcS : c ∈ U ⊔ T
    · exact hW.not_conj_mem_F_sup g (by rw [hg]; exact hC₀SU c hcm hcS)
    · have h1 : g * t * g⁻¹ ∈ swapS₂ P U T := by
        rw [hg]
        exact (mem_inf.mp (mem_inf.mp hcm).1).1
      have h2 := hc g h1
      rw [hg] at h2
      exact hcS h2
  have hC₀card : 2 * Nat.card A ≤ Nat.card C₀ := by
    have hpos : 0 < Nat.card C₀ := Nat.card_pos
    have hne : Nat.card C₀ ≠ Nat.card A := fun heq => hyA (by
      rw [eq_of_le_of_card_ge hAC₀ heq.le]
      exact hyC₀)
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAC₀
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k
      · rw [mul_zero] at hk
        omega
      · rw [mul_one] at hk
        exact hne hk
    rw [hk, mul_comm]
    exact Nat.mul_le_mul_left _ hk2
  have hwc : ∀ h ∈ I, (∀ c ∈ C₀, h * c * h⁻¹ ∈ S₀) → ∀ c ∈ C₀, h * c * h⁻¹ ∈ C₀ := by
    intro h _ hhS₀
    set X := C₀.map (MulAut.conj h).toMonoidHom with hXdef
    have hXmem : ∀ x ∈ X, h⁻¹ * x * h⁻¹⁻¹ ∈ C₀ := fun x hx => gmf_conj_mem_of_mem_map hx
    have hXS₀ : X ≤ S₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hhS₀ x hx
    have hXA := hW.gmf_inf_le_A hXS₀ fun x hx => gmf_conj_props hC₀p (hXmem x hx)
    have hXcard : Nat.card X = Nat.card C₀ := card_map_of_injective (MulAut.conj h).injective
    have h1 := hW.gmf_card_le_two_mul_inf (hXS₀.trans inf_le_left)
    have hXeq : X ⊓ (U ⊔ T) = A := eq_of_le_of_card_ge hXA (by omega)
    have hAX : A ≤ X := by
      rw [← hXeq]
      exact inf_le_left
    intro c hc
    have hcX : h * c * h⁻¹ ∈ X := ⟨c, hc, rfl⟩
    refine mem_inf.mpr ⟨hhS₀ c hc, mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact gmf_comm_of_conj hC₀ab (hXmem a (hAX ha)) (hXmem _ hcX)
  refine ⟨hC₀ab, ?_⟩
  rcases gmf_cor4_self_rel hSyl hC₀S₀ hwc hC₀ab hC₀sq with hcl | hB
  · exact hcl
  · intro c hc g hgI hgS₀
    by_contra hgC₀
    obtain ⟨B, hBS₀, hBC₀, ⟨g', -, hg'⟩, -, hcard⟩ := hB _ hgS₀ hgC₀
      ⟨g, hgI, by rw [show g * (g⁻¹ * c * g) * g⁻¹ = c by group]; exact hc⟩
    have hBp : ∀ x ∈ B, x ^ 2 = 1 ∧ ∀ g : G, g * t * g⁻¹ ≠ x := fun x hx =>
      gmf_conj_props hC₀p (hg' x hx)
    have hBA := hW.gmf_inf_le_A hBS₀ hBp
    have h1 := hW.gmf_card_le_two_mul_inf (hBS₀.trans inf_le_left)
    have h2 : Nat.card (B ⊓ (U ⊔ T) : Subgroup G) ≤
        Nat.card (B ⊓ centralizer (C₀ : Set G) : Subgroup G) :=
      Subgroup.card_le_of_le (le_inf inf_le_left fun x hx =>
        mem_centralizer_iff.mpr fun c' hc' =>
          ((mem_centralizer_iff.mp (mem_inf.mp hc').2) x (hBA hx)).symm)
    have hpos : 0 < Nat.card (B ⊓ centralizer (C₀ : Set G) : Subgroup G) := Nat.card_pos
    have h3 : Nat.card C₀ ≤ 2 * Nat.card B := by
      have h4 : Nat.card C₀ * Nat.card (B ⊓ centralizer (C₀ : Set G) : Subgroup G) ≤
          (2 * Nat.card B) * Nat.card (B ⊓ centralizer (C₀ : Set G) : Subgroup G) := by
        calc _ ≤ Nat.card B * Nat.card B := hcard
          _ ≤ Nat.card B * (2 * Nat.card (B ⊓ centralizer (C₀ : Set G) : Subgroup G)) :=
            Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left 2 h2))
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_right h4 hpos
    have h5 : Nat.card A ≤ 2 * Nat.card (B ⊓ (U ⊔ T) : Subgroup G) := by omega
    obtain ⟨y', hy'B, hy'C₀⟩ : ∃ y' ∈ B, y' ∉ C₀ := by
      by_contra hall
      push Not at hall
      exact hBC₀ hall
    have hy'S₀ := hBS₀ hy'B
    have hy'S : y' ∉ U ⊔ T := fun hS => hy'C₀ (hAC₀ (hBA (mem_inf.mpr ⟨hy'B, hS⟩)))
    have hy'F := hW.gmf_comm_F (mem_inf.mp hy'S₀).1
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hy'S₀).2) hy'S (hBp y' hy'B).1
      (M := B ⊓ (U ⊔ T)) hBA
      (fun m hm => gmf_comm_of_conj hC₀ab (hg' y' hy'B) (hg' m (mem_inf.mp hm).1)) h5
    exact hy'C₀ (hW.gmf_mem_C₀ hy'S₀ hy'F)

theorem gmf_closure (hc : ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T)
    (hSyl : IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
      (centralizer ({t * w} : Set G))) :
    ∃ J : Subgroup G, (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J ∧
      J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) ∧
      (J = (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ∨
        J = (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
          centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :
            Subgroup G) : Set G)) ∧
      (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) ∧
      ∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
        g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J := by
  by_cases hcl : ∀ a ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w),
      ∀ g ∈ centralizer ({t * w} : Set G),
        g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
          g⁻¹ * a * g ∈ (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w)
  · exact ⟨_, le_rfl, hW.gmf_A_le_S₀, Or.inl rfl, fun a ha b hb => hW.gmf_A_comm ha hb, hcl⟩
  · obtain ⟨y, hyC₀, hyA, hy2⟩ := hW.gmf_exists_mem_C₀ hSyl hcl
    obtain ⟨hab, hcl'⟩ := hW.gmf_C₀_closed hc hSyl hyC₀ hyA hy2
    refine ⟨_, ?_, inf_le_left, Or.inr rfl, hab, hcl'⟩
    exact le_inf hW.gmf_A_le_S₀ fun a ha =>
      mem_centralizer_iff.mpr fun b hb => hW.gmf_A_comm hb ha

end U3C1OuterSwapHigh

theorem u3C1GmsClosureInput_holds : U3C1GmsClosureInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW _ _ hc _ hSyl => hW.gmf_closure hc hSyl

end CFSG.SeitzReduction.RankOne
