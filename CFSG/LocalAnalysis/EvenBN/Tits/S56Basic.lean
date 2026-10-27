module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec5Four
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec5Eleven

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

theorem s56_card_sup_zpowers_le {G : Type*} [Group G] [Finite G] {A : Subgroup G} {y : G}
    (hy : ∀ a ∈ A, a * y = y * a) (hy2 : y * y ∈ A) :
    Nat.card (A ⊔ zpowers y : Subgroup G) ≤ 2 * Nat.card A := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ A ∨ ∃ a ∈ A, x = a * y}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro x w (hx | ⟨a, ha, rfl⟩) (hw | ⟨b, hb, rfl⟩)
        · exact Or.inl (mul_mem hx hw)
        · exact Or.inr ⟨x * b, mul_mem hx hb, by group⟩
        · refine Or.inr ⟨a * w, mul_mem ha hw, ?_⟩
          have := hy w hw
          calc a * y * w = a * (y * w) := by group
            _ = a * (w * y) := by rw [this]
            _ = a * w * y := by group
        · refine Or.inl ?_
          have h1 := hy b hb
          have : a * y * (b * y) = a * b * (y * y) := by
            calc a * y * (b * y) = a * (y * b) * y := by group
              _ = a * (b * y) * y := by rw [← h1]
              _ = a * b * (y * y) := by group
          rw [this]
          exact mul_mem (mul_mem ha hb) hy2
      inv_mem' := by
        rintro x (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl (inv_mem hx)
        ·
          refine Or.inr ⟨a⁻¹ * (y * y)⁻¹, mul_mem (inv_mem ha) (inv_mem hy2), ?_⟩
          have hc : Commute a y := hy a ha
          calc (a * y)⁻¹ = y⁻¹ * a⁻¹ := by group
            _ = a⁻¹ * y⁻¹ := hc.inv_inv.eq.symm
            _ = a⁻¹ * (y * y)⁻¹ * y := by group }
  have hle : A ⊔ zpowers y ≤ S := by
    apply sup_le
    · intro a ha
      exact Or.inl ha
    · rw [zpowers_le]
      exact Or.inr ⟨1, one_mem _, by simp⟩
  calc Nat.card (A ⊔ zpowers y : Subgroup G) ≤ Nat.card S := Subgroup.card_le_of_le hle
    _ = (S : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ (A : Set G).ncard + ((fun a => a * y) '' (A : Set G)).ncard := by
        refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans (Set.ncard_union_le _ _)
        rintro x (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨a, ha, rfl⟩
    _ ≤ (A : Set G).ncard + (A : Set G).ncard := by
        exact Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
    _ = 2 * Nat.card A := by
        rw [← Nat.card_coe_set_eq]
        change Nat.card A + Nat.card A = 2 * Nat.card A
        ring

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


@[expose] noncomputable def s56Q0 (d : Data G) : Subgroup G :=
  (CFSG.pCore 2 ↥d.M).map d.M.subtype

@[expose] noncomputable def s56Q2 (d : Data G) : Subgroup G :=
  d.M ⊓ centralizer (d.E : Set G)

theorem s56_A_le_M (d : Data G) : d.A ≤ d.M := Subgroup.le_normalizer

theorem s56_E_le_M (d : Data G) : d.E ≤ d.M := le_sup_left.trans d.s56_A_le_M

theorem s56_centralizer_A_le_M (d : Data G) : centralizer (d.A : Set G) ≤ d.M := by
  intro g hg
  rw [Data.M, mem_normalizer_iff]
  intro h
  have hg' := mem_centralizer_iff.1 hg
  have hg'' := mem_centralizer_iff.1 (inv_mem hg : g⁻¹ ∈ centralizer (d.A : Set G))
  constructor
  · intro hh
    have h1 := hg' h hh
    have h2 : g * h * g⁻¹ = h := by
      calc g * h * g⁻¹ = (h * g) * g⁻¹ := by rw [h1]
        _ = h := by group
    rw [h2]
    exact hh
  · intro hh
    have h1 := hg'' (g * h * g⁻¹) hh
    have h2 : g * h * g⁻¹ = h := by
      calc g * h * g⁻¹ = ((g * h * g⁻¹) * g⁻¹) * g := by group
        _ = (g⁻¹ * (g * h * g⁻¹)) * g := by rw [h1]
        _ = h := by group
    rw [← h2]
    exact hh

theorem s56_subgroupOf_ne_top : titsD.subgroupOf titsA ≠ ⊤ := by
  intro h
  have h5 : Model.parrottV 5 ∈ titsA :=
    Model.twoF4H_le_titsA (Model.twoF4S_le_twoF4H (Model.parrottV_five.1))
  have : (⟨Model.parrottV 5, h5⟩ : titsA) ∈ titsD.subgroupOf titsA := h ▸ mem_top _
  exact Model.parrottV_five.2.1 (mem_subgroupOf.1 this)

theorem Hyp.s56_centralizer_A (hd : d.Hyp) :
    IsPGroup 2 (centralizer (d.A : Set G)) ∧
      ((d.ρ.range = titsD.subgroupOf titsA ∧ Nat.card (centralizer (d.A : Set G)) = 2 ^ 6) ∨
       (d.ρ.range = ⊤ ∧ Nat.card (centralizer (d.A : Set G)) ≤ 2 ^ 7)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hE32, hAt, hAelem, hA64, hAL⟩ := hd.A_facts
  rcases hd.centralizer_A with ⟨hr, hC⟩ | ⟨hr, hC⟩
  · rw [hC]
    exact ⟨IsPGroup.of_card (n := 6) hA64, Or.inl ⟨hr, hA64⟩⟩
  · have h5 : Model.parrottV 5 ∈ titsA :=
      Model.twoF4H_le_titsA (Model.twoF4S_le_twoF4H (Model.parrottV_five.1))
    have hmem : (⟨Model.parrottV 5, h5⟩ : titsA) ∈ d.ρ.range := hr ▸ mem_top _
    obtain ⟨y, hy⟩ := hmem
    have hyρ : (d.ρ y : Equiv.Perm (Fin 1755)) = Model.parrottV 5 := congrArg Subtype.val hy
    have hCy : centralizer (d.A : Set G) = d.A ⊔ zpowers (y : G) := hC y y.2 hyρ
    have hycent : (y : G) ∈ centralizer (d.A : Set G) := by
      rw [hCy]
      exact mem_sup_right (mem_zpowers _)
    have hycomm : ∀ a ∈ d.A, a * (y : G) = (y : G) * a := fun a ha =>
      mem_centralizer_iff.1 hycent a ha
    have hzA : d.z ∈ d.A := (hd.orbits_A).1.2
    have htA : d.t ∈ d.A := mem_sup_right (mem_zpowers _)
    have hy2C : (y : G) * (y : G) ∈ centralizer ({d.t} : Set G) := mul_mem y.2 y.2
    have hρy2 : (d.ρ ⟨(y : G) * (y : G), hy2C⟩ : Equiv.Perm (Fin 1755)) = titsZ := by
      have : (⟨(y : G) * (y : G), hy2C⟩ : centralizer ({d.t} : Set G)) = y * y := rfl
      rw [this, map_mul]
      change (d.ρ y : Equiv.Perm (Fin 1755)) * (d.ρ y : Equiv.Perm (Fin 1755)) = titsZ
      rw [hyρ]
      exact Model.parrottV_five.2.2
    have hy2A : (y : G) * (y : G) ∈ d.A := by
      have hD : (d.ρ ⟨(y : G) * (y : G), hy2C⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
        rw [hρy2]
        exact titsZ_mem_titsD
      rcases hd.eq_lift_or hy2C hD with h | h
      · rw [h, hρy2]
        exact hzA
      · rw [h, hρy2]
        exact mul_mem htA hzA
    have hcard := s56_card_sup_zpowers_le hycomm hy2A
    rw [← hCy, hA64] at hcard
    have h128 : (2 : ℕ) * 2 ^ 6 = 128 := by norm_num
    rw [h128] at hcard
    have hdvd : Nat.card d.A ∣ Nat.card (centralizer (d.A : Set G)) := by
      rw [hCy]
      exact Subgroup.card_dvd_of_le le_sup_left
    rw [hA64] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [h64] at hm
    have hpos : 0 < Nat.card (centralizer (d.A : Set G)) := Nat.card_pos
    have hm12 : m = 1 ∨ m = 2 := by omega
    refine ⟨?_, Or.inr ⟨hr, by norm_num; omega⟩⟩
    rcases hm12 with rfl | rfl
    · exact IsPGroup.of_card (n := 6) (by rw [hm]; norm_num)
    · exact IsPGroup.of_card (n := 7) (by rw [hm]; norm_num)

theorem Hyp.s56_card_M_facts (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ¬ 3 ∣ Nat.card d.M ∧ 10240 * Nat.card (centralizer (d.A : Set G)) ≤ Nat.card d.M := by
  obtain ⟨hCp, hCc⟩ := hd.s56_centralizer_A
  rcases hd.card_M_N_values h49 with ⟨hr, hM, -⟩ | ⟨hr, hM, -⟩
  · rcases hCc with ⟨-, hc⟩ | ⟨hr', -⟩
    · refine ⟨?_, ?_⟩
      · rw [hM]; norm_num
      · rw [hM, hc]; norm_num
    · exact absurd (hr.symm.trans hr') s56_subgroupOf_ne_top
  · rcases hCc with ⟨hr', -⟩ | ⟨-, hc⟩
    · exact absurd (hr'.symm.trans hr) s56_subgroupOf_ne_top
    · refine ⟨?_, ?_⟩
      · rw [hM]; norm_num
      · rw [hM]
        calc 10240 * Nat.card (centralizer (d.A : Set G)) ≤ 10240 * 2 ^ 7 :=
              Nat.mul_le_mul_left _ hc
          _ = 2 ^ 18 * 5 := by norm_num

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
