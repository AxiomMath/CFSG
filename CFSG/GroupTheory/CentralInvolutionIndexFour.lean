module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem normal_of_relIndex_two_of_isSimpleGroup {G₀ G₁ : Subgroup G} [hG₀ : G₀.Normal]
    (hG₁ : G₁ ≤ G₀) (hi : G₁.relIndex G₀ = 2) (hsimple : IsSimpleGroup G₁)
    (hbig : 2 < Nat.card G₁) : G₁.Normal := by
  refine ⟨fun x hx g => ?_⟩
  let c : G →* G := (MulAut.conj g).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hG₀c : G₀.map c = G₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact hG₀.conj_mem y hy g
    · rw [Subgroup.card_map_of_injective hcinj]
  have hG₁c_le : G₁.map c ≤ G₀ := hG₀c ▸ Subgroup.map_mono hG₁
  have hic : (G₁.map c).relIndex G₀ = 2 := by
    have h1 := Subgroup.relIndex_map_map_of_injective G₁ G₀ hcinj (f := c)
    rw [hG₀c] at h1
    rw [h1, hi]
  have hnc : ((G₁.map c).subgroupOf G₀).Normal := normal_of_index_eq_two hic
  have hP : (G₁ ⊓ G₁.map c).relIndex G₀ ≤ 4 := by
    have h1 := Subgroup.relIndex_inf_le (H := G₁) (K := G₁.map c) (L := G₀)
    rw [hi, hic] at h1
    exact h1
  have hG₀card : Nat.card G₀ = 2 * Nat.card G₁ := by
    have h1 := Subgroup.relIndex_mul_card G₁ G₀
    rw [inf_eq_left.mpr hG₁, hi] at h1
    omega
  have hPcard : 1 < Nat.card (G₁ ⊓ G₁.map c : Subgroup G) := by
    have h1 := Subgroup.relIndex_mul_card (G₁ ⊓ G₁.map c) G₀
    rw [inf_eq_left.mpr (inf_le_left.trans hG₁), hG₀card] at h1
    by_contra hle
    have h2 : Nat.card (G₁ ⊓ G₁.map c : Subgroup G) ≤ 1 := by omega
    have h3 : (G₁ ⊓ G₁.map c).relIndex G₀ * Nat.card (G₁ ⊓ G₁.map c : Subgroup G) ≤ 4 * 1 :=
      Nat.mul_le_mul hP h2
    omega
  have hnt : Nontrivial (G₁ ⊓ G₁.map c : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact hPcard
  have hPn : ((G₁ ⊓ G₁.map c).subgroupOf G₁).Normal := by
    refine ⟨fun y hy x' => ?_⟩
    have hy' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact G₁.mul_mem (G₁.mul_mem x'.2 hy'.1) (G₁.inv_mem x'.2)
    · have h1 : (⟨(y : G), hG₁ y.2⟩ : G₀) ∈ (G₁.map c).subgroupOf G₀ :=
        Subgroup.mem_subgroupOf.mpr hy'.2
      have h2 := hnc.conj_mem _ h1 ⟨(x' : G), hG₁ x'.2⟩
      exact Subgroup.mem_subgroupOf.mp h2
  have hPtop : (G₁ ⊓ G₁.map c).subgroupOf G₁ = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal ((G₁ ⊓ G₁.map c).subgroupOf G₁) with h | h
    · exfalso
      obtain ⟨p, hp, hp1⟩ := Subgroup.exists_ne_one_of_nontrivial (G₁ ⊓ G₁.map c : Subgroup G)
      have : (⟨p, (Subgroup.mem_inf.mp hp).1⟩ : G₁) ∈ (G₁ ⊓ G₁.map c).subgroupOf G₁ :=
        Subgroup.mem_subgroupOf.mpr hp
      rw [h, Subgroup.mem_bot] at this
      exact hp1 (congrArg Subtype.val this)
    · exact h
  have hle : G₁ ≤ G₁.map c := by
    intro y hy
    have h1 : (⟨y, hy⟩ : G₁) ∈ (G₁ ⊓ G₁.map c).subgroupOf G₁ := by
      rw [hPtop]
      trivial
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).2
  have heq : G₁.map c = G₁ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective hcinj]
  have hmem : c x ∈ G₁.map c := ⟨x, hx, rfl⟩
  rw [heq] at hmem
  exact hmem

theorem exists_central_involution_not_mem_of_index_four {G₀ G₁ : Subgroup G} [G₀.Normal]
    (hG₀ : G₀.index = 2) (hG₁ : G₁ ≤ G₀) (hi : G₁.relIndex G₀ = 2)
    (hsimple : IsSimpleGroup G₁) (hbig : 2 < Nat.card G₁)
    (hC : ∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1)
    (hAut : Nat.card (MulAut G₁) ∣ 6 * Nat.card G₁) :
    ∃ c : G, c ∉ G₀ ∧ c * c = 1 ∧ ∀ g : G, g * c = c * g := by
  have hnorm : G₁.Normal := normal_of_relIndex_two_of_isSimpleGroup hG₁ hi hsimple hbig
  let φ : G →* MulAut G₁ := MulAut.conjNormal
  let C : Subgroup G := φ.ker
  have hCmem : ∀ g : G, g ∈ C ↔ ∀ x ∈ G₁, g * x = x * g := by
    intro g
    constructor
    · intro hg x hx
      have h1 : φ g = 1 := MonoidHom.mem_ker.mp hg
      have h2 := congrArg (fun a : MulAut G₁ => ((a ⟨x, hx⟩ : G₁) : G)) h1
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h2]
    · intro hg
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply]
      calc g * (x : G) * g⁻¹ = (x : G) * g * g⁻¹ := by rw [hg x x.2]
        _ = x := by group
  have hG₀card : Nat.card G₀ = 2 * Nat.card G₁ := by
    have h1 := Subgroup.relIndex_mul_card G₁ G₀
    rw [inf_eq_left.mpr hG₁, hi] at h1
    omega
  have hGcard : Nat.card G = 4 * Nat.card G₁ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup G₀
    have h2 : Nat.card (G ⧸ G₀) = 2 := hG₀
    rw [h2, hG₀card] at h1
    omega
  have hquot : Nat.card (G ⧸ C) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hdvd : Nat.card (G ⧸ C) ∣ 6 * Nat.card G₁ :=
    hquot ▸ (Subgroup.card_subgroup_dvd_card φ.range).trans hAut
  have hGC : Nat.card G = Nat.card (G ⧸ C) * Nat.card C :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup C
  obtain ⟨m, hm⟩ := hdvd
  have hapos : 0 < Nat.card (G ⧸ C) := Nat.card_pos
  have hG₁pos : 0 < Nat.card G₁ := Nat.card_pos
  have h3 : 3 * Nat.card C = 2 * m := by
    apply Nat.eq_of_mul_eq_mul_left hapos
    calc Nat.card (G ⧸ C) * (3 * Nat.card C) = 3 * (Nat.card (G ⧸ C) * Nat.card C) := by ring
      _ = 3 * (4 * Nat.card G₁) := by rw [← hGC, hGcard]
      _ = 2 * (6 * Nat.card G₁) := by ring
      _ = Nat.card (G ⧸ C) * (2 * m) := by rw [hm]; ring
  have hCeven : 2 ∣ Nat.card C := by omega
  have hCG₀ : G₀ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hC x hx.1 ((hCmem x).mp hx.2)
  have hCle : Nat.card C ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card G₀ C
    rw [hCG₀] at h1
    have h2 : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    rw [h2, mul_one] at h1
    have h3' : G₀.relIndex C ≤ G₀.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right, hG₀]; omega)
    rw [Subgroup.relIndex_top_right, hG₀] at h3'
    omega
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hC2 : Nat.card C = 2 := by omega
  have hCnt : Nontrivial C := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨c, hcC, hc1⟩ := Subgroup.exists_ne_one_of_nontrivial C
  have hcG₀ : c ∉ G₀ := fun hc => hc1 (by
    have : c ∈ G₀ ⊓ C := Subgroup.mem_inf.mpr ⟨hc, hcC⟩
    rwa [hCG₀, Subgroup.mem_bot] at this)
  have huniq := (Nat.card_eq_two_iff' (1 : C)).mp hC2
  have hcc : c * c = 1 := by
    have h1 : (⟨c, hcC⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hC2] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  refine ⟨c, hcG₀, hcc, fun g => ?_⟩
  have hgc : g * c * g⁻¹ ∈ C := by
    have : C.Normal := MonoidHom.normal_ker φ
    exact this.conj_mem c hcC g
  have hne : (⟨g * c * g⁻¹, hgc⟩ : C) ≠ 1 := by
    intro h
    apply hc1
    have h1 := congrArg Subtype.val h
    have : g * c * g⁻¹ = 1 := h1
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  obtain ⟨y, -, hy⟩ := huniq
  have h1 : (⟨g * c * g⁻¹, hgc⟩ : C) = y := hy _ hne
  have h2 : (⟨c, hcC⟩ : C) = y := hy _ (fun h => hc1 (congrArg Subtype.val h))
  have h3'' : g * c * g⁻¹ = c := congrArg Subtype.val (h1.trans h2.symm)
  calc g * c = g * c * g⁻¹ * g := by group
    _ = c * g := by rw [h3'']

end CFSG.GroupTheory
