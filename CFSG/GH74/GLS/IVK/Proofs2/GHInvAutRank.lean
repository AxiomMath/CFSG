module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem conj_injective_of_center_eq_bot {L : Type} [Group L] (hZ : center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun a : MulAut L => a h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (calc g * h = (g * h * g⁻¹) * g := by group
      _ = h * g := by rw [h1]).symm
  rw [hZ, Subgroup.mem_bot] at this
  exact this

theorem card_le_two_pow_add_of_aut {L : Type} [Group L] (hZ : center L = ⊥) {r s : ℕ}
    (hL : ∀ E : Subgroup L, (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ r)
    (hOut : ∀ E : Subgroup (Outer L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ s)
    (E : Subgroup (MulAut L)) (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 ^ (r + s) := by
  classical
  have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L
  let π : MulAut L →* Outer L := QuotientGroup.mk' (inner L)
  let ρ : ↥E →* Outer L := π.comp E.subtype
  have himg : Nat.card ↥ρ.range ≤ 2 ^ s := by
    refine hOut ρ.range ?_
    rintro _ ⟨x, rfl⟩
    show ρ x * ρ x = 1
    rw [← map_mul]
    have h2 : x * x = 1 := Subtype.ext (hE x x.2)
    rw [h2, map_one]
  have hker : Nat.card ↥ρ.ker ≤ 2 ^ r := by
    have hc : Function.Injective (MulAut.conj : L →* MulAut L) := conj_injective_of_center_eq_bot hZ
    let H : Subgroup (MulAut L) := ρ.ker.map E.subtype
    have hHle : H ≤ inner L := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π x = 1 := hx
      exact (QuotientGroup.eq_one_iff (N := inner L) _).1 h1
    let E₁ : Subgroup L := H.comap (MulAut.conj : L →* MulAut L)
    have hE₁ : ∀ e ∈ E₁, e * e = 1 := by
      intro e he
      obtain ⟨x, -, hx⟩ := he
      have h2 : (MulAut.conj : L →* MulAut L) e * (MulAut.conj : L →* MulAut L) e = 1 := by
        rw [← hx]; exact hE _ x.2
      rw [← map_mul] at h2
      exact hc (by rw [h2, map_one])
    have hcard1 : Nat.card ↥E₁ ≤ 2 ^ r := hL E₁ hE₁
    have hEH : Nat.card ↥E₁ = Nat.card ↥H := by
      have h1 : E₁.map (MulAut.conj : L →* MulAut L) = H := by
        rw [Subgroup.map_comap_eq]
        exact inf_eq_right.2 hHle
      have h2 : Nat.card ↥(E₁.map (MulAut.conj : L →* MulAut L)) = Nat.card ↥E₁ :=
        Subgroup.card_map_of_injective hc
      rw [← h2, h1]
    have hHker : Nat.card ↥H = Nat.card ↥ρ.ker := Subgroup.card_map_of_injective E.subtype_injective
    rw [← hHker, ← hEH]
    exact hcard1
  have hcardE : Nat.card ↥E = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    exact congrArg (· * Nat.card ↥ρ.ker) (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv)
  calc Nat.card ↥E = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := hcardE
    _ ≤ 2 ^ s * 2 ^ r := Nat.mul_le_mul himg hker
    _ = 2 ^ (r + s) := by rw [← pow_add, add_comm]

theorem card_mulAut_eq_card_of_inner {L : Type} [Group L] (hZ : center L = ⊥)
    (hin : ∀ φ : MulAut L, ∃ g : L, φ = MulAut.conj g) : Nat.card (MulAut L) = Nat.card L :=
  (Nat.card_congr (Equiv.ofBijective (MulAut.conj : L →* MulAut L)
    ⟨conj_injective_of_center_eq_bot hZ, fun φ => (hin φ).imp fun _ hg => hg.symm⟩)).symm

theorem all_inner_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (hin : ∀ φ : MulAut L', ∃ g : L', φ = MulAut.conj g) :
    ∀ φ : MulAut L, ∃ g : L, φ = MulAut.conj g := by
  intro φ
  obtain ⟨g, hg⟩ := hin (e.symm.trans (φ.trans e))
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun a : MulAut L' => a (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  apply e.injective
  rw [h1]
  simp [MulAut.conj_apply]

theorem exists_ne_one_mem_inner {L : Type} [Group L] [Finite L] {s : ℕ}
    (hOut : ∀ E : Subgroup (Outer L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ s)
    (D : Subgroup (MulAut L)) (hD : ∀ e ∈ D, e * e = 1) (hcard : 2 ^ s < Nat.card D) :
    ∃ x ∈ D, x ≠ 1 ∧ x ∈ inner L := by
  classical
  have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L
  have hfin : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  let π : MulAut L →* Outer L := QuotientGroup.mk' (inner L)
  let ρ : ↥D →* Outer L := π.comp D.subtype
  have himg : Nat.card ↥ρ.range ≤ 2 ^ s := by
    refine hOut ρ.range ?_
    rintro _ ⟨x, rfl⟩
    show ρ x * ρ x = 1
    rw [← map_mul]
    have h2 : x * x = 1 := Subtype.ext (hD x x.2)
    rw [h2, map_one]
  by_contra hcon
  push Not at hcon
  have hker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have h1 : (x : MulAut L) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact hcon x x.2 h1 ((QuotientGroup.eq_one_iff (N := inner L) _).1 hx)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  have : Nat.card ↥D ≤ Nat.card ↥ρ.range :=
    Nat.card_le_card_of_injective (ρ.rangeRestrict) (by
      intro a b hab
      exact hinj (congrArg Subtype.val hab))
  omega

theorem card_le_two_of_isCyclic {G : Type*} [Group G] (hG : IsCyclic G) (E : Subgroup G)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 ^ 1 := by
  have hc : IsCyclic ↥E := Subgroup.isCyclic E
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hord : orderOf g = Nat.card ↥E := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (hE g g.2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [← hord]
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.GH74.GLS.IVK.GHInv
