module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem not_isSolvable_of_isQuasisimple {X : Type*} [Group X] (hX : IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hX
  have : Group.IsSolvable (X ⧸ center X) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := X ⧸ center X)).2 this a b)

theorem Ivk73Cfg.exists_involutory_aut (h : Ivk73Cfg N L K Q) :
    ∃ α : MulAut ↥L, α ^ 2 = 1 ∧ α ≠ 1 ∧ ∀ x ∈ K.subgroupOf L, α x = x := by
  have := h.normal
  obtain ⟨u, huQ, -, -, hu2, -, -, -⟩ := C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
  have huK : ∀ k ∈ K, k * u = u * k := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le huQ) k hk
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  refine ⟨MulAut.conjNormal u, ?_, ?_, ?_⟩
  · rw [pow_two, ← map_mul, huu, map_one]
  · intro h1
    have hcent : ∀ l ∈ L, u * l = l * u := by
      intro l hl
      have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : N)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc u * l = u * l * u⁻¹ * u := by group
        _ = l * u := by rw [h2]
    have := h.cent_trivial u hcent
    rw [this, orderOf_one] at hu2
    omega
  · intro x hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hxK : (x : N) ∈ K := hx
    calc u * (x : N) * u⁻¹ = (x : N) * u * u⁻¹ := by rw [← huK _ hxK]
      _ = x := by group

theorem Ivk73Cfg.false_of_fixed_solvable (h : Ivk73Cfg N L K Q)
    (hfix : ∀ α : MulAut ↥L, α ^ 2 = 1 → α ≠ 1 → ∀ M : Subgroup ↥L, (∀ x ∈ M, α x = x) →
      Group.IsSolvable ↥M) : False := by
  obtain ⟨α, hα2, hα1, hαK⟩ := h.exists_involutory_aut
  have hs : Group.IsSolvable ↥(K.subgroupOf L) := hfix α hα2 hα1 _ hαK
  have hsK : Group.IsSolvable ↥K := by
    have := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h.K_le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h.K_le).symm.injective
  exact not_isSolvable_of_isQuasisimple h.K_quasi hsK

theorem conjNormal_injective_of_cent_trivial [L.Normal]
    (hcent : ∀ n : N, (∀ l ∈ L, n * l = l * n) → n = 1) :
    Function.Injective (MulAut.conjNormal : N →* MulAut ↥L) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  apply hcent n
  intro l hl
  have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : N)) hn
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc n * l = n * l * n⁻¹ * n := by group
    _ = l * n := by rw [h1]

theorem Ivk73Cfg.exists_involution_mem_L (h : Ivk73Cfg N L K Q)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1) :
    ∃ u : N, u ∈ Q ∧ orderOf u = 2 ∧ u ∈ L := by
  have := h.normal
  obtain ⟨E, hEQ, hE, hEc⟩ := h.exists_E
  have hsq : ∀ a : ↥E, a * a = 1 := fun a => by
    rw [← pow_two]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hE.exponent_dvd_p) a
  let φ : N →* MulAut ↥L := MulAut.conjNormal
  have hφ : Function.Injective φ := conjNormal_injective_of_cent_trivial h.cent_trivial
  have hDsq : ∀ e ∈ E.map φ, e * e = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have h2 : a * a = 1 := congrArg Subtype.val (hsq ⟨a, ha⟩)
    rw [h2, map_one]
  have hDcard : 2 ^ 1 < Nat.card ↥(E.map φ) := by
    rw [Subgroup.card_map_of_injective hφ, hEc]
    norm_num
  obtain ⟨x, ⟨u, huE, rfl⟩, hx1, hxin⟩ := GHInv.exists_ne_one_mem_inner hOut (E.map φ) hDsq hDcard
  obtain ⟨l, hl⟩ := hxin
  have hu1 : u ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have hul : u = (l : N) := by
    apply hφ
    rw [← hl]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    simp [φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  refine ⟨u, hEQ huE, orderOf_eq_prime ?_ hu1, hul ▸ l.2⟩
  have h2 := hsq ⟨u, huE⟩
  rw [pow_two]
  exact congrArg Subtype.val h2

theorem Ivk73Cfg.false_of_inner_solvable (h : Ivk73Cfg N L K Q)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1)
    (hfix : ∀ y : ↥L, y * y = 1 → y ≠ 1 → ∀ M : Subgroup ↥L, M ≤ centralizer ({y} : Set ↥L) →
      Group.IsSolvable ↥M) : False := by
  obtain ⟨u, huQ, hu2, huL⟩ := h.exists_involution_mem_L hOut
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  let y : ↥L := ⟨u, huL⟩
  have hy2 : y * y = 1 := Subtype.ext huu
  have hy1 : y ≠ 1 := by
    intro h1
    have : u = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hu2
    omega
  have hle : K.subgroupOf L ≤ centralizer ({y} : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxK : (x : N) ∈ K := hx
    exact Subgroup.mem_centralizer_iff.1 (h.Q_sylow.le huQ) _ hxK
  have hs : Group.IsSolvable ↥(K.subgroupOf L) := hfix y hy2 hy1 _ hle
  have hsK : Group.IsSolvable ↥K := by
    have := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h.K_le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h.K_le).symm.injective
  exact not_isSolvable_of_isQuasisimple h.K_quasi hsK


end CFSG.GH74.GLS.IVK
