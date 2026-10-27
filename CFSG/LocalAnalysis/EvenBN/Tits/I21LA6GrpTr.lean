module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6GrpMod

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Transfer

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem a6grp_sylow_nonabelian [Finite G] [Group.IsPerfect G] {p : ℕ} [Fact p.Prime] {c : G}
    (hc : c ∈ center G) (hcp : orderOf c = p) (P : Sylow p G) :
    ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  haveI : IsMulCommutative (P : Subgroup G) := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  have hcP : c ∈ (P : Subgroup G) := by
    have hle : Subgroup.zpowers c ≤ center G := (Subgroup.zpowers_le).mpr hc
    haveI : (Subgroup.zpowers c).Normal :=
      ⟨fun n hn g => by
        have hn' := mem_center_iff.mp (hle hn) g
        rw [hn', mul_assoc, mul_inv_cancel, mul_one]
        exact hn⟩
    have hpg : IsPGroup p (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcp, pow_one])
    exact hpg.le_sylow_of_normal P (Subgroup.mem_zpowers c)
  have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * c ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * c ^ k * g₀ = c ^ k := by
    intro k g₀ _
    have hz : c ^ k ∈ center G := pow_mem hc k
    rw [mul_assoc, ← mem_center_iff.mp hz g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : MonoidHom.transfer (MonoidHom.id (P : Subgroup G)) c = 1 :=
    a6grp_perfect_map_one _ c
  rw [MonoidHom.transfer_eq_pow _ c hkey] at h1
  have h2 : c ^ (P : Subgroup G).index = 1 := congrArg Subtype.val h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hcp] at h3
  exact P.not_dvd_index h3

theorem a6grp_commutator_prime_order {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, b * a * b⁻¹ * a⁻¹ ∈ center G)
    (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    ∃ a b c : G, c = b * a * b⁻¹ * a⁻¹ ∧ c ∈ center G ∧ orderOf c = p := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = b * a * b⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hcen : c₀ ∈ center G := hc₀ ▸ hcomm a ha b hb
  have hc₀P : c₀ ∈ (P : Subgroup G) := by
    rw [hc₀]
    exact mul_mem (mul_mem (mul_mem hb ha) (inv_mem hb)) (inv_mem ha)
  have hc₀1 : c₀ ≠ 1 := by
    intro h1
    apply hab
    have h2 : b * a = a * b := by
      calc b * a = (b * a * b⁻¹ * a⁻¹) * (a * b) := by group
        _ = a * b := by rw [← hc₀, h1, one_mul]
    exact h2.symm
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨c₀, hc₀P⟩
  have hm' : orderOf c₀ = p ^ m := by
    rw [← hm]; exact (Subgroup.orderOf_mk _ _).symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm'
    exact hc₀1 hm'
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hpk : 0 < p ^ m' := pow_pos hp.out.pos _
  refine ⟨a ^ (p ^ m'), b, c₀ ^ (p ^ m'), ?_, pow_mem hcen _, ?_⟩
  · have hcomm' : Commute c₀ a := (mem_center_iff.mp hcen a).symm
    have h1 : b * a * b⁻¹ = c₀ * a := by rw [hc₀]; group
    have h2 : b * a ^ (p ^ m') * b⁻¹ = c₀ ^ (p ^ m') * a ^ (p ^ m') := by
      rw [← conj_pow, h1, hcomm'.mul_pow]
    rw [h2, mul_inv_cancel_right]
  · rw [orderOf_pow_of_dvd hpk.ne' (by rw [hm']; exact pow_dvd_pow p (Nat.le_succ m')), hm',
      pow_succ, Nat.mul_div_cancel_left _ hpk]

end Transfer

section Glue

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]

theorem a6grp_inf_eq_bot (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (hinj : Function.Injective ρ)
    (hdim : finrank (ZMod 2) V = 8) {x : Y} (hfix : ∀ v : V, ρ x v = v → v = 0)
    {O G₀ : Subgroup Y} (hO : Odd (Nat.card O)) [Group.IsPerfect G₀] (hxG : x ∈ G₀)
    (hcent : ∀ g ∈ G₀, ∀ o ∈ O, g * o = o * g)
    (hquot : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Q : Subgroup Y, Q ≤ G₀ → IsPGroup p Q →
      ∀ a ∈ Q, ∀ b ∈ Q, b * a * b⁻¹ * a⁻¹ ∈ O) :
    G₀ ⊓ O = ⊥ := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  by_contra hne
  have hcard1 : Nat.card ↥(G₀ ⊓ O) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Nat.card O := hpd.trans (Subgroup.card_dvd_of_le inf_le_right)
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(G₀ ⊓ O)) p hpd
  have hc₀G : (c₀ : Y) ∈ G₀ := (Subgroup.mem_inf.mp c₀.2).1
  have hc₀O : (c₀ : Y) ∈ O := (Subgroup.mem_inf.mp c₀.2).2
  let c : G₀ := ⟨(c₀ : Y), hc₀G⟩
  have hcc : ∀ j : G₀, j * c = c * j := fun j => Subtype.ext (hcent j j.2 c₀ hc₀O)
  have hcz : c ∈ center G₀ := Subgroup.mem_center_iff.mpr hcc
  have hcp : orderOf c = p := by
    rw [← Subgroup.orderOf_coe c]
    show orderOf (c₀ : Y) = p
    rw [Subgroup.orderOf_coe]
    exact hc₀
  obtain ⟨P⟩ : Nonempty (Sylow p G₀) := inferInstance
  have hnab := a6grp_sylow_nonabelian hcz hcp P
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, b * a * b⁻¹ * a⁻¹ ∈ center G₀ := by
    intro a ha b hb
    have hQ : IsPGroup p ((P : Subgroup G₀).map G₀.subtype) := P.isPGroup'.map G₀.subtype
    have hQG : (P : Subgroup G₀).map G₀.subtype ≤ G₀ := by
      rintro _ ⟨g, -, rfl⟩
      exact g.2
    have hO' := hquot p hp hp2 _ hQG hQ (a : Y) ⟨a, ha, rfl⟩ (b : Y) ⟨b, hb, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hcent g g.2 _ hO'
  obtain ⟨a', b', c', hc', hcz', hcp'⟩ := a6grp_commutator_prime_order P hcomm hnab
  exact a6grp_module_contra (G := G₀) (ρ.comp G₀.subtype) (hinj.comp Subtype.val_injective)
    hdim (x := ⟨x, hxG⟩) (fun v hv => hfix v hv) hc' (Subgroup.mem_center_iff.mp hcz') hp hp2
    hcp'

end Glue


end CFSG.LocalAnalysis.EvenBN.Tits.I21L
