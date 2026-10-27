module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X G : Type} [Group X] [Finite X] [Group G] [Finite G] {Z A : Subgroup X}
  {π : X →* G} {M : Subgroup G} {H : Subgroup X}

theorem l2_mem_bar (S : L2Setup Z A π M H) {a : X} (ha : a ∈ A) : l2Mu X a ∈ l2Bar H := by
  have hpa : π a ∈ M := S.A_le (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  rw [← S.map_H] at hpa
  obtain ⟨h, hh, hph⟩ := Subgroup.mem_map.mp hpa
  have hker : h⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hph]
    simp
  rw [S.ker] at hker
  obtain ⟨z, hz, o, ho, hzo⟩ := Subgroup.mem_sup_of_normal_right.mp hker
  have haeq : a = h * (z * o) := by
    rw [hzo]
    group
  refine Subgroup.mem_map.mpr ⟨h * z, mul_mem hh (S.Z_le_H hz), ?_⟩
  rw [haeq]
  simp only [map_mul]
  have ho1 : l2Mu X o = 1 := by
    simpa only [QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff (N := CFSG.oddCore X) o).mpr ho
  rw [ho1, mul_one]

theorem l2_lift (S : L2Setup Z A π M H) {ρ : ↥(l2Bar H) →* ↥M}
    (hρ : ∀ (x : ↥(l2Bar H)) (y : X), (x : X ⧸ CFSG.oddCore X) = l2Mu X y → (ρ x : G) = π y)
    (x : ↥(l2Bar H)) (hx : (ρ x : G) ∈ A.map π) :
    ∃ a ∈ A, (x : X ⧸ CFSG.oddCore X) = l2Mu X a := by
  obtain ⟨y₀, hy₀, hμy⟩ := Subgroup.mem_map.mp x.2
  have hρx : (ρ x : G) = π y₀ := hρ x y₀ hμy.symm
  rw [hρx] at hx
  obtain ⟨a₀, ha₀, hπa⟩ := Subgroup.mem_map.mp hx
  have hker : a₀⁻¹ * y₀ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπa]
    simp
  rw [S.ker] at hker
  obtain ⟨z, hz, o, ho, hzo⟩ := Subgroup.mem_sup_of_normal_right.mp hker
  have hyeq : y₀ = a₀ * (z * o) := by
    rw [hzo]
    group
  refine ⟨a₀ * z, mul_mem ha₀ (S.Z_le_A hz), ?_⟩
  rw [← hμy, hyeq]
  simp only [map_mul]
  have ho1 : l2Mu X o = 1 := by
    simpa only [QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff (N := CFSG.oddCore X) o).mpr ho
  rw [ho1, mul_one]

private theorem l2_comm_eq {a b : X} (x y : ↥(l2Bar H))
    (hx : (x : X ⧸ CFSG.oddCore X) = l2Mu X a)
    (hy : (y : X ⧸ CFSG.oddCore X) = l2Mu X b) :
    ((⁅x, y⁆ : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X) = l2Mu X ⁅a, b⁆ := by
  have h1 : ((⁅x, y⁆ : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X)
      = ⁅(x : X ⧸ CFSG.oddCore X), (y : X ⧸ CFSG.oddCore X)⁆ :=
    map_commutatorElement (f := Subgroup.subtype (l2Bar H)) x y
  rw [h1, hx, hy, map_commutatorElement (f := l2Mu X)]

theorem l2_pauli (S : L2Setup Z A π M H) (hform : L2Form Z A) {ρ : ↥(l2Bar H) →* ↥M}
    (hρ : ∀ (x : ↥(l2Bar H)) (y : X), (x : X ⧸ CFSG.oddCore X) = l2Mu X y → (ρ x : G) = π y) :
    L2Pauli ρ ((A.map π).subgroupOf M) := by
  classical
  obtain ⟨ι, hιZ, hι2, hsq, hcomm, hnd⟩ := hform
  let ι' : ↥(l2Bar H) := ⟨l2Mu X ι, l2_mem_bar S (S.Z_le_A hιZ)⟩
  have hpow : ι' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (l2Mu X ι) ^ 2 = (1 : X ⧸ CFSG.oddCore X)
    rw [← map_pow]
    have hιsq : ι ^ 2 = 1 := by
      rw [← hι2]; exact pow_orderOf_eq_one ι
    rw [hιsq, map_one]
  have hne : ι' ≠ 1 := by
    intro h1
    have hmu : l2Mu X ι = 1 := by
      have := congrArg (fun z : ↥(l2Bar H) => (z : X ⧸ CFSG.oddCore X)) h1
      simpa [ι'] using this
    have hO : ι ∈ CFSG.oddCore X := by
      refine (QuotientGroup.eq_one_iff (N := CFSG.oddCore X) ι).mp ?_
      simpa only [QuotientGroup.mk'_apply] using hmu
    have hdvd : 2 ∣ Nat.card (CFSG.oddCore X) := by
      simpa [hι2] using Subgroup.orderOf_dvd_natCard (CFSG.oddCore X) hO
    exact (lit_odd_card_oddCore X).not_two_dvd_nat hdvd
  have hord : orderOf ι' = 2 := orderOf_eq_prime (p := 2) hpow hne
  have hcent : ι' ∈ center ↥(l2Bar H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp g.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    change (g : X ⧸ CFSG.oddCore X) * l2Mu X ι = l2Mu X ι * (g : X ⧸ CFSG.oddCore X)
    rw [← hgy, ← map_mul, ← map_mul, S.central ι hιZ y]
  refine ⟨ι', hcent, hord, ?_, ?_, ?_⟩
  · intro x y hx hy
    have hx' : (ρ x : G) ∈ A.map π := Subgroup.mem_subgroupOf.mp hx
    have hy' : (ρ y : G) ∈ A.map π := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨a, ha, hxa⟩ := l2_lift S hρ x hx'
    obtain ⟨b, hb, hyb⟩ := l2_lift S hρ y hy'
    rcases hcomm a ha b hb with hc | hc
    · left
      apply Subtype.ext
      rw [l2_comm_eq x y hxa hyb, hc]
      simp only [map_one, Subgroup.coe_one]
    · right
      apply Subtype.ext
      rw [l2_comm_eq x y hxa hyb, hc]
  · intro x hx hxne
    have hx' : (ρ x : G) ∈ A.map π := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨a, ha, hxa⟩ := l2_lift S hρ x hx'
    have haZ : a ∉ Z := by
      intro haZ
      apply hxne
      apply Subtype.ext
      have hπa : π a = 1 := by
        have : a ∈ π.ker := by
          rw [S.ker]
          exact Subgroup.mem_sup_left haZ
        exact MonoidHom.mem_ker.mp this
      rw [hρ x a hxa, hπa]
      simp
    obtain ⟨b, hb, hcb⟩ := hnd a ha haZ
    let y : ↥(l2Bar H) := ⟨l2Mu X b, l2_mem_bar S hb⟩
    refine ⟨y, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, hρ y b rfl]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    · apply Subtype.ext
      rw [l2_comm_eq x y hxa rfl, hcb]
  · intro e he
    have he' : (e : G) ∈ A.map π := Subgroup.mem_subgroupOf.mp he
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp he'
    let x : ↥(l2Bar H) := ⟨l2Mu X a, l2_mem_bar S ha⟩
    refine ⟨x, ?_, ?_⟩
    · apply Subtype.ext
      rw [hρ x a rfl]
      exact hae
    · have hx2 : ((x ^ 2 : ↥(l2Bar H)) : X ⧸ CFSG.oddCore X) = l2Mu X (a ^ 2) := by
        rw [Subgroup.coe_pow]
        change (l2Mu X a) ^ 2 = l2Mu X (a ^ 2)
        rw [← map_pow]
      rcases hsq a ha with h1 | h1
      · left
        apply Subtype.ext
        rw [hx2, h1]
        simp only [map_one, Subgroup.coe_one]
      · right
        apply Subtype.ext
        rw [hx2, h1]

end CFSG.OddStandard.HigherRank.YamadaG23
