module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

def fixCosetSub {V : Type} (N Rh : Subgroup (Equiv.Perm V)) : Subgroup (Equiv.Perm V) where
  carrier := {m | m ∈ N ∧ ∀ r ∈ Rh, r * m * r⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨N.mul_mem ha hb, fun r hr => ?_⟩
    have e : r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
    rw [e]
    exact N.mul_mem (ha' r hr) (hb' r hr)
  one_mem' := ⟨N.one_mem, fun r _ => by simp [N.one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨N.inv_mem ha, fun r hr => ?_⟩
    have e : r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
    rw [e]
    exact N.inv_mem (ha' r hr)

theorem mem_fixCosetSub {V : Type} {N Rh : Subgroup (Equiv.Perm V)} {m : Equiv.Perm V} :
    m ∈ fixCosetSub N Rh ↔ m ∈ N ∧ ∀ r ∈ Rh, r * m * r⁻¹ ∈ N := Iff.rfl

theorem conj_mem_fixCosetSub {V : Type} {N Rh : Subgroup (Equiv.Perm V)} {s : Equiv.Perm V}
    (hs : s ∈ Rh) {m : Equiv.Perm V} (hm : m ∈ fixCosetSub N Rh) :
    s * m * s⁻¹ ∈ fixCosetSub N Rh := by
  obtain ⟨-, hm'⟩ := mem_fixCosetSub.mp hm
  refine mem_fixCosetSub.mpr ⟨hm' s hs, fun r hr => ?_⟩
  have e : r * (s * m * s⁻¹) * r⁻¹ = (r * s) * m * (r * s)⁻¹ := by group
  rw [e]
  exact hm' (r * s) (Rh.mul_mem hr hs)

theorem conj_n_mem_fixCoset {V : Type} {N Rh : Subgroup (Equiv.Perm V)} (g : Equiv.Perm V)
    (hg : ∀ r ∈ Rh, g⁻¹ * (r * g * r⁻¹) ∈ N) {r s : Equiv.Perm V} (hr : r ∈ Rh)
    (hs : s ∈ Rh) : r * (g⁻¹ * (s * g * s⁻¹)) * r⁻¹ ∈ N := by
  have e : r * (g⁻¹ * (s * g * s⁻¹)) * r⁻¹ =
      (g⁻¹ * (r * g * r⁻¹))⁻¹ * (g⁻¹ * ((r * s) * g * (r * s)⁻¹)) := by group
  rw [e]
  exact N.mul_mem (N.inv_mem (hg r hr)) (hg (r * s) (Rh.mul_mem hr hs))

theorem n_mem_fixCosetSub {V : Type} {N Rh : Subgroup (Equiv.Perm V)} (g : Equiv.Perm V)
    (hg : ∀ r ∈ Rh, g⁻¹ * (r * g * r⁻¹) ∈ N) {s : Equiv.Perm V} (hs : s ∈ Rh) :
    g⁻¹ * (s * g * s⁻¹) ∈ fixCosetSub N Rh :=
  mem_fixCosetSub.mpr ⟨hg s hs, fun _ hr => conj_n_mem_fixCoset g hg hr hs⟩

theorem act_mem_fixCosetSub {V : Type} {N Rh : Subgroup (Equiv.Perm V)} (g : Equiv.Perm V)
    (hg : ∀ r ∈ Rh, g⁻¹ * (r * g * r⁻¹) ∈ N) {r : Equiv.Perm V} (hr : r ∈ Rh)
    {m : Equiv.Perm V} (hm : m ∈ fixCosetSub N Rh) :
    g⁻¹ * (r * (g * m) * r⁻¹) ∈ fixCosetSub N Rh := by
  have e : g⁻¹ * (r * (g * m) * r⁻¹) = (g⁻¹ * (r * g * r⁻¹)) * (r * m * r⁻¹) := by group
  rw [e]
  exact (fixCosetSub N Rh).mul_mem (n_mem_fixCosetSub g hg hr) (conj_mem_fixCosetSub hr hm)

theorem exists_fixed_coset {V : Type} [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hR : IsPGroup p Rh)
    (G : Subgroup (Equiv.Perm V)) (hG : ∀ r ∈ Rh, ∀ g ∈ G, r * g * r⁻¹ ∈ G)
    (N : Subgroup (Equiv.Perm V)) (hNG : N ≤ G) (hNn : (N.subgroupOf G).Normal)
    (hN2 : IsPGroup 2 N) (g : Equiv.Perm V) (hgG : g ∈ G)
    (hg : ∀ r ∈ Rh, g⁻¹ * (r * g * r⁻¹) ∈ N) :
    ∃ c ∈ G, (∀ r ∈ Rh, r * c = c * r) ∧ c⁻¹ * g ∈ N := by
  have hMN : fixCosetSub N Rh ≤ N := fun m hm => (mem_fixCosetSub.mp hm).1
  have hM2 : IsPGroup 2 (fixCosetSub N Rh) := hN2.to_le hMN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hM2
  have hpp : p.Prime := Fact.out
  have hndvd : ¬ p ∣ Nat.card (fixCosetSub N Rh) := by
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))
  letI act : MulAction Rh (fixCosetSub N Rh) :=
    { smul := fun r m =>
        ⟨g⁻¹ * ((r : Equiv.Perm V) * (g * (m : Equiv.Perm V)) * (r : Equiv.Perm V)⁻¹),
          act_mem_fixCosetSub g hg r.2 m.2⟩
      one_smul := fun m => Subtype.ext (by
        show g⁻¹ * ((1 : Equiv.Perm V) * (g * (m : Equiv.Perm V)) * (1 : Equiv.Perm V)⁻¹) =
          (m : Equiv.Perm V)
        simp)
      mul_smul := fun r s m => Subtype.ext (by
        show g⁻¹ * (((r * s : Rh) : Equiv.Perm V) * (g * (m : Equiv.Perm V)) *
            ((r * s : Rh) : Equiv.Perm V)⁻¹) =
          g⁻¹ * ((r : Equiv.Perm V) * (g * (g⁻¹ * ((s : Equiv.Perm V) *
            (g * (m : Equiv.Perm V)) * (s : Equiv.Perm V)⁻¹))) * (r : Equiv.Perm V)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨m₀, hm₀⟩ :=
    IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hR (fixCosetSub N Rh) hndvd
  have hfix := MulAction.mem_fixedPoints.mp hm₀
  have hcomm : ∀ r ∈ Rh, r * (g * (m₀ : Equiv.Perm V)) = (g * (m₀ : Equiv.Perm V)) * r := by
    intro r hr
    have h0 := congrArg Subtype.val (hfix ⟨r, hr⟩)
    have h1 : g⁻¹ * (r * (g * (m₀ : Equiv.Perm V)) * r⁻¹) = (m₀ : Equiv.Perm V) := h0
    have h2 : r * (g * (m₀ : Equiv.Perm V)) * r⁻¹ = g * (m₀ : Equiv.Perm V) :=
      inv_mul_eq_iff_eq_mul.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hm₀N : (m₀ : Equiv.Perm V) ∈ N := (mem_fixCosetSub.mp m₀.2).1
  refine ⟨g * (m₀ : Equiv.Perm V), G.mul_mem hgG (hNG hm₀N), hcomm, ?_⟩
  have e : (g * (m₀ : Equiv.Perm V))⁻¹ * g = (m₀ : Equiv.Perm V)⁻¹ := by group
  rw [e]
  exact N.inv_mem hm₀N

end CFSG.LieType.ChevTwo.OppCl.TK
