module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type w} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

theorem triv_of_anisotropic [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hρ : IsIsometric F ρ) {X : Submodule K V} (hX : F.IsTotallyIsotropic X)
    (hmax : ∀ v ∈ F.perp X, F.β v v = 0 → v ∈ X) (S : Subgroup H) (hS : IsPGroup p S)
    (hstab : ∀ g ∈ S, ∀ v ∈ X, ρ g v ∈ X) :
    ∀ g ∈ S, ∀ v ∈ F.perp X, ρ g v - v ∈ X := by
  set Φ := relFix F ρ X S with hΦ
  suffices hΦtop : F.perp X ≤ Φ by
    intro g hg v hv
    exact (hΦtop hv).2 g hg
  by_contra hne
  have hΦle : Φ ≤ F.perp X := relFix_le_perp F ρ X S
  have hΦlt : Φ < F.perp X := lt_of_le_of_ne hΦle fun h => hne h.symm.le
  have hXle : X ≤ F.perp Φ := le_perp_relFix F ρ X S
  have hXne : X ≠ F.perp Φ := by
    intro h
    have hpp : F.perp (F.perp Φ) = F.perp X := by rw [← h]
    have : FiniteDimensional K V := Module.Finite.of_finite
    rw [F.perp_perp] at hpp
    exact hΦlt.ne hpp
  have hXlt : X < F.perp Φ := lt_of_le_of_ne hXle hXne
  have hstabΦ : ∀ g ∈ S, ∀ v ∈ Φ, ρ g v ∈ Φ := fun g hg v hv =>
    apply_mem_relFix F ρ hX hstab hg hv
  have hstabΦperp : ∀ g ∈ S, ∀ v ∈ F.perp Φ, ρ g v ∈ F.perp Φ := by
    intro g hg v hv
    exact IsIsometric.apply_mem_perp_of_forall hρ (fun w hw => hstabΦ g⁻¹ (inv_mem hg) w hw) hv
  obtain ⟨v, hvΦ, hvX, hvfix⟩ :=
    exists_mem_notMem_forall_sub_mem ρ p S hS hXlt hstab hstabΦperp
  have hvperp : v ∈ F.perp X := F.perp_antitone (le_relFix F ρ hX hstab) hvΦ
  have hvin : v ∈ Φ := ⟨hvperp, hvfix⟩
  exact hvX (hmax v hvperp (hvΦ v hvin))

end CFSG.LieType.BorelTits
