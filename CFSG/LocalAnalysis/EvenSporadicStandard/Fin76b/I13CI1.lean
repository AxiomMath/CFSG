module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Cl1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Sig2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α) {π : MulAut ↥E →* Equiv.Perm (Fin 5)}

include c

theorem card_range_caseI (hπ : EPi E π)
    (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
      π a ∈ alternatingGroup (Fin 5) ∧ π b = π a) :
    Nat.card ↥c.rho.range = 15360 := by
  set A : Subgroup (MulAut ↥E) := (alternatingGroup (Fin 5)).comap π with hA
  let f : ↥c.rho.range ≃ ↥A × ↥(innAutE E) :=
    { toFun := fun p => (⟨p.1.1, ((hI p.1.1 p.1.2).1 p.2).1⟩,
        ⟨p.1.1⁻¹ * p.1.2, (hπ.ker _).1 (by
          rw [map_mul, map_inv, ((hI p.1.1 p.1.2).1 p.2).2]; group)⟩)
      invFun := fun q => ⟨(q.1.1, q.1.1 * q.2.1), (hI _ _).2 ⟨q.1.2, by
          rw [map_mul, (hπ.ker _).2 q.2.2, mul_one]⟩⟩
      left_inv := fun p => by
        apply Subtype.ext
        refine Prod.ext rfl ?_
        show p.1.1 * (p.1.1⁻¹ * p.1.2) = p.1.2
        group
      right_inv := fun q => by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          show q.1.1⁻¹ * (q.1.1 * q.2.1) = q.2.1
          group }
  rw [Nat.card_congr f, Nat.card_prod, c.card_AE hπ, c.card_inn]

theorem card_pgroup_range_le (hπ : EPi E π)
    (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
      π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)
    {P : Subgroup (MulAut ↥E × MulAut ↥E)} (hP : IsPGroup 2 P) (hPR : P ≤ c.rho.range) :
    Nat.card P ≤ 1024 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ 15360 := (c.card_range_caseI hπ hI) ▸ Subgroup.card_dvd_of_le hPR
  have hk10 : k ≤ 10 := by
    by_contra hk11
    have h2 : 2 ^ 11 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h2.trans (hk ▸ hdvd)
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk10
    _ = 1024 := by norm_num

theorem card_le_four_Rhat {R : Subgroup G} (hRN : R ≤ c.N1) (hKR : R ⊓ c.KR ≤ c.Zs) :
    Nat.card R ≤ 4 * Nat.card (c.Rhat R) := by
  let g : ↥R →* MulAut ↥E × MulAut ↥E := c.rho.comp (Subgroup.inclusion hRN)
  have h1 := Subgroup.card_ker_mul_card_range g
  have hrange : g.range = c.Rhat R := by
    ext p
    constructor
    · rintro ⟨r, rfl⟩
      exact c.mem_Rhat.2 ⟨⟨(r : G), hRN r.2⟩, r.2, rfl⟩
    · intro hp
      obtain ⟨r, hrR, rfl⟩ := c.mem_Rhat.1 hp
      exact ⟨⟨(r : G), hrR⟩, rfl⟩
  have hker : Nat.card g.ker ≤ 4 := by
    have hinj : Function.Injective (fun r : g.ker => (⟨((r : ↥R) : G), hKR ⟨(r : ↥R).2,
        c.mem_KR.2 ⟨hRN (r : ↥R).2, r.2⟩⟩⟩ : ↥c.Zs)) := by
      intro a b hab
      have h5 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h5)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [c.card_Zs'] at this
  rw [hrange] at h1
  calc Nat.card R = Nat.card g.ker * Nat.card (c.Rhat R) := h1.symm
    _ ≤ 4 * Nat.card (c.Rhat R) := Nat.mul_le_mul_right _ hker

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
