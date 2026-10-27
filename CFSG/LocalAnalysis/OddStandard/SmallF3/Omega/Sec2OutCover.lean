module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {Y P : Type} [Group Y] [Group P] {ρ : Y →* P} {σ : MulAut Y} {α : MulAut P}

theorem aut_apply_apply (hσ : σ * σ = 1) (y : Y) : σ (σ y) = y := by
  simpa using congrArg (fun f : MulAut Y => f y) hσ

@[expose] def fixHom (ρ : Y →* P) (σ : MulAut Y) (α : MulAut P) (h : ∀ y, ρ (σ y) = α (ρ y)) :
    ↥(fixSub σ) →* ↥(fixSub α) where
  toFun y := ⟨ρ (y : Y), by rw [mem_fixSub_iff, ← h, show σ (y : Y) = y from y.2]⟩
  map_one' := Subtype.ext (map_one ρ)
  map_mul' a b := Subtype.ext (map_mul ρ (a : Y) (b : Y))

theorem coe_fixHom (h : ∀ y, ρ (σ y) = α (ρ y)) (y : ↥(fixSub σ)) :
    ((fixHom ρ σ α h y : ↥(fixSub α)) : P) = ρ (y : Y) := rfl

namespace OddCentralCover

variable (hρ : OddCentralCover ρ)
include hρ

theorem exists_sqrt {n : Y} (hn : n ∈ ρ.ker) : ∃ k : ℕ, (n ^ k) * (n ^ k) = n := by
  obtain ⟨j, hj⟩ := hρ.odd_card_ker
  have hnk : n ^ Nat.card ρ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hn)
  refine ⟨j + 1, ?_⟩
  calc n ^ (j + 1) * n ^ (j + 1) = n ^ (Nat.card ρ.ker + 1) := by
        rw [← pow_add, hj]
        congr 1
        omega
    _ = n := by rw [pow_succ, hnk, one_mul]

theorem fixHom_surjective (hσ : σ * σ = 1) (h : ∀ y, ρ (σ y) = α (ρ y)) :
    Function.Surjective (fixHom ρ σ α h) := by
  intro c
  obtain ⟨y, hy⟩ := hρ.surjective (c : P)
  have hc : α (c : P) = c := mem_fixSub_iff.mp c.2
  have hn : y⁻¹ * σ y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, hy, hc, inv_mul_cancel]
  have hσn : σ (y⁻¹ * σ y) = (y⁻¹ * σ y)⁻¹ := by
    rw [map_mul, map_inv, aut_apply_apply hσ, mul_inv_rev, inv_inv]
  obtain ⟨k, hk⟩ := hρ.exists_sqrt hn
  set n : Y := y⁻¹ * σ y with hndef
  set m : Y := n ^ k with hm
  have hmk : m ∈ ρ.ker := Subgroup.pow_mem _ hn k
  have hσm : σ m = m⁻¹ := by
    rw [hm, map_pow, hσn, inv_pow]
  have hfix : σ (y * m) = y * m := by
    have h1 : σ y = y * n := by rw [hndef]; group
    rw [map_mul, hσm, h1]
    calc y * n * m⁻¹ = y * (m * m) * m⁻¹ := by rw [hk]
      _ = y * m := by group
  refine ⟨⟨y * m, hfix⟩, Subtype.ext ?_⟩
  change ρ (y * m) = c
  rw [map_mul, MonoidHom.mem_ker.mp hmk, mul_one, hy]

theorem oddCentralCover_fixHom (hσ : σ * σ = 1) (h : ∀ y, ρ (σ y) = α (ρ y)) :
    OddCentralCover (fixHom ρ σ α h) := by
  have hker : ∀ p : ↥(fixSub σ), p ∈ (fixHom ρ σ α h).ker → (p : Y) ∈ ρ.ker := by
    intro p hp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
  refine ⟨hρ.fixHom_surjective hσ h, ?_, ?_⟩
  · intro p hp
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hρ.ker_le_center (hker p hp)) (g : Y))
  · have hle : ((fixHom ρ σ α h).ker).map (fixSub σ).subtype ≤ ρ.ker := by
      rintro _ ⟨p, hp, rfl⟩
      exact hker p hp
    have hcard : Nat.card ((fixHom ρ σ α h).ker) =
        Nat.card (((fixHom ρ σ α h).ker).map (fixSub σ).subtype) :=
      Nat.card_congr (((fixHom ρ σ α h).ker).equivMapOfInjective _
        (fixSub σ).subtype_injective).toEquiv
    rw [hcard]
    exact hρ.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)

end OddCentralCover

end CFSG.OddStandard.SmallF3.Omega
