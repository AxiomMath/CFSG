module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Frame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem PspFrame.Setup107.of_ctx {t z : G} {L S K1 K2 : Subgroup G} [Finite G]
    (hctx : Sec10Ctx G t L S z K1 K2) (hSN : S ≤ normalizer (L : Set G))
    (hCS : centralizer (L : Set G) ⊓ S = zpowers t) : PspFrame.Setup107 L t S := by
  have ht2 : orderOf t = 2 := hctx.involution
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  exact
    { S_le_N := hSN
      S_two := hctx.sylow.2.1
      t_sq := htsq
      t_ne := htne
      t_comm := fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hctx.sylow.1 hs)
      cent_S := hCS }

theorem exists_conj_invol {S : Subgroup G} {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hss : s * s = 1) :
    ∃ α : ↥S →* ↥S, (∀ y : ↥S, ((α y : ↥S) : G) = s * y * s) ∧ ∀ y : ↥S, α (α y) = y := by
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hss' : ∀ X : G, s * (s * X) = X := fun X => by rw [← mul_assoc, hss, one_mul]
  have hconj : ∀ y ∈ S, s * y * s ∈ S := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.1 hsN y).1 hy
    rwa [hs1] at h
  refine ⟨{ toFun := fun y => ⟨s * y * s, hconj y y.2⟩
            map_one' := Subtype.ext (by simp [hss])
            map_mul' := fun a b => Subtype.ext ?_ }, fun y => rfl, fun y => Subtype.ext ?_⟩
  · show s * ((a : G) * b) * s = s * a * s * (s * b * s)
    simp only [mul_assoc, hss', mul_one]
  · show s * (s * (y : G) * s) * s = y
    simp only [mul_assoc, hss, hss', mul_one]

theorem conj_swap [Finite G] {A A2 : Subgroup G} {s : G} (hss : s * s = 1)
    (hA : ∀ a ∈ A, s⁻¹ * a * s ∈ A2) (hcard : Nat.card A2 ≤ Nat.card A) :
    ∀ b ∈ A2, s⁻¹ * b * s ∈ A := by
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hss' : ∀ X : G, s * (s * X) = X := fun X => by rw [← mul_assoc, hss, one_mul]
  let f : ↥A → ↥A2 := fun a => ⟨s⁻¹ * a * s, hA a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : s⁻¹ * (a : G) * s = s⁻¹ * (b : G) * s := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  obtain ⟨-, hsurj⟩ := hf.bijective_of_nat_card_le hcard
  intro b hb
  obtain ⟨a, ha⟩ := hsurj ⟨b, hb⟩
  have h1 : s⁻¹ * (a : G) * s = b := congrArg Subtype.val ha
  have h2 : s⁻¹ * b * s = a := by
    rw [← h1, hs1]
    simp only [mul_assoc, hss, hss', mul_one]
  rw [h2]
  exact a.2

end CFSG.OddStandard.SmallF3.Omega
