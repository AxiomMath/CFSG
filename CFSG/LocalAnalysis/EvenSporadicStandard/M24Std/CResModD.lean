module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResModA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResModC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResModB

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

@[expose] noncomputable def kappa (h : Setup L A C z) : egNL L A →* MulAut C :=
  (actC C h.hC.comm).comp (psi h)

theorem kappa_apply (h : Setup L A C z) (n : egNL L A) (c : C) :
    ((kappa h n c : C) : G) = (n : G) * c * (n : G)⁻¹ := rfl

theorem modData_of_setup (h : Setup L A C z) (hQ : SextetFactsQ L A) {H : Subgroup (egNL L A)}
    (hH : H.index = 2) :
    ModData (A.subgroupOf C) (H.map (kappa h)) (actC C h.hC.comm (zt h)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro θ ⟨n, hn, rfl⟩ a ha
    rw [mem_subgroupOf] at ha ⊢
    rw [kappa_apply]
    exact (mem_normalizer_iff.1 (mem_inf.1 n.2).1 a).1 ha
  · intro B hBA hBinv
    let BG : Subgroup G := B.map C.subtype
    have hBGA : BG ≤ A := by
      rintro _ ⟨b, hb, rfl⟩
      exact mem_subgroupOf.1 (hBA hb)
    have hBGinv : ∀ n ∈ H, ∀ b ∈ BG, (n : G) * b * (n : G)⁻¹ ∈ BG := by
      rintro n hn _ ⟨b, hb, rfl⟩
      exact ⟨kappa h n b, hBinv _ (mem_map_of_mem _ hn) b hb, rfl⟩
    rcases irreducible_of_index_two h.hF hH hBGA hBGinv with h1 | h1
    · left
      rw [eq_bot_iff]
      intro b hb
      have : (b : G) ∈ BG := ⟨b, hb, rfl⟩
      rw [h1, mem_bot] at this
      exact mem_bot.2 (Subtype.ext this)
    · right
      refine le_antisymm hBA fun a ha => ?_
      have : (a : G) ∈ BG := by
        rw [h1]
        exact mem_subgroupOf.1 ha
      obtain ⟨b, hb, hba⟩ := this
      have hba' : b = a := Subtype.ext hba
      rw [← hba']
      exact hb
  · rintro θ ⟨n, hn, rfl⟩
    have := congrArg (actC C h.hC.comm) (psi_comm h n)
    rw [map_mul, map_mul] at this
    exact this.symm
  · intro v
    rw [mem_subgroupOf]
    have := h.hC.comm_z v v.2
    exact this
  · intro a ha
    obtain ⟨c, hc, hcz⟩ := h.hC.onto a (mem_subgroupOf.1 ha)
    exact ⟨⟨c, hc⟩, Subtype.ext hcz⟩
  · intro v hv
    rw [mem_subgroupOf]
    have hv' : z * (v : G) * z⁻¹ * (v : G)⁻¹ = 1 := congrArg Subtype.val hv
    have hcz : (v : G) * z = z * v := by
      have := mul_inv_eq_one.1 hv'
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    exact mem_A_of_comm h v.2 hcz
  · intro x hx hx1
    have key : ∀ a : {a : C // a ∈ A.subgroupOf C ∧ ∀ θ ∈ H.map (kappa h), θ x = x → θ a = a},
        ∀ n ∈ H, (n : G) * (x : G) * (n : G)⁻¹ = (x : G) →
          (n : G) * (a.1 : G) * (n : G)⁻¹ = (a.1 : G) := by
      intro a n hn hnx
      have hθx : kappa h n x = x := Subtype.ext hnx
      exact congrArg Subtype.val (a.2.2 (kappa h n) (mem_map_of_mem _ hn) hθx)
    refine le_trans (Nat.card_le_card_of_injective
      (fun a : {a : C // a ∈ A.subgroupOf C ∧ ∀ θ ∈ H.map (kappa h), θ x = x → θ a = a} =>
        (⟨(a.1 : G), mem_subgroupOf.1 a.2.1, key a⟩ :
          {a : G // a ∈ A ∧ ∀ n ∈ H, (n : G) * (x : G) * (n : G)⁻¹ = (x : G) →
            (n : G) * a * (n : G)⁻¹ = a})) ?_)
      (card_fixfix_le_four h.hF hQ hH (mem_subgroupOf.1 hx) (fun e => hx1 (Subtype.ext e)))
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  · intro hbot
    obtain ⟨a₁, ha₁, -, -, h1, -⟩ := h.hF.orbits
    have : (⟨a₁, h.hC.A_le ha₁⟩ : C) ∈ A.subgroupOf C := mem_subgroupOf.2 ha₁
    rw [hbot, mem_bot] at this
    exact h1 (congrArg Subtype.val this)

theorem card_centralizer_le (h : Setup L A C z) (hQ : SextetFactsQ L A)
    {H : Subgroup (egNL L A)} (hH : H.index = 2) (K : Subgroup (MulAut C))
    (hK : ∀ k ∈ K, ∀ t ∈ H.map (psi h),
      k * actC C h.hC.comm t = actC C h.hC.comm t * k) : Nat.card K ≤ 256 := by
  refine card_le_of_centralizes (fun a b => Subtype.ext (h.hC.comm a a.2 b b.2))
    (modData_of_setup h hQ hH) K ?_
  rintro k hk θ ⟨n, hn, rfl⟩
  exact hK k hk (psi h n) (mem_map_of_mem _ hn)

end CSide

end CFSG.EvenSporadicStandard.M24Std
