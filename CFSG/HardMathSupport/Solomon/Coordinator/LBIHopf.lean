module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open
open scoped commutatorElement

theorem lbi_commutatorElement_mul_mul {Q : Type*} [Group Q] {a b z₁ z₂ : Q} (h1b : Commute z₁ b)
    (h12 : Commute z₁ z₂) (h2a : Commute z₂ a) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * (b * z₂) = b * z₂ * z₁ := (h1b.mul_right h12).eq
  have e2 : z₂ * a⁻¹ = a⁻¹ * z₂ := h2a.inv_right.eq
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]; group

theorem lbi_exists_surj_hopf {X Y : Type} [Group X] [Group Y] (π : Y →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y)
    (hperf : commutator Y = ⊤) :
    ∃ f : griessHopfMultiplier X →* ↥π.ker, Function.Surjective f := by
  classical
  let s : X → Y := Function.surjInv hπ
  have hs : ∀ x, π (s x) = x := Function.surjInv_eq hπ
  let φ : FreeGroup X →* Y := FreeGroup.lift s
  have hφ : ∀ w, π (φ w) = FreeGroup.lift id w := by
    intro w
    have : π.comp φ = FreeGroup.lift id :=
      FreeGroup.ext_hom (π.comp φ) (FreeGroup.lift id) (fun x => by simp [φ, hs])
    exact DFunLike.congr_fun this w
  have hRker : ∀ r ∈ griessHopfRelations X, φ r ∈ π.ker := fun r hr => by
    rw [MonoidHom.mem_ker, hφ]
    exact hr
  let g0 : ↥(griessHopfRelations X ⊓ commutator (FreeGroup X)) →* ↥π.ker :=
    (φ.comp (griessHopfRelations X ⊓ commutator (FreeGroup X)).subtype).codRestrict π.ker
      fun r => hRker r.1 r.2.1
  have hbot : ⁅(⊤ : Subgroup Y), π.ker⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_center_iff.1 (hcen hh) g).symm
  have hker : ∀ n : ↥(griessHopfRelations X ⊓ commutator (FreeGroup X)),
      n ∈ (⁅(⊤ : Subgroup (FreeGroup X)), griessHopfRelations X⁆).subgroupOf
        (griessHopfRelations X ⊓ commutator (FreeGroup X)) → g0 n = 1 := by
    intro n hn
    have h1 : φ n ∈ Subgroup.map φ ⁅(⊤ : Subgroup (FreeGroup X)), griessHopfRelations X⁆ :=
      Subgroup.mem_map_of_mem φ ((Subgroup.mem_subgroupOf).1 hn)
    rw [Subgroup.map_commutator] at h1
    have h2 : ⁅Subgroup.map φ ⊤, Subgroup.map φ (griessHopfRelations X)⁆ ≤
        ⁅(⊤ : Subgroup Y), π.ker⁆ :=
      Subgroup.commutator_mono le_top (fun y ⟨r, hr, hry⟩ => hry ▸ hRker r hr)
    rw [hbot] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 (h2 h1))
  refine ⟨QuotientGroup.lift _ g0 (fun n hn => hker n hn), ?_⟩
  intro z
  have hsup : ∀ y : Y, ∃ u : FreeGroup X, ∃ c ∈ π.ker, y = φ u * c := by
    intro y
    refine ⟨FreeGroup.of (π y), (φ (FreeGroup.of (π y)))⁻¹ * y, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ]
    simp
  have hC : ∀ c ∈ π.ker, ∀ g : Y, Commute c g := fun c hc g =>
    (Subgroup.mem_center_iff.1 (hcen hc) g).symm
  have hcomm : ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ Subgroup.map φ (commutator (FreeGroup X)) := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨u, c, hc, rfl⟩ := hsup a
    obtain ⟨v, c', hc', rfl⟩ := hsup b
    rw [lbi_commutatorElement_mul_mul (hC c hc _) (hC c hc c') (hC c' hc' _)]
    refine ⟨⁅u, v⁆, ?_, map_commutatorElement φ u v⟩
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup (FreeGroup X)))
      (H₂ := (⊤ : Subgroup (FreeGroup X))) (Subgroup.mem_top u) (Subgroup.mem_top v)
  have hz : (z : Y) ∈ ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ := by
    rw [← commutator_def, hperf]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcz⟩ := hcomm hz
  have hcR : c ∈ griessHopfRelations X := by
    show FreeGroup.lift id c = 1
    rw [← hφ, hcz]
    exact z.2
  exact ⟨QuotientGroup.mk ⟨c, hcR, hc⟩, Subtype.ext hcz⟩

theorem lbi_card_ker_dvd {X Y A : Type} [Group X] [Group Y] [Group A] [Finite A]
    (π : Y →* X) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y)
    (hperf : commutator Y = ⊤) (e : griessHopfMultiplier X ≃* A) :
    Nat.card ↥π.ker ∣ Nat.card A := by
  obtain ⟨f, hf⟩ := lbi_exists_surj_hopf π hπ hcen hperf
  have : Finite (griessHopfMultiplier X) := Finite.of_equiv A e.symm.toEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact Subgroup.card_dvd_of_surjective hf

end CFSG.HardMathSupport.Solomon.Coordinator
