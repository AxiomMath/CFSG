module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutEngine
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutLift

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

theorem autConj_mul_conj {Y : Type} [Group Y] (α : MulAut Y) (x : Y) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp [MulAut.conj_apply]

theorem SylowWitness.F_unique {Y : Type} [Group Y] (hcZ : Subgroup.center Y = ⊥)
    {S : Subgroup (MulAut Y)} {t t' : Y} {F F' : Subgroup Y} (W : SylowWitness Y S t F)
    (W' : SylowWitness Y S t' F') : F = F' := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    HypOne.conj_injective_of_center_eq_bot hcZ
  have hE : innerImage Y F' = innerImage Y F := by
    refine W.e16.unique _ W'.e16.inner_le ?_ ?_ ?_ ?_ ?_ ?_
    · rintro α hα _ ⟨x, hx, rfl⟩
      refine ⟨α x, (W'.e16.normal α hα x).1 hx, ?_⟩
      show MulAut.conj (α x) = α * MulAut.conj x * α⁻¹
      exact (autConj_mul_conj α x).symm
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      show MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x
      rw [← map_mul, ← map_mul, W'.e16.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      show MulAut.conj x * MulAut.conj x = 1
      rw [← map_mul, W'.e16.sq x hx, map_one]
    · have : Nat.card (innerImage Y F') = Nat.card F' := Subgroup.card_map_of_injective hinj
      rw [this]
      exact W'.e16.card
    · intro γ _ hcomm
      refine W'.e16.cent γ fun x hx => ?_
      have h1 := hcomm (MulAut.conj x) ⟨x, hx, rfl⟩
      have h2 : MulAut.conj (γ x) = MulAut.conj x := by
        rw [← autConj_mul_conj γ x]
        calc γ * MulAut.conj x * γ⁻¹ = MulAut.conj x * γ * γ⁻¹ := by rw [h1]
          _ = MulAut.conj x := by group
      exact hinj h2
    · obtain ⟨x, hx, hx1, hx8⟩ := W'.e16.orbit8
      refine ⟨MulAut.conj x, ⟨x, hx, rfl⟩, ?_, ?_⟩
      · intro h1
        exact hx1 (hinj (by rw [map_one]; exact h1))
      · have hset : autConjClass S (MulAut.conj x) =
            (MulAut.conj : Y →* MulAut Y) '' autOrbit S x := by
          ext β
          constructor
          · rintro ⟨α, hα, rfl⟩
            exact ⟨α x, ⟨α, hα, rfl⟩, (autConj_mul_conj α x).symm⟩
          · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
            exact ⟨α, hα, (autConj_mul_conj α x).symm⟩
        rw [hset, Set.ncard_image_of_injective _ hinj]
        exact hx8
  exact (Subgroup.map_injective hinj hE).symm

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem engine [Finite G] (hcZ : center (L ⧸ center L) = ⊥)
    (hEng : AutSylowEngine (L ⧸ center L)) : EngineData (L ⧸ center L) F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup (MulAut (L ⧸ center L)) := T₁.map (thetaH D.cfg.cent_le) with hS
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 8) (by rw [D.W.card_S]; norm_num)
  obtain ⟨P, hP⟩ := hSp.exists_le_sylow
  obtain ⟨t₂, F₂, W₂, E₂⟩ := hEng P P.isPGroup' P.not_dvd_index
  have hPS : S = P := Subgroup.eq_of_le_of_card_ge hP (by rw [W₂.card_S, D.W.card_S])
  have hW : SylowWitness (L ⧸ center L) (P : Subgroup _) tb F := hPS ▸ D.W
  have hF : F = F₂ := SylowWitness.F_unique hcZ hW W₂
  exact hF ▸ E₂

include D in
theorem exists_embedding :
    ∃ ρ : (L ⧸ center L) →* G, Function.Injective ρ ∧ ρ.range = L ∧ F.map ρ = liftSub F := by
  have hinj : Function.Injective (QuotientGroup.mk' (center L)) := fun a b h => D.mk_injective h
  let κe : L ≃* L ⧸ center L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let ρ : (L ⧸ center L) →* G := L.subtype.comp κe.symm.toMonoidHom
  have hρ : Function.Injective ρ := L.subtype_injective.comp κe.symm.injective
  have hrange : ρ.range = L := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact (κe.symm y).2
    · intro hg
      exact ⟨κe ⟨g, hg⟩, by simp [ρ]⟩
  have hF : F.map ρ = liftSub F := by
    have h2 : F.comap (QuotientGroup.mk' (center L)) = F.map κe.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm κe F
    rw [liftSub, h2, Subgroup.map_map]
  exact ⟨ρ, hρ, hrange, hF⟩

include D in
theorem fixedData (hfix : FixedData (⊤ : Subgroup (L ⧸ center L)) F) :
    FixedData L (liftSub F) := by
  obtain ⟨ρ, hρ, hrange, hF⟩ := D.exists_embedding
  have h1 := FixedData.map hρ hfix
  rwa [hrange, hF] at h1

include D in
theorem liftData (hlift : LiftData (⊤ : Subgroup (L ⧸ center L)) F) :
    LiftData L (liftSub F) := by
  obtain ⟨ρ, hρ, hrange, hF⟩ := D.exists_embedding
  have h1 := LiftData.map hρ hlift
  rwa [hrange, hF] at h1

end OutData

end CFSG.EvenSporadicStandard.M22Std
