module

public import CFSG.LieType.SeitzGeneration.ExcTorusEmbed
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open scoped Pointwise


theorem sylowTorus_of_twisted_torus {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (Φ : ModGL τ L →* ModGL τ L)
    (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) {p : ℕ}
    (hp : p.Prime) {N m : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range)
    (hcomm : IsMulCommutative (twistedTorusOf n Φ))
    (hcard : Nat.card (twistedTorusOf n Φ) = N)
    (htors : Nat.card (torsionSubgroup (twistedTorusOf n Φ) hcomm p) = p ^ m)
    (hord : p ^ (Nat.card C).factorization p = p ^ N.factorization p) :
    SylowTorus C p m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hT0fin : Finite (twistedTorusOf n Φ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  let cg : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  set X : Subgroup (ModGL τ L) := (twistedTorusOf n Φ).map cg with hX
  have hXfin : Finite X :=
    Finite.of_surjective (cg.subgroupMap (twistedTorusOf n Φ))
      (cg.subgroupMap_surjective (twistedTorusOf n Φ))
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hXcomm : IsMulCommutative X := isMulCommutative_map cg hcomm
  have hpg := hrat X hXC hXF
  set V : Subgroup (ModGL τ L) := torsionSubgroup X hXcomm p with hV
  have hVX : V ≤ X := fun x hx => hx.1
  have hVp : IsPGroup p V := fun x => ⟨1, by
    have : (x : ModGL τ L) ^ p = 1 := x.2.2
    apply Subtype.ext
    simpa using this⟩
  have hVrange : V ≤ ι.range := hpg V hVX hVp
  have hVcard : Nat.card V = p ^ m := by
    have hVmap : V = (torsionSubgroup (twistedTorusOf n Φ) hcomm p).map cg := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxp⟩
        refine ⟨y, ⟨hy, hcg ?_⟩, rfl⟩
        rw [map_pow, hxp, map_one]
      · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rw [← map_pow, hyp, map_one]
    rw [hVmap, Subgroup.card_map_of_injective hcg, htors]
  set T : Subgroup (ModGL τ L) := X ⊓ ι.range with hT
  have hTcomm : IsMulCommutative T := by
    refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    have := hXcomm
    exact setLike_mul_comm a.2.1 b.2.1
  have hSylow : ∃ S : Sylow p C, ι '' (S : Set C) ⊆ X := by
    obtain ⟨P0⟩ : Nonempty (Sylow p (twistedTorusOf n Φ)) := inferInstance
    set P1 : Subgroup (ModGL τ L) :=
      ((P0 : Subgroup (twistedTorusOf n Φ)).map (twistedTorusOf n Φ).subtype).map cg with hP1
    have hP1X : P1 ≤ X := Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hP1p : IsPGroup p P1 := (P0.isPGroup'.map _).map cg
    have hP1range : P1 ≤ ι.range := hpg P1 hP1X hP1p
    set P : Subgroup C := P1.comap ι with hP
    have hPmap : P.map ι = P1 := by
      rw [hP, Subgroup.map_comap_eq, inf_eq_right.2 hP1range]
    have hPcard : Nat.card P = p ^ (Nat.card C).factorization p := by
      have h1 : Nat.card P = Nat.card P1 := by
        rw [← hPmap, Subgroup.card_map_of_injective hι]
      have h2 : Nat.card P1 = Nat.card (P0 : Subgroup (twistedTorusOf n Φ)) := by
        rw [hP1, Subgroup.card_map_of_injective hcg,
          Subgroup.card_map_of_injective (twistedTorusOf n Φ).subtype_injective]
      rw [h1, h2, Sylow.card_eq_multiplicity P0, hcard, hord]
    refine ⟨Sylow.ofCard P hPcard, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((Sylow.ofCard P hPcard : Sylow p C) : Subgroup C) := hy
    rw [Sylow.coe_ofCard] at hy'
    exact hP1X hy'
  obtain ⟨S, hSX⟩ := hSylow
  have hconj : ∀ Q : Subgroup C, IsPGroup p Q →
      ∃ c : C, (Q.map (MulAut.conj c).toMonoidHom).map ι ≤ T := by
    intro Q hQ
    obtain ⟨S', hS'⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C S' S
    refine ⟨g, ?_⟩
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have h1 := Subgroup.smul_mem_pointwise_smul q (MulAut.conj g) (S' : Subgroup _) (hS' hq)
    have h2 : (MulAut.conj g • (S' : Subgroup C)) = ((g • S' : Sylow p C) : Subgroup C) := rfl
    rw [h2, hg] at h1
    exact ⟨hSX ⟨_, h1, rfl⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩
  exact SylowTorus.of_embedding ι hι hTcomm inf_le_right hconj
    (fun x => by
      constructor
      · intro hx
        exact ⟨⟨hVX hx, hVrange hx⟩, hx.2⟩
      · rintro ⟨⟨hxX, -⟩, hxp⟩
        exact ⟨hxX, hxp⟩) hVcard

end CFSG.LieType.SeitzGeneration
