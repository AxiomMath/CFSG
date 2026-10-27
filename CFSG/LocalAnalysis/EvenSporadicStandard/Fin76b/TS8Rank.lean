module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def ORankStatement {G : Type*} [Group G] (z : G) : Prop :=
  ∀ {u : G}, (∃ g : G, u = g * z * g⁻¹) → ∀ {A : Subgroup G}, A ≤ centralizer ({u} : Set G) →
    (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 32

theorem card_le_two_of_le_cent {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hC : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card ↥S = 2) {P : Subgroup G}
    (hP : P ≤ centralizer (L : Set G)) (hP2 : ∀ x ∈ P, x * x = 1) : Nat.card ↥P ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer (L : Set G))) :=
    ea16_isPGroup_two (fun a ha => Subtype.ext (hP2 _ (mem_subgroupOf.1 ha)))
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP'
  have hcard1 : Nat.card ↥(P.subgroupOf (centralizer (L : Set G))) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have hle : Nat.card ↥(P.subgroupOf (centralizer (L : Set G))) ≤ Nat.card ↥Q :=
    Subgroup.card_le_of_le hQ
  rw [hC Q] at hle
  rw [← hcard1]
  exact hle

theorem orank {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T : Subgroup G}
    (hcfg : OuterConfig G L z t T) (hC : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card ↥S = 2)
    (hEA : ElAb16 (MulAut ↥L)) : ORankStatement z := by
  intro u hu A hA hA2
  obtain ⟨g, rfl⟩ := hu
  have hconj : ∀ x : G, (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := fun x => by
    simp [MulAut.conj_apply]
  have hA'sq : ∀ a ∈ A.map (MulAut.conj g⁻¹).toMonoidHom, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hA2 x hx]; group
  have hA'C : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hcx := mem_centralizer_singleton_iff.1 (hA hx)
    rw [hconj, mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hcx]
      _ = z * (g⁻¹ * x * g) := by group
  have hA'N : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (L : Set G) :=
    (hA'C).trans hcfg.cent_le
  have hcardA' : Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  let A'' : Subgroup ↥(normalizer (L : Set G)) :=
    (A.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (normalizer (L : Set G))
  let ψ : A'' →* MulAut ↥L := (normalizerMonoidHom L).comp A''.subtype
  have hcardA'' : Nat.card ↥A'' = Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'N).toEquiv
  have hxx : ∀ x : A'', x * x = 1 := fun x =>
    Subtype.ext (Subtype.ext (hA'sq _ (mem_subgroupOf.1 x.2)))
  have hrange : Nat.card ↥ψ.range ≤ 16 := by
    apply hEA ψ.range
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, hxx x, map_one]
  have hkerC : ∀ x : A'', ψ x = 1 → (x.1 : G) ∈ centralizer (L : Set G) := by
    intro x hx
    have hx' : x.1 ∈ (normalizerMonoidHom L).ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    rw [normalizerMonoidHom_ker] at hx'
    exact mem_subgroupOf.1 hx'
  have hfinj : Function.Injective ((normalizer (L : Set G)).subtype.comp A''.subtype) :=
    fun x y hxy => Subtype.ext (Subtype.ext hxy)
  have hK₀card : Nat.card ↥(ψ.ker.map ((normalizer (L : Set G)).subtype.comp A''.subtype)) =
      Nat.card ↥ψ.ker := Subgroup.card_map_of_injective hfinj
  have hK₀C : ψ.ker.map ((normalizer (L : Set G)).subtype.comp A''.subtype) ≤
      centralizer (L : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hkerC x (MonoidHom.mem_ker.1 hx)
  have hK₀sq : ∀ y ∈ ψ.ker.map ((normalizer (L : Set G)).subtype.comp A''.subtype),
      y * y = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact hA'sq _ (mem_subgroupOf.1 x.2)
  have hkerle : Nat.card ↥ψ.ker ≤ 2 := by
    rw [← hK₀card]
    exact card_le_two_of_le_cent hC hK₀C hK₀sq
  have hsplit : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥A'' :=
    Subgroup.card_ker_mul_card_range ψ
  calc Nat.card ↥A = Nat.card ↥(A.map (MulAut.conj g⁻¹).toMonoidHom) := hcardA'.symm
    _ = Nat.card ↥A'' := hcardA''.symm
    _ = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := hsplit.symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hkerle hrange
    _ = 32 := by norm_num

end CFSG.EvenSporadicStandard.Fin76b
