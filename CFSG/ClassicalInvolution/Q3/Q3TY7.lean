module

public import CFSG.ClassicalInvolution.RouteD.GapsPerfect
public import CFSG.ClassicalInvolution.Q3.Q3TNGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open scoped MatrixGroups

theorem card_sylow_three_le_four {B : Type*} [Group B] [Finite B] (hB : Nat.card B = 24) :
    Nat.card (Sylow 3 B) ≤ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 B))
  have h1 := card_sylow_modEq_one 3 B
  have h2 := P.card_dvd_index
  have hP : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hB]
    norm_num [Nat.factorization]
  have hidx : P.index = 8 := by
    have := Subgroup.index_mul_card (P : Subgroup B)
    rw [hB] at this
    have h3 : Nat.card (P : Subgroup B) = 3 := hP
    rw [h3] at this
    omega
  rw [hidx] at h2
  have hle : Nat.card (Sylow 3 B) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  generalize Nat.card (Sylow 3 B) = n at *
  interval_cases n <;> simp_all [Nat.ModEq]


theorem perfect_le_centralizer_of_zpowers {H : Type*} [Group H] (S : Subgroup H) (x : H)
    (hS : ⁅S, S⁆ = S) (hN : S ≤ Subgroup.normalizer (Subgroup.zpowers x : Set H)) :
    S ≤ Subgroup.centralizer ({x} : Set H) := by
  have hmem : ∀ g ∈ S, ∃ a : ℤ, g * x * g⁻¹ = x ^ a := fun g hg => by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp (hN hg) x).mp (Subgroup.mem_zpowers x))
    exact ⟨a, ha.symm⟩
  have hc := RouteD.Gaps.perfect_le_centralizer_of_commuting_conj S (Subgroup.zpowers x) hS hN
    (fun s hs s' hs' p hp => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      obtain ⟨a, ha⟩ := hmem s hs
      obtain ⟨b, hb⟩ := hmem s' hs'
      have c1 : ∀ (g : H) (n : ℤ), g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n := fun g n =>
        (conj_zpow).symm
      have e1 : s * (s' * x ^ k * s'⁻¹) * s⁻¹ = x ^ (a * (b * k)) := by
        rw [c1 s' k, hb, ← zpow_mul, c1 s (b * k), ha, ← zpow_mul]
      have e2 : s' * (s * x ^ k * s⁻¹) * s'⁻¹ = x ^ (b * (a * k)) := by
        rw [c1 s k, ha, ← zpow_mul, c1 s' (a * k), hb, ← zpow_mul]
      rw [e1, e2]
      congr 1
      ring)
  exact hc.trans (Subgroup.centralizer_le (by simp))


theorem perfect_le_centralizer_of_normalizes_sl2 {G : Type*} [Group G] {β S : Subgroup G}
    (e : β ≃* SL(2, ZMod 3)) (hSp : ⁅S, S⁆ = S) (hSN : S ≤ Subgroup.normalizer (β : Set G)) :
    S ≤ Subgroup.centralizer (β : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfinβ : Finite β := Finite.of_equiv _ e.symm.toEquiv
  have hβ24 : Nat.card β = 24 := (Nat.card_congr e.toEquiv).trans natCard_sl2Three
  have hfac : 3 ^ (Nat.card β).factorization 3 = 3 := by
    rw [hβ24]
    norm_num [Nat.factorization]
  set 𝓕 : Set (Subgroup G) := {P | P ≤ β ∧ Nat.card P = 3} with h𝓕
  have hcardP : ∀ P ∈ 𝓕, Nat.card (P.subgroupOf β) = 3 ^ (Nat.card β).factorization 3 := by
    intro P hP
    rw [hfac]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv).trans hP.2
  let φ : 𝓕 → Sylow 3 β := fun P => Sylow.ofCard (P.1.subgroupOf β) (hcardP P.1 P.2)
  have hφ : Function.Injective φ := by
    intro P Q h
    have h1 : P.1.subgroupOf β = Q.1.subgroupOf β :=
      congrArg (fun R : Sylow 3 β => (R : Subgroup β)) h
    apply Subtype.ext
    have h2 := (Subgroup.subgroupOf_inj).mp h1
    rwa [inf_eq_left.mpr P.2.1, inf_eq_left.mpr Q.2.1] at h2
  have : Finite 𝓕 := Finite.of_injective φ hφ
  have hfin : 𝓕.Finite := Set.toFinite _
  have hcard : 𝓕.ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_le_card_of_injective φ hφ).trans (card_sylow_three_le_four hβ24)
  have hstable : ∀ g ∈ S, ∀ A ∈ 𝓕, A.map (MulAut.conj g).toMonoidHom ∈ 𝓕 := by
    intro g hg A hA
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hSN hg) y).mp (hA.1 hy)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA.2
  have hS3 : ∀ x : G, x ∈ β → x ^ 3 = 1 → S ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hxβ hx3
    have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hSp
    by_cases hx1 : x = 1
    · rw [hx1]
      intro s _
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]; simp
    · have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
      have hP : Subgroup.zpowers x ∈ 𝓕 :=
        ⟨(Subgroup.zpowers_le).mpr hxβ, by rw [Nat.card_zpowers, hord]⟩
      exact perfect_le_centralizer_of_zpowers S x hSp
        (RouteD.Gaps.perfect_le_normalizer_of_card_le_four S 𝓕 hfin hcard hstable hP)
  have hclos : Subgroup.closure {y : β | y ^ 3 = 1} = ⊤ := by
    have h1 := Q3T.sl2_closure_three_eq_top
    have h2 : Subgroup.map e.symm.toMonoidHom (Subgroup.closure {y : SL(2, ZMod 3) | y ^ 3 = 1}) =
        Subgroup.closure {y : β | y ^ 3 = 1} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        show (e.symm y') ^ 3 = 1
        rw [← map_pow, show y' ^ 3 = 1 from hy', map_one]
      · intro hy
        refine ⟨e y, ?_, by simp⟩
        show (e y) ^ 3 = 1
        rw [← map_pow, show y ^ 3 = 1 from hy, map_one]
    rw [← h2, h1, Subgroup.map_top_of_surjective _ e.symm.surjective]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have key : ∀ y : β, Commute (y : G) s ∧ True := by
    intro y
    have hy : y ∈ Subgroup.closure {y : β | y ^ 3 = 1} := by rw [hclos]; trivial
    refine ⟨?_, trivial⟩
    refine Subgroup.closure_induction (p := fun (y : β) _ => Commute (y : G) s) ?_ ?_ ?_ ?_ hy
    · intro y hy
      have := hS3 (y : G) y.2 (by simpa using congrArg Subtype.val hy)
      exact Subgroup.mem_centralizer_iff.mp (this hs) (y : G) (Set.mem_singleton _)
    · exact Commute.one_left s
    · intro y z _ _ hy hz
      exact hy.mul_left hz
    · intro y _ hy
      exact hy.inv_left
  exact (key ⟨b, hb⟩).1.eq

end CFSG.ClassicalInvolution.Q3.Q3TY
