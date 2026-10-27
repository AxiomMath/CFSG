module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Rho2

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
  {W X : Type} [Group W] [Group X] [Finite W] (D : AutModelData L W X)

theorem exists_outer_involution
    (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1) (htL : t ∉ L)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    (hW : Nat.card W = 2 * Nat.card X)
    (hu : ∃ u : W, u ∉ D.ι.range ∧ u * u = 1)
    (S : Subgroup G) (hSC : S ≤ centralizer ({t} : Set G)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)))
    (z : G) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzc : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z)
    (n : G) (hn : n ∈ normalizer (S : Set G)) (hnt : n * t * n⁻¹ = z * t)
    (hcount : ∀ Sw : Subgroup W, IsPGroup 2 Sw → ¬ 2 ∣ Sw.index → ∀ zw : W, zw ∈ D.ι.range →
      orderOf zw = 2 → centralizer ((Sw ⊓ D.ι.range : Subgroup W) : Set W) ⊓ D.ι.range =
        zpowers zw →
      Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = 1} ≠
        Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = zw}) :
    ∃ v ∈ centralizer ({t} : Set G), v ∉ L ⊔ zpowers t ∧ v * v = 1 := by
  classical
  by_contra hno
  push Not at hno
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  set N' : Subgroup G := L ⊔ zpowers t with hN'def
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hLC : L ≤ C := le_centralizer_of_mem_centralizer hL
  have hcomm : ∀ β ∈ L, Commute β t := fun β hβ => mem_centralizer_iff.1 hL β hβ
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  have hzt : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  set ρ : C →* W := D.rhoC hC with hρdef
  have hρker : ∀ x : C, ρ x = 1 ↔ (x : G) ∈ zpowers t := rhoC_eq_one_iff D hC hker
  have hρmem : ∀ x : C, ρ x ∈ D.ι.range ↔ (x : G) ∈ N' := rhoC_mem_range_iff D hC hL hker
  have hρL : ∀ l : L, ρ ⟨l, hLC l.2⟩ = D.ι (D.θ l) := rhoC_of_mem D hC hL
  have hzp : ∀ a : G, a ∈ zpowers t → a = 1 ∨ a = t := by
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    exact zpow_eq_one_or_self ht2 j
  obtain ⟨y₀, hy₀C, hy₀N⟩ : ∃ y ∈ C, y ∉ N' := by
    by_contra h
    push Not at h
    have h1 : N'.relIndex C = 1 := Subgroup.relIndex_eq_one.2 fun x hx => h x hx
    omega
  have hsurj : Function.Surjective ρ := rhoC_surjective D hL hC hker hidx hW
  have hN'sq : ∀ x ∈ N', ∃ l ∈ L, x * x = l := fun x hx => sq_mem_of_mem_sup hL ht2 hx
  obtain ⟨u, huR, hu2⟩ := hu
  obtain ⟨x₀c, hx₀⟩ := hsurj u
  have hx₀N : (x₀c : G) ∉ N' := fun h => huR (hx₀ ▸ (hρmem x₀c).2 h)
  have hx₀sq : (x₀c : G) * x₀c = t := by
    have h1 : ρ (x₀c * x₀c) = 1 := by rw [map_mul, hx₀, hu2]
    rcases hzp _ ((hρker _).1 h1) with h | h
    · exact absurd h (hno _ x₀c.2 hx₀N)
    · exact h
  have hsq : ∀ x ∈ C, x ∉ N' → ∃ l ∈ L, x * x = l * t := fun x hx hxN =>
    sq_mem_of_outer hL ht2 hC hidx x₀c.2 hx₀N hx₀sq hx hxN
  have htS : t ∈ S := mem_of_central_involution hSC hS2 hSidx htC ht2 ht1 fun c hc =>
    mem_centralizer_singleton_iff.1 hc
  set σ : S →* W := ρ.comp (Subgroup.inclusion hSC) with hσdef
  have hσ : ∀ x : S, σ x = ρ ⟨x, hSC x.2⟩ := fun x => rfl
  have hσker : ∀ x : S, σ x = 1 ↔ (x : G) ∈ zpowers t := fun x => by
    rw [hσ]
    exact hρker ⟨x, hSC x.2⟩
  have hσmem : ∀ x : S, σ x ∈ D.ι.range ↔ (x : G) ∈ N' := fun x => by
    rw [hσ]
    exact hρmem ⟨x, hSC x.2⟩
  set zw : W := D.ι (D.θ ⟨z, hzL⟩) with hzw
  have hzρ : ρ ⟨z, hLC hzL⟩ = zw := hρL ⟨z, hzL⟩
  have hA : ∀ x : S, ((x : G) * x = t) ↔ (σ x ∉ D.ι.range ∧ σ x * σ x = 1) := by
    intro x
    constructor
    · intro hx
      have hxN : (x : G) ∉ N' := by
        intro h
        obtain ⟨l, hl, hl'⟩ := hN'sq x h
        exact htL (hx ▸ hl' ▸ hl)
      refine ⟨fun h => hxN ((hσmem x).1 h), ?_⟩
      rw [← map_mul]
      exact (hσker _).2 (by rw [show ((x * x : S) : G) = t from hx]; exact mem_zpowers t)
    · rintro ⟨hxr, hx1⟩
      have hxN : (x : G) ∉ N' := fun h => hxr ((hσmem x).2 h)
      rw [← map_mul] at hx1
      rcases hzp _ ((hσker _).1 hx1) with h | h
      · exact absurd h (hno _ (hSC x.2) hxN)
      · exact h
  have hB : ∀ x : S, ((x : G) * x = z * t) ↔ (σ x ∉ D.ι.range ∧ σ x * σ x = zw) := by
    intro x
    constructor
    · intro hx
      have hxN : (x : G) ∉ N' := by
        intro h
        obtain ⟨l, hl, hl'⟩ := hN'sq x h
        apply htL
        have : t = z⁻¹ * l := by rw [← hl', hx]; group
        rw [this]
        exact L.mul_mem (L.inv_mem hzL) hl
      refine ⟨fun h => hxN ((hσmem x).1 h), ?_⟩
      rw [← map_mul]
      have : σ (x * x) = ρ (⟨z, hLC hzL⟩ * ⟨t, htC⟩) := by
        rw [hσ]
        exact congrArg ρ (Subtype.ext hx)
      rw [this, map_mul, hzρ, (hρker ⟨t, htC⟩).2 (mem_zpowers t), mul_one]
    · rintro ⟨hxr, hx1⟩
      have hxN : (x : G) ∉ N' := fun h => hxr ((hσmem x).2 h)
      have h1 : ρ (⟨x, hSC x.2⟩ * ⟨x, hSC x.2⟩ * ⟨z, hLC hzL⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hzρ, ← hσ x, hx1, mul_inv_cancel]
      have h2 : (x : G) * x * z⁻¹ ∈ zpowers t := (hρker _).1 h1
      rcases hzp _ h2 with h | h
      · exfalso
        obtain ⟨l, hl, hl'⟩ := hsq x (hSC x.2) hxN
        apply htL
        have hz : x * x = z := by
          calc (x : G) * x = (x * x * z⁻¹) * z := by group
            _ = z := by rw [h, one_mul]
        have : t = l⁻¹ * z := by
          rw [← hz, hl']
          group
        rw [this]
        exact L.mul_mem (L.inv_mem hl) hzL
      · calc (x : G) * x = (x * x * z⁻¹) * z := by group
          _ = t * z := by rw [h]
          _ = z * t := ((hcomm z hzL).eq).symm
  set Sw : Subgroup W := σ.range with hSw
  have hker_eq : σ.ker = (zpowers t).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, hσker, mem_subgroupOf]
  have hzS' : zpowers t ≤ S := zpowers_le.2 htS
  have hker_card : Nat.card σ.ker = 2 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzS').toEquiv, hzt]
  have hcnt : ∀ (a : G) (q : W → Prop), (∀ x : S, ((x : G) * x = a) ↔ q (σ x)) →
      Nat.card {x : S // (x : G) * x = a} = 2 * Nat.card {y : Sw // q y.1} := by
    intro a q hq
    have h := card_subtype_comp σ q
    rw [hker_card] at h
    rw [← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight hq)
  have hc1 : Nat.card {x : S // (x : G) * x = t} =
      2 * Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = 1} :=
    hcnt t (fun y => y ∉ D.ι.range ∧ y * y = 1) hA
  have hc2 : Nat.card {x : S // (x : G) * x = z * t} =
      2 * Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = zw} :=
    hcnt (z * t) (fun y => y ∉ D.ι.range ∧ y * y = zw) hB
  have hconj := card_sq_eq_conj S hn t
  rw [hnt] at hconj
  have hBeq : Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = 1} =
      Nat.card {y : Sw // y.1 ∉ D.ι.range ∧ y.1 * y.1 = zw} := by omega
  obtain ⟨-, hSwp, hSwidx⟩ := sylow_range_rhoC D hL ht2 htL hC hker hidx hW S hSC hS2 hSidx
  have hzwR : zw ∈ D.ι.range := ⟨_, rfl⟩
  have hΦinj : Function.Injective (D.ι.comp D.θ.toMonoidHom) :=
    D.ι_injective.comp D.θ.injective
  have hzw2 : orderOf zw = 2 := by
    have h := orderOf_injective _ hΦinj ⟨z, hzL⟩
    rw [show zw = (D.ι.comp D.θ.toMonoidHom) ⟨z, hzL⟩ from rfl, h, Subgroup.orderOf_mk, hz2]
  have hcent : centralizer ((Sw ⊓ D.ι.range : Subgroup W) : Set W) ⊓ D.ι.range = zpowers zw :=
    centralizer_range_rhoS D hL hC hker S hSC htS z hzL hzc
  exact hcount Sw hSwp hSwidx zw hzwR hzw2 hcent hBeq

end CFSG.EvenSporadicStandard.HSStd
