module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCGoldB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem eq_of_selfNormalizing {T P : Subgroup G} (hT : IsPGroup 2 T) (hPT : P ≤ T)
    (h : ∀ n ∈ T, n ∈ Subgroup.normalizer (P : Set G) → n ∈ P) : P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hNC
  have h1 : Subgroup.normalizer ((P.subgroupOf T : Subgroup ↥T) : Set ↥T) = P.subgroupOf T := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      by_cases hg : g ∈ T
      · have h2 := (Subgroup.mem_normalizer_iff.mp hx) ⟨g, hg⟩
        simpa [Subgroup.mem_subgroupOf] using h2
      · constructor
        · intro hgP
          exact absurd (hPT hgP) hg
        · intro hP'
          exfalso
          apply hg
          have h3 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem x.2) (hPT hP')) x.2
          have e : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) = g := by group
          rwa [e] at h3
    exact Subgroup.mem_subgroupOf.mpr (h x x.2 hxN)
  have h2 := hNC _ h1
  exact le_antisymm hPT (Subgroup.subgroupOf_eq_top.mp h2)

end Normalizer

section Sylow


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem eq_sylow_of_matching (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ omegaNbr Ω K) (hJ₂ : J₂ ∈ omegaNbr Ω K)
    (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂) {P T : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer ({z} : Set G)) (hzP : z ∈ P) (hT2 : IsPGroup 2 T)
    (hPT : P ≤ T) (hCT : ∀ x ∈ T, x ∈ Subgroup.centralizer ({z} : Set G) → x ∈ P)
    (hmax : ∀ H : Subgroup G, IsPGroup 2 H → H ≤ Subgroup.centralizer ({z} : Set G) →
      Nat.card H ≤ Nat.card P) : P = T := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_of_selfNormalizing hT2 hPT fun n hnT hnN => ?_
  by_contra hnP
  have hzin : z ∈ invIn Ω P := ⟨hzP, K, hK, hz⟩
  have hyP : n * z * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hnN z).mp hzP
  have hy : n * z * n⁻¹ ∈ invIn Ω P := invIn_conj hΩ hzin hyP
  have hyz : n * z * n⁻¹ ≠ z := by
    intro h
    have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : n * z = z * n := by
        calc n * z = (n * z * n⁻¹) * n := by group
          _ = z * n := by rw [h]
      exact h1
    exact hnP (hCT n hnT hnC)
  set y := n * z * n⁻¹ with hydef
  have hz1 : z ≠ 1 := hz.ne_one
  have hy1 : y ≠ 1 := by
    intro h
    apply hz1
    have : n * z * n⁻¹ = 1 := h
    simpa using this
  have hw : z * y ∈ invIn Ω P :=
    mul_mem_invIn hs hnt hK hz hnoI hJ₁ hJ₂ hne hPC hzP hy hyz
  have hset : invIn Ω P = {z, y, z * y} := by
    ext x
    constructor
    · intro hx
      by_cases hxz : x = z
      · exact Or.inl hxz
      · rcases invIn_cases hs hnt hK hz hnoI hJ₁ hJ₂ hne hP2 hPC hzP hy hx hyz hxz with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl)
      · exact hzin
      · exact hy
      · exact hw
  have hzy : z ≠ y := fun h => hyz h.symm
  have hzw : z ≠ z * y := fun h => hy1 (by
    have : z * y = z * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this)
  have hyw : y ≠ z * y := fun h => hz1 (by
    have : 1 * y = z * y := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm)
  set N : Subgroup G := T ⊓ Subgroup.normalizer (P : Set G) with hNdef
  have hN2 : IsPGroup 2 N := hT2.to_le inf_le_left
  have hnN' : n ∈ N := ⟨hnT, hnN⟩
  have hPN : P ≤ N := fun x hx => ⟨hPT hx, Subgroup.le_normalizer hx⟩
  let _inst : MulAction N G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (r : N) (g : G), r • g = (r : G) * g * (r : G)⁻¹ := fun r g => rfl
  let S : SubMulAction N G :=
    { carrier := invIn Ω P
      smul_mem' := fun r x hx => by
        rw [hsmul]
        have hrN : (r : G) ∈ Subgroup.normalizer (P : Set G) := r.2.2
        exact invIn_conj hΩ hx ((Subgroup.mem_normalizer_iff.mp hrN x).mp hx.1) }
  have hcard : Nat.card S = 3 := by
    have h1 : Nat.card S = Set.ncard (invIn Ω P) := by
      show Nat.card ↥(invIn Ω P) = _
      exact Nat.card_coe_set_eq _
    rw [h1, hset]
    exact Set.ncard_eq_three.mpr ⟨z, y, z * y, hzy, hzw, hyw, rfl⟩
  obtain ⟨p, hp⟩ := hN2.nonempty_fixed_point_of_prime_not_dvd_card S (by rw [hcard]; decide)
  have hpfix : ∀ r : N, r • p = p := fun r => MulAction.mem_fixedPoints.mp hp r
  obtain ⟨x, hxS⟩ := p
  have hxfix : ∀ r : N, (r : G) * x * (r : G)⁻¹ = x := fun r => by
    have := congrArg Subtype.val (hpfix r)
    rw [SubMulAction.val_smul, hsmul] at this
    exact this
  have hxmem : x = z ∨ x = y ∨ x = z * y := by
    have hxin : x ∈ invIn Ω P := hxS
    rw [hset] at hxin
    simpa using hxin
  have hxw : x = z * y := by
    rcases hxmem with h | h | h
    · exfalso
      have h1 := hxfix ⟨n, hnN'⟩
      rw [h] at h1
      exact hyz h1
    · exfalso
      have h1 := hxfix ⟨n, hnN'⟩
      rw [h] at h1
      have h2 : y = z := by
        have h3 : n⁻¹ * (n * y * n⁻¹) * n = n⁻¹ * y * n := by rw [h1]
        have e1 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
        have e2 : n⁻¹ * y * n = z := by rw [hydef]; group
        rw [e1, e2] at h3
        exact h3
      exact hyz h2
    · exact h
  have hNw : ∀ r ∈ N, r * (z * y) * r⁻¹ = z * y := fun r hr => by
    have := hxfix ⟨r, hr⟩
    rw [hxw] at this
    exact this
  obtain ⟨-, M, hM, hwM⟩ := hw
  obtain ⟨g, hg⟩ : ∃ g : G, conjSub g K = M := by
    obtain ⟨g₁, hg₁⟩ := hs.trans M hM
    obtain ⟨g₂, hg₂⟩ := hs.trans K hK
    exact ⟨g₁ * g₂⁻¹, by rw [conjSub_mul, ← hg₂, conjSub_inv_conjSub, hg₁]⟩
  have hwg : z * y = g * z * g⁻¹ := by
    have h1 : IsUniqueInvolution M (g * z * g⁻¹) := by
      rw [← hg]
      exact hz.conj g
    exact hwM.eq h1
  have hN'2 : IsPGroup 2 (N.map (MulAut.conj g⁻¹).toMonoidHom) := hN2.map _
  have hN'C : N.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hNw r hr
    rw [hwg] at h1
    show (g⁻¹ * r * g⁻¹⁻¹) * z = z * (g⁻¹ * r * g⁻¹⁻¹)
    have h2 : (g⁻¹ * r * g⁻¹⁻¹) * z * (g⁻¹ * r * g⁻¹⁻¹)⁻¹ = z := by
      have e : (g⁻¹ * r * g⁻¹⁻¹) * z * (g⁻¹ * r * g⁻¹⁻¹)⁻¹ =
          g⁻¹ * (r * (g * z * g⁻¹) * r⁻¹) * g := by group
      rw [e, h1]
      group
    calc (g⁻¹ * r * g⁻¹⁻¹) * z = ((g⁻¹ * r * g⁻¹⁻¹) * z * (g⁻¹ * r * g⁻¹⁻¹)⁻¹) *
          (g⁻¹ * r * g⁻¹⁻¹) := by group
      _ = z * (g⁻¹ * r * g⁻¹⁻¹) := by rw [h2]
  have hcardN : Nat.card N = Nat.card (N.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  have hle : Nat.card N ≤ Nat.card P := by
    rw [hcardN]
    exact hmax _ hN'2 hN'C
  have hPeq : P = N := Subgroup.eq_of_le_of_card_ge hPN hle
  exact hnP (by rw [hPeq]; exact hnN')

end Sylow

end CFSG.ClassicalInvolution.Hat2A7S
