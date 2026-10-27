module

public import CFSG.Timmesfeld.ARS.BasicRankOne

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G]

section Sylow

variable [Finite G]

theorem exists_conj_of_sylow_le {N P Q : Subgroup G} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) (hPN : P ≤ N) (hQN : Q ≤ N) :
    ∃ n ∈ N, Q = conjSub P n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp₁ : IsPGroup 2 (P.subgroupOf N) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hp₂ : IsPGroup 2 (Q.subgroupOf N) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hi₁ : ¬ 2 ∣ (P.subgroupOf N).index := fun h => hPi (by
    rw [← Subgroup.relIndex_mul_index hPN]
    exact Dvd.dvd.mul_right h _)
  have hi₂ : ¬ 2 ∣ (Q.subgroupOf N).index := fun h => hQi (by
    rw [← Subgroup.relIndex_mul_index hQN]
    exact Dvd.dvd.mul_right h _)
  let S₁ : Sylow 2 ↥N := hp₁.toSylow hi₁
  let S₂ : Sylow 2 ↥N := hp₂.toSylow hi₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N S₁ S₂
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [mem_conjSub]
  by_cases hx : x ∈ N
  · have h1 : (⟨x, hx⟩ : ↥N) ∈ (S₂ : Subgroup ↥N) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥N) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥N) ∈ (S₂ : Subgroup ↥N) ↔ x ∈ Q := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥N) ↔ (g : G)⁻¹ * x * g ∈ P :=
      Subgroup.mem_subgroupOf (H := P) (K := N) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxQ : x ∉ Q := fun h => hx (hQN h)
    have hxP : (g : G)⁻¹ * x * g ∉ P := fun h => hx (by
      have := N.mul_mem (N.mul_mem g.2 (hPN h)) (N.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxQ, fun h => absurd h hxP⟩

end Sylow

theorem conjSub_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub H g = H := by
  ext x
  rw [mem_conjSub]
  exact (Subgroup.mem_normalizer_iff''.1 hg x).symm

theorem mem_normalizer_of_conjSub_eq {H : Subgroup G} {g : G} (h : conjSub H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  rw [← mem_conjSub, h]

theorem conjSub_le_conjSub {H K : Subgroup G} (h : H ≤ K) (g : G) : conjSub H g ≤ conjSub K g :=
  Subgroup.map_mono h

theorem sq_of_mem_conjSub {V : Subgroup G} (hV : ∀ x ∈ V, x * x = 1) (g : G) :
    ∀ x ∈ conjSub V g, x * x = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, hV x hx, map_one]

theorem commute_of_mem_conjSub {V : Subgroup G} (hV : ∀ x ∈ V, ∀ y ∈ V, Commute x y) (g : G) :
    ∀ x ∈ conjSub V g, ∀ y ∈ conjSub V g, Commute x y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hV x hx y hy).map (MulAut.conj g).toMonoidHom

theorem card_conjSub_eq (V : Subgroup G) (g : G) : Nat.card (conjSub V g) = Nat.card V :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_conjSub_inv_eq (H : Subgroup G) (g : G) : conjSub (conjSub H g) g⁻¹ = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

section Fusion

variable {J V V₂ : Subgroup G}

structure FusionData (J V V₂ : Subgroup G) : Prop where
  pgroup : IsPGroup 2 J
  odd_index : ¬ 2 ∣ J.index
  le : V ≤ J
  normalizes : J ≤ Subgroup.normalizer (V : Set G)
  normalizes₂ : J ≤ Subgroup.normalizer (V₂ : Set G)
  ne : V ≠ V₂
  abelian : ∀ x ∈ V, ∀ y ∈ V, Commute x y
  sq : ∀ x ∈ V, x * x = 1
  mem : ∀ A : Subgroup G, A ≤ J → (∀ x ∈ A, ∀ y ∈ A, Commute x y) → (∀ x ∈ A, x * x = 1) →
    Nat.card A = Nat.card V → A = V ∨ A = V₂

theorem FusionData.conjSub_mem (h : FusionData J V V₂) {b : G}
    (hb : b ∈ Subgroup.normalizer (J : Set G)) : conjSub V b = V ∨ conjSub V b = V₂ := by
  refine h.mem _ ?_ (commute_of_mem_conjSub h.abelian b) (sq_of_mem_conjSub h.sq b)
    (card_conjSub_eq V b)
  calc conjSub V b ≤ conjSub J b := conjSub_le_conjSub h.le b
    _ = J := conjSub_of_mem_normalizer hb

theorem FusionData.conjSub_ne [Finite G] (h : FusionData J V V₂) {b : G}
    (hb : b ∈ Subgroup.normalizer (J : Set G)) : conjSub V b ≠ V₂ := by
  intro hbV
  have hb2 : b * b ∈ Subgroup.normalizer (J : Set G) := Subgroup.mul_mem _ hb hb
  have hV2 : conjSub V (b * b) = V := by
    rcases h.conjSub_mem hb2 with h1 | h1
    · exact h1
    · exfalso
      rw [conjSub_mul, hbV] at h1
      exact h.ne (Subgroup.map_injective (MulAut.conj b).injective (hbV.trans h1.symm))
  have hbN : b * b ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_conjSub_eq hV2
  set N := Subgroup.normalizer (J : Set G) with hN
  set m := (J.subgroupOf N).index with hmdef
  have hm : b ^ m ∈ J := by
    have := Subgroup.pow_index_mem (J.subgroupOf N) (⟨b, hb⟩ : ↥N)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at this
    exact this
  have hodd : Odd m := by
    have hle : J ≤ N := Subgroup.le_normalizer
    have h1 : ¬ 2 ∣ m := fun h2 => h.odd_index (by
      rw [← Subgroup.relIndex_mul_index hle]
      exact Dvd.dvd.mul_right h2 _)
    exact Nat.odd_iff.2 (by omega)
  obtain ⟨k, hk⟩ := hodd
  have hbm : b ^ m ∈ Subgroup.normalizer (V : Set G) := h.normalizes hm
  have hbV' : b ∈ Subgroup.normalizer (V : Set G) := by
    have e : (b * b) ^ (k + 1) = b ^ m * b := by
      rw [← pow_two, ← pow_mul, ← pow_succ, hk]
      congr 1
    have h1 : b = (b ^ m)⁻¹ * (b * b) ^ (k + 1) := by rw [e]; group
    rw [h1]
    exact (Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).inv_mem hbm)
      ((Subgroup.normalizer (V : Set G)).pow_mem hbN (k + 1))
  exact h.ne ((conjSub_of_mem_normalizer hbV').symm.trans hbV)

theorem FusionData.not_conj [Finite G] (h : FusionData J V V₂) (g : G) : conjSub V g ≠ V₂ := by
  intro hg
  have hJg : conjSub J g ≤ Subgroup.normalizer (V₂ : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    apply mem_normalizer_of_conjSub_eq
    change conjSub V₂ (g * j * g⁻¹) = V₂
    rw [← hg, ← conjSub_mul, show g * j * g⁻¹ * g = g * j by group, conjSub_mul,
      conjSub_of_mem_normalizer (h.normalizes hj)]
  have hi : ¬ 2 ∣ (conjSub J g).index := by
    rw [Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
    exact h.odd_index
  obtain ⟨n, hn, hn'⟩ := exists_conj_of_sylow_le h.pgroup h.odd_index (h.pgroup.map _) hi
    h.normalizes₂ hJg
  have hn'' : conjSub J g = conjSub J n := hn'
  have hb : n⁻¹ * g ∈ Subgroup.normalizer (J : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, hn'', conjSub_conjSub_inv_eq]
  have hV : conjSub V (n⁻¹ * g) = V₂ := by
    rw [conjSub_mul, hg]
    exact conjSub_of_mem_normalizer ((Subgroup.normalizer (V₂ : Set G)).inv_mem hn)
  exact h.conjSub_ne hb hV

theorem FusionData.weaklyClosed [Finite G] (h : FusionData J V V₂) {g : G} (hg : conjSub V g ≤ J) :
    conjSub V g = V := by
  rcases h.mem _ hg (commute_of_mem_conjSub h.abelian g) (sq_of_mem_conjSub h.sq g)
    (card_conjSub_eq V g) with h1 | h1
  · exact h1
  · exact absurd h1 (h.not_conj g)

end Fusion

end CFSG.CGT.PushingUpLit.A78
