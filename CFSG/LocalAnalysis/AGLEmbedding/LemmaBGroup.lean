module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_of_sup_eq_of_central {Y C Z : Subgroup G} (hCY : C ≤ Y) (hYZ : ⁅Y, Y⁆ = Z)
    (hZc : Z ≤ Subgroup.centralizer (Y : Set G)) (h : C ⊔ Z = Y) : Y ≤ C := by
  have hcomm : ∀ z ∈ Z, ∀ y ∈ Y, Commute z y := fun z hz y hy =>
    (Subgroup.mem_centralizer_iff.mp (hZc hz) y hy).symm
  have hCN : C ≤ Subgroup.normalizer (Z : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      hcomm z hz c (hCY hc))
  have hmul : ∀ y ∈ Y, ∃ c ∈ C, ∃ z ∈ Z, c * z = y := by
    intro y hy
    rw [← h, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right C Z hCN] at hy
    obtain ⟨c, hc, z, hz, rfl⟩ := hy
    exact ⟨c, hc, z, hz, rfl⟩
  have hYC : ⁅Y, Y⁆ ≤ C := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := hmul g₁ hg₁
    obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := hmul g₂ hg₂
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr (hcomm z₁ hz₁ _ hg₂), mul_one, mul_inv_cancel,
      one_mul, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hcomm z₂ hz₂ _ (hCY hc₁)).symm, mul_one,
      mul_inv_cancel_right, commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
  rw [← h]
  exact sup_le le_rfl (hYZ ▸ hYC)

theorem relIndex_le_of_cyclic_mod_central {Y Z : Subgroup G} {p : ℕ} (hp : 0 < p) {u : G}
    (hu : u ∈ Y) (hZc : Z ≤ Subgroup.centralizer (Y : Set G)) (hup : u ^ p ∈ Z)
    (hcov : ∀ x ∈ Y, ∃ k : ℕ, x * (u ^ k)⁻¹ ∈ Z) : Z.relIndex Y ≤ p := by
  let u' : Y := ⟨u, hu⟩
  let f : Fin p → (↥Y ⧸ Z.subgroupOf Y) := fun i => ((u' ^ (i : ℕ) : Y) : ↥Y ⧸ Z.subgroupOf Y)
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hcov x x.2
      refine ⟨⟨k % p, Nat.mod_lt _ hp⟩, ?_⟩
      show ((u' ^ (k % p) : Y) : ↥Y ⧸ Z.subgroupOf Y) = (x : ↥Y ⧸ Z.subgroupOf Y)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hx : (x : G) = (x : G) * (u ^ k)⁻¹ * u ^ k := by group
      have hk' : u ^ k = u ^ (k % p) * (u ^ p) ^ (k / p) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      have hzc : (u ^ (k % p))⁻¹ * ((x : G) * (u ^ k)⁻¹) =
          ((x : G) * (u ^ k)⁻¹) * (u ^ (k % p))⁻¹ :=
        Subgroup.mem_centralizer_iff.mp (hZc hk) _ (Y.inv_mem (Y.pow_mem hu _))
      have key : (u ^ (k % p))⁻¹ * (x : G) = ((x : G) * (u ^ k)⁻¹) * (u ^ p) ^ (k / p) := by
        calc (u ^ (k % p))⁻¹ * (x : G) = (u ^ (k % p))⁻¹ * ((x : G) * (u ^ k)⁻¹ * u ^ k) := by
              rw [← hx]
          _ = ((u ^ (k % p))⁻¹ * ((x : G) * (u ^ k)⁻¹)) * u ^ k := by group
          _ = ((x : G) * (u ^ k)⁻¹) * ((u ^ (k % p))⁻¹ * u ^ k) := by rw [hzc]; group
          _ = ((x : G) * (u ^ k)⁻¹) * (u ^ p) ^ (k / p) := by
              rw [hk', ← mul_assoc (u ^ (k % p))⁻¹, inv_mul_cancel, one_mul]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
      rw [key]
      exact Z.mul_mem hk (Z.pow_mem hup _)
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

private def trivOnAbelianization (Y : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (Y : Set G) ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ ⁅Y, Y⁆}
  one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun y hy => ?_⟩
    have hgZ : g ∈ Subgroup.normalizer ((⁅Y, Y⁆ : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (by rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN])
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hgZ _).mp (hh y hy)) (hg y hy)
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨Subgroup.inv_mem _ hgN, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) y).mp hy
    have h1 := hg _ hy'
    have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ = (g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact Subgroup.inv_mem _ h1

theorem conj_mem_of_coprime {Y : Subgroup G} {t : G} (htY : t ∈ Subgroup.normalizer (Y : Set G))
    {n r : ℕ} (hnr : Nat.Coprime n r)
    (hn : ∀ y ∈ Y, t ^ n * y * (t ^ n)⁻¹ * y⁻¹ ∈ ⁅Y, Y⁆)
    (hr : ∀ y ∈ Y, t ^ r * y * (t ^ r)⁻¹ * y⁻¹ ∈ ⁅Y, Y⁆) :
    ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ ⁅Y, Y⁆ := by
  have h1 : t ^ n ∈ trivOnAbelianization Y := ⟨Subgroup.pow_mem _ htY n, hn⟩
  have h2 : t ^ r ∈ trivOnAbelianization Y := ⟨Subgroup.pow_mem _ htY r, hr⟩
  have hg : ((Nat.gcd n r : ℕ) : ℤ) = n * Nat.gcdA n r + r * Nat.gcdB n r := Nat.gcd_eq_gcd_ab n r
  rw [hnr.gcd_eq_one, Nat.cast_one] at hg
  have ht : t = (t ^ n) ^ (Nat.gcdA n r) * (t ^ r) ^ (Nat.gcdB n r) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  have h3 : t ∈ trivOnAbelianization Y := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h1 _) (Subgroup.zpow_mem _ h2 _)
  exact h3.2

theorem isCyclic_of_le_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] {p : ℕ}
    [Fact p.Prime] (φ : G₁ →* G₂) {B : Subgroup G₁}
    (hB : ∀ A : Subgroup G₁, A ≤ B → IsPGroup p A → IsCyclic A)
    {A : Subgroup G₂} (hAB : A ≤ B.map φ) (hA : IsPGroup p A) : IsCyclic A := by
  set A₁ := A.comap φ ⊓ B with hA₁
  let ψ : ↥A₁ →* ↥A := (φ.comp A₁.subtype).codRestrict A (fun x => x.2.1)
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb, rfl⟩ := hAB ha
    exact ⟨⟨b, ha, hb⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥A₁) := inferInstance
  have : Finite ↥A := Finite.of_surjective ψ hψ
  have hmap : (P : Subgroup ↥A₁).map ψ = ⊤ := by
    obtain ⟨k, hk⟩ := hA.index ((P : Subgroup ↥A₁).map ψ)
    have hdvd := Subgroup.index_map_dvd (P : Subgroup ↥A₁) hψ
    have hnd := P.not_dvd_index
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.index_eq_one.mp hk
    · exact absurd ((hk ▸ dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd) hnd
  have hPc : IsCyclic (P : Subgroup ↥A₁) := by
    have hc : IsCyclic ((P : Subgroup ↥A₁).map A₁.subtype) :=
      hB _ ((Subgroup.map_subtype_le _).trans inf_le_right) (P.isPGroup'.map _)
    exact isCyclic_of_injective
      ((Subgroup.equivMapOfInjective _ _ A₁.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ A₁.subtype_injective).injective
  have hsurj : Function.Surjective (ψ.comp (P : Subgroup ↥A₁).subtype) := by
    intro a
    have ha : a ∈ (P : Subgroup ↥A₁).map ψ := hmap ▸ Subgroup.mem_top a
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective _ hsurj

end CFSG.AGLEmbedding
