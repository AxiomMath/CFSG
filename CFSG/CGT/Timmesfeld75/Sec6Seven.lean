module

public import CFSG.CGT.Timmesfeld75.Sec6Five
public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem card_fixed_eq_card_centralizer {H : Subgroup G} [(T.subgroupOf H).Normal]
    (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 m))
    (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m))
    (hcompat : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
        Multiplicative.ofAdd (((e (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t))))
    {x : G} (hxH : x ∈ H) (hxN : x ∈ Subgroup.normalizer (T : Set G)) :
    Nat.card {w : Fin n → GaloisField 2 m //
        ((e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ w = w} =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hnorm : ∀ t : ↥T, x * (t : G) * x⁻¹ ∈ T := fun t => conj_mem_of_mem_normalizer hxN t.2
  have key : ∀ t : ↥T, (x * (t : G) * x⁻¹ = t) ↔
      ((e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ Multiplicative.toAdd (φ t) =
        Multiplicative.toAdd (φ t) := by
    intro t
    have h := hcompat ⟨x, hxH⟩ t (hnorm t)
    constructor
    · intro hxt
      have h1 : (⟨x * (t : G) * x⁻¹, hnorm t⟩ : ↥T) = t := Subtype.ext hxt
      have h2 : φ t = Multiplicative.ofAdd (((e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) :
          SL(n, GaloisField 2 m)) : Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ
            Multiplicative.toAdd (φ t)) := by
        rw [← h]
        exact congrArg φ h1.symm
      exact (congrArg Multiplicative.toAdd h2).symm
    · intro hu
      have h1 : φ ⟨x * (t : G) * x⁻¹, hnorm t⟩ = φ t := by
        rw [h, hu]
        rfl
      exact congrArg Subtype.val (φ.injective h1)
  let e₁ : ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≃ {t : ↥T // x * (t : G) * x⁻¹ = t} :=
    { toFun := fun c => ⟨⟨c, c.2.1⟩, by
        have := Subgroup.mem_centralizer_iff.1 c.2.2 x (Set.mem_singleton x)
        show x * (c : G) * x⁻¹ = c
        rw [this, mul_inv_cancel_right]⟩
      invFun := fun t => ⟨t.1, t.1.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have := t.2
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this⟩
      left_inv := fun c => rfl
      right_inv := fun t => rfl }
  let e₂ : {t : ↥T // x * (t : G) * x⁻¹ = t} ≃
      {w : Fin n → GaloisField 2 m //
        ((e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ w = w} :=
    Equiv.subtypeEquiv (φ.toEquiv.trans Multiplicative.toAdd) fun t => key t
  exact (Nat.card_congr (e₁.trans e₂)).symm

theorem Sec6Ctx.sec67_transv (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) :
    ∃ _ : (T.subgroupOf (hSub T (normIn T₁ T))).Normal,
      ∃ (e : ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)) ≃* SL(n, GaloisField 2 m))
        (φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m)),
        (∀ (h : ↥(hSub T (normIn T₁ T))) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
          φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
            Multiplicative.ofAdd (((e (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
              Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t)))) ∧
        ∀ x ∈ normD T, x ∉ T → ∃ hxH : x ∈ (hSub T (normIn T₁ T)),
          IsTransvection (e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(hSub T (normIn T₁ T))))) := by
  have := hc.finite
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hc.hy.card
    rw [hc.hT, pow_zero, one_pow] at this
    omega
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  have hxH : ∀ x ∈ normD T, x ∈ hSub T (normIn T₁ T) := fun x hx =>
    hc.normD_le_hSub_of_not_a8 h1 h63 hA8 hx
  have hcen : ∀ x ∈ normD T, x ∉ T → Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card (GaloisField 2 m) ^ (n - 1) := fun x hx hxT => by
    rw [hc.card_centralizer_eq h63 hA8 hx hxT, hc.card_normIn, hcardF]
  have hx2 : ∀ x ∈ normD T, x * x = 1 := fun x hx =>
    mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 hx.1
  clear h1 h63
  generalize hHdef : hSub T (normIn T₁ T) = H at *
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  refine ⟨hN, e, φ, hcompat, fun x hx hxT => ?_⟩
  refine ⟨hxH x hx, ?_⟩
  have hu2 : e (QuotientGroup.mk (⟨x, hxH x hx⟩ : ↥H)) * e (QuotientGroup.mk (⟨x, hxH x hx⟩ : ↥H))
      = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul]
    have : (⟨x, hxH x hx⟩ * ⟨x, hxH x hx⟩ : ↥H) = 1 := Subtype.ext (hx2 x hx)
    rw [this, QuotientGroup.mk_one, map_one]
  have hu1 : e (QuotientGroup.mk (⟨x, hxH x hx⟩ : ↥H)) ≠ 1 := by
    intro h
    have h' : (QuotientGroup.mk (⟨x, hxH x hx⟩ : ↥H) : ↥H ⧸ T.subgroupOf H) = 1 :=
      e.injective (by rw [map_one]; exact h)
    exact hxT (Subgroup.mem_subgroupOf.1
      ((QuotientGroup.eq_one_iff (N := T.subgroupOf H) (⟨x, hxH x hx⟩ : ↥H)).1 h'))
  refine isTransvection_of_card_fixed hu2 hu1 ?_
  rw [card_fixed_eq_card_centralizer e φ hcompat (hxH x hx) hx.2, hcen x hx hxT]

theorem Sec6Ctx.sec67_conj (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) :
    ∀ x ∈ normD T, x ∉ T → ∀ y ∈ normD T, y ∉ T →
      ∃ g ∈ Subgroup.normalizer (T : Set G), y = g * x * g⁻¹ := by
  have := hc.finite
  obtain ⟨hN, e, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have hHN : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun z hz => (mem_normIn.1 hz).2)
  have hx2 : ∀ x ∈ normD T, x * x = 1 := fun x hx =>
    mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 hx.1
  intro x hx hxT y hy hyT
  obtain ⟨hxH, hux⟩ := htr x hx hxT
  obtain ⟨hyH, huy⟩ := htr y hy hyT
  clear h1 hnat
  generalize hHdef : hSub T (normIn T₁ T) = H at *
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hux huy
  obtain ⟨q, hq⟩ := e.surjective W
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hmk : (QuotientGroup.mk (w * ⟨x, hxH⟩ * w⁻¹) : ↥H ⧸ T.subgroupOf H) =
      QuotientGroup.mk (⟨y, hyH⟩ : ↥H) := by
    apply e.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hq, ← hW]
  have hmem := QuotientGroup.eq.1 hmk
  rw [Subgroup.mem_subgroupOf] at hmem
  set z : G := (w : G) * x * (w : G)⁻¹ with hz
  have hzD : z ∈ classD T := by
    have := classD_conj hx.1 (w : G)⁻¹
    rwa [inv_inv] at this
  have hzy : z = y * (z⁻¹ * y)⁻¹ := by group
  have hT' : z⁻¹ * y ∈ T := by
    have : (↑(w * ⟨x, hxH⟩ * w⁻¹ : ↥H))⁻¹ * y ∈ T := hmem
    simpa [hz] using this
  obtain ⟨s, hs, hzs⟩ := hc.eq_conj_of_mem_coset h62 h63 hy hyT hzD (T.inv_mem hT') hzy
  refine ⟨s * w, (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer hs)
    (hHN w.2), ?_⟩
  have hsz : s * z * s⁻¹ = y := by
    have : z = s⁻¹ * y * s := hzs
    rw [this]
    group
  rw [← hsz, hz]
  group

end CFSG.CGT.Timmesfeld75
