module

public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a').mp
          ha'), b * b', B.mul_mem hb hb', by group⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer _).inv_mem (hBA hb)) a⁻¹).mp (A.inv_mem ha), b⁻¹, B.inv_mem hb,
          by group⟩ }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem frattini {X Y P : Subgroup G} (hXY : X ≤ Y) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hP : IsSylow2In P X) {y : G} (hy : y ∈ Y) :
    ∃ x ∈ X, ∃ n ∈ Y ⊓ Subgroup.normalizer (P : Set G), y = x * n := by
  have hPy : IsSylow2In (conjSub y P) X := by
    have := IsSylow2In.conj hP y
    rwa [mem_normalizer_iff_conjSub_eq.mp (hYX hy)] at this
  obtain ⟨x, hx, hxP⟩ := exists_conjSub_eq_of_isSylow2In hP hPy
  refine ⟨x, hx, x⁻¹ * y, Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem (hXY hx)) hy, ?_⟩, by group⟩
  rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hxP, ← conjSub_mul, inv_mul_cancel,
    conjSub_one]

theorem isSylow2In_of_eq_oddCoreOf_sup {X P : Subgroup G} (hPX : P ≤ X) (hP2 : IsPGroup 2 P)
    (hX : X = oddCoreOf X ⊔ P) : IsSylow2In P X := by
  refine ⟨hPX, hP2, fun P' hP'X hP'2 hPP' => le_antisymm (fun p hp => ?_) hPP'⟩
  have hPN : P ≤ Subgroup.normalizer ((oddCoreOf X : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hPX hw))
  have hpX : p ∈ oddCoreOf X ⊔ P := hX ▸ hP'X hp
  obtain ⟨o, ho, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPN hpX
  have hoP' : o ∈ P' := by
    have := P'.mul_mem hp (P'.inv_mem (hPP' hw))
    simpa using this
  have ho1 : o = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) ho
    (hP'2.to_le (Subgroup.zpowers_le.mpr hoP'))
  rw [ho1, one_mul]
  exact hw

omit [Finite G] in
theorem IsQuatSub.pow_half_eq_one {R : Subgroup G} (hR : IsQuatSub R) {x : G} (hx : x ∈ R) :
    x ^ (Nat.card R / 2) = 1 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hR
  have hcard : Nat.card R = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hhalf : Nat.card R / 2 = 2 * 2 ^ k := by omega
  rw [hhalf]
  have hord : orderOf (e ⟨x, hx⟩) ∣ 2 * 2 ^ k := by
    generalize e ⟨x, hx⟩ = q
    cases q with
    | a i =>
      rw [QuaternionGroup.orderOf_a]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    | xa i =>
      rw [QuaternionGroup.orderOf_xa]
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = 2 * m := ⟨2 ^ (k - 1), by
        rw [← pow_succ']; congr 1; omega⟩
      exact ⟨m, by rw [hm]; ring⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at hord
  exact orderOf_dvd_iff_pow_eq_one.mp hord

omit [Finite G] in
theorem centralizes_of_odd_pow {A : Subgroup G} (hA2 : IsPGroup 2 ↥A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {n : G}
    (hnA : n ∈ Subgroup.normalizer (A : Set G)) (hinv : ∀ x ∈ A, x * x = 1 → n * x * n⁻¹ = x)
    {k : ℕ} (hk : Odd k) (hpow : ∀ x ∈ A, n ^ k * x * (n ^ k)⁻¹ = x) :
    ∀ x ∈ A, n * x * n⁻¹ = x := by
  have key : ∀ i : ℕ, ∀ x ∈ A, x ^ 2 ^ i = 1 → n * x * n⁻¹ = x := by
    intro i
    induction i with
    | zero =>
      intro x _ hx
      rw [pow_zero, pow_one] at hx
      rw [hx]
      group
    | succ i ih =>
      intro x hx hxi
      have hy : n * (x * x) * n⁻¹ = x * x := by
        refine ih (x * x) (A.mul_mem hx hx) ?_
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hxi
      have hx' : n * x * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnA x).mp hx
      set δ := x⁻¹ * (n * x * n⁻¹) with hδ
      have hδA : δ ∈ A := A.mul_mem (A.inv_mem hx) hx'
      have hδ2 : δ * δ = 1 := by
        have hc : (n * x * n⁻¹) * x⁻¹ = x⁻¹ * (n * x * n⁻¹) := hAab _ hx' _ (A.inv_mem hx)
        calc δ * δ = x⁻¹ * ((n * x * n⁻¹) * x⁻¹) * (n * x * n⁻¹) := by rw [hδ]; group
          _ = x⁻¹ * (x⁻¹ * (n * x * n⁻¹)) * (n * x * n⁻¹) := by rw [hc]
          _ = (x * x)⁻¹ * (n * (x * x) * n⁻¹) := by group
          _ = 1 := by rw [hy]; group
      have hnδ : n * δ * n⁻¹ = δ := hinv δ hδA hδ2
      have hcomm : Commute n δ := by
        show n * δ = δ * n
        calc n * δ = n * δ * n⁻¹ * n := by group
          _ = δ * n := by rw [hnδ]
      have hpowm : ∀ m : ℕ, n ^ m * x * (n ^ m)⁻¹ = x * δ ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
          have hcm : n ^ m * δ * (n ^ m)⁻¹ = δ := by
            rw [(hcomm.pow_left m).eq]
            group
          calc n ^ (m + 1) * x * (n ^ (m + 1))⁻¹ =
                n ^ m * (n * x * n⁻¹) * (n ^ m)⁻¹ := by rw [pow_succ]; group
            _ = n ^ m * (x * δ) * (n ^ m)⁻¹ := by rw [hδ]; group
            _ = (n ^ m * x * (n ^ m)⁻¹) * (n ^ m * δ * (n ^ m)⁻¹) := by group
            _ = x * δ ^ m * δ := by rw [ihm, hcm]
            _ = x * δ ^ (m + 1) := by rw [pow_succ, mul_assoc]
      have hδk : δ ^ k = 1 := by
        have h1 := hpowm k
        rw [hpow x hx] at h1
        have := congrArg (fun w => x⁻¹ * w) h1
        simpa using this.symm
      have hδ1 : δ = 1 := by
        obtain ⟨l, rfl⟩ := hk
        have hsq : δ ^ 2 = 1 := by rw [pow_two]; exact hδ2
        rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at hδk
        exact hδk
      have : x⁻¹ * (n * x * n⁻¹) = 1 := hδ1
      calc n * x * n⁻¹ = x * (x⁻¹ * (n * x * n⁻¹)) := by group
        _ = x := by rw [this, mul_one]
  intro x hx
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hA2) ⟨x, hx⟩
  refine key i x hx ?_
  rw [Subgroup.orderOf_mk] at hi
  rw [← hi]
  exact pow_orderOf_eq_one x

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
