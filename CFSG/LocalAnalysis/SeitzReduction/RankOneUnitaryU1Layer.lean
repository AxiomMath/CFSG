module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Coords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeU3

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_fixed_of_isPGroup_quot {G : Type*} [Group G] {R K P : Subgroup G}
    [(K.subgroupOf R).Normal] [Finite (R ⧸ K.subgroupOf R)]
    (hev : 2 ∣ Nat.card (R ⧸ K.subgroupOf R)) (hP : IsPGroup 2 P)
    (hPR : P ≤ normalizer (R : Set G)) (hPK : P ≤ normalizer (K : Set G)) :
    ∃ x ∈ R, x ∉ K ∧ ∀ v ∈ P, x⁻¹ * (v * x * v⁻¹) ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P (R ⧸ K.subgroupOf R) := MulAction.compHom _ (quotConj P hPR hPK)
  have h1 : (1 : R ⧸ K.subgroupOf R) ∈ MulAction.fixedPoints P (R ⧸ K.subgroupOf R) := by
    intro v
    change quotConj P hPR hPK v 1 = 1
    exact map_one _
  obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hev h1
  induction b using QuotientGroup.induction_on with | H x => ?_
  refine ⟨x, x.2, fun hxK => hb1 ?_, fun v hv => ?_⟩
  · exact ((QuotientGroup.eq_one_iff x).mpr (mem_subgroupOf.mpr hxK)).symm
  · have h2 : quotConj P hPR hPK ⟨v, hv⟩ (x : R ⧸ K.subgroupOf R) = x := hb ⟨v, hv⟩
    rw [quotConj_mk, QuotientGroup.eq, mem_subgroupOf] at h2
    have h3 := inv_mem h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using h3

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem conj_mem_of_mem_u3U_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hEn : (E.subgroupOf
      (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {v : G} (hv : v ∈ u3U L T R₂ t E) {x : G} (hx : x ∈ szT₁ L T) :
    x⁻¹ * (v * x * v⁻¹) ∈ R₂ := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hNA, hNAR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  set U := u3U L T R₂ t E with hU
  have hUY := u3U_le_normalizer L T R₂ t E
  have hYU := le_normalizer_u3U hEn
  have hUH : U ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) :=
    fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).1
  have hUR₂ : U ≤ normalizer (R₂ : Set G) := fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).2
  have hU2 : IsPGroup 2 U := h.isPGroup_u3U_of_card_sylow hS2 hR hc hΩ hEreg
  have hcen : ∀ a ∈ R₂, ∀ y ∈ szT₁ L T ⊔ R₂, a * y = y * a := fun a ha y hy =>
    hR.comm_of_mem_sup ha hy
  let W : Subgroup G :=
    { carrier := {x | x ∈ szT₁ L T ∧ ∀ v ∈ U, x⁻¹ * (v * x * v⁻¹) ∈ R₂}
      mul_mem' := by
        rintro x y ⟨hxT, hxW⟩ ⟨hyT, hyW⟩
        refine ⟨mul_mem hxT hyT, fun v hv => ?_⟩
        have ha := hxW v hv
        have hb := hyW v hv
        have hya : y⁻¹ * (x⁻¹ * (v * x * v⁻¹)) = (x⁻¹ * (v * x * v⁻¹)) * y⁻¹ :=
          (hcen _ ha _ (mem_sup_left (inv_mem hyT))).symm
        have e : (x * y)⁻¹ * (v * (x * y) * v⁻¹) =
            y⁻¹ * (x⁻¹ * (v * x * v⁻¹)) * (v * y * v⁻¹) := by group
        rw [e, hya, mul_assoc]
        exact mul_mem ha hb
      one_mem' := ⟨one_mem _, fun v _ => by simp⟩
      inv_mem' := by
        rintro x ⟨hxT, hxW⟩
        refine ⟨inv_mem hxT, fun v hv => ?_⟩
        have ha := hxW v hv
        have hxa : Commute x (x⁻¹ * (v * x * v⁻¹)) :=
          (hcen _ ha _ (mem_sup_left hxT)).symm
        have e : x⁻¹⁻¹ * (v * x⁻¹ * v⁻¹) = x * (x⁻¹ * (v * x * v⁻¹))⁻¹ * x⁻¹ := by group
        rw [e, hxa.inv_right.eq, mul_inv_cancel_right]
        exact inv_mem ha }
  have hmemW : ∀ y, y ∈ W ↔ y ∈ szT₁ L T ∧ ∀ v ∈ U, y⁻¹ * (v * y * v⁻¹) ∈ R₂ := fun _ => Iff.rfl
  have hA₁W : ∀ a ∈ szA₁ (szT₁ L T), a ∈ W := fun a ha =>
    ⟨szA₁_le _ ha, fun v hv => mul_mem (inv_mem (hR.le ha))
      ((mem_normalizer_iff.mp (hUR₂ hv) a).mp (hR.le ha))⟩
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hT₁card, -⟩ := h.facts_of_card_sylow hS2
  have hNorm : (R₂.subgroupOf (szT₁ L T ⊔ R₂)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer)
  have hHcard : Nat.card (szT₁ L T ⊔ R₂ : Subgroup G) = (2 ^ f) ^ 4 := by
    have h1 := hR.card_sup_mul
    rw [hA₁card, hT₁card, hR.card] at h1
    have h2 : Nat.card (szT₁ L T ⊔ R₂ : Subgroup G) * 2 ^ f = (2 ^ f) ^ 4 * 2 ^ f := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have hev : 2 ∣ Nat.card ((szT₁ L T ⊔ R₂ : Subgroup G) ⧸ R₂.subgroupOf (szT₁ L T ⊔ R₂)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R₂.subgroupOf (szT₁ L T ⊔ R₂))
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : R₂ ≤ szT₁ L T ⊔ R₂)).toEquiv,
      hHcard, hR.card] at h1
    have h2 : Nat.card ((szT₁ L T ⊔ R₂ : Subgroup G) ⧸ R₂.subgroupOf (szT₁ L T ⊔ R₂)) =
        (2 ^ f) ^ 2 := by
      have h3 : (2 ^ f) ^ 2 * (2 ^ f) ^ 2 =
          Nat.card ((szT₁ L T ⊔ R₂ : Subgroup G) ⧸ R₂.subgroupOf (szT₁ L T ⊔ R₂)) *
            (2 ^ f) ^ 2 := by rw [← h1]; ring
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) h3).symm
    rw [h2]
    exact dvd_pow (dvd_pow_self 2 (by have := h.two_le; omega)) (by norm_num)
  obtain ⟨x₀, hx₀H, hx₀R, hx₀fix⟩ := exists_fixed_of_isPGroup_quot hev hU2 hUH hUR₂
  obtain ⟨w₀, hw₀, r₀, hr₀, rfl⟩ := hR.mem_sup_iff.mp hx₀H
  have hw₀A : w₀ ∉ szA₁ (szT₁ L T) := fun hA => hx₀R (mul_mem (hR.le hA) hr₀)
  have hw₀W : w₀ ∈ W := by
    refine ⟨hw₀, fun v hv => ?_⟩
    have h1 := hx₀fix v hv
    have hvr : v * r₀ * v⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hUR₂ hv) r₀).mp hr₀
    have e : w₀⁻¹ * (v * w₀ * v⁻¹) =
        r₀ * ((w₀ * r₀)⁻¹ * (v * (w₀ * r₀) * v⁻¹)) * (v * r₀ * v⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hr₀ h1) (inv_mem hvr)
  obtain ⟨K, _, _, _, σ, hKcard, -, u, uu, hcoord, hA₁u, d, hdL, hdT, μ, hμ0, hμord, hdμ⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have hdA : d ∈ normalizer (szA L T t : Set G) := h.inf_normalizer_le_normalizer_szA ⟨hdL, hdT⟩
  have hdU : d ∈ normalizer (U : Set G) := hYU (hNA hdA)
  have hdR₂ : d ∈ normalizer (R₂ : Set G) := hNAR₂ hdA
  have hdW : ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
    rintro w ⟨hwT, hwW⟩
    refine ⟨(mem_normalizer_iff.mp hdT w).mp hwT, fun v hv => ?_⟩
    have hv' : d⁻¹ * v * d ∈ U := by
      have := (mem_normalizer_iff.mp (inv_mem hdU) v).mp hv
      rwa [inv_inv] at this
    have h2 := (mem_normalizer_iff.mp hdR₂ _).mp (hwW _ hv')
    have e : (d * w * d⁻¹)⁻¹ * (v * (d * w * d⁻¹) * v⁻¹) =
        d * (w⁻¹ * ((d⁻¹ * v * d) * w * (d⁻¹ * v * d)⁻¹)) * d⁻¹ := by group
    rw [e]
    exact h2
  have hdWpow : ∀ m : ℕ, ∀ w ∈ W,
      d ^ m * w * (d ^ m)⁻¹ ∈ W ∧ u (d ^ m * w * (d ^ m)⁻¹) = μ ^ m * u w := by
    intro m
    induction m with
    | zero => intro w hw; simp [hw]
    | succ m ih =>
      intro w hw
      obtain ⟨h1, h2⟩ := ih w hw
      have e : d ^ (m + 1) * w * (d ^ (m + 1))⁻¹ = d * (d ^ m * w * (d ^ m)⁻¹) * d⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      refine ⟨hdW _ h1, ?_⟩
      rw [hdμ _ ((hmemW _).mp h1).1, h2, pow_succ']
      ring
  let A : AddSubgroup K :=
    { carrier := {a | ∃ w ∈ W, u w = a}
      add_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w * w', mul_mem hw hw',
          hcoord.mul_u w ((hmemW _).mp hw).1 w' ((hmemW _).mp hw').1⟩
      zero_mem' := ⟨1, one_mem _, hcoord.u_one⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, inv_mem hw, hcoord.u_inv ((hmemW _).mp hw).1⟩ }
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hAtop : A = ⊤ := by
    set μu : Kˣ := (Ne.isUnit hμ0).unit with hμu
    have hμuval : (μu : K) = μ := IsUnit.unit_spec _
    refine addSubgroup_eq_top_of_scalar_stable (q := 2 ^ f) hKcard (by omega) A
      ⟨w₀, hw₀W, rfl⟩ (fun h0 => hw₀A ((hA₁u w₀ hw₀).mpr h0)) (zpowers μu) ?_ ?_
    · intro s hs y hy
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨m, hm⟩ := (isOfFinOrder_of_finite μu).mem_powers_iff_mem_zpowers.mpr hs
      refine ⟨d ^ m * w * (d ^ m)⁻¹, (hdWpow m w hw).1, ?_⟩
      rw [(hdWpow m w hw).2, ← hm, Units.val_pow_eq_pow_val, hμuval]
    · rw [Nat.card_zpowers]
      have h1 : orderOf μu = orderOf μ := by rw [← hμuval]; exact orderOf_units.symm
      rw [h1, hμord]
      obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
      rw [← hq] at hq4 ⊢
      have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
      have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have h2 : q ≤ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
        rw [Nat.le_div_iff_mul_le hgpos]
        have h3 : 3 * q + 1 ≤ q ^ 2 := by nlinarith
        have h4 : q * Nat.gcd 3 (q + 1) ≤ 3 * q := by nlinarith
        omega
      omega
  have hxA : u x ∈ A := by
    rw [hAtop]
    exact AddSubgroup.mem_top _
  obtain ⟨w, hw, hwx⟩ := hxA
  have hwT := ((hmemW _).mp hw).1
  have h0 : u (w⁻¹ * x) = 0 := by rw [hcoord.u_mul_inv hwT hx, hwx, sub_self]
  have hwxA : w⁻¹ * x ∈ szA₁ (szT₁ L T) := (hA₁u _ (mul_mem (inv_mem hwT) hx)).mpr h0
  have hxW : x ∈ W := by
    have := mul_mem hw (hA₁W _ hwxA)
    rwa [mul_inv_cancel_left] at this
  exact ((hmemW _).mp hxW).2 v hv

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
