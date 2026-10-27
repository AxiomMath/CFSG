module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))

include h11 hE16 hF hL hodd hyA hyE hyU hy3 hW

theorem eq_one_of_mem_centralizer_sec2W {r : G} (hr : r ∈ R)
    (hrW : r ∈ centralizer (sec2W A E y : Set G)) : r = 1 := by
  by_contra hr1
  have hCr := sec2W_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hr1
  have hle : sec2W A E y ≤ E ⊓ A := by
    rw [← hCr]
    refine le_inf le_rfl fun w hw => mem_centralizer_iff.mpr fun t ht => ?_
    rw [Set.mem_singleton_iff.mp ht]
    exact (mem_centralizer_iff.mp hrW w hw).symm
  have := card_le_of_le hle
  rw [card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3, card_inf_left hF hodd] at this
  omega

theorem sec2P_inf_centralizer_eq :
    sec2P E ⊓ centralizer (sec2W A E y : Set G) = sec2W A E y := by
  obtain ⟨-, -, hWP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hWc : ∀ x ∈ sec2W A E y, ∀ x' ∈ sec2W A E y, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  refine le_antisymm (fun p hp => ?_) (le_inf hWP fun w hw => mem_centralizer_iff.mpr
    fun x hx => hWc x hx w hw)
  obtain ⟨w, hw, r, hr, rfl⟩ :=
    exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 hp.1
  have hwC : w ∈ centralizer (sec2W A E y : Set G) :=
    mem_centralizer_iff.mpr fun x hx => hWc x hx w hw
  have hrW : r ∈ centralizer (sec2W A E y : Set G) := by
    have := (centralizer (sec2W A E y : Set G)).mul_mem
      ((centralizer (sec2W A E y : Set G)).inv_mem hwC) hp.2
    simpa using this
  rw [eq_one_of_mem_centralizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hr hrW, mul_one]
  exact hw

theorem mem_sec2P_of_mem_normalizer_of_mem_centralizer {q : G}
    (hqN : q ∈ normalizer (sec2P E : Set G)) (hqC : q ∈ centralizer (sec2W A E y : Set G))
    (hq2 : ∃ n : ℕ, q ^ 2 ^ n = 1) : q ∈ sec2P E := by
  obtain ⟨hD, T₀, hT₀⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  obtain ⟨-, hUW, hWP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hqE : q ∈ normalizer (E : Set G) :=
    normalizer_sec2P_le_normalizer h11 hE16 hF hL hodd hyA hyE hyU hy3 hW hqN
  set W := sec2W A E y with hWdef
  have hWc : ∀ x ∈ W, ∀ x' ∈ W, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hW.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hqw : ∀ w ∈ W, q * w = w * q := fun w hw => (mem_centralizer_iff.mp hqC w hw).symm
  have hpt : ∀ Q ∈ pointsIn R E, ∃ w ∈ W, rightConjugate R w = Q := by
    intro Q hQ
    obtain ⟨p, hp, rfl⟩ := htr Q hQ
    obtain ⟨w, hw, r, hr, hpe⟩ :=
      exists_eq_mul_of_mem_sec2P h11 hE16 hF hL hodd hyA hyE hyU hy3 ((sec2P E).inv_mem hp)
    refine ⟨w⁻¹, W.inv_mem hw, ?_⟩
    have hp' : p = r⁻¹ * w⁻¹ := by rw [← mul_inv_rev, ← hpe, inv_inv]
    rw [hp', ← rightConjugate_mul, (rightConjugate_eq_self_iff R r⁻¹).mpr
      (le_normalizer (R.inv_mem hr))]
  obtain ⟨w₀, hw₀, hw₀R⟩ := hpt _ (rightConjugate_mem_pointsIn hD.self_mem hqE)
  set k := q * w₀⁻¹ with hk
  have hkR : rightConjugate R k = R := by
    rw [hk, ← rightConjugate_mul, ← hw₀R, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hkpt : ∀ Q ∈ pointsIn R E, k ∈ normalizer (Q : Set G) := by
    intro Q hQ
    obtain ⟨w, hw, rfl⟩ := hpt Q hQ
    refine (rightConjugate_eq_self_iff _ k).mp ?_
    have hwk : w * k = k * w := by
      calc w * k = (w * q) * w₀⁻¹ := by rw [hk, mul_assoc]
        _ = q * (w * w₀⁻¹) := by rw [← hqw w hw, mul_assoc]
        _ = q * (w₀⁻¹ * w) := by rw [hWc w hw _ (W.inv_mem hw₀)]
        _ = k * w := by rw [hk, mul_assoc]
    rw [rightConjugate_mul, hwk, ← rightConjugate_mul, hkR]
  have hkW : ∀ w ∈ W, k * w * k⁻¹ = w := fun w hw => by
    have h1 : w₀⁻¹ * w * w₀⁻¹⁻¹ = w := by
      rw [hWc _ (W.inv_mem hw₀) w hw, inv_inv, inv_mul_cancel_right]
    calc k * w * k⁻¹ = q * (w₀⁻¹ * w * w₀⁻¹⁻¹) * q⁻¹ := by rw [hk]; group
      _ = w := by rw [h1, hqw w hw, mul_inv_cancel_right]
  have hkE : k ∈ normalizer (E : Set G) :=
    mul_mem hqE (inv_mem (Sec2.sec2P_le E (hWP hw₀)))
  have hkr : ∀ r ∈ R, k * r * k⁻¹ = r := by
    intro r hr
    have hr' : k * r * k⁻¹ ∈ R := by
      have : r ∈ rightConjugate R k := by rw [hkR]; exact hr
      exact (mem_rightConjugate_iff R k r).mp this
    set r' := k * r * k⁻¹ with hr'def
    have hrr : r * r'⁻¹ ∈ centralizer (W : Set G) := mem_centralizer_iff.mpr fun w hw => by
      have hu : r⁻¹ * w⁻¹ * r * w ∈ E ⊓ A :=
        hD.commutator_mem hT₀ hCE hF.elemE (hF.R_le_E hr) (hWP hw)
      have h1 : k * (r⁻¹ * w⁻¹ * r * w) * k⁻¹ = r⁻¹ * w⁻¹ * r * w := hkW _ (hUW hu)
      have h2 : k * (r⁻¹ * w⁻¹ * r * w) * k⁻¹ = r'⁻¹ * w⁻¹ * r' * w := by
        calc k * (r⁻¹ * w⁻¹ * r * w) * k⁻¹
            = (k * r * k⁻¹)⁻¹ * (k * w * k⁻¹)⁻¹ * (k * r * k⁻¹) * (k * w * k⁻¹) := by group
          _ = r'⁻¹ * w⁻¹ * r' * w := by rw [hkW w hw]
      have h3 : r'⁻¹ * w⁻¹ * r' = r⁻¹ * w⁻¹ * r := by
        have := h2.symm.trans h1
        exact mul_right_cancel this
      calc w * (r * r'⁻¹) = r * (r⁻¹ * w⁻¹ * r)⁻¹ * r'⁻¹ := by group
        _ = r * (r'⁻¹ * w⁻¹ * r')⁻¹ * r'⁻¹ := by rw [h3]
        _ = r * r'⁻¹ * w := by group
    have h1 := eq_one_of_mem_centralizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
      (R.mul_mem hr (R.inv_mem hr')) hrr
    rw [mul_inv_eq_one] at h1
    exact h1.symm
  obtain ⟨r₀, hr₀, hr₀1⟩ := hD.exists_ne_one
  have hkC : k ∈ centralizer (E : Set G) :=
    hD.mem_centralizer_of_fix hkE hkpt hr₀ hr₀1 (hkr r₀ hr₀)
  obtain ⟨n, hn⟩ := hq2
  have hcomm : Commute q w₀⁻¹ := (hqw _ (W.inv_mem hw₀))
  have hw₀2 : w₀⁻¹ ^ 2 = 1 := by rw [inv_pow, hW.2 w₀ hw₀, inv_one]
  have hk2 : k ^ 2 ^ (n + 1) = 1 := by
    rw [hk, hcomm.mul_pow, pow_succ, pow_mul, hn, one_pow, one_mul, pow_mul', hw₀2, one_pow]
  have hkE' : k ∈ E := hCE k hkC (n + 1) hk2
  have hq : q = k * w₀ := by rw [hk, inv_mul_cancel_right]
  rw [hq]
  exact mul_mem (hEP hkE') (hWP hw₀)

theorem isSylowOf_sec2P_sup :
    IsSylowOf 2 (sec2P E) (centralizer (sec2W A E y : Set G) ⊔ sec2P E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  set C := centralizer (sec2W A E y : Set G) with hC
  have hPC : sec2P E ≤ normalizer (C : Set G) := fun p hp =>
    normalizer_le_normalizer_centralizer _ (hPW hp)
  have hP2 := Sec2.isPGroup_sec2P E
  obtain ⟨S₁, hS₁, hPS₁⟩ := AschbacherTheorem3.exists_isSylowOf_le hP2
    (le_sup_right : sec2P E ≤ C ⊔ sec2P E)
  suffices hS : S₁ = sec2P E by rwa [hS] at hS₁
  by_contra hne
  have : Group.IsNilpotent ↥S₁ := hS₁.isPGroup.isNilpotent
  have hlt : (sec2P E).subgroupOf S₁ < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun h => hne (le_antisymm h hPS₁)
  have h1 := Group.normalizerCondition_of_isNilpotent _ hlt
  rw [← subgroupOf_normalizer_eq hPS₁] at h1
  obtain ⟨x, hxN, hxP⟩ := IsConcreteLE.exists_of_lt h1
  have hxN' : (x : G) ∈ normalizer (sec2P E : Set G) := hxN
  have hxP' : (x : G) ∉ sec2P E := fun h => hxP (mem_subgroupOf.mpr h)
  have hxX : (x : G) ∈ ((C ⊔ sec2P E : Subgroup G) : Set G) := hS₁.le x.2
  rw [coe_mul_of_right_le_normalizer_left C _ hPC] at hxX
  obtain ⟨c, hc, p, hp, hcp⟩ := hxX
  have hcp' : c * p = x := hcp
  have hcN : c ∈ normalizer (sec2P E : Set G) := by
    have : c = x * p⁻¹ := by rw [← hcp', mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxN' (inv_mem (le_normalizer hp))
  have hcS : c ∈ S₁ := by
    have : c = x * p⁻¹ := by rw [← hcp', mul_inv_cancel_right]
    rw [this]
    exact mul_mem x.2 (inv_mem (hPS₁ hp))
  obtain ⟨n, hn⟩ := (hS₁.isPGroup ⟨c, hcS⟩)
  have hc2 : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcP := mem_sec2P_of_mem_normalizer_of_mem_centralizer h11 hE16 hF hL hodd hyA hyE hyU hy3
    hW hcN hc ⟨n, hc2⟩
  exact hxP' (hcp' ▸ mul_mem hcP hp)

theorem mem_sec2W_of_mem_centralizer {c : G} (hc : c ∈ centralizer (sec2W A E y : Set G))
    (hc2 : ∃ n : ℕ, c ^ 2 ^ n = 1) : c ∈ sec2W A E y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hPW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  set C := centralizer (sec2W A E y : Set G) with hC
  have hPC : sec2P E ≤ normalizer (C : Set G) := fun p hp =>
    normalizer_le_normalizer_centralizer _ (hPW hp)
  have hsyl := isSylowOf_sec2P_sup h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  obtain ⟨n, hn⟩ := hc2
  obtain ⟨g', hg', hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hsyl
    (AS76b.isPGroup_zpowers_of_pow_eq_one hn) (zpowers_le.mpr (mem_sup_left hc))
  have hg'' : g' ∈ ((C ⊔ sec2P E : Subgroup G) : Set G) := hg'
  rw [coe_mul_of_right_le_normalizer_left C _ hPC] at hg''
  obtain ⟨c₁, hc₁, p₁, hp₁, hg₁⟩ := hg''
  have hg₁' : c₁ * p₁ = g' := hg₁
  have hmem : g'⁻¹ * c * g' ∈ sec2P E := by
    refine hle ?_
    rw [mem_rightConjugate_iff]
    simp [mul_assoc]
  have h1 : c₁⁻¹ * c * c₁ ∈ sec2P E := by
    have := (sec2P E).mul_mem ((sec2P E).mul_mem hp₁ hmem) ((sec2P E).inv_mem hp₁)
    rw [← hg₁'] at this
    simpa [mul_assoc] using this
  have h2 : c₁⁻¹ * c * c₁ ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hc₁) hc) hc₁
  have h3 : c₁⁻¹ * c * c₁ ∈ sec2W A E y := by
    rw [← sec2P_inf_centralizer_eq h11 hE16 hF hL hodd hyA hyE hyU hy3 hW]
    exact ⟨h1, h2⟩
  have h4 : c = c₁ * (c₁⁻¹ * c * c₁) * c₁⁻¹ := by group
  rw [h4, ← mem_centralizer_iff.mp hc₁ _ h3, mul_inv_cancel_right]
  exact h3

end Frame

end CFSG.ComponentClassification.AS81
