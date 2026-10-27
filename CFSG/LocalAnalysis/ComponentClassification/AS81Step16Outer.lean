module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Line

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_mem_inf_of_even (hF : Frame G A A R g E F) (heven : Even (Nat.card (center ↥A))) :
    ∃ z ∈ R ⊓ A, z ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥A) 2 (even_iff_two_dvd.mp heven)
  have hzA : ((z : ↥A) : G) ∈ A := (z : ↥A).2
  have hzK : ((z : ↥A) : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp z.2 ⟨b, hb⟩)
  have hord : orderOf ((z : ↥A) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have h2 : IsPGroup 2 (zpowers ((z : ↥A) : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  refine ⟨_, ⟨mem_of_mem_centralizer_of_isPGroup hF.sylowR hzA hzK h2, hzA⟩, ?_⟩
  intro h1
  rw [h1, orderOf_one] at hord
  omega

theorem exists_three_element_of_card_pointsIn_inf_eq_two
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    ∃ y : G, (∃ n : ℕ, y ^ 3 ^ n = 1) ∧ y ∈ normalizer (R : Set G) ∧
      y ∈ normalizer (A : Set G) ∧ ∀ r ∈ R, y * r = r * y → r = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  set V := E ⊓ F with hVdef
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hcommE a ha.1 b hb.1
  have hR : R ∈ pointsIn R V := self_mem_pointsIn (le_inf hF.R_le_E hF.R_le_F)
  have hRg : rightConjugate R g ∈ pointsIn R V :=
    ⟨by rw [hVdef, hF.inf_eq]; exact le_sup_right, g, rfl⟩
  have hRne : rightConjugate R g ≠ R := by
    intro h
    have h1 : V = R := by rw [hVdef, hF.inf_eq, h, sup_idem]
    have := card_inf_of_frame hF
    rw [← hVdef, h1, hF.cardR] at this
    omega
  have hRRg : R ⊓ rightConjugate R g = ⊥ :=
    inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hVab hR hRg hRne.symm
  have hpts : ∀ Q ∈ pointsIn R V, Q = R ∨ Q = rightConjugate R g := by
    intro Q hQ
    by_contra hQ'
    push Not at hQ'
    have hsub : ({R, rightConjugate R g, Q} : Set (Subgroup G)) ⊆ pointsIn R V := by
      rintro P (rfl | rfl | rfl)
      · exact hR
      · exact hRg
      · exact hQ
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [hRne.symm, hQ'.1.symm]),
      Set.ncard_pair hQ'.2.symm, ← Nat.card_coe_set_eq, h2] at h1
    omega
  obtain ⟨A', y, hyA, hPC, hNA, hy3, hyEF, hCV, -⟩ := exists_point_data hE16 h11 hF hL hRg
  have hyRg : y ∈ normalizer (rightConjugate R g : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hPC hr) y hyA).symm)
  have hyV : y ∈ normalizer (V : Set G) := by
    rw [hVdef, hF.inf_eq_center]
    exact mem_normalizer_centerIn hyEF
  have hyR : y ∈ normalizer (R : Set G) := by
    rw [← rightConjugate_eq_self_iff]
    have hmem : rightConjugate R y ∈ pointsIn R V := by
      refine ⟨?_, y, rfl⟩
      have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hR.1 y
      rwa [(rightConjugate_eq_self_iff V y).mpr hyV] at h1
    rcases hpts _ hmem with h | h
    · exact h
    · exfalso
      apply hRne
      have h1 := congrArg (fun Q => rightConjugate Q y⁻¹) h
      rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
        (rightConjugate_eq_self_iff _ _).mpr (inv_mem hyRg)] at h1
      exact h1.symm
  have hNRA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have hR1 : R ≠ ⊥ := by
      intro h
      have := hF.cardR
      rw [h, Subgroup.card_bot] at this
      omega
    rw [← AS76b.normalizer_centralizer_eq hstd]
    exact normalizer_two_subgroup_le _ _ hKte hF.sylowR.isPGroup hF.sylowR.le hR1
  refine ⟨y, hy3, hyR, hNRA hyR, fun r hr hyr => ?_⟩
  have hrV : r ∈ V := hR.1 hr
  have hrRg := hCV r hrV hyr
  have : r ∈ R ⊓ rightConjugate R g := ⟨hr, hrRg⟩
  rwa [hRRg, mem_bot] at this

theorem le_of_card_pointsIn_inf_eq_two {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (heven : Even (Nat.card (center ↥A))) (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    R ≤ A := by
  obtain ⟨y, ⟨n, hn⟩, hyR, hyA, hfree⟩ :=
    exists_three_element_of_card_pointsIn_inf_eq_two hE16 h11 hF hL h2
  obtain ⟨z, ⟨hzR, hzA⟩, hz1⟩ := exists_mem_inf_of_even hF heven
  have hRe := hF.elemR
  have hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨z₁, hz₁⟩ : ∃ w, w = y⁻¹ * z * y := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ w, w = y⁻¹ * z₁ * y := ⟨_, rfl⟩
  have hR' : ∀ x ∈ R, y⁻¹ * x * y ∈ R := fun x hx => (mem_normalizer_iff''.mp hyR x).mp hx
  have hA' : ∀ x ∈ A, y⁻¹ * x * y ∈ A := fun x hx => (mem_normalizer_iff''.mp hyA x).mp hx
  have hz₁R : z₁ ∈ R := hz₁ ▸ hR' z hzR
  have hz₂R : z₂ ∈ R := hz₂ ▸ hR' z₁ hz₁R
  have hz₁A : z₁ ∈ A := hz₁ ▸ hA' z hzA
  have hz₂A : z₂ ∈ A := hz₂ ▸ hA' z₁ hz₁A
  have hfix : ∀ x ∈ R, y⁻¹ * x * y = x → x = 1 := by
    intro x hx h
    apply hfree x hx
    calc y * x = y * (y⁻¹ * x * y) := by rw [h]
      _ = x * y := by group
  have hzz₁ : z = y * z₁ * y⁻¹ := by rw [hz₁]; group
  have hz₁z₂ : z₁ = y * z₂ * y⁻¹ := by rw [hz₂]; group
  have hne1 : z₁ ≠ z := fun h => hz1 (hfix z hzR (hz₁ ▸ h))
  have hne2 : z₂ ≠ z₁ := fun h => by
    have := hfix z₁ hz₁R (hz₂ ▸ h)
    exact hz1 (by rw [hzz₁, this]; group)
  have hne3 : z₂ ≠ z := by
    intro h
    have hcomm : Commute (y ^ 2) z := by
      show y ^ 2 * z = z * y ^ 2
      have h2' : (y ^ 2)⁻¹ * z * y ^ 2 = z₂ := by rw [hz₂, hz₁, sq, mul_inv_rev]; group
      have : (y ^ 2)⁻¹ * z * y ^ 2 = z := h2'.trans h
      calc y ^ 2 * z = y ^ 2 * ((y ^ 2)⁻¹ * z * y ^ 2) := by rw [this]
        _ = z * y ^ 2 := by group
    have hpow : (y ^ 2) ^ ((3 ^ n + 1) / 2) = y := by
      have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨m, hm⟩ := hodd
      have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
      rw [h1, ← pow_mul]
      have h2 : 2 * (m + 1) = 3 ^ n + 1 := by omega
      rw [h2, pow_succ, hn, one_mul]
    have := (hcomm.pow_left ((3 ^ n + 1) / 2)).eq
    rw [hpow] at this
    exact hz1 (hfix z hzR (by rw [mul_assoc, ← this]; group))
  have hz₁1 : z₁ ≠ 1 := fun h => hz1 (by rw [hzz₁, h]; group)
  have hz₂1 : z₂ ≠ 1 := fun h => hz₁1 (by rw [hz₁z₂, h]; group)
  intro r hr
  by_contra hrA
  have hsub : ({1, z, z₁, z₂, r} : Set G) ⊆ (R : Set G) := by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact R.one_mem
    · exact hzR
    · exact hz₁R
    · exact hz₂R
    · exact hr
  have hr1 : r ≠ 1 := fun h => hrA (h ▸ A.one_mem)
  have hrz : r ≠ z := fun h => hrA (h ▸ hzA)
  have hrz₁ : r ≠ z₁ := fun h => hrA (h ▸ hz₁A)
  have hrz₂ : r ≠ z₂ := fun h => hrA (h ▸ hz₂A)
  have h5 : ({1, z, z₁, z₂, r} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hz1.symm, hz₁1.symm, hz₂1.symm, hr1.symm]),
      Set.ncard_insert_of_notMem (by simp [hne1.symm, hne3.symm, hrz.symm]),
      Set.ncard_insert_of_notMem (by simp [hne2.symm, hrz₁.symm]),
      Set.ncard_pair hrz₂.symm]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h5, ← Nat.card_coe_set_eq] at h1
  have := hF.cardR
  change Nat.card ↥R = 4 at this
  have h4 : Nat.card ↥(R : Set G) = 4 := this
  omega

theorem exists_outer_of_card_pointsIn_inf_eq_two {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (heven : Even (Nat.card (center ↥A))) (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) :
    ∃ y : G, y ∈ normalizer (A : Set G) ∧ (∃ k : ℕ, orderOf y = 3 ^ k) ∧
      (∀ a ∈ A, ¬ ∀ x ∈ A, y⁻¹ * x * y = a⁻¹ * x * a) ∧ ∀ r ∈ R, r ≠ 1 → y * r ≠ r * y := by
  obtain ⟨y, ⟨n, hn⟩, -, hyA, hfree⟩ :=
    exists_three_element_of_card_pointsIn_inf_eq_two hE16 h11 hF hL h2
  have hRA := le_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2
  refine ⟨y, hyA, ?_, ?_, fun r hr hr1 h => hr1 (hfree r hr h)⟩
  · have hdvd : orderOf y ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨k, hk⟩
  · intro a ha hinn
    obtain ⟨r, hr, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
      by_contra h
      push Not at h
      have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr h
      have hc := hF.cardR
      rw [this, Subgroup.card_bot] at hc
      omega
    have h1 := hinn r (hRA hr)
    have hra : a * r = r * a := mem_centralizer_iff.mp (hF.sylowR.le hr) a ha
    have h2 : y⁻¹ * r * y = r := by
      rw [h1]
      calc a⁻¹ * r * a = a⁻¹ * (r * a) := by group
        _ = a⁻¹ * (a * r) := by rw [hra]
        _ = r := by group
    apply hr1
    apply hfree r hr
    calc y * r = y * (y⁻¹ * r * y) := by rw [h2]
      _ = r * y := by group

end CFSG.ComponentClassification.AS81
