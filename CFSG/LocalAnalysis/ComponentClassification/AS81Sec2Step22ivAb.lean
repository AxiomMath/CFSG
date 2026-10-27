module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivW
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivBad
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivWeyl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_rightConjugate {X : Subgroup G} {a y : G}
    (h : a * y * a⁻¹ ∈ normalizer (X : Set G)) :
    y ∈ normalizer (rightConjugate X a : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff,
    show a * (y * x * y⁻¹) * a⁻¹ = (a * y * a⁻¹) * (a * x * a⁻¹) * (a * y * a⁻¹)⁻¹ by group]
  exact mem_normalizer_iff.mp h _

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

omit h11 hE16 hL hodd in
theorem mem_normalizer_of_mem_normalizer_inf {y : G} (hyA : y ∈ A)
    (hy : y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G)) : y ∈ normalizer (E : Set G) := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hyR : y ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) y hyA).symm)
  rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
  exact mem_normalizer_sup hy hyR

omit h11 hE16 in
theorem pow_three_mem_centralizer_sec2P {y : G} (hy3 : y * y * y ∈ (center ↥A).map A.subtype) :
    y * y * y ∈ centralizer (sec2P E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzy⟩ := hy3
  have hzy' : (z : G) = y * y * y := hzy
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hzE : (z : G) ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
    have hza : a * z = z * a := congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha.2⟩)
    have hzr : r * z = z * r := (mem_centralizer_iff.mp (hRA hr) z z.2).symm
    calc a * r * z = a * (r * z) := by group
      _ = a * (z * r) := by rw [hzr]
      _ = z * (a * r) := by rw [← mul_assoc, hza, mul_assoc]
  have hzodd : Odd (orderOf (z : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  obtain ⟨hCEO, -, -⟩ := centralizer_eq_sup_oddCoreIn hF hL hodd
  set O := AS76b.oddCoreIn (centralizer (E : Set G))
  have hOC : O ≤ centralizer (E : Set G) := AS76b.oddCoreIn_le _
  have hON : O ≤ normalizer (E : Set G) := hOC.trans (Subgroup.centralizer_le_normalizer _)
  have hzO : (z : G) ∈ O := by
    have hz' : (z : G) ∈ ((E ⊔ O : Subgroup G) : Set G) := by rw [← hCEO]; exact hzE
    rw [coe_mul_of_right_le_normalizer_left E O hON] at hz'
    obtain ⟨e, he, o, ho, he''⟩ := hz'
    have he' : e * o = z := he''
    have hco : Commute e o := mem_centralizer_iff.mp (hOC ho) e he
    have he2 : e * e = 1 := by rw [← sq]; exact hF.elemE.2 e he
    obtain ⟨m, hm⟩ := hzodd
    have hpow : (z : G) ^ (2 * m + 1) = 1 := by rw [← hm, pow_orderOf_eq_one]
    have h1 : (z : G) ^ (2 * m + 1) = e * o ^ (2 * m + 1) := by
      rw [← he', hco.mul_pow, pow_succ, pow_mul, sq, he2, one_pow, one_mul]
    rw [hpow] at h1
    have heO : e ∈ O := by
      rw [eq_inv_of_mul_eq_one_left h1.symm]
      exact O.inv_mem (O.pow_mem ho _)
    have he1 : e = 1 := by
      have h2 : e ∈ O ⊓ E := ⟨heO, he⟩
      rwa [AS76b.oddCoreIn_inf_eq_bot (isPGroup_two_of_isElemAbelian hF.elemE), mem_bot] at h2
    rw [← he', he1, one_mul]
    exact ho
  have hNO : normalizer (E : Set G) ≤ normalizer (O : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn _ (normalizer_le_normalizer_centralizer E hn)
  have hOP : O ⊓ sec2P E = ⊥ := AS76b.oddCoreIn_inf_eq_bot (Sec2.isPGroup_sec2P E)
  have hNP : normalizer (E : Set G) ≤ normalizer (sec2P E : Set G) :=
    Sec2.normalizer_le_normalizer_sec2P E
  rw [← hzy', mem_centralizer_iff]
  intro p hp
  have h1 : (z : G) * p * (z : G)⁻¹ * p⁻¹ ∈ sec2P E :=
    (sec2P E).mul_mem ((mem_normalizer_iff.mp (hNP (hON hzO)) p).mp hp) ((sec2P E).inv_mem hp)
  have h2 : (z : G) * p * (z : G)⁻¹ * p⁻¹ ∈ O := by
    have := O.mul_mem hzO ((mem_normalizer_iff.mp (hNO (Sec2.sec2P_le E hp)) _).mp
      (O.inv_mem hzO))
    simpa [mul_assoc] using this
  have h3 : (z : G) * p * (z : G)⁻¹ * p⁻¹ = 1 := by
    have h4 : (z : G) * p * (z : G)⁻¹ * p⁻¹ ∈ O ⊓ sec2P E := ⟨h2, h1⟩
    rwa [hOP, mem_bot] at h4
  calc p * (z : G) = ((z : G) * p * (z : G)⁻¹ * p⁻¹)⁻¹ * ((z : G) * p) := by group
    _ = (z : G) * p := by rw [h3, inv_one, one_mul]

omit h11 hE16 in
theorem exists_torus_weyl_sec2 :
    ∃ y ∈ A, ∃ a ∈ A, y ∈ normalizer (E : Set G) ∧
      y ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) ∧ (∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1) ∧
      (∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) ∧ a ∈ normalizer (E : Set G) ∧
      a * y * a⁻¹ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) ∧
      ∀ w ∈ sec2Z A E F, a * w * a⁻¹ ∈ sec2Z A E F → w = 1 := by
  obtain ⟨y, hyA, a, haA, hyU, hyFA, hyfix, hy3, haU, hayF, hafix⟩ :=
    exists_torus_weyl_frame hF hL hodd
  have hyE := mem_normalizer_of_mem_normalizer_inf hF hyA hyU
  have hyF := mem_normalizer_of_mem_normalizer_inf hF.symm hyA hyFA
  have hZ := hF.sec2Z_eq
  obtain ⟨hyZ, -, -⟩ := mem_normalizer_sec2S_of_mem hF hyA hyE hyF
  have hyfixZ : ∀ w ∈ sec2Z A E F, y * w * y⁻¹ = w → w = 1 := fun w hw => hyfix w (hZ ▸ hw)
  refine ⟨y, hyA, a, haA, hyE, hyFA,
    fun u hu hfix => eq_one_of_conj_eq_of_sec2Z hF hL hodd hyA hyZ hyfixZ hu hfix,
    fun p hp => (mem_centralizer_iff.mp (pow_three_mem_centralizer_sec2P hF hL hodd hy3) p hp).symm,
    mem_normalizer_of_mem_normalizer_inf hF haA haU, hayF,
    fun w hw hmem => hafix w (hZ ▸ hw) (hZ ▸ hmem)⟩

theorem card_sec2W {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) :
    Nat.card (sec2W A E y) = 256 := by
  obtain ⟨-, -, hWP, hWE, hWEP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  obtain ⟨hEP, hPidx, -⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  have hprod := card_sup_mul_card_inf_of_le_normalizer_left (X := sec2W A E y) (N := E)
    (hWP.trans (Sec2.sec2P_le E))
  have hP : Nat.card (sec2P E) = 16 * 64 := by
    have h := relIndex_mul_card E (sec2P E)
    rw [inf_eq_left.mpr hEP, hPidx, hF.cardE] at h
    exact h.symm
  rw [hWEP, hWE, hP, card_inf_left hF hodd, hF.cardE] at hprod
  omega

theorem conjClosure_inf_sec2P_le_sec2W (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) {y : G}
    (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyFA : y ∈ normalizer ((F ⊓ A : Subgroup G) : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) :
    conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y := by
  have hEP : E ≤ sec2P E := (isElemQuot_sec2P h11 hE16 hF hL hodd).1
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  refine (sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3).2.2.2.2.2.2.2 _ inf_le_right
    (inf_normalizer_le_normalizer_inf ⟨mem_normalizer_conjClosure hyFA hyP, hyP⟩) ?_
  rw [inf_assoc, inf_eq_right.mpr hEP, conjClosure_inf_eq h11 hE16 hF hL hodd hT, hF.sec2Z_eq]
  exact fun z hz => ⟨hz.1.1, hz.2⟩

theorem rightConjugate_le_sec2W (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) {y a : G}
    (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (haA : a ∈ A)
    (haE : a ∈ normalizer (E : Set G))
    (hay : a * y * a⁻¹ ∈ normalizer ((F ⊓ A : Subgroup G) : Set G)) :
    rightConjugate (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) a ≤ sec2W A E y := by
  have haP := Sec2.normalizer_le_normalizer_sec2P E haE
  have hayE : a * y * a⁻¹ ∈ normalizer (E : Set G) := mul_mem (mul_mem haE hyE) (inv_mem haE)
  have hayP := Sec2.normalizer_le_normalizer_sec2P E hayE
  have hTE := conjClosure_inf_eq h11 hE16 hF hL hodd hT
  refine (sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3).2.2.2.2.2.2.2 _ ?_
    (mem_normalizer_rightConjugate (inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_conjClosure hay hayP, hayP⟩)) ?_
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := (mem_normalizer_iff.mp (inv_mem haP) _).mp hx.2
    simpa [mul_assoc] using this
  · intro x hx'
    obtain ⟨hx₀, hxE⟩ := mem_inf.mp hx'
    have hx := (mem_rightConjugate_iff _ _ _).mp hx₀
    have haxE : a * x * a⁻¹ ∈ E := (mem_normalizer_iff.mp haE x).mp hxE
    have hZ : a * x * a⁻¹ ∈ sec2Z A E F := by rw [← hTE]; exact ⟨hx.1, haxE⟩
    rw [hF.sec2Z_eq] at hZ
    refine ⟨hxE, ?_⟩
    have := A.mul_mem (A.mul_mem (A.inv_mem haA) hZ.2) haA
    simpa [mul_assoc] using this

theorem inf_rightConjugate_eq_bot (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) {a : G}
    (haA : a ∈ A) (haE : a ∈ normalizer (E : Set G))
    (hafix : ∀ w ∈ sec2Z A E F, a * w * a⁻¹ ∈ sec2Z A E F → w = 1) :
    (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) ⊓
      rightConjugate (conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E) a = ⊥ := by
  obtain ⟨hD, T₀, hT₀⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT₀ hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hSP := sec2S_inf_sec2P h11 hE16 hF hL hodd
  have hTS := conjClosure_le_sec2S h11 hE16 hF hL hodd
  have hTE := conjClosure_inf_eq h11 hE16 hF hL hodd hT
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hC : ∀ c ∈ conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E,
      c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := fun c hc => by
    rw [← hSP]
    exact ⟨hTS hc.1, hc.2⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx₁, hx₀⟩ := mem_inf.mp hx
  have hx₂ := (mem_rightConjugate_iff _ _ _).mp hx₀
  have hxR : x ∈ centralizer (R : Set G) := mem_centralizer_iff.mpr fun r hr => by
    have hk₁ := (mem_centralizerMod.mp (hC x hx₁)).2.2 r (mem_sup_left hr)
    have hk₂ := (mem_centralizerMod.mp (hC _ hx₂)).2.2 r (mem_sup_left hr)
    have har : a * r * a⁻¹ = r := by
      rw [mem_centralizer_iff.mp (hRA hr) a haA, mul_inv_cancel_right]
    have hk : a * (r⁻¹ * x⁻¹ * r * x) * a⁻¹ =
        r⁻¹ * (a * x * a⁻¹)⁻¹ * r * (a * x * a⁻¹) := by
      calc a * (r⁻¹ * x⁻¹ * r * x) * a⁻¹
          = (a * r * a⁻¹)⁻¹ * (a * x * a⁻¹)⁻¹ * (a * r * a⁻¹) * (a * x * a⁻¹) := by group
        _ = r⁻¹ * (a * x * a⁻¹)⁻¹ * r * (a * x * a⁻¹) := by rw [har]
    have h1 := hafix _ hk₁ (by rw [hk]; exact hk₂)
    calc r * x = r * x * (r⁻¹ * x⁻¹ * r * x)⁻¹ := by rw [h1, inv_one, mul_one]
      _ = x * r := by group
  have hxE : x ∈ E := by
    rw [← hPR]
    exact ⟨hx₁.2, Subgroup.centralizer_le_normalizer _ hxR⟩
  have hxZ : x ∈ sec2Z A E F := by rw [← hTE]; exact ⟨hx₁.1, hxE⟩
  have haxZ : a * x * a⁻¹ ∈ sec2Z A E F := by
    rw [← hTE]
    exact ⟨hx₂.1, (mem_normalizer_iff.mp haE x).mp hxE⟩
  rw [mem_bot]
  exact hafix x hxZ haxZ

theorem exists_isElemAbelian_sec2W (hT : ¬ E ⊓ A ≤ conjClosure (F ⊓ A) (sec2P E)) :
    ∃ y ∈ A, y ∈ normalizer (E : Set G) ∧ (∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1) ∧
      (∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) ∧
      conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E ≤ sec2W A E y ∧ IsElemAbelian 2 (sec2W A E y) := by
  obtain ⟨y, hyA, a, haA, hyE, hyFA, hyU, hy3, haE, hay, hafix⟩ :=
    exists_torus_weyl_sec2 hF hL hodd
  obtain ⟨-, -, hWP, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
  set W₁ := conjClosure (F ⊓ A) (sec2P E) ⊓ sec2P E with hW₁
  set W₂ := rightConjugate W₁ a with hW₂
  have h₁ : W₁ ≤ sec2W A E y :=
    conjClosure_inf_sec2P_le_sec2W h11 hE16 hF hL hodd hT hyA hyE hyFA hyU hy3
  have h₂ : W₂ ≤ sec2W A E y :=
    rightConjugate_le_sec2W h11 hE16 hF hL hodd hT hyA hyE hyU hy3 haA haE hay
  have h₁₂ : W₁ ⊓ W₂ = ⊥ := inf_rightConjugate_eq_bot h11 hE16 hF hL hodd hT haA haE hafix
  have hel₁ : IsElemAbelian 2 W₁ := isElemAbelian_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT
  have hel₂ : IsElemAbelian 2 W₂ := AS76b.isElemAbelian_rightConjugate hel₁ a
  have hc₁ : Nat.card W₁ = 16 := card_conjClosure_inf_sec2P h11 hE16 hF hL hodd hT
  have hc₂ : Nat.card W₂ = 16 := by rw [hW₂, rightConjugate_card, hc₁]
  have haP := Sec2.normalizer_le_normalizer_sec2P E haE
  have hPT := le_normalizer_conjClosure (F ⊓ A) (sec2P E)
  have hPW₁ : sec2P E ≤ normalizer (W₁ : Set G) := fun p hp =>
    inf_normalizer_le_normalizer_inf ⟨hPT hp, le_normalizer hp⟩
  have hPW₂ : sec2P E ≤ normalizer (W₂ : Set G) := fun p hp =>
    mem_normalizer_rightConjugate (hPW₁ ((mem_normalizer_iff.mp haP p).mp hp))
  have hW₁P : W₁ ≤ sec2P E := inf_le_right
  have hW₂P : W₂ ≤ sec2P E := h₂.trans hWP
  have hcomm : W₁ ≤ centralizer (W₂ : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun w hw => by
      have hk₂ : x * w * x⁻¹ * w⁻¹ ∈ W₂ :=
        W₂.mul_mem ((mem_normalizer_iff.mp (hPW₂ (hW₁P hx)) w).mp hw) (W₂.inv_mem hw)
      have hk₁ : x * w * x⁻¹ * w⁻¹ ∈ W₁ := by
        have := W₁.mul_mem hx ((mem_normalizer_iff.mp (hPW₁ (hW₂P hw)) x⁻¹).mp (W₁.inv_mem hx))
        simpa [mul_assoc] using this
      have h1 : x * w * x⁻¹ * w⁻¹ = 1 := by
        have h2 : x * w * x⁻¹ * w⁻¹ ∈ W₁ ⊓ W₂ := ⟨hk₁, hk₂⟩
        rwa [h₁₂, mem_bot] at h2
      calc w * x = (x * w * x⁻¹ * w⁻¹)⁻¹ * (x * w) := by group
        _ = x * w := by rw [h1, inv_one, one_mul]
  have hsup : W₁ ⊔ W₂ = sec2W A E y := by
    have hprod := card_sup_mul_card_inf_of_le_normalizer_left (X := W₁) (N := W₂)
      (hW₁P.trans hPW₂)
    rw [h₁₂, card_bot, hc₁, hc₂, mul_one] at hprod
    refine eq_of_le_of_card_ge (sup_le h₁ h₂) ?_
    rw [card_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3]
    omega
  refine ⟨y, hyA, hyE, hyU, hy3, h₁, ?_⟩
  rw [← hsup]
  exact isElemAbelian_sup_of_le_centralizer hel₁ hel₂ hcomm

end Frame

end CFSG.ComponentClassification.AS81
