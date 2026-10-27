module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Count
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Dich

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Helpers

variable {G : Type} [Group G]

theorem map_conj_eq_self_of_centralizes {X Q : Subgroup G} {c : G}
    (hc : ∀ x ∈ X, c * x * c⁻¹ = x) (hQ : Q ≤ X) : Q.map (MulAut.conj c).toMonoidHom = Q := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have h1 := hc _ (hQ h)
    rw [show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at h1
    rw [h1]
    exact h
  · intro h
    have h1 := hc _ (hQ h)
    have h2 : c⁻¹ * y * c = y := by
      calc c⁻¹ * y * c = c⁻¹ * (c * y * c⁻¹) * c := by rw [h1]
        _ = y := by group
    rw [h2]
    exact h

variable {A B W : Subgroup G}

end Helpers

section S1

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] in
theorem twoLift_g2YGroup_inf_bc
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (α γ : K) : twoLift ψ (g2YGroup K α γ) ⊓ twoLift ψ (g2BCGroup K) = ⊥ := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
  obtain ⟨hxA, hx2, y, hy, hyU⟩ := (mem_twoLift hψ hZ (g2YGroup_comm α γ)).1 hx₁
  obtain ⟨_, -, y', hy', hyU'⟩ := (mem_twoLift hψ hZ
    (fun u hu v hv => g2ShortRadical_comm u (g2BCGroup_le hu) v (g2BCGroup_le hv))).1 hx₂
  have hyy : y = y' := hinj (hy.symm.trans hy')
  subst hyy
  have h1 : (y : ModGL .G2 K) ∈ g2YGroup K α γ ⊓ g2BCGroup K := mem_inf.2 ⟨hyU, hyU'⟩
  rw [g2YGroup_inf_g2BCGroup, mem_bot] at h1
  have hy1 : y = 1 := Subtype.ext h1
  rw [hy1, map_one] at hy
  exact eq_of_sq_eq_one hψ hZ hxA (one_mem A) hx2 (one_pow 2) (by rw [hy]; exact (map_one ψ).symm)

theorem inf_centralizer_conj_eq (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (hZA : Odd (Nat.card (center A))) {y : G}
    (hy : rightConjugate R y ≤ R ⊔ T) (hne : rightConjugate R y ≠ R) :
    A ⊓ centralizer (rightConjugate R y : Set G) =
      A ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  have hyN : y ∉ normalizer (A : Set G) := by
    intro hyN
    apply hne
    have hKy : rightConjugate (centralizer (A : Set G)) y = centralizer (A : Set G) := by
      rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A y).2 hyN]
    have h1 : rightConjugate R y ≤ (R ⊔ T) ⊓ centralizer (A : Set G) :=
      le_inf hy (hKy ▸ map_mono hc.sylowR.le)
    rw [inf_centralizer_sec3 hc h32 h4 h34 hZA] at h1
    exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
  have hcy := sec3_of_conj hc h32 (x := 1) (x' := y) (by rw [rightConjugate_one]; exact le_sup_left)
    hy (by rwa [inv_one, mul_one])
  rw [inv_one, mul_one] at hcy
  have hsup : R ⊔ rightConjugate R y = R ⊔ T := by
    refine eq_of_le_of_card_ge (sup_le le_sup_left hy) ?_
    rw [card_sup_sec3 hcy, card_sup_sec3 hc]
  refine le_antisymm (fun a ha => ?_) (inf_le_inf_left _ (centralizer_le fun v hv => hy hv))
  obtain ⟨haA, haQ⟩ := mem_inf.1 ha
  refine mem_inf.2 ⟨haA, ?_⟩
  rw [← hsup]
  refine RankTwoClassical.mem_centralizer_sup ?_ haQ
  rw [mem_centralizer_iff]
  intro r hr
  exact (mem_centralizer_iff.1 (hc.sylowR.le hr) a haA).symm

omit [Finite K] in
theorem map_conj_le_sup_of_mem_unipStab
    (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {d : G} (hd : d ∈ unipStab A (twoLift ψ (g2ShortRadical K)) (twoLift ψ (g2BCGroup K)))
    {Q : Subgroup G} (hQ : Q ≤ R ⊔ twoLift ψ (g2ShortRadical K)) :
    Q.map (MulAut.conj d).toMonoidHom ≤ Q ⊔ twoLift ψ (g2BCGroup K) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, b, hb, hrb⟩ := exists_mul_of_mem_sup_twoLift hc _ (hQ hx)
  have hdr : d * r * d⁻¹ = r := by
    rw [mem_centralizer_iff.1 (hc.sylowR.le hr) d hd.1, mul_inv_cancel_right]
  have hw := hd.2.2.1 b hb
  have hwb : (d * b * d⁻¹ * b⁻¹) * b = b * (d * b * d⁻¹ * b⁻¹) :=
    commute_of_mem_twoLift hψ hZ g2ShortRadical_comm (twoLift_mono g2BCGroup_le hw) hb
  have e : d * x * d⁻¹ = x * (d * b * d⁻¹ * b⁻¹) := by
    rw [← hrb]
    calc d * (r * b) * d⁻¹ = (d * r * d⁻¹) * ((d * b * d⁻¹ * b⁻¹) * b) := by group
      _ = r * (b * (d * b * d⁻¹ * b⁻¹)) := by rw [hdr, hwb]
      _ = r * b * (d * b * d⁻¹ * b⁻¹) := by group
  change d * x * d⁻¹ ∈ Q ⊔ twoLift ψ (g2BCGroup K)
  rw [e]
  exact mul_mem (mem_sup_left hx) (mem_sup_right hw)

theorem sup_bc_inf_le
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (α γ : K) :
    (R ⊔ twoLift ψ (g2BCGroup K)) ⊓ (R ⊔ twoLift ψ (g2YGroup K α γ)) ≤ R := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
  obtain ⟨r₁, hr₁, w, hw, rfl⟩ := exists_mul_of_mem_sup_twoLift hc _ hx₁
  obtain ⟨r₂, hr₂, z, hz, he⟩ := exists_mul_of_mem_sup_twoLift hc _ hx₂
  have hrr : r₂⁻¹ * r₁ = z * w⁻¹ := by
    calc r₂⁻¹ * r₁ = r₂⁻¹ * (r₁ * w) * w⁻¹ := by group
      _ = r₂⁻¹ * (r₂ * z) * w⁻¹ := by rw [he]
      _ = z * w⁻¹ := by group
  have hrA : r₂⁻¹ * r₁ ∈ R ⊓ A :=
    mem_inf.2 ⟨mul_mem (inv_mem hr₂) hr₁, by
      rw [hrr]; exact mul_mem (twoLift_le hz) (inv_mem (twoLift_le hw))⟩
  rw [inf_eq_bot_sec3 hc hZA, mem_bot, hrr, mul_inv_eq_one] at hrA
  have hw1 : w = 1 := by
    have h1 : w ∈ twoLift ψ (g2YGroup K α γ) ⊓ twoLift ψ (g2BCGroup K) :=
      mem_inf.2 ⟨hrA ▸ hz, hw⟩
    rwa [twoLift_g2YGroup_inf_bc hZA hψ α γ, mem_bot] at h1
  rw [hw1, mul_one]
  exact hr₁

end S1

section S1Main

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem g2_short_inf_false
    {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) (hTp : G2Pinned ψ T g2v)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v))
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c))
    (h2tr : ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ R ⊔ T → rightConjugate R x₂ ≤ R ⊔ T →
      rightConjugate R x₁' ≤ R ⊔ T → rightConjugate R x₂' ≤ R ⊔ T →
      rightConjugate R x₁ ≠ rightConjugate R x₂ →
      rightConjugate R x₁' ≠ rightConjugate R x₂' →
      ∃ n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G),
        rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
          rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂') : False := by
  classical
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set B := twoLift ψ (g2ShortRadical K) with hBdef
  set W := twoLift ψ (g2BCGroup K) with hWdef
  set M := CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) with hMdef
  have hWM : oTwoIn M = W := oTwoIn_perfectCore_eq h4 h32 h184s hK4 hc hZA hψ hTp hTv
  have hRB : R ⊔ B = (R ⊔ T) ⊔ oTwoIn M :=
    sup_twoLift_radical h4 h32 h184s hK4 hc hZA hψ hRq hTp hTv
  have hVRB : R ⊔ T ≤ R ⊔ B := by rw [hRB]; exact le_sup_left
  have hV00 : R ⊔ T = R ⊔ twoLift ψ (g2YGroup K 0 0) := by
    rw [g2YGroup_zero, ← inf_eq_twoLift_of_actsIn h4 h32 hc hZA hψ hRq hTv,
      sup_inf_sec3 hc h32 h4 h34]
  obtain ⟨xT, hxT, hAxT⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hRneT : R ≠ T := by
    intro h
    apply hc.R_ne_bot
    have h1 := hc.inf_eq_bot
    rwa [← h, inf_idem] at h1
  have hcentR : ∀ a ∈ A, R.map (MulAut.conj a).toMonoidHom = R := by
    intro a ha
    refine map_conj_eq_self_of_centralizes (X := R) (fun r hr => ?_) le_rfl
    rw [mem_centralizer_iff.1 (hc.sylowR.le hr) a ha, mul_inv_cancel_right]
  set H : Subgroup G := normalizer ((R ⊔ B : Subgroup G) : Set G) ⊓ normalizer (W : Set G)
    with hHdef
  let Ω := {Q : Subgroup G // Q ≤ R ⊔ B ∧ ∃ x : G, Q = rightConjugate R x}
  have hmapΩ : ∀ (h : H) (Q : Ω), Q.1.map (MulAut.conj (h : G)).toMonoidHom ≤ R ⊔ B ∧
      ∃ x : G, Q.1.map (MulAut.conj (h : G)).toMonoidHom = rightConjugate R x := by
    rintro ⟨h, hhRB, -⟩ ⟨Q, hQ, x, rfl⟩
    refine ⟨?_, x * h⁻¹, by rw [map_conj_eq_rightConjugate, rightConjugate_mul]⟩
    have h1 := map_mono (f := (MulAut.conj h).toMonoidHom) hQ
    have h2 : (R ⊔ B).map (MulAut.conj h).toMonoidHom = R ⊔ B :=
      (mem_normalizer_iff_map_conj_eq).1 hhRB
    rwa [h2] at h1
  let _ : MulAction H Ω :=
    { smul := fun h Q => ⟨Q.1.map (MulAut.conj (h : G)).toMonoidHom, hmapΩ h Q⟩
      one_smul := fun Q => Subtype.ext (map_conj_one Q.1)
      mul_smul := fun h₁ h₂ Q => Subtype.ext (map_conj_mul Q.1 h₁ h₂).symm }
  have hsmul : ∀ (h : H) (Q : Ω),
      ((h • Q : Ω) : Subgroup G) = Q.1.map (MulAut.conj (h : G)).toMonoidHom := fun _ _ => rfl
  let R₀ : Ω := ⟨R, le_sup_left, 1, (rightConjugate_one R).symm⟩
  let T₀ : Ω := ⟨T, le_sup_right.trans hVRB, xT, hxT⟩
  have hDH : unipStab A B W ≤ H := by
    intro d hd
    have hdR : d ∈ centralizer (R : Set G) := by
      rw [mem_centralizer_iff]
      intro r hr
      exact (mem_centralizer_iff.1 (hc.sylowR.le hr) d hd.1).symm
    refine mem_inf.2 ⟨RankTwoClassical.mem_normalizer_sup (centralizer_le_normalizer _ hdR)
      hd.2.1, centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)⟩
    exact (hd.2.2.2 w hw).symm
  have hnH : ∀ n y : G, n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) →
      rightConjugate R y ≤ R ⊔ T → rightConjugate R y ≠ R →
      rightConjugate R n = rightConjugate R y → rightConjugate T n = R → n ∈ H := by
    intro n y hnV hy hyne hRn hTn
    have hAgn : rightConjugate (rightConjugate A g) n = A := by
      rw [← hAxT, rightConjugate_mul]
      apply (rightConjugate_eq_self_iff A (xT * n)).2
      have h1 : xT * n ∈ normalizer (R : Set G) := by
        rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← hxT, hTn]
      have h2 := Lemma36.normalizer_le hc.hyp hc.sylowR 1 (by rwa [rightConjugate_one])
      rwa [rightConjugate_one] at h2
    have hM' : M = CFSG.Quasithin.perfectCore (rightConjugate A g ⊓ centralizer (R : Set G)) :=
      hc.perfectCore_eq h32 h4 h34 hOut
    have hTV : A ⊓ centralizer (T : Set G) =
        A ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
      have h1 := inf_centralizer_conj_eq hc h32 h4 h34 hZA (y := xT)
        (by rw [← hxT]; exact le_sup_right) (by rw [← hxT]; exact hRneT.symm)
      rwa [← hxT] at h1
    have hMn : rightConjugate M n = M := by
      calc rightConjugate M n = CFSG.Quasithin.perfectCore
            (rightConjugate (rightConjugate A g ⊓ centralizer (R : Set G)) n) := by
            rw [hM', RankTwoClassical.rightConjugate_perfectCore]
        _ = CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R y : Set G)) := by
            rw [RankTwoClassical.rightConjugate_inf, ← centralizer_rightConjugate, hAgn, hRn]
        _ = M := by rw [inf_centralizer_conj_eq hc h32 h4 h34 hZA hy hyne, ← hTV]
    have hnM : n ∈ normalizer (M : Set G) := (rightConjugate_eq_self_iff M n).1 hMn
    have hnW : n ∈ normalizer (W : Set G) := hWM ▸ mem_normalizer_oTwoIn hnM
    refine mem_inf.2 ⟨?_, hnW⟩
    rw [hRB]
    exact RankTwoClassical.mem_normalizer_sup hnV (mem_normalizer_oTwoIn hnM)
  have hreach : ∀ Q : Ω, ∃ h : H, h • R₀ = Q := by
    intro Q
    by_cases hQR : Q.1 = R
    · exact ⟨1, by rw [one_smul]; exact Subtype.ext hQR.symm⟩
    · obtain ⟨y, hy⟩ := Q.2.2
      have hyB : rightConjugate R y ≤ R ⊔ B := hy ▸ Q.2.1
      have hyne : rightConjugate R y ≠ R := hy ▸ hQR
      obtain ⟨α, γ, hαγ⟩ :=
        le_sup_lift_of_conj h4 h32 h184 h184s hK4 hc hOut hZA hψ hnolong hyB hyne
      rw [← hy] at hαγ
      obtain ⟨u, huD, hu⟩ := exists_lift_ru hZA hψ α γ
      have huA : u ∈ A := huD.1
      have hmapV : (R ⊔ T).map (MulAut.conj u).toMonoidHom =
          R ⊔ twoLift ψ (g2YGroup K α γ) := by
        rw [hV00, Subgroup.map_sup, hcentR u huA, hu]
      have hQ0y : Q.1.map (MulAut.conj u⁻¹).toMonoidHom = rightConjugate R (y * u) := by
        rw [hy, map_conj_eq_rightConjugate, inv_inv, rightConjugate_mul]
      have hQ0 : rightConjugate R (y * u) ≤ R ⊔ T := by
        rw [← hQ0y]
        have h1 := map_mono (f := (MulAut.conj u⁻¹).toMonoidHom) hαγ
        rwa [← hmapV, map_conj_mul, inv_mul_cancel, map_conj_one] at h1
      have hQ0ne : rightConjugate R (y * u) ≠ R := by
        intro h
        apply hQR
        have h1 : Q.1 = (Q.1.map (MulAut.conj u⁻¹).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by
          rw [map_conj_mul, mul_inv_cancel, map_conj_one]
        rw [h1, hQ0y, h, hcentR u huA]
      obtain ⟨n, hnV, hn1, hn2⟩ := h2tr 1 xT (y * u) 1
        (by rw [rightConjugate_one]; exact le_sup_left) (by rw [← hxT]; exact le_sup_right) hQ0
        (by rw [rightConjugate_one]; exact le_sup_left)
        (by rw [rightConjugate_one, ← hxT]; exact hRneT) (by rw [rightConjugate_one]; exact hQ0ne)
      rw [rightConjugate_one] at hn1 hn2
      rw [← hxT] at hn2
      have hn : n ∈ H := hnH n (y * u) hnV hQ0 hQ0ne hn1 hn2
      refine ⟨⟨u, hDH huD⟩ * ⟨n, hn⟩⁻¹, Subtype.ext ?_⟩
      rw [hsmul]
      change R.map (MulAut.conj (u * n⁻¹)).toMonoidHom = Q.1
      rw [← map_conj_mul, map_conj_eq_rightConjugate R n⁻¹, inv_inv, hn1, ← hQ0y, map_conj_mul,
        mul_inv_cancel, map_conj_one]
  have hfib : ∀ Q : Subgroup G, Q ≤ R ⊔ B → (∃ x : G, Q = rightConjugate R x) →
      Q ⊔ W = R ⊔ W → Q = R := by
    rintro Q hQB ⟨y, rfl⟩ hQ
    by_contra hQR
    obtain ⟨α, γ, hαγ⟩ :=
      le_sup_lift_of_conj h4 h32 h184 h184s hK4 hc hOut hZA hψ hnolong hQB hQR
    have hle : rightConjugate R y ≤ R := by
      refine le_trans (le_inf ?_ hαγ) (sup_bc_inf_le hc hZA hψ α γ)
      rw [← hQ]
      exact le_sup_left
    exact hQR (eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))
  obtain ⟨a₁, ha₁A, -, ha₁D, ha₁Y⟩ := exists_lift_r_mem hZA hψ (1 : K)
  have hTB : T ≤ R ⊔ B := le_sup_right.trans hVRB
  have hneT : T.map (MulAut.conj a₁).toMonoidHom ≠ T := by
    intro h
    have hmap : (R ⊔ T).map (MulAut.conj a₁).toMonoidHom = R ⊔ twoLift ψ (g2YGroup K 1 0) := by
      rw [hV00, Subgroup.map_sup, hcentR a₁ ha₁A, ha₁Y, zero_add]
    have hT1 : T ≤ R ⊔ twoLift ψ (g2YGroup K 1 0) := by
      have h2 : T.map (MulAut.conj a₁).toMonoidHom ≤ (R ⊔ T).map (MulAut.conj a₁).toMonoidHom :=
        map_mono le_sup_right
      rwa [h, hmap] at h2
    have hT0 : T ≤ R ⊔ twoLift ψ (g2YGroup K 0 0) := by
      rw [← hV00]
      exact le_sup_right
    have hTR : T ≤ R := (le_inf hT0 hT1).trans (sup_lift_inf_le hc hZA hψ (Or.inl zero_ne_one))
    apply hc.T_ne_bot
    refine eq_bot_iff.2 fun t ht => ?_
    have h1 : t ∈ R ⊓ T := mem_inf.2 ⟨hTR ht, ht⟩
    rwa [hc.inf_eq_bot] at h1
  have hT₁B : T.map (MulAut.conj a₁).toMonoidHom ≤ R ⊔ B := by
    have h1 := map_mono (f := (MulAut.conj a₁).toMonoidHom) hTB
    have h2 : (R ⊔ B).map (MulAut.conj a₁).toMonoidHom = R ⊔ B :=
      (mem_normalizer_iff_map_conj_eq).1 (mem_inf.1 (hDH ha₁D)).1
    rwa [h2] at h1
  have hmapT : T.map (MulAut.conj a₁).toMonoidHom ⊔ W = T ⊔ W := by
    refine le_antisymm (sup_le (map_conj_le_sup_of_mem_unipStab hc hZA hψ ha₁D hTB)
      le_sup_right) (sup_le ?_ le_sup_right)
    have h1 := map_conj_le_sup_of_mem_unipStab hc hZA hψ (inv_mem ha₁D) hT₁B
    rwa [map_conj_mul, inv_mul_cancel, map_conj_one] at h1
  obtain ⟨h, hh⟩ := hreach T₀
  have hhT : R.map (MulAut.conj (h : G)).toMonoidHom = T := congrArg Subtype.val hh
  have hhRB : (R ⊔ B).map (MulAut.conj (h : G)⁻¹).toMonoidHom = R ⊔ B :=
    (mem_normalizer_iff_map_conj_eq).1 (inv_mem (mem_inf.1 h.2).1)
  have hhW : W.map (MulAut.conj (h : G)⁻¹).toMonoidHom = W :=
    (mem_normalizer_iff_map_conj_eq).1 (inv_mem (mem_inf.1 h.2).2)
  set Q := (T.map (MulAut.conj a₁).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom
    with hQdef
  have hQB : Q ≤ R ⊔ B := by
    have h1 := map_mono (f := (MulAut.conj (h : G)⁻¹).toMonoidHom) hT₁B
    rwa [hhRB] at h1
  have hQx : ∃ x : G, Q = rightConjugate R x := by
    refine ⟨xT * (a₁⁻¹ * (h : G)), ?_⟩
    rw [hQdef, hxT, map_conj_eq_rightConjugate, map_conj_eq_rightConjugate, rightConjugate_mul,
      rightConjugate_mul, inv_inv]
  have hQW : Q ⊔ W = R ⊔ W := by
    calc Q ⊔ W = (T.map (MulAut.conj a₁).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom ⊔
          W.map (MulAut.conj (h : G)⁻¹).toMonoidHom := by rw [hhW]
      _ = (T.map (MulAut.conj a₁).toMonoidHom ⊔ W).map (MulAut.conj (h : G)⁻¹).toMonoidHom :=
          (Subgroup.map_sup _ _ _).symm
      _ = (T ⊔ W).map (MulAut.conj (h : G)⁻¹).toMonoidHom := by rw [hmapT]
      _ = R ⊔ W := by
          rw [Subgroup.map_sup, hhW, ← hhT, map_conj_mul, inv_mul_cancel, map_conj_one]
  have hQR := hfib Q hQB hQx hQW
  apply hneT
  calc T.map (MulAut.conj a₁).toMonoidHom = Q.map (MulAut.conj (h : G)).toMonoidHom := by
        rw [hQdef, map_conj_mul, mul_inv_cancel, map_conj_one]
    _ = R.map (MulAut.conj (h : G)).toMonoidHom := by rw [hQR]
    _ = T := hhT

end S1Main

end CFSG.ComponentClassification.RankTwoExceptional
