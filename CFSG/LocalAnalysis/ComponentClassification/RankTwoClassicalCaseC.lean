module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalReduce

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem sec3_of_le (h32 : Lemma32) (hZ : Odd (Nat.card (center ↥A))) {x : G}
    (hxA : rightConjugate R x ≤ A) : Sec3 A R (rightConjugate R x) x := by
  obtain ⟨s, hs, hs1⟩ := (rightConjugate R x).bot_or_exists_ne_one.resolve_left (by
    intro h
    apply hc.R_ne_bot
    have hcd := rightConjugate_card R x
    rw [h, card_bot] at hcd
    exact card_eq_one.mp hcd.symm)
  have hxR : rightConjugate R x ≤ centralizer (R : Set G) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro r hr
    exact (hc.commute_of_mem (hxA hu) hr).eq.symm
  have hs2 : s ^ 2 = 1 := (isElemAbelian_rightConjugate (hc.elemR h32) x).2 s hs
  exact sec3_of_conj hc.hyp hc.sylowR hZ hxR hs (hxA hs) (by rw [inv_mul_cancel]; exact one_mem _)
    hs1 hs2

theorem commute_mul_R (h32 : Lemma32) {α β r r' : G} (hα : α ∈ A) (hβ : β ∈ A)
    (hαβ : Commute α β) (hr : r ∈ R) (hr' : r' ∈ R) : Commute (α * r) (β * r') :=
  (hαβ.mul_right (hc.commute_of_mem hα hr')).mul_left
    ((hc.commute_of_mem hβ hr).symm.mul_right (hc.commute_R h32 hr hr'))

theorem exists_ne_ne : ∃ t₁ ∈ T, t₁ ≠ 1 ∧ ∃ t₂ ∈ T, t₂ ≠ 1 ∧ t₁ ≠ t₂ := by
  classical
  have hT4 : 4 ≤ Nat.card T := hc.card_eq ▸ hc.four_le
  have := Fintype.ofFinite ↥T
  have hcardT : 1 < ((Finset.univ : Finset ↥T).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨⟨t₁, ht₁⟩, ht₁', ⟨t₂, ht₂⟩, ht₂', ht₁₂⟩ := Finset.one_lt_card.mp hcardT
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at ht₁' ht₂'
  exact ⟨t₁, ht₁, fun h => ht₁' (Subtype.ext h), t₂, ht₂, fun h => ht₂' (Subtype.ext h),
    fun h => ht₁₂ (Subtype.ext h)⟩

theorem aPart_sq (h32 : Lemma32) {u p : G} (hu : u ∈ T) (hρ : u⁻¹ * p ∈ R) : p ^ 2 = 1 := by
  have hcomm : Commute u (u⁻¹ * p) := hc.commute_T_R hu hρ
  rw [show p = u * (u⁻¹ * p) by group, hcomm.mul_pow, (hc.elemT h32).2 u hu,
    (hc.elemR h32).2 _ hρ, one_mul]

theorem caseC_core (I : Inputs74) (hZ : Odd (Nat.card (center ↥A))) (D : ClassicalModel A)
    {n : ℕ} {J : Subgroup G} (hle : ∀ u ∈ T, ∀ p' ∈ A, u⁻¹ * p' ∈ R → p' ∈ J) {a : G}
    (haA : a ∈ A) (hcomm : ∀ j ∈ J, ∀ j' ∈ J, Commute j (a⁻¹ * j' * a))
    (hJa : ∀ j ∈ J, ∀ j' ∈ J, j = a⁻¹ * j' * a → j = 1) {t₁ t₂ : G} (ht₁ : t₁ ∈ T)
    (ht₂ : t₂ ∈ T) (ht₁₂ : t₁ ≠ t₂)
    (hφ : ∀ u ∈ T, u ≠ 1 → ∀ p' ∈ A, u⁻¹ * p' ∈ R → Smaller D n (p' * (a⁻¹ * p' * a)))
    (hσ : ∀ p₁ ∈ A, t₁⁻¹ * p₁ ∈ R → ∀ p₂ ∈ A, t₂⁻¹ * p₂ ∈ R →
      Smaller D n (p₂ * (a⁻¹ * p₁ * a)))
    (hcov : rightConjugate T a ≤ centralizer (T : Set G) → rightConjugate T a ≠ T →
      rightConjugate T a = sec3V T (rightConjugate T a) ⊓ rightConjugate A g ∨
      ∀ v ∈ sec3V T (rightConjugate T a), v ∉ rightConjugate A g →
        ∃ y : G, rightConjugate T y ≤ sec3V T (rightConjugate T a) ∧ v ∈ rightConjugate T y)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A) :
    ∃ (T' : Subgroup G) (x : G), Sec3 A R T' x ∧
      ∃ s ∈ T', s ≠ 1 ∧ ∃ q ∈ A, s⁻¹ * q ∈ R ∧ Smaller D n q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT := hc.inf_eq_bot
  have hconjA : ∀ x ∈ A, a⁻¹ * x * a ∈ A := fun x hx => mul_mem (mul_mem (inv_mem haA) hx) haA
  have hone : ∀ u ∈ T, u⁻¹ ∈ R → u = 1 := by
    intro u hu hu'
    have : u ∈ R ⊓ T := mem_inf.mpr ⟨by simpa using inv_mem hu', hu⟩
    rwa [hRT, mem_bot] at this
  have hmemc : ∀ u ∈ T, a⁻¹ * u * a ∈ rightConjugate T a := by
    intro u hu
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hu
  have hcen : rightConjugate T a ≤ centralizer (T : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro u hu
    rw [mem_rightConjugate_iff] at hv
    set u' := a * v * a⁻¹ with hu'
    have hv' : v = a⁻¹ * u' * a := by rw [hu']; group
    obtain ⟨p₁, hp₁, hρ₁⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hu
    obtain ⟨p₂, hp₂, hρ₂⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hv
    have h1 := hc.aPart_conj hρ₂ haA
    rw [← hv'] at h1
    have e1 : u = p₁ * (u⁻¹ * p₁)⁻¹ := by group
    have e2 : v = (a⁻¹ * p₂ * a) * (v⁻¹ * (a⁻¹ * p₂ * a))⁻¹ := by group
    have h3 := hc.commute_mul_R I.h32 hp₁ (hconjA p₂ hp₂)
      (hcomm p₁ (hle u hu p₁ hp₁ hρ₁) p₂ (hle u' hv p₂ hp₂ hρ₂)) (inv_mem hρ₁) (inv_mem h1)
    rw [← e1, ← e2] at h3
    exact h3.eq
  have hinf : T ⊓ rightConjugate T a = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvT, hva⟩ := mem_inf.mp hv
    rw [mem_rightConjugate_iff] at hva
    set u := a * v * a⁻¹ with hu
    have hv' : v = a⁻¹ * u * a := by rw [hu]; group
    obtain ⟨pv, hpv, hρv⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hvT
    obtain ⟨pu, hpu, hρu⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hva
    have h1 := hc.aPart_conj hρu haA
    rw [← hv'] at h1
    have h2 := hc.aPart_unique hZ hpv hρv (hconjA pu hpu) h1
    have h3 := hJa pv (hle v hvT pv hpv hρv) pu (hle u hva pu hpu hρu) h2
    rw [mem_bot]
    apply hone v hvT
    rwa [h3, mul_one] at hρv
  have hne : rightConjugate T a ≠ T := by
    intro heq
    apply hc.T_ne_bot
    rw [← inf_idem T]
    conv_lhs => rw [show T ⊓ T = T ⊓ rightConjugate T a by rw [heq]]
    exact hinf
  obtain ⟨w, hw⟩ := hc.exists_conj
  rcases hcov hcen hne with h1 | hcov
  · exfalso
    have hle' : rightConjugate T (a * g⁻¹) ≤ A := by
      rw [← rightConjugate_mul, rightConjugate_le_iff, inv_inv, h1]
      exact inf_le_right
    have hRx : rightConjugate T (a * g⁻¹) = rightConjugate R (w * (a * g⁻¹)) := by
      rw [hw, rightConjugate_mul]
    rw [hRx] at hle'
    exact hno _ _ (hc.sec3_of_le I.h32 hZ hle') hle'
  set S₂ := (T ⊔ rightConjugate T a) ⊓ rightConjugate A g with hS₂
  have hTN : T ≤ normalizer (S₂ : Set G) := by
    intro u hu
    refine mem_normalizer_inf (Subgroup.le_normalizer (mem_sup_left hu)) ?_
    have hK : u ∈ rightConjugate (centralizer (A : Set G)) g := hc.sylowT.le hu
    rw [← centralizer_rightConjugate] at hK
    exact centralizer_le_normalizer _ hK
  have hS₂T : S₂ ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hc.T_inf_conj hZ]
    intro u hu
    exact mem_inf.mpr ⟨(mem_inf.mp hu).2, (mem_inf.mp (mem_inf.mp hu).1).2⟩
  have hcardS : Nat.card S₂ ≤ Nat.card T := by
    have h1 := card_sup_eq_mul hTN hS₂T
    have h2 : Nat.card ↥(S₂ ⊔ T) ≤ Nat.card ↥(T ⊔ rightConjugate T a) :=
      card_le_of_le (sup_le inf_le_left le_sup_left)
    rw [card_sup_eq_mul (hcen.trans (centralizer_le_normalizer _)) hinf,
      rightConjugate_card] at h2
    have hT0 : 0 < Nat.card T := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (h1 ▸ h2) hT0
  have hout : ∃ s ∈ T ⊔ rightConjugate T a, s ∉ rightConjugate A g ∧
      ∃ q ∈ A, s⁻¹ * q ∈ R ∧ q ≠ 1 ∧ q ^ 2 = 1 ∧ Smaller D n q := by
    by_contra hno'
    push Not at hno'
    have hsq : ∀ x ∈ J, ∀ y ∈ J, x ^ 2 = 1 → y ^ 2 = 1 → (x * (a⁻¹ * y * a)) ^ 2 = 1 := by
      intro x hx y hy hx2 hy2
      rw [(hcomm x hx y hy).mul_pow, hx2, one_mul, sq, show a⁻¹ * y * a * (a⁻¹ * y * a) =
        a⁻¹ * (y * y) * a by group, ← sq, hy2]
      group
    have hne1 : ∀ x ∈ J, ∀ y ∈ J, x * (a⁻¹ * y * a) = 1 → x = 1 ∧ y = 1 := by
      intro x hx y hy h
      have h2 : x = a⁻¹ * y⁻¹ * a := by
        rw [show a⁻¹ * y⁻¹ * a = (a⁻¹ * y * a)⁻¹ by group]
        exact eq_inv_of_mul_eq_one_left h
      have h3 := hJa x hx _ (inv_mem hy) h2
      refine ⟨h3, ?_⟩
      rw [h3, one_mul] at h
      calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hφA : ∀ u ∈ T, ∀ p' ∈ A, u⁻¹ * p' ∈ R →
        (u * (a⁻¹ * u * a))⁻¹ * (p' * (a⁻¹ * p' * a)) ∈ R := fun u _ p' hp' hρ' =>
      hc.aPart_mul hρ' (hc.aPart_conj hρ' haA) (hconjA p' hp')
    have hφmem : ∀ u ∈ T, u * (a⁻¹ * u * a) ∈ S₂ := by
      intro u hu
      refine mem_inf.mpr ⟨mul_mem (mem_sup_left hu) (mem_sup_right (hmemc u hu)), ?_⟩
      by_cases hu1 : u = 1
      · subst hu1
        simp
      by_contra hφ'
      obtain ⟨p', hp', hρ'⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hu
      have hJ := hle u hu p' hp' hρ'
      have h2 := hc.aPart_sq I.h32 hu hρ'
      refine hno' _ (mul_mem (mem_sup_left hu) (mem_sup_right (hmemc u hu))) hφ' _
        (mul_mem hp' (hconjA p' hp')) (hφA u hu p' hp' hρ') (fun h => hu1 ?_)
        (hsq p' hJ p' hJ h2 h2) (hφ u hu hu1 p' hp' hρ')
      apply hone u hu
      rw [(hne1 p' hJ p' hJ h).1, mul_one] at hρ'
      exact hρ'
    obtain ⟨p₁, hp₁, hρ₁⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht₁
    obtain ⟨p₂, hp₂, hρ₂⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht₂
    have hp₁J := hle t₁ ht₁ p₁ hp₁ hρ₁
    have hp₂J := hle t₂ ht₂ p₂ hp₂ hρ₂
    have hσA : p₂ * (a⁻¹ * p₁ * a) ∈ A := mul_mem hp₂ (hconjA p₁ hp₁)
    have hσρ : (t₂ * (a⁻¹ * t₁ * a))⁻¹ * (p₂ * (a⁻¹ * p₁ * a)) ∈ R :=
      hc.aPart_mul hρ₂ (hc.aPart_conj hρ₁ haA) (hconjA p₁ hp₁)
    have hp₁₂ : p₁ = p₂ → False := by
      intro h
      apply ht₁₂
      have h1 : t₁⁻¹ * t₂ ∈ R := by
        have := mul_mem hρ₁ (inv_mem hρ₂)
        rw [h] at this
        simpa [mul_assoc] using this
      have h2 : t₁⁻¹ * t₂ ∈ R ⊓ T := mem_inf.mpr ⟨h1, mul_mem (inv_mem ht₁) ht₂⟩
      rw [hRT, mem_bot] at h2
      calc t₁ = t₁ * (t₁⁻¹ * t₂) := by rw [h2, mul_one]
        _ = t₂ := by group
    have hσmem : t₂ * (a⁻¹ * t₁ * a) ∈ S₂ := by
      refine mem_inf.mpr ⟨mul_mem (mem_sup_left ht₂) (mem_sup_right (hmemc t₁ ht₁)), ?_⟩
      by_contra hσ'
      refine hno' _ (mul_mem (mem_sup_left ht₂) (mem_sup_right (hmemc t₁ ht₁))) hσ' _ hσA hσρ
        (fun h => ?_) (hsq p₂ hp₂J p₁ hp₁J (hc.aPart_sq I.h32 ht₂ hρ₂)
          (hc.aPart_sq I.h32 ht₁ hρ₁)) (hσ p₁ hp₁ hρ₁ p₂ hp₂ hρ₂)
      obtain ⟨h1, h2⟩ := hne1 p₂ hp₂J p₁ hp₁J h
      exact hp₁₂ (h2.trans h1.symm)
    let f : ↥T → ↥S₂ := fun u => ⟨u * (a⁻¹ * u * a), hφmem u u.2⟩
    have hinj : Function.Injective f := by
      intro u u' huu
      have h1 : (u : G) * (a⁻¹ * u * a) = u' * (a⁻¹ * u' * a) := congrArg Subtype.val huu
      have h2 : (u' : G)⁻¹ * u = a⁻¹ * ((u' : G) * (u : G)⁻¹) * a := by
        calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * (a⁻¹ * u * a)) * (a⁻¹ * u * a)⁻¹ := by group
          _ = (u' : G)⁻¹ * (u' * (a⁻¹ * u' * a)) * (a⁻¹ * u * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * ((u' : G) * (u : G)⁻¹) * a := by group
      have h3 : (u' : G)⁻¹ * u ∈ T ⊓ rightConjugate T a := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem u'.2) u.2, ?_⟩
        rw [h2]
        exact hmemc _ (mul_mem u'.2 (inv_mem u.2))
      rw [hinf, mem_bot] at h3
      apply Subtype.ext
      calc (u : G) = u' * ((u' : G)⁻¹ * u) := by group
        _ = u' := by rw [h3, mul_one]
    obtain ⟨u₀, hu₀⟩ := (hinj.bijective_of_nat_card_le hcardS).2 ⟨_, hσmem⟩
    have heq : (u₀ : G) * (a⁻¹ * u₀ * a) = t₂ * (a⁻¹ * t₁ * a) := congrArg Subtype.val hu₀
    obtain ⟨p₀, hp₀, hρ₀⟩ := hc.exists_aPart I.h32 I.h4 I.h34 u₀.2
    have hp₀J := hle _ u₀.2 p₀ hp₀ hρ₀
    have h1 := hφA _ u₀.2 p₀ hp₀ hρ₀
    rw [heq] at h1
    have h2 := hc.aPart_unique hZ hσA hσρ (mul_mem hp₀ (hconjA p₀ hp₀)) h1
    have h3 : p₀⁻¹ * p₂ = a⁻¹ * (p₀ * p₁⁻¹) * a := by
      calc p₀⁻¹ * p₂ = p₀⁻¹ * (p₂ * (a⁻¹ * p₁ * a)) * (a⁻¹ * p₁ * a)⁻¹ := by group
        _ = p₀⁻¹ * (p₀ * (a⁻¹ * p₀ * a)) * (a⁻¹ * p₁ * a)⁻¹ := by rw [h2]
        _ = a⁻¹ * (p₀ * p₁⁻¹) * a := by group
    have h4 := hJa _ (mul_mem (inv_mem hp₀J) hp₂J) _ (mul_mem hp₀J (inv_mem hp₁J)) h3
    rw [h4] at h3
    have h5 : p₀ * p₁⁻¹ = 1 := by
      calc p₀ * p₁⁻¹ = a * (a⁻¹ * (p₀ * p₁⁻¹) * a) * a⁻¹ := by group
        _ = 1 := by rw [← h3]; group
    exact hp₁₂ ((mul_inv_eq_one.mp h5).symm.trans (eq_of_inv_mul_eq_one h4))
  obtain ⟨s, hsV, hsA, q, hqA, hqρ, hq1, hq2, hqs⟩ := hout
  obtain ⟨y, hyV, hsy⟩ := hcov s (le_sec3V_of ⟨a, rfl⟩ hsV) hsA
  have hRW : R ≤ sec3W T (rightConjugate T a) := by
    have hR : R = rightConjugate T w⁻¹ := by rw [hw, rightConjugate_rightConjugate_inv]
    have hRC : R ≤ centralizer ((T ⊔ rightConjugate T a : Subgroup G) : Set G) := by
      refine le_centralizer_sup (le_centralizer_iff.mp hc.le_centralizer) ?_
      intro r hr
      rw [mem_centralizer_iff]
      intro v hv
      rw [SetLike.mem_coe, mem_rightConjugate_iff] at hv
      have h1 : Commute (a * v * a⁻¹) r := hc.commute_T_R hv hr
      have h2 : Commute a r := hc.commute_of_mem haA hr
      have h3 : Commute (a⁻¹ * (a * v * a⁻¹) * a) r := (h2.inv_left.mul_left h1).mul_left h2
      rw [show a⁻¹ * (a * v * a⁻¹) * a = v by group] at h3
      exact h3.eq
    rw [hR] at hRC ⊢
    exact le_sec3W hRC
  have hyR : rightConjugate T y ≤ centralizer (R : Set G) :=
    hyV.trans ((sec3V_le_centralizer _ _).trans (centralizer_le hRW))
  have hRy : rightConjugate T y = rightConjugate R (w * y) := by rw [hw, rightConjugate_mul]
  refine ⟨rightConjugate T y, w * y, ?_, s, hsy, ?_, q, hqA, hqρ, hqs⟩
  · rw [hRy] at hyR hsy ⊢
    exact sec3_of_conj hc.hyp hc.sylowR hZ hyR hsy hqA hqρ hq1 hq2
  · rintro rfl
    apply hq1
    have : q ∈ R ⊓ A := mem_inf.mpr ⟨by simpa using hqρ, hqA⟩
    rwa [hc.R_inf_A hZ, mem_bot] at this

theorem caseC_split (I : Inputs74) (hZ : Odd (Nat.card (center ↥A))) (D : ClassicalModel A)
    {n : ℕ} {J : Subgroup G} (hle : ∀ u ∈ T, ∀ p' ∈ A, u⁻¹ * p' ∈ R → p' ∈ J) {F : Type}
    [Field F] [Finite F] {ι₁ ι₂ : F → G} (hF : Nat.card F = D.q)
    (hsd : SplitData A J (Smaller D n) (Smaller D n) F ι₁ ι₂)
    (hcov : ∀ b : G, rightConjugate T b ≤ centralizer (T : Set G) → rightConjugate T b ≠ T →
      rightConjugate T b = sec3V T (rightConjugate T b) ⊓ rightConjugate A g ∨
      ∀ v ∈ sec3V T (rightConjugate T b), v ∉ rightConjugate A g →
        ∃ y : G, rightConjugate T y ≤ sec3V T (rightConjugate T b) ∧ v ∈ rightConjugate T y)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A) :
    ∃ (T' : Subgroup G) (x : G), Sec3 A R T' x ∧
      ∃ s ∈ T', s ≠ 1 ∧ ∃ q ∈ A, s⁻¹ * q ∈ R ∧ Smaller D n q := by
  classical
  obtain ⟨m, hm⟩ := D.exists_q_eq
  have : CharP F 2 := charP_two_of_card (k := m) (by rw [hF, hm])
  have hRT := hc.inf_eq_bot
  have hap : ∀ u ∈ T, ∃ d : F, u⁻¹ * (ι₁ d * ι₂ d) ∈ R := by
    intro u hu
    obtain ⟨q, hqA, hqρ⟩ := hc.exists_aPart I.h32 I.h4 I.h34 hu
    obtain ⟨d, rfl⟩ := (hsd.mem_iff q).mp (hle u hu q hqA hqρ)
    exact ⟨d, hqρ⟩
  have hπA : ∀ d : F, ι₁ d * ι₂ d ∈ A := fun d => mul_mem (hsd.mem₁ d) (hsd.mem₂ d)
  have hone : ∀ u ∈ T, u⁻¹ ∈ R → u = 1 := by
    intro u hu hu'
    have : u ∈ R ⊓ T := mem_inf.mpr ⟨by simpa using inv_mem hu', hu⟩
    rwa [hRT, mem_bot] at this
  obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, ht₁₂'⟩ := hc.exists_ne_ne
  obtain ⟨d₁, hd₁⟩ := hap t₁ ht₁
  obtain ⟨d₂, hd₂⟩ := hap t₂ ht₂
  have hd0 : ∀ {u : G} {d : F}, u ∈ T → u ≠ 1 → u⁻¹ * (ι₁ d * ι₂ d) ∈ R → d ≠ 0 := by
    intro u d hu hu1 hud hd
    apply hu1
    apply hone u hu
    rw [hd, hsd.map_zero₁, hsd.map_zero₂, mul_one, mul_one] at hud
    exact hud
  have hd₁0 := hd0 ht₁ ht₁1 hd₁
  have hd₂0 := hd0 ht₂ ht₂1 hd₂
  have hd₁₂ : d₁ ≠ d₂ := by
    rintro rfl
    apply ht₁₂'
    have h1 : t₁⁻¹ * t₂ ∈ R := by
      have := mul_mem hd₁ (inv_mem hd₂)
      simpa [mul_assoc] using this
    have h2 : t₁⁻¹ * t₂ ∈ R ⊓ T := mem_inf.mpr ⟨h1, mul_mem (inv_mem ht₁) ht₂⟩
    rw [hRT, mem_bot] at h2
    calc t₁ = t₁ * (t₁⁻¹ * t₂) := by rw [h2, mul_one]
      _ = t₂ := by group
  set c : F := d₂ / d₁ with hcdef
  have hc0 : c ≠ 0 := div_ne_zero hd₂0 hd₁0
  have hc1 : c ≠ 1 := fun h => hd₁₂ ((div_eq_one_iff_eq hd₁0).mp h).symm
  have hcd : c * d₁ = d₂ := div_mul_cancel₀ d₂ hd₁0
  obtain ⟨a, haA, ha⟩ := hsd.scalar c hc0
  have hconj : ∀ d : F, a⁻¹ * (ι₁ d * ι₂ d) * a = ι₁ d * ι₂ (c * d) := by
    intro d
    calc a⁻¹ * (ι₁ d * ι₂ d) * a = (a⁻¹ * ι₁ d * a) * (a⁻¹ * ι₂ d * a) := by group
      _ = ι₁ d * ι₂ (c * d) := by rw [(ha d).1, (ha d).2]
  have hcoord : ∀ u ∈ T, ∀ p' ∈ A, u⁻¹ * p' ∈ R → ∃ d : F, p' = ι₁ d * ι₂ d ∧
      u⁻¹ * (ι₁ d * ι₂ d) ∈ R := by
    intro u hu p' hp' hρ'
    obtain ⟨d, rfl⟩ := (hsd.mem_iff p').mp (hle u hu p' hp' hρ')
    exact ⟨d, rfl, hρ'⟩
  have h1c : (1 : F) + c ≠ 0 := by
    intro h
    apply hc1
    have : c = -1 := by linear_combination h
    rw [this, CharTwo.neg_eq]
  have hd12 : d₁ + d₂ ≠ 0 := by
    intro h
    apply hd₁₂
    have : d₁ = -d₂ := by linear_combination h
    rw [this, CharTwo.neg_eq]
  refine hc.caseC_core I hZ D hle haA ?_ ?_ ht₁ ht₂ ht₁₂' ?_ ?_ (hcov a) hno
  ·
    intro j hj j' hj'
    obtain ⟨d, rfl⟩ := (hsd.mem_iff j).mp hj
    obtain ⟨d', rfl⟩ := (hsd.mem_iff j').mp hj'
    rw [hconj]
    exact hsd.commute_mul d d d' (c * d')
  ·
    intro j hj j' hj' he
    obtain ⟨d, rfl⟩ := (hsd.mem_iff j).mp hj
    obtain ⟨d', rfl⟩ := (hsd.mem_iff j').mp hj'
    rw [hconj] at he
    obtain ⟨rfl, h3⟩ := hsd.eq_of_mul_eq he
    have h4 : (1 - c) * d = 0 := by rw [sub_mul, one_mul, ← h3, sub_self]
    have h5 : d = 0 := by
      rcases mul_eq_zero.mp h4 with h6 | h6
      · exact absurd (sub_eq_zero.mp h6).symm hc1
      · exact h6
    rw [h5, hsd.map_zero₁, hsd.map_zero₂, mul_one]
  ·
    intro u hu hu1 p' hp' hρ'
    obtain ⟨d, rfl, hd⟩ := hcoord u hu p' hp' hρ'
    rw [hconj, hsd.mul_mul, CharTwo.add_self_eq_zero, hsd.map_zero₁, one_mul,
      show d + c * d = (1 + c) * d by ring]
    exact hsd.prop₂ _ (mul_ne_zero h1c (hd0 hu hu1 hd))
  ·
    intro p₁ hp₁ hρ₁ p₂ hp₂ hρ₂
    obtain ⟨e₁, rfl, he₁⟩ := hcoord t₁ ht₁ p₁ hp₁ hρ₁
    obtain ⟨e₂, rfl, he₂⟩ := hcoord t₂ ht₂ p₂ hp₂ hρ₂
    have h₁ := (hsd.eq_of_mul_eq (hc.aPart_unique hZ (hπA e₁) he₁ (hπA d₁) hd₁)).1
    have h₂ := (hsd.eq_of_mul_eq (hc.aPart_unique hZ (hπA e₂) he₂ (hπA d₂) hd₂)).1
    rw [h₁, h₂, hconj, hsd.mul_mul, hcd, CharTwo.add_self_eq_zero, hsd.map_zero₂, mul_one,
      add_comm]
    exact hsd.prop₁ _ hd12

theorem caseC (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (D : ClassicalModel A) (hfam : D.family ≠ .symplectic) (hq : 4 ≤ D.q) (hS : ClassicalSplit)
    {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R)
    (hnp : ¬ D.IsPrimary p) {n : ℕ} (hn : D.HasMeasure p n)
    (hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A) :
    ∃ (T' : Subgroup G) (x : G), Sec3 A R T' x ∧
      ∃ s ∈ T', s ≠ 1 ∧ ∃ q ∈ A, s⁻¹ * q ∈ R ∧ Smaller D n q := by
  obtain ⟨hZ, hle, -, hI⟩ := hc.case14 I hTy D hfam hq ht ht1 hp hρ
  obtain ⟨F, _, _, ι₁, ι₂, hF, hsd⟩ := exists_splitAt_smaller hS D hfam hc.hyp.standard.1 hZ hq hp
    (hc.orderOf_aPart I.h32 ht ht1 hρ) hnp hn hI
  exact hc.caseC_split I hZ D hle hF hsd
    (fun b hbT hne => hc.cover_derived I hTy D hfam hq hbT hne) hno

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
