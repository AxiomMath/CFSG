module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Push
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

theorem exists_two_ne_one_of_four_le {H : Subgroup G} (h : 4 ≤ Nat.card H) :
    ∃ s₁ ∈ H, ∃ s₂ ∈ H, s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ s₁ ≠ s₂ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := ((H : Set G).toFinset).erase 1 with hS
  have hc : 1 < S.card := by
    rw [show Nat.card H = Nat.card (H : Set G) from rfl, Nat.card_eq_card_toFinset] at h
    rw [hS, Finset.card_erase_of_mem (by simp)]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  simp only [hS, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx hy
  exact ⟨x, hx.2, y, hy.2, hx.1, hy.1, hxy⟩

@[expose] def GMS5NotSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T R R₂ : Subgroup G) (a : ℕ) (y d : G),
    SzMinCounter G L a → Sec3.SzR G L T R a y d → Sec3.IsR₂ L T R R₂ d →
    ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) →
    ¬ IsSylowOf 2 R (normalizer (R : Set G))

@[expose] def GMS5Swap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T R R₂ : Subgroup G) (a : ℕ) (y d : G),
    SzMinCounter G L a → Sec3.SzR G L T R a y d → Sec3.IsR₂ L T R R₂ d →
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ (2 * a + 1) →
    (∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) → (∀ r ∈ R₂, r ^ 2 = 1) →
    ∀ g ∈ normalizer (R : Set G), rightConjugate (gmsV L T) g ≠ R₂

namespace Sec3

namespace SzR

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

theorem mem_T_of_commute_T₀
    (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d) {s : G}
    (hs : s ∈ T ⊓ centralizer (L : Set G)) (hs1 : s ≠ 1) {x : G} (hx : x ∈ R)
    (hxs : x * s = s * x) : x ∈ T := by
  obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hx' : x ∈ R₂ ⊔ T := by rw [sup_comm, hR₂.sup_eq]; exact hx
  obtain ⟨r, hr, t, ht, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hR₂.le_R.trans hS.le_normalizer_T) hx'
  have hts : t * s = s * t :=
    mem_centralizer_iff.mp (hVC (mem_sup_right hs)) t (by rw [hS.eq_gmsW] at ht; exact ht)
  have hrs : r * s = s * r := by
    have h1 : r * s * t = s * r * t := by
      calc r * s * t = r * (t * s) := by rw [mul_assoc, hts]
        _ = r * t * s := by group
        _ = s * (r * t) := hxs
        _ = s * r * t := by group
    exact mul_right_cancel h1
  have hrA : r ∈ gmsA L T :=
    (hS.commutator_eq_one_iff hR₂ hs hs1 hr).mp (by rw [hrs]; group)
  exact mul_mem (gmsA_le_T hrA) ht

theorem swap_of_ne
    (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (hgV : rightConjugate (gmsV L T) g ≠ gmsV L T) :
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ (2 * a + 1) ∧
      (∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) ∧ (∀ r ∈ R₂, r ^ 2 = 1) ∧
      rightConjugate (gmsV L T) g = R₂ := by
  classical
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨hVc, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  have hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z * x⁻¹ * z⁻¹ ∈ gmsA L T := fun x hx z hz =>
    hS.commutator_mem_gmsA h34 hx hz
  have hgN := hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hgA : ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T := fun b hb =>
    (mem_normalizer_iff.mp hgN b).mp hb
  have hgA' : ∀ b ∈ gmsA L T, g⁻¹ * b * g ∈ gmsA L T := fun b hb => by
    simpa using (mem_normalizer_iff.mp (inv_mem hgN) b).mp hb
  have hgR : ∀ x ∈ R, g⁻¹ * x * g ∈ R := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  have hgR' : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hT₀R : ∀ s ∈ T ⊓ centralizer (L : Set G), s ∈ R := fun s hs => hS.T_le (mem_inf.mp hs).1
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hφeq : ∀ x ∈ R, ∀ x' ∈ R, φ x = φ x' → x * x'⁻¹ ∈ gmsA L T := by
    intro x hx x' hx' h
    rw [← hC.ker _ (mul_mem hx (inv_mem hx')), hC.mul _ hx _ (inv_mem hx'), h,
      ← hC.mul _ hx' _ (inv_mem hx'), mul_inv_cancel, hφ1]
  obtain ⟨E, hE⟩ : ∃ E : AddSubgroup (BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1)),
      ∀ z, z ∈ E ↔ ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z :=
    ⟨{ carrier := {z | ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z}
       add_mem' := by
         rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
         refine ⟨s * s', mul_mem hs hs', ?_⟩
         rw [← hC.mul _ (hgR _ (hT₀R s hs)) _ (hgR _ (hT₀R s' hs'))]
         congr 1
         group
       zero_mem' := ⟨1, one_mem _, by rw [show g⁻¹ * 1 * g = 1 by group, hφ1]⟩
       neg_mem' := by
         rintro _ ⟨s, hs, rfl⟩
         exact ⟨s, hs, Prod.ext (CharTwo.neg_eq _).symm
           (Prod.ext (CharTwo.neg_eq _).symm (CharTwo.neg_eq _).symm)⟩ }, fun z => Iff.rfl⟩
  have hφs0 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = 0 → s = 1 := by
    intro s hs h0
    have hA := (hC.ker _ (hgR _ (hT₀R s hs))).mp h0
    have hsA : s ∈ gmsA L T := by simpa [mul_assoc] using hgA _ hA
    have hs' : s ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨hs, hsA⟩
    rw [hS.lemma313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at hs'
    exact hs'
  have hs1 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) ≠ 0 → s ≠ 1 := by
    rintro s - h rfl
    exact h (by rw [show g⁻¹ * 1 * g = 1 by group, hφ1])
  have htwo : ∃ z ∈ E, ∃ z' ∈ E, z ≠ 0 ∧ z' ≠ 0 ∧ z ≠ z' := by
    obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := exists_two_ne_one_of_four_le h4
    refine ⟨_, (hE _).mpr ⟨s₁, hs₁, rfl⟩, _, (hE _).mpr ⟨s₂, hs₂, rfl⟩,
      fun h => h1 (hφs0 _ hs₁ h), fun h => h2 (hφs0 _ hs₂ h), fun h => h12 ?_⟩
    have h3 : φ (g⁻¹ * (s₁ * s₂) * g) = 0 := by
      rw [show g⁻¹ * (s₁ * s₂) * g = g⁻¹ * s₁ * g * (g⁻¹ * s₂ * g) by group,
        hC.mul _ (hgR _ (hT₀R _ hs₁)) _ (hgR _ (hT₀R _ hs₂)), h]
      exact Prod.ext (CharTwo.add_self_eq_zero _)
        (Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _))
    have h5 := hφs0 _ (mul_mem hs₁ hs₂) h3
    rw [eq_inv_of_mul_eq_one_right h5, inv_eq_of_mul_eq_one_right
      (by rw [← sq]; exact hT₀el.2 s₁ hs₁)]
  have hVgV : rightConjugate (gmsV L T) g ⊓ gmsV L T = gmsA L T :=
    (hS.rightConjugate_eq_or_inf_eq hR₂ hg).resolve_left hgV
  have hinf : ∀ z ∈ E, z.1 = 0 → z.2.1 = 0 → z = 0 := by
    intro z hz h1 h2
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    have hsR := hgR _ (hT₀R s hs)
    obtain ⟨s', hs', hs'φ⟩ := hC.T₀_surj _ (hC.mem _ hsR)
    have hmem := hφeq _ hsR _ (hT₀R s' hs') (by rw [hs'φ]; exact Prod.ext h1 (Prod.ext h2 rfl))
    have hV : g⁻¹ * s * g ∈ gmsV L T := by
      have e : g⁻¹ * s * g = g⁻¹ * s * g * s'⁻¹ * s' := by group
      rw [e]
      exact mul_mem (mem_sup_left hmem) (mem_sup_right hs')
    have hVg : g⁻¹ * s * g ∈ rightConjugate (gmsV L T) g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using (mem_sup_right hs : s ∈ gmsV L T)
    have hA : g⁻¹ * s * g ∈ gmsA L T := by rw [← hVgV]; exact mem_inf.mpr ⟨hVg, hV⟩
    exact (hC.ker _ hsR).mpr hA
  have hsq : ∀ z ∈ E, VLike.sqMap a c e z = 0 := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    rw [← hC.sq _ (hgR _ (hT₀R s hs))]
    have e1 : (g⁻¹ * s * g) ^ 2 = 1 := by
      have e2 : (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g := by simp only [sq]; group
      rw [e2, hT₀el.2 s hs]
      group
    rw [e1, hv1]
  have hsurj : ∀ z ∈ E, z ≠ 0 → ∀ w, ∃ z' : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1),
      z'.2.2 ∈ Λ ∧ VLike.commMap a c z z' = w := by
    intro z hz hz0 w
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨b, hb, hbw⟩ := hC.v_surj w
    obtain ⟨r, hr, hrb⟩ := hS.exists_commutator_eq hR₂ hs (hs1 s hs hz0) (hgA _ (inv_mem hb))
    have hrR := hR₂.le_R hr
    refine ⟨φ (g⁻¹ * r * g), hC.mem _ (hgR _ hrR), ?_⟩
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ (hgR _ hrR)]
    have e1 : g⁻¹ * s * g * (g⁻¹ * r * g) * (g⁻¹ * s * g)⁻¹ * (g⁻¹ * r * g)⁻¹ =
        g⁻¹ * (r * s * r⁻¹ * s⁻¹)⁻¹ * g := by group
    rw [e1, hrb, show g⁻¹ * (g * b⁻¹ * g⁻¹)⁻¹ * g = b by group, hbw]
  have hker : ∀ z ∈ E, ∀ z' ∈ E, z ≠ 0 → z' ≠ 0 → ∀ x : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1), x.2.2 ∈ Λ →
      VLike.commMap a c z x = 0 → VLike.commMap a c z' x = 0 := by
    intro z hz z' hz' hz0 _ x hx h0
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨s', hs', rfl⟩ := (hE z').mp hz'
    obtain ⟨w, hw, rfl⟩ := hC.surj x hx
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ hw] at h0
    rw [← hC.comm _ (hgR _ (hT₀R s' hs')) _ hw]
    have h1 := hC.v_inj _ (hcomm _ (hgR _ (hT₀R s hs)) _ hw) h0
    have hc1 : g * w * g⁻¹ * s = s * (g * w * g⁻¹) := by
      have h3 : g⁻¹ * s * g * w = w * (g⁻¹ * s * g) := by
        calc g⁻¹ * s * g * w =
            g⁻¹ * s * g * w * (g⁻¹ * s * g)⁻¹ * w⁻¹ * (w * (g⁻¹ * s * g)) := by group
          _ = w * (g⁻¹ * s * g) := by rw [h1, one_mul]
      calc g * w * g⁻¹ * s = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * s * g * w) * g⁻¹ := by rw [h3]
        _ = s * (g * w * g⁻¹) := by group
    have hT := hS.mem_T_of_commute_T₀ hR₂ hs (hs1 s hs hz0) (hgR' _ hw) hc1
    have hc2 : g * w * g⁻¹ * s' = s' * (g * w * g⁻¹) :=
      mem_centralizer_iff.mp (hVC (mem_sup_right hs')) _ (by rw [hS.eq_gmsW] at hT; exact hT)
    have e1 : g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ = 1 := by
      calc g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ =
          g⁻¹ * (s' * (g * w * g⁻¹) * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹ * s' * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by rw [← hc2]
        _ = 1 := by group
    rw [e1, hv1]
  have hH : VLike.Hyp a c e Λ E := ⟨hS.one_le, hK, by rw [hC.card]; exact h4,
    fun z hz => by obtain ⟨s, hs, rfl⟩ := (hE z).mp hz; exact hC.mem _ (hgR _ (hT₀R s hs)),
    htwo, hinf, hsq, hsurj, hker⟩
  obtain ⟨hc0, he0, hΛK, hEz⟩ := hH.eq_zero_of_hyp (by rw [hC.card]; exact hne)
  subst hc0 he0
  have hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ (2 * a + 1) := by
    rw [← hC.card, hΛK, hK]
  refine ⟨hq, fun x hx r hr => ?_, fun r hr => ?_, ?_⟩
  ·
    have hxR := hS.T_le (mem_inf.mp hx).1
    have hrR := hR₂.le_R hr
    obtain ⟨-, hx2⟩ := hC.of_T₁ x hx
    obtain ⟨hr1, hr2⟩ := hC.of_R₂ r hr
    have hφr : φ r = (0, (φ r).2.1, 0) := Prod.ext hr1 (Prod.ext rfl hr2)
    have h0 : v (x * r * x⁻¹ * r⁻¹) = 0 := by
      rw [hC.comm x hxR r hrR, hφr, VLike.commMap_snd, hx2]
      ring
    have h1 := hC.v_inj _ (hcomm _ hxR _ hrR) h0
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [h1, one_mul]
  ·
    have hrR := hR₂.le_R hr
    obtain ⟨hr1, hr2⟩ := hC.of_R₂ r hr
    refine hC.v_inj _ (hS.sq_mem_gmsA_of_mem_R h34 hX hrR) ?_
    rw [hC.sq r hrR, VLike.sqMap, hr1, hr2, zero_pow (Nat.succ_ne_zero _)]
    ring
  ·
    have hA₁N : gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
      fun b hb => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs =>
        (mem_centralizer_iff.mp (mem_inf.mp hs).2 b (mem_inf.mp (mem_inf.mp hb).1).2).symm)
    have hle : rightConjugate (gmsV L T) g ≤ R₂ := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      obtain ⟨b, hb, s, hs, hbs⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hx
      have hsR := hgR _ (hT₀R s hs)
      obtain ⟨hs1', hs3⟩ := hEz _ ((hE _).mpr ⟨s, hs, rfl⟩)
      obtain ⟨r, hr, hrφ⟩ := hC.R₂_surj (φ (g⁻¹ * s * g)).2.1
      have hmem := hφeq _ hsR _ (hR₂.le_R hr)
        (by rw [hrφ]; exact Prod.ext hs1' (Prod.ext rfl hs3))
      have hsR₂ : g⁻¹ * s * g ∈ R₂ := by
        have e1 : g⁻¹ * s * g = g⁻¹ * s * g * r⁻¹ * r := by group
        rw [e1]
        exact mul_mem (hR₂.gmsA_le hmem) hr
      have e1 : x = g⁻¹ * b * g * (g⁻¹ * s * g) := by
        have e2 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [e2, ← hbs]
        group
      rw [e1]
      exact mul_mem (hR₂.gmsA_le (hgA' b hb)) hsR₂
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    rw [rightConjugate_card, hVc, hS.card_isR₂ hR₂, hq]

end SzR

end Sec3

theorem SzMinCounter.false_of_gms5
    {L T R R₂ : Subgroup G} {a : ℕ} {y d : G} (hNS : GMS5NotSylow) (hSw : GMS5Swap)
    (hM : SzMinCounter G L a) (hS : Sec3.SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hall : ∀ g ∈ normalizer (R : Set G), rightConjugate (gmsV L T) g = gmsV L T
  · exact hNS G L T R R₂ a y d hM hS hR₂ hne (hS.isSylowOf_normalizer.of_le le_normalizer
      fun g hg => (rightConjugate_eq_self_iff _ _).mp (hall g hg))
  · push Not at hall
    obtain ⟨g, hg, hgV⟩ := hall
    obtain ⟨E, hE, -, hE4⟩ := hS.sec3.exists_four_le
    have h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) :=
      hE4 ▸ Subgroup.card_le_of_le hE
    obtain ⟨hq, hcomm, hsq, hgR⟩ := hS.swap_of_ne h34 hR₂ h4 hne hg hgV
    exact hSw G L T R R₂ a y d hM hS hR₂ hq hcomm hsq g hg hgR

end CFSG.ComponentClassification.GMS78
