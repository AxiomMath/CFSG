module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89Sp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreModFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_prime_exponent_of_minimal {Y I : Type} [Group Y] [Group I] [Finite I]
    (hab : ∀ x y : I, x * y = y * x) (hodd : ¬ 2 ∣ Nat.card I) (hI1 : Nat.card I ≠ 1)
    (ρ : Y →* MulAut I)
    (hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ x : I, x ^ p = 1 := by
  classical
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hI1
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ?_, ?_⟩
  · rintro rfl
    exact hodd hpd
  let Ω : Subgroup I :=
    { carrier := {x | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        change x ^ p = 1 at hx
        change y ^ p = 1 at hy
        change (x * y) ^ p = 1
        have hc : Commute x y := hab x y
        rw [hc.mul_pow, hx, hy, one_mul]
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x ^ p = 1 at hx
        change x⁻¹ ^ p = 1
        rw [inv_pow, hx, inv_one] }
  have hΩn : Ω.Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hab g n, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact hn⟩
  have hΩinv : ActInv ρ Ω := by
    intro y z hz
    change ρ y z ^ p = 1
    have hz' : z ^ p = 1 := hz
    rw [← map_pow, hz', map_one]
  have hΩne : Ω ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I) p hpd
    intro h
    have hxΩ : x ∈ Ω := by
      change x ^ p = 1
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [h, Subgroup.mem_bot] at hxΩ
    rw [hxΩ, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hΩtop : Ω = ⊤ := (hmin Ω hΩn hΩinv).resolve_left hΩne
  intro x
  have : x ∈ Ω := by rw [hΩtop]; trivial
  exact this

theorem core_S (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable) (hF2 : KFactL32OddFix)
    {Y : Type} [Group Y] [Finite Y] (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) {a : Y}
    (ha : orderOf a = 3) (S : Subgroup Y) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    ∀ (n : ℕ) (I : Type) [Group I] [Finite I], Nat.card I = n → CFSG.Open.IsKGroup I →
      ¬ 3 ∣ n → ∀ (ρ : Y →* MulAut I) (J : Subgroup I), ActInv ρ J →
        (∀ x : I, ρ a x = x → x ∈ J) → ∀ u : I, (∀ s ∈ S, u⁻¹ * ρ s u ∈ J) → u ∈ J := by
  have hmod : ModFix Y a := modFix hY ha
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I _ _ hn hK h3 ρ J hJ hC u hu
  by_cases hproper : ∃ K : Subgroup I, K.Normal ∧ ActInv ρ K ∧ K ≠ ⊥ ∧ K ≠ ⊤
  · obtain ⟨K, hKn, hKinv, hKbot, hKtop⟩ := hproper
    have hKdvd : Nat.card K ∣ Nat.card I := Subgroup.card_subgroup_dvd_card K
    have hKcard : Nat.card K < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hKdvd) fun h => hKtop ?_
      exact (Subgroup.card_eq_iff_eq_top K).1 h
    have hK2 : 2 ≤ Nat.card K := by
      have h1 : Nat.card K ≠ 1 := fun h => hKbot (Subgroup.card_eq_one.1 h)
      have := Nat.card_pos (α := K)
      omega
    have hQcard : Nat.card (I ⧸ K) < n := by
      have e : Nat.card (I ⧸ K) * Nat.card K = Nat.card I := Subgroup.index_mul_card K
      have hpos : 0 < Nat.card (I ⧸ K) := Nat.card_pos
      rw [← hn, ← e]
      nlinarith
    have h3K : ¬ 3 ∣ Nat.card K := fun h => h3 (hn ▸ h.trans hKdvd)
    have h3Q : ¬ 3 ∣ Nat.card (I ⧸ K) := fun h =>
      h3 (hn ▸ h.trans (Subgroup.index_dvd_card K))
    have hquot : (QuotientGroup.mk u : I ⧸ K) ∈ (J ⊔ K).map (QuotientGroup.mk' K) := by
      refine ih (Nat.card (I ⧸ K)) hQcard (I ⧸ K) rfl
        (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hK K) h3Q (actQuot ρ K hKinv)
        ((J ⊔ K).map (QuotientGroup.mk' K)) ?_ ?_ (QuotientGroup.mk u) ?_
      · rintro y _ ⟨x, hx, rfl⟩
        exact ⟨ρ y x, (hJ.sup hKinv) y x hx, rfl⟩
      · intro x hx
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨x', hx'1, hx'2⟩ := exists_fixed_of_mk_fixed hKinv ha3 h3K x hx
        exact ⟨x', (le_sup_left : J ≤ J ⊔ K) (hC x' hx'2), hx'1⟩
      · intro s hs
        exact ⟨u⁻¹ * ρ s u, (le_sup_left : J ≤ J ⊔ K) (hu s hs), rfl⟩
    obtain ⟨w, hw, hwu⟩ := hquot
    have hwK : w⁻¹ * u ∈ K := QuotientGroup.eq.1 hwu
    have huJK : u ∈ K ⊔ J := by
      have : u = w * (w⁻¹ * u) := by group
      rw [this, sup_comm]
      exact Subgroup.mul_mem _ hw ((le_sup_right : K ≤ J ⊔ K) hwK)
    have huset : u ∈ ((K ⊔ J : Subgroup I) : Set I) := huJK
    rw [Subgroup.normal_mul] at huset
    obtain ⟨k, hk, j, hj, rfl⟩ := huset
    have hkJ : k ∈ J := by
      have hres := ih (Nat.card K) hKcard K rfl
        (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hK K) h3K (actSub ρ K hKinv)
        (J.subgroupOf K)
        (fun y x hx => by
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          exact hJ y _ hx)
        (fun x hx => by
          rw [Subgroup.mem_subgroupOf]
          apply hC
          exact congrArg Subtype.val hx)
        ⟨k, hk⟩
        (fun s hs => by
          rw [Subgroup.mem_subgroupOf]
          have h1 := hu s hs
          have h2 : k⁻¹ * ρ s k = j * ((k * j)⁻¹ * ρ s (k * j)) * (ρ s j)⁻¹ := by
            rw [map_mul]
            group
          change k⁻¹ * ρ s k ∈ J
          rw [h2]
          exact J.mul_mem (J.mul_mem hj h1) (J.inv_mem (hJ s j hj)))
      exact hres
    exact J.mul_mem hkJ hj
  · have hmin : ∀ K : Subgroup I, K.Normal → ActInv ρ K → K = ⊥ ∨ K = ⊤ := by
      intro K hKn hKinv
      by_contra h
      push Not at h
      exact hproper ⟨K, hKn, hKinv, h.1, h.2⟩
    by_cases hab : ∀ x y : I, x * y = y * x
    · by_cases h2 : 2 ∣ Nat.card I
      · have := abel_base hmod hab h2 ρ hmin J hJ hC
        rw [this]
        trivial
      · by_cases hI1 : Nat.card I = 1
        · haveI : Subsingleton I := (Nat.card_eq_one_iff_unique.1 hI1).1
          rw [Subsingleton.elim u 1]
          exact J.one_mem
        · obtain ⟨p, hp, hp2, hpe⟩ := exists_prime_exponent_of_minimal hab h2 hI1 ρ hmin
          have hJn : J.Normal :=
            ⟨fun n hn g => by
              have : g * n * g⁻¹ = n := by rw [hab g n, mul_assoc, mul_inv_cancel, mul_one]
              rw [this]
              exact hn⟩
          rcases hmin J hJn hJ with hJbot | hJtop
          · have hfix : ∀ x : I, ρ a x = x → x = 1 := fun x hx => by
              have := hC x hx
              rw [hJbot, Subgroup.mem_bot] at this
              exact this
            have hu1 : u = 1 := hF2 Y hY a ha S hS I hab ⟨p, hp, hp2, hpe⟩ ρ hfix u
              (fun s hs => by
                have := hu s hs
                rw [hJbot, Subgroup.mem_bot, inv_mul_eq_one] at this
                exact this.symm)
            rw [hu1]
            exact J.one_mem
          · rw [hJtop]
            trivial
    · push Not at hab
      have := nonab_base hCat hY ha hK (hn ▸ h3) ρ hab hmin J hJ hC
      rw [this]
      trivial

end CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof
