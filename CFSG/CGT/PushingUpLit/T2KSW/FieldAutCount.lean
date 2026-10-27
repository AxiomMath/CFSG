module

public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutFamily
public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutSemilinear

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem relIndex_pos' (H K : Subgroup G) : 0 < H.relIndex K :=
  Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

theorem cnt_master (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) {B : Subgroup G}
    (hBT : B ≤ T) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB1 : ¬ B ≤ Rl L T ⊔ Dc L T) :
    ∃ k q₀ b₁ t m e : ℕ,
      Nat.card B = k * (b₁ * (t * (m * e))) ∧ e = Nat.card ↥(Ec L T ⊓ B) ∧ q₀ ^ k = 2 ^ n ∧
      2 ≤ k ∧ 2 ≤ q₀ ∧ 0 < b₁ ∧ 0 < t ∧ 0 < m ∧ b₁ * m ≤ q₀ ^ 2 ∧ t ≤ q₀ ∧
      (t = 1 ↔ Dc L T ⊓ B ≤ blockU L ⊔ Ec L T) := by
  classical
  have hT := hs.sylow
  obtain ⟨H, hA⟩ := exists_utri_coord hs.hyp.natBlock hs.hyp.le (hs.hyp.normal hE1) hT
  set T₁ : Subgroup G := Rl L T ⊔ Dc L T with hT₁
  set VE : Subgroup G := blockU L ⊔ Ec L T with hVE
  have hDT₁ : Dc L T ≤ T₁ := le_sup_right
  have hEVE : Ec L T ≤ VE := le_sup_right
  have hVEDc : VE ≤ Dc L T := H.blockU_sup_Ec_le_Dc hT
  have hEDc : Ec L T ≤ Dc L T := Ec_le_Dc
  obtain ⟨x, hxB, hk⟩ := H.exists_mem_orderOf_chi_eq hT hBT
  have hxT : x ∈ T := hBT hxB
  set σ := H.chi ⟨x, hT.le hxT⟩ with hσ
  have hcomm : ∀ y ∈ B, x * y = y * x := fun y hy => hBab x hxB y hy
  set b₁ := (Dc L T).relIndex (T₁ ⊓ B) with hb₁
  set t := VE.relIndex (Dc L T ⊓ B) with ht
  set Y : Subgroup G := VE ⊓ (Dc L T ⊓ B) with hY
  set m := (Ec L T).relIndex Y with hm
  set e := Nat.card ↥(Ec L T ⊓ B) with he
  have c1 := Subgroup.relIndex_mul_card (H := T₁) (K := B)
  have c2 := Subgroup.relIndex_mul_card (H := Dc L T) (K := T₁ ⊓ B)
  have c3 := Subgroup.relIndex_mul_card (H := VE) (K := Dc L T ⊓ B)
  have c4 := Subgroup.relIndex_mul_card (H := Ec L T) (K := Y)
  have eq1 : Dc L T ⊓ (T₁ ⊓ B) = Dc L T ⊓ B := by
    ext y
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hDT₁ h.1, h.2⟩⟩
  have eq2 : Ec L T ⊓ Y = Ec L T ⊓ B := by
    ext y
    simp only [hY, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, hEVE h.1, hEDc h.1, h.2⟩⟩
  rw [eq1] at c2
  rw [eq2] at c4
  have hcard : Nat.card B = T₁.relIndex B * (b₁ * (t * (m * e))) := by
    rw [← c1, ← c2, ← c3, ← c4]
  have hk2 : 2 ≤ T₁.relIndex B := by
    have h1 : T₁.relIndex B ≠ 1 := fun h => hB1 (Subgroup.relIndex_eq_one.1 h)
    have h0 := relIndex_pos' (T₁) B
    omega
  have hq₀ : fixCard σ ^ T₁.relIndex B = 2 ^ n := by
    rw [← hk]
    exact H.fixCard_pow_chi _
  have hb₁le : b₁ ≤ fixCard σ := by
    have := H.relIndex_Dc_le hT hA hxT (X := T₁ ⊓ B) inf_le_left (fun y hy => hcomm y hy.2)
    rwa [Subgroup.inf_relIndex_right] at this
  have htle : t ≤ fixCard σ := by
    have := H.relIndex_sup_le hT hA hxT (X := Dc L T ⊓ B) inf_le_left
      (fun u hu => hcomm u hu.2)
    rwa [Subgroup.inf_relIndex_right] at this
  have hYVE : Y ≤ VE := inf_le_left
  have hmle : m ≤ fixCard σ ^ 2 := by
    have := H.relIndex_Ec_le hT hxT (Y := Y) hYVE (fun u hu => hcomm u hu.2.2)
    rwa [Subgroup.inf_relIndex_right] at this
  have hbm : b₁ * m ≤ fixCard σ ^ 2 := by
    by_cases hb1 : b₁ = 1
    · rw [hb1, one_mul]
      exact hmle
    · have hnle : ¬ T₁ ⊓ B ≤ Dc L T := fun h => hb1 (Subgroup.relIndex_eq_one.2 h)
      obtain ⟨r, hr, hrD⟩ := Set.not_subset.1 hnle
      have hml : m ≤ fixCard σ := by
        have := H.relIndex_Ec_le_line hT hA hxT (Y := Y) hYVE
          (fun u hu => hcomm u hu.2.2) (r := r) hr.1 hrD (fun u hu => hBab r hr.2 u hu.2.2)
        rwa [Subgroup.inf_relIndex_right] at this
      calc b₁ * m ≤ fixCard σ * fixCard σ := Nat.mul_le_mul hb₁le hml
        _ = fixCard σ ^ 2 := (sq _).symm
  refine ⟨T₁.relIndex B, fixCard σ, b₁, t, m, e, hcard, rfl, hq₀, hk2, two_le_fixCard σ,
    relIndex_pos' _ _, relIndex_pos' _ _, relIndex_pos' _ _, hbm, htle, ?_⟩
  exact Subgroup.relIndex_eq_one

theorem arith_ge_three {k q₀ : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q₀) :
    2 * k * q₀ ^ 3 < q₀ ^ (2 * k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have h1 : j < 4 ^ j := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (2 * j + 3) ≤ q₀ ^ (2 * j + 3) := Nat.pow_le_pow_left hq _
  have h3 : 2 ^ (2 * j + 3) = 8 * 4 ^ j := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have h4 : 2 * (j + 3) < q₀ ^ (2 * j + 3) := by omega
  have h5 : 0 < q₀ ^ 3 := by positivity
  calc 2 * (j + 3) * q₀ ^ 3 < q₀ ^ (2 * j + 3) * q₀ ^ 3 := Nat.mul_lt_mul_of_pos_right h4 h5
    _ = q₀ ^ (2 * (j + 3)) := by
      rw [← pow_add]
      ring_nf

theorem arith_beta_two {q₀ b₁ t m e Ee a : ℕ} (hq : 2 ≤ q₀) (hEe : 0 < Ee) (he : e ≤ Ee)
    (he1 : 0 < e) (hbm : b₁ * m ≤ q₀ ^ 2) (ht : t ≤ q₀)
    (ha : (q₀ ^ 2) ^ 2 * Ee ≤ a) (hB : a ≤ 2 * (b₁ * (t * (m * e)))) :
    q₀ = 2 ∧ e = Ee ∧ t = 2 ∧ a = 16 * Ee := by
  have h1 : b₁ * (t * (m * e)) ≤ q₀ ^ 2 * (q₀ * Ee) := by
    calc b₁ * (t * (m * e)) = (b₁ * m) * (t * e) := by ring
      _ ≤ q₀ ^ 2 * (q₀ * Ee) := Nat.mul_le_mul hbm (Nat.mul_le_mul ht he)
  have h2 : q₀ ^ 3 * (q₀ * Ee) ≤ q₀ ^ 3 * (2 * Ee) := by
    calc q₀ ^ 3 * (q₀ * Ee) = (q₀ ^ 2) ^ 2 * Ee := by ring
      _ ≤ a := ha
      _ ≤ 2 * (b₁ * (t * (m * e))) := hB
      _ ≤ 2 * (q₀ ^ 2 * (q₀ * Ee)) := Nat.mul_le_mul_left _ h1
      _ = q₀ ^ 3 * (2 * Ee) := by ring
  have h3 : q₀ * Ee ≤ 2 * Ee := Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hq2 : q₀ = 2 := by
    have : q₀ ≤ 2 := Nat.le_of_mul_le_mul_right h3 hEe
    omega
  subst hq2
  have h4 : 16 * Ee ≤ 2 * (b₁ * (t * (m * e))) := by
    calc 16 * Ee = (2 ^ 2) ^ 2 * Ee := by norm_num
      _ ≤ a := ha
      _ ≤ _ := hB
  have h5 : b₁ * (t * (m * e)) ≤ 4 * (t * e) := by
    calc b₁ * (t * (m * e)) = (b₁ * m) * (t * e) := by ring
      _ ≤ 2 ^ 2 * (t * e) := Nat.mul_le_mul_right _ hbm
      _ = 4 * (t * e) := by norm_num
  have h6 : t * e ≤ 2 * e := Nat.mul_le_mul_right _ ht
  have h7 : 16 * Ee ≤ 16 * e := by omega
  have hee : e = Ee := le_antisymm he (by omega)
  subst hee
  have ht2 : t = 2 := by
    by_contra hne
    have : t ≤ 1 := by omega
    have h8 : t * e ≤ 1 * e := Nat.mul_le_mul_right _ this
    omega
  subst ht2
  refine ⟨rfl, rfl, rfl, ?_⟩
  omega

theorem arith_alpha_two {q₀ b₁ t m Ee a : ℕ} (hq : 2 ≤ q₀) (hEe : 2 ≤ Ee)
    (hbm : b₁ * m ≤ q₀ ^ 2) (ht : t ≤ q₀) (ha : (q₀ ^ 2) ^ 2 * Ee ≤ a)
    (hB : a ≤ 2 * (2 * (b₁ * (t * (m * 1))))) : q₀ = 2 ∧ Ee = 2 ∧ t = 2 ∧ a = 32 := by
  have h1 : b₁ * (t * (m * 1)) ≤ q₀ ^ 2 * q₀ := by
    calc b₁ * (t * (m * 1)) = (b₁ * m) * t := by ring
      _ ≤ q₀ ^ 2 * q₀ := Nat.mul_le_mul hbm ht
  have h2 : q₀ ^ 3 * (q₀ * Ee) ≤ q₀ ^ 3 * 4 := by
    calc q₀ ^ 3 * (q₀ * Ee) = (q₀ ^ 2) ^ 2 * Ee := by ring
      _ ≤ a := ha
      _ ≤ 2 * (2 * (b₁ * (t * (m * 1)))) := hB
      _ ≤ 2 * (2 * (q₀ ^ 2 * q₀)) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = q₀ ^ 3 * 4 := by ring
  have h3 : q₀ * Ee ≤ 4 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hq2 : q₀ = 2 := by nlinarith
  have hEe2 : Ee = 2 := by
    subst hq2
    omega
  subst hq2
  subst hEe2
  have h4 : 32 ≤ a := by
    calc 32 = (2 ^ 2) ^ 2 * 2 := by norm_num
      _ ≤ a := ha
  have h5 : b₁ * (t * (m * 1)) ≤ 4 * t := by
    calc b₁ * (t * (m * 1)) = (b₁ * m) * t := by ring
      _ ≤ 2 ^ 2 * t := Nat.mul_le_mul_right _ hbm
      _ = 4 * t := by norm_num
  have ht2 : t = 2 := by
    by_contra hne
    have : t ≤ 1 := by omega
    omega
  subst ht2
  refine ⟨rfl, rfl, rfl, ?_⟩
  omega

theorem Ec_central_of_card_two (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (h2 : Nat.card ↥(Ec L T) = 2) {y : G} (hy : y ∈ T) {c : G} (hc : c ∈ Ec L T) :
    y * c = c * y := by
  by_cases hc1 : c = 1
  · rw [hc1]
    simp
  have hyc : y * c * y⁻¹ ∈ Ec L T :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Ec (hs.hyp.normal hE1) hs.sylow.le hy) c).1 hc
  have hyc1 : y * c * y⁻¹ ≠ 1 := by
    intro h
    apply hc1
    have : y * c * y⁻¹ = 1 := h
    simpa using this
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (⟨1, one_mem _⟩ : ↥(Ec L T))).1 h2
  have e1 : (⟨c, hc⟩ : ↥(Ec L T)) = z := huniq _ (fun h => hc1 (congrArg Subtype.val h))
  have e2 : (⟨y * c * y⁻¹, hyc⟩ : ↥(Ec L T)) = z := huniq _ (fun h => hyc1 (congrArg Subtype.val h))
  have : y * c * y⁻¹ = c := congrArg Subtype.val (e2.trans e1.symm)
  calc y * c = (y * c * y⁻¹) * y := by group
    _ = c * y := by rw [this]

omit [Finite G] in
theorem mem_sup_of_centralizes {A : Subgroup G} (hAeq : A = blockU L ⊔ Ec L T)
    (hA1 : Dc L T ⊓ Subgroup.centralizer (A : Set G) ≤ A) {d : G} (hd : d ∈ Dc L T)
    (hdE : ∀ c ∈ Ec L T, d * c = c * d) : d ∈ blockU L ⊔ Ec L T := by
  have hle : blockU L ⊔ Ec L T ≤ Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (fun v hv => ?_) (fun c hc => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hd.2 v hv |>.symm.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hdE c hc).symm
  have hdA : d ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hAeq] at ha
    have := (Subgroup.mem_centralizer_singleton_iff.1 (hle ha))
    exact this
  rw [← hAeq]
  exact hA1 ⟨hd, hdA⟩

theorem cnt_beta (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) (hE : Ec L T ≠ ⊥)
    {A : Subgroup G} (hA : IsFamily L T A)
    (hA1 : Dc L T ⊓ Subgroup.centralizer (A : Set G) ≤ A) {B : Subgroup G} (hBT : B ≤ T)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB1 : ¬ B ≤ Rl L T ⊔ Dc L T) :
    Nat.card B < Nat.card A := by
  obtain ⟨k, q₀, b₁, t, m, e, hcard, he, hq, hk, hq₀, hb₁, ht, hm, hbm, htq, ht1⟩ :=
    cnt_master hs hE1 hBT hBab hB1
  have hEe : 2 ≤ Nat.card ↥(Ec L T) := (Subgroup.one_lt_card_iff_ne_bot _).2 hE
  have hAle := family_card_le hs hE1 hA
  have heEe : e ≤ Nat.card ↥(Ec L T) := he ▸ Subgroup.card_le_of_le inf_le_left
  have he1 : 0 < e := he ▸ Nat.card_pos
  rw [← hq] at hAle
  by_contra hcon
  have hAB : Nat.card ↥A ≤ Nat.card ↥B := not_lt.1 hcon
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    obtain ⟨hq2, hee, ht2, hAa⟩ := arith_beta_two hq₀ (by omega) heEe he1 hbm htq hAle
      (hAB.trans hcard.le)
    subst hq2
    have hEB : Ec L T ≤ B := by
      have h1 : Ec L T ⊓ B = Ec L T := Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [← he, hee])
      exact inf_eq_left.1 h1
    have hnot : ¬ Dc L T ⊓ B ≤ blockU L ⊔ Ec L T := fun h => by
      have := ht1.2 h
      omega
    obtain ⟨d, hd, hdVE⟩ := Set.not_subset.1 hnot
    have hAeq : A = blockU L ⊔ Ec L T := by
      refine family_eq_sup_of_card_eq hs hE1 hA ?_
      rw [hAa, ← hq]
      norm_num
    exact hdVE (mem_sup_of_centralizes hAeq hA1 hd.1 fun c hc => hBab d hd.2 c (hEB hc))
  · have h1 : b₁ * (t * (m * e)) ≤ q₀ ^ 2 * (q₀ * Nat.card ↥(Ec L T)) := by
      calc b₁ * (t * (m * e)) = (b₁ * m) * (t * e) := by ring
        _ ≤ q₀ ^ 2 * (q₀ * Nat.card ↥(Ec L T)) :=
          Nat.mul_le_mul hbm (Nat.mul_le_mul htq heEe)
    have h2 := arith_ge_three hk3 hq₀
    have hEpos : 0 < Nat.card ↥(Ec L T) := by omega
    have h3 : (q₀ ^ k) ^ 2 = q₀ ^ (2 * k) := by
      rw [← pow_mul, mul_comm]
    rw [h3] at hAle
    have h4 : Nat.card ↥B ≤ k * (q₀ ^ 2 * (q₀ * Nat.card ↥(Ec L T))) := by
      rw [hcard]
      exact Nat.mul_le_mul_left _ h1
    have hlt : Nat.card ↥B < Nat.card ↥A := by
      calc Nat.card ↥B ≤ k * (q₀ ^ 2 * (q₀ * Nat.card ↥(Ec L T))) := h4
        _ = (k * q₀ ^ 3) * Nat.card ↥(Ec L T) := by ring
        _ ≤ (2 * k * q₀ ^ 3) * Nat.card ↥(Ec L T) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
        _ < q₀ ^ (2 * k) * Nat.card ↥(Ec L T) := Nat.mul_lt_mul_of_pos_right h2 hEpos
        _ ≤ Nat.card ↥A := hAle
    exact absurd hAB (not_le.2 hlt)

theorem cnt_alpha (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) (hE : Ec L T ≠ ⊥)
    {A : Subgroup G} (hA : IsFamily L T A)
    (hA1 : Dc L T ⊓ Subgroup.centralizer (A : Set G) ≤ A) {B : Subgroup G} (hBT : B ≤ T)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB1 : ¬ B ≤ Rl L T ⊔ Dc L T)
    (hBE : B ⊓ Ec L T = ⊥) : 2 * Nat.card B < Nat.card A := by
  obtain ⟨k, q₀, b₁, t, m, e, hcard, he, hq, hk, hq₀, hb₁, ht, hm, hbm, htq, ht1⟩ :=
    cnt_master hs hE1 hBT hBab hB1
  have hEe : 2 ≤ Nat.card ↥(Ec L T) := (Subgroup.one_lt_card_iff_ne_bot _).2 hE
  have hAle := family_card_le hs hE1 hA
  have he1 : e = 1 := by
    rw [he, inf_comm, hBE]
    exact Subgroup.card_bot
  rw [← hq] at hAle
  by_contra hcon
  have hAB : Nat.card ↥A ≤ 2 * Nat.card ↥B := not_lt.1 hcon
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    rw [he1] at hcard
    obtain ⟨hq2, hEe2, ht2, hAa⟩ := arith_alpha_two hq₀ hEe hbm htq hAle
      (by rw [hcard] at hAB; exact hAB)
    subst hq2
    have hnot : ¬ Dc L T ⊓ B ≤ blockU L ⊔ Ec L T := fun h => by
      have := ht1.2 h
      omega
    obtain ⟨d, hd, hdVE⟩ := Set.not_subset.1 hnot
    have hAeq : A = blockU L ⊔ Ec L T := by
      refine family_eq_sup_of_card_eq hs hE1 hA ?_
      rw [hAa, hEe2, ← hq]
      norm_num
    exact hdVE (mem_sup_of_centralizes hAeq hA1 hd.1 fun c hc =>
      Ec_central_of_card_two hs hE1 hEe2 (hBT hd.2) hc)
  · have h1 : b₁ * (t * (m * e)) ≤ q₀ ^ 2 * q₀ := by
      calc b₁ * (t * (m * e)) = (b₁ * m) * (t * e) := by ring
        _ ≤ q₀ ^ 2 * (q₀ * 1) := Nat.mul_le_mul hbm (Nat.mul_le_mul htq he1.le)
        _ = q₀ ^ 2 * q₀ := by ring
    have h2 := arith_ge_three hk3 hq₀
    have hEpos : 0 < Nat.card ↥(Ec L T) := by omega
    have h3 : (q₀ ^ k) ^ 2 = q₀ ^ (2 * k) := by
      rw [← pow_mul, mul_comm]
    rw [h3] at hAle
    have h4 : Nat.card ↥B ≤ k * (q₀ ^ 2 * q₀) := by
      rw [hcard]
      exact Nat.mul_le_mul_left _ h1
    have hlt : 2 * Nat.card ↥B < Nat.card ↥A := by
      calc 2 * Nat.card ↥B ≤ 2 * (k * (q₀ ^ 2 * q₀)) := Nat.mul_le_mul_left _ h4
        _ = (2 * k) * q₀ ^ 3 := by ring
        _ < q₀ ^ (2 * k) := h2
        _ ≤ q₀ ^ (2 * k) * Nat.card ↥(Ec L T) := Nat.le_mul_of_pos_right _ hEpos
        _ ≤ Nat.card ↥A := hAle
    exact absurd hAB (not_le.2 hlt)

theorem cnt (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) (hE : Ec L T ≠ ⊥)
    {A : Subgroup G} (hA : IsFamily L T A)
    (hA1 : Dc L T ⊓ Subgroup.centralizer (A : Set G) ≤ A) :
    ∀ B : Subgroup G, B ≤ T → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      ¬ B ≤ Rl L T ⊔ Dc L T →
        Nat.card B < Nat.card A ∧ (B ⊓ Ec L T = ⊥ → 2 * Nat.card B < Nat.card A) :=
  fun _ hBT hBab hB1 => ⟨cnt_beta hs hE1 hE hA hA1 hBT hBab hB1,
    fun hBE => cnt_alpha hs hE1 hE hA hA1 hBT hBab hB1 hBE⟩

theorem cnt_of_maximal (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) (hE : Ec L T ≠ ⊥)
    {A : Subgroup G} (hA : IsMaximalFamily L T A) :
    ∀ B : Subgroup G, B ≤ T → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      ¬ B ≤ Rl L T ⊔ Dc L T →
        Nat.card B < Nat.card A ∧ (B ⊓ Ec L T = ⊥ → 2 * Nat.card B < Nat.card A) :=
  cnt hs hE1 hE hA.1 (family_Dc_inf_centralizer_eq hs hE1 hA).le

end CFSG.CGT.PushingUpLit.T2KSW
