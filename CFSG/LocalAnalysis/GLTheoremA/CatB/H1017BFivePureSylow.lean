module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSeven

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Blueprint CFSG.Monster.GMS Subgroup
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

section Generic

private theorem factorization_five_babyCentOrder {k : Fin 4} (hk : k ≠ 1) :
    (babyCentOrder k).factorization 5 = 2 := by
  have hk' : 5 ^ 2 ∣ babyCentOrder k ∧ ¬ 5 ^ 3 ∣ babyCentOrder k := by
    revert hk
    fin_cases k <;> decide
  have hn : babyCentOrder k ≠ 0 := fun h => hk'.2 (h ▸ dvd_zero _)
  have e1 := (Nat.prime_five.pow_dvd_iff_le_factorization hn).1 hk'.1
  have e2 := mt (Nat.prime_five.pow_dvd_iff_le_factorization hn).2 hk'.2
  omega

variable {G : Type*} [Group G]

private theorem orderOf_conj_eq (g y : G) : orderOf (g * y * g⁻¹) = orderOf y := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

private theorem mul_comm_of_mem_inf {a b y : G}
    (hy : y ∈ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) :
    y * (a * b) = a * b * y := by
  have ha : y * a = a * y := mem_centralizer_singleton_iff.1 (mem_inf.1 hy).1
  have hb : y * b = b * y := mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2
  rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

private theorem exists_le_card_of_dvd [Finite G] {p n : ℕ} [Fact p.Prime] {H : Subgroup G}
    (h : p ^ n ∣ Nat.card H) : ∃ K ≤ H, Nat.card K = p ^ n := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p h
  exact ⟨K.map H.subtype, map_subtype_le K, by rw [card_map_of_injective H.subtype_injective, hK]⟩

private theorem exists_conj_mem_of_conj [Finite G] {t t₀ c y₀ : G} (hct : c * t * c⁻¹ = t₀)
    {F : Subgroup G} (hFt : F ≤ centralizer ({t} : Set G))
    (hF : Nat.card F = 5 ^ (Nat.card (centralizer ({t₀} : Set G))).factorization 5)
    (hy₀ : y₀ ^ 5 = 1) (hc : y₀ * t₀ = t₀ * y₀) : ∃ g : G, g * y₀ * g⁻¹ ∈ F := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hF' : F.map (MulAut.conj c).toMonoidHom ≤ centralizer ({t₀} : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    have hft : f * t = t * f := mem_centralizer_singleton_iff.1 (hFt hf)
    rw [mem_centralizer_singleton_iff, ← hct]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * f * c⁻¹ * (c * t * c⁻¹) = c * (f * t) * c⁻¹ := by group
      _ = c * (t * f) * c⁻¹ := by rw [hft]
      _ = c * t * c⁻¹ * (c * f * c⁻¹) := by group
  have hcard : Nat.card (F.map (MulAut.conj c).toMonoidHom) =
      5 ^ (Nat.card (centralizer ({t₀} : Set G))).factorization 5 := by
    rw [card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective, hF]
  obtain ⟨d, -, hd⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.exists_conj_mem_of_card hF' hcard
      (mem_centralizer_singleton_iff.2 hc) hy₀
  obtain ⟨f, hf, hfd⟩ := mem_map.1 hd
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfd
  refine ⟨c⁻¹ * d, ?_⟩
  have e : (c⁻¹ * d) * y₀ * (c⁻¹ * d)⁻¹ = f := by
    calc (c⁻¹ * d) * y₀ * (c⁻¹ * d)⁻¹ = c⁻¹ * (d * y₀ * d⁻¹) * c := by group
      _ = c⁻¹ * (c * f * c⁻¹) * c := by rw [hfd]
      _ = f := by group
  rw [e]
  exact hf

end Generic

theorem exists_fiveA_mem_of_witness_B (hT3 : BabyTableIII) {k : Fin 4} (hk : k ≠ 1)
    {t₀ y₀ : NativeSporadic.B} (ht₀ : BabyInv k t₀) (hy₀ : orderOf y₀ = 5)
    (hr₀ : Matrix.rank (CFSG.Monster.B.bMat y₀ - 1) = 3480) (hc : y₀ * t₀ = t₀ * y₀)
    {t : NativeSporadic.B} (ht : BabyInv k t) {F : Subgroup NativeSporadic.B}
    (hFt : F ≤ centralizer ({t} : Set NativeSporadic.B)) (hF : Nat.card F = 5 ^ 2) :
    ∃ y ∈ F, orderOf y = 5 ∧ Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨c, hct⟩ := isConj_iff.1 (hT3.2 k t t₀ ht ht₀)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_conj hct hFt
    (by rw [hF, ht₀.2, factorization_five_babyCentOrder hk])
    (by rw [← hy₀]; exact pow_orderOf_eq_one y₀) hc
  exact ⟨_, hg, (orderOf_conj_eq g y₀).trans hy₀,
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.rank_bMat_conj g y₀).trans hr₀⟩


theorem exists_fiveA_mem_of_babyInv_zero_B
    {t : NativeSporadic.B} (ht : BabyInv 0 t)
    {F : Subgroup NativeSporadic.B} (hFt : F ≤ centralizer ({t} : Set NativeSporadic.B))
    (hF : Nat.card F = 5 ^ 2) :
    ∃ y ∈ F, orderOf y = 5 ∧ Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have P := bSevenElem_parts
  exact exists_fiveA_mem_of_witness_B CFSG.Monster.Existence.babyTableIII (by decide)
    (babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank)
    (orderOf_eq_prime P.y_pow P.y_ne) CFSG.HardMathSupport.Dickson.I271.TabMFive.rank_ySeven
    P.alpha_y.symm ht hFt hF

theorem exists_fiveA_mem_of_babyInv_three_B
    {t : NativeSporadic.B} (ht : BabyInv 3 t)
    {F : Subgroup NativeSporadic.B} (hFt : F ≤ centralizer ({t} : Set NativeSporadic.B))
    (hF : Nat.card F = 5 ^ 2) :
    ∃ y ∈ F, orderOf y = 5 ∧ Matrix.rank (CFSG.Monster.B.bMat y - 1) = 3480 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have P := bSevenElem_parts
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  obtain ⟨s, hs, hαs⟩ : {s | BabyInv 0 s ∧ BabyOrbit 1 alphaB s}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      rw [(CFSG.Monster.Existence.babyTableIV alphaB hα).2.2 1]
      decide)
  have hN := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.card_inf_mul_babyOrbitSize
    CFSG.Monster.Existence.babyTableIV hα hs hαs
  have h25 : 5 ^ 2 ∣ Nat.card (centralizer ({alphaB} : Set NativeSporadic.B) ⊓
      centralizer ({s} : Set NativeSporadic.B) : Subgroup NativeSporadic.B) := by
    have hco : Nat.Coprime (5 ^ 2) (babyOrbitSize 1) := by decide
    refine hco.dvd_of_dvd_mul_right ?_
    rw [hN]
    decide
  obtain ⟨K, hKH, hKc⟩ := exists_le_card_of_dvd h25
  obtain ⟨y₀, hy₀K, hy₀, hr₀⟩ :=
    exists_fiveA_mem_of_babyInv_zero_B hα (hKH.trans inf_le_left) hKc
  have hc := mul_comm_of_mem_inf (hKH hy₀K)
  exact exists_fiveA_mem_of_witness_B CFSG.Monster.Existence.babyTableIII (by decide)
    (show BabyInv 3 (alphaB * s) from hαs) hy₀ hr₀ hc ht hFt hF

end CFSG.LocalAnalysis.GLTheoremA.H1017
