module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16b

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.E16

open CFSG Subgroup ThmC CFSG.GH74.GLS.Bg.TwoGroups

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_perfect {G : Type*} [Group G] [Finite G]
    (hG : commutator G = ⊤) (S : Sylow 2 G) [IsMulCommutative (S : Subgroup G)] {v : G}
    (hvS : v ∈ (S : Subgroup G)) (hv : v ∈ center G) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * v ^ k * g₀ ∈ (S : Subgroup G) →
      g₀⁻¹ * v ^ k * g₀ = v ^ k := fun k g₀ _ => by
    rw [mul_assoc, ← (mem_center_iff.mp (pow_mem hv k) g₀), inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup G)) v key
  have h2 : MonoidHom.transfer (MonoidHom.id (S : Subgroup G)) v = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker _ (by rw [hG]; exact mem_top v))
  rw [h2] at h1
  have h3 : v ^ (S : Subgroup G).index = 1 := (congrArg Subtype.val h1).symm
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨v, hvS⟩
  have h4 : v ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  have hcop : Nat.Coprime (2 ^ k) (S : Subgroup G).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index)
  have h5 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h4) hcop)
    (orderOf_dvd_of_pow_eq_one h3)
  exact orderOf_eq_one_iff.mp h5

variable {X : Type} [Group X] [Finite X]

variable (D : ThmC.UTSylow X)

theorem eq_one_of_central (hG : CFSG.Goldschmidt.TopStatement) (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E)
    {v : X} (hvT : v ∈ (D.T : Subgroup X)) (hvL : v ∈ gL D.E)
    (hv : ∀ l ∈ gL D.E, v * l = l * v) : v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL := T_inf_gL_le_E D hG hO hcl
  obtain ⟨S, hS⟩ :=
    CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal D.T (gL_normal D.E).isSubnormal
  have hmem : ∀ a : gL D.E, a ∈ (S : Subgroup (gL D.E)) → (a : X) ∈ D.E := fun a ha => by
    have h := mem_map_of_mem (gL D.E).subtype ha
    rw [hS] at h
    exact hTL h
  have : IsMulCommutative (S : Subgroup (gL D.E)) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (D.E_comm (hmem _ a.2) (hmem _ b.2)))⟩⟩
  have hvS : (⟨v, hvL⟩ : gL D.E) ∈ (S : Subgroup (gL D.E)) := by
    have h : v ∈ (S : Subgroup (gL D.E)).map (gL D.E).subtype := by
      rw [hS]
      exact mem_inf.mpr ⟨hvT, hvL⟩
    obtain ⟨w, hw, hwv⟩ := h
    rwa [show w = ⟨v, hvL⟩ from Subtype.ext hwv] at hw
  have hvc : (⟨v, hvL⟩ : gL D.E) ∈ center (gL D.E) :=
    mem_center_iff.mpr fun l => Subtype.ext (hv l l.2).symm
  exact congrArg Subtype.val
    (eq_one_of_mem_center_of_perfect (gL_isPerfect D.E).commutator_eq_top S hvS hvc)

structure CaseB : Prop where
  E_le : D.E ≤ gL D.E
  T_inf_le : (D.T : Subgroup X) ⊓ gL D.E ≤ D.E
  eq_one : ∀ K, gComp D.E K → ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1
  type : ∀ K, gComp D.E K → CFSG.Open.goldschmidtSimpleType K

theorem caseB_of (hG : CFSG.Goldschmidt.TopStatement) (hO : pPrimeCore 2 X = ⊥)
    (hcl : ∀ a ∈ D.E, ∀ g : X, g⁻¹ * a * g ∈ (D.T : Subgroup X) → g⁻¹ * a * g ∈ D.E)
    (hZ : D.Z ≤ (D.T : Subgroup X) ⊓ gL D.E) : CaseB D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hE, hcomp⟩ := gold_facts hG hO D.T D.E_le_T (E_isMulCommutative D) hcl
  have hTL := T_inf_gL_le_E D hG hO hcl
  set W := closure {t | t ∈ (D.T : Subgroup X) ⊓ gL D.E ∧ t ^ 2 = 1}
  have hPE : gP D.E ≤ D.E := le_sup_left.trans hE.ge
  have hWTL : W ≤ (D.T : Subgroup X) ⊓ gL D.E := (closure_le _).mpr fun t ht => ht.1
  have hPL : ∀ p ∈ gP D.E, p ∈ gL D.E → p = 1 := fun p hp hpL =>
    eq_one_of_central D hG hO hcl (D.E_le_T (hPE hp)) hpL (gP_comm_gL D.E p hp)
  have hP : gP D.E = ⊥ := by
    have hPT : ∀ t ∈ (D.T : Subgroup X), ∀ p ∈ gP D.E, t * p * t⁻¹ ∈ gP D.E :=
      fun t _ p hp => (gP_normal D.E).conj_mem p hp t
    rcases D.le_Z_or_Z_le hPE hPT with hPZ | hZP
    · exact eq_bot_iff.mpr fun p hp => mem_bot.mpr (hPL p hp (mem_inf.mp (hZ (hPZ hp))).2)
    · exfalso
      have hz : D.toX ⟨0, 0, 1⟩ ∈ D.Z := D.toX_mem_Z_iff.mpr ⟨rfl, rfl⟩
      have h1 := hPL _ (hZP hz) (mem_inf.mp (hZ hz)).2
      have h2 := D.toX_injective (h1.trans (map_one D.toX).symm)
      exact absurd (congrArg UT3.c h2) (by decide)
  have hEW : D.E = W := by
    rw [hP, bot_sup_eq] at hE
    exact hE
  have hEL : D.E ≤ gL D.E := fun e he => (mem_inf.mp (hWTL (hEW.le he))).2
  have hZL : ∀ v ∈ gL D.E, (∀ l ∈ gL D.E, v * l = l * v) → v = 1 := by
    have := gL_normal D.E
    set C := gL D.E ⊓ centralizer (gL D.E : Set X)
    have hCn : C.Normal := inferInstance
    have hCT : (D.T : Subgroup X) ⊓ C = ⊥ := eq_bot_iff.mpr fun v hv => by
      obtain ⟨hvT, hvL, hvc⟩ := hv
      exact mem_bot.mpr (eq_one_of_central D hG hO hcl hvT hvL fun l hl =>
        (mem_centralizer_iff.mp hvc l hl).symm)
    obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal D.T hCn.isSubnormal
    rw [hCT] at hQ
    have hQb : (Q : Subgroup C) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (subtype_injective _)).mp hQ
    have hodd : Odd (Nat.card C) := by
      have h := Q.not_dvd_index
      rw [hQb, index_bot] at h
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
    have hCb := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hO hCn.isSubnormal hodd
    intro v hvL hv
    have hvC : v ∈ C := mem_inf.mpr ⟨hvL, mem_centralizer_iff.mpr fun l hl => (hv l hl).symm⟩
    rw [hCb] at hvC
    exact mem_bot.mp hvC
  have hKc : ∀ K, gComp D.E K → ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1 := by
    intro K hK k hk hkc
    have hLc : gL D.E ≤ centralizer ({k} : Set X) := by
      rw [gL_eq_sSup]
      refine sSup_le fun K' hK' y hy => mem_centralizer_singleton_iff.mpr ?_
      by_cases hKK : K' = K
      · subst hKK
        exact (hkc y hy).symm
      · exact gComp_comm hK' hK hKK y hy k hk
    exact hZL k (gComp_le hK hk) fun l hl => (mem_centralizer_singleton_iff.mp (hLc hl)).symm
  refine ⟨hEL, hTL, hKc, fun K hK => gComp_type hcomp hK (eq_bot_iff.mpr fun z hz => ?_)⟩
  exact mem_bot.mpr (Subtype.ext (hKc K hK z z.2 fun k' hk' =>
    (congrArg Subtype.val (mem_center_iff.mp hz ⟨k', hk'⟩)).symm))

end CFSG.ComponentClassification.GHarris.E16
