module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem13
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

theorem stmt6_1_13_F4 (h432 : Stmt4_3_2_F4) (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) :
    Stmt6_1_13_F4 := by
  classical
  intro G _ _ T M L V n h U hUV hmU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := h.hypE61_F4 h432
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le

  have hUcard : Nat.card U = 2 ^ n := by
    have hrel : U.relIndex V ∣ 2 ^ (n + n) := by
      rw [pow_add, ← hVcard]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
    have hjn : j = n := by
      unfold mQuot at hmU
      rw [hj, padicValNat.prime_pow] at hmU
      exact hmU
    have h1 := card_mul_relIndex_of_le hUV
    rw [hj, hjn, hVcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hUcard
    omega
  by_cases hCM : M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G)
  ·
    left
    by_contra hCU
    have hCUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun hle => hCU fun c hc =>
      (h.normalizer_le hU1 hUV ⟨hle hc, Subgroup.centralizer_le_normalizer _ hc⟩).2
    have hr1 := (hE612 G T M V U hE hU1 hUV hCM hCUM).2
    have hr := (h6110 G T M L V n h).1
    rw [hr1] at hr
    have : n ≤ 1 := by exact_mod_cast hr
    have := h.two_le
    omega
  right

  have hle : M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left M (Subgroup.centralizer_le hUV)
  obtain ⟨m, ⟨hmM, hmU'⟩, hmV⟩ : ∃ m ∈ M ⊓ Subgroup.centralizer (U : Set G),
      m ∉ M ⊓ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hCM (le_antisymm hcon hle)
  have hmV' : m ∉ Subgroup.centralizer (V : Set G) := fun hc => hmV ⟨hmM, hc⟩
  have hmN : m ∈ Subgroup.normalizer (V : Set G) :=
    (h.normalizer_le hU1 hUV ⟨hmM, Subgroup.centralizer_le_normalizer _ hmU'⟩).2
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := h.normal hmM
  set D := h.data with hD
  set mm : Subgroup.normalizer (V : Set G) := ⟨m, hmN⟩ with hmm
  obtain ⟨σ, hσ⟩ := D.exists_semilinear mm hmL

  have hUC : U = V ⊓ Subgroup.centralizer ({m} : Set G) := by
    have hsub : U ≤ V ⊓ Subgroup.centralizer ({m} : Set G) := fun u hu =>
      ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hmU' u hu).symm⟩
    exact Subgroup.eq_of_le_of_card_ge hsub
      (by rw [hUcard]; exact D.card_fixed_le_two_pow mm hmL hmV')
  have hfixcard : Nat.card {w : Fin 2 → D.K // D.conj mm w = w} = 2 ^ n := by
    rw [← Nat.card_congr (D.fixedEquiv mm), ← hUC, hUcard]

  have hmemU : ∀ u (hu : u ∈ V), u ∈ U ↔
      D.conj mm (Multiplicative.toAdd (D.E ⟨u, hu⟩)) = Multiplicative.toAdd (D.E ⟨u, hu⟩) := by
    intro u hu
    rw [hUC]
    constructor
    · rintro ⟨-, hc⟩
      exact D.conj_E_eq_of_commute mm ⟨u, hu⟩
        ((Subgroup.mem_centralizer_iff.mp hc m rfl))
    · intro hfix
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      rw [D.conj_apply] at hfix
      have h2 := congrArg Subtype.val (D.E.injective (Multiplicative.toAdd.injective hfix))
      rw [conjAct_apply_coe] at h2
      have h3 : m * u * m⁻¹ = u := h2
      calc m * u = (m * u * m⁻¹) * m := by group
        _ = u * m := by rw [h3]
  by_cases hσid : ∀ c, σ c = c
  ·
    left
    have hlin : ∀ (a : D.K) (w : Fin 2 → D.K), D.conj mm (a • w) = a • D.conj mm w :=
      fun a w => by rw [hσ, hσid]
    have hF : 1 < Nat.card D.K := by rw [D.card]; omega
    obtain ⟨x, hx0, hx⟩ := exists_line_of_card_fixed (D.conj mm) hlin
      (by rw [hfixcard, D.card]) hF
    exact h.exists_conj_ZS_of_line hUV hx0 fun u hu => (hmemU u hu).trans (hx _)
  ·
    right
    push Not at hσid
    obtain ⟨θ, hθ⟩ := hσid
    have hle1 := card_fixed_le_fix_mul_self (D.conj mm) σ hσ
    have hle2 := card_fixed_mul_self_le σ hθ
    rw [hfixcard] at hle1
    rw [D.card] at hle2
    have hF0 : Nat.card {c : D.K // σ c = c} * Nat.card {c : D.K // σ c = c} = 2 ^ n :=
      le_antisymm hle2 hle1

    have hEven : Even n := by
      have hdvd : Nat.card {c : D.K // σ c = c} ∣ 2 ^ n := Dvd.intro _ hF0
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hk, ← pow_add] at hF0
      exact ⟨k, (Nat.pow_right_injective (le_refl 2) hF0).symm⟩

    have hσ2 : σ * σ = 1 := mul_self_eq_one_of_card σ hθ (by rw [hF0, D.card])

    have hm2 : m * m ∈ Subgroup.centralizer (V : Set G) := by
      by_contra hc
      have hmm2 : mm * mm = ⟨m * m, (Subgroup.normalizer (V : Set G)).mul_mem hmN hmN⟩ := rfl
      have hlin2 : ∀ (a : D.K) (w : Fin 2 → D.K),
          D.conj (mm * mm) (a • w) = a • D.conj (mm * mm) w := by
        intro a w
        rw [D.conj_mul, D.conj_mul, hσ, hσ]
        change (σ * σ) a • _ = _
        rw [hσ2]
        rfl
      have hne : ∃ w, D.conj (mm * mm) w ≠ w := by
        by_contra hcon
        push Not at hcon
        exact hc (D.mem_centralizer_of_conj_eq (mm * mm) hcon)
      have hle3 := card_fixed_le_semilinear (D.conj (mm * mm)) (RingEquiv.refl D.K)
        (fun a w => hlin2 a w) hne
      rw [D.card] at hle3

      have hsubset : ∀ w, D.conj mm w = w → D.conj (mm * mm) w = w := fun w hw => by
        rw [D.conj_mul, hw, hw]
      have heq : ∀ w, D.conj (mm * mm) w = w → D.conj mm w = w := by
        intro w hw
        by_contra hw'
        have hinj : Function.Injective (fun v : {v : Fin 2 → D.K // D.conj mm v = v} =>
            (⟨v.1, hsubset v.1 v.2⟩ : {v : Fin 2 → D.K // D.conj (mm * mm) v = v})) :=
          fun a b hab => by
            have h1 := congrArg Subtype.val hab
            exact Subtype.ext h1
        have hnotsurj : ¬ Function.Surjective (fun v : {v : Fin 2 → D.K // D.conj mm v = v} =>
            (⟨v.1, hsubset v.1 v.2⟩ : {v : Fin 2 → D.K // D.conj (mm * mm) v = v})) := by
          intro hs
          obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
          have h1 : v.1 = w := congrArg Subtype.val hv
          exact hw' (h1 ▸ v.2)
        apply hnotsurj
        exact (hinj.bijective_of_nat_card_le (by rw [hfixcard]; exact hle3)).2

      obtain ⟨x, hx0, hx⟩ : ∃ x : Fin 2 → D.K, x ≠ 0 ∧ D.conj mm x = x := by
        by_contra hcon
        push Not at hcon
        have hsub : Subsingleton {v : Fin 2 → D.K // D.conj mm v = v} :=
          ⟨fun a b => Subtype.ext (by
            have ha : a.1 = 0 := by by_contra hne; exact hcon a.1 hne a.2
            have hb : b.1 = 0 := by by_contra hne; exact hcon b.1 hne b.2
            rw [ha, hb])⟩
        have := Finite.card_le_one_iff_subsingleton.mpr hsub
        rw [hfixcard] at this
        omega
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      simp only [Pi.zero_apply] at hi
      apply hθ
      have h1 := heq (θ • x) (by rw [hlin2, hsubset x hx])
      rw [hσ, hx] at h1
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hi this
    refine ⟨hEven, m, hmM, ⟨hmL, ?_, ?_⟩, hUC⟩
    ·
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer hx
      refine h.toHyp5_0_1.inf_centralizer_le D.le_normalizer h.module.2.2 ⟨?_, ?_⟩
      · have h1 : m ^ 2 * x * (m ^ 2)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).pow_mem hmL 2) x).mp
            hx
        exact L.mul_mem h1 (L.inv_mem hx)
      · have hm2' : m ^ 2 ∈ Subgroup.centralizer (V : Set G) := by rw [pow_two]; exact hm2
        have h1 : x * (m ^ 2)⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
          exact (Subgroup.mem_normalizer_iff.mp
            (F7.normalizer_le_normalizer_centralizer V hxN) ((m ^ 2)⁻¹)).mp
            (Subgroup.inv_mem _ hm2')
        have e : m ^ 2 * x * (m ^ 2)⁻¹ * x⁻¹ = m ^ 2 * (x * (m ^ 2)⁻¹ * x⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hm2' h1
    ·
      rintro ⟨y, hyL, hy⟩
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer hyL
      set m' : Subgroup.normalizer (V : Set G) := ⟨y⁻¹ * m, Subgroup.mul_mem _
        (Subgroup.inv_mem _ hyN) hmN⟩ with hm'
      have hcomm : ∀ g ∈ L, (m' : G) * g * (m' : G)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        intro g hg
        have h1 := hy g hg
        have h2 : y⁻¹ * ((m * g * m⁻¹) * (y * g * y⁻¹)⁻¹) * y ∈ pCoreOf 2 L := by
          have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (L.inv_mem hyL)
          have := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
          simpa [mul_assoc] using this
        have e : (m' : G) * g * (m' : G)⁻¹ * g⁻¹ =
            y⁻¹ * ((m * g * m⁻¹) * (y * g * y⁻¹)⁻¹) * y := by
          simp only [hm']
          group
        rw [e]
        exact h.toHyp611.pCoreOf_le_centralizer h2
      obtain ⟨c, hc⟩ := D.exists_conj_eq_smul m' hcomm

      apply hθ
      have hmy : mm = ⟨y, hyN⟩ * m' := Subtype.ext (by simp [hm', hmm])
      obtain ⟨B, hB⟩ := D.exists_matrix_of_mem ⟨y, hyN⟩ hyL
      have hlin : ∀ (a : D.K) (w : Fin 2 → D.K), D.conj mm (a • w) = a • D.conj mm w := by
        intro a w
        rw [hmy, D.conj_mul, D.conj_mul, hc, hc, hB, hB, smul_smul, mul_comm, ← smul_smul,
          Matrix.mulVec_smul]
      have := semilinear_unique (D.conj mm) hσ (τ := RingEquiv.refl D.K) (fun a w => hlin a w)
      rw [this]
      rfl

end CFSG.Quasithin.H13
