module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private lemma centerOf_eq_map_center' {C : Type*} [Group C] (Q : Subgroup C) :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (g : C) g.2)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

private lemma conj_iterate_apply {K : Type*} [Group K] (ρ q : K) (n : ℕ) :
    (fun a : K => ρ * a * ρ⁻¹)^[n] q = ρ ^ n * q * (ρ ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      group

theorem card_commute_eq_of_fixed_five {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {x ρ ζ : K} (hζ : centerOf Q = Subgroup.zpowers ζ)
    (hζc : ∀ g : K, g * ζ = ζ * g) (hρ5 : orderOf ρ = 5) (hρx : ρ * x = x * ρ)
    (hρQ : Q ⊓ Subgroup.centralizer ({ρ} : Set K) = centerOf Q)
    (hW : Nat.card {q : K // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} = 2 ^ 5) :
    Nat.card {q : K // q ∈ Q ∧ q * x = x * q} = 2 ^ 5 := by
  classical
  have hZcard : Nat.card ↥(centerOf Q) = 2 := by
    rw [centerOf_eq_map_center', Subgroup.card_map_of_injective Q.subtype_injective]
    exact hQ.1.center_order_p
  have hζorder : orderOf ζ = 2 := by
    rw [← Nat.card_zpowers ζ, ← hζ, hZcard]
  have hζcenter : ζ ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr hζc
  have hZ_le_center : centerOf Q ≤ Subgroup.center K := by
    rw [hζ]
    exact Subgroup.zpowers_le.mpr hζcenter
  have hZQcomm : ∀ z ∈ centerOf Q, ∀ q ∈ Q, q * z = z * q := by
    intro z hz q hq
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 q hq
  let Wsub : Subgroup K :=
    { carrier := {q | q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q}
      one_mem' := ⟨Q.one_mem, by rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haQ, haZ⟩ := ha
        obtain ⟨hbQ, hbZ⟩ := hb
        refine ⟨Q.mul_mem haQ hbQ, ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hconj : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
          rw [hZQcomm _ hbZ a haQ]; group
        rw [hconj]
        exact mul_mem hbZ haZ
      inv_mem' := by
        intro a ha
        obtain ⟨haQ, haZ⟩ := ha
        refine ⟨Q.inv_mem haQ, ?_⟩
        rw [commutatorElement_inv_left, ← commutatorElement_inv a x]
        have hconj : a⁻¹ * ⁅a, x⁆⁻¹ * a = ⁅a, x⁆⁻¹ := by
          rw [hZQcomm _ (inv_mem haZ) a⁻¹ (Q.inv_mem haQ)]; group
        rw [hconj]
        exact inv_mem haZ }
  have hWsub_card : Nat.card ↥Wsub = 2 ^ 5 := hW
  let φ : ↥Wsub →* ↥(centerOf Q) :=
    { toFun := fun w => ⟨⁅w.1, x⁆, w.2.2⟩
      map_one' := by
        apply Subtype.ext
        show ⁅(1 : K), x⁆ = 1
        rw [commutatorElement_one_left]
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ⁅a.1 * b.1, x⁆ = ⁅a.1, x⁆ * ⁅b.1, x⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hconj : a.1 * ⁅b.1, x⁆ * a.1⁻¹ = ⁅b.1, x⁆ := by
          rw [hZQcomm _ b.2.2 a.1 a.2.1]; group
        rw [hconj]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp b.2.2).2
          ⁅a.1, x⁆ (Subgroup.mem_inf.mp a.2.2).1).symm }
  have hker_goal : Nat.card ↥φ.ker = Nat.card {q : K // q ∈ Q ∧ q * x = x * q} := by
    let toF : ↥φ.ker → {q : K // q ∈ Q ∧ q * x = x * q} := fun w =>
      ⟨w.1.1, w.1.2.1,
        commutatorElement_eq_one_iff_mul_comm.mp
          (congrArg (fun t : ↥(centerOf Q) => t.1) (MonoidHom.mem_ker.mp w.2))⟩
    let invF : {q : K // q ∈ Q ∧ q * x = x * q} → ↥φ.ker := fun c =>
      ⟨⟨c.1, ⟨c.2.1, by
          rw [commutatorElement_eq_one_iff_mul_comm.mpr c.2.2]
          exact Subgroup.one_mem _⟩⟩, by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        show ⁅c.1, x⁆ = 1
        exact commutatorElement_eq_one_iff_mul_comm.mpr c.2.2⟩
    refine Nat.card_congr ⟨toF, invF, ?_, ?_⟩
    · intro w
      apply Subtype.ext
      apply Subtype.ext
      rfl
    · intro c
      apply Subtype.ext
      rfl
  have hrange_dvd : Nat.card ↥φ.range ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hZcard] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hrange_dvd with hrange | hrange
  ·
    have hker : Nat.card ↥φ.ker = 2 ^ 5 := by
      have h := Subgroup.card_ker_mul_card_range φ
      rw [hWsub_card, hrange, mul_one] at h
      exact h
    rw [← hker_goal]
    exact hker
  ·
    exfalso
    have hker : Nat.card ↥φ.ker = 16 := by
      have h := Subgroup.card_ker_mul_card_range φ
      rw [hWsub_card, hrange] at h
      omega
    let f : Function.End ↥φ.ker := fun w => by
      have hq1 : ⁅w.1.1, x⁆ = 1 :=
        congrArg (fun t : ↥(centerOf Q) => t.1) (MonoidHom.mem_ker.mp w.2)
      have hconj : ⁅ρ * w.1.1 * ρ⁻¹, x⁆ = ρ * ⁅w.1.1, x⁆ * ρ⁻¹ := by
        have h1 : ⁅ρ * w.1.1 * ρ⁻¹, ρ * x * ρ⁻¹⁆ = ⁅ρ * w.1.1 * ρ⁻¹, x⁆ := by
          rw [show ρ * x * ρ⁻¹ = x by rw [hρx]; group]
        rw [← h1, ← conjugate_commutatorElement]
      refine ⟨⟨ρ * w.1.1 * ρ⁻¹, ⟨?_, ?_⟩⟩, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance w.1.1 w.1.2.1 ρ
      · rw [hconj, hq1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        show ⁅ρ * w.1.1 * ρ⁻¹, x⁆ = 1
        rw [hconj, hq1, mul_one, mul_inv_cancel]
    haveI : Fintype ↥φ.ker := Fintype.ofFinite _
    have hf5 : f ^ 5 ^ 1 = 1 := by
      funext w
      apply Subtype.ext
      apply Subtype.ext
      have hiter : ∀ n : ℕ,
          (f^[n] w).1.1 = (fun a : K => ρ * a * ρ⁻¹)^[n] w.1.1 := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [Function.iterate_succ_apply']
            change ρ * (f^[n] w).1.1 * ρ⁻¹ =
              (fun a : K => ρ * a * ρ⁻¹)^[n + 1] w.1.1
            rw [Function.iterate_succ_apply', ih]
      show (f^[5] w).1.1 = w.1.1
      rw [hiter 5, conj_iterate_apply]
      rw [show ρ ^ 5 = 1 by rw [← hρ5, pow_orderOf_eq_one]]
      group
    have hfix : Fintype.card (Function.fixedPoints f) = 2 := by
      rw [← Nat.card_eq_fintype_card, ← hZcard]
      let toF : (Function.fixedPoints f) → ↥(centerOf Q) := fun w =>
        ⟨w.1.1.1, by
          have hval : ρ * w.1.1.1 * ρ⁻¹ = w.1.1.1 :=
            congrArg (fun t : ↥φ.ker => t.1.1) w.2
          have hcent : w.1.1.1 ∈ Subgroup.centralizer ({ρ} : Set K) := by
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            rw [Set.mem_singleton_iff] at hh
            rw [hh]
            calc ρ * w.1.1.1 = ρ * w.1.1.1 * ρ⁻¹ * ρ := by group
              _ = w.1.1.1 * ρ := by rw [hval]
          have hmem : w.1.1.1 ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set K) :=
            Subgroup.mem_inf.mpr ⟨w.1.1.2.1, hcent⟩
          rw [hρQ] at hmem
          exact hmem⟩
      let invF : ↥(centerOf Q) → (Function.fixedPoints f) := fun z => by
        have hzQ : z.1 ∈ Q := (Subgroup.mem_inf.mp z.2).1
        have hzcomm : z.1 * x = x * z.1 :=
          (Subgroup.mem_center_iff.mp (hZ_le_center z.2) x).symm
        have hzZ : ⁅z.1, x⁆ ∈ centerOf Q := by
          rw [commutatorElement_eq_one_iff_mul_comm.mpr hzcomm]
          exact Subgroup.one_mem _
        refine ⟨⟨⟨z.1, ⟨hzQ, hzZ⟩⟩, ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker]
          apply Subtype.ext
          show ⁅z.1, x⁆ = 1
          exact commutatorElement_eq_one_iff_mul_comm.mpr hzcomm
        · apply Subtype.ext
          apply Subtype.ext
          show ρ * z.1 * ρ⁻¹ = z.1
          have hzρmem : z.1 ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set K) := by
            rw [hρQ]; exact z.2
          have hzρ : ρ * z.1 = z.1 * ρ :=
            Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzρmem).2 ρ (by simp)
          rw [hzρ]; group
      refine Nat.card_congr ⟨toF, invF, ?_, ?_⟩
      · intro w
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl
      · intro z
        apply Subtype.ext
        rfl
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
    have hmod' : Nat.card ↥φ.ker ≡ Nat.card (Function.fixedPoints f) [MOD 5] := by
      have h1 : Nat.card ↥φ.ker = Fintype.card ↥φ.ker := Nat.card_eq_fintype_card
      have h2 : Nat.card (Function.fixedPoints f) = Fintype.card (Function.fixedPoints f) :=
        Nat.card_eq_fintype_card
      rw [h1, h2]
      exact hmod
    have hfix_nat : Nat.card (Function.fixedPoints f) = 2 := by
      rw [Nat.card_eq_fintype_card]; exact hfix
    rw [hker, hfix_nat] at hmod'
    exact absurd hmod' (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section3
