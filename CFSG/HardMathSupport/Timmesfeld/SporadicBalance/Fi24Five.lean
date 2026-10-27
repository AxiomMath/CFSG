module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
public import CFSG.Sporadic.FischerOddCore.Fi24Stab
public import CFSG.Sporadic.Fi24.PtGraphBridge
public import Certificates.Certificate16947
public import CFSG.Sporadic.Fi24.OctadAction

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi24.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 MR)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

namespace Fi24Five

section General

variable {T M : Type*} [Group T] [Group M]

theorem map_centralizer_singleton_eq {f : T →* M} (hf : Function.Injective f) (t : T) :
    (Subgroup.centralizer ({t} : Set T)).map f = Subgroup.centralizer ({f t} : Set M) ⊓ f.range := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [← map_mul, hx, map_mul], x, rfl⟩
  · rintro ⟨hy, x, rfl⟩
    refine ⟨x, hf ?_, rfl⟩
    rw [map_mul, map_mul, hy]

end General

section Class

theorem D24_mul_self {x : R} (hx : x ∈ D24) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [CFSG.Sporadic.Fi24.orderOf_mem_D24 hx, sq] at h
  exact h

theorem D24_ne_one {x : R} (hx : x ∈ D24) : x ≠ 1 := by
  intro h
  have h2 := CFSG.Sporadic.Fi24.orderOf_mem_D24 hx
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem D24_conj {x : R} (hx : x ∈ D24) (g : R) : g * x * g⁻¹ ∈ D24 :=
  IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩)

theorem D24_cube {x y : R} (hx : x ∈ D24) (hy : y ∈ D24) (hne : x * y ≠ y * x) :
    x * y * (x * y) * (x * y) = 1 := by
  rcases CFSG.Sporadic.Fi24.orderOf_mul_mem_D24 hx hy with h | h | h
  · exfalso
    apply hne
    have h1 : x * y = 1 := orderOf_eq_one_iff.1 h
    have h2 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_cancel, inv_mul_cancel]
  · exfalso
    apply hne
    have h3 := pow_orderOf_eq_one (x * y)
    rw [h, sq] at h3
    have h4 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hx2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (D24_mul_self hx)
    have hy2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (D24_mul_self hy)
    rw [h4, mul_inv_rev, hx2, hy2]
  · have h3 := pow_orderOf_eq_one (x * y)
    rw [h, pow_three'] at h3
    exact h3

end Class

section Local

theorem oPrimeCoreTrivialAt_MR_five : OPrimeCoreTrivialAt 5 ↥MR :=
  CFSG.HardMathSupport.Solomon.Coordinator.oPrimeCoreTrivialAt_subgroup_of_mulEquiv
    (CFSG.Sporadic.Fi24.fi23EquivMR.trans CFSG.Sporadic.Fi23.fi23EquivJ)
    Fi23Five.oPrimeCoreTrivialAt_Fi23J_five

theorem fi24_local_tR {s : R} (hs : orderOf s = 5) (hst : s * tR = tR * s) (n : R)
    (hn : n ∈ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set R))) (hnt : n * tR = tR * n) :
    n = 1 ∨ n = tR := by
  set N := GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set R)) with hN
  have hodd : Odd (orderOf s) := by rw [hs]; decide
  have hsM : s ∈ MR := CFSG.Sporadic.FischerOddCore.mem_MR_of_odd hst hodd
  have htt : tR * tR = 1 := CFSG.Sporadic.Fi24.tR_mul_tR
  have hti : tR⁻¹ = tR := inv_eq_of_mul_eq_one_right htt
  have hcm : ∀ m ∈ MR, m * tR = tR * m := fun m hm => CFSG.Sporadic.Fi24.commute_tR_of_mem_MR hm
  have hNC : ∀ y ∈ N, y * s = s * y := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff (g := s)).1 (GLAPPrimeCoreOf_le _ hy)
  let K : Subgroup ↥MR :=
    { carrier := {m | (m : R) ∈ N ∨ (m : R) * tR ∈ N}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (N.mul_mem ha hb)
        · right
          rw [mul_assoc]
          exact N.mul_mem ha hb
        · right
          have e : (a : R) * b * tR = (a : R) * tR * b := by
            rw [mul_assoc, hcm _ b.2, ← mul_assoc]
          rw [e]
          exact N.mul_mem ha hb
        · left
          have e : (a : R) * b = (a : R) * tR * ((b : R) * tR) := by
            calc (a : R) * b = (a : R) * b * (tR * tR) := by rw [htt, mul_one]
              _ = (a : R) * (b * tR) * tR := by group
              _ = (a : R) * (tR * b) * tR := by rw [hcm _ b.2]
              _ = (a : R) * tR * ((b : R) * tR) := by group
          rw [e]
          exact N.mul_mem ha hb
      one_mem' := Or.inl N.one_mem
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at ha ⊢
        rcases ha with ha | ha
        · exact Or.inl (N.inv_mem ha)
        · right
          have e : (a : R)⁻¹ * tR = ((a : R) * tR)⁻¹ := by
            rw [mul_inv_rev, hti, hcm _ (MR.inv_mem a.2)]
          rw [e]
          exact N.inv_mem ha }
  set s₀ : ↥MR := ⟨s, hsM⟩ with hs₀
  have hs₀o : orderOf s₀ = 5 := by rw [← Subgroup.orderOf_coe]; exact hs
  have hKC : K ≤ Subgroup.centralizer ({s₀} : Set ↥MR) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rcases hm with hm | hm
    · exact hNC _ hm
    · have h1 := hNC _ hm
      have h2 : (m : R) * tR * s = (m : R) * s * tR := by rw [mul_assoc, ← hst, ← mul_assoc]
      have h3 : s * ((m : R) * tR) = s * m * tR := by group
      rw [h2, h3] at h1
      exact mul_right_cancel h1
  have hKn : ∀ y ∈ Subgroup.centralizer ({s₀} : Set ↥MR), ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    have hyR : (y : R) ∈ Subgroup.centralizer ({s} : Set R) := by
      have h1 := (Subgroup.mem_centralizer_singleton_iff).1 hy
      rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact (Subgroup.mem_centralizer_singleton_iff).2 h1
    rcases hk with hk | hk
    · left
      have := GLAPPrimeCoreOf_conj_mem (y : R) hyR _ hk
      simpa using this
    · right
      have := GLAPPrimeCoreOf_conj_mem (y : R) hyR _ hk
      have e : ((y * k * y⁻¹ : ↥MR) : R) * tR = (y : R) * ((k : R) * tR) * (y : R)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (y : R) * k * (y : R)⁻¹ * tR = (y : R) * k * ((y : R)⁻¹ * tR) := by group
          _ = (y : R) * k * (tR * (y : R)⁻¹) := by rw [hcm _ (MR.inv_mem y.2)]
          _ = (y : R) * ((k : R) * tR) * (y : R)⁻¹ := by group
      rw [e]
      exact this
  have hKcop : Nat.Coprime 5 (Nat.card K) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hko : orderOf ((k : ↥MR) : R) = 5 := by
      rw [Subgroup.orderOf_coe]
      first
        | exact hk
        | (rw [Subgroup.orderOf_coe]; exact hk)
    have hk2 : ((k : ↥MR) : R) ∈ N ∨ ((k : ↥MR) : R) * tR ∈ N := k.2
    have hkM : ((k : ↥MR) : R) ∈ MR := (k : ↥MR).2
    generalize ((k : ↥MR) : R) = m at hko hk2 hkM
    have hcop := coprime_card_GLAPPrimeCoreOf Nat.prime_five
      (Subgroup.centralizer ({s} : Set R))
    rcases hk2 with h | h
    · have hdvd := Subgroup.orderOf_dvd_natCard N h
      rw [hko] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hcop hdvd
    · have e : m * m = m * tR * (m * tR) := by
        calc m * m = m * m * (tR * tR) := by rw [htt, mul_one]
          _ = m * (m * tR) * tR := by group
          _ = m * (tR * m) * tR := by rw [hcm m hkM]
          _ = m * tR * (m * tR) := by group
      have hmem : m * m ∈ N := by rw [e]; exact N.mul_mem h h
      have hord : orderOf (m * m) = 5 := by
        rw [← sq, Nat.Coprime.orderOf_pow (by rw [hko]; norm_num), hko]
      have hdvd := Subgroup.orderOf_dvd_natCard N hmem
      rw [hord] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hcop hdvd
  have hKle := le_GLAPPrimeCoreOf_of_normal hKC hKn hKcop
  rw [oPrimeCoreTrivialAt_MR_five s₀ hs₀o] at hKle
  rcases CFSG.Sporadic.Fi24.mem_MR_or_of_commute
      ((Subgroup.mem_centralizer_singleton_iff (g := tR)).2 hnt) with h | h
  · left
    have hK : (⟨n, h⟩ : ↥MR) ∈ K := Or.inl hn
    have h1 := congrArg Subtype.val (Subgroup.mem_bot.1 (hKle hK))
    rw [Subgroup.coe_one] at h1
    exact h1
  · right
    have hK : (⟨n * tR, h⟩ : ↥MR) ∈ K := by
      right
      show n * tR * tR ∈ N
      rw [mul_assoc, htt, mul_one]
      exact hn
    have h1 := congrArg Subtype.val (Subgroup.mem_bot.1 (hKle hK))
    rw [Subgroup.coe_one] at h1
    change n * tR = 1 at h1
    calc n = n * tR * tR := by rw [mul_assoc, htt, mul_one]
      _ = tR := by rw [h1, one_mul]

theorem fi24_local {s : R} (hs : orderOf s = 5) {x : R} (hx : x ∈ D24) (hxs : x * s = s * x)
    (n : R) (hn : n ∈ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set R)))
    (hnx : n * x = x * n) : n = 1 ∨ n = x := by
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR hx
  have hs' : orderOf (jR g * s * (jR g)⁻¹) = 5 := by
    rw [CFSG.Sporadic.Fi24.orderOf_conj', hs]
  have hs't : jR g * s * (jR g)⁻¹ * tR = tR * (jR g * s * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * s * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (s * x) * (jR g)⁻¹ := by group
      _ = jR g * (x * s) * (jR g)⁻¹ := by rw [hxs]
      _ = jR g * x * (jR g)⁻¹ * (jR g * s * (jR g)⁻¹) := by group
  have hn' := @conj_mem_gLAPPrimeCoreOf_centralizer R (inferInstance : Group R) 5 (jR g) s n hn
  have hn't : jR g * n * (jR g)⁻¹ * tR = tR * (jR g * n * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * n * (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) = jR g * (n * x) * (jR g)⁻¹ := by group
      _ = jR g * (x * n) * (jR g)⁻¹ := by rw [hnx]
      _ = jR g * x * (jR g)⁻¹ * (jR g * n * (jR g)⁻¹) := by group
  rcases fi24_local_tR hs' hs't _ hn' hn't with h | h
  · left
    calc n = (jR g)⁻¹ * (jR g * n * (jR g)⁻¹) * jR g := by group
      _ = 1 := by rw [h]; group
  · right
    calc n = (jR g)⁻¹ * (jR g * n * (jR g)⁻¹) * jR g := by group
      _ = (jR g)⁻¹ * (jR g * x * (jR g)⁻¹) * jR g := by rw [h, hg]
      _ = x := by group

theorem gLAPPrimeCoreOf_fi24_five_eq_bot {s : R} (hs : orderOf s = 5)
    (hT0 : ∃ e ∈ D24, e * s = s * e)
    (hT1 : ∀ x ∈ D24, x * s = s * x → ∃ y ∈ D24, y * s = s * y ∧ y ≠ x ∧ x * y = y * x)
    (hT2 : ∀ x ∈ D24, x * s = s * x → ∀ y ∈ D24, y * s = s * y → x * y ≠ y * x →
      ∃ z ∈ D24, z * s = s * z ∧ z * x = x * z ∧ z * y = y * z) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set R)) = ⊥ :=
  @gLAPPrimeCoreOf_eq_bot_of_fixed_graph R (inferInstance : Group R) inferInstance D24 5
    (fun x hx => D24_mul_self hx) (fun x hx => D24_ne_one hx)
    (fun x hx y hy hxy => D24_cube hx hy hxy) (fun x hx g => D24_conj hx g) s hT0 hT1 hT2
    (fun x hx hxs n hn hnx => fi24_local hs hx hxs n hn hnx)

end Local

section Sylow

theorem exists_conj_sylow5 {G : Type*} [Group G] [Finite G] (H : Subgroup G) {e f : G}
    (he : e ∈ H) (hf : f ∈ H) (h5e : e ^ 5 = 1) (he1 : e ≠ 1) (h5f : f ^ 5 = 1)
    (hcomm : e * f = f * e) (hpow : ∀ k < 5, f ≠ e ^ k) {m : ℕ} (hH : Nat.card H = 5 ^ 2 * m)
    (h5 : ¬ 5 ∣ m) {s : H} (hs : orderOf s = 5) :
    ∃ g : H, ∃ a < 5, ∃ b < 5, a + b ≠ 0 ∧ ((g⁻¹ * s * g : H) : G) = e ^ a * f ^ b := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : Commute (⟨e, he⟩ : H) ⟨f, hf⟩ := Subtype.ext hcomm
  have h5e' : (⟨e, he⟩ : H) ^ 5 = 1 := Subtype.ext (by simpa using h5e)
  have h5f' : (⟨f, hf⟩ : H) ^ 5 = 1 := Subtype.ext (by simpa using h5f)
  have he1' : (⟨e, he⟩ : H) ≠ 1 := fun h => he1 (by simpa using congrArg Subtype.val h)
  have hpow' : ∀ k < 5, (⟨f, hf⟩ : H) ≠ ⟨e, he⟩ ^ k := fun k hk h =>
    hpow k hk (by simpa using congrArg Subtype.val h)
  have hQ := CommutingPair.card_closure_pair_eq_sq hc h5e' h5f' he1' hpow' (by
    rw [hH]
    intro h
    exact h5 ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5 ^ 2)).1 (by
      rw [show 5 ^ 3 = 5 ^ 2 * 5 by norm_num] at h; exact h)))
  have hQfull : Nat.card (Subgroup.closure ({⟨e, he⟩, ⟨f, hf⟩} : Set H)) =
      5 ^ (Nat.card (⊤ : Subgroup H)).factorization 5 := by
    rw [hQ, Subgroup.card_top, hH, CommutingPair.factorization_pow_mul Nat.prime_five 2 _ h5]
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨a, ha, b, hb, hw⟩ :=
    CommutingPair.exists_pow_mul_pow_of_mem (by norm_num) hc h5e' h5f' hgQ
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [CommutingPair.orderOf_inv_mul_mul, hs]
  refine ⟨g, a, ha, b, hb, fun h0 => ?_, by rw [hw]; simp⟩
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  rw [ha0, hb0, pow_zero, pow_zero, mul_one] at hw
  rw [hw, orderOf_one] at hwo
  exact absurd hwo (by norm_num)

end Sylow

section Main

theorem fi24Five_parts : ∃ e ∈ CFSG.Sporadic.Fi24.J, ∃ f ∈ CFSG.Sporadic.Fi24.J, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 → ∀ w : CFSG.Sporadic.Fi24.J,
      (w : GL (Fin 781) (ZMod 3)) = e ^ a * f ^ b →
      (∃ x ∈ D24, x * jR w = jR w * x) ∧
      (∀ x ∈ D24, x * jR w = jR w * x → ∃ y ∈ D24, y * jR w = jR w * y ∧ y ≠ x ∧ x * y = y * x) ∧
      (∀ x ∈ D24, x * jR w = jR w * x → ∀ y ∈ D24, y * jR w = jR w * y → x * y ≠ y * x →
        ∃ z ∈ D24, z * jR w = jR w * z ∧ z * x = x * z ∧ z * y = y * z) := by
  obtain ⟨e, he, f, hf, h5e, he1, h5f, hc, hp, hg⟩ := Certificates.certificate16947
  rw [CFSG.Sporadic.Fi24.mem_seedGrp_iff] at he hf
  refine ⟨e, he, f, hf, h5e, he1, h5f, hc, hp, fun a ha b hb hab w hw => ?_⟩
  apply CFSG.Sporadic.Fi24.graph_D24
  rw [hw]
  exact hg a ha b hb hab

theorem gLAPPrimeCoreOf_J_eq_bot_of_R {w : CFSG.Sporadic.Fi24.J}
    (h : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({jR w} : Set R)) = ⊥) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J)) = ⊥ := by
  have hmap := map_glaPPrimeCoreOf_of_injective 5 jR CFSG.Sporadic.Fi24.jR_injective
    (Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J))
  rw [map_centralizer_singleton_eq CFSG.Sporadic.Fi24.jR_injective w,
    CFSG.Sporadic.Fi24.range_jR] at hmap
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_le_of_ambient
    Nat.prime_five (le_top : JR ≤ ⊤)
    (fun r _ q hq => CFSG.Sporadic.Fi24.normal_JR.conj_mem q hq r) (jR w)
  rw [inf_top_eq, h, le_bot_iff, ← hmap] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ CFSG.Sporadic.Fi24.jR_injective).1 hle

theorem oPrimeCoreTrivialAt_Fi24J_five : OPrimeCoreTrivialAt 5 CFSG.Sporadic.Fi24.J := by
  obtain ⟨e, he, f, hf, h5e, he1, h5f, hcomm, hpow, hgraph⟩ := fi24Five_parts
  intro s hs
  obtain ⟨g, a, ha, b, hb, hab, hw⟩ := exists_conj_sylow5 CFSG.Sporadic.Fi24.J he hf h5e he1 h5f hcomm hpow
    (m := 50208228367626468851712) (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num) (by norm_num) hs
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [CommutingPair.orderOf_inv_mul_mul, hs]
  obtain ⟨hT0, hT1, hT2⟩ := hgraph a ha b hb hab _ hw
  have hwoR : orderOf (jR (g⁻¹ * s * g)) = 5 := by
    rw [orderOf_injective jR CFSG.Sporadic.Fi24.jR_injective, hwo]
  have hbot := gLAPPrimeCoreOf_J_eq_bot_of_R (gLAPPrimeCoreOf_fi24_five_eq_bot hwoR hT0 hT1 hT2)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' := @conj_mem_gLAPPrimeCoreOf_centralizer CFSG.Sporadic.Fi24.J (inferInstance : Group CFSG.Sporadic.Fi24.J) 5 g⁻¹ s x hx
  rw [inv_inv, hbot, Subgroup.mem_bot] at hx'
  exact CommutingPair.eq_one_of_inv_mul_mul_eq_one hx'

end Main

end Fi24Five

open Fi24Five

theorem sporadicOPrimeHolds_Fi24_five :
    SporadicOPrimeHolds .Fi24Prime 5 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Fi24prime := e
  exact @OPrimeCoreTrivialAt.of_mulEquiv 5 S _ ↥CFSG.Sporadic.Fi24.J inferInstance
    (e0.trans CFSG.Sporadic.Fi24.fi24EquivJ) oPrimeCoreTrivialAt_Fi24J_five

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
