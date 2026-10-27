module

public import CFSG.GH74.Uniqueness.Bender.Sylow2Special
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution

section Subnormal

variable {G : Type} [Group G]

theorem comm_map_mem {Q : Subgroup G} {x : G} (hQ : ∀ w ∈ Q, x * w * x⁻¹ ∈ Q) {w : G}
    (hw : w ∈ Q) : x * w * x⁻¹ * w⁻¹ ∈ Q :=
  Q.mul_mem (hQ w hw) (Q.inv_mem hw)

theorem iterate_comm_mem {Q : Subgroup G} {x : G} (hQ : ∀ w ∈ Q, x * w * x⁻¹ ∈ Q) (m : ℕ)
    {w : G} (hw : w ∈ Q) : (fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w ∈ Q := by
  induction m generalizing w with
  | zero => exact hw
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (comm_map_mem hQ hw)

theorem exists_iterate_comm_mem {K X Q : Subgroup G} (h : IsSubnormal K X)
    (hQ : ∀ g ∈ X, ∀ w ∈ Q, g * w * g⁻¹ ∈ Q) {x : G} (hx : x ∈ K) :
    ∃ m : ℕ, ∀ w ∈ Q, w ∈ X → (fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w ∈ K := by
  induction h with
  | refl => exact ⟨0, fun w _ hw => hw⟩
  | @step K' M X' hKM hN hMX ih =>
    obtain ⟨m, hm⟩ := ih hQ (hKM hx)
    have hxX : x ∈ X' := isSubnormal_le hMX (hKM hx)
    refine ⟨m + 1, fun w hwQ hwX => ?_⟩
    have hv : (fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w ∈ M := hm w hwQ hwX
    rw [Function.iterate_succ_apply']
    have hnorm := (Subgroup.normal_subgroupOf_iff hKM).mp hN
    have h1 := hnorm x⁻¹ _ (K'.inv_mem hx) hv
    have h2 : x * (fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w * x⁻¹ *
        ((fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w)⁻¹ =
        x * (((fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w) * x⁻¹ *
          ((fun y : G => x * y * x⁻¹ * y⁻¹)^[m] w)⁻¹) := by group
    rw [h2]
    exact K'.mul_mem hx h1

end Subnormal

section ClassTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_comm_map_eq_mod {Q Z : Subgroup G} {x : G} (hxQ : ∀ w ∈ Q, x * w * x⁻¹ ∈ Q)
    (hZc : ∀ c ∈ Z, ∀ w ∈ Q, c * w = w * c)
    (hcomm : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' * y⁻¹ * y'⁻¹ ∈ Z) (hxZ : ∀ c ∈ Z, x * c * x⁻¹ = c)
    (hfpf : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z → y ∈ Z) :
    ∀ y ∈ Q, ∃ w ∈ Q, (x * w * x⁻¹ * w⁻¹)⁻¹ * y ∈ Z := by
  classical
  have key : ∀ W W' : G, W ∈ Q → W' ∈ Q →
      (x * (W * W') * x⁻¹ * (W * W')⁻¹)⁻¹ * ((x * W * x⁻¹ * W⁻¹) * (x * W' * x⁻¹ * W'⁻¹)) ∈ Z := by
    intro W W' hW hW'
    have hbQ : x * W' * x⁻¹ ∈ Q := hxQ W' hW'
    have hz₁ : (x * W' * x⁻¹)⁻¹ * W⁻¹ * (x * W' * x⁻¹) * W ∈ Z := by
      have := hcomm _ (Q.inv_mem hbQ) W⁻¹ (Q.inv_mem hW)
      simpa using this
    have hz₂ : W * W' * W⁻¹ * W'⁻¹ ∈ Z := hcomm W hW W' hW'
    have hc := hZc _ hz₁ (W * W') (Q.mul_mem hW hW')
    have e : (x * (W * W') * x⁻¹ * (W * W')⁻¹)⁻¹ * ((x * W * x⁻¹ * W⁻¹) * (x * W' * x⁻¹ * W'⁻¹)) =
        ((x * W' * x⁻¹)⁻¹ * W⁻¹ * (x * W' * x⁻¹) * W) * (W * W' * W⁻¹ * W'⁻¹) := by
      calc (x * (W * W') * x⁻¹ * (W * W')⁻¹)⁻¹ * ((x * W * x⁻¹ * W⁻¹) * (x * W' * x⁻¹ * W'⁻¹))
          = (W * W') * ((x * W' * x⁻¹)⁻¹ * W⁻¹ * (x * W' * x⁻¹) * W) * (W⁻¹ * W'⁻¹) := by group
        _ = ((x * W' * x⁻¹)⁻¹ * W⁻¹ * (x * W' * x⁻¹) * W) * (W * W') * (W⁻¹ * W'⁻¹) := by
          rw [hc]
        _ = ((x * W' * x⁻¹)⁻¹ * W⁻¹ * (x * W' * x⁻¹) * W) * (W * W' * W⁻¹ * W'⁻¹) := by group
    rw [e]
    exact Z.mul_mem hz₁ hz₂
  set N : Subgroup Q := Z.subgroupOf Q with hN
  have hNmem : ∀ w : Q, w ∈ N ↔ (w : G) ∈ Z := fun w => Iff.rfl
  have : N.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hNmem] at hc ⊢
    have h := hZc _ hc g.1 g.2
    have h2 : ((g * c * g⁻¹ : Q) : G) = c := by
      change (g : G) * c * (g : G)⁻¹ = c
      calc (g : G) * c * (g : G)⁻¹ = (c * g) * (g : G)⁻¹ := by rw [← h]
        _ = c := by group
    rw [h2]
    exact hc
  let ψ' : Q → Q := fun w => ⟨x * w * x⁻¹ * w⁻¹, Q.mul_mem (hxQ w w.2) (Q.inv_mem w.2)⟩
  have hψmul : ∀ w w' : Q, (ψ' (w * w'))⁻¹ * (ψ' w * ψ' w') ∈ N := by
    intro w w'
    rw [hNmem]
    exact key w w' w.2 w'.2
  let φ : Q →* Q ⧸ N :=
    MonoidHom.mk' (fun w => (QuotientGroup.mk (ψ' w) : Q ⧸ N)) (fun w w' => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hψmul w w')
  have hker : N ≤ φ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    have hcZ : (c : G) ∈ Z := (hNmem c).mp hc
    have h1 : ψ' c = 1 := by
      apply Subtype.ext
      show x * (c : G) * x⁻¹ * (c : G)⁻¹ = 1
      rw [hxZ _ hcZ]
      group
    show (QuotientGroup.mk (ψ' c) : Q ⧸ N) = 1
    rw [h1]
    rfl
  let φbar : Q ⧸ N →* Q ⧸ N := QuotientGroup.lift N φ hker
  have hφbar : ∀ w : Q, φbar (QuotientGroup.mk w) = QuotientGroup.mk (ψ' w) := fun w => rfl
  have hinj : Function.Injective φbar := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hφbar, QuotientGroup.eq_one_iff, hNmem] at ha
    have hwZ := hfpf w w.2 ha
    rw [QuotientGroup.eq_one_iff, hNmem]
    exact hwZ
  have hsurj : Function.Surjective φbar := Finite.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨a, ha⟩ := hsurj (QuotientGroup.mk ⟨y, hy⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  rw [hφbar, QuotientGroup.eq, hNmem] at ha
  exact ⟨w, w.2, ha⟩

theorem comm_map_mul_central {Q Z : Subgroup G} {x : G} (hZc : ∀ c ∈ Z, ∀ w ∈ Q, c * w = w * c)
    (hxZ : ∀ c ∈ Z, x * c * x⁻¹ = c) {u c : G} (hu : u ∈ Q) (hc : c ∈ Z) :
    x * (u * c) * x⁻¹ * (u * c)⁻¹ = x * u * x⁻¹ * u⁻¹ := by
  have h1 := hxZ c hc
  have h2 := hZc c hc u hu
  calc x * (u * c) * x⁻¹ * (u * c)⁻¹ = x * u * (x⁻¹ * (x * c * x⁻¹)) * c⁻¹ * u⁻¹ := by group
    _ = x * u * (x⁻¹ * c) * c⁻¹ * u⁻¹ := by rw [h1]
    _ = x * u * x⁻¹ * u⁻¹ := by group

theorem exists_iterate_comm_map_eq_mod {Q Z : Subgroup G} {x : G}
    (hxQ : ∀ w ∈ Q, x * w * x⁻¹ ∈ Q) (hZc : ∀ c ∈ Z, ∀ w ∈ Q, c * w = w * c)
    (hcomm : ∀ y ∈ Q, ∀ y' ∈ Q, y * y' * y⁻¹ * y'⁻¹ ∈ Z) (hxZ : ∀ c ∈ Z, x * c * x⁻¹ = c)
    (hfpf : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z → y ∈ Z) (m : ℕ) :
    ∀ y ∈ Q, ∃ w ∈ Q, ((fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w)⁻¹ * y ∈ Z := by
  have hone := exists_comm_map_eq_mod hxQ hZc hcomm hxZ hfpf
  induction m with
  | zero =>
    intro y hy
    exact ⟨y, hy, by simp⟩
  | succ m ih =>
    intro y hy
    obtain ⟨w₁, hw₁, hw₁y⟩ := hone y hy
    obtain ⟨w, hw, hww₁⟩ := ih w₁ hw₁
    refine ⟨w, hw, ?_⟩
    rw [Function.iterate_succ_apply']
    set v := (fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w with hv
    have hvQ : v ∈ Q := iterate_comm_mem hxQ m hw
    have hc : w₁⁻¹ * v ∈ Z := by
      have := Z.inv_mem hww₁
      simpa [mul_assoc] using this
    have hvw : v = w₁ * (w₁⁻¹ * v) := by group
    have := comm_map_mul_central hZc hxZ hw₁ hc
    rw [← hvw] at this
    rw [this]
    exact hw₁y

end ClassTwo

section Bender

open CFSG.GH74.Uniqueness.Bender CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped Pointwise commutatorElement


theorem false_of_isBenderGroup_weakMember {G : Type} [Group G] [Finite G]
    (hB : CFSG.BenderSuzuki.IsBenderGroup G) {K : Subgroup G} {z : G}
    (hK : Q3.IsClassicalMember3 K z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, i, e, hT⟩ := isBenderGroup_iff_exists_benderType.mp hB
  have hz2 : orderOf z = 2 := hK.orderOf_eq_two
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_orderOf_two hz2)
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  have hQp : IsPGroup 2 (Q : Subgroup G) := Q.isPGroup'
  have hzQ' : z ∈ (Q : Subgroup G) := hzQ (Subgroup.mem_zpowers z)
  have hzr := hc.involution_iff.mp ⟨le_borel _ hzQ', hz2⟩
  have hXeq : Subgroup.centralizer ({z} : Set G) =
      (Q : Subgroup G) ⊔ fixCartan (Q : Subgroup G) t :=
    hc.centralizer_eq hzr.1 hzr.2
  have hKX : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hK.subnormal
  obtain ⟨e₀⟩ := hK.nonempty_equiv
  have hcardK : Nat.card K =
      24 * Nat.card (classicalInvolutionOddCore ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥K),
      Nat.card_congr e₀.toEquiv, natCard_sl2Three]
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥K
  have h3 : 3 ∣ Nat.card K := by rw [hcardK]; exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : orderOf (x₁ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx₁
  have hxK : (x₁ : G) ∈ K := x₁.2
  set x : G := (x₁ : G) with hxdef
  have hFnorm : fixCartan (Q : Subgroup G) t ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    (fixCartan_le_cartan _ _).trans (cartan_le_borel _ _)
  have hxX : x ∈ (Q : Subgroup G) ⊔ fixCartan (Q : Subgroup G) t := by
    rw [← hXeq]; exact hKX hxK
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (Q : Subgroup G)
    (fixCartan (Q : Subgroup G) t) hFnorm
  have hxmul : x ∈ ((Q : Subgroup G) : Set G) * (fixCartan (Q : Subgroup G) t : Set G) := by
    rw [← hset]; exact hxX
  obtain ⟨a, haQ, f, hfF, hxaf⟩ := Set.mem_mul.mp hxmul
  have hnot2 : ∀ y ∈ (Q : Subgroup G), orderOf y = 3 → False := by
    intro y hy hy3
    obtain ⟨k, hk⟩ := hQp ⟨y, hy⟩
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [hy3] at h1
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    omega
  have hf1 : f ≠ 1 := by
    rintro rfl
    apply hnot2 a haQ
    rw [mul_one] at hxaf
    rw [hxaf]; exact hx3
  rcases hT.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -⟩ | ⟨hi, he, hn2⟩
  · exact hf1 (by
      have h1 : Nat.card (fixCartan (Q : Subgroup G) t) = 1 := by rw [hc.card_fixCartan, he]
      have h2 := Subgroup.eq_bot_of_card_eq _ h1
      rw [h2] at hfF
      exact Subgroup.mem_bot.mp hfF)
  · exact hf1 (by
      have h1 : Nat.card (fixCartan (Q : Subgroup G) t) = 1 := by rw [hc.card_fixCartan, he]
      have h2 := Subgroup.eq_bot_of_card_eq _ h1
      rw [h2] at hfF
      exact Subgroup.mem_bot.mp hfF)
  subst hi
  obtain ⟨hQ'Z, -⟩ := hT.lemma_3_5_a_unitary Q
  have hXle : (Q : Subgroup G) ⊔ fixCartan (Q : Subgroup G) t ≤ borel (Q : Subgroup G) :=
    sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _))
  have hQnormX : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ w ∈ (Q : Subgroup G),
      g * w * g⁻¹ ∈ (Q : Subgroup G) := by
    intro g hg w hw
    rw [hXeq] at hg
    exact ((Subgroup.mem_normalizer_iff.mp (hXle hg)) w).mp hw
  have hxQ : ∀ w ∈ (Q : Subgroup G), x * w * x⁻¹ ∈ (Q : Subgroup G) :=
    hQnormX x (hKX hxK)
  have hZc : ∀ c ∈ rootCenter (Q : Subgroup G), ∀ w ∈ (Q : Subgroup G), c * w = w * c :=
    fun c hc' w hw => ((mem_rootCenter_iff.mp hc').2 w hw).symm
  have hcommQ : ∀ y ∈ (Q : Subgroup G), ∀ y' ∈ (Q : Subgroup G),
      y * y' * y⁻¹ * y'⁻¹ ∈ rootCenter (Q : Subgroup G) := by
    intro y hy y' hy'
    have := Subgroup.commutator_mem_commutator hy hy'
    rw [hQ'Z, commutatorElement_def] at this
    exact this
  have hxZ : ∀ c ∈ rootCenter (Q : Subgroup G), x * c * x⁻¹ = c := by
    intro c hcZ
    rcases eq_or_ne c 1 with rfl | hc1
    · simp
    · have hcen : f ∈ Subgroup.centralizer ({c} : Set G) := by
        rw [hc.centralizer_eq hcZ hc1]
        exact Subgroup.mem_sup_right hfF
      have hfc : f * c = c * f := Subgroup.mem_centralizer_singleton_iff.mp hcen
      have hac : c * a = a * c := hZc c hcZ a haQ
      rw [← hxaf]
      calc a * f * c * (a * f)⁻¹ = a * (f * c) * f⁻¹ * a⁻¹ := by group
        _ = a * (c * f) * f⁻¹ * a⁻¹ := by rw [hfc]
        _ = a * c * a⁻¹ := by group
        _ = c := by rw [← hac]; group
  have hfpf : ∀ y ∈ (Q : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ rootCenter (Q : Subgroup G) →
      y ∈ rootCenter (Q : Subgroup G) := by
    intro y hy hψ
    have hy' : f * y * f⁻¹ ∈ (Q : Subgroup G) :=
      ((Subgroup.mem_normalizer_iff.mp (hFnorm hfF)) y).mp hy
    have hc₁ := hcommQ a haQ _ hy'
    have e1 : x * y * x⁻¹ * y⁻¹ =
        (a * (f * y * f⁻¹) * a⁻¹ * (f * y * f⁻¹)⁻¹) * ((f * y * f⁻¹) * y⁻¹) := by
      rw [← hxaf]; group
    have hdx : f * y * f⁻¹ * y⁻¹ ∈ rootCenter (Q : Subgroup G) := by
      have h2 : (f * y * f⁻¹) * y⁻¹ = (a * (f * y * f⁻¹) * a⁻¹ * (f * y * f⁻¹)⁻¹)⁻¹ *
          (x * y * x⁻¹ * y⁻¹) := by rw [e1]; group
      rw [h2]
      exact (rootCenter (Q : Subgroup G)).mul_mem ((rootCenter (Q : Subgroup G)).inv_mem hc₁) hψ
    exact hT.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem
      (fixCartan_le_cartan _ _ hfF) hf1 hy hdx
  obtain ⟨m, hm⟩ := exists_iterate_comm_mem hK.subnormal hQnormX hxK
  have hQX : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hXeq]; exact le_sup_left
  have hQle : (Q : Subgroup G) ≤ (K ⊓ (Q : Subgroup G)) ⊔ rootCenter (Q : Subgroup G) := by
    intro y hy
    obtain ⟨w, hwQ, hw⟩ := exists_iterate_comm_map_eq_mod hxQ hZc hcommQ hxZ hfpf m y hy
    have hwK := hm w hwQ (hQX hwQ)
    have hwQ' := iterate_comm_mem hxQ m hwQ
    have hmem : (fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w ∈ K ⊓ (Q : Subgroup G) := ⟨hwK, hwQ'⟩
    have hy' : y = ((fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w) *
        (((fun v : G => x * v * x⁻¹ * v⁻¹)^[m] w)⁻¹ * y) := by group
    rw [hy']
    exact Subgroup.mul_mem_sup hmem hw
  have hT0p : IsPGroup 2 ↥(K ⊓ (Q : Subgroup G)) := hQp.to_le inf_le_right
  obtain ⟨k, hk⟩ := hT0p.exists_card_eq
  have hT0K : Nat.card ↥(K ⊓ (Q : Subgroup G)) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  have hT08 : Nat.card ↥(K ⊓ (Q : Subgroup G)) ≤ 8 := by
    by_contra hgt
    push Not at hgt
    have hk4 : 4 ≤ k := by
      by_contra hk3
      push Not at hk3
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h16 : 16 ∣ Nat.card K := by
      refine dvd_trans ?_ (hk ▸ hT0K)
      calc 16 = 2 ^ 4 := by norm_num
        _ ∣ 2 ^ k := pow_dvd_pow 2 hk4
    rw [hcardK] at h16
    obtain ⟨r, hr⟩ := hOodd
    rw [hr] at h16
    omega
  have hZnorm : (K ⊓ (Q : Subgroup G)) ≤
      Subgroup.normalizer ((rootCenter (Q : Subgroup G) : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc'
      have h1 : w * c = c * w := (hZc c hc' w hw.2).symm
      have h2 : w * c * w⁻¹ = c := by rw [h1]; group
      rw [h2]; exact hc'
    · intro hc'
      have h : (w * c * w⁻¹) * w⁻¹ = w⁻¹ * (w * c * w⁻¹) :=
        hZc _ hc' w⁻¹ ((Q : Subgroup G).inv_mem hw.2)
      have h2 : c = w * c * w⁻¹ := by
        calc c = w⁻¹ * (w * c * w⁻¹) * w := by group
          _ = ((w * c * w⁻¹) * w⁻¹) * w := by rw [← h]
          _ = w * c * w⁻¹ := by group
      rw [h2]; exact hc'
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hZnorm
  have hcardQ := Subgroup.card_le_of_le hQle
  have hzT : z ∈ (K ⊓ (Q : Subgroup G)) ⊓ rootCenter (Q : Subgroup G) :=
    ⟨⟨hK.mem, hzQ'⟩, hzr.1⟩
  have hinf2 : 2 ≤ Nat.card ↥((K ⊓ (Q : Subgroup G)) ⊓ rootCenter (Q : Subgroup G)) := by
    have hd := Subgroup.orderOf_dvd_natCard _ hzT
    rw [hz2] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hQcard := hc.card_eq
  have hZcard := hc.card_center
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
  rw [← hq] at hq4 hQcard hZcard
  have hS : q ^ 3 ≤ Nat.card ↥((K ⊓ (Q : Subgroup G)) ⊔ rootCenter (Q : Subgroup G)) := by
    rw [← hQcard]; exact hcardQ
  have h1 := Nat.mul_le_mul hS hinf2
  rw [hprod, hZcard] at h1
  have h2 : Nat.card ↥(K ⊓ (Q : Subgroup G)) * q ≤ 8 * q := Nat.mul_le_mul_right q hT08
  have h3 : 16 ≤ q ^ 2 := by nlinarith
  have h4 : q * 16 ≤ q ^ 3 := by
    calc q * 16 ≤ q * q ^ 2 := Nat.mul_le_mul_left q h3
      _ = q ^ 3 := by ring
  nlinarith

end Bender

end CFSG.ClassicalInvolution.Q3.Q3T8
