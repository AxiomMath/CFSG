module

public import CFSG.CGT.PushingUpLit.SolK.Block
public import CFSG.CGT.PushingUpLit.SolK.Defs

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

section ThreeBlock

variable {L : Type} [Group L] [Finite L]

theorem exists_order_three (h3 : Nat.card (L ⧸ CFSG.pCore 2 L) = 3) :
    ∃ a : L, orderOf a = 3 ∧ ∀ x : L, ∃ y ∈ CFSG.pCore 2 L, ∃ j : ℕ, x = y * a ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hdvd : 3 ∣ Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 L), h3]
    exact dvd_mul_right _ _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨a, ha, fun x => ?_⟩
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have haY : a ∉ CFSG.pCore 2 L := by
    intro haY
    obtain ⟨k, hk⟩ := hY2 ⟨a, haY⟩
    have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : 3 ∣ 2 ^ k := ha ▸ orderOf_dvd_of_pow_eq_one hk'
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hā : (a : L ⧸ CFSG.pCore 2 L) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hz : Subgroup.zpowers (a : L ⧸ CFSG.pCore 2 L) = ⊤ := zpowers_eq_top_of_prime_card h3 hā
  have hx : (x : L ⧸ CFSG.pCore 2 L) ∈ Subgroup.zpowers (a : L ⧸ CFSG.pCore 2 L) := by
    rw [hz]
    exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hā3 : (a : L ⧸ CFSG.pCore 2 L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ha3]
    rfl
  have hmod : (a : L ⧸ CFSG.pCore 2 L) ^ i = (a : L ⧸ CFSG.pCore 2 L) ^ (i % 3).toNat := by
    have h0 : (0 : ℤ) ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have e : i = i % 3 + 3 * (i / 3) := (Int.emod_add_mul_ediv i 3).symm
    calc (a : L ⧸ CFSG.pCore 2 L) ^ i
        = (a : L ⧸ CFSG.pCore 2 L) ^ (i % 3 + 3 * (i / 3)) := by rw [← e]
      _ = (a : L ⧸ CFSG.pCore 2 L) ^ (i % 3) * ((a : L ⧸ CFSG.pCore 2 L) ^ (3 : ℤ)) ^ (i / 3) := by
          rw [zpow_add, zpow_mul]
      _ = (a : L ⧸ CFSG.pCore 2 L) ^ (i % 3).toNat := by
          have : ((a : L ⧸ CFSG.pCore 2 L) ^ (3 : ℤ)) = 1 := by
            rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
            exact hā3
          have h5 : (a : L ⧸ CFSG.pCore 2 L) ^ (i % 3) =
              (a : L ⧸ CFSG.pCore 2 L) ^ (((i % 3).toNat : ℕ) : ℤ) := by
            rw [Int.toNat_of_nonneg h0]
          rw [this, one_zpow, mul_one, h5, zpow_natCast]
  set j : ℕ := (i % 3).toNat with hj
  have hxj : (x : L ⧸ CFSG.pCore 2 L) = ((a ^ j : L) : L ⧸ CFSG.pCore 2 L) := by
    rw [QuotientGroup.mk_pow, ← hmod]
    exact hi.symm
  have hy₁ : x⁻¹ * a ^ j ∈ CFSG.pCore 2 L := QuotientGroup.eq.1 hxj
  refine ⟨a ^ j * (x⁻¹ * a ^ j)⁻¹ * (a ^ j)⁻¹, ?_, j, ?_⟩
  · exact Subgroup.Normal.conj_mem inferInstance _ ((CFSG.pCore 2 L).inv_mem hy₁) (a ^ j)
  · group


theorem pCore_le_shortU (hL : IsShortGroup L) {a : L} (ha : orderOf a = 3)
    (hdec : ∀ x : L, ∃ y ∈ CFSG.pCore 2 L, ∃ j : ℕ, x = y * a ^ j) :
    CFSG.pCore 2 L ≤ shortU L := by
  classical
  have hY2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hUn : (shortU L).Normal := by
    unfold shortU
    infer_instance
  have hUY : shortU L ≤ CFSG.pCore 2 L := shortU_le_pCore
  set N : Subgroup L := shortU L ⊔ Subgroup.zpowers a with hN
  have hmemN : ∀ n ∈ N, ∃ u ∈ shortU L, ∃ i : ℤ, n = u * a ^ i := by
    intro n hn
    obtain ⟨u, hu, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hn
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ⟨u, hu, i, rfl⟩
  have haN : a ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hconjY : ∀ y ∈ CFSG.pCore 2 L, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    obtain ⟨u, hu, i, rfl⟩ := hmemN n hn
    have hc : ⁅y, a ^ i⁆ ∈ shortU L :=
      Subgroup.commutator_mem_commutator hy (Subgroup.mem_top _)
    have h1 : y * u * y⁻¹ = u := by
      have := shortU_comm_pCore hL hu hy
      calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [this]
        _ = u := by group
    have e : y * (u * a ^ i) * y⁻¹ = (u * ⁅y, a ^ i⁆) * a ^ i := by
      calc y * (u * a ^ i) * y⁻¹ = (y * u * y⁻¹) * (y * a ^ i * y⁻¹) := by group
        _ = u * (⁅y, a ^ i⁆ * a ^ i) := by
            rw [h1]
            congr 1
            simp only [commutatorElement_def]
            group
        _ = (u * ⁅y, a ^ i⁆) * a ^ i := by group
    rw [e]
    exact N.mul_mem (Subgroup.mem_sup_left ((shortU L).mul_mem hu hc))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers a i))
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, hy, j, rfl⟩ := hdec g
    have h1 : (a ^ j) * n * (a ^ j)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.pow_mem haN j) hn) (N.inv_mem (N.pow_mem haN j))
    have h2 := hconjY y hy _ h1
    have e : (y * a ^ j) * n * (y * a ^ j)⁻¹ = y * ((a ^ j) * n * (a ^ j)⁻¹) * y⁻¹ := by group
    rw [e]
    exact h2
  have hq : IsPGroup 2 (L ⧸ N) := by
    intro g'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g'
    obtain ⟨y, hy, j, rfl⟩ := hdec x
    obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
    have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hxy : ((y * a ^ j : L) : L ⧸ N) = (y : L ⧸ N) := by
      rw [QuotientGroup.eq]
      have : (y * a ^ j)⁻¹ * y = (a ^ j)⁻¹ := by group
      rw [this]
      exact N.inv_mem (N.pow_mem haN j)
    rw [hxy, ← QuotientGroup.mk_pow, hk']
    rfl
  have hNtop : N = ⊤ := by
    have hle : oResidualTwo L ≤ N := sInf_le ⟨hNn, hq⟩
    rw [hL.residual_eq, top_le_iff] at hle
    exact hle
  intro y hy
  have hyN : y ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top y
  obtain ⟨u, hu, i, hyi⟩ := hmemN y hyN
  have hai : a ^ i ∈ CFSG.pCore 2 L := by
    have : a ^ i = u⁻¹ * y := by rw [hyi]; group
    rw [this]
    exact (CFSG.pCore 2 L).mul_mem ((CFSG.pCore 2 L).inv_mem (hUY hu)) hy
  have hai1 : a ^ i = 1 := by
    obtain ⟨k, hk⟩ := hY2 ⟨a ^ i, hai⟩
    have hk' : (a ^ i) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 : a ^ (i * ((2 ^ k : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, zpow_natCast]
      exact hk'
    have h2 : (orderOf a : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [ha] at h2
    have hcop : IsCoprime (3 : ℤ) ((2 ^ k : ℕ) : ℤ) := by
      have h23 : IsCoprime (3 : ℤ) 2 := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        rfl
      simpa using h23.pow_right (n := k)
    have h3 : (3 : ℤ) ∣ i := hcop.dvd_of_dvd_mul_right h2
    exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [ha]; exact_mod_cast h3)
  rw [hai1, mul_one] at hyi
  rw [hyi]
  exact hu


theorem fixed_eq_one_three (hL : IsShortGroup L) {a : L} (ha : orderOf a = 3)
    (hdec : ∀ x : L, ∃ y ∈ CFSG.pCore 2 L, ∃ j : ℕ, x = y * a ^ j)
    (hYU : CFSG.pCore 2 L ≤ shortU L)
    (hab : ∀ y ∈ CFSG.pCore 2 L, ∀ y' ∈ CFSG.pCore 2 L, y * y' = y' * y)
    (hsq : ∀ y ∈ CFSG.pCore 2 L, y * y = 1) :
    ∀ c ∈ CFSG.pCore 2 L, a * c * a⁻¹ = c → c = 1 := by
  classical
  have hY2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  let _ : CommGroup ↥(CFSG.pCore 2 L) := { (inferInstance : Group ↥(CFSG.pCore 2 L)) with
    mul_comm := fun x y => Subtype.ext (hab x x.2 y y.2) }
  let ρ : L →* MulAut ↥(CFSG.pCore 2 L) := MulAut.conjNormal
  have hρ : ∀ (x : L) (v : ↥(CFSG.pCore 2 L)), ((ρ x v : ↥(CFSG.pCore 2 L)) : L) = x * (v : L) * x⁻¹ :=
    fun x v => MulAut.conjNormal_apply x v
  have hρY : ∀ y ∈ CFSG.pCore 2 L, ρ y = 1 := by
    intro y hy
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [hρ]
    have := hab y hy v v.2
    show y * (v : L) * y⁻¹ = (v : L)
    rw [this]
    group
  have hσ3 : ∀ v, ρ a (ρ a (ρ a v)) = v := by
    intro v
    have h3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have := congrArg (fun f : MulAut ↥(CFSG.pCore 2 L) => f v) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  let nrm : ↥(CFSG.pCore 2 L) →* ↥(CFSG.pCore 2 L) :=
    MonoidHom.mk' (fun v => v * ρ a v * ρ a (ρ a v)) (fun v w => by
      simp only [map_mul]
      ac_rfl)
  have hnrmσ : ∀ v, nrm (ρ a v) = nrm v := by
    intro v
    show ρ a v * ρ a (ρ a v) * ρ a (ρ a (ρ a v)) = v * ρ a v * ρ a (ρ a v)
    rw [hσ3 v]
    ac_rfl
  have hpow : ∀ (j : ℕ) v, nrm ((ρ a ^ j) v) = nrm v := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
      intro v
      rw [pow_succ, MulAut.mul_apply, ih (ρ a v), hnrmσ]
  have hnrmx : ∀ (x : L) v, nrm (ρ x v) = nrm v := by
    intro x v
    obtain ⟨y, hy, j, rfl⟩ := hdec x
    rw [map_mul, hρY y hy, one_mul, map_pow]
    exact hpow j v
  intro c hc hac
  have hmem : ∀ y₀ ∈ CFSG.pCore 2 L, ∀ x : L, ⁅y₀, x⁆ ∈ CFSG.pCore 2 L := by
    intro y₀ hy₀ x
    have h1 : x * y₀⁻¹ * x⁻¹ ∈ CFSG.pCore 2 L :=
      Subgroup.Normal.conj_mem inferInstance _ ((CFSG.pCore 2 L).inv_mem hy₀) x
    have : ⁅y₀, x⁆ = y₀ * (x * y₀⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact (CFSG.pCore 2 L).mul_mem hy₀ h1
  have hkill : ∀ y₀ (hy₀ : y₀ ∈ CFSG.pCore 2 L), ∀ x : L, nrm ⟨⁅y₀, x⁆, hmem y₀ hy₀ x⟩ = 1 := by
    intro y₀ hy₀
    let cm : L → ↥(CFSG.pCore 2 L) := fun x => ⟨⁅y₀, x⁆, hmem y₀ hy₀ x⟩
    let κ : L → L := fun x => ((nrm (cm x) : ↥(CFSG.pCore 2 L)) : L)
    have hκ : ∀ x x', κ (x * x') = κ x * κ x' := by
      intro x x'
      have hcm : cm (x * x') = cm x * ρ x (cm x') := by
        refine Subtype.ext ?_
        show ⁅y₀, x * x'⁆ = ⁅y₀, x⁆ * ((ρ x (cm x') : ↥(CFSG.pCore 2 L)) : L)
        rw [hρ, commutator_mul_right]
      show ((nrm (cm (x * x')) : ↥(CFSG.pCore 2 L)) : L) =
        ((nrm (cm x) : ↥(CFSG.pCore 2 L)) : L) * ((nrm (cm x') : ↥(CFSG.pCore 2 L)) : L)
      rw [hcm, map_mul, hnrmx]
      rfl
    have h1 := forall_eq_one_of_mul (B := CFSG.pCore 2 L) hL.residual_eq hY2 κ
      (fun l => (nrm (cm l)).2) hκ
    intro x
    exact Subtype.ext (h1 x)
  have hK : shortU L ≤ (nrm.ker).map (CFSG.pCore 2 L).subtype := by
    unfold shortU
    rw [Subgroup.commutator_le]
    intro y₀ hy₀ x _
    exact ⟨⟨⁅y₀, x⁆, hmem y₀ hy₀ x⟩, MonoidHom.mem_ker.2 (hkill y₀ hy₀ x), rfl⟩
  obtain ⟨k, hk, hkc⟩ := hK (hYU hc)
  have hkc' : k = ⟨c, hc⟩ := Subtype.ext hkc
  rw [hkc'] at hk
  have hfix : ρ a ⟨c, hc⟩ = ⟨c, hc⟩ := by
    refine Subtype.ext ?_
    rw [hρ]
    exact hac
  have hcc : (⟨c, hc⟩ : ↥(CFSG.pCore 2 L)) * ⟨c, hc⟩ = 1 := Subtype.ext (hsq c hc)
  have hn : nrm ⟨c, hc⟩ = ⟨c, hc⟩ := by
    show (⟨c, hc⟩ : ↥(CFSG.pCore 2 L)) * ρ a ⟨c, hc⟩ * ρ a (ρ a ⟨c, hc⟩) = ⟨c, hc⟩
    rw [hfix, hfix, hcc, one_mul]
  have h1 : nrm ⟨c, hc⟩ = 1 := MonoidHom.mem_ker.1 hk
  rw [hn] at h1
  exact congrArg Subtype.val h1


theorem card_coreMod_three_eq : Nat.card (coreMod 3) = 4 := by
  show Nat.card {x : PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem three_block_structure (hL : IsShortGroup L) (hnat : IsNaturalAltModule L 1) :
    ∃ a : L, orderOf a = 3 ∧
      (∀ x : L, ∃ y ∈ CFSG.pCore 2 L, ∃ j : ℕ, x = y * a ^ j) ∧
      (∀ y ∈ CFSG.pCore 2 L, ∀ y' ∈ CFSG.pCore 2 L, y * y' = y' * y) ∧
      (∀ y ∈ CFSG.pCore 2 L, y * y = 1) ∧
      Nat.card ↥(CFSG.pCore 2 L) = 4 ∧
      (∀ y ∈ CFSG.pCore 2 L, a * y * a⁻¹ = y → y = 1) := by
  classical
  have hsq2 := shortU_sq_eq_one hL hnat
  obtain ⟨φ, ψ, hsum, hsurj, hker, hequiv⟩ := hnat
  have h3 : Nat.card (L ⧸ CFSG.pCore 2 L) = 3 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card]
    decide
  obtain ⟨a, ha, hdec⟩ := exists_order_three h3
  have hYU : CFSG.pCore 2 L ≤ shortU L := pCore_le_shortU hL ha hdec
  have hUY : shortU L ≤ CFSG.pCore 2 L := shortU_le_pCore
  have hab : ∀ y ∈ CFSG.pCore 2 L, ∀ y' ∈ CFSG.pCore 2 L, y * y' = y' * y :=
    fun y hy y' hy' => shortU_comm_pCore hL (hYU hy) hy'
  have hsq : ∀ y ∈ CFSG.pCore 2 L, y * y = 1 := fun y hy => by
    have := hsq2 y (hYU hy)
    rwa [pow_two] at this
  have hfix := fixed_eq_one_three hL ha hdec hYU hab hsq
  refine ⟨a, ha, hdec, hab, hsq, ?_, hfix⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : u ∈ ψ.ker := hu
    rw [hker, Subgroup.mem_subgroupOf] at h1
    have hz : (u : L) ∈ Subgroup.center L := h1.2
    have hcomm : a * (u : L) = (u : L) * a := Subgroup.mem_center_iff.1 hz a
    have hu1 : (u : L) = 1 := hfix u (hUY u.2) (by rw [hcomm]; group)
    exact Subtype.ext hu1
  let β0 : ↥(shortU L) → ↥(coreMod 3) := fun u => ⟨ψ u, mem_coreMod.2 (hsum u)⟩
  have hβ0 : Function.Bijective β0 := by
    refine ⟨fun u u' h => hinj (congrArg Subtype.val h), fun v => ?_⟩
    obtain ⟨u, hu⟩ := hsurj (fun i => Multiplicative.toAdd v.1 i) (mem_coreMod.1 v.2)
    exact ⟨u, Subtype.ext hu⟩
  have hcardU : Nat.card ↥(shortU L) = 4 := by
    rw [Nat.card_congr (Equiv.ofBijective β0 hβ0)]
    exact card_coreMod_three_eq
  have hYUeq : CFSG.pCore 2 L = shortU L := le_antisymm hYU hUY
  rw [hYUeq]
  exact hcardU


end ThreeBlock

section Ambient

variable {G : Type} [Group G] [Finite G] {X : Subgroup G}

theorem three_block_ambient (hX : IsShortGroup ↥X) (hnat : IsNaturalAltModule ↥X 1) :
    ∃ a ∈ X, a ^ 3 = 1 ∧
      (∀ x ∈ X, ∃ y ∈ pCoreOf 2 X, ∃ j : ℕ, x = y * a ^ j) ∧
      (∀ y ∈ pCoreOf 2 X, ∀ y' ∈ pCoreOf 2 X, y * y' = y' * y) ∧
      (∀ y ∈ pCoreOf 2 X, y * y = 1) ∧
      Nat.card ↥(pCoreOf 2 X) = 4 ∧
      (∀ y ∈ pCoreOf 2 X, a * y * a⁻¹ = y → y = 1) := by
  obtain ⟨a, ha, hdec, hab, hsq, hcard, hfix⟩ := three_block_structure hX hnat
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hmem : ∀ {y : G}, y ∈ pCoreOf 2 X ↔ ∃ y' ∈ CFSG.pCore 2 ↥X, (y' : G) = y := by
    intro y
    rw [pCoreOf_eq_map 2 X, Subgroup.mem_map]
    rfl
  refine ⟨(a : G), a.2, by rw [← Subgroup.coe_pow, ha3]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, j, hxy⟩ := hdec ⟨x, hx⟩
    refine ⟨(y : G), hmem.2 ⟨y, hy, rfl⟩, j, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · intro y hy y' hy'
    obtain ⟨z, hz, rfl⟩ := hmem.1 hy
    obtain ⟨z', hz', rfl⟩ := hmem.1 hy'
    have := congrArg Subtype.val (hab z hz z' hz')
    simpa using this
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hmem.1 hy
    have := congrArg Subtype.val (hsq z hz)
    simpa using this
  · rw [pCoreOf_eq_map 2 X, Subgroup.card_map_of_injective X.subtype_injective]
    exact hcard
  · intro y hy hay
    obtain ⟨z, hz, rfl⟩ := hmem.1 hy
    have h1 : a * z * a⁻¹ = z := Subtype.ext (by simpa using hay)
    have := hfix z hz h1
    rw [this]
    rfl

end Ambient


end CFSG.CGT.PushingUpLit.SolK
