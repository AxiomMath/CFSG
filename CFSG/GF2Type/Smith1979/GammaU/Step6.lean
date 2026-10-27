module

public import CFSG.GF2Type.Smith1979.GammaU.ThetaFree
public import CFSG.GF2Type.Smith1979.GammaU.FrameFix
public import Certificates.Certificate16974
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module Subgroup MulAction

theorem card_cases_of_orbits {P X : Type*} [Group P] [MulAction P X] :
    ∀ (n : ℕ) (Y : Finset X), Y.card = n → (∀ p : P, ∀ y ∈ Y, p • y ∈ Y) →
      (∀ y ∈ Y, (orbit P y).ncard = 18 ∨ (orbit P y).ncard = 36 ∨ (orbit P y).ncard = 45) →
      n ≤ 45 → n = 0 ∨ n = 18 ∨ n = 36 ∨ n = 45 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hYn hinv horb h45
    rcases Y.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · left
      rw [← hYn, Finset.card_empty]
    · have hOY : orbit P y ⊆ Y := by
        rintro _ ⟨p, rfl⟩
        exact hinv p y hy
      have h1 : ((Y.filter (· ∈ orbit P y) : Finset X) : Set X) = orbit P y := by
        ext z
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨hOY h, h⟩⟩
      have hcard1 : (Y.filter (· ∈ orbit P y)).card = (orbit P y).ncard := by
        rw [← Set.ncard_coe_finset, h1]
      have hsum : (Y.filter (· ∈ orbit P y)).card + (Y.filter (· ∉ orbit P y)).card = Y.card :=
        Finset.card_filter_add_card_filter_not _
      have hinv2 : ∀ p : P, ∀ z ∈ Y.filter (· ∉ orbit P y), p • z ∈ Y.filter (· ∉ orbit P y) := by
        intro p z hz
        rw [Finset.mem_filter] at hz ⊢
        refine ⟨hinv p z hz.1, fun h => hz.2 ?_⟩
        obtain ⟨q, hq⟩ := h
        refine ⟨p⁻¹ * q, ?_⟩
        simp only at hq ⊢
        rw [mul_smul, hq, inv_smul_smul]
      have horb2 : ∀ z ∈ Y.filter (· ∉ orbit P y), (orbit P z).ncard = 18 ∨
          (orbit P z).ncard = 36 ∨ (orbit P z).ncard = 45 :=
        fun z hz => horb z (Finset.mem_filter.1 hz).1
      have hO := horb y hy
      have hlt : (Y.filter (· ∉ orbit P y)).card < n := by omega
      have := ih _ hlt _ rfl hinv2 horb2 (by omega)
      omega

theorem theta0_fix {v : V12} (h : theta0 v = v) : v = 0 := by
  refine ext_lo_hi (fun j => ?_) (fun j => ?_)
  · have h1 := congrFun h (lo j)
    have h2 := congrFun h (hi j)
    rw [theta0_lo] at h1
    rw [theta0_hi, h1] at h2
    simpa using h2
  · have h1 := congrFun h (lo j)
    rw [theta0_lo] at h1
    have h2 := congrFun h (hi j)
    rw [theta0_hi, h1] at h2
    have hz : ∀ a : ZMod 2, a + a = a → a = 0 := by decide
    rw [h1, hz _ h2]
    rfl

theorem vecOf_a0_ne_zero : vecOf a0 ≠ 0 := fun h =>
  absurd ((vecOf_eq_zero a0_lt).1 h) (by norm_num [a0])

theorem not_anti_of_pow_three {τ : V12 ≃ₗ[ZMod 2] V12} (h3 : τ ^ 3 = 1)
    (ha : ∀ x, τ (theta0 x) = theta0 (theta0 (τ x))) : False := by
  have h3v : ∀ v, τ (τ (τ v)) = v := fun v => by
    have := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => f v) h3
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] at this
    exact this
  have hb : ∀ x, τ (theta0 (theta0 x)) = theta0 (τ x) := fun x => by
    rw [ha, ha, theta0_theta0_theta0]
  have key : ∀ x, theta0 x = theta0 (theta0 x) := fun x => by
    have := h3v (theta0 x)
    rw [ha x, hb (τ x), ha (τ (τ x)), h3v x] at this
    exact this.symm
  have h0 := key (vecOf a0)
  rw [theta0_theta0_eq] at h0
  have : vecOf a0 = 0 := by
    have h' : vecOf a0 + theta0 (vecOf a0) - theta0 (vecOf a0) = vecOf a0 := by abel
    rw [← h0, sub_self] at h'
    exact h'.symm
  exact vecOf_a0_ne_zero this

structure Step6Hyp (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop where
  isom : ∀ m ∈ M, ∀ v, q0 (m v) = q0 v
  theta : thetaU ∈ M
  n2_le : ResPair.n2 i ≤ M
  step5 : ∀ k ∈ M, k ∈ gammaU → (ResPair.n2 i).map (MulAut.conj k).toMonoidHom = ResPair.n2 i ∧
    ∃ y ∈ SigmaP.s45 i, k (vecOf a0) = vecOf y
  canon : ∀ m ∈ M, m (vecOf a0) = vecOf a0 → m ∈ gammaU
  irred : ∀ W : Submodule (ZMod 2) V12, (∀ m ∈ M, ∀ w ∈ W, m w ∈ W) → W = ⊥ ∨ W = ⊤

section

variable {i : ℕ} (hi : i = 0 ∨ i = 1)
  {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Step6Hyp i M)
include hi H

theorem p2_le_n2 : SigmaP.p2 i ≤ ResPair.n2 i := by
  rw [← SigmaP.commutator_n2 hi]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem p2_le_gammaU : SigmaP.p2 i ≤ gammaU := (p2_le_n2 hi H).trans (n2_le_gammaU hi)

theorem mem_gammaU_of_conj {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ M)
    (hτ : g⁻¹ * thetaU * g ∈ gammaU) : g ∈ gammaU := by
  set τ := g⁻¹ * thetaU * g with hτdef
  have hτM : τ ∈ M := mul_mem (mul_mem (inv_mem hg) H.theta) hg
  have h3 : τ ^ 3 = 1 := by
    have hc := conj_pow (a := g⁻¹) (b := thetaU) (i := 3)
    rw [inv_inv] at hc
    rw [hτdef, hc, SigmaP.thetaU_pow_three, mul_one, inv_mul_cancel]
  have hθ : ∀ x, τ (theta0 x) = theta0 (τ x) := by
    rcases hτ.2 with h | h
    · exact h
    · exact (not_anti_of_pow_three h3 h).elim
  have hfix : ∀ v, τ v = v → v = 0 := fun v hv => by
    have h1 : thetaU (g v) = g v := by
      have := congrArg g hv
      simpa [hτdef, LinearEquiv.mul_apply] using this
    have h2 : g v = 0 := theta0_fix h1
    exact g.injective (h2.trans (map_zero g).symm)
  obtain ⟨hN, ha⟩ := H.step5 τ hτM hτ
  rcases SigmaP.fpf_three_of_normalizes hi (H.isom τ hτM) hθ hN ha h3 hfix with h | h
  ·
    have hc : thetaU * g = g * thetaU := by
      rw [hτdef] at h
      calc thetaU * g = g * (g⁻¹ * thetaU * g) := by group
        _ = g * thetaU := by rw [h]
    refine ⟨H.isom g hg, Or.inl fun x => ?_⟩
    have := LinearEquiv.congr_fun hc x
    simp only [LinearEquiv.mul_apply, thetaU_apply] at this
    exact this.symm
  ·
    have hc : thetaU * g = g * thetaU⁻¹ := by
      rw [hτdef] at h
      calc thetaU * g = g * (g⁻¹ * thetaU * g) := by group
        _ = g * thetaU⁻¹ := by rw [h]
    refine ⟨H.isom g hg, Or.inr fun x => ?_⟩
    have := LinearEquiv.congr_fun hc (theta0 x)
    simp only [LinearEquiv.mul_apply, thetaU_apply] at this
    rw [show thetaU⁻¹ (theta0 x) = x by
      rw [thetaU_inv_apply, theta0_theta0_theta0]] at this
    rw [← this, theta0_theta0_theta0]

theorem s45_nodup : (SigmaP.s45 i).Nodup := by
  rcases hi with rfl | rfl <;> decide

theorem s45_length : (SigmaP.s45 i).length = 45 := by
  rcases hi with rfl | rfl <;> decide

theorem ncard_s45 : ({v | ∃ y ∈ SigmaP.s45 i, vecOf y = v} : Set V12).ncard = 45 := by
  classical
  have hset : ({v | ∃ y ∈ SigmaP.s45 i, vecOf y = v} : Set V12) =
      vecOf '' ((SigmaP.s45 i).toFinset : Set ℕ) := by
    ext v
    simp
  have hinj : Set.InjOn vecOf ((SigmaP.s45 i).toFinset : Set ℕ) := by
    intro a ha b hb hab
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at ha hb
    exact vecOf_inj (SigmaP.orbit_lt hi a ha) (SigmaP.orbit_lt hi b hb) hab
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (s45_nodup hi H), s45_length hi H]

theorem orbit_K :
    (orbit ↥((gammaU.subgroupOf M)) (vecOf a0) : Set V12) =
      {v | ∃ y ∈ SigmaP.s45 i, vecOf y = v} := by
  ext v
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨-, y, hy, hky⟩ := H.step5 _ k.1.2 (mem_subgroupOf.1 k.2)
    exact ⟨y, hy, hky.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨U, hU, hUy⟩ := SigmaP.orbit_reach hi y hy
    exact ⟨⟨⟨U, H.n2_le hU⟩, mem_subgroupOf.2 (n2_le_gammaU hi hU)⟩, hUy⟩

end

theorem ncard_sing :
    ({v : V12 | v ≠ 0 ∧ q0 v = 0} : Set V12).ncard = 2079 := by
  classical
  have h := Certificates.certificate16974
  simp only [singCount, beq_iff_eq] at h
  have hnd : (singCodes ()).Nodup := List.nodup_range.filter _
  have hmem : ∀ n, n ∈ singCodes () ↔ n < 4096 ∧ n ≠ 0 ∧ q0b n = false := fun n => by
    simp only [singCodes, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_true']
  have hset : ({v : V12 | v ≠ 0 ∧ q0 v = 0} : Set V12) =
      vecOf '' ((singCodes ()).toFinset : Set ℕ) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image, List.coe_toFinset, hmem]
    constructor
    · rintro ⟨hv0, hq⟩
      refine ⟨codeOf v, ⟨codeOf_lt v, fun h0 => hv0 ?_, ?_⟩, vecOf_codeOf v⟩
      · rw [← vecOf_codeOf v, h0, vecOf_zero]
      · have h' := q0_vecOf (codeOf v)
        rw [vecOf_codeOf, hq] at h'
        cases hb : q0b (codeOf v)
        · rfl
        · rw [hb] at h'
          exact absurd h' (by decide)
    · rintro ⟨n, ⟨hn, hn0, hq⟩, rfl⟩
      refine ⟨fun h0 => hn0 ((vecOf_eq_zero hn).1 h0), ?_⟩
      rw [q0_vecOf, hq]
      rfl
  have hinj : Set.InjOn vecOf ((singCodes ()).toFinset : Set ℕ) := by
    intro a ha b hb hab
    simp only [List.coe_toFinset, Set.mem_setOf_eq, hmem] at ha hb
    exact vecOf_inj ha.1 hb.1 hab
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, h]

theorem no_elem_order (p : ℕ) [Fact p.Prime] (hp : ∀ w < 12, ¬ 4096 ≡ 2 ^ w [MOD p])
    {g : V12 ≃ₗ[ZMod 2] V12} (hg : orderOf g = p) : False := by
  classical
  set Z := zpowers g with hZ
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (by rw [hZ, Nat.card_zpowers, hg, pow_one])
  have hmod := hZp.card_modEq_card_fixedPoints V12
  set W : Submodule (ZMod 2) V12 := LinearMap.ker ((g : V12 →ₗ[ZMod 2] V12) - LinearMap.id)
    with hW
  have hmemW : ∀ v, v ∈ W ↔ g v = v := fun v => by
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hfix : fixedPoints Z V12 = (W : Set V12) := by
    ext v
    rw [mem_fixedPoints, SetLike.mem_coe, hmemW]
    constructor
    · intro h
      exact h ⟨g, mem_zpowers g⟩
    · intro h z
      have hz : (z : V12 ≃ₗ[ZMod 2] V12) ∈ stabilizer (V12 ≃ₗ[ZMod 2] V12) v :=
        (zpowers_le.2 (show g ∈ stabilizer (V12 ≃ₗ[ZMod 2] V12) v from h)) z.2
      exact hz
  have hcardV : Nat.card V12 = 4096 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hcardW : Nat.card (fixedPoints Z V12) = 2 ^ finrank (ZMod 2) W := by
    rw [hfix, SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
      Nat.card_zmod]
  have hle : finrank (ZMod 2) W ≤ 12 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at this
  rcases hle.lt_or_eq with hlt | heq
  · rw [hcardV, hcardW] at hmod
    exact hp _ hlt hmod
  · have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [heq, Module.finrank_fin_fun])
    have hg1 : g = 1 := LinearEquiv.ext fun v => by
      have : v ∈ W := by rw [htop]; trivial
      exact (hmemW v).1 this
    rw [hg1, orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg

section

variable {i : ℕ} (hi : i = 0 ∨ i = 1)
  {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Step6Hyp i M)
include hi H

theorem card_orbit_a0 :
    (orbit ↥M (vecOf a0) : Set V12).ncard = 45 * (gammaU.subgroupOf M).index := by
  set K := gammaU.subgroupOf M with hK
  have hCK : stabilizer ↥M (vecOf a0) ≤ K := fun m hm =>
    mem_subgroupOf.2 (H.canon _ m.2 hm)
  have hrel : (stabilizer ↥M (vecOf a0)).relIndex K = 45 := by
    have heq : (stabilizer ↥M (vecOf a0)).subgroupOf K = stabilizer ↥K (vecOf a0) := by
      ext k
      rw [mem_subgroupOf, mem_stabilizer_iff, mem_stabilizer_iff]
      rfl
    rw [Subgroup.relIndex, heq, index_stabilizer, orbit_K hi H, ncard_s45 hi H]
  rw [← index_stabilizer, ← Subgroup.relIndex_mul_index hCK, hrel]

theorem index_le : (gammaU.subgroupOf M).index ≤ 46 := by
  have hsub : (orbit ↥M (vecOf a0) : Set V12) ⊆ {v | v ≠ 0 ∧ q0 v = 0} := by
    rintro _ ⟨m, rfl⟩
    refine ⟨fun h0 => vecOf_a0_ne_zero ?_, ?_⟩
    · have : (m : V12 ≃ₗ[ZMod 2] V12) (vecOf a0) = 0 := h0
      exact (m : V12 ≃ₗ[ZMod 2] V12).injective (this.trans (map_zero _).symm)
    · change q0 ((m : V12 ≃ₗ[ZMod 2] V12) (vecOf a0)) = 0
      rw [H.isom _ m.2, q0_vecOf]
      rfl
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [card_orbit_a0 hi H, ncard_sing] at h
  omega

theorem index_cases : (gammaU.subgroupOf M).index = 1 ∨ (gammaU.subgroupOf M).index = 19 ∨
    (gammaU.subgroupOf M).index = 37 ∨ (gammaU.subgroupOf M).index = 46 := by
  classical
  set K := gammaU.subgroupOf M with hK
  let X := ↥M ⧸ K
  haveI : Fintype X := Fintype.ofFinite X
  have hPM : SigmaP.p2 i ≤ M := (p2_le_n2 hi H).trans H.n2_le
  let ι : ↥(SigmaP.p2 i) →* ↥M := Subgroup.inclusion hPM
  letI : MulAction ↥(SigmaP.p2 i) X := MulAction.compHom X ι
  have hsmul : ∀ (p : ↥(SigmaP.p2 i)) (g : ↥M), p • (g : X) = ((ι p * g : ↥M) : X) := fun _ _ => rfl
  set x₀ : X := ((1 : ↥M) : X)
  have hfix0 : ∀ p : ↥(SigmaP.p2 i), p • x₀ = x₀ := fun p => by
    rw [hsmul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff, mem_subgroupOf]
    exact p2_le_gammaU hi H p.2
  set θ' : ↥(SigmaP.p2 i) := ⟨thetaU, SigmaP.thetaU_mem_p2 hi⟩
  have hθfix : ∀ x : X, θ' • x = x → x = x₀ := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hsmul, QuotientGroup.eq, mem_subgroupOf] at hx
    have hx' : (g : V12 ≃ₗ[ZMod 2] V12)⁻¹ * thetaU * g ∈ gammaU := by
      have h1 := inv_mem hx
      have h2 : (((ι θ' * g)⁻¹ * g)⁻¹ : ↥M) = g⁻¹ * ι θ' * g := by group
      rw [← Subgroup.coe_inv, h2] at h1
      exact h1
    have hg := mem_gammaU_of_conj hi H g.2 hx'
    rw [QuotientGroup.eq, mul_one, inv_mem_iff, mem_subgroupOf]
    exact hg
  set Y : Finset X := Finset.univ.filter (· ≠ x₀) with hY
  have hYcard : Y.card + 1 = K.index := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X)) (· ≠ x₀)
    have h2 : (Finset.univ.filter fun x : X => ¬ x ≠ x₀).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨x₀, by ext x; simp⟩
    rw [h2, Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
    exact h1
  have hYinv : ∀ p : ↥(SigmaP.p2 i), ∀ y ∈ Y, p • y ∈ Y := by
    intro p y hy
    rw [hY, Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, fun h => hy.2 ?_⟩
    rw [← inv_smul_smul p y, h, hfix0]
  have hY45 : Y.card ≤ 45 := by
    have := index_le hi H
    rw [← hK] at this
    omega
  have horb : ∀ y ∈ Y, (orbit ↥(SigmaP.p2 i) y).ncard = 18 ∨
      (orbit ↥(SigmaP.p2 i) y).ncard = 36 ∨ (orbit ↥(SigmaP.p2 i) y).ncard = 45 := by
    intro y hy
    rw [← index_stabilizer]
    refine SigmaP.theta_free_index_le hi _ (fun x hx hxθ => ?_) ?_
    · have hx' : x = θ' := Subtype.ext hxθ
      rw [hx', mem_stabilizer_iff] at hx
      exact (Finset.mem_filter.1 hy).2 (hθfix y hx)
    · rw [index_stabilizer]
      have hsub : orbit ↥(SigmaP.p2 i) y ⊆ (Y : Set X) := by
        rintro _ ⟨p, rfl⟩
        exact hYinv p y hy
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at this
      omega
  rcases card_cases_of_orbits Y.card Y rfl hYinv horb hY45 with h | h | h | h <;> omega

theorem le_gammaU : M ≤ gammaU := by
  classical
  set K := gammaU.subgroupOf M with hK
  have hdvd : K.index ∣ Nat.card ↥M := K.index_dvd_card
  have hprime : ∀ p, K.index = p → p = 19 ∨ p = 37 → False := by
    intro p hp hp'
    have hpr : p.Prime := by rcases hp' with rfl | rfl <;> decide
    haveI : Fact p.Prime := ⟨hpr⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (hp ▸ hdvd)
    have hg' : orderOf (g : V12 ≃ₗ[ZMod 2] V12) = p := by
      rw [← hg]
      exact orderOf_injective M.subtype M.subtype_injective g
    refine no_elem_order p ?_ hg'
    rcases hp' with rfl | rfl <;> decide
  rcases index_cases hi H with h | h | h | h
  ·
    intro m hm
    have htop : K = ⊤ := Subgroup.index_eq_one.1 h
    have : (⟨m, hm⟩ : ↥M) ∈ K := by rw [htop]; trivial
    exact mem_subgroupOf.1 this
  · exact (hprime 19 h (Or.inl rfl)).elim
  · exact (hprime 37 h (Or.inr rfl)).elim
  ·
    exfalso
    set Ω : Set V12 := orbit ↥M (vecOf a0) with hΩ
    set T : Set V12 := {v | v ≠ 0 ∧ q0 v = 0} \ Ω with hT
    have hΩsub : Ω ⊆ {v | v ≠ 0 ∧ q0 v = 0} := by
      rintro _ ⟨m, rfl⟩
      refine ⟨fun h0 => vecOf_a0_ne_zero ?_, ?_⟩
      · have : (m : V12 ≃ₗ[ZMod 2] V12) (vecOf a0) = 0 := h0
        exact (m : V12 ≃ₗ[ZMod 2] V12).injective (this.trans (map_zero _).symm)
      · change q0 ((m : V12 ≃ₗ[ZMod 2] V12) (vecOf a0)) = 0
        rw [H.isom _ m.2, q0_vecOf]
        rfl
    have hTcard : T.ncard = 9 := by
      rw [hT, Set.ncard_diff hΩsub (Set.toFinite _), ncard_sing, hΩ, card_orbit_a0 hi H, h]
    have hTinv : ∀ m ∈ M, ∀ t ∈ T, m t ∈ T := by
      intro m hm t ⟨⟨ht0, htq⟩, htΩ⟩
      refine ⟨⟨fun h0 => ht0 (m.injective (h0.trans (map_zero m).symm)), by rw [H.isom m hm, htq]⟩,
        fun ⟨n, hn⟩ => htΩ ⟨⟨m, hm⟩⁻¹ * n, ?_⟩⟩
      change (m⁻¹ * (n : V12 ≃ₗ[ZMod 2] V12)) (vecOf a0) = t
      rw [LinearEquiv.mul_apply]
      have hn' : (n : V12 ≃ₗ[ZMod 2] V12) (vecOf a0) = m t := hn
      rw [hn', inv_apply_apply]
    set W := Submodule.span (ZMod 2) T with hW
    have hWinv : ∀ m ∈ M, ∀ w ∈ W, m w ∈ W := by
      intro m hm w hw
      have hle : W ≤ W.comap (m : V12 →ₗ[ZMod 2] V12) :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hTinv m hm t ht)
      exact hle hw
    rcases H.irred W hWinv with hbot | htop
    · obtain ⟨t, ht⟩ : T.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hTcard]; norm_num)
      have : t ∈ W := Submodule.subset_span ht
      rw [hbot, Submodule.mem_bot] at this
      exact ht.1.1 this
    · have hfin := finrank_span_le_card (R := ZMod 2) T
      rw [← hW, htop, finrank_top, Module.finrank_fin_fun] at hfin
      have : T.toFinset.card = 9 := by rw [← Set.ncard_eq_toFinset_card']; exact hTcard
      omega

theorem false_of_step6Hyp : False := by
  have hU := le_gammaU hi H
  have hinv : ∀ m ∈ M, ∀ w ∈ SigmaP.sigma i, m w ∈ SigmaP.sigma i := by
    intro m hm w hw
    obtain ⟨hN, ha⟩ := H.step5 m hm (hU hm)
    have hS := SigmaP.s45_stable hi hN ha
    have hle : SigmaP.sigma i ≤ (SigmaP.sigma i).comap (m : V12 →ₗ[ZMod 2] V12) := by
      refine (SigmaP.sigma_le_span hi).trans (Submodule.span_le.2 ?_)
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hS x hx
      change m (vecOf x) ∈ SigmaP.sigma i
      rw [hxy]
      exact SigmaP.orbit_mem_sigma hi y hy
    exact hle hw
  have ha0 : vecOf a0 ∈ SigmaP.sigma i := by
    obtain ⟨y, hy, hay⟩ := SigmaP.orbit_subset hi 1 (one_mem _)
    rw [show (1 : V12 ≃ₗ[ZMod 2] V12) (vecOf a0) = vecOf a0 from rfl] at hay
    rw [hay]
    exact SigmaP.orbit_mem_sigma hi y hy
  rcases H.irred _ hinv with hbot | htop
  · rw [hbot, Submodule.mem_bot] at ha0
    exact vecOf_a0_ne_zero ha0
  · have h6 := SigmaP.finrank_sigma hi
    rw [htop, finrank_top, Module.finrank_fin_fun] at h6
    omega

end

end CFSG.GF2Type.Smith1979.GammaU.StepA
