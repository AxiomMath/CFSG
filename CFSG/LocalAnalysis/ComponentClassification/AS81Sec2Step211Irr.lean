module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Ker

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_modEq_card_inf_centralizer {B : Subgroup G} {a : G}
    (haB : a ∈ normalizer (B : Set G)) {p k : ℕ} [Fact p.Prime]
    (hak : ∀ b ∈ B, a ^ p ^ k * b * (a ^ p ^ k)⁻¹ = b) :
    Nat.card B ≡ Nat.card (B ⊓ centralizer ({a} : Set G) : Subgroup G) [MOD p] := by
  classical
  have : Fintype ↥B := Fintype.ofFinite _
  let σ : Equiv.Perm ↥B :=
    { toFun := fun b => ⟨a * b * a⁻¹, (mem_normalizer_iff.mp haB b).mp b.2⟩
      invFun := fun b => ⟨a⁻¹ * b * a, by
        simpa using (mem_normalizer_iff.mp (inv_mem haB) b).mp b.2⟩
      left_inv := fun b => Subtype.ext (by simp [mul_assoc])
      right_inv := fun b => Subtype.ext (by simp [mul_assoc]) }
  have hpow : ∀ j : ℕ, ∀ b : ↥B, (((σ ^ j) b : ↥B) : G) = a ^ j * b * (a ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [pow_succ', Equiv.Perm.mul_apply]
      show a * (((σ ^ j) b : ↥B) : G) * a⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσ : σ ^ p ^ k = 1 := Equiv.ext fun b => Subtype.ext (by
    rw [hpow, hak b b.2]
    rfl)
  have hσb : ∀ b : ↥B, σ b = b ↔ (b : G) ∈ centralizer ({a} : Set G) := fun b => by
    rw [mem_centralizer_singleton_iff, Subtype.ext_iff]
    show a * (b : G) * a⁻¹ = b ↔ _
    constructor
    · intro h
      calc (b : G) * a = a * b * a⁻¹ * a := by rw [h]
        _ = a * b := by group
    · intro h
      rw [← h]
      group
  have hfix : (σ.supportᶜ).card = Nat.card (B ⊓ centralizer ({a} : Set G) : Subgroup G) := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr
      { toFun := fun b => ⟨b.1, b.1.2, (hσb b.1).mp (by
          have h := b.2
          rwa [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at h)⟩
        invFun := fun c => ⟨⟨c, c.2.1⟩, by
          rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
          exact (hσb _).mpr c.2.2⟩
        left_inv := fun b => rfl
        right_inv := fun c => rfl }
  have h := Equiv.Perm.card_compl_support_modEq hσ
  rw [Nat.card_eq_fintype_card, ← hfix]
  exact h.symm

theorem card_modEq_one_of_fix {B : Subgroup G} {a : G} (haB : a ∈ normalizer (B : Set G))
    {p k : ℕ} [Fact p.Prime] (hak : ∀ b ∈ B, a ^ p ^ k * b * (a ^ p ^ k)⁻¹ = b)
    (hfix : ∀ b ∈ B, a * b * a⁻¹ = b → b = 1) :
    Nat.card B ≡ 1 [MOD p] := by
  have h := card_modEq_card_inf_centralizer haB hak
  have hbot : B ⊓ centralizer ({a} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    refine hfix b hb.1 ?_
    have h1 := mem_centralizer_singleton_iff.mp hb.2
    rw [← h1]
    group
  rwa [hbot, card_bot] at h

omit [Finite G] in
theorem eq_bot_or_eq_of_card_modEq [Finite G] {B V : Subgroup G} (hBV : B ≤ V)
    (hV : Nat.card V = 16) (h5 : Nat.card B ≡ 1 [MOD 5]) : B = ⊥ ∨ B = V := by
  have hdvd : Nat.card B ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hV]
    exact Subgroup.card_dvd_of_le hBV
  obtain ⟨j, hj, hjB⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases j
  · left
    exact Subgroup.card_eq_one.mp (by rw [hjB]; rfl)
  · rw [hjB] at h5; exact absurd h5 (by decide)
  · rw [hjB] at h5; exact absurd h5 (by decide)
  · rw [hjB] at h5; exact absurd h5 (by decide)
  · right
    exact Subgroup.eq_of_le_of_card_ge hBV (by rw [hV, hjB]; norm_num)

omit [Finite G] in
theorem commutator_mul_mul_eq {a b e f : G} (heb : e * b = b * e) (hfa : f * a = a * f)
    (hef : e * f = f * e) : a * e * (b * f) * (a * e)⁻¹ * (b * f)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hfa' : f * a⁻¹ = a⁻¹ * f := (Commute.inv_right (show Commute f a from hfa)).eq
  calc a * e * (b * f) * (a * e)⁻¹ * (b * f)⁻¹
      = a * (e * b) * f * e⁻¹ * a⁻¹ * f⁻¹ * b⁻¹ := by group
    _ = a * (b * e) * f * e⁻¹ * a⁻¹ * f⁻¹ * b⁻¹ := by rw [heb]
    _ = a * b * (e * f) * e⁻¹ * a⁻¹ * f⁻¹ * b⁻¹ := by group
    _ = a * b * (f * e) * e⁻¹ * a⁻¹ * f⁻¹ * b⁻¹ := by rw [hef]
    _ = a * b * (f * a⁻¹) * f⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * f) * f⁻¹ * b⁻¹ := by rw [hfa']
    _ = a * b * a⁻¹ * b⁻¹ := by group

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_centralizer_of_commute_of_odd (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {a w : G} (haA : a ∈ A)
    (ha : Odd (orderOf a)) (hwA : w ∈ A) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) (haw : a * w = w * a) :
    a ∈ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hNZ := oddCore_le_center hq.1 hq.2
  obtain ⟨T, hT, hwT⟩ := exists_isSylowOf_mem_centerIn c hwA hw2 hw1
  have hwK : w ∉ centralizer (A : Set G) := fun h => by
    have h1 := inf_eq_bot_of_odd_center (zpowers_le.mpr h)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1, pow_one]))
      hodd
    have h2 : w ∈ zpowers w ⊓ A := ⟨mem_zpowers w, hwA⟩
    rw [h1, mem_bot] at h2
    exact hw1 h2
  have hu := mem_sup_centralizer_of_commute c hNZ hT hwT hwK haA haw
  have hKT : centralizer (A : Set G) ≤ normalizer (T : Set G) := fun k hk =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      (mem_centralizer_iff.mp hk t (hT.le ht)))
  have hu' : a ∈ ((T ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := hu
  rw [coe_mul_of_right_le_normalizer_left T _ hKT] at hu'
  obtain ⟨t, htT, k, hk, rfl⟩ := hu'
  have htA : t ∈ A := hT.le htT
  have hconj : ∀ b ∈ A, t * k * b * (t * k)⁻¹ = t * b * t⁻¹ := fun b hb => by
    have hkb : b * k = k * b := mem_centralizer_iff.mp hk b hb
    calc t * k * b * (t * k)⁻¹ = t * (k * b) * k⁻¹ * t⁻¹ := by group
      _ = t * (b * k) * k⁻¹ * t⁻¹ := by rw [hkb]
      _ = t * b * t⁻¹ := by group
  have hpow : ∀ j : ℕ, ∀ b ∈ A, (t * k) ^ j * b * ((t * k) ^ j)⁻¹ = t ^ j * b * (t ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro b _; simp
    | succ j ih =>
      intro b hb
      have htb : t * b * t⁻¹ ∈ A := A.mul_mem (A.mul_mem htA hb) (A.inv_mem htA)
      calc (t * k) ^ (j + 1) * b * ((t * k) ^ (j + 1))⁻¹
          = (t * k) ^ j * (t * k * b * (t * k)⁻¹) * ((t * k) ^ j)⁻¹ := by
            rw [pow_succ]; group
        _ = (t * k) ^ j * (t * b * t⁻¹) * ((t * k) ^ j)⁻¹ := by rw [hconj b hb]
        _ = t ^ j * (t * b * t⁻¹) * (t ^ j)⁻¹ := ih _ htb
        _ = t ^ (j + 1) * b * (t ^ (j + 1))⁻¹ := by rw [pow_succ]; group
  set m := orderOf (t * k) with hm
  have hm1 : (t * k) ^ m = 1 := pow_orderOf_eq_one _
  have h3 : ∀ b ∈ A, Commute (t ^ m) b := fun b hb => by
    have h1 := hpow m b hb
    rw [hm1, one_mul, inv_one, mul_one] at h1
    rw [Commute, SemiconjBy, mul_inv_eq_iff_eq_mul.mp h1.symm]
  obtain ⟨n, hn⟩ := hT.isPGroup ⟨t, htT⟩
  have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime m (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr ha)
  have hab := Nat.gcd_eq_gcd_ab m (2 ^ n)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hab
  have ht : t = (t ^ m) ^ (Nat.gcdA m (2 ^ n)) * (t ^ 2 ^ n) ^ (Nat.gcdB m (2 ^ n)) := by
    rw [← zpow_natCast t m, ← zpow_natCast t (2 ^ n), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hab, zpow_one]
  have htC : ∀ b ∈ A, Commute t b := fun b hb => by
    rw [ht, htn, one_zpow, mul_one]
    exact (h3 b hb).zpow_left _
  refine mem_centralizer_iff.mpr fun b hb => ?_
  have h1 := (htC b hb).eq
  have h2 : b * k = k * b := mem_centralizer_iff.mp hk b hb
  calc b * (t * k) = (b * t) * k := by group
    _ = (t * b) * k := by rw [h1]
    _ = t * (b * k) := by group
    _ = t * (k * b) := by rw [h2]
    _ = t * k * b := by group

theorem mem_centralizer_E_of_mem_centralizer (hF : Frame G A A R g E F) {n : G} (hnA : n ∈ A)
    (hnC : n ∈ centralizer (A : Set G)) : n ∈ centralizer (E : Set G) := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
  have hle : (E ⊓ A : Subgroup G) ⊔ R ≤ centralizer ({n} : Set G) := sup_le
    (fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hnC a ha.2))
    (fun r hr => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRA hr) n hnA).symm)
  exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hle ha)

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) (e : ↥(sec2PlanesP E F) ≃ Fin 6)

include h11 hE16 hF hL hodd hx hxS h4

omit h4 in
theorem sec2PlanesActionFin_eq_one_of_mem_centralizer {n : ↥(normalizer (sec2P E : Set G))}
    (hnA : (n : G) ∈ A) (hnC : (n : G) ∈ centralizer (A : Set G)) :
    sec2PlanesActionFin E F e n = 1 := by
  have hnE : (n : G) ∈ normalizer (E : Set G) :=
    centralizer_le_normalizer _ (mem_centralizer_E_of_mem_centralizer hF hnA hnC)
  have hnF : (n : G) ∈ normalizer (F : Set G) :=
    centralizer_le_normalizer _ (mem_centralizer_E_of_mem_centralizer hF.symm hnA hnC)
  have hnF0 := mem_normalizer_sec2F0_of_mem h11 hE16 hF hL hodd hnA hnE hnF hx hxS
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply, sec2PlanesActionFin_apply_eq_iff]
  set V := e.symm i with hV
  by_cases hVE : (V : Subgroup G) = E
  · rw [hVE]
    exact hnE
  · obtain ⟨m, hm, hVm, -, -⟩ :=
      exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS V.2.1 V.2.2 hVE
    rw [hVm]
    have hnm : (n : G) * m = m * n := (mem_centralizer_iff.mp hnC m hm.1).symm
    refine mem_normalizer_iff.mpr fun v => ?_
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have h1 : m * (n * v * (n : G)⁻¹) * m⁻¹ = n * (m * v * m⁻¹) * (n : G)⁻¹ := by
      calc m * (n * v * (n : G)⁻¹) * m⁻¹ = (m * n) * v * (m * n)⁻¹ := by group
        _ = (n * m) * v * (n * m)⁻¹ := by rw [hnm]
        _ = n * (m * v * m⁻¹) * (n : G)⁻¹ := by group
    rw [h1]
    exact mem_normalizer_iff.mp hnF0 _

theorem nonempty_equiv_fin : Nonempty (↥(sec2PlanesP E F) ≃ Fin 6) :=
  ⟨Finite.equivFinOfCardEq (ncard_planes_sec2P h11 hE16 hF hL hodd hx hxS h4)⟩

theorem exists_five_element : ∃ a : G, a ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
    (∃ k : ℕ, a ^ 5 ^ k = 1) ∧ ∃ ha : a ∈ normalizer (sec2P E : Set G),
      sec2PlanesActionFin E F e ⟨a, ha⟩ ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set X := A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) with hX
  have hXP : X ≤ normalizer (sec2P E : Set G) := fun m hm =>
    Sec2.normalizer_le_normalizer_sec2P E (mem_normalizer_of_mem_inf_normalizer hF hm).1
  set ρX := (sec2PlanesActionFin E F e).comp (inclusion hXP) with hρX
  have hEpl : E ∈ sec2PlanesP E F :=
    ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  have hF0pl : sec2F0 A E x ∈ sec2PlanesP E F :=
    ⟨sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4, sec2F0_le_sec2P hF x⟩
  set i₀ := e ⟨E, hEpl⟩ with hi₀
  set i₁ := e ⟨_, hF0pl⟩ with hi₁
  have h01 : i₁ ≠ i₀ := fun h => by
    have h1 := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rw [rightConjugate_one] at h1
    exact h1 (congrArg Subtype.val (e.injective h))
  have hfix : ∀ m : ↥X, ρX m i₀ = i₀ := fun m => by
    rw [hρX, MonoidHom.comp_apply, sec2PlanesActionFin_apply_eq_iff, hi₀,
      Equiv.symm_apply_apply]
    exact (mem_normalizer_of_mem_inf_normalizer hF m.2).1
  have horb : ∀ j : Fin 6, j ≠ i₀ → ∃ m : ↥X, ρX m i₁ = j := by
    intro j hj
    have hVE : ((e.symm j : ↥(sec2PlanesP E F)) : Subgroup G) ≠ E := fun h => hj (by
      rw [← Equiv.apply_symm_apply e j]
      exact congrArg e (Subtype.ext h))
    obtain ⟨m, hm, hVm, -, -⟩ := exists_eq_of_mem_planes_ne h11 hE16 hF hL hodd hx hxS
      (e.symm j).2.1 (e.symm j).2.2 hVE
    refine ⟨⟨m⁻¹, inv_mem hm⟩, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    rw [hρX, MonoidHom.comp_apply, coe_symm_sec2PlanesActionFin_apply, hi₁,
      Equiv.symm_apply_apply, hVm]
    change rightConjugate _ (m⁻¹)⁻¹ = _
    rw [inv_inv]
  set T := ρX.range with hT
  have horbit : MulAction.orbit T i₁ = {j | j ≠ i₀} := by
    ext j
    constructor
    · rintro ⟨⟨t, m, rfl⟩, rfl⟩ h
      change ρX m i₁ = i₀ at h
      exact h01 ((ρX m).injective (h.trans (hfix m).symm))
    · intro hj
      obtain ⟨m, hm⟩ := horb j hj
      exact ⟨⟨ρX m, m, rfl⟩, hm⟩
  have hcard : (MulAction.orbit T i₁).ncard = 5 := by
    rw [horbit, Set.ncard_eq_toFinset_card']
    rw [show Set.toFinset {j : Fin 6 | j ≠ i₀} = Finset.univ.erase i₀ by
      ext j; simp]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have h5 : 5 ∣ Nat.card T := by
    rw [← hcard, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨m, hm⟩ := σ.2
  obtain ⟨r, s, hs, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 5 (by norm_num)
  refine ⟨(m : G) ^ s, pow_mem m.2 s, ⟨r, ?_⟩, hXP (pow_mem m.2 s), ?_⟩
  · rw [← pow_mul, mul_comm, ← hrs, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  · intro h1
    have h2 : (σ : Equiv.Perm (Fin 6)) ^ s = 1 := by
      rw [← hm, ← map_pow]
      exact h1
    have h3 : σ ^ s = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h2)
    exact hs (hσ ▸ orderOf_dvd_of_pow_eq_one h3)

omit h4 in
theorem eq_one_of_conj_eq_of_five {a : G} (haA : a ∈ A) {k : ℕ} (hak : a ^ 5 ^ k = 1)
    (ha : a ∈ normalizer (sec2P E : Set G)) (hρ : sec2PlanesActionFin E F e ⟨a, ha⟩ ≠ 1)
    {w : G} (hw : w ∈ E ⊓ A) (haw : a * w * a⁻¹ = w) : w = 1 := by
  by_contra hw1
  have hodd' : Odd (orderOf a) := by
    have h := orderOf_dvd_of_pow_eq_one hak
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp h
    rw [hj]
    exact Odd.pow (by decide)
  have hw2 : w ^ 2 = 1 := hF.elemE.2 w hw.1
  have haw' : a * w = w * a := by
    calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [haw]
  exact hρ (sec2PlanesActionFin_eq_one_of_mem_centralizer h11 hE16 hF hL hodd hx hxS e haA
    (mem_centralizer_of_commute_of_odd hF hL hodd haA hodd' hw.2 hw2 hw1 haw'))

theorem eq_bot_or_eq_of_le_inf {B : Subgroup G} (hB : B ≤ E ⊓ A)
    (hKB : sec2K E ≤ normalizer (B : Set G)) : B = ⊥ ∨ B = E ⊓ A := by
  obtain ⟨e⟩ := nonempty_equiv_fin h11 hE16 hF hL hodd hx hxS h4
  obtain ⟨a, ha, ⟨k, hk⟩, haP, hρ⟩ := exists_five_element h11 hE16 hF hL hodd hx hxS h4 e
  have hodd' : Odd (orderOf a) := by
    have h := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp h
    rw [hj]
    exact Odd.pow (by decide)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 := card_modEq_one_of_fix (hKB (mem_sec2K_of_odd haP hodd')) (p := 5) (k := k)
    (fun b _ => by rw [hk]; group)
    (fun b hb hab => eq_one_of_conj_eq_of_five h11 hE16 hF hL hodd hx hxS e ha.1 hk haP hρ
      (hB hb) hab)
  exact eq_bot_or_eq_of_card_modEq hB (card_inf_left hF hodd) h5

theorem commutator_sec2P_eq : ⁅sec2P E, sec2P E⁆ = E ⊓ A := by
  have hle : ⁅sec2P E, sec2P E⁆ ≤ E ⊓ A := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 ha hb).2
  have hK : sec2K E ≤ normalizer ((⁅sec2P E, sec2P E⁆ : Subgroup G) : Set G) := fun k hk => by
    have hkP := sec2K_le_normalizer_sec2P E hk
    refine Sec2.mem_normalizer_of_forall_conj_mem fun c hc => ?_
    have hle' : ⁅sec2P E, sec2P E⁆ ≤ (⁅sec2P E, sec2P E⁆).comap (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e1 : k * ⁅a, b⁆ * k⁻¹ = ⁅k * a * k⁻¹, k * b * k⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [e1]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.mp hkP a).mp ha)
        ((mem_normalizer_iff.mp hkP b).mp hb)
    exact hle' hc
  rcases eq_bot_or_eq_of_le_inf h11 hE16 hF hL hodd hx hxS h4 hle hK with h | h
  · exfalso
    have hEpl : E ∈ planes E F := ⟨1, Or.inl (rightConjugate_one E).symm⟩
    obtain ⟨hF0e, hF064⟩ := isElemAbelian_and_card_of_mem_planes hF
      (sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4)
    have hF0E : sec2F0 A E x ≤ E := by
      intro f hf
      have hfP := sec2F0_le_sec2P hF x hf
      have hfC : f ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun a ha => by
        have h1 : ⁅a, f⁆ ∈ ⁅sec2P E, sec2P E⁆ :=
          Subgroup.commutator_mem_commutator (le_sec2P_of_frame hF ha) hfP
        rw [h, mem_bot, commutatorElement_def] at h1
        calc a * f = a * f * a⁻¹ * f⁻¹ * (f * a) := by group
          _ = f * a := by rw [h1, one_mul]
      have hf2 : f ^ 2 ^ 1 = 1 := by
        rw [pow_one]
        exact hF0e.2 f hf
      exact mem_of_mem_centralizer_of_mem_planes hF hL hodd hEpl hfC hf2
    have hcard : Nat.card (sec2F0 A E x) = Nat.card E := by
      rw [hF064, hF.cardE]
    have heq := Subgroup.eq_of_le_of_card_ge hF0E hcard.ge
    have h1 := rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS (Subgroup.one_mem _)
    rw [rightConjugate_one] at h1
    exact h1 heq
  · exact h

theorem centralizerMod_le_centralizer :
    centralizerMod (sec2K E) (sec2P E) (E ⊓ A) ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
  intro c hc
  obtain ⟨-, -, hcP⟩ := mem_centralizerMod.mp hc
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hEAP : E ⊓ A ≤ sec2P E := inf_le_left.trans (le_sec2P_of_frame hF)
  have hcomm : ⁅sec2P E, sec2P E⁆ ≤ centralizer ({c} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_centralizer_singleton_iff, commutatorElement_def]
    set α := a⁻¹ * c⁻¹ * a * c with hα
    set β := b⁻¹ * c⁻¹ * b * c with hβ
    have hαE : α ∈ E ⊓ A := hcP a ha
    have hβE : β ∈ E ⊓ A := hcP b hb
    have hab : c⁻¹ * (a * b * a⁻¹ * b⁻¹) * c = a * α * (b * β) * (a * α)⁻¹ * (b * β)⁻¹ := by
      rw [hα, hβ]
      group
    have heb : α * b = b * α := mem_centralizer_iff.mp (hPC hb) α hαE
    have hfa : β * a = a * β := mem_centralizer_iff.mp (hPC ha) β hβE
    have hef : α * β = β * α := mem_centralizer_iff.mp (hPC (hEAP hβE)) α hαE
    rw [commutator_mul_mul_eq heb hfa hef] at hab
    calc a * b * a⁻¹ * b⁻¹ * c = c * (c⁻¹ * (a * b * a⁻¹ * b⁻¹) * c) := by group
      _ = c * (a * b * a⁻¹ * b⁻¹) := by rw [hab]
  rw [← commutator_sec2P_eq h11 hE16 hF hL hodd hx hxS h4]
  exact mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (hcomm hw)

end Frame

end CFSG.ComponentClassification.AS81
