module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise

variable {G : Type*} [Group G]

@[reducible] def conjOn {P L : Subgroup G} (hn : ∀ g ∈ P, ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    MulDistribMulAction ↥P ↥L where
  smul g x := ⟨g * x * (g : G)⁻¹, hn g g.2 x x.2⟩
  one_smul x := Subtype.ext (by
    change (1 : G) * (x : G) * (1 : G)⁻¹ = x
    simp)
  mul_smul g h x := Subtype.ext (by
    change ((g : G) * h) * (x : G) * ((g : G) * h)⁻¹ = g * ((h : G) * x * (h : G)⁻¹) * (g : G)⁻¹
    group)
  smul_one g := Subtype.ext (by
    change (g : G) * 1 * (g : G)⁻¹ = 1
    simp)
  smul_mul g x y := Subtype.ext (by
    change (g : G) * ((x : G) * y) * (g : G)⁻¹ = (g * x * (g : G)⁻¹) * (g * y * (g : G)⁻¹)
    group)

theorem exists_sylow_conj_invariant [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {P L : Subgroup G} (hP : IsPGroup p P) (hcop : ¬ p ∣ Nat.card L)
    (hn : ∀ g ∈ P, ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    ∃ V : Subgroup G, V ≤ L ∧ IsPGroup q V ∧ Nat.card V = q ^ (Nat.card L).factorization q ∧
      ∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  let _ := conjOn hn
  have hdvd : Nat.card (Sylow q ↥L) ∣ Nat.card L := by
    obtain ⟨T⟩ : Nonempty (Sylow q ↥L) := inferInstance
    exact (Sylow.card_dvd_index T).trans (Subgroup.index_dvd_card _)
  have hnd : ¬ p ∣ Nat.card (Sylow q ↥L) := fun h => hcop (h.trans hdvd)
  obtain ⟨T, hT⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥L) hnd
  refine ⟨(T : Subgroup ↥L).map L.subtype, Subgroup.map_subtype_le _, T.isPGroup'.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity]
  · rintro g hg _ ⟨t, ht, rfl⟩
    have hfix : (⟨g, hg⟩ : ↥P) • T = T := hT ⟨g, hg⟩
    have hmem : (⟨g, hg⟩ : ↥P) • t ∈ (((⟨g, hg⟩ : ↥P) • T : Sylow q ↥L) : Subgroup ↥L) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul t _ _ ht
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩

theorem exists_orbit_card_dvd {p : ℕ} (hp : p.Prime) {H X : Type*} [Group H] [MulAction H X]
    [Finite X] [Nonempty X] (hH : IsPGroup p H) :
    ∃ x₀ : X, (∀ x : X, Nat.card (MulAction.orbit H x₀) ∣ Nat.card (MulAction.orbit H x)) ∧
      Nat.card (MulAction.orbit H x₀) ∣ Nat.card X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min (fun x : X => Nat.card (MulAction.orbit H x))
  have hdvd : ∀ x : X, Nat.card (MulAction.orbit H x₀) ∣ Nat.card (MulAction.orbit H x) := by
    intro x
    obtain ⟨i, hi⟩ := hH.card_orbit x₀
    obtain ⟨j, hj⟩ := hH.card_orbit x
    have hle := hx₀ x
    rw [hi, hj] at hle ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 hle)
  refine ⟨x₀, hdvd, ?_⟩
  classical
  have : Fintype (MulAction.orbitRel.Quotient H X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits H X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => hdvd _

@[reducible] def conjOnNe {P V : Subgroup G} (hn : ∀ g ∈ P, ∀ x ∈ V, g * x * g⁻¹ ∈ V) :
    MulAction ↥P {v : ↥V // v ≠ 1} where
  smul g v := ⟨⟨g * v.1 * (g : G)⁻¹, hn g g.2 v.1 v.1.2⟩, fun h => v.2 (Subtype.ext (by
    have h1 := congrArg Subtype.val h
    change (g : G) * v.1 * (g : G)⁻¹ = 1 at h1
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1))⟩
  one_smul v := Subtype.ext (Subtype.ext (by
    change (1 : G) * v.1 * (1 : G)⁻¹ = v.1
    simp))
  mul_smul g h v := Subtype.ext (Subtype.ext (by
    change ((g : G) * h) * v.1 * ((g : G) * h)⁻¹ = g * ((h : G) * v.1 * (h : G)⁻¹) * (g : G)⁻¹
    group))

theorem card_stabilizer_conjOnNe {P V : Subgroup G} (hn : ∀ g ∈ P, ∀ x ∈ V, g * x * g⁻¹ ∈ V)
    (v : {v : ↥V // v ≠ 1}) :
    Nat.card (@MulAction.stabilizer ↥P _ _ (conjOnNe hn) v) =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({((v.1 : ↥V) : G)} : Set G)) := by
  let _ := conjOnNe hn
  have hmap : (MulAction.stabilizer ↥P v).map P.subtype =
      P ⊓ Subgroup.centralizer ({((v.1 : ↥V) : G)} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      have h1 := congrArg (fun u : {v : ↥V // v ≠ 1} => ((u.1 : ↥V) : G)) hg
      change (g : G) * v.1 * (g : G)⁻¹ = v.1 at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · rintro ⟨hxP, hx⟩
      refine ⟨⟨x, hxP⟩, Subtype.ext (Subtype.ext ?_), rfl⟩
      change x * v.1 * x⁻¹ = v.1
      rw [mul_inv_eq_iff_eq_mul]
      exact hx
  rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]

theorem exists_pow_dvd_of_orbits [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {C P V : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup p P) {a k : ℕ} (ha : Nat.card P = p ^ a)
    (hVC : V ≤ C) (hVq : IsPGroup q V) (hVc : Nat.card V = q ^ k) (hk : 0 < k)
    (hn : ∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V) {m : ℕ}
    (hm : ∀ w ∈ C, orderOf w = q → ∀ R : Subgroup G, IsPGroup p R → R ≤ C →
      R ≤ Subgroup.centralizer ({w} : Set G) → Nat.card R ≤ m) :
    ∃ j : ℕ, p ^ j ∣ q ^ k - 1 ∧ p ^ a ≤ p ^ j * m := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  let _ := conjOnNe hn
  have hV1 : (1 : ℕ) < Nat.card V := by
    rw [hVc]
    exact Nat.one_lt_pow hk.ne' hq.one_lt
  have : Nonempty {v : ↥V // v ≠ 1} := by
    obtain ⟨v, hv⟩ := @exists_ne _ (Finite.one_lt_card_iff_nontrivial.1 hV1) (1 : ↥V)
    exact ⟨⟨v, hv⟩⟩
  obtain ⟨x₀, -, hx₀⟩ := exists_orbit_card_dvd hp (H := ↥P) (X := {v : ↥V // v ≠ 1}) hP
  obtain ⟨j, hj⟩ := hP.card_orbit x₀
  refine ⟨j, ?_, ?_⟩
  · have hX : Nat.card {v : ↥V // v ≠ 1} = Nat.card V - 1 := by
      classical
      have := Fintype.ofFinite ↥V
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      convert Set.card_ne_eq (1 : ↥V)
      exact Iff.rfl
    rw [← hj, ← hVc, ← hX]
    exact hx₀
  ·
    set v : G := ((x₀.1 : ↥V) : G) with hvdef
    have hv1 : v ≠ 1 := fun h => x₀.2 (Subtype.ext h)
    have hvV : v ∈ V := x₀.1.2
    have hzq : q ∣ Nat.card (Subgroup.zpowers v) := by
      have hpg : IsPGroup q (Subgroup.zpowers v) := hVq.to_le (Subgroup.zpowers_le.2 hvV)
      obtain ⟨e, he⟩ := hpg.exists_card_eq
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at he
        exact hv1 he
      rw [he]
      exact dvd_pow_self q he0
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers v) q hzq
    have hwo : orderOf (w : G) = q := by rw [Subgroup.orderOf_coe, hw]
    have hwC : (w : G) ∈ C := hVC ((Subgroup.zpowers_le.2 hvV) w.2)
    have hle : P ⊓ Subgroup.centralizer ({v} : Set G) ≤
        P ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
      refine inf_le_inf_left _ ?_
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 w.2
      rw [← hi]
      exact ((Commute.zpow_left (show Commute v g from hg.symm) i)).eq.symm
    have hR := hm (w : G) hwC hwo (P ⊓ Subgroup.centralizer ({(w : G)} : Set G))
      (hP.to_le inf_le_left) (inf_le_left.trans hPC) inf_le_right
    have hstab : Nat.card (MulAction.stabilizer ↥P x₀) ≤ m :=
      (card_stabilizer_conjOnNe hn x₀).trans_le
        ((Subgroup.card_le_of_le hle).trans hR)
    classical
    have e1 : Nat.card (MulAction.orbit ↥P x₀) * Nat.card (MulAction.stabilizer ↥P x₀) =
        Nat.card ↥P := by
      have := Fintype.ofFinite ↥P
      have := Fintype.ofFinite (MulAction.orbit ↥P x₀)
      have := Fintype.ofFinite (MulAction.stabilizer ↥P x₀)
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥P x₀
    rw [hj, ha] at e1
    rw [← e1]
    exact Nat.mul_le_mul_left _ hstab

theorem gLAPPrimeCoreOf_eq_bot_of_orbits [Finite G] {p : ℕ} (hp : p.Prime) {C P : Subgroup G}
    (hPC : P ≤ C) (hP : IsPGroup p P) {a : ℕ} (ha : Nat.card P = p ^ a)
    (h : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card C →
      (∃ m : ℕ, (∀ w ∈ C, orderOf w = q → ∀ R : Subgroup G, IsPGroup p R → R ≤ C →
          R ≤ Subgroup.centralizer ({w} : Set G) → Nat.card R ≤ m) ∧
        ∀ k j : ℕ, 0 < k → q ^ k ∣ Nat.card C → p ^ j ∣ q ^ k - 1 → p ^ j * m < p ^ a) ∨
      ∃ A : Subgroup G, A ≤ C ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
        ∀ x ∈ A, x ≠ 1 → ¬ q ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({x} : Set G))) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hL
  set L := GLAPPrimeCoreOf p C with hLdef
  have hLC : L ≤ C := GLAPPrimeCoreOf_le C
  have hcop' : ¬ p ∣ Nat.card L :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_GLAPPrimeCoreOf hp C)
  have hLne : Nat.card L ≠ 1 := fun h1 => hL (Subgroup.card_eq_one.1 h1)
  obtain ⟨q, hq, hqL⟩ := Nat.exists_prime_and_dvd hLne
  have : Fact q.Prime := ⟨hq⟩
  have hqp : q ≠ p := by
    rintro rfl
    exact hcop' hqL
  have hqC : q ∣ Nat.card C := hqL.trans (Subgroup.card_dvd_of_le hLC)
  have hk0 : 0 < (Nat.card L).factorization q :=
    hq.factorization_pos_of_dvd Nat.card_pos.ne' hqL
  rcases h q hq hqp hqC with ⟨m, hm, hkj⟩ | ⟨A, hAC, hA, hAc, hAq⟩
  · obtain ⟨V, hVL, hVq, hVc, hVn⟩ := exists_sylow_conj_invariant hp hq hP hcop'
      (fun g hg x hx => GLAPPrimeCoreOf_conj_mem g (hPC hg) x hx)
    have hqkC : q ^ (Nat.card L).factorization q ∣ Nat.card C :=
      (Nat.ordProj_dvd _ _).trans (Subgroup.card_dvd_of_le hLC)
    obtain ⟨j, hj1, hj2⟩ :=
      exists_pow_dvd_of_orbits hp hq hPC hP ha (hVL.trans hLC) hVq hVc hk0 hVn hm
    have := hkj _ j hk0 hqkC hj1
    omega
  · have hAp : IsPGroup p A := IsPGroup.of_card hAc
    obtain ⟨V, hVL, hVq, hVc, hVn⟩ := exists_sylow_conj_invariant hp hq hAp hcop'
      (fun g hg x hx => GLAPPrimeCoreOf_conj_mem g (hAC hg) x hx)
    have hVnp : ¬ p ∣ Nat.card V := fun hd => hcop' (hd.trans (Subgroup.card_dvd_of_le hVL))
    have hnorm : A ≤ Subgroup.normalizer (V : Set G) := by
      intro g hg
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hVn g hg x hx, fun hx => ?_⟩
      have := hVn g⁻¹ (A.inv_mem hg) _ hx
      simpa [mul_assoc] using this
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      p hp A V (fun x => Subtype.ext (by simpa using hA.2 x x.2)) hAc hVnp hnorm
    have hbot : V = ⊥ := by
      rw [hgen]
      refine iSup_eq_bot.2 fun x => iSup_eq_bot.2 fun hx => ?_
      have hx1 : (x : G) ≠ 1 := fun e => hx (Subtype.ext e)
      have hle : V ⊓ Subgroup.centralizer ({(x : G)} : Set G) ≤
          C ⊓ Subgroup.centralizer ({(x : G)} : Set G) :=
        inf_le_inf_right _ (hVL.trans hLC)
      have hpg : IsPGroup q ↥(V ⊓ Subgroup.centralizer ({(x : G)} : Set G)) :=
        hVq.to_le inf_le_left
      obtain ⟨e, he⟩ := hpg.exists_card_eq
      rcases e with _ | e
      · exact Subgroup.card_eq_one.1 (by simpa using he)
      · exfalso
        apply hAq x x.2 hx1
        have hd : q ∣ Nat.card ↥(V ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
          rw [he]
          exact dvd_pow_self q (Nat.succ_ne_zero e)
        exact hd.trans (Subgroup.card_dvd_of_le hle)
    rw [hbot, Subgroup.card_bot] at hVc
    have := Nat.one_lt_pow hk0.ne' hq.one_lt
    omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
