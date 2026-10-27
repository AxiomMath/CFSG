module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGBridge

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

section LocalPairFacts

variable {X : Type} [Group X] {τ : X} {D S : Subgroup X}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Equiv.Perm (Fin 5)}

theorem LocalPair.pow_split (h : LocalPair τ D S eD eS) {d s : X} (hd : d ∈ D) (hs : s ∈ S)
    (n : ℕ) : (d * s) ^ n = d ^ n * s ^ n :=
  (Commute.mul_pow (h.comm d hd s hs) n)

theorem LocalPair.pow_eq_one_iff (h : LocalPair τ D S eD eS) {d s : X} (hd : d ∈ D) (hs : s ∈ S)
    (n : ℕ) : (d * s) ^ n = 1 ↔ d ^ n = 1 ∧ s ^ n = 1 := by
  rw [h.pow_split hd hs]
  constructor
  · intro h1
    have h2 : d ^ n = (s ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : d ^ n = 1 := h.inf _ (pow_mem hd n) (by rw [h2]; exact inv_mem (pow_mem hs n))
    refine ⟨h3, ?_⟩
    rw [h3, one_mul] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    rw [h1, h2, one_mul]

theorem dihedral_pow_odd : (∀ a : DihedralGroup 4, a ^ 13 = 1 → a = 1) ∧
    ∀ a : DihedralGroup 4, a ^ 15 = 1 → a = 1 := by
  have h8 : ∀ a : DihedralGroup 4, a ^ 8 = 1 := by
    intro a
    have h := pow_card_eq_one' (G := DihedralGroup 4) (x := a)
    rwa [Nat.card_eq_fintype_card, DihedralGroup.card] at h
  refine ⟨fun a h => ?_, fun a h => ?_⟩
  · have := pow_gcd_eq_one.2 ⟨h, h8 a⟩
    simpa using this
  · have := pow_gcd_eq_one.2 ⟨h, h8 a⟩
    simpa using this

theorem perm_five_no_orders : (∀ σ : Equiv.Perm (Fin 5), σ ^ 13 = 1 → σ = 1) ∧
    ∀ σ : Equiv.Perm (Fin 5), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  refine ⟨fun σ h => ?_, fun σ h => ?_⟩
  · have h120 : σ ^ 120 = 1 := by
      have h' := pow_card_eq_one' (G := Equiv.Perm (Fin 5)) (x := σ)
      rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h'
    have := pow_gcd_eq_one.2 ⟨h, h120⟩
    simpa using this
  · have hord : orderOf σ ∣ 15 := orderOf_dvd_of_pow_eq_one h
    have hsum : σ.cycleType.sum ≤ 5 := by
      have h5 := Equiv.Perm.sum_cycleType_le σ
      simpa using h5
    have hmem : ∀ n ∈ σ.cycleType, n = 3 ∨ n = 5 := by
      intro n hn
      have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
      have h15 : n ∣ 15 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
      have hle : n ≤ σ.cycleType.sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) n hn
      have h5 : n ≤ 5 := hle.trans hsum
      interval_cases n <;> simp_all
    by_cases h3 : 3 ∈ σ.cycleType
    · by_cases h5 : 5 ∈ σ.cycleType
      · exfalso
        obtain ⟨c', hc'⟩ := Multiset.exists_cons_of_mem h3
        have h5' : 5 ∈ c' := by
          have : 5 ∈ (3 ::ₘ c') := hc' ▸ h5
          simpa using this
        obtain ⟨c'', hc''⟩ := Multiset.exists_cons_of_mem h5'
        rw [hc', hc'', Multiset.sum_cons, Multiset.sum_cons] at hsum
        omega
      · left
        have hd : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.2 fun n hn => by
          rcases hmem n hn with rfl | rfl
          · exact dvd_rfl
          · exact absurd hn h5
        rw [Equiv.Perm.lcm_cycleType] at hd
        exact orderOf_dvd_iff_pow_eq_one.1 hd
    · right
      have hd : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.2 fun n hn => by
        rcases hmem n hn with rfl | rfl
        · exact absurd hn h3
        · exact dvd_rfl
      rw [Equiv.Perm.lcm_cycleType] at hd
      exact orderOf_dvd_iff_pow_eq_one.1 hd

theorem LocalPair.false_of_order_fifteen (h : LocalPair τ D S eD eS) {x : X} (hx : x * τ = τ * x)
    (h15 : x ^ 15 = 1) (h3 : x ^ 3 ≠ 1) (h5 : x ^ 5 ≠ 1) : False := by
  obtain ⟨d, hd, s, hs, rfl⟩ := (h.cent x).1 hx
  obtain ⟨hd1, hs1⟩ := (h.pow_eq_one_iff hd hs 15).1 h15
  have hd0 : d = 1 := by
    have := dihedral_pow_odd.2 (eD ⟨d, hd⟩) (by
      rw [← map_pow]
      have : (⟨d, hd⟩ : D) ^ 15 = 1 := Subtype.ext hd1
      rw [this, map_one])
    have h2 : (⟨d, hd⟩ : D) = 1 := eD.injective (by rw [this, map_one])
    exact congrArg Subtype.val h2
  subst hd0
  have hs15 : eS ⟨s, hs⟩ ^ 15 = 1 := by
    rw [← map_pow]
    have : (⟨s, hs⟩ : S) ^ 15 = 1 := Subtype.ext hs1
    rw [this, map_one]
  rcases perm_five_no_orders.2 _ hs15 with h' | h'
  · apply h3
    rw [one_mul]
    have : (⟨s, hs⟩ : S) ^ 3 = 1 := eS.injective (by rw [map_pow, h', map_one])
    exact congrArg Subtype.val this
  · apply h5
    rw [one_mul]
    have : (⟨s, hs⟩ : S) ^ 5 = 1 := eS.injective (by rw [map_pow, h', map_one])
    exact congrArg Subtype.val this

theorem LocalPair.false_of_order_thirteen (h : LocalPair τ D S eD eS) {x : X} (hx : x * τ = τ * x)
    (h13 : x ^ 13 = 1) (h1 : x ≠ 1) : False := by
  obtain ⟨d, hd, s, hs, rfl⟩ := (h.cent x).1 hx
  obtain ⟨hd1, hs1⟩ := (h.pow_eq_one_iff hd hs 13).1 h13
  have hd0 : d = 1 := by
    have := dihedral_pow_odd.1 (eD ⟨d, hd⟩) (by
      rw [← map_pow]
      have : (⟨d, hd⟩ : D) ^ 13 = 1 := Subtype.ext hd1
      rw [this, map_one])
    have h2 : (⟨d, hd⟩ : D) = 1 := eD.injective (by rw [this, map_one])
    exact congrArg Subtype.val h2
  subst hd0
  have hs15 : eS ⟨s, hs⟩ ^ 13 = 1 := by
    rw [← map_pow]
    have : (⟨s, hs⟩ : S) ^ 13 = 1 := Subtype.ext hs1
    rw [this, map_one]
  have h2 : eS ⟨s, hs⟩ = 1 := perm_five_no_orders.1 _ hs15
  have h3 : (⟨s, hs⟩ : S) = 1 := eS.injective (by rw [h2, map_one])
  apply h1
  rw [one_mul]
  exact congrArg Subtype.val h3

theorem dihedral_comm : ∀ a b : DihedralGroup 4,
    b * a = a * b ∨ b * a = a * DihedralGroup.r 2 * b := by
  decide

theorem LocalPair.cent_comm_D (h : LocalPair τ D S eD eS) {x d : X} (hx : x * τ = τ * x)
    (hd : d ∈ D) : x * d = d * x ∨ x * d = (d * τ) * x := by
  obtain ⟨d'', hd'', s'', hs'', rfl⟩ := (h.cent x).1 hx
  obtain ⟨hτD, hτe⟩ := h.tau_mem
  have hss : s'' * d = d * s'' := (h.comm d hd s'' hs'').symm
  have hs2 : s'' * d'' = d'' * s'' := (h.comm d'' hd'' s'' hs'').symm
  rcases dihedral_comm (eD ⟨d, hd⟩) (eD ⟨d'', hd''⟩) with h1 | h1
  · left
    have h2 : d'' * d = d * d'' := by
      have := eD.injective (a₁ := (⟨d'', hd''⟩ : D) * ⟨d, hd⟩) (a₂ := ⟨d, hd⟩ * ⟨d'', hd''⟩)
        (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val this
    calc d'' * s'' * d = d'' * (s'' * d) := by group
      _ = d'' * (d * s'') := by rw [hss]
      _ = (d'' * d) * s'' := by group
      _ = (d * d'') * s'' := by rw [h2]
      _ = d * (d'' * s'') := by group
  · right
    have h2 : d'' * d = d * τ * d'' := by
      have := eD.injective (a₁ := (⟨d'', hd''⟩ : D) * ⟨d, hd⟩)
        (a₂ := ⟨d, hd⟩ * ⟨τ, hτD⟩ * ⟨d'', hd''⟩)
        (by rw [map_mul, map_mul, map_mul, hτe]; exact h1)
      exact congrArg Subtype.val this
    calc d'' * s'' * d = d'' * (s'' * d) := by group
      _ = d'' * (d * s'') := by rw [hss]
      _ = (d'' * d) * s'' := by group
      _ = (d * τ * d'') * s'' := by rw [h2]
      _ = (d * τ) * (d'' * s'') := by group

theorem LocalPair.card_cent [Finite X] (h : LocalPair τ D S eD eS) :
    Nat.card (centralizer ({τ} : Set X)) = 960 := by
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hS : Nat.card S = 120 := by
    rw [Nat.card_congr eS.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  let f : D × S → centralizer ({τ} : Set X) := fun p =>
    ⟨p.1.1 * p.2.1, by
      rw [mem_centralizer_singleton_iff]
      exact (h.cent _).2 ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨d₁, hd₁⟩, ⟨s₁, hs₁⟩⟩ ⟨⟨d₂, hd₂⟩, ⟨s₂, hs₂⟩⟩ he
      have he' : d₁ * s₁ = d₂ * s₂ := congrArg Subtype.val he
      have h1 : d₂⁻¹ * d₁ = s₂ * s₁⁻¹ := by
        have : d₁ = d₂ * (s₂ * s₁⁻¹) := by
          calc d₁ = d₁ * s₁ * s₁⁻¹ := by group
            _ = d₂ * s₂ * s₁⁻¹ := by rw [he']
            _ = d₂ * (s₂ * s₁⁻¹) := by group
        rw [this]; group
      have h2 : d₂⁻¹ * d₁ = 1 := h.inf _ (mul_mem (inv_mem hd₂) hd₁)
        (by rw [h1]; exact mul_mem hs₂ (inv_mem hs₁))
      have hd : d₁ = d₂ := by
        have := mul_eq_one_iff_eq_inv.1 h2
        simpa using this.symm
      have hs : s₁ = s₂ := by
        rw [hd] at he'
        exact mul_left_cancel he'
      subst hd; subst hs; rfl
    · rintro ⟨x, hx⟩
      obtain ⟨d, hd, s, hs, rfl⟩ := (h.cent x).1 (mem_centralizer_singleton_iff.1 hx)
      exact ⟨(⟨d, hd⟩, ⟨s, hs⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, hD, hS]

end LocalPairFacts

section Stage

theorem PGStage1.len (hc : PGStage1) : pgP0List.length = 128 := hc.1
theorem PGStage1.nodup (hc : PGStage1) : pgP0List.Nodup := hc.2.1
theorem PGStage1.so (hc : PGStage1) : ∀ A ∈ pgP0List, IsSO5 A := hc.2.2.1
theorem PGStage1.one_mem (hc : PGStage1) : (1 : SoMat5) ∈ pgP0List := hc.2.2.2.1
theorem PGStage1.mul_mem (hc : PGStage1) : ∀ A ∈ pgP0List, ∀ B ∈ pgP0List, A * B ∈ pgP0List :=
  hc.2.2.2.2.1
theorem PGStage1.inv_mem (hc : PGStage1) : ∀ A ∈ pgP0List, ∃ B ∈ pgP0List, A * B = 1 :=
  hc.2.2.2.2.2.1
theorem PGStage1.reps (hc : PGStage1) :
    ∀ i : Fin 4, IsSO5 (pgReps i) ∧ pgReps i * pgReps i = 1 := hc.2.2.2.2.2.2.1
theorem PGStage1.invols (hc : PGStage1) :
    ∀ A ∈ pgP0List, A * A = 1 → A = 1 ∨ ∃ e ∈ pgConjTable, e.1 = A := hc.2.2.2.2.2.2.2.1
theorem PGStage1.table (hc : PGStage1) : ∀ e ∈ pgConjTable, e.1 ∈ pgP0List ∧ IsSO5 e.2.1 ∧
    e.2.1 * e.1 = pgReps e.2.2 * e.2.1 := hc.2.2.2.2.2.2.2.2.1
theorem PGStage1.tau3 (hc : PGStage1) : ∀ A ∈ pgP0List, A * pgTau3 = pgTau3 * A :=
  hc.2.2.2.2.2.2.2.2.2.1
theorem PGStage1.x15 (hc : PGStage1) : IsSO5 pgX15 ∧ pgX15 * pgTau2 = pgTau2 * pgX15 ∧
    pgX15 ^ 15 = 1 ∧ pgX15 ^ 3 ≠ 1 ∧ pgX15 ^ 5 ≠ 1 := hc.2.2.2.2.2.2.2.2.2.2.1
theorem PGStage1.x13 (hc : PGStage1) : IsSO5 pgX13 ∧ pgX13 * pgTau4 = pgTau4 * pgX13 ∧
    pgX13 ^ 13 = 1 ∧ pgX13 ≠ 1 := hc.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGStage1.f2 (hc : PGStage1) : ∀ k ∈ ([1, 3] : List ℕ), ∀ j ∈ ([0, 1] : List ℕ),
    IsSO5 (pgF2 k j) ∧ pgF2 k j * pgTau1 =
      (pgRefl k * (if j = 0 then pgS1 else pgTau1 * pgS1)) * pgF2 k j :=
  hc.2.2.2.2.2.2.2.2.2.2.2.2

theorem pg_inv_mul_val (x : PGSp45) : (x⁻¹).1.1 * x.1.1 = 1 := by
  simp

def pgP0 (hc : PGStage1) : Subgroup PGSp45 where
  carrier := {x | x.1.1 ∈ pgP0List}
  mul_mem' := by
    intro x y hx hy
    have := hc.mul_mem _ hx _ hy
    rwa [← pg_mul_val] at this
  one_mem' := by
    show (1 : PGSp45).1.1 ∈ pgP0List
    rw [pg_one_val]
    exact hc.one_mem
  inv_mem' := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := hc.inv_mem _ hx
    show (x⁻¹).1.1 ∈ pgP0List
    have : (x⁻¹).1.1 = B := by
      calc (x⁻¹).1.1 = (x⁻¹).1.1 * (x.1.1 * B) := by rw [hxB, Matrix.mul_one]
        _ = ((x⁻¹).1.1 * x.1.1) * B := by rw [Matrix.mul_assoc]
        _ = B := by rw [pg_inv_mul_val, Matrix.one_mul]
    rw [this]
    exact hB

theorem mem_pgP0 (hc : PGStage1) {x : PGSp45} : x ∈ pgP0 hc ↔ x.1.1 ∈ pgP0List := Iff.rfl

theorem card_pgP0 (hc : PGStage1) : Nat.card (pgP0 hc) = 128 := by
  let e : pgP0 hc ≃ {A : SoMat5 // A ∈ pgP0List} :=
    { toFun := fun x => ⟨x.1.1.1, x.2⟩
      invFun := fun A => ⟨mkPG A.1 (hc.so A.1 A.2), by rw [mem_pgP0, mkPG_val]; exact A.2⟩
      left_inv := fun x => Subtype.ext (pg_ext (by simp))
      right_inv := fun A => Subtype.ext (by simp) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun A : SoMat5 => A ∈ pgP0List) = pgP0List.toFinset := by
    ext A; simp
  rw [this, List.toFinset_card_of_nodup hc.nodup, hc.len]

theorem isPGroup_two_zpowers_of_sq {G : Type*} [Group G] {t : G} (h : t * t = 1) :
    IsPGroup 2 (zpowers t) := by
  intro g
  obtain ⟨k, hk⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : G) ^ (2 ^ 1) = 1
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_one, pow_two, h,
    one_zpow]

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {P : Subgroup G} (SP : Sylow 2 G)
    (hSP : (SP : Subgroup G) = P) {t : G} (ht : t * t = 1) : ∃ g : G, g⁻¹ * t * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_sq ht)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SP Q
  have htQ : t ∈ (Q : Subgroup G) := hQ (mem_zpowers t)
  rw [← hg] at htQ
  refine ⟨g, ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ
  obtain ⟨y, hy, rfl⟩ := htQ
  rw [hSP] at hy
  have e : g⁻¹ * (MulAut.conj g • y) * g = y := by
    simp [MulAut.smul_def, MulAut.conj_apply]; group
  rw [e]
  exact hy

theorem conj_eq_of_mat {g t u : PGSp45} (h : g.1.1 * t.1.1 = u.1.1 * g.1.1) :
    g * t * g⁻¹ = u := by
  rw [mul_inv_eq_iff_eq_mul]
  exact pg_ext (by simpa using h)

theorem pg_eq_one_iff {x : PGSp45} : x = 1 ↔ x.1.1 = 1 :=
  ⟨fun h => by rw [h, pg_one_val], fun h => pg_ext (by rw [h, pg_one_val])⟩

theorem pg_pow_val (x : PGSp45) (n : ℕ) : (x ^ n).1.1 = x.1.1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pg_mul_val, ih, pow_succ]

def pgRep (hc : PGStage1) (i : Fin 4) : PGSp45 := mkPG (pgReps i) (hc.reps i).1

theorem exists_conj_rep (hc : PGStage1)
    (hsyl : Nat.card (pgP0 hc) = 2 ^ (Nat.card PGSp45).factorization 2)
    {t : PGSp45} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ (g : PGSp45) (i : Fin 4), g * t * g⁻¹ = pgRep hc i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g0, hg0⟩ := exists_conj_mem_sylow (Sylow.ofCard (pgP0 hc) hsyl) rfl ht
  set t' := g0⁻¹ * t * g0 with ht'
  have ht'1 : t' * t' = 1 := by
    rw [ht']
    calc g0⁻¹ * t * g0 * (g0⁻¹ * t * g0) = g0⁻¹ * (t * t) * g0 := by group
      _ = 1 := by rw [ht]; group
  have ht'ne : t' ≠ 1 := by
    intro h1
    apply ht1
    have : t = g0 * t' * g0⁻¹ := by rw [ht']; group
    rw [this, h1]; group
  have hA : t'.1.1 ∈ pgP0List := hg0
  have hAA : t'.1.1 * t'.1.1 = 1 := by
    rw [← pg_mul_val, ht'1, pg_one_val]
  rcases hc.invols _ hA hAA with h1 | ⟨e, he, he1⟩
  · exact absurd (pg_ext (by rw [h1, pg_one_val])) ht'ne
  · obtain ⟨-, hso, hmat⟩ := hc.table e he
    set h := mkPG e.2.1 hso with hh
    have hconj : h * t' * h⁻¹ = pgRep hc e.2.2 := by
      apply conj_eq_of_mat
      have h2 := hmat
      rw [he1] at h2
      exact h2
    refine ⟨h * g0⁻¹, e.2.2, ?_⟩
    rw [← hconj, ht']
    group

theorem conj_inv_pow {G : Type*} [Group G] (g z : G) (n : ℕ) :
    (g⁻¹ * z * g) ^ n = g⁻¹ * z ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := z) (i := n)

theorem card_centralizer_map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) :
    Nat.card (centralizer ({φ x} : Set Y)) = Nat.card (centralizer ({x} : Set X)) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun z : centralizer ({x} : Set X) =>
      (⟨φ z.1, ?_⟩ : centralizer ({φ x} : Set Y))) ⟨?_, ?_⟩)).symm
  · have := mem_centralizer_singleton_iff.1 z.2
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
  · intro a b hab
    exact Subtype.ext (φ.injective (congrArg Subtype.val hab))
  · rintro ⟨y, hy⟩
    refine ⟨⟨φ.symm y, ?_⟩, Subtype.ext (by simp)⟩
    have := mem_centralizer_singleton_iff.1 hy
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact this

variable {X : Type} [Group X] {τ : X} {D S : Subgroup X}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Equiv.Perm (Fin 5)}

theorem LocalPair.card_dvd_false [Finite X] (h : LocalPair τ D S eD eS) (φ : X ≃* PGSp45)
    {t' : PGSp45} (ht' : t' = φ τ) (H : Subgroup PGSp45) (hH : Nat.card H = 128)
    (hle : H ≤ centralizer ({t'} : Set PGSp45)) : False := by
  have h1 := Subgroup.card_dvd_of_le hle
  rw [hH, ht', card_centralizer_map φ τ, h.card_cent] at h1
  omega

theorem tau_conj_tau1 (hc : PGStage1) [Finite X] (φ : X ≃* PGSp45)
    (hsyl : Nat.card (pgP0 hc) = 2 ^ (Nat.card PGSp45).factorization 2)
    (h : LocalPair τ D S eD eS) :
    ∃ g : PGSp45, g * φ τ * g⁻¹ = mkPG pgTau1 pgTau1_so := by
  have hτ2 : φ τ * φ τ = 1 := by rw [← map_mul, h.tau_sq, map_one]
  have hτ1 : φ τ ≠ 1 := by
    intro h1
    obtain ⟨hτD, hτe⟩ := h.tau_mem
    have : τ = 1 := φ.injective (by rw [h1, map_one])
    have h2 : (⟨τ, hτD⟩ : D) = 1 := Subtype.ext this
    rw [h2, map_one] at hτe
    exact absurd hτe (by decide)
  obtain ⟨g, i, hgi⟩ := exists_conj_rep hc hsyl hτ2 hτ1
  have key : ∀ {z : PGSp45}, z * pgRep hc i = pgRep hc i * z →
      (φ.symm (g⁻¹ * z * g)) * τ = τ * φ.symm (g⁻¹ * z * g) := by
    intro z hz
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    rw [← hgi] at hz
    calc g⁻¹ * z * g * φ τ = g⁻¹ * (z * (g * φ τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * φ τ * g⁻¹) * z) * g := by rw [hz]
      _ = φ τ * (g⁻¹ * z * g) := by group
  have hpow : ∀ (A : SoMat5) (hA : IsSO5 A) (n : ℕ),
      (φ.symm (g⁻¹ * mkPG A hA * g)) ^ n = 1 ↔ A ^ n = 1 := by
    intro A hA n
    rw [← map_pow, conj_inv_pow, map_eq_one_iff _ φ.symm.injective,
      show g⁻¹ * mkPG A hA ^ n * g = g⁻¹ * mkPG A hA ^ n * (g⁻¹)⁻¹ by rw [inv_inv],
      conj_eq_one_iff, pg_eq_one_iff, pg_pow_val, mkPG_val]
  have hone : ∀ (A : SoMat5) (hA : IsSO5 A), φ.symm (g⁻¹ * mkPG A hA * g) = 1 ↔ A = 1 := by
    intro A hA
    simpa using hpow A hA 1
  refine ⟨g, ?_⟩
  fin_cases i
  ·
    rw [hgi]
    exact pg_ext rfl
  ·
    exfalso
    obtain ⟨hso, hcomm, h15, h3, h5⟩ := hc.x15
    have hxc : mkPG pgX15 hso * pgRep hc 1 = pgRep hc 1 * mkPG pgX15 hso := by
      apply pg_ext
      exact hcomm
    refine h.false_of_order_fifteen (key hxc) ((hpow _ hso 15).2 h15) ?_ ?_
    · intro h3'
      rw [hpow _ hso 3] at h3'
      exact h3 h3'
    · intro h5'
      rw [hpow _ hso 5] at h5'
      exact h5 h5'
  ·
    exfalso
    let H : Subgroup PGSp45 := (pgP0 hc).map (MulAut.conj g⁻¹).toMonoidHom
    have hH : Nat.card H = 128 := by
      rw [show Nat.card H = Nat.card (pgP0 hc) from
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_pgP0]
    refine h.card_dvd_false φ rfl H hH ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hpc : p * pgRep hc 2 = pgRep hc 2 * p := by
      apply pg_ext
      exact hc.tau3 _ hp
    change g * φ τ * g⁻¹ = pgRep hc 2 at hgi
    rw [← hgi] at hpc
    show g⁻¹ * p * g⁻¹⁻¹ * φ τ = φ τ * (g⁻¹ * p * g⁻¹⁻¹)
    calc g⁻¹ * p * g⁻¹⁻¹ * φ τ = g⁻¹ * (p * (g * φ τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * φ τ * g⁻¹) * p) * g := by rw [hpc]
      _ = φ τ * (g⁻¹ * p * g⁻¹⁻¹) := by group
  ·
    exfalso
    obtain ⟨hso, hcomm, h13, hne⟩ := hc.x13
    have hxc : mkPG pgX13 hso * pgRep hc 3 = pgRep hc 3 * mkPG pgX13 hso := by
      apply pg_ext
      exact hcomm
    refine h.false_of_order_thirteen (key hxc) ((hpow _ hso 13).2 h13) ?_
    · intro h1
      rw [hone] at h1
      exact hne h1

end Stage

end CFSG.EvenSporadicStandard.TwoHS
