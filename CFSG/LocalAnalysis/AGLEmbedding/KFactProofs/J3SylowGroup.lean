module

public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Sylow

open CFSG.Quasithin

@[expose] def evalW {X : Type*} [Group X] (t₁ t₂ : X) (w : List Bool) : X :=
  (w.map fun b => if b then t₂ else t₁).prod

@[expose] def cnt (b : Bool) (w : List Bool) : ZMod 3 := (w.count b : ZMod 3)

theorem map_evalW {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (t₁ t₂ : X) (w : List Bool) :
    f (evalW t₁ t₂ w) = evalW (f t₁) (f t₂) w := by
  induction w with
  | nil => simp [evalW]
  | cons b w ih => cases b <;> simp_all [evalW]

theorem toAdd_evalW (x y : Multiplicative (ZMod 3)) (w : List Bool) :
    (evalW x y w).toAdd = cnt false w * x.toAdd + cnt true w * y.toAdd := by
  induction w with
  | nil => simp [evalW, cnt]
  | cons b w ih =>
    simp only [evalW, cnt, List.map_cons, List.prod_cons, toAdd_mul, List.count_cons] at ih ⊢
    rw [ih]
    cases b <;> simp <;> ring

@[expose] def NoEigen (a b c d : ZMod 3) : Prop :=
  ∀ e₁ e₂ : ZMod 3, (e₁ ≠ 0 ∨ e₂ ≠ 0) → ∃ m n : ZMod 3,
    ¬ ((m * e₁ + n * e₂ = 0) ↔ (m * (a * e₁ + b * e₂) + n * (c * e₁ + d * e₂) = 0))

instance (a b c d : ZMod 3) : Decidable (NoEigen a b c d) := by
  unfold NoEigen; infer_instance

section General

variable {X : Type*} [Group X]

theorem mem_centerOf {K : Subgroup X} {x : X} :
    x ∈ centerOf K ↔ x ∈ K ∧ ∀ y ∈ K, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem centerOf_le (K : Subgroup X) : centerOf K ≤ K := fun _ hx => (mem_centerOf.1 hx).1

theorem le_centralizer_centerOf (K : Subgroup X) :
    K ≤ Subgroup.centralizer (centerOf K : Set X) :=
  fun p hp => Subgroup.mem_centralizer_iff.2 fun _ hz => ((mem_centerOf.1 hz).2 p hp).symm

theorem normalizer_eq_of_le [IsSimpleGroup X] {H K : Subgroup X} (hH : IsCoatom H)
    (hKH : K ≤ H) (hK : K ≠ ⊥) (hle : H ≤ Subgroup.normalizer (K : Set X)) :
    Subgroup.normalizer (K : Set X) = H := by
  rcases hH.le_iff.mp hle with h | h
  · have : K.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h' | h'
    · exact absurd h' hK
    · exact absurd (top_le_iff.mp (h' ▸ hKH)) hH.1
  · exact h

end General

structure LocalData {X : Type} [Group X] (H : Subgroup X) (t₁ t₂ s : X) (Z : Fin 9 → X)
    (w₁ w₂ : List Bool) : Prop where
  t₁_mem : t₁ ∈ H
  t₂_mem : t₂ ∈ H
  s_mem : s ∈ H
  card_H : Nat.card H = 1944
  card_P : Nat.card (Subgroup.closure ({t₁, t₂} : Set X)) = 243
  conj₁ : s * t₁ * s⁻¹ ∈ Subgroup.closure ({t₁, t₂} : Set X)
  conj₂ : s * t₂ * s⁻¹ ∈ Subgroup.closure ({t₁, t₂} : Set X)
  s_pow_eight : s ^ 8 = 1
  s_pow_four : s ^ 4 ≠ 1
  noncomm : t₁ * t₂ ≠ t₂ * t₁
  Z_mem : ∀ g, g ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)) ↔ ∃ i, g = Z i
  Z_inj : Function.Injective Z
  Z_cube : ∀ i, Z i ^ 3 = 1
  Z_conj : ∀ i, ∃ j, s * Z i * s⁻¹ = Z j
  Z_irred : ∀ i, Z i ≠ 1 →
    s * Z i * s⁻¹ ≠ 1 ∧ s * Z i * s⁻¹ ≠ Z i ∧ s * Z i * s⁻¹ ≠ Z i ^ 2
  Z_cent : ∀ k : ℕ, 0 < k → k < 8 → ∃ i, s ^ k * Z i ≠ Z i * s ^ k
  w₁_eq : s ^ 2 * t₁ * (s ^ 2)⁻¹ = evalW t₁ t₂ w₁
  w₂_eq : s ^ 2 * t₂ * (s ^ 2)⁻¹ = evalW t₁ t₂ w₂
  sing : NoEigen (cnt false w₁) (cnt true w₁) (cnt false w₂) (cnt true w₂)

namespace LocalData

variable {X : Type} [Group X] {H : Subgroup X} {t₁ t₂ s : X} {Z : Fin 9 → X}
  {w₁ w₂ : List Bool}

theorem closure_le (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    Subgroup.closure ({t₁, t₂} : Set X) ≤ H := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact D.t₁_mem
  · exact D.t₂_mem

theorem conj_mem (D : LocalData H t₁ t₂ s Z w₁ w₂) {x : X}
    (hx : x ∈ Subgroup.closure ({t₁, t₂} : Set X)) :
    s * x * s⁻¹ ∈ Subgroup.closure ({t₁, t₂} : Set X) := by
  have h : Subgroup.closure ({t₁, t₂} : Set X) ≤
      (Subgroup.closure ({t₁, t₂} : Set X)).comap (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · simpa using D.conj₁
    · simpa using D.conj₂
  simpa using h hx

theorem mem_normalizer [Finite X] (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    s ∈ Subgroup.normalizer (Subgroup.closure ({t₁, t₂} : Set X) : Set X) :=
  Subgroup.mem_normalizer_fintype fun _ hx => D.conj_mem hx

theorem orderOf_s (D : LocalData H t₁ t₂ s Z w₁ w₂) : orderOf s = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := s) (by norm_num [D.s_pow_four])
    (by norm_num [D.s_pow_eight])
  simpa using h

theorem pow_not_mem (D : LocalData H t₁ t₂ s Z w₁ w₂) {j : ℕ} (hj0 : 0 < j) (hj8 : j < 8) :
    s ^ j ∉ Subgroup.closure ({t₁, t₂} : Set X) := by
  intro hmem
  have h1 : orderOf (s ^ j) ∣ 243 := by
    have := orderOf_dvd_natCard (⟨s ^ j, hmem⟩ : Subgroup.closure ({t₁, t₂} : Set X))
    rwa [Subgroup.orderOf_mk, D.card_P] at this
  have h2 : orderOf (s ^ j) ∣ 8 := orderOf_dvd_of_pow_eq_one (by
    rw [← pow_mul, mul_comm, pow_mul, D.s_pow_eight, one_pow])
  have h3 : orderOf (s ^ j) = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  have h4 : 8 ∣ j := D.orderOf_s ▸ orderOf_dvd_of_pow_eq_one h3
  omega

theorem eq_of_pow_mul (D : LocalData H t₁ t₂ s Z w₁ w₂) {i j : ℕ} (hi : i < 8) (hj : j < 8)
    {p q : X} (hp : p ∈ Subgroup.closure ({t₁, t₂} : Set X))
    (hq : q ∈ Subgroup.closure ({t₁, t₂} : Set X)) (h : s ^ i * p = s ^ j * q) :
    i = j ∧ p = q := by
  wlog hij : i ≤ j generalizing i j p q
  · obtain ⟨h1, h2⟩ := this hj hi hq hp h.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add, mul_assoc] at h
  have h' : p = s ^ d * q := mul_left_cancel h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using h'
  · refine absurd ?_ (D.pow_not_mem hd (by omega))
    have : s ^ d = p * q⁻¹ := by rw [h']; group
    rw [this]
    exact mul_mem hp (inv_mem hq)

theorem decomp [Finite X] (D : LocalData H t₁ t₂ s Z w₁ w₂) {y : X} (hy : y ∈ H) :
    ∃ k < 8, ∃ p ∈ Subgroup.closure ({t₁, t₂} : Set X), y = s ^ k * p := by
  let φ : Fin 8 × Subgroup.closure ({t₁, t₂} : Set X) → H := fun x =>
    ⟨s ^ (x.1 : ℕ) * x.2, H.mul_mem (H.pow_mem D.s_mem _) (D.closure_le x.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨i, p⟩ ⟨j, q⟩ h
    obtain ⟨h1, h2⟩ := D.eq_of_pow_mul i.2 j.2 p.2 q.2 (congrArg Subtype.val h)
    exact Prod.ext (Fin.ext h1) (Subtype.ext h2)
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, D.card_H, D.card_P, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨⟨k, p⟩, hk⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨k, k.2, p, p.2, (congrArg Subtype.val hk).symm⟩

theorem le_of_mem [Finite X] (D : LocalData H t₁ t₂ s Z w₁ w₂) {K : Subgroup X}
    (hP : Subgroup.closure ({t₁, t₂} : Set X) ≤ K) (hs : s ∈ K) : H ≤ K := by
  intro y hy
  obtain ⟨k, -, p, hp, rfl⟩ := D.decomp hy
  exact K.mul_mem (K.pow_mem hs k) (hP hp)

theorem normalizer_eq [Finite X] [IsSimpleGroup X] (hH : IsCoatom H)
    (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    Subgroup.normalizer (Subgroup.closure ({t₁, t₂} : Set X) : Set X) = H := by
  refine normalizer_eq_of_le hH D.closure_le (fun h => ?_)
    (D.le_of_mem Subgroup.le_normalizer D.mem_normalizer)
  have := D.card_P
  rw [h, Subgroup.card_bot] at this
  omega

theorem card_center (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    Nat.card (centerOf (Subgroup.closure ({t₁, t₂} : Set X))) = 9 := by
  have hbij : Function.Bijective (fun i : Fin 9 =>
      (⟨Z i, (D.Z_mem _).2 ⟨i, rfl⟩⟩ : centerOf (Subgroup.closure ({t₁, t₂} : Set X)))) := by
    refine ⟨fun i j h => D.Z_inj (congrArg Subtype.val h), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := (D.Z_mem g).1 hg
    exact ⟨i, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem center_elem (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    CFSG.Open.IsElemAbelian 3 (centerOf (Subgroup.closure ({t₁, t₂} : Set X))) ∧
      Nat.card (centerOf (Subgroup.closure ({t₁, t₂} : Set X))) = 9 := by
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, D.card_center⟩
  · exact (mem_centerOf.1 b.2).2 a (mem_centerOf.1 a.2).1
  · obtain ⟨i, rfl⟩ := (D.Z_mem x).1 hx
    exact D.Z_cube i

theorem mem_normalizer_center [Finite X] (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    s ∈ Subgroup.normalizer (centerOf (Subgroup.closure ({t₁, t₂} : Set X)) : Set X) :=
  Subgroup.mem_normalizer_fintype fun x hx => by
    obtain ⟨i, rfl⟩ := (D.Z_mem x).1 hx
    obtain ⟨j, hj⟩ := D.Z_conj i
    exact (D.Z_mem _).2 ⟨j, hj⟩

theorem normalizer_center_eq [Finite X] [IsSimpleGroup X] (hH : IsCoatom H)
    (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    Subgroup.normalizer (centerOf (Subgroup.closure ({t₁, t₂} : Set X)) : Set X) = H := by
  refine normalizer_eq_of_le hH ((centerOf_le _).trans D.closure_le) (fun h => ?_)
    (D.le_of_mem ((le_centralizer_centerOf _).trans (Subgroup.centralizer_le_normalizer _))
      D.mem_normalizer_center)
  have := D.card_center
  rw [h, Subgroup.card_bot] at this
  omega

theorem centralizer_center_le [Finite X] [IsSimpleGroup X] (hH : IsCoatom H)
    (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    Subgroup.centralizer (centerOf (Subgroup.closure ({t₁, t₂} : Set X)) : Set X) ≤
      Subgroup.closure ({t₁, t₂} : Set X) := by
  intro y hy
  have hyH : y ∈ H := D.normalizer_center_eq hH ▸ Subgroup.centralizer_le_normalizer _ hy
  obtain ⟨k, hk, p, hp, rfl⟩ := D.decomp hyH
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hp
  · obtain ⟨i, hi⟩ := D.Z_cent k hk0 hk
    have hZi : Z i ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)) := (D.Z_mem _).2 ⟨i, rfl⟩
    have h1 : Z i * (s ^ k * p) = s ^ k * p * Z i := Subgroup.mem_centralizer_iff.1 hy _ hZi
    have h2 : p * Z i = Z i * p := (mem_centerOf.1 hZi).2 p hp
    refine absurd (mul_right_cancel (b := p) ?_) hi
    rw [mul_assoc, ← h2, ← mul_assoc, ← h1, ← mul_assoc]

theorem center_irreducible [Finite X] (D : LocalData H t₁ t₂ s Z w₁ w₂) (W : Subgroup X)
    (hW : W ≤ centerOf (Subgroup.closure ({t₁, t₂} : Set X)))
    (hN : Subgroup.normalizer (Subgroup.closure ({t₁, t₂} : Set X) : Set X) ≤
      Subgroup.normalizer (W : Set X)) :
    W = ⊥ ∨ W = centerOf (Subgroup.closure ({t₁, t₂} : Set X)) := by
  have hdvd : Nat.card W ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hW
    rwa [D.card_center] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases k
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ (by simpa using hk'))
  · exfalso
    obtain ⟨w, hwW, hw1⟩ := W.bot_or_exists_ne_one.resolve_left fun h => by
      rw [h, Subgroup.card_bot] at hk'
      norm_num at hk'
    obtain ⟨i, rfl⟩ := (D.Z_mem w).1 (hW hwW)
    have ho : orderOf (Z i) = 3 := orderOf_eq_prime (D.Z_cube i) hw1
    have hWz : Subgroup.zpowers (Z i) = W := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.2 hwW) (by rw [Nat.card_zpowers, ho, hk', pow_one])
    have hmem : s * Z i * s⁻¹ ∈ Subgroup.zpowers (Z i) := by
      rw [hWz]
      exact (Subgroup.mem_normalizer_iff.1 (hN D.mem_normalizer) _).1 hwW
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← zpow_mod_orderOf, ho] at hn
    obtain ⟨h1, h2, h3⟩ := D.Z_irred i hw1
    have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3' : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize n % ((3 : ℕ) : ℤ) = r at hn h0 h3'
    interval_cases r
    · exact h1 (by simpa using hn.symm)
    · exact h2 (by simpa using hn.symm)
    · exact h3 (by simpa using hn.symm)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hW (by rw [D.card_center, hk']; norm_num))

theorem two_top [Finite X] [IsSimpleGroup X] (hH : IsCoatom H)
    (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    ∀ y ∈ Subgroup.normalizer (Subgroup.closure ({t₁, t₂} : Set X) : Set X),
      ∃ e : ℕ, y ^ 2 ^ e ∈ Subgroup.closure ({t₁, t₂} : Set X) := by
  intro y hy
  rw [D.normalizer_eq hH] at hy
  have : ((Subgroup.closure ({t₁, t₂} : Set X)).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer D.closure_le).2 (D.normalizer_eq hH).ge
  have hidx : ((Subgroup.closure ({t₁, t₂} : Set X)).subgroupOf H).index = 8 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.closure ({t₁, t₂} : Set X)).subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.closure_le).toEquiv, D.card_P,
      D.card_H] at h1
    omega
  have h := Subgroup.pow_index_mem ((Subgroup.closure ({t₁, t₂} : Set X)).subgroupOf H) ⟨y, hy⟩
  rw [hidx, Subgroup.mem_subgroupOf] at h
  exact ⟨3, by simpa using h⟩

theorem sq_not_mem_normalizer (D : LocalData H t₁ t₂ s Z w₁ w₂) {W : Subgroup X}
    (hW : W.relIndex (Subgroup.closure ({t₁, t₂} : Set X)) = 3) :
    s ^ 2 ∉ Subgroup.normalizer (W : Set X) := by
  intro hsW
  set P := Subgroup.closure ({t₁, t₂} : Set X)
  have hidx : (W.subgroupOf P).index = 3 := hW
  have : (W.subgroupOf P).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, D.card_P]; norm_num)
  let e : (P ⧸ W.subgroupOf P) ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hidx (by simp)
  let χ : P →* Multiplicative (ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hχ : ∀ g : P, χ g = 1 ↔ (g : X) ∈ W := fun g => by
    simp [χ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let a : P := ⟨t₁, Subgroup.subset_closure (by simp)⟩
  let b : P := ⟨t₂, Subgroup.subset_closure (by simp)⟩
  have hχ' : ∀ g : P, (χ g).toAdd = 0 ↔ (g : X) ∈ W := fun g => toAdd_eq_zero.trans (hχ g)
  have hne : (χ a).toAdd ≠ 0 ∨ (χ b).toAdd ≠ 0 := by
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.1 hcon
    have ha : t₁ ∈ W := (hχ' a).1 (not_not.1 h1)
    have hb : t₂ ∈ W := (hχ' b).1 (not_not.1 h2)
    have hle : P ≤ W := (Subgroup.closure_le W).2 (by rintro x (rfl | rfl) <;> assumption)
    rw [Subgroup.relIndex_eq_one.2 hle] at hW
    norm_num at hW
  have key : ∀ m n : ℕ, ((m : ZMod 3) * (χ a).toAdd + n * (χ b).toAdd = 0 ↔
      (m : ZMod 3) * (cnt false w₁ * (χ a).toAdd + cnt true w₁ * (χ b).toAdd) +
        n * (cnt false w₂ * (χ a).toAdd + cnt true w₂ * (χ b).toAdd) = 0) := by
    intro m n
    have hev : ∀ w : List Bool, evalW t₁ t₂ w = ((evalW a b w : P) : X) := fun w =>
      (map_evalW P.subtype a b w).symm
    have hg := Subgroup.mem_normalizer_iff.1 hsW (t₁ ^ m * t₂ ^ n)
    have hw1 := D.w₁_eq
    have hw2 := D.w₂_eq
    generalize s ^ 2 = σ at hg hw1 hw2
    have e1 : σ * (t₁ ^ m * t₂ ^ n) * σ⁻¹ =
        ((evalW a b w₁ ^ m * evalW a b w₂ ^ n : P) : X) := by
      have hc : ∀ x : X, σ * x * σ⁻¹ = MulAut.conj σ x := fun _ => rfl
      rw [hc, map_mul, map_pow, map_pow, ← hc, ← hc, hw1, hw2, hev, hev]
      simp
    have e0 : t₁ ^ m * t₂ ^ n = ((a ^ m * b ^ n : P) : X) := by simp [a, b]
    rw [e1, e0, ← hχ', ← hχ'] at hg
    simpa only [map_mul, map_pow, toAdd_mul, toAdd_pow, map_evalW χ, toAdd_evalW,
      nsmul_eq_mul] using hg
  obtain ⟨m, n, hmn⟩ := D.sing _ _ hne
  have := key m.val n.val
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  exact hmn this

end LocalData

theorem LocalData.facts {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {H : Subgroup X}
    (hH : IsCoatom H) {t₁ t₂ s : X} {Z : Fin 9 → X} {w₁ w₂ : List Bool}
    (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    J3SylowFacts X (Subgroup.closure ({t₁, t₂} : Set X)) where
  maximal Y₀ hY := by
    rw [D.normalizer_eq hH] at hY ⊢
    exact (hH.le_iff.1 hY).symm
  centralizer_center := D.centralizer_center_le hH
  center_irreducible := D.center_irreducible
  center_elem := D.center_elem
  nonabelian := ⟨t₁, Subgroup.subset_closure (by simp), t₂, Subgroup.subset_closure (by simp),
    D.noncomm⟩
  singer := ⟨s, D.mem_normalizer,
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, D.orderOf_s]; norm_num),
    fun _ _ hW => D.sq_not_mem_normalizer hW⟩
  two_top := D.two_top hH

end CFSG.AGLEmbedding.KFactProofs.J3Sylow
