module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.KC.G2Three.Sec1

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Matrix

variable {G : Type} [Group G]

@[expose] def vecE (f : Fin 3 → G) (v : Fin 3 → ZMod 2) : G :=
  f 0 ^ (v 0).val * f 1 ^ (v 1).val * f 2 ^ (v 2).val

theorem closure_le_normalizer [Finite G] {S T : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ closure T) :
    closure S ≤ normalizer (closure T : Set G) := by
  rw [closure_le]
  intro s hs
  let f := (MulAut.conj s).toMonoidHom
  have hle : (closure T).map f ≤ closure T := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact h s hs t ht
  have heq : (closure T).map f = closure T :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj s).injective).symm)
  rw [SetLike.mem_coe, mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← heq]
    exact mem_map.2 ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨y', hy', e⟩ := mem_map.1 hy
    have : y' = y := by
      simp only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      exact mul_left_cancel (mul_right_cancel e)
    rwa [← this]

theorem closure_comm {S : Set G} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
  have h1 : closure S ≤ centralizer S :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb => hc b hb a ha
  have h2 : closure S ≤ centralizer (closure S : Set G) :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb =>
      (mem_centralizer_iff.1 (h1 hb) a ha).symm
  intro x hx y hy
  exact mem_centralizer_iff.1 (h2 hy) x hx

theorem closure_sq {S : Set G} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a * a = 1) : ∀ x ∈ closure S, x ^ 2 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => rw [sq]; exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (closure_comm hc x hx y hy) 2), ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem isElemAbelian_closure {S : Set G} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a * a = 1) : IsElemAbelian 2 (closure S) :=
  ⟨⟨⟨fun u v => Subtype.ext (closure_comm hc _ u.2 _ v.2)⟩⟩, closure_sq hc hs⟩

theorem isE_closure {S : Set G} {n : ℕ} (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hs : ∀ a ∈ S, a * a = 1) (hn : Nat.card (closure S) = 2 ^ n) : IsE n ↥(closure S) := by
  refine ⟨⟨⟨⟨fun u v => Subtype.ext (Subtype.ext (closure_comm hc _ u.1.2 _ v.1.2))⟩⟩,
    fun x _ => ?_⟩, hn⟩
  apply Subtype.ext
  simpa using closure_sq hc hs _ x.2

theorem conjSub_eq_self {H : Subgroup G} {x : G} (hx : x ∈ normalizer (H : Set G)) :
    conjSub x H = H := by
  ext y
  simp only [conjSub, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_normalizer_iff.1 hx h).1 hh
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    rw [mem_normalizer_iff.1 hx]
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e]

theorem conjSub_mul' (a b : G) (H : Subgroup G) :
    conjSub (a * b) H = conjSub a (conjSub b H) := by
  ext y
  simp only [conjSub, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨b * h * b⁻¹, ⟨h, hh, rfl⟩, by group⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, by group⟩

theorem card_mul_card_normIn_le [Finite G] {T H : Subgroup G} {k : ℕ} (c : Fin k → G)
    (hc : ∀ i, c i ∈ T) (hd : ∀ i j, conjSub (c i) H = conjSub (c j) H → i = j) :
    k * Nat.card (normIn T H) ≤ Nat.card T := by
  have hNT : normIn T H ≤ T := inf_le_left
  let N := (normIn T H).subgroupOf T
  have hinj : Function.Injective
      (fun i : Fin k => (QuotientGroup.mk (⟨c i, hc i⟩ : T) : T ⧸ N)) := by
    intro i j hij
    have h1 := QuotientGroup.eq.1 hij
    rw [mem_subgroupOf] at h1
    have hn : (c i)⁻¹ * c j ∈ normalizer (H : Set G) := h1.2
    apply hd
    calc conjSub (c i) H = conjSub (c i) (conjSub ((c i)⁻¹ * c j) H) := by
          rw [conjSub_eq_self hn]
      _ = conjSub (c j) H := by rw [← conjSub_mul', mul_inv_cancel_left]
  have hk : k ≤ N.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index_eq_card] at this
  have hcN : Nat.card N = Nat.card (normIn T H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  calc k * Nat.card (normIn T H) ≤ N.index * Nat.card N := by
        rw [hcN]
        exact Nat.mul_le_mul_right _ hk
    _ = Nat.card T := by rw [mul_comm]; exact Subgroup.card_mul_index N

theorem card_mul_card_centEl_le [Finite G] {T : Subgroup G} {z : G} {k : ℕ} (c : Fin k → G)
    (hc : ∀ i, c i ∈ T) (hd : ∀ i j, c i * z * (c i)⁻¹ = c j * z * (c j)⁻¹ → i = j) :
    k * Nat.card (centEl T z) ≤ Nat.card T := by
  have hNT : centEl T z ≤ T := inf_le_left
  let N := (centEl T z).subgroupOf T
  have hinj : Function.Injective
      (fun i : Fin k => (QuotientGroup.mk (⟨c i, hc i⟩ : T) : T ⧸ N)) := by
    intro i j hij
    have h1 := QuotientGroup.eq.1 hij
    rw [mem_subgroupOf] at h1
    have hx : z * ((c i)⁻¹ * c j) = ((c i)⁻¹ * c j) * z :=
      mem_centralizer_iff.1 h1.2 z (Set.mem_singleton z)
    apply hd
    have e : c j = c i * ((c i)⁻¹ * c j) := (mul_inv_cancel_left _ _).symm
    generalize (c i)⁻¹ * c j = x at hx e
    rw [e]
    calc c i * z * (c i)⁻¹ = c i * (z * x) * x⁻¹ * (c i)⁻¹ := by group
      _ = c i * x * z * (c i * x)⁻¹ := by rw [hx]; group
  have hk : k ≤ N.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index_eq_card] at this
  have hcN : Nat.card N = Nat.card (centEl T z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  calc k * Nat.card (centEl T z) ≤ N.index * Nat.card N := by
        rw [hcN]
        exact Nat.mul_le_mul_right _ hk
    _ = Nat.card T := by rw [mul_comm]; exact Subgroup.card_mul_index N

theorem exists_coset_of_card [Finite G] {V Z : Subgroup G} (hZV : Z ≤ V) {k : ℕ} (w : Fin k → G)
    (hwV : ∀ i, w i ∈ V) (hw : ∀ i j, (w j)⁻¹ * w i ∈ Z → i = j)
    (hcard : Nat.card V = k * Nat.card Z) : ∀ u ∈ V, ∃ i, (w i)⁻¹ * u ∈ Z := by
  let N := Z.subgroupOf V
  let f := fun i : Fin k => (QuotientGroup.mk (⟨w i, hwV i⟩ : V) : V ⧸ N)
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 := QuotientGroup.eq.1 hij
    rw [mem_subgroupOf] at h1
    exact (hw j i h1).symm
  have hcN : Nat.card N = Nat.card Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have hidx : N.index = k := by
    have h := Subgroup.card_mul_index N
    rw [hcN, hcard, mul_comm k] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [← Subgroup.index_eq_card, hidx, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro u hu
  obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk (⟨u, hu⟩ : V))
  have h1 := QuotientGroup.eq.1 hi
  rw [mem_subgroupOf] at h1
  exact ⟨i, h1⟩

theorem conjSub_eq_of_gens [Finite G] {E Y : Subgroup G} {e : Set G} (hE : E = closure e) {t : G}
    (ht : ∀ x ∈ e, t * x * t⁻¹ ∈ Y) (hcard : Nat.card Y ≤ Nat.card E) : conjSub t E = Y := by
  have hle : conjSub t E ≤ Y := by
    rw [conjSub, hE, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ht x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  exact hcard

theorem mem_conjSub_of {E : Subgroup G} {c e z : G} (he : e ∈ E) (h : c * e = z * c) :
    z ∈ conjSub c E := by
  refine mem_map.2 ⟨e, he, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h]
  group

theorem conjSub_ne_of_witness {E : Subgroup G} {ci cj d e : G} (hd : cj * d = ci) (he : e ∈ E)
    (hw : ∀ e' ∈ E, d * e ≠ e' * d) : conjSub ci E ≠ conjSub cj E := by
  intro heq
  have hm : ci * e * ci⁻¹ ∈ conjSub cj E := by
    rw [← heq]
    exact mem_conjSub_of he (by group)
  obtain ⟨e', he', hee⟩ := mem_map.1 hm
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
  apply hw e' he'
  rw [← hd] at hee
  calc d * e = cj⁻¹ * (cj * d * e * (cj * d)⁻¹) * cj * d := by group
    _ = cj⁻¹ * (cj * e' * cj⁻¹) * cj * d := by rw [hee]
    _ = e' * d := by group

theorem exists_perm3 {P Z : Subgroup G} (w : Fin 3 → G) (hw : ∀ i j, (w j)⁻¹ * w i ∈ Z → i = j)
    (hZ : P ≤ normalizer (Z : Set G)) (hP : ∀ x ∈ P, ∀ i, ∃ j, (w j)⁻¹ * (x * w i * x⁻¹) ∈ Z) :
    ∃ φ : ↥P →* Equiv.Perm (Fin 3),
      ∀ (x : ↥P) (i : Fin 3), (w (φ x i))⁻¹ * ((x : G) * w i * (x : G)⁻¹) ∈ Z := by
  have huniq : ∀ (y : G) (j j' : Fin 3), (w j)⁻¹ * y ∈ Z → (w j')⁻¹ * y ∈ Z → j = j' := by
    intro y j j' h1 h2
    have e : (w j')⁻¹ * y * ((w j)⁻¹ * y)⁻¹ = (w j')⁻¹ * w j := by group
    exact hw j j' (e ▸ mul_mem h2 (inv_mem h1))
  have hP' : ∀ (x : ↥P) (i : Fin 3), ∃ j, (w j)⁻¹ * ((x : G) * w i * (x : G)⁻¹) ∈ Z :=
    fun x i => hP x x.2 i
  choose σ hσ using hP'
  have hone : ∀ i, σ 1 i = i := fun i =>
    huniq _ _ _ (hσ 1 i) (by simp [one_mem])
  have hmul : ∀ x y : ↥P, ∀ i, σ (x * y) i = σ x (σ y i) := by
    intro x y i
    refine huniq _ _ _ (hσ (x * y) i) ?_
    have ha := hσ y i
    have hxa := (mem_normalizer_iff.1 (hZ x.2) _).1 ha
    have hb := hσ x (σ y i)
    have e : (w (σ x (σ y i)))⁻¹ * ((↑(x * y) : G) * w i * (↑(x * y) : G)⁻¹) =
        ((w (σ x (σ y i)))⁻¹ * ((x : G) * w (σ y i) * (x : G)⁻¹)) *
          ((x : G) * ((w (σ y i))⁻¹ * ((y : G) * w i * (y : G)⁻¹)) * (x : G)⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    rw [e]
    exact mul_mem hb hxa
  let π : ↥P → Equiv.Perm (Fin 3) := fun x =>
    { toFun := σ x
      invFun := σ x⁻¹
      left_inv := fun i => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun i => by rw [← hmul, mul_inv_cancel, hone] }
  refine ⟨{ toFun := π, map_one' := ?_, map_mul' := ?_ }, fun x i => hσ x i⟩
  · ext i
    exact congrArg Fin.val (hone i)
  · intro x y
    ext i
    exact congrArg Fin.val (hmul x y i)

theorem perm3_surjective {P : Type} [Group P] (φ : P →* Equiv.Perm (Fin 3)) {x y : P}
    (hx : orderOf (φ x) = 3) (hy : orderOf (φ y) = 2) : Function.Surjective φ := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h3 : 3 ∣ Nat.card φ.range := by
    have := Subgroup.orderOf_dvd_natCard φ.range (MonoidHom.mem_range.2 ⟨x, rfl⟩)
    rwa [hx] at this
  have h2 : 2 ∣ Nat.card φ.range := by
    have := Subgroup.orderOf_dvd_natCard φ.range (MonoidHom.mem_range.2 ⟨y, rfl⟩)
    rwa [hy] at this
  have hd : 6 ∣ Nat.card φ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
  have hle : Nat.card φ.range ≤ 6 := h6 ▸ Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have heq : Nat.card φ.range = 6 := by
    obtain ⟨m, hm⟩ := hd
    rcases m with _ | _ | m
    · omega
    · omega
    · omega
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (heq.trans h6.symm)
  exact MonoidHom.range_eq_top.1 htop

theorem secProp_perm3 [Finite G] {P B : Subgroup G} (hBP : B ≤ P) (φ : ↥P →* Equiv.Perm (Fin 3))
    (hφ : Function.Surjective φ) (hker : ∀ x : ↥P, (x : G) ∈ B → φ x = 1)
    (hcard : Nat.card P = 6 * Nat.card B) :
    SecProp P B (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hle : B.subgroupOf P ≤ φ.ker := fun x hx => hker x hx
  have hidx : φ.ker.index = 6 := by
    rw [Subgroup.index_eq_card, ← h6]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have hcB : Nat.card (B.subgroupOf P) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  have hck : Nat.card φ.ker = Nat.card B := by
    have h := Subgroup.card_mul_index φ.ker
    rw [hidx, hcard, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have heq : B.subgroupOf P = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hck, hcB])
  have hn : (B.subgroupOf P).Normal := by
    rw [heq]
    infer_instance
  exact ⟨hn, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩⟩

theorem actsRegularly_zpowers [Finite G] {τ : G} {V Z : Subgroup G} (hZV : Z ≤ V)
    (hcard : Nat.card V = 4 * Nat.card Z) (hτ : τ ^ 3 = 1)
    (hτV : τ ∈ normalizer (V : Set G)) (hτZ : τ ∈ normalizer (Z : Set G))
    (hfp : ∀ u ∈ V, u ∉ Z → u⁻¹ * (τ * u * τ⁻¹) ∉ Z) : ActsRegularly (zpowers τ) V Z := by
  refine ⟨(zpowers_le (H := normalizer (V : Set G))).2 hτV,
    (zpowers_le (H := normalizer (Z : Set G))).2 hτZ, ?_⟩
  have hk3 : ∀ k ∈ zpowers τ, k = 1 ∨ k = τ ∨ k = τ * τ := by
    intro k hk
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    have h3' : τ ^ (3 : ℤ) = 1 := by exact_mod_cast hτ
    have hn : τ ^ n = τ ^ (n % 3) := by
      have e : n = n % 3 + 3 * (n / 3) := by omega
      conv_lhs => rw [e]
      rw [zpow_add, zpow_mul, h3', one_zpow, mul_one]
    have h0 := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
    have h3 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
    rw [hn]
    interval_cases h : n % 3
    · simp
    · simp
    · right
      right
      exact zpow_two τ
  intro u hu huZ v hv hvZ
  let c : G → G := fun y => τ * y * τ⁻¹
  have hcV : ∀ y ∈ V, c y ∈ V := fun y hy => (mem_normalizer_iff.1 hτV y).1 hy
  have hcZ : ∀ y, y ∉ Z → c y ∉ Z := fun y hy h => hy ((mem_normalizer_iff.1 hτZ y).2 h)
  have hc3 : c (c (c u)) = u := by
    have h3m : τ * τ * τ = 1 := by
      rw [← hτ]
      simp only [pow_succ, pow_zero, one_mul]
    have e : c (c (c u)) = (τ * τ * τ) * u * (τ * τ * τ)⁻¹ := by
      simp only [c]
      group
    rw [e, h3m]
    group
  have ninv : ∀ a b : G, a⁻¹ * b ∉ Z → b⁻¹ * a ∉ Z := fun a b h h' => by
    apply h
    have := inv_mem h'
    rwa [mul_inv_rev, inv_inv] at this
  have d01 : u⁻¹ * c u ∉ Z := hfp u hu huZ
  have d12 : (c u)⁻¹ * c (c u) ∉ Z := hfp (c u) (hcV u hu) (hcZ u huZ)
  have d20 : (c (c u))⁻¹ * u ∉ Z := by
    have := hfp (c (c u)) (hcV _ (hcV u hu)) (hcZ _ (hcZ u huZ))
    change (c (c u))⁻¹ * c (c (c u)) ∉ Z at this
    rwa [hc3] at this
  let W : Fin 3 → G := ![u, c u, c (c u)]
  let K : Fin 3 → G := ![1, τ, τ * τ]
  have hKW : ∀ a, K a * u * (K a)⁻¹ = W a := by
    intro a
    fin_cases a
    · simp [K, W]
    · rfl
    · change τ * τ * u * (τ * τ)⁻¹ = τ * (τ * u * τ⁻¹) * τ⁻¹
      group
  have hWV : ∀ a, W a ∈ V := by
    intro a
    fin_cases a
    · exact hu
    · exact hcV u hu
    · exact hcV _ (hcV u hu)
  have hWZ : ∀ a, W a ∉ Z := by
    intro a
    fin_cases a
    · exact huZ
    · exact hcZ u huZ
    · exact hcZ _ (hcZ u huZ)
  have hWd : ∀ a b, (W b)⁻¹ * W a ∈ Z → a = b := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h (ninv _ _ d01)
    · exact absurd h d20
    · exact absurd h d01
    · rfl
    · exact absurd h (ninv _ _ d12)
    · exact absurd h (ninv _ _ d20)
    · exact absurd h d12
    · rfl
  have hKmem : ∀ a, K a ∈ zpowers τ := by
    intro a
    fin_cases a
    · exact one_mem _
    · exact mem_zpowers τ
    · exact mul_mem (mem_zpowers τ) (mem_zpowers τ)
  let w4 : Fin 4 → G := ![1, u, c u, c (c u)]
  have hw4 : ∀ i j, (w4 j)⁻¹ * w4 i ∈ Z → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa [w4] using h) huZ
    · exact absurd (by simpa [w4] using h) (hcZ u huZ)
    · exact absurd (by simpa [w4] using h) (hcZ _ (hcZ u huZ))
    · exact absurd (by simpa [w4] using h) huZ
    · rfl
    · exact absurd (hWd 0 1 h) (by decide)
    · exact absurd (hWd 0 2 h) (by decide)
    · exact absurd (by simpa [w4] using h) (hcZ u huZ)
    · exact absurd (hWd 1 0 h) (by decide)
    · rfl
    · exact absurd (hWd 1 2 h) (by decide)
    · exact absurd (by simpa [w4] using h) (hcZ _ (hcZ u huZ))
    · exact absurd (hWd 2 0 h) (by decide)
    · exact absurd (hWd 2 1 h) (by decide)
    · rfl
  have hw4V : ∀ i, w4 i ∈ V := by
    intro i
    fin_cases i
    · exact one_mem _
    · exact hWV 0
    · exact hWV 1
    · exact hWV 2
  obtain ⟨i, hi⟩ := exists_coset_of_card hZV w4 hw4V hw4 hcard v hv
  have hex : ∃ a, (W a)⁻¹ * v ∈ Z := by
    fin_cases i
    · exact absurd (by simpa [w4] using hi) hvZ
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨2, hi⟩
  obtain ⟨a, ha⟩ := hex
  have ha' : v⁻¹ * W a ∈ Z := by
    have := inv_mem ha
    rwa [mul_inv_rev, inv_inv] at this
  refine ⟨K a, ⟨hKmem a, by rw [hKW]; exact ha'⟩, ?_⟩
  rintro k ⟨hk, hkv⟩
  have hb : ∃ b, k = K b := by
    rcases hk3 k hk with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨b, rfl⟩ := hb
  rw [hKW] at hkv
  have : (W a)⁻¹ * W b ∈ Z := by
    have e : (W a)⁻¹ * W b = ((W a)⁻¹ * v) * (v⁻¹ * W b) := by group
    rw [e]
    exact mul_mem ha hkv
  rw [hWd b a this]

theorem no_complement [Finite G] {S F : Subgroup G} (hFS : F ≤ S)
    (hFn : S ≤ normalizer (F : Set G)) (hS : Nat.card S = 64) (hF : Nat.card F = 8)
    (hsq : ∀ y ∈ S, y ^ 4 = 1 → y ^ 2 ∈ F) {x : G} (hx : x ∈ S) (hx2 : x ^ 2 ∉ F) :
    ∀ P : Subgroup G, P ≤ S → P ⊓ F = ⊥ → Nat.card P * Nat.card F ≠ Nat.card S := by
  intro P hPS hPF hc
  have hP8 : Nat.card P = 8 := by
    rw [hS, hF] at hc
    omega
  have hPF' : ∀ y, y ∈ P → y ∈ F → y = 1 := fun y h1 h2 => by
    have : y ∈ P ⊓ F := ⟨h1, h2⟩
    rwa [hPF, mem_bot] at this
  let m : ↥P × ↥F → ↥S := fun q => ⟨q.1 * q.2, mul_mem (hPS q.1.2) (hFS q.2.2)⟩
  have hm : Function.Injective m := by
    rintro ⟨p1, f1⟩ ⟨p2, f2⟩ h
    have h' : (p1 : G) * f1 = p2 * f2 := congrArg Subtype.val h
    have e1 : (p2 : G)⁻¹ * p1 = f2 * (f1 : G)⁻¹ := by
      calc (p2 : G)⁻¹ * p1 = (p2 : G)⁻¹ * (p1 * f1) * (f1 : G)⁻¹ := by group
        _ = (p2 : G)⁻¹ * (p2 * f2) * (f1 : G)⁻¹ := by rw [h']
        _ = f2 * (f1 : G)⁻¹ := by group
    have h1 := hPF' _ (mul_mem (inv_mem p2.2) p1.2) (e1 ▸ mul_mem f2.2 (inv_mem f1.2))
    have hp : (p1 : G) = p2 := by
      calc (p1 : G) = p2 * ((p2 : G)⁻¹ * p1) := by group
        _ = p2 := by rw [h1, mul_one]
    have hf : (f1 : G) = f2 := by
      have := h'
      rw [hp] at this
      exact mul_left_cancel this
    rw [Prod.mk.injEq]
    exact ⟨Subtype.ext hp, Subtype.ext hf⟩
  have hbij : Function.Bijective m := by
    refine hm.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, ← hc]
  obtain ⟨⟨p, f⟩, hpf⟩ := hbij.2 ⟨x, hx⟩
  have hxpf : x = p * f := (congrArg Subtype.val hpf).symm
  have hpS : (p : G) ∈ S := hPS p.2
  have hconj : (p : G)⁻¹ * f * (p : G)⁻¹⁻¹ ∈ F :=
    (mem_normalizer_iff.1 (hFn (inv_mem hpS)) f).1 f.2
  have hp2 : (p : G) ^ 2 ∉ F := by
    intro h
    apply hx2
    have e : x ^ 2 = (p : G) ^ 2 * ((p : G)⁻¹ * f * (p : G)⁻¹⁻¹) * f := by
      rw [hxpf]
      simp only [sq, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (mul_mem h hconj) f.2
  have hp8 : (p : G) ^ 8 = 1 := by
    have : p ^ Nat.card ↥P = 1 := pow_card_eq_one'
    rw [hP8] at this
    exact congrArg Subtype.val this
  have hp4F : (p : G) ^ 4 ∈ F := by
    have h := hsq ((p : G) ^ 2) (pow_mem hpS 2) (by rw [← pow_mul]; exact hp8)
    rwa [← pow_mul] at h
  have hp4 : (p : G) ^ 4 = 1 := hPF' _ (pow_mem p.2 4) hp4F
  exact hp2 (hsq p hpS hp4)

@[expose] def evec {n : ℕ} (j : Fin n) : Fin n → ZMod 2 := fun i => if j = i then 1 else 0

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem mulVec_evec {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin n) :
    M *ᵥ evec j = fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, evec]

theorem hom_zero {n : ℕ} {h : (Fin n → ZMod 2) → G} (a : ∀ v w, h (v + w) = h v * h w) :
    h 0 = 1 := by
  have e := a 0 0
  rw [add_zero] at e
  calc h 0 = h 0 * h 0 * (h 0)⁻¹ := by group
    _ = h 0 * (h 0)⁻¹ := by rw [← e]
    _ = 1 := mul_inv_cancel _

theorem hom_eq_of_evec {n : ℕ} {h1 h2 : (Fin n → ZMod 2) → G}
    (a1 : ∀ v w, h1 (v + w) = h1 v * h1 w) (a2 : ∀ v w, h2 (v + w) = h2 v * h2 w)
    (he : ∀ j, h1 (evec j) = h2 (evec j)) (v : Fin n → ZMod 2) : h1 v = h2 v := by
  have hs : ∀ s : Finset (Fin n), h1 (∑ i ∈ s, v i • evec i) = h2 (∑ i ∈ s, v i • evec i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, hom_zero a1, hom_zero a2]
    · intro j s hj ih
      rw [Finset.sum_insert hj, a1, a2, ih]
      congr 1
      rcases zmod2_cases (v j) with h | h
      · rw [h, zero_smul, hom_zero a1, hom_zero a2]
      · rw [h, one_smul, he]
  have hv : v = ∑ i, v i • evec i := by
    funext k
    simp [evec, Finset.sum_apply]
  rw [hv]
  exact hs Finset.univ

theorem exists_glHom [Finite G] {n : ℕ} {N F : Subgroup G} (E : (Fin n → ZMod 2) → G)
    (hadd : ∀ v w, E (v + w) = E v * E w) (hmem : ∀ v, E v ∈ F) (hinj : Function.Injective E)
    (hsurj : ∀ y ∈ F, ∃ v, E v = y) (hN : N ≤ normalizer (F : Set G)) :
    ∃ φ : ↥N →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2),
      (∀ x : ↥N, φ x = 1 ↔ ∀ y ∈ F, (x : G) * y = y * x) ∧
      ∀ (x : ↥N) (v : Fin n → ZMod 2),
        (x : G) * E v * (x : G)⁻¹ = E ((φ x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) := by
  classical
  let Einv : G → (Fin n → ZMod 2) := fun y => if h : ∃ v, E v = y then h.choose else 0
  have hEinv : ∀ y ∈ F, E (Einv y) = y := by
    intro y hy
    have h := hsurj y hy
    simp only [Einv, dif_pos h]
    exact h.choose_spec
  have hEinvE : ∀ v, Einv (E v) = v := fun v => hinj (hEinv _ (hmem v))
  have hconj : ∀ x ∈ N, ∀ y ∈ F, x * y * x⁻¹ ∈ F := fun x hx y hy =>
    (mem_normalizer_iff.1 (hN hx) y).1 hy
  let M : G → Matrix (Fin n) (Fin n) (ZMod 2) := fun x =>
    Matrix.of fun i j => Einv (x * E (evec j) * x⁻¹) i
  have hcol : ∀ x ∈ N, ∀ j, E (M x *ᵥ evec j) = x * E (evec j) * x⁻¹ := by
    intro x hx j
    rw [mulVec_evec]
    exact hEinv _ (hconj x hx _ (hmem _))
  have hkey : ∀ x ∈ N, ∀ v, x * E v * x⁻¹ = E (M x *ᵥ v) := by
    intro x hx v
    refine hom_eq_of_evec (h1 := fun v => x * E v * x⁻¹) (h2 := fun v => E (M x *ᵥ v)) ?_ ?_ ?_ v
    · intro v w
      simp only [hadd]
      group
    · intro v w
      simp only [Matrix.mulVec_add, hadd]
    · intro j
      exact (hcol x hx j).symm
  have hMmul : ∀ x ∈ N, ∀ y ∈ N, M (x * y) = M x * M y := by
    intro x hx y hy
    ext i j
    have e : (x * y) * E (evec j) * (x * y)⁻¹ = E ((M x * M y) *ᵥ evec j) := by
      calc (x * y) * E (evec j) * (x * y)⁻¹ = x * (y * E (evec j) * y⁻¹) * x⁻¹ := by group
        _ = x * E (M y *ᵥ evec j) * x⁻¹ := by rw [hkey y hy]
        _ = E (M x *ᵥ (M y *ᵥ evec j)) := hkey x hx _
        _ = E ((M x * M y) *ᵥ evec j) := by rw [Matrix.mulVec_mulVec]
    have h2 := congrFun (congrArg Einv e) i
    rw [hEinvE, mulVec_evec] at h2
    exact h2
  have hM1 : M 1 = 1 := by
    ext i j
    simp only [M, Matrix.of_apply, one_mul, inv_one, mul_one, hEinvE, evec, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  let φ0 : ↥N →* Matrix (Fin n) (Fin n) (ZMod 2) :=
    { toFun := fun x => M x
      map_one' := hM1
      map_mul' := fun x y => hMmul x x.2 y y.2 }
  refine ⟨φ0.toHomUnits, fun x => ?_, fun x v => hkey x x.2 v⟩
  rw [Units.ext_iff, Units.val_one]
  change M x = 1 ↔ _
  constructor
  · intro h y hy
    obtain ⟨v, rfl⟩ := hsurj y hy
    have e := hkey x x.2 v
    rw [h, Matrix.one_mulVec] at e
    calc (x : G) * E v = x * E v * (x : G)⁻¹ * x := by group
      _ = E v * x := by rw [e]
  · intro h
    ext i j
    have e : (x : G) * E (evec j) * (x : G)⁻¹ = E (evec j) := by
      rw [h _ (hmem _)]
      group
    change Einv ((x : G) * E (evec j) * (x : G)⁻¹) i = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
    rw [e, hEinvE, Matrix.one_apply]
    simp only [evec]
    by_cases h' : i = j
    · simp [h']
    · simp [h', Ne.symm h']

theorem pow_val_add {x : G} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show ZMod.val (1 : ZMod 2) = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl, hx]

theorem zmod2_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  rcases zmod2_cases (v i) with h | h <;> simp [h] <;> rfl

theorem basis_of_E [Finite G] {n : ℕ} (f : Fin n → G) (E : (Fin n → ZMod 2) → G)
    (hadd : ∀ v w, E (v + w) = E v * E w) (hmem : ∀ v, E v ∈ closure (Set.range f))
    (he : ∀ j, E (evec j) = f j) (hcard : Nat.card (closure (Set.range f)) = 2 ^ n) :
    Function.Injective E ∧ ∀ y ∈ closure (Set.range f), ∃ v, E v = y := by
  have hsurj : ∀ y ∈ closure (Set.range f), ∃ v, E v = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨evec j, he j⟩
    | one => exact ⟨0, hom_zero hadd⟩
    | mul x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact ⟨v + w, hadd v w⟩
    | inv x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      refine ⟨v, (inv_eq_of_mul_eq_one_right ?_).symm⟩
      rw [← hadd, zmod2_add_self, hom_zero hadd]
  refine ⟨?_, hsurj⟩
  let E' : (Fin n → ZMod 2) → ↥(closure (Set.range f)) := fun v => ⟨E v, hmem v⟩
  have hE' : Function.Surjective E' := fun y => by
    obtain ⟨v, hv⟩ := hsurj y y.2
    exact ⟨v, Subtype.ext hv⟩
  have hb : Function.Bijective E' := by
    have : Fintype ↥(closure (Set.range f)) := Fintype.ofFinite _
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨hE', ?_⟩
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  intro v w h
  exact hb.1 (Subtype.ext h)

theorem vecE_add {f : Fin 3 → G} (hcomm : ∀ i j, f i * f j = f j * f i)
    (hsq : ∀ i, f i * f i = 1) (v w : Fin 3 → ZMod 2) : vecE f (v + w) = vecE f v * vecE f w := by
  simp only [vecE, Pi.add_apply, pow_val_add (hsq _)]
  have c : ∀ i j (a b : ℕ), Commute (f i ^ a) (f j ^ b) := fun i j a b =>
    (show Commute (f i) (f j) from hcomm i j).pow_pow a b
  rw [(c 0 1 _ _).mul_mul_mul_comm, ((c 0 2 _ _).mul_left (c 1 2 _ _)).mul_mul_mul_comm]

theorem vecE_mem (f : Fin 3 → G) (v : Fin 3 → ZMod 2) : vecE f v ∈ closure (Set.range f) :=
  mul_mem (mul_mem (pow_mem (subset_closure (Set.mem_range_self 0)) _)
    (pow_mem (subset_closure (Set.mem_range_self 1)) _))
    (pow_mem (subset_closure (Set.mem_range_self 2)) _)

theorem vecE_evec (f : Fin 3 → G) (j : Fin 3) : vecE f (evec j) = f j := by
  fin_cases j <;> simp [vecE, evec, show ZMod.val (1 : ZMod 2) = 1 from rfl]

theorem card_GL3 : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  rfl

theorem secProp_gl3 [Finite G] {T F : Subgroup G} (f : Fin 3 → G)
    (hcomm : ∀ i j, f i * f j = f j * f i) (hsq : ∀ i, f i * f i = 1)
    (hF : F = closure (Set.range f)) (hF8 : Nat.card F = 8) (hFT : F ≤ T)
    (hnorm : T ≤ normalizer (F : Set G)) (hT : Nat.card T = 1344) {k : ℕ} (g : Fin k → G)
    (hg : ∀ s, g s ∈ T) (A : Fin k → Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hA : ∀ s j, g s * f j * (g s)⁻¹ = vecE f (fun i => A s i j))
    (h168 : 168 ≤ Nat.card (Submonoid.closure (Set.range A))) :
    SecProp T F (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
  subst hF
  have hadd := vecE_add hcomm hsq
  obtain ⟨hinj, hsurj⟩ := basis_of_E f (vecE f) hadd (vecE_mem f) (vecE_evec f) hF8
  obtain ⟨φ, hker, hact⟩ := exists_glHom (N := T) (vecE f) hadd (vecE_mem f) hinj hsurj hnorm
  have hφg : ∀ s, (φ ⟨g s, hg s⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = A s := by
    intro s
    ext i j
    have e : g s * vecE f (evec j) * (g s)⁻¹ =
        vecE f ((φ ⟨g s, hg s⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ evec j) :=
      hact ⟨g s, hg s⟩ (evec j)
    rw [vecE_evec, hA s j, mulVec_evec] at e
    exact (congrFun (hinj e) i).symm
  let ψ : ↥T →* Matrix (Fin 3) (Fin 3) (ZMod 2) := (Units.coeHom _).comp φ
  have hcl : Submonoid.closure (Set.range A) ≤ MonoidHom.mrange ψ := by
    rw [Submonoid.closure_le]
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨g s, hg s⟩, hφg s⟩
  have h1 : 168 ≤ Nat.card (MonoidHom.mrange ψ) :=
    h168.trans (Nat.card_le_card_of_injective _ (Submonoid.inclusion_injective hcl))
  let r : ↥φ.range → ↥(MonoidHom.mrange ψ) := fun u =>
    ⟨(u.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)), by
      obtain ⟨t, ht⟩ := u.2
      exact ⟨t, by simp [ψ, ht]⟩⟩
  have hr : Function.Surjective r := by
    rintro ⟨M, t, rfl⟩
    exact ⟨⟨φ t, t, rfl⟩, rfl⟩
  have h2 := Nat.card_le_card_of_surjective r hr
  have h3 : Nat.card φ.range ≤ 168 := card_GL3 ▸ Subgroup.card_le_card_group _
  have hrange : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [card_GL3]; omega)
  have hφs : Function.Surjective φ := MonoidHom.range_eq_top.1 hrange
  have hidx : φ.ker.index = 168 := by
    rw [Subgroup.index_eq_card, ← card_GL3]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have hck : Nat.card φ.ker = 8 := by
    have h := Subgroup.card_mul_index φ.ker
    rw [hidx, hT] at h
    omega
  have hc' : ∀ a ∈ Set.range f, ∀ b ∈ Set.range f, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hle : (closure (Set.range f)).subgroupOf T ≤ φ.ker := fun x hx =>
    (hker x).2 fun y hy => closure_comm hc' _ (mem_subgroupOf.1 hx) _ hy
  have hcF : Nat.card ((closure (Set.range f)).subgroupOf T) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv).trans hF8
  have heq : (closure (Set.range f)).subgroupOf T = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hck, hcF])
  have hn : ((closure (Set.range f)).subgroupOf T).Normal := by
    rw [heq]
    infer_instance
  exact ⟨hn, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩⟩

end CFSG.KC.G2Three.Sec1

end
