module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.SylowCharacterTable
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

namespace CFSG.LyonsUnitaryFour

open scoped BigOperators Classical

variable {G : Type} [Group G]

section Inner

@[expose] def innerActing (S : Subgroup G) : Subgroup G where
  carrier := {k | ∃ s ∈ S, ∀ w ∈ S, k⁻¹ * w * k = s⁻¹ * w * s}
  one_mem' := ⟨1, S.one_mem, fun w _ => by group⟩
  mul_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    refine ⟨s * t, S.mul_mem hs ht, fun w hw => ?_⟩
    have h1 := ha w hw
    have h2 := hb (s⁻¹ * w * s) (S.mul_mem (S.mul_mem (S.inv_mem hs) hw) hs)
    calc (a * b)⁻¹ * w * (a * b) = b⁻¹ * (a⁻¹ * w * a) * b := by group
      _ = b⁻¹ * (s⁻¹ * w * s) * b := by rw [h1]
      _ = t⁻¹ * (s⁻¹ * w * s) * t := h2
      _ = (s * t)⁻¹ * w * (s * t) := by group
  inv_mem' := by
    rintro a ⟨s, hs, ha⟩
    refine ⟨s⁻¹, S.inv_mem hs, fun w hw => ?_⟩
    have h := ha (s * w * s⁻¹) (S.mul_mem (S.mul_mem hs hw) (S.inv_mem hs))
    have h' : a⁻¹ * (s * w * s⁻¹) * a = w := by rw [h]; group
    calc a⁻¹⁻¹ * w * a⁻¹ = a * (a⁻¹ * (s * w * s⁻¹) * a) * a⁻¹ := by rw [h']; group
      _ = s⁻¹⁻¹ * w * s⁻¹ := by group

theorem mem_innerActing_iff {S : Subgroup G} {k : G} :
    k ∈ innerActing S ↔ ∃ s ∈ S, ∀ w ∈ S, k⁻¹ * w * k = s⁻¹ * w * s := Iff.rfl

theorem le_innerActing (S : Subgroup G) : S ≤ innerActing S :=
  fun k hk => ⟨k, hk, fun _ _ => rfl⟩

theorem centralizer_le_innerActing (S : Subgroup G) :
    Subgroup.centralizer (S : Set G) ≤ innerActing S := by
  intro k hk
  refine ⟨1, S.one_mem, fun w hw => ?_⟩
  have h : w * k = k * w := Subgroup.mem_centralizer_iff.mp hk w hw
  calc k⁻¹ * w * k = k⁻¹ * (k * w) := by rw [mul_assoc, h]
    _ = 1⁻¹ * w * 1 := by group

theorem sup_centralizer_le_innerActing (S : Subgroup G) :
    S ⊔ Subgroup.centralizer (S : Set G) ≤ innerActing S :=
  sup_le (le_innerActing S) (centralizer_le_innerActing S)

end Inner

section Conjugate

theorem conj_mem_of_mem_normalizer {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) {x : G} (hx : x ∈ S) : n⁻¹ * x * n ∈ S :=
  (Subgroup.mem_normalizer_iff''.mp hn x).mp hx

theorem conj_mem_of_mem_normalizer' {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) {x : G} (hx : x ∈ S) : n * x * n⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hn x).mp hx

@[expose] noncomputable def conjugateCharacter (S : Subgroup G) (n : G) (θ : S → ℂ) : S → ℂ :=
  fun x => if h : n⁻¹ * (x : G) * n ∈ S then θ ⟨n⁻¹ * x * n, h⟩ else 0

theorem conjugateCharacter_apply {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (θ : S → ℂ) (x : S) :
    conjugateCharacter S n θ x = θ ⟨n⁻¹ * x * n, conj_mem_of_mem_normalizer hn x.property⟩ := by
  unfold conjugateCharacter
  rw [dite_eq_left (conj_mem_of_mem_normalizer hn x.property)]

theorem conjugateCharacter_one (S : Subgroup G) (θ : S → ℂ) : conjugateCharacter S 1 θ = θ := by
  funext x
  rw [conjugateCharacter_apply (Subgroup.one_mem _)]
  congr 1
  ext
  simp

theorem conjugateCharacter_mul {S : Subgroup G} {m n : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (hn : n ∈ Subgroup.normalizer (S : Set G))
    (θ : S → ℂ) :
    conjugateCharacter S m (conjugateCharacter S n θ) = conjugateCharacter S (m * n) θ := by
  funext x
  rw [conjugateCharacter_apply hm, conjugateCharacter_apply hn,
    conjugateCharacter_apply (Subgroup.mul_mem _ hm hn)]
  congr 1
  ext
  simp only [mul_inv_rev]
  group

theorem conjugateCharacter_pow {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (θ : S → ℂ) (j : ℕ) :
    conjugateCharacter S n (conjugateCharacter S (n ^ j) θ) =
      conjugateCharacter S (n ^ (j + 1)) θ := by
  rw [conjugateCharacter_mul hn (Subgroup.pow_mem _ hn j), pow_succ']

theorem conjugateCharacter_innerActing {S : Subgroup G} {k : G} (hk : k ∈ innerActing S)
    (θ : S → ℂ) (hθ : ∀ c x : S, θ (c * x * c⁻¹) = θ x) : conjugateCharacter S k θ = θ := by
  obtain ⟨s, hs, hks⟩ := hk
  funext x
  unfold conjugateCharacter
  have hmem : k⁻¹ * (x : G) * k ∈ S := by
    rw [hks x x.property]
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) x.property) hs
  rw [dite_eq_left hmem]
  have := hθ ⟨s, hs⟩⁻¹ x
  rw [← this]
  congr 1
  ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  exact hks x x.property

theorem conjugateCharacter_mem_blocksIrr {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) {θ : S → ℂ} (hθ : θ ∈ CFSG.BlocksIrr S) :
    conjugateCharacter S n θ ∈ CFSG.BlocksIrr S := by
  obtain ⟨V, hV, hM, hF, ρ, hirr, rfl⟩ := hθ
  let φ : S →* S :=
    { toFun := fun x => ⟨n⁻¹ * x * n, conj_mem_of_mem_normalizer hn x.property⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hφ : Function.Surjective φ := by
    intro y
    refine ⟨⟨n * y * n⁻¹, conj_mem_of_mem_normalizer' hn y.property⟩, ?_⟩
    ext
    change n⁻¹ * (n * y * n⁻¹) * n = y
    group
  refine ⟨V, hV, hM, hF, ρ.comp φ, isIrreducible_comp_surjective φ hφ ρ hirr, ?_⟩
  funext x
  rw [conjugateCharacter_apply hn]
  rfl

@[expose] def normalizerConj (S : Subgroup G) {m : G} (hm : m ∈ Subgroup.normalizer (S : Set G)) :
    S ≃* S where
  toFun x := ⟨m⁻¹ * x * m, conj_mem_of_mem_normalizer hm x.property⟩
  invFun x := ⟨m * x * m⁻¹, conj_mem_of_mem_normalizer' hm x.property⟩
  left_inv x := by ext; change m * (m⁻¹ * x * m) * m⁻¹ = x; group
  right_inv x := by ext; change m⁻¹ * (m * x * m⁻¹) * m = x; group
  map_mul' x y := by ext; change m⁻¹ * (x * y) * m = m⁻¹ * x * m * (m⁻¹ * y * m); group

theorem normalizerConj_apply (S : Subgroup G) {m : G} (hm : m ∈ Subgroup.normalizer (S : Set G))
    (x : S) : (normalizerConj S hm x : G) = m⁻¹ * x * m := rfl

theorem conjugateCharacter_eq_comp {S : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (θ : S → ℂ) :
    conjugateCharacter S m θ = θ ∘ normalizerConj S hm := by
  funext x
  rw [conjugateCharacter_apply hm]
  rfl

theorem normalizerConj_fixedPointFree {S : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G))
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → m * z * m⁻¹ ≠ z) :
    ∀ z ∈ Subgroup.center S, normalizerConj S hm z = z → z = 1 := by
  intro z hz hφ
  by_contra hz1
  have hzG : (z : G) ∈ (Subgroup.center S).map S.subtype := ⟨z, hz, rfl⟩
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  apply hfix _ hzG hz1'
  have h : m⁻¹ * (z : G) * m = z := congrArg Subtype.val hφ
  calc m * (z : G) * m⁻¹ = m * (m⁻¹ * (z : G) * m) * m⁻¹ := by rw [h]
    _ = z := by group

theorem conjugateCharacter_apply_one {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (θ : S → ℂ) :
    conjugateCharacter S n θ 1 = θ 1 := by
  rw [conjugateCharacter_apply hn]
  congr 1
  ext
  simp

end Conjugate

section Normalizer

theorem conj_mem_map_center_of_mem_normalizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) {z : G}
    (hz : z ∈ (Subgroup.center S).map S.subtype) :
    g⁻¹ * z * g ∈ (Subgroup.center S).map S.subtype := by
  rw [mem_map_center_iff] at hz ⊢
  obtain ⟨hzS, hzc⟩ := hz
  refine ⟨conj_mem_of_mem_normalizer hg hzS, fun s hs => ?_⟩
  have h := hzc (g * s * g⁻¹) (conj_mem_of_mem_normalizer' hg hs)
  calc s * (g⁻¹ * z * g) = g⁻¹ * ((g * s * g⁻¹) * z) * g := by group
    _ = g⁻¹ * (z * (g * s * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * z * g * s := by group

theorem order_three_normalizer_generator [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      (∀ m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
        ∃ j : ℕ, j < 3 ∧ (n ^ j)⁻¹ * m ∈ innerActing (S : Subgroup G)) ∧
      n ^ 3 ∈ innerActing (S : Subgroup G) ∧
      (∀ j : ℕ, 0 < j → j < 3 →
        ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype,
          z ≠ 1 → n ^ j * z * (n ^ j)⁻¹ ≠ z) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hindex, -, -, hcent⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  set M := Sg ⊔ Subgroup.centralizer (Sg : Set G) with hM
  set K := (Subgroup.centralizer (Z : Set G)).subgroupOf N with hK
  have hMC : M ≤ Subgroup.centralizer (Z : Set G) := by
    refine sup_le ?_ ?_
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((mem_map_center_iff.mp hz).2 s hs).symm
    · exact Subgroup.centralizer_le fun z hz => (mem_map_center_iff.mp hz).1
  have hMK : M.subgroupOf N ≤ K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hMC hx
  have hKM : K ≤ M.subgroupOf N := by
    have h := Subgroup.relIndex_mul_index hMK
    rw [hd, hindex] at h
    have h1 : (M.subgroupOf N).relIndex K = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hKnormal : K.Normal := by
    constructor
    intro k hk g
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hk ⊢
    intro z hz
    have h := hk _ (conj_mem_map_center_of_mem_normalizer g.property hz)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc z * (g * k * (g : G)⁻¹) = g * (((g : G)⁻¹ * z * g) * k) * (g : G)⁻¹ := by group
      _ = g * (k * ((g : G)⁻¹ * z * g)) * (g : G)⁻¹ := by rw [h]
      _ = g * k * (g : G)⁻¹ * z := by group
  have hQcard : Nat.card (N ⧸ K) = 3 := by rw [← Subgroup.index_eq_card]; exact hindex
  have hKne : K ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hindex
    norm_num at hindex
  obtain ⟨n', hn'⟩ : ∃ n' : N, n' ∉ K := by
    by_contra hall
    push Not at hall
    exact hKne (eq_top_iff.mpr fun x _ => hall x)
  have hq1 : (n' : N ⧸ K) ≠ 1 := by
    intro h
    exact hn' ((QuotientGroup.eq_one_iff n').mp h)
  have hqord : orderOf (n' : N ⧸ K) = 3 := by
    have hdvd : orderOf (n' : N ⧸ K) ∣ 3 := hQcard ▸ orderOf_dvd_natCard _
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq1
    · exact h
  have htop : Subgroup.zpowers (n' : N ⧸ K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hqord, hQcard])
  have hinner : ∀ k : N, k ∈ K → (k : G) ∈ innerActing Sg := by
    intro k hk
    have := hKM hk
    rw [Subgroup.mem_subgroupOf] at this
    exact sup_centralizer_le_innerActing Sg this
  refine ⟨n'.val, n'.property, ?_, ?_, ?_⟩
  · intro m hm
    have hmem : ((⟨m, hm⟩ : N) : N ⧸ K) ∈ Subgroup.zpowers (n' : N ⧸ K) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [mem_zpowers_iff_mem_range_orderOf, hqord, Finset.mem_image] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    refine ⟨j, Finset.mem_range.mp hj, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hjeq
    have := hinner _ hjeq
    simpa using this
  · have h3 : (n' : N ⧸ K) ^ 3 = 1 := by rw [← hqord]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
    have := hinner _ h3
    simpa using this
  · intro j hj0 hj3 z hz hz1 hfix
    have hqj : (n' : N ⧸ K) ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    apply hqj
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf]
    have hC : (n' : G) ^ j ∈ N ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ n'.property j, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (n' : G) ^ j * z = (n' : G) ^ j * z * ((n' : G) ^ j)⁻¹ * (n' : G) ^ j := by group
        _ = z * (n' : G) ^ j := by rw [hfix]
    rw [(hcent z hz hz1).1] at hC
    simpa using hC.2

end Normalizer

section Classes

variable {S : Subgroup G}

theorem mem_center_of_conj_mul_inv_mem {m : G}
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → m * z * m⁻¹ ≠ z) {w : G}
    (hw : w ∈ S) (hwz : m * w * m⁻¹ * w⁻¹ ∈ (Subgroup.center S).map S.subtype) :
    w ∈ (Subgroup.center S).map S.subtype := by
  by_contra hwZ
  set z := m * w * m⁻¹ * w⁻¹ with hzdef
  have hzS := (mem_map_center_iff.mp hwz).1
  have hzw : w * z = z * w := (mem_map_center_iff.mp hwz).2 w hw
  have hz2 : z ^ 2 = 1 := (hsq z hzS).mpr hwz
  have hmw : m * w * m⁻¹ = z * w := by rw [hzdef]; group
  have hsq' : m * w ^ 2 * m⁻¹ = w ^ 2 := by
    calc m * w ^ 2 * m⁻¹ = (m * w * m⁻¹) * (m * w * m⁻¹) := by rw [pow_two]; group
      _ = (z * w) * (z * w) := by rw [hmw]
      _ = z ^ 2 * w ^ 2 := by
        rw [pow_two, pow_two]
        calc z * w * (z * w) = z * (w * z) * w := by group
          _ = z * (z * w) * w := by rw [hzw]
          _ = z * z * (w * w) := by group
      _ = w ^ 2 := by rw [hz2, one_mul]
  have hw2 : w ^ 2 ≠ 1 := fun h => hwZ ((hsq w hw).mp h)
  exact hfix _ (hsqmem w hw) hw2 hsq'

theorem conj_ne_conj_of_fixedPointFree {m : G}
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hcomm : (Subgroup.center S).map S.subtype = ⁅S, S⁆)
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → m * z * m⁻¹ ≠ z) {x : G}
    (hx : x ∈ S) (hx1 : x ≠ 1) {s : G} (hs : s ∈ S) : m * x * m⁻¹ ≠ s * x * s⁻¹ := by
  intro heq
  have hcom : m * x * m⁻¹ * x⁻¹ ∈ (Subgroup.center S).map S.subtype := by
    rw [heq, hcomm]
    have := Subgroup.commutator_mem_commutator hs hx
    rwa [commutatorElement_def] at this
  have hxZ := mem_center_of_conj_mul_inv_mem hsq hsqmem hfix hx hcom
  have hsx : s * x * s⁻¹ = x := by
    rw [(mem_map_center_iff.mp hxZ).2 s hs, mul_inv_cancel_right]
  exact hfix x hxZ hx1 (heq.trans hsx)

theorem isConj_iff_exists_pow {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    (hgen : ∀ m ∈ Subgroup.normalizer (S : Set G), ∃ j : ℕ, j < 3 ∧ (n ^ j)⁻¹ * m ∈ innerActing S)
    (hfusion : ∀ P : Subgroup G, P ≤ S → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ m ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ P, m⁻¹ * x * m = g⁻¹ * x * g)
    {x : G} (hx : x ∈ S) {y : G} (hy : y ∈ S) :
    IsConj x y ↔ ∃ j : ℕ, j < 3 ∧ ∃ s ∈ S, y = s * ((n ^ j)⁻¹ * x * n ^ j) * s⁻¹ := by
  constructor
  · intro hxy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hP : Subgroup.zpowers x ≤ S := (Subgroup.zpowers_le).mpr hx
    have hmap : (Subgroup.zpowers x).map (MulAut.conj c⁻¹⁻¹).toMonoidHom ≤ S := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, map_zpow]
      have : c * x * c⁻¹ ∈ S := hc ▸ hy
      exact S.zpow_mem this k
    obtain ⟨m, hm, hmx⟩ := hfusion _ hP c⁻¹ hmap
    have hmx' : m⁻¹ * x * m = y := by
      rw [hmx x (Subgroup.mem_zpowers x), inv_inv, hc]
    obtain ⟨j, hj, s, hs, hk⟩ := hgen m hm
    refine ⟨j, hj, s⁻¹, S.inv_mem hs, ?_⟩
    have hw : (n ^ j)⁻¹ * x * n ^ j ∈ S :=
      conj_mem_of_mem_normalizer (Subgroup.pow_mem _ hn j) hx
    have h := hk _ hw
    rw [← hmx']
    calc m⁻¹ * x * m = ((n ^ j)⁻¹ * m)⁻¹ * ((n ^ j)⁻¹ * x * n ^ j) * ((n ^ j)⁻¹ * m) := by group
      _ = s⁻¹ * ((n ^ j)⁻¹ * x * n ^ j) * s := h
      _ = s⁻¹ * ((n ^ j)⁻¹ * x * n ^ j) * s⁻¹⁻¹ := by rw [inv_inv]
  · rintro ⟨j, -, s, hs, rfl⟩
    exact isConj_iff.mpr ⟨s * (n ^ j)⁻¹, by group⟩

theorem conj_pow_ne_conj_pow {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hcomm : (Subgroup.center S).map S.subtype = ⁅S, S⁆)
    (hfix : ∀ j : ℕ, 0 < j → j < 3 → ∀ z ∈ (Subgroup.center S).map S.subtype,
      z ≠ 1 → n ^ j * z * (n ^ j)⁻¹ ≠ z)
    {x : G} (hx : x ∈ S) (hx1 : x ≠ 1) {i j : ℕ} (hij : i < j) (hj : j < 3) {s : G}
    (hs : s ∈ S) : (n ^ j)⁻¹ * x * n ^ j ≠ s * ((n ^ i)⁻¹ * x * n ^ i) * s⁻¹ := by
  intro heq
  set d := j - i with hd
  have hjd : j = i + d := by omega
  have hfix' : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 →
      (n ^ d)⁻¹ * z * (n ^ d)⁻¹⁻¹ ≠ z := by
    intro z hz hz1 h
    apply hfix d (by omega) (by omega) z hz hz1
    calc n ^ d * z * (n ^ d)⁻¹ = n ^ d * ((n ^ d)⁻¹ * z * (n ^ d)⁻¹⁻¹) * (n ^ d)⁻¹ := by
          rw [h]
      _ = z := by group
  have hs' : n ^ i * s * (n ^ i)⁻¹ ∈ S := conj_mem_of_mem_normalizer' (Subgroup.pow_mem _ hn i) hs
  apply conj_ne_conj_of_fixedPointFree hsq hsqmem hcomm hfix' hx hx1 hs'
  calc (n ^ d)⁻¹ * x * (n ^ d)⁻¹⁻¹ = n ^ i * ((n ^ j)⁻¹ * x * n ^ j) * (n ^ i)⁻¹ := by
        rw [hjd, pow_add]; group
    _ = n ^ i * (s * ((n ^ i)⁻¹ * x * n ^ i) * s⁻¹) * (n ^ i)⁻¹ := by rw [heq]
    _ = n ^ i * s * (n ^ i)⁻¹ * x * (n ^ i * s * (n ^ i)⁻¹)⁻¹ := by group

end Classes

section FixedCharacters

theorem monoidHom_eq_one_of_fixedPointFree {A M : Type*} [Group A] [Finite A] [Monoid M]
    (β : A →* A) (hβ : ∀ a, β a = a → a = 1) (f : A →* M) (hf : ∀ a, f (β a) = f a) :
    f = 1 := by
  have hinj : Function.Injective (fun a => β a * a⁻¹) := by
    intro a b hab
    simp only at hab
    have h1 : β (b⁻¹ * a) = b⁻¹ * a := by
      rw [map_mul, map_inv]
      calc (β b)⁻¹ * β a = (β b)⁻¹ * (β a * a⁻¹) * a := by group
        _ = (β b)⁻¹ * (β b * b⁻¹) * a := by rw [hab]
        _ = b⁻¹ * a := by group
    have h2 := hβ _ h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  ext c
  obtain ⟨a, rfl⟩ := hsurj c
  show f (β a * a⁻¹) = 1
  rw [map_mul, hf, ← map_mul, mul_inv_cancel, map_one]

variable {S : Type} [Group S]

theorem UnitaryFourSylowShape.mem_center_of_mul_inv_mem (h : UnitaryFourSylowShape S)
    (φ : S →* S) (hφ : ∀ z ∈ Subgroup.center S, φ z = z → z = 1) {x : S}
    (hx : φ x * x⁻¹ ∈ Subgroup.center S) : x ∈ Subgroup.center S := by
  by_contra hxZ
  set z := φ x * x⁻¹ with hzdef
  have hzx : x * z = z * x := Subgroup.mem_center_iff.mp hx x
  have hz2 : z ^ 2 = 1 := (h.sq_eq_one_iff z).mpr hx
  have hφx : φ x = z * x := by rw [hzdef]; group
  have hsq : φ (x ^ 2) = x ^ 2 := by
    rw [map_pow, hφx, pow_two, pow_two]
    calc z * x * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [hzx]
      _ = z ^ 2 * (x * x) := by rw [pow_two]; group
      _ = x * x := by rw [hz2, one_mul]
  have hx2 : x ^ 2 ≠ 1 := fun h' => hxZ ((h.sq_eq_one_iff x).mp h')
  exact hx2 (hφ _ (h.sq_mem_center x) hsq)

theorem UnitaryFourSylowShape.eq_one_of_fixed (h : UnitaryFourSylowShape S) (φ : S →* S)
    (hφ : ∀ z ∈ Subgroup.center S, φ z = z → z = 1) {x : S} (hx : φ x = x) : x = 1 := by
  have hmem : φ x * x⁻¹ ∈ Subgroup.center S := by rw [hx, mul_inv_cancel]; exact one_mem _
  exact hφ x (h.mem_center_of_mul_inv_mem φ hφ hmem) hx

theorem mulEquiv_mem_center {A : Type*} [Group A] (φ : A ≃* A) {z : A}
    (hz : z ∈ Subgroup.center A) : φ z ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g]

variable [Finite S]

theorem UnitaryFourSylowShape.linear_comp_ne (h : UnitaryFourSylowShape S) (φ : S ≃* S)
    (hφ : ∀ z ∈ Subgroup.center S, φ z = z → z = 1) {χ : S → ℂ} (hχ : χ ∈ CFSG.BlocksIrr S)
    (h1 : χ 1 = 1) (hne : χ ≠ 1) : χ ∘ φ ≠ χ := by
  let := Fintype.ofFinite S
  obtain ⟨hlin, -⟩ := h.character_table
  have hmem : χ ∈ {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} := ⟨hχ, h1⟩
  rw [hlin] at hmem
  obtain ⟨l, rfl⟩ := hmem
  intro hfix
  apply hne
  have htriv := monoidHom_eq_one_of_fixedPointFree φ.toMonoidHom
    (fun x hx => h.eq_one_of_fixed φ.toMonoidHom hφ hx) (inflateSign (Subgroup.center S) l)
    (fun a => congrFun hfix a)
  funext s
  have := congrArg (fun f : S →* ℂ => f s) htriv
  simpa [inflateSign_apply] using this

theorem UnitaryFourSylowShape.degree_four_comp_ne (h : UnitaryFourSylowShape S) (φ : S ≃* S)
    (hφ : ∀ z ∈ Subgroup.center S, φ z = z → z = 1) {ψ : S → ℂ} (hψ : ψ ∈ CFSG.BlocksIrr S)
    (h4 : ψ 1 = 4) : ψ ∘ φ ≠ ψ := by
  let := Fintype.ofFinite S
  obtain ⟨-, -, -, -, -, -, hcases, -⟩ := h.character_table
  rcases hcases ψ hψ with h1 | ⟨l, hl1, hl⟩
  · rw [h4] at h1; norm_num at h1
  intro hfix
  apply hl1
  let β : Subgroup.center S →* Subgroup.center S :=
    { toFun := fun z => ⟨φ z, mulEquiv_mem_center φ z.property⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  refine monoidHom_eq_one_of_fixedPointFree β (fun z hz => ?_) l (fun z => ?_)
  · have h' : φ z = z := congrArg Subtype.val hz
    exact Subtype.ext (hφ z z.property h')
  · have h1 := hl (β z)
    have h2 := hl z
    have h3 : ψ (φ z) = ψ z := congrFun hfix z
    change ψ (φ z) = ψ 1 * _ at h1
    rw [h3, h2, h4] at h1
    have h5 : (((l z : ℤˣ) : ℤ) : ℂ) = (((l (β z) : ℤˣ) : ℤ) : ℂ) := by
      linear_combination h1 / 4
    have h6 : ((l z : ℤˣ) : ℤ) = ((l (β z) : ℤˣ) : ℤ) := by exact_mod_cast h5
    exact (Units.ext h6).symm

end FixedCharacters

end CFSG.LyonsUnitaryFour
