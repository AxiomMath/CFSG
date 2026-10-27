module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverRoots
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley.G2FieldFour CFSG.LocalAnalysis.ComponentInitial
open Subgroup
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

abbrev weylX
    (i : Fin Tag.G2.rank) : adjointGroup .G2 K :=
  ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup _ _⟩

abbrev torusXi
    (i : Fin Tag.G2.rank) (t : Kˣ) : adjointGroup .G2 K :=
  ⟨torusElt .G2 K i t, torusElt_mem_adjointGroup _ _⟩

theorem weylX_conj
    (i : Fin Tag.G2.rank) {d d' : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d)
    (hdd' : reflect .G2 i d = d') (x : K) :
    weylX i * rootX d x * (weylX i)⁻¹ = rootX d' x :=
  Subtype.ext (by
    change weylElt .G2 K i 1 * X d x * (weylElt .G2 K i 1)⁻¹ = X d' x
    rw [weylElt_conj i hd, hdd'])

theorem weylX_mul_self
    (i : Fin Tag.G2.rank) : weylX (K := K) i * weylX i = 1 :=
  Subtype.ext (weylElt_mul_self i)

omit [CharP K 2] in
theorem torusXi_conj
    (i : Fin Tag.G2.rank) {d : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d)
    (t : Kˣ) {m : ℤ} (hm : ∑ j, Tag.G2.cartan i j * d j = m) (x : K) :
    torusXi i t * rootX d x * (torusXi i t)⁻¹ = rootX d (((t ^ m : Kˣ) : K) * x) :=
  Subtype.ext (by
    change torusElt .G2 K i t * X d x * (torusElt .G2 K i t)⁻¹ = X d _
    rw [root_torus_conjugation i hd t x, hm])

omit [CharP K 2] in
theorem torusXi_comm
    (i j : Fin Tag.G2.rank) (t u : Kˣ) :
    torusXi (K := K) i t * torusXi j u = torusXi j u * torusXi i t :=
  Subtype.ext (torusElt_mul_comm i j t u)

omit [CharP K 2] in
theorem weylX_conj_torus_comm
    (t u : Kˣ) :
    weylX g2ir * torusXi g2ia t * (weylX g2ir)⁻¹ * torusXi g2ia u =
      torusXi g2ia u * (weylX g2ir * torusXi g2ia t * (weylX g2ir)⁻¹) := by
  have h : weylX (K := K) g2ir * torusXi g2ia t * (weylX g2ir)⁻¹ =
      torusXi g2ia t * torusXi g2ir (t ^ (-Tag.G2.cartan g2ia g2ir)) :=
    Subtype.ext (by
      change weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia t * (weylElt .G2 K g2ir 1)⁻¹ = _
      rw [weylElt_mul_torusElt, mul_inv_cancel_right]
      rfl)
  rw [h, mul_assoc, torusXi_comm g2ir g2ia, ← mul_assoc, torusXi_comm g2ia g2ia, mul_assoc]

theorem mul_mul_mul_of_mem_center {G : Type*} [Group G] {u : G} (hu : u ∈ center G)
    (a b v : G) : a * u * (b * v) = a * b * (u * v) := by
  calc a * u * (b * v) = a * (u * b) * v := by group
    _ = a * (b * u) * v := by rw [← mem_center_iff.1 hu b]
    _ = a * b * (u * v) := by group

variable {M : Type*} [Group M] {π : M →* adjointGroup .G2 K} {z : M}

theorem exists_canonical_lifts
    (hK : Nat.card K = 4) (hπ : Function.Surjective π)
    (hker : ∀ k, π k = 1 → k ∈ center M) (hz1 : z ≠ 1) (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z) :
    ∃ C : K → M, (∀ s, π (C s) = rootX rootC s) ∧ (∀ s s', C (s + s') = C s * C s') ∧
      (∀ e e' : M, π e = rootX rootA 1 → π e' = rootX rootB 1 → ⁅e, e'⁆ = C 1) ∧
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) → ∀ κ : M ≃* M,
        (∀ m, (π (κ m) : ModGL .G2 K) = Units.map (entrywiseHom σ.toRingHom) (π m)) →
        (∀ m, κ (κ m) = m) → ∀ s, κ (C s) = C (s ^ 2) := by
  obtain ⟨ω, hω1, hω21, hωsq⟩ := exists_unit_ne_one (K := K) hK
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hω3 : (ω : K) ^ 3 = 1 := by
    linear_combination ((ω : K) - 1) * hωsq
  have hωinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination hω3)
  set t₀ := torusXi (K := K) g2ia ω with ht₀
  have hta : ∀ x : K, t₀ * rootX rootA x * t₀⁻¹ = rootX rootA (((ω ^ (2 : ℤ) : Kˣ) : K) * x) :=
    torusXi_conj g2ia isRoot_g2a ω (m := 2) (by decide)
  have htb : ∀ x : K, t₀ * rootX rootB x * t₀⁻¹ = rootX rootB (((ω ^ (-1 : ℤ) : Kˣ) : K) * x) :=
    torusXi_conj g2ia isRoot_g2b ω (m := -1) (by decide)
  have htc : ∀ x : K, t₀ * rootX rootC x * t₀⁻¹ = rootX rootC (((ω ^ (1 : ℤ) : Kˣ) : K) * x) :=
    torusXi_conj g2ia isRoot_g2c ω (m := 1) (by decide)
  have hr2 : ((ω ^ (2 : ℤ) : Kˣ) : K) = (ω : K) ^ 2 := by rw [zpow_ofNat, Units.val_pow_eq_pow_val]
  have hrm1 : ((ω ^ (-1 : ℤ) : Kˣ) : K) = (ω : K) ^ 2 := by rw [zpow_neg_one, hωinv]
  have hr1 : ((ω ^ (1 : ℤ) : Kˣ) : K) = (ω : K) := by rw [zpow_one]
  obtain ⟨A, hAπ, hAadd, hAeq⟩ := LinearCover.exists_torus_lift π hker hπ (x := rootX rootA)
    (rootX_add rootA) (fun e e' a b he he' => lift_commute_a hπ hker he he')
    (by rw [hr2]; exact hω21) hta
  obtain ⟨B, hBπ, hBadd, hBeq⟩ := LinearCover.exists_torus_lift π hker hπ (x := rootX rootB)
    (rootX_add rootB) (fun e e' a b he he' => lift_commute_b hπ hker he he')
    (by rw [hrm1]; exact hω21) htb
  obtain ⟨C, hCπ, hCadd, hCeq⟩ := LinearCover.exists_torus_lift π hker hπ (x := rootX rootC)
    (rootX_add rootC) (fun e e' a b he he' => lift_commute_c hπ hker he he')
    (by rw [hr1]; exact hω1) htc
  obtain ⟨g₀, hg₀⟩ := hπ t₀
  have hg₀B : ∀ a, g₀ * B a * g₀⁻¹ = B ((ω : K) ^ 2 * a) := fun a => by
    rw [← hrm1]; exact hBeq g₀ _ (by rw [hg₀]) (by rw [hg₀]; exact htb) a
  have hg₀C : ∀ a, g₀ * C a * g₀⁻¹ = C ((ω : K) * a) := fun a => by
    rw [← hr1]; exact hCeq g₀ _ (by rw [hg₀]) (by rw [hg₀]; exact htc) a
  have hzsq : z * z = 1 := mul_self_z hz1 hz
  have hsq_ker : ∀ k : M, π k = 1 → k * k = 1 := fun k hk => by
    rcases (hz k).1 hk with h | h
    · rw [h, mul_one]
    · rw [h, hzsq]
  let f : K → K → M := fun s s' => (C (s * s'))⁻¹ * ⁅A s, B s'⁆
  have hπcomm : ∀ s s', π ⁅A s, B s'⁆ = rootX rootC (s * s') := fun s s' => by
    rw [map_commutatorElement, hAπ, hBπ, commutator_rootX_ab]
  have hfker : ∀ s s', π (f s s') = 1 := fun s s' => by
    simp only [f, map_mul, map_inv, hCπ, hπcomm, inv_mul_cancel]
  have hfc : ∀ s s', f s s' ∈ center M := fun s s' => hker _ (hfker s s')
  have hf2 : ∀ s s', f s s' * f s s' = 1 := fun s s' => hsq_ker _ (hfker s s')
  have hcomm_eq : ∀ s s', ⁅A s, B s'⁆ = C (s * s') * f s s' := fun s s' => by
    simp only [f, mul_inv_cancel_left]
  have hC0 : C 0 = 1 := by
    have h := hCadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hC2 : ∀ s, C s * C s = 1 := fun s => by
    rw [← hCadd, CharTwo.add_self_eq_zero, hC0]
  have hf_add_left : ∀ s₁ s₂ s', f (s₁ + s₂) s' = f s₁ s' * f s₂ s' := by
    intro s₁ s₂ s'
    have h1 : ⁅A (s₁ + s₂), B s'⁆ = A s₁ * ⁅A s₂, B s'⁆ * (A s₁)⁻¹ * ⁅A s₁, B s'⁆ := by
      rw [hAadd]; simp only [commutatorElement_def]; group
    have h2 : A s₁ * ⁅A s₂, B s'⁆ * (A s₁)⁻¹ = ⁅A s₂, B s'⁆ := by
      rw [lift_commute_a_c hπ hker (hAπ s₁) (hπcomm s₂ s'), mul_inv_cancel_right]
    have key : ⁅A (s₁ + s₂), B s'⁆ = C ((s₁ + s₂) * s') * (f s₂ s' * f s₁ s') := by
      rw [h1, h2, hcomm_eq s₂ s', hcomm_eq s₁ s', mul_mul_mul_of_mem_center (hfc s₂ s'), ← hCadd,
        show s₂ * s' + s₁ * s' = (s₁ + s₂) * s' by ring]
    change (C ((s₁ + s₂) * s'))⁻¹ * ⁅A (s₁ + s₂), B s'⁆ = f s₁ s' * f s₂ s'
    rw [key, inv_mul_cancel_left]
    exact (mem_center_iff.1 (hfc s₂ s') (f s₁ s')).symm
  have hf_add_right : ∀ s s₁ s₂, f s (s₁ + s₂) = f s s₁ * f s s₂ := by
    intro s s₁ s₂
    have h1 : ⁅A s, B (s₁ + s₂)⁆ = ⁅A s, B s₁⁆ * (B s₁ * ⁅A s, B s₂⁆ * (B s₁)⁻¹) := by
      rw [hBadd]; simp only [commutatorElement_def]; group
    have h2 : B s₁ * ⁅A s, B s₂⁆ * (B s₁)⁻¹ = ⁅A s, B s₂⁆ := by
      rw [lift_commute_b_c hπ hker (hBπ s₁) (hπcomm s s₂), mul_inv_cancel_right]
    have key : ⁅A s, B (s₁ + s₂)⁆ = C (s * (s₁ + s₂)) * (f s s₁ * f s s₂) := by
      rw [h1, h2, hcomm_eq s s₁, hcomm_eq s s₂, mul_mul_mul_of_mem_center (hfc s s₁), ← hCadd,
        show s * s₁ + s * s₂ = s * (s₁ + s₂) by ring]
    change (C (s * (s₁ + s₂)))⁻¹ * ⁅A s, B (s₁ + s₂)⁆ = f s s₁ * f s s₂
    rw [key, inv_mul_cancel_left]
  have hf_torus : ∀ (l : Kˣ) (s s' : K),
      f (((l ^ (2 : ℤ) : Kˣ) : K) * s) (((l ^ (-1 : ℤ) : Kˣ) : K) * s') = f s s' := by
    intro l s s'
    obtain ⟨g, hg⟩ := hπ (torusXi g2ia l)
    have hgt : π g * t₀ = t₀ * π g := by rw [hg, ht₀]; exact torusXi_comm g2ia g2ia l ω
    have hgA := hAeq g _ hgt (by rw [hg]; exact torusXi_conj g2ia isRoot_g2a l (m := 2) (by decide))
    have hgB := hBeq g _ hgt (by
      rw [hg]; exact torusXi_conj g2ia isRoot_g2b l (m := -1) (by decide))
    have hgC := hCeq g _ hgt (by rw [hg]; exact torusXi_conj g2ia isRoot_g2c l (m := 1) (by decide))
    have h1 : g * f s s' * g⁻¹ = f s s' := by
      rw [mem_center_iff.1 (hfc s s') g, mul_inv_cancel_right]
    have h2 : g * f s s' * g⁻¹ = (C (((l ^ (1 : ℤ) : Kˣ) : K) * (s * s')))⁻¹ *
        ⁅A (((l ^ (2 : ℤ) : Kˣ) : K) * s), B (((l ^ (-1 : ℤ) : Kˣ) : K) * s')⁆ := by
      rw [← hgC, ← hgA, ← hgB]
      change g * ((C (s * s'))⁻¹ * ⁅A s, B s'⁆) * g⁻¹ = _
      simp only [commutatorElement_def]
      group
    have hl0 : (l : K) ≠ 0 := l.ne_zero
    have h3 : ((l ^ (1 : ℤ) : Kˣ) : K) * (s * s') =
        ((l ^ (2 : ℤ) : Kˣ) : K) * s * (((l ^ (-1 : ℤ) : Kˣ) : K) * s') := by
      rw [zpow_one, zpow_neg_one, zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      have h4 : (l : K) ^ 2 * s * ((l : K)⁻¹ * s') =
          (l : K) * (s * s') * ((l : K) * (l : K)⁻¹) := by
        ring
      rw [h4, mul_inv_cancel₀ hl0, mul_one]
    rw [h3] at h2
    exact h2.symm.trans h1
  obtain ⟨n, hn⟩ := hπ (weylX g2ir)
  have hna : ∀ x : K, weylX g2ir * rootX rootA x * (weylX g2ir)⁻¹ = rootX rootB x :=
    weylX_conj g2ir isRoot_g2a reflect_r_a
  have hnb : ∀ x : K, weylX g2ir * rootX rootB x * (weylX g2ir)⁻¹ = rootX rootA x :=
    weylX_conj g2ir isRoot_g2b reflect_r_b
  have hnc : ∀ x : K, weylX g2ir * rootX rootC x * (weylX g2ir)⁻¹ = rootX rootC x :=
    weylX_conj g2ir isRoot_g2c reflect_r_c
  have hnbA : ∀ x : K, (weylX g2ir)⁻¹ * rootX rootB x * weylX g2ir = rootX rootA x :=
    fun x => by rw [← hna x]; group
  have hninv : (weylX (K := K) g2ir)⁻¹ = weylX g2ir :=
    inv_eq_of_mul_eq_one_right (weylX_mul_self g2ir)
  have hncC : ∀ x : K, (weylX g2ir)⁻¹ * rootX rootC x * weylX g2ir = rootX rootC x :=
    fun x => by
      have h := hnc x
      rw [hninv] at h ⊢
      exact h
  set g' := n⁻¹ * g₀ * n with hg'
  have hπg' : π g' = (weylX g2ir)⁻¹ * t₀ * weylX g2ir := by
    rw [hg', map_mul, map_mul, map_inv, hn, hg₀]
  have hg't : π g' * t₀ = t₀ * π g' := by
    have h := weylX_conj_torus_comm (K := K) ω ω
    rw [hninv] at h
    rw [hπg', hninv, ht₀]
    exact h
  have hg'A : ∀ a, g' * A a * g'⁻¹ = A ((ω : K) ^ 2 * a) := by
    refine hAeq g' _ hg't fun x => ?_
    rw [hπg', show (weylX g2ir)⁻¹ * t₀ * weylX g2ir * rootX rootA x *
        ((weylX g2ir)⁻¹ * t₀ * weylX g2ir)⁻¹ =
      (weylX g2ir)⁻¹ * (t₀ * (weylX g2ir * rootX rootA x * (weylX g2ir)⁻¹) * t₀⁻¹) *
        weylX g2ir by group, hna, htb, hrm1, hnbA]
  have hg'C : ∀ a, g' * C a * g'⁻¹ = C ((ω : K) * a) := by
    refine hCeq g' _ hg't fun x => ?_
    rw [hπg', show (weylX g2ir)⁻¹ * t₀ * weylX g2ir * rootX rootC x *
        ((weylX g2ir)⁻¹ * t₀ * weylX g2ir)⁻¹ =
      (weylX g2ir)⁻¹ * (t₀ * (weylX g2ir * rootX rootC x * (weylX g2ir)⁻¹) * t₀⁻¹) *
        weylX g2ir by group, hnc, htc, hr1, hncC]
  have hnA : ∀ a, n * A a * n⁻¹ = B a := fun a =>
    LinearCover.eq_of_conj_eq_smul π hker (p := fun a => n * A a * n⁻¹) (q := B) (g := g₀)
      (fun a b => by simp only [hAadd]; group) hBadd
      (fun a => by simp only [map_mul, map_inv, hn, hAπ, hBπ, hna]) hω21
      (fun a => by
        show g₀ * (n * A a * n⁻¹) * g₀⁻¹ = n * A ((ω : K) ^ 2 * a) * n⁻¹
        rw [← hg'A, hg']
        group)
      hg₀B a
  have hnC : ∀ a, n * C a * n⁻¹ = C a := fun a =>
    LinearCover.eq_of_conj_eq_smul π hker (p := fun a => n * C a * n⁻¹) (q := C) (g := g₀)
      (fun a b => by simp only [hCadd]; group) hCadd
      (fun a => by simp only [map_mul, map_inv, hn, hCπ, hnc]) hω1
      (fun a => by
        show g₀ * (n * C a * n⁻¹) * g₀⁻¹ = n * C ((ω : K) * a) * n⁻¹
        rw [← hg'C, hg']
        group)
      hg₀C a
  have hn2 : n * n ∈ center M := hker _ (by rw [map_mul, hn, weylX_mul_self])
  have hnB : ∀ a, n * B a * n⁻¹ = A a := fun a => by
    rw [← hnA a, show n * (n * A a * n⁻¹) * n⁻¹ = (n * n) * A a * (n * n)⁻¹ by group,
      ← mem_center_iff.1 hn2 (A a), mul_inv_cancel_right]
  have hf_symm : ∀ s s', f s s' = f s' s := by
    intro s s'
    have h1 : n * f s s' * n⁻¹ = f s s' := by
      rw [mem_center_iff.1 (hfc s s') n, mul_inv_cancel_right]
    have h2 : n * f s s' * n⁻¹ = (C (s * s'))⁻¹ * ⁅B s, A s'⁆ := by
      calc n * f s s' * n⁻¹ = (n * C (s * s') * n⁻¹)⁻¹ * ⁅n * A s * n⁻¹, n * B s' * n⁻¹⁆ := by
            change n * ((C (s * s'))⁻¹ * ⁅A s, B s'⁆) * n⁻¹ = _
            simp only [commutatorElement_def]
            group
        _ = (C (s * s'))⁻¹ * ⁅B s, A s'⁆ := by rw [hnA, hnB, hnC]
    have h3 : ⁅B s, A s'⁆ = (f s' s)⁻¹ * (C (s * s'))⁻¹ := by
      rw [← commutatorElement_inv, hcomm_eq, mul_inv_rev, mul_comm s' s]
    have hinv : (f s' s)⁻¹ = f s' s := inv_eq_of_mul_eq_one_right (hf2 s' s)
    have hCinv : (C (s * s'))⁻¹ = C (s * s') := inv_eq_of_mul_eq_one_right (hC2 _)
    rw [← h1, h2, h3, hinv, hCinv, ← mul_assoc, mem_center_iff.1 (hfc s' s) (C (s * s')),
      mul_assoc, hC2, mul_one]
  have h1ω : (1 : K) = ω + (ω : K) ^ 2 := by
    linear_combination -hωsq + CharTwo.two_eq_zero (R := K)
  have hfω : f ω ω = f 1 1 := by
    have h := hf_torus (ω ^ 2) 1 1
    rw [show (((ω ^ 2) ^ (2 : ℤ) : Kˣ) : K) * 1 = ω by
        rw [mul_one, zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
        linear_combination (ω : K) * hω3,
      show (((ω ^ 2) ^ (-1 : ℤ) : Kˣ) : K) * 1 = ω by
        rw [mul_one, zpow_neg_one, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        exact inv_eq_of_mul_eq_one_right (by linear_combination hω3)] at h
    exact h
  have hfω2 : f ((ω : K) ^ 2) ((ω : K) ^ 2) = f 1 1 := by
    have h := hf_torus ω 1 1
    rw [mul_one, mul_one, hr2, hrm1] at h
    exact h
  have hf11 : f 1 1 = 1 := by
    have h : f 1 1 = f 1 1 * f ω ((ω : K) ^ 2) * (f ω ((ω : K) ^ 2) * f 1 1) := by
      conv_lhs => rw [h1ω]
      rw [hf_add_left, hf_add_right, hf_add_right, hfω, hfω2, hf_symm ((ω : K) ^ 2) (ω : K)]
    rw [show f 1 1 * f ω ((ω : K) ^ 2) * (f ω ((ω : K) ^ 2) * f 1 1) =
      f 1 1 * (f ω ((ω : K) ^ 2) * f ω ((ω : K) ^ 2)) * f 1 1 by group, hf2, mul_one, hf2] at h
    exact h
  refine ⟨C, hCπ, hCadd, fun e e' he he' => ?_, ?_⟩
  ·
    rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq π hker
      (he.trans (hAπ 1).symm) (he'.trans (hBπ 1).symm), hcomm_eq, mul_one, hf11, mul_one]
  ·
    intro σ hσ κ hκ hκ2 s
    have hσω : σ ω = (ω : K) ^ 2 := hσ ω
    obtain ⟨ν, hν⟩ : ∃ ν : Kˣ, (ν : K) = (ω : K) ^ 2 :=
      ⟨⟨(ω : K) ^ 2, ω, by linear_combination hω3, by linear_combination hω3⟩, rfl⟩
    have hπκ : ∀ m x, π m = rootX rootC x → π (κ m) = rootX rootC (x ^ 2) := fun m x hm =>
      Subtype.ext (by rw [hκ, hm, coe_rootX, units_map_entrywise_pinnedX, hσ]; rfl)
    have hg'' : π (κ g₀) = torusXi g2ia ν := Subtype.ext (by
      rw [hκ, hg₀, ht₀]
      change Units.map (entrywiseHom σ.toRingHom) (torusElt .G2 K g2ia ω) =
        torusElt .G2 K g2ia ν
      rw [entrywise_torusElt]
      congr 1
      exact Units.ext (by rw [Units.coe_map, hν]; exact hσω))
    have hκg : ∀ a, κ g₀ * C a * (κ g₀)⁻¹ = C ((ω : K) ^ 2 * a) := by
      have h := hCeq (κ g₀) _ (by rw [hg'', ht₀]; exact torusXi_comm g2ia g2ia ν ω)
        (by rw [hg'']; exact torusXi_conj g2ia isRoot_g2c ν (m := 1) (by decide))
      intro a
      rw [h a, zpow_one, hν]
    have hpadd : ∀ a b, κ (C (a + b)) = κ (C a) * κ (C b) := fun a b => by rw [hCadd, map_mul]
    have hqadd : ∀ a b, C ((a + b) ^ 2) = C (a ^ 2) * C (b ^ 2) := fun a b => by
      rw [CharTwo.add_sq, hCadd]
    have hgq : ∀ a, g₀ * C (a ^ 2) * g₀⁻¹ = C (((ω : K) ^ 2 * a) ^ 2) := fun a => by
      rw [hg₀C]
      congr 1
      linear_combination (-(ω : K) * a ^ 2) * hω3
    have hgp : ∀ a, g₀ * κ (C a) * g₀⁻¹ = κ (C ((ω : K) ^ 2 * a)) := fun a => by
      rw [← hκg a, map_mul, map_mul, map_inv, hκ2]
    exact LinearCover.eq_of_conj_eq_smul π hker (p := fun a => κ (C a))
      (q := fun a => C (a ^ 2)) (g := g₀) hpadd hqadd
      (fun a => by rw [hπκ (C a) a (hCπ a), hCπ]) hω21 hgp hgq s

end CFSG.EvenSmallLie.GTwoFour
