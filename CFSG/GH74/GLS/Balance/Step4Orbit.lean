module

public import CFSG.GH74.GLS.Balance.Step4Basic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace Step4

section Generic

variable {X : Type} [Group X]

theorem cj_pow_eq_self {g : X} {K : Subgroup X} (h : cj g K = K) (n : ℕ) : cj (g ^ n) K = K := by
  induction n with
  | zero => rw [pow_zero, cj_one]
  | succ n ih => rw [pow_succ', cj_mul, ih, h]

theorem conj_mem_centralizer_cj {g z : X} {K : Subgroup X} (hz : z ∈ centralizer (K : Set X)) :
    g * z * g⁻¹ ∈ centralizer ((cj g K : Subgroup X) : Set X) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hk : g⁻¹ * y * g ∈ K := mem_cj.mp hy
  have h := mem_centralizer_iff.mp hz _ hk
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * y := by group

theorem mem_centralizer_cj {g p : X} {K : Subgroup X} (h : g⁻¹ * p * g ∈ centralizer (K : Set X)) :
    p ∈ centralizer ((cj g K : Subgroup X) : Set X) := by
  have := conj_mem_centralizer_cj (g := g) h
  have e : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
  rwa [e] at this

theorem conj_mem_inf_centralizer {L K : Subgroup X} {g b : X} (hgL : g ∈ normalizer (L : Set X))
    (hgK : g ∈ normalizer (K : Set X)) (hb : b ∈ L ⊓ centralizer (K : Set X)) :
    g * b * g⁻¹ ∈ L ⊓ centralizer (K : Set X) := by
  refine ⟨(mem_normalizer_iff.mp hgL b).mp hb.1, ?_⟩
  have h1 := conj_mem_centralizer_cj (g := g) hb.2
  rwa [mem_normalizer_iff_cj_eq.mp hgK] at h1

theorem part_central {P L K₀ : Subgroup X} {u a b : X} (hu : u ∈ centralizer (P : Set X))
    (huL : u ∈ normalizer (L : Set X)) (huK : u ∈ normalizer (K₀ : Set X)) (ha : a ∈ K₀)
    (hb : b ∈ L ⊓ centralizer (K₀ : Set X)) (hab : a * b ∈ P) :
    a⁻¹ * (u * a * u⁻¹) ∈ K₀ ⊓ centralizer (K₀ : Set X) := by
  have hub : u * b * u⁻¹ ∈ L ⊓ centralizer (K₀ : Set X) := conj_mem_inf_centralizer huL huK hb
  have hcomm : Commute u (a * b) := (mem_centralizer_iff.mp hu _ hab).symm
  have h1 : u * a * u⁻¹ = a * b * (u * b * u⁻¹)⁻¹ := by
    calc u * a * u⁻¹ = (u * (a * b) * u⁻¹) * (u * b * u⁻¹)⁻¹ := by group
      _ = a * b * (u * b * u⁻¹)⁻¹ := by rw [hcomm.mul_inv_cancel]
  have h2 : a⁻¹ * (u * a * u⁻¹) = b * (u * b * u⁻¹)⁻¹ := by
    rw [h1]
    group
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact K₀.mul_mem (K₀.inv_mem ha) ((mem_normalizer_iff.mp huK a).mp ha)
  · rw [h2]
    exact (centralizer (K₀ : Set X)).mul_mem (Subgroup.mem_inf.mp hb).2
      ((centralizer (K₀ : Set X)).inv_mem (Subgroup.mem_inf.mp hub).2)

theorem comm_aux {t z : X} (h : t * z = z * t) : t * (t * z) = t * z * t := by
  rw [mul_assoc, h]

@[expose] def conjElt (w a : X) (n : ℕ) : X := w ^ n * a * (w ^ n)⁻¹

theorem conjElt_zero (w a : X) : conjElt w a 0 = a := by simp [conjElt]

theorem conjElt_succ (w a : X) (n : ℕ) : w * conjElt w a n * w⁻¹ = conjElt w a (n + 1) := by
  simp only [conjElt, pow_succ', mul_inv_rev]
  group

theorem conjElt_mem_cj {w a : X} {K : Subgroup X} (ha : a ∈ K) (n : ℕ) :
    conjElt w a n ∈ cj (w ^ n) K :=
  conj_mem_cj ha

theorem conjElt_pow {w a : X} {k : ℕ} (h : a ^ k = 1) (n : ℕ) : conjElt w a n ^ k = 1 := by
  rw [conjElt, conj_pow, h]
  group

theorem conj_conjElt {w x a : X} (h : x * w = w * x) (n : ℕ) :
    x * conjElt w a n * x⁻¹ = conjElt w (x * a * x⁻¹) n := by
  have hc : x * w ^ n = w ^ n * x := ((show Commute x w from h).pow_right n).eq
  unfold conjElt
  calc x * (w ^ n * a * (w ^ n)⁻¹) * x⁻¹ = (x * w ^ n) * a * (x * w ^ n)⁻¹ := by group
    _ = (w ^ n * x) * a * (w ^ n * x)⁻¹ := by rw [hc]
    _ = w ^ n * (x * a * x⁻¹) * (w ^ n)⁻¹ := by group

end Generic

variable {X : Type} [Group X] {x : X} {V : Subgroup X}

structure OrbitHyp (A : SolvAPI x V) (S : Set (Subgroup X)) (K₀ : Subgroup X) : Prop where
  mem : K₀ ∈ S
  comp : ∀ K ∈ S, IsComponent K
  xK : ∀ K ∈ S, x ∈ normalizer (K : Set X)
  wS : ∀ K ∈ S, cj A.w K ∈ S
  orb : ∀ K ∈ S, ∃ n : ℕ, K = cj (A.w ^ n) K₀
  ne : ∃ K ∈ S, K ≠ K₀
  P_le : A.P ≤ compProd S

namespace OrbitHyp

section NoFinite

variable {A : SolvAPI x V} {S : Set (Subgroup X)} {K₀ : Subgroup X}

theorem isComponent_K₀ (H : OrbitHyp A S K₀) : IsComponent K₀ := H.comp K₀ H.mem

theorem cj_w_ne (H : OrbitHyp A S K₀) : cj A.w K₀ ≠ K₀ := by
  intro h
  obtain ⟨K, hK, hne⟩ := H.ne
  obtain ⟨n, rfl⟩ := H.orb K hK
  exact hne (cj_pow_eq_self h n)

theorem three_dvd (H : OrbitHyp A S K₀) {d : ℕ} (h : cj (A.w ^ d) K₀ = K₀) : 3 ∣ d := by
  by_contra h3
  apply H.cj_w_ne
  obtain ⟨k, hk⟩ := A.w_three
  have hcop : Nat.Coprime d (orderOf A.w) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have := cj_pow_eq_self h m
  rwa [hm] at this

theorem pow_mem_centralizer (A : SolvAPI x V) {d : ℕ} (h3 : 3 ∣ d) :
    A.w ^ d ∈ centralizer (A.P : Set X) := by
  obtain ⟨j, rfl⟩ := h3
  have h : A.w ^ 3 ∈ centralizer (A.P : Set X) := by
    rw [mem_centralizer_iff]
    intro p hp
    exact (A.w3 p hp).symm
  rw [pow_mul]
  exact Subgroup.pow_mem _ h j

end NoFinite

section Fin

variable [Finite X] {A : SolvAPI x V} {S : Set (Subgroup X)} {K₀ : Subgroup X}

theorem w_mem_normalizer (H : OrbitHyp A S K₀) : A.w ∈ normalizer (compProd S : Set X) := by
  refine mem_normalizer_compProd fun K hK k hk => ?_
  exact le_compProd (H.wS K hK) (conj_mem_cj hk)

theorem x_mem_normalizer (H : OrbitHyp A S K₀) : x ∈ normalizer (compProd S : Set X) := by
  refine mem_normalizer_compProd fun K hK k hk => ?_
  exact le_compProd hK ((mem_normalizer_iff.mp (H.xK K hK) k).mp hk)

theorem decomp (H : OrbitHyp A S K₀) {g : X} (hg : g ∈ compProd S) :
    ∃ a ∈ K₀, ∃ b ∈ compProd S ⊓ centralizer (K₀ : Set X), g = a * b := by
  have hle : compProd S ≤ K₀ ⊔ (compProd S ⊓ centralizer (K₀ : Set X)) := by
    refine compProd_le fun K hK => ?_
    by_cases hKK : K = K₀
    · rw [hKK]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      refine le_inf (le_compProd hK) ?_
      rcases CFSG.LocalCores.distinct_components_commute (H.comp K hK) H.isComponent_K₀ with h | h
      · exact absurd h hKK
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (H := K₀)
    (K := compProd S ⊓ centralizer (K₀ : Set X))
    (fun a ha b hb => mem_centralizer_iff.mp hb.2 a ha) (hle hg)
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_not_central (H : OrbitHyp A S K₀) : ∃ p ∈ A.P, p ∉ centralizer (K₀ : Set X) := by
  by_contra hcon
  have hP : ∀ p ∈ A.P, p ∈ centralizer (K₀ : Set X) := fun p hp =>
    by_contra fun h => hcon ⟨p, hp, h⟩
  have hcentS : ∀ K ∈ S, ∀ p ∈ A.P, p ∈ centralizer (K : Set X) := by
    intro K hK p hp
    obtain ⟨n, rfl⟩ := H.orb K hK
    have hn : A.w ^ n ∈ normalizer (A.P : Set X) := Subgroup.pow_mem _ A.w_norm n
    refine mem_centralizer_cj (hP _ ?_)
    have h := (mem_normalizer_iff.mp (inv_mem hn) p).mp hp
    simpa using h
  have hPZ : A.P ≤ layerZ X := by
    intro p hp
    rw [mem_layerZ_iff]
    refine ⟨compProd_le_layer H.comp (H.P_le hp), fun K hK => ?_⟩
    by_cases hKS : K ∈ S
    · exact hcentS K hKS p hp
    · exact compProd_le_centralizer H.comp hK hKS (H.P_le hp)
  obtain ⟨a, ha, b, hb, hne⟩ := A.P_nonab
  exact hne (layerZ_comm (hPZ ha) (hPZ hb))

theorem exists_part (H : OrbitHyp A S K₀) (hO : pPrimeCore 2 X = ⊥) :
    ∃ a ∈ K₀, ∃ b ∈ compProd S ⊓ centralizer (K₀ : Set X), a * b ∈ A.P ∧
      a ∉ centralizer (K₀ : Set X) ∧ ∃ m : ℕ, a ^ (2 ^ m) = 1 := by
  obtain ⟨p, hp, hpc⟩ := H.exists_not_central
  obtain ⟨a, ha, b, hb, rfl⟩ := H.decomp (H.P_le hp)
  have hanc : a ∉ centralizer (K₀ : Set X) := fun h => hpc (mul_mem h hb.2)
  have hab : Commute a b := mem_centralizer_iff.mp hb.2 a ha
  obtain ⟨m, hm⟩ := exists_pow_eq_one_of_mem A.P_two hp
  rw [hab.mul_pow] at hm
  have h1 : a ^ (2 ^ m) ∈ layerZ X := by
    have hbm : b ^ (2 ^ m) ∈ compProd S ⊓ centralizer (K₀ : Set X) :=
      Subgroup.pow_mem _ hb _
    have e : a ^ (2 ^ m) = (b ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left hm
    have : a ^ (2 ^ m) ∈ K₀ ⊓ centralizer (K₀ : Set X) :=
      ⟨K₀.pow_mem ha _, by rw [e]; exact (centralizer (K₀ : Set X)).inv_mem hbm.2⟩
    exact inf_centralizer_le_layerZ H.isComponent_K₀ this
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem (layerZ_isPGroup hO) h1
  exact ⟨a, ha, b, hb, hp, hanc, m + j, by rw [pow_add, pow_mul]; exact hj⟩

theorem conjElt_comm_le (H : OrbitHyp A S K₀) {a b : X} (ha : a ∈ K₀)
    (hb : b ∈ compProd S ⊓ centralizer (K₀ : Set X)) (hab : a * b ∈ A.P) {n m : ℕ} (hnm : n ≤ m) :
    conjElt A.w a n * conjElt A.w a m = conjElt A.w a m * conjElt A.w a n := by
  have hKn := isComponent_cj (g := A.w ^ n) H.isComponent_K₀
  have hKm := isComponent_cj (g := A.w ^ m) H.isComponent_K₀
  by_cases hK : cj (A.w ^ n) K₀ = cj (A.w ^ m) K₀
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hd : cj (A.w ^ d) K₀ = K₀ := by
      rw [pow_add, cj_mul] at hK
      exact (cj_injective _ hK).symm
    have huP := pow_mem_centralizer A (H.three_dvd hd)
    have huL : A.w ^ d ∈ normalizer (compProd S : Set X) :=
      Subgroup.pow_mem _ H.w_mem_normalizer d
    have huK : A.w ^ d ∈ normalizer (K₀ : Set X) := mem_normalizer_iff_cj_eq.mpr hd
    have hz := part_central huP huL huK ha hb hab
    have hza : A.w ^ d * a * (A.w ^ d)⁻¹ = a * (a⁻¹ * (A.w ^ d * a * (A.w ^ d)⁻¹)) := by group
    have hz'K : A.w ^ n * (a⁻¹ * (A.w ^ d * a * (A.w ^ d)⁻¹)) * (A.w ^ n)⁻¹ ∈
        cj (A.w ^ n) K₀ := conj_mem_cj hz.1
    have hz'C : A.w ^ n * (a⁻¹ * (A.w ^ d * a * (A.w ^ d)⁻¹)) * (A.w ^ n)⁻¹ ∈
        centralizer ((cj (A.w ^ n) K₀ : Subgroup X) : Set X) := conj_mem_centralizer_cj hz.2
    have htm : conjElt A.w a (n + d) = conjElt A.w a n *
        (A.w ^ n * (a⁻¹ * (A.w ^ d * a * (A.w ^ d)⁻¹)) * (A.w ^ n)⁻¹) := by
      unfold conjElt
      calc A.w ^ (n + d) * a * (A.w ^ (n + d))⁻¹
          = A.w ^ n * (A.w ^ d * a * (A.w ^ d)⁻¹) * (A.w ^ n)⁻¹ := by rw [pow_add]; group
        _ = A.w ^ n * (a * (a⁻¹ * (A.w ^ d * a * (A.w ^ d)⁻¹))) * (A.w ^ n)⁻¹ := by rw [← hza]
        _ = _ := by group
    have hcz := mem_centralizer_iff.mp hz'C _ (conjElt_mem_cj (w := A.w) ha n)
    rw [htm]
    exact comm_aux hcz
  · rcases CFSG.LocalCores.distinct_components_commute hKn hKm with h | h
    · exact absurd h hK
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (mem_centralizer_iff.mp (hle (conjElt_mem_cj (w := A.w) ha n)) _
        (conjElt_mem_cj (w := A.w) ha m)).symm

theorem conjElt_comm (H : OrbitHyp A S K₀) {a b : X} (ha : a ∈ K₀)
    (hb : b ∈ compProd S ⊓ centralizer (K₀ : Set X)) (hab : a * b ∈ A.P) (n m : ℕ) :
    conjElt A.w a n * conjElt A.w a m = conjElt A.w a m * conjElt A.w a n := by
  rcases le_total n m with h | h
  · exact H.conjElt_comm_le ha hb hab h
  · exact (H.conjElt_comm_le ha hb hab h).symm

end Fin

end OrbitHyp

theorem orbit_lemma [Finite X] (hx : orderOf x = 2) (hO : pPrimeCore 2 X = ⊥) {A : SolvAPI x V}
    {S : Set (Subgroup X)} {K₀ : Subgroup X} (H : OrbitHyp A S K₀) : False := by
  obtain ⟨a, ha, b, hb, hab, hanc, m, hm⟩ := H.exists_part hO
  have hZn : (layerZ X).Normal := layerZ_normal
  have hZ2 := layerZ_isPGroup hO
  have hLayer : ∀ n, conjElt A.w a n ∈ layer X := fun n =>
    CFSG.LocalCores.component_le_layer (isComponent_cj H.isComponent_K₀) (conjElt_mem_cj ha n)
  have hcomm : ∀ y ∈ (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)),
      ∀ z ∈ (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)), y * z = z * y := by
    rintro y (⟨n, rfl⟩ | hy) z (⟨k, rfl⟩ | hz)
    · exact H.conjElt_comm ha hb hab n k
    · exact mem_centralizer_iff.mp hz.2 _ (hLayer n)
    · exact (mem_centralizer_iff.mp hy.2 _ (hLayer k)).symm
    · exact layerZ_comm hy hz
  have h2 : ∀ y ∈ (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)), ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    rintro y (⟨n, rfl⟩ | hy)
    · exact ⟨m, conjElt_pow hm n⟩
    · exact exists_pow_eq_one_of_mem hZ2 hy
  have hwT : A.w ∈ normalizer
      ((Subgroup.closure (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)) : Subgroup X) : Set X) := by
    refine mem_normalizer_closure fun y hy => ?_
    rcases hy with ⟨n, rfl⟩ | hy
    · rw [conjElt_succ]
      exact Subgroup.subset_closure (Or.inl ⟨n + 1, rfl⟩)
    · exact Subgroup.subset_closure (Or.inr (hZn.conj_mem y hy A.w))
  have hz1 := part_central A.x_mem_centralizer_P H.x_mem_normalizer (H.xK K₀ H.mem) ha hb hab
  have hz1Z : a⁻¹ * (x * a * x⁻¹) ∈ layerZ X := inf_centralizer_le_layerZ H.isComponent_K₀ hz1
  have hxT : x ∈ normalizer
      ((Subgroup.closure (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)) : Subgroup X) : Set X) := by
    refine mem_normalizer_closure fun y hy => ?_
    rcases hy with ⟨n, rfl⟩ | hy
    · have e : x * a * x⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) := by group
      have : x * conjElt A.w a n * x⁻¹ = conjElt A.w a n *
          (A.w ^ n * (a⁻¹ * (x * a * x⁻¹)) * (A.w ^ n)⁻¹) := by
        rw [conj_conjElt A.w_mul_x.symm n, e]
        unfold conjElt
        group
      rw [this]
      exact mul_mem (Subgroup.subset_closure (Or.inl ⟨n, rfl⟩))
        (Subgroup.subset_closure (Or.inr (hZn.conj_mem _ hz1Z (A.w ^ n))))
    · exact Subgroup.subset_closure (Or.inr (hZn.conj_mem y hy x))
  have hT := A.abelian hx _ (isPGroup_closure_of_commute hcomm h2) (closure_comm hcomm) hwT hxT
  have h0 : a ∈ Subgroup.closure (Set.range (conjElt A.w a) ∪ (layerZ X : Set X)) :=
    Subgroup.subset_closure (Or.inl ⟨0, conjElt_zero _ _⟩)
  have hwa : A.w * a = a * A.w :=
    mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hT h0) A.w
      (Subgroup.mem_zpowers A.w)
  have h1 : conjElt A.w a 1 = a := by
    simp only [conjElt, pow_one]
    rw [hwa]
    group
  have haK1 : a ∈ cj A.w K₀ := by
    have := conjElt_mem_cj (w := A.w) ha 1
    rwa [h1, pow_one] at this
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_cj H.isComponent_K₀)
    H.isComponent_K₀ with h | h
  · exact H.cj_w_ne h
  · exact hanc (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h haK1)

end Step4

end CFSG.GH74.GLS.Balance
