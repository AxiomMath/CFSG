module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePElem
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_conj_commute {Λ : Subgroup G} {g y : G}
    (hc : ∀ b ∈ Λ.map (MulAut.conj g).toMonoidHom, (g * y * g⁻¹) * b = b * (g * y * g⁻¹)) :
    ∀ a ∈ Λ, a * y = y * a := by
  intro a ha
  have h := hc (g * a * g⁻¹) ⟨a, ha, rfl⟩
  have : g * (y * a) * g⁻¹ = g * (a * y) * g⁻¹ := by
    calc g * (y * a) * g⁻¹ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := h
      _ = g * (a * y) * g⁻¹ := by group
  have := mul_left_cancel (mul_right_cancel this)
  exact this.symm

omit [Finite G] in
theorem map_conj_pow_ne {Λ : Subgroup G} {c : G}
    (hc : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → c ^ k ∉ Subgroup.normalizer (Λ : Set G))
    {i j : ℕ} (hij : i < j) (hj4 : j ≤ 4) :
    Λ.map (MulAut.conj (c ^ j)).toMonoidHom ≠ Λ.map (MulAut.conj (c ^ i)).toMonoidHom := by
  intro heq
  apply hc (j - i) (by omega) (by omega)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hji : c ^ j = c ^ i * c ^ (j - i) := by rw [← pow_add]; congr 1; omega
  have e1 : x ∈ Λ ↔ c ^ j * x * (c ^ j)⁻¹ ∈ Λ.map (MulAut.conj (c ^ j)).toMonoidHom := by
    rw [mem_map_conj_iff]
    have : (c ^ j)⁻¹ * (c ^ j * x * (c ^ j)⁻¹) * c ^ j = x := by group
    rw [this]
  have e2 : c ^ j * x * (c ^ j)⁻¹ ∈ Λ.map (MulAut.conj (c ^ i)).toMonoidHom ↔
      c ^ (j - i) * x * (c ^ (j - i))⁻¹ ∈ Λ := by
    rw [mem_map_conj_iff]
    have : (c ^ i)⁻¹ * (c ^ j * x * (c ^ j)⁻¹) * c ^ i =
        c ^ (j - i) * x * (c ^ (j - i))⁻¹ := by rw [hji]; group
    rw [this]
  rw [e1, heq, e2]

theorem commute_map_conj_pow {Λ : Subgroup G} (hΛ : CFSG.IsComponent Λ) {c : G}
    (hc : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → c ^ k ∉ Subgroup.normalizer (Λ : Set G))
    {i j : ℕ} (hij : i ≠ j) (hi4 : i ≤ 4) (hj4 : j ≤ 4) :
    ∀ a ∈ Λ.map (MulAut.conj (c ^ i)).toMonoidHom,
      ∀ b ∈ Λ.map (MulAut.conj (c ^ j)).toMonoidHom, a * b = b * a := by
  have hΛi : ∀ k, CFSG.IsComponent (Λ.map (MulAut.conj (c ^ k)).toMonoidHom) := fun k =>
    CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact commute_of_ne (hΛi i) (hΛi j) (map_conj_pow_ne hc h hj4)
  · intro a ha b hb
    exact (commute_of_ne (hΛi j) (hΛi i) (map_conj_pow_ne hc h hi4) b hb a ha).symm

omit [Finite G] in
theorem mul_conj_inv_commute {u g y : G} (hgu : g * u = u * g)
    (hgφ : g * (y⁻¹ * (u * y * u⁻¹)) = (y⁻¹ * (u * y * u⁻¹)) * g) :
    y * (g * y * g⁻¹)⁻¹ * u = u * (y * (g * y * g⁻¹)⁻¹) := by
  set φ := y⁻¹ * (u * y * u⁻¹) with hφ
  have huy : u * y * u⁻¹ = y * φ := by rw [hφ]; group
  have h1 : u * (g * y * g⁻¹) * u⁻¹ = g * (u * y * u⁻¹) * g⁻¹ := by
    calc u * (g * y * g⁻¹) * u⁻¹ = (u * g) * y * (u * g)⁻¹ := by group
      _ = (g * u) * y * (g * u)⁻¹ := by rw [hgu]
      _ = _ := by group
  have h2 : g * φ * g⁻¹ = φ := by rw [hgφ]; group
  have h3 : u * (g * y * g⁻¹) * u⁻¹ = (g * y * g⁻¹) * φ := by
    rw [h1, huy]
    calc g * (y * φ) * g⁻¹ = (g * y * g⁻¹) * (g * φ * g⁻¹) := by group
      _ = _ := by rw [h2]
  have h4 : u * (y * (g * y * g⁻¹)⁻¹) * u⁻¹ = y * (g * y * g⁻¹)⁻¹ := by
    calc u * (y * (g * y * g⁻¹)⁻¹) * u⁻¹ =
          (u * y * u⁻¹) * (u * (g * y * g⁻¹) * u⁻¹)⁻¹ := by group
      _ = _ := by rw [huy, h3]; group
  calc y * (g * y * g⁻¹)⁻¹ * u = (u * (y * (g * y * g⁻¹)⁻¹) * u⁻¹) * u := by rw [h4]
    _ = _ := by group

omit [Finite G] in
theorem mul_conj_inv_pow_eq_one {g y : G} {p : ℕ}
    (hy : y * (g * y * g⁻¹) = (g * y * g⁻¹) * y) (hgp : g * y ^ p = y ^ p * g) :
    (y * (g * y * g⁻¹)⁻¹) ^ p = 1 := by
  have hc1 : Commute y (g * y * g⁻¹)⁻¹ := Commute.inv_right hy
  have hyp : (g * y * g⁻¹) ^ p = y ^ p := by rw [conj_pow, hgp]; group
  rw [hc1.mul_pow, inv_pow, hyp, mul_inv_cancel]

omit [Finite G] in
theorem mul_conj_inv_not_mem_centralizer {Λ : Subgroup G} {g y : G}
    (hy : ¬ ∀ a ∈ Λ, a * y = y * a)
    (hyc : ∀ b ∈ Λ.map (MulAut.conj g).toMonoidHom, y * b = b * y) :
    y * (g * y * g⁻¹)⁻¹ ∉ Subgroup.centralizer (Λ.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro hmem
  apply hy
  apply commute_of_conj_commute (g := g)
  intro b hb
  have h1 : b * (y * (g * y * g⁻¹)⁻¹) = (y * (g * y * g⁻¹)⁻¹) * b :=
    Subgroup.mem_centralizer_iff.mp hmem b hb
  have h2 := hyc b hb
  have h3 : y * (b * (g * y * g⁻¹)⁻¹) = y * ((g * y * g⁻¹)⁻¹ * b) := by
    calc y * (b * (g * y * g⁻¹)⁻¹) = (y * b) * (g * y * g⁻¹)⁻¹ := by group
      _ = (b * y) * (g * y * g⁻¹)⁻¹ := by rw [h2]
      _ = b * (y * (g * y * g⁻¹)⁻¹) := by group
      _ = (y * (g * y * g⁻¹)⁻¹) * b := h1
      _ = y * ((g * y * g⁻¹)⁻¹ * b) := by group
  have h4 : Commute b (g * y * g⁻¹)⁻¹ := mul_left_cancel h3
  exact (Commute.inv_right_iff.mp h4).symm.eq

theorem exists_elemAbelian_six {p : ℕ} [hp : Fact p.Prime] {Λ X : Subgroup G}
    (hΛ : CFSG.IsComponent Λ) {u c : G}
    (hu : u ∈ Subgroup.normalizer (Λ : Set G)) (hup : ∃ k : ℕ, u ^ p ^ k = 1)
    (hcu : c * u = u * c)
    (hc : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → c ^ i ∉ Subgroup.normalizer (Λ : Set G))
    (hcX : ∀ x ∈ X, c * x = x * c) (hXu : ∀ x ∈ X, x * u = u * x)
    (hXE : ∀ Λ' : Subgroup G, CFSG.IsComponent Λ' → ∀ x ∈ X, ∀ a ∈ Λ', x * a = a * x)
    (hXel : CFSG.Open.IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    (hZX : ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) → (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ X)
    (hpZ : p ∣ (Subgroup.center Λ).index) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({u} : Set G) ∧ CFSG.Open.IsElemAbelian p A ∧
      p ^ 6 ≤ Nat.card A := by
  classical
  obtain ⟨y, hyZ, ⟨m, hym⟩, hyp, hyφ⟩ := exists_pelem_mod_center hΛ.2 hu hup hpZ
  set y₀ : G := (y : G) with hy₀
  have hy₀Λ : y₀ ∈ Λ := y.2
  have hy₀Z : ¬ ∀ a ∈ Λ, a * y₀ = y₀ * a := by
    intro h
    apply hyZ
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (h a a.2)
  have hcen : ∀ z : Λ, z ∈ Subgroup.center Λ → ∀ a ∈ Λ, a * (z : G) = (z : G) * a :=
    fun z hz a ha => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, ha⟩)
  set φ : G := y₀⁻¹ * (u * y₀ * u⁻¹) with hφ
  have hφΛ : φ ∈ Λ := Λ.mul_mem (Λ.inv_mem hy₀Λ)
    ((Subgroup.mem_normalizer_iff.mp hu y₀).mp hy₀Λ)
  have hφc : ∀ a ∈ Λ, a * φ = φ * a := hcen _ hyφ
  have hym' : y₀ ^ p ^ m = 1 := by simpa using congrArg Subtype.val hym
  have hφp : φ ^ p ^ m = 1 := by
    have hcomm : Commute y₀⁻¹ (u * y₀ * u⁻¹) := by
      have h1 : y₀ * φ = φ * y₀ := hφc y₀ hy₀Λ
      have h2 : u * y₀ * u⁻¹ = y₀ * φ := by rw [hφ]; group
      show y₀⁻¹ * (u * y₀ * u⁻¹) = (u * y₀ * u⁻¹) * y₀⁻¹
      rw [h2]
      calc y₀⁻¹ * (y₀ * φ) = φ := by group
        _ = y₀ * φ * y₀⁻¹ := by rw [h1]; group
    rw [hφ, hcomm.mul_pow, inv_pow, hym', conj_pow, hym']
    group
  have hφX : φ ∈ X := hZX φ hφΛ hφc ⟨m, hφp⟩
  have hypX : y₀ ^ p ∈ X := hZX _ (Λ.pow_mem hy₀Λ p) (hcen _ hyp)
    ⟨m, by rw [← pow_mul, mul_comm, pow_mul, hym', one_pow]⟩
  set Λi : ℕ → Subgroup G := fun i => Λ.map (MulAut.conj (c ^ i)).toMonoidHom with hΛidef
  set yi : ℕ → G := fun i => c ^ i * y₀ * (c ^ i)⁻¹ with hyidef
  have hyiΛ : ∀ i, yi i ∈ Λi i := fun i => ⟨y₀, hy₀Λ, rfl⟩
  have hΛi : ∀ i, CFSG.IsComponent (Λi i) := fun i =>
    CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
  have hΛ0 : ∀ a ∈ Λ, a ∈ Λi 0 := fun a ha => ⟨a, ha, by simp⟩
  have hcomm_ne : ∀ i j : ℕ, i ≠ j → i ≤ 4 → j ≤ 4 → ∀ a ∈ Λi i, ∀ b ∈ Λi j, a * b = b * a :=
    fun i j hij hi4 hj4 => commute_map_conj_pow hΛ hc hij hi4 hj4
  have hy₀i : ∀ i, 1 ≤ i → i ≤ 4 → ∀ b ∈ Λi i, y₀ * b = b * y₀ :=
    fun i hi1 hi4 b hb => hcomm_ne 0 i (by omega) (by omega) hi4 y₀ (hΛ0 y₀ hy₀Λ) b hb
  have hciX : ∀ i : ℕ, ∀ x ∈ X, c ^ i * x = x * c ^ i :=
    fun i x hx => (Commute.pow_left (hcX x hx) i).eq
  have hciu : ∀ i : ℕ, c ^ i * u = u * c ^ i := fun i => (Commute.pow_left hcu i).eq
  set w : ℕ → G := fun i => y₀ * (yi i)⁻¹ with hwdef
  have hwu : ∀ i, w i * u = u * w i := fun i =>
    mul_conj_inv_commute (u := u) (g := c ^ i) (y := y₀) (hciu i) (hciX i φ hφX)
  have hwp : ∀ i, 1 ≤ i → i ≤ 4 → w i ^ p = 1 := fun i hi1 hi4 =>
    mul_conj_inv_pow_eq_one (g := c ^ i) (y := y₀) (hy₀i i hi1 hi4 _ (hyiΛ i)) (hciX i _ hypX)
  have hwX : ∀ i, ∀ x ∈ X, Commute x (w i) := fun i x hx =>
    Commute.mul_right (hXE Λ hΛ x hx y₀ hy₀Λ)
      (Commute.inv_right (hXE (Λi i) (hΛi i) x hx (yi i) (hyiΛ i)))
  have hww : ∀ i j, 1 ≤ i → i ≤ 4 → 1 ≤ j → j ≤ 4 → Commute (w i) (w j) := by
    intro i j hi1 hi4 hj1 hj4
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    have a1 : Commute y₀ (yi j)⁻¹ := Commute.inv_right (hy₀i j hj1 hj4 _ (hyiΛ j))
    have a2 : Commute (yi i)⁻¹ y₀ := Commute.inv_left (hy₀i i hi1 hi4 _ (hyiΛ i)).symm
    have a3 : Commute (yi i)⁻¹ (yi j)⁻¹ :=
      Commute.inv_inv (hcomm_ne i j hij hi4 hj4 _ (hyiΛ i) _ (hyiΛ j))
    exact ((Commute.refl y₀).mul_right a1).mul_left (a2.mul_right a3)
  have hwnot : ∀ i, 1 ≤ i → i ≤ 4 → w i ∉ Subgroup.centralizer (Λi i : Set G) :=
    fun i hi1 hi4 => mul_conj_inv_not_mem_centralizer hy₀Z (hy₀i i hi1 hi4)
  have hwcent : ∀ k i, 1 ≤ k → k ≤ 4 → 1 ≤ i → i ≤ 4 → k ≠ i →
      w k ∈ Subgroup.centralizer (Λi i : Set G) := by
    intro k i hk1 hk4 hi1 hi4 hki
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : Commute b y₀ := (hy₀i i hi1 hi4 b hb).symm
    have h2 : Commute b (yi k) := (hcomm_ne k i hki hk4 hi4 (yi k) (hyiΛ k) b hb).symm
    exact h1.mul_right h2.inv_right
  have hXcent : ∀ i, X ≤ Subgroup.centralizer (Λi i : Set G) := fun i x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hXE (Λi i) (hΛi i) x hx b hb).symm
  set s4 : Set G := insert (w 4) (insert (w 3) (insert (w 2) (insert (w 1) (X : Set G))))
    with hs4def
  have hs4 : ∀ a ∈ s4, a ∈ X ∨ a = w 1 ∨ a = w 2 ∨ a = w 3 ∨ a = w 4 := by
    intro a ha
    simp only [hs4def, Set.mem_insert_iff, SetLike.mem_coe] at ha
    tauto
  have hcommX : ∀ a ∈ X, ∀ b ∈ s4, Commute a b := by
    intro a ha b hb
    rcases hs4 b hb with hb | rfl | rfl | rfl | rfl
    · exact congrArg Subtype.val (hXel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    all_goals exact hwX _ a ha
  have hcommW : ∀ i, 1 ≤ i → i ≤ 4 → ∀ b ∈ s4, Commute (w i) b := by
    intro i hi1 hi4 b hb
    rcases hs4 b hb with hb | rfl | rfl | rfl | rfl
    · exact (hwX i b hb).symm
    · exact hww i 1 hi1 hi4 le_rfl (by norm_num)
    · exact hww i 2 hi1 hi4 (by norm_num) (by norm_num)
    · exact hww i 3 hi1 hi4 (by norm_num) (by norm_num)
    · exact hww i 4 hi1 hi4 (by norm_num) le_rfl
  have hpair : s4.Pairwise Commute := by
    intro a ha b hb _
    rcases hs4 a ha with ha' | rfl | rfl | rfl | rfl
    · exact hcommX a ha' b hb
    · exact hcommW 1 le_rfl (by norm_num) b hb
    · exact hcommW 2 (by norm_num) (by norm_num) b hb
    · exact hcommW 3 (by norm_num) (by norm_num) b hb
    · exact hcommW 4 (by norm_num) le_rfl b hb
  have hexp : ∀ a ∈ s4, a ^ p = 1 := by
    intro a ha
    rcases hs4 a ha with ha' | rfl | rfl | rfl | rfl
    · exact hXel.2 a ha'
    · exact hwp 1 le_rfl (by norm_num)
    · exact hwp 2 (by norm_num) (by norm_num)
    · exact hwp 3 (by norm_num) (by norm_num)
    · exact hwp 4 (by norm_num) le_rfl
  have hA : CFSG.Open.IsElemAbelian p (closure s4) := elemAbelian_closure hpair hexp
  have hApg : IsPGroup p (closure s4) := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  refine ⟨closure s4, ?_, hA, six_le_card_closure hXcard w
    (fun i => Subgroup.centralizer (Λi i : Set G)) hApg hXcent
    (fun k i hk1 hki hi4 => hwcent k i hk1 (by omega) (by omega) hi4 (by omega)) hwnot⟩
  rw [closure_le]
  intro a ha
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rcases hs4 a ha with ha' | rfl | rfl | rfl | rfl
  · exact (hXu a ha').symm
  all_goals exact (hwu _).symm

end CFSG.AGLEmbedding.SPLMSide
