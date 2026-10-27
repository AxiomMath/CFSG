module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def diag (x m : G) : G := m * (x * m * x⁻¹)

@[expose] def DiagComm (x : G) (M : Subgroup G) : Prop :=
  ∀ a ∈ M, ∀ b ∈ cj x M, a * b = b * a

variable {M : Subgroup G} {x : G}

theorem commutatorElement_mul_of_commute {a b z₁ z₂ : G}
    (h1b : z₁ * b = b * z₁) (h12 : z₁ * z₂ = z₂ * z₁) (h2a : a * z₂ = z₂ * a) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have hz1 : ⁅z₁, b * z₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    calc z₁ * (b * z₂) = (z₁ * b) * z₂ := by group
      _ = (b * z₁) * z₂ := by rw [h1b]
      _ = b * (z₁ * z₂) := by group
      _ = b * (z₂ * z₁) := by rw [h12]
      _ = (b * z₂) * z₁ := by group
  have hz2 : ⁅a, z₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h2a
  rw [commutatorElement_mul_left_eq_conj_mul a z₁ (b * z₂)]
  rw [commutatorElement_mul_right_eq_mul_conj a b z₂]
  rw [hz1, hz2]
  group

theorem mul_comm_of_commutatorElement_eq {a c b : G} (h : ⁅a, b⁆ = ⁅c, b⁆) :
    (a⁻¹ * c) * b = b * (a⁻¹ * c) := by
  have h' : a * b * a⁻¹ = c * b * c⁻¹ := by
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using
      congrArg (fun t => t * b) h
  have hab : a * b = c * b * c⁻¹ * a := by
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = (c * b * c⁻¹) * a := by rw [h']
      _ = c * b * c⁻¹ * a := by group
  have hx : (c⁻¹ * a) * b = b * (c⁻¹ * a) := by
    calc (c⁻¹ * a) * b = c⁻¹ * (a * b) := by group
      _ = c⁻¹ * (c * b * c⁻¹ * a) := by rw [hab]
      _ = b * (c⁻¹ * a) := by group
  have hxinv : (c⁻¹ * a)⁻¹ * b = b * (c⁻¹ * a)⁻¹ := by
    calc (c⁻¹ * a)⁻¹ * b = (c⁻¹ * a)⁻¹ * (b * (c⁻¹ * a)) * (c⁻¹ * a)⁻¹ := by group
      _ = (c⁻¹ * a)⁻¹ * ((c⁻¹ * a) * b) * (c⁻¹ * a)⁻¹ := by rw [hx]
      _ = b * (c⁻¹ * a)⁻¹ := by group
  calc (a⁻¹ * c) * b = (c⁻¹ * a)⁻¹ * b := by
        rw [show (c⁻¹ * a)⁻¹ = a⁻¹ * c by group]
    _ = b * (c⁻¹ * a)⁻¹ := hxinv
    _ = b * (a⁻¹ * c) := by rw [show (c⁻¹ * a)⁻¹ = a⁻¹ * c by group]

theorem diag_one : diag x (1 : G) = 1 := by
  simp [diag]

theorem diag_mul (hc : DiagComm x M) {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    diag x (a * b) = diag x a * diag x b := by
  simp only [diag]
  rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
  rw [show a * b * ((x * a * x⁻¹) * (x * b * x⁻¹))
        = a * (b * (x * a * x⁻¹)) * (x * b * x⁻¹) by group]
  rw [hc b hb (x * a * x⁻¹) (conj_mem_cj ha)]
  group

theorem diag_inv (hc : DiagComm x M) {a : G} (ha : a ∈ M) : diag x a⁻¹ = (diag x a)⁻¹ := by
  simp only [diag]
  rw [mul_inv_rev]
  rw [show (x * a * x⁻¹)⁻¹ = x * a⁻¹ * x⁻¹ by group]
  rw [hc a⁻¹ (M.inv_mem ha) (x * a⁻¹ * x⁻¹) (conj_mem_cj (M.inv_mem ha))]

theorem diag_commutator (hc : DiagComm x M) {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    diag x ⁅a, b⁆ = ⁅diag x a, diag x b⁆ := by
  have h1 : diag x (a * b) = diag x a * diag x b := diag_mul hc ha hb
  have h2 : diag x (a⁻¹ * b⁻¹) = diag x a⁻¹ * diag x b⁻¹ :=
    diag_mul hc (M.inv_mem ha) (M.inv_mem hb)
  rw [commutatorElement_def, commutatorElement_def]
  rw [show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group]
  rw [show diag x ((a * b) * (a⁻¹ * b⁻¹)) = diag x (a * b) * diag x (a⁻¹ * b⁻¹) from
        diag_mul hc (M.mul_mem ha hb) (M.mul_mem (M.inv_mem ha) (M.inv_mem hb))]
  rw [h1, h2, diag_inv hc ha, diag_inv hc hb]
  group

theorem diag_mem_sup {m : G} (hm : m ∈ M) : diag x m ∈ M ⊔ cj x M := by
  rw [diag]
  exact mul_mem_sup hm (conj_mem_cj hm)

theorem diag_fixed (hx : x * x = 1) (hc : DiagComm x M) {m : G} (hm : m ∈ M) :
    x * diag x m * x⁻¹ = diag x m := by
  have hAm : x * (x * m * x⁻¹) * x⁻¹ = m := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
    rw [hxinv]
    simp only [mul_assoc]
    rw [hx, mul_one, ← mul_assoc, hx, one_mul]
  simp only [diag]
  calc x * (m * (x * m * x⁻¹)) * x⁻¹
      = (x * m * x⁻¹) * (x * (x * m * x⁻¹) * x⁻¹) := by group
    _ = (x * m * x⁻¹) * m := by rw [hAm]
    _ = m * (x * m * x⁻¹) := (hc m hm (x * m * x⁻¹) (conj_mem_cj hm)).symm

theorem exists_diagSub (hc : DiagComm x M) :
    ∃ D : Subgroup G, ∀ g : G, g ∈ D ↔ ∃ m ∈ M, g = diag x m := by
  let f : M →* G := {
    toFun := fun m => diag x m.1
    map_one' := diag_one
    map_mul' := fun a b => diag_mul hc a.2 b.2 }
  refine ⟨f.range, fun g => ?_⟩
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m.1, m.2, hm.symm⟩
  · rintro ⟨m, hm, hgm⟩
    exact ⟨⟨m, hm⟩, hgm.symm⟩

theorem mem_sup_cj_iff (hc : DiagComm x M) {g : G} :
    g ∈ M ⊔ cj x M ↔ ∃ m ∈ M, ∃ n ∈ M, g = m * (x * n * x⁻¹) := by
  let φ : M × M →* G := {
    toFun := fun p => p.1.1 * (x * p.2.1 * x⁻¹)
    map_one' := by simp
    map_mul' := fun p q => by
      change (p.1.1 * q.1.1) * (x * (p.2.1 * q.2.1) * x⁻¹)
        = (p.1.1 * (x * p.2.1 * x⁻¹)) * (q.1.1 * (x * q.2.1 * x⁻¹))
      rw [show x * (p.2.1 * q.2.1) * x⁻¹
            = (x * p.2.1 * x⁻¹) * (x * q.2.1 * x⁻¹) by group]
      rw [show (p.1.1 * q.1.1) * ((x * p.2.1 * x⁻¹) * (x * q.2.1 * x⁻¹))
            = p.1.1 * (q.1.1 * (x * p.2.1 * x⁻¹)) * (x * q.2.1 * x⁻¹) by group]
      rw [hc q.1.1 q.1.2 (x * p.2.1 * x⁻¹) (conj_mem_cj p.2.2)]
      group }
  have hsup : M ⊔ cj x M = φ.range := by
    apply le_antisymm
    · apply sup_le
      · intro m hm
        refine MonoidHom.mem_range.mpr ⟨(⟨m, hm⟩, ⟨1, M.one_mem⟩), ?_⟩
        change m * (x * 1 * x⁻¹) = m
        group
      · intro y hy
        rw [mem_cj] at hy
        refine MonoidHom.mem_range.mpr ⟨(⟨1, M.one_mem⟩, ⟨x⁻¹ * y * x, hy⟩), ?_⟩
        change 1 * (x * (x⁻¹ * y * x) * x⁻¹) = y
        group
    · intro g hg
      rw [MonoidHom.mem_range] at hg
      obtain ⟨p, rfl⟩ := hg
      change p.1.1 * (x * p.2.1 * x⁻¹) ∈ M ⊔ cj x M
      exact mul_mem_sup p.1.2 (conj_mem_cj p.2.2)
  rw [hsup, MonoidHom.mem_range]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, hp.symm⟩
  · rintro ⟨m, hm, n, hn, rfl⟩
    exact ⟨(⟨m, hm⟩, ⟨n, hn⟩), rfl⟩

theorem inf_cj_central (hc : DiagComm x M) {z : G} (hz : z ∈ M ⊓ cj x M) :
    ∀ w ∈ M ⊔ cj x M, w * z = z * w := by
  have hM : M ≤ centralizer ({z} : Set G) := by
    intro m hm
    rw [mem_centralizer_singleton_iff]
    exact hc m hm z hz.2
  have hcj : cj x M ≤ centralizer ({z} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact (hc z hz.1 w hw).symm
  intro w hw
  have := (sup_le hM hcj) hw
  rwa [mem_centralizer_singleton_iff] at this

theorem exists_diag_mul_of_fixed (hx : x * x = 1) (hc : DiagComm x M) {g : G}
    (hg : g ∈ M ⊔ cj x M) (hfix : x * g * x⁻¹ = g) :
    ∃ m ∈ M, ∃ z ∈ M ⊓ cj x M, g = diag x m * z := by
  obtain ⟨a, ha, b, hb, hgab⟩ := (mem_sup_cj_iff hc).mp hg
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hconj : x * (x * b * x⁻¹) * x⁻¹ = b := by
    rw [hxinv]
    simp only [mul_assoc]
    rw [hx, mul_one, ← mul_assoc, hx, one_mul]
  have hE : (x * a * x⁻¹) * b = a * (x * b * x⁻¹) := by
    have h1 : x * g * x⁻¹ = (x * a * x⁻¹) * b := by
      rw [hgab]
      rw [show x * (a * (x * b * x⁻¹)) * x⁻¹
            = (x * a * x⁻¹) * (x * (x * b * x⁻¹) * x⁻¹) by group]
      rw [hconj]
    rw [hfix, hgab] at h1
    exact h1.symm
  have hmain : a * ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)) = b := by
    calc a * ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹))
        = (a * (x * a * x⁻¹)⁻¹) * (x * b * x⁻¹) := by group
      _ = ((x * a * x⁻¹)⁻¹ * a) * (x * b * x⁻¹) := by
            rw [hc a ha (x * a * x⁻¹)⁻¹ ((cj x M).inv_mem (conj_mem_cj ha))]
      _ = (x * a * x⁻¹)⁻¹ * (a * (x * b * x⁻¹)) := by group
      _ = (x * a * x⁻¹)⁻¹ * ((x * a * x⁻¹) * b) := by rw [← hE]
      _ = b := by group
  set w : G := a⁻¹ * b with hw
  have hwM : w ∈ M := by rw [hw]; exact M.mul_mem (M.inv_mem ha) hb
  have hw_eq : w = (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) := by
    rw [hw]
    calc a⁻¹ * b = a⁻¹ * (a * ((x * a * x⁻¹)⁻¹ * (x * b * x⁻¹))) := by rw [hmain]
      _ = (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hwcj : w ∈ cj x M := by
    rw [hw_eq]
    exact (cj x M).mul_mem ((cj x M).inv_mem (conj_mem_cj ha)) (conj_mem_cj hb)
  refine ⟨a, ha, x * w * x⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [hxinv]
    exact (mem_cj_of_mul_self hx).mp hwcj
  · exact conj_mem_cj hwM
  · have haw : a * w = b := by rw [hw]; group
    have hAw : (x * a * x⁻¹) * (x * w * x⁻¹) = x * b * x⁻¹ := by
      rw [← haw]; group
    rw [hgab]
    simp only [diag]
    rw [show a * (x * a * x⁻¹) * (x * w * x⁻¹)
          = a * ((x * a * x⁻¹) * (x * w * x⁻¹)) by group, hAw]

theorem le_diag_of_perfect (hx : x * x = 1) (hc : DiagComm x M) {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hle : K ≤ M ⊔ cj x M) (hfix : ∀ k ∈ K, x * k * x⁻¹ = k) :
    ∀ k ∈ K, ∃ m ∈ M, k = diag x m := by
  obtain ⟨D, hD⟩ := exists_diagSub (M := M) hc
  have hKD : K ≤ D := by
    rw [← hK]
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨m₁, hm₁, z₁, hz₁, ha_eq⟩ :=
      exists_diag_mul_of_fixed hx hc (hle ha) (hfix a ha)
    obtain ⟨m₂, hm₂, z₂, hz₂, hb_eq⟩ :=
      exists_diag_mul_of_fixed hx hc (hle hb) (hfix b hb)
    refine (hD ⁅a, b⁆).mpr ⟨⁅m₁, m₂⁆, ?_, ?_⟩
    · rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
    · have hda : diag x m₁ ∈ M ⊔ cj x M := diag_mem_sup hm₁
      have hdb : diag x m₂ ∈ M ⊔ cj x M := diag_mem_sup hm₂
      have hc1 := inf_cj_central hc hz₁
      have hc2 := inf_cj_central hc hz₂
      have h1b : z₁ * diag x m₂ = diag x m₂ * z₁ := (hc1 (diag x m₂) hdb).symm
      have h2a : diag x m₁ * z₂ = z₂ * diag x m₁ := hc2 (diag x m₁) hda
      have h12 : z₁ * z₂ = z₂ * z₁ := (hc1 z₂ ((le_sup_left : M ≤ M ⊔ cj x M) hz₂.1)).symm
      rw [ha_eq, hb_eq, commutatorElement_mul_of_commute h1b h12 h2a,
          ← diag_commutator hc hm₁ hm₂]
  intro k hk
  exact (hD k).mp (hKD hk)

theorem diag_of_le_sup_conj [Finite G] (hx : x * x = 1) (hc : DiagComm x M) {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hle : K ≤ M ⊔ cj x M) (hfix : ∀ k ∈ K, x * k * x⁻¹ = k)
    (hcard : Nat.card K = Nat.card M) :
    (∀ g : G, g ∈ K ↔ ∃ m ∈ M, g = diag x m) ∧ (∀ m ∈ M, diag x m = 1 → m = 1) := by
  obtain ⟨D, hD⟩ := exists_diagSub (M := M) hc
  have hKD : K ≤ D := fun k hk => (hD k).mpr (le_diag_of_perfect hx hc hK hle hfix k hk)
  let g : M → D := fun m => ⟨diag x m.1, (hD _).mpr ⟨m.1, m.2, rfl⟩⟩
  have hg : Function.Surjective g := by
    intro d
    obtain ⟨m, hm, hmd⟩ := (hD d.1).mp d.2
    exact ⟨⟨m, hm⟩, Subtype.ext hmd.symm⟩
  have hcardD : Nat.card D ≤ Nat.card M := Nat.card_le_card_of_surjective g hg
  have hKD_eq : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [hcard]; exact hcardD)
  have hcardD_M : Nat.card D = Nat.card M := by rw [← hKD_eq]; exact hcard
  have hinj : Function.Injective g :=
    (hg.bijective_of_nat_card_le (le_of_eq hcardD_M.symm)).1
  constructor
  · intro h
    rw [hKD_eq]
    exact hD h
  · intro m hm hdiag
    have h1 : g ⟨m, hm⟩ = g ⟨1, M.one_mem⟩ := by
      apply Subtype.ext
      change diag x m = diag x 1
      rw [hdiag, diag_one]
    exact congrArg (fun x : M => (x : G)) (hinj h1)

theorem centralizes_of_normalizes (hx : x * x = 1) (hc : DiagComm x M) (hM : ⁅M, M⁆ = M) {g : G}
    (hgN : g ∈ normalizer (M : Set G)) (hg : ∀ m ∈ M, g * diag x m = diag x m * g) :
    (∀ m ∈ M, g * m = m * g) ∧ ∀ m ∈ M, g * (x * m * x⁻¹) = (x * m * x⁻¹) * g := by
  have hgn : ∀ n ∈ M, g * n * g⁻¹ ∈ M := fun n hn => (mem_normalizer_iff.mp hgN n).mp hn
  have hginv : ∀ n ∈ M, g⁻¹ * n * g ∈ M := by
    intro n hn
    have h := (mem_normalizer_iff.mp ((normalizer (M : Set G)).inv_mem hgN) n).mp hn
    rwa [inv_inv] at h
  have step1 : ∀ n ∈ M, ∀ m ∈ M, ⁅diag x n, m⁆ = ⁅n, m⁆ := by
    intro n hn m hm
    have hA : ⁅x * n * x⁻¹, m⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hc m hm (x * n * x⁻¹) (conj_mem_cj hn)).symm
    rw [diag, commutatorElement_mul_left_eq_conj_mul, hA, mul_one]
    group
  have step2 : ∀ n ∈ M, ∀ m ∈ M, ⁅n, g * m * g⁻¹⁆ = ⁅g * n * g⁻¹, g * m * g⁻¹⁆ := by
    intro n hn m hm
    have hmg := hgn m hm
    have hdiag : g * diag x n * g⁻¹ = diag x n := by
      rw [hg n hn]; group
    calc ⁅n, g * m * g⁻¹⁆ = ⁅diag x n, g * m * g⁻¹⁆ :=
          (step1 n hn (g * m * g⁻¹) hmg).symm
      _ = ⁅g * diag x n * g⁻¹, g * m * g⁻¹⁆ := by rw [hdiag]
      _ = g * ⁅diag x n, m⁆ * g⁻¹ :=
            (conjugate_commutatorElement (g₁ := diag x n) (g₂ := m) (g₃ := g)).symm
      _ = g * ⁅n, m⁆ * g⁻¹ := by rw [step1 n hn m hm]
      _ = ⁅g * n * g⁻¹, g * m * g⁻¹⁆ :=
            conjugate_commutatorElement (g₁ := n) (g₂ := m) (g₃ := g)
  have step2' : ∀ n ∈ M, ∀ m' ∈ M, ⁅n, m'⁆ = ⁅g * n * g⁻¹, m'⁆ := by
    intro n hn m' hm'
    have hm := hginv m' hm'
    have h := step2 n hn (g⁻¹ * m' * g) hm
    rw [show g * (g⁻¹ * m' * g) * g⁻¹ = m' by group] at h
    exact h
  have hcentral : ∀ n ∈ M, ∀ m' ∈ M,
      (n⁻¹ * (g * n * g⁻¹)) * m' = m' * (n⁻¹ * (g * n * g⁻¹)) :=
    fun n hn m' hm' => mul_comm_of_commutatorElement_eq (step2' n hn m' hm')
  have hMM : ⁅M, M⁆ ≤ centralizer ({g} : Set G) := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    rw [mem_centralizer_singleton_iff]
    have hcomm_ab : (a⁻¹ * (g * a * g⁻¹)) * b = b * (a⁻¹ * (g * a * g⁻¹)) :=
      hcentral a ha b hb
    have hcomm_ba : (b⁻¹ * (g * b * g⁻¹)) * a = a * (b⁻¹ * (g * b * g⁻¹)) :=
      hcentral b hb a ha
    have hcomm_uv : (a⁻¹ * (g * a * g⁻¹)) * (b⁻¹ * (g * b * g⁻¹))
        = (b⁻¹ * (g * b * g⁻¹)) * (a⁻¹ * (g * a * g⁻¹)) :=
      hcentral a ha (b⁻¹ * (g * b * g⁻¹)) (M.mul_mem (M.inv_mem hb) (hgn b hb))
    have key : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
      calc g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ :=
            conjugate_commutatorElement (g₁ := a) (g₂ := b) (g₃ := g)
        _ = ⁅a * (a⁻¹ * (g * a * g⁻¹)), b * (b⁻¹ * (g * b * g⁻¹))⁆ := by
              rw [show a * (a⁻¹ * (g * a * g⁻¹)) = g * a * g⁻¹ by group,
                  show b * (b⁻¹ * (g * b * g⁻¹)) = g * b * g⁻¹ by group]
        _ = ⁅a, b⁆ := commutatorElement_mul_of_commute hcomm_ab hcomm_uv hcomm_ba.symm
    have hgcomm : g * ⁅a, b⁆ = ⁅a, b⁆ * g := by
      calc g * ⁅a, b⁆ = (g * ⁅a, b⁆ * g⁻¹) * g := by group
        _ = ⁅a, b⁆ * g := by rw [key]
    exact hgcomm.symm
  have hMcent : M ≤ centralizer ({g} : Set G) := by rw [← hM]; exact hMM
  constructor
  · intro m hm
    have h := hMcent hm
    rw [mem_centralizer_singleton_iff] at h
    exact h.symm
  · intro m hm
    have hgm : g * m = m * g := by
      have h := hMcent hm
      rw [mem_centralizer_singleton_iff] at h
      exact h.symm
    have h1 : g * (m * (x * m * x⁻¹)) = (m * (x * m * x⁻¹)) * g := hg m hm
    have h2 : m * (g * (x * m * x⁻¹)) = m * ((x * m * x⁻¹) * g) := by
      calc m * (g * (x * m * x⁻¹)) = (m * g) * (x * m * x⁻¹) := by group
        _ = (g * m) * (x * m * x⁻¹) := by rw [← hgm]
        _ = g * (m * (x * m * x⁻¹)) := by group
        _ = (m * (x * m * x⁻¹)) * g := h1
        _ = m * ((x * m * x⁻¹) * g) := by group
    exact mul_left_cancel h2

theorem centralizes_of_central_diag (hx : x * x = 1) (hc : DiagComm x M) (hM : ⁅M, M⁆ = M)
    {m : G} (hm : m ∈ M) (hz : ∀ n ∈ M, diag x m * diag x n = diag x n * diag x m) :
    (∀ n ∈ M, diag x m * n = n * diag x m) ∧
      ∀ n ∈ M, diag x m * (x * n * x⁻¹) = (x * n * x⁻¹) * diag x m := by
  have step1 : ∀ n ∈ M, ⁅m, n⁆ ∈ M ⊓ cj x M := by
    intro n hn
    have hcM : ⁅m, n⁆ ∈ M := by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm hn) (M.inv_mem hm)) (M.inv_mem hn)
    have hdiag : diag x ⁅m, n⁆ = 1 := by
      rw [diag_commutator hc hm hn]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hz n hn)
    have hxconj : x * ⁅m, n⁆ * x⁻¹ = ⁅m, n⁆⁻¹ := by
      rw [diag] at hdiag
      exact eq_inv_of_mul_eq_one_right hdiag
    refine ⟨hcM, ?_⟩
    have hthis : x * ⁅m, n⁆⁻¹ * x⁻¹ = ⁅m, n⁆ := by
      have h := congrArg Inv.inv hxconj
      rw [show (x * ⁅m, n⁆ * x⁻¹)⁻¹ = x * ⁅m, n⁆⁻¹ * x⁻¹ by group, inv_inv] at h
      exact h
    rw [← hthis]
    exact conj_mem_cj (M.inv_mem hcM)
  let φ : M →* G := {
    toFun := fun n => ⁅m, n.1⁆
    map_one' := by simp
    map_mul' := fun n₁ n₂ => by
      have hz₂ : ⁅m, n₂.1⁆ ∈ M ⊓ cj x M := step1 n₂.1 n₂.2
      have hcent := inf_cj_central hc hz₂
      change ⁅m, n₁.1 * n₂.1⁆ = ⁅m, n₁.1⁆ * ⁅m, n₂.1⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [show ⁅m, n₁.1⁆ * n₁.1 * ⁅m, n₂.1⁆ * n₁.1⁻¹
            = ⁅m, n₁.1⁆ * (n₁.1 * ⁅m, n₂.1⁆) * n₁.1⁻¹ by group]
      rw [hcent n₁.1 ((le_sup_left : M ≤ M ⊔ cj x M) n₁.2)]
      group }
  have hcommut : ∀ a ∈ M, ∀ b ∈ M, ⁅m, ⁅a, b⁆⁆ = 1 := by
    intro a ha b hb
    have ha' : φ ⟨a, ha⟩ ∈ M ⊓ cj x M := step1 a ha
    have hb' : φ ⟨b, hb⟩ ∈ M ⊓ cj x M := step1 b hb
    have hcomm : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ :=
      (inf_cj_central hc ha' (φ ⟨b, hb⟩) ((le_sup_left : M ≤ M ⊔ cj x M) hb'.1)).symm
    have h1 : ⁅φ ⟨a, ha⟩, φ ⟨b, hb⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    have h2 : φ ⁅(⟨a, ha⟩ : M), (⟨b, hb⟩ : M)⁆ = 1 := by rw [map_commutatorElement, h1]
    exact h2
  have hcommM : ∀ n ∈ M, m * n = n * m := by
    have hMM : ⁅M, M⁆ ≤ centralizer ({m} : Set G) := by
      apply Subgroup.commutator_le.mpr
      intro a ha b hb
      rw [mem_centralizer_singleton_iff]
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hcommut a ha b hb)).symm
    intro n hn
    have h : n ∈ centralizer ({m} : Set G) := hMM (by rw [hM]; exact hn)
    rw [mem_centralizer_singleton_iff] at h
    exact h.symm
  constructor
  · intro n hn
    rw [diag]
    calc m * (x * m * x⁻¹) * n = m * ((x * m * x⁻¹) * n) := by group
      _ = m * (n * (x * m * x⁻¹)) := by
            rw [← hc n hn (x * m * x⁻¹) (conj_mem_cj hm)]
      _ = (m * n) * (x * m * x⁻¹) := by group
      _ = (n * m) * (x * m * x⁻¹) := by rw [hcommM n hn]
      _ = n * (m * (x * m * x⁻¹)) := by group
  · intro n hn
    rw [diag]
    have hmx_comm : (x * m * x⁻¹) * (x * n * x⁻¹) = (x * n * x⁻¹) * (x * m * x⁻¹) := by
      calc (x * m * x⁻¹) * (x * n * x⁻¹) = x * (m * n) * x⁻¹ := by group
        _ = x * (n * m) * x⁻¹ := by rw [hcommM n hn]
        _ = (x * n * x⁻¹) * (x * m * x⁻¹) := by group
    calc m * (x * m * x⁻¹) * (x * n * x⁻¹) = m * ((x * m * x⁻¹) * (x * n * x⁻¹)) := by group
      _ = m * ((x * n * x⁻¹) * (x * m * x⁻¹)) := by rw [hmx_comm]
      _ = (m * (x * n * x⁻¹)) * (x * m * x⁻¹) := by group
      _ = ((x * n * x⁻¹) * m) * (x * m * x⁻¹) := by
            rw [hc m hm (x * n * x⁻¹) (conj_mem_cj hn)]
      _ = (x * n * x⁻¹) * (m * (x * m * x⁻¹)) := by group

theorem not_le_normalizer_diag (hx : x * x = 1) (hc : DiagComm x M) (hM : ⁅M, M⁆ = M)
    (hne : cj x M ≠ M) {B : Subgroup G} (hB : ∀ g : G, g ∈ B ↔ ∃ m ∈ M, g = diag x m) :
    ¬ M ≤ normalizer (B : Set G) := by
  intro hle
  apply hne
  have hBM : ⁅M, M⁆ ≤ B := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have hbB : diag x b ∈ B := (hB _).mpr ⟨b, hb, rfl⟩
    have hmbB : a * diag x b * a⁻¹ ∈ B :=
      (mem_normalizer_iff.mp (hle ha) (diag x b)).mp hbB
    have hinvB : (diag x b)⁻¹ ∈ B := B.inv_mem hbB
    have hca : a⁻¹ * (x * b * x⁻¹) = (x * b * x⁻¹) * a⁻¹ := by
      have h := hc a ha (x * b * x⁻¹) (conj_mem_cj hb)
      calc a⁻¹ * (x * b * x⁻¹) = a⁻¹ * ((x * b * x⁻¹) * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * (x * b * x⁻¹)) * a⁻¹ := by rw [← h]
        _ = (x * b * x⁻¹) * a⁻¹ := by group
    have hcomm : a * diag x b * a⁻¹ * (diag x b)⁻¹ = ⁅a, b⁆ := by
      rw [diag, commutatorElement_def]
      rw [show a * (b * (x * b * x⁻¹)) * a⁻¹ * (b * (x * b * x⁻¹))⁻¹
            = (a * b) * ((x * b * x⁻¹) * a⁻¹) * (b * (x * b * x⁻¹))⁻¹ by group]
      rw [← hca]
      group
    rw [← hcomm]
    exact B.mul_mem hmbB hinvB
  have hMB : M ≤ B := by rw [← hM]; exact hBM
  refine cj_eq_of_commute (fun b hb => ?_)
  have hbB : b ∈ B := hMB hb
  obtain ⟨b', hb', hb'_eq⟩ := (hB b).mp hbB
  have hfixb : x * b * x⁻¹ = b := by rw [hb'_eq, diag_fixed hx hc hb']
  calc x * b = (x * b * x⁻¹) * x := by group
    _ = b * x := by rw [hfixb]

theorem diag_not_centralize_left (hx : x * x = 1) (hc : DiagComm x M)
    (hM : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) :
    ¬ ∀ m ∈ M, ∀ n ∈ M, diag x m * n = n * diag x m := by
  intro h
  apply hM
  intro a ha b hb
  have hA : x * a * x⁻¹ ∈ cj x M := conj_mem_cj ha
  have hcomm : b * (x * a * x⁻¹) = (x * a * x⁻¹) * b := hc b hb (x * a * x⁻¹) hA
  have hab := h a ha b hb
  rw [diag] at hab
  have h2 : (a * b) * (x * a * x⁻¹) = (b * a) * (x * a * x⁻¹) := by
    calc (a * b) * (x * a * x⁻¹) = a * (b * (x * a * x⁻¹)) := by group
      _ = a * ((x * a * x⁻¹) * b) := by rw [hcomm]
      _ = a * (x * a * x⁻¹) * b := by group
      _ = b * (a * (x * a * x⁻¹)) := hab
      _ = (b * a) * (x * a * x⁻¹) := by group
  exact mul_right_cancel h2

theorem diag_not_centralize_right (hx : x * x = 1) (hc : DiagComm x M)
    (hM : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) :
    ¬ ∀ m ∈ M, ∀ n ∈ M, diag x m * (x * n * x⁻¹) = (x * n * x⁻¹) * diag x m := by
  intro h
  apply hM
  intro a ha b hb
  have hmB : a * (x * b * x⁻¹) = (x * b * x⁻¹) * a := hc a ha (x * b * x⁻¹) (conj_mem_cj hb)
  have hA : (x * a * x⁻¹) * (x * b * x⁻¹) = (x * b * x⁻¹) * (x * a * x⁻¹) := by
    have hab := h a ha b hb
    rw [diag] at hab
    have h' : a * ((x * a * x⁻¹) * (x * b * x⁻¹))
        = a * ((x * b * x⁻¹) * (x * a * x⁻¹)) := by
      calc a * ((x * a * x⁻¹) * (x * b * x⁻¹))
          = a * (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        _ = (x * b * x⁻¹) * (a * (x * a * x⁻¹)) := hab
        _ = (x * b * x⁻¹) * a * (x * a * x⁻¹) := by group
        _ = a * (x * b * x⁻¹) * (x * a * x⁻¹) := by rw [← hmB]
        _ = a * ((x * b * x⁻¹) * (x * a * x⁻¹)) := by group
    exact mul_left_cancel h'
  have : a * b = b * a := by
    rw [show a * b = x⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * x by group,
        show b * a = x⁻¹ * ((x * b * x⁻¹) * (x * a * x⁻¹)) * x by group]
    exact congrArg (fun t => x⁻¹ * t * x) hA
  exact this

theorem conj_diag_of_commute {y z l : G} (hzy : z * y = y * z) :
    z * diag y l * z⁻¹ = diag y (z * l * z⁻¹) := by
  have hzy' : y⁻¹ * z⁻¹ = z⁻¹ * y⁻¹ := by
    have h := congrArg Inv.inv hzy
    rwa [mul_inv_rev, mul_inv_rev] at h
  have h1 : z * (y * l * y⁻¹) * z⁻¹ = y * (z * l * z⁻¹) * y⁻¹ := by
    rw [show z * (y * l * y⁻¹) * z⁻¹ = (z * y) * l * (y⁻¹ * z⁻¹) by group, hzy, hzy']
    group
  simp only [diag]
  calc z * (l * (y * l * y⁻¹)) * z⁻¹
      = (z * l * z⁻¹) * (z * (y * l * y⁻¹) * z⁻¹) := by group
    _ = (z * l * z⁻¹) * (y * (z * l * z⁻¹) * y⁻¹) := by rw [h1]

theorem cj_eq_of_diag [Finite G] {L : Subgroup G} {y z : G} (hy : y * y = 1) (hc : DiagComm y L)
    (hM : ∀ g : G, g ∈ M ↔ ∃ l ∈ L, g = diag y l) (hzy : z * y = y * z)
    (hz : cj z L = L ∨ cj z L = cj y L) : cj z M = M := by
  have hcl : ∀ m ∈ M, z * m * z⁻¹ ∈ M := by
    intro m hm
    obtain ⟨l, hl, rfl⟩ := (hM m).mp hm
    rw [conj_diag_of_commute hzy]
    rcases hz with hzL | hzyL
    · exact (hM _).mpr ⟨z * l * z⁻¹, by rw [← hzL]; exact conj_mem_cj hl, rfl⟩
    · have hzl : z * l * z⁻¹ ∈ cj y L := by rw [← hzyL]; exact conj_mem_cj hl
      rw [cj] at hzl
      obtain ⟨l'', hl'', hl''eq⟩ := Subgroup.mem_map.mp hzl
      have hl''eq' : y * l'' * y⁻¹ = z * l * z⁻¹ := by
        simpa [MulAut.conj_apply] using hl''eq
      refine (hM _).mpr ⟨l'', hl'', ?_⟩
      rw [← hl''eq']
      simp only [diag]
      have hyconj : y * (y * l'' * y⁻¹) * y⁻¹ = l'' := by
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
        rw [hyinv]
        simp only [mul_assoc]
        rw [hy, mul_one, ← mul_assoc, hy, one_mul]
      rw [hyconj]
      exact (hc l'' hl'' (y * l'' * y⁻¹) (conj_mem_cj hl'')).symm
  have hle : cj z M ≤ M := by
    intro g hg
    rw [cj] at hg
    obtain ⟨m, hm, hm_eq⟩ := Subgroup.mem_map.mp hg
    rw [← hm_eq]
    change z * m * z⁻¹ ∈ M
    exact hcl m hm
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_cj z M).symm)

theorem cj_le_sup_of_diag {L : Subgroup G} {y z : G} (hy : y * y = 1)
    (hM : ∀ g : G, g ∈ M ↔ ∃ l ∈ L, g = diag y l) (hzy : z * y = y * z) :
    cj z M ≤ cj z L ⊔ cj y (cj z L) := by
  intro g hg
  rw [cj] at hg
  obtain ⟨m, hm, hm_eq⟩ := Subgroup.mem_map.mp hg
  obtain ⟨l, hl, rfl⟩ := (hM m).mp hm
  rw [← hm_eq]
  change z * diag y l * z⁻¹ ∈ cj z L ⊔ cj y (cj z L)
  rw [conj_diag_of_commute hzy]
  rw [diag]
  have hzl : z * l * z⁻¹ ∈ cj z L := conj_mem_cj hl
  exact mul_mem_sup hzl (conj_mem_cj hzl)

end CFSG.EvenSporadicStandard.Induction.ThmU
