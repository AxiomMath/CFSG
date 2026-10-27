module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem X_comm [Finite X] (hσ : Setup42 h hS w z) {a b : X}
    (ha : a ∈ closure {t, w ^ (orderOf w / 2), z}) (hb : b ∈ closure {t, w ^ (orderOf w / 2), z}) :
    a * b = b * a :=
  (mem_centralizer_iff.mp (hσ.X_le_center_T ha).2 b (hσ.X_le_T hb)).symm

theorem conj_z_of_mem_normalizer_T [Finite X] (hσ : Setup42 h hS w z) {m : X}
    (hm : m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) :
    m * z * m⁻¹ = z :=
  hσ.conj_z_eq (le_sup_left.trans' le_sup_right) hσ.T_le hm

theorem ncard_conj_t_le_four [Finite X] (hσ : Setup42 h hS w z) {g : X}
    (hgM : g ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    (hgt : g * t * g⁻¹ ≠ t) (hgodd : Odd (orderOf g))
    (hgM' : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∃ j : ℕ, ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
        (m * g * m⁻¹) * x * (m * g * m⁻¹)⁻¹ = g ^ j * x * (g ^ j)⁻¹) :
    {y : X | ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      m * t * m⁻¹ = y}.ncard ≤ 4 := by
  classical
  have hMX := hσ.normalizer_T_le_normalizer_X
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hgX : ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
      g * x * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    fun x hx => (mem_normalizer_iff.mp (hMX hgM) x).mp hx
  have hgz : g * z * g⁻¹ = z := hσ.conj_z_of_mem_normalizer_T hgM
  let δ : ↥(closure {t, w ^ (orderOf w / 2), z}) →* X :=
    { toFun := fun x => (x : X)⁻¹ * (g * x * g⁻¹)
      map_one' := by simp
      map_mul' := fun x y => by
        have hc1 := hσ.X_comm (inv_mem y.2) (hgX x x.2)
        have hc2 := hσ.X_comm (inv_mem x.2) (inv_mem y.2)
        simp only [Subgroup.coe_mul]
        calc ((x : X) * y)⁻¹ * (g * (x * y) * g⁻¹) =
            ((y : X)⁻¹ * (x : X)⁻¹) * ((g * x * g⁻¹) * (g * y * g⁻¹)) := by group
          _ = ((x : X)⁻¹ * (y : X)⁻¹) * ((g * x * g⁻¹) * (g * y * g⁻¹)) := by rw [hc2]
          _ = (x : X)⁻¹ * ((y : X)⁻¹ * (g * x * g⁻¹)) * (g * y * g⁻¹) := by group
          _ = (x : X)⁻¹ * ((g * x * g⁻¹) * (y : X)⁻¹) * (g * y * g⁻¹) := by rw [hc1]
          _ = (x : X)⁻¹ * (g * x * g⁻¹) * ((y : X)⁻¹ * (g * y * g⁻¹)) := by group }
  have hδ : ∀ x : ↥(closure {t, w ^ (orderOf w / 2), z}), δ x = (x : X)⁻¹ * (g * x * g⁻¹) :=
    fun x => rfl
  set E := δ.range with hE
  have hEX : E ≤ closure {t, w ^ (orderOf w / 2), z} := by
    rintro _ ⟨x, rfl⟩
    rw [hδ]
    exact mul_mem (inv_mem x.2) (hgX x x.2)
  have hker : (⟨z, hzX⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) ∈ δ.ker := by
    rw [MonoidHom.mem_ker, hδ]
    simp [hgz]
  have hz1 : z ≠ 1 := by
    intro hz
    have := hσ.z_order
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  have hker2 : 2 ≤ Nat.card δ.ker := by
    have hne : δ.ker ≠ ⊥ := by
      intro hb
      rw [hb, mem_bot] at hker
      exact hz1 (congrArg Subtype.val hker)
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hcardE : Nat.card E ≤ 4 := by
    have h1 := Subgroup.card_ker_mul_card_range δ
    have h2 := hσ.card_X_le
    have h3 : 2 * Nat.card δ.range ≤ Nat.card δ.ker * Nat.card δ.range :=
      Nat.mul_le_mul_right _ hker2
    rw [← hE] at h1 h3
    omega
  have hgpow : ∀ x : X, g * x * g⁻¹ = x * z → ∀ j : ℕ, g ^ j * x * (g ^ j)⁻¹ = x * z ^ j := by
    intro x hx j
    induction j with
    | zero => simp
    | succ j ih =>
      calc g ^ (j + 1) * x * (g ^ (j + 1))⁻¹ = g * (g ^ j * x * (g ^ j)⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ * (g * z ^ j * g⁻¹) := by rw [ih]; group
        _ = x * z * z ^ j := by rw [hx, ← conj_pow, hgz]
        _ = x * z ^ (j + 1) := by rw [mul_assoc, ← pow_succ']
  have hzE : z ∉ E := by
    rintro ⟨x, hx⟩
    rw [hδ] at hx
    have hx' : g * x * g⁻¹ = x * z := by
      have h1 : g * (x : X) * g⁻¹ = x * ((x : X)⁻¹ * (g * x * g⁻¹)) := by group
      rwa [hx] at h1
    have := hgpow x hx' (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    obtain ⟨k, hk⟩ := hgodd
    rw [hk, pow_succ, pow_mul, show z ^ 2 = 1 by rw [← hσ.z_order, pow_orderOf_eq_one],
      one_pow, one_mul] at this
    exact hz1 (by simpa using this.symm)
  have htE : (t⁻¹ * (g * t * g⁻¹)) ∈ E := ⟨⟨t, htX⟩, rfl⟩
  have hE2 : 2 ≤ Nat.card E := by
    have hne : E ≠ ⊥ := by
      intro hb
      rw [hb, mem_bot] at htE
      apply hgt
      calc g * t * g⁻¹ = t * (t⁻¹ * (g * t * g⁻¹)) := by group
        _ = t := by rw [htE, mul_one]
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨g * x * g⁻¹, hgX x x.2⟩, ?_⟩
    rw [hδ, hδ]
    group
  have hpowE : ∀ j : ℕ, ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
      x⁻¹ * (g ^ j * x * (g ^ j)⁻¹) ∈ E := by
    intro j
    induction j with
    | zero =>
      intro x _
      simp [one_mem]
    | succ j ih =>
      intro x hx
      have h1 : x⁻¹ * (g * x * g⁻¹) ∈ E := ⟨⟨x, hx⟩, rfl⟩
      have h2 := hgE _ (ih x hx)
      rw [show x⁻¹ * (g ^ (j + 1) * x * (g ^ (j + 1))⁻¹) =
        (x⁻¹ * (g * x * g⁻¹)) * (g * (x⁻¹ * (g ^ j * x * (g ^ j)⁻¹)) * g⁻¹) by group]
      exact mul_mem h1 h2
  have hME : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ e ∈ E, m * e * m⁻¹ ∈ E := by
    rintro m hm _ ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := hgM' m hm
    have hx' : m * x * m⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      (mem_normalizer_iff.mp (hMX hm) x).mp x.2
    have := hpowE j _ hx'
    rw [← hj _ hx'] at this
    rw [hδ]
    convert this using 1
    group
  set OM := {y : X | ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :
    Set X), m * t * m⁻¹ = y} with hOM
  have hOMX : OM ⊆ closure {t, w ^ (orderOf w / 2), z} := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.mp (hMX hm) t).mp htX
  have hOM1 : ∀ y ∈ OM, y ≠ 1 := by
    rintro _ ⟨m, -, rfl⟩ h1
    apply hgt
    have : t = 1 := by
      calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    group
  have hOMz : ∀ y ∈ OM, y ≠ z := by
    rintro _ ⟨m, -, rfl⟩
    exact hσ.conj_t_ne_z m
  have hzEinv : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ e ∈ E, m * (z * e) * m⁻¹ = z * (m * e * m⁻¹) := by
    intro m hm e _
    have := hσ.conj_z_of_mem_normalizer_T hm
    calc m * (z * e) * m⁻¹ = (m * z * m⁻¹) * (m * e * m⁻¹) := by group
      _ = z * (m * e * m⁻¹) := by rw [this]
  have hEcard : (E : Set X).ncard = Nat.card E := (Nat.card_coe_set_eq (E : Set X)).symm
  have hcardzE : ((fun e => z * e) '' (E : Set X)).ncard = Nat.card E := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective z), hEcard]
  by_cases htE' : t ∈ E
  ·
    have hsub : OM ⊆ (E : Set X) \ {1} := by
      intro y hy
      refine ⟨?_, hOM1 y hy⟩
      obtain ⟨m, hm, rfl⟩ := hy
      exact hME m hm t htE'
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr (one_mem E)), Set.ncard_singleton, hEcard]
      at this
    omega
  by_cases htzE : t ∈ (fun e => z * e) '' (E : Set X)
  ·
    obtain ⟨e₀, he₀, hte₀⟩ := htzE
    have hsub : OM ⊆ ((fun e => z * e) '' (E : Set X)) \ {z} := by
      intro y hy
      refine ⟨?_, hOMz y hy⟩
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨m * e₀ * m⁻¹, hME m hm e₀ he₀, ?_⟩
      beta_reduce at hte₀ ⊢
      rw [← hte₀, hzEinv m hm e₀ he₀]
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr
      (show z ∈ (fun e => z * e) '' (E : Set X) from ⟨1, one_mem E, mul_one z⟩)),
      Set.ncard_singleton, hcardzE] at this
    omega
  ·
    have hsub : OM ⊆ (closure {t, w ^ (orderOf w / 2), z} : Set X) \
        ((E : Set X) ∪ (fun e => z * e) '' (E : Set X)) := by
      intro y hy
      refine ⟨hOMX hy, ?_⟩
      obtain ⟨m, hm, rfl⟩ := hy
      rintro (hyE | ⟨e, he, hye⟩)
      · apply htE'
        have := hME m⁻¹ (inv_mem hm) _ hyE
        simpa [mul_assoc] using this
      · apply htzE
        refine ⟨m⁻¹ * e * m, ?_, ?_⟩
        · have := hME m⁻¹ (inv_mem hm) e he
          simpa using this
        · beta_reduce at hye ⊢
          have h1 := hzEinv m⁻¹ (inv_mem hm) e he
          rw [hye, inv_inv] at h1
          rw [show m⁻¹ * (m * t * m⁻¹) * m = t by group] at h1
          rw [h1]
    have hdisj : Disjoint (E : Set X) ((fun e => z * e) '' (E : Set X)) := by
      rw [Set.disjoint_left]
      rintro y hyE ⟨e, he, rfl⟩
      apply hzE
      have := mul_mem hyE (inv_mem he)
      simpa using this
    have hunion : ((E : Set X) ∪ (fun e => z * e) '' (E : Set X)).ncard = 2 * Nat.card E := by
      rw [Set.ncard_union_eq hdisj, hEcard, hcardzE]
      ring
    have hsubX : (E : Set X) ∪ (fun e => z * e) '' (E : Set X) ⊆
        (closure {t, w ^ (orderOf w / 2), z} : Set X) := by
      rintro y (hy | ⟨e, he, rfl⟩)
      · exact hEX hy
      · exact mul_mem hzX (hEX he)
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_sdiff hsubX, hunion,
      ← Nat.card_coe_set_eq (closure {t, w ^ (orderOf w / 2), z} : Set X)] at this
    have h2 := hσ.card_X_le
    have hde : Nat.card ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
        Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) := rfl
    omega

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
