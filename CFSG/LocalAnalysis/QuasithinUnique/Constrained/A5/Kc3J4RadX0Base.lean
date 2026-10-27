
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadCentBase

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4
open scoped commutatorElement

@[expose] def cm {Y : Type*} [Group Y] (a : Y) : Y →* Y := (MulAut.conj a).toMonoidHom

theorem cm_apply {Y : Type*} [Group Y] (a y : Y) : cm a y = a * y * a⁻¹ := rfl

theorem cm_injective {Y : Type*} [Group Y] (a : Y) : Function.Injective (cm a) :=
  (MulAut.conj a).injective

theorem cm_comp {Y : Type*} [Group Y] (a b : Y) : (cm a).comp (cm b) = cm (a * b) := by
  ext y
  simp [cm_apply, mul_assoc]

theorem cm_comp_inv {Y : Type*} [Group Y] (a : Y) : (cm a⁻¹).comp (cm a) = MonoidHom.id Y := by
  ext y
  simp [cm_apply, mul_assoc]

theorem centralizer_image_cm {Y : Type*} [Group Y] (a : Y) (S : Set Y) :
    Subgroup.centralizer (cm a '' S) = (Subgroup.centralizer S).map (cm a) := by
  ext c
  rw [Subgroup.mem_map]
  constructor
  · intro hc
    refine ⟨a⁻¹ * c * a, ?_, by simp [cm_apply, mul_assoc]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := Subgroup.mem_centralizer_iff.1 hc (a * s * a⁻¹) ⟨s, hs, rfl⟩
    calc s * (a⁻¹ * c * a) = a⁻¹ * ((a * s * a⁻¹) * c) * a := by group
      _ = a⁻¹ * (c * (a * s * a⁻¹)) * a := by rw [this]
      _ = (a⁻¹ * c * a) * s := by group
  · rintro ⟨c', hc', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc' s hs
    show a * s * a⁻¹ * (a * c' * a⁻¹) = a * c' * a⁻¹ * (a * s * a⁻¹)
    calc a * s * a⁻¹ * (a * c' * a⁻¹) = a * (s * c') * a⁻¹ := by group
      _ = a * (c' * s) * a⁻¹ := by rw [this]
      _ = a * c' * a⁻¹ * (a * s * a⁻¹) := by group

@[expose] def radOf {Y : Type*} [Group Y] (V : Subgroup Y) : Subgroup Y :=
  pCoreOf 2 (Subgroup.normalizer (V : Set Y))

theorem radOf_map_cm {Y : Type*} [Group Y] (m : Y) (V : Subgroup Y) :
    radOf (V.map (cm m)) = (radOf V).map (cm m) := by
  unfold radOf
  rw [show V.map (cm m) = V.map (MulAut.conj m).toMonoidHom from rfl,
    normalizer_map_equiv_eq (MulAut.conj m) V,
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj m)]
  rfl

@[expose] def RadV {Y : Type*} [Group Y] (x₀ : Y) (V : Subgroup Y) : Prop :=
  Subgroup.centralizer (radOf V : Set Y) ≤ radOf V ∧
    16 < (radOf V ⊓ Subgroup.centralizer ({x₀} : Set Y)).relIndex (radOf V)

theorem radV_of_centralizer {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y} (x₀ : Y)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hU : IsPGroup 2 (Subgroup.centralizer (V : Set Y)))
    (hidx : 16 < (Subgroup.centralizer (V : Set Y) ⊓
      Subgroup.centralizer ({x₀} : Set Y)).relIndex (Subgroup.centralizer (V : Set Y))) :
    RadV x₀ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVU : V ≤ Subgroup.centralizer (V : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hab b hb a ha
  have hUR : Subgroup.centralizer (V : Set Y) ≤ radOf V :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizer_le_normalizer_set _)
      (normalizer_le_normalizer_centralizer _) hU
  have hVR : V ≤ radOf V := hVU.trans hUR
  exact ⟨fun c hc => hUR (Subgroup.centralizer_le (fun x hx => hVR hx) hc),
    lt_of_lt_of_le hidx (relIndex_inf_mono hUR x₀)⟩

@[expose] def NonHAt {Y : Type} [Group Y] (Hy : Subgroup Y) (x₀ : Y) : Prop :=
  ∃ Vs : List (Subgroup Y), (∀ V ∈ Vs, RadV x₀ V) ∧
    ∀ L : Subgroup Y, D5Plus L → ⁅L, L⁆ = L → x₀ ∈ L →
      (∀ g : Y, ¬ L ≤ Hy.map (MulAut.conj g).toMonoidHom) →
      (¬ ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) →
      ∃ V ∈ Vs, ∃ k : Y, k * x₀ = x₀ * k ∧ pCoreOf 2 L = V.map (cm k)

theorem globalRad_of_nonHAt {Y : Type} [Group Y] [Finite Y] (Hy : Subgroup Y) {x₀ : Y}
    (hconj : ∀ x : Y, orderOf x = 5 → ∃ g : Y, g * x * g⁻¹ = x₀) (h : NonHAt Hy x₀)
    {L : Subgroup Y} (hL : D5Plus L) (hLp : ⁅L, L⁆ = L)
    (hnH : ∀ g : Y, ¬ L ≤ Hy.map (MulAut.conj g).toMonoidHom)
    (hno : ¬ ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) :
    Subgroup.centralizer (blockRadAbs L : Set Y) ≤ blockRadAbs L ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (blockRadAbs L ⊓ Subgroup.centralizer ({g} : Set Y)).relIndex (blockRadAbs L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxL, hx5⟩ : ∃ g ∈ L, orderOf g = 5 := by
    obtain ⟨V, Q, -, -, -, -, -, -, α, hα, -, -, -⟩ := hL
    exact exists_orderOf_five α hα
  obtain ⟨g, hg⟩ := hconj x hx5
  have hL' : D5Plus (L.map (cm g)) := d5Plus_map (cm g) (cm_injective g) hL
  have hLp' : ⁅L.map (cm g), L.map (cm g)⁆ = L.map (cm g) := by
    rw [← Subgroup.map_commutator, hLp]
  have hx0 : x₀ ∈ L.map (cm g) := ⟨x, hxL, by rw [cm_apply, hg]⟩
  have hnH' : ∀ h : Y, ¬ L.map (cm g) ≤ Hy.map (MulAut.conj h).toMonoidHom := by
    intro h' hle
    apply hnH (g⁻¹ * h')
    intro l hl
    obtain ⟨a, ha, hal⟩ := hle ⟨l, hl, rfl⟩
    have h1 : h' * a * h'⁻¹ = g * l * g⁻¹ := hal
    refine ⟨a, ha, ?_⟩
    show (g⁻¹ * h') * a * (g⁻¹ * h')⁻¹ = l
    calc (g⁻¹ * h') * a * (g⁻¹ * h')⁻¹ = g⁻¹ * (h' * a * h'⁻¹) * g := by group
      _ = l := by rw [h1]; group
  have hno' : ¬ ∃ y : Y, orderOf y = 2 ∧ ∀ l ∈ L.map (cm g), l * y = y * l := by
    rintro ⟨y, hyo, hyc⟩
    apply hno
    refine ⟨g⁻¹ * y * g, ?_, fun l hl => ?_⟩
    · have := (MulAut.conj g⁻¹).orderOf_eq y
      rw [MulAut.conj_apply] at this
      rw [← hyo, ← this]
      simp
    · have h1 := hyc (g * l * g⁻¹) ⟨l, hl, rfl⟩
      calc l * (g⁻¹ * y * g) = g⁻¹ * ((g * l * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * l * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * y * g * l := by group
  obtain ⟨Vs, hRad, hcl⟩ := h
  obtain ⟨V, hVs, k, hk, hV⟩ := hcl _ hL' hLp' hx0 hnH' hno'
  have hP : pCoreOf 2 L = V.map (cm (g⁻¹ * k)) := by
    have h1 : pCoreOf 2 (L.map (cm g)) = (pCoreOf 2 L).map (cm g) :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) L
    rw [h1] at hV
    have h2 := congrArg (Subgroup.map (cm g⁻¹)) hV
    rw [Subgroup.map_map, cm_comp_inv, Subgroup.map_id, Subgroup.map_map, cm_comp] at h2
    exact h2
  have hxm : cm (g⁻¹ * k) x₀ = x := by
    rw [cm_apply]
    calc g⁻¹ * k * x₀ * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * x₀ * k⁻¹) * g := by group
      _ = g⁻¹ * x₀ * g := by rw [hk]; group
      _ = x := by rw [← hg]; group
  have hR : blockRadAbs L = (radOf V).map (cm (g⁻¹ * k)) := by
    unfold blockRadAbs
    rw [hP]
    exact radOf_map_cm (g⁻¹ * k) V
  have hC : Subgroup.centralizer (blockRadAbs L : Set Y) =
      (Subgroup.centralizer (radOf V : Set Y)).map (cm (g⁻¹ * k)) := by
    rw [hR, ← centralizer_image_cm]
    rfl
  have hCx : Subgroup.centralizer ({x} : Set Y) =
      (Subgroup.centralizer ({x₀} : Set Y)).map (cm (g⁻¹ * k)) := by
    rw [← centralizer_image_cm, Set.image_singleton, hxm]
  have hf := cm_injective (g⁻¹ * k)
  obtain ⟨hR1, hR2⟩ := hRad V hVs
  refine ⟨?_, x, hxL, hx5, ?_⟩
  · rw [hC, hR]
    exact Subgroup.map_mono hR1
  · rw [hR, hCx, ← Subgroup.map_inf _ _ (cm (g⁻¹ * k)) hf,
      Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hR2

theorem exists_conj_five {Y : Type} [Group Y] [Finite Y] (hY : ¬ 5 ^ 2 ∣ Nat.card Y) {x₀ n : Y}
    (h5 : orderOf x₀ = 5) (hn : n * x₀ * n⁻¹ = x₀ ^ 2) {x : Y} (hx : orderOf x = 5) :
    ∃ g : Y, g * x * g⁻¹ = x₀ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : ¬ 5 ^ 2 ∣ Nat.card (⊤ : Subgroup Y) := by rwa [Subgroup.card_top]
  obtain ⟨m, -, k, hk⟩ := Kc3J4.exists_conj_of_orderOf_prime (p := 5) hP (Subgroup.mem_top x₀)
    (Subgroup.mem_top x) h5 hx
  have key : ∀ j : ℕ, n ^ j * x₀ * (n ^ j)⁻¹ = x₀ ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n ^ (j + 1) * x₀ * (n ^ (j + 1))⁻¹ = n * (n ^ j * x₀ * (n ^ j)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = n * x₀ ^ (2 ^ j) * n⁻¹ := by rw [ih]
        _ = (n * x₀ * n⁻¹) ^ (2 ^ j) := by rw [conj_pow]
        _ = x₀ ^ (2 ^ (j + 1)) := by rw [hn, ← pow_mul, pow_succ]; ring_nf
  have hmod : x₀ ^ k = x₀ ^ ((k % (orderOf x₀ : ℤ)).toNat) := by
    rw [← zpow_mod_orderOf, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      rw [h5]; norm_num))]
  obtain ⟨r, hr, hkr⟩ : ∃ r : ℕ, r < 5 ∧ x₀ ^ k = x₀ ^ r :=
    ⟨(k % (orderOf x₀ : ℤ)).toNat, by
      have h1 : k % (orderOf x₀ : ℤ) < 5 := by rw [h5]; exact Int.emod_lt_of_pos _ (by norm_num)
      omega, hmod⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [hkr, pow_zero, mul_one, mul_inv_cancel] at hk
    rw [hk, orderOf_one] at hx
    omega
  have hpow : ∀ j : ℕ, x₀ ^ (2 ^ j) = x₀ ^ (2 ^ j % 5) := fun j => by
    rw [← pow_mod_orderOf, h5]
  have hcase : ∃ j : ℕ, x₀ ^ r = n ^ j * x₀ * (n ^ j)⁻¹ := by
    interval_cases r
    · exact absurd rfl hr0
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [key, pow_one]⟩
    · refine ⟨3, ?_⟩
      rw [key, hpow]
      norm_num
    · refine ⟨2, ?_⟩
      rw [key, hpow]
      norm_num
  obtain ⟨j, hj⟩ := hcase
  refine ⟨(m * n ^ j)⁻¹, ?_⟩
  rw [hk, hkr, hj]
  group

@[expose] def J4NonHAt (x₀ : ↥J) : Prop := NonHAt Hj x₀

theorem j4GlobalRad_of_nonHAt {x₀ : ↥J}
    (hconj : ∀ x : ↥J, orderOf x = 5 → ∃ g : ↥J, g * x * g⁻¹ = x₀) (h : J4NonHAt x₀) :
    J4GlobalRad := by
  intro L hL hLp hnH hno
  exact globalRad_of_nonHAt (Y := ↥J) Hj hconj h hL hLp hnH hno

end CFSG.QuasithinUnique.A5
