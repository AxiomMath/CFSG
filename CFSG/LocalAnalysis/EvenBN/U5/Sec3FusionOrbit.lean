module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionLevi
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.BangOrbit
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionModel

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp Matrix
open CFSG.ABGLocalTools (IsSylowOf)

section Model

variable {f : ℕ} {K : Type} [Field K]

theorem squares_generate_Vsub (h : UnitaryFieldData 2 f K) :
    Vsub h ≤ closure {g | ∃ y ∈ Ssub h, g = y * y} := by
  have := h.charP
  set Q : Subgroup (hypSU h 2 1) := closure {g | ∃ y ∈ Ssub h, g = y * y} with hQ
  let InQ : Matrix (Fin 2) (Fin 2) K → Prop := fun Y => ∃ g ∈ Q, mat g = oddUni h 0 Y
  have hsq : ∀ x : Fin 2 → K, InQ (vecMulVec x fun j => h.bar (x j)) := by
    intro x
    obtain ⟨s, hs, C, hsm⟩ := exists_mem_Ssub_coord (hK := h) x
    refine ⟨s * s, subset_closure ⟨s, hs, rfl⟩, ?_⟩
    rw [mat_mul, hsm, oddUni_mul_self]
  have hadd : ∀ Y Y', InQ Y → InQ Y' → InQ (Y + Y') := by
    rintro Y Y' ⟨g, hg, hgm⟩ ⟨g', hg', hg'm⟩
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [mat_mul, hgm, hg'm, oddUni_mul]
    congr 1
    · simp
    · ext i j
      simp [vecMulVec]
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hdiag : ∀ (i : Fin 2) (y : K), h.bar y = y →
      InQ (Matrix.of fun a b => if a = i ∧ b = i then y else 0) := by
    intro i y hy
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨y, h.mem_fixedField.2 hy⟩
    have hc' : c * h.bar c = y := by
      have := congrArg Subtype.val hc
      simpa [UnitaryFieldData.norm] using this
    have := hsq (Pi.single i c)
    convert this using 1
    ext a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [vecMulVec, ha, hb, hc']
  have hoff : ∀ b : K, InQ (hermM h 0 0 b) := by
    intro b
    have e1 := hsq ![1, h.bar b]
    have e2 := hsq ![1, 0]
    have e3 := hsq ![0, h.bar b]
    have := hadd _ _ (hadd _ _ e1 e2) e3
    convert this using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermM, vecMulVec, h.bar_bar, h2]
  intro v hv
  obtain ⟨-, Y, hYm⟩ := hv
  have hYh := herm_of_mem_Vsub hYm
  obtain ⟨h00, h11, -⟩ := isHerm_iff.1 hYh
  have hY : Y = (Matrix.of fun a b => if a = (0 : Fin 2) ∧ b = 0 then Y 0 0 else 0) +
      (Matrix.of fun a b => if a = (1 : Fin 2) ∧ b = 1 then Y 1 1 else 0) +
        hermM h 0 0 (Y 0 1) := by
    rw [eq_hermM hYh]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermM]
  obtain ⟨g, hg, hgm⟩ : InQ Y := by
    rw [hY]
    exact hadd _ _ (hadd _ _ (hdiag 0 _ h00) (hdiag 1 _ h11)) (hoff _)
  rwa [mat_injective (hgm.trans hYm.symm)] at hg

end Model

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem square_mem_A₁ (d : Data G h) {y : G} (hy : y ∈ d.A₃) : y * y ∈ d.A₁ := by
  obtain ⟨s, ⟨hsU, x, C, hsm⟩, rfl⟩ := hy
  refine ⟨s * s, mem_Vsub_of_mat (by rw [mat_mul, hsm, oddUni_mul_self]), map_mul _ _ _⟩

theorem A₁_le_closure_squares (d : Data G h) :
    d.A₁ ≤ closure {z | ∃ y ∈ d.A₃, z = y * y} := by
  rintro _ ⟨v, hv, rfl⟩
  have h1 := Subgroup.map_mono (f := d.η) (squares_generate_Vsub h) ⟨v, hv, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨g, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨d.η y, ⟨y, hy, rfl⟩, map_mul _ _ _⟩

theorem B₁_le_B₃ (d : Data G h) : d.B₁ ≤ d.B₃ := sup_le_sup_left d.A₁_le_A₃ _

theorem A₃_le_B₃ (d : Data G h) : d.A₃ ≤ d.B₃ := le_sup_right

variable [Finite G]

theorem Hyp.zpow_t_eq (hd : d.Hyp) (i : ℤ) : d.t ^ i = 1 ∨ d.t ^ i = d.t := by
  have hk : d.t ^ i = d.t ^ (i % 2) := by
    rw [← zpow_mod_orderOf, hd.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one i with h0 | h0
  · left; rw [hk, h0, zpow_zero]
  · right; rw [hk, h0, zpow_one]

theorem Hyp.A₃_le_centralizer_zpowers (hd : d.Hyp) :
    d.A₃ ≤ centralizer (zpowers d.t : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hat : d.t * a = a * d.t :=
    (mem_centralizer_iff.1 hd.t_mem a (d.A₃_le_P.trans d.P_le_L ha)).symm
  exact (Commute.zpow_left hat k).eq

theorem Hyp.exists_of_mem_B₃ (hd : d.Hyp) {z : G} (hz : z ∈ d.B₃) :
    ∃ a ∈ d.A₃, z = a ∨ z = d.t * a := by
  obtain ⟨x, hx, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => mem_centralizer_iff.1 (hd.A₃_le_centralizer_zpowers hy) x hx) hz
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨a, ha, ?_⟩
  rcases hd.zpow_t_eq i with h1 | h1
  · left; rw [h1, one_mul]
  · right; rw [h1]

theorem Hyp.exists_of_mem_B₁ (hd : d.Hyp) {z : G} (hz : z ∈ d.B₁) :
    ∃ a ∈ d.A₁, z = a ∨ z = d.t * a := by
  obtain ⟨x, hx, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => mem_centralizer_iff.1 (hd.A₁_le_centralizer_zpowers hy) x hx) hz
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨a, ha, ?_⟩
  rcases hd.zpow_t_eq i with h1 | h1
  · left; rw [h1, one_mul]
  · right; rw [h1]

theorem Hyp.square_mem_A₁_of_mem_B₃ (hd : d.Hyp) {z : G} (hz : z ∈ d.B₃) : z * z ∈ d.A₁ := by
  obtain ⟨a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₃ hz
  · exact d.square_mem_A₁ ha
  · have hat : a * d.t = d.t * a :=
      mem_centralizer_iff.1 hd.t_mem a (d.A₃_le_P.trans d.P_le_L ha)
    have : d.t * a * (d.t * a) = a * a := by
      calc d.t * a * (d.t * a) = d.t * (a * d.t) * a := by group
        _ = d.t * (d.t * a) * a := by rw [hat]
        _ = (d.t * d.t) * (a * a) := by group
        _ = a * a := by rw [hd.t_mul_t, one_mul]
    rw [this]
    exact d.square_mem_A₁ ha

theorem Hyp.conj_mem_A₁ (hd : d.Hyp) {n : G} (hn : n ∈ normalizer (d.B₃ : Set G)) {a : G}
    (ha : a ∈ d.A₁) : n⁻¹ * a * n ∈ d.A₁ := by
  have hn' : n⁻¹ ∈ normalizer (d.B₃ : Set G) := inv_mem hn
  have key : ∀ z ∈ closure {z | ∃ y ∈ d.A₃, z = y * y}, n⁻¹ * z * n ∈ d.A₁ := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have hy' : n⁻¹ * y * n ∈ d.B₃ := by
        have := (mem_normalizer_iff.1 hn' y).1 (d.A₃_le_B₃ hy)
        rwa [inv_inv] at this
      rw [show n⁻¹ * (y * y) * n = (n⁻¹ * y * n) * (n⁻¹ * y * n) by group]
      exact hd.square_mem_A₁_of_mem_B₃ hy'
    | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
    | mul x y _ _ hx hy =>
      rw [show n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show n⁻¹ * x⁻¹ * n = (n⁻¹ * x * n)⁻¹ by group]
      exact inv_mem hx
  exact key a (d.A₁_le_closure_squares ha)

theorem Hyp.B₃_le_centralizer (hd : d.Hyp) : d.B₃ ≤ centralizer ({d.t} : Set G) :=
  sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    ((d.A₃_le_P.trans d.P_le_L).trans hd.L_le_centralizer)

theorem Hyp.B₁_commute_B₃ (hd : d.Hyp) : ∀ b ∈ d.B₁, ∀ z ∈ d.B₃, b * z = z * b := by
  intro b hb z hz
  have htB : d.t ∈ d.B₁ := mem_sup_left (mem_zpowers _)
  have hle : d.B₃ ≤ centralizer ({b} : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (hd.B₁_le_R hb).2 d.t htB)
    · intro a ha
      exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hd.A₃_le_R ha).2 b hb).symm
  exact (mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem Hyp.mem_B₁_of_central (hd : d.Hyp) {z : G} (hz : z ∈ d.B₃)
    (hc : ∀ b ∈ d.B₃, b * z = z * b) : z ∈ d.B₁ := by
  obtain ⟨a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₃ hz
  · exact mem_sup_right (d.mem_A₁_of_commute ha fun b hb => hc b (d.A₃_le_B₃ hb))
  · have ha1 : a ∈ d.A₁ := d.mem_A₁_of_commute ha fun b hb => by
      have h1 := hc b (d.A₃_le_B₃ hb)
      have htb : b * d.t = d.t * b :=
        mem_centralizer_singleton_iff.1 (hd.B₃_le_centralizer (d.A₃_le_B₃ hb))
      have h2 : d.t * (b * a) = d.t * (a * b) := by
        calc d.t * (b * a) = (b * d.t) * a := by rw [htb, mul_assoc]
          _ = b * (d.t * a) := by group
          _ = d.t * a * b := h1
          _ = d.t * (a * b) := by group
      exact mul_left_cancel h2
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ha1)

theorem Hyp.normalizer_B₃_le (hd : d.Hyp) :
    normalizer (d.B₃ : Set G) ≤ normalizer (d.B₁ : Set G) := by
  have key : ∀ n ∈ normalizer (d.B₃ : Set G), ∀ z ∈ d.B₁, n * z * n⁻¹ ∈ d.B₁ := by
    intro n hn z hz
    have hzB : n * z * n⁻¹ ∈ d.B₃ := (mem_normalizer_iff.1 hn z).1 (d.B₁_le_B₃ hz)
    refine hd.mem_B₁_of_central hzB fun b hb => ?_
    have hb' : n⁻¹ * b * n ∈ d.B₃ := by
      have := (mem_normalizer_iff.1 (inv_mem hn) b).1 hb
      rwa [inv_inv] at this
    have h1 := hd.B₁_commute_B₃ z hz _ hb'
    calc b * (n * z * n⁻¹) = n * ((n⁻¹ * b * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * b * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * b := by group
  intro n hn
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key n hn z, fun hz => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hz
  rwa [show n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z by group] at this

theorem Hyp.R_eq_B₃ (hd : d.Hyp) (hI : InvolutionsConjIntoV h) (hO : OuterInvolutionFusion h)
    (hP : PerfectLeInn h) (hC : TwoCentralizerV h) :
    d.T ⊓ centralizer (d.B₁ : Set G) = d.B₃ := by
  apply le_antisymm
  · have h1 := hd.R_le hC
    rw [hd.sec3_1_two hI hO hP hC, sup_comm] at h1
    exact h1
  · exact sup_le (zpowers_le.2 (hd.B₁_le_R (mem_sup_left (mem_zpowers _)))) hd.A₃_le_R

theorem Hyp.conj_mem_tA₁ (hd : d.Hyp) {n : G} (hn : n ∈ normalizer (d.B₃ : Set G)) :
    ∃ a ∈ d.A₁, n⁻¹ * d.t * n = d.t * a := by
  have htB₁ : d.t ∈ d.B₁ := mem_sup_left (mem_zpowers _)
  have hB₁ : n⁻¹ * d.t * n ∈ d.B₁ := by
    have := (mem_normalizer_iff.1 (hd.normalizer_B₃_le (inv_mem hn)) d.t).1 htB₁
    rwa [inv_inv] at this
  obtain ⟨a, ha, h1 | h1⟩ := hd.exists_of_mem_B₁ hB₁
  · exfalso
    have hA := hd.conj_mem_A₁ (inv_mem hn) (h1 ▸ ha : n⁻¹ * d.t * n ∈ d.A₁)
    rw [show n⁻¹⁻¹ * (n⁻¹ * d.t * n) * n⁻¹ = d.t by group] at hA
    exact hd.t_not_mem_A₁ hA
  · exact ⟨a, ha, h1⟩

theorem Hyp.sec3_1_three (hd : d.Hyp) (hI : InvolutionsConjIntoV h)
    (hO : OuterInvolutionFusion h) (hP : PerfectLeInn h) (hC : TwoCentralizerV h)
    (hLev : LeviOrbitsV h) :
    {x | ∃ n ∈ normalizer (d.B₃ : Set G), x = n⁻¹ * d.t * n} = {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) = {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      ∀ g : G, g⁻¹ * d.t * g ∉ d.L := by
  set Ω : Set G := {x | ∃ n ∈ normalizer (d.B₃ : Set G), x = n⁻¹ * d.t * n} with hΩ
  set tA : Set G := {x | ∃ a ∈ d.A₁, x = d.t * a} with htA
  have hR := hd.R_eq_B₃ hI hO hP hC
  have hfus : ∀ g : G, g⁻¹ * d.t * g ∈ d.B₁ → g⁻¹ * d.t * g ∈ Ω := by
    intro g hg
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_eq_of_weakly_closed_in hd.T_syl
      (inf_le_left : d.T ⊓ centralizer (d.B₁ : Set G) ≤ d.T) hd.weakly_closed_R (g := g)
      (fun r hr => (mem_centralizer_iff.1 hr.2 _ hg).symm)
    rw [hR] at hn
    exact ⟨n, hn, hnt.symm⟩
  have hΩtA : Ω ⊆ tA := by
    rintro _ ⟨n, hn, rfl⟩
    exact hd.conj_mem_tA₁ hn
  have htA_B₁ : tA ⊆ (d.B₁ : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ha)
  have hfin : ∀ s : Set G, s.Finite := fun s => s.toFinite
  have hcard_tA : tA.ncard = (2 ^ f) ^ 4 := by
    have : tA = (fun a => d.t * a) '' (d.A₁ : Set G) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    rw [this, Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
    exact d.card_A₁
  set X : Set (hypSU h 2 1) := {v | v ∈ Vsub h ∧ v ≠ 1 ∧ d.t * d.η v ∈ Ω} with hX
  have hXsub : X ⊆ (Vsub h : Set (hypSU h 2 1)) \ {1} := fun v hv => ⟨hv.1, hv.2.1⟩
  have hXinv : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ v ∈ X,
      lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ ∈ X := by
    intro A hA v hv
    set ℓ := lev (hK := h) A hA
    refine ⟨lev_conj_mem_Vsub A hA hv.1, fun h1 => hv.2.1 ?_, ?_⟩
    · calc v = ℓ⁻¹ * (ℓ * v * ℓ⁻¹) * ℓ := by group
        _ = 1 := by rw [h1]; group
    · obtain ⟨n, hn, hnx⟩ := hv.2.2
      have hℓt : d.η ℓ * d.t = d.t * d.η ℓ :=
        (mem_centralizer_iff.1 hd.t_mem _ (d.η_mem ℓ))
      have hℓN : d.η ℓ ∈ normalizer (d.B₃ : Set G) := by
        refine mem_normalizer_of_conj_le fun z hz => ?_
        obtain ⟨a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₃ hz
        · obtain ⟨s₀, hs₀, rfl⟩ := ha
          refine d.A₃_le_B₃ ⟨ℓ * s₀ * ℓ⁻¹, lev_conj_mem_Ssub A hA hs₀, ?_⟩
          rw [map_mul, map_mul, map_inv]
        · obtain ⟨s₀, hs₀, rfl⟩ := ha
          have h3 : d.η ℓ * (d.t * d.η s₀) * (d.η ℓ)⁻¹ = d.t * d.η (ℓ * s₀ * ℓ⁻¹) := by
            rw [map_mul, map_mul, map_inv]
            calc d.η ℓ * (d.t * d.η s₀) * (d.η ℓ)⁻¹ = (d.η ℓ * d.t) * d.η s₀ * (d.η ℓ)⁻¹ := by
                  group
              _ = (d.t * d.η ℓ) * d.η s₀ * (d.η ℓ)⁻¹ := by rw [hℓt]
              _ = d.t * (d.η ℓ * d.η s₀ * (d.η ℓ)⁻¹) := by group
          rw [h3]
          exact mul_mem (mem_sup_left (mem_zpowers _))
            (mem_sup_right ⟨ℓ * s₀ * ℓ⁻¹, lev_conj_mem_Ssub A hA hs₀, rfl⟩)
      refine ⟨n * (d.η ℓ)⁻¹, mul_mem hn (inv_mem hℓN), ?_⟩
      have h4 : d.t * d.η (ℓ * v * ℓ⁻¹) = d.η ℓ * (d.t * d.η v) * (d.η ℓ)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        calc d.t * (d.η ℓ * d.η v * (d.η ℓ)⁻¹) = (d.t * d.η ℓ) * d.η v * (d.η ℓ)⁻¹ := by
              group
          _ = (d.η ℓ * d.t) * d.η v * (d.η ℓ)⁻¹ := by rw [hℓt]
          _ = d.η ℓ * (d.t * d.η v) * (d.η ℓ)⁻¹ := by group
      rw [h4, hnx]
      group
  have hXcard := hLev hd.two_le hd.center_hypPSU X hXsub hXinv
  have htΩ : d.t ∈ Ω := ⟨1, one_mem _, by group⟩
  have himage : Ω \ {d.t} = (fun v => d.t * d.η v) '' X := by
    ext x
    constructor
    · rintro ⟨hxΩ, hxt⟩
      obtain ⟨a, ⟨v, hv, rfl⟩, rfl⟩ := hΩtA hxΩ
      refine ⟨v, ⟨hv, fun h1 => hxt ?_, hxΩ⟩, rfl⟩
      rw [h1, map_one, mul_one]
      rfl
    · rintro ⟨v, hv, rfl⟩
      refine ⟨hv.2.2, fun h1 => hv.2.1 ?_⟩
      have h2 : d.η v = 1 := by
        have := h1
        simp only [Set.mem_singleton_iff] at this
        exact mul_eq_left.1 this
      exact d.η_injOn (Vsub_le_Ssub.trans Ssub_le_Usub hv.1) (one_mem _) (by rw [h2, map_one])
  have hinj : Set.InjOn (fun v => d.t * d.η v) X := by
    intro v hv w hw hvw
    exact d.η_injOn (Vsub_le_Ssub.trans Ssub_le_Usub hv.1)
      (Vsub_le_Ssub.trans Ssub_le_Usub hw.1) (mul_left_cancel hvw)
  have hΩcard : Ω.ncard = X.ncard + 1 := by
    rw [← Set.ncard_sdiff_singleton_add_one htΩ (hfin Ω), himage, hinj.ncard_image]
  have hXne : X.ncard ≠ 0 := by
    obtain ⟨g, hgB, hgne⟩ := hd.exists_conj_mem_B₁ hI hO hP
    have hx : g⁻¹ * d.t * g ∈ Ω \ {d.t} := ⟨hfus g hgB, hgne⟩
    rw [himage] at hx
    obtain ⟨v, hv, -⟩ := hx
    have := CFSG.RankThree.PartOne.U5K.Hyp.finite_hypSU h
    exact (Set.ncard_pos X.toFinite).2 ⟨v, hv⟩ |>.ne'
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hΩ3 : Ω.ncard = (2 ^ f) ^ 3 - (2 ^ f) ^ 2 + 2 ^ f ∨
      Ω.ncard = (2 ^ f) ^ 4 - (2 ^ f) ^ 3 + (2 ^ f) ^ 2 - 2 ^ f + 1 ∨
      Ω.ncard = (2 ^ f) ^ 4 := by
    rw [hΩcard, U4.pow_three_sub_eq_one_add hq1, U4.pow_four_sub_eq_one_add hq1]
    rw [← Nat.card_coe_set_eq] at hXne
    rw [← Nat.card_coe_set_eq]
    rcases hXcard with h0 | h1 | h2 | h3
    · exact absurd h0 hXne
    · left; rw [h1]; ring
    · right; left; rw [h2]; ring
    · right; right
      rw [h3]
      have : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
      omega
  have hB₁card : Nat.card d.B₁ = 2 ^ (4 * f + 1) := by
    rw [hd.card_B₁, ← pow_mul, pow_succ, mul_comm 4 f]
    ring
  have hBang := U4.card_conj_set_eq_of_bang hd.two_le hB₁card hd.normalizer_B₃_le
    (mem_sup_left (mem_zpowers _) : d.t ∈ d.B₁) (by rw [Nat.card_coe_set_eq]; exact hΩ3)
  rw [Nat.card_coe_set_eq] at hBang
  have hΩeq : Ω = tA :=
    Set.eq_of_subset_of_ncard_le hΩtA (by rw [hcard_tA, ← hBang]) (hfin tA)
  have hGB : {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) = tA := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨g, rfl⟩, hgB⟩
      rw [← hΩeq]
      exact hfus g hgB
    · intro x hx
      refine ⟨?_, htA_B₁ hx⟩
      rw [← hΩeq] at hx
      obtain ⟨n, -, rfl⟩ := hx
      exact ⟨n, rfl⟩
  refine ⟨hΩeq, hGB, fun g hgL => ?_⟩
  have h2 : g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = 1 := by
    calc g⁻¹ * d.t * g * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g := by group
      _ = 1 := by rw [hd.t_mul_t]; group
  obtain ⟨m, -, hmA⟩ := hd.exists_conj_mem_A₁ hI hgL h2
  have hmB : (g * m)⁻¹ * d.t * (g * m) ∈ {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) := by
    refine ⟨⟨g * m, rfl⟩, ?_⟩
    rw [show (g * m)⁻¹ * d.t * (g * m) = m⁻¹ * (g⁻¹ * d.t * g) * m by group]
    exact mem_sup_right hmA
  rw [hGB] at hmB
  obtain ⟨a, ha, hEq⟩ := hmB
  rw [show (g * m)⁻¹ * d.t * (g * m) = m⁻¹ * (g⁻¹ * d.t * g) * m by group] at hEq
  apply hd.t_not_mem_A₁
  have : d.t = (m⁻¹ * (g⁻¹ * d.t * g) * m) * a⁻¹ := by rw [hEq]; group
  rw [this]
  exact mul_mem hmA (inv_mem ha)

end Data

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec3_1 (hd : d.Hyp) (hO : OuterInvolutionFusion h) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t ∧
      (∀ X : Subgroup G, X ≤ centralizer ({d.t} : Set G) → CFSG.IsElementaryAbelian 2 X →
        Nat.card X ≤ 2 * (2 ^ f) ^ 4) ∧
      (∀ X : Subgroup G, X ≤ d.T → CFSG.IsElementaryAbelian 2 X →
        Nat.card X = 2 * (2 ^ f) ^ 4 → X = d.B₁) ∧
      {x | ∃ n ∈ normalizer (d.B₃ : Set G), x = n⁻¹ * d.t * n} =
        {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) = {x | ∃ a ∈ d.A₁, x = d.t * a} ∧
      ∀ g : G, g⁻¹ * d.t * g ∉ d.L := by
  obtain ⟨-, -, -, h1, h1'⟩ := hd.sec3_1_one
  obtain ⟨h3, h3', h3''⟩ := hd.sec3_1_three (involutionsConjIntoV h) hO (perfectLeInn h)
    (twoCentralizerV h) (leviOrbitsV h)
  exact ⟨hd.sec3_1_two (involutionsConjIntoV h) hO (perfectLeInn h) (twoCentralizerV h), h1,
    h1', h3, h3', h3''⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
