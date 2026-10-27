module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBPerfect
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CoverFixed
public import CFSG.LargeExtraspecial.S8CBFL3
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ElementaryAbelianCard

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.OddStandard.Seitz77 (Datum)
open scoped commutatorElement

section Conj

variable {G : Type*} [Group G]

theorem exists_fixed_of_mem_normalizer [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f) {X : Subgroup G}
    (π : X →* projectiveSL 3 K) (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hodd : Odd (Nat.card π.ker)) {t : G} (ht : t ∈ normalizer (X : Set G)) (htt : t * t = 1) :
    (∃ E : Subgroup G, E ≤ X ⊓ centralizer ({t} : Set G) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
        (∀ a ∈ E, a * a = 1) ∧ Nat.card E = Nat.card K ^ 2) ∨
      ∃ D : Subgroup G, D ≤ X ⊓ centralizer ({t} : Set G) ∧ ⁅D, D⁆ = D ∧
        ∃ c ∈ D, orderOf c = 2 :=
  (exists_fixed_four_of_mem_normalizer hf hK π hπ hker hodd ht htt).imp id
    fun ⟨D, hD, hDp, hc, _⟩ => ⟨D, hD, hDp, hc⟩

end Conj

section Contradiction

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem isElemAbelian_two_of_forall {H : Type*} [Group H] {E : Subgroup H}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun a ha => by rw [sq]; exact h2 a ha⟩

theorem Hyp.card_le_two_of_le_centralizer (h : Hyp G A f) {E : Subgroup G}
    (hEC : E ≤ centralizer (A : Set G)) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := E.subgroupOf (centralizer (A : Set G)) with hE'
  have hp : IsPGroup 2 E' := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simp only [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    exact hE2 _ (mem_subgroupOf.1 x.2)))⟩
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hcyc := h.cyc S
  have h1 := card_le_two_of_isCyclic (E'.subgroupOf S) fun y hy => Subtype.ext (Subtype.ext (by
    simp only [sq, Subgroup.coe_mul, Subgroup.coe_one]
    exact hE2 _ (mem_subgroupOf.1 (mem_subgroupOf.1 hy))))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv] at h1

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def actRange (e : A ≃* projectiveSL 3 K) {E : Subgroup G}
    (hEN : E ≤ normalizer (A : Set G)) : Subgroup (MulAut (projectiveSL 3 K)) :=
  ((act e).comp (inclusion hEN)).range

theorem Hyp.card_le_eight_mul (h : Hyp G A f) (hK : Nat.card K = 2 ^ f)
    (e : A ≃* projectiveSL 3 K) {E : Subgroup G} (hEN : E ≤ normalizer (A : Set G))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a * a = 1) :
    Nat.card E ≤ 8 * Nat.card ↥(actRange e hEN ⊓
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) := by
  have hf1 : 1 ≤ f := by have := h.three_le; omega
  set φ := (act e).comp (inclusion hEN) with hφ
  have hR : IsElemAbelian 2 φ.range := isElemAbelian_two_of_forall
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have hxy : x * y = y * x := Subtype.ext (hEc x x.2 y y.2)
      rw [← map_mul, ← map_mul, hxy])
    (by
      rintro _ ⟨x, rfl⟩
      have hx2 : x * x = 1 := Subtype.ext (hE2 x x.2)
      rw [← map_mul, hx2, map_one])
  have hF7 := card_le_four_mul_card_inf_range hf1 hK hR
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map E.subtype ≤ centralizer (A : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (act_eq_one_iff e _).1 hx
    have h2 := h.card_le_two_of_le_centralizer hle (by
      rintro _ ⟨x, -, rfl⟩
      exact hE2 x x.2)
    rwa [Subgroup.card_map_of_injective E.subtype_injective] at h2
  have hcard := Subgroup.card_ker_mul_card_range φ
  change Nat.card E ≤ 8 * Nat.card ↥(φ.range ⊓
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ 2 * (4 * Nat.card ↥(φ.range ⊓
          (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)) :=
        Nat.mul_le_mul hker hF7
    _ = 8 * Nat.card ↥(φ.range ⊓
          (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) := by ring

variable [CharP K 2]

omit [Finite G] in
theorem card_actRange_inf_le (e : A ≃* projectiveSL 3 K) {E : Subgroup G}
    (hEN : E ≤ normalizer (A : Set G)) (hE2 : ∀ a ∈ E, a * a = 1) :
    Nat.card ↥(actRange e hEN ⊓
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) ≤ Nat.card K ^ 2 := by
  have hinj := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  set I := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  set F := (actRange e hEN ⊓ I).comap
    (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K))
  have hmap : F.map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) =
      actRange e hEN ⊓ I := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 inf_le_right]
  have hF2 : ∀ a ∈ F, a * a = 1 := by
    intro a ha
    obtain ⟨⟨x, hx⟩, -⟩ := ha
    have hx2 : x * x = 1 := Subtype.ext (hE2 x x.2)
    apply hinj
    rw [map_mul, map_one]
    change MulAut.conj a * MulAut.conj a = 1
    rw [← hx, ← map_mul, hx2, map_one]
  rw [← hmap, Subgroup.card_map_of_injective hinj]
  exact card_le_sq_of_mul_self hF2

theorem Hyp.perfect_le_of_le_centralizer (h : Hyp G A f) (d : Datum A) {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (hPt : P ≤ centralizer ({d.t} : Set G)) : P ≤ A := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := h.exists_model
  have hOut : Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer A) := by
    have := (UnitaryHigher.linear_higher_schreier (K := K) (n := 3) le_rfl).2
    exact ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  exact SeitzReduction.perfect_le_of_standard h.standard ⟨d.R, h.cyc d.R⟩ hOut d.t_mem_K
    d.sector.t_order (h.core _ d.sector.t_order) hP hPt

@[expose] def FixesLarge (t : G) (q : ℕ) (X : Subgroup G) : Prop :=
  (∃ E : Subgroup G, E ≤ X ⊓ centralizer ({t} : Set G) ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a * a = 1) ∧ Nat.card E = q ^ 2) ∨
    ∃ D : Subgroup G, D ≤ X ⊓ centralizer ({t} : Set G) ∧ ⁅D, D⁆ = D ∧ ∃ c ∈ D, orderOf c = 2

omit [Finite G] in
theorem eq_bot_of_le_centralizer (hKc : Nat.card K = 2 ^ f) (e : A ≃* projectiveSL 3 K) {c : G}
    (hcA : c ∈ A) (hc2 : c * c = 1) (hc1 : c ≠ 1) {P : Subgroup G}
    (hP : P ≤ A ⊓ centralizer ({c} : Set G)) (hPp : ⁅P, P⁆ = P) : P = ⊥ := by
  have hord : orderOf (e ⟨c, hcA⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  have hS := CFSG.LargeExtraspecial.S8.isSolvable_centralizer_projectiveSL_three hKc hord
  let ψ : P →* centralizer ({e ⟨c, hcA⟩} : Set (projectiveSL 3 K)) :=
    { toFun := fun x => ⟨e ⟨x, (hP x.2).1⟩, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.1 (hP x.2).2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        rw [← map_mul]
        rfl) }
  have hψ : Function.Injective ψ := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    have h2 := congrArg Subtype.val (e.injective h1)
    exact Subtype.ext h2
  have : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective hψ
  exact eq_bot_of_commutator_eq_of_isSolvable hPp

theorem Hyp.card_le_eight_of_centralizes (h : Hyp G A f) (hKc : Nat.card K = 2 ^ f)
    (e : A ≃* projectiveSL 3 K) {D E : Subgroup G} (hDA : D ≤ A) (hDp : ⁅D, D⁆ = D)
    (hD : ∃ c ∈ D, orderOf c = 2) (hEN : E ≤ normalizer (A : Set G))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a * a = 1)
    (hED : ∀ x ∈ E, ∀ y ∈ D, x * y = y * x) : Nat.card E ≤ 8 := by
  have hbot : actRange e hEN ⊓
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨x, rfl⟩, hxI⟩
    have hxI' : act e ⟨x, hEN x.2⟩ ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := hxI
    have hxAC := (act_mem_range_iff e (hEN x.2)).1 hxI'
    obtain ⟨a, haA, k, hkC, hxak⟩ := OddStandard.Seitz77.mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.1 hk a ha) hxAC
    have hak : a * k = k * a := mem_centralizer_iff.1 hkC a haA
    have haD : D ≤ A ⊓ centralizer ({a} : Set G) := by
      intro y hy
      refine ⟨hDA hy, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : (x : G) * y = y * x := hED x x.2 y hy
      have h2 : k * y = y * k := (mem_centralizer_iff.1 hkC y (hDA hy)).symm
      have hxa : a = x * k⁻¹ := by rw [hxak]; group
      have h2' : k⁻¹ * y = y * k⁻¹ := by
        calc k⁻¹ * y = k⁻¹ * (y * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * y) * k⁻¹ := by rw [h2]
          _ = y * k⁻¹ := by group
      rw [hxa]
      calc y * (x * k⁻¹) = (y * x) * k⁻¹ := by group
        _ = x * y * k⁻¹ := by rw [h1]
        _ = x * (y * k⁻¹) := by group
        _ = x * k⁻¹ * y := by rw [← h2']; group
    have ha2 : a * a = 1 := by
      have hx2 : (a * k) * (a * k) = 1 := by rw [← hxak]; exact hE2 x x.2
      have hkk : a * a = (k * k)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc a * a * (k * k) = a * (a * k) * k := by group
          _ = a * (k * a) * k := by rw [hak]
          _ = (a * k) * (a * k) := by group
          _ = 1 := hx2
      have hkC' : (k * k)⁻¹ ∈ centralizer (A : Set G) := inv_mem (mul_mem hkC hkC)
      have hmem : a * a ∈ A ⊓ centralizer (A : Set G) := ⟨mul_mem haA haA, by rw [hkk]; exact hkC'⟩
      rw [h.facts.center_eq_bot, mem_bot] at hmem
      exact hmem
    have ha1 : a = 1 := by
      by_contra ha1
      obtain ⟨c, hcD, hc2⟩ := hD
      have := eq_bot_of_le_centralizer hKc e haA ha2 ha1 haD hDp
      rw [this, mem_bot] at hcD
      rw [hcD, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    rw [ha1, one_mul] at hxak
    have hxC : (x : G) ∈ centralizer (A : Set G) := hxak ▸ hkC
    exact (act_eq_one_iff e _).2 hxC
  have h8 := h.card_le_eight_mul hKc e hEN hEc hE2
  rw [hbot, Subgroup.card_bot, mul_one] at h8
  exact h8

theorem Hyp.false_of_fixesLarge (h : Hyp G A f) (d : Datum A) {X Y : Subgroup G}
    (hXY : Y ≤ centralizer (X : Set G)) (hXYinv : ∀ z ∈ X ⊓ Y, z * z = 1 → z = 1)
    (hX : FixesLarge d.t (2 ^ f) X) (hY : FixesLarge d.t (2 ^ f) Y) : False := by
  have hf3 := h.three_le
  obtain ⟨K, _, _, _, hKc, ⟨e⟩⟩ := h.exists_model
  have hq8 : 8 ≤ 2 ^ f :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hq64 : 8 < (2 ^ f) ^ 2 := by
    calc 8 < 8 * 8 := by norm_num
      _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq8 hq8
      _ = (2 ^ f) ^ 2 := (sq _).symm
  have hCt : centralizer ({d.t} : Set G) ≤ normalizer (A : Set G) :=
    (OddStandard.centralizer_t_facts d.sector).1
  have hperf : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer ({d.t} : Set G) → P ≤ A :=
    fun P hP hPt => h.perfect_le_of_le_centralizer d hP hPt
  have hYX : X ≤ centralizer (Y : Set G) := le_centralizer_iff.1 hXY
  have hDE : ∀ {D E : Subgroup G}, D ≤ centralizer ({d.t} : Set G) → ⁅D, D⁆ = D →
      (∃ c ∈ D, orderOf c = 2) → E ≤ centralizer ({d.t} : Set G) →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E = (2 ^ f) ^ 2 →
      (∀ x ∈ E, ∀ y ∈ D, x * y = y * x) → False := by
    intro D E hDt hDp hD hEt hEc hE2 hEcard hED
    have h8 := h.card_le_eight_of_centralizes hKc e (hperf D hDp hDt) hDp hD (hEt.trans hCt)
      hEc hE2 hED
    rw [hEcard] at h8
    exact absurd h8 (not_le.2 hq64)
  rcases hX with ⟨EX, hEX, hEXc, hEX2, hEXcard⟩ | ⟨DX, hDX, hDXp, cX, hcX, hcX2⟩ <;>
    rcases hY with ⟨EY, hEY, hEYc, hEY2, hEYcard⟩ | ⟨DY, hDY, hDYp, cY, hcY, hcY2⟩
  ·
    have hc : ∀ x ∈ EX, ∀ y ∈ EY, x * y = y * x := fun x hx y hy =>
      mem_centralizer_iff.1 (hXY (hEY hy).1) x (hEX hx).1
    have hinf : EX ⊓ EY = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzX, hzY⟩
      exact hXYinv z ⟨(hEX hzX).1, (hEY hzY).1⟩ (hEX2 z hzX)
    set E := EX ⊔ EY with hE
    have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc ha
      obtain ⟨x', hx', y', hy', rfl⟩ := exists_mul_of_mem_sup hc hb
      have h1 := hEXc x hx x' hx'
      have h2 := hEYc y hy y' hy'
      have h3 := hc x' hx' y hy
      have h4 := hc x hx y' hy'
      calc x * y * (x' * y') = x * (y * x') * y' := by group
        _ = x * (x' * y) * y' := by rw [← h3]
        _ = (x * x') * (y * y') := by group
        _ = (x' * x) * (y' * y) := by rw [h1, h2]
        _ = x' * (x * y') * y := by group
        _ = x' * (y' * x) * y := by rw [h4]
        _ = x' * y' * (x * y) := by group
    have hE2 : ∀ a ∈ E, a * a = 1 := by
      intro a ha
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc ha
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hc x hx y hy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hEX2 x hx, hEY2 y hy, one_mul]
    have hEN : E ≤ normalizer (A : Set G) :=
      (sup_le (fun x hx => (hEX hx).2) fun y hy => (hEY hy).2).trans hCt
    have hcard : Nat.card E = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by
      rw [hE, card_sup_of_commute hc hinf, hEXcard, hEYcard]
    have h8 := h.card_le_eight_mul hKc e hEN hEc hE2
    have hI := card_actRange_inf_le e hEN hE2
    rw [hKc] at hI
    rw [hcard] at h8
    have h1 : (2 ^ f) ^ 2 * (2 ^ f) ^ 2 ≤ 8 * (2 ^ f) ^ 2 := h8.trans (Nat.mul_le_mul_left 8 hI)
    have h2 : (2 ^ f) ^ 2 ≤ 8 :=
      Nat.le_of_mul_le_mul_right h1 (by positivity)
    exact absurd h2 (not_le.2 hq64)
  · exact hDE (fun y hy => (hDY hy).2) hDYp ⟨cY, hcY, hcY2⟩ (fun x hx => (hEX hx).2) hEXc hEX2
      hEXcard fun x hx y hy => mem_centralizer_iff.1 (hXY (hDY hy).1) x (hEX hx).1
  · exact hDE (fun y hy => (hDX hy).2) hDXp ⟨cX, hcX, hcX2⟩ (fun x hx => (hEY hx).2) hEYc hEY2
      hEYcard fun x hx y hy => (mem_centralizer_iff.1 (hXY (hEY hx).1) y (hDX hy).1).symm
  ·
    have hDXA := hperf DX hDXp fun y hy => (hDX hy).2
    have hDYA := hperf DY hDYp fun y hy => (hDY hy).2
    have hcX2' : cX * cX = 1 := by rw [← sq, ← hcX2, pow_orderOf_eq_one]
    have hcX1 : cX ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hcX2
      exact absurd hcX2 (by norm_num)
    have hle : DY ≤ A ⊓ centralizer ({cX} : Set G) := fun y hy => ⟨hDYA hy,
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hXY (hDY hy).1) cX (hDX hcX).1).symm⟩
    have hbot := eq_bot_of_le_centralizer hKc e (hDXA hcX) hcX2' hcX1 hle hDYp
    rw [hbot, mem_bot] at hcY
    rw [hcY, orderOf_one] at hcY2
    exact absurd hcY2 (by norm_num)

theorem Hyp.false_of_nonswap (h : Hyp G A f) (d : Datum A) (hKc : Nat.card K = 2 ^ f)
    {X Y : Subgroup G}
    (πX : X →* projectiveSL 3 K) (hπX : Function.Surjective πX) (hkX : πX.ker ≤ center X)
    (hoX : Odd (Nat.card πX.ker))
    (πY : Y →* projectiveSL 3 K) (hπY : Function.Surjective πY) (hkY : πY.ker ≤ center Y)
    (hoY : Odd (Nat.card πY.ker))
    (htX : d.t ∈ normalizer (X : Set G)) (htY : d.t ∈ normalizer (Y : Set G))
    (hXY : Y ≤ centralizer (X : Set G)) (hXYinv : ∀ z ∈ X ⊓ Y, z * z = 1 → z = 1) : False := by
  have hf3 := h.three_le
  refine h.false_of_fixesLarge d hXY hXYinv ?_ ?_
  · have := exists_fixed_of_mem_normalizer hf3 hKc πX hπX hkX hoX htX d.t_mul_self
    rwa [hKc] at this
  · have := exists_fixed_of_mem_normalizer hf3 hKc πY hπY hkY hoY htY d.t_mul_self
    rwa [hKc] at this

end Contradiction

end CFSG.LocalAnalysis.EvenBN.LinearThree
