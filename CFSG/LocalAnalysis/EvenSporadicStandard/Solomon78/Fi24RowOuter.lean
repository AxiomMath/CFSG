module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowEdgeY
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24
public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Sporadic.Fi24
open CFSG.Sporadic.FischerOddCore CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Small


theorem conj_conj_eq {c g a b : R} (h : g⁻¹ * c * g * a * (g⁻¹ * c * g)⁻¹ = b) :
    c * (g * a * g⁻¹) * c⁻¹ = g * b * g⁻¹ := by
  rw [← h]
  group

theorem conj_inj {g a b : R} (h : g * a * g⁻¹ = g * b * g⁻¹) : a = b :=
  calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
    _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [h]
    _ = b := by group

theorem conj_commute_iff {γ x y : R} :
    γ * x * γ⁻¹ * (γ * y * γ⁻¹) = γ * y * γ⁻¹ * (γ * x * γ⁻¹) ↔ x * y = y * x := by
  constructor
  · intro h
    apply conj_inj (g := γ)
    calc γ * (x * y) * γ⁻¹ = γ * x * γ⁻¹ * (γ * y * γ⁻¹) := by group
      _ = γ * y * γ⁻¹ * (γ * x * γ⁻¹) := h
      _ = γ * (y * x) * γ⁻¹ := by group
  · intro h
    calc γ * x * γ⁻¹ * (γ * y * γ⁻¹) = γ * (x * y) * γ⁻¹ := by group
      _ = γ * (y * x) * γ⁻¹ := by rw [h]
      _ = γ * y * γ⁻¹ * (γ * x * γ⁻¹) := by group

theorem mul3_cyc {a b c : R} (hab : a * b = b * a) (hac : a * c = c * a) :
    a * b * c = b * c * a := by
  calc a * b * c = b * a * c := by rw [hab]
    _ = b * (a * c) := by group
    _ = b * (c * a) := by rw [hac]
    _ = b * c * a := by group

theorem mul3_swap23 {a b c : R} (hbc : b * c = c * b) : a * b * c = a * c * b := by
  rw [mul_assoc, hbc, ← mul_assoc]

theorem exists_fixed_of_perm3 {x₁ x₂ x₃ z : R} (hz : z * z = 1) (n12 : x₁ ≠ x₂) (n13 : x₁ ≠ x₃)
    (n23 : x₂ ≠ x₃) (h1 : z * x₁ * z⁻¹ ∈ ({x₁, x₂, x₃} : Set R))
    (h2 : z * x₂ * z⁻¹ ∈ ({x₁, x₂, x₃} : Set R)) (h3 : z * x₃ * z⁻¹ ∈ ({x₁, x₂, x₃} : Set R)) :
    z * x₁ * z⁻¹ = x₁ ∨ z * x₂ * z⁻¹ = x₂ ∨ z * x₃ * z⁻¹ = x₃ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have inv : ∀ a b : R, z * a * z⁻¹ = b → z * b * z⁻¹ = a := fun a b h => by
    rw [← h, hzi]
    calc z * (z * a * z) * z = (z * z) * a * (z * z) := by group
      _ = a := by rw [hz, one_mul, mul_one]
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  rcases h1 with h1 | h1 | h1
  · exact c1 h1
  · have e2 := inv _ _ h1
    rcases h3 with h3 | h3 | h3
    · exact n23 (conj_inj (h3.trans e2.symm)).symm
    · exact n13 (conj_inj (h1.trans h3.symm))
    · exact c3 h3
  · have e2 := inv _ _ h1
    rcases h2 with h2 | h2 | h2
    · exact n23 (conj_inj (h2.trans e2.symm))
    · exact c2 h2
    · exact n12 (conj_inj (h1.trans h2.symm))

end Small


section Triples

@[expose] def IsTriple (r : R) : Prop :=
  ∃ x₁ x₂ x₃ : R, x₁ ∈ D24 ∧ x₂ ∈ D24 ∧ x₃ ∈ D24 ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
    x₁ * x₂ = x₂ * x₁ ∧ x₁ * x₃ = x₃ * x₁ ∧ x₂ * x₃ = x₃ * x₂ ∧ r = x₁ * x₂ * x₃ ∧
    ∀ c : R, c * r = r * c → ∀ x ∈ ({x₁, x₂, x₃} : Set R), c * x * c⁻¹ ∈ ({x₁, x₂, x₃} : Set R)

theorem IsTriple.conj {r : R} (h : IsTriple r) (g : R) : IsTriple (g * r * g⁻¹) := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, n12, n13, n23, c12, c13, c23, hr, hperm⟩ := h
  have hc : ∀ {a b : R}, a * b = b * a → g * a * g⁻¹ * (g * b * g⁻¹) =
      g * b * g⁻¹ * (g * a * g⁻¹) := fun {a b} hab => by
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  refine ⟨g * x₁ * g⁻¹, g * x₂ * g⁻¹, g * x₃ * g⁻¹, Pair.conj_mem pair_R h₁ g,
    Pair.conj_mem pair_R h₂ g, Pair.conj_mem pair_R h₃ g, fun h => n12 (conj_inj h),
    fun h => n13 (conj_inj h), fun h => n23 (conj_inj h), hc c12, hc c13, hc c23, ?_, ?_⟩
  · rw [hr]
    group
  · intro c hcr x hx
    have hc' : (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g) := by
      calc g⁻¹ * c * g * r = g⁻¹ * (c * (g * r * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r * g⁻¹) * c) * g := by rw [hcr]
        _ = r * (g⁻¹ * c * g) := by group
    have key : ∀ y ∈ ({x₁, x₂, x₃} : Set R),
        c * (g * y * g⁻¹) * c⁻¹ ∈ ({g * x₁ * g⁻¹, g * x₂ * g⁻¹, g * x₃ * g⁻¹} : Set R) := by
      intro y hy
      have h := hperm _ hc' y hy
      rcases h with h | h | h
      · exact Or.inl (conj_conj_eq h)
      · exact Or.inr (Or.inl (conj_conj_eq h))
      · exact Or.inr (Or.inr (conj_conj_eq h))
    rcases hx with rfl | rfl | rfl
    · exact key _ (Or.inl rfl)
    · exact key _ (Or.inr (Or.inl rfl))
    · exact key _ (Or.inr (Or.inr rfl))

theorem isTriple_of_facts {r : R} {k₁ k₂ k₃ : Fin 306936}
    (hne : k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃) (hr : r = cls k₁ * cls k₂ * cls k₃)
    (hfix : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k)
    (hcomm : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k)
    (hchar : ∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) → k ∈ ({k₁, k₂, k₃} : Set (Fin 306936))) :
    IsTriple r := by
  have m1 : k₁ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m2 : k₂ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m3 : k₃ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  refine ⟨cls k₁, cls k₂, cls k₃, cls_mem _, cls_mem _, cls_mem _, fun h => hne.1 (cls_injective h),
    fun h => hne.2.1 (cls_injective h), fun h => hne.2.2 (cls_injective h),
    hcomm k₁ m1 k₂ (hfix k₂ m2), hcomm k₁ m1 k₃ (hfix k₃ m3), hcomm k₂ m2 k₃ (hfix k₃ m3), hr,
    ?_⟩
  intro c hc x hx
  have key : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)),
      c * cls k * c⁻¹ ∈ ({cls k₁, cls k₂, cls k₃} : Set R) := by
    intro k hk
    have h := fo24_triple_perm hfix hcomm hchar hc hk
    rw [← cls_smul_R]
    rcases h with h | h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr (Or.inl rfl)
    · rw [h]; exact Or.inr (Or.inr rfl)
  rcases hx with rfl | rfl | rfl
  · exact key _ m1
  · exact key _ m2
  · exact key _ m3

theorem isTriple_U2T : IsTriple (fi24U2 * tR) := by
  obtain ⟨k₁, k₂, k₃, hne, hr, hfix, hcomm, hchar⟩ := fi24U2T_triple
  exact isTriple_of_facts hne hr hfix hcomm hchar

theorem isTriple_U3T : IsTriple (fi24U3 * tR) := by
  obtain ⟨k₁, k₂, k₃, hne, hr, hfix, hcomm, hchar⟩ := fi24U3T_triple
  exact isTriple_of_facts hne hr hfix hcomm hchar

theorem fi24_outer_cases {w : R} (hw : w * w = 1) (hwJ : w ∉ JR) : w ∈ D24 ∨ IsTriple w := by
  have hw1 : w ≠ 1 := fun h => hwJ (h ▸ JR.one_mem)
  obtain ⟨r, hr, hrw⟩ := fi24_involution_class hw hw1
  obtain ⟨c, hc⟩ := isConj_iff.1 hrw
  have hrJ : r ∉ JR := fun h => hwJ (by rw [← hc]; exact normal_JR.conj_mem r h c)
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (MR_le_JR (fi23ToR_mem _)) hrJ
  · exact absurd (MR_le_JR (fi23ToR_mem _)) hrJ
  · exact absurd (MR_le_JR (fi23ToR_mem _)) hrJ
  · exact Or.inl hrw
  · left
    have h : fi24D * tR ∈ D24 := fi24D_mul_tR_mem
    exact (show IsConj tR (fi24D * tR) from h).trans hrw
  · right
    rw [← hc]
    exact isTriple_U2T.conj c
  · right
    rw [← hc]
    exact isTriple_U3T.conj c

end Triples

section Houter

variable (hPF : PolarFacts)
  (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
  (hcent22 : ∀ (χ : Fi22.D) (σ : Equiv.Perm Fi22.D),
    (∀ g : Fi22.J, g * χ = χ * g →
      σ * Pair.conjPerm Fi22.pair_D g = Pair.conjPerm Fi22.pair_D g * σ) →
    σ = 1 ∨ σ = Pair.conjPerm Fi22.pair_D (χ : Fi22.J))
  {e : J} (he : EdgeSwap e)

include hPF hfix22 hcent22 he in
theorem ho_triple_core {a b c' w : R} (ha : a ∈ D24) (hb : b ∈ LocalClass D24 a)
    (hc : c' ∈ LocalClass D24 a ∩ LocalClass D24 b) (hwdef : w = a * b * c') {z : R}
    (hzJ : z ∈ JR) (hz1 : z ≠ 1) (hzc : z * c' = c' * z) (hzw : z * w = w * z)
    (hcent : ∀ y ∈ JR, y * w = w * y → y * z = z * y) : False := by
  subst hwdef
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair ha hb
  have hp : jR g * c' * (jR g)⁻¹ ∈ LocalClass D24 tR ∩ LocalClass D24 xb := by
    refine ⟨?_, ?_⟩
    · rw [← hg1]; exact (Pair.conj_mem_localClass_iff pair_R (jR g)).2 hc.1
    · rw [← hg2]; exact (Pair.conj_mem_localClass_iff pair_R (jR g)).2 hc.2
  have hw : tR * xb * (jR g * c' * (jR g)⁻¹) = jR g * (a * b * c') * (jR g)⁻¹ := by
    rw [← hg1, ← hg2]
    group
  refine fi24_ho_edge hPF hfix22 hcent22 he hp (z := jR g * z * (jR g)⁻¹)
    (normal_JR.conj_mem z hzJ (jR g)) (fun h => hz1 (conj_inj (g := jR g) (by rw [h]; group)))
    ((conj_commute_iff).2 hzc) (by rw [hw]; exact (conj_commute_iff).2 hzw) ?_
  intro y hy hyw
  rw [hw] at hyw
  have hy₀ : (jR g)⁻¹ * y * jR g ∈ JR := by
    have := normal_JR.conj_mem y hy (jR g)⁻¹
    simpa using this
  have hy₀w : (jR g)⁻¹ * y * jR g * (a * b * c') = (a * b * c') * ((jR g)⁻¹ * y * jR g) := by
    calc (jR g)⁻¹ * y * jR g * (a * b * c')
        = (jR g)⁻¹ * (y * (jR g * (a * b * c') * (jR g)⁻¹)) * jR g := by group
      _ = (jR g)⁻¹ * ((jR g * (a * b * c') * (jR g)⁻¹) * y) * jR g := by rw [hyw]
      _ = (a * b * c') * ((jR g)⁻¹ * y * jR g) := by group
  have h := hcent _ hy₀ hy₀w
  calc y * (jR g * z * (jR g)⁻¹) = jR g * ((jR g)⁻¹ * y * jR g * z) * (jR g)⁻¹ := by group
    _ = jR g * (z * ((jR g)⁻¹ * y * jR g)) * (jR g)⁻¹ := by rw [h]
    _ = jR g * z * (jR g)⁻¹ * y := by group

include hPF hfix22 hcent22 he in
theorem ho_triple {w : R} (hw : IsTriple w) {z : R} (hzJ : z ∈ JR) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzw : z * w = w * z) (hcent : ∀ y ∈ JR, y * w = w * y → y * z = z * y) :
    False := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, n12, n13, n23, c12, c13, c23, hr, hperm⟩ := hw
  have hp := hperm z hzw
  have hfix := exists_fixed_of_perm3 hz2 n12 n13 n23 (hp x₁ (by simp)) (hp x₂ (by simp))
    (hp x₃ (by simp))
  have comm : ∀ x : R, z * x * z⁻¹ = x → z * x = x * z := fun x h => by
    calc z * x = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h]
  have l12 : x₂ ∈ LocalClass D24 x₁ := ⟨h₂, n12.symm, c12.symm⟩
  have l13 : x₃ ∈ LocalClass D24 x₁ := ⟨h₃, n13.symm, c13.symm⟩
  have l23 : x₃ ∈ LocalClass D24 x₂ := ⟨h₃, n23.symm, c23.symm⟩
  have l32 : x₂ ∈ LocalClass D24 x₃ := ⟨h₂, n23, c23⟩
  have l21 : x₁ ∈ LocalClass D24 x₂ := ⟨h₁, n12, c12⟩
  have l31 : x₁ ∈ LocalClass D24 x₃ := ⟨h₁, n13, c13⟩
  rcases hfix with h | h | h
  · exact ho_triple_core hPF hfix22 hcent22 he h₂ l23 ⟨l21, l31⟩
      (hr.trans (mul3_cyc c12 c13)) hzJ hz1 (comm _ h) hzw hcent
  · exact ho_triple_core hPF hfix22 hcent22 he h₁ l13 ⟨l12, l32⟩
      (hr.trans (mul3_swap23 c23)) hzJ hz1 (comm _ h) hzw hcent
  · exact ho_triple_core hPF hfix22 hcent22 he h₁ l12 ⟨l13, l23⟩ hr hzJ hz1 (comm _ h) hzw hcent

include hPF hfix22 hcent22 he in
theorem fi24_houter {w : R} (hw : w * w = 1) (hwJ : w ∉ JR) {z : R} (hzJ : z ∈ JR)
    (hz2 : orderOf z = 2) (hzw : z * w = w * z) (hall : ∀ y ∈ JR, y * w = w * y → y * z = z * y) :
    False := by
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  rcases fi24_outer_cases hw hwJ with hD | hT
  · obtain ⟨c, hc⟩ := isConj_iff.1 hD
    have hz'J : c⁻¹ * z * c ∈ JR := by
      have := normal_JR.conj_mem z hzJ c⁻¹
      simpa using this
    have hz'T : c⁻¹ * z * c * tR = tR * (c⁻¹ * z * c) := by
      rw [← hc] at hzw
      calc c⁻¹ * z * c * tR = c⁻¹ * (z * (c * tR * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * tR * c⁻¹) * z) * c := by rw [hzw]
        _ = tR * (c⁻¹ * z * c) := by group
    obtain ⟨g, hg, hgz⟩ : ∃ g : J, g ∈ M ∧ jR g = c⁻¹ * z * c := by
      obtain ⟨g, hg⟩ : c⁻¹ * z * c ∈ jR.range := by rw [range_jR]; exact hz'J
      exact ⟨g, (commute_tR_iff g).1 (by rw [hg]; exact hz'T), hg⟩
    have hcen : (⟨c⁻¹ * z * c, ⟨g, hg, hgz⟩⟩ : MR) ∈ Subgroup.center MR := by
      rw [Subgroup.mem_center_iff]
      intro m
      have hmJ : (m : R) ∈ JR := MR_le_JR m.2
      have hmT := commute_tR_of_mem_MR m.2
      have hy : c * (m : R) * c⁻¹ ∈ JR := normal_JR.conj_mem _ hmJ c
      have hyw : c * (m : R) * c⁻¹ * w = w * (c * (m : R) * c⁻¹) := by
        rw [← hc]
        calc c * (m : R) * c⁻¹ * (c * tR * c⁻¹) = c * ((m : R) * tR) * c⁻¹ := by group
          _ = c * (tR * (m : R)) * c⁻¹ := by rw [hmT]
          _ = c * tR * c⁻¹ * (c * (m : R) * c⁻¹) := by group
      have h := hall _ hy hyw
      apply Subtype.ext
      show (m : R) * (c⁻¹ * z * c) = c⁻¹ * z * c * m
      calc (m : R) * (c⁻¹ * z * c) = c⁻¹ * ((c * (m : R) * c⁻¹) * z) * c := by group
        _ = c⁻¹ * (z * (c * (m : R) * c⁻¹)) * c := by rw [h]
        _ = c⁻¹ * z * c * m := by group
    rw [center_MR, Subgroup.mem_bot] at hcen
    have h1 : c⁻¹ * z * c = 1 := by
      have h0 := congrArg Subtype.val hcen
      rwa [OneMemClass.coe_one] at h0
    exact hz1 (calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  · exact ho_triple hPF hfix22 hcent22 he hT hzJ hz1 hzz hzw hall

end Houter

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
