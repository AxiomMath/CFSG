module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74.GLS CFSG.GorensteinWalter CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace L4Pgl

section Join

variable {X : Type*} [Group X] {P : Subgroup X} {y : X}

theorem mem_sup_zpowers_of_sq_one (hy2 : y * y = 1) (hyN : y ∈ normalizer (P : Set X)) {b : X}
    (hb : b ∈ P ⊔ zpowers y) : b ∈ P ∨ b * y ∈ P := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconj : ∀ p ∈ P, y * p * y ∈ P := by
    intro p hp
    have := (Subgroup.mem_normalizer_iff.1 hyN p).1 hp
    simpa [hyi] using this
  rw [Subgroup.sup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact Or.inl hg
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · left
        have : y ^ (2 * m) = 1 := by
          rw [zpow_mul, zpow_two, hy2, one_zpow]
        rw [this]
        exact P.one_mem
      · right
        have : y ^ (2 * m + 1) * y = 1 := by
          rw [zpow_add_one, zpow_mul, zpow_two, hy2, one_zpow, one_mul, hy2]
        rw [this]
        exact P.one_mem
  | one => exact Or.inl P.one_mem
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (P.mul_mem ha hb)
    · exact Or.inr (by
        have : a * b * y = a * (b * y) := by group
        rw [this]
        exact P.mul_mem ha hb)
    · refine Or.inr ?_
      have : a * b * y = (a * y) * (y * b * y) := by
        calc a * b * y = a * (y * y) * b * y := by rw [hy2, mul_one]
          _ = (a * y) * (y * b * y) := by group
      rw [this]
      exact P.mul_mem ha (hconj b hb)
    · refine Or.inl ?_
      have : a * b = (a * y) * (y * (b * y) * y) := by
        calc a * b = a * (y * y) * b * (y * y) := by rw [hy2]; group
          _ = (a * y) * (y * (b * y) * y) := by group
      rw [this]
      exact P.mul_mem ha (hconj _ hb)
  | inv a _ ha =>
    rcases ha with ha | ha
    · exact Or.inl (P.inv_mem ha)
    · refine Or.inr ?_
      have h1 : y * (a * y)⁻¹ * y ∈ P := hconj _ (P.inv_mem ha)
      have : a⁻¹ * y = y * (a * y)⁻¹ * y := by
        calc a⁻¹ * y = y⁻¹ * y * a⁻¹ * y := by group
          _ = y * y * a⁻¹ * y := by rw [hyi]
          _ = y * (y⁻¹ * a⁻¹) * y := by rw [hyi]; group
          _ = y * (a * y)⁻¹ * y := by group
      rw [this]
      exact h1

theorem card_sup_zpowers [Finite X] (hy2 : y * y = 1) (hyN : y ∈ normalizer (P : Set X)) (hyP : y ∉ P) :
    Nat.card ↥(P ⊔ zpowers y) = 2 * Nat.card ↥P := by
  have hPA : P ≤ P ⊔ zpowers y := le_sup_left
  have hyA : y ∈ P ⊔ zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hidx : (P.subgroupOf (P ⊔ zpowers y)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyA⟩, fun b => ?_⟩
    have hb := mem_sup_zpowers_of_sq_one hy2 hyN b.2
    have hnot : ¬ ((b : X) ∈ P ∧ (b : X) * y ∈ P) := by
      rintro ⟨h1, h2⟩
      apply hyP
      have := P.mul_mem (P.inv_mem h1) h2
      simpa using this
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | hb
    · exact Or.inr ⟨hb, fun h => hnot ⟨hb, h⟩⟩
    · exact Or.inl ⟨hb, fun h => hnot ⟨h, hb⟩⟩
  have h1 := Subgroup.index_mul_card (P.subgroupOf (P ⊔ zpowers y))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv] at h1
  exact h1.symm

end Join

section SL2

theorem card_hasSL2Model {K : Type} [Group K] {q : ℕ} (h : HasSL2Model K (fun s => s = q)) :
    Nat.card K = q * (q ^ 2 - 1) := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFq]

theorem card_center_le_two {K : Type} [Group K] {P : ℕ → Prop} (h : HasSL2Model K P) :
    Nat.card (center K) ≤ 2 := by
  obtain ⟨F, hF, hFin, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr (Subgroup.centerCongr (e.trans (specialLinearGroupEquivStatedSL 2 F).symm)).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := F)).toEquiv]
  simpa using card_rootsOfUnity F 2

end SL2

end L4Pgl

theorem exists_dihedral_hom_of_pglOver {X : Type} [Group X] [Finite X] {L P : Subgroup X} {y : X}
    {q a : ℕ} (hodd : Odd q) (_hq : 3 < q) (hy2 : y * y = 1)
    (hL : HasSL2Model ↥L (fun s => s = q))
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) (hPcard : Nat.card ↥P = 2 ^ a)
    (hZP : (center ↥L).map L.subtype ≤ P) (hyN : y ∈ normalizer (P : Set X)) (hyL : y ∉ L)
    (h : PGLOver L (zpowers y) q) :
    ∃ (D : Type) (_ : Group D) (f : ↥(P ⊔ zpowers y) →* D),
      Function.Surjective f ∧ f.ker = ((center ↥L).map L.subtype).subgroupOf (P ⊔ zpowers y) ∧
      IVK.IsDihedralTwoGroup D a := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLcard : Nat.card ↥L = q * (q ^ 2 - 1) := L4Pgl.card_hasSL2Model hL
  have hZle : Nat.card ↥(center ↥L) ≤ 2 := L4Pgl.card_center_le_two hL
  obtain ⟨hZn, F, iF, fF, hFq, ⟨φ⟩⟩ := h
  set Z : Subgroup X := (center ↥L).map L.subtype with hZdef
  set N : Subgroup X := L ⊔ zpowers y with hNdef
  set A : Subgroup X := P ⊔ zpowers y with hAdef
  have hPL : P ≤ L := hP.le
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hLN : L ≤ N := le_sup_left
  have hyN' : y ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hAN : A ≤ N := sup_le (hPL.trans hLN) (Subgroup.zpowers_le.2 hyN')
  have hZA : Z ≤ A := hZP.trans le_sup_left
  have hZN : Z ≤ N := hZL.trans hLN
  have hyP : y ∉ P := fun hy => hyL (hPL hy)
  have hZcard : Nat.card ↥Z = Nat.card ↥(center ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hPGL : Nat.card (PGL2 F) = q * (q ^ 2 - 1) := by rw [pgl2_card_formula, hFq]
  have hNcard : Nat.card ↥N = Nat.card ↥Z * (q * (q ^ 2 - 1)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf N)
    rw [Nat.card_congr φ.toEquiv, hPGL,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv] at h1
    rw [h1]
    ring
  have hZ2 : Nat.card ↥Z = 2 := by
    have hlt : Nat.card ↥L < Nat.card ↥N := by
      by_contra hge
      push Not at hge
      have hLeq := Subgroup.eq_of_le_of_card_ge hLN hge
      exact hyL (hLeq ▸ hyN')
    rw [hNcard, ← hLcard] at hlt
    have h1 : 1 < Nat.card ↥Z := by
      by_contra hle
      push Not at hle
      have : Nat.card ↥Z * Nat.card ↥L ≤ 1 * Nat.card ↥L := Nat.mul_le_mul_right _ hle
      omega
    omega
  let ψ : ↥N →* PGL2 F := φ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf N))
  let f₀ : ↥A →* PGL2 F := ψ.comp (Subgroup.inclusion hAN)
  have hker : f₀.ker = Z.subgroupOf A := by
    ext a'
    constructor
    · intro ha
      have h1 : φ (QuotientGroup.mk' (Z.subgroupOf N) (Subgroup.inclusion hAN a')) = 1 := ha
      rw [MulEquiv.map_eq_one_iff] at h1
      have h2' := (QuotientGroup.eq_one_iff _).1 h1
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 h2')
    · intro ha
      show φ (QuotientGroup.mk' (Z.subgroupOf N) (Subgroup.inclusion hAN a')) = 1
      rw [MulEquiv.map_eq_one_iff]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha))
  have hkercard : Nat.card ↥f₀.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv]
    exact hZ2
  have hAcard : Nat.card ↥A = 2 * 2 ^ a := by
    rw [hAdef, L4Pgl.card_sup_zpowers hy2 hyN hyP, hPcard]
  have hHcard : Nat.card ↥f₀.range = 2 ^ a := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f₀).toEquiv, hkercard, hAcard] at h1
    omega
  have hHp : IsPGroup 2 ↥f₀.range := IsPGroup.of_card hHcard
  have hHidx : ¬ 2 ∣ f₀.range.index := by
    have h1 := Subgroup.index_mul_card f₀.range
    rw [hHcard, hPGL, ← hLcard] at h1
    have h3 := Subgroup.index_mul_card (P.subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hPcard] at h3
    have hpos : 0 < 2 ^ a := by positivity
    have heq : f₀.range.index = (P.subgroupOf L).index :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)
    rw [heq]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.2
  let S : Sylow 2 (PGL2 F) := hHp.toSylow hHidx
  have hS : (S : Subgroup (PGL2 F)) = f₀.range := rfl
  have hFodd : Odd (Nat.card F) := by rw [hFq]; exact hodd
  have hOPP : IsOddPrimePower (Nat.card F) := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hFodd
  obtain ⟨m, hm, ⟨eS⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hOPP S
  have hScard : Nat.card ↥(S : Subgroup (PGL2 F)) = 2 ^ a := by
    rw [hS]
    exact hHcard
  have hDcard : Nat.card (DihedralGroup (2 ^ m)) = 2 * 2 ^ m := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  have ham : a = m + 1 := by
    have h1 : 2 ^ a = 2 ^ (m + 1) := by
      rw [← hScard, Nat.card_congr eS.toEquiv, hDcard, pow_succ]
      ring
    exact Nat.pow_right_injective (le_refl 2) h1
  have hmem : ∀ x : ↥A, f₀ x ∈ (S : Subgroup (PGL2 F)) := fun x => ⟨x, rfl⟩
  refine ⟨↥(S : Subgroup (PGL2 F)), inferInstance, f₀.codRestrict (S : Subgroup (PGL2 F)) hmem,
    ?_, ?_, ?_⟩
  · intro s
    obtain ⟨x, hx⟩ := (show (s : PGL2 F) ∈ f₀.range from s.2)
    exact ⟨x, Subtype.ext hx⟩
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · refine ⟨by omega, 2 ^ m, ?_, ?_, ⟨eS⟩⟩
    · rw [ham, pow_succ]
      ring
    · exact Nat.le_self_pow (by omega) 2

end CFSG.GH74.GLS.Stage2.Local.P27
