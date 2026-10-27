module

public import CFSG.GH74.GLS.SP.Local.SPLCtT2
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.SP.Local.SPLCtT

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CtQuot

section Aux

variable {G : Type} [Group G]

theorem sup_zpowers_decomp {I : Subgroup G} {x : G} (hx : ∀ i ∈ I, x * i * x⁻¹ ∈ I)
    (hx' : ∀ i ∈ I, x⁻¹ * i * x ∈ I) {m : G} (hm : m ∈ I ⊔ zpowers x) :
    ∃ (k : ℤ) (i : G), i ∈ I ∧ m = x ^ k * i := by
  have hnorm : zpowers x ≤ Subgroup.normalizer (I : Set G) := by
    rw [zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hx h hh, fun hh => ?_⟩
    have := hx' _ hh
    simpa [mul_assoc] using this
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) I hnorm
  rw [sup_comm] at hm
  have hm' : m ∈ ((zpowers x : Subgroup G) : Set G) * (I : Set G) := by
    rw [← hcoe]
    exact hm
  obtain ⟨a, ha, i, hi, rfl⟩ := Set.mem_mul.mp hm'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
  exact ⟨k, i, hi, rfl⟩

variable [Finite G]

theorem mul_mem_of_index_two {B Y : Subgroup G} (hBY : B ≤ Y) (hcard : Nat.card ↥Y = 2 * Nat.card ↥B)
    {a b : G} (ha : a ∈ Y) (hb : b ∈ Y) (ha' : a ∉ B) (hb' : b ∉ B) : a * b ∈ B := by
  have hidx : (B.subgroupOf Y).index = 2 := by
    have h1 := Subgroup.card_mul_index (B.subgroupOf Y)
    have h2 : Nat.card ↥(B.subgroupOf Y) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : ↥Y)) (b := (⟨b, hb⟩ : ↥Y))
  have h3 : (⟨a, ha⟩ : ↥Y) * ⟨b, hb⟩ ∈ B.subgroupOf Y := by
    rw [key]
    exact iff_of_false ha' hb'
  exact h3

end Aux

section Rho

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G}

omit [Finite G] in
theorem normal_Ict_subgroupOf (hA : SPLCtA D) : (D.Ict.subgroupOf D.Ct).Normal :=
  ⟨fun k hk c => hA.I_normal c c.2 k hk⟩

theorem exists_sylow_Ct {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    ∃ T' : Sylow 2 ↥D.Ct, (T' : Subgroup ↥D.Ct) = T.subgroupOf D.Ct := by
  apply SylowL2.exists_sylow_eq
  · exact hT.T_p.of_equiv (Subgroup.subgroupOfEquivOfLe hT.T_le).symm
  · intro P hP hle
    have hinj : Function.Injective D.Ct.subtype := Subtype.val_injective
    have hP' : IsPGroup 2 ↥(P.map D.Ct.subtype) := hP.of_equiv (P.equivMapOfInjective _ hinj)
    have hTP : T ≤ P.map D.Ct.subtype := by
      intro g hg
      have hgC : g ∈ D.Ct := hT.T_le hg
      refine ⟨⟨g, hgC⟩, hle (show (⟨g, hgC⟩ : ↥D.Ct) ∈ T.subgroupOf D.Ct from hg), rfl⟩
    have hPC : P.map D.Ct.subtype ≤ D.Ct := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have heq : P.map D.Ct.subtype = T := hT.T_max _ hPC hP' hTP
    refine le_antisymm (fun c hc => ?_) hle
    have : (c : G) ∈ P.map D.Ct.subtype := ⟨c, hc, rfl⟩
    rw [heq] at this
    exact this

omit [Finite G] in
@[expose] noncomputable def ctRho (hA : SPLCtA D) :
    ↥D.Ct →* MulAut ↥(D.Ict.subgroupOf D.Ct) :=
  haveI := normal_Ict_subgroupOf hA
  MulAut.conjNormal

omit [Finite G] in
theorem ctRho_apply (hA : SPLCtA D) (c : ↥D.Ct) (k : ↥(D.Ict.subgroupOf D.Ct)) :
    ((((ctRho hA c) k : ↥(D.Ict.subgroupOf D.Ct)) : ↥D.Ct) : G) =
      (c : G) * ((k : ↥D.Ct) : G) * (c : G)⁻¹ := rfl

omit [Finite G] in
theorem ctRho_eq_one_iff (hA : SPLCtA D) (hI : D.Ict ≤ D.Ct) {g : G} (hg : g ∈ D.Ct) :
    ctRho hA ⟨g, hg⟩ = 1 ↔ ∀ i ∈ D.Ict, g * i = i * g := by
  constructor
  · intro h i hi
    have h1 := congrArg (fun φ : MulAut ↥(D.Ict.subgroupOf D.Ct) =>
      (((φ ⟨⟨i, hI hi⟩, hi⟩ : ↥(D.Ict.subgroupOf D.Ct)) : ↥D.Ct) : G)) h
    simp only [ctRho_apply, MulAut.one_apply] at h1
    calc g * i = (g * i * g⁻¹) * g := by group
      _ = i * g := by rw [show g * i * g⁻¹ = i from h1]
  · intro h
    ext k
    rw [ctRho_apply, MulAut.one_apply]
    have hk : ((k : ↥D.Ct) : G) ∈ D.Ict := k.2
    have := h _ hk
    calc g * ((k : ↥D.Ct) : G) * g⁻¹ = ((k : ↥D.Ct) : G) * g * g⁻¹ := by rw [this]
      _ = ((k : ↥D.Ct) : G) := by group

omit [Finite G] in
theorem ctRho_mem_innAut (hA : SPLCtA D) (hI : D.Ict ≤ D.Ct) {i : G} (hi : i ∈ D.Ict) :
    ctRho hA ⟨i, hI hi⟩ ∈ IVK.innAut ↥(D.Ict.subgroupOf D.Ct) := by
  have := normal_Ict_subgroupOf hA
  have h : ctRho hA ⟨i, hI hi⟩ = MulAut.conj (⟨⟨i, hI hi⟩, hi⟩ : ↥(D.Ict.subgroupOf D.Ct)) :=
    MulAut.conjNormal_val (h := (⟨⟨i, hI hi⟩, hi⟩ : ↥(D.Ict.subgroupOf D.Ct)))
  rw [h]
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem exists_ctRho_of_mem_innAut (hA : SPLCtA D) {a : MulAut ↥(D.Ict.subgroupOf D.Ct)}
    (ha : a ∈ IVK.innAut ↥(D.Ict.subgroupOf D.Ct)) :
    ∃ (i : G) (_ : i ∈ D.Ict) (hiC : i ∈ D.Ct), ctRho hA ⟨i, hiC⟩ = a := by
  have := normal_Ict_subgroupOf hA
  obtain ⟨k, rfl⟩ := ha
  exact ⟨((k : ↥D.Ct) : G), k.2, (k : ↥D.Ct).2, MulAut.conjNormal_val (h := k)⟩

end Rho

section Heart

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G} {T T₀ T₁ : Subgroup G} {y : G}

omit [Finite G] in
theorem card_two_mul_of_dihedral {B Y : Subgroup G} (hB : IVK.IsDihedralOrder ↥B (2 ^ (D.n - 1)))
    (hY : IVK.IsDihedralOrder ↥Y (2 ^ D.n)) (hn : 3 ≤ D.n) :
    Nat.card ↥Y = 2 * Nat.card ↥B := by
  rw [CtW.card_of_isDihedralOrder hB, CtW.card_of_isDihedralOrder hY]
  obtain ⟨j, hj⟩ : ∃ j, D.n = j + 1 := ⟨D.n - 1, by omega⟩
  rw [hj, Nat.add_sub_cancel, pow_succ, mul_comm]

theorem ctRho_injOn (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hT : SPLCtT D T T₀ T₁ y) {g : G}
    (hg : g ∈ T₁ ⊔ zpowers y) (hgC : g ∈ D.Ct) (h1 : ctRho hA ⟨g, hgC⟩ = 1) : g = 1 := by
  have hI := Ict_le_Ct D hs
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hT₁T : T₁ ≤ T := by rw [hT.T₁_eq]; exact inf_le_left
  have hyT : y ∈ T := hT.y_mem
  have hYT : T₁ ⊔ zpowers y ≤ T := sup_le hT₁T (zpowers_le.mpr hyT)
  have hgT : g ∈ T := hYT hg
  have hg0 : g ∈ T₀ := (hT.T₀_mem g).mpr ⟨hgT, (ctRho_eq_one_iff hA hI hgC).mp h1⟩
  have hynot := SPLCtT.y_not_mem hs hT
  by_cases hgT₁ : g ∈ T₁
  · have : g ∈ T₀ ⊓ T₁ := ⟨hg0, hgT₁⟩
    rw [hT.T₀_inf_T₁, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hyY : y ∈ T₁ ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
    have hyT₁ : y ∉ T₁ := fun h => hynot (Subgroup.mem_sup_right h)
    have hcard := card_two_mul_of_dihedral hT.T₁_dih hT.T₁y_dih hn3
    have hgy : g * y ∈ T₁ :=
      mul_mem_of_index_two (le_sup_left : T₁ ≤ T₁ ⊔ zpowers y) hcard hg hyY hgT₁ hyT₁
    apply hynot
    have : y = g⁻¹ * (g * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (T₀.inv_mem hg0) hgy

theorem ctRho_y_facts (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hT : SPLCtT D T T₀ T₁ y)
    {F : Type} [Field F] [Finite F] (hL : IVK.L2Field F)
    (e' : ↥(D.Ict.subgroupOf D.Ct) ≃* IVK.L2 F) (N : IVK.L2Notation e')
    (hF1 : ∀ (g : G) (hg : g ∈ D.Ct), g ∈ T →
      ctRho hA ⟨g, hg⟩ ∈ (N.T : Subgroup (MulAut ↥(D.Ict.subgroupOf D.Ct))))
    (hF2b : ∀ p ∈ N.P, ∃ (g : G) (hg : g ∈ D.Ct), g ∈ T₁ ∧ ctRho hA ⟨g, hg⟩ = p) :
    ctRho hA ⟨y, hT.T_le hT.y_mem⟩ ∈ IVK.innDiagSub e' ∧
      ctRho hA ⟨y, hT.T_le hT.y_mem⟩ ∉ IVK.innAut ↥(D.Ict.subgroupOf D.Ct) := by
  have hI := Ict_le_Ct D hs
  have hyT : y ∈ T := hT.y_mem
  have hyC : y ∈ D.Ct := hT.T_le hyT
  have hT₁T : T₁ ≤ T := by rw [hT.T₁_eq]; exact inf_le_left
  have hyYT : T₁ ⊔ zpowers y ≤ T := sup_le hT₁T (zpowers_le.mpr hyT)
  have hynot := SPLCtT.y_not_mem hs hT
  have hnot : ctRho hA ⟨y, hyC⟩ ∉ IVK.innAut ↥(D.Ict.subgroupOf D.Ct) := by
    intro hin
    have hP : ctRho hA ⟨y, hyC⟩ ∈ N.P := ⟨hF1 y hyC hyT, hin⟩
    obtain ⟨g, hgC, hgT₁, hg⟩ := hF2b _ hP
    have hyg : ctRho hA ⟨y * g⁻¹, D.Ct.mul_mem hyC (D.Ct.inv_mem hgC)⟩ = 1 := by
      have : (⟨y * g⁻¹, D.Ct.mul_mem hyC (D.Ct.inv_mem hgC)⟩ : ↥D.Ct) = ⟨y, hyC⟩ * ⟨g, hgC⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, hg, mul_inv_cancel]
    have hcen := (ctRho_eq_one_iff hA hI _).mp hyg
    have hmemT : y * g⁻¹ ∈ T₀ :=
      (hT.T₀_mem _).mpr ⟨T.mul_mem hyT (T.inv_mem (hT₁T hgT₁)), hcen⟩
    apply hynot
    have : y = (y * g⁻¹) * g := by group
    rw [this]
    exact Subgroup.mul_mem_sup hmemT hgT₁
  refine ⟨?_, hnot⟩
  have hYC : T₁ ⊔ zpowers y ≤ D.Ct := hyYT.trans hT.T_le
  let φ : ↥(T₁ ⊔ zpowers y) →* MulAut ↥(D.Ict.subgroupOf D.Ct) :=
    (ctRho hA).comp (Subgroup.inclusion hYC)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (ctRho_injOn hs hA hT g.2 (hYC g.2) hg)
  have hφT : φ.range ≤ (N.T : Subgroup (MulAut ↥(D.Ict.subgroupOf D.Ct))) := by
    rintro _ ⟨g, rfl⟩
    exact hF1 g (hYC g.2) (hyYT g.2)
  have hPφ : N.P ≤ φ.range := by
    intro p hp
    obtain ⟨g, hgC, hgT₁, hg⟩ := hF2b p hp
    exact ⟨⟨g, Subgroup.mem_sup_left hgT₁⟩, hg⟩
  have hdih : ∃ n, IVK.IsDihedralTwoGroup ↥φ.range n := by
    obtain ⟨k, hk, hk2, ⟨d⟩⟩ := hT.T₁y_dih
    have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
    exact ⟨D.n, by omega, k, hk, hk2, ⟨(MonoidHom.ofInjective hφinj).symm.trans d⟩⟩
  have hyφ : ctRho hA ⟨y, hyC⟩ ∈ φ.range := ⟨⟨y, Subgroup.mem_sup_right (mem_zpowers y)⟩, rfl⟩
  have hPle : N.P ≤ IVK.innDiagSub e' := fun p hp => IVK.innAut_le_innDiagSub e' hp.2
  rcases IVK.ivk_1_2j F hL ↥(D.Ict.subgroupOf D.Ct) e' N φ.range hφT hPφ hdih with h | h
  · exfalso
    rw [h] at hyφ
    exact hnot hyφ.2
  · rw [h] at hyφ
    exact sup_le hPle (zpowers_le.mpr N.t_mem_diag) hyφ

theorem ctRho_x_eq_inv (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) (hT : SPLCtT D T T₀ T₁ y) {x : G}
    (hxY : x ∈ T₀ ⊔ zpowers y) (hxT₀ : x ∉ T₀) (hxC : x ∈ D.Ct) :
    ctRho hA ⟨x, hxC⟩ = (ctRho hA ⟨y, hT.T_le hT.y_mem⟩)⁻¹ := by
  have hI := Ict_le_Ct D hs
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hyT : y ∈ T := hT.y_mem
  have hyC : y ∈ D.Ct := hT.T_le hyT
  have hynot := SPLCtT.y_not_mem hs hT
  have hy0 : y ∉ T₀ := fun h => hynot (Subgroup.mem_sup_left h)
  have hyY : y ∈ T₀ ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
  have hcard := card_two_mul_of_dihedral hT.T₀_dih hT.T₀y_dih hn3
  have hxy : x * y ∈ T₀ :=
    mul_mem_of_index_two (le_sup_left : T₀ ≤ T₀ ⊔ zpowers y) hcard hxY hyY hxT₀ hy0
  have hT₀T : T₀ ≤ T := fun c hc => ((hT.T₀_mem c).mp hc).1
  have hxyC : x * y ∈ D.Ct := D.Ct.mul_mem hxC hyC
  have h1 : ctRho hA ⟨x * y, hxyC⟩ = 1 :=
    (ctRho_eq_one_iff hA hI hxyC).mpr (((hT.T₀_mem _).mp hxy).2)
  have h2 : (⟨x * y, hxyC⟩ : ↥D.Ct) = ⟨x, hxC⟩ * ⟨y, hyC⟩ := rfl
  rw [h2, map_mul] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem ctRho_ker_le (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {x : G} (hxC : x ∈ D.Ct)
    (hx2 : ctRho hA ⟨x, hxC⟩ ^ 2 = 1)
    (hxI : ctRho hA ⟨x, hxC⟩ ∉ IVK.innAut ↥(D.Ict.subgroupOf D.Ct))
    {m : G} (hm : m ∈ D.Ict ⊔ zpowers x) (hmC : m ∈ D.Ct) (h1 : ctRho hA ⟨m, hmC⟩ = 1) :
    m ∈ zpowers (x ^ 2) := by
  have hI := Ict_le_Ct D hs
  have hxn : ∀ i ∈ D.Ict, x * i * x⁻¹ ∈ D.Ict := fun i hi => hA.I_normal x hxC i hi
  have hxn' : ∀ i ∈ D.Ict, x⁻¹ * i * x ∈ D.Ict := by
    intro i hi
    simpa using hA.I_normal x⁻¹ (D.Ct.inv_mem hxC) i hi
  obtain ⟨k, i, hi, rfl⟩ := sup_zpowers_decomp (I := D.Ict) hxn hxn' hm
  have hiC : i ∈ D.Ct := hI hi
  have hdec : ctRho hA ⟨x ^ k * i, hmC⟩ = ctRho hA ⟨x, hxC⟩ ^ k * ctRho hA ⟨i, hiC⟩ := by
    have : (⟨x ^ k * i, hmC⟩ : ↥D.Ct) = ⟨x, hxC⟩ ^ k * ⟨i, hiC⟩ := rfl
    rw [this, map_mul, map_zpow]
  rw [hdec] at h1
  have hinn : ctRho hA ⟨x, hxC⟩ ^ k ∈ IVK.innAut ↥(D.Ict.subgroupOf D.Ct) := by
    have : ctRho hA ⟨x, hxC⟩ ^ k = (ctRho hA ⟨i, hiC⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem (ctRho_mem_innAut hA hI hi)
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · subst hj
    have h2 : ctRho hA ⟨x, hxC⟩ ^ (2 * j) = 1 := by
      rw [zpow_mul, zpow_two, ← pow_two, hx2, one_zpow]
    rw [h2, one_mul] at h1
    have hcen := (ctRho_eq_one_iff hA hI hiC).mp h1
    have hi1 : i = 1 := I_center_trivial D hs hi hcen
    subst hi1
    rw [mul_one]
    exact ⟨j, by rw [zpow_mul, zpow_two, pow_two]⟩
  · exfalso
    subst hj
    have h2 : ctRho hA ⟨x, hxC⟩ ^ (2 * j + 1) = ctRho hA ⟨x, hxC⟩ := by
      rw [zpow_add_one, zpow_mul, zpow_two, ← pow_two, hx2, one_zpow, one_mul]
    rw [h2] at hinn
    exact hxI hinn

theorem ctRho_mem_innDiag (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {F : Type} [Field F] [Finite F]
    (e' : ↥(D.Ict.subgroupOf D.Ct) ≃* IVK.L2 F) {x : G} (hxC : x ∈ D.Ct)
    (hxΔ : ctRho hA ⟨x, hxC⟩ ∈ IVK.innDiagSub e')
    {m : G} (hm : m ∈ D.Ict ⊔ zpowers x) (hmC : m ∈ D.Ct) :
    ctRho hA ⟨m, hmC⟩ ∈ IVK.innDiagSub e' := by
  have hI := Ict_le_Ct D hs
  have hxn : ∀ i ∈ D.Ict, x * i * x⁻¹ ∈ D.Ict := fun i hi => hA.I_normal x hxC i hi
  have hxn' : ∀ i ∈ D.Ict, x⁻¹ * i * x ∈ D.Ict := by
    intro i hi
    simpa using hA.I_normal x⁻¹ (D.Ct.inv_mem hxC) i hi
  obtain ⟨k, i, hi, rfl⟩ := sup_zpowers_decomp (I := D.Ict) hxn hxn' hm
  have hiC : i ∈ D.Ct := hI hi
  have hdec : ctRho hA ⟨x ^ k * i, hmC⟩ = ctRho hA ⟨x, hxC⟩ ^ k * ctRho hA ⟨i, hiC⟩ := by
    have : (⟨x ^ k * i, hmC⟩ : ↥D.Ct) = ⟨x, hxC⟩ ^ k * ⟨i, hiC⟩ := rfl
    rw [this, map_mul, map_zpow]
  rw [hdec]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hxΔ k)
    (IVK.innAut_le_innDiagSub e' (ctRho_mem_innAut hA hI hi))

end Heart

end CtQuot

section Main

open CtQuot

variable {G : Type} [Group G] [Finite G]

theorem ct_quot (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D)
    {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) {x : G}
    (hxY : x ∈ T₀ ⊔ zpowers y) (hxT₀ : x ∉ T₀) (hx2 : x ^ 2 ∈ T₀) :
    ∃ _ : ((zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x)).Normal,
      IVK.IsPGL2 (↥(D.Ict ⊔ zpowers x) ⧸ (zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x))
        (fun r => r = D.q) := by
  have hI := Ict_le_Ct D hs
  have hT₀T : T₀ ≤ T := fun c hc => ((hT.T₀_mem c).mp hc).1
  have hyT : y ∈ T := hT.y_mem
  have hxT : x ∈ T := (sup_le hT₀T (zpowers_le.mpr hyT)) hxY
  have hxC : x ∈ D.Ct := hT.T_le hxT
  have hyC : y ∈ D.Ct := hT.T_le hyT
  have hMC : D.Ict ⊔ zpowers x ≤ D.Ct := sup_le hI (zpowers_le.mpr hxC)
  obtain ⟨F, hF, hfin, hq, ⟨e₀⟩⟩ := Ict_isL2 D hs
  have hL : IVK.L2Field F := ⟨by rw [hq]; exact hs.odd_q, by have := hs.q_ge; rw [hq]; omega⟩
  have := normal_Ict_subgroupOf hA
  let eK : ↥(D.Ict.subgroupOf D.Ct) ≃* IVK.L2 F := (Subgroup.subgroupOfEquivOfLe hI).trans e₀
  obtain ⟨T', hT'⟩ := exists_sylow_Ct hT
  obtain ⟨e', N, hN1, hN2⟩ :=
    IVK.ivk_1_2_general F hL ↥D.Ct (D.Ict.subgroupOf D.Ct) ⟨eK⟩ T'
  have hF1 : ∀ (g : G) (hg : g ∈ D.Ct), g ∈ T →
      ctRho hA ⟨g, hg⟩ ∈ (N.T : Subgroup (MulAut ↥(D.Ict.subgroupOf D.Ct))) := by
    intro g hg hgT
    apply hN1
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [hT']
    exact hgT
  have hF2b : ∀ p ∈ N.P, ∃ (g : G) (hg : g ∈ D.Ct), g ∈ T₁ ∧ ctRho hA ⟨g, hg⟩ = p := by
    intro p hp
    rw [← hN2] at hp
    obtain ⟨c, ⟨hcT', hcK⟩, rfl⟩ := hp
    rw [hT'] at hcT'
    refine ⟨c, c.2, ?_, rfl⟩
    rw [hT.T₁_eq]
    exact ⟨hcT', hcK⟩
  obtain ⟨hyΔ, hyI⟩ := ctRho_y_facts hs hA hT hL e' N hF1 hF2b
  have hρx := ctRho_x_eq_inv hs hA hT hxY hxT₀ hxC
  have hxΔ : ctRho hA ⟨x, hxC⟩ ∈ IVK.innDiagSub e' := by
    rw [hρx]
    exact inv_mem hyΔ
  have hxI : ctRho hA ⟨x, hxC⟩ ∉ IVK.innAut ↥(D.Ict.subgroupOf D.Ct) := by
    rw [hρx, inv_mem_iff]
    exact hyI
  have hx2' : ctRho hA ⟨x, hxC⟩ ^ 2 = 1 := by
    have hx2C : x ^ 2 ∈ D.Ct := D.Ct.pow_mem hxC 2
    have h1 : ctRho hA ⟨x ^ 2, hx2C⟩ = 1 :=
      (ctRho_eq_one_iff hA hI hx2C).mpr (((hT.T₀_mem _).mp hx2).2)
    have h2 : (⟨x ^ 2, hx2C⟩ : ↥D.Ct) = ⟨x, hxC⟩ ^ 2 := rfl
    rw [h2, map_pow] at h1
    exact h1
  let ψ : ↥(D.Ict ⊔ zpowers x) →* MulAut ↥(D.Ict.subgroupOf D.Ct) :=
    (ctRho hA).comp (Subgroup.inclusion hMC)
  have hker : ψ.ker = (zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x) := by
    ext m
    constructor
    · intro hm
      exact ctRho_ker_le hs hA hxC hx2' hxI m.2 (hMC m.2) hm
    · intro hm
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (show (m : G) ∈ zpowers (x ^ 2) from hm)
      have hmT₀ : (m : G) ∈ T₀ := by
        rw [← hj]
        exact Subgroup.zpow_mem _ hx2 j
      exact (ctRho_eq_one_iff hA hI (hMC m.2)).mpr (((hT.T₀_mem _).mp hmT₀).2)
  have hrange : ψ.range = IVK.innDiagSub e' := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact ctRho_mem_innDiag hs hA e' hxC hxΔ m.2 (hMC m.2)
    · rw [← IVK.innAut_sup_zpowers_eq e' hL hxΔ hxI]
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · obtain ⟨i, hi, hiC, rfl⟩ := exists_ctRho_of_mem_innAut hA ha
        exact ⟨⟨i, Subgroup.mem_sup_left hi⟩, rfl⟩
      · exact ⟨⟨x, Subgroup.mem_sup_right (mem_zpowers x)⟩, rfl⟩
  have hN : ((zpowers (x ^ 2)).subgroupOf (D.Ict ⊔ zpowers x)).Normal := hker ▸ ψ.normal_ker
  refine ⟨hN, F, hF, hfin, hq, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans
    ((MulEquiv.subgroupCongr hrange).trans (IVK.innDiagEquiv e'))

end Main

end CFSG.GH74.GLS.SP.Local
