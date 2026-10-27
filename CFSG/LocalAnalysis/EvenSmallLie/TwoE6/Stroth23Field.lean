module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {G : Type*} [Group G]

theorem mul_self_eq_one_of_normalizes {S : Subgroup G} {d r : G}
    (hr : ∀ y ∈ S, r * y * r⁻¹ ∈ S) (hd : r * d * r⁻¹ ≠ d)
    (hsq : ∀ y ∈ S, y * y = 1 ∨ y * y = d) {y : G} (hy : y ∈ S) : y * y = 1 := by
  rcases hsq y hy with h | h
  · exact h
  · have h2 := hsq _ (hr y hy)
    have e : r * y * r⁻¹ * (r * y * r⁻¹) = r * d * r⁻¹ := by rw [← h]; group
    rw [e] at h2
    rcases h2 with h2 | h2
    · have hd1 : d = 1 := by
        calc d = r⁻¹ * (r * d * r⁻¹) * r := by group
          _ = 1 := by rw [h2]; group
      rw [h, hd1]
    · exact absurd h2 hd

@[expose] noncomputable def conjOfNormalizes {C : Subgroup G} [Finite C] {g : G}
    (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C) : MulAut C :=
  MulEquiv.ofBijective
    ({ toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
       map_one' := by ext; simp
       map_mul' := fun x y => by ext; simp only [coe_mul]; group } : C →* C)
    (Finite.injective_iff_bijective.1 fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [MonoidHom.coe_mk, OneHom.coe_mk] at h'
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h')))

theorem coe_conjOfNormalizes {C : Subgroup G} [Finite C] {g : G}
    (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C) (x : C) :
    ((conjOfNormalizes hg x : C) : G) = g * x * g⁻¹ := rfl

theorem mem_normalizer_of_conj_mem {C : Subgroup G} [Finite C] {g : G}
    (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C) : g ∈ normalizer (C : Set G) := by
  refine mem_normalizer_iff.2 fun x => ⟨hg x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := (conjOfNormalizes hg).surjective ⟨_, hx⟩
  have h := congrArg Subtype.val hy
  rw [coe_conjOfNormalizes] at h
  have hxy : (y : G) = x := by simpa using h
  rw [← hxy]
  exact y.2

theorem exists_mul_normalizes {p : ℕ} [Fact p.Prime] {C : Subgroup G} [Finite C] {g : G}
    (hg : ∀ x ∈ C, g * x * g⁻¹ ∈ C) (P : Sylow p C) :
    ∃ c ∈ C, ∀ x ∈ (P : Subgroup C).map C.subtype,
      c * g * x * (c * g)⁻¹ ∈ (P : Subgroup C).map C.subtype := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C ((conjOfNormalizes hg) • P) P
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : conjOfNormalizes hg x ∈ ((conjOfNormalizes hg • P : Sylow p C) : Subgroup C) := by
    rw [Sylow.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  have h2 : c * conjOfNormalizes hg x * c⁻¹ ∈ ((c • (conjOfNormalizes hg • P) : Sylow p C) :
      Subgroup C) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact ⟨_, h1, rfl⟩
  rw [hc] at h2
  refine ⟨_, h2, ?_⟩
  simp only [coe_subtype, coe_mul, coe_inv, coe_conjOfNormalizes]
  group

theorem eq_top_of_index_le_two {A : Type*} [Group A] [Finite A] {I J : Subgroup A} (hIJ : I ≤ J)
    (hI : I.index ≤ 2) (hne : ¬ J ≤ I) : J = ⊤ := by
  have h := relIndex_mul_index hIJ
  have h1 : I.relIndex J ≠ 1 := fun h1 => hne (relIndex_eq_one.1 h1)
  have hI0 : I.index ≠ 0 := FiniteIndex.index_ne_zero
  have h0 : I.relIndex J ≠ 0 := fun h0 => hI0 (by rw [← h, h0, zero_mul])
  have h2 : 2 ≤ I.relIndex J := by omega
  have hJ0 : J.index ≠ 0 := FiniteIndex.index_ne_zero
  have hJ : J.index = 1 := by
    by_contra hJ1
    have h3 : 2 ≤ J.index := by omega
    have := Nat.mul_le_mul h2 h3
    omega
  exact index_eq_one.1 hJ

theorem mem_of_normalizerMonoidHom_mem_range {L : Subgroup G} (hC : centralizer (L : Set G) ≤ L)
    {x : normalizer (L : Set G)}
    (hx : L.normalizerMonoidHom x ∈ (MulAut.conj : L →* MulAut L).range) : (x : G) ∈ L := by
  obtain ⟨l, hl⟩ := hx
  have key : ∀ m ∈ L, (x : G) * m * (x : G)⁻¹ = l * m * (l : G)⁻¹ := fun m hm => by
    have h := congrArg Subtype.val (DFunLike.congr_fun hl ⟨m, hm⟩)
    exact h.symm
  have hc : (l : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro m hm
    calc m * ((l : G)⁻¹ * x) = (l : G)⁻¹ * (l * m * (l : G)⁻¹) * x := by group
      _ = (l : G)⁻¹ * x * m := by rw [← key m hm]; group
  simpa using L.mul_mem l.2 (hC hc)

end Generic

section Transfer

variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable abbrev conjE
    : Eam →* MulAut (commutator Eam) := MulAut.conjNormal

noncomputable abbrev conjG
    (ι : L ≃* commutator Eam) :
    normalizer (L : Set G) →* MulAut (commutator Eam) :=
  (MulAut.congr ι).toMonoidHom.comp L.normalizerMonoidHom

theorem conjG_apply
    (ι : L ≃* commutator Eam) (x : normalizer (L : Set G)) (l : L) :
    conjG ι x (ι l) = ι ⟨x * l * (x : G)⁻¹, (x.2 l).1 l.2⟩ := by
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem coe_conjE_apply
    (e : Eam) (a : commutator Eam) :
    ((conjE e a : commutator Eam) : Eam) = e * a * e⁻¹ := rfl

theorem conjG_of_mem
    (ι : L ≃* commutator Eam) (l : L) :
    conjG ι ⟨(l : G), le_normalizer l.2⟩ = MulAut.conj (ι l) := by
  ext b
  have h : (L.normalizerMonoidHom ⟨(l : G), le_normalizer l.2⟩) (ι.symm b) =
      l * ι.symm b * l⁻¹ := Subtype.ext rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, h, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

theorem conjG_symm_of_mem
    (ι : L ≃* commutator Eam) (a : commutator Eam) :
    conjG ι ⟨((ι.symm a : L) : G), le_normalizer (ι.symm a).2⟩ = MulAut.conj a := by
  ext b
  have h : (L.normalizerMonoidHom ⟨((ι.symm a : L) : G), le_normalizer (ι.symm a).2⟩)
      (ι.symm b) = ι.symm a * ι.symm b * (ι.symm a)⁻¹ := Subtype.ext rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, h, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

theorem centralizer_commutator_Eam_le :
    centralizer ((commutator Eam : Subgroup Eam) : Set Eam) ≤ commutator Eam := by
  rw [centralizer_commutator_Eam]
  exact zpowers_le.2 cE'_mem_commutator

theorem conjE_mem_range_iff
    (e : Eam) :
    conjE e ∈ (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range ↔
      e ∈ commutator Eam := by
  constructor
  · exact mem_of_conjNormal_mem_range centralizer_commutator_Eam_le
  · intro he
    exact ⟨⟨e, he⟩, MulAut.conjNormal_val.symm⟩

theorem range_conjE
    (hO : CoverOuterLeTwo) : conjE.range = ⊤ := by
  obtain ⟨b, hb, -⟩ := exists_mul_self_eq_one_not_mem_commutator
  have hO' : (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range.index ≤ 2 := hO
  have hle : (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range ≤ conjE.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, MulAut.conjNormal_val⟩
  exact eq_top_of_index_le_two hle hO' fun h => hb ((conjE_mem_range_iff b).1 (h ⟨b, rfl⟩))

theorem conjG_mem_range_iff
    (ι : L ≃* commutator Eam) (hC : centralizer (L : Set G) ≤ L)
    (x : normalizer (L : Set G)) :
    conjG ι x ∈ (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range ↔
      (x : G) ∈ L := by
  constructor
  · intro h
    have e : conjG ι x = MulAut.congr ι (L.normalizerMonoidHom x) := rfl
    rw [e, congr_mem_range_conj_iff] at h
    exact mem_of_normalizerMonoidHom_mem_range hC h
  · intro hx
    exact ⟨ι ⟨x, hx⟩, (conjG_of_mem ι ⟨x, hx⟩).symm⟩

theorem range_conjG
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) (hX : ∃ x ∈ normalizer (L : Set G), x ∉ L) :
    (conjG ι).range = ⊤ := by
  obtain ⟨x, hxN, hxL⟩ := hX
  have hO' : (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range.index ≤ 2 := hO
  have hle : (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range ≤
      (conjG ι).range := by
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨((ι.symm a : L) : G), le_normalizer (ι.symm a).2⟩, ?_⟩
    exact conjG_symm_of_mem ι a
  exact eq_top_of_index_le_two hle hO' fun h =>
    hxL ((conjG_mem_range_iff ι hC ⟨x, hxN⟩).1 (h ⟨⟨x, hxN⟩, rfl⟩))

@[expose] def SameAction
    (ι : L ≃* commutator Eam) (e : Eam) (y : G) : Prop :=
  ∃ hy : y ∈ normalizer (L : Set G), ∀ l : L,
    ((ι ⟨y * l * y⁻¹, (hy l).1 l.2⟩ : commutator Eam) : Eam) = e * (ι l : Eam) * e⁻¹

theorem sameAction_iff_conj
    (ι : L ≃* commutator Eam) (e : Eam) {y : G}
    (hy : y ∈ normalizer (L : Set G)) : SameAction ι e y ↔ conjE e = conjG ι ⟨y, hy⟩ := by
  constructor
  · rintro ⟨hy', h⟩
    refine MulEquiv.ext fun a => Subtype.ext ?_
    obtain ⟨l, rfl⟩ := ι.surjective a
    calc ((conjE e (ι l) : commutator Eam) : Eam) = e * ι l * e⁻¹ := rfl
      _ = ((ι ⟨y * l * y⁻¹, (hy l).1 l.2⟩ : commutator Eam) : Eam) := (h l).symm
      _ = ((conjG ι ⟨y, hy⟩ (ι l) : commutator Eam) : Eam) :=
        congrArg Subtype.val (conjG_apply ι ⟨y, hy⟩ l).symm
  · intro h
    refine ⟨hy, fun l => ?_⟩
    have h1 := congrArg (fun f : MulAut (commutator Eam) => ((f (ι l) : commutator Eam) : Eam)) h
    simp only [coe_conjE_apply] at h1
    rw [h1, conjG_apply]

theorem exists_sameAction_of_mem_normalizer
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    {y : G} (hy : y ∈ normalizer (L : Set G)) : ∃ e : Eam, SameAction ι e y := by
  obtain ⟨e, he⟩ := (range_conjE hO).symm ▸ mem_top (conjG ι ⟨y, hy⟩)
  exact ⟨e, (sameAction_iff_conj ι e hy).2 he⟩

theorem exists_sameAction_of_eam
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) (hX : ∃ x ∈ normalizer (L : Set G), x ∉ L) (e : Eam) :
    ∃ y : G, SameAction ι e y := by
  obtain ⟨y, hy⟩ := (range_conjG hO ι hC hX).symm ▸ mem_top (conjE e)
  exact ⟨y, (sameAction_iff_conj ι e y.2).2 hy.symm⟩

theorem mem_commutator_iff_of_sameAction
    (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) {e : Eam} {y : G} (h : SameAction ι e y) :
    e ∈ commutator Eam ↔ y ∈ L := by
  have hy := h.1
  rw [← conjE_mem_range_iff, (sameAction_iff_conj ι e hy).1 h, conjG_mem_range_iff ι hC]

theorem sameAction_mul
    (ι : L ≃* commutator Eam) {e e' : Eam} {y y' : G}
    (h : SameAction ι e y) (h' : SameAction ι e' y') : SameAction ι (e * e') (y * y') := by
  obtain ⟨hy, h1⟩ := h
  obtain ⟨hy', h2⟩ := h'
  refine ⟨mul_mem hy hy', fun l => ?_⟩
  have e1 := h2 l
  have e2 := h1 ⟨y' * l * y'⁻¹, (hy' l).1 l.2⟩
  have e3 : (⟨y * y' * l * (y * y')⁻¹, ((mul_mem hy hy') l).1 l.2⟩ : L) =
      ⟨y * ((⟨y' * l * y'⁻¹, (hy' l).1 l.2⟩ : L) : G) * y⁻¹, (hy _).1 ((hy' l).1 l.2)⟩ :=
    Subtype.ext (by
      show y * y' * l * (y * y')⁻¹ = y * (y' * l * y'⁻¹) * y⁻¹
      group)
  rw [e3, e2, e1]
  group

theorem sameAction_pow
    (ι : L ≃* commutator Eam) {e : Eam} {y : G} (h : SameAction ι e y)
    (n : ℕ) : SameAction ι (e ^ n) (y ^ n) := by
  induction n with
  | zero =>
    refine ⟨by rw [pow_zero]; exact one_mem _, fun l => ?_⟩
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact sameAction_mul ι ih h

theorem mem_centralizer_of_sameAction_one
    (ι : L ≃* commutator Eam) {y : G}
    (h : SameAction ι 1 y) : y ∈ centralizer (L : Set G) := by
  obtain ⟨hy, h1⟩ := h
  rw [mem_centralizer_iff]
  intro m hm
  have h2 := h1 ⟨m, hm⟩
  simp only [one_mul, inv_one, mul_one] at h2
  have h3 : (⟨y * m * y⁻¹, (hy m).1 hm⟩ : L) = ⟨m, hm⟩ :=
    ι.injective (Subtype.ext h2)
  have h4 : y * m * y⁻¹ = m := congrArg Subtype.val h3
  calc m * y = y * m * y⁻¹ * y := by rw [h4]
    _ = y * m := by group

theorem mem_zpowers_of_sameAction_one
    (ι : L ≃* commutator Eam) {e : Eam}
    (h : SameAction ι e 1) : e ∈ zpowers cE' := by
  rw [← centralizer_commutator_Eam, mem_centralizer_iff]
  obtain ⟨hy1, h1⟩ := h
  intro a ha
  have h2 := h1 (ι.symm ⟨a, ha⟩)
  have e4 : (⟨1 * ((ι.symm ⟨a, ha⟩ : L) : G) * 1⁻¹, (hy1 _).1 (ι.symm ⟨a, ha⟩).2⟩ : L) =
      ι.symm ⟨a, ha⟩ := Subtype.ext (by simp)
  rw [e4, MulEquiv.apply_symm_apply] at h2
  calc a * e = e * a * e⁻¹ * e := by rw [← h2]
    _ = e * a := by group

theorem mul_self_mem_of_mem_normalizer
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) {y : G} (hy : y ∈ normalizer (L : Set G)) : y * y ∈ L := by
  obtain ⟨e, he⟩ := exists_sameAction_of_mem_normalizer hO ι hy
  exact (mem_commutator_iff_of_sameAction ι hC (sameAction_mul ι he he)).1
    (mul_self_mem_of_index_two short_F4_derived_standard_perfect_cover.1 e)

theorem mem_of_pow_eq_one_of_mem_normalizer
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) {y : G} (hy : y ∈ normalizer (L : Set G)) {n : ℕ}
    (hn : Odd n) (hyn : y ^ n = 1) : y ∈ L := by
  obtain ⟨j, rfl⟩ := hn
  have e : y = (y * y) ^ (j + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hyn,
      one_mul]
  rw [e]
  exact L.pow_mem (mul_self_mem_of_mem_normalizer hO ι hC hy) _

end Transfer

@[expose] def RootElevenTest
    (x₀ : Eam) : Prop :=
  (∃ ν ∈ commutator Eam, ν ∈ centralizer ({x₀} : Set Eam) ∧ orderOf ν = 11) ∧
    ∀ Q : Subgroup Eam, Q ≤ centralizer ({x₀} : Set Eam) → IsPGroup 11 Q → Q ≠ ⊥ →
      (∃ e ∈ centralizer ({x₀} : Set Eam), e ∉ commutator Eam ∧ ∀ q ∈ Q, e * q * e⁻¹ ∈ Q) ∧
      ∀ y ∈ centralizer ({x₀} : Set Eam), (∀ q ∈ Q, y * q * y⁻¹ ∈ Q) →
        (∃ k : ℕ, y ^ 2 ^ k = 1) → y * y = 1

section Frattini

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem conj_comm_of_comm {a b g : G} (h : a * b = b * a) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) := by
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem exists_two_pow_not_mem {L : Subgroup G} {x : G} (hxL : x ∉ L) (hsq : x * x ∈ L) :
    ∃ m a : ℕ, x ^ m ∉ L ∧ (x ^ m) ^ 2 ^ a = 1 := by
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨m, a, fun h => hxL ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := hm
    have e : x = x ^ (2 * j + 1) * ((x * x) ^ j)⁻¹ := by
      rw [← pow_two, ← pow_mul, pow_succ]
      group
    rw [e]
    exact L.mul_mem h (L.inv_mem (L.pow_mem hsq j))
  · rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]

theorem exists_involution_of_frattini {C : Subgroup G} {D Z g : G}
    (hCD : ∀ c ∈ C, c * D = D * c) (hCZ : ∀ c ∈ C, c * Z = Z * c) (hZ1 : Z ≠ 1)
    (hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C) (hg1 : g * D * g⁻¹ = D * Z)
    (P₀ : Sylow 11 C) {L : Subgroup G} (hsqL : ∀ c ∈ C, c * c ∈ L)
    (hT2 : ∀ y ∈ C, y ∈ normalizer (((P₀ : Subgroup C).map C.subtype : Subgroup G) : Set G) →
      (∃ k : ℕ, y ^ 2 ^ k = 1) → y * y = 1 ∨ y * y = D)
    (hT1 : ∃ x ∈ C, x ∈ normalizer (((P₀ : Subgroup C).map C.subtype : Subgroup G) : Set G) ∧
      x ∉ L) :
    ∃ s ∈ C, s ∉ L ∧ s * s = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = (P₀ : Subgroup C).map C.subtype := ⟨_, rfl⟩
  rw [← hPdef] at hT1 hT2
  obtain ⟨c₁, hc₁C, hn⟩ := exists_mul_normalizes hgC P₀
  rw [← hPdef] at hn
  obtain ⟨n, hndef⟩ : ∃ n : G, n = c₁ * g := ⟨_, rfl⟩
  rw [← hndef] at hn
  have hc₁d : c₁ * D * c₁⁻¹ = D := by rw [hCD c₁ hc₁C]; group
  have hc₁z : c₁ * Z * c₁⁻¹ = Z := by rw [hCZ c₁ hc₁C]; group
  have hnd : n * D * n⁻¹ = D * Z := by
    calc n * D * n⁻¹ = c₁ * (g * D * g⁻¹) * c₁⁻¹ := by rw [hndef]; group
      _ = c₁ * (D * Z) * c₁⁻¹ := by rw [hg1]
      _ = (c₁ * D * c₁⁻¹) * (c₁ * Z * c₁⁻¹) := by group
      _ = D * Z := by rw [hc₁d, hc₁z]
  have hnC : ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro c hc
    have e : n * c * n⁻¹ = c₁ * (g * c * g⁻¹) * c₁⁻¹ := by rw [hndef]; group
    rw [e]
    exact C.mul_mem (C.mul_mem hc₁C (hgC c hc)) (C.inv_mem hc₁C)
  have hnP : n ∈ normalizer (P : Set G) := by
    have : Finite P := by rw [hPdef]; infer_instance
    exact mem_normalizer_of_conj_mem hn
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = C ⊓ normalizer (P : Set G) := ⟨_, rfl⟩
  have hnM : ∀ m ∈ M, n * m * n⁻¹ ∈ M := fun m hm => by
    rw [hMdef] at hm ⊢
    exact ⟨hnC m hm.1, (normalizer (P : Set G)).mul_mem
      ((normalizer (P : Set G)).mul_mem hnP hm.2) ((normalizer (P : Set G)).inv_mem hnP)⟩
  obtain ⟨x₁, hx₁C, hx₁P, hx₁L⟩ := hT1
  obtain ⟨m, a, hy₁L, hy₁2⟩ := exists_two_pow_not_mem hx₁L (hsqL x₁ hx₁C)
  have hy₁M : x₁ ^ m ∈ M := by
    rw [hMdef]
    exact ⟨C.pow_mem hx₁C m, (normalizer (P : Set G)).pow_mem hx₁P m⟩
  have hcyc : IsPGroup 2 (zpowers (⟨x₁ ^ m, hy₁M⟩ : M)) := by
    have hdvd : orderOf (⟨x₁ ^ m, hy₁M⟩ : M) ∣ 2 ^ a :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hy₁2))
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  obtain ⟨S₀, hS₀⟩ := hcyc.exists_le_sylow
  obtain ⟨m₁, hm₁M, hr⟩ := exists_mul_normalizes hnM S₀
  have hm₁C : m₁ ∈ C := (hMdef ▸ hm₁M).1
  have hrd : m₁ * n * D * (m₁ * n)⁻¹ ≠ D := by
    have e : m₁ * n * D * (m₁ * n)⁻¹ = m₁ * (n * D * n⁻¹) * m₁⁻¹ := by group
    rw [e, hnd]
    intro h
    have h2 : m₁ * (D * Z) * m₁⁻¹ = (m₁ * D * m₁⁻¹) * (m₁ * Z * m₁⁻¹) := by group
    rw [h2, show m₁ * D * m₁⁻¹ = D by rw [hCD m₁ hm₁C]; group,
      show m₁ * Z * m₁⁻¹ = Z by rw [hCZ m₁ hm₁C]; group] at h
    exact hZ1 (by simpa using h)
  have hSM : (S₀ : Subgroup M).map M.subtype ≤ M := map_subtype_le _
  have hsq : ∀ y ∈ (S₀ : Subgroup M).map M.subtype, y * y = 1 ∨ y * y = D := by
    rintro _ ⟨y, hy, rfl⟩
    have hyM : (y : G) ∈ C ⊓ normalizer (P : Set G) := hMdef ▸ y.2
    obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨y, hy⟩
    have hk1 : y ^ 2 ^ k = 1 := by
      have h := congrArg (fun w : (S₀ : Subgroup M) => (w : M)) hk
      simpa using h
    have hk2 : (y : G) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk1
      simpa using h
    exact hT2 y hyM.1 hyM.2 ⟨k, hk2⟩
  have hy₁S : x₁ ^ m ∈ (S₀ : Subgroup M).map M.subtype :=
    ⟨⟨x₁ ^ m, hy₁M⟩, hS₀ (mem_zpowers _), rfl⟩
  exact ⟨x₁ ^ m, C.pow_mem hx₁C m, hy₁L, mul_self_eq_one_of_normalizes hr hrd hsq hy₁S⟩

omit [Finite G] in
theorem conj_mem_centralizer_inf {D Z g c : G} (hg1 : g * D * g⁻¹ = D * Z)
    (hg2 : g * Z * g⁻¹ = Z) (hc : c ∈ centralizer {D} ⊓ centralizer {Z}) :
    g * c * g⁻¹ ∈ centralizer {D} ⊓ centralizer {Z} := by
  have hdg : D = g * (D * Z⁻¹) * g⁻¹ := by
    calc D = (g * D * g⁻¹) * (g * Z * g⁻¹)⁻¹ := by rw [hg1, hg2]; group
      _ = g * (D * Z⁻¹) * g⁻¹ := by group
  have h1 : c * D = D * c := mem_centralizer_singleton_iff.1 hc.1
  have h2 : c * Z = Z * c := mem_centralizer_singleton_iff.1 hc.2
  have h2' : c * Z⁻¹ = Z⁻¹ * c := by
    calc c * Z⁻¹ = Z⁻¹ * (Z * c) * Z⁻¹ := by group
      _ = Z⁻¹ * (c * Z) * Z⁻¹ := by rw [h2]
      _ = Z⁻¹ * c := by group
  have h3 : c * (D * Z⁻¹) = (D * Z⁻¹) * c := by
    calc c * (D * Z⁻¹) = (c * D) * Z⁻¹ := by group
      _ = D * (c * Z⁻¹) := by rw [h1]; group
      _ = (D * Z⁻¹) * c := by rw [h2']; group
  refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
  · rw [hdg]
    exact conj_comm_of_comm h3
  · calc g * c * g⁻¹ * Z = g * c * g⁻¹ * (g * Z * g⁻¹) := by rw [hg2]
      _ = g * Z * g⁻¹ * (g * c * g⁻¹) := conj_comm_of_comm h2
      _ = Z * (g * c * g⁻¹) := by rw [hg2]

end Frattini

section Test

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] noncomputable def imageE
    (ι : L ≃* commutator Eam) (P : Subgroup G) : Subgroup Eam :=
  (P.subgroupOf L).map ((commutator Eam).subtype.comp ι.toMonoidHom)

theorem mem_imageE
    (ι : L ≃* commutator Eam) (P : Subgroup G) (q : Eam) :
    q ∈ imageE ι P ↔ ∃ p : L, (p : G) ∈ P ∧ (ι p : Eam) = q := by
  rw [imageE, mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, mem_subgroupOf.1 hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, mem_subgroupOf.2 hp, rfl⟩

theorem coe_map_mul
    (ι : L ≃* commutator Eam) (a b : L) :
    ((ι (a * b) : commutator Eam) : Eam) = (ι a : Eam) * (ι b : Eam) := by
  rw [map_mul]
  rfl

theorem coe_map_comm
    (ι : L ≃* commutator Eam) {a b : L} (h : (a : G) * b = b * a) :
    (ι a : Eam) * (ι b : Eam) = (ι b : Eam) * (ι a : Eam) := by
  have h' : a * b = b * a := Subtype.ext h
  calc (ι a : Eam) * (ι b : Eam) = ((ι (a * b) : commutator Eam) : Eam) :=
        (coe_map_mul ι a b).symm
    _ = ((ι (b * a) : commutator Eam) : Eam) := by rw [h']
    _ = (ι b : Eam) * (ι a : Eam) := coe_map_mul ι b a

theorem imageE_le_centralizer
    (ι : L ≃* commutator Eam) {z : L} {x₀ : commutator Eam}
    (hz : ι z = x₀) {P : Subgroup G} (hPz : ∀ p ∈ P, p * z = z * p) :
    imageE ι P ≤ centralizer ({(x₀ : Eam)} : Set Eam) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := (mem_imageE ι P q).1 hq
  rw [mem_centralizer_singleton_iff, ← hz]
  exact coe_map_comm ι (hPz p hp)

theorem isPGroup_imageE
    (ι : L ≃* commutator Eam) {P : Subgroup G} (hPL : P ≤ L) {p : ℕ}
    (hP : IsPGroup p P) : IsPGroup p (imageE ι P) :=
  (hP.of_equiv (subgroupOfEquivOfLe hPL).symm).map _

theorem imageE_ne_bot
    (ι : L ≃* commutator Eam) {P : Subgroup G} (hPL : P ≤ L) (hP0 : P ≠ ⊥) :
    imageE ι P ≠ ⊥ := by
  intro h
  apply hP0
  rw [eq_bot_iff]
  intro p hp
  have hq : (ι ⟨p, hPL hp⟩ : Eam) ∈ imageE ι P := (mem_imageE ι P _).2 ⟨_, hp, rfl⟩
  rw [h, mem_bot] at hq
  have h1 : ι ⟨p, hPL hp⟩ = 1 := Subtype.ext hq
  rw [map_eq_one_iff _ ι.injective] at h1
  exact congrArg Subtype.val h1

theorem mul_self_eq_of_rootElevenTest
    (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    {d z : L} {x₀ : commutator Eam} (hz : ι z = x₀) (hT : RootElevenTest (x₀ : Eam))
    (hCd : ∀ w ∈ centralizer (L : Set G), w = 1 ∨ w = (d : G))
    {P : Subgroup G} (hPL : P ≤ L) (hPz : ∀ p ∈ P, p * z = z * p) (hP11 : IsPGroup 11 P)
    (hP0 : P ≠ ⊥) {y : G} (hyN : y ∈ normalizer (L : Set G)) (hyz : y * z = z * y)
    (hyP : y ∈ normalizer (P : Set G)) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) :
    y * y = 1 ∨ y * y = d := by
  obtain ⟨e, he⟩ := exists_sameAction_of_mem_normalizer hO ι hyN
  have heC : e ∈ centralizer ({(x₀ : Eam)} : Set Eam) := by
    have h1 := he.2 z
    have e5 : (⟨y * z * y⁻¹, (he.1 z).1 z.2⟩ : L) = z := Subtype.ext (by
      show y * z * y⁻¹ = z
      rw [hyz]
      group)
    rw [e5, hz] at h1
    rw [mem_centralizer_singleton_iff]
    calc e * (x₀ : Eam) = e * x₀ * e⁻¹ * e := by group
      _ = x₀ * e := by rw [← h1]
  have heQ : ∀ q ∈ imageE ι P, e * q * e⁻¹ ∈ imageE ι P := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := (mem_imageE ι P q).1 hq
    exact (mem_imageE ι P _).2 ⟨_, (mem_normalizer_iff.1 hyP p).1 hp, he.2 p⟩
  have he2 : ∃ k : ℕ, e ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy2
    have h := sameAction_pow ι he (2 ^ k)
    rw [hk] at h
    refine ⟨k + 1, ?_⟩
    rcases CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers
      short_F4_central_extension_nonsplit.2.2.2.2.2.1 (mem_zpowers_of_sameAction_one ι h)
      with h1 | h1
    · rw [pow_succ, pow_mul, h1, one_pow]
    · rw [pow_succ, pow_mul, h1, ← orderOf_dvd_iff_pow_eq_one,
        short_F4_central_extension_nonsplit.2.2.2.2.2.1]
  have hee := (hT.2 (imageE ι P) (imageE_le_centralizer ι hz hPz) (isPGroup_imageE ι hPL hP11)
    (imageE_ne_bot ι hPL hP0)).2 e heC heQ he2
  have h := sameAction_mul ι he he
  rw [hee] at h
  exact hCd _ (mem_centralizer_of_sameAction_one ι h)

theorem exists_not_mem_of_rootElevenTest
    [Finite G] (hO : CoverOuterLeTwo) (ι : L ≃* commutator Eam)
    (hC : centralizer (L : Set G) ≤ L) (hX : ∃ x ∈ normalizer (L : Set G), x ∉ L)
    {z : L} {x₀ : commutator Eam} (hz : ι z = x₀) (hT : RootElevenTest (x₀ : Eam))
    {P : Subgroup G} (hPL : P ≤ L) (hPz : ∀ p ∈ P, p * z = z * p) (hP11 : IsPGroup 11 P)
    (hP0 : P ≠ ⊥) :
    ∃ x ∈ normalizer (L : Set G), x * z = z * x ∧ x ∈ normalizer (P : Set G) ∧ x ∉ L := by
  obtain ⟨e₁, he₁C, he₁E, he₁Q⟩ := (hT.2 (imageE ι P) (imageE_le_centralizer ι hz hPz)
    (isPGroup_imageE ι hPL hP11) (imageE_ne_bot ι hPL hP0)).1
  obtain ⟨x, hx⟩ := exists_sameAction_of_eam hO ι hC hX e₁
  refine ⟨x, hx.1, ?_, ?_, fun h => he₁E ((mem_commutator_iff_of_sameAction ι hC hx).2 h)⟩
  · have h1 := hx.2 z
    have hc := mem_centralizer_singleton_iff.1 he₁C
    rw [hz] at h1
    have h2 : e₁ * (x₀ : Eam) * e₁⁻¹ = x₀ := by rw [hc]; group
    rw [h2, ← hz] at h1
    have h3 : (⟨x * z * x⁻¹, (hx.1 z).1 z.2⟩ : L) = z := ι.injective (Subtype.ext h1)
    have h4 : x * z * x⁻¹ = z := congrArg Subtype.val h3
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h4]
  · refine mem_normalizer_of_conj_mem fun p hp => ?_
    have h1 := hx.2 ⟨p, hPL hp⟩
    obtain ⟨p', hp', hp'e⟩ := (mem_imageE ι P _).1
      (he₁Q _ ((mem_imageE ι P _).2 ⟨⟨p, hPL hp⟩, hp, rfl⟩))
    rw [← h1] at hp'e
    have h2 : p' = ⟨x * p * x⁻¹, (hx.1 _).1 (hPL hp)⟩ := ι.injective (Subtype.ext hp'e)
    rw [← show (p' : G) = x * p * x⁻¹ from congrArg Subtype.val h2]
    exact hp'

theorem comm_of_map_eq_cE'
    (ι : L ≃* commutator Eam) {d : L} (hd : (ι d : Eam) = cE') (l : L) :
    (d : G) * l = l * d := by
  have h := (Subgroup.mem_center_iff.1 short_F4_central_extension_nonsplit.2.2.2.2.1)
    (ι l : Eam)
  rw [← hd] at h
  have h' : ι (l * d) = ι (d * l) := Subtype.ext (by
    rw [coe_map_mul, coe_map_mul]
    exact h)
  exact (congrArg Subtype.val (ι.injective h')).symm

theorem exists_outer_involution_of_rootElevenTest
    [Finite G] (hO : CoverOuterLeTwo)
    (ι : L ≃* commutator Eam) (hC : centralizer (L : Set G) ≤ L)
    {d z : L} (hd : (ι d : Eam) = cE') {x₀ : commutator Eam} (hz : ι z = x₀) (hx₀ : x₀ ≠ 1)
    (hT : RootElevenTest (x₀ : Eam))
    (hCd : ∀ w ∈ centralizer (L : Set G), w = 1 ∨ w = (d : G))
    (hdN : centralizer {(d : G)} = normalizer (L : Set G))
    (hX : ∃ x ∈ normalizer (L : Set G), x ∉ L)
    {g : G} (hg1 : g * d * g⁻¹ = d * z) (hg2 : g * z * g⁻¹ = z) :
    ∃ s ∈ normalizer (L : Set G), s ∉ L ∧ s * s = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = centralizer {(d : G)} ⊓ centralizer {(z : G)} :=
    ⟨_, rfl⟩
  have hCN : C ≤ normalizer (L : Set G) := fun c hc => hdN ▸ (hCdef ▸ hc).1
  have hCD : ∀ c ∈ C, c * d = d * c := fun c hc =>
    mem_centralizer_singleton_iff.1 (hCdef ▸ hc).1
  have hCZ : ∀ c ∈ C, c * z = z * c := fun c hc =>
    mem_centralizer_singleton_iff.1 (hCdef ▸ hc).2
  have hgC : ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun c hc => by
    rw [hCdef] at hc ⊢
    exact conj_mem_centralizer_inf hg1 hg2 hc
  have hz1 : (z : G) ≠ 1 := by
    intro h
    apply hx₀
    rw [← hz, show z = 1 from Subtype.ext h, map_one]
  obtain ⟨P₀⟩ : Nonempty (Sylow 11 C) := inferInstance
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = (P₀ : Subgroup C).map C.subtype := ⟨_, rfl⟩
  have hPC : P ≤ C := hPdef ▸ map_subtype_le _
  have hP11 : IsPGroup 11 P := hPdef ▸ P₀.isPGroup'.map C.subtype
  have hPL : P ≤ L := by
    intro p hp
    obtain ⟨k, hk⟩ := hP11 ⟨p, hp⟩
    have hk' : p ^ 11 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact mem_of_pow_eq_one_of_mem_normalizer hO ι hC (hCN (hPC hp)) (Odd.pow (by decide)) hk'
  have hPz : ∀ p ∈ P, p * z = z * p := fun p hp => hCZ p (hPC hp)
  have hP0 : P ≠ ⊥ := by
    obtain ⟨ν, hνE, hνC, hν11⟩ := hT.1
    have hνCG : ((ι.symm ⟨ν, hνE⟩ : L) : G) ∈ C := by
      rw [hCdef]
      refine ⟨mem_centralizer_singleton_iff.2 (comm_of_map_eq_cE' ι hd _).symm,
        mem_centralizer_singleton_iff.2 ?_⟩
      have h := mem_centralizer_singleton_iff.1 hνC
      have e1 : ((ι (ι.symm ⟨ν, hνE⟩) : commutator Eam) : Eam) = ν :=
        congrArg Subtype.val (ι.apply_symm_apply ⟨ν, hνE⟩)
      have e2 : ((ι z : commutator Eam) : Eam) = x₀ := congrArg Subtype.val hz
      have h' : ι (ι.symm ⟨ν, hνE⟩ * z) = ι (z * ι.symm ⟨ν, hνE⟩) := Subtype.ext (by
        rw [coe_map_mul, coe_map_mul, e1, e2]
        exact h)
      exact congrArg Subtype.val (ι.injective h')
    have h11C : 11 ∣ Nat.card C := by
      have h := orderOf_dvd_natCard (⟨_, hνCG⟩ : C)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk,
        hν11] at h
    rw [hPdef]
    intro h
    exact P₀.ne_bot_of_dvd_card h11C ((map_eq_bot_iff_of_injective _ C.subtype_injective).1 h)
  obtain ⟨s, hsC, hsL, hs⟩ := exists_involution_of_frattini (L := L) hCD hCZ hz1 hgC hg1 P₀
    (fun c hc => mul_self_mem_of_mem_normalizer hO ι hC (hCN hc))
    (fun y hy hyP hy2 => mul_self_eq_of_rootElevenTest hO ι hz hT hCd hPL hPz hP11 hP0
      (hCN hy) (hCZ y hy) (hPdef ▸ hyP) hy2)
    (by
      obtain ⟨x, hxN, hxz, hxP, hxL⟩ := exists_not_mem_of_rootElevenTest hO ι hC hX hz hT hPL
        hPz hP11 hP0
      refine ⟨x, ?_, hPdef ▸ hxP, hxL⟩
      rw [hCdef]
      exact ⟨hdN ▸ hxN, mem_centralizer_singleton_iff.2 hxz⟩)
  exact ⟨s, hCN hsC, hsL, hs⟩

end Test

end CFSG.EvenSmallLie.TwoE6
