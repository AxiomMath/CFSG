module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTypes
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbParabSelfNorm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

@[expose] def PCentral (p : ℕ) {Γ : Type*} [Group Γ] (D : Subgroup Γ) : Prop :=
  D.Normal ∧ ∀ α : Γ, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → ∀ γ : Γ, ⁅γ, α⁆ ∈ D

theorem exists_normal_index_three {Y Γ : Type*} [Group Y] [Finite Y] [Group Γ] [Finite Γ]
    (φ : Y →* Γ) {D : Subgroup Γ} (hD : PCentral 3 D) {a : Y}
    (ha3 : IsPGroup 3 (Subgroup.zpowers a)) (hφa : φ a ∉ D) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : D.Normal := hD.1
  set q : Y →* Γ ⧸ D := (QuotientGroup.mk' D).comp φ with hq
  have hqa : q a ≠ 1 := fun h => hφa ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hqak : (q a) ^ (3 ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hcent : ∀ y : Γ ⧸ D, (∃ k : ℕ, y ^ (3 ^ k) = 1) → y ∈ Subgroup.center (Γ ⧸ D) := by
    rintro y ⟨k, hk⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : ⁅γ, g⁆ ∈ D := hD.2 g ⟨k, by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hk⟩ γ
    have h2 : ⁅(QuotientGroup.mk' D γ), (QuotientGroup.mk' D g)⁆ = 1 := by
      rw [← map_commutatorElement]; exact (QuotientGroup.eq_one_iff _).2 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  obtain ⟨S⟩ : Nonempty (Sylow 3 (Γ ⧸ D)) := inferInstance
  have hSc : (S : Subgroup (Γ ⧸ D)) ≤ Subgroup.center (Γ ⧸ D) := by
    intro s hs
    apply hcent
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hS : Subgroup.normalizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) ≤
      Subgroup.centralizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_center_iff.1 (hSc hs) n).symm
  let T : Γ ⧸ D →* S := MonoidHom.transferSylow S hS
  let t : Y →* S := T.comp q
  have hdisj := MonoidHom.ker_transferSylow_disjoint S hS (Subgroup.zpowers (q a)) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ⟨k, Subtype.ext (by
      show (q a ^ m) ^ 3 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqak, one_zpow])⟩)
  have hta : t a ≠ 1 := by
    intro h
    have hmem : q a ∈ T.ker := by rw [MonoidHom.mem_ker]; exact h
    exact hqa (Subgroup.disjoint_def.1 hdisj hmem (Subgroup.mem_zpowers _))
  have htak : (t a) ^ (3 ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hB3 : IsPGroup 3 t.range := S.isPGroup'.of_injective t.range.subtype
    (Subgroup.subtype_injective _)
  haveI : Group.IsNilpotent t.range := hB3.isNilpotent
  have hd3 : 3 ∣ Nat.card t.range := by
    have h1 : orderOf (t a) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one htak
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hta (orderOf_eq_one_iff.1 (by simpa using hj))
    have h2 : orderOf (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range) = 3 ^ j := by
      rw [← hj, ← Subgroup.orderOf_coe]
    have h3 := orderOf_dvd_natCard (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range)
    rw [h2] at h3
    exact (dvd_pow_self 3 hj0).trans h3
  obtain ⟨M, hMi, hMn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hd3
  refine ⟨M.comap t.rangeRestrict, Subgroup.Normal.comap hMn _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ t.rangeRestrict_surjective, hMi]

open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)

theorem pCentral_of_outPNice {p : ℕ} {X : Type*} [Group X] (h : OutPNice p X) :
    ∃ D : Subgroup (MulAut X), PCentral p D ∧ Inn X ≤ D ∧
      ∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X := by
  obtain ⟨D, E, hID, hD2, hpE, hD3, -⟩ := h
  have hDE : D ≤ E := fun δ hδ => hpE δ ⟨0, by rw [pow_zero, pow_one]; exact hδ⟩
  refine ⟨D, ⟨⟨fun d hd α => ?_⟩, fun α hα γ => hD3 γ α (hpE α hα)⟩, hID, hD2⟩
  have : α * d * α⁻¹ = ⁅α, d⁆ * d := by rw [commutatorElement_def]; group
  rw [this]
  exact mul_mem (hD3 α d (hDE hd)) hd

section Conj

variable {Y : Type*} [Group Y] (L : Subgroup Y) [L.Normal]

@[expose] noncomputable def autQuotHom : MulAut ↥L →* MulAut (↥L ⧸ Subgroup.center ↥L) where
  toFun φ := QuotientGroup.congr _ _ φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def convAut : Y →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
  (autQuotHom L).comp MulAut.conjNormal

theorem convAut_apply_mk (y : Y) (l : ↥L) :
    convAut L y (l : ↥L ⧸ Subgroup.center ↥L) =
      ((⟨y * l * y⁻¹, Subgroup.Normal.conj_mem inferInstance _ l.2 y⟩ : ↥L) :
        ↥L ⧸ Subgroup.center ↥L) :=
  rfl

omit [L.Normal] in
theorem mulAut_eq_one_of_mul_inv_mem_center {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    (σ : MulAut Q) (h : ∀ s : Q, σ s * s⁻¹ ∈ Subgroup.center Q) : σ = 1 := by
  let F : Subgroup Q :=
    { carrier := {x | σ x = x}
      mul_mem' := fun {a b} ha hb => by
        change σ a = a at ha
        change σ b = b at hb
        change σ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one σ
      inv_mem' := fun {a} ha => by
        change σ a = a at ha
        change σ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hF : commutator Q ≤ F := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change σ ⁅a, b⁆ = ⁅a, b⁆
    have hσ : ∀ x : Q, σ x = x * (σ x * x⁻¹) := fun x => by
      have := Subgroup.mem_center_iff.1 (h x) x
      rw [this]; group
    rw [map_commutatorElement, hσ a, hσ b]
    exact commutatorElement_mul_central (h a) (h b)
  ext s
  have : s ∈ F := hF (hQ ▸ Subgroup.mem_top s)
  exact this

theorem convAut_eq_one_iff (hL : commutator ↥L = ⊤) (y : Y) :
    convAut L y = 1 ↔ y ∈ Subgroup.centralizer (L : Set Y) := by
  constructor
  · intro h
    have h1 : (MulAut.conjNormal y : MulAut ↥L) = 1 := by
      refine mulAut_eq_one_of_mul_inv_mem_center hL _ fun s => ?_
      have h2 := congrArg (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) =>
        φ (s : ↥L ⧸ Subgroup.center ↥L)) h
      simp only [convAut_apply_mk, MulAut.one_apply] at h2
      exact (QuotientGroup.eq_one_iff _).1 (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        exact mul_inv_eq_one.2 h2)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : Y)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  · intro hy
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [convAut_apply_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      simp only
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.1 hy l l.2).symm

theorem convAut_of_mem (l : ↥L) :
    convAut L (l : Y) = MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H m =>
    rw [convAut_apply_mk, MulAut.conj_apply]
    rfl

theorem exists_mem_centralizer_of_convAut_mem_inn (hL : commutator ↥L = ⊤) {a : Y}
    (h : convAut L a ∈ Inn (↥L ⧸ Subgroup.center ↥L)) :
    ∃ l : ↥L, a * (l : Y)⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨l, (convAut_eq_one_iff L hL _).1 ?_⟩
  rw [map_mul, map_inv, ← hx, convAut_of_mem]
  exact mul_inv_cancel (MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L))

end Conj

section Levi

variable {Y : Type} [Group Y]

@[expose] def LeviInnAt (P : Subgroup Y) : Prop :=
  ∀ l ∈ P, ∀ k : ℕ, (∀ w ∈ perfectJoin P, ⁅l ^ (3 ^ k), w⁆ = 1) →
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅l * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)

variable [Finite Y]

theorem actsInnerly_of_inn {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (hLevi : LeviInnAt P) {a : Y} (ha3 : IsPGroup 3 (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hin : convAut L a ∈ Inn (↥L ⧸ Subgroup.center ↥L)) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  have hPL : P ≤ L := hCP.parab.1
  obtain ⟨l₀, hc⟩ := exists_mem_centralizer_of_convAut_mem_inn L hCP.comp.2.2.1 hin
  set c : Y := a * (l₀ : Y)⁻¹ with hcdef
  have hcL : ∀ x ∈ L, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.1 hc x hx
  have hac : a = c * (l₀ : Y) := by rw [hcdef]; group
  have hconj : ∀ h : Y, h ∈ L → (l₀ : Y) * h * (l₀ : Y)⁻¹ = a * h * a⁻¹ := by
    intro h hh
    have hX : (l₀ : Y) * h * (l₀ : Y)⁻¹ ∈ L := L.mul_mem (L.mul_mem l₀.2 hh) (L.inv_mem l₀.2)
    have key : c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ = (l₀ : Y) * h * (l₀ : Y)⁻¹ := by
      rw [← hcL _ hX]; group
    rw [hac]
    calc (l₀ : Y) * h * (l₀ : Y)⁻¹ = c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ := key.symm
      _ = c * (l₀ : Y) * h * (c * (l₀ : Y))⁻¹ := by group
  have hl₀N : (l₀ : Y) ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj h (hPL hh)]
      exact (Subgroup.mem_normalizer_iff.1 haN h).1 hh
    · intro hh
      have hhL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem l₀.2) (hPL hh)) l₀.2
        simpa [mul_assoc] using this
      rw [hconj h hhL] at hh
      exact (Subgroup.mem_normalizer_iff.1 haN h).2 hh
  have hl₀P : (l₀ : Y) ∈ P :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo hCP.parab
      l₀.2 hl₀N
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute c (l₀ : Y) := (hcL _ l₀.2).symm
  have hpow : (l₀ : Y) ^ (3 ^ k) = (c ^ (3 ^ k))⁻¹ := by
    rw [hac, hcomm.mul_pow] at hak
    exact eq_inv_of_mul_eq_one_right hak
  have hVL : perfectJoin P ≤ L := (perfectJoin_le P).trans hPL
  obtain ⟨v, hv, hvw⟩ := hLevi _ hl₀P k fun w hw => by
    have h1 : Commute (c ^ (3 ^ k)) w := Commute.pow_left (hcL w (hVL hw)).symm _
    rw [commutatorElement_eq_one_iff_mul_comm, hpow]
    exact h1.inv_left.eq
  refine ⟨v, hv, fun w hw => ?_⟩
  have hvL : v ∈ L := hVL hv
  have hwL : w ∈ L := hVL hw
  have hX : (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.mul_mem l₀.2 hvL) hwL) (L.inv_mem hvL)) (L.inv_mem l₀.2)
  have hkey : c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹ =
      (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ := by
    rw [← hcL _ hX]; group
  have : ⁅a * v, w⁆ = ⁅(l₀ : Y) * v, w⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hac]
    calc c * (l₀ : Y) * v * w * (c * (l₀ : Y) * v)⁻¹ * w⁻¹
        = (c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹) * w⁻¹ := by group
      _ = ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * w⁻¹ := by rw [hkey]
      _ = (l₀ : Y) * v * w * ((l₀ : Y) * v)⁻¹ * w⁻¹ := by group
  rw [this]
  exact hvw w hw

theorem fieldIndex_core {L P : Subgroup Y} [L.Normal]
    {D : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))} (hD : PCentral 3 D) {a : Y}
    (ha3 : IsPGroup 3 (Subgroup.zpowers a))
    (hout : ¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P))
    (hLevi : convAut L a ∈ D →
      ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = 3 := by
  have : Finite (↥L ⧸ Subgroup.center ↥L) := inferInstance
  by_cases h : convAut L a ∈ D
  · exact absurd (hLevi h) hout
  · exact exists_normal_index_three (convAut L) hD ha3 h

theorem fieldIndex_of_outPNice {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (hO : OutPNice 3 (↥L ⧸ Subgroup.center ↥L)) (hLevi : LeviInnAt P) {a : Y}
    (ha3 : IsPGroup 3 (Subgroup.zpowers a)) (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hout : ¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = 3 := by
  obtain ⟨D, hD, hID, hD2⟩ := pCentral_of_outPNice hO
  refine fieldIndex_core hD ha3 hout fun hmem => ?_
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine actsInnerly_of_inn hCP hLevi ha3 haN (hD2 _ hmem k ?_)
  rw [← map_pow, hak, map_one]
  exact Subgroup.one_mem _

end Levi

section Families

@[expose] def FieldIndexAt {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    3 ∣ Nat.card (perfectJoin P) → Open.pRank 3 (perfectJoin P) ≤ 1 →
    ∀ a : Y, IsPGroup 3 (Subgroup.zpowers a) → a ∈ Subgroup.normalizer (P : Set Y) →
    (¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) →
    ∃ N : Subgroup Y, N.Normal ∧ N.index = 3

@[expose] def FieldIndexOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → FieldIndexAt L P

theorem kFactCompParabFieldIndex_of_families (hA : FieldIndexOn (IsLieOf IdxA))
    (h2A : FieldIndexOn (IsLieOf IdxTwistedA)) (hB : FieldIndexOn (IsLieOf IdxB))
    (hD : FieldIndexOn (IsLieOf IdxD)) (h2D : FieldIndexOn (IsLieOf IdxTwistedD))
    (hG : FieldIndexOn (IsLieOf IdxG2)) (hS : FieldIndexOn IsSmallTwoOrG2) :
    KFactCompParabFieldIndex := by
  intro Y _ _ L P hCP hLn hrank h3 hrk a ha3 haN hout
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    h2A Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hB Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hD Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    h2D Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hG Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hS Y L P hCP h hLn hrank h3 hrk a ha3 haN hout]

@[expose] def LeviInnOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    3 ∣ Nat.card (perfectJoin P) → Open.pRank 3 (perfectJoin P) ≤ 1 → LeviInnAt P

theorem fieldIndexOn_of_outPNice {C : (X : Type) → [Group X] → Prop}
    (hT : ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
      C (↥L ⧸ Subgroup.center ↥L) → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
      OutPNice 3 (↥L ⧸ Subgroup.center ↥L))
    (hL : LeviInnOn C) : FieldIndexOn C := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  exact fieldIndex_of_outPNice hCP (hT Y L P hCP hC hrank) (hL Y L P hCP hC hLn hrank h3 hrk)
    ha3 haN hout

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
