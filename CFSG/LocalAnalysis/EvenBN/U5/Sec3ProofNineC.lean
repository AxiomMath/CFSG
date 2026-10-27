module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

section Generic

variable {Q : Type*} [Group Q]

theorem sec39c_normal_in_prod {D₁ D₂ D K : Subgroup Q} (h1 : IsSimpleGroup D₁)
    (h2 : IsSimpleGroup D₂) (hD : D₁ ⊔ D₂ = D) (hc : ⁅D₁, D₂⁆ = ⊥)
    (hCD : centralizer (D : Set Q) = ⊥) (hKD : K ≤ D)
    (hKn : ∀ x ∈ D, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : K = ⊥ ∨ D₁ ≤ K ∨ D₂ ≤ K := by
  have hD₁ : D₁ ≤ D := hD ▸ le_sup_left
  have hD₂ : D₂ ≤ D := hD ▸ le_sup_right
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := fun x hx y hy => by
    have : ⁅x, y⁆ ∈ (⁅D₁, D₂⁆ : Subgroup Q) := Subgroup.commutator_mem_commutator hx hy
    rw [hc, Subgroup.mem_bot, commutatorElement_def] at this
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [this, one_mul]
  have hN₁ : D ≤ normalizer (D₁ : Set Q) := by
    rw [← hD]
    refine sup_le le_normalizer ?_
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have : y * x * y⁻¹ = x := by rw [← hcomm x hx y hy]; group
    rw [this]; exact hx
  have hN₂ : D ≤ normalizer (D₂ : Set Q) := by
    rw [← hD]
    refine sup_le ?_ le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have : y * x * y⁻¹ = x := by rw [hcomm y hy x hx]; group
    rw [this]; exact hx
  have key : ∀ X : Subgroup Q, IsSimpleGroup X → X ≤ D → D ≤ normalizer (X : Set Q) →
      K ⊓ X = ⊥ ∨ X ≤ K := by
    intro X hX hXD hNX
    haveI : ((K ⊓ X).subgroupOf X).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hKn _ (hXD g.2) _ hn.1, (g * n * g⁻¹).2⟩⟩
    rcases hX.eq_bot_or_eq_top_of_normal ((K ⊓ X).subgroupOf X) with e | e
    · left
      rw [Subgroup.subgroupOf_eq_bot] at e
      have := disjoint_iff.1 e
      rwa [inf_assoc, inf_idem] at this
    · right
      rw [Subgroup.subgroupOf_eq_top] at e
      exact fun x hx => (e hx).1
  have hcent : ∀ X : Subgroup Q, X ≤ D → D ≤ normalizer (X : Set Q) → K ⊓ X = ⊥ →
      ∀ k ∈ K, ∀ x ∈ X, x * k = k * x := by
    intro X hXD hNX hX k hk x hx
    have h₁ : x * k * x⁻¹ * k⁻¹ ∈ K := K.mul_mem (hKn x (hXD hx) k hk) (K.inv_mem hk)
    have h₂ : x * k * x⁻¹ * k⁻¹ ∈ X := by
      have : k * x⁻¹ * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hNX (hKD hk)) _).1 (inv_mem hx)
      have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
      rw [e]; exact mul_mem hx this
    have : x * k * x⁻¹ * k⁻¹ = 1 := by
      have := Subgroup.mem_inf.2 ⟨h₁, h₂⟩
      rwa [hX, Subgroup.mem_bot] at this
    calc x * k = x * k * x⁻¹ * k⁻¹ * (k * x) := by group
      _ = k * x := by rw [this, one_mul]
  rcases key D₁ h1 hD₁ hN₁ with e1 | e1
  · rcases key D₂ h2 hD₂ hN₂ with e2 | e2
    · left
      rw [eq_bot_iff]
      intro k hk
      have hk1 := hcent D₁ hD₁ hN₁ e1 k hk
      have hk2 := hcent D₂ hD₂ hN₂ e2 k hk
      have : D ≤ centralizer ({k} : Set Q) := by
        rw [← hD]
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hk1 x hx
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hk2 x hx
      have hkC : k ∈ centralizer (D : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have := Subgroup.mem_centralizer_singleton_iff.1 (this hx)
        exact this
      rw [hCD] at hkC
      exact hkC
    · exact Or.inr (Or.inr e2)
  · exact Or.inr (Or.inl e1)

def sec39cCentMod (E V : Subgroup Q) : Subgroup Q where
  carrier := {g | g ∈ normalizer (E : Set Q) ∧ ∀ e ∈ E, ⁅g, e⁆ ∈ V}
  one_mem' := ⟨one_mem _, fun e _ => by rw [commutatorElement_one_left]; exact one_mem _⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgc⟩ ⟨hg', hgc'⟩
    refine ⟨mul_mem hg hg', fun e he => ?_⟩
    have hx : g' * e * g'⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hg' e).1 he
    have : ⁅g * g', e⁆ = ⁅g, g' * e * g'⁻¹⁆ * ⁅g', e⁆ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact V.mul_mem (hgc _ hx) (hgc' e he)
  inv_mem' := by
    rintro g ⟨hg, hgc⟩
    refine ⟨inv_mem hg, fun e he => ?_⟩
    have he' : g⁻¹ * e * g ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) e).1 he
      rwa [inv_inv] at this
    have : ⁅g⁻¹, e⁆ = (⁅g, g⁻¹ * e * g⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact V.inv_mem (hgc _ he')

theorem sec39c_mem_centMod {E V : Subgroup Q} {g : Q} :
    g ∈ sec39cCentMod E V ↔ g ∈ normalizer (E : Set Q) ∧ ∀ e ∈ E, ⁅g, e⁆ ∈ V := Iff.rfl

theorem sec39c_centMod_conj {E V : Subgroup Q} {x y : Q} (hxE : x ∈ normalizer (E : Set Q))
    (hxV : x ∈ normalizer (V : Set Q)) (hy : y ∈ sec39cCentMod E V) :
    x * y * x⁻¹ ∈ sec39cCentMod E V := by
  obtain ⟨hyE, hyc⟩ := hy
  refine ⟨mul_mem (mul_mem hxE hyE) (inv_mem hxE), fun e he => ?_⟩
  have he' : x⁻¹ * e * x ∈ E := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxE) e).1 he
    rwa [inv_inv] at this
  have : ⁅x * y * x⁻¹, e⁆ = x * ⁅y, x⁻¹ * e * x⁆ * x⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.1 hxV _).1 (hyc _ he')

theorem sec39c_lift_fixed [Finite Q] {p : ℕ} [Fact p.Prime] {P N A : Subgroup Q} (hNP : N ≤ P)
    (hPN : P ≤ normalizer (N : Set Q)) (hAP : A ≤ normalizer (P : Set Q))
    (hAN : A ≤ normalizer (N : Set Q)) (hN : IsPGroup p N) (hA : ¬ p ∣ Nat.card A) {x : Q}
    (hx : x ∈ P) (htriv : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N) :
    ∃ c ∈ P ⊓ centralizer (A : Set Q), c⁻¹ * x ∈ N := by
  classical
  let : MulDistribMulAction A P := Subgroup.conjMulDistribMulActionOfLeNormalizer A P hAP
  have hsmul : ∀ (a : A) (y : P), ((a • y : P) : Q) = a * y * (a : Q)⁻¹ := fun _ _ => rfl
  have : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).2 hPN
  have hinv : CFSG.IsInvariant A P (N.subgroupOf P) := ⟨fun a y => by
    rw [mem_subgroupOf, mem_subgroupOf, hsmul]
    exact mem_normalizer_iff.1 (hAN a.2) y⟩
  have hNp : IsPGroup p (N.subgroupOf P) := hN.comap_subtype
  have hsolv : Group.IsSolvable (N.subgroupOf P) := by
    have := hNp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (N.subgroupOf P)) := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hA).symm
  have hl := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting (N.subgroupOf P)
    hinv hsolv hcop
  let : MulDistribMulAction A (P ⧸ N.subgroupOf P) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := P) (N.subgroupOf P) hinv
  let : MulAction.QuotientAction A (N.subgroupOf P) :=
    CFSG.quotientAction_of_isInvariant (A := A) (N.subgroupOf P) hinv
  have hx' : ((⟨x, hx⟩ : P) : P ⧸ N.subgroupOf P) ∈
      CFSG.fixedPointSubgroup A (P ⧸ N.subgroupOf P) := by
    intro a
    rw [MulAction.Quotient.smul_coe (H := N.subgroupOf P) a ⟨x, hx⟩, QuotientGroup.eq,
      mem_subgroupOf]
    change ((a : Q) * x * (a : Q)⁻¹)⁻¹ * x ∈ N
    have e : ((a : Q) * x * (a : Q)⁻¹)⁻¹ * x = (x⁻¹ * ((a : Q) * x * (a : Q)⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem (htriv _ a.2)
  rw [hl] at hx'
  obtain ⟨c, hc, hcx⟩ := hx'
  refine ⟨c, ⟨c.2, mem_centralizer_iff.2 fun a ha => ?_⟩, ?_⟩
  · have h2 : a * c * a⁻¹ = c := congrArg Subtype.val (hc ⟨a, ha⟩)
    calc a * c = a * c * a⁻¹ * a := by group
      _ = c * a := by rw [h2]
  · have h3 : ((c : P) : P ⧸ N.subgroupOf P) = ((⟨x, hx⟩ : P) : P ⧸ N.subgroupOf P) := hcx
    have h4 : c⁻¹ * (⟨x, hx⟩ : P) ∈ N.subgroupOf P := QuotientGroup.eq.1 h3
    exact h4

theorem sec39c_mem_of_odd_mul {L Y : Subgroup Q} (hYL : Y ≤ L)
    (hY : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {s y o : Q} (hs : s ∈ L) (hy : y ∈ Y)
    (ho : o ∈ L) (hso : s = y * o) {k m : ℕ} (hsk : s ^ 2 ^ k = 1) (hom : o ^ m = 1)
    (hm : Odd m) : s ∈ Y := by
  haveI : (Y.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hY g.1 g.2 n hn⟩
  set N := Y.subgroupOf L with hN
  let sL : L := ⟨s, hs⟩
  let yL : L := ⟨y, hYL hy⟩
  let oL : L := ⟨o, ho⟩
  have hyN : yL ∈ N := hy
  have hsyo : sL = yL * oL := Subtype.ext hso
  have e1 : QuotientGroup.mk' N yL = 1 := (QuotientGroup.eq_one_iff yL).2 hyN
  have e2 : QuotientGroup.mk' N sL = QuotientGroup.mk' N oL := by
    rw [hsyo, map_mul, e1, one_mul]
  have h1 : (QuotientGroup.mk' N sL) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : sL ^ 2 ^ k = 1 := Subtype.ext (by simpa using hsk)
    rw [this, map_one]
  have h2 : (QuotientGroup.mk' N sL) ^ m = 1 := by
    rw [e2, ← map_pow]
    have : oL ^ m = 1 := Subtype.ext (by simpa using hom)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have hdvd : orderOf (QuotientGroup.mk' N sL) ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact (QuotientGroup.eq_one_iff sL).1 hdvd

end Generic

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem sec39c_sSU_not_comm : ∃ x ∈ A₂sub h, sSU h * x * (sSU h)⁻¹ * x⁻¹ ∉ ZPsub h := by
  obtain ⟨x, hx, x1, x2, x3⟩ := exists_A₂sub_coord h 1 0 0
  refine ⟨x, hx, fun hz => ?_⟩
  obtain ⟨hy, y1, y2, y3⟩ := A₂_conj_sSU hx
  set y := sSU h * x * (sSU h)⁻¹ with hydef
  have hxU := A₂sub_le_U hx
  have hzx : x⁻¹ * y ∈ ZPsub h := by
    have hc := ZPsub_commute hz hxU
    have e : x⁻¹ * y = x⁻¹ * (y * x⁻¹) * x := by group
    rw [e, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hz
  have h0 := (mem_ZPsub.1 hzx).2.1
  rw [(A₂_inv_mul hx hy).1, x1, y1, x3, add_zero] at h0
  exact one_ne_zero h0

theorem sec39c_mem_Ssub_of_comm {x : hypSU h 2 1} (hx : x ∈ A₂sub h)
    (hc : ∀ z ∈ Z₂Psub h, z * x = x * z) : x ∈ Ssub h := by
  have key : ∀ c : K, mat x ιe₁ ιe₂ * h.bar c = h.bar (mat x ιe₁ ιe₂ * h.bar c) := by
    intro c
    obtain ⟨z, hz, z1, z2, z3⟩ := exists_A₂sub_coord h 0 0 c
    have hzZ : z ∈ Z₂Psub h := mem_Z₂Psub_of_A₂ hz z1 z2
    have := (mul_comm_iff_coord hx hz).1 (hc z hzZ).symm
    rw [z1, z2, z3] at this
    simpa using this
  have hα : mat x ιe₁ ιe₂ = 0 := by
    obtain ⟨ω, hω⟩ := h.exists_bar_ne
    have k1 := key 1
    have k2 := key ω
    rw [map_one, mul_one] at k1
    rw [map_mul, h.bar_bar, ← k1] at k2
    have : mat x ιe₁ ιe₂ * (h.bar ω - ω) = 0 := by linear_combination k2
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hω)
  obtain ⟨c1, -, -⟩ := A₂_rel hx
  exact mem_Ssub'.2 ⟨A₂sub_le_U hx, hα, by rw [c1, hα, map_zero]⟩

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

abbrev sec39cH (d : Data G h) : Subgroup G := centralizer (d.I₂ : Set G)

abbrev sec39cQ (d : Data G h) : Type _ := ↥(sec39cH d) ⧸ standardComponentOddCore ↥(sec39cH d)

abbrev sec39cθ (d : Data G h) : ↥(sec39cH d) →* sec39cQ d :=
  QuotientGroup.mk' (standardComponentOddCore ↥(sec39cH d))

omit [Finite G] in
theorem sec39c_conj_V (k8 : d.Know8) {g v : G} (hg : g ∈ d.L₂) (hv : v ∈ d.V) :
    g * v * g⁻¹ = v := by
  have hc := (k8.s8.2.1 hv).2
  rw [mem_centralizer_iff.1 hc g hg, mul_inv_cancel_right]

theorem sec39c_L₂_le_normalizer_V (k8 : d.Know8) : d.L₂ ≤ normalizer (d.V : Set G) := fun g hg =>
  mem_normalizer_fintype fun v hv => by rw [sec39c_conj_V k8 hg hv]; exact hv

omit [Finite G] in
theorem sec39c_M₂_le_L₂ (k8 : d.Know8) : d.M₂ ≤ d.L₂ := by
  rw [k8.s8.1]; exact le_sup_right

omit [Finite G] in
theorem sec39c_M₂_le_H (d : Data G h) : d.M₂ ≤ sec39cH d := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

omit [Finite G] in
theorem sec39c_N₂_le_M₂ (d : Data G h) : d.N₂ ≤ d.M₂ := fun n hn =>
  ⟨⟨n, d.N₂_le_centralizer_I₂ hn⟩, Subgroup.subset_normalClosure (by exact hn), rfl⟩

theorem sec39c_H_le_normalizer_M₂ (d : Data G h) : sec39cH d ≤ normalizer (d.M₂ : Set G) :=
  fun x hx => mem_normalizer_fintype fun n hn => by
    obtain ⟨m, hm, rfl⟩ := hn
    exact ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, (Subgroup.normalClosure_normal).conj_mem m hm ⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem sec39c_s_not_comm (d : Data G h) :
    ∃ a ∈ d.A₂, d.s * a * d.s⁻¹ * a⁻¹ ∈ d.A₂ ∧ d.s * a * d.s⁻¹ * a⁻¹ ∉ d.Zp := by
  obtain ⟨x, hx, hnz⟩ := sec39c_sSU_not_comm (h := h)
  have hg : sSU h * x * (sSU h)⁻¹ * x⁻¹ ∈ A₂sub h :=
    mul_mem (A₂_conj_sSU hx).1 (inv_mem hx)
  have e : d.s * d.η x * d.s⁻¹ * (d.η x)⁻¹ = d.η (sSU h * x * (sSU h)⁻¹ * x⁻¹) := by
    simp only [Data.s, map_mul, map_inv]
  refine ⟨d.η x, ⟨x, hx, rfl⟩, ?_, ?_⟩
  · rw [e]; exact ⟨_, hg, rfl⟩
  · rw [e]
    intro hz
    exact hnz ((d.η_mem_pull_iff ZPsub_le_U (A₂sub_le_U hg)).1 hz)

omit [Finite G] in
theorem sec39c_mem_A₃_of_comm (d : Data G h) {a : G} (ha : a ∈ d.A₂)
    (hc : ∀ z ∈ d.Z₂p, z * a = a * z) : a ∈ d.A₃ := by
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨x, sec39c_mem_Ssub_of_comm hx fun z hz => ?_, rfl⟩
  have hzU := Z₂Psub_le_A₂sub.trans A₂sub_le_U hz
  have := hc (d.η z) ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul] at this
  exact d.η_injOn (mul_mem hzU (A₂sub_le_U hx)) (mul_mem (A₂sub_le_U hx) hzU) this

theorem sec39c_prod (hp : d.ProductCaseHyp) :
    ∃ D₁ D₂ : Subgroup (sec39cQ d), IsSimpleGroup D₁ ∧ IsSimpleGroup D₂ ∧
      D₁ ⊔ D₂ = layer (sec39cQ d) ∧ ⁅D₁, D₂⁆ = ⊥ ∧
      centralizer ((layer (sec39cQ d) : Subgroup (sec39cQ d)) : Set (sec39cQ d)) = ⊥ ∧
      D₁.map (MulAut.conj ((sec39cθ d) ⟨d.t, hp.hyp.t_mem_centralizer_I₂⟩)⁻¹).toMonoidHom = D₂ ∧
      (d.M₂.subgroupOf (sec39cH d)).map (sec39cθ d) = layer (sec39cQ d) := by
  have hd := hp.hyp
  obtain ⟨hsh1, hlay⟩ := hd.sec3_3_two hp.gms
  unfold GMSK.SharpOutcome at hsh1
  obtain ⟨⟨hp2, hfit, hAl, hnc, hcent, halt, hfaith⟩, hsimple⟩ := hsh1
  have hns : ¬ IsSimpleGroup (layer (sec39cQ d)) := hp.caseB
  rcases halt with ⟨hP, hnQ⟩ |
    ⟨⟨D₁, D₂, hc1, hc2, hne, hs1, hn1, hs2, hn2, hsup, hinf, hcomm, hconj, hJ, ψ, hψ1, hψ2⟩, hnP⟩
  · exfalso
    apply hns
    have := hP.1
    rwa [hnc] at this
  · refine ⟨D₁, D₂, hs1, hs2, ?_, hcomm, ?_, hconj, hlay⟩
    · rw [hsup, hnc]
    · rw [← hnc]; exact hcent

theorem sec39c_Y₂_mem_odd (hp : d.ProductCaseHyp) (k8 : d.Know8) {m : G} (hm : m ∈ d.M₂)
    (hmc : m ∈ sec39cCentMod d.E d.V) :
    ∃ hmH : m ∈ sec39cH d,
      (⟨m, hmH⟩ : ↥(sec39cH d)) ∈ standardComponentOddCore ↥(sec39cH d) := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨D₁, D₂, hD₁, hD₂, hsup, hcomm, hcent, hconj, hlay⟩ := sec39c_prod hp
  have hME : ∀ x ∈ d.M₂, x ∈ normalizer (d.E : Set G) := fun x hx =>
    d.L₂_le_normalizer_E (sec39c_M₂_le_L₂ k8 hx)
  have hMV : ∀ x ∈ d.M₂, x ∈ normalizer (d.V : Set G) := fun x hx =>
    sec39c_L₂_le_normalizer_V k8 (sec39c_M₂_le_L₂ k8 hx)
  have htE : d.t ∈ normalizer (d.E : Set G) := hd.t_mem_normalizer_E_caseB hGMS
  have htV : d.t ∈ normalizer (d.V : Set G) :=
    hd.normalizer_B₄_le_normalizer_V hGMS (le_normalizer hd.t_mem_B₄)
  have htM : d.t ∈ normalizer (d.M₂ : Set G) :=
    sec39c_H_le_normalizer_M₂ d hd.t_mem_centralizer_I₂
  let Y₂ : Subgroup G := sec39cCentMod d.E d.V ⊓ d.M₂
  let Kb : Subgroup (sec39cQ d) := (Y₂.subgroupOf (sec39cH d)).map (sec39cθ d)
  have hKD : Kb ≤ layer (sec39cQ d) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hlay]
    exact ⟨y, (Subgroup.mem_subgroupOf.1 hy).2, rfl⟩
  have hKn : ∀ x ∈ layer (sec39cQ d), ∀ k ∈ Kb, x * k * x⁻¹ ∈ Kb := by
    intro x hx k hk
    rw [← hlay] at hx
    obtain ⟨m₀, hm₀, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hk
    refine ⟨m₀ * y * m₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hm₀' : (m₀ : G) ∈ d.M₂ := Subgroup.mem_subgroupOf.1 hm₀
    obtain ⟨hyc, hyM⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨sec39c_centMod_conj (hME _ hm₀') (hMV _ hm₀') hyc,
      d.M₂.mul_mem (d.M₂.mul_mem hm₀' hyM) (d.M₂.inv_mem hm₀')⟩
  have hKconj : ∀ g : ↥(sec39cH d), (g : G) ∈ normalizer (d.E : Set G) →
      (g : G) ∈ normalizer (d.V : Set G) → (g : G) ∈ normalizer (d.M₂ : Set G) →
      ∀ k ∈ Kb, sec39cθ d g * k * (sec39cθ d g)⁻¹ ∈ Kb := by
    intro g hgE hgV hgM k hk
    obtain ⟨y, hy, rfl⟩ := hk
    refine ⟨g * y * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    obtain ⟨hyc, hyM⟩ := Subgroup.mem_subgroupOf.1 hy
    exact ⟨sec39c_centMod_conj hgE hgV hyc, (Subgroup.mem_normalizer_iff.1 hgM _).1 hyM⟩
  have htH : d.t ∈ sec39cH d := hd.t_mem_centralizer_I₂
  have hfinal : ¬ layer (sec39cQ d) ≤ Kb := by
    intro hlayK
    have hsH : d.s ∈ sec39cH d := d.N₂_le_centralizer_I₂ d.s_mem_N₂
    have hsl : sec39cθ d ⟨d.s, hsH⟩ ∈ layer (sec39cQ d) := by
      rw [← hlay]
      exact ⟨⟨d.s, hsH⟩, Subgroup.mem_subgroupOf.2 (sec39c_N₂_le_M₂ d d.s_mem_N₂), rfl⟩
    obtain ⟨y, hy, hys⟩ := hlayK hsl
    have ho : y⁻¹ * ⟨d.s, hsH⟩ ∈ standardComponentOddCore ↥(sec39cH d) :=
      QuotientGroup.eq.1 hys
    obtain ⟨hyc, hyM⟩ := Subgroup.mem_subgroupOf.1 hy
    have hodd : Odd (Nat.card (standardComponentOddCore ↥(sec39cH d))) :=
      GMSK.odd_card_standardComponentOddCore _
    have ho1 : (y⁻¹ * ⟨d.s, hsH⟩ : ↥(sec39cH d)) ^
        (Nat.card (standardComponentOddCore ↥(sec39cH d))) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ ho)
    have ho2 : ((y : G)⁻¹ * d.s) ^ Nat.card (standardComponentOddCore ↥(sec39cH d)) = 1 := by
      have := congrArg Subtype.val ho1
      simpa using this
    have hyL : (y : G) ∈ d.L₂ := sec39c_M₂_le_L₂ k8 hyM
    have hsL : d.s ∈ d.L₂ := d.N₂_le_L₂ d.s_mem_N₂
    have hs2 : d.s ^ 2 ^ 1 = 1 := by
      have := pow_orderOf_eq_one d.s
      rwa [d.orderOf_s] at this
    have hsmem : d.s ∈ sec39cCentMod d.E d.V ⊓ d.L₂ :=
      sec39c_mem_of_odd_mul (L := d.L₂) (Y := sec39cCentMod d.E d.V ⊓ d.L₂) inf_le_right
        (fun g hg y' hy' => ⟨sec39c_centMod_conj (d.L₂_le_normalizer_E hg)
          (sec39c_L₂_le_normalizer_V k8 hg) hy'.1,
            d.L₂.mul_mem (d.L₂.mul_mem hg hy'.2) (d.L₂.inv_mem hg)⟩)
        hsL ⟨hyc, hyL⟩ (d.L₂.mul_mem (d.L₂.inv_mem hyL) hsL) (by group) hs2 ho2 hodd
    obtain ⟨a₀, ha₀, hA, hnZ⟩ := sec39c_s_not_comm d
    have ha₀E : a₀ ∈ d.E := hd.A₂_le_E hGMS ha₀
    have hV : d.s * a₀ * d.s⁻¹ * a₀⁻¹ ∈ d.V := hsmem.1.2 a₀ ha₀E
    exact hnZ (by rw [← hd.V_inf_A₂]; exact ⟨hV, hA⟩)
  have hKa : ∀ k ∈ Kb, (sec39cθ d ⟨d.t, htH⟩)⁻¹ * k * (sec39cθ d ⟨d.t, htH⟩)⁻¹⁻¹ ∈ Kb := by
    intro k hk
    have := hKconj ⟨d.t, htH⟩⁻¹ (inv_mem htE) (inv_mem htV) (inv_mem htM) k hk
    simpa only [map_inv] using this
  have hKa' : ∀ k ∈ Kb, (sec39cθ d ⟨d.t, htH⟩) * k * (sec39cθ d ⟨d.t, htH⟩)⁻¹ ∈ Kb :=
    hKconj ⟨d.t, htH⟩ htE htV htM
  rcases sec39c_normal_in_prod hD₁ hD₂ hsup hcomm hcent hKD hKn with h0 | h1 | h2
  · have hmH := sec39c_M₂_le_H d hm
    refine ⟨hmH, ?_⟩
    have hmY : (⟨m, hmH⟩ : ↥(sec39cH d)) ∈ Y₂.subgroupOf (sec39cH d) :=
      Subgroup.mem_subgroupOf.2 ⟨hmc, hm⟩
    have : sec39cθ d ⟨m, hmH⟩ ∈ Kb := ⟨_, hmY, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  · exfalso
    refine hfinal ?_
    rw [← hsup]
    refine sup_le h1 ?_
    rw [← hconj]
    rintro _ ⟨x, hx, rfl⟩
    exact hKa x (h1 hx)
  · exfalso
    refine hfinal ?_
    rw [← hsup]
    refine sup_le ?_ h2
    intro x hx
    have hx2 : (MulAut.conj (sec39cθ d ⟨d.t, htH⟩)⁻¹).toMonoidHom x ∈ D₂ := by
      rw [← hconj]; exact ⟨x, hx, rfl⟩
    have := hKa' _ (h2 hx2)
    have e : (sec39cθ d ⟨d.t, htH⟩) *
        ((MulAut.conj (sec39cθ d ⟨d.t, htH⟩)⁻¹).toMonoidHom x) *
          (sec39cθ d ⟨d.t, htH⟩)⁻¹ = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [e] at this

omit [Finite G] in
theorem sec39c_E_le_S {S : Subgroup G} (ha : d.Sec39a S) : d.E ≤ S := ha.S_eq ▸ le_sup_left

omit [Finite G] in
theorem sec39c_D_le_S {S : Subgroup G} (ha : d.Sec39a S) : d.D ≤ S := ha.S_eq ▸ le_sup_right

theorem sec39c_exists_W_cr (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {a : G}
    (ha : a ∈ d.Z₂p) : ∃ w ∈ d.W, w⁻¹ * d.t * w * d.t = a := by
  rw [hd.Z₂p_eq.1] at ha
  obtain ⟨z₀, hz₀, z, hz, hz₀z⟩ := exists_mul_of_mem_sup_of_le_normalizer d.C₄_le_normalizer_Zp ha
  obtain ⟨v, hv, hvz⟩ := hd.exists_V_cr_eq hz₀
  obtain ⟨c, hc, hcz⟩ := hd.exists_F_I₄_cr_eq hGMS hz
  refine ⟨v * c, ?_, ?_⟩
  · rw [hd.W_eq hGMS]; exact mul_mem (mem_sup_left hv) (mem_sup_right hc)
  · rw [hd.cr_F_mul (d.V_le_F hv) hc.1, hvz, hcz, hz₀z]

theorem sec39c_Z₂p_of_fixed (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {z v a : G} (hz : z ∈ d.E) (hv : v ∈ d.V) (ha : a ∈ d.A₂)
    (hcr : z⁻¹ * d.t * z * d.t = v * a) (hP : ∀ p ∈ d.P, ⁅p, z⁆ ∈ d.V) : a ∈ d.Z₂p := by
  obtain ⟨-, -, -, -, ⟨ψ, -, hψk, hψ1, hψ2⟩, -⟩ := hd.sec3_6 hGMS
  have ha' : a ∈ d.P := d.A₂_le_P ha
  refine (d.mem_Z₂p_iff ha').2 fun p hp => ?_
  have hpt : p ∈ centralizer ({d.t} : Set G) := hd.tP_le_centralizer (mem_sup_right hp)
  have hpN : p ∈ normalizer (d.ZtP : Set G) := d.tP_le_normalizer_ZtP (mem_sup_right hp)
  have hpB₂ : p ∈ normalizer (d.B₂ : Set G) := hd.normalizer_ZtP_le_normalizer_B₂ hpN
  have hpA : p * a * p⁻¹ ∈ d.A₂ := hd.conj_mem_A₂ hpN hpt ha
  have hpz : p * z * p⁻¹ ∈ d.E :=
    (Subgroup.mem_normalizer_iff.1 (d.L₂_le_normalizer_E (hd.P_le_L₂ hGMS hp)) z).1 hz
  have h1 : ψ ⟨z, hz⟩ = QuotientGroup.mk ⟨a, ha⟩ := hψ1 ⟨z, hz⟩ ⟨a, ha⟩ v hv hcr
  have h2 := hψ2 p ⟨hpB₂, hpt⟩ ⟨z, hz⟩ ⟨a, ha⟩ hpz hpA h1
  have h3 : ψ ⟨p * z * p⁻¹, hpz⟩ = ψ ⟨z, hz⟩ := by
    have e : (⟨p * z * p⁻¹, hpz⟩ : d.E) = ⟨⁅p, z⁆, d.V_le_E (hP p hp)⟩ * ⟨z, hz⟩ :=
      Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul]; group)
    rw [e, map_mul]
    have : ψ ⟨⁅p, z⁆, d.V_le_E (hP p hp)⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hψk]
      exact Subgroup.mem_subgroupOf.2 (mem_sup_left (hP p hp))
    rw [this, one_mul]
  rw [h3, h1] at h2
  have h4 : (⟨a, ha⟩ : ↥d.A₂)⁻¹ * ⟨p * a * p⁻¹, hpA⟩ ∈ d.Zp.subgroupOf d.A₂ :=
    QuotientGroup.eq.1 h2
  have h5 : a⁻¹ * (p * a * p⁻¹) ∈ d.Zp := Subgroup.mem_subgroupOf.1 h4
  have e : ⁅a, p⁆ = a * (a⁻¹ * (p * a * p⁻¹))⁻¹ * a⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (d.P_le_normalizer_Zp ha') _).1 (inv_mem h5)

omit [Finite G] in
theorem sec39c_F_le_D (hb : d.Sec39b) : d.F ≤ d.D := hb.1 ▸ inf_le_left

omit [Finite G] in
theorem sec39c_D_comm_W (hb : d.Sec39b) (hWF : d.W ≤ d.F) {x w : G} (hx : x ∈ d.D)
    (hw : w ∈ d.W) : w * x = x * w := by
  have : w ∈ CFSG.centerIn d.D := hb.1 ▸ hWF hw
  exact (Subgroup.mem_centralizer_iff.1 this.2 x hx).symm

theorem sec39c_A₃_le_D (hd : d.Hyp) {S : Subgroup G} (hP : d.P ≤ S) (ha : d.Sec39a S)
    (hb : d.Sec39b) : d.A₃ ≤ d.D := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := d.sec2_1_two hd.two_le
  rw [h8]
  refine sup_le (sup_le (hd.A₁_le_F.trans (sec39c_F_le_D hb)) ?_) ?_
  · intro x hx
    have : x ∈ S ⊓ centralizer (d.I₂ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← ha.cD₂] at this
    exact this.1
  · intro x hx
    have : x ∈ S ⊓ centralizer (d.I₅ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← ha.cD₅] at this
    exact this.1

omit [Finite G] in
theorem sec39c_C₅_le_normalizer_Z₂p (d : Data G h) :
    d.P ⊓ centralizer (d.I₅ : Set G) ≤ normalizer (d.Z₂p : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro c hc z hz
  have hcP : c ∈ d.P := hc.1
  have hzP : z ∈ d.P := d.A₂_le_P (d.Z₂p_le_A₂ hz)
  refine (d.mem_Z₂p_iff (d.P.mul_mem (d.P.mul_mem hcP hzP) (d.P.inv_mem hcP))).2 fun u hu => ?_
  have h1 := (d.mem_Z₂p_iff hzP).1 hz (c⁻¹ * u * c)
    (d.P.mul_mem (d.P.mul_mem (d.P.inv_mem hcP) hu) hcP)
  have e : ⁅c * z * c⁻¹, u⁆ = c * ⁅z, c⁻¹ * u * c⁆ * c⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (d.P_le_normalizer_Zp hcP) _).1 h1

theorem sec39c_lift_I₅ (hp : d.CaseHyp) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (ha : d.Sec39a S) {e₀ : G} (he₀ : e₀ ∈ d.E)
    (hfix : ∀ i ∈ d.I₅, e₀⁻¹ * (i * e₀ * i⁻¹) ∈ d.V ⊔ d.A₂) :
    ∃ c ∈ d.E ⊓ centralizer (d.I₅ : Set G), c⁻¹ * e₀ ∈ d.V ⊔ d.A₂ := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨-, -, -, -, ⟨ψ, -, hψk, -, -⟩, -⟩ := hd.sec3_6 hGMS
  have hNP : d.V ⊔ d.A₂ ≤ d.E := hd.VA_le_E hGMS
  have hPN : d.E ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := by
    have : (((d.V ⊔ d.A₂ : Subgroup G)).subgroupOf d.E).Normal := hψk ▸ ψ.normal_ker
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).1 this
  have hAP : d.I₅ ≤ normalizer (d.E : Set G) := fun i hi =>
    hd.normalizer_B₄_le_normalizer_E hGMS (hd.I_le_normalizer_B₄ (d.I₅_le_I hi))
  have hAN : d.I₅ ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := fun i hi =>
    hd.normalizer_B₄_le_normalizer_VA hGMS (hd.I_le_normalizer_B₄ (d.I₅_le_I hi))
  have hN : IsPGroup 2 (d.V ⊔ d.A₂ : Subgroup G) :=
    hS.isPGroup.to_le (hNP.trans (sec39c_E_le_S ha))
  have hodd : Odd (Nat.card d.I₅) :=
    Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₅_le_I)
  have hA : ¬ 2 ∣ Nat.card d.I₅ := fun hdvd =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  exact sec39c_lift_fixed (p := 2) hNP hPN hAP hAN hN hA he₀ hfix

theorem sec39c_I_mem (hd : d.Hyp) {i : G} (hi : i ∈ d.I) :
    i ∈ normalizer (d.ZtP : Set G) ∧ i ∈ centralizer ({d.t} : Set G) :=
  ⟨d.normalizer_tP_le_normalizer_ZtP (hd.I_le hi).2, (hd.I_le hi).1⟩

theorem sec39c_CE_le_D (hp : d.CaseHyp) (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b) {e : G} (he : e ∈ d.E)
    (hec : ∀ w ∈ d.W, w * e = e * w) : e ∈ d.D := by
  have hd := hp.hyp
  have hGMS := hp.gms
  obtain ⟨-, -, -, -, ⟨ψ, hψs, hψk, hψ1, hψ2⟩, -⟩ := hd.sec3_6 hGMS
  have hWF : d.W ≤ d.F := (hd.sec3_5_one hGMS).2.2.2.2.2.1
  have hFD := sec39c_F_le_D hb
  have hZW : d.Z₂p ≤ d.W := hd.Z₂p_le_W hGMS
  have hA₃D := sec39c_A₃_le_D hd hP ha hb
  have hZL : ∀ z ∈ d.Z₂p, z ∈ d.L := fun z hz => d.pull_le_L _ (d.Z₂p_le_A₂ hz)
  have hZP : ∀ z ∈ d.Z₂p, z ∈ d.P := fun z hz => d.A₂_le_P (d.Z₂p_le_A₂ hz)
  have hVP : ∀ z ∈ d.P, ∀ v ∈ d.V, Commute z v := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.1 (hd.FP_le_centralizer_V hGMS (mem_sup_right hz)) v hv).symm
  have hEC := hd.E_le_C₀ hGMS he
  obtain ⟨v, hv, a, ha₂, hva⟩ :=
    hd.exists_mul_of_mem_VA (hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ hEC))
  have haZ : ∀ z ∈ d.Z₂p, z * a = a * z := by
    intro z hz
    have hze : Commute z e := hec z (hZW hz)
    have hzt : Commute z d.t := hd.comm_t (hZL z hz)
    have hzc : Commute z (e⁻¹ * d.t * e * d.t) :=
      ((hze.inv_right.mul_right hzt).mul_right hze).mul_right hzt
    have h1 : Commute z (v⁻¹ * (e⁻¹ * d.t * e * d.t)) :=
      (hVP z (hZP z hz) v hv).inv_right.mul_right hzc
    rw [hva, inv_mul_cancel_left] at h1
    exact h1
  have haA₃ : a ∈ d.A₃ := sec39c_mem_A₃_of_comm d ha₂ haZ
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := d.sec2_1_two hd.two_le
  have ha' : a ∈ d.Z₂p ⊔ (d.P ⊓ centralizer (d.I₅ : Set G)) := by
    rw [← h9]; exact ⟨ha₂, haA₃⟩
  obtain ⟨z₂, hz₂, c₅, hc₅, hac⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (sec39c_C₅_le_normalizer_Z₂p d) ha'
  have hz₂A : z₂ ∈ d.A₂ := d.Z₂p_le_A₂ hz₂
  have hc₅A : c₅ ∈ d.A₂ := by
    have : c₅ ∈ d.A₂ ⊓ d.A₃ := by rw [h9]; exact mem_sup_right hc₅
    exact this.1
  obtain ⟨w, hwW, hwc⟩ := sec39c_exists_W_cr hGMS hd hz₂
  have hwE := d.W_le_E hwW
  have hψw : ψ ⟨w, hwE⟩ = QuotientGroup.mk ⟨z₂, hz₂A⟩ :=
    hψ1 ⟨w, hwE⟩ ⟨z₂, hz₂A⟩ 1 (one_mem _) (by rw [hwc, one_mul])
  have hψe : ψ ⟨e, he⟩ = QuotientGroup.mk ⟨a, ha₂⟩ := hψ1 ⟨e, he⟩ ⟨a, ha₂⟩ v hv hva
  obtain ⟨⟨e₀, he₀⟩, hε⟩ := hψs (QuotientGroup.mk ⟨c₅, hc₅A⟩)
  have hfix : ∀ i ∈ d.I₅, e₀⁻¹ * (i * e₀ * i⁻¹) ∈ d.V ⊔ d.A₂ := by
    intro i hi
    have hiI := d.I₅_le_I hi
    obtain ⟨hiN, hit⟩ := sec39c_I_mem hd hiI
    have hiB₂ : i ∈ normalizer (d.B₂ : Set G) := hd.normalizer_ZtP_le_normalizer_B₂ hiN
    have hiE : i * e₀ * i⁻¹ ∈ d.E :=
      (Subgroup.mem_normalizer_iff.1
        (hd.normalizer_B₄_le_normalizer_E hGMS (hd.I_le_normalizer_B₄ hiI)) e₀).1 he₀
    have hic₅ : i * c₅ * i⁻¹ ∈ d.A₂ := hd.conj_mem_A₂ hiN hit hc₅A
    have h2 := hψ2 i ⟨hiB₂, hit⟩ ⟨e₀, he₀⟩ ⟨c₅, hc₅A⟩ hiE hic₅ hε
    have hfixc : i * c₅ * i⁻¹ = c₅ := by
      rw [Subgroup.mem_centralizer_iff.1 hc₅.2 i hi, mul_inv_cancel_right]
    have e1 : (⟨i * c₅ * i⁻¹, hic₅⟩ : ↥d.A₂) = ⟨c₅, hc₅A⟩ := Subtype.ext hfixc
    rw [e1, ← hε] at h2
    have h3 : ψ (⟨e₀, he₀⟩⁻¹ * ⟨i * e₀ * i⁻¹, hiE⟩) = 1 := by
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hψk] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  obtain ⟨c', ⟨hc'E, hc'C⟩, hc'⟩ := sec39c_lift_I₅ hp hS ha he₀ hfix
  have hψc : ψ ⟨c', hc'E⟩ = QuotientGroup.mk ⟨c₅, hc₅A⟩ := by
    have h3 : ψ (⟨c', hc'E⟩⁻¹ * ⟨e₀, he₀⟩) = 1 := by
      rw [← MonoidHom.mem_ker, hψk]; exact Subgroup.mem_subgroupOf.2 hc'
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    rw [h3, hε]
  have hc'D : c' ∈ d.D := by
    have : c' ∈ S ⊓ centralizer (d.I₅ : Set G) := ⟨sec39c_E_le_S ha hc'E, hc'C⟩
    rw [← ha.cD₅] at this
    exact this.1
  have hxD : w * c' ∈ d.D := d.D.mul_mem (hFD (hWF hwW)) hc'D
  have hxE : w * c' ∈ d.E := d.E.mul_mem hwE hc'E
  have hψx : ψ ⟨w * c', hxE⟩ = ψ ⟨e, he⟩ := by
    have e1 : (⟨w * c', hxE⟩ : ↥d.E) = ⟨w, hwE⟩ * ⟨c', hc'E⟩ := rfl
    rw [e1, map_mul, hψw, hψc, hψe, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hac.symm
  have hu : (w * c')⁻¹ * e ∈ d.V ⊔ d.A₂ := by
    have h3 : ψ (⟨w * c', hxE⟩⁻¹ * ⟨e, he⟩) = 1 := by
      rw [map_mul, map_inv, hψx, inv_mul_cancel]
    rw [← MonoidHom.mem_ker, hψk] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  have huc : ∀ w' ∈ d.W, Commute w' ((w * c')⁻¹ * e) := fun w' hw' =>
    (show Commute w' (w * c') from sec39c_D_comm_W hb hWF hxD hw').inv_right.mul_right
      (hec w' hw')
  obtain ⟨v₁, hv₁, a₁, ha₁, hva₁⟩ := hd.exists_mul_of_mem_VA hu
  have ha₁Z : ∀ z ∈ d.Z₂p, z * a₁ = a₁ * z := by
    intro z hz
    have h1 : Commute z (v₁⁻¹ * ((w * c')⁻¹ * e)) :=
      (hVP z (hZP z hz) v₁ hv₁).inv_right.mul_right (huc z (hZW hz))
    rw [hva₁, inv_mul_cancel_left] at h1
    exact h1
  have ha₁D : a₁ ∈ d.D := hA₃D (sec39c_mem_A₃_of_comm d ha₁ ha₁Z)
  have huD : (w * c')⁻¹ * e ∈ d.D := by
    rw [hva₁]; exact d.D.mul_mem (hFD (d.V_le_F hv₁)) ha₁D
  have : e = (w * c') * ((w * c')⁻¹ * e) := by group
  rw [this]
  exact d.D.mul_mem hxD huD

@[expose] def Sec39cY₂ (d : Data G h) : Prop :=
  ∀ {m : G}, m ∈ d.M₂ → m ∈ sec39cCentMod d.E d.V →
    ∃ hmH : m ∈ sec39cH d, (⟨m, hmH⟩ : ↥(sec39cH d)) ∈ standardComponentOddCore ↥(sec39cH d)

theorem sec39c_claimY (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hY₂ : d.Sec39cY₂) :
    ∀ s ∈ S, (∀ e ∈ d.E, ⁅s, e⁆ ∈ d.V) → s ∈ d.E := by
  intro s hs hsc
  have hd := hp.hyp
  obtain ⟨-, -, -, -, -, -, hEA, -⟩ := hd.sec3_6 hp.gms
  have hME : d.M₂ ≤ normalizer (d.E : Set G) := fun x hx =>
    d.L₂_le_normalizer_E (sec39c_M₂_le_L₂ k8 hx)
  have hs' : s ∈ ((d.E ⊔ d.M₂ : Subgroup G) : Set G) := by
    rw [← k8.s8.1]; exact hS.le hs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hME] at hs'
  obtain ⟨e, he, m, hm, rfl⟩ := hs'
  have heS : e ∈ S := sec39c_E_le_S ha he
  have hmS : m ∈ S := by
    have := S.mul_mem (S.inv_mem heS) hs
    rwa [inv_mul_cancel_left] at this
  have hmc : m ∈ sec39cCentMod d.E d.V := by
    refine ⟨hME hm, fun x hx => ?_⟩
    have hx' : m * x * m⁻¹ ∈ d.E := (Subgroup.mem_normalizer_iff.1 (hME hm) x).1 hx
    have e1 : ⁅m, x⁆ = (⁅e, m * x * m⁻¹⁆)⁻¹ * ⁅e * m, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact d.V.mul_mem (d.V.inv_mem (hEA.2 e he _ hx')) (hsc x hx)
  obtain ⟨hmH, hmO⟩ := hY₂ hm hmc
  have hodd : Odd (Nat.card (standardComponentOddCore ↥(sec39cH d))) :=
    GMSK.odd_card_standardComponentOddCore _
  have hm1 : m ^ Nat.card (standardComponentOddCore ↥(sec39cH d)) = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hmO)
    have := congrArg Subtype.val this
    simpa using this
  obtain ⟨k, hk⟩ := hS.isPGroup ⟨m, hmS⟩
  have hm2 : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (standardComponentOddCore ↥(sec39cH d))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hdvd : orderOf m ∣ Nat.gcd (2 ^ k) (Nat.card (standardComponentOddCore ↥(sec39cH d))) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm2) (orderOf_dvd_of_pow_eq_one hm1)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  show e * m ∈ d.E
  rw [hdvd, mul_one]
  exact he

theorem sec39c_center (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hY₂ : d.Sec39cY₂) :
    CFSG.centerIn S = d.V := by
  have hY := sec39c_claimY hp k8 S hS hP ha hY₂
  obtain ⟨-, -, -, -, -, hZE, -, -⟩ := hp.hyp.sec3_6 hp.gms
  apply le_antisymm
  · intro z hz
    have hzc : ∀ x ∈ S, x * z = z * x := Subgroup.mem_centralizer_iff.1 hz.2
    have hzE : z ∈ d.E := hY z hz.1 (fun e he => by
      have h1 : z * e = e * z := (hzc e (sec39c_E_le_S ha he)).symm
      have : ⁅z, e⁆ = 1 := by
        rw [commutatorElement_def, h1]; group
      rw [this]; exact one_mem _)
    rw [← hZE]
    exact ⟨hzE, Subgroup.mem_centralizer_iff.2 fun x hx => hzc x (sec39c_E_le_S ha hx)⟩
  · intro v hv
    refine ⟨sec39c_E_le_S ha (d.V_le_E hv), Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 (k8.s8.2.1 hv).2 x (hS.le hx)

theorem sec39c_W_le_Z₂ (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b)
    (hY₂ : d.Sec39cY₂) :
    d.W ≤ (Subgroup.upperCentralSeries ↥S 2).map S.subtype := by
  intro w hw
  have hd := hp.hyp
  obtain ⟨-, -, -, -, -, -, hEA, -⟩ := hd.sec3_6 hp.gms
  have hWF : d.W ≤ d.F := (hd.sec3_5_one hp.gms).2.2.2.2.2.1
  have hwE : w ∈ d.E := d.W_le_E hw
  have hcS := sec39c_center hp k8 S hS hP ha hY₂
  rw [mem_map_upperCentralSeries_two]
  refine ⟨sec39c_E_le_S ha hwE, fun y hy => ?_⟩
  rw [hcS]
  have hDE : d.D ≤ normalizer (d.E : Set G) :=
    (sec39c_D_le_S ha).trans (hS.le.trans d.L₂_le_normalizer_E)
  have hy' : y ∈ ((d.E ⊔ d.D : Subgroup G) : Set G) := by rw [← ha.S_eq]; exact hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDE] at hy'
  obtain ⟨e, he, δ, hδ, rfl⟩ := hy'
  have hwc : ∀ x ∈ d.D, x * w = w * x := by
    have : w ∈ CFSG.centerIn d.D := hb.1 ▸ hWF hw
    exact Subgroup.mem_centralizer_iff.1 this.2
  have h1 : δ * w⁻¹ * δ⁻¹ = w⁻¹ := by
    have hcom : Commute δ w := hwc δ hδ
    rw [(Commute.inv_right hcom).eq, mul_inv_cancel_right]
  have : ⁅w, e * δ⁆ = ⁅w, e⁆ := by
    simp only [commutatorElement_def]
    calc w * (e * δ) * w⁻¹ * (e * δ)⁻¹ = w * e * (δ * w⁻¹ * δ⁻¹) * e⁻¹ := by group
      _ = w * e * w⁻¹ * e⁻¹ := by rw [h1]
  rw [show (fun x1 x2 => x1 * x2) e δ = e * δ from rfl, this]
  exact hEA.2 w hwE e he

theorem sec39c_Z₂ (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b)
    (hY₂ : d.Sec39cY₂) :
    (Subgroup.upperCentralSeries ↥S 2).map S.subtype = d.W := by
  have hd := hp.hyp
  have hGMS := hp.gms
  have hcS := sec39c_center hp k8 S hS hP ha hY₂
  have hWZ := sec39c_W_le_Z₂ hp k8 S hS hP ha hb hY₂
  refine le_antisymm (fun z hz => ?_) hWZ
  obtain ⟨hzS, hzc⟩ := mem_map_upperCentralSeries_two.1 hz
  rw [hcS] at hzc
  have hzE : z ∈ d.E := sec39c_claimY hp k8 S hS hP ha hY₂ z hzS fun e he =>
    hzc e (sec39c_E_le_S ha he)
  have hEC := hd.E_le_C₀ hGMS hzE
  obtain ⟨v, hv, a, ha₂, hva⟩ := hd.exists_mul_of_mem_VA
    (hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ hEC))
  have haZ : a ∈ d.Z₂p := sec39c_Z₂p_of_fixed hGMS hd hzE hv ha₂ hva fun p hp' => by
    rw [← commutatorElement_inv]
    exact d.V.inv_mem (hzc p (hP hp'))
  obtain ⟨w, hwW, hwc⟩ := sec39c_exists_W_cr hGMS hd haZ
  have hwE := d.W_le_E hwW
  have hxy : (w⁻¹ * d.t * w * d.t)⁻¹ * (z⁻¹ * d.t * z * d.t) ∈ d.V := by
    rw [hwc, hva]
    have hcomm : a * v = v * a := hd.comm_V_of_mem_VA hGMS (mem_sup_right ha₂) hv
    have : a⁻¹ * (v * a) = v := by rw [← hcomm]; group
    rw [this]; exact hv
  have hwz : w⁻¹ * z ∈ d.B₄ := hd.inv_mul_mem_B₄ hGMS (hd.W_le_C₀ hGMS hwW) hEC hxy
  have hwzVA : w⁻¹ * z ∈ d.V ⊔ d.A₂ := by
    rw [← hd.E_inf_B₄ hGMS]; exact ⟨d.E.mul_mem (d.E.inv_mem hwE) hzE, hwz⟩
  obtain ⟨v₁, hv₁, a₁, ha₁, hva₁⟩ := hd.exists_mul_of_mem_VA hwzVA
  let Z2S : Subgroup G := (Subgroup.upperCentralSeries ↥S 2).map S.subtype
  have hVW : d.V ≤ d.W := le_sup_left
  have ha₁Z : a₁ ∈ Z2S := by
    have e : a₁ = v₁⁻¹ * (w⁻¹ * z) := by rw [hva₁]; group
    rw [e]
    exact Z2S.mul_mem (Z2S.inv_mem (hWZ (hVW hv₁))) (Z2S.mul_mem (Z2S.inv_mem (hWZ hwW)) hz)
  obtain ⟨-, ha₁c⟩ := mem_map_upperCentralSeries_two.1 ha₁Z
  rw [hcS] at ha₁c
  have ha₁P : a₁ ∈ d.P := d.A₂_le_P ha₁
  have ha₁Z₂ : a₁ ∈ d.Z₂p := (d.mem_Z₂p_iff ha₁P).2 fun q hq => by
    rw [← hd.V_inf_P]
    refine ⟨ha₁c q (hP hq), ?_⟩
    rw [commutatorElement_def]
    exact d.P.mul_mem (d.P.mul_mem (d.P.mul_mem ha₁P hq) (d.P.inv_mem ha₁P)) (d.P.inv_mem hq)
  have hz' : z = w * (v₁ * a₁) := by rw [← hva₁]; group
  rw [hz']
  exact d.W.mul_mem hwW (d.W.mul_mem (hVW hv₁) (hd.Z₂p_le_W hGMS ha₁Z₂))

theorem sec39c_D (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b) :
    d.D = S ⊓ centralizer (d.W : Set G) := by
  have hd := hp.hyp
  have hWF : d.W ≤ d.F := (hd.sec3_5_one hp.gms).2.2.2.2.2.1
  refine le_antisymm (le_inf (sec39c_D_le_S ha) fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun w hw => sec39c_D_comm_W hb hWF hx hw) ?_
  intro y hy
  have hDE : d.D ≤ normalizer (d.E : Set G) :=
    (sec39c_D_le_S ha).trans (hS.le.trans d.L₂_le_normalizer_E)
  have hy' : y ∈ ((d.E ⊔ d.D : Subgroup G) : Set G) := by rw [← ha.S_eq]; exact hy.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDE] at hy'
  obtain ⟨e, he, δ, hδ, hyeδ⟩ := hy'
  have hecw : ∀ w ∈ d.W, w * e = e * w := fun w hw => by
    have hyc : w * y = y * w := Subgroup.mem_centralizer_iff.1 hy.2 w hw
    rw [← hyeδ] at hyc
    have hδc : w * δ = δ * w := sec39c_D_comm_W hb hWF hδ hw
    calc w * e = w * (e * δ) * δ⁻¹ := by group
      _ = e * δ * w * δ⁻¹ := by rw [hyc]
      _ = e * (δ * w) * δ⁻¹ := by group
      _ = e * (w * δ) * δ⁻¹ := by rw [hδc]
      _ = e * w := by group
  rw [← hyeδ]
  exact d.D.mul_mem (sec39c_CE_le_D hp S hS hP ha hb he hecw) hδ

theorem sec39c_of_hyp (hp : d.CaseHyp) (k8 : d.Know8) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (ha : d.Sec39a S) (hb : d.Sec39b)
    (hY₂ : d.Sec39cY₂) : d.Sec39c S :=
  ⟨sec39c_center hp k8 S hS hP ha hY₂, sec39c_Z₂ hp k8 S hS hP ha hb hY₂,
    sec39c_D hp k8 S hS hP ha hb⟩

end Data

namespace CaseBParts

theorem sec39c : Sec39cStatement :=
  fun _ _ _ _ _ _ _ _ hp k8 S hS hP ha hb =>
    Data.sec39c_of_hyp hp k8 S hS hP ha hb (fun hm hmc => Data.sec39c_Y₂_mem_odd hp k8 hm hmc)

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
