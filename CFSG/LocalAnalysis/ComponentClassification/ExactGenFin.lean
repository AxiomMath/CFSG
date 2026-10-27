module

public import CFSG.Certificates.NativeSchreierArrays
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  Subgroup

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]



@[instance_reducible] def conjAction (P : Subgroup Γ) : MulAction P Γ :=
  MulAction.compHom Γ ((ConjAct.toConjAct : Γ ≃* ConjAct Γ).toMonoidHom.comp P.subtype)

theorem conjAction_smul (P : Subgroup Γ) (g : P) (x : Γ) :
    (conjAction P).smul g x = (g : Γ) * x * (g : Γ)⁻¹ := by
  show ConjAct.toConjAct (g : Γ) • x = _
  rw [ConjAct.smul_def]
  simp

theorem card_le_of_distinct_conjugates {P : Subgroup Γ} [Finite P] (ν : Γ) (L : List Γ)
    (hL : L.Nodup) (hconj : ∀ y ∈ L, ∃ g ∈ P, g * ν * g⁻¹ = y) :
    L.length * Nat.card ((centralizer ({ν} : Set Γ)).subgroupOf P) ≤ Nat.card P := by
  classical
  letI := conjAction P
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer P ν)
  rw [MulAction.index_stabilizer] at h1
  have hstab : MulAction.stabilizer P ν = (centralizer ({ν} : Set Γ)).subgroupOf P := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    change (conjAction P).smul g ν = ν ↔ _
    rw [conjAction_smul, mul_inv_eq_iff_eq_mul]
  rw [hstab] at h1
  have hLsub : (L.toFinset : Set Γ) ⊆ MulAction.orbit P ν := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hconj y (List.mem_toFinset.1 hy)
    exact ⟨⟨g, hg⟩, conjAction_smul P ⟨g, hg⟩ ν⟩
  have hcard : L.length ≤ Nat.card (MulAction.orbit P ν) := by
    rw [← List.toFinset_card_of_nodup hL]
    calc L.toFinset.card = (L.toFinset : Set Γ).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit P ν).ncard := Set.ncard_le_ncard hLsub (Set.finite_range _)
      _ = Nat.card (MulAction.orbit P ν) := (Nat.card_coe_set_eq _).symm
  calc L.length * Nat.card ((centralizer ({ν} : Set Γ)).subgroupOf P)
      ≤ Nat.card (MulAction.orbit P ν) * Nat.card ((centralizer ({ν} : Set Γ)).subgroupOf P) :=
        Nat.mul_le_mul_right _ hcard
    _ = Nat.card P := by rw [mul_comm]; exact h1

theorem mem_closure_of_commutes {P : Subgroup Γ} [Finite P] (ν : Γ) (L : List Γ)
    (hL : L.Nodup) (hconj : ∀ y ∈ L, ∃ g ∈ P, g * ν * g⁻¹ = y) (cg : Set Γ) (hcgP : cg ⊆ P)
    (hcg : ∀ c ∈ cg, ν * c = c * ν) (hcard : Nat.card P ≤ L.length * Nat.card (closure cg)) :
    ∀ g ∈ P, ν * g = g * ν → g ∈ closure cg := by
  have hCP : closure cg ≤ P := (closure_le _).2 hcgP
  have hcomm : ∀ x ∈ closure cg, ν * x = x * ν := by
    intro x hx
    have : closure cg ≤ centralizer ({ν} : Set Γ) := by
      refine (closure_le _).2 fun c hc => ?_
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hcg c hc).symm
    have := this hx
    rw [mem_centralizer_singleton_iff] at this
    exact this.symm
  have h1 := card_le_of_distinct_conjugates (P := P) ν L hL hconj
  set C' := (closure cg).subgroupOf P with hC'
  set Cs := (centralizer ({ν} : Set Γ)).subgroupOf P with hCs
  have hle : C' ≤ Cs := by
    intro x hx
    rw [hC', Subgroup.mem_subgroupOf] at hx
    rw [hCs, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    exact (hcomm _ hx).symm
  have hcardC' : Nat.card C' = Nat.card (closure cg) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hLpos : 0 < L.length := by
    by_contra h0
    have : L.length = 0 := by omega
    rw [this, zero_mul] at hcard
    omega
  have hCsle : Nat.card Cs ≤ Nat.card C' := by
    rw [hcardC']
    have : L.length * Nat.card Cs ≤ L.length * Nat.card (closure cg) := h1.trans hcard
    exact Nat.le_of_mul_le_mul_left this hLpos
  have heq : C' = Cs := Subgroup.eq_of_le_of_card_ge hle hCsle
  intro g hg hgc
  have : (⟨g, hg⟩ : P) ∈ Cs := by
    rw [hCs, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    exact hgc.symm
  rw [← heq, hC', Subgroup.mem_subgroupOf] at this
  exact this

theorem inv_conj_mem_of_conj_mem [Finite Γ] {X : Subgroup Γ} {g : Γ}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
  let f : X → X := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have : g * (a : Γ) * g⁻¹ = g * (b : Γ) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  intro x hx
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨x, hx⟩
  have : g * (y : Γ) * g⁻¹ = x := congrArg Subtype.val hy
  have : g⁻¹ * x * g = y := by rw [← this]; group
  rw [this]; exact y.2

theorem commutator_le_of_gen [Finite Γ] {C X : Subgroup Γ} {cg : Set Γ} (hC : C = closure cg)
    (hXC : X ≤ C) (hnorm : ∀ c ∈ cg, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hcomm : ∀ c ∈ cg, ∀ c' ∈ cg, ⁅c, c'⁆ ∈ X) : ⁅C, C⁆ ≤ X := by
  subst hC
  have hnormC : ∀ g ∈ closure cg, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem c hc => exact hnorm c hc
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb =>
      intro x hx
      have := ha _ (hb x hx)
      simpa [mul_assoc] using this
    | inv a _ ha => intro x hx; simpa using inv_conj_mem_of_conj_mem ha x hx
  have hA : ∀ c ∈ cg, ∀ g' ∈ closure cg, ⁅c, g'⁆ ∈ X := by
    intro c hc g' hg'
    induction hg' using Subgroup.closure_induction with
    | mem c' hc' => exact hcomm c hc c' hc'
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact X.mul_mem iha (hnormC a ha _ ihb)
    | inv a ha iha =>
      have e : ⁅c, a⁻¹⁆ = a⁻¹ * ⁅c, a⁆⁻¹ * a := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := hnormC a⁻¹ (inv_mem ha) _ (X.inv_mem iha)
      simpa [mul_assoc] using this
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  induction hg using Subgroup.closure_induction with
  | mem c hc => exact hA c hc g' hg'
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : ⁅a * b, g'⁆ = a * ⁅b, g'⁆ * a⁻¹ * ⁅a, g'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem (hnormC a ha _ ihb) iha
  | inv a ha iha =>
    have e : ⁅a⁻¹, g'⁆ = a⁻¹ * ⁅a, g'⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hnormC a⁻¹ (inv_mem ha) _ (X.inv_mem iha)
    simpa [mul_assoc] using this

theorem cover_of_sylow [Finite Γ] {N T K : Subgroup Γ} (hNK : N ≤ K) (hTN : T ≤ N)
    (hT : Nat.card T = 2 ^ (Nat.card N).factorization 2) (R : Set Γ)
    (hcov : ∀ t ∈ T, t * t = 1 → t = 1 ∨ ∃ μ ∈ K, ∃ ρ ∈ R, μ * t * μ⁻¹ = ρ) :
    ∀ x ∈ N, x * x = 1 → x = 1 ∨ ∃ μ ∈ K, ∃ ρ ∈ R, μ * x * μ⁻¹ = ρ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx2
  let T' : Subgroup N := T.subgroupOf N
  have hT' : Nat.card T' = 2 ^ (Nat.card N).factorization 2 := by
    rw [← hT]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  let S₀ : Sylow 2 N := Sylow.ofCard T' hT'
  let x' : N := ⟨x, hx⟩
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hP : IsPGroup 2 (zpowers x') := by
    intro g
    obtain ⟨m, hm⟩ := g.2
    refine ⟨1, ?_⟩
    have hsq : x' ^ 2 = 1 := by rw [pow_two, hx'2]
    have : (g : N) ^ (2 ^ 1) = 1 := by
      rw [← hm]
      show (x' ^ m) ^ (2 ^ 1) = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
    exact Subtype.ext this
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q S₀
  have hmem : g * x' * g⁻¹ ∈ (S₀ : Subgroup N) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have h1 : x' ∈ (Q : Subgroup N) := hQ (mem_zpowers x')
    have := Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Q : Subgroup N) h1
    simpa [MulAut.smul_def] using this
  have hmemT : ((g : Γ) * x * (g : Γ)⁻¹) ∈ T := by
    have : (g * x' * g⁻¹ : N) ∈ T' := hmem
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hsq : ((g : Γ) * x * (g : Γ)⁻¹) * ((g : Γ) * x * (g : Γ)⁻¹) = 1 := by
    calc ((g : Γ) * x * (g : Γ)⁻¹) * ((g : Γ) * x * (g : Γ)⁻¹)
        = (g : Γ) * (x * x) * (g : Γ)⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rcases hcov _ hmemT hsq with h1 | ⟨μ', hμ', ρ, hρ, hconj⟩
  · left
    have : (g : Γ) * x * (g : Γ)⁻¹ = (g : Γ) * 1 * (g : Γ)⁻¹ := by rw [h1]; group
    simpa using this
  · right
    refine ⟨μ' * g, K.mul_mem hμ' (hNK g.2), ρ, hρ, ?_⟩
    rw [← hconj]; group




structure ChainData where
  S : Array (Array ℕ)
  k : ℕ
  base : List ℕ
  W : Array (List ℤ)
  chunks : ℕ
  deriving Inhabited

namespace ChainData

variable (n : ℕ) (cd : ChainData)

@[expose] noncomputable def gs (h : ℕ) : Equiv.Perm (Fin n) := permOfArr n cd.S[h]!

@[expose] noncomputable def sub : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ i < cd.k, g = permOfArr n cd.S[i]!}

@[expose] def order : ℕ :=
  ((rawLevels n cd.S cd.base.toArray).toList.map fun L => L.pts.size).prod

@[expose] def baseFin : List (Fin n) :=
  cd.base.filterMap fun b => if h : b < n then some ⟨b, h⟩ else none

@[expose] def check : Bool :=
  decide (1 ≤ n) && decide (cd.k ≤ cd.S.size) && decide cd.base.Nodup &&
    cd.base.all (fun b => decide (b < n)) && decide (0 < cd.chunks) &&
    rawChainOK n (cd.S.extract 0 cd.k) cd.S cd.base.toArray cd.W cd.chunks

theorem map_val_filterMap (l : List ℕ) (hlt : ∀ b ∈ l, b < n) :
    (l.filterMap fun b => if h : b < n then some (⟨b, h⟩ : Fin n) else none).map Fin.val = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb : b < n := hlt b List.mem_cons_self
    have ih' := ih (fun x hx => hlt x (List.mem_cons_of_mem b hx))
    simp only [List.filterMap_cons, dif_pos hb, List.map_cons, ih']

theorem map_val_baseFin (hlt : ∀ b ∈ cd.base, b < n) : (cd.baseFin n).map Fin.val = cd.base :=
  map_val_filterMap n cd.base hlt

theorem check_sound (h : cd.check n = true) :
    (∀ j < cd.S.size, Rep n cd.S[j]! (cd.gs n j) ∧
      Rep n (rawInvs n cd.S)[j]! (cd.gs n j)⁻¹) ∧
    (∀ j < cd.S.size, cd.gs n j ∈ cd.sub n) ∧ Nat.card (cd.sub n) = cd.order n := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hn, hk⟩, hnodup⟩, hlt⟩, hchunks⟩, hchain⟩ := h
  have hlt' : ∀ b ∈ cd.base, b < n := fun b hb => by simpa using hlt b hb
  have hF := chainCheckFacts hchain
  have hinv := hF.strong_inv
  have hb : (cd.baseFin n).Nodup := by
    have := map_val_baseFin n cd hlt'
    exact List.Nodup.of_map _ (this ▸ hnodup)
  let Q := RawSchreierDatum.ofArrays n hn cd.S cd.k hk (cd.baseFin n) hb cd.W
  have hA := chainArrays_ofArrays (hn := hn) (S := cd.S) (k := cd.k) (hk := hk)
    (base := cd.baseFin n) (hb := hb) (W := cd.W) hinv
  rw [map_val_baseFin n cd hlt'] at hA
  obtain ⟨hQ, horb⟩ := validSchreier_of_chainOK hA hchunks hchain
  have horig : Q.originalSubgroup = cd.sub n := by
    unfold RawSchreierDatum.originalSubgroup sub
    congr 1
    ext g
    constructor
    · intro hg
      have hg' : g ∈ Q.original.toList := hg
      change g ∈ (Vector.ofFn fun i : Fin cd.k => permOfArr n cd.S[(i : ℕ)]!).toList at hg'
      rw [Vector.toList_ofFn, List.mem_ofFn] at hg'
      obtain ⟨i, rfl⟩ := hg'
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      show _ ∈ (Vector.ofFn fun i : Fin cd.k => permOfArr n cd.S[(i : ℕ)]!).toList
      rw [Vector.toList_ofFn, List.mem_ofFn]
      exact ⟨⟨i, hi⟩, rfl⟩
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
  · exact rep_permOfArr (hinv j hj)
  · have := RawSchreierDatum.strong_get_mem_originalSubgroup Q hQ ⟨j, hj⟩
    rw [RawSchreierDatum.ofArrays_strong_get] at this
    rw [← horig]
    exact this
  · rw [← horig, ← RawSchreierDatum.orderCertificate_eq_card Q hQ]
    unfold RawSchreierDatum.orderCertificate order
    congr 1
    have hbl : (cd.baseFin n).length = cd.base.length := by
      have := congrArg List.length (map_val_baseFin n cd hlt')
      simpa using this
    apply List.ext_getElem
    · simp [Q, RawSchreierDatum.ofArrays, rawLevels, hbl]
    · intro k h1 h2
      have hk' : k < (rawLevels n cd.S cd.base.toArray).size := by simpa using h2
      simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
      rw [horb]
      simp only [Fin.val_cast, Fin.val_mk]
      rw [getElem!_pos (rawLevels n cd.S cd.base.toArray) k hk']

@[expose] noncomputable def val (w : List ℤ) : Equiv.Perm (Fin n) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin cd.S.size => cd.gs n h) (toLetters cd.S.size w)

@[expose] def wordArr (w : List ℤ) : Array ℕ := wordA n cd.S (rawInvs n cd.S) w

theorem rep_wordArr (h : cd.check n = true) {w : List ℤ} (hw : lettersOK cd.S.size w = true) :
    Rep n (cd.wordArr n w) (cd.val n w) := by
  obtain ⟨hrep, -, -⟩ := cd.check_sound n h
  exact rep_wordA (S := cd.S) (Sinv := rawInvs n cd.S) (gs := fun h => cd.gs n h)
    (j := cd.S.size) (fun h hh => (hrep h hh).1) (fun h hh => (hrep h hh).2) w hw

theorem val_mem (h : cd.check n = true) (w : List ℤ) {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : ∀ j < cd.S.size, cd.gs n j ∈ H) : cd.val n w ∈ H := by
  unfold val
  have := Quiver.SchreierGraph.evalWord_mem_closure (fun h : Fin cd.S.size => cd.gs n h)
    (toLetters cd.S.size w)
  refine (Subgroup.closure_le H).2 ?_ this
  rintro _ ⟨a, rfl⟩
  exact hH a a.2

theorem val_mem_sub (h : cd.check n = true) (w : List ℤ) : cd.val n w ∈ cd.sub n :=
  cd.val_mem n h w (cd.check_sound n h).2.1

end ChainData


@[expose] def hashN (n : ℕ) (t : Array ℕ) : ℕ :=
  (List.range n).foldl (fun h i => (h * 1000003 + t[i]!) % 2305843009213693951) 7

@[expose] noncomputable def hashP (n : ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  (List.range n).foldl (fun h i => (h * 1000003 + (if hi : i < n then (g ⟨i, hi⟩ : ℕ) else 0)) %
    2305843009213693951) 7

theorem hashN_eq_hashP {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    hashN n t = hashP n g := by
  unfold hashN hashP
  refine List.foldl_ext _ _ _ fun acc i hi => ?_
  have hi' : i < n := List.mem_range.1 hi
  rw [dif_pos hi', h ⟨i, hi'⟩]

@[expose] def strictInc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && strictInc (b :: l)

theorem strictInc_pairwise : ∀ l : List ℕ, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => by simp
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih0 := strictInc_pairwise (b :: l) h.2
    have ih1 := List.pairwise_cons.1 ih0
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih0⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (ih1.1 x hx)


theorem elems_cover (cd : ChainData) (n : ℕ) (h : cd.check n = true) (ws : List (List ℤ))
    (hl : ws.all (lettersOK cd.S.size) = true)
    (hs : strictInc (ws.map fun w => hashN n (cd.wordArr n w)) = true)
    (hlen : ws.length = cd.order n) : ∀ t ∈ cd.sub n, ∃ w ∈ ws, cd.val n w = t := by
  classical
  have hl' : ∀ w ∈ ws, lettersOK cd.S.size w = true := fun w hw => by
    simpa using (List.all_eq_true.1 hl) w hw
  have hmap : ws.map (fun w => hashN n (cd.wordArr n w)) =
      (ws.map (cd.val n)).map (hashP n) := by
    rw [List.map_map]
    refine List.map_congr_left fun w hw => ?_
    exact hashN_eq_hashP (cd.rep_wordArr n h (hl' w hw))
  have hnd : (ws.map (cd.val n)).Nodup := by
    have hp := strictInc_pairwise _ hs
    rw [hmap] at hp
    exact List.Nodup.of_map _ (List.Pairwise.imp (fun hab => ne_of_lt hab) hp)
  have hcard : Nat.card (cd.sub n) = (ws.map (cd.val n)).length := by
    rw [List.length_map, hlen, (cd.check_sound n h).2.2]
  intro t ht
  by_contra hcon
  have htA : t ∉ (ws.map (cd.val n)).toFinset := by
    intro hm
    obtain ⟨w, hw, hwt⟩ := List.mem_map.1 (List.mem_toFinset.1 hm)
    exact hcon ⟨w, hw, hwt⟩
  have h1 : ((insert t (ws.map (cd.val n)).toFinset : Finset _) : Set (Equiv.Perm (Fin n))) ⊆
      (cd.sub n : Set _) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ht
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact cd.val_mem_sub n h w
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem htA,
    List.toFinset_card_of_nodup hnd] at h2
  have h3 : (cd.sub n : Set (Equiv.Perm (Fin n))).ncard = Nat.card (cd.sub n) := by
    rw [← Nat.card_coe_set_eq]; rfl
  omega



@[expose] def conjArr (n : ℕ) (g gi y : Array ℕ) : Array ℕ := compA n (compA n g y) gi

theorem rep_conjArr {n : ℕ} {g gi y : Array ℕ} {G Gi Y : Equiv.Perm (Fin n)} (hg : Rep n g G)
    (hgi : Rep n gi Gi) (hy : Rep n y Y) : Rep n (conjArr n g gi y) (G * Y * Gi) :=
  rep_compA (rep_compA hg hy) hgi

@[expose] def invPair (n : ℕ) (g gi : Array ℕ) : Bool := eqA n (compA n g gi) (idA n)

theorem rep_inv_of_invPair {n : ℕ} {g gi : Array ℕ} {G Gi : Equiv.Perm (Fin n)} (hg : Rep n g G)
    (hgi : Rep n gi Gi) (h : invPair n g gi = true) : Gi = G⁻¹ := by
  have := (eqA_iff (rep_compA hg hgi) (rep_idA (n := n))).1 h
  exact (eq_inv_of_mul_eq_one_right this)

open Subgroup in
theorem normalizes_of_gens {Γ : Type*} [Group Γ] [Finite Γ] {P N : Subgroup Γ} {ng pg : Set Γ}
    (hN : N = closure ng) (hP : P = closure pg) (h : ∀ g ∈ ng, ∀ p ∈ pg, g * p * g⁻¹ ∈ P) :
    ∀ μ ∈ N, ∀ x, x ∈ P ↔ μ * x * μ⁻¹ ∈ P := by
  have h1 : ∀ g ∈ ng, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    rw [hP] at hx
    induction hx using Subgroup.closure_induction with
    | mem p hp => rw [hP]; rw [hP] at h; exact h g hg p hp
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]; exact P.mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]; exact P.inv_mem ha
  have h2 : ∀ μ ∈ N, ∀ x ∈ P, μ * x * μ⁻¹ ∈ P := by
    intro μ hμ
    rw [hN] at hμ
    induction hμ using Subgroup.closure_induction with
    | mem g hg => exact h1 g hg
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb =>
      intro x hx
      have := ha _ (hb x hx)
      simpa [mul_assoc] using this
    | inv a _ ha =>
      intro x hx
      have := inv_conj_mem_of_conj_mem (X := P) ha x hx
      simpa using this
  intro μ hμ x
  constructor
  · exact h2 μ hμ x
  · intro hx
    have hμi : μ⁻¹ ∈ N := N.inv_mem hμ
    have := h2 μ⁻¹ hμi _ hx
    simpa [mul_assoc] using this


end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
