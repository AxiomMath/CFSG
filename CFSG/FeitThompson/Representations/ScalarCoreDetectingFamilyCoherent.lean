module

import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Local.MetacyclicCoprimeActionAbelian
import CFSG.FeitThompson.Representations.CoordinateKernelPermutationCharacterNorm
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentAssembly
import CFSG.FeitThompson.Representations.FieldActionDetectingFamilyCoherence
import CFSG.FeitThompson.Representations.AbelianNormalLayerDegreeBound
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
public import Mathlib.GroupTheory.Frattini
public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentInflation
import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentModel
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentScalar
public import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentAxis
import CFSG.FeitThompson.Representations.AbelianByAbelianFrobeniusCharacters
import CFSG.FeitThompson.Representations.AbelianQuotientExtensionInducedFamily
import CFSG.FeitThompson.Representations.FixedFreeQuotientUniformCoreDegrees
import CFSG.FeitThompson.Local.SplitKernelSubgroupInheritsComplement
import CFSG.FeitThompson.Representations.ScalarCoreDetectingFamilyCoherentQuotient
import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription
import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
public import CFSG.FeitThompson.Representations.TwoDegreesRemainingIrreducibleCount
import CFSG.FeitThompson.OddOrder.QuotientFrobeniusAction
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarCoreCoherence

open scoped ComplexOrder

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {L : Type*} [Group L]

def virtualCharsOn (A : Set L) : Submodule ℤ (L → ℂ) where
  carrier := {f | f ∈ virtualChars L ∧ ∀ x ∉ A, f x = 0}
  add_mem' {f g} hf hg := ⟨Submodule.add_mem _ hf.1 hg.1, fun x hx => by
    simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  smul_mem' c {f} hf := ⟨Submodule.smul_mem _ c hf.1, fun x hx => by simp [hf.2 x hx]⟩

theorem mem_virtualCharsOn {A : Set L} {f : L → ℂ} :
    f ∈ virtualCharsOn A ↔ f ∈ virtualChars L ∧ ∀ x ∉ A, f x = 0 := Iff.rfl

theorem virtualCharsOn_le (A : Set L) : virtualCharsOn A ≤ virtualChars L := fun _ hf => hf.1

theorem eq_zero_of_mem_virtualCharsOn {A : Set L} {f : L → ℂ} (hf : f ∈ virtualCharsOn A)
    {x : L} (hx : x ∉ A) : f x = 0 := hf.2 x hx

def virtualCharsOnOne (A : Set L) : Submodule ℤ (L → ℂ) where
  carrier := {f | f ∈ virtualChars L ∧ ∀ x ∉ A, x ≠ 1 → f x = 0}
  add_mem' {f g} hf hg := ⟨Submodule.add_mem _ hf.1 hg.1, fun x hx hx1 => by
    simp [hf.2 x hx hx1, hg.2 x hx hx1]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' c {f} hf := ⟨Submodule.smul_mem _ c hf.1, fun x hx hx1 => by simp [hf.2 x hx hx1]⟩

theorem mem_virtualCharsOnOne {A : Set L} {f : L → ℂ} :
    f ∈ virtualCharsOnOne A ↔ f ∈ virtualChars L ∧ ∀ x ∉ A, x ≠ 1 → f x = 0 := Iff.rfl

theorem virtualCharsOn_le_virtualCharsOnOne (A : Set L) :
    virtualCharsOn A ≤ virtualCharsOnOne A := fun _ hf => ⟨hf.1, fun x hx _ => hf.2 x hx⟩

theorem mem_virtualCharsOn_of_mem_virtualCharsOnOne {A : Set L} {f : L → ℂ}
    (hf : f ∈ virtualCharsOnOne A) (h1 : f 1 = 0) : f ∈ virtualCharsOn A :=
  ⟨hf.1, fun x hx => by
    by_cases hx1 : x = 1
    · rw [hx1]; exact h1
    · exact hf.2 x hx hx1⟩

section LineAut

variable {H H0 U : Subgroup L} [H.Normal] [H0.Normal]
  {Ei : Subgroup (↥H ⧸ H0.subgroupOf H)}

noncomputable def lineAut (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    (Ei : Subgroup (↥H ⧸ H0.subgroupOf H))
    (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei) : ↥U →* MulAut ↥Ei where
  toFun u := (MulEquiv.subgroupMap (conjQuotientAut H H0 (u : L)) Ei).trans
    (MulEquiv.subgroupCongr (hinv u u.2))
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp [MulEquiv.subgroupCongr_apply]
  map_mul' u v := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp [MulEquiv.subgroupCongr_apply, MulAut.mul_apply]

@[simp] theorem coe_lineAut_apply_apply
    (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei) (u : ↥U) (x : ↥Ei) :
    ((lineAut H H0 U Ei hinv u x : ↥Ei) : ↥H ⧸ H0.subgroupOf H)
      = conjQuotientAut H H0 (u : L) (x : ↥H ⧸ H0.subgroupOf H) := (rfl)

theorem ker_lineAut (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei) :
    (lineAut H H0 U Ei hinv).ker = (lineFixer H H0 U Ei).subgroupOf U := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_lineFixer]
  refine ⟨fun h => ⟨u.2, fun v hv => ?_⟩, fun h => MulEquiv.ext fun x => Subtype.ext ?_⟩
  · have := congrArg (fun σ => (σ (⟨v, hv⟩ : ↥Ei) : ↥H ⧸ H0.subgroupOf H)) h
    simpa using this
  · simpa using h.2 (x : ↥H ⧸ H0.subgroupOf H) x.2

theorem commutator_le_ker_of_isMulCommutative {G M : Type*} [Group G] [Group M]
    [IsMulCommutative M] (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def]
  simp [IsMulCommutative.is_comm.comm (f a) (f b)]

theorem commutator_le_lineFixer {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ei = p)
    (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei) :
    ⁅U, U⁆ ≤ lineFixer H H0 U Ei := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite ↥Ei := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  have : IsCyclic ↥Ei := isCyclic_of_prime_card (p := p) hcard
  have _habel : IsMulCommutative (MulAut ↥Ei) :=
    ⟨⟨fun _ _ => (IsCyclic.mulAutMulEquiv ↥Ei).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hker : commutator ↥U ≤ (lineFixer H H0 U Ei).subgroupOf U :=
    ker_lineAut hinv ▸ commutator_le_ker_of_isMulCommutative (lineAut H H0 U Ei hinv)
  rw [← Subgroup.map_subtype_commutator U]
  rintro x ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hker hy)

theorem mem_lineFixer_of_forall_apply_eq {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ei = p)
    (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei)
    {lam : (↥H ⧸ H0.subgroupOf H) →* ℂˣ} (hne : ∃ v ∈ Ei, lam v ≠ 1)
    {u : L} (huU : u ∈ U) (hfix : ∀ v ∈ Ei, lam (conjQuotientAut H H0 u v) = lam v) :
    u ∈ lineFixer H H0 U Ei := by
  have : Fact p.Prime := ⟨hp⟩
  have _hfin : Finite ↥Ei := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  set μ : ↥Ei →* ℂˣ := lam.comp Ei.subtype with hμ
  have hμapply : ∀ x : ↥Ei, μ x = lam (x : ↥H ⧸ H0.subgroupOf H) := fun _ => rfl
  have hμne : ∃ x : ↥Ei, μ x ≠ 1 := by
    obtain ⟨v, hv, hvne⟩ := hne
    exact ⟨⟨v, hv⟩, by rw [hμapply]; exact hvne⟩
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hxne
    obtain ⟨y, hyne⟩ := hμne
    refine hyne ?_
    have htop : Subgroup.zpowers x = ⊤ := by
      have hdvd : Nat.card (Subgroup.zpowers x) ∣ p := hcard ▸ Subgroup.card_subgroup_dvd_card _
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.1 h1 ▸ Subgroup.mem_zpowers x) (by simpa using hxne)
      · exact Subgroup.eq_top_of_le_card _ (by rw [hcard, h1])
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top y)
    simp [map_zpow, hx]
  refine mem_lineFixer.2 ⟨huU, fun v hv => ?_⟩
  have hmem : conjQuotientAut H H0 u v ∈ Ei := by
    rw [← hinv u huU]
    exact ⟨v, hv, rfl⟩
  exact congrArg Subtype.val (hinj (a₁ := (⟨conjQuotientAut H H0 u v, hmem⟩ : ↥Ei))
    (a₂ := (⟨v, hv⟩ : ↥Ei)) (by rw [hμapply, hμapply]; exact hfix v hv))

theorem relIndex_lineFixer_dvd_sub_one {p : ℕ} (hp : p.Prime) (hcard : Nat.card Ei = p)
    (hinv : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) Ei = Ei) :
    (lineFixer H H0 U Ei).relIndex U ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite ↥Ei := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  have : IsCyclic ↥Ei := isCyclic_of_prime_card (p := p) hcard
  have hker : (lineFixer H H0 U Ei).relIndex U = ((lineAut H H0 U Ei hinv).ker).index := by
    rw [Subgroup.relIndex, ker_lineAut]
  have h1 : Nat.card (MulAut ↥Ei) = p - 1 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime hp]
  rw [hker, Subgroup.index_ker]
  exact h1 ▸ Subgroup.card_subgroup_dvd_card _

section Conjugation

open Pointwise ScalarComplementPermutationNorm

theorem lineFixer_eq_inf_autFixer (H H0 U : Subgroup L) [H.Normal] [H0.Normal]
    (Ei : Subgroup (↥H ⧸ H0.subgroupOf H)) :
    lineFixer H H0 U Ei
      = U ⊓ autFixer (conjQuotientAut H H0) (Ei : Set (↥H ⧸ H0.subgroupOf H)) := by
  ext x; rw [mem_lineFixer, Subgroup.mem_inf, mem_autFixer]; rfl

theorem conj_smul_autFixer {V : Type*} [Group V] (ρ : L →* MulAut V) (S : Set V) (g : L) :
    MulAut.conj g • autFixer ρ S = autFixer ρ (ρ g '' S) := by
  have key : ∀ (x : L) (v : V), ρ (g⁻¹ * x * g) v = v ↔ ρ x (ρ g v) = ρ g v := fun x v => by
    rw [map_mul, map_mul, map_inv]
    change (ρ g).symm ((ρ x) ((ρ g) v)) = v ↔ _
    rw [MulEquiv.symm_apply_eq]
  ext x
  rw [mem_conj_smul_iff, mem_autFixer, mem_autFixer]
  exact ⟨fun h w hw => by obtain ⟨v, hv, rfl⟩ := hw; exact (key x v).1 (h v hv),
    fun h v hv => (key x v).2 (h (ρ g v) ⟨v, hv, rfl⟩)⟩

theorem conj_smul_lineFixer {Ej : Subgroup (↥H ⧸ H0.subgroupOf H)} {g : L}
    (hU : MulAut.conj g • U = U) (hE : Subgroup.map (conjQuotientAut H H0 g) Ei = Ej) :
    MulAut.conj g • lineFixer H H0 U Ei = lineFixer H H0 U Ej := by
  rw [lineFixer_eq_inf_autFixer, lineFixer_eq_inf_autFixer, Subgroup.smul_inf, hU,
    conj_smul_autFixer]
  congr 2
  rw [← hE, Subgroup.coe_map]
  rfl

theorem relIndex_lineFixer_eq_of_conj {Ej : Subgroup (↥H ⧸ H0.subgroupOf H)} {g : L}
    (hU : MulAut.conj g • U = U) (hE : Subgroup.map (conjQuotientAut H H0 g) Ei = Ej) :
    (lineFixer H H0 U Ei).relIndex U = (lineFixer H H0 U Ej).relIndex U := by
  have h := Subgroup.relIndex_pointwise_smul (MulAut.conj g) (lineFixer H H0 U Ei) U
  rw [conj_smul_lineFixer hU hE, hU] at h
  exact h.symm

theorem map_coe_mulAut_mul {Q : Type*} [Group Q] (σ τ : MulAut Q) (S : Subgroup Q) :
    Subgroup.map ((σ * τ : MulAut Q) : Q →* Q) S
      = Subgroup.map ((σ : Q →* Q)) (Subgroup.map ((τ : Q →* Q)) S) := by
  rw [Subgroup.map_map]
  exact congrFun (congrArg Subgroup.map (MonoidHom.ext fun _ => rfl)) S

theorem map_coe_mulAut_one {Q : Type*} [Group Q] (S : Subgroup Q) :
    Subgroup.map ((1 : MulAut Q) : Q →* Q) S = S := by
  ext x
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem map_conjQuotientAut_pow_Eline {q : ℕ}
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {b : L}
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) (n : ℕ)
    (i : ZMod q) :
    Subgroup.map (conjQuotientAut H H0 (b ^ n)) (Eline i) = Eline (i + n) := by
  induction n with
  | zero => rw [pow_zero, map_one, map_coe_mulAut_one]; simp
  | succ k ih =>
    rw [pow_succ', map_mul, map_coe_mulAut_mul, ih, hb]
    push_cast
    ring_nf

end Conjugation

end LineAut

section ElemAbelian

variable {G : Type*} [Group G] {p : ℕ} {ι : Type*} [Fintype ι]

theorem prod_card_le_card_of_iSupIndep [Finite G] [IsMulCommutative G] {E : ι → Subgroup G}
    (hind : iSupIndep E) : ∏ i, Nat.card (E i) ≤ Nat.card G := by
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ E i → y ∈ E j → Commute x y :=
    fun _ _ _ x y _ _ => IsMulCommutative.is_comm.comm x y
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  calc ∏ i, Nat.card (E i) = Nat.card (∀ i, ↥(E i)) := (Nat.card_pi).symm
    _ ≤ Nat.card G := Nat.card_le_card_of_injective _ hinj

theorem frattini_eq_bot_of_iSupIndep [Finite G] (hp : p.Prime) {E : ι → Subgroup G}
    (hcard : Nat.card G = p ^ Fintype.card ι) (hind : iSupIndep E) (hsup : ⨆ i, E i = ⊤)
    (hE : ∀ i, Nat.card (E i) = p) : frattini G = ⊥ := by
  classical
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_mulEquiv_quotient_frattini hp hcard
  set Φ := frattini G with hΦ
  set f := QuotientGroup.mk' Φ with hf
  have habel : IsMulCommutative (G ⧸ Φ) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hkey : ∀ j : ι, ¬ (E j ≤ (⨆ i, ⨆ (_ : i ≠ j), E i) ⊔ Φ) := by
    intro j hle
    have hNtop : (⨆ i, ⨆ (_ : i ≠ j), E i) ⊔ Φ = ⊤ := by
      refine top_le_iff.1 ?_
      rw [← hsup]
      refine iSup_le fun i => ?_
      by_cases hij : i = j
      · exact hij ▸ hle
      · exact le_sup_of_le_left (le_iSup_of_le i (le_iSup_of_le hij le_rfl))
    have hdisj := (iSupIndep_def.1 hind) j
    rw [frattini_nongenerating hNtop, disjoint_top] at hdisj
    have h1 : Nat.card (E j) = 1 := by rw [hdisj]; simp
    rw [hE j] at h1
    exact hp.one_lt.ne' h1
  have hmapcard : ∀ j : ι, Nat.card ((E j).map f) = p := by
    intro j
    have hdvd : Nat.card ((E j).map f) ∣ p := hE j ▸ Subgroup.card_map_dvd (E j) f
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · refine absurd (le_trans (fun x hx => ?_) (le_sup_right (a := ⨆ i, ⨆ (_ : i ≠ j), E i)))
        (hkey j)
      have hmem : f x ∈ (E j).map f := ⟨x, hx, rfl⟩
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).1 hmem
    · exact h1
  have hindmap : iSupIndep fun i => (E i).map f := by
    rw [iSupIndep_def]
    intro j
    rw [disjoint_iff]
    by_contra hne
    have hsub : (E j).map f ≤ (⨆ i, ⨆ (_ : i ≠ j), (E i).map f) := by
      have hle : (E j).map f ⊓ (⨆ i, ⨆ (_ : i ≠ j), (E i).map f) ≤ (E j).map f := inf_le_left
      have hcard' : Nat.card ((E j).map f ⊓ (⨆ i, ⨆ (_ : i ≠ j), (E i).map f) : Subgroup (G ⧸ Φ))
          = p := by
        have hdvd := Subgroup.card_dvd_of_le hle
        rw [hmapcard j] at hdvd
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.1 h1) hne
        · exact h1
      rw [← Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', hmapcard j])]
      exact inf_le_right
    refine hkey j fun x hx => ?_
    have hfx : f x ∈ (⨆ i, ⨆ (_ : i ≠ j), (E i).map f) := hsub ⟨x, hx, rfl⟩
    have hmapsup : (⨆ i, ⨆ (_ : i ≠ j), (E i).map f)
        = Subgroup.map f (⨆ i, ⨆ (_ : i ≠ j), E i) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by rw [Subgroup.map_iSup]
    rw [hmapsup] at hfx
    have hmem := Subgroup.mem_comap.2 hfx
    rwa [Subgroup.comap_map_eq, hf, QuotientGroup.ker_mk'] at hmem
  have hbig : p ^ Fintype.card ι ≤ Φ.index := by
    have h := prod_card_le_card_of_iSupIndep (G := G ⧸ Φ) hindmap
    rwa [Finset.prod_congr rfl (fun i _ => hmapcard i), Finset.prod_const, Finset.card_univ] at h
  have hmul := Subgroup.index_mul_card Φ
  rw [hcard] at hmul
  have hcpos : 0 < Nat.card Φ := Nat.card_pos
  have hidxpos : 0 < Φ.index := by
    rcases Nat.eq_zero_or_pos Φ.index with h0 | h0
    · rw [h0] at hmul; simp at hmul; exact absurd hmul.symm (pow_ne_zero _ hp.pos.ne')
    · exact h0
  exact Subgroup.card_eq_one.1 (by nlinarith [hmul, hbig, hcpos, hidxpos])

theorem isMulCommutative_of_iSupIndep [Finite G] (hp : p.Prime) {E : ι → Subgroup G}
    (hcard : Nat.card G = p ^ Fintype.card ι) (hind : iSupIndep E) (hsup : ⨆ i, E i = ⊤)
    (hE : ∀ i, Nat.card (E i) = p) : IsMulCommutative G := by
  refine (commutator_eq_bot_iff G).1 (le_bot_iff.1 ?_)
  rw [← frattini_eq_bot_of_iSupIndep hp hcard hind hsup hE,
    frattini_eq_commutatorSupPowClosure hp hcard]
  exact commutator_le_commutatorSupPowClosure

end ElemAbelian

theorem commutator_le_of_isMulCommutative_quotient {H H0 : Subgroup L} [H0.Normal]
    (habel : IsMulCommutative (↥H ⧸ H0.subgroupOf H)) : ⁅H, H⁆ ≤ H0 := by
  have hcomm : commutator ↥H ≤ H0.subgroupOf H :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 habel
  rw [← Subgroup.map_subtype_commutator H]
  rintro x ⟨y, hy, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hcomm hy)

theorem exists_degree_le_relIndex_chiefActionKer [Finite L] {H H0 U K : Subgroup L} [H.Normal]
    [H0.Normal] (hH0H : H0 ≤ H) (hdisj : Disjoint H U) (hsup : H ⊔ U = K) (habel : ⁅H, H⁆ ≤ H0)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hker : ((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K : Set ↥K)
      ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = (n : ℂ) ∧ n ≤ (chiefActionKer H H0 U).relIndex U := by
  set C := chiefActionKer H H0 U with hCdef
  have hHK : H ≤ K := hsup ▸ le_sup_left
  have hUK : U ≤ K := hsup ▸ le_sup_right
  have hH0ker : ∀ x ∈ H0.subgroupOf K, θ x = θ 1 := fun x hx =>
    mem_charValueKernel.1 (hker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.mpr
      ((le_sup_left : H0 ≤ H0 ⊔ ⁅C, C⁆) (Subgroup.mem_subgroupOf.mp hx)))))
  obtain ⟨ψ, hψIrr, hψθ⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := H0.subgroupOf K)
    (mem_irrTrivialOn.2 ⟨hθ, hH0ker⟩)
  have hψval : ∀ x : ↥K, ψ (QuotientGroup.mk x) = θ x := fun x => congrFun hψθ x
  have hψ1 : ψ 1 = θ 1 := hψval 1
  have _hEnormal : (FieldActionCoreCoherence.quotImage H0 H K).Normal :=
    FieldActionCoreCoherence.quotImage_normal
  have _hEabel : IsMulCommutative (FieldActionCoreCoherence.quotImage H0 H K) :=
    FieldActionCoreCoherence.isMulCommutative_quotImage habel
  have hEU : (FieldActionCoreCoherence.quotImage H0 H K).IsComplement'
      (FieldActionCoreCoherence.quotImage H0 U K) :=
    FieldActionCoreCoherence.isComplement'_quotImage hH0H hdisj hsup
  have hCeq : FieldActionCoreCoherence.quotImage H0 C K
      = FieldActionCoreCoherence.quotImage H0 U K ⊓ Subgroup.centralizer
        ((FieldActionCoreCoherence.quotImage H0 H K : Subgroup (↥K ⧸ H0.subgroupOf K)) :
          Set (↥K ⧸ H0.subgroupOf K)) :=
    FieldActionCoreCoherence.quotImage_chiefActionKer_eq hHK
  have hψCker : ((⁅FieldActionCoreCoherence.quotImage H0 U K ⊓ Subgroup.centralizer
        ((FieldActionCoreCoherence.quotImage H0 H K : Subgroup (↥K ⧸ H0.subgroupOf K)) :
          Set (↥K ⧸ H0.subgroupOf K)),
      FieldActionCoreCoherence.quotImage H0 U K ⊓ Subgroup.centralizer
        ((FieldActionCoreCoherence.quotImage H0 H K : Subgroup (↥K ⧸ H0.subgroupOf K)) :
          Set (↥K ⧸ H0.subgroupOf K))⁆ : Subgroup (↥K ⧸ H0.subgroupOf K)) :
      Set (↥K ⧸ H0.subgroupOf K)) ⊆ charValueKernel ψ := by
    intro z hz
    rw [← hCeq] at hz
    obtain ⟨a, haK, haC, haz⟩ :=
      FieldActionCoreCoherence.exists_of_mem_quotImage
        (FieldActionCoreCoherence.commutator_quotImage_le hz)
    rw [mem_charValueKernel, hψ1, ← haz, hψval]
    exact mem_charValueKernel.1 (hker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : (⁅C, C⁆ : Subgroup L) ≤ H0 ⊔ ⁅C, C⁆) haC))))
  obtain ⟨n, hn, hle⟩ := exists_degree_le_relIndex_centralizer_of_isComplement'
    (E := FieldActionCoreCoherence.quotImage H0 H K)
    (U := FieldActionCoreCoherence.quotImage H0 U K) hEU hψIrr hψCker
  refine ⟨n, by rw [← hψ1, hn], ?_⟩
  rwa [← hCeq, FieldActionCoreCoherence.relIndex_quotImage_chiefActionKer (H := H) hH0H hdisj hUK]
    at hle

theorem charValueKernel_star {X : Type*} [Group X] (θ : X → ℂ) :
    charValueKernel (star θ) = charValueKernel θ := by
  ext x
  simp only [mem_charValueKernel, Pi.star_apply]
  exact star_inj

theorem star_mem_irrKer {X : Type*} [Group X] [Finite X] {Hx Mx : Subgroup X} {θ : X → ℂ}
    (hθ : θ ∈ irrKer ℂ Hx Mx) : star θ ∈ irrKer ℂ Hx Mx := by
  obtain ⟨hirr, hM, hH⟩ := mem_irrKer.1 hθ
  refine mem_irrKer.2 ⟨?_, ?_, ?_⟩
  · rw [irrChar_eq_Irr] at hirr ⊢
    exact star_mem_Irr hirr
  · rw [charValueKernel_star]; exact hM
  · rw [charValueKernel_star]; exact hH

theorem star_mem_scalarEqualityFamily [Fintype L] {K H H0 U : Subgroup L} [H.Normal] [H0.Normal]
    {q : ℕ} {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {f : L → ℂ}
    (hf : f ∈ scalarEqualityFamily K H H0 U Eline) :
    star f ∈ scalarEqualityFamily K H H0 U Eline := by
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hf
  exact mem_scalarEqualityFamily.2 ⟨star θ, star_mem_irrKer hθ,
    DisjointCoherentFamilies.indClassFun_star K θ⟩

open scoped Classical in
noncomputable def largeLayer (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (S : Finset (L → ℂ)) : Finset (L → ℂ) :=
  S.filter fun χ => χ ∈ Irr L ∧
    ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ ∧
    χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)

open scoped Classical in
noncomputable def smallLayer (H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (S : Finset (L → ℂ)) : Finset (L → ℂ) :=
  S.filter fun χ =>
    ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ ∧
    χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ)

section LargeLayer

variable {H H0 U : Subgroup L} [H.Normal] [H0.Normal] {q : ℕ}
  {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {S : Finset (L → ℂ)}

theorem mem_smallLayer {χ : L → ℂ} :
    χ ∈ smallLayer H H0 U Eline S ↔ χ ∈ S ∧
      ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ ∧
      χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) := by
  classical
  simp only [smallLayer, Finset.mem_filter, and_assoc]

theorem smallLayer_subset : smallLayer H H0 U Eline S ⊆ S := fun _ h => (mem_smallLayer.1 h).1

theorem subset_charValueKernel_of_mem_smallLayer {χ : L → ℂ}
    (hχ : χ ∈ smallLayer H H0 U Eline S) :
    ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ :=
  (mem_smallLayer.1 hχ).2.1

theorem apply_one_of_mem_smallLayer {χ : L → ℂ} (hχ : χ ∈ smallLayer H H0 U Eline S) :
    χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) := (mem_smallLayer.1 hχ).2.2

theorem mem_largeLayer {χ : L → ℂ} :
    χ ∈ largeLayer H H0 U Eline S ↔ χ ∈ S ∧ χ ∈ Irr L ∧
      ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ ∧
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ) := by
  classical
  simp only [largeLayer, Finset.mem_filter, and_assoc]

theorem largeLayer_subset : largeLayer H H0 U Eline S ⊆ S := fun _ h => (mem_largeLayer.1 h).1

theorem mem_Irr_of_mem_largeLayer {χ : L → ℂ} (hχ : χ ∈ largeLayer H H0 U Eline S) :
    χ ∈ Irr L := (mem_largeLayer.1 hχ).2.1

theorem subset_charValueKernel_of_mem_largeLayer {χ : L → ℂ}
    (hχ : χ ∈ largeLayer H H0 U Eline S) :
    ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ :=
  (mem_largeLayer.1 hχ).2.2.1

theorem apply_one_of_mem_largeLayer {χ : L → ℂ} (hχ : χ ∈ largeLayer H H0 U Eline S) :
    χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ) := (mem_largeLayer.1 hχ).2.2.2

theorem star_mem_largeLayer [Fintype L] {K : Subgroup L}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    {χ : L → ℂ} (hχ : χ ∈ largeLayer H H0 U Eline S) : star χ ∈ largeLayer H H0 U Eline S := by
  obtain ⟨hχS, hIrr, hker, hdeg⟩ := mem_largeLayer.1 hχ
  refine mem_largeLayer.2 ⟨?_, star_mem_Irr hIrr, ?_, ?_⟩
  · have h1 : χ ∈ scalarEqualityFamily K H H0 U Eline := hS ▸ Finset.mem_coe.2 hχS
    have h2 := star_mem_scalarEqualityFamily h1
    rw [← hS] at h2
    exact Finset.mem_coe.1 h2
  · rw [charValueKernel_star]; exact hker
  · rw [Pi.star_apply, hdeg]
    simp

end LargeLayer

noncomputable def coreLayer [Finite L] (K H H0 U : Subgroup L) [H.Normal] [H0.Normal] {q : ℕ}
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) : Finset (↥K → ℂ) :=
  irrKerFinset ((H ⊔ lineFixerInf H H0 U Eline).subgroupOf K)
    ((H0 ⊔ lineFixerInf H H0 U Eline).subgroupOf K)

theorem mem_coreLayer [Finite L] {K H H0 U : Subgroup L} [H.Normal] [H0.Normal] {q : ℕ}
    {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {θ : ↥K → ℂ} :
    θ ∈ coreLayer K H H0 U Eline ↔ θ ∈ irrKer ℂ ((H ⊔ lineFixerInf H H0 U Eline).subgroupOf K)
      ((H0 ⊔ lineFixerInf H H0 U Eline).subgroupOf K) := by
  rw [coreLayer, mem_irrKerFinset]

theorem mem_irrKer_subgroupOf_iff_indClassFun [Fintype L] {K Z0 Z1 : Subgroup L} [Z0.Normal]
    [Z1.Normal] (h0 : Z0 ≤ K) (h1 : Z1 ≤ K) {θ : ↥K → ℂ} :
    θ ∈ irrKer ℂ (Z1.subgroupOf K) (Z0.subgroupOf K) ↔ θ ∈ Irr ↥K ∧
      (Z0 : Set L) ⊆ charValueKernel (indClassFun K θ) ∧
        ¬ (Z1 : Set L) ⊆ charValueKernel (indClassFun K θ) := by
  rw [mem_irrKer, irrChar_eq_Irr]
  constructor
  · rintro ⟨hθ, ha, hb⟩
    exact ⟨hθ, (subset_charValueKernel_indClassFun_iff h0 hθ).2 ha,
      fun h => hb ((subset_charValueKernel_indClassFun_iff h1 hθ).1 h)⟩
  · rintro ⟨hθ, ha, hb⟩
    exact ⟨hθ, (subset_charValueKernel_indClassFun_iff h0 hθ).1 ha,
      fun h => hb ((subset_charValueKernel_indClassFun_iff h1 hθ).2 h)⟩

theorem count_of_sum_sq_degree {p q a u s₁ n : ℕ} (hu : 0 < u)
    (hp : (p : ℝ) - 1 = 2 * a) (hs₁ : (s₁ : ℝ) * a = 2 * u)
    (hsum : (q : ℝ) * (s₁ * a ^ 2) + (q : ℝ) * (n * u ^ 2) + ((p : ℝ) - 1) * u ^ 2
      = (u : ℝ) * ((p : ℝ) ^ q - 1)) :
    (q : ℝ) * u * n + ((p : ℝ) - 1) * ((q : ℝ) + u) = (p : ℝ) ^ q - 1 := by
  have hu0 : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hu.ne'
  refine mul_left_cancel₀ hu0 ?_
  linear_combination hsum + ((q : ℝ) * u) * hp - ((q : ℝ) * a) * hs₁

section ResConstituentsLinear

variable {H H0 K : Subgroup L} [H.Normal] [H0.Normal]

theorem coe_coe_subgroupOfEquivOfLe_symm (hHK : H ≤ K) (h : ↥H) :
    ((((Subgroup.subgroupOfEquivOfLe hHK).symm h : ↥(H.subgroupOf K)) : ↥K) : L) = (h : L) := by
  simp [Subgroup.subgroupOfEquivOfLe]

theorem exists_monoidHom_units_of_mem_resConstituents [Finite L] (hHK : H ≤ K)
    [Fintype ↥(H.subgroupOf K)] (habel : IsMulCommutative (↥H ⧸ H0.subgroupOf H))
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hH0 : ((H0.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ)
    {lam : ↥(H.subgroupOf K) → ℂ} (hlam : lam ∈ resConstituents (H.subgroupOf K) θ) :
    ∃ μ : (↥H ⧸ H0.subgroupOf H) →* ℂˣ, ∀ h : ↥H,
      ((μ (QuotientGroup.mk h) : ℂ)) = lam ((Subgroup.subgroupOfEquivOfLe hHK).symm h) := by
  set e : ↥H ≃* ↥(H.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hHK).symm with he
  have hlamIrr : lam ∈ Irr ↥(H.subgroupOf K) := resConstituents_subset_Irr (Finset.mem_coe.2 hlam)
  have hlam'Irr : lam ∘ e ∈ Irr ↥H := FrobeniusInduction.mem_Irr_comp_mulEquiv hlamIrr e
  have hkerlam := FixedFreeCoreDegree.subset_charValueKernel_of_mem_resConstituents
    (Z := H0.subgroupOf K) hθ hH0 hlam
  have hker : ((H0.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel (lam ∘ e) := by
    intro x hx
    have hxH0 : (x : L) ∈ H0 := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hx)
    have hmem : e x ∈ (H0.subgroupOf K).subgroupOf (H.subgroupOf K) := by
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ?_)
      rw [he, coe_coe_subgroupOfEquivOfLe_symm]
      exact hxH0
    have h1 := mem_charValueKernel.1 (hkerlam (SetLike.mem_coe.2 hmem))
    refine mem_charValueKernel.2 ?_
    have hone : e 1 = 1 := map_one e
    simp only [Function.comp_apply]
    rw [h1, ← hone]
  obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn
    (N := H0.subgroupOf H) (mem_irrTrivialOn.2 ⟨hlam'Irr, fun n hn =>
      mem_charValueKernel.1 (hker (SetLike.mem_coe.2 hn))⟩)
  obtain ⟨μ, hμ⟩ := AbelianQuotientExtension.exists_monoidHom_units_of_mem_Irr hψ
  exact ⟨μ, fun h => by rw [hμ]; exact congrFun hcomp h⟩

end ResConstituentsLinear

section QuotientInclusion

noncomputable def quotientInclusion (H H0 : Subgroup L) [H0.Normal] :
    (↥H ⧸ H0.subgroupOf H) →* L ⧸ H0 :=
  QuotientGroup.map (H0.subgroupOf H) H0 H.subtype (fun _ hx => hx)

@[simp] theorem quotientInclusion_mk (H H0 : Subgroup L) [H0.Normal] (h : ↥H) :
    quotientInclusion H H0 (QuotientGroup.mk h) = QuotientGroup.mk (h : L) := (rfl)

theorem exists_quotientInclusion_eq (H H0 : Subgroup L) [H0.Normal]
    (y : ↥H ⧸ H0.subgroupOf H) : ∃ h ∈ H, quotientInclusion H H0 y = QuotientGroup.mk h := by
  induction y using QuotientGroup.induction_on with
  | _ h => exact ⟨h, h.2, rfl⟩

theorem quotientInclusion_factorConjAut (H H0 : Subgroup L) [H.Normal] [H0.Normal] (g : L)
    (y : ↥H ⧸ H0.subgroupOf H) :
    quotientInclusion H H0 (ChiefFactorLinearAction.factorConjAut H H0 g y)
      = (QuotientGroup.mk g : L ⧸ H0) * quotientInclusion H H0 y * (QuotientGroup.mk g)⁻¹ := by
  induction y using QuotientGroup.induction_on with
  | _ h =>
    rw [ChiefFactorLinearAction.factorConjAut_mk, quotientInclusion_mk, quotientInclusion_mk]
    rfl

theorem quotientInclusion_factorLinearAut {W : Type*} [AddCommGroup W] {p : ℕ}
    [Module (ZMod p) W] (H H0 : Subgroup L) [H.Normal] [H0.Normal]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W) (g : L) (v : W) :
    quotientInclusion H H0
        (e.symm (Multiplicative.ofAdd (ChiefFactorFaithfulImage.factorLinearAut p H H0 e g v)))
      = (QuotientGroup.mk g : L ⧸ H0) * quotientInclusion H H0 (e.symm (Multiplicative.ofAdd v))
        * (QuotientGroup.mk g)⁻¹ := by
  rw [ChiefFactorFaithfulImage.factorLinearAut_apply', ofAdd_toAdd, MulEquiv.symm_apply_apply,
    quotientInclusion_factorConjAut]

end QuotientInclusion

variable {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal] [H0.Normal]
  {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}

structure IsScalarCoreConfig (p q : ℕ) (K H U B H0 : Subgroup L) [H.Normal] [H0.Normal]
    (Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)) (A : Set L) : Prop where
  solvable : Group.IsSolvable L
  odd_card : Odd (Nat.card L)
  q_prime : q.Prime
  p_prime : p.Prime
  p_odd : Odd p
  p_ne_q : p ≠ q
  isComplement_K_B : K.IsComplement' B
  H_le_K : H ≤ K
  U_le_K : U ≤ K
  disjoint_H_U : Disjoint H U
  sup_H_U : H ⊔ U = K
  card_B : Nat.card B = q
  exists_gen_B : ∃ b ∈ B, B = Subgroup.zpowers b ∧
    ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)
  B_le_normalizer_U : B ≤ Subgroup.normalizer (U : Set L)
  coprime_H_U : (Nat.card H).Coprime (Nat.card U)
  coprime_q_K : q.Coprime (Nat.card K)
  inf_centralizer_U_B : U ⊓ Subgroup.centralizer (B : Set L) = ⊥
  H0_le_H : H0 ≤ H
  card_quotient : Nat.card (↥H ⧸ H0.subgroupOf H) = p ^ q
  indep_Eline : iSupIndep Eline
  iSup_Eline : ⨆ i, Eline i = ⊤
  card_Eline : ∀ i, Nat.card (Eline i) = p
  map_U_Eline : ∀ u ∈ U, ∀ i, Subgroup.map (conjQuotientAut H H0 u) (Eline i) = Eline i
  lineFixer_ne : ∀ i, lineFixer H H0 U (Eline i) ≠ U
  A_subset : A ⊆ (K : Set L) \ {1}
  A_invariant : ∀ g : L, ∀ x ∈ A, g⁻¹ * x * g ∈ A
  centralizer_subset_A : ∀ h ∈ H, h ≠ 1 →
    ((K ⊓ Subgroup.centralizer ({h} : Set L) : Subgroup L) : Set L) \ {1} ⊆ A

namespace IsScalarCoreConfig

theorem of_isScalarEqualityConfig (hc : IsScalarEqualityConfig p q K H U B H0 Eline A) :
    IsScalarCoreConfig p q K H U B H0 Eline A where
  solvable := hc.solvable
  odd_card := hc.odd_card
  q_prime := hc.q_prime
  p_prime := hc.p_prime
  p_odd := hc.p_odd
  p_ne_q := hc.p_ne_q
  isComplement_K_B := hc.isComplement_K_B
  H_le_K := hc.H_le_K
  U_le_K := hc.U_le_K
  disjoint_H_U := hc.disjoint_H_U
  sup_H_U := hc.sup_H_U
  card_B := hc.card_B
  exists_gen_B := hc.exists_gen_B
  B_le_normalizer_U := hc.B_le_normalizer_U
  coprime_H_U := hc.coprime_H_U
  coprime_q_K := hc.coprime_q_K
  inf_centralizer_U_B := hc.inf_centralizer_U_B
  H0_le_H := hc.H0_le_H
  card_quotient := hc.card_quotient
  indep_Eline := hc.indep_Eline
  iSup_Eline := hc.iSup_Eline
  card_Eline := hc.card_Eline
  map_U_Eline := hc.map_U_Eline
  lineFixer_ne := hc.lineFixer_ne
  A_subset := hc.A_subset
  A_invariant := hc.A_invariant
  centralizer_subset_A := hc.centralizer_subset_A

variable (hc : IsScalarCoreConfig p q K H U B H0 Eline A)

include hc

theorem isScalarEqualityConfig
    (hcomm : lineFixerInf H H0 U Eline = ⁅U, U⁆)
    (hsub : p - 1 = 2 * (lineFixer H H0 U (Eline 0)).relIndex U)
    (hlt : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hinf : ∀ i j, i ≠ j →
      lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) = lineFixerInf H H0 U Eline) :
    IsScalarEqualityConfig p q K H U B H0 Eline A where
  solvable := hc.solvable
  odd_card := hc.odd_card
  q_prime := hc.q_prime
  p_prime := hc.p_prime
  p_odd := hc.p_odd
  p_ne_q := hc.p_ne_q
  isComplement_K_B := hc.isComplement_K_B
  H_le_K := hc.H_le_K
  U_le_K := hc.U_le_K
  disjoint_H_U := hc.disjoint_H_U
  sup_H_U := hc.sup_H_U
  card_B := hc.card_B
  exists_gen_B := hc.exists_gen_B
  B_le_normalizer_U := hc.B_le_normalizer_U
  coprime_H_U := hc.coprime_H_U
  coprime_q_K := hc.coprime_q_K
  inf_centralizer_U_B := hc.inf_centralizer_U_B
  H0_le_H := hc.H0_le_H
  card_quotient := hc.card_quotient
  indep_Eline := hc.indep_Eline
  iSup_Eline := hc.iSup_Eline
  card_Eline := hc.card_Eline
  map_U_Eline := hc.map_U_Eline
  lineFixer_ne := hc.lineFixer_ne
  A_subset := hc.A_subset
  A_invariant := hc.A_invariant
  centralizer_subset_A := hc.centralizer_subset_A
  commutator_eq := hcomm
  sub_one_eq := hsub
  lt_relIndex := hlt
  inf_lineFixer := hinf

theorem one_notMem_A : (1 : L) ∉ A := fun h => (hc.A_subset h).2 rfl

theorem q_odd : Odd q := by
  have hdvd : q ∣ Nat.card L := hc.card_B ▸ Subgroup.card_subgroup_dvd_card B
  rcases Nat.even_or_odd q with he | ho
  · exact absurd (he.two_dvd.trans hdvd)
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.1 hc.odd_card)
  · exact ho

theorem isCyclic_B : IsCyclic B := by
  obtain ⟨b, hbB, hB, -⟩ := hc.exists_gen_B
  refine ⟨⟨⟨b, hbB⟩, fun x => ?_⟩⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hB ▸ x.2 : (x : L) ∈ Subgroup.zpowers b)
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem inf_centralizer_eq_bot {x : L} (hxK : x ∈ K) (hx1 : x ≠ 1) (hxA : x ∉ A) :
    H ⊓ Subgroup.centralizer ({x} : Set L) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro h hh
  obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.1 hh
  by_contra hh1
  refine hxA (hc.centralizer_subset_A h hhH hh1 ⟨Subgroup.mem_inf.2 ⟨hxK, ?_⟩, hx1⟩)
  exact Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hhc).symm

theorem inf_centralizer_subgroupOf_eq_bot {z : ↥K} (hz1 : (z : L) ≠ 1) (hzA : (z : L) ∉ A) :
    (H.subgroupOf K) ⊓ Subgroup.centralizer ({z} : Set ↥K) = ⊥ := by
  have hbot := hc.inf_centralizer_eq_bot z.2 hz1 hzA
  rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
  intro w hw
  obtain ⟨hwH, hwc⟩ := Subgroup.mem_inf.1 hw
  have hcomm : (w : L) * (z : L) = (z : L) * (w : L) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hwc)
  exact Subtype.ext (hbot (w : L) (Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.1 hwH, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩))

theorem eq_zero_of_mem_scalarEqualityFamily [Fintype L] [K.Normal]
    {chi : L → ℂ} (hchi : chi ∈ scalarEqualityFamily K H H0 U Eline) {y : L} (hy1 : y ≠ 1)
    (hyA : y ∉ A) : chi y = 0 := by
  classical
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hchi
  obtain ⟨hirr, -, hdet⟩ := mem_irrKer.1 hθ
  have _hHn : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hmem : t⁻¹ * y * t ∈ K
  · rw [dif_pos hmem]
    set z : ↥K := ⟨t⁻¹ * y * t, hmem⟩ with hzdef
    have hzcoe : (z : L) = t⁻¹ * y * t := rfl
    have hz1 : (z : L) ≠ 1 := by
      intro hcon
      refine hy1 ?_
      have h2 : t * (t⁻¹ * y * t) * t⁻¹ = t * 1 * t⁻¹ := by rw [← hzcoe, hcon]
      simpa [mul_assoc] using h2
    have hzA : (z : L) ∉ A := by
      intro hcon
      have h2 := hc.A_invariant t⁻¹ _ hcon
      simp only [inv_inv, hzcoe] at h2
      exact hyA (by simpa [show t * (t⁻¹ * y * t) * t⁻¹ = y from by group] using h2)
    exact eq_zero_of_inf_centralizer_eq_bot hirr hdet
      (hc.inf_centralizer_subgroupOf_eq_bot hz1 hzA)
  · rw [dif_neg hmem]

omit hc in
theorem scalarEqualityFamily_subset_virtualChars [Fintype L] :
    scalarEqualityFamily K H H0 U Eline ⊆ (virtualChars L : Set (L → ℂ)) := by
  intro f hf
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam K
    (scalarEqualityFamily_subset_indFam Eline hf)
  exact SetLike.mem_coe.2 (mem_virtualChars_of_mem_span_Irr
    (hW ▸ FDRep.character_mem_span_Irr W))

theorem span_scalarEqualityFamily_le [Fintype L] [K.Normal] :
    Submodule.span ℤ (scalarEqualityFamily K H H0 U Eline) ≤ virtualCharsOnOne A :=
  Submodule.span_le.2 fun _ hf => ⟨scalarEqualityFamily_subset_virtualChars hf,
    fun _ hx hx1 => hc.eq_zero_of_mem_scalarEqualityFamily hf hx1 hx⟩

theorem charSpanZero_le_virtualCharsOn [Fintype L] [K.Normal] {S : Set (L → ℂ)}
    (hS : S = scalarEqualityFamily K H H0 U Eline) : charSpanZero S ≤ virtualCharsOn A := by
  intro f hf
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  exact mem_virtualCharsOn_of_mem_virtualCharsOnOne
    (hc.span_scalarEqualityFamily_le (hS ▸ hspan)) h1

omit hc in
theorem relIndex_dvd_card [Finite L] (X Y : Subgroup L) : X.relIndex Y ∣ Nat.card Y :=
  Dvd.intro_left (Nat.card ↥(X.subgroupOf Y)) (Subgroup.card_mul_index (X.subgroupOf Y))

omit hc in
theorem relIndex_ne_zero [Finite L] (X Y : Subgroup L) : X.relIndex Y ≠ 0 := fun h0 => by
  have h := relIndex_dvd_card X Y
  rw [h0, zero_dvd_iff] at h
  exact absurd h Nat.card_pos.ne'

theorem one_lt_relIndex_lineFixer [Finite L] :
    1 < (lineFixer H H0 U (Eline 0)).relIndex U := by
  have hle : lineFixer H H0 U (Eline 0) ≤ U := lineFixer_le H H0 U (Eline 0)
  have hnz := relIndex_ne_zero (lineFixer H H0 U (Eline 0)) U
  have hn1 : (lineFixer H H0 U (Eline 0)).relIndex U ≠ 1 := fun h =>
    hc.lineFixer_ne 0 (le_antisymm hle (Subgroup.relIndex_eq_one.1 h))
  omega

theorem odd_relIndex_lineFixer [Finite L] :
    Odd ((lineFixer H H0 U (Eline 0)).relIndex U) :=
  hc.odd_card.of_dvd_nat
    ((relIndex_dvd_card (lineFixer H H0 U (Eline 0)) U).trans (Subgroup.card_subgroup_dvd_card U))

omit hc in
theorem relIndex_lineFixer_dvd_relIndex_lineFixerInf :
    (lineFixer H H0 U (Eline 0)).relIndex U ∣ (lineFixerInf H H0 U Eline).relIndex U :=
  Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _
    (lineFixerInf_le_lineFixer H H0 U Eline 0) (lineFixer_le H H0 U (Eline 0)))

omit hc in
theorem pos_relIndex_lineFixerInf [Finite L] :
    0 < (lineFixerInf H H0 U Eline).relIndex U :=
  Nat.pos_of_ne_zero (relIndex_ne_zero _ _)

omit hc in
theorem relIndex_lineFixerInf_le_relIndex_commutator [Finite L]
    (hcomm : ⁅U, U⁆ ≤ lineFixerInf H H0 U Eline) :
    (lineFixerInf H H0 U Eline).relIndex U ≤ (⁅U, U⁆ : Subgroup L).relIndex U := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ hcomm (lineFixerInf_le H H0 U Eline 0)
  have hcpos : 0 < (⁅U, U⁆ : Subgroup L).relIndex (lineFixerInf H H0 U Eline) :=
    Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  calc (lineFixerInf H H0 U Eline).relIndex U
      ≤ (⁅U, U⁆ : Subgroup L).relIndex (lineFixerInf H H0 U Eline)
          * (lineFixerInf H H0 U Eline).relIndex U := Nat.le_mul_of_pos_left _ hcpos
    _ = _ := h

theorem three_le_p : 3 ≤ p := by
  have h2 := hc.p_prime.two_le
  rcases Nat.lt_or_ge p 3 with hl | hl
  · interval_cases p
    · exact absurd hc.p_odd (by decide)
  · exact hl

theorem three_le_q : 3 ≤ q := by
  have h2 := hc.q_prime.two_le
  have ho := hc.q_odd
  rcases Nat.lt_or_ge q 3 with hl | hl
  · interval_cases q
    · exact absurd ho (by decide)
  · exact hl

omit hc in
theorem eq_one_of_forall_line_apply_eq_one (hspan : ⨆ i, Eline i = ⊤)
    {lam : (↥H ⧸ H0.subgroupOf H) →* ℂˣ} (h : ∀ i, ∀ v ∈ Eline i, lam v = 1)
    (v : ↥H ⧸ H0.subgroupOf H) : lam v = 1 := by
  have hle : (⊤ : Subgroup (↥H ⧸ H0.subgroupOf H)) ≤ lam.ker :=
    hspan ▸ iSup_le fun i => fun w hw => MonoidHom.mem_ker.2 (h i w hw)
  exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top v))

omit hc in
theorem exists_line_apply_ne_one (hspan : ⨆ i, Eline i = ⊤)
    {lam : (↥H ⧸ H0.subgroupOf H) →* ℂˣ} {v : ↥H ⧸ H0.subgroupOf H} (hv : lam v ≠ 1) :
    ∃ i, ∃ w ∈ Eline i, lam w ≠ 1 := by
  by_contra hcon
  refine hv (eq_one_of_forall_line_apply_eq_one hspan (fun i w hw => ?_) v)
  by_contra hne
  exact hcon ⟨i, w, hw, hne⟩

omit hc in
theorem lineFixerInf_eq_chiefActionKer_of_iSup_eq_top [NeZero q] (hspan : ⨆ i, Eline i = ⊤) :
    lineFixerInf H H0 U Eline = chiefActionKer H H0 U := by
  refine le_antisymm (fun x hx => ?_) (le_lineFixerInf fun i => fun x hx => ?_)
  · have hxU : x ∈ U := lineFixerInf_le H H0 U Eline 0 hx
    refine (mem_chiefActionKer_iff_mem_ker H H0 U).2 ⟨hxU, MonoidHom.mem_ker.2 ?_⟩
    set σ := conjQuotientAut H H0 x with hσ
    have hfix : ∀ i, Eline i ≤ (σ.toMonoidHom).eqLocus (MonoidHom.id _) := fun i v hv =>
      (mem_lineFixer.1 (lineFixerInf_le_lineFixer H H0 U Eline i hx)).2 v hv
    have htop : (⊤ : Subgroup (↥H ⧸ H0.subgroupOf H))
        ≤ (σ.toMonoidHom).eqLocus (MonoidHom.id _) := hspan ▸ iSup_le hfix
    exact MulEquiv.ext fun v => htop (Subgroup.mem_top v)
  · obtain ⟨hxU, hxker⟩ := (mem_chiefActionKer_iff_mem_ker H H0 U).1 hx
    exact mem_lineFixer.2 ⟨hxU, fun v _ => by rw [MonoidHom.mem_ker.1 hxker]; rfl⟩

theorem isMulCommutative_quotient [Finite L] : IsMulCommutative (↥H ⧸ H0.subgroupOf H) := by
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  have : Fintype (ZMod q) := ZMod.fintype q
  exact isMulCommutative_of_iSupIndep hc.p_prime (by rw [hc.card_quotient, ZMod.card q])
    hc.indep_Eline hc.iSup_Eline hc.card_Eline

theorem commutator_H_le_H0 [Finite L] : ⁅H, H⁆ ≤ H0 :=
  commutator_le_of_isMulCommutative_quotient hc.isMulCommutative_quotient

theorem pow_eq_one_quotient [Finite L] (x : ↥H ⧸ H0.subgroupOf H) : x ^ p = 1 := by
  have := hc.isMulCommutative_quotient
  exact pow_eq_one_of_iSup_eq_top hc.iSup_Eline hc.card_Eline x

theorem isElementaryAbelian_top_quotient [Finite L] :
    IsElementaryAbelian p (⊤ : Subgroup (↥H ⧸ H0.subgroupOf H)) := by
  have := hc.isMulCommutative_quotient
  exact isElementaryAbelian_iff.2 ⟨⟨⟨fun a b => Subtype.ext
      (IsMulCommutative.is_comm.comm (a : ↥H ⧸ H0.subgroupOf H) b)⟩⟩,
    fun x _ => hc.pow_eq_one_quotient x⟩

theorem nonempty_mulEquiv_quotient [Finite L] :
    Nonempty ((↥H ⧸ H0.subgroupOf H) ≃* Multiplicative (ULift.{u_1} (Fin q → ZMod p))) := by
  have hcard : Nat.card (⊤ : Subgroup (↥H ⧸ H0.subgroupOf H)) = p ^ q := by
    rw [Subgroup.card_top, hc.card_quotient]
  obtain ⟨f⟩ := nonempty_mulEquiv_pi_of_isElementaryAbelian (d := q) hc.p_prime
    hc.isElementaryAbelian_top_quotient hcard
  exact ⟨(Subgroup.topEquiv.symm.trans f).trans
    ((MulEquiv.funMultiplicative (Fin q) (ZMod p)).symm.trans
      (MulEquiv.ulift (α := Multiplicative (Fin q → ZMod p))).symm)⟩

theorem coprime_p_card_U [Finite L] : Nat.Coprime p (Nat.card ↥U) := by
  have hdvd : p ∣ Nat.card ↥H :=
    dvd_trans (dvd_pow_self p hc.q_prime.pos.ne')
      (hc.card_quotient ▸ Subgroup.card_quotient_dvd_card (H0.subgroupOf H))
  exact Nat.Coprime.coprime_dvd_left hdvd hc.coprime_H_U

theorem lineFixerInf_eq_chiefActionKer : lineFixerInf H H0 U Eline = chiefActionKer H H0 U := by
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  exact lineFixerInf_eq_chiefActionKer_of_iSup_eq_top hc.iSup_Eline

theorem relIndex_lineFixer_dvd_sub_one' (i : ZMod q) :
    (lineFixer H H0 U (Eline i)).relIndex U ∣ p - 1 :=
  relIndex_lineFixer_dvd_sub_one hc.p_prime (hc.card_Eline i) fun u hu => hc.map_U_Eline u hu i

theorem index_eq_q : K.index = q := by
  rw [hc.isComplement_K_B.symm.index_eq_card, hc.card_B]

theorem sup_K_B : K ⊔ B = ⊤ := hc.isComplement_K_B.sup_eq_top

theorem normal_K : K.Normal := by
  have hB : ∀ g ∈ B, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    have hnb := Subgroup.mem_normalizer_iff.1 (hc.B_le_normalizer_U hg)
    have hle : H ⊔ U ≤ Subgroup.comap (MulAut.conj g : L →* L) K :=
      sup_le (fun y hy => Subgroup.mem_comap.2 (hc.H_le_K (‹H.Normal›.conj_mem y hy g)))
        (fun y hy => Subgroup.mem_comap.2 (hc.U_le_K ((hnb y).1 hy)))
    rw [hc.sup_H_U] at hle
    exact Subgroup.mem_comap.1 (hle hx)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, b, hb, hkb⟩ : ∃ k ∈ K, ∃ b ∈ B, g = k * b := by
    obtain ⟨⟨⟨k, hk⟩, ⟨b, hb⟩⟩, hx, -⟩ := hc.isComplement_K_B.existsUnique g
    exact ⟨k, hk, b, hb, hx.symm⟩
  subst hkb
  rw [show (k * b) * n * (k * b)⁻¹ = k * (b * n * b⁻¹) * k⁻¹ from by group]
  exact K.mul_mem (K.mul_mem hk (hB b hb n hn)) (K.inv_mem hk)

theorem indClassFun_apply_one_eq [Fintype L] (θ : ↥K → ℂ) :
    indClassFun K θ 1 = (q : ℂ) * θ 1 := by
  have hKne : ((Nat.card K : ℂ)) ≠ 0 := by simpa using (Nat.card_pos (α := ↥K)).ne'
  have hindex : (Nat.card L : ℂ) / (Nat.card K : ℂ) = (q : ℂ) := by
    rw [div_eq_iff hKne, ← hc.index_eq_q, ← Nat.cast_mul, Subgroup.index_mul_card]
  rw [indClassFun_one, hindex]

theorem exists_mem_irrKer_apply_one_eq [Fintype L] {χ : L → ℂ}
    (hχ : χ ∈ scalarEqualityFamily K H H0 U Eline) :
    ∃ θ ∈ irrKer ℂ (H.subgroupOf K)
      ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K),
      θ ∈ Irr ↥K ∧ χ 1 = (q : ℂ) * θ 1 := by
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hχ
  refine ⟨θ, hθ, mem_Irr.2 (mem_irrChar.1 (mem_irrKer.1 hθ).1), ?_⟩
  have hcard : (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have hKne : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [indClassFun_one, hcard, mul_div_assoc, div_self hKne, mul_one, hc.index_eq_q]

omit hc in
theorem map_conj_lineFixer {Ei Ej : Subgroup (↥H ⧸ H0.subgroupOf H)} {g : L}
    (hU : g ∈ Subgroup.normalizer (U : Set L))
    (hE : Subgroup.map (conjQuotientAut H H0 g) Ei = Ej) :
    Subgroup.map (MulAut.conj g : L →* L) (lineFixer H H0 U Ei) = lineFixer H H0 U Ej := by
  have hUx : ∀ x : L, x ∈ U ↔ g⁻¹ * x * g ∈ U := Subgroup.mem_normalizer_iff''.1 hU
  set ρ := conjQuotientAut H H0 with hρ
  have key : ∀ (y : L) (v : ↥H ⧸ H0.subgroupOf H),
      ρ (g⁻¹ * y * g) v = v ↔ ρ y (ρ g v) = ρ g v := by
    intro y v
    rw [map_mul, map_mul, map_inv]
    change (ρ g)⁻¹ ((ρ y) ((ρ g) v)) = v ↔ _
    rw [show ((ρ g)⁻¹ : MulAut (↥H ⧸ H0.subgroupOf H)) ((ρ y) ((ρ g) v))
      = (ρ g).symm ((ρ y) ((ρ g) v)) from rfl, MulEquiv.symm_apply_eq]
  ext x
  have hmap : x ∈ Subgroup.map (MulAut.conj g : L →* L) (lineFixer H H0 U Ei)
      ↔ g⁻¹ * x * g ∈ lineFixer H H0 U Ei := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : g⁻¹ * ((MulAut.conj g : L →* L) y) * g = y := by
        change g⁻¹ * (g * y * g⁻¹) * g = y
        group
      rwa [h1]
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  rw [hmap, mem_lineFixer, mem_lineFixer]
  constructor
  · rintro ⟨hxU, hfix⟩
    refine ⟨(hUx x).2 hxU, fun v hv => ?_⟩
    rw [← hE] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact (key x w).1 (hfix w hw)
  · rintro ⟨hxU, hfix⟩
    refine ⟨(hUx x).1 hxU, fun w hw => ?_⟩
    refine (key x w).2 (hfix _ ?_)
    rw [← hE]
    exact ⟨w, hw, rfl⟩

omit hc in
theorem natCard_map_conj (I : Subgroup L) (g : L) :
    Nat.card (Subgroup.map (MulAut.conj g : L →* L) I) = Nat.card I := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : I => (⟨(MulAut.conj g) (x : L), ⟨x, x.2, rfl⟩⟩ :
    Subgroup.map (MulAut.conj g : L →* L) I)) ?_).symm
  refine ⟨fun x y h => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h)), ?_⟩
  rintro ⟨z, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

omit hc in
theorem relIndex_eq_of_natCard_eq [Finite L] {I J : Subgroup L} (hI : I ≤ U) (hJ : J ≤ U)
    (h : Nat.card I = Nat.card J) : I.relIndex U = J.relIndex U := by
  have h1 := ScalarComplementPermutationNorm.card_mul_relIndex hI
  have h2 := ScalarComplementPermutationNorm.card_mul_relIndex hJ
  rw [h] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem relIndex_lineFixer_eq [Finite L] (i : ZMod q) :
    (lineFixer H H0 U (Eline i)).relIndex U = (lineFixer H H0 U (Eline 0)).relIndex U := by
  have : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  obtain ⟨b, hbB, -, hbE⟩ := hc.exists_gen_B
  have hbN : b ∈ Subgroup.normalizer (U : Set L) := hc.B_le_normalizer_U hbB
  set n : ℕ := (i : ZMod q).val with hn
  have hcast : ((n : ℕ) : ZMod q) = i := by simp [hn, ZMod.natCast_val, ZMod.cast_id]
  have hbn : b ^ n ∈ Subgroup.normalizer (U : Set L) := (Subgroup.normalizer _).pow_mem hbN n
  have hmapE : Subgroup.map (conjQuotientAut H H0 (b ^ n)) (Eline 0) = Eline i := by
    rw [map_conjQuotientAut_pow_Eline hbE n 0, zero_add, hcast]
  refine relIndex_eq_of_natCard_eq (lineFixer_le H H0 U _) (lineFixer_le H H0 U _) ?_
  rw [← map_conj_lineFixer (U := U) hbn hmapE, natCard_map_conj]

noncomputable def axisSystem [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) :
    ScalarAxis.AxisSystem p q W ↥U ↥B :=
  ScalarLineModel.axisSystemOfLines U hc.q_prime.two_le e hc.card_Eline hc.indep_Eline
    hc.iSup_Eline hc.map_U_Eline hc.coprime_p_card_U hc.relIndex_lineFixer_eq
    hc.one_lt_relIndex_lineFixer hc.B_le_normalizer_U hc.card_B hbB hbgen hb

theorem axisSystem_a [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) :
    (hc.axisSystem e hbB hbgen hb).a = (lineFixer H H0 U (Eline 0)).relIndex U := by
  rw [axisSystem, ScalarLineModel.axisSystemOfLines_a]

theorem axisSystem_scalar_act [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) (u : ↥U) :
    (hc.axisSystem e hbB hbgen hb).scalar.act u
      = ChiefFactorFaithfulImage.factorLinearAut p H H0 e (u : L) := by
  rw [axisSystem, ScalarLineModel.axisSystemOfLines_scalar,
    ScalarLineModel.scalarCoordinateSystemOfLines_act]

theorem axisSystem_actB [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) (g : ↥B) :
    (hc.axisSystem e hbB hbgen hb).actB g
      = ChiefFactorFaithfulImage.factorLinearAut p H H0 e (g : L) := by
  rw [axisSystem, ScalarLineModel.axisSystemOfLines_actB, ScalarLineModel.factorLinearActOn_apply]

theorem coe_axisSystem_autB_apply [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1))
    (g : ↥B) (u : ↥U) :
    (((hc.axisSystem e hbB hbgen hb).autB g u : ↥U) : L) = (g : L) * u * (g : L)⁻¹ := by
  rw [axisSystem, ScalarLineModel.axisSystemOfLines_autB,
    ScalarLineModel.coe_autBOfNormalizer_apply]

theorem natCard_K [Finite L] : Nat.card K = Nat.card H * Nat.card U := by
  have h1 := natCard_mul_mul_natCard_inf H U
  rw [hc.disjoint_H_U.eq_bot, Subgroup.card_bot, mul_one] at h1
  rw [← h1, ← hc.sup_H_U, ← Subgroup.normal_mul]
  rfl

theorem exists_mul_eq_of_mem_K {k : L} (hk : k ∈ K) : ∃ h ∈ H, ∃ u ∈ U, h * u = k := by
  rw [← hc.sup_H_U, ← SetLike.mem_coe, Subgroup.normal_mul] at hk
  obtain ⟨h, hh, u, hu, rfl⟩ := hk
  exact ⟨h, hh, u, hu, rfl⟩

theorem exists_mulEquiv_quotient_axisSystem [Finite L] [Fact p.Prime] [NeZero q]
    {W : Type u_1} [AddCommGroup W] [Module (ZMod p) W]
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {b : L} (hbB : b ∈ B) (hbgen : B = Subgroup.zpowers b)
    (hb : ∀ i, Subgroup.map (conjQuotientAut H H0 b) (Eline i) = Eline (i + 1)) :
    ∃ f : (hc.axisSystem e hbB hbgen hb).amb ≃* (L ⧸ H0),
      Subgroup.map (f : (hc.axisSystem e hbB hbgen hb).amb →* L ⧸ H0)
          (hc.axisSystem e hbB hbgen hb).core
        = Subgroup.map (QuotientGroup.mk' H0) K ∧
      (∀ u : ↥U, f (SemidirectProduct.inl (SemidirectProduct.inr u))
        = QuotientGroup.mk (u : L)) ∧
      (∀ v : Multiplicative W, ∃ h ∈ H,
        f (SemidirectProduct.inl (SemidirectProduct.inl v)) = QuotientGroup.mk h) := by
  set S := hc.axisSystem e hbB hbgen hb with hS
  have hact : ∀ u : ↥U, S.scalar.act u
      = ChiefFactorFaithfulImage.factorLinearAut p H H0 e (u : L) :=
    hc.axisSystem_scalar_act e hbB hbgen hb
  have hactB : ∀ g : ↥B, S.actB g = ChiefFactorFaithfulImage.factorLinearAut p H H0 e (g : L) :=
    hc.axisSystem_actB e hbB hbgen hb
  have hautB : ∀ (g : ↥B) (u : ↥U), ((S.autB g u : ↥U) : L) = (g : L) * u * (g : L)⁻¹ :=
    hc.coe_axisSystem_autB_apply e hbB hbgen hb
  let fE : Multiplicative W →* L ⧸ H0 := (quotientInclusion H H0).comp e.symm.toMonoidHom
  have hfE : ∀ (g : L) (v : W),
      fE (Multiplicative.ofAdd (ChiefFactorFaithfulImage.factorLinearAut p H H0 e g v))
        = (QuotientGroup.mk g : L ⧸ H0) * fE (Multiplicative.ofAdd v) * (QuotientGroup.mk g)⁻¹ :=
    fun g v => quotientInclusion_factorLinearAut H H0 e g v
  have hfEH : ∀ h : ↥H, fE (e (QuotientGroup.mk h)) = QuotientGroup.mk (h : L) := fun h => by
    change quotientInclusion H H0 (e.symm (e _)) = _
    rw [MulEquiv.symm_apply_apply, quotientInclusion_mk]
  let fU : ↥U →* L ⧸ H0 := (QuotientGroup.mk' H0).comp U.subtype
  let fB : ↥B →* L ⧸ H0 := (QuotientGroup.mk' H0).comp B.subtype
  let F0 : S.scalar.grp →* L ⧸ H0 := SemidirectProduct.lift fE fU (fun u => by
    refine MonoidHom.ext fun x => ?_
    induction x using Multiplicative.rec with
    | _ v =>
      change fE (S.scalar.mulAutHom u (Multiplicative.ofAdd v)) = _
      rw [S.scalar.mulAutHom_apply, hact, hfE]
      rfl)
  have hF0 : ∀ x : S.scalar.grp, F0 x = fE x.left * fU x.right := fun x => rfl
  let F : S.amb →* L ⧸ H0 := SemidirectProduct.lift F0 fB (fun g => by
    refine MonoidHom.ext fun x => ?_
    change F0 (S.autCore g x)
      = (QuotientGroup.mk (g : L) : L ⧸ H0) * F0 x * (QuotientGroup.mk (g : L))⁻¹
    rw [hF0, hF0, S.autCore_apply_left, S.autCore_apply_right]
    have hU : fU (S.autB g x.right) = (QuotientGroup.mk (g : L) : L ⧸ H0) * fU x.right
        * (QuotientGroup.mk (g : L))⁻¹ := by
      change (QuotientGroup.mk (((S.autB g x.right : ↥U) : L)) : L ⧸ H0) = _
      rw [hautB]; rfl
    have hE : fE (S.mulAutV g x.left) = (QuotientGroup.mk (g : L) : L ⧸ H0) * fE x.left
        * (QuotientGroup.mk (g : L))⁻¹ := by
      induction x.left using Multiplicative.rec with
      | _ v => rw [S.mulAutV_apply, hactB, hfE]
    rw [hU, hE]
    group)
  have hFinl : ∀ x, F (SemidirectProduct.inl x) = F0 x := fun x =>
    SemidirectProduct.lift_inl _ _ _ _
  have hFinr : ∀ g, F (SemidirectProduct.inr g) = fB g := fun x =>
    SemidirectProduct.lift_inr _ _ _ _
  have hF0K : ∀ k ∈ K, ∃ x, F0 x = QuotientGroup.mk k := by
    intro k hk
    obtain ⟨h, hh, u, hu, rfl⟩ := hc.exists_mul_eq_of_mem_K hk
    refine ⟨SemidirectProduct.inl (e (QuotientGroup.mk ⟨h, hh⟩)) *
      SemidirectProduct.inr ⟨u, hu⟩, ?_⟩
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, hfEH]
    rfl
  have hF0K' : ∀ x, ∃ k ∈ K, F0 x = QuotientGroup.mk k := by
    intro x
    obtain ⟨h, hh, hEq⟩ := exists_quotientInclusion_eq H H0 (e.symm x.left)
    refine ⟨h * x.right, K.mul_mem (hc.H_le_K hh) (hc.U_le_K x.right.2), ?_⟩
    rw [hF0]
    change quotientInclusion H H0 (e.symm x.left) * _ = _
    rw [hEq]; rfl
  have hsurj : Function.Surjective F := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ l =>
      obtain ⟨⟨⟨k, hk⟩, ⟨g, hg⟩⟩, hx, -⟩ := hc.isComplement_K_B.existsUnique l
      obtain ⟨y, hy⟩ := hF0K k hk
      refine ⟨SemidirectProduct.inl y * SemidirectProduct.inr ⟨g, hg⟩, ?_⟩
      rw [map_mul, hFinl, hFinr, hy, ← hx]
      rfl
  have hcard : Nat.card S.amb = Nat.card (L ⧸ H0) := by
    rw [SemidirectProduct.card, SemidirectProduct.card]
    have hL : Nat.card L = Nat.card (L ⧸ H0) * Nat.card H0 :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H0
    have hH : Nat.card H = Nat.card (↥H ⧸ H0.subgroupOf H) * Nat.card (H0.subgroupOf H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hH0 : Nat.card (H0.subgroupOf H) = Nat.card H0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.H0_le_H).toEquiv
    have hKB := hc.isComplement_K_B.card_mul_card
    rw [hc.natCard_K] at hKB
    have hpos : 0 < Nat.card H0 := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← hL, ← hKB, hH, hH0, Nat.card_congr e.toEquiv]
    ring
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_surjective_and_card F).2 ⟨hsurj, hcard⟩
  refine ⟨MulEquiv.ofBijective F hbij, ?_, fun u => ?_, fun v => ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := S.mem_core.1 hz
      obtain ⟨k, hk, hkx⟩ := hF0K' x
      exact ⟨k, hk, by
        change _ = F (SemidirectProduct.inl x)
        rw [hFinl, hkx]; rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨x, hx⟩ := hF0K k hk
      exact ⟨SemidirectProduct.inl x, S.inl_mem_core x, by
        change F (SemidirectProduct.inl x) = _
        rw [hFinl, hx]; rfl⟩
  · change F _ = _
    rw [hFinl, SemidirectProduct.lift_inr]; rfl
  · change ∃ h ∈ H, F _ = _
    rw [hFinl, SemidirectProduct.lift_inl]
    exact exists_quotientInclusion_eq H H0 _

theorem exists_axisSystem [Finite L] [Fact p.Prime] :
    ∃ (W : Type _) (_ : AddCommGroup W) (_ : Module (ZMod p) W)
      (Sys : ScalarAxis.AxisSystem p q W ↥U ↥B) (e : Sys.amb ≃* (L ⧸ H0)),
      Sys.a = (lineFixer H H0 U (Eline 0)).relIndex U ∧
      Subgroup.map (e : Sys.amb →* L ⧸ H0) Sys.core
        = Subgroup.map (QuotientGroup.mk' H0) K ∧
      (∀ u : ↥U, e (SemidirectProduct.inl (SemidirectProduct.inr u))
        = QuotientGroup.mk (u : L)) ∧
      (∀ v : Multiplicative W, ∃ h ∈ H,
        e (SemidirectProduct.inl (SemidirectProduct.inl v)) = QuotientGroup.mk h) := by
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  obtain ⟨e⟩ := hc.nonempty_mulEquiv_quotient
  obtain ⟨b, hbB, hbgen, hb⟩ := hc.exists_gen_B
  obtain ⟨f, hcore, hU, hH⟩ := hc.exists_mulEquiv_quotient_axisSystem e hbB hbgen hb
  exact ⟨_, _, _, hc.axisSystem e hbB hbgen hb, f, hc.axisSystem_a e hbB hbgen hb,
    hcore, hU, hH⟩

theorem exists_axisIrrQuotient [Finite L] [Fintype (L ⧸ H0)] :
    ∃ T : Finset (↥(Subgroup.map (QuotientGroup.mk' H0) K) → ℂ),
      (∀ θ ∈ T, θ ∈ Irr ↥(Subgroup.map (QuotientGroup.mk' H0) K)) ∧
      (∀ θ ∈ T, ∀ x : ↥K, (x : L) ∈ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆ →
        θ (quotSubgroupHom H0 K x) = θ 1) ∧
      (∀ θ ∈ T, ∃ x : ↥K, (x : L) ∈ H ∧ θ (quotSubgroupHom H0 K x) ≠ θ 1) ∧
      (∀ θ ∈ T, θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)) ∧
      (∀ θ ∈ T, indClassFun (Subgroup.map (QuotientGroup.mk' H0) K) θ ∈ Irr (L ⧸ H0)) ∧
      (∀ θ ∈ T, ∀ ψ ∈ T, indClassFun (Subgroup.map (QuotientGroup.mk' H0) K) θ
        = indClassFun (Subgroup.map (QuotientGroup.mk' H0) K) ψ → θ = ψ) ∧
      T.card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
        = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U := by
  classical
  have _hfp : Fact p.Prime := ⟨hc.p_prime⟩
  obtain ⟨W, _hW1, _hW2, Sys, e, ha, hKmap, hU, hH⟩ := hc.exists_axisSystem
  have _hfU : Finite ↥U := Subtype.finite
  obtain ⟨T0, hT0mem, hT0inj, hT0card⟩ := Sys.exists_axisIrr_transversal
  refine ⟨T0.image (Sys.transportChar e hKmap), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    exact Sys.transportChar_mem_Irr e hKmap (Sys.axisIrr_subset_Irr (hT0mem θ hθ))
  ·
    intro θ' hθ' x hx
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    have hxU : (x : L) ∈ U :=
      ((Subgroup.commutator_le_self _).trans (lineFixerInf_le H H0 U Eline 0)) hx
    have hxcomm : (x : L) ∈ (⁅U, U⁆ : Subgroup L) :=
      Subgroup.commutator_mono (lineFixerInf_le H H0 U Eline 0)
        (lineFixerInf_le H H0 U Eline 0) hx
    have hucomm : (⟨(x : L), hxU⟩ : ↥U) ∈ commutator ↥U := by
      rw [commutator_eq_subgroupOf_commutator]
      exact Subgroup.mem_subgroupOf.2 hxcomm
    rw [Sys.transportChar_apply e hKmap θ (x := SemidirectProduct.inr ⟨(x : L), hxU⟩) (by
        rw [hU ⟨(x : L), hxU⟩, coe_quotSubgroupHom_apply]),
      Sys.transportChar_one e hKmap]
    exact (Sys.mem_axisIrr.1 (hT0mem θ hθ)).2.1 _ hucomm
  ·
    intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    obtain ⟨v, hvne⟩ := Sys.exists_apply_inl_ne_of_mem_axisIrr (hT0mem θ hθ)
    obtain ⟨h, hhH, hhe⟩ := hH v
    refine ⟨⟨h, hc.H_le_K hhH⟩, hhH, ?_⟩
    rw [Sys.transportChar_apply e hKmap θ (x := SemidirectProduct.inl v) (by
        rw [hhe, coe_quotSubgroupHom_apply]), Sys.transportChar_one e hKmap]
    exact hvne
  ·
    intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    rw [Sys.transportChar_one e hKmap, Sys.apply_one_of_mem_axisIrr (hT0mem θ hθ), ha]
  ·
    intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    exact Sys.indClassFun_transportChar_mem_Irr e hKmap (hT0mem θ hθ)
  ·
    intro θ' hθ' ψ' hψ' hind
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hψ'
    refine congrArg (Sys.transportChar e hKmap) (hT0inj θ hθ ψ hψ ?_)
    rw [← Sys.indClassFun_transportChar_comp e hKmap θ,
      ← Sys.indClassFun_transportChar_comp e hKmap ψ, hind]
  ·
    rw [Finset.card_image_of_injective _ (Sys.transportChar_injective e hKmap), ← ha,
      Subgroup.relIndex, ← commutator_eq_subgroupOf_commutator]
    exact hT0card

theorem exists_axisIrrFinset [Fintype L] :
    ∃ T : Finset (↥K → ℂ),
      (∀ θ ∈ T, θ ∈ irrKer ℂ (H.subgroupOf K)
        ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K)) ∧
      (∀ θ ∈ T, θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)) ∧
      (∀ θ ∈ T, indClassFun K θ ∈ Irr L) ∧
      (∀ θ ∈ T, ∀ ψ ∈ T, indClassFun K θ = indClassFun K ψ → θ = ψ) ∧
      T.card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
        = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U := by
  classical
  have _hfq : Fintype (L ⧸ H0) := Fintype.ofFinite _
  obtain ⟨T, hIrr, hker, hdet, hdeg, hindIrr, hinj, hcard⟩ := hc.exists_axisIrrQuotient
  have hH0K : H0 ≤ K := hc.H0_le_H.trans hc.H_le_K
  have hCK : lineFixerInf H H0 U Eline ≤ K := (lineFixerInf_le H H0 U Eline 0).trans hc.U_le_K
  refine ⟨T.image (deflateChar H0 K), ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    refine mem_irrKer.2 ⟨?_, ?_, ?_⟩
    · rw [← Irr_eq_irrChar]
      exact deflateChar_mem_Irr (hIrr θ hθ)
    · intro x hx
      have hxmem : (x : L) ∈ H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆ :=
        Subgroup.mem_subgroupOf.1 hx
      rw [← SetLike.mem_coe, Subgroup.normal_mul H0
        (⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆ : Subgroup L)] at hxmem
      obtain ⟨h, hh, c, hcm, hhc⟩ := hxmem
      have hcK : c ∈ K :=
        ((Subgroup.commutator_le_self (lineFixerInf H H0 U Eline)).trans hCK) hcm
      have hstep : quotSubgroupHom H0 K x = quotSubgroupHom H0 K ⟨c, hcK⟩ := by
        refine Subtype.ext ?_
        rw [coe_quotSubgroupHom_apply, coe_quotSubgroupHom_apply]
        refine QuotientGroup.eq.2 ?_
        have hxc : (x : L)⁻¹ * c = c⁻¹ * h⁻¹ * (c⁻¹)⁻¹ := by
          rw [show (x : L) = h * c from hhc.symm]; group
        rw [hxc]
        exact ‹H0.Normal›.conj_mem _ (H0.inv_mem hh) _
      rw [mem_charValueKernel, deflateChar_one, deflateChar_apply, hstep]
      exact hker θ hθ ⟨c, hcK⟩ hcm
    · intro hsub
      obtain ⟨x, hxH, hxne⟩ := hdet θ hθ
      refine hxne ?_
      have hx : x ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.2 hxH
      have hval := mem_charValueKernel.1 (hsub (SetLike.mem_coe.2 hx))
      rwa [deflateChar_apply, deflateChar_one] at hval
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    rw [deflateChar_one]
    exact hdeg θ hθ
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    rw [← indClassFun_comp_mk hH0K θ]
    exact FrobeniusInduction.mem_Irr_comp_of_surjective
      (QuotientGroup.mk'_surjective H0) (hindIrr θ hθ)
  · intro θ' hθ' ψ' hψ' hind
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hψ'
    rw [← indClassFun_comp_mk hH0K θ, ← indClassFun_comp_mk hH0K ψ] at hind
    refine congrArg (deflateChar H0 K) (hinj θ hθ ψ hψ (funext fun z => ?_))
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective H0 z
    exact congrFun hind y
  · rw [Finset.card_image_of_injective _ deflateChar_injective]
    exact hcard

theorem exists_axisSubfamily [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline) :
    ∃ Q : Finset (L → ℂ), Q ⊆ S ∧ (∀ γ ∈ Q, γ ∈ Irr L) ∧
      (∀ γ ∈ Q, γ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ)) ∧
      Q.card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
        = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U := by
  classical
  obtain ⟨T, hTker, hTdeg, hTIrr, hTinj, hTcard⟩ := hc.exists_axisIrrFinset
  refine ⟨T.image (indClassFun K), ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hγ
    rw [← Finset.mem_coe, hS]
    exact mem_scalarEqualityFamily.2 ⟨θ, hTker θ hθ, rfl⟩
  · intro γ hγ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hγ
    exact hTIrr θ hθ
  · intro γ hγ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hγ
    have hcardL : (Nat.card L : ℂ) = (K.index : ℂ) * (Nat.card ↥K : ℂ) := by
      rw [← Nat.cast_mul, Subgroup.index_mul_card]
    have hKne : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [indClassFun_one, hcardL, mul_div_assoc, div_self hKne, mul_one, hc.index_eq_q,
      hTdeg θ hθ]
    push_cast
    ring
  · rw [Finset.card_image_of_injOn (fun θ hθ ψ hψ h => hTinj θ hθ ψ hψ h)]
    exact hTcard

omit hc in
theorem inf_subgroupOf_eq (X Y Z : Subgroup L) :
    (X ⊓ Y).subgroupOf Z = X.subgroupOf Z ⊓ Y.subgroupOf Z := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem exists_axisIrrFinset_covering [Fintype L]
    (hinf : ∀ i j : ZMod q, i ≠ j → (lineFixer H H0 U (Eline 0)).relIndex U
      < (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U) :
    ∃ T : Finset (↥K → ℂ),
      (∀ θ ∈ T, θ ∈ Irr ↥K) ∧
      (∀ θ ∈ T, (((H0 ⊔ ⁅U, U⁆).subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ) ∧
      (∀ θ ∈ T, ¬ ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ) ∧
      (∀ θ ∈ T, θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)) ∧
      (∀ θ ∈ T, ∀ ψ ∈ T, indClassFun K θ = indClassFun K ψ → θ = ψ) ∧
      (∀ θ ∈ Irr ↥K,
        (((H0 ⊔ ⁅U, U⁆).subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ →
        ¬ ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ →
        θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) →
        ∃ ψ ∈ T, indClassFun K ψ = indClassFun K θ) ∧
      T.card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
        = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U := by
  classical
  have _hfp : Fact p.Prime := ⟨hc.p_prime⟩
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  have _hfq : Fintype (L ⧸ H0) := Fintype.ofFinite _
  have _hfU : Finite ↥U := Subtype.finite
  obtain ⟨e0⟩ := hc.nonempty_mulEquiv_quotient
  obtain ⟨b, hbB, hbgen, hb⟩ := hc.exists_gen_B
  obtain ⟨f, hKmap, hU, hH⟩ := hc.exists_mulEquiv_quotient_axisSystem e0 hbB hbgen hb
  have ha := hc.axisSystem_a e0 hbB hbgen hb
  have hlc : ∀ k : Fin q, (hc.axisSystem e0 hbB hbgen hb).scalar.lineCentralizer k
      = (lineFixer H H0 U (Eline ((ZMod.finEquiv q) k))).subgroupOf U := fun k => by
    unfold axisSystem
    rw [ScalarLineModel.axisSystemOfLines_scalar]
    exact ScalarLineModel.lineCentralizer_scalarCoordinateSystemOfLines _ _ _ _ _ _ _ _ k
  generalize hc.axisSystem e0 hbB hbgen hb = Sys at f hKmap hU hH ha hlc
  have hinf' : ∀ i j : Fin q, i ≠ j → Sys.a
      < (Sys.scalar.lineCentralizer i ⊓ Sys.scalar.lineCentralizer j).index := by
    intro i j hij
    rw [hlc, hlc, ha, ← inf_subgroupOf_eq]
    exact hinf _ _ fun h => hij ((ZMod.finEquiv q).injective h)
  have hH0K : H0 ≤ K := hc.H0_le_H.trans hc.H_le_K
  obtain ⟨T0, hT0mem, hT0inj, hT0cov, hT0card⟩ := Sys.exists_axisIrr_transversal_covering
  set tr : (Sys.scalar.grp → ℂ) → ↥K → ℂ :=
    fun θ => deflateChar H0 K (Sys.transportChar f hKmap θ) with htr
  have hind : ∀ θ, indClassFun K (tr θ)
      = indClassFun Sys.core (Sys.pushChar θ) ∘ f.symm ∘ QuotientGroup.mk := by
    intro θ
    rw [htr, ← indClassFun_comp_mk hH0K, ← Sys.indClassFun_transportChar_comp f hKmap θ]
    funext y
    simp
  have htrinj : Function.Injective tr := fun θ ψ h =>
    Sys.transportChar_injective f hKmap (deflateChar_injective h)
  have htrone : ∀ θ, tr θ 1 = θ 1 := fun θ => by
    simp only [htr]
    rw [deflateChar_one, Sys.transportChar_one]
  have htrapply : ∀ θ (x : ↥K) (y : Sys.scalar.grp),
      (QuotientGroup.mk (x : L) : L ⧸ H0) = f (SemidirectProduct.inl y) → tr θ x = θ y := by
    intro θ x y h
    simp only [htr]
    rw [deflateChar_apply]
    exact Sys.transportChar_apply f hKmap θ (by rw [coe_quotSubgroupHom_apply]; exact h)
  have hmemU : ∀ u : ↥U, u ∈ commutator ↥U ↔ (u : L) ∈ (⁅U, U⁆ : Subgroup L) := fun u => by
    rw [commutator_eq_subgroupOf_commutator, Subgroup.mem_subgroupOf]
  refine ⟨T0.image tr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ψ hψ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hψ
    exact deflateChar_mem_Irr (Sys.transportChar_mem_Irr f hKmap
      (Sys.axisIrr_subset_Irr (hT0mem θ hθ)))
  ·
    intro ψ hψ x hx
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hψ
    have hxmem : (x : L) ∈ H0 ⊔ ⁅U, U⁆ := Subgroup.mem_subgroupOf.1 hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul H0 (⁅U, U⁆ : Subgroup L)] at hxmem
    obtain ⟨h, hh, c, hcm, hhc⟩ := hxmem
    have hcU : c ∈ U := Subgroup.commutator_le_self U hcm
    have hmk : (QuotientGroup.mk (x : L) : L ⧸ H0)
        = f (SemidirectProduct.inl (SemidirectProduct.inr ⟨c, hcU⟩)) := by
      rw [hU]
      refine QuotientGroup.eq.2 ?_
      have hxc : (x : L)⁻¹ * c = c⁻¹ * h⁻¹ * (c⁻¹)⁻¹ := by
        rw [show (x : L) = h * c from hhc.symm]; group
      rw [hxc]
      exact ‹H0.Normal›.conj_mem _ (H0.inv_mem hh) _
    rw [mem_charValueKernel, htrapply θ x _ hmk, htrone]
    exact (Sys.mem_axisIrr.1 (hT0mem θ hθ)).2.1 _ ((hmemU _).2 hcm)
  ·
    intro ψ hψ hsub
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hψ
    obtain ⟨v, hvne⟩ := Sys.exists_apply_inl_ne_of_mem_axisIrr (hT0mem θ hθ)
    obtain ⟨h, hhH, hhe⟩ := hH v
    have hx : (⟨h, hc.H_le_K hhH⟩ : ↥K) ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.2 hhH
    have hval := mem_charValueKernel.1 (hsub (SetLike.mem_coe.2 hx))
    rw [htrapply θ _ _ hhe.symm, htrone] at hval
    exact hvne hval
  ·
    intro ψ hψ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hψ
    rw [htrone, Sys.apply_one_of_mem_axisIrr (hT0mem θ hθ), ha]
  ·
    intro ψ hψ ψ' hψ' h
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hψ
    obtain ⟨θ', hθ', rfl⟩ := Finset.mem_image.1 hψ'
    rw [hind, hind] at h
    refine congrArg tr (hT0inj θ hθ θ' hθ' (funext fun z => ?_))
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (f z)
    have h2 := congrFun h l
    simp only [Function.comp_apply, hl, MulEquiv.symm_apply_apply] at h2
    exact h2
  ·
    intro θK hθK hker hdet hdeg
    have hmem : θK ∈ irrTrivialOn (quotSubgroupHom H0 K).ker := by
      refine mem_irrTrivialOn.2 ⟨hθK, fun n hn => ?_⟩
      have hn1 : (QuotientGroup.mk (n : L) : L ⧸ H0) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
        rwa [coe_quotSubgroupHom_apply] at this
      have hnH0 : (n : L) ∈ H0 := (QuotientGroup.eq_one_iff _).1 hn1
      exact mem_charValueKernel.1 (hker (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hnH0)))
    obtain ⟨θbar, hθbarIrr, hθbarEq⟩ :=
      (bijOn_comp_of_surjective (surjective_quotSubgroupHom (N := H0) (K := K))).surjOn hmem
    set G := Sys.grpMulEquivOfIso f hKmap with hG
    set θm : Sys.scalar.grp → ℂ := θbar ∘ G with hθm
    have hθmIrr : θm ∈ Irr Sys.scalar.grp := FrobeniusInduction.mem_Irr_comp_mulEquiv hθbarIrr G
    have hvalm : ∀ (k : ↥K) (x : Sys.scalar.grp),
        (QuotientGroup.mk (k : L) : L ⧸ H0) = f (SemidirectProduct.inl x) → θm x = θK k := by
      intro k x hkx
      have hGx : G x = quotSubgroupHom H0 K k := by
        refine Subtype.ext ?_
        rw [hG, Sys.coe_grpMulEquivOfIso_apply, coe_quotSubgroupHom_apply, hkx]
      rw [hθm, Function.comp_apply, hGx, ← hθbarEq]
      rfl
    have hθm1 : θm 1 = θK 1 := hvalm 1 1 (by simp)
    have htransθm : Sys.transportChar f hKmap θm = θbar := by
      funext y
      rw [Sys.transportChar_apply f hKmap θm (x := G.symm y)
        (by rw [← Sys.coe_grpMulEquivOfIso_apply f hKmap, ← hG, MulEquiv.apply_symm_apply]),
        hθm, Function.comp_apply, MulEquiv.apply_symm_apply]
    have htrθm : tr θm = θK := by
      funext k
      simp only [htr]
      rw [deflateChar_apply, htransθm, ← hθbarEq]
      rfl
    have hkerm : ∀ u ∈ commutator ↥U, θm (SemidirectProduct.inr u) = θm 1 := by
      intro u hu
      rw [hvalm ⟨u, hc.U_le_K u.2⟩ _ (hU u).symm, hθm1]
      exact mem_charValueKernel.1 (hker (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_sup_right ((hmemU u).1 hu))))
    have hdetm : ¬ ((Sys.scalar.base : Set Sys.scalar.grp) ⊆ charValueKernel θm) := by
      intro hsub
      refine hdet fun k hk => ?_
      have hkH : (k : L) ∈ H := Subgroup.mem_subgroupOf.1 hk
      have hmkK : (QuotientGroup.mk (k : L) : L ⧸ H0)
          ∈ Subgroup.map (f : Sys.amb →* L ⧸ H0) Sys.core := by
        rw [hKmap]; exact ⟨k, k.2, rfl⟩
      obtain ⟨z, hz, hzk⟩ := hmkK
      obtain ⟨x, rfl⟩ := Sys.mem_core.1 hz
      have hzk' : f (SemidirectProduct.inl x) = QuotientGroup.mk (k : L) := hzk
      obtain ⟨h', hh'H, hh'⟩ := hH x.left
      have hdecomp : f (SemidirectProduct.inl x)
          = QuotientGroup.mk (h' * (x.right : L)) := by
        rw [QuotientGroup.mk_mul, ← hh', ← hU, ← map_mul, ← map_mul,
          SemidirectProduct.inl_left_mul_inr_right]
      have hq := QuotientGroup.eq.1 (hzk'.symm.trans hdecomp)
      have hr : (x.right : L) ∈ H := by
        have h1 : (k : L)⁻¹ * (h' * (x.right : L)) ∈ H := hc.H0_le_H hq
        have h2 : (x.right : L) = h'⁻¹ * (k : L) * ((k : L)⁻¹ * (h' * (x.right : L))) := by
          group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem hh'H) hkH) h1
      have hr1 : x.right = 1 := by
        have := hc.disjoint_H_U.le_bot ⟨hr, x.right.2⟩
        exact Subtype.ext (by simpa using this)
      have hxbase : x ∈ Sys.scalar.base := by
        have hx : SemidirectProduct.inl x.left = x := by
          conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
          rw [hr1, map_one, mul_one]
        rw [← hx]
        exact Sys.scalar.inl_mem_base _
      rw [mem_charValueKernel, ← hvalm k x hzk'.symm, ← hθm1]
      exact mem_charValueKernel.1 (hsub hxbase)
    have hdegm : θm 1 = (Sys.a : ℂ) := by rw [hθm1, hdeg, ha]
    obtain ⟨i, hi⟩ :=
      Sys.scalar.exists_mem_axisWeightFinset_of_apply_one_eq hinf' hθmIrr hdetm hdegm
    have hθmAx : θm ∈ Sys.axisIrr := (Sys.mem_axisIrr_iff).2 ⟨hkerm, i, hi⟩
    obtain ⟨ψ0, hψ0, hψ0eq⟩ := hT0cov θm hθmAx
    refine ⟨tr ψ0, Finset.mem_image_of_mem tr hψ0, ?_⟩
    rw [← htrθm, hind, hind, hψ0eq]
  ·
    rw [Finset.card_image_of_injective _ htrinj, ← ha, Subgroup.relIndex,
      ← commutator_eq_subgroupOf_commutator]
    exact hT0card

theorem exists_degree_dvd_relIndex_lineFixer [Finite L] {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hH0 : ((H0.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ)
    (hdet : ¬ ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = (n : ℂ) ∧ (lineFixer H H0 U (Eline 0)).relIndex U ∣ n := by
  classical
  have habel := hc.isMulCommutative_quotient
  have hHK : H ≤ K := hc.H_le_K
  have hUK : U ≤ K := hc.U_le_K
  set N : Subgroup ↥K := H.subgroupOf K with hNdef
  have _hNn : N.Normal := Subgroup.normal_subgroupOf
  have _hfinK : Finite ↥K := inferInstance
  have _hfinN : Fintype ↥N := Fintype.ofFinite _
  set e : ↥H ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hHK).symm with he
  obtain ⟨d, hdpos, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := N) hθ
  set T := resConstituents N θ with hT
  have hval : ∀ x : ↥N, θ (x : ↥K) = (d : ℂ) * ∑ lam ∈ T, lam x := by
    intro x
    have h := congrFun hres x
    rw [resClassFun_apply] at h
    rw [h]
    simp [Finset.sum_apply]
  have hlin : ∀ lam ∈ T, ∃ μ : (↥H ⧸ H0.subgroupOf H) →* ℂˣ, ∀ h : ↥H,
      ((μ (QuotientGroup.mk h) : ℂ)) = lam (e h) := fun lam hlam =>
    exists_monoidHom_units_of_mem_resConstituents hHK habel hθ hH0 hlam
  have hdeg1 : ∀ lam ∈ T, lam (1 : ↥N) = 1 := by
    intro lam hlam
    obtain ⟨μ, hμ⟩ := hlin lam hlam
    have h1 := hμ 1
    simpa using h1.symm
  have hdegree : θ 1 = ((d * T.card : ℕ) : ℂ) := by
    have h := hval 1
    rw [Subgroup.coe_one, Finset.sum_congr rfl hdeg1] at h
    rw [h]
    push_cast
    simp
  obtain ⟨lam, hlamT⟩ := resConstituents_nonempty (N := N) hθ
  have hone : (1 : ↥N → ℂ) ∉ T := one_notMem_resConstituents hθ hdet
  obtain ⟨x₀, hx₀⟩ : ∃ x : ↥N, lam x ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hone (by rw [show lam = (1 : ↥N → ℂ) from funext fun x => hcon x] at hlamT; exact hlamT)
  obtain ⟨μ, hμ⟩ := hlin lam hlamT
  have hμne : ∃ v, μ v ≠ 1 := by
    refine ⟨QuotientGroup.mk (e.symm x₀), fun hcon => hx₀ ?_⟩
    have h := hμ (e.symm x₀)
    rw [hcon, e.apply_symm_apply] at h
    simpa using h.symm
  obtain ⟨v₀, hv₀⟩ := hμne
  obtain ⟨i, w, hwE, hwne⟩ := exists_line_apply_ne_one (Eline := Eline) hc.iSup_Eline hv₀
  set I := inertiaGroup N lam with hI
  have hNI : N ≤ I := le_inertiaGroup N (Irr_subset_classFun
    (resConstituents_subset_Irr (Finset.mem_coe.2 hlamT)))
  have hkey : (I ⊓ U.subgroupOf K) ≤ (lineFixer H H0 U (Eline i)).subgroupOf K := by
    rintro z ⟨hzI, hzU⟩
    have hzU' : (z : L) ∈ U := Subgroup.mem_subgroupOf.1 hzU
    refine Subgroup.mem_subgroupOf.2 ?_
    refine mem_lineFixer_of_forall_apply_eq hc.p_prime (hc.card_Eline i)
      (fun u hu => hc.map_U_Eline u hu i) ⟨w, hwE, hwne⟩ hzU' ?_
    intro v hv
    induction v using QuotientGroup.induction_on with
    | _ h =>
      have hconj : conjQuotientAut H H0 (z : L) (QuotientGroup.mk h)
          = QuotientGroup.mk (MulAut.conjNormal (z : L) h) := conjQuotientAut_apply_mk H H0 _ h
      refine Units.ext ?_
      rw [hconj, hμ, hμ]
      have hzinert := mem_inertiaGroup_iff_forall_conj.1 hzI (e (MulAut.conjNormal (z : L) h))
      have hcoe : ((MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) : ↥N) : L)
          = ((e h : ↥N) : L) := by
        have h1 := MulAut.conjNormal_apply (H := N) (z⁻¹) (e (MulAut.conjNormal (z : L) h))
        have h2 : (((e (MulAut.conjNormal (z : L) h) : ↥N) : ↥K) : L)
            = (z : L) * (h : L) * (z : L)⁻¹ := by
          rw [he, coe_coe_subgroupOfEquivOfLe_symm, MulAut.conjNormal_apply]
        have h3 : (((e h : ↥N) : ↥K) : L) = (h : L) := by
          rw [he, coe_coe_subgroupOfEquivOfLe_symm]
        rw [show (((MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) : ↥N) : ↥K))
            = (z⁻¹ : ↥K) * ((e (MulAut.conjNormal (z : L) h) : ↥N) : ↥K) * (z⁻¹ : ↥K)⁻¹ from h1]
        push_cast
        rw [h2, h3]
        group
      have heq : MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) = e h :=
        Subtype.ext (Subtype.ext hcoe)
      rw [heq] at hzinert
      exact hzinert.symm
  have hsupN : N ⊔ U.subgroupOf K = ⊤ := by
    rw [hNdef, ← Subgroup.subgroupOf_sup hHK hUK, hc.sup_H_U, Subgroup.subgroupOf_self]
  have hinfN : N ⊓ U.subgroupOf K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.1 hx
    have hbot := hc.disjoint_H_U.le_bot (Subgroup.mem_inf.2
      ⟨Subgroup.mem_subgroupOf.1 hxH, Subgroup.mem_subgroupOf.1 hxU⟩)
    exact Subtype.ext (by simpa using hbot)
  have hcompl : N.IsComplement' (U.subgroupOf K) :=
    (isComplement'_of_sup_eq_top_of_inf_eq_bot hsupN hinfN).symm
  have hrel : (I ⊓ U.subgroupOf K).relIndex (U.subgroupOf K) = I.index :=
    relIndex_inf_eq_index_of_isComplement' hcompl hNI
  have hUiU : (lineFixer H H0 U (Eline i)).subgroupOf K ≤ U.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (lineFixer_le H H0 U (Eline i) (Subgroup.mem_subgroupOf.1 hx))
  have hdvd1 : ((lineFixer H H0 U (Eline i)).subgroupOf K).relIndex (U.subgroupOf K)
      ∣ (I ⊓ U.subgroupOf K).relIndex (U.subgroupOf K) :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _ hkey hUiU)
  have hIcard : I.index = T.card := by
    rw [Subgroup.index_eq_card]
    exact ScalarCoordinateSystem.natCard_quotient_inertiaGroup_eq_card hθ hlamT
  have hai : ((lineFixer H H0 U (Eline i)).subgroupOf K).relIndex (U.subgroupOf K)
      = (lineFixer H H0 U (Eline 0)).relIndex U := by
    rw [Subgroup.relIndex_subgroupOf hUK, hc.relIndex_lineFixer_eq i]
  refine ⟨d * T.card, hdegree, ?_⟩
  rw [← hai]
  exact (hdvd1.trans (by rw [hrel, hIcard])).trans (Dvd.intro_left d rfl)

theorem exists_degree_of_mem_scalarEqualityFamily [Fintype L] {χ : L → ℂ}
    (hχ : χ ∈ scalarEqualityFamily K H H0 U Eline) :
    ∃ d : ℕ, 0 < d ∧ χ 1 = ((q * d : ℕ) : ℂ) ∧
      (lineFixer H H0 U (Eline 0)).relIndex U ∣ d ∧
      d ≤ (lineFixerInf H H0 U Eline).relIndex U := by
  obtain ⟨θ, hθ, hθIrr, hdeg⟩ := hc.exists_mem_irrKer_apply_one_eq hχ
  obtain ⟨-, hker, hdet⟩ := mem_irrKer.1 hθ
  have hCeq := hc.lineFixerInf_eq_chiefActionKer
  obtain ⟨m, hm, hle⟩ := by
    rw [hCeq] at hθ
    exact exists_degree_le_relIndex_chiefActionKer hc.H0_le_H hc.disjoint_H_U hc.sup_H_U
      hc.commutator_H_le_H0 hθIrr (mem_irrKer.1 hθ).2.1
  have hH0 : ((H0.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ := fun x hx =>
    hker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.2
      ((le_sup_left : H0 ≤ H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆)
        (Subgroup.mem_subgroupOf.1 hx))))
  obtain ⟨n, hn, hdvd⟩ := hc.exists_degree_dvd_relIndex_lineFixer hθIrr hH0 hdet
  have hmn : m = n := by exact_mod_cast hm.symm.trans hn
  have hpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [hm, h0]; norm_num) (apply_one_ne_zero_of_mem_Irr hθIrr)
    · exact h0
  exact ⟨m, hpos, by rw [hdeg, hm]; push_cast; ring, hmn ▸ hdvd, hCeq ▸ hle⟩

omit hc in
theorem commutator_le_lineFixer_of_isCyclic {V : Subgroup (↥H ⧸ H0.subgroupOf H)} [IsCyclic ↥V]
    (hmap : ∀ u ∈ U, Subgroup.map (conjQuotientAut H H0 u) V = V) :
    ⁅U, U⁆ ≤ lineFixer H H0 U V := by
  have hV : IsInvariantSubgroup ((conjQuotientAut H H0).comp U.subtype) V :=
    isInvariantSubgroup_iff_forall_map_eq.2 fun u => hmap (u : L) u.2
  set ρ := hV.restrictAut with hρ
  have habel : ∀ x y : MulAut ↥V, x * y = y * x := commute_mulAut_of_isCyclic _
  have key : ∀ x y : ↥U, ρ (x * y * x⁻¹ * y⁻¹) = 1 := by
    intro x y
    simp only [map_mul, map_inv]
    rw [habel (ρ x) (ρ y)]
    group
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [mem_lineFixer, commutatorElement_def]
  refine ⟨mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb), fun v hv => ?_⟩
  have h2 := congrArg (fun e : MulAut ↥V => ((e ⟨v, hv⟩ : ↥V) : ↥H ⧸ H0.subgroupOf H))
    (key ⟨a, ha⟩ ⟨b, hb⟩)
  simp only [hρ, IsInvariantSubgroup.coe_restrictAut_apply, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, MulAut.one_apply] at h2
  simpa using h2

theorem commutator_le_lineFixerInf : ⁅U, U⁆ ≤ lineFixerInf H H0 U Eline :=
  le_lineFixerInf fun i =>
    commutator_le_lineFixer hc.p_prime (hc.card_Eline i) fun u hu => hc.map_U_Eline u hu i

omit hc in
theorem index_map_mk'_subgroupOf {X C : Subgroup L} [(C.subgroupOf U).Normal] (hCX : C ≤ X) :
    ((X.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))).index = X.relIndex U := by
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact Subgroup.subgroupOf_mono U hCX), Subgroup.relIndex]

theorem commutator_le_subgroupOf_lineFixerInf :
    commutator ↥U ≤ (lineFixerInf H H0 U Eline).subgroupOf U := by
  rw [commutator_eq_subgroupOf_commutator]
  exact Subgroup.subgroupOf_mono U hc.commutator_le_lineFixerInf

theorem normal_subgroupOf_lineFixerInf :
    ((lineFixerInf H H0 U Eline).subgroupOf U).Normal :=
  Subgroup.Normal.of_commutator_le ↥U hc.commutator_le_subgroupOf_lineFixerInf

theorem isMulCommutative_quotient_subgroupOf_lineFixerInf
    [((lineFixerInf H H0 U Eline).subgroupOf U).Normal] :
    IsMulCommutative (↥U ⧸ (lineFixerInf H H0 U Eline).subgroupOf U) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2
    hc.commutator_le_subgroupOf_lineFixerInf

omit hc in
theorem lineFixerInf_eq_commutator [Finite L] (hcomm : ⁅U, U⁆ ≤ lineFixerInf H H0 U Eline)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U) :
    lineFixerInf H H0 U Eline = ⁅U, U⁆ := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ hcomm (lineFixerInf_le H H0 U Eline 0)
  rw [hvu] at h
  have hupos : 0 < (lineFixerInf H H0 U Eline).relIndex U :=
    Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
  have h1 : (⁅U, U⁆ : Subgroup L).relIndex (lineFixerInf H H0 U Eline) = 1 := by
    nlinarith [h, hupos]
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hcomm

theorem axisLayer [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline) :
      (lineFixer H H0 U (Eline 0)).relIndex U ∣ p - 1 ∧
      (∀ χ ∈ S, ∃ m : ℕ, 0 < m ∧
        χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U * m : ℕ) : ℂ)) ∧
      (∀ χ ∈ S, χ 1 ≤ ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) ∧
      ∃ Q : Finset (L → ℂ), Q ⊆ S ∧ (∀ γ ∈ Q, γ ∈ Irr L) ∧
        (∀ γ ∈ Q, γ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ)) ∧
        ∃ r : ℕ, 0 < r ∧
          r * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
            = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U ∧ r ≤ Q.card := by
  refine ⟨hc.relIndex_lineFixer_dvd_sub_one' 0, fun χ hχ => ?_, fun χ hχ => ?_, ?_⟩
  ·
    obtain ⟨d, hd0, hdeg, ⟨m, rfl⟩, -⟩ :=
      hc.exists_degree_of_mem_scalarEqualityFamily (hS ▸ Finset.mem_coe.2 hχ)
    exact ⟨m, Nat.pos_of_ne_zero fun h0 => by simp [h0] at hd0, by rw [hdeg]; push_cast; ring⟩
  ·
    obtain ⟨d, -, hdeg, -, hle⟩ :=
      hc.exists_degree_of_mem_scalarEqualityFamily (hS ▸ Finset.mem_coe.2 hχ)
    rw [hdeg]
    exact_mod_cast Nat.mul_le_mul_left q hle
  ·
    obtain ⟨Q, hQS, hQIrr, hQdeg, hcount⟩ := hc.exists_axisSubfamily hS
    refine ⟨Q, hQS, hQIrr, hQdeg, Q.card, ?_, hcount, le_rfl⟩
    have hppos : 0 < p - 1 := by have := hc.three_le_p; omega
    have hvpos : 0 < (⁅U, U⁆ : Subgroup L).relIndex U :=
      Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
    rcases Nat.eq_zero_or_pos Q.card with h0 | h0
    · rw [h0, zero_mul] at hcount
      exact absurd hcount.symm (Nat.mul_ne_zero hppos.ne' hvpos.ne')
    · exact h0

omit hc in
open scoped Pointwise in
theorem relIndex_inf_le_sq [Finite L] {A' B' : Subgroup L} (hAU : A' ≤ U) (hBU : B' ≤ U)
    {a : ℕ} (hA : A'.relIndex U = a) (hB : B'.relIndex U = a) :
    (A' ⊓ B' : Subgroup L).relIndex U ≤ a ^ 2 := by
  set C := A' ⊓ B' with hCdef
  have hCU : C ≤ U := inf_le_left.trans hAU
  have hcA : Nat.card A' * a = Nat.card U := by
    rw [← hA]; exact ScalarComplementPermutationNorm.card_mul_relIndex hAU
  have hcB : Nat.card B' * a = Nat.card U := by
    rw [← hB]; exact ScalarComplementPermutationNorm.card_mul_relIndex hBU
  have hcC : Nat.card C * C.relIndex U = Nat.card U :=
    ScalarComplementPermutationNorm.card_mul_relIndex hCU
  have hprod : Nat.card ((A' : Set L) * (B' : Set L)) * Nat.card C = Nat.card A' * Nat.card B' :=
    natCard_mul_mul_natCard_inf A' B'
  have hsub : ((A' : Set L) * (B' : Set L)) ⊆ (U : Set L) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact U.mul_mem (hAU hx) (hBU hy)
  have hle : Nat.card ((A' : Set L) * (B' : Set L)) ≤ Nat.card U := by
    refine Nat.card_le_card_of_injective
      (fun z : ((A' : Set L) * (B' : Set L)) => (⟨(z : L), hsub z.2⟩ : ↥U)) ?_
    intro x y h
    exact Subtype.ext (congrArg (Subtype.val (p := fun x => x ∈ U)) h)
  have hkey : Nat.card U * Nat.card U
      = Nat.card ((A' : Set L) * (B' : Set L)) * Nat.card C * (a * a) := by
    calc Nat.card U * Nat.card U = (Nat.card A' * a) * (Nat.card B' * a) := by rw [hcA, hcB]
      _ = (Nat.card A' * Nat.card B') * (a * a) := by ring
      _ = _ := by rw [← hprod]
  have hstep : Nat.card U * Nat.card U ≤ Nat.card U * (Nat.card C * (a * a)) := by
    rw [hkey]
    calc Nat.card ((A' : Set L) * (B' : Set L)) * Nat.card C * (a * a)
        ≤ Nat.card U * Nat.card C * (a * a) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
      _ = Nat.card U * (Nat.card C * (a * a)) := by ring
  have h2 : Nat.card U ≤ Nat.card C * (a * a) := Nat.le_of_mul_le_mul_left hstep Nat.card_pos
  rw [← hcC, mul_comm (Nat.card C) (C.relIndex U)] at h2
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have h3 : C.relIndex U ≤ a * a := by nlinarith [h2, hCpos]
  simpa [pow_two] using h3

omit hc in
theorem exists_nsmul_eq (hq : q.Prime) {m : ZMod q} (hm : m ≠ 0) (c : ZMod q) :
    ∃ t : ℕ, t • m = c := by
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨(c * m⁻¹).val, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel_right₀ hm]

theorem lineFixerInf_eq_of_lineFixer_eq {i j : ZMod q} (hij : i ≠ j)
    (heq : lineFixer H H0 U (Eline i) = lineFixer H H0 U (Eline j)) :
    lineFixerInf H H0 U Eline = lineFixer H H0 U (Eline i) := by
  have : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  obtain ⟨b, hbB, -, hbE⟩ := hc.exists_gen_B
  have hbN : b ∈ Subgroup.normalizer (U : Set L) := hc.B_le_normalizer_U hbB
  have hconj : ∀ (n : ℕ) (k : ZMod q),
      Subgroup.map (MulAut.conj (b ^ n) : L →* L) (lineFixer H H0 U (Eline k))
        = lineFixer H H0 U (Eline (k + n)) := fun n k =>
    map_conj_lineFixer ((Subgroup.normalizer _).pow_mem hbN n)
      (map_conjQuotientAut_pow_Eline hbE n k)
  have hshift : ∀ d : ZMod q,
      lineFixer H H0 U (Eline (i + d)) = lineFixer H H0 U (Eline (j + d)) := by
    intro d
    have hcast : ((d.val : ℕ) : ZMod q) = d := by simp [ZMod.natCast_val, ZMod.cast_id]
    have h1 := hconj d.val i
    have h2 := hconj d.val j
    rw [hcast] at h1 h2
    rw [← h1, ← h2, heq]
  set m : ZMod q := j - i with hm
  have hm0 : m ≠ 0 := sub_ne_zero_of_ne (Ne.symm hij)
  have hstep : ∀ d : ZMod q,
      lineFixer H H0 U (Eline (i + (d + m))) = lineFixer H H0 U (Eline (i + d)) := fun d => by
    rw [show i + (d + m) = j + d from by rw [hm]; ring, ← hshift d]
  have hall : ∀ t : ℕ, lineFixer H H0 U (Eline (i + t • m)) = lineFixer H H0 U (Eline i) := by
    intro t
    induction t with
    | zero => simp
    | succ k ih => rw [succ_nsmul, hstep (k • m), ih]
  refine le_antisymm (lineFixerInf_le_lineFixer H H0 U Eline i)
    (le_lineFixerInf fun k => ?_)
  obtain ⟨t, ht⟩ := exists_nsmul_eq hc.q_prime hm0 (k - i)
  have hk : i + t • m = k := by rw [ht]; ring
  rw [← hk, hall t]

theorem inf_lineFixer_eq_of_relIndex_eq [Finite L] {i j : ZMod q} (hij : i ≠ j)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdich : (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U
        = (lineFixer H H0 U (Eline 0)).relIndex U ∨
      (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U
        = (lineFixerInf H H0 U Eline).relIndex U) :
    lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) = lineFixerInf H H0 U Eline := by
  have hCle : lineFixerInf H H0 U Eline
      ≤ lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) :=
    le_inf (lineFixerInf_le_lineFixer H H0 U Eline i) (lineFixerInf_le_lineFixer H H0 U Eline j)
  rcases hdich with hsm | hlg
  ·
    exfalso
    have hpos : 0 < (lineFixer H H0 U (Eline 0)).relIndex U :=
      Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
    have h1 : (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex
        (lineFixer H H0 U (Eline i)) = 1 := by
      have hm := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left (b := lineFixer H H0 U (Eline j)))
        (lineFixer_le H H0 U (Eline i))
      rw [hsm, hc.relIndex_lineFixer_eq i] at hm
      nlinarith [hm, hpos]
    have h2 : (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex
        (lineFixer H H0 U (Eline j)) = 1 := by
      have hm := Subgroup.relIndex_mul_relIndex _ _ _
        (inf_le_right (a := lineFixer H H0 U (Eline i))) (lineFixer_le H H0 U (Eline j))
      rw [hsm, hc.relIndex_lineFixer_eq j] at hm
      nlinarith [hm, hpos]
    have heqi : lineFixer H H0 U (Eline i)
        = lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) :=
      (Subgroup.relIndex_eq_one.1 h1).antisymm inf_le_left
    have heqj : lineFixer H H0 U (Eline j)
        = lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) :=
      (Subgroup.relIndex_eq_one.1 h2).antisymm inf_le_right
    have hCeq := hc.lineFixerInf_eq_of_lineFixer_eq hij (heqi.trans heqj.symm)
    rw [hCeq, hc.relIndex_lineFixer_eq i] at hau
    omega
  ·
    have hm := Subgroup.relIndex_mul_relIndex _ _ _ hCle
      (inf_le_left.trans (lineFixer_le H H0 U (Eline i)))
    rw [hlg] at hm
    have hupos : 0 < (lineFixerInf H H0 U Eline).relIndex U :=
      Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
    have h1 : (lineFixerInf H H0 U Eline).relIndex
        (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)) = 1 := by
      nlinarith [hm, hupos]
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hCle

theorem exists_mem_irrKer_apply_one_eq_relIndex_inf_lineFixer [Fintype L] [K.Normal]
    {i j : ZMod q} (hij : i ≠ j) :
    ∃ θ ∈ irrKer ℂ (H.subgroupOf K)
        ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K),
      θ 1 = (((lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U : ℕ) : ℂ) := by
  classical
  have _hp : Fact p.Prime := ⟨hc.p_prime⟩
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  obtain ⟨e⟩ := hc.nonempty_mulEquiv_quotient
  set C := lineFixerInf H H0 U Eline with hCdef
  set S0 := ScalarLineModel.scalarCoordinateSystemOfLines U hc.q_prime.two_le e hc.card_Eline
    hc.indep_Eline hc.iSup_Eline hc.map_U_Eline hc.coprime_p_card_U with hS0
  have hlc : ∀ k : Fin q, S0.lineCentralizer k
      = (lineFixer H H0 U (Eline ((ZMod.finEquiv q) k))).subgroupOf U := fun k =>
    ScalarLineModel.lineCentralizer_scalarCoordinateSystemOfLines _ _ _ _ _ _ _ _ k
  set N : Subgroup ↥U := C.subgroupOf U with hN
  have _hNn : N.Normal := hc.normal_subgroupOf_lineFixerInf
  have _hab : IsMulCommutative (↥U ⧸ N) := hc.isMulCommutative_quotient_subgroupOf_lineFixerInf
  have hNC : N ≤ S0.totalCentralizer := by
    rw [S0.totalCentralizer_eq_iInf]
    refine le_iInf fun k => ?_
    rw [hlc k]
    exact Subgroup.subgroupOf_mono U (lineFixerInf_le_lineFixer H H0 U Eline _)
  set S := S0.quotient N hNC with hS
  set i' := (ZMod.finEquiv q).symm i with hi'
  set j' := (ZMod.finEquiv q).symm j with hj'
  have hij' : i' ≠ j' := fun h => hij ((ZMod.finEquiv q).symm.injective h)
  obtain ⟨θ0, hθ0, hdet0, hdeg0⟩ := S.exists_mem_Irr_detecting_base_apply_one_eq_index hij'
  have hindex : (S.lineCentralizer i' ⊓ S.lineCentralizer j').index
      = (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U := by
    have hmk : ∀ k : Fin q, (S.lineCentralizer k).comap (QuotientGroup.mk' N)
        = S0.lineCentralizer k := by
      intro k
      rw [hS, ScalarCoordinateSystem.lineCentralizer_quotient]
      refine Subgroup.comap_map_eq_self ?_
      rw [QuotientGroup.ker_mk']
      exact hNC.trans (S0.totalCentralizer_le_lineCentralizer k)
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
      Subgroup.comap_inf, hmk, hmk, hlc, hlc, hi', hj', RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Subgroup.relIndex]
    rfl
  have hHK : H ≤ K := hc.H_le_K
  have hUK : U ≤ K := hc.U_le_K
  set ψ := quotientEquivSemidirectProductOfBot H H0 U (K := K) hc.H0_le_H hc.sup_H_U
    hc.disjoint_H_U with hψ
  have hψinl : ∀ h : ↥H, ψ.symm (QuotientGroup.mk ⟨(h : L), hHK h.2⟩)
      = SemidirectProduct.inl (QuotientGroup.mk h) := by
    intro h
    rw [MulEquiv.symm_apply_eq, hψ, quotientEquivSemidirectProductOfBot_inl]
    rfl
  have hψinr : ∀ u : ↥U, ψ.symm (QuotientGroup.mk ⟨(u : L), hUK u.2⟩)
      = SemidirectProduct.inr u := by
    intro u
    rw [MulEquiv.symm_apply_eq, hψ, quotientEquivSemidirectProductOfBot_inr]
    rfl
  have hcompat : ∀ u : ↥U, (e.toMonoidHom).comp (conjQuotAutRestrict H H0 U u).toMonoidHom
      = (S.mulAutHom (QuotientGroup.mk' N u)).toMonoidHom.comp e.toMonoidHom := by
    intro u
    refine MonoidHom.ext fun y => ?_
    obtain ⟨v, rfl⟩ : ∃ v, e.symm (Multiplicative.ofAdd v) = y :=
      ⟨Multiplicative.toAdd (e y), by simp⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply, conjQuotAutRestrict_apply, QuotientGroup.mk'_apply]
    rw [S.mulAutHom_apply, hS, ScalarCoordinateSystem.quotient_act_mk, hS0,
      ScalarLineModel.scalarCoordinateSystemOfLines_act,
      ChiefFactorFaithfulImage.factorLinearAut_apply',
      ChiefLineDictionary.conjQuotientAut_eq_factorConjAut']
    simp
  set Φ : (↥H ⧸ H0.subgroupOf H) ⋊[conjQuotAutRestrict H H0 U] ↥U →* S.grp :=
    SemidirectProduct.map e.toMonoidHom (QuotientGroup.mk' N) hcompat with hΦ
  set F : ↥K →* S.grp :=
    (Φ.comp ψ.symm.toMonoidHom).comp (QuotientGroup.mk' (H0.subgroupOf K)) with hF
  have hFH : ∀ h : ↥H, F ⟨(h : L), hHK h.2⟩ = SemidirectProduct.inl (e (QuotientGroup.mk h)) := by
    intro h
    simp only [hF, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, hψinl, hΦ, SemidirectProduct.map_inl]
  have hFU : ∀ u : ↥U, F ⟨(u : L), hUK u.2⟩ = SemidirectProduct.inr (QuotientGroup.mk u) := by
    intro u
    simp only [hF, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, hψinr, hΦ, SemidirectProduct.map_inr]
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨y, hy⟩ := e.surjective x.left
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N x.right
    refine ⟨SemidirectProduct.inl y * SemidirectProduct.inr u, ?_⟩
    rw [map_mul, hΦ, SemidirectProduct.map_inl, SemidirectProduct.map_inr]
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    simp only [MulEquiv.coe_toMonoidHom] at hy ⊢
    rw [hy, hu]
  have hFsurj : Function.Surjective F :=
    (hΦsurj.comp ψ.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  have hH0ker : H0.subgroupOf K ≤ F.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hF, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).2 hx, map_one]
  have hCker : C.subgroupOf K ≤ F.ker := by
    intro x hx
    have hxC : (x : L) ∈ C := Subgroup.mem_subgroupOf.1 hx
    have hxU : (x : L) ∈ U := lineFixerInf_le H H0 U Eline 0 hxC
    have hx' : x = ⟨((⟨(x : L), hxU⟩ : ↥U) : L), hUK hxU⟩ := rfl
    rw [MonoidHom.mem_ker, hx', hFU]
    have h1 : (QuotientGroup.mk (⟨(x : L), hxU⟩ : ↥U) : ↥U ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hxC)
    rw [h1, map_one]
  have hCK : ⁅C, C⁆ ≤ K :=
    (Subgroup.commutator_le_self C).trans ((lineFixerInf_le H H0 U Eline 0).trans hUK)
  have hker : (H0 ⊔ ⁅C, C⁆).subgroupOf K ≤ F.ker := by
    rw [Subgroup.subgroupOf_sup (hc.H0_le_H.trans hHK) hCK]
    exact sup_le hH0ker ((Subgroup.subgroupOf_mono K (Subgroup.commutator_le_self C)).trans hCker)
  refine ⟨θ0 ∘ F, mem_irrKer.2 ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← Irr_eq_irrChar]
    exact FrobeniusInduction.mem_Irr_comp_of_surjective hFsurj hθ0
  · intro x hx
    rw [mem_charValueKernel, Function.comp_apply, Function.comp_apply, map_one,
      MonoidHom.mem_ker.1 (hker hx)]
  · intro hsub
    obtain ⟨y, hy, hyne⟩ := Set.not_subset.1 hdet0
    rw [SetLike.mem_coe, S.base_eq_range_inl] at hy
    obtain ⟨v, rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm v)
    refine hyne (mem_charValueKernel.2 ?_)
    have hmem : (⟨(h : L), hHK h.2⟩ : ↥K) ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.2 h.2
    have h1 := mem_charValueKernel.1 (hsub hmem)
    rw [Function.comp_apply, Function.comp_apply, map_one, hFH, hh,
      MulEquiv.apply_symm_apply] at h1
    exact h1
  · rw [Function.comp_apply, map_one, hdeg0, hindex]

theorem relIndex_inf_lineFixer_eq_or [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
    ∀ i j : ZMod q, i ≠ j →
      (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U
          = (lineFixer H H0 U (Eline 0)).relIndex U ∨
        (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U
          = (lineFixerInf H H0 U Eline).relIndex U := by
  intro i j hij
  obtain ⟨θ, hθ, hθ1⟩ :=
    hc.exists_mem_irrKer_apply_one_eq_relIndex_inf_lineFixer hij
  have hχS : indClassFun K θ ∈ S := by
    rw [← Finset.mem_coe, hS]
    exact mem_scalarEqualityFamily.2 ⟨θ, hθ, rfl⟩
  have hχ1 : indClassFun K θ 1
      = ((q * (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U : ℕ) : ℂ) := by
    rw [hc.indClassFun_apply_one_eq, hθ1]
    push_cast
    ring
  have hq : 0 < q := hc.q_prime.pos
  rcases hdeg2 _ hχS with h | h
  · exact Or.inl (Nat.eq_of_mul_eq_mul_left hq (by exact_mod_cast hχ1.symm.trans h))
  · exact Or.inr (Nat.eq_of_mul_eq_mul_left hq (by exact_mod_cast hχ1.symm.trans h))

theorem sup_H_sup_U_B : H ⊔ (U ⊔ B) = ⊤ := by
  rw [← sup_assoc, hc.sup_H_U, hc.sup_K_B]

theorem normal_sup_H0_lineFixerInf : (H0 ⊔ lineFixerInf H H0 U Eline).Normal := by
  rw [hc.lineFixerInf_eq_chiefActionKer]
  exact normal_sup_H0_chiefActionKer H H0 U B hc.B_le_normalizer_U hc.sup_H_sup_U_B

theorem normal_sup_lineFixerInf : (H ⊔ lineFixerInf H H0 U Eline).Normal := by
  rw [hc.lineFixerInf_eq_chiefActionKer]
  exact normal_sup_chiefActionKer H H0 U B hc.B_le_normalizer_U hc.sup_H_sup_U_B hc.H0_le_H

theorem sup_H0_lineFixerInf_le_K : H0 ⊔ lineFixerInf H H0 U Eline ≤ K :=
  sup_le (hc.H0_le_H.trans hc.H_le_K) ((lineFixerInf_le H H0 U Eline 0).trans hc.U_le_K)

theorem sup_H_lineFixerInf_le_K : H ⊔ lineFixerInf H H0 U Eline ≤ K :=
  sup_le hc.H_le_K ((lineFixerInf_le H H0 U Eline 0).trans hc.U_le_K)

theorem relIndex_sup_lineFixerInf [Finite L] :
    (H ⊔ lineFixerInf H H0 U Eline).relIndex K = (lineFixerInf H H0 U Eline).relIndex U ∧
    (H0 ⊔ lineFixerInf H H0 U Eline).relIndex K
      = p ^ q * (lineFixerInf H H0 U Eline).relIndex U := by
  have hMr := ScalarComplementPermutationNorm.card_mul_relIndex hc.sup_H_lineFixerInf_le_K
  have hNr := ScalarComplementPermutationNorm.card_mul_relIndex hc.sup_H0_lineFixerInf_le_K
  have hCU : lineFixerInf H H0 U Eline ≤ U := lineFixerInf_le H H0 U Eline 0
  have hCr := ScalarComplementPermutationNorm.card_mul_relIndex hCU
  have hK := hc.natCard_K
  have hH : Nat.card H = p ^ q * Nat.card H0 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H0.subgroupOf H)
    rw [hc.card_quotient, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.H0_le_H).toEquiv] at h1
    exact h1
  have hdHC : Disjoint H (lineFixerInf H H0 U Eline) := hc.disjoint_H_U.mono_right hCU
  have hM := card_sup_eq_mul_of_disjoint H _ hdHC
  have hN := card_sup_eq_mul_of_disjoint H0 _ (hdHC.mono_left hc.H0_le_H)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hH0pos : 0 < Nat.card H0 := Nat.card_pos
  generalize lineFixerInf H H0 U Eline = C at *
  have hCpos : 0 < Nat.card C := Nat.card_pos
  constructor
  · rw [← hM, hK, ← hCr] at hMr
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hHpos hCpos) ?_
    linarith [hMr]
  · rw [← hN, hK, ← hCr, hH] at hNr
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hH0pos hCpos) ?_
    nlinarith [hNr]

theorem sum_sq_degree_coreLayer [Finite L] :
    ∑ θ ∈ coreLayer K H H0 U Eline, θ 1 ^ 2
      = ((lineFixerInf H H0 U Eline).relIndex U : ℂ) * ((p : ℂ) ^ q - 1) := by
  have h0n : ((H0 ⊔ lineFixerInf H H0 U Eline).subgroupOf K).Normal :=
    hc.normal_sup_H0_lineFixerInf.subgroupOf K
  have h1n : ((H ⊔ lineFixerInf H H0 U Eline).subgroupOf K).Normal :=
    hc.normal_sup_lineFixerInf.subgroupOf K
  obtain ⟨hr1, hr0⟩ := hc.relIndex_sup_lineFixerInf
  rw [coreLayer, sum_sq_degree_irrKer_eq_sub
    (Subgroup.subgroupOf_mono K (sup_le_sup_right hc.H0_le_H _))]
  change (((H0 ⊔ _).relIndex K : ℕ) : ℂ) - ((H ⊔ _).relIndex K : ℕ) = _
  rw [hr0, hr1]; push_cast; ring

theorem mem_coreLayer_iff [Fintype L] {θ : ↥K → ℂ} :
    θ ∈ coreLayer K H H0 U Eline ↔ θ ∈ Irr ↥K ∧
      ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L)
        ⊆ charValueKernel (indClassFun K θ) ∧
      ¬ ((H ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L)
        ⊆ charValueKernel (indClassFun K θ) := by
  have := hc.normal_sup_H0_lineFixerInf
  have := hc.normal_sup_lineFixerInf
  rw [mem_coreLayer]
  exact mem_irrKer_subgroupOf_iff_indClassFun hc.sup_H0_lineFixerInf_le_K
    hc.sup_H_lineFixerInf_le_K

theorem conjClassFun_mem_coreLayer [Finite L] [K.Normal] (t : L) {θ : ↥K → ℂ}
    (hθ : θ ∈ coreLayer K H H0 U Eline) :
    NormalInduction.conjClassFun K t θ ∈ coreLayer K H H0 U Eline := by
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨hIrr, h0, h1⟩ := hc.mem_coreLayer_iff.1 hθ
  refine hc.mem_coreLayer_iff.2 ⟨conjClassFun_mem_Irr K t hIrr, ?_, ?_⟩ <;>
    rw [NormalInducedFamily.indClassFun_conjClassFun]
  · exact h0
  · exact h1

open scoped Classical in
theorem card_filter_indClassFun_eq [Fintype L] [K.Normal] {θ : ↥K → ℂ}
    (hθ : θ ∈ coreLayer K H H0 U Eline) :
    ((coreLayer K H H0 U Eline).filter fun θ' => indClassFun K θ' = indClassFun K θ).card
      = (inertiaGroup K θ).index := by
  have hθIrr := (hc.mem_coreLayer_iff.1 hθ).1
  have hfilter : (((coreLayer K H H0 U Eline).filter
      fun θ' => indClassFun K θ' = indClassFun K θ : Finset (↥K → ℂ)) : Set (↥K → ℂ))
        = NormalInducedFamily.charOrbit K θ := by
    ext θ'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hθ', heq⟩
      obtain ⟨t, ht⟩ := (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun K
        (hc.mem_coreLayer_iff.1 hθ').1 hθIrr).1 heq
      exact NormalInducedFamily.mem_charOrbit.2 ⟨t, ht⟩
    · intro h
      obtain ⟨t, rfl⟩ := NormalInducedFamily.mem_charOrbit.1 h
      exact ⟨hc.conjClassFun_mem_coreLayer t hθ,
        NormalInducedFamily.indClassFun_conjClassFun K t θ⟩
  rw [← NormalInducedFamily.natCard_charOrbit θ, ← hfilter, Nat.card_coe_set_eq,
    Set.ncard_coe_finset]

theorem mem_irrKer_of_mem_coreLayer [Finite L] {θ : ↥K → ℂ}
    (hθ : θ ∈ coreLayer K H H0 U Eline) :
    θ ∈ irrKer ℂ (H.subgroupOf K)
      ((H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆).subgroupOf K) := by
  obtain ⟨hirr, hker0, hnot⟩ := mem_irrKer.1 (mem_coreLayer.1 hθ)
  refine mem_irrKer.2 ⟨hirr, fun x hx => hker0 (Subgroup.subgroupOf_mono K
    (sup_le_sup_left (Subgroup.commutator_le_self _) H0) hx), fun hH => hnot fun x hx => ?_⟩
  have hirr' : θ ∈ Irr ↥K := by rw [← irrChar_eq_Irr]; exact hirr
  have _hN : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  have hT : θ ∈ irrTrivialOn (H.subgroupOf K) :=
    mem_irrTrivialOn.2 ⟨hirr', fun n hn => mem_charValueKernel.1 (hH hn)⟩
  have hxm : (x : L) ∈ H ⊔ lineFixerInf H H0 U Eline := Subgroup.mem_subgroupOf.1 hx
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hxm
  obtain ⟨y, hy, z, hz, hyz⟩ := hxm
  have hzK : z ∈ K := ((lineFixerInf_le H H0 U Eline 0).trans hc.U_le_K) hz
  have hmH : z⁻¹ * y * z ∈ H := by
    simpa using ‹H.Normal›.conj_mem y hy z⁻¹
  have hx' : x = (⟨z, hzK⟩ : ↥K) * ⟨z⁻¹ * y * z, hc.H_le_K hmH⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← hyz]; group
  rw [mem_charValueKernel, hx',
    apply_mul_eq_of_mem_irrTrivialOn hT _ (Subgroup.mem_subgroupOf.2 hmH)]
  have hzmem : (⟨z, hzK⟩ : ↥K) ∈ (H0 ⊔ lineFixerInf H H0 U Eline).subgroupOf K :=
    Subgroup.mem_subgroupOf.2 (le_sup_right (a := H0) (SetLike.mem_coe.1 hz))
  exact mem_charValueKernel.1 (hker0 hzmem)

theorem exists_mem_coreLayer_of_mem [Fintype L] {χ : L → ℂ}
    (hχ : χ ∈ scalarEqualityFamily K H H0 U Eline)
    (hker : ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ) :
    ∃ θ ∈ coreLayer K H H0 U Eline, indClassFun K θ = χ := by
  obtain ⟨θ, hθ, rfl⟩ := mem_scalarEqualityFamily.1 hχ
  obtain ⟨hirr, -, hnot⟩ := mem_irrKer.1 hθ
  have hirr' : θ ∈ Irr ↥K := by rw [← irrChar_eq_Irr]; exact hirr
  refine ⟨θ, hc.mem_coreLayer_iff.2 ⟨hirr', hker, fun h => hnot ?_⟩, rfl⟩
  exact (subset_charValueKernel_indClassFun_iff hc.H_le_K hirr').1
    (fun x hx => h (le_sup_left (b := lineFixerInf H H0 U Eline) hx))

theorem mem_lineFixer_of_mem_inertiaGroup {lam : ↥(H.subgroupOf K) → ℂ}
    {μ : (↥H ⧸ H0.subgroupOf H) →* ℂˣ}
    (hμ : ∀ h : ↥H, ((μ (QuotientGroup.mk h) : ℂ))
      = lam ((Subgroup.subgroupOfEquivOfLe hc.H_le_K).symm h))
    {j : ZMod q} (hne : ∃ w ∈ Eline j, μ w ≠ 1) {z : ↥K}
    (hzI : z ∈ inertiaGroup (H.subgroupOf K) lam) (hzU : (z : L) ∈ U) :
    (z : L) ∈ lineFixer H H0 U (Eline j) := by
  set N : Subgroup ↥K := H.subgroupOf K with hNdef
  set e : ↥H ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hc.H_le_K).symm with he
  refine mem_lineFixer_of_forall_apply_eq hc.p_prime (hc.card_Eline j)
    (fun u hu => hc.map_U_Eline u hu j) hne hzU ?_
  intro v hv
  induction v using QuotientGroup.induction_on with
  | _ h =>
    have hconj : conjQuotientAut H H0 (z : L) (QuotientGroup.mk h)
        = QuotientGroup.mk (MulAut.conjNormal (z : L) h) := conjQuotientAut_apply_mk H H0 _ h
    refine Units.ext ?_
    rw [hconj, hμ, hμ]
    have hzinert := mem_inertiaGroup_iff_forall_conj.1 hzI (e (MulAut.conjNormal (z : L) h))
    have hcoe : ((MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) : ↥N) : L)
        = ((e h : ↥N) : L) := by
      have h1 := MulAut.conjNormal_apply (H := N) (z⁻¹) (e (MulAut.conjNormal (z : L) h))
      have h2 : (((e (MulAut.conjNormal (z : L) h) : ↥N) : ↥K) : L)
          = (z : L) * (h : L) * (z : L)⁻¹ := by
        rw [he, coe_coe_subgroupOfEquivOfLe_symm, MulAut.conjNormal_apply]
      have h3 : (((e h : ↥N) : ↥K) : L) = (h : L) := by
        rw [he, coe_coe_subgroupOfEquivOfLe_symm]
      rw [show (((MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) : ↥N) : ↥K))
          = (z⁻¹ : ↥K) * ((e (MulAut.conjNormal (z : L) h) : ↥N) : ↥K) * (z⁻¹ : ↥K)⁻¹ from h1]
      push_cast
      rw [h2, h3]
      group
    have heq : MulAut.conjNormal (z⁻¹ : ↥K) (e (MulAut.conjNormal (z : L) h)) = e h :=
      Subtype.ext (Subtype.ext hcoe)
    rw [heq] at hzinert
    exact hzinert.symm

theorem apply_one_of_indClassFun_notMem_Irr [Fintype L] [K.Normal] {θ : ↥K → ℂ}
    (hθ : θ ∈ coreLayer K H H0 U Eline) (hred : indClassFun K θ ∉ Irr L) :
    θ 1 = ((lineFixerInf H H0 U Eline).relIndex U : ℂ) := by
  classical
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  have hHK : H ≤ K := hc.H_le_K
  have hUK : U ≤ K := hc.U_le_K
  have hθIrr : θ ∈ Irr ↥K := (hc.mem_coreLayer_iff.1 hθ).1
  obtain ⟨-, hker, hdet⟩ := mem_irrKer.1 (hc.mem_irrKer_of_mem_coreLayer hθ)
  have hH0 : ((H0.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊆ charValueKernel θ := fun x hx =>
    hker (SetLike.mem_coe.2 (Subgroup.mem_subgroupOf.2
      ((le_sup_left : H0 ≤ H0 ⊔ ⁅lineFixerInf H H0 U Eline, lineFixerInf H H0 U Eline⁆)
        (Subgroup.mem_subgroupOf.1 hx))))
  obtain ⟨m, hm, hle⟩ : ∃ m : ℕ, θ 1 = (m : ℂ) ∧ m ≤ (lineFixerInf H H0 U Eline).relIndex U := by
    have hCeq := hc.lineFixerInf_eq_chiefActionKer
    rw [hCeq] at hker ⊢
    exact exists_degree_le_relIndex_chiefActionKer hc.H0_le_H hc.disjoint_H_U hc.sup_H_U
      hc.commutator_H_le_H0 hθIrr hker
  have hIK : inertiaGroup K θ ≠ K := fun h =>
    hred ((FreeCore.mem_Irr_indClassFun_iff K hθIrr).2 h)
  have hKI : K ≤ inertiaGroup K θ := le_inertiaGroup K (Irr_subset_classFun hθIrr)
  have hItop : inertiaGroup K θ = ⊤ := by
    have hmul := Subgroup.relIndex_mul_index hKI
    rw [hc.index_eq_q] at hmul
    rcases hc.q_prime.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h1 | h1
    · exact Subgroup.index_eq_one.1 h1
    · exfalso
      rw [h1] at hmul
      have h2 : K.relIndex (inertiaGroup K θ) = 1 :=
        Nat.eq_of_mul_eq_mul_right hc.q_prime.pos (hmul.trans (one_mul q).symm)
      exact hIK (le_antisymm (Subgroup.relIndex_eq_one.1 h2) hKI)
  obtain ⟨b, hbB, hB, hbE⟩ := hc.exists_gen_B
  have hbq : b ^ q = 1 := by
    have hord : orderOf b = q := by rw [← Nat.card_zpowers, ← hB, hc.card_B]
    rw [← hord]; exact pow_orderOf_eq_one b
  have hbinv : ∀ k : ↥K, θ (MulAut.conjNormal b k) = θ k := by
    have hb' : b⁻¹ ∈ inertiaGroup K θ := by rw [hItop]; exact Subgroup.mem_top _
    intro k
    have h := mem_inertiaGroup_iff_forall_conj.1 hb' k
    rwa [inv_inv] at h
  set N : Subgroup ↥K := H.subgroupOf K with hNdef
  have _hNn : N.Normal := Subgroup.normal_subgroupOf
  have _hfinN : Fintype ↥N := Fintype.ofFinite _
  set e0 : ↥H ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hHK).symm with he0
  set eb : MulAut ↥N := MulAut.congr e0 (MulAut.conjNormal b) with heb
  have heb_apply : ∀ h : ↥H, eb (e0 h) = e0 (MulAut.conjNormal b h) := by
    intro h
    simp [heb, MulAut.congr]
  have hebq : eb ^ q = 1 := by
    rw [heb, ← map_pow, ← map_pow, hbq, map_one, map_one]
  have hcoe : ∀ x : ↥N, ((eb x : ↥N) : ↥K) = MulAut.conjNormal b (x : ↥K) := by
    intro x
    obtain ⟨h, rfl⟩ := e0.surjective x
    rw [heb_apply]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, he0, coe_coe_subgroupOfEquivOfLe_symm,
      coe_coe_subgroupOfEquivOfLe_symm, MulAut.conjNormal_apply]
  have hqK : ¬ q ∣ Nat.card ↥K := (Nat.Prime.coprime_iff_not_dvd hc.q_prime).1 hc.coprime_q_K
  obtain ⟨lam, hlamT, hlamfix⟩ := exists_comp_eq_mem_resConstituents hc.q_prime hqK eb hebq
    hθIrr (fun x => by rw [hcoe, hbinv])
  obtain ⟨d, hdpos, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := N) hθIrr
  set T := resConstituents N θ with hT
  have hval : ∀ x : ↥N, θ (x : ↥K) = (d : ℂ) * ∑ lam ∈ T, lam x := by
    intro x
    have h := congrFun hres x
    rw [resClassFun_apply] at h
    rw [h]
    simp [Finset.sum_apply]
  have habel := hc.isMulCommutative_quotient
  have hlin : ∀ lam ∈ T, ∃ μ : (↥H ⧸ H0.subgroupOf H) →* ℂˣ, ∀ h : ↥H,
      ((μ (QuotientGroup.mk h) : ℂ)) = lam (e0 h) := fun lam hlam =>
    exists_monoidHom_units_of_mem_resConstituents hHK habel hθIrr hH0 hlam
  have hdeg1 : ∀ lam ∈ T, lam (1 : ↥N) = 1 := by
    intro lam hlam
    obtain ⟨μ, hμ⟩ := hlin lam hlam
    have h1 := hμ 1
    simpa using h1.symm
  have hdegree : θ 1 = ((d * T.card : ℕ) : ℂ) := by
    have h := hval 1
    rw [Subgroup.coe_one, Finset.sum_congr rfl hdeg1] at h
    rw [h]
    push_cast
    simp
  have hone : (1 : ↥N → ℂ) ∉ T := one_notMem_resConstituents hθIrr hdet
  obtain ⟨μ, hμ⟩ := hlin lam hlamT
  have hμb : ∀ v, μ (conjQuotientAut H H0 b v) = μ v := by
    intro v
    induction v using QuotientGroup.induction_on with
    | _ h =>
      refine Units.ext ?_
      rw [conjQuotientAut_apply_mk, hμ, hμ, ← heb_apply]
      exact congrFun hlamfix (e0 h)
  have hμbn : ∀ (n : ℕ) v, μ (conjQuotientAut H H0 (b ^ n) v) = μ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [pow_succ', map_mul, MulAut.mul_apply, hμb, ih]
  obtain ⟨x₀, hx₀⟩ : ∃ x : ↥N, lam x ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hone (by rw [show lam = (1 : ↥N → ℂ) from funext fun x => hcon x] at hlamT; exact hlamT)
  have hμne : ∃ v, μ v ≠ 1 := by
    refine ⟨QuotientGroup.mk (e0.symm x₀), fun hcon => hx₀ ?_⟩
    have h := hμ (e0.symm x₀)
    rw [hcon, e0.apply_symm_apply] at h
    simpa using h.symm
  obtain ⟨v₀, hv₀⟩ := hμne
  obtain ⟨i, w, hwE, hwne⟩ := exists_line_apply_ne_one (Eline := Eline) hc.iSup_Eline hv₀
  have hall : ∀ j : ZMod q, ∃ w ∈ Eline j, μ w ≠ 1 := by
    intro j
    refine ⟨conjQuotientAut H H0 (b ^ (j - i).val) w, ?_, by rw [hμbn]; exact hwne⟩
    have hmap := map_conjQuotientAut_pow_Eline hbE (j - i).val i
    rw [ZMod.natCast_zmod_val, show i + (j - i) = j from by ring] at hmap
    rw [← hmap]
    exact ⟨w, hwE, rfl⟩
  set I := inertiaGroup N lam with hI
  have hNI : N ≤ I := le_inertiaGroup N (Irr_subset_classFun
    (resConstituents_subset_Irr (Finset.mem_coe.2 hlamT)))
  have hkey : I ⊓ U.subgroupOf K ≤ (lineFixerInf H H0 U Eline).subgroupOf K := by
    rintro z ⟨hzI, hzU⟩
    refine Subgroup.mem_subgroupOf.2 (mem_lineFixerInf.2 fun j => ?_)
    exact hc.mem_lineFixer_of_mem_inertiaGroup hμ (hall j) hzI (Subgroup.mem_subgroupOf.1 hzU)
  have hsupN : N ⊔ U.subgroupOf K = ⊤ := by
    rw [hNdef, ← Subgroup.subgroupOf_sup hHK hUK, hc.sup_H_U, Subgroup.subgroupOf_self]
  have hinfN : N ⊓ U.subgroupOf K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.1 hx
    have hbot := hc.disjoint_H_U.le_bot (Subgroup.mem_inf.2
      ⟨Subgroup.mem_subgroupOf.1 hxH, Subgroup.mem_subgroupOf.1 hxU⟩)
    exact Subtype.ext (by simpa using hbot)
  have hcompl : N.IsComplement' (U.subgroupOf K) :=
    (isComplement'_of_sup_eq_top_of_inf_eq_bot hsupN hinfN).symm
  have hrel : (I ⊓ U.subgroupOf K).relIndex (U.subgroupOf K) = I.index :=
    relIndex_inf_eq_index_of_isComplement' hcompl hNI
  have hCU' : (lineFixerInf H H0 U Eline).subgroupOf K ≤ U.subgroupOf K :=
    Subgroup.subgroupOf_mono K (lineFixerInf_le H H0 U Eline 0)
  have hdvd1 : ((lineFixerInf H H0 U Eline).subgroupOf K).relIndex (U.subgroupOf K)
      ∣ (I ⊓ U.subgroupOf K).relIndex (U.subgroupOf K) :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _ hkey hCU')
  have hIcard : I.index = T.card := by
    rw [Subgroup.index_eq_card]
    exact ScalarCoordinateSystem.natCard_quotient_inertiaGroup_eq_card hθIrr hlamT
  have hu : ((lineFixerInf H H0 U Eline).subgroupOf K).relIndex (U.subgroupOf K)
      = (lineFixerInf H H0 U Eline).relIndex U := Subgroup.relIndex_subgroupOf hUK
  have hudvd : (lineFixerInf H H0 U Eline).relIndex U ∣ d * T.card := by
    rw [← hu]
    exact (hdvd1.trans (by rw [hrel, hIcard])).trans (Dvd.intro_left d rfl)
  have hTpos : 0 < T.card := Finset.card_pos.2 ⟨lam, hlamT⟩
  have hn : d * T.card = m := by exact_mod_cast hdegree.symm.trans hm
  have hge := Nat.le_of_dvd (Nat.mul_pos hdpos hTpos) hudvd
  rw [hm]
  exact_mod_cast le_antisymm hle (hn ▸ hge)

omit hc in
theorem notMem_Irr_indClassFun_iff_mem_inertiaGroup [Fintype L] [K.Normal]
    (hKB : K.IsComplement' B) {b : L} (hbB : b ∈ B) (hcardB : Nat.card B = q) (hq : q.Prime)
    (hb1 : b ≠ 1) {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) :
    indClassFun K θ ∉ Irr L ↔ b ∈ inertiaGroup K θ := by
  have hKle : K ≤ inertiaGroup K θ := le_inertiaGroup K (Irr_subset_classFun hθ)
  have hbK : b ∉ K := fun hbK => hb1 (Subgroup.disjoint_def.1 hKB.disjoint hbK hbB)
  rw [FreeCore.mem_Irr_indClassFun_iff K hθ]
  constructor
  · intro hne
    obtain ⟨g, hg, hgK⟩ : ∃ g ∈ inertiaGroup K θ, g ∉ K := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon hKle)
    obtain ⟨⟨⟨k, hk⟩, ⟨c, hc⟩⟩, hx, -⟩ := hKB.existsUnique g
    have hx' : k * c = g := hx
    have hcI : c ∈ inertiaGroup K θ := by
      have : c = k⁻¹ * g := by rw [← hx']; group
      rw [this]
      exact (inertiaGroup K θ).mul_mem ((inertiaGroup K θ).inv_mem (hKle hk)) hg
    have hc1 : (⟨c, hc⟩ : B) ≠ 1 := by
      intro h
      have : c = 1 := congrArg Subtype.val h
      subst this
      exact hgK (by rw [← hx', mul_one]; exact hk)
    have htop := zpowers_eq_top_of_ne_one hq hcardB hc1
    have hbmem : (⟨b, hbB⟩ : B) ∈ Subgroup.zpowers (⟨c, hc⟩ : B) := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hbmem
    have hbn : c ^ n = b := by simpa using congrArg Subtype.val hn
    rw [← hbn]
    exact (inertiaGroup K θ).zpow_mem hcI n
  · intro hb heq
    exact hbK (heq ▸ hb)

theorem exists_scalarInvariantSystem [Finite L] [K.Normal] [Fact p.Prime] [Fact q.Prime] :
    ∃ (W : Type u_1) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (D : Type u_1) (_ : Group D)
      (SI : ScalarInvariantSystem p q W D) (F : ↥K →* SI.grp),
      Function.Surjective F ∧
      F.ker = (H0 ⊔ lineFixerInf H H0 U Eline).subgroupOf K ∧
      (∀ x : ↥K, (x : L) ∈ H → F x ∈ SI.base) ∧
      (∀ y ∈ SI.base, ∃ x : ↥K, (x : L) ∈ H ∧ F x = y) ∧
      ∃ b ∈ B, B = Subgroup.zpowers b ∧
        ∀ k : ↥K, F (MulAut.conjNormal b k) = SI.semiAut (F k) := by
  obtain ⟨e⟩ := hc.nonempty_mulEquiv_quotient
  obtain ⟨b, hbB, hbgen, hb⟩ := hc.exists_gen_B
  have _hq : NeZero q := ⟨hc.q_prime.pos.ne'⟩
  have _hsolv := hc.solvable
  set C := lineFixerInf H H0 U Eline with hCdef
  set S0 := ScalarLineModel.scalarCoordinateSystemOfLines U hc.q_prime.two_le e hc.card_Eline
    hc.indep_Eline hc.iSup_Eline hc.map_U_Eline hc.coprime_p_card_U with hS0
  have hlc : ∀ k : Fin q, S0.lineCentralizer k
      = (lineFixer H H0 U (Eline ((ZMod.finEquiv q) k))).subgroupOf U := fun k =>
    ScalarLineModel.lineCentralizer_scalarCoordinateSystemOfLines _ _ _ _ _ _ _ _ k
  set N : Subgroup ↥U := C.subgroupOf U with hN
  have _hNn : N.Normal := hc.normal_subgroupOf_lineFixerInf
  have hNC : N ≤ S0.totalCentralizer := by
    rw [S0.totalCentralizer_eq_iInf]
    refine le_iInf fun k => ?_
    rw [hlc k]
    exact Subgroup.subgroupOf_mono U (lineFixerInf_le_lineFixer H H0 U Eline _)
  set S := S0.quotient N hNC with hS
  have hHK : H ≤ K := hc.H_le_K
  have hUK : U ≤ K := hc.U_le_K
  set ψ := quotientEquivSemidirectProductOfBot H H0 U (K := K) hc.H0_le_H hc.sup_H_U
    hc.disjoint_H_U with hψ
  have hψinl : ∀ h : ↥H, ψ.symm (QuotientGroup.mk ⟨(h : L), hHK h.2⟩)
      = SemidirectProduct.inl (QuotientGroup.mk h) := by
    intro h
    rw [MulEquiv.symm_apply_eq, hψ, quotientEquivSemidirectProductOfBot_inl]
    rfl
  have hψinr : ∀ u : ↥U, ψ.symm (QuotientGroup.mk ⟨(u : L), hUK u.2⟩)
      = SemidirectProduct.inr u := by
    intro u
    rw [MulEquiv.symm_apply_eq, hψ, quotientEquivSemidirectProductOfBot_inr]
    rfl
  have hcompat : ∀ u : ↥U, (e.toMonoidHom).comp (conjQuotAutRestrict H H0 U u).toMonoidHom
      = (S.mulAutHom (QuotientGroup.mk' N u)).toMonoidHom.comp e.toMonoidHom := by
    intro u
    refine MonoidHom.ext fun y => ?_
    obtain ⟨v, rfl⟩ : ∃ v, e.symm (Multiplicative.ofAdd v) = y :=
      ⟨Multiplicative.toAdd (e y), by simp⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply, conjQuotAutRestrict_apply, QuotientGroup.mk'_apply]
    rw [S.mulAutHom_apply, hS, ScalarCoordinateSystem.quotient_act_mk, hS0,
      ScalarLineModel.scalarCoordinateSystemOfLines_act,
      ChiefFactorFaithfulImage.factorLinearAut_apply',
      ChiefLineDictionary.conjQuotientAut_eq_factorConjAut']
    simp
  set Φ : (↥H ⧸ H0.subgroupOf H) ⋊[conjQuotAutRestrict H H0 U] ↥U →* S.grp :=
    SemidirectProduct.map e.toMonoidHom (QuotientGroup.mk' N) hcompat with hΦ
  set F : ↥K →* S.grp :=
    (Φ.comp ψ.symm.toMonoidHom).comp (QuotientGroup.mk' (H0.subgroupOf K)) with hF
  have hFH : ∀ h : ↥H, F ⟨(h : L), hHK h.2⟩ = SemidirectProduct.inl (e (QuotientGroup.mk h)) := by
    intro h
    simp only [hF, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, hψinl, hΦ, SemidirectProduct.map_inl]
  have hFU : ∀ u : ↥U, F ⟨(u : L), hUK u.2⟩ = SemidirectProduct.inr (QuotientGroup.mk u) := by
    intro u
    simp only [hF, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, hψinr, hΦ, SemidirectProduct.map_inr]
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨y, hy⟩ := e.surjective x.left
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N x.right
    refine ⟨SemidirectProduct.inl y * SemidirectProduct.inr u, ?_⟩
    rw [map_mul, hΦ, SemidirectProduct.map_inl, SemidirectProduct.map_inr]
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    simp only [MulEquiv.coe_toMonoidHom] at hy ⊢
    rw [hy, hu]
  have hFsurj : Function.Surjective F :=
    (hΦsurj.comp ψ.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  have hH0ker : H0.subgroupOf K ≤ F.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hF, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).2 hx, map_one]
  have hCker : C.subgroupOf K ≤ F.ker := by
    intro x hx
    have hxC : (x : L) ∈ C := Subgroup.mem_subgroupOf.1 hx
    have hxU : (x : L) ∈ U := lineFixerInf_le H H0 U Eline 0 hxC
    have hx' : x = ⟨((⟨(x : L), hxU⟩ : ↥U) : L), hUK hxU⟩ := rfl
    rw [MonoidHom.mem_ker, hx', hFU]
    have h1 : (QuotientGroup.mk (⟨(x : L), hxU⟩ : ↥U) : ↥U ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hxC)
    rw [h1, map_one]
  have hker_ge : (H0 ⊔ C).subgroupOf K ≤ F.ker := by
    rw [Subgroup.subgroupOf_sup (hc.H0_le_H.trans hHK) ((lineFixerInf_le H H0 U Eline 0).trans hUK)]
    exact sup_le hH0ker hCker
  have hker : F.ker = (H0 ⊔ C).subgroupOf K := by
    have hcardW : Nat.card (Multiplicative (ULift.{u_1} (Fin q → ZMod p))) = p ^ q := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_ulift, Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hidx : F.ker.index = p ^ q * C.relIndex U := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hFsurj, Subgroup.card_top,
        SemidirectProduct.card, hcardW, ← Subgroup.index_eq_card]
      rfl
    have h2 := Subgroup.relIndex_mul_index hker_ge
    rw [hidx, ← Subgroup.relIndex, (hc.relIndex_sup_lineFixerInf).2] at h2
    have hpos : 0 < p ^ q * C.relIndex U :=
      Nat.mul_pos (pow_pos hc.p_prime.pos _) (Nat.pos_of_ne_zero (relIndex_ne_zero _ _))
    have h3 : ((H0 ⊔ C).subgroupOf K).relIndex F.ker = 1 := by
      nlinarith
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hker_ge
  set ρ := ScalarLineModel.autBOfNormalizer U hc.B_le_normalizer_U with hρ
  have hNinv : IsInvariantSubgroup ρ N := by
    refine isInvariantSubgroup_of_forall fun g u hu => ?_
    rw [hN, Subgroup.mem_subgroupOf] at hu ⊢
    rw [hρ, ScalarLineModel.coe_autBOfNormalizer_apply]
    rw [hCdef, hc.lineFixerInf_eq_chiefActionKer] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.1
      (le_normalizer_chiefActionKer H H0 U hc.B_le_normalizer_U g.2) u).1 hu
  set bB : ↥B := ⟨b, hbB⟩ with hbBdef
  have hbBq : bB ^ q = 1 := by
    have h := pow_card_eq_one' (x := bB)
    rwa [hc.card_B] at h
  have hbq : b ^ q = 1 := by
    have h := congrArg Subtype.val hbBq
    simpa [hbBdef] using h
  set σ := hNinv.quotientAut bB with hσ
  set β := ChiefFactorFaithfulImage.factorLinearAut p H H0 e b with hβ
  have hzp : Subgroup.zpowers bB = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hbgen ▸ x.2 : (x : L) ∈ Subgroup.zpowers b)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  have hfree : MonoidHom.FixedPointFree (ρ bB : ↥U → ↥U) := by
    intro u hu
    have hu' : b * (u : L) * b⁻¹ = u := by
      have h := congrArg Subtype.val hu
      rwa [hρ, ScalarLineModel.coe_autBOfNormalizer_apply] at h
    have hcomm : Commute b (u : L) := by
      change b * (u : L) = u * b
      calc b * (u : L) = b * (u : L) * b⁻¹ * b := by group
        _ = u * b := by rw [hu']
    have hmem : (u : L) ∈ U ⊓ Subgroup.centralizer (B : Set L) := by
      refine ⟨u.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [hbgen] at hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (hcomm.zpow_left n).eq
    rw [hc.inf_centralizer_U_B, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let SI : ScalarInvariantSystem p q (ULift.{u_1} (Fin q → ZMod p)) (↥U ⧸ N) :=
    { toScalarCoordinateSystem := S
      not_dvd_card_units := by
        refine (Nat.Prime.coprime_iff_not_dvd hc.q_prime).1 ?_
        exact hc.coprime_q_K.coprime_dvd_right
          ((Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_dvd_of_le hc.U_le_K))
      ne_prime := hc.p_ne_q.symm
      a := (lineFixer H H0 U (Eline 0)).relIndex U
      index_lineCentralizer_eq := by
        intro i
        rw [hS, ScalarCoordinateSystem.lineCentralizer_quotient, hlc,
          IsScalarCoreConfig.index_map_mk'_subgroupOf (lineFixerInf_le_lineFixer H H0 U Eline _),
          hc.relIndex_lineFixer_eq]
      one_lt_a := hc.one_lt_relIndex_lineFixer
      lineAut := β
      unitAut := σ
      act_unitAut := by
        intro u
        induction u using QuotientGroup.induction_on with
        | _ u =>
          rw [hσ, IsInvariantSubgroup.quotientAut_mk, hS, ScalarCoordinateSystem.quotient_act_mk,
            ScalarCoordinateSystem.quotient_act_mk, hS0,
            ScalarLineModel.scalarCoordinateSystemOfLines_act,
            ScalarLineModel.scalarCoordinateSystemOfLines_act, hρ,
            ScalarLineModel.coe_autBOfNormalizer_apply, map_mul, map_mul, map_inv]
      map_lineAut := by
        intro i
        rw [hS, ScalarCoordinateSystem.quotient_line, hS0,
          ScalarLineModel.scalarCoordinateSystemOfLines_line,
          ScalarLineModel.scalarCoordinateSystemOfLines_line, hβ,
          ChiefLineDictionary.map_subgroupOrderIsoSubmodule,
          ← ChiefLineDictionary.conjQuotientAut_eq_factorConjAut', hb, map_add, map_one]
      lineAut_pow := by rw [hβ, ← map_pow, hbq, map_one]
      unitAut_pow := by rw [hσ, ← map_pow, hbBq, map_one]
      unitAut_free := fun u hu =>
        fixedPointFree_quotientAut hc.q_prime hc.card_B hzp hfree hNinv u hu }
  refine ⟨_, _, _, _, _, SI, F, hFsurj, hker, ?_, ?_, b, hbB, hbgen, ?_⟩
  · intro x hx
    have hx' : x = ⟨((⟨(x : L), hx⟩ : ↥H) : L), hHK hx⟩ := rfl
    rw [hx', hFH]
    exact ScalarCoordinateSystem.inl_mem_base _ _
  · intro y hy
    rw [ScalarCoordinateSystem.base_eq_range_inl] at hy
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e.symm w)
    refine ⟨⟨(h : L), hHK h.2⟩, h.2, ?_⟩
    rw [hFH, hh, MulEquiv.apply_symm_apply]
  ·
    intro k
    obtain ⟨h, hh, u, hu, hk⟩ := hc.exists_mul_eq_of_mem_K k.2
    have hk' : k = ⟨((⟨h, hh⟩ : ↥H) : L), hHK hh⟩ * ⟨((⟨u, hu⟩ : ↥U) : L), hUK hu⟩ :=
      Subtype.ext hk.symm
    have hbh : MulAut.conjNormal b (⟨((⟨h, hh⟩ : ↥H) : L), hHK hh⟩ : ↥K)
        = ⟨((MulAut.conjNormal b (⟨h, hh⟩ : ↥H) : ↥H) : L), hHK (Subtype.prop _)⟩ := by
      ext; simp
    have hbu : MulAut.conjNormal b (⟨((⟨u, hu⟩ : ↥U) : L), hUK hu⟩ : ↥K)
        = ⟨((ρ bB ⟨u, hu⟩ : ↥U) : L), hUK (Subtype.prop _)⟩ := by
      ext; simp [hρ, ScalarLineModel.coe_autBOfNormalizer_apply, hbBdef]
    rw [hk', map_mul, map_mul, map_mul, map_mul, hbh, hbu, hFH, hFU, hFH, hFU]
    congr 1
    · have key : ∀ y, SI.lineAutMul (e y) = e (ChiefFactorLinearAction.factorConjAut H H0 b y) := by
        intro y
        have h1 := SI.lineAutMul_apply (Multiplicative.toAdd (e y))
        rw [ofAdd_toAdd] at h1
        rw [h1]
        change Multiplicative.ofAdd (β (Multiplicative.toAdd (e y))) = _
        rw [hβ, ChiefFactorFaithfulImage.factorLinearAut_apply, ofAdd_toAdd]
      rw [ScalarInvariantSystem.semiAut_inl, key, ChiefFactorLinearAction.factorConjAut_mk]
    · rw [ScalarInvariantSystem.semiAut_inr]
      congr 1
      exact (hNinv.quotientAut_mk bB _).symm

open scoped Classical in
theorem card_filter_indClassFun_notMem_Irr [Fintype L] [K.Normal] :
    ((coreLayer K H H0 U Eline).filter fun θ => indClassFun K θ ∉ Irr L).card = p - 1 := by
  have _hp : Fact p.Prime := ⟨hc.p_prime⟩
  have _hq : Fact q.Prime := ⟨hc.q_prime⟩
  obtain ⟨W, _, _, D, _, SI, F, hFsurj, hker, hFH, hbase, b, hbB, hbgen, hFb⟩ :=
    hc.exists_scalarInvariantSystem
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot] at hbgen
    have h := hc.card_B
    rw [hbgen, Subgroup.card_bot] at h
    exact hc.q_prime.one_lt.ne h
  have hFbinv : ∀ k : ↥K, F (MulAut.conjNormal b⁻¹ k) = SI.semiAut.symm (F k) := by
    intro k
    rw [MulEquiv.eq_symm_apply, ← hFb, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply]
  set C := lineFixerInf H H0 U Eline with hCdef
  have hCK : C ≤ K := (lineFixerInf_le H H0 U Eline 0).trans hc.U_le_K
  have hHC : (H ⊔ C).subgroupOf K ≤ SI.base.comap F := by
    rw [Subgroup.subgroupOf_sup hc.H_le_K hCK]
    refine sup_le (fun x hx => hFH x (Subgroup.mem_subgroupOf.1 hx)) (fun x hx => ?_)
    have : x ∈ F.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx))
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 this]
    exact SI.base.one_mem
  rw [← SI.card_invIrrDetectBase]
  symm
  refine Finset.card_bij (fun θ' _ => θ' ∘ F) ?_ ?_ ?_
  · intro θ' hθ'
    obtain ⟨hθT, hinv⟩ := SI.mem_invIrrDetectBase.1 hθ'
    obtain ⟨hθI, hdet⟩ := SI.mem_irrKerFinset_base_bot.1 hθT
    have hIrr : θ' ∘ F ∈ Irr ↥K := FrobeniusInduction.mem_Irr_comp_of_surjective hFsurj hθI
    refine Finset.mem_filter.2 ⟨mem_coreLayer.2 (mem_irrKer.2 ⟨?_, ?_, ?_⟩), ?_⟩
    · rw [irrChar_eq_Irr]; exact hIrr
    · intro x hx
      rw [← hker] at hx
      rw [mem_charValueKernel, Function.comp_apply, Function.comp_apply, MonoidHom.mem_ker.1 hx,
        map_one]
    · intro hsub
      obtain ⟨y, hy, hyne⟩ := Set.not_subset.1 hdet
      obtain ⟨x, hxH, rfl⟩ := hbase y hy
      refine hyne (mem_charValueKernel.2 ?_)
      have hmem : x ∈ (H ⊔ C).subgroupOf K :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hxH)
      have h1 := mem_charValueKernel.1 (hsub hmem)
      rwa [Function.comp_apply, Function.comp_apply, map_one] at h1
    · refine (notMem_Irr_indClassFun_iff_mem_inertiaGroup hc.isComplement_K_B hbB hc.card_B
        hc.q_prime hb1 hIrr).2 ?_
      refine mem_inertiaGroup_iff_forall_conj.2 fun k => ?_
      simp only [Function.comp_apply]
      rw [hFbinv, ← hinv (SI.semiAut.symm (F k)), MulEquiv.apply_symm_apply]
  · intro θ₁ _ θ₂ _ h
    exact hFsurj.injective_comp_right h
  · intro θ hθ
    obtain ⟨hθC, hred⟩ := Finset.mem_filter.1 hθ
    obtain ⟨hθI, hker0, hnot⟩ := mem_irrKer.1 (mem_coreLayer.1 hθC)
    rw [irrChar_eq_Irr] at hθI
    have hT : θ ∈ irrTrivialOn F.ker := by
      rw [hker]
      exact mem_irrTrivialOn.2 ⟨hθI, fun n hn => mem_charValueKernel.1 (hker0 hn)⟩
    obtain ⟨ψ, hψ, hψθ⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn hT
    set E := QuotientGroup.quotientKerEquivOfSurjective F hFsurj with hE
    set θ' : SI.grp → ℂ := ψ ∘ E.symm with hθ'
    have hθ'F : θ' ∘ F = θ := by
      rw [← hψθ]
      funext x
      simp only [Function.comp_apply, hθ']
      congr 1
      rw [MulEquiv.symm_apply_eq]
      rfl
    have hθ'I : θ' ∈ Irr SI.grp := FrobeniusInduction.mem_Irr_comp_mulEquiv hψ E.symm
    refine ⟨θ', SI.mem_invIrrDetectBase.2 ⟨SI.mem_irrKerFinset_base_bot.2 ⟨hθ'I, ?_⟩, ?_⟩, hθ'F⟩
    · intro hsub
      refine hnot fun x hx => ?_
      have h1 := mem_charValueKernel.1 (hsub (hHC hx))
      rw [mem_charValueKernel, ← hθ'F, Function.comp_apply, Function.comp_apply, map_one]
      exact h1
    · have hbI := (notMem_Irr_indClassFun_iff_mem_inertiaGroup hc.isComplement_K_B hbB hc.card_B
        hc.q_prime hb1 hθI).1 hred
      have hconj := mem_inertiaGroup_iff_forall_conj.1 hbI
      intro y
      obtain ⟨k, rfl⟩ := hFsurj y
      have h2 := hconj (MulAut.conjNormal b k)
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
      rw [← hFb]
      change (θ' ∘ F) _ = (θ' ∘ F) k
      rw [hθ'F]
      exact h2.symm

theorem card_smallLayer_mul_sq [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
    (smallLayer H H0 U Eline S).card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
      = (p - 1) * (lineFixerInf H H0 U Eline).relIndex U := by
  classical
  have hinf : ∀ i j : ZMod q, i ≠ j → (lineFixer H H0 U (Eline 0)).relIndex U
      < (lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j)).relIndex U := by
    intro i j hij
    rw [hc.inf_lineFixer_eq_of_relIndex_eq hij hau
      (hc.relIndex_inf_lineFixer_eq_or hS h2a hvu hau hdeg2 i j hij)]
    exact hau
  have hCU : lineFixerInf H H0 U Eline = ⁅U, U⁆ :=
    lineFixerInf_eq_commutator hc.commutator_le_lineFixerInf hvu
  have hN : (H0 ⊔ ⁅U, U⁆ : Subgroup L).Normal := hCU ▸ hc.normal_sup_H0_lineFixerInf
  have hNK : H0 ⊔ ⁅U, U⁆ ≤ K := hCU ▸ hc.sup_H0_lineFixerInf_le_K
  have hq : 0 < q := hc.q_prime.pos
  obtain ⟨T, hTIrr, hTker, hTdet, hTdeg, hTinj, hTcov, hTcard⟩ :=
    hc.exists_axisIrrFinset_covering hinf
  have himage : smallLayer H H0 U Eline S = T.image (indClassFun K) := by
    ext χ
    rw [mem_smallLayer, Finset.mem_image]
    constructor
    · rintro ⟨hχS, hker, hdeg⟩
      obtain ⟨θ, hθT, rfl⟩ := hc.exists_mem_coreLayer_of_mem (hS ▸ Finset.mem_coe.2 hχS) hker
      have hθIrr := (hc.mem_coreLayer_iff.1 hθT).1
      have hθker : (((H0 ⊔ ⁅U, U⁆).subgroupOf K : Subgroup ↥K) : Set ↥K)
          ⊆ charValueKernel θ := by
        rw [hCU] at hker
        exact (subset_charValueKernel_indClassFun_iff hNK hθIrr).1 hker
      have hθdet := (mem_irrKer.1 (hc.mem_irrKer_of_mem_coreLayer hθT)).2.2
      have hθdeg : θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) := by
        rw [hc.indClassFun_apply_one_eq] at hdeg
        push_cast at hdeg
        exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hq.ne') hdeg
      exact hTcov θ hθIrr hθker hθdet hθdeg
    · rintro ⟨ψ, hψT, rfl⟩
      have hψIrr := hTIrr ψ hψT
      refine ⟨?_, ?_, ?_⟩
      · rw [← Finset.mem_coe, hS]
        refine mem_scalarEqualityFamily.2 ⟨ψ, mem_irrKer.2 ⟨by rw [← Irr_eq_irrChar]; exact hψIrr,
          fun x hx => hTker ψ hψT ?_, hTdet ψ hψT⟩, rfl⟩
        have hx' := Subgroup.mem_subgroupOf.1 hx
        refine Subgroup.mem_subgroupOf.2 ?_
        refine (sup_le_sup_left ?_ H0) hx'
        rw [hCU]
        exact Subgroup.commutator_le_self _
      · rw [hCU]
        exact (subset_charValueKernel_indClassFun_iff hNK hψIrr).2 (hTker ψ hψT)
      · rw [hc.indClassFun_apply_one_eq, hTdeg ψ hψT]
        push_cast
        ring
  rw [himage, Finset.card_image_of_injOn (fun θ hθ ψ hψ h => hTinj θ hθ ψ hψ h), hTcard, hvu]

theorem sum_sq_degree_layers [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
    ((smallLayer H H0 U Eline S).card : ℝ)
          * ((lineFixer H H0 U (Eline 0)).relIndex U : ℝ)
        = 2 * ((lineFixerInf H H0 U Eline).relIndex U : ℝ) ∧
      (q : ℝ) * (((smallLayer H H0 U Eline S).card : ℝ)
            * ((lineFixer H H0 U (Eline 0)).relIndex U : ℝ) ^ 2)
          + (q : ℝ) * (((largeLayer H H0 U Eline S).card : ℝ)
            * ((lineFixerInf H H0 U Eline).relIndex U : ℝ) ^ 2)
          + ((p : ℝ) - 1) * ((lineFixerInf H H0 U Eline).relIndex U : ℝ) ^ 2
        = ((lineFixerInf H H0 U Eline).relIndex U : ℝ) * ((p : ℝ) ^ q - 1) := by
  classical
  set a := (lineFixer H H0 U (Eline 0)).relIndex U with ha
  set u := (lineFixerInf H H0 U Eline).relIndex U with hu
  set T := coreLayer K H H0 U Eline with hT
  have h3p := hc.three_le_p
  have hapos : 0 < a := by have := hc.one_lt_relIndex_lineFixer; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.q_prime.pos.ne'
  have hqa_ne : ((q * a : ℕ) : ℂ) ≠ ((q * u : ℕ) : ℂ) := by
    intro h
    have := Nat.eq_of_mul_eq_mul_left hc.q_prime.pos (Nat.cast_injective h)
    omega
  have hsmall := hc.card_smallLayer_mul_sq hS h2a hvu hau hdeg2
  have hfirst : (smallLayer H H0 U Eline S).card * a = 2 * u := by
    have h1 : (smallLayer H H0 U Eline S).card * a * a = 2 * u * a := by
      rw [mul_assoc, ← sq, hsmall, ← h2a]; ring
    exact Nat.eq_of_mul_eq_mul_right hapos h1
  refine ⟨by exact_mod_cast hfirst, ?_⟩
  set f : (L → ℂ) → ℂ := fun χ => (q : ℂ) * (χ 1 / q) ^ 2 with hf
  set Ti := T.filter fun θ => indClassFun K θ ∈ Irr L with hTi
  set Tr := T.filter fun θ => indClassFun K θ ∉ Irr L with hTr
  have hsplit : ∑ θ ∈ T, θ 1 ^ 2 = ∑ θ ∈ Ti, θ 1 ^ 2 + ∑ θ ∈ Tr, θ 1 ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not T _ _).symm
  have hTrsum : ∑ θ ∈ Tr, θ 1 ^ 2 = ((p : ℂ) - 1) * (u : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => (u : ℂ) ^ 2) (fun θ hθ => by
      rw [hc.apply_one_of_indClassFun_notMem_Irr (Finset.mem_filter.1 hθ).1
        (Finset.mem_filter.1 hθ).2]), Finset.sum_const, hTr,
      hc.card_filter_indClassFun_notMem_Irr, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hTisum : ∑ θ ∈ Ti, θ 1 ^ 2 = ∑ χ ∈ Ti.image (indClassFun K), f χ := by
    refine (Finset.sum_image' _ fun θ hθ => ?_).symm
    obtain ⟨hθT, hθI⟩ := Finset.mem_filter.1 hθ
    have hθIrr := (hc.mem_coreLayer_iff.1 hθT).1
    have hIK : inertiaGroup K θ = K := (FreeCore.mem_Irr_indClassFun_iff K hθIrr).1 hθI
    have hfib : Ti.filter (fun j => indClassFun K j = indClassFun K θ)
        = T.filter (fun j => indClassFun K j = indClassFun K θ) := by
      ext j
      simp only [hTi, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hθI⟩, h3⟩
    have hval : ∀ j ∈ T.filter (fun j => indClassFun K j = indClassFun K θ),
        j 1 ^ 2 = θ 1 ^ 2 := by
      intro j hj
      obtain ⟨hjT, hjeq⟩ := Finset.mem_filter.1 hj
      obtain ⟨t, rfl⟩ := (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun K
        (hc.mem_coreLayer_iff.1 hjT).1 hθIrr).1 hjeq
      rw [NormalInducedFamily.conjClassFun_apply_one]
    rw [hfib, Finset.sum_congr rfl hval, Finset.sum_const, hc.card_filter_indClassFun_eq hθT,
      hIK, hc.index_eq_q, nsmul_eq_mul, hf]
    simp only
    rw [hc.indClassFun_apply_one_eq, mul_div_cancel_left₀ _ hq0]
  have himage : Ti.image (indClassFun K)
      = smallLayer H H0 U Eline S ∪ largeLayer H H0 U Eline S := by
    ext χ
    rw [Finset.mem_union, mem_smallLayer, mem_largeLayer, Finset.mem_image]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨hθT, hθI⟩ := Finset.mem_filter.1 hθ
      have hχS : indClassFun K θ ∈ S := by
        rw [← Finset.mem_coe, hS]
        exact mem_scalarEqualityFamily.2 ⟨θ, hc.mem_irrKer_of_mem_coreLayer hθT, rfl⟩
      have hker := (hc.mem_coreLayer_iff.1 hθT).2.1
      rcases hdeg2 _ hχS with h | h
      · exact Or.inl ⟨hχS, hker, h⟩
      · exact Or.inr ⟨hχS, hθI, hker, h⟩
    · have key : ∀ χ ∈ S, χ ∈ Irr L →
          ((H0 ⊔ lineFixerInf H H0 U Eline : Subgroup L) : Set L) ⊆ charValueKernel χ →
          ∃ θ ∈ Ti, indClassFun K θ = χ := by
        intro χ hχS hIrr hker
        obtain ⟨θ, hθT, rfl⟩ := hc.exists_mem_coreLayer_of_mem
          (hS ▸ Finset.mem_coe.2 hχS) hker
        exact ⟨θ, Finset.mem_filter.2 ⟨hθT, hIrr⟩, rfl⟩
      rintro (⟨hχS, hker, hdeg⟩ | ⟨hχS, hIrr, hker, -⟩)
      · refine key χ hχS ?_ hker
        by_contra hred
        obtain ⟨θ, hθT, rfl⟩ := hc.exists_mem_coreLayer_of_mem
          (hS ▸ Finset.mem_coe.2 hχS) hker
        refine hqa_ne (hdeg.symm.trans ?_)
        rw [hc.indClassFun_apply_one_eq, hc.apply_one_of_indClassFun_notMem_Irr hθT hred]
        push_cast; ring
      · exact key χ hχS hIrr hker
  have hdisj : Disjoint (smallLayer H H0 U Eline S) (largeLayer H H0 U Eline S) :=
    Finset.disjoint_left.2 fun χ h1 h2 =>
      hqa_ne ((apply_one_of_mem_smallLayer h1).symm.trans (apply_one_of_mem_largeLayer h2))
  have hsm : ∑ χ ∈ smallLayer H H0 U Eline S, f χ
      = (q : ℂ) * (((smallLayer H H0 U Eline S).card : ℂ) * (a : ℂ) ^ 2) := by
    rw [Finset.sum_congr rfl (g := fun _ => (q : ℂ) * (a : ℂ) ^ 2) (fun χ hχ => by
      rw [hf]; simp only
      rw [apply_one_of_mem_smallLayer hχ]; push_cast
      rw [mul_div_cancel_left₀ _ hq0]), Finset.sum_const, nsmul_eq_mul]
    ring
  have hlg : ∑ χ ∈ largeLayer H H0 U Eline S, f χ
      = (q : ℂ) * (((largeLayer H H0 U Eline S).card : ℂ) * (u : ℂ) ^ 2) := by
    rw [Finset.sum_congr rfl (g := fun _ => (q : ℂ) * (u : ℂ) ^ 2) (fun χ hχ => by
      rw [hf]; simp only
      rw [apply_one_of_mem_largeLayer hχ]; push_cast
      rw [mul_div_cancel_left₀ _ hq0]), Finset.sum_const, nsmul_eq_mul]
    ring
  have hC : (q : ℂ) * (((smallLayer H H0 U Eline S).card : ℂ) * (a : ℂ) ^ 2)
      + (q : ℂ) * (((largeLayer H H0 U Eline S).card : ℂ) * (u : ℂ) ^ 2)
      + ((p : ℂ) - 1) * (u : ℂ) ^ 2 = (u : ℂ) * ((p : ℂ) ^ q - 1) := by
    rw [← hc.sum_sq_degree_coreLayer, hsplit, hTrsum, hTisum, himage,
      Finset.sum_union hdisj, hsm, hlg]
  have hR : (((q : ℝ) * (((smallLayer H H0 U Eline S).card : ℝ) * (a : ℝ) ^ 2)
      + (q : ℝ) * (((largeLayer H H0 U Eline S).card : ℝ) * (u : ℝ) ^ 2)
      + ((p : ℝ) - 1) * (u : ℝ) ^ 2 : ℝ) : ℂ) = (((u : ℝ) * ((p : ℝ) ^ q - 1) : ℝ) : ℂ) := by
    push_cast; exact hC
  exact Complex.ofReal_injective hR

theorem card_largeLayer_count [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
    (q : ℝ) * ((lineFixerInf H H0 U Eline).relIndex U : ℝ)
          * ((largeLayer H H0 U Eline S).card : ℝ)
        + ((p : ℝ) - 1) * ((q : ℝ) + ((lineFixerInf H H0 U Eline).relIndex U : ℝ))
      = (p : ℝ) ^ q - 1 := by
  obtain ⟨hsmall, hsum⟩ := hc.sum_sq_degree_layers hS h2a hvu hau hdeg2
  have h3p := hc.three_le_p
  have hp : (p : ℝ) - 1 = 2 * ((lineFixer H H0 U (Eline 0)).relIndex U : ℝ) := by
    have h : ((2 * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by
      rw [h2a]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at h
    linarith
  exact count_of_sum_sq_degree
    (pos_relIndex_lineFixerInf (H := H) (H0 := H0) (U := U) (Eline := Eline)) hp hsmall hsum

theorem exists_largeLayer [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
    ∃ S4 : Finset (L → ℂ), S4 ⊆ S ∧ (∀ γ ∈ S4, γ ∈ Irr L) ∧ (∀ γ ∈ S4, star γ ∈ S4) ∧
      (∀ γ ∈ S4, γ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) ∧
      (q : ℝ) * ((lineFixerInf H H0 U Eline).relIndex U : ℝ) * (S4.card : ℝ)
          + ((p : ℝ) - 1) * ((q : ℝ) + ((lineFixerInf H H0 U Eline).relIndex U : ℝ))
        = (p : ℝ) ^ q - 1 :=
  ⟨largeLayer H H0 U Eline S, largeLayer_subset,
    fun _ hγ => mem_Irr_of_mem_largeLayer hγ,
    fun _ hγ => star_mem_largeLayer hS hγ,
    fun _ hγ => apply_one_of_mem_largeLayer hγ,
    hc.card_largeLayer_count hS h2a hvu hau hdeg2⟩

theorem equalityBranch [Fintype L] [K.Normal] {S : Finset (L → ℂ)}
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (h2a : 2 * (lineFixer H H0 U (Eline 0)).relIndex U = p - 1)
    (hvu : (⁅U, U⁆ : Subgroup L).relIndex U = (lineFixerInf H H0 U Eline).relIndex U)
    (hau : (lineFixer H H0 U (Eline 0)).relIndex U < (lineFixerInf H H0 U Eline).relIndex U)
    (hdeg2 : ∀ χ ∈ S, χ 1 = ((q * (lineFixer H H0 U (Eline 0)).relIndex U : ℕ) : ℂ) ∨
      χ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) :
      (∀ i j : ZMod q, i ≠ j →
        lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) = lineFixerInf H H0 U Eline) ∧
      (lineFixerInf H H0 U Eline).relIndex U
        ≤ (lineFixer H H0 U (Eline 0)).relIndex U ^ 2 ∧
      ∃ S4 : Finset (L → ℂ), S4 ⊆ S ∧ (∀ γ ∈ S4, γ ∈ Irr L) ∧ (∀ γ ∈ S4, star γ ∈ S4) ∧
        (∀ γ ∈ S4, γ 1 = ((q * (lineFixerInf H H0 U Eline).relIndex U : ℕ) : ℂ)) ∧
        (q : ℝ) * ((lineFixerInf H H0 U Eline).relIndex U : ℝ) * (S4.card : ℝ)
            + ((p : ℝ) - 1) * ((q : ℝ) + ((lineFixerInf H H0 U Eline).relIndex U : ℝ))
          = (p : ℝ) ^ q - 1 := by
  have hinf : ∀ i j : ZMod q, i ≠ j →
      lineFixer H H0 U (Eline i) ⊓ lineFixer H H0 U (Eline j) = lineFixerInf H H0 U Eline :=
    fun i j hij => hc.inf_lineFixer_eq_of_relIndex_eq hij hau
      (hc.relIndex_inf_lineFixer_eq_or hS h2a hvu hau hdeg2 i j hij)
  refine ⟨hinf, ?_, hc.exists_largeLayer hS h2a hvu hau hdeg2⟩
  have h3q := hc.three_le_q
  have : Fact (1 < q) := ⟨by omega⟩
  have h01 : (0 : ZMod q) ≠ 1 := zero_ne_one
  rw [← hinf 0 1 h01]
  exact relIndex_inf_le_sq (lineFixer_le H H0 U _) (lineFixer_le H H0 U _) rfl
    (hc.relIndex_lineFixer_eq 1)

end IsScalarCoreConfig

variable {G : Type*} [Group G]

theorem isCoherent_scalarCoreDetectFam [Fintype L] [Fintype G] [K.Normal]
    (hc : IsScalarCoreConfig p q K H U B H0 Eline A)
    {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
    (hsub : IsSubcoherent S tau R)
    (hS : (S : Set (L → ℂ)) = scalarEqualityFamily K H H0 U Eline)
    (tauhat : virtualCharsOn A →+ virtualChars G)
    (htauhatIsom : ∀ f g : virtualCharsOn A,
      cfInner (tauhat f : G → ℂ) (tauhat g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (htauhatTau : ∀ f : charSpanZero (S : Set (L → ℂ)),
      (tauhat (Submodule.inclusion (hc.charSpanZero_le_virtualCharsOn hS) f) : G → ℂ)
        = tau (f : L → ℂ))
    (τS : charSpanZero (S : Set (L → ℂ)) →+ virtualChars G)
    (hτS : ∀ f : charSpanZero (S : Set (L → ℂ)), (τS f : G → ℂ) = tau (f : L → ℂ)) :
    IsCoherent (S : Set (L → ℂ)) τS := by
  classical
  set a : ℕ := (lineFixer H H0 U (Eline 0)).relIndex U with hadef
  set u : ℕ := (lineFixerInf H H0 U Eline).relIndex U with hudef
  obtain ⟨hadvd, hdeg, hdegle, Q, hQS, hQIrr, hQdeg, r, hr, hrdef, hQcard⟩ := hc.axisLayer hS
  refine ScalarCoherenceAssembly.isCoherent_of_layers hsub
    (hc.charSpanZero_le_virtualCharsOn hS) tauhat htauhatIsom htauhatTau hτS
    hc.three_le_p hc.p_odd hc.three_le_q hc.one_lt_relIndex_lineFixer
    hc.odd_relIndex_lineFixer hadvd
    (IsScalarCoreConfig.relIndex_lineFixer_dvd_relIndex_lineFixerInf (H := H) (H0 := H0) (U := U)
      (Eline := Eline))
    (IsScalarCoreConfig.pos_relIndex_lineFixerInf (H := H) (H0 := H0) (U := U) (Eline := Eline))
    (IsScalarCoreConfig.relIndex_lineFixerInf_le_relIndex_commutator
      hc.commutator_le_lineFixerInf)
    hdeg hdegle hQS hQIrr hQdeg hr hrdef hQcard ?_ ?_
  ·
    intro h2a hvu hau hdeg2
    obtain ⟨-, hua, S4, hS4S, hS4Irr, hS4star, hS4deg, hcount⟩ :=
      hc.equalityBranch hS h2a hvu hau hdeg2
    exact ⟨hua, S4, hS4S, hS4Irr, hS4star, hS4deg, hcount⟩
  ·
    intro ψ hψS hψIrr hψdeg h2a hvu hau hdeg2
    obtain ⟨hinf, -, -⟩ := hc.equalityBranch hS h2a hvu hau hdeg2
    have hce : IsScalarEqualityConfig p q K H U B H0 Eline A :=
      hc.isScalarEqualityConfig
        (IsScalarCoreConfig.lineFixerInf_eq_commutator hc.commutator_le_lineFixerInf hvu)
        (by omega) hau hinf
    have hψSet : ψ ∈ scalarEqualityFamily K H H0 U Eline := hS ▸ Finset.mem_coe.2 hψS
    have hdeg' : ψ 1 = (q : ℂ) * (a : ℂ) := by rw [hψdeg]; push_cast; ring
    obtain ⟨hnorm, hinner, hzero⟩ := scalarTestChar_norm_and_inner hce hψSet hψIrr
    refine ⟨scalarTestChar H H0 U Eline ψ, mem_virtualCharsOn.2
      ⟨scalarTestChar_mem_virtualChars H H0 U Eline hψIrr,
        fun x hx => scalarTestChar_eq_zero_of_notMem hce hψSet hdeg' hx⟩, hnorm, hinner, ?_⟩
    exact fun χ hχ hne => hzero χ (hS ▸ Finset.mem_coe.2 hχ) hne

end ScalarCoreCoherence

end CFSG.FeitThompson
