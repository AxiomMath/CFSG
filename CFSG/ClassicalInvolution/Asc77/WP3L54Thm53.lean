module

public import CFSG.ClassicalInvolution.Asc77.WP3L54Prelim
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Def

variable {G : Type} [Group G]

@[expose] def thetaA (A : Subgroup G) (d : G) : Subgroup G :=
  ⁅involutionOddCore d, A⁆ ⊔ (centralOddCore A ⊓ Subgroup.centralizer ({d} : Set G))

end Def

namespace Lemma54Proof

section Theta

variable {G : Type} [Group G] [Finite G] {B A : Subgroup G}

omit [Finite G] in
theorem comm_of_isElemAbelian (hB : IsElemAbelian 2 B) : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
  fun x hx y hy => congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)

omit [Finite G] in
theorem le_normalizer_involutionOddCore (hB : IsElemAbelian 2 B) {d : G} (hd : d ∈ B) :
    B ≤ Subgroup.normalizer (involutionOddCore d : Set G) := fun x hx =>
  normalizer_oddCoreIn (Subgroup.centralizer ({d} : Set G))
    (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_isElemAbelian hB x hx d hd))

omit [Finite G] in
theorem le_normalizer_commutator (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    B ≤ Subgroup.normalizer ((⁅involutionOddCore d, A⁆ : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_commutator (le_normalizer_involutionOddCore hB hd hx)
    (le_normalizer_of_le (comm_of_isElemAbelian hB) hAB hx)

omit [Finite G] in
theorem mem_normalizer_centralOddCore {g : G} (hg : g ∈ Subgroup.centralizer (A : Set G)) :
    g ∈ Subgroup.normalizer (centralOddCore A : Set G) :=
  normalizer_oddCoreIn (Subgroup.centralizer (A : Set G)) hg

omit [Finite G] in
theorem le_normalizer_central (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    B ≤ Subgroup.normalizer ((centralOddCore A ⊓ Subgroup.centralizer ({d} : Set G) :
      Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_inf
    (mem_normalizer_centralOddCore (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (comm_of_isElemAbelian hB x hx a (hAB ha)).symm))
    (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_isElemAbelian hB x hx d hd)))

omit [Finite G] in
theorem le_normalizer_commutator_of_central {d : G} :
    (centralOddCore A ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.normalizer ((⁅involutionOddCore d, A⁆ : Subgroup G) : Set G) := fun _ ht =>
  mem_normalizer_commutator
    (normalizer_oddCoreIn (Subgroup.centralizer ({d} : Set G)) ht.2)
    (mem_normalizer_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht.1) a ha).symm)

omit [Finite G] in
theorem le_normalizer_commutator_of_le (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G}
    (hd : d ∈ B) :
    A ≤ Subgroup.normalizer ((⁅involutionOddCore d, A⁆ : Subgroup G) : Set G) := fun _ hx =>
  le_normalizer_commutator hB hAB hd (hAB hx)

omit [Finite G] in
theorem commutator_le_involutionOddCore (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G}
    (hd : d ∈ B) : ⁅involutionOddCore d, A⁆ ≤ involutionOddCore d :=
  commutator_le_self fun _ hx => le_normalizer_involutionOddCore hB hd (hAB hx)

omit [Finite G] in
theorem thetaA_le_centralizer (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    thetaA A d ≤ Subgroup.centralizer ({d} : Set G) :=
  sup_le ((commutator_le_involutionOddCore hB hAB hd).trans (involutionOddCore_le_centralizer d))
    inf_le_right

theorem odd_card_thetaA (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    Odd (Nat.card (thetaA A d)) := by
  have hX : Odd (Nat.card (⁅involutionOddCore d, A⁆ : Subgroup G)) :=
    (odd_card_oddCoreIn (Subgroup.centralizer ({d} : Set G))).of_dvd_nat
      (Subgroup.card_dvd_of_le (commutator_le_involutionOddCore hB hAB hd))
  have hT : Odd (Nat.card (centralOddCore A ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G)) :=
    (odd_card_centralOddCore A).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have h := odd_card_sup_of_le_normalizer le_normalizer_commutator_of_central hT hX
  rwa [sup_comm] at h

omit [Finite G] in
theorem le_normalizer_thetaA (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    B ≤ Subgroup.normalizer ((thetaA A d : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup (le_normalizer_commutator hB hAB hd hx) (le_normalizer_central hB hAB hd hx)

omit [Finite G] in
theorem mem_thetaA_decomp {d w : G} (hw : w ∈ thetaA A d) :
    ∃ x ∈ (⁅involutionOddCore d, A⁆ : Subgroup G),
      ∃ t ∈ (centralOddCore A ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G), x * t = w :=
  (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _ le_normalizer_commutator_of_central
    w).mp hw

omit [Finite G] in
theorem commutator_thetaA_le (hB : IsElemAbelian 2 B) (hAB : A ≤ B) {d : G} (hd : d ∈ B) :
    ⁅thetaA A d, A⁆ ≤ ⁅involutionOddCore d, A⁆ := by
  rw [Subgroup.commutator_le]
  intro w hw a ha
  obtain ⟨x, hx, t, ht, rfl⟩ := mem_thetaA_decomp hw
  have hta : t * a = a * t :=
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer A ht.1) a ha).symm
  have hta' : t * a * t⁻¹ = a := by rw [hta]; group
  have e : ⁅x * t, a⁆ = ⁅x, a⁆ := by
    calc ⁅x * t, a⁆ = x * (t * a * t⁻¹) * x⁻¹ * a⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x, a⁆ := by rw [hta']; simp only [commutatorElement_def]
  rw [e]
  exact commutator_le_self (le_normalizer_commutator_of_le hB hAB hd)
    (Subgroup.commutator_mem_commutator hx ha)

theorem thetaA_inf_centralizer_le (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B)
    (hW : WeakBalanced B) (hAB : A ≤ B) (hA4 : 4 ≤ Nat.card A) {d : G} (hd : d ∈ B)
    (hd1 : d ≠ 1) : thetaA A d ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A := by
  rintro w ⟨hw, hwC⟩
  obtain ⟨x, hx, t, ht, rfl⟩ := mem_thetaA_decomp hw
  have htC : t ∈ Subgroup.centralizer (A : Set G) := centralOddCore_le_centralizer A ht.1
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := by
    have e : x = (x * t) * t⁻¹ := by group
    rw [e]
    exact (Subgroup.centralizer (A : Set G)).mul_mem hwC
      ((Subgroup.centralizer (A : Set G)).inv_mem htC)
  exact (centralOddCore A).mul_mem
    (commutator_inf_centralizer_le hB h8 hW hAB hA4 hd hd1 ⟨hx, hxC⟩) ht.1

theorem thetaA_balance (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B) (hW : WeakBalanced B)
    (hAB : A ≤ B) (hA4 : 4 ≤ Nat.card A) {c d : G} (hc : c ∈ B) (hc1 : c ≠ 1) (hd : d ∈ B)
    (hd1 : d ≠ 1) :
    thetaA A d ⊓ Subgroup.centralizer ({c} : Set G) ≤ thetaA A c := by
  have hAel : IsElemAbelian 2 A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hAB
  have hAp : IsPGroup 2 A := isPGroup_two hAel
  have hAθ : A ≤ Subgroup.normalizer ((thetaA A d : Subgroup G) : Set G) := fun x hx =>
    le_normalizer_thetaA hB hAB hd (hAB hx)
  have hAC : A ≤ Subgroup.normalizer ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_isElemAbelian hB x (hAB hx) c hc))
  have hAY : A ≤ Subgroup.normalizer
      ((thetaA A d ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hAθ hx) (hAC hx)
  have hYodd : Odd (Nat.card (thetaA A d ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)) :=
    (odd_card_thetaA hB hAB hd).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  refine (commutator_sup_centralizer hAp hAY hYodd).symm.le.trans (sup_le ?_ ?_)
  ·
    have h1 := commutator_le_self (P := A) (Y := thetaA A d ⊓ Subgroup.centralizer ({c} : Set G))
      hAY
    have h2 : ⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆ ≤ ⁅involutionOddCore d, A⁆ :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans (commutator_thetaA_le hB hAB hd)
    have h3 : ⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆ ≤
        involutionOddCore d ⊓ Subgroup.centralizer ({c} : Set G) :=
      le_inf (h2.trans (commutator_le_involutionOddCore hB hAB hd)) (h1.trans inf_le_right)
    have hidem := commutator_commutator_eq hAp hAY hYodd
    have h5 : ⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆ ≤ involutionOddCore c := by
      calc ⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆
          = ⁅⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆, A⁆ := hidem.symm
        _ ≤ ⁅involutionOddCore d ⊓ Subgroup.centralizer ({c} : Set G), B⁆ :=
          Subgroup.commutator_mono h3 hAB
        _ ≤ involutionOddCore c := hW d hd hd1 c hc hc1
    calc ⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆
        = ⁅⁅thetaA A d ⊓ Subgroup.centralizer ({c} : Set G), A⁆, A⁆ := hidem.symm
      _ ≤ ⁅involutionOddCore c, A⁆ := Subgroup.commutator_mono h5 le_rfl
      _ ≤ thetaA A c := le_sup_left
  ·
    have h6 : thetaA A d ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A :=
      thetaA_inf_centralizer_le hB h8 hW hAB hA4 hd hd1
    calc (thetaA A d ⊓ Subgroup.centralizer ({c} : Set G)) ⊓ Subgroup.centralizer (A : Set G)
        ≤ centralOddCore A ⊓ Subgroup.centralizer ({c} : Set G) :=
          le_inf ((inf_le_inf_right _ inf_le_left).trans h6) (inf_le_left.trans inf_le_right)
      _ ≤ thetaA A c := le_sup_right

end Theta

end Lemma54Proof

section Lemma53

open Lemma54Proof

variable {G : Type} [Group G] [Finite G] {B A : Subgroup G}

theorem isSolvableSignalizerFunctor_thetaA_of_rankThreeBalance (hR : RankThreeBalance B)
    (hAB : A ≤ B) (hA4 : Nat.card A = 4) : IsSolvableSignalizerFunctor 2 B (thetaA A) where
  le_centralizer _ ha _ := thetaA_le_centralizer hR.elem hAB ha
  coprime _ ha _ := Nat.coprime_two_left.mpr (odd_card_thetaA hR.elem hAB ha)
  invariant _ ha _ _ hx := conjSub_eq_of_mem_normalizer (le_normalizer_thetaA hR.elem hAB ha hx)
  balance _ ha ha1 _ hb hb1 :=
    thetaA_balance hR.elem hR.card.ge hR.weak hAB hA4.ge hb hb1 ha ha1
  solvable _ ha _ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_thetaA hR.elem hAB ha)

@[expose] def Lemma53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G), Hyp51 B → ∀ A : Subgroup G, A ≤ B →
    IsElemAbelian2 A 2 → IsSolvableSignalizerFunctor 2 B (thetaA A)

theorem lemma53 : Lemma53 := fun _ _ _ B hB _ hAB hA =>
  isSolvableSignalizerFunctor_thetaA_of_rankThreeBalance (lemma52 _ B hB) hAB hA.1

end Lemma53

end CFSG.ClassicalInvolution.Asc77
