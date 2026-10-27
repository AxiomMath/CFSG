module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
import CFSG.FeitThompson.OddOrder.PConfigAlignDerivedComplement
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson (conjSubgroup conjSubgroup_eq mem_conjSubgroup
  hallCoreIn hallCoreIn_eq hallCoreIn_le)
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd hallCoreOf
  centralizerIn centralizerIn_eq IsFixedPointFreeOn)

universe u

variable {G : Type*} [Group G]

theorem natCard_subgroupOf_eq {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem le_of_subgroupOf_le_subgroupOf {A B L : Subgroup G} (hA : A ≤ L)
    (h : A.subgroupOf L ≤ B.subgroupOf L) : A ≤ B := by
  intro x hx
  exact h (show (⟨x, hA hx⟩ : ↥L) ∈ A.subgroupOf L from hx)

theorem mem_conjSubgroup_iff {Y : Subgroup G} {g x : G} :
    x ∈ conjSubgroup Y g ↔ g * x * g⁻¹ ∈ Y := by
  rw [mem_conjSubgroup]
  refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨g * x * g⁻¹, hx, by group⟩⟩
  have h : g * x * g⁻¹ = y := by rw [← hyx]; group
  rw [h]; exact hy

theorem conjSubgroup_conjSubgroup_inv (Y : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup Y g) g⁻¹ = Y := by
  ext x
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have h : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  rw [h]

theorem conjSubgroup_eq_self_of_mem {L : Subgroup G} {g : G} (hg : g ∈ L) :
    conjSubgroup L g = L := by
  ext x
  rw [mem_conjSubgroup_iff]
  refine ⟨fun h => ?_, fun h => mul_mem (mul_mem hg h) (inv_mem hg)⟩
  have hx : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [← hx]
  exact mul_mem (mul_mem (inv_mem hg) h) hg

theorem natCard_conjSubgroup (Y : Subgroup G) (g : G) :
    Nat.card ↥(conjSubgroup Y g) = Nat.card ↥Y := by
  rw [conjSubgroup_eq]
  exact Subgroup.card_map_of_injective fun _ _ h => (MulAut.conj g⁻¹).injective h

theorem conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjSubgroup A g ≤ conjSubgroup B g := fun _ hx =>
  mem_conjSubgroup_iff.2 (h (mem_conjSubgroup_iff.1 hx))

theorem conjSubgroup_le_normalizer_conjSubgroup {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) (g : G) :
    conjSubgroup A g ≤ normalizer ((conjSubgroup B g : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  have key := Subgroup.mem_set_normalizer_iff.1 (h hx) (g * y * g⁻¹)
  simp only [SetLike.mem_coe, mem_conjSubgroup_iff] at key ⊢
  have heq : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by group
  rw [key, heq]

theorem map_conj_conjSubgroup (Y : Subgroup G) (a g : G) :
    (conjSubgroup Y g).map (MulAut.conj a : G →* G) = Y.map (MulAut.conj (a * g⁻¹) : G →* G) := by
  rw [conjSubgroup_eq, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_of_map_conj_eq {A : Subgroup G} {a : G}
    (h : A.map (MulAut.conj a : G →* G) = A) : a ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff_conj_image_eq]
  have hh := congrArg (fun S : Subgroup G => (S : Set G)) h
  simpa [Subgroup.coe_map] using hh

theorem commute_of_normal_of_disjoint {L U W₁ Q : Subgroup G} (hUL : U ≤ L) (hQL : Q ≤ L)
    (hQnormal : (Q.subgroupOf L).Normal) (hW₁Q : W₁ ≤ Q)
    (hW₁U : W₁ ≤ normalizer (U : Set G)) (hdisj : U ⊓ Q = ⊥)
    {u w : G} (hu : u ∈ U) (hw : w ∈ W₁) : u * w = w * u := by
  have huL : u ∈ L := hUL hu
  have hcU : u⁻¹ * (w⁻¹ * u * w) ∈ U := by
    refine mul_mem (inv_mem hu) ?_
    have h3 := (Subgroup.mem_set_normalizer_iff.1 (hW₁U (inv_mem hw)) u).1 hu
    have h2 : w⁻¹ * u * w = w⁻¹ * u * w⁻¹⁻¹ := by group
    rw [h2]; exact h3
  have hcQ : u⁻¹ * (w⁻¹ * u * w) ∈ Q := by
    have hQconj : ∀ x ∈ Q, ∀ y ∈ L, y * x * y⁻¹ ∈ Q := by
      intro x hx y hy
      have hmem := hQnormal.conj_mem ⟨x, hQL hx⟩ hx ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using hmem
    have h1 : u⁻¹ * w⁻¹ * u ∈ Q := by
      have := hQconj w⁻¹ (inv_mem (hW₁Q hw)) u⁻¹ (inv_mem huL)
      simpa using this
    have h2 : u⁻¹ * (w⁻¹ * u * w) = u⁻¹ * w⁻¹ * u * w := by group
    rw [h2]
    exact mul_mem h1 (hW₁Q hw)
  have hcbot : u⁻¹ * (w⁻¹ * u * w) = 1 := by
    have hmem : u⁻¹ * (w⁻¹ * u * w) ∈ U ⊓ Q := ⟨hcU, hcQ⟩
    rw [hdisj] at hmem
    simpa using hmem
  have hfix : w⁻¹ * u * w = u := (inv_mul_eq_one.1 hcbot).symm
  calc u * w = w * (w⁻¹ * u * w) := by group
    _ = w * u := by rw [hfix]

variable [Finite G]

theorem relIndex_conjSubgroup {A B : Subgroup G} (hAB : A ≤ B) (g : G) :
    (conjSubgroup A g).relIndex (conjSubgroup B g) = A.relIndex B := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥A)) ?_
  calc Nat.card ↥A * (conjSubgroup A g).relIndex (conjSubgroup B g)
      = Nat.card ↥(conjSubgroup A g) * (conjSubgroup A g).relIndex (conjSubgroup B g) := by
        rw [natCard_conjSubgroup]
    _ = Nat.card ↥(conjSubgroup B g) := natCard_mul_relIndex (conjSubgroup_mono hAB g)
    _ = Nat.card ↥B := natCard_conjSubgroup B g
    _ = Nat.card ↥A * A.relIndex B := (natCard_mul_relIndex hAB).symm

omit [Finite G] in
theorem isHallSubgroup_subgroupOf {A B : Subgroup G} (hAB : A ≤ B)
    (h : (Nat.card ↥A).Coprime (A.relIndex B)) :
    IsHallSubgroup ((Nat.card ↥A).primeFactors : Set ℕ) (A.subgroupOf B) := by
  have hc : (Nat.card ↥(A.subgroupOf B)).Coprime (A.subgroupOf B).index := by
    rw [natCard_subgroupOf_eq hAB]; exact h
  have hH := isHallSubgroup_primeFactors_natCard hc
  rwa [natCard_subgroupOf_eq hAB] at hH

theorem coprime_natCard_relIndex_hallCoreIn (T : Subgroup G) :
    (Nat.card ↥(hallCoreIn T)).Coprime ((hallCoreIn T).relIndex T) := by
  have h := coprime_natCard_index_hallCore (X := ↥T)
  rw [← subgroupOf_hallCoreIn_eq T] at h
  rw [← natCard_subgroupOf_eq (hallCoreIn_le T)]
  exact h

theorem coprime_natCard_natCard_W₁ {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    (Nat.card ↥U).Coprime (Nat.card ↥W₁) :=
  (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hc.le_commutator_E)
    hc.coprime_natCard_W₁_natCard_commutator).symm

theorem coprime_natCard_relIndex_of_semidirect {M U W₁ W₂ P : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsdM : FreeCore.IsInternalSemidirectProduct M P (U ⊔ W₁))
    (hsdU : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥U * Nat.card ↥W₁)) :
    (Nat.card ↥U).Coprime (U.relIndex M) := by
  have hUM : U ≤ M := hsdU.left_le.trans hsdM.right_le
  have hidx : U.relIndex M = Nat.card ↥P * Nat.card ↥W₁ := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥U)) ?_
    rw [natCard_mul_relIndex hUM, hsdM.natCard_eq_mul, hsdU.natCard_eq_mul]
    ring
  rw [hidx]
  exact Nat.Coprime.mul_right
    (Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hcop).symm
    (coprime_natCard_natCard_W₁ hc)

theorem ne_conjSubgroup_left {M U W₁ W₂ L P : Subgroup G}
    (hsolvL : Group.IsSolvable ↥L)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsdM : FreeCore.IsInternalSemidirectProduct M P (U ⊔ W₁))
    (hsdU : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hcopP : Nat.Coprime (Nat.card ↥P) (Nat.card ↥U * Nat.card ↥W₁))
    (hNU : normalizer (U : Set G) ≤ L)
    (hNUM : ¬ normalizer (U : Set G) ≤ M) (g : G) : L ≠ conjSubgroup M g := by
  intro hLM
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNU
  have hUM : U ≤ M := hsdU.left_le.trans hsdM.right_le
  have hUHall : (Nat.card ↥U).Coprime (U.relIndex M) :=
    coprime_natCard_relIndex_of_semidirect hc hsdM hsdU hcopP
  have hUgL : conjSubgroup U g ≤ L := hLM ▸ conjSubgroup_mono hUM g
  have hUgcard : Nat.card ↥(conjSubgroup U g) = Nat.card ↥U := natCard_conjSubgroup U g
  have hUgIdx : (conjSubgroup U g).relIndex L = U.relIndex M := by
    rw [hLM]; exact relIndex_conjSubgroup hUM g
  have hUgHall : (Nat.card ↥(conjSubgroup U g)).Coprime ((conjSubgroup U g).relIndex L) := by
    rw [hUgcard, hUgIdx]; exact hUHall
  have hUidxL : U.relIndex L = (conjSubgroup U g).relIndex L := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥U)) ?_
    rw [natCard_mul_relIndex hUL, ← hUgcard, natCard_mul_relIndex hUgL]
  have hUHallL : (Nat.card ↥U).Coprime (U.relIndex L) := by
    rw [hUidxL, ← hUgcard]; exact hUgHall
  have h1 : IsHallSubgroup ((Nat.card ↥U).primeFactors : Set ℕ)
      ((conjSubgroup U g).subgroupOf L) := by
    have h := isHallSubgroup_subgroupOf hUgL hUgHall
    rwa [hUgcard] at h
  have h2 : IsHallSubgroup ((Nat.card ↥U).primeFactors : Set ℕ) (U.subgroupOf L) :=
    isHallSubgroup_subgroupOf hUL hUHallL
  obtain ⟨c, hc'⟩ := exists_map_conj_eq_of_isHallSubgroup h1 h2
  have hconj : (conjSubgroup U g).map (MulAut.conj (c : G) : G →* G) = U :=
    map_conj_eq_of_map_conj_subgroupOf hUgL hUL hc'
  rw [map_conj_conjSubgroup] at hconj
  have hmem : (c : G) * g⁻¹ ∈ normalizer (U : Set G) := mem_normalizer_of_map_conj_eq hconj
  have hgL : g ∈ L := by
    have hcgL : (c : G) * g⁻¹ ∈ L := hNU hmem
    have hinv : g⁻¹ ∈ L := by simpa using mul_mem (inv_mem c.2) hcgL
    simpa using inv_mem hinv
  have hML : M = L := by
    have h := conjSubgroup_conjSubgroup_inv M g
    rw [← hLM, conjSubgroup_eq_self_of_mem (inv_mem hgL)] at h
    exact h.symm
  exact hNUM (hML ▸ hNU)

theorem le_conjSubgroup_hallCoreIn {T L W₁ : Subgroup G} {g : G} (hLT : L = conjSubgroup T g)
    {q p : ℕ} (hq : Nat.card ↥W₁ = q) (hp : p ≠ 0) (hQ : Nat.card ↥(hallCoreIn T) = q ^ p)
    (hW₁L : W₁ ≤ L) : W₁ ≤ conjSubgroup (hallCoreIn T) g := by
  set Q : Subgroup G := conjSubgroup (hallCoreIn T) g with hQdef
  have hQL : Q ≤ L := hLT ▸ conjSubgroup_mono (hallCoreIn_le T) g
  have hQcard : Nat.card ↥Q = q ^ p := by rw [hQdef, natCard_conjSubgroup, hQ]
  have hQnormal : (Q.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).2 ?_
    rw [hLT, hQdef]
    exact conjSubgroup_le_normalizer_conjSubgroup (le_normalizer_map_subtype_hallCore T) g
  have hQHall : (Nat.card ↥Q).Coprime (Q.relIndex L) := by
    have hidx : Q.relIndex L = (hallCoreIn T).relIndex T := by
      rw [hQdef, hLT]; exact relIndex_conjSubgroup (hallCoreIn_le T) g
    rw [hidx, hQdef, natCard_conjSubgroup]
    exact coprime_natCard_relIndex_hallCoreIn T
  have hQhp : IsHallSubgroup ((Nat.card ↥Q).primeFactors : Set ℕ) (Q.subgroupOf L) :=
    isHallSubgroup_subgroupOf hQL hQHall
  have hπ : ((Nat.card ↥Q).primeFactors : Set ℕ) = (q.primeFactors : Set ℕ) := by
    rw [hQcard, Nat.primeFactors_pow _ hp]
  rw [hπ] at hQhp
  have hW₁pi : IsPiSubgroup (q.primeFactors : Set ℕ) (W₁.subgroupOf L) := by
    rw [isPiSubgroup_iff, natCard_subgroupOf_eq hW₁L, hq]
    exact fun r hr => hr
  have : (Q.subgroupOf L).Normal := hQnormal
  exact le_of_subgroupOf_le_subgroupOf hW₁L (hQhp.isHallPiSubgroup.le_of_isPiSubgroup hW₁pi)

theorem ne_conjSubgroup_right {T U W₁ L : Subgroup G}
    {p q : ℕ} (hp : p ≠ 0) (hq : Nat.card ↥W₁ = q)
    (hQcard : Nat.card ↥(hallCoreIn T) = q ^ p)
    (hUne : U ≠ ⊥) (hUW₁ : (Nat.card ↥U).Coprime q)
    (hffp : IsFixedPointFreeOn U W₁) (hW₁ne : W₁ ≠ ⊥)
    (hNU : normalizer (U : Set G) ≤ L)
    (hsdU : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁) (g : G) :
    L ≠ conjSubgroup T g := by
  intro hLT
  have hW₁NU : W₁ ≤ normalizer (U : Set G) := hsdU.right_le.trans hsdU.le_normalizer
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNU
  have hW₁L : W₁ ≤ L := hW₁NU.trans hNU
  have hW₁Q : W₁ ≤ conjSubgroup (hallCoreIn T) g :=
    le_conjSubgroup_hallCoreIn hLT hq hp hQcard hW₁L
  set Qg : Subgroup G := conjSubgroup (hallCoreIn T) g with hQg
  have hQgL : Qg ≤ L := hLT ▸ conjSubgroup_mono (hallCoreIn_le T) g
  have hQgnormal : (Qg.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQgL).2 ?_
    rw [hLT, hQg]
    exact conjSubgroup_le_normalizer_conjSubgroup (le_normalizer_map_subtype_hallCore T) g
  have hQgcard : Nat.card ↥Qg = q ^ p := by rw [hQg, natCard_conjSubgroup, hQcard]
  have hdisj : U ⊓ Qg = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hQgcard]
    exact hUW₁.pow_right p
  have hcomm : ∀ u ∈ U, ∀ w ∈ W₁, u * w = w * u := fun u hu w hw =>
    commute_of_normal_of_disjoint hUL hQgL hQgnormal hW₁Q hW₁NU hdisj hu hw
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW₁ne
  have hw1 : (w : G) ≠ 1 := by simpa using hw
  have hUcent : U ≤ centralizer ((zpowers (w : G) : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hcw : Commute u (w : G) := hcomm u hu (w : G) w.2
    have hres := (hcw.zpow_right k).eq
    rw [← hk]
    exact hres.symm
  have hbot : centralizerIn U (zpowers (w : G)) = ⊥ := hffp (w : G) w.2 hw1
  rw [centralizerIn_eq, inf_eq_left.2 hUcent] at hbot
  exact hUne hbot

theorem FBG_type_II_supporting_maximum_excludes_pair
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FBG_type_II_supporting_maximum_excludes_pair.{u} := by
  intro G _ _ hG M T U V W₁ W₂ hM hT _hMT hcM hcT hII _hcyc _hMTcap hcover L hL hNU
    _P _Q _H _hP _hQ _hH p q hp hq
  have hG' : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hpp, -, -, -, -, hUne, -, hsdM, hsdU, hcopP, hffp, -, -, -, -, -, -, -, -, -, -, -,
    -⟩ := h₁ G hG' M U W₁ W₂ hM hcM p q hp hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQcard, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₁ G hG' T V W₂ W₁ hT hcT q p hq hp
  have hQcard' : Nat.card ↥(hallCoreIn T) = q ^ p := hQcard
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  obtain ⟨-, -, -, hNUM, -, -⟩ := hII.clauses_of_isWitnessedPConfiguration hsolvM hcM
  have hsolvL : Group.IsSolvable ↥L := hG.isSolvable_of_ne_top L hL.1
  have hleft : ∀ g : G, L ≠ conjSubgroup M g :=
    ne_conjSubgroup_left hsolvL hcM hsdM hsdU hcopP hNU hNUM
  have hright : ∀ g : G, L ≠ conjSubgroup T g := by
    refine ne_conjSubgroup_right hpp.pos.ne' hq.symm hQcard' hUne ?_ hffp hcM.ne_bot_W₁ hNU hsdU
    rw [hq]; exact coprime_natCard_natCard_W₁ hcM
  refine ⟨hleft, hright, ?_⟩
  by_contra hI
  rcases hcover L hL hI with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hleft g hg
  · exact hright g hg

end

end CFSG.FeitThompson.Proofs
