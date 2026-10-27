module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37TwoAltCrux
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37TwoSL2
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37TripleA7
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact34Holds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap
public import CFSG.Quasithin.Background.B69Alt
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPAlt
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridge
public import CFSG.Quasithin.Background.FFC11A
public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Model

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.Quasithin.B1Red
open CFSG.Open (quasithinGenFitting)
open CFSG.Quasithin.G6 (PermMod coreMod permAct permAct_apply permAct_mem_coreMod allOnes coreAct)
open CFSG.RankThree.PartTwo (altHeart evenWeightPerm)
open CFSG.QuasithinUnique (evenWeight)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct altAct_mk)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive IsAltNaturalSection)
open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

variable {W : Type} [CommGroup W] [Finite W]



private theorem coreHeart_bijective {n : ℕ} (hno : Odd n) :
    Function.Bijective (coreHeart n) := by
  have hinj : Function.Injective (coreHeart n) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h := (coreHeart_eq_one_iff hno.pos x).1 hx
    rwa [CFSG.Quasithin.B69.natKer_inf_eq_bot hno, Subgroup.mem_bot] at h
  exact ⟨hinj, coreHeart_surjective n⟩

private structure AltConv (V : Type) [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) (n : ℕ) where
  α : ↥L →* alternatingGroup (Fin n)
  hα : Function.Surjective α
  π : alternatingGroup (Fin n) →* ↥L
  hπs : Function.Surjective π
  hπα : ∀ γ, α (π γ) = γ
  π₀ : ↥(commV L) →* Multiplicative (altHeart n)
  hπ₀ : Function.Surjective π₀
  hker : π₀.ker = (commV L ⊓ fixV L).subgroupOf (commV L)
  heq : ∀ (l : ↥L) (u v : ↥(commV L)), (v : V) = (l : MulAut V) (u : V) →
    ∀ x : evenWeight n, Multiplicative.toAdd (π₀ u) = (x : altHeart n) →
      Multiplicative.toAdd (π₀ v) =
        (evenWeightPerm (α l : Equiv.Perm (Fin n)) x : altHeart n)
  β : ↥(commV L) →* ↥(coreMod n)
  hβs : Function.Surjective β
  hβker : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L)
  hβu : ∀ u, coreHeart n (β u) = π₀ u

private theorem altConv_of_naturalSection {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {n : ℕ} (hno : Odd n)
    (e : ↥L ≃* alternatingGroup (Fin n)) (h : IsAltNaturalSection L (commV L) n) :
    Nonempty (AltConv V L n) := by
  classical
  obtain ⟨α, hα, π₀, hπ₀, hker, heq⟩ := h
  have hαi : Function.Injective α :=
    (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hα
  let αe : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective α ⟨hαi, hα⟩
  let π : alternatingGroup (Fin n) →* ↥L := αe.symm.toMonoidHom
  have hπs : Function.Surjective π := αe.symm.surjective
  have hπα : ∀ γ, α (π γ) = γ := fun γ => αe.apply_symm_apply γ
  let Φ : ↥(coreMod n) ≃* Multiplicative (altHeart n) :=
    MulEquiv.ofBijective _ (coreHeart_bijective hno)
  have hΦ : ∀ x : ↥(coreMod n), (Φ x : Multiplicative (altHeart n)) = coreHeart n x :=
    fun _ => rfl
  let β : ↥(commV L) →* ↥(coreMod n) := Φ.symm.toMonoidHom.comp π₀
  have hβs : Function.Surjective β := Φ.symm.surjective.comp hπ₀
  have hβ1 : ∀ u : ↥(commV L), β u = 1 ↔ π₀ u = 1 := by
    intro u
    show Φ.symm (π₀ u) = 1 ↔ π₀ u = 1
    rw [MulEquiv.symm_apply_eq, map_one]
  have hβker : β.ker = (commV L ⊓ fixV L).subgroupOf (commV L) := by
    ext u
    constructor
    · intro hu
      have h1 : β u = 1 := MonoidHom.mem_ker.mp hu
      have h2 : π₀ u = 1 := (hβ1 u).mp h1
      have h3 : u ∈ π₀.ker := MonoidHom.mem_ker.mpr h2
      rwa [hker] at h3
    · intro hu
      have h3 : u ∈ π₀.ker := by rwa [hker]
      have h2 : π₀ u = 1 := MonoidHom.mem_ker.mp h3
      exact MonoidHom.mem_ker.mpr ((hβ1 u).mpr h2)
  have hβu : ∀ u, coreHeart n (β u) = π₀ u := by
    intro u
    change Φ (β u) = π₀ u
    rw [show β u = Φ.symm (π₀ u) from rfl, Φ.apply_symm_apply]
  exact ⟨⟨α, hα, π, hπs, hπα, π₀, hπ₀, hker, heq, β, hβs, hβker, hβu⟩⟩

private theorem altConv_coreAct {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {n : ℕ} (hno : Odd n) (C : AltConv V L n)
    (γ : alternatingGroup (Fin n)) (u : ↥(commV L))
    (hu : ((C.π γ : ↥L) : MulAut V) (u : V) ∈ commV L) :
    C.β ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ =
      coreAct n (γ : Equiv.Perm (Fin n)) (C.β u) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective
    (Multiplicative.toAdd (C.π₀ u))
  set m₀ : ↥(coreMod n) :=
    (CFSG.Quasithin.C124.coreEvenEquiv n).symm (Multiplicative.ofAdd x) with hm₀
  have hm₀x : coreHeart n m₀ = Multiplicative.ofAdd (x : altHeart n) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_coreHeart, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  have hπu : C.π₀ u = Multiplicative.ofAdd (x : altHeart n) :=
    Multiplicative.toAdd.injective hx.symm
  have hβu : C.β u = m₀ := by
    apply (coreHeart_bijective hno).1
    rw [C.hβu, hm₀x, hπu]
  have h1 := C.heq (C.π γ) u ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ rfl x hπu
  rw [C.hπα] at h1
  have h1' : C.π₀ ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (C.π₀ u))) := by
    apply Multiplicative.toAdd.injective
    rw [h1, ← hx, altAct_mk]
    rfl
  have h2 : coreHeart n ⟨permAct n (γ : Equiv.Perm (Fin n)) (C.β u), by
      rw [hβu]; exact permAct_mem_coreMod _ m₀.2⟩ =
      Multiplicative.ofAdd (altAct (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (C.π₀ u))) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_coreHeart_permAct, hβu, hm₀x, hx]
    rfl
  have h3 : coreHeart n (C.β ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩) = coreHeart n
      ⟨permAct n (γ : Equiv.Perm (Fin n)) (C.β u), by
        rw [hβu]; exact permAct_mem_coreMod _ m₀.2⟩ := by
    rw [show coreHeart n (C.β ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩) =
      C.π₀ ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ from by
        rw [← C.hβu], h1', h2]
  exact (coreHeart_bijective hno).1 h3

private theorem altConv_betaQ {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {n : ℕ} (hno : Odd n) (C : AltConv V L n) :
    ∃ βq : ↥(commV L) →* (↥(FFModel.altDn n).sec ⧸
        (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec),
      Function.Surjective βq ∧
      (∀ u, βq u = 1 ↔ (u : V) ∈ commV L ⊓ fixV L) ∧
      (∀ (γ : (FFModel.altDn n).Gam) (u : ↥(commV L)) (m : ↥(FFModel.altDn n).sec)
        (hu : ((C.π γ : ↥L) : MulAut V) (u : V) ∈ commV L)
        (hm : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
          (FFModel.altDn n).sec),
        βq u = QuotientGroup.mk m →
          βq ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ =
            QuotientGroup.mk ⟨(FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb), hm⟩) := by
  let D := FFModel.altDn n
  let N : Subgroup ↥D.sec := D.ker.subgroupOf D.sec
  have hNbot : N = ⊥ := CFSG.Quasithin.B69.natKer_inf_eq_bot hno
  let β' : ↥(commV L) →* ↥D.sec := C.β
  have hβ1 : ∀ u : ↥(commV L), C.β u = 1 ↔ C.π₀ u = 1 := by
    intro u
    constructor
    · intro h
      rw [← C.hβu, h, map_one]
    · intro h
      apply (coreHeart_bijective hno).1
      rw [C.hβu, h, map_one]
  let βq : ↥(commV L) →* (↥D.sec ⧸ N) := (QuotientGroup.mk' N).comp β'
  refine ⟨βq, (QuotientGroup.mk'_surjective N).comp C.hβs, ?_, ?_⟩
  · intro u
    show βq u = 1 ↔ (u : V) ∈ commV L ⊓ fixV L
    rw [show βq u = QuotientGroup.mk (β' u) from rfl, QuotientGroup.eq_one_iff, hNbot,
      Subgroup.mem_bot]
    change C.β u = 1 ↔ (u : V) ∈ commV L ⊓ fixV L
    rw [hβ1 u, ← MonoidHom.mem_ker, C.hker, Subgroup.mem_subgroupOf]
  · intro γ u m hu hm hβq
    have hm_eq : m = β' u := by
      have h1 := QuotientGroup.eq.mp hβq
      rw [hNbot, Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact h1.symm
    have hβv := altConv_coreAct hno C γ u hu
    cases hm_eq
    show βq ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ = QuotientGroup.mk
      ⟨D.act γ (β' u), hm⟩
    rw [show βq ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ =
      QuotientGroup.mk (β' ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩) from rfl,
      show β' ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ =
        C.β ⟨((C.π γ : ↥L) : MulAut V) (u : V), hu⟩ from rfl, hβv]
    rfl

private theorem altDn_realizes_of_naturalSection {V : Type} [CommGroup V] [Finite V]
    {L : Subgroup (MulAut V)} {n : ℕ} (hno : Odd n)
    (e : ↥L ≃* alternatingGroup (Fin n)) (h : IsAltNaturalSection L (commV L) n) :
    (FFModel.altDn n).Realizes L (commV L) (gomiWXKer L) := by
  obtain ⟨C⟩ := altConv_of_naturalSection hno e h
  obtain ⟨βq, hβqs, hβq1, hβqe⟩ := altConv_betaQ hno C
  refine ⟨C.π, C.hπs, inf_le_left, inf_le_right, ?_, ?_, ?_, ?_, ⟨βq, hβqs, hβq1, ?_⟩⟩
  · intro l u hu
    exact commV_apply_mem_of_mem l.2 hu
  · intro l z hz
    exact ⟨commV_apply_mem_of_mem l.2 hz.1,
      fixV_apply_mem_of_mem_normalizer (Subgroup.le_normalizer l.2) hz.2⟩
  · intro γ m hm
    change ↥(alternatingGroup (Fin n)) at γ
    exact permAct_mem_coreMod ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) hm
  · intro γ m hm
    change ↥(alternatingGroup (Fin n)) at γ
    have hfix : permAct n ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        (allOnes n) = allOnes n := by
      ext i
      rw [permAct_apply]
      rfl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm.1
    change permAct n ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        (allOnes n ^ k) ∈ Subgroup.zpowers (allOnes n) ∧
      permAct n ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        (allOnes n ^ k) ∈ coreMod n
    have h1 : permAct n ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        (allOnes n ^ k) = (permAct n ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
          (allOnes n)) ^ k := map_zpow (permAct n
            ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) (allOnes n) k
    exact ⟨Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [h1, hfix]⟩,
      permAct_mem_coreMod ((γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) hm.2⟩
  · intro γ u m hu hm hβ
    exact hβqe γ u m hu hm hβ

private structure AltFixVData (V : Type*) [CommGroup V] [Finite V] where
  H : Subgroup (MulAut V)
  L : Subgroup (MulAut V)
  A : Subgroup (MulAut V)
  n : ℕ
  hV : ∀ v : V, v ^ 2 = 1
  e : ↥L ≃* alternatingGroup (Fin n)
  hn5 : 5 ≤ n
  hLH : L ≤ H
  hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L
  hHA : H ≤ L ⊔ A
  hoff : IsFFStarOffender H A
  hAL : ¬ ∀ a ∈ A, ∀ l ∈ L, a * l = l * a

variable {V : Type} [CommGroup V] [Finite V]

private def AltFixVData.fixW (D : AltFixVData V) : Subgroup V :=
  fixV (CFSG.Open.pCoreOf 2 D.H)

private def altFixVDataOf {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L A : Subgroup (MulAut W)} {n : ℕ}
    (e : ↥L ≃* alternatingGroup (Fin n)) (hn5 : 5 ≤ n)
    (hA : IsFFStarOffender Y A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLA : ⁅L, A⁆ ≠ ⊥) : AltFixVData W where
  H := L ⊔ A
  L := L
  A := A
  n := n
  hV := hW
  e := e
  hn5 := hn5
  hLH := le_sup_left
  hLn := by
    intro h hh l hl
    have hnorm : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      sup_le Subgroup.le_normalizer hAN
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hh) l).1 hl
  hHA := le_rfl
  hoff := ⟨le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
  hAL := by
    intro hc
    apply hLA
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hc a ha l hl).symm

private theorem altFixV_inf_pCoreOf (D : AltFixVData V) : D.L ⊓ CFSG.Open.pCoreOf 2 D.H = ⊥ := by
  have hn5 : 5 ≤ D.n := D.hn5
  have hsimple : IsSimpleGroup ↥D.L := by
    have : IsSimpleGroup (alternatingGroup (Fin D.n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup D.e
  have hnorm : ((D.L ⊓ CFSG.Open.pCoreOf 2 D.H).subgroupOf D.L).Normal :=
    (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y l hy hl =>
      ⟨D.L.mul_mem (D.L.mul_mem hl hy.1) (D.L.inv_mem hl),
        conj_mem_pCoreOf (D.hLH hl) hy.2⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥D.L _ _ _ hnorm with h | h
  · refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (⟨x, hx.1⟩ : ↥D.L) ∈ (D.L ⊓ CFSG.Open.pCoreOf 2 D.H).subgroupOf D.L := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
  · exfalso
    have hLP : D.L ≤ CFSG.Open.pCoreOf 2 D.H := fun x hx => by
      have hx' : (⟨x, hx⟩ : ↥D.L) ∈ (D.L ⊓ CFSG.Open.pCoreOf 2 D.H).subgroupOf D.L := by
        rw [h]; trivial
      exact hx'.2
    have h2 : IsPGroup 2 ↥D.L :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.H).to_le hLP
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.alt_not_two_group (by omega : 3 ≤ D.n)
      (h2.of_surjective D.e.toMonoidHom D.e.surjective)

private theorem altFixV_commute_pCoreOf (D : AltFixVData V) :
    ∀ x ∈ D.L, ∀ q ∈ CFSG.Open.pCoreOf 2 D.H, x * q = q * x := by
  intro x hx q hq
  have h1 : x * q * x⁻¹ * q⁻¹ ∈ D.L := by
    have := D.L.mul_mem hx (D.hLn q (CFSG.LieType.BorelTits.pCoreOf_le 2 D.H hq) x⁻¹
      (D.L.inv_mem hx))
    simpa [mul_assoc] using this
  have h2 : x * q * x⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 D.H :=
    (CFSG.Open.pCoreOf 2 D.H).mul_mem (conj_mem_pCoreOf (D.hLH hx) hq)
      ((CFSG.Open.pCoreOf 2 D.H).inv_mem hq)
  have h3 : x * q * x⁻¹ * q⁻¹ ∈ D.L ⊓ CFSG.Open.pCoreOf 2 D.H := ⟨h1, h2⟩
  rw [altFixV_inf_pCoreOf D, Subgroup.mem_bot] at h3
  calc x * q = (x * q * x⁻¹ * q⁻¹) * q * x := by group
    _ = q * x := by rw [h3]; group

private theorem altFixV_normalizer (D : AltFixVData V) :
    D.A ≤ Subgroup.normalizer (D.L : Set (MulAut V)) :=
  le_normalizer_of_conj fun a ha l hl => D.hLn a (D.hoff.1 ha) l hl

private theorem altFixV_sq_mem (D : AltFixVData V) : ∀ x ∈ D.H, x ^ 2 ∈ D.L := by
  intro x hx
  obtain ⟨l, hl, a, ha, rfl⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.exists_mul_of_sup
      (altFixV_normalizer D) (D.hHA hx)
  have ha1 : a * a = 1 := by
    simpa [pow_two] using D.hoff.2.2.1.2 a ha
  have h := D.hLn a (D.hoff.1 ha) l hl
  have hsq : (l * a) ^ 2 = l * (a * l * a⁻¹) := by
    rw [pow_two]
    calc (l * a) * (l * a) = l * (a * l * a⁻¹) * (a * a) := by group
      _ = l * (a * l * a⁻¹) := by rw [ha1, mul_one]
  rw [hsq]
  exact D.L.mul_mem hl h

private theorem altFixV_odd_mem (D : AltFixVData V) :
    ∀ x ∈ D.H, Odd (orderOf x) → x ∈ D.L := by
  intro x hx ho
  obtain ⟨m, hm⟩ := ho
  have hx1 : x ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one x
  have h : (x ^ 2) ^ (m + 1) = x := by
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hx1, one_mul]
  exact h ▸ D.L.pow_mem (altFixV_sq_mem D x hx) (m + 1)

private theorem altFixV_kernel (D : AltFixVData V) :
    D.H ⊓ centSub D.fixW = CFSG.Open.pCoreOf 2 D.H :=
  CFSG.Quasithin.B1Red.kernel_eq_pCoreOf D.hV (altFixV_odd_mem D)
    (altFixV_commute_pCoreOf D)

private theorem altFixV_pCoreOf_autSub (D : AltFixVData V) :
    CFSG.Open.pCoreOf 2 (autSub D.H D.fixW) = ⊥ :=
  CFSG.Quasithin.B1Red.pCoreOf_autSub_eq_bot (altFixV_kernel D)

private theorem altFixV_restriction_equiv (D : AltFixVData V) :
    ∃ eL : ↥D.L ≃* ↥(autSub D.L D.fixW),
      ∀ (l : ↥D.L) (w : ↥D.fixW),
        (((eL l : ↥(autSub D.L D.fixW)) : MulAut D.fixW) w : V) = (l : MulAut V) w.1 := by
  have hHst : D.H ≤ stabSub D.fixW := le_stabSub_fixV_pCoreOf D.H
  have hLst : D.L ≤ stabSub D.fixW := D.hLH.trans hHst
  let fL : ↥D.L →* MulAut D.fixW := (resHom D.fixW).comp (Subgroup.inclusion hLst)
  have hfL_mem : ∀ l, fL l ∈ autSub D.L D.fixW := fun l =>
    mem_autSub.2 ⟨⟨l, hLst l.2⟩, l.2, rfl⟩
  let φ : ↥D.L →* ↥(autSub D.L D.fixW) := fL.codRestrict _ hfL_mem
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : fL l = 1 := congrArg Subtype.val hl
    have h2 : (⟨(l : MulAut V), hLst l.2⟩ : stabSub D.fixW) ∈ (resHom D.fixW).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
    have h3 : (l : MulAut V) ∈ D.H ⊓ centSub D.fixW := ⟨D.hLH l.2, h2⟩
    rw [altFixV_kernel D] at h3
    have h4 : (l : MulAut V) ∈ D.L ⊓ CFSG.Open.pCoreOf 2 D.H := ⟨l.2, h3⟩
    rw [altFixV_inf_pCoreOf D, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hψ
    exact ⟨⟨g.1, hgL⟩, Subtype.ext hg⟩
  refine ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun l w => rfl⟩

private theorem altFixV_quasithinGenFitting (D : AltFixVData V) :
    quasithinGenFitting (autSub D.H D.fixW) = autSub D.L D.fixW := by
  obtain ⟨eL, -⟩ := altFixV_restriction_equiv D
  let eLb : ↥(autSub D.L D.fixW) ≃* alternatingGroup (Fin D.n) := eL.symm.trans D.e
  have hn5 : 5 ≤ D.n := D.hn5
  have hq : CFSG.Open.IsQuasisimple ↥(autSub D.L D.fixW) :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt (by omega) eLb
  have hconj : ∀ y ∈ autSub D.H D.fixW, ∀ l ∈ autSub D.L D.fixW,
      y * l * y⁻¹ ∈ autSub D.L D.fixW :=
    fun y hy l hl => autSub_conj_mem (fun x hx y hy => D.hLn x hx y hy) hy hl
  have h2 : ∀ y ∈ autSub D.H D.fixW, ∃ k : ℕ, y ^ 2 ^ k ∈ autSub D.L D.fixW := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    exact ⟨1, mem_autSub.2 ⟨g ^ 2, altFixV_sq_mem D g hgH, by simp [map_pow]⟩⟩
  exact CFSG.Quasithin.C124.quasithinGenFitting_eq_of_two_group_quot
    (autSub_mono D.hLH D.fixW) hconj (Or.inl hq) h2 (altFixV_pCoreOf_autSub D)

private theorem altFixV_offender (D : AltFixVData V) :
    IsFFStarOffender (autSub D.H D.fixW) (autSub D.A D.fixW) := by
  have hWA : commSub D.fixW D.A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply D.hAL
    intro a ha l hl
    have h1 : a ∈ D.H ⊓ centSub D.fixW := ⟨D.hoff.1 ha, fun w hw => h hw a ha⟩
    rw [altFixV_kernel D] at h1
    exact (altFixV_commute_pCoreOf D l hl a h1).symm
  exact B7_1_1 D.hoff (fun a ha w hw => fixV_pCoreOf_inv a (D.hoff.1 ha) w hw) hWA

private theorem altFixV_naturalSection (D : AltFixVData V) (h85 : GF2EightFive)
    (hn7 : D.n = 7 ∨ 9 ≤ D.n) :
    IsAltNaturalSection (autSub D.L D.fixW) (commV (autSub D.H D.fixW)) D.n ∨
      (D.n = 7 ∧ autSub D.H D.fixW = autSub D.L D.fixW ∧
        Nat.card (commV (autSub D.H D.fixW)) = 2 ^ 4) := by
  obtain ⟨eL, -⟩ := altFixV_restriction_equiv D
  let eLb : ↥(autSub D.L D.fixW) ≃* alternatingGroup (Fin D.n) := eL.symm.trans D.e
  have hW2 : ∀ v : ↥D.fixW, v ^ 2 = 1 := fun v => Subtype.ext (D.hV v)
  exact h85 ↥D.fixW hW2 (autSub D.H D.fixW) (autSub D.L D.fixW)
    (altFixV_quasithinGenFitting D).symm D.n hn7 ⟨eLb⟩ ⟨_, altFixV_offender D⟩

private theorem altFixV_commSub_fixW (D : AltFixVData V) (hperf : Group.IsPerfect ↥D.L)
    (hW1 : commV D.L ≤ D.fixW) : commSub D.fixW D.L = commV D.L := by
  have hperf' : commutator ↥D.L = ⊤ := hperf.commutator_eq_top
  apply le_antisymm
  · calc commSub D.fixW D.L ≤ commSub ⊤ D.L := commSub_mono le_top le_rfl
      _ = commV D.L := (commV_eq_commSub D.L).symm
  · calc commV D.L = commSub (commV D.L) D.L :=
        (@commSub_commV_of_perfect V _ D.L hperf').symm
      _ ≤ commSub D.fixW D.L := commSub_mono hW1 le_rfl

private theorem altFixV_realizes_of_natural {n : ℕ} (D : AltFixVData V)
    (hperf : Group.IsPerfect ↥D.L) (hW1 : commV D.L ≤ D.fixW)
    (hReal : (FFModel.altDn n).Realizes (autSub D.L D.fixW)
      (commV (autSub D.L D.fixW)) (gomiWXKer (autSub D.L D.fixW))) :
    (FFModel.altDn n).Realizes D.L (commV D.L) (gomiWXKer D.L) := by
  obtain ⟨eL, heL⟩ := altFixV_restriction_equiv D
  have hst : D.L ≤ stabSub D.fixW := D.hLH.trans (le_stabSub_fixV_pCoreOf D.H)
  have hequiv : ∀ (h : ↥(autSub D.L D.fixW)) (w : ↥D.fixW),
      (D.fixW).subtype ((h : MulAut D.fixW) w) =
        ((eL.symm h : ↥D.L) : MulAut V) ((D.fixW).subtype w) := by
    intro h w
    have := heL (eL.symm h) w
    rwa [eL.apply_symm_apply] at this
  have hker : (D.fixW).subtype.ker ≤ gomiWXKer (autSub D.L D.fixW) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [show x = 1 from Subtype.ext hx]
    exact Subgroup.one_mem _
  have hR := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16k_realizes_map (D := FFModel.altDn n)
    hReal (D.fixW).subtype hker eL.symm.toMonoidHom eL.symm.surjective hequiv
  have hU : (commV (autSub D.L D.fixW)).map (D.fixW).subtype = commV D.L := by
    rw [CFSG.Quasithin.B15P4.map_subtype_commV_autSub hst]
    exact altFixV_commSub_fixW D hperf hW1
  have hZ : (gomiWXKer (autSub D.L D.fixW)).map (D.fixW).subtype =
      gomiWXKer D.L := by
    rw [gomiWXKer, Subgroup.map_inf_eq _ _ _ (D.fixW).subtype_injective,
      CFSG.Quasithin.map_subtype_fixV_autSub hst, hU, gomiWXKer]
    rw [← inf_assoc, inf_eq_left.mpr hW1]
  rw [hU, hZ] at hR
  exact hR

private theorem eq_two_of_dvd_four {n : ℕ} (hdvd : n ∣ 4)
    (h1 : n ≠ 1) (h4 : n ≠ 4) : n = 2 := by
  have hdvd2 : n ∣ 2 ^ 2 := by simpa using hdvd
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [hk_eq] at h1
    exact absurd rfl h1
  · have hk1 : k = 1 ∨ k = 2 := by omega
    rcases hk1 with rfl | rfl
    · rw [hk_eq]
      norm_num
    · rw [hk_eq] at h4
      exact absurd rfl h4

private theorem altThree_irreducible {S : Type} [CommGroup S] [Finite S]
    (hS4 : Nat.card S = 4) (L : Subgroup (MulAut S))
    (hinf : fixV L = ⊥) :
    ∀ J : Subgroup S, (∀ γ ∈ L, ∀ x ∈ J, γ x ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  right
  by_contra htop
  have hJcard : Nat.card ↥J = 2 := by
    have hdvd : Nat.card ↥J ∣ 4 := by
      simpa [hS4] using Subgroup.card_subgroup_dvd_card J
    exact eq_two_of_dvd_four hdvd
      (fun h => hbot (Subgroup.eq_bot_of_card_eq J h))
      (fun h => htop (Subgroup.eq_top_of_card_eq J (by rw [h, hS4])))
  obtain ⟨y, hy1, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥J)).1 hJcard
  have htriv : ∀ γ ∈ L, ∀ j ∈ J, γ j = j := by
    intro γ hγ j hj
    let jJ : ↥J := ⟨j, hj⟩
    have hmem : γ (y : S) ∈ J := hJ γ hγ y y.2
    have hne : (⟨γ (y : S), hmem⟩ : ↥J) ≠ 1 := by
      intro h
      have hγ1 : γ (y : S) = γ 1 := by
        rw [show γ (y : S) = 1 from congrArg Subtype.val h, map_one γ]
      exact hy1 (Subtype.ext (γ.injective hγ1))
    have hγy : γ (y : S) = y := congrArg Subtype.val (hyuniq ⟨γ (y : S), hmem⟩ hne)
    rcases eq_or_ne jJ 1 with h1 | h1
    · rw [show j = 1 from congrArg Subtype.val h1, map_one]
    · have hjy : jJ = y := hyuniq jJ h1
      rw [show j = (y : S) from congrArg Subtype.val hjy, hγy]
  have hJfix : J ≤ fixV L := by
    intro j hj
    rw [CFSG.Quasithin.mem_fixV]
    intro l hl
    exact htriv l hl j hj
  have hJbot : J = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    rw [← hinf]
    exact hJfix hj
  exact hbot hJbot

private theorem altThree_restriction_equiv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hLS : L ≤ stabSub (commV L))
    (h4 : Nat.card (commV L) = 4) (hinf : commV L ⊓ fixV L = ⊥)
    (hLcard : Nat.card L = 3) :
    ∃ eL : ↥L ≃* ↥(autSub L (commV L)),
      ∀ (l : ↥L) (s : ↥(commV L)),
        (((eL l : ↥(autSub L (commV L))) : MulAut ↥(commV L)) s : W) =
          (l : MulAut W) s.1 := by
  let fL : ↥L →* MulAut ↥(commV L) := (resHom (commV L)).comp (Subgroup.inclusion hLS)
  have hfL_mem : ∀ l, fL l ∈ autSub L (commV L) := fun l =>
    mem_autSub.2 ⟨⟨l, hLS l.2⟩, l.2, rfl⟩
  let φ : ↥L →* ↥(autSub L (commV L)) := fL.codRestrict _ hfL_mem
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases @Subgroup.eq_bot_or_eq_top_of_prime_card ↥L _ φ.ker
      ⟨by rw [hLcard]; norm_num⟩ with h | h
    · exact h
    · exfalso
      have hSfix : commV L ≤ fixV L := by
        intro s hs
        rw [CFSG.Quasithin.mem_fixV]
        intro l hl
        have hl' : φ ⟨l, hl⟩ = 1 := by
          have hmem : (⟨l, hl⟩ : ↥L) ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
          exact MonoidHom.mem_ker.mp hmem
        have h2 := congrArg (fun f : ↥(autSub L (commV L)) =>
          (((f : MulAut ↥(commV L)) ⟨s, hs⟩ : ↥(commV L)) : W)) hl'
        exact h2
      have hSbot : commV L = ⊥ := by
        rw [eq_bot_iff]
        intro s hs
        exact hinf ▸ ⟨hs, hSfix hs⟩
      rw [hSbot, Subgroup.card_bot] at h4
      omega
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hψ
    exact ⟨⟨g.1, hgL⟩, Subtype.ext hg⟩
  refine ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩, fun l s => rfl⟩

private theorem alt_ge_seven (h85 : GF2EightFive) (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (hyp : GomiFact37Hyp Y S L) {m : ℕ} (hm : 2 ≤ m)
    (h7 : 7 ≤ 2 * m - 1) (hL : IsAlt ↥L (2 * m - 1))
    (hP : ⁅L, sSup (PstarSet Y)⁆ ≠ ⊥) :
    (∃ m' : ℕ, 2 ≤ m' ∧ IsAlt ↥L (2 * m' - 1) ∧
        (FFModel.altDn (2 * m' - 1)).Realizes L (commV L) (gomiWXKer L)) ∨
      (IsAlt ↥L 7 ∧ Nat.card (commV L) = 16) := by
  obtain ⟨-, -, hLY, hsn, -, -⟩ := hyp
  obtain ⟨A, hAP, hLA⟩ := exists_mem_commutator_ne_bot_of_sSup hP
  have hA : IsFFStarOffender Y A := hAP.1
  obtain ⟨e⟩ := hL
  have hn5 : 5 ≤ 2 * m - 1 := by omega
  have hqL : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isAlt hn5 ⟨e⟩
  have hcomp : CFSG.IsComponent (L.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hqL,
      hsn⟩
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    le_normalizer_of_offender_component (fun v : W => by rw [← pow_two]; exact hW v)
      hLY hcomp hA
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have hW1 : commV L ≤ fixV (CFSG.Open.pCoreOf 2 (L ⊔ A)) :=
    commV_le_fixV_pCoreOf h85 hW (by omega) hodd ⟨e⟩ hAP hAN hLA
  let D : AltFixVData W := altFixVDataOf hW e hn5 hA hAN hLA
  have hn5' : 5 ≤ D.n := hn5
  have hn7 : 2 * m - 1 = 7 ∨ 9 ≤ 2 * m - 1 := by
    by_cases h : 2 * m - 1 = 7
    · exact Or.inl h
    · right; omega
  rcases altFixV_naturalSection D h85 hn7 with hnat | ⟨h7n, hHeq, hcard⟩
  · have hL'le : autSub L D.fixW ≤ autSub (L ⊔ A) D.fixW := autSub_mono le_sup_left D.fixW
    have hnatL : IsAltNaturalSection (autSub L D.fixW) (commV (autSub L D.fixW)) D.n :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.isAltNaturalSection_commV_of_le
        hL'le (by omega) hnat
    obtain ⟨eL, -⟩ := altFixV_restriction_equiv D
    let eLb : ↥(autSub L D.fixW) ≃* alternatingGroup (Fin D.n) := eL.symm.trans D.e
    have hRealL : (FFModel.altDn D.n).Realizes (autSub L D.fixW)
        (commV (autSub L D.fixW)) (gomiWXKer (autSub L D.fixW)) :=
      altDn_realizes_of_naturalSection hodd eLb hnatL
    exact Or.inl ⟨m, hm, ⟨e⟩, altFixV_realizes_of_natural D hqL.1 hW1 hRealL⟩
  · have hst : D.L ≤ stabSub D.fixW := D.hLH.trans (le_stabSub_fixV_pCoreOf D.H)
    have hcard' : Nat.card (commV (autSub D.L D.fixW)) = 2 ^ 4 := hHeq ▸ hcard
    have h16 : Nat.card (commV L) = 16 := by
      change Nat.card ↥(commV D.L) = 16
      rw [← altFixV_commSub_fixW D hqL.1 hW1,
        ← CFSG.Quasithin.B15P4.map_subtype_commV_autSub hst,
        Subgroup.card_map_of_injective (D.fixW).subtype_injective]
      exact hcard'.trans (by norm_num)
    exact Or.inr ⟨by rw [← h7n]; exact ⟨e⟩, h16⟩

private theorem alt_three_realizes (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL : IsAlt ↥L 3)
    (h4 : Nat.card (commV L) = 4) (hinf : commV L ⊓ fixV L = ⊥) :
    (FFModel.altDn 3).Realizes L (commV L) (gomiWXKer L) := by
  classical
  let S := commV L
  have hS2 : ∀ s : ↥S, s ^ 2 = 1 := fun s => Subtype.ext (by simpa using hW s)
  have hnt : Nontrivial ↥S := Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
  have hLS : L ≤ stabSub S :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant (fun l hl u hu => commV_apply_mem_of_mem hl hu)
  obtain ⟨e⟩ := hL
  have hLcard : Nat.card ↥L = 3 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  obtain ⟨eL, heL⟩ := altThree_restriction_equiv hLS h4 hinf hLcard
  let LS := autSub L S
  have hLScard : Nat.card ↥LS = 3 := by
    rw [← Nat.card_congr eL.toEquiv]
    exact hLcard
  have hinfLS : fixV LS = ⊥ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [CFSG.Quasithin.map_subtype_fixV_autSub hLS, Subgroup.map_bot]
    exact hinf
  have hirr := altThree_irreducible h4 LS hinfLS
  obtain ⟨π, -, hR⟩ := @CFSG.QuasithinUnique.L246.exists_altDn_three ↥S _
    hS2 hnt LS hLScard hirr
  have hker : S.subtype.ker ≤ (⊥ : Subgroup ↥S) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [show x = 1 from Subtype.ext hx]
    exact Subgroup.one_mem _
  have hequiv : ∀ (h : ↥LS) (s : S),
      S.subtype ((h : MulAut S) s) = ((eL.symm h : ↥L) : MulAut W) (S.subtype s) := by
    intro h s
    have := heL (eL.symm h) ⟨s, s.2⟩
    rwa [eL.apply_symm_apply] at this
  let π' : (FFModel.altDn 3).Gam →* ↥LS := π
  have hRπ : (FFModel.altDn 3).RealizesVia LS ⊤ ⊥ π' := hR
  have hR' := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16k_realizesVia_map (D := FFModel.altDn 3)
    hRπ S.subtype hker eL.symm.toMonoidHom eL.symm.surjective hequiv
  have hU : (⊤ : Subgroup ↥S).map S.subtype = S := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hZ : (⊥ : Subgroup ↥S).map S.subtype = ⊥ := Subgroup.map_bot S.subtype
  have hZg : gomiWXKer L = ⊥ := by rw [gomiWXKer, hinf]
  rw [hU, hZ] at hR'
  rw [hZg]
  exact ⟨_, hR'⟩

theorem gomiFact37Two_of_isAlt (h85 : GF2EightFive) (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (hyp : GomiFact37Hyp Y S L) {m : ℕ} (hm : 2 ≤ m)
    (hm5 : 2 * m - 1 ≠ 5) (hL : IsAlt ↥L (2 * m - 1)) (hP : ⁅L, sSup (PstarSet Y)⁆ ≠ ⊥) :
    (∃ m' : ℕ, 2 ≤ m' ∧ IsAlt ↥L (2 * m' - 1) ∧
        (FFModel.altDn (2 * m' - 1)).Realizes L (commV L) (gomiWXKer L)) ∨
      (IsAlt ↥L 7 ∧ Nat.card (commV L) = 16) := by
  obtain ⟨hPne, hSyl, hLY, hsn, htype, h3card⟩ := hyp
  by_cases h3 : 2 * m - 1 = 3
  · have hL3 : IsAlt ↥L 3 := h3 ▸ hL
    have h4 : Nat.card (commV L) = 4 := h3card hL3
    have hLcard : Nat.card ↥L = 3 := by
      obtain ⟨e⟩ := hL3
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hinf : commV L ⊓ fixV L = ⊥ :=
      commV_inf_fixV_eq_bot_of_odd_card hW L (by rw [hLcard]; decide)
    exact Or.inl ⟨2, by norm_num, hL3, alt_three_realizes hW hL3 h4 hinf⟩
  · have h7 : 7 ≤ 2 * m - 1 := by omega
    exact alt_ge_seven h85 hW ⟨hPne, hSyl, hLY, hsn, htype, h3card⟩ hm h7 hL hP

omit [Finite W] in
private theorem altDn_five_pi_injective
    {L : Subgroup (MulAut W)} {π : (FFModel.altDn 5).Gam →* ↥L}
    (hπs : Function.Surjective π) (hLne : L ≠ ⊥) : Function.Injective π := by
  have h5card : 5 ≤ Nat.card (Fin 5) := by simp
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup h5card
  have : IsSimpleGroup (FFModel.altDn 5).Gam := this
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · exact hk
  · exfalso
    apply hLne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have h2 : γ ∈ π.ker := by rw [hk]; exact Subgroup.mem_top γ
    rw [MonoidHom.mem_ker] at h2
    rw [Subgroup.mem_bot]
    have hγ' : ((π γ : ↥L) : MulAut W) = x := congrArg Subtype.val hγ
    have h2' : ((π γ : ↥L) : MulAut W) = 1 := congrArg Subtype.val h2
    rw [← hγ', h2']

theorem gomiFact37Two_of_gf2EightFive (h85 : GF2EightFive) : GomiFact37Two := by
  intro W _ _ hW Y S L hyp hP
  have hHyp : GomiFact37Hyp Y S L := hyp
  obtain ⟨hPne, hSyl, hLY, hsn, htype, h3card⟩ := hyp
  rcases htype with ⟨m, hm, hSL | hAlt⟩ | ⟨hq, hZ, hA7⟩
  · rcases gomiFact37Two_of_isSLn hW hHyp hm hSL hP with h | ⟨hm2, hreal⟩
    · exact Or.inl ⟨m, hm, hSL, h⟩
    ·
      have hreal' : (FFModel.altDn 5).Realizes L (commV L) (gomiWXKer L) := hreal
      obtain ⟨π, hπR⟩ := hreal
      have hπs : Function.Surjective π := hπR.1
      obtain ⟨K, _, _, _, ⟨e⟩⟩ := hSL
      have hntSL : Nontrivial ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
        CFSG.Quasithin.B69.nontrivial_statedSL_two
      have hntL : Nontrivial ↥L := by
        have hcard : 1 < Nat.card ↥L := by
          rw [Nat.card_congr e.toEquiv]
          exact Finite.one_lt_card_iff_nontrivial.mpr hntSL
        exact Finite.one_lt_card_iff_nontrivial.mp hcard
      have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp hntL
      have hπinj : Function.Injective π := altDn_five_pi_injective hπs hLne
      let e5 : ↥L ≃* alternatingGroup (Fin 5) :=
        (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm
      exact Or.inr (Or.inl ⟨3, by norm_num, ⟨e5⟩, by simpa using hreal'⟩)
  · by_cases h5 : 2 * m - 1 = 5
    · rcases gomiFact37Two_of_isAlt_five hW hHyp (by rwa [h5] at hAlt) hP with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases gomiFact37Two_of_isAlt h85 hW hHyp hm h5 hAlt hP with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · exfalso
    exact not_tripleA7_of_gomiFact37Hyp hW
      ⟨hPne, hSyl, hLY, hsn, Or.inr ⟨hq, hZ, hA7⟩, h3card⟩
      (by
        intro hbot
        apply hP
        rw [eq_bot_iff]
        calc ⁅L, sSup (PstarSet Y)⁆ ≤ ⁅L, ffJ Y⁆ :=
              Subgroup.commutator_mono le_rfl (sSup_pstarSet_le_ffJ Y)
          _ = ⊥ := hbot)
      ⟨hq, hZ, hA7⟩

end CFSG.GroupTheory

end
