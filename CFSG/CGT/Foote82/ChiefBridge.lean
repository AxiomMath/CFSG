module

public import CFSG.CGT.Foote82.ChiefLin
public import CFSG.CGT.Foote82.LayerClosure
public import CFSG.CGT.Foote82.FModuleTransfer
public import CFSG.CGT.Foote82.BlockBasics
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW35

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev NHat (N : Subgroup G) : Type := ↥N ⧸ CFSG.pCore 2 ↥N

abbrev hatIn (N A : Subgroup G) : Subgroup (NHat N) :=
  (A.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))

@[expose] def footeX (N K : Subgroup G) : Subgroup G :=
  ((layerClosure (hatIn N K)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥N))).map N.subtype

theorem mem_pCore_iff {N : Subgroup G} (x : ↥N) :
    x ∈ CFSG.pCore 2 ↥N ↔ (x : G) ∈ pCoreOf 2 N := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem mk_eq_one_iff {N : Subgroup G} (x : ↥N) :
    (QuotientGroup.mk x : NHat N) = 1 ↔ (x : G) ∈ pCoreOf 2 N := by
  rw [QuotientGroup.eq_one_iff, mem_pCore_iff]

theorem mk_eq_mk_iff {N : Subgroup G} (x y : ↥N) :
    (QuotientGroup.mk x : NHat N) = QuotientGroup.mk y ↔ (x : G)⁻¹ * y ∈ pCoreOf 2 N := by
  rw [QuotientGroup.eq, mem_pCore_iff]
  rfl

theorem mem_footeX {N K : Subgroup G} {g : G} :
    g ∈ footeX N K ↔
      ∃ h : g ∈ N, (QuotientGroup.mk ⟨g, h⟩ : NHat N) ∈ layerClosure (hatIn N K) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

theorem footeX_le (N K : Subgroup G) : footeX N K ≤ N := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem core_le_footeX (N K : Subgroup G) : pCoreOf 2 N ≤ footeX N K := by
  intro g hg
  have hgN : g ∈ N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N hg
  refine (mem_footeX).mpr ⟨hgN, ?_⟩
  rw [(mk_eq_one_iff ⟨g, hgN⟩).mpr hg]
  exact Subgroup.one_mem _

structure ChiefHyp (N K Q : Subgroup G) : Prop where
  faithful : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N
  block : IsFooteBlock K K
  ftype : IsFType K
  two : IsPGroup 2 Q
  core_le : pCoreOf 2 N ≤ Q
  le : Q ≤ N
  normalizes : Q ≤ Subgroup.normalizer (K : Set G)
  cent : ⁅Q, K⁆ ≤ blockQ K
  blockU_le : blockU K ≤ pCoreOf 2 N
  subnormal : IsSubnormal K (N ⊓ Subgroup.normalizer (Q : Set G))

namespace ChiefHyp

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q)
include h

theorem K_le : K ≤ N :=
  (CFSG.Open.IsSubnormal.le h.subnormal).trans inf_le_left

theorem core_isPGroup : IsPGroup 2 (pCoreOf 2 N) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N

theorem le_normalizer_core : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N

theorem commutator_Q_le : ⁅K, Q⁆ ≤ blockU K :=
  IsFooteBlock.commutator_le_blockU h.block h.normalizes h.cent

theorem commutator_core_le : ⁅K, pCoreOf 2 N⁆ ≤ blockU K :=
  IsFooteBlock.commutator_le_blockU h.block (h.core_le.trans h.normalizes)
    ((Subgroup.commutator_mono h.core_le le_rfl).trans h.cent)

end ChiefHyp

theorem isPerfect_of_block {K : Subgroup G} (hK : IsFooteBlock K K) : Group.IsPerfect ↥K := by
  refine ⟨Subgroup.map_injective K.subtype_injective ?_⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
    IsFooteBlock.commutator_eq hK]

theorem le_pCore_of_normal {K : Subgroup G} (S : Subgroup ↥K) [S.Normal] (hS : IsPGroup 2 S) :
    S ≤ CFSG.pCore 2 ↥K :=
  le_sSup ⟨inferInstance, hS⟩

theorem isQuasisimple_of_block {K : Subgroup G} (hK : IsFooteBlock K K) {L : Type*} [Group L]
    (f : ↥K →* L) (hf : Function.Surjective f) (hker : f.ker ≤ CFSG.pCore 2 ↥K)
    (hU : ∀ k : ↥K, (k : G) ∈ blockU K → f k = 1) : CFSG.IsQuasisimple L := by
  haveI := isPerfect_of_block hK
  have hLp : Group.IsPerfect L := Group.IsPerfect.ofSurjective hf
  let g : L →* ↥K ⧸ CFSG.pCore 2 ↥K := f.liftOfSurjective hf
    ⟨QuotientGroup.mk' _, by rwa [QuotientGroup.ker_mk']⟩
  have hg : ∀ k, g (f k) = QuotientGroup.mk k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨f k, hg k⟩
  have hgk : g.ker ≤ Subgroup.center L := by
    intro l hl
    obtain ⟨k, rfl⟩ := hf l
    have hk : k ∈ CFSG.pCore 2 ↥K := by
      rw [MonoidHom.mem_ker, hg] at hl
      exact (QuotientGroup.eq_one_iff k).mp hl
    rw [Subgroup.mem_center_iff]
    intro l'
    obtain ⟨k', rfl⟩ := hf l'
    have hkQ : (k : G) ∈ blockQ K := (mem_pCore_iff k).mp hk
    have hc : ⁅(k : G), (k' : G)⁆ ∈ blockU K :=
      Subgroup.commutator_mem_commutator hkQ k'.2
    have h1 := hU ⁅k, k'⁆ (by
      rw [show ((⁅k, k'⁆ : ↥K) : G) = ⁅(k : G), (k' : G)⁆ from rfl]
      exact hc)
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have : f k * f k' = f k' * f k := by
      have := congrArg (· * (f k' * f k)) h1
      simpa [mul_assoc] using this
    exact this.symm
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ⟨⟨hK.quasisimple.1⟩, hK.quasisimple.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
        hK.quasisimple⟩
  exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hLp g hgs hgk).mpr hq

theorem isQuasisimple_open_of_native {L : Type*} [Group L] (h : CFSG.IsQuasisimple L) :
    CFSG.Open.IsQuasisimple L :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

@[expose] noncomputable def hatMap {N K : Subgroup G} (hKN : K ≤ N) : ↥K →* ↥(hatIn N K) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥N)).comp (Subgroup.inclusion hKN)).codRestrict
    (hatIn N K) fun k => ⟨Subgroup.inclusion hKN k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

theorem hatMap_apply {N K : Subgroup G} (hKN : K ≤ N) (k : ↥K) :
    ((hatMap hKN k : ↥(hatIn N K)) : NHat N) = QuotientGroup.mk (Subgroup.inclusion hKN k) :=
  rfl

theorem hatMap_surjective {N K : Subgroup G} (hKN : K ≤ N) : Function.Surjective (hatMap hKN) := by
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩

theorem mem_ker_hatMap {N K : Subgroup G} (hKN : K ≤ N) (k : ↥K) :
    k ∈ (hatMap hKN).ker ↔ (k : G) ∈ pCoreOf 2 N := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, hatMap_apply, OneMemClass.coe_one, mk_eq_one_iff]
  rfl

theorem ker_hatMap_le {N K : Subgroup G} (hKN : K ≤ N) : (hatMap hKN).ker ≤ CFSG.pCore 2 ↥K := by
  refine le_pCore_of_normal _ ?_
  refine IsPGroup.of_injective (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N)
    { toFun := fun k => ⟨((k : ↥K) : G), (mem_ker_hatMap hKN k).mp k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } ?_
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  have h1 := congrArg (fun x : ↥(pCoreOf 2 N) => (x : G)) hab
  simpa using h1

theorem mem_normalizer_layerClosure {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {y : Y}
    (hy : y ∈ Subgroup.normalizer (A : Set Y)) :
    y ∈ Subgroup.normalizer (layerClosure A : Set Y) := by
  haveI := CFSG.ComponentClassification.GrSLit.pLayer_two_normal' (X := Y)
  have key : ∀ y ∈ Subgroup.normalizer (A : Set Y), ∀ x ∈ layerClosure A,
      y * x * y⁻¹ ∈ layerClosure A := by
    intro y hy x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, a, ha, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨y * b * y⁻¹, ?_, y * a * y⁻¹, ?_, by group⟩
      · exact (inferInstance : (CFSG.pLayer Y 2).Normal).conj_mem b hb y
      · exact (Subgroup.mem_normalizer_iff.mp hy a).mp ha
    | one => simp
    | mul x z _ _ hx hz =>
      have : y * (x * z) * y⁻¹ = (y * x * y⁻¹) * (y * z * y⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hz
    | inv x _ hx =>
      have : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem commutator_eq_of_isPerfect {Y : Type*} [Group Y] {A : Subgroup Y}
    (hA : Group.IsPerfect ↥A) : ⁅A, A⁆ = A := by
  have h := congrArg (Subgroup.map A.subtype) hA.commutator_eq_top
  rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h

@[expose] def kClosure (N K : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | ∃ x ∈ footeX N K, ∃ k ∈ K, g = x * k * x⁻¹}

@[expose] def wOne (N K Q : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | ∃ γ ∈ footeX N K ⊔ Q, ∃ u ∈ blockU K, g = γ * u * γ⁻¹}

namespace ChiefHyp

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q)
include h

theorem isQuasisimple_hatK : CFSG.IsQuasisimple ↥(hatIn N K) :=
  isQuasisimple_of_block h.block (hatMap h.K_le) (hatMap_surjective h.K_le)
    (ker_hatMap_le h.K_le) fun k hk => (mem_ker_hatMap h.K_le k).mpr (h.blockU_le hk)

theorem hatK_le_centralizer :
    hatIn N K ≤ Subgroup.centralizer (hatIn N Q : Set (NHat N)) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have hk' : (k : G) ∈ K := hk
  have hq' : (q : G) ∈ Q := hq
  show (QuotientGroup.mk q : NHat N) * QuotientGroup.mk k =
    QuotientGroup.mk k * QuotientGroup.mk q
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff]
  have hc : ⁅(k : G)⁻¹, (q : G)⁻¹⁆ ∈ pCoreOf 2 N :=
    h.blockU_le (h.commutator_Q_le (Subgroup.commutator_mem_commutator (inv_mem hk')
      (inv_mem hq')))
  simpa [commutatorElement_def, mul_assoc] using hc

theorem mem_normalizer_of_mk_mem_centralizer {n : ↥N}
    (hn : (QuotientGroup.mk n : NHat N) ∈ Subgroup.centralizer (hatIn N Q : Set (NHat N))) :
    (n : G) ∈ Subgroup.normalizer (Q : Set G) := by
  have key : ∀ m : ↥N, (QuotientGroup.mk m : NHat N) ∈
      Subgroup.centralizer (hatIn N Q : Set (NHat N)) →
      ∀ x : G, x ∈ Q → (m : G) * x * (m : G)⁻¹ ∈ Q := by
    intro m hm x hx
    have hxN : x ∈ N := h.le hx
    have hc := Subgroup.mem_centralizer_iff.mp hm (QuotientGroup.mk ⟨x, hxN⟩)
      ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff] at hc
    have hconj : (m : G) * (((⟨x, hxN⟩ * m : ↥N) : G)⁻¹ * ((m * ⟨x, hxN⟩ : ↥N) : G)) *
        (m : G)⁻¹ ∈ pCoreOf 2 N :=
      (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_core m.2) _).mp hc
    have heq : (m : G) * x * (m : G)⁻¹ = x * ((m : G) *
        (((⟨x, hxN⟩ * m : ↥N) : G)⁻¹ * ((m * ⟨x, hxN⟩ : ↥N) : G)) * (m : G)⁻¹) := by
      simp [mul_assoc]
    rw [heq]
    exact Q.mul_mem hx (h.core_le hconj)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have hinv : (QuotientGroup.mk n⁻¹ : NHat N) ∈
      Subgroup.centralizer (hatIn N Q : Set (NHat N)) := by
    rw [QuotientGroup.mk_inv]
    exact inv_mem hn
  have := key n⁻¹ hinv _ hx
  simpa [mul_assoc] using this

theorem isSubnormal_hatK :
    IsSubnormal (hatIn N K) (Subgroup.centralizer (hatIn N Q : Set (NHat N))) := by
  have h1 : IsSubnormal (K.subgroupOf N) ((N ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf N) :=
    CFSG.Open.IsSubnormal.comap N.subtype h.subnormal
  have h2 := CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) h1
  have h3 : Subgroup.centralizer (hatIn N Q : Set (NHat N)) ≤
      ((N ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf N).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) := by
    intro c hc
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨n, Subgroup.mem_subgroupOf.mpr ⟨n.2, h.mem_normalizer_of_mk_mem_centralizer hc⟩, rfl⟩
  have h4 := CFSG.Open.IsSubnormal.inf_of_le h2 h3
  rwa [inf_eq_left.mpr h.hatK_le_centralizer] at h4

theorem hatK_le_pLayer : hatIn N K ≤ CFSG.pLayer (NHat N) 2 := by
  set C := Subgroup.centralizer (hatIn N Q : Set (NHat N)) with hC
  have hKC : hatIn N K ≤ C := h.hatK_le_centralizer
  set K' : Subgroup ↥C := (hatIn N K).subgroupOf C with hK'
  have hq : CFSG.IsQuasisimple ↥K' :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC) h.isQuasisimple_hatK
  have hcomp : CFSG.IsComponent K' :=
    ⟨hq, CFSG.Open.IsSubnormal.subgroupOf h.isSubnormal_hatK⟩
  have hnot : ¬ K' ≤ CFSG.pPrimeCore 2 ↥C := by
    intro hle
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable ↥(CFSG.pPrimeCore 2 ↥C) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card)
    haveI : Group.IsSolvable ↥K' := by
      haveI := hsolv
      exact solvable_of_solvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    haveI : Group.IsPerfect ↥K' := hq.1
    haveI : Nontrivial ↥K' := by
      haveI := hq.2.1.toNontrivial
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      exact not_subsingleton (↥K' ⧸ Subgroup.center ↥K') inferInstance
    exact Group.IsPerfect.not_isSolvable (G := ↥K') inferInstance
  have hpc : CFSG.IsPComponent 2 K' :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp hnot
  have hQ2 : IsPGroup 2 ↥(hatIn N Q) :=
    (h.two.comap_of_injective N.subtype Subtype.val_injective).map _
  have hbal := CFSG.ClassicalInvolution.l2PrimeBalance (NHat N) (hatIn N Q) hQ2
  have hle : K' ≤ CFSG.pLayer ↥C 2 := le_sSup hpc
  calc hatIn N K = K'.map C.subtype := by
        rw [hK', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKC]
    _ ≤ (CFSG.pLayer ↥C 2).map C.subtype := Subgroup.map_mono hle
    _ ≤ CFSG.pLayer (NHat N) 2 := hbal

theorem K_le_footeX : K ≤ footeX N K := by
  intro k hk
  refine (mem_footeX).mpr ⟨h.K_le hk, le_layerClosure ?_⟩
  exact ⟨⟨k, h.K_le hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem Q_le_normalizer_footeX : Q ≤ Subgroup.normalizer (footeX N K : Set G) := by
  have key : ∀ q ∈ Q, ∀ x ∈ footeX N K, q * x * q⁻¹ ∈ footeX N K := by
    intro q hq x hx
    obtain ⟨hxN, hxL⟩ := (mem_footeX).mp hx
    have hqN : q ∈ N := h.le hq
    have hnorm : (QuotientGroup.mk ⟨q, hqN⟩ : NHat N) ∈
        Subgroup.normalizer (hatIn N K : Set (NHat N)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
      constructor
      · rintro ⟨k, hk, hkn⟩
        refine ⟨⟨q, hqN⟩ * k * ⟨q, hqN⟩⁻¹, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr
            ((Subgroup.mem_normalizer_iff.mp (h.normalizes hq) k).mp hk)
        · rw [← hkn]; simp
      · rintro ⟨k, hk, hkn⟩
        refine ⟨⟨q, hqN⟩⁻¹ * k * ⟨q, hqN⟩⁻¹⁻¹, ?_, ?_⟩
        · refine Subgroup.mem_subgroupOf.mpr ?_
          have := (Subgroup.mem_normalizer_iff.mp (h.normalizes (inv_mem hq)) k).mp hk
          simpa using this
        · simp only [map_mul, map_inv, QuotientGroup.mk'_apply] at hkn ⊢
          rw [hkn]
          group
    have hconj := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_layerClosure hnorm) _).mp hxL
    have hmem : q * x * q⁻¹ ∈ N := N.mul_mem (N.mul_mem hqN hxN) (N.inv_mem hqN)
    have heq : (⟨q * x * q⁻¹, hmem⟩ : ↥N) = ⟨q, hqN⟩ * ⟨x, hxN⟩ * ⟨q, hqN⟩⁻¹ := rfl
    refine (mem_footeX).mpr ⟨hmem, ?_⟩
    rw [heq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hconj
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key q hq x, fun hx => ?_⟩
  have := key q⁻¹ (inv_mem hq) _ hx
  simpa [mul_assoc] using this

theorem isSubnormal_footeX : IsSubnormal (footeX N K) N := by
  have h1 : IsSubnormal (layerClosure (hatIn N K)) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (isSubnormal_layerClosure h.hatK_le_pLayer)
  have h2 := CFSG.Open.IsSubnormal.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) h1
  have h3 := CFSG.Open.IsSubnormal.map N.subtype h2
  rwa [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype] at h3

theorem le_core_of_isPGroup {R : Subgroup G} (hR : IsPGroup 2 R) (hRX : R ≤ footeX N K)
    (hXR : footeX N K ≤ Subgroup.normalizer (R : Set G)) : R ≤ pCoreOf 2 N := by
  have hn : (R.subgroupOf (footeX N K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr hXR
  have hsub : IsSubnormal R N := .step hRX hn h.isSubnormal_footeX
  exact CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub hR

theorem commutator_hatK : ⁅hatIn N K, hatIn N K⁆ = hatIn N K := by
  haveI := isPerfect_of_block h.block
  exact commutator_eq_of_isPerfect (Group.IsPerfect.ofSurjective (hatMap_surjective h.K_le))

theorem kClosure_le_footeX : kClosure N K ≤ footeX N K := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, k, hk, rfl⟩
  exact (footeX N K).mul_mem ((footeX N K).mul_mem hx (h.K_le_footeX hk))
    ((footeX N K).inv_mem hx)

theorem K_le_kClosure : K ≤ kClosure N K := fun k hk =>
  Subgroup.subset_closure ⟨1, (footeX N K).one_mem, k, hk, by group⟩

theorem footeX_le_normalizer_kClosure :
    footeX N K ≤ Subgroup.normalizer (kClosure N K : Set G) := by
  have key : ∀ y ∈ footeX N K, ∀ g ∈ kClosure N K, y * g * y⁻¹ ∈ kClosure N K := by
    intro y hy g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, hx, k, hk, rfl⟩ := hg
      exact Subgroup.subset_closure ⟨y * x, (footeX N K).mul_mem hy hx, k, hk, by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key y hy g, fun hg => ?_⟩
  have := key y⁻¹ ((footeX N K).inv_mem hy) _ hg
  simpa [mul_assoc] using this

theorem footeX_eq_sup : footeX N K = kClosure N K ⊔ pCoreOf 2 N := by
  refine le_antisymm ?_ (sup_le h.kClosure_le_footeX (core_le_footeX N K))
  intro x hx
  obtain ⟨hxN, hxL⟩ := (mem_footeX).mp hx
  rw [← closure_conj_layerClosure h.hatK_le_pLayer h.commutator_hatK] at hxL
  have hle : Subgroup.closure {y | ∃ b ∈ layerClosure (hatIn N K), ∃ a ∈ hatIn N K,
      y = b * a * b⁻¹} ≤ ((kClosure N K ⊔ pCoreOf 2 N).subgroupOf N).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, hb, _, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective b
    have hx' : (x' : G) ∈ footeX N K := (mem_footeX).mpr ⟨x'.2, hb⟩
    refine ⟨x' * k * x'⁻¹, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ?_), ?_⟩
    · exact Subgroup.subset_closure ⟨x', hx', k, Subgroup.mem_subgroupOf.mp hk, by simp⟩
    · simp
  obtain ⟨y, hy, hyx⟩ := hle hxL
  have hy' : (y : G) ∈ kClosure N K ⊔ pCoreOf 2 N := Subgroup.mem_subgroupOf.mp hy
  have hyx' : (y : G)⁻¹ * x ∈ pCoreOf 2 N := (mk_eq_mk_iff y ⟨x, hxN⟩).mp hyx
  have : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem _ hy' (Subgroup.mem_sup_right hyx')

theorem gam_le : footeX N K ⊔ Q ≤ N := sup_le (footeX_le N K) h.le

theorem blockU_le_wOne : blockU K ≤ wOne N K Q := fun u hu =>
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, u, hu, by group⟩

theorem wOne_le_core : wOne N K Q ≤ pCoreOf 2 N := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨γ, hγ, u, hu, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_core (h.gam_le hγ)) u).mp
    (h.blockU_le hu)

theorem gam_le_normalizer_wOne : footeX N K ⊔ Q ≤ Subgroup.normalizer (wOne N K Q : Set G) := by
  have key : ∀ y ∈ footeX N K ⊔ Q, ∀ g ∈ wOne N K Q, y * g * y⁻¹ ∈ wOne N K Q := by
    intro y hy g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨γ, hγ, u, hu, rfl⟩ := hg
      exact Subgroup.subset_closure ⟨y * γ, Subgroup.mul_mem _ hy hγ, u, hu, by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key y hy g, fun hg => ?_⟩
  have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hg
  simpa [mul_assoc] using this

theorem wOne_le_of {W : Subgroup G} (hW : blockU K ≤ W)
    (hn : footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G)) : wOne N K Q ≤ W := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨γ, hγ, u, hu, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hn hγ) u).mp (hW hu)

theorem K_le_gam : K ≤ footeX N K ⊔ Q := h.K_le_footeX.trans le_sup_left

theorem exists_wZero : ∃ W₀ : Subgroup G, Maximal (fun W : Subgroup G => W ≤ wOne N K Q ∧
    footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G) ∧ ¬ blockU K ≤ W) W₀ := by
  refine Set.Finite.exists_maximal (Set.toFinite _) ⟨⊥, bot_le, fun _ _ => ?_, fun hle => ?_⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    trivial
  · obtain ⟨u, hu, hz⟩ := SetLike.exists_of_lt h.block.chief.1
    have h1 : u = 1 := (Subgroup.mem_bot).mp (hle hu)
    exact hz (h1 ▸ Subgroup.one_mem _)

end ChiefHyp

section CommWOne

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q)
include h

theorem ChiefHyp.kClosure_comm_mem_wOne {d : G} (hd : d ∈ kClosure N K) {x : G}
    (hx : x ∈ pCoreOf 2 N) : d * x * d⁻¹ * x⁻¹ ∈ wOne N K Q := by
  have hΓ := h.gam_le_normalizer_wOne
  have hHΓ : footeX N K ⊔ Q ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    h.gam_le.trans h.le_normalizer_core
  suffices hP : ∀ d ∈ kClosure N K, d ∈ footeX N K ⊔ Q ∧
      ∀ x ∈ pCoreOf 2 N, d * x * d⁻¹ * x⁻¹ ∈ wOne N K Q from (hP d hd).2 x hx
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem d hd =>
    obtain ⟨y, hy, k, hk, rfl⟩ := hd
    have hyΓ : y ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left hy
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hyΓ (h.K_le_gam hk)) (Subgroup.inv_mem _ hyΓ),
      fun x hx => ?_⟩
    have hx' : y⁻¹ * x * y⁻¹⁻¹ ∈ pCoreOf 2 N :=
      (Subgroup.mem_normalizer_iff.mp (hHΓ (Subgroup.inv_mem _ hyΓ)) x).mp hx
    have hc : ⁅k, y⁻¹ * x * y⁻¹⁻¹⁆ ∈ wOne N K Q :=
      h.blockU_le_wOne (h.commutator_core_le (Subgroup.commutator_mem_commutator hk hx'))
    have e : y * k * y⁻¹ * x * (y * k * y⁻¹)⁻¹ * x⁻¹ = y * ⁅k, y⁻¹ * x * y⁻¹⁻¹⁆ * y⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hΓ hyΓ) _).mp hc
  | one => exact ⟨Subgroup.one_mem _, fun x _ => by simp [Subgroup.one_mem]⟩
  | mul a b _ _ ha hb =>
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun x hx => ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hΓ ha.1) _).mp (hb.2 x hx))
      (ha.2 x hx)
  | inv a _ ha =>
    refine ⟨Subgroup.inv_mem _ ha.1, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ pCoreOf 2 N :=
      (Subgroup.mem_normalizer_iff.mp (hHΓ (Subgroup.inv_mem _ ha.1)) x).mp hx
    have h1 := ha.2 _ hx'
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ *
        (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact (wOne N K Q).inv_mem h1

end CommWOne

section ChiefFactor

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q) {W₀ : Subgroup G}
  (hW₀ : Maximal (fun W : Subgroup G => W ≤ wOne N K Q ∧
    footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G) ∧ ¬ blockU K ≤ W) W₀)
include h hW₀

theorem ChiefHyp.isChiefFactor : IsChiefFactor (footeX N K ⊔ Q) W₀ (wOne N K Q) where
  lt := lt_of_le_of_ne hW₀.1.1 fun he => hW₀.1.2.2 (he ▸ h.blockU_le_wOne)
  norm₀ := hW₀.1.2.1
  norm₁ := h.gam_le_normalizer_wOne
  chief W h₀ h₁ hn := by
    by_cases hU : blockU K ≤ W
    · exact Or.inr (le_antisymm h₁ (h.wOne_le_of hU hn))
    · exact Or.inl (le_antisymm (hW₀.2 ⟨h₁, hn, hU⟩ h₀) h₀)

theorem ChiefHyp.K_le_normalizer_wZero : K ≤ Subgroup.normalizer (W₀ : Set G) :=
  h.K_le_gam.trans hW₀.1.2.1

omit hW₀ in
theorem ChiefHyp.blockU_le_of_commutator {W : Subgroup G} (hW : ⁅blockU K, K⁆ ≤ W) :
    blockU K ≤ W :=
  (IsFooteBlock.commutator_blockU h.block).symm ▸ hW

private def cW (K W₀ : Subgroup G) (hKW : K ≤ Subgroup.normalizer (W₀ : Set G)) : Subgroup G where
  carrier := {u | u ∈ blockU K ∧ ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ W₀}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(blockU K).mul_mem ha hb, fun k hk => ?_⟩
    have e : a * b * k * (a * b)⁻¹ * k⁻¹ = a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by
      group
    rw [e]
    exact W₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKW (blockU_le_self K ha)) _).mp
      (hb' k hk)) (ha' k hk)
  one_mem' := ⟨(blockU K).one_mem, fun k _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(blockU K).inv_mem ha, fun k hk => ?_⟩
    have e : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKW (blockU_le_self K ((blockU K).inv_mem ha))) _).mp
      (W₀.inv_mem (ha' k hk))

theorem ChiefHyp.inf_wZero_le_blockZ : blockU K ⊓ W₀ ≤ blockZ K := by
  have hKW := h.K_le_normalizer_wZero hW₀
  set C := cW K W₀ hKW with hC
  have hZC : blockZ K ≤ C := fun z hz => ⟨blockZ_le_blockU K hz, fun k hk => by
    have hzk : z * k = k * z :=
      (Subgroup.mem_centralizer_iff.mp hz.2 k hk).symm
    rw [hzk]
    simp [mul_assoc]⟩
  have hCU : C ≤ blockU K := fun u hu => hu.1
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := by
    have key : ∀ k ∈ K, ∀ u ∈ C, k * u * k⁻¹ ∈ C := by
      intro k hk u hu
      refine ⟨(Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) u).mp hu.1,
        fun k' hk' => ?_⟩
      have e : k * u * k⁻¹ * k' * (k * u * k⁻¹)⁻¹ * k'⁻¹ =
          k * (u * (k⁻¹ * k' * k) * u⁻¹ * (k⁻¹ * k' * k)⁻¹) * k⁻¹ := by group
      rw [e]
      have hk'' : k⁻¹ * k' * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hk') hk
      exact (Subgroup.mem_normalizer_iff.mp (hKW hk) _).mp (hu.2 _ hk'')
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key k hk u, fun hu => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ hu
    simpa [mul_assoc] using this
  rcases h.block.chief.2 C hZC hCU hKC with hCZ | hCU'
  · intro a ha
    rw [← hCZ]
    refine ⟨ha.1, fun k hk => ?_⟩
    have e : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
    rw [e]
    exact W₀.mul_mem ha.2 ((Subgroup.mem_normalizer_iff.mp (hKW hk) _).mp (W₀.inv_mem ha.2))
  · exfalso
    apply hW₀.1.2.2
    refine h.blockU_le_of_commutator ((Subgroup.commutator_le).mpr fun u hu k hk => ?_)
    rw [← hCU'] at hu
    exact hu.2 k hk

theorem ChiefHyp.commutator_wZero_K : ⁅W₀, K⁆ = ⊥ := by
  have hKW := h.K_le_normalizer_wZero hW₀
  have hW₀H : W₀ ≤ pCoreOf 2 N := hW₀.1.1.trans h.wOne_le_core
  have h1 : ⁅W₀, K⁆ ≤ blockZ K := by
    refine (Subgroup.commutator_le).mpr fun w hw k hk => h.inf_wZero_le_blockZ hW₀ ⟨?_, ?_⟩
    · have : ⁅w, k⁆ ∈ ⁅pCoreOf 2 N, K⁆ := Subgroup.commutator_mem_commutator (hW₀H hw) hk
      rw [Subgroup.commutator_comm] at this
      exact h.commutator_core_le this
    · have e : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact W₀.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hKW hk) _).mp (W₀.inv_mem hw))
  have hcent : ⁅⁅W₀, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h1.trans inf_le_right
  have h3 : ⁅⁅K, K⁆, W₀⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (by rwa [Subgroup.commutator_comm K W₀])
      hcent
  rw [IsFooteBlock.commutator_eq h.block, Subgroup.commutator_comm] at h3
  exact h3

theorem ChiefHyp.kClosure_le_centralizer_wZero :
    kClosure N K ≤ Subgroup.centralizer (W₀ : Set G) := by
  have hc := h.commutator_wZero_K hW₀
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨x, hx, k, hk, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  have hxΓ : x ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left hx
  have hw' : x⁻¹ * w * x⁻¹⁻¹ ∈ W₀ :=
    (Subgroup.mem_normalizer_iff.mp (hW₀.1.2.1 (Subgroup.inv_mem _ hxΓ)) w).mp hw
  have hkw : k * (x⁻¹ * w * x) = (x⁻¹ * w * x) * k := by
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc (by simpa using hw') k hk
  calc w * (x * k * x⁻¹) = x * ((x⁻¹ * w * x) * k) * x⁻¹ := by group
    _ = x * (k * (x⁻¹ * w * x)) * x⁻¹ := by rw [hkw]
    _ = x * k * x⁻¹ * w := by group

end ChiefFactor

namespace ChiefLin

variable {Γ W₀ W₁ : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : ChiefLin Γ W₀ W₁ V)

@[expose] noncomputable def restr {A : Subgroup G} (hA : A ≤ Γ) : ↥A →* ↥(lin.img A) :=
  (lin.ρ.comp (Subgroup.inclusion hA)).codRestrict (lin.img A) fun a =>
    ⟨Subgroup.inclusion hA a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩

theorem restr_apply {A : Subgroup G} (hA : A ≤ Γ) (a : ↥A) :
    ((lin.restr hA a : ↥(lin.img A)) : GLV V) = lin.ρ (Subgroup.inclusion hA a) := rfl

theorem restr_surjective {A : Subgroup G} (hA : A ≤ Γ) : Function.Surjective (lin.restr hA) := by
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext rfl⟩

@[expose] noncomputable def uMap {B : Subgroup G} (hB : B ≤ W₁) (S : Submodule (ZMod 2) V)
    (hS : ∀ u : ↥B, lin.vec (Subgroup.inclusion hB u) ∈ S) : ↥B →* Multiplicative ↥S where
  toFun u := Multiplicative.ofAdd ⟨lin.vec (Subgroup.inclusion hB u), hS u⟩
  map_one' := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact lin.vec_one
  map_mul' u v := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact lin.vec_mul (Subgroup.inclusion hB u) (Subgroup.inclusion hB v)

end ChiefLin

section Lin

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q) {W₀ : Subgroup G}
  (hW₀ : Maximal (fun W : Subgroup G => W ≤ wOne N K Q ∧
    footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G) ∧ ¬ blockU K ≤ W) W₀)
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : ChiefLin (footeX N K ⊔ Q) W₀ (wOne N K Q) V)
include h hW₀

theorem ChiefHyp.ρ_eq_one_of_mem_core (x : ↥(footeX N K ⊔ Q)) (hx : (x : G) ∈ pCoreOf 2 N) :
    lin.ρ x = 1 :=
  lin.ρ_eq_one_of_normal (h.isChiefFactor hW₀) h.core_isPGroup
    (h.gam_le.trans h.le_normalizer_core) x hx

theorem ChiefHyp.eq_one_of_odd (x : ↥(footeX N K ⊔ Q)) (hxD : (x : G) ∈ kClosure N K)
    (hρ : lin.ρ x = 1) (hodd : Odd (orderOf (x : G))) : (x : G) = 1 := by
  set z : G := (x : G) with hz
  have hW₁H := h.wOne_le_core
  have hW₁2 : IsPGroup 2 ↥(wOne N K Q) := h.core_isPGroup.to_le hW₁H
  have hzW₀ : ∀ w ∈ W₀, z * w * z⁻¹ = w := by
    intro w hw
    have := Subgroup.mem_centralizer_iff.mp (h.kClosure_le_centralizer_wZero hW₀ hxD) w hw
    rw [← this]; group
  have hzW₁ : ∀ w ∈ wOne N K Q, z * w * z⁻¹ ∈ wOne N K Q := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (h.gam_le_normalizer_wOne x.2) w).mp hw
  have hc₁ : ∀ w ∈ wOne N K Q, ⁅z, w⁆ ∈ W₀ := fun w hw => by
    rw [commutatorElement_def]
    exact (lin.ρ_eq_one_iff x).mp hρ w hw
  have step1 := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series hodd hW₁2
    hW₀.1.1 hzW₁ hzW₀ hc₁
  have hzH : ∀ y ∈ pCoreOf 2 N, z * y * z⁻¹ ∈ pCoreOf 2 N := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_core (h.gam_le x.2)) y).mp hy
  have hc₂ : ∀ y ∈ pCoreOf 2 N, ⁅z, y⁆ ∈ wOne N K Q := fun y hy => by
    rw [commutatorElement_def]
    exact h.kClosure_comm_mem_wOne hxD hy
  have step2 := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.odd_trivial_of_series hodd
    h.core_isPGroup hW₁H hzH step1 hc₂
  have hzN : z ∈ N := h.gam_le x.2
  have hzC : z ∈ N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) := by
    refine ⟨hzN, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := step2 y hy
    calc y * z = z * y * z⁻¹ * z := by rw [this]
      _ = z * y := by group
  have hzQ := h.faithful hzC
  obtain ⟨k, hk⟩ := h.core_isPGroup ⟨z, hzQ⟩
  have hk' : z ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem ChiefHyp.ρ_eq_one_iff (x : ↥(footeX N K ⊔ Q)) (hx : (x : G) ∈ footeX N K) :
    lin.ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 N := by
  refine ⟨fun hρ => ?_, h.ρ_eq_one_of_mem_core hW₀ lin x⟩
  set R : Subgroup G := lin.ρ.ker.map (footeX N K ⊔ Q).subtype ⊓ footeX N K with hR
  set D := kClosure N K
  have memR : ∀ y : G, y ∈ R ↔ ∃ hy : y ∈ footeX N K ⊔ Q, lin.ρ ⟨y, hy⟩ = 1 ∧ y ∈ footeX N K := by
    intro y
    constructor
    · rintro ⟨⟨y', hy', rfl⟩, hyX⟩
      exact ⟨y'.2, hy', hyX⟩
    · rintro ⟨hy, hρy, hyX⟩
      exact ⟨⟨⟨y, hy⟩, hρy, rfl⟩, hyX⟩
  have hRD : IsPGroup 2 ↥(R ⊓ D) := by
    intro r
    have hr0 : orderOf (r : G) ≠ 0 := (orderOf_pos (r : G)).ne'
    obtain ⟨a, m, hm, hrm⟩ := Nat.exists_eq_two_pow_mul_odd hr0
    refine ⟨a, ?_⟩
    obtain ⟨hrΓ, hrρ, hrX⟩ := (memR r).mp r.2.1
    set z : G := (r : G) ^ 2 ^ a with hzdef
    have hzR : z ∈ R := R.pow_mem r.2.1 _
    obtain ⟨hzΓ, hzρ, -⟩ := (memR z).mp hzR
    have hzD : z ∈ D := D.pow_mem r.2.2 _
    have hzo : orderOf z = m := by
      rw [hzdef, orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hrm,
        Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    have hz1 := h.eq_one_of_odd hW₀ lin ⟨z, hzΓ⟩ hzD hzρ (show Odd (orderOf z) from hzo ▸ hm)
    apply Subtype.ext
    simpa [hzdef] using hz1
  have hXR : footeX N K ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ y ∈ footeX N K, ∀ g ∈ R, y * g * y⁻¹ ∈ R := by
      intro y hy g hg
      obtain ⟨hgΓ, hgρ, hgX⟩ := (memR g).mp hg
      have hyΓ : y ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left hy
      refine (memR _).mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hyΓ hgΓ)
        (Subgroup.inv_mem _ hyΓ), ?_, (footeX N K).mul_mem ((footeX N K).mul_mem hy hgX)
        ((footeX N K).inv_mem hy)⟩
      have e : (⟨y * g * y⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hyΓ hgΓ)
          (Subgroup.inv_mem _ hyΓ)⟩ : ↥(footeX N K ⊔ Q)) = ⟨y, hyΓ⟩ * ⟨g, hgΓ⟩ * ⟨y, hyΓ⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, hgρ, mul_one, map_inv, mul_inv_cancel]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key y hy g, fun hg => ?_⟩
    have := key y⁻¹ ((footeX N K).inv_mem hy) _ hg
    simpa [mul_assoc] using this
  have hXH : footeX N K ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    (footeX_le N K).trans h.le_normalizer_core
  have hXD := h.footeX_le_normalizer_kClosure
  have hXRD : footeX N K ≤ Subgroup.normalizer ((R ⊓ D : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp (hXR hy) g
    have h2 := Subgroup.mem_normalizer_iff.mp (hXD hy) g
    exact ⟨fun hg => ⟨h1.mp hg.1, h2.mp hg.2⟩, fun hg => ⟨h1.mpr hg.1, h2.mpr hg.2⟩⟩
  have hRDX : R ⊓ D ≤ footeX N K := inf_le_left.trans inf_le_right
  have hT2 : IsPGroup 2 ↥((R ⊓ D) ⊔ pCoreOf 2 N) :=
    IsPGroup.to_sup_of_normal_right' hRD h.core_isPGroup (hRDX.trans hXH)
  have hTX : (R ⊓ D) ⊔ pCoreOf 2 N ≤ footeX N K := sup_le hRDX (core_le_footeX N K)
  have hXT : footeX N K ≤ Subgroup.normalizer (((R ⊓ D) ⊔ pCoreOf 2 N : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf ⟨hXRD hy, hXH hy⟩ g
      hg, fun hg => ?_⟩
    have := Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
      ⟨Subgroup.inv_mem _ (hXRD hy), Subgroup.inv_mem _ (hXH hy)⟩ _ hg
    simpa [mul_assoc] using this
  have hRDH : R ⊓ D ≤ pCoreOf 2 N := le_sup_left.trans (h.le_core_of_isPGroup hT2 hTX hXT)
  have hxDH : (x : G) ∈ ((D ⊔ pCoreOf 2 N : Subgroup G) : Set G) := by
    rw [← h.footeX_eq_sup]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D (pCoreOf 2 N)
    (h.kClosure_le_footeX.trans hXH)] at hxDH
  obtain ⟨d, hd, k₀, hk₀, hdk⟩ := hxDH
  have hk₀Γ : k₀ ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left (core_le_footeX N K hk₀)
  have hdR : d ∈ R := by
    have hd' : d = (x : G) * k₀⁻¹ := by rw [← hdk]; group
    have hρk₀ : lin.ρ ⟨k₀, hk₀Γ⟩ = 1 := h.ρ_eq_one_of_mem_core hW₀ lin _ hk₀
    rw [hd']
    refine (memR _).mpr ⟨Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ hk₀Γ), ?_,
      (footeX N K).mul_mem hx ((footeX N K).inv_mem (core_le_footeX N K hk₀))⟩
    have e : (⟨(x : G) * k₀⁻¹, Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ hk₀Γ)⟩ :
        ↥(footeX N K ⊔ Q)) = x * (⟨k₀, hk₀Γ⟩ : ↥(footeX N K ⊔ Q))⁻¹ := rfl
    rw [e, map_mul, hρ, map_inv, hρk₀, inv_one, one_mul]
  rw [← hdk]
  exact (pCoreOf 2 N).mul_mem (hRDH ⟨hdR, hd⟩) hk₀

theorem ChiefHyp.vec_mem_commSpace (u : ↥(blockU K)) :
    lin.vec (Subgroup.inclusion h.blockU_le_wOne u) ∈ commSpace (lin.img K) ⊤ := by
  have hKΓ := h.K_le_gam
  have hle : blockU K ≤ lin.preW (commSpace (lin.img K) ⊤) := by
    refine h.blockU_le_of_commutator ((Subgroup.commutator_le).mpr fun a ha k hk => ?_)
    have haW : a ∈ wOne N K Q := h.blockU_le_wOne ha
    have hkW : k * a⁻¹ * k⁻¹ ∈ wOne N K Q :=
      (Subgroup.mem_normalizer_iff.mp (h.gam_le_normalizer_wOne (hKΓ hk)) _).mp
        ((wOne N K Q).inv_mem haW)
    have hcW : ⁅a, k⁆ ∈ wOne N K Q := by
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
      exact (wOne N K Q).mul_mem haW hkW
    refine (lin.mem_preW).mpr ⟨hcW, ?_⟩
    have e : (⟨⁅a, k⁆, hcW⟩ : ↥(wOne N K Q)) = ⟨a, haW⟩ * ⟨k * a⁻¹ * k⁻¹, hkW⟩ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    rw [e, lin.vec_mul]
    have hρ := lin.ρ_vec ⟨k, hKΓ hk⟩ ⟨a⁻¹, (wOne N K Q).inv_mem haW⟩ ⟨k * a⁻¹ * k⁻¹, hkW⟩ rfl
    rw [← hρ]
    have hinv : lin.vec (⟨a⁻¹, (wOne N K Q).inv_mem haW⟩ : ↥(wOne N K Q)) =
        - lin.vec ⟨a, haW⟩ := by
      rw [← lin.vec_inv]; rfl
    rw [hinv, map_neg]
    have hgen : lin.ρ ⟨k, hKΓ hk⟩ (lin.vec ⟨a, haW⟩) - lin.vec ⟨a, haW⟩ ∈
        commSpace (lin.img K) ⊤ :=
      Submodule.subset_span ⟨lin.ρ ⟨k, hKΓ hk⟩, ⟨⟨k, hKΓ hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩,
        lin.vec ⟨a, haW⟩, Submodule.mem_top, rfl⟩
    have : lin.vec ⟨a, haW⟩ + -(lin.ρ ⟨k, hKΓ hk⟩) (lin.vec ⟨a, haW⟩) =
        -(lin.ρ ⟨k, hKΓ hk⟩ (lin.vec ⟨a, haW⟩) - lin.vec ⟨a, haW⟩) := by abel
    rw [this]
    exact Submodule.neg_mem _ hgen
  obtain ⟨_, hv⟩ := (lin.mem_preW).mp (hle u.2)
  exact hv

theorem ChiefHyp.exists_vec_eq {w : V} (hw : w ∈ commSpace (lin.img K) ⊤) :
    ∃ u : ↥(blockU K), lin.vec (Subgroup.inclusion h.blockU_le_wOne u) = w := by
  have hKΓ := h.K_le_gam
  let T : AddSubgroup V :=
    { carrier := {v | ∃ u : ↥(blockU K), lin.vec (Subgroup.inclusion h.blockU_le_wOne u) = v}
      zero_mem' := ⟨1, lin.vec_one⟩
      add_mem' := by
        rintro _ _ ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
        exact ⟨u₁ * u₂, by rw [map_mul, lin.vec_mul]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, lin.vec_inv]⟩ }
  have hle : commSpace (lin.img K) ⊤ ≤ AddSubgroup.toZModSubmodule 2 T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨k, hk, rfl⟩, v, -, rfl⟩
    obtain ⟨w', rfl⟩ := lin.vec_surjective v
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hw'H : (w' : G) ∈ pCoreOf 2 N := h.wOne_le_core w'.2
    have hcU : ⁅(k : G), (w' : G)⁆ ∈ blockU K :=
      h.commutator_core_le (Subgroup.commutator_mem_commutator hk' hw'H)
    refine ⟨⟨_, hcU⟩, ?_⟩
    have hconj : (k : G) * w' * (k : G)⁻¹ ∈ wOne N K Q :=
      (Subgroup.mem_normalizer_iff.mp (h.gam_le_normalizer_wOne k.2) _).mp w'.2
    have e : Subgroup.inclusion h.blockU_le_wOne ⟨_, hcU⟩ =
        ⟨(k : G) * w' * (k : G)⁻¹, hconj⟩ * w'⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    rw [e, lin.vec_mul, lin.vec_inv, ← lin.ρ_vec k w' _ rfl]
    abel
  obtain ⟨u, hu⟩ := hle hw
  exact ⟨u, hu⟩

theorem ChiefHyp.vec_mem_fixedSpace_iff (u : ↥(blockU K)) :
    lin.vec (Subgroup.inclusion h.blockU_le_wOne u) ∈ fixedSpace (lin.img K) ↔
      (u : G) ∈ blockZ K := by
  have hKΓ := h.K_le_gam
  have hZ : ∀ z : ↥(blockU K), (z : G) ∈ blockZ K →
      lin.vec (Subgroup.inclusion h.blockU_le_wOne z) ∈ fixedSpace (lin.img K) := by
    intro z hz
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hcomm : (k : G) * z * (k : G)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hz.2 k hk'
      rw [this]; group
    rw [lin.ρ_vec k (Subgroup.inclusion h.blockU_le_wOne z)
      (Subgroup.inclusion h.blockU_le_wOne z) hcomm.symm]
  refine ⟨fun hu => ?_, hZ u⟩
  set F := lin.preW (fixedSpace (lin.img K)) ⊓ blockU K with hF
  have hInv : Invariant (lin.img K) (fixedSpace (lin.img K)) := by
    intro g hg v hv g' hg'
    rw [hv g hg]
    exact hv g' hg'
  have hFn : K ≤ Subgroup.normalizer (F : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (lin.le_normalizer_preW hKΓ hInv hk) x
    have h2 := Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hZF : blockZ K ≤ F := fun z hz =>
    ⟨(lin.mem_preW).mpr ⟨h.blockU_le_wOne (blockZ_le_blockU K hz),
      hZ ⟨z, blockZ_le_blockU K hz⟩ hz⟩, blockZ_le_blockU K hz⟩
  rcases h.block.chief.2 F hZF inf_le_right hFn with hFZ | hFU
  · rw [← hFZ]
    exact ⟨(lin.mem_preW).mpr ⟨_, hu⟩, u.2⟩
  · exfalso
    apply hW₀.1.2.2
    refine h.blockU_le_of_commutator ((Subgroup.commutator_le).mpr fun a ha k hk => ?_)
    have haF : a ∈ F := hFU ▸ ha
    obtain ⟨haW, hfix⟩ := (lin.mem_preW).mp haF.1
    have hkW : k * a⁻¹ * k⁻¹ ∈ wOne N K Q :=
      (Subgroup.mem_normalizer_iff.mp (h.gam_le_normalizer_wOne (hKΓ hk)) _).mp
        ((wOne N K Q).inv_mem haW)
    have hcW : ⁅a, k⁆ ∈ wOne N K Q := by
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
      exact (wOne N K Q).mul_mem haW hkW
    have hvec : lin.vec ⟨⁅a, k⁆, hcW⟩ = 0 := by
      have e : (⟨⁅a, k⁆, hcW⟩ : ↥(wOne N K Q)) = ⟨a, haW⟩ * ⟨k * a⁻¹ * k⁻¹, hkW⟩ := by
        apply Subtype.ext
        simp [commutatorElement_def, mul_assoc]
      rw [e, lin.vec_mul, ← lin.ρ_vec ⟨k, hKΓ hk⟩ ⟨a⁻¹, (wOne N K Q).inv_mem haW⟩
        ⟨k * a⁻¹ * k⁻¹, hkW⟩ rfl]
      have hinv : lin.vec (⟨a⁻¹, (wOne N K Q).inv_mem haW⟩ : ↥(wOne N K Q)) =
          - lin.vec ⟨a, haW⟩ := by
        rw [← lin.vec_inv]; rfl
      rw [hinv, map_neg, hfix _ ⟨⟨k, hKΓ hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩]
      abel
    exact (lin.vec_eq_zero_iff _).mp hvec

end Lin

section Setup

variable {N K Q : Subgroup G} (h : ChiefHyp N K Q) {W₀ : Subgroup G}
  (hW₀ : Maximal (fun W : Subgroup G => W ≤ wOne N K Q ∧
    footeX N K ⊔ Q ≤ Subgroup.normalizer (W : Set G) ∧ ¬ blockU K ≤ W) W₀)
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (lin : ChiefLin (footeX N K ⊔ Q) W₀ (wOne N K Q) V)
include h hW₀

private noncomputable def psiK : ↥(blockU K) →* Multiplicative ↥(commSpace (lin.img K) ⊤) :=
  lin.uMap h.blockU_le_wOne (commSpace (lin.img K) ⊤) (h.vec_mem_commSpace hW₀ lin)

private theorem psiK_apply (u : ↥(blockU K)) :
    ((Multiplicative.toAdd (psiK h hW₀ lin u) : ↥(commSpace (lin.img K) ⊤)) : V) =
      lin.vec (Subgroup.inclusion h.blockU_le_wOne u) := rfl

private theorem psiK_surjective : Function.Surjective (psiK h hW₀ lin) := by
  intro w
  obtain ⟨u, hu⟩ := h.exists_vec_eq hW₀ lin (Multiplicative.toAdd w).2
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [psiK_apply, hu]

private theorem psiK_fixed (u : ↥(blockU K)) :
    ((Multiplicative.toAdd (psiK h hW₀ lin u) : ↥(commSpace (lin.img K) ⊤)) : V) ∈
      fixedSpace (lin.img K) ↔ (u : G) ∈ blockZ K := by
  rw [psiK_apply]
  exact h.vec_mem_fixedSpace_iff hW₀ lin u

private theorem psiK_equiv (k : ↥K) (u v : ↥(blockU K)) (huv : (v : G) = k * u * (k : G)⁻¹) :
    ((Multiplicative.toAdd (psiK h hW₀ lin v) : ↥(commSpace (lin.img K) ⊤)) : V) =
      (lin.restr h.K_le_gam k : GLV V)
        ((Multiplicative.toAdd (psiK h hW₀ lin u) : ↥(commSpace (lin.img K) ⊤)) : V) := by
  rw [psiK_apply, psiK_apply, lin.restr_apply]
  exact (lin.ρ_vec _ _ _ huv).symm

theorem ChiefHyp.ker_restr_le : (lin.restr h.K_le_gam).ker ≤ CFSG.pCore 2 ↥K := by
  refine le_pCore_of_normal _ ?_
  have hmem : ∀ k : ↥(lin.restr h.K_le_gam).ker, ((k : ↥K) : G) ∈ pCoreOf 2 N := by
    intro k
    have hk : lin.ρ (Subgroup.inclusion h.K_le_gam (k : ↥K)) = 1 := by
      have := k.2
      rw [MonoidHom.mem_ker, ← Subtype.coe_inj, lin.restr_apply] at this
      exact this
    exact (h.ρ_eq_one_iff hW₀ lin _ (h.K_le_footeX (k : ↥K).2)).mp hk
  refine IsPGroup.of_injective h.core_isPGroup
    { toFun := fun k => ⟨((k : ↥K) : G), hmem k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } ?_
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  have h1 := congrArg (fun x : ↥(pCoreOf 2 N) => (x : G)) hab
  simpa using h1

private theorem restr_blockU (k : ↥K) (hk : (k : G) ∈ blockU K) : lin.restr h.K_le_gam k = 1 := by
  apply Subtype.ext
  rw [lin.restr_apply]
  exact h.ρ_eq_one_of_mem_core hW₀ lin _ (h.blockU_le hk)

private theorem isQuasisimple_img : CFSG.Open.IsQuasisimple ↥(lin.img K) :=
  isQuasisimple_open_of_native (isQuasisimple_of_block h.block (lin.restr h.K_le_gam)
    (lin.restr_surjective h.K_le_gam) (h.ker_restr_le hW₀ lin) (restr_blockU h hW₀ lin))

private theorem img_le_img {A : Subgroup G} : lin.img A ≤ lin.img (footeX N K ⊔ Q) := by
  refine Subgroup.map_mono ?_
  rw [Subgroup.subgroupOf_self]
  exact le_top

private theorem img_K_le_centralizer :
    lin.img K ≤ Subgroup.centralizer (lin.img Q : Set (GLV V)) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hq' : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have hc : ((⁅k, q⁆ : ↥(footeX N K ⊔ Q)) : G) ∈ pCoreOf 2 N :=
    h.blockU_le (h.commutator_Q_le (Subgroup.commutator_mem_commutator hk' hq'))
  have h1 := h.ρ_eq_one_of_mem_core hW₀ lin _ hc
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have : lin.ρ k * lin.ρ q = lin.ρ q * lin.ρ k := by
    have := congrArg (· * (lin.ρ q * lin.ρ k)) h1
    simpa [mul_assoc] using this
  exact this.symm

private theorem isComponentOf_img :
    IsComponentOf (lin.img K)
      (lin.img (footeX N K ⊔ Q) ⊓ Subgroup.centralizer (lin.img Q : Set (GLV V))) := by
  refine ⟨le_inf (img_le_img h hW₀ lin) (img_K_le_centralizer h hW₀ lin), ?_,
    isQuasisimple_img h hW₀ lin⟩
  let Cst : Subgroup G := footeX N K ⊓
    ((Subgroup.centralizer (hatIn N Q : Set (NHat N))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥N))).map N.subtype
  have memCst : ∀ x : G, x ∈ Cst ↔ x ∈ footeX N K ∧ ∃ hx : x ∈ N,
      (QuotientGroup.mk ⟨x, hx⟩ : NHat N) ∈ Subgroup.centralizer (hatIn N Q : Set (NHat N)) := by
    intro x
    constructor
    · rintro ⟨hxX, ⟨y, hy, rfl⟩⟩
      exact ⟨hxX, y.2, hy⟩
    · rintro ⟨hxX, hxN, hc⟩
      exact ⟨hxX, ⟨x, hxN⟩, hc, rfl⟩
  have hKCst : K ≤ Cst := fun k hk => (memCst k).mpr ⟨h.K_le_footeX hk, h.K_le hk,
    h.hatK_le_centralizer ⟨⟨k, h.K_le hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩⟩
  have hCstN : Cst ≤ N ⊓ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨-, hxN, hc⟩ := (memCst x).mp hx
    exact ⟨hxN, h.mem_normalizer_of_mk_mem_centralizer hc⟩
  have hsub1 : IsSubnormal K Cst := by
    have := CFSG.Open.IsSubnormal.inf_of_le h.subnormal hCstN
    rwa [inf_eq_left.mpr hKCst] at this
  have hsub2 : IsSubnormal (lin.img K) (lin.img Cst) :=
    CFSG.Open.IsSubnormal.map lin.ρ
      (CFSG.Open.IsSubnormal.comap (footeX N K ⊔ Q).subtype hsub1)
  have hΓX : footeX N K ⊔ Q ≤ Subgroup.normalizer (footeX N K : Set G) :=
    sup_le Subgroup.le_normalizer h.Q_le_normalizer_footeX
  have hCst_eq : lin.img Cst =
      lin.img (footeX N K) ⊓ Subgroup.centralizer (lin.img Q : Set (GLV V)) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hc' := (memCst (c : G)).mp (Subgroup.mem_subgroupOf.mp hc)
      refine ⟨⟨c, Subgroup.mem_subgroupOf.mpr hc'.1, rfl⟩, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      obtain ⟨hcN, hcC⟩ := hc'.2
      have hqN : (q : G) ∈ N := h.le hq'
      have hcomm := Subgroup.mem_centralizer_iff.mp hcC (QuotientGroup.mk ⟨q, hqN⟩)
        ⟨⟨q, hqN⟩, hq', rfl⟩
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff] at hcomm
      have hmem : (((q * c)⁻¹ * (c * q) : ↥(footeX N K ⊔ Q)) : G) ∈ pCoreOf 2 N := by
        simpa using hcomm
      have h1 := h.ρ_eq_one_of_mem_core hW₀ lin _ hmem
      rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h1
      exact h1
    · rintro _ ⟨⟨γ, hγ, rfl⟩, hγC⟩
      have hγX : (γ : G) ∈ footeX N K := Subgroup.mem_subgroupOf.mp hγ
      have hγN : (γ : G) ∈ N := footeX_le N K hγX
      refine ⟨γ, Subgroup.mem_subgroupOf.mpr ((memCst _).mpr ⟨hγX, hγN, ?_⟩), rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      have hqΓ : (q : G) ∈ footeX N K ⊔ Q := Subgroup.mem_sup_right hq'
      have hqN : (q : G) ∈ N := h.le hq'
      have hρc := Subgroup.mem_centralizer_iff.mp hγC (lin.ρ ⟨q, hqΓ⟩)
        ⟨⟨q, hqΓ⟩, Subgroup.mem_subgroupOf.mpr hq', rfl⟩
      have hcX : (q : G)⁻¹ * (γ : G)⁻¹ * q * γ ∈ footeX N K := by
        have hqγ : (q : G)⁻¹ * (γ : G)⁻¹ * q ∈ footeX N K := by
          have := (Subgroup.mem_normalizer_iff.mp (hΓX (Subgroup.inv_mem _ hqΓ)) _).mp
            ((footeX N K).inv_mem hγX)
          simpa [mul_assoc] using this
        exact (footeX N K).mul_mem hqγ hγX
      have hcρ : lin.ρ ((⟨q, hqΓ⟩ : ↥(footeX N K ⊔ Q))⁻¹ * γ⁻¹ * ⟨q, hqΓ⟩ * γ) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc (_ * _), hρc]
        group
      have hcH := (h.ρ_eq_one_iff hW₀ lin _ hcX).mp hcρ
      show (QuotientGroup.mk ⟨q, hqN⟩ : NHat N) * QuotientGroup.mk ⟨γ, hγN⟩ =
        QuotientGroup.mk ⟨γ, hγN⟩ * QuotientGroup.mk ⟨q, hqN⟩
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff]
      have e : ((⟨q, hqN⟩ * ⟨γ, hγN⟩ : ↥N) : G)⁻¹ * ((⟨γ, hγN⟩ * ⟨q, hqN⟩ : ↥N) : G) =
          ((q : G)⁻¹ * (γ : G)⁻¹ * q * γ)⁻¹ := by
        simp only [Subgroup.coe_mul]; group
      rw [e]
      exact (pCoreOf 2 N).inv_mem hcH
  have hnorm : ((lin.img (footeX N K) ⊓ Subgroup.centralizer (lin.img Q : Set (GLV V))).subgroupOf
      (lin.img (footeX N K ⊔ Q) ⊓ Subgroup.centralizer (lin.img Q : Set (GLV V)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right _ (img_le_img h hW₀ lin))]
    rintro d k ⟨⟨x, hx, rfl⟩, hd⟩ ⟨⟨γ, -, rfl⟩, hk⟩
    refine ⟨⟨γ * x * γ⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hΓX γ.2) _).mp (Subgroup.mem_subgroupOf.mp hx)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hd) (Subgroup.inv_mem _ hk)
  rw [hCst_eq] at hsub2
  exact CFSG.Open.IsSubnormal.trans hsub2
    (.step (inf_le_inf_right _ (img_le_img h hW₀ lin)) hnorm (.refl _))

private theorem gen_img :
    lin.img (footeX N K ⊔ Q) =
      normalClosure (lin.img (footeX N K ⊔ Q)) (lin.img K) ⊔ lin.img Q := by
  have hDΓ : kClosure N K ≤ footeX N K ⊔ Q := h.kClosure_le_footeX.trans le_sup_left
  have hQΓ : Q ≤ footeX N K ⊔ Q := le_sup_right
  have hΓeq : footeX N K ⊔ Q = kClosure N K ⊔ Q := by
    rw [h.footeX_eq_sup, sup_assoc, sup_eq_right.mpr h.core_le]
  apply le_antisymm
  · have himg : lin.img (footeX N K ⊔ Q) = lin.img (kClosure N K) ⊔ lin.img Q := by
      change ((footeX N K ⊔ Q).subgroupOf (footeX N K ⊔ Q)).map lin.ρ =
        ((kClosure N K).subgroupOf (footeX N K ⊔ Q)).map lin.ρ ⊔
          (Q.subgroupOf (footeX N K ⊔ Q)).map lin.ρ
      conv_lhs => rw [show (footeX N K ⊔ Q).subgroupOf (footeX N K ⊔ Q) =
        (kClosure N K ⊔ Q).subgroupOf (footeX N K ⊔ Q) by rw [← hΓeq]]
      rw [Subgroup.subgroupOf_sup hDΓ hQΓ, Subgroup.map_sup]
    refine himg.le.trans (sup_le_sup_right ?_ _)
    rintro _ ⟨d, hd, rfl⟩
    have hd' : (d : G) ∈ kClosure N K := Subgroup.mem_subgroupOf.mp hd
    suffices hP : kClosure N K ≤ ((normalClosure (lin.img (footeX N K ⊔ Q))
        (lin.img K)).comap lin.ρ).map (footeX N K ⊔ Q).subtype by
      obtain ⟨y, hy, hyd⟩ := hP hd'
      rw [← Subtype.ext hyd]
      exact hy
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, k, hk, rfl⟩
    have hxΓ : x ∈ footeX N K ⊔ Q := Subgroup.mem_sup_left hx
    have hkΓ : k ∈ footeX N K ⊔ Q := h.K_le_gam hk
    refine ⟨⟨x, hxΓ⟩ * ⟨k, hkΓ⟩ * ⟨x, hxΓ⟩⁻¹, ?_, rfl⟩
    show lin.ρ (⟨x, hxΓ⟩ * ⟨k, hkΓ⟩ * ⟨x, hxΓ⟩⁻¹) ∈ normalClosure _ _
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.subset_closure ⟨lin.ρ ⟨x, hxΓ⟩, ⟨⟨x, hxΓ⟩, by
      rw [Subgroup.subgroupOf_self]; exact Subgroup.mem_top _, rfl⟩,
      lin.ρ ⟨k, hkΓ⟩, ⟨⟨k, hkΓ⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
  · refine sup_le ?_ (img_le_img h hW₀ lin)
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ (img_le_img h hW₀ lin hl))
      (Subgroup.inv_mem _ hγ)

theorem ChiefHyp.setup6Irr_img : Setup6Irr (lin.img (footeX N K ⊔ Q)) (lin.img Q) (lin.img K) where
  S_le := img_le_img h hW₀ lin
  isPGroup := (h.two.comap_of_injective (footeX N K ⊔ Q).subtype Subtype.val_injective).map lin.ρ
  component := isComponentOf_img h hW₀ lin
  irrTilde := hasIrrTildeV_of_uMap h.block (lin.restr h.K_le_gam)
    (lin.restr_surjective h.K_le_gam) (psiK h hW₀ lin) (psiK_surjective h hW₀ lin)
    (psiK_fixed h hW₀ lin) (psiK_equiv h hW₀ lin)
  irr := lin.isIrr_img (h.isChiefFactor hW₀)
  gen := gen_img h hW₀ lin

theorem ChiefHyp.isFPrimeModule_img (hKF : IsFPrimeType K) : IsFPrimeModule (lin.img K) :=
  isFPrimeModule_of_uMap hKF (lin.restr h.K_le_gam) (lin.restr_surjective h.K_le_gam)
    (h.ker_restr_le hW₀ lin) (psiK h hW₀ lin) (psiK_surjective h hW₀ lin)
    (psiK_fixed h hW₀ lin) (psiK_equiv h hW₀ lin)

end Setup

end CFSG.CGT.Foote82
