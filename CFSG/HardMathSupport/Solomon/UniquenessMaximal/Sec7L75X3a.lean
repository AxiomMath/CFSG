module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L75Ctx
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bClosureIa_eq_of_component {B K : Subgroup G} {x : G}
    (hxK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hKL : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) (hI : IsIaFacts B K x) :
    bClosureIa K x = K := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set I := bClosureIa K x with hIdef
  have hIC : I ≤ C := hI.component.1
  have hKC : K ≤ C := hxK.1
  have hOIC : GLAPPrimeCoreOf 3 I ≤ GLAPPrimeCoreOf 3 C :=
    glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hI.component.2.1
  have hI' : I ≤ K ⊔ GLAPPrimeCoreOf 3 C :=
    hI.le_kZero_sup.trans (sup_le_sup (kZeroOf_le B K) hOIC)
  have hKN : K ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 C : Set G) :=
    hKC.trans (le_normalizer_glaPPrimeCoreOf 3 C)
  have hle : barX 3 C I ≤ barX 3 C K := by
    refine barX_le_of_forall hKC fun i hi => ?_
    have hi' : i ∈ ((K ⊔ GLAPPrimeCoreOf 3 C : Subgroup G) : Set G) := hI' hi
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKN] at hi'
    obtain ⟨k, hk, o, ho, rfl⟩ := hi'
    exact ⟨k, hk, by simpa using ho⟩
  have hcardI : Nat.card (barX 3 C I) = 20160 := by
    rw [← Nat.card_congr (quotEquivBarX Nat.prime_three hIC hI.component.2.1).toEquiv]
    exact card_eq_of_isLThreeFour hI.lThreeFour
  have hcardK : Nat.card (barX 3 C K) = 20160 := by
    rw [← Nat.card_congr (quotEquivBarX Nat.prime_three hKC hxK.2.1).toEquiv]
    exact card_eq_of_isLThreeFour hKL
  have heq : barX 3 C I = barX 3 C K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardI, hcardK])
  exact glaPComponent_unique hI.component hxK heq

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem hCx (c : Ctx75 B N K x) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have hxA : x ∈ centralizerQuot B K := mem_centralizerQuot_of_le_centralizer c.hxB c.hxK.1
  have hI : IsIaFacts B K x := c.hf.ia x hxA c.hx1
  have h := bClosureIa_eq_of_component c.hxK c.hf.lThreeFour hI
  have := hI.normal
  rwa [h] at this

end Ctx75

omit [Finite G] in
private theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {H : Subgroup G} (y : H) :
    (y : G) ∈ GLAPPrimeCoreOf p H ↔ y ∈ GLAPPrimeCore p ↥H := by
  constructor
  · rintro ⟨y', hy', e⟩
    have : y' = y := Subtype.ext e
    subst this
    exact hy'
  · intro h
    exact ⟨y, h, rfl⟩

private noncomputable def quotInfEquiv {K N : Subgroup G} (hcov : Covers3 N K) :
    (↥(K ⊓ N) ⧸ GLAPPrimeCore 3 ↥(K ⊓ N)) ≃* (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
  set H := K ⊓ N with hH
  set O := GLAPPrimeCoreOf 3 K with hO
  have hHK : H ≤ K := inf_le_left
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hcov' : K ≤ H ⊔ O := by rwa [hH, inf_comm]
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := hHK.trans hKO
  let f : ↥H →* (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hHK)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hk' : (k : G) ∈ ((H ⊔ O : Subgroup G) : Set G) := hcov' k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H O hHO] at hk'
    obtain ⟨j, hj, o, ho, hjo⟩ := hk'
    refine ⟨⟨j, hj⟩, ?_⟩
    change QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hHK ⟨j, hj⟩) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) k
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hmem : ((Subgroup.inclusion hHK ⟨j, hj⟩)⁻¹ * k : ↥K) ∈ GLAPPrimeCore 3 ↥K := by
      rw [← mem_glaPPrimeCoreOf_iff]
      have : (((Subgroup.inclusion hHK ⟨j, hj⟩)⁻¹ * k : ↥K) : G) = o := by
        have h1 : j * o = (k : G) := hjo
        simp [← h1]
      rw [this]
      exact ho
    exact hmem
  have hker : f.ker = GLAPPrimeCore 3 ↥H := by
    ext y
    rw [MonoidHom.mem_ker, ← mem_glaPPrimeCoreOf_iff, Sec7.glaPPrimeCoreOf_inf_eq hcov]
    change QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hHK y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← mem_glaPPrimeCoreOf_iff]
    constructor
    · intro h
      exact ⟨y.2, h⟩
    · intro h
      exact h.2
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)


omit [Finite G] in
private theorem isQuasisimple_of_simple' {L : Type*} [Group L] (hT : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsQuasisimple L := by
  have hcenter : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · have e : L ⧸ Subgroup.center L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).2 hT

omit [Finite G] in
private theorem eq_top_of_isComponentOf {Q : Type*} [Group Q] {A : Subgroup Q}
    (hQ : CFSG.Open.IsQuasisimple Q) (hA : IsComponentOf A ⊤) : A = ⊤ := by
  have hperf : Group.IsPerfect ↥A := ⟨hA.2.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hQ A hA.2.1
    with h | h
  · exfalso
    have hq := hA.2.2
    have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    subst h
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this rfl
  · exact h

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem layer_data (c : Ctx75 B N K x) :
    GLAPComponent 3 (K ⊓ N) (GLAPLayer 3 (K ⊓ N)) ∧
      barX 3 (K ⊓ N) (GLAPLayer 3 (K ⊓ N)) = ⊤ ∧
      K ≤ GLAPLayer 3 (K ⊓ N) ⊔ GLAPPrimeCoreOf 3 K := by
  set Y := K ⊓ N with hY
  have hYK : Y ≤ K := inf_le_left
  have hL34 : IsLThreeFour (↥Y ⧸ GLAPPrimeCore 3 ↥Y) :=
    IsLThreeFour.of_mulEquiv (quotInfEquiv c.cov).symm c.hf.lThreeFour
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_isLThreeFour hL34
  have hQ : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore 3 ↥Y) := isQuasisimple_of_simple' hs hnab
  have hcompTop : IsComponentOf (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ⟩
  obtain ⟨L, hL, hLtop⟩ := exists_glaPComponent_barX_eq (p := 3) Y hcompTop
  have hset : {L' : Subgroup G | GLAPComponent 3 Y L'} = {L} := by
    ext L'
    refine ⟨fun hL' => ?_, fun hL' => ?_⟩
    · have h1 : barX 3 Y L' = ⊤ := eq_top_of_isComponentOf hQ hL'.2.2.1
      exact glaPComponent_unique hL' hL (h1.trans hLtop.symm)
    · rw [Set.mem_singleton_iff.1 hL']
      exact hL
  have hlayer : GLAPLayer 3 Y = L := by
    unfold GLAPLayer
    rw [hset, sSup_singleton]
  rw [hlayer]
  refine ⟨hL, hLtop, ?_⟩
  have hcov' : K ≤ Y ⊔ GLAPPrimeCoreOf 3 K := by
    have := c.cov
    rwa [Covers3, inf_comm] at this
  have hOYK : GLAPPrimeCoreOf 3 Y ≤ GLAPPrimeCoreOf 3 K := by
    rw [hY, Sec7.glaPPrimeCoreOf_inf_eq c.cov]
    exact inf_le_right
  have hYL : Y ≤ L ⊔ GLAPPrimeCoreOf 3 K := by
    intro y hy
    have hle : barX 3 Y Y ≤ barX 3 Y L := by rw [barX_self, hLtop]
    obtain ⟨l, hl, hlo⟩ := exists_of_barX_le hle hy hy
    have h1 := Subgroup.mul_mem_sup hl (hOYK hlo)
    simpa using h1
  exact hcov'.trans (sup_le hYL le_sup_right)

end Ctx75

theorem glaPComponent_of_normal {p : ℕ} (hp : p.Prime) {H M L : Subgroup G}
    (hL : GLAPComponent p H L) (hHM : H ≤ M) (hM : M ≤ Subgroup.normalizer (L : Set G)) :
    GLAPComponent p M L := by
  obtain ⟨hLH, hsnH, hcomp, hmin⟩ := hL
  have hLM : L ≤ M := hLH.trans hHM
  have hsnM : IsSubnormal L M :=
    IsSubnormal.step (M := M) hLM ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hM)
      (IsSubnormal.refl M)
  refine ⟨hLM, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p H L) ≃* ↥(barX p M L) :=
      (quotEquivBarX hp hLH hsnH).symm.trans (quotEquivBarX hp hLM hsnM)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJL : J ≤ L := hJ.le
    have hcoreL : L ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsnH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJL.trans hLH) hHM
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H L
    refine le_antisymm (barX_mono p hJL) ?_
    refine barX_le_of_forall (hJL.trans hLH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hLM hk)
    exact ⟨j, hj, hcoreL ⟨L.mul_mem (L.inv_mem (hJL hj)) hk, hjk⟩⟩

namespace Ctx75

variable {B N K : Subgroup G} {x : G}

theorem K0_comp (c : Ctx75 B N K x) :
    GLAPComponent 3 (N ⊓ Subgroup.centralizer ({x} : Set G)) (GLAPLayer 3 (K ⊓ N)) := by
  refine glaPComponent_of_normal Nat.prime_three c.layer_data.1 ?_ ?_
  · exact le_inf inf_le_right (inf_le_left.trans c.hxK.1)
  · intro g hg
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := c.hCx hg.2
    exact Sec7.mem_normalizer_glaPLayer (Sec7.inf_normalizer_le_normalizer_inf K N
      ⟨hgK, Subgroup.le_normalizer hg.1⟩)

theorem B_le_normalizer_K0 (c : Ctx75 B N K x) :
    B ≤ Subgroup.normalizer (GLAPLayer 3 (K ⊓ N) : Set G) := fun _ hb =>
  Sec7.mem_normalizer_glaPLayer (Sec7.inf_normalizer_le_normalizer_inf K N
    ⟨c.hf.normalizes hb, Subgroup.le_normalizer (c.hBN hb)⟩)

end Ctx75

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
