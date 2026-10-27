module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrNon
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Pair
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Tri
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

theorem TypeRFam.coreFamIn (h : TypeRFam r Ω) {X : Subgroup G}
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) (hLX : ∀ C ∈ coreFam Ω x, C ≤ X) :
    TypeRFam r (restrictFamily (coreFam Ω x) X) := by
  have hz : ∀ L, XMem Ω x L → ∃ z : G, IsUniqueInvolution L z := fun L hL =>
    Sec6Gen.exists_uniqueInvolution h.hyp hL.1
  have hsyl : ∀ L, XMem Ω x L → ∀ P, IsSylow2In P (coreAt x L) → IsSylow2In P L :=
    fun L hL P hP => ((isSylow2In_coreAt_iff hL).mp hP).1
  have hCX : ∀ {L}, XMem Ω x L → coreAt x L ≤ X := fun hL => hLX _ (coreAt_mem_coreFam hL)
  refine
    { hyp := hypOmegaGen_restrict_of X hLX
        (fun n hn C hC => conjSub_mem_coreFam h.hyp.conjInvariant hC (hXx hn)) ?_ ?_ ?_ ?_ ?_
      cls := ?_
      twoGroup := ?_
      quat := ?_
      tight := ?_
      noTwins := ?_ }
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hzL⟩ := hz L hL
    obtain ⟨P₀, hP₀, hP₀x⟩ := XMem.exists_sylow hL
    obtain ⟨-, P₁, hP₁, hP₁nc⟩ := h.hyp.omega1 L hL.1
    refine ⟨⟨z, isUniqueInvolution_coreAt h hL hzL⟩, P₀,
      (isSylow2In_coreAt_iff hL).mpr ⟨hP₀, hP₀x⟩, fun hc => hP₁nc ?_⟩
    obtain ⟨g, -, hg⟩ := Thompson.exists_conj_of_isSylow2In hP₁ hP₀
    subst hg
    let e : ↥P₁ ≃* ↥(conjSub g P₁) :=
      P₁.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _)⟩⟩
  · rintro _ ⟨L, -, rfl⟩
    exact closure_twoElts_coreAt x L
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ P Q hP hQ
    exact h.hyp.omega3 K hK.1 J hJ.1 P Q (hsyl K hK P hP) (hsyl J hJ Q hQ)
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact coreAt_omega4 h hK.1 hJ.1 hne
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ - z' hz' v hv - - hvz
    obtain ⟨z, hzK⟩ := hz K hK
    have hzz : z' = z := hz'.eq (isUniqueInvolution_coreAt h hK hzK)
    subst hzz
    exact coreAt_mem_normalizer h hK.1 hzK (coreAt_le_centralizer x J hv) hvz
  · have hnorm : ∀ L, XMem Ω x L → ∀ z : G, IsUniqueInvolution L z →
        ∀ y : ↥X, (y : G) * z = z * (y : G) →
          y ∈ Subgroup.normalizer (((coreAt x L).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      intro L hL z hzL y hyz
      exact (mem_normalizer_subgroupOf_iff (hCX hL)).mp
        (coreAt_mem_normalizer h hL.1 hzL (hXx y.2) hyz)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩
      obtain ⟨z, hzL⟩ := hz L hL
      have hzC := isUniqueInvolution_coreAt h hL hzL
      have hz' := isUniqueInvolution_subgroupOf hzC hCY
      refine ⟨_, hz'.mem, orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
      have hle : (coreAt x L).subgroupOf X ≤
          Subgroup.centralizer ({(⟨z, hCY hzC.mem⟩ : ↥X)} : Set ↥X) := by
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (h.le_centralizer hL.1 hzL (coreAt_le x L (Subgroup.mem_subgroupOf.mp hy)))
      have hn : (((coreAt x L).subgroupOf X).subgroupOf
          (Subgroup.centralizer ({(⟨z, hCY hzC.mem⟩ : ↥X)} : Set ↥X))).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
        intro y hy
        exact hnorm L hL z hzL y
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
      exact IsSubnormal.step hle hn (IsSubnormal.refl _)
    · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ u a b hu hu2 huu ha hb hau hbu
      obtain ⟨P₀, hP₀, hP₀x⟩ := XMem.exists_sylow hL
      obtain ⟨e⟩ := h.quat L hL.1 P₀ hP₀
      have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
      have hu' : (u : G) ∈ coreAt x L := Subgroup.mem_subgroupOf.mp hu
      have ha' : (a : G) ∈ coreAt x L := Subgroup.mem_subgroupOf.mp ha
      have hb' : (b : G) ∈ coreAt x L := Subgroup.mem_subgroupOf.mp hb
      have hc := commOdd_of_quat (twoGroup_coreAt h hL.1)
        ((isSylow2In_coreAt_iff hL).mpr ⟨hP₀, hP₀x⟩) e hu' (isPGroup_zpowers_coe_iff.mpr hu2)
        (fun h1 => huu (Subtype.ext h1)) ha' hb' (congrArg Subtype.val hau)
        (congrArg Subtype.val hbu)
      rw [oddCoreOf_subgroupOf hCY]
      exact Subgroup.mem_subgroupOf.mpr hc
  · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩
    let φ : ↥((coreAt x L).subgroupOf X) ≃* ↥(coreAt x L) := Subgroup.subgroupOfEquivOfLe hCY
    exact (twoGroup_coreAt h hL.1).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ P' hP'
    have hP : IsSylow2In (P'.map X.subtype) (coreAt x L) := by
      have := isSylow2In_map_subtype_iff.mpr hP'
      rwa [Subgroup.map_subgroupOf_eq_of_le hCY] at this
    obtain ⟨e⟩ := h.quat L hL.1 _ ((isSylow2In_coreAt_iff hL).mp hP).1
    exact ⟨(P'.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩
  · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ w hw y hy
    obtain ⟨z, hzL⟩ := hz L hL
    have hzC := isUniqueInvolution_coreAt h hL hzL
    have hwz : (w : G) = z := (isUniqueInvolution_of_subgroupOf hw hCY).eq hzC
    have hyz := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact (mem_normalizer_subgroupOf_iff hCY).mp
      (coreAt_mem_normalizer h hL.1 hzL (hXx y.2) (hwz ▸ congrArg Subtype.val hyz))
  · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ _ ⟨⟨_, ⟨M, hM, rfl⟩, hDY, rfl⟩, w, hwL, hwM⟩
    obtain ⟨z, hzL⟩ := hz L hL
    obtain ⟨y, hyM⟩ := hz M hM
    have e1 : (w : G) = z :=
      (isUniqueInvolution_of_subgroupOf hwL hCY).eq (isUniqueInvolution_coreAt h hL hzL)
    have e2 : (w : G) = y :=
      (isUniqueInvolution_of_subgroupOf hwM hDY).eq (isUniqueInvolution_coreAt h hM hyM)
    have hMt : M ∈ twinSet Ω L := ⟨hM.1, z, hzL, by rw [← e1, e2]; exact hyM⟩
    rw [h.noTwins L hL.1 M hMt]

section Vertex

variable (Ω) (c : G)

@[expose] def vtxFam : Set (Subgroup (OddQuot c)) :=
  quotFamily (restrictFamily (coreFam Ω c) (Subgroup.centralizer ({c} : Set G)))
    (componentClassificationOddCore ↥(Subgroup.centralizer ({c} : Set G)))

variable {Ω c}

theorem TypeRFam.vtxFam (h : TypeRFam r Ω) : TypeRFam r (vtxFam Ω c) :=
  (h.coreFamIn le_rfl fun _ ⟨L, _, hC⟩ => hC ▸ coreAt_le_centralizer c L).quotFamily
    (CFSG.ComponentClassification.OddCore.odd_card _)

omit [Finite G] in
theorem modOdd_coreAt_mem_vtxFam {L : Subgroup G} (hL : XMem Ω c L) :
    modOdd c (coreAt c L) ∈ vtxFam Ω c :=
  map_mem_quotFamily ⟨coreAt c L, coreAt_mem_coreFam hL, coreAt_le_centralizer c L, rfl⟩

theorem isUniqueInvolution_modOdd_coreAt (h : TypeRFam r Ω) {L : Subgroup G} (hL : XMem Ω c L)
    {z : G} (hz : IsUniqueInvolution L z) (hzc : z ∈ Subgroup.centralizer ({c} : Set G)) :
    IsUniqueInvolution (modOdd c (coreAt c L)) (oddQuotMk c ⟨z, hzc⟩) :=
  isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card _) _)
    (isUniqueInvolution_subgroupOf (isUniqueInvolution_coreAt h hL hz)
      (coreAt_le_centralizer c L))

theorem modOdd_coreAt_mem_omegaNbr {L M : Subgroup G} (hM : XMem Ω c M)
    {P : Subgroup G} (hP : IsSylow2In P M) (hPc : P ≤ Subgroup.centralizer ({c} : Set G))
    (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hne : modOdd c (coreAt c L) ≠ modOdd c (coreAt c M)) :
    modOdd c (coreAt c M) ∈ omegaNbr (vtxFam Ω c) (modOdd c (coreAt c L)) := by
  have hPC : IsSylow2In P (coreAt c M) := (isSylow2In_coreAt_iff hM).mpr ⟨hP, hPc⟩
  have hP' : IsSylow2In (P.subgroupOf (Subgroup.centralizer ({c} : Set G)))
      ((coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    hPC.subgroupOf (coreAt_le_centralizer c M)
  refine ⟨modOdd_coreAt_mem_vtxFam hM, hne.symm,
    (P.subgroupOf (Subgroup.centralizer ({c} : Set G))).map (oddQuotMk c),
    mem_RSet_of_isSylow2In (modOdd_coreAt_mem_vtxFam hM)
      (isSylow2In_map_mk (CFSG.ComponentClassification.OddCore.odd_card _) hP'),
    Subgroup.map_mono hP'.1, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hpN : (p : G) ∈ Subgroup.normalizer (coreAt c L : Set G) :=
    mem_normalizer_coreAt c (hPN hp') (hPc hp')
  exact mk_mem_normalizer_map
    ((mem_normalizer_subgroupOf_iff (coreAt_le_centralizer c L)).mp hpN)

variable (c) in
theorem oddQuot_oddCore_eq_bot : classicalInvolutionOddCore (OddQuot c) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree _

theorem natCard_oddQuot_lt (hZ : Subgroup.center G = ⊥) (hc1 : c ≠ 1) :
    Nat.card (OddQuot c) < Nat.card G :=
  lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _))
    (card_centralizer_lt_of_center hZ hc1)

end Vertex

theorem xMem_of_triFrame_of_mem (hΩ : HypOmegaGen Ω)
    (hnt : ∀ L ∈ Ω, ∀ L' ∈ twinSet Ω L, L' = L) {M : Fin 3 → Subgroup G} {x : Fin 3 → G}
    {P : Fin 3 → Subgroup G} (hF : TriFrame Ω M x P) {c : G}
    (hc : c ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G)) (i : Fin 3) : XMem Ω c (M i) := by
  have hle : Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤
      Subgroup.centralizer ({x i} : Set G) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl) <;>
      exact Subgroup.mem_centralizer_singleton_iff.mpr (triFrame_comm_gen hF hΩ _ i)
  refine ⟨hF.mem i, T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
    (hnt _ (hF.mem i)) (hF.inv i) (hle hc), P i, hF.syl i, fun p hp => ?_⟩
  have hle' : Subgroup.closure ({x 0, x 1, x 2} : Set G) ≤
      Subgroup.centralizer ({p} : Set G) := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl) <;>
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hF.cent i _ hp)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle' hc)).symm

end CFSG.ClassicalInvolution.Q3.TL4
