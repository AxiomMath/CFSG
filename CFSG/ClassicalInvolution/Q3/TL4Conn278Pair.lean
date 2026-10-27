module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lay
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quot

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Restrict

variable {Λ : Set (Subgroup G)}

theorem hypOmegaGen_restrict_of (X : Subgroup G) (hLX : ∀ L ∈ Λ, L ≤ X)
    (hinv : ∀ n ∈ X, ∀ L ∈ Λ, conjSub n L ∈ Λ)
    (h1 : ∀ K ∈ Λ, (∃ z : G, IsUniqueInvolution K z) ∧
      ∃ P : Subgroup G, IsSylow2In P K ∧ ¬ IsMulCommutative ↥P)
    (h2 : ∀ K ∈ Λ, Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K)
    (h3 : ∀ K ∈ Λ, ∀ J ∈ Λ, ∀ P Q : Subgroup G, IsSylow2In P K → IsSylow2In Q J →
      Nat.card ↥P = Nat.card ↥Q)
    (h4 : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J →
      padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J))
    (h5 : ∀ K ∈ Λ, ∀ J ∈ Λ, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
      (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (K : Set G)) :
    HypOmegaGen (restrictFamily Λ X) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLX', rfl⟩
    refine ⟨conjSub (n : G) L, hinv _ n.2 L hL, hLX _ (hinv _ n.2 L hL),
      conjSub_subgroupOf X n L⟩
  omega1 := by
    rintro _ ⟨L, hL, hLX', rfl⟩
    obtain ⟨⟨z, hz⟩, P, hP, hPnc⟩ := h1 L hL
    refine ⟨⟨_, isUniqueInvolution_subgroupOf hz hLX'⟩, P.subgroupOf X, hP.subgroupOf hLX', ?_⟩
    intro hc
    apply hPnc
    let e : P.subgroupOf X ≃* P := Subgroup.subgroupOfEquivOfLe (hP.1.trans hLX')
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1' : e.symm a * e.symm b = e.symm b * e.symm a := hc.is_comm.comm _ _
    have h2' := congrArg e h1'
    simpa using h2'
  omega2 := by
    rintro _ ⟨L, hL, hLX', rfl⟩
    left
    apply Subgroup.map_injective X.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hLX']
    conv_rhs => rw [← h2 L hL]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, ⟨hxL, hx2⟩, rfl⟩
      exact ⟨hxL, isPGroup_zpowers_coe_iff.mpr hx2⟩
    · rintro ⟨hyL, hy2⟩
      exact ⟨⟨y, hLX' hyL⟩, ⟨hyL, isPGroup_zpowers_coe_iff.mp hy2⟩, rfl⟩
  omega3 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ P Q hP hQ
    have hP' : IsSylow2In (P.map X.subtype) K := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hKX] at this
    have hQ' : IsSylow2In (Q.map X.subtype) J := by
      have := isSylow2In_map_subtype_iff.mpr hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at this
    have h := h3 K hK J hJ _ _ hP' hQ'
    rwa [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective X.subtype_injective] at h
  omega4 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1', h2'⟩ := h4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf X ⊓ J.subgroupOf X) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKX)).toEquiv
    rw [hcard]
    refine ⟨h1', fun h => ?_⟩
    have hle := h2' h
    rw [oddCoreOf_subgroupOf hKX, oddCoreOf_subgroupOf hJX]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKX
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := h5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKX).mp hn

end Restrict


section Layer

variable (Ω : Set (Subgroup G)) (x : G)

@[expose] def coreFam : Set (Subgroup G) := {C | ∃ L, XMem Ω x L ∧ C = coreAt x L}

@[expose] noncomputable def layerY : Subgroup G := ⨆ C ∈ coreFam Ω x, C

@[expose] def pairFam : Set (Subgroup ↥(layerY Ω x)) := restrictFamily (coreFam Ω x) (layerY Ω x)

variable {Ω x}

omit [Finite G] in
theorem coreAt_mem_coreFam {L : Subgroup G} (hL : XMem Ω x L) : coreAt x L ∈ coreFam Ω x :=
  ⟨L, hL, rfl⟩

omit [Finite G] in
theorem le_layerY {C : Subgroup G} (hC : C ∈ coreFam Ω x) : C ≤ layerY Ω x :=
  le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ coreFam Ω x) => C) C hC

omit [Finite G] in
theorem coreAt_le_layerY {L : Subgroup G} (hL : XMem Ω x L) : coreAt x L ≤ layerY Ω x :=
  le_layerY (coreAt_mem_coreFam hL)

omit [Finite G] in
theorem layerY_le_centralizer : layerY Ω x ≤ Subgroup.centralizer ({x} : Set G) :=
  iSup₂_le fun _ ⟨L, _, hC⟩ => hC ▸ coreAt_le_centralizer x L

omit [Finite G] in
theorem subgroupOf_mem_pairFam {L : Subgroup G} (hL : XMem Ω x L) :
    (coreAt x L).subgroupOf (layerY Ω x) ∈ pairFam Ω x :=
  ⟨coreAt x L, coreAt_mem_coreFam hL, coreAt_le_layerY hL, rfl⟩

omit [Finite G] in
theorem conjSub_mem_coreFam (hΩ : ConjInvariant Ω) {C : Subgroup G} (hC : C ∈ coreFam Ω x)
    {c : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : conjSub c C ∈ coreFam Ω x := by
  obtain ⟨L, hL, rfl⟩ := hC
  exact ⟨conjSub c L, XMem.conj' hΩ hL hc, conjSub_coreAt x hc L⟩

end Layer

section TypeR

variable {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

theorem TypeRFam.pairFam (h : TypeRFam r Ω) : TypeRFam r (pairFam Ω x) := by
  have hYx := layerY_le_centralizer (Ω := Ω) (x := x)
  have hLX : ∀ C ∈ coreFam Ω x, C ≤ layerY Ω x := fun C hC => le_layerY hC
  have hz : ∀ L, XMem Ω x L → ∃ z : G, IsUniqueInvolution L z := fun L hL =>
    Sec6Gen.exists_uniqueInvolution h.hyp hL.1
  have hsyl : ∀ L, XMem Ω x L → ∀ P, IsSylow2In P (coreAt x L) → IsSylow2In P L :=
    fun L hL P hP => ((isSylow2In_coreAt_iff hL).mp hP).1
  refine
    { hyp := hypOmegaGen_restrict_of (layerY Ω x) hLX
        (fun n hn C hC => conjSub_mem_coreFam h.hyp.conjInvariant hC (hYx hn)) ?_ ?_ ?_ ?_ ?_
      cls := ?_
      twoGroup := ?_
      quat := ?_
      tight := ?_
      noTwins := ?_ }
  ·
    rintro _ ⟨L, hL, rfl⟩
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
  ·
    rintro _ ⟨L, -, rfl⟩
    exact closure_twoElts_coreAt x L
  ·
    rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ P Q hP hQ
    exact h.hyp.omega3 K hK.1 J hJ.1 P Q (hsyl K hK P hP) (hsyl J hJ Q hQ)
  ·
    rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact coreAt_omega4 h hK.1 hJ.1 hne
  ·
    rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ - z' hz' v hv - - hvz
    obtain ⟨z, hzK⟩ := hz K hK
    have hzz : z' = z := hz'.eq (isUniqueInvolution_coreAt h hK hzK)
    subst hzz
    exact coreAt_mem_normalizer h hK.1 hzK (coreAt_le_centralizer x J hv) hvz
  ·
    have hnorm : ∀ L, XMem Ω x L → ∀ z : G, IsUniqueInvolution L z →
        ∀ y : ↥(layerY Ω x), (y : G) * z = z * (y : G) →
          y ∈ Subgroup.normalizer (((coreAt x L).subgroupOf (layerY Ω x) :
            Subgroup ↥(layerY Ω x)) : Set ↥(layerY Ω x)) := by
      intro L hL z hzL y hyz
      exact (mem_normalizer_subgroupOf_iff (coreAt_le_layerY hL)).mp
        (coreAt_mem_normalizer h hL.1 hzL (hYx y.2) hyz)
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩
      obtain ⟨z, hzL⟩ := hz L hL
      have hzC := isUniqueInvolution_coreAt h hL hzL
      have hz' := isUniqueInvolution_subgroupOf hzC hCY
      refine ⟨_, hz'.mem, orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
      have hle : (coreAt x L).subgroupOf (layerY Ω x) ≤
          Subgroup.centralizer ({(⟨z, hCY hzC.mem⟩ : ↥(layerY Ω x))} : Set ↥(layerY Ω x)) := by
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (h.le_centralizer hL.1 hzL (coreAt_le x L (Subgroup.mem_subgroupOf.mp hy)))
      have hn : (((coreAt x L).subgroupOf (layerY Ω x)).subgroupOf
          (Subgroup.centralizer ({(⟨z, hCY hzC.mem⟩ : ↥(layerY Ω x))} :
            Set ↥(layerY Ω x)))).Normal := by
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
  ·
    rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩
    let φ : ↥((coreAt x L).subgroupOf (layerY Ω x)) ≃* ↥(coreAt x L) :=
      Subgroup.subgroupOfEquivOfLe hCY
    exact (twoGroup_coreAt h hL.1).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  ·
    rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ P' hP'
    have hP : IsSylow2In (P'.map (layerY Ω x).subtype) (coreAt x L) := by
      have := isSylow2In_map_subtype_iff.mpr hP'
      rwa [Subgroup.map_subgroupOf_eq_of_le hCY] at this
    obtain ⟨e⟩ := h.quat L hL.1 _ ((isSylow2In_coreAt_iff hL).mp hP).1
    exact ⟨(P'.equivMapOfInjective (layerY Ω x).subtype
      (layerY Ω x).subtype_injective).trans e⟩
  ·
    rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ w hw y hy
    obtain ⟨z, hzL⟩ := hz L hL
    have hzC := isUniqueInvolution_coreAt h hL hzL
    have hwz : (w : G) = z := (isUniqueInvolution_of_subgroupOf hw hCY).eq hzC
    have hyz := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact (mem_normalizer_subgroupOf_iff hCY).mp
      (coreAt_mem_normalizer h hL.1 hzL (hYx y.2) (hwz ▸ congrArg Subtype.val hyz))
  ·
    rintro _ ⟨_, ⟨L, hL, rfl⟩, hCY, rfl⟩ _ ⟨⟨_, ⟨M, hM, rfl⟩, hDY, rfl⟩, w, hwL, hwM⟩
    obtain ⟨z, hzL⟩ := hz L hL
    obtain ⟨y, hyM⟩ := hz M hM
    have e1 : (w : G) = z :=
      (isUniqueInvolution_of_subgroupOf hwL hCY).eq (isUniqueInvolution_coreAt h hL hzL)
    have e2 : (w : G) = y :=
      (isUniqueInvolution_of_subgroupOf hwM hDY).eq (isUniqueInvolution_coreAt h hM hyM)
    have hMt : M ∈ twinSet Ω L := ⟨hM.1, z, hzL, by rw [← e1, e2]; exact hyM⟩
    rw [h.noTwins L hL.1 M hMt]

end TypeR

end CFSG.ClassicalInvolution.Q3.TL4
