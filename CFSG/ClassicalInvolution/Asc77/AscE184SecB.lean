module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecA
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE184Sect

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def sectionMembers (Ω : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ ⁅A, J⁆ ≤ oddCoreOf J}

@[expose] def sectionFamily (Ω : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  secMember A '' sectionMembers Ω A

@[expose] def sectionHull (Ω : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  ⨆ L ∈ sectionFamily Ω A, L

omit [Finite G] [Fact p.Prime] in
theorem secMember_mem_sectionFamily {A J : Subgroup G} (hJ : J ∈ sectionMembers Ω A) :
    secMember A J ∈ sectionFamily Ω A :=
  ⟨J, hJ, rfl⟩

omit [Finite G] [Fact p.Prime] in
theorem le_sectionHull {A J : Subgroup G} (hJ : J ∈ sectionMembers Ω A) :
    secMember A J ≤ sectionHull Ω A :=
  le_iSup₂_of_le _ (secMember_mem_sectionFamily hJ) le_rfl

omit [Finite G] [Fact p.Prime] in
theorem sectionHull_le_centralizer (Ω : Set (Subgroup G)) (A : Subgroup G) :
    sectionHull Ω A ≤ Subgroup.centralizer (A : Set G) := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨J, -, rfl⟩ := hL
  exact secMember_le_centralizer A J

omit [Finite G] [Fact p.Prime] in
theorem oddCoreOf_conjSub (g : G) (J : Subgroup G) :
    oddCoreOf (conjSub g J) = conjSub g (oddCoreOf J) := by
  let e : ↥J ≃* ↥(conjSub g J) :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hinv : (classicalInvolutionOddCore ↥J).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g J) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcoe : ∀ j : ↥J, ((e j : ↥(conjSub g J)) : G) = g * (j : G) * g⁻¹ := fun j => rfl
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hyO⟩ := mem_oddCoreOf_iff.mp hy
    rw [← hinv] at hyO
    obtain ⟨j, hj, hje⟩ := hyO
    have h1 : g * (j : G) * g⁻¹ = y := by
      have hje' : e j = ⟨y, hyC⟩ := hje
      have := congrArg Subtype.val hje'
      rw [hcoe] at this
      exact this
    rw [mem_conjSub_iff]
    have h2 : g⁻¹ * y * g = (j : G) := by rw [← h1]; group
    rw [h2]
    exact mem_oddCoreOf_iff.mpr ⟨j.2, hj⟩
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨hjJ, hjO⟩ := mem_oddCoreOf_iff.mp hy
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hyC : y ∈ conjSub g J := by
      rw [← h1]
      exact conj_mem_conjSub hjJ
    refine mem_oddCoreOf_iff.mpr ⟨hyC, ?_⟩
    rw [← hinv]
    refine ⟨⟨g⁻¹ * y * g, hjJ⟩, hjO, Subtype.ext ?_⟩
    show ((e ⟨g⁻¹ * y * g, hjJ⟩ : ↥(conjSub g J)) : G) = y
    rw [hcoe]
    exact h1

omit [Finite G] in
theorem conjSub_mem_sectionMembers (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) (hJ : J ∈ sectionMembers Ω A) :
    conjSub g J ∈ sectionMembers Ω A := by
  refine ⟨hΩ.conjInvariant g J hJ.1, ?_⟩
  rw [oddCoreOf_conjSub]
  refine Subgroup.commutator_le.mpr fun a ha y hy => ?_
  rw [mem_conjSub_iff] at hy ⊢
  have hag : g⁻¹ * a * g = a := by
    have := Subgroup.mem_centralizer_iff.mp hg a ha
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [this]
      _ = a := by group
  have e : g⁻¹ * ⁅a, y⁆ * g = ⁅g⁻¹ * a * g, g⁻¹ * y * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hag]
  exact hJ.2 (Subgroup.commutator_mem_commutator ha hy)


omit [Finite G] in
theorem conjSub_mem_sectionFamily (hΩ : HypOmegaMod p f Ω) {A L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) (hL : L ∈ sectionFamily Ω A) :
    conjSub g L ∈ sectionFamily Ω A := by
  obtain ⟨J, hJ, rfl⟩ := hL
  exact ⟨conjSub g J, conjSub_mem_sectionMembers hΩ hg hJ, (conjSub_secMember hg).symm⟩

omit [Finite G] [Fact p.Prime] in
theorem conjSub_secMember_of_normalizer {A J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) (hgN : g ∈ Subgroup.normalizer (J : Set G)) :
    conjSub g (secMember A J) = secMember A J := by
  rw [conjSub_secMember hg, mem_normalizer_iff_conjSub_eq.mp hgN]

theorem eq_of_secMember_eq (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {A J J' : Subgroup G}
    (hA : IsPGroup 2 ↥A) (hJ : J ∈ sectionMembers Ω A) (hJ' : J' ∈ sectionMembers Ω A)
    (h : secMember A J = secMember A J') : J = J' := by
  obtain ⟨T, hT⟩ := exists_mem_fixedSylows hA hJ.2
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJ.1 hT.1)
  have hTJ' : T ≤ J' := by
    have := le_secMember hT
    rw [h] at this
    exact this.trans (secMember_le_left A J')
  exact hΩ.eq_of_le_of_le hJ.1 hJ'.1 hT.1.2.1 (by omega) hT.1.1 hTJ'

omit [Finite G] in
theorem isSubnormal_member (hΩ : HypOmegaMod p f Ω) {J : Subgroup G} (hJ : J ∈ Ω) {z : G}
    (hz : IsUniqueInvolution J z) : IsSubnormal J (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'⟩ := hΩ.classical J hJ
  have hz'sq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hz'ne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = z := (hz.unique z' hz'.mem hz'sq).resolve_left hz'ne
  exact hz'.subnormal

omit [Finite G] in
theorem isClassicalMember_subgroupOf_of_subnormal {L H : Subgroup G} {z : G} (hLH : L ≤ H)
    (hzL : z ∈ L) (hz2 : orderOf z = 2) (hperf : Group.IsPerfect ↥L)
    (hsub : IsSubnormal L (Subgroup.centralizer ({z} : Set G) ⊓ H))
    (hequiv : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, GaloisField p f))) :
    IsClassicalMember p f (L.subgroupOf H) (⟨z, hLH hzL⟩ : H) := by
  have e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr hzL, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact hz2
  · have := hperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ H).subgroupOf H =
        Subgroup.centralizer ({(⟨z, hLH hzL⟩ : H)} : Set H) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf hsub H
  · obtain ⟨e'⟩ := hequiv
    have hO : (classicalInvolutionOddCore (L.subgroupOf H)).map e.toMonoidHom =
        classicalInvolutionOddCore L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).trans e'⟩

theorem exists_isClassicalMember_secMember (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {A J Y : Subgroup G} (hA : IsPGroup 2 ↥A) (hJ : J ∈ sectionMembers Ω A)
    (hYC : Y ≤ Subgroup.centralizer (A : Set G)) (hJY : secMember A J ≤ Y) :
    ∃ z' : ↥Y, IsClassicalMember p f ((secMember A J).subgroupOf Y) z' := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hJ.1
  have hzM := isUniqueInvolution_secMember hp hΩ hA hJ.1 hJ.2 hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hsubJ := isSubnormal_member hΩ hJ.1 hz
  have h1 : IsSubnormal (J ⊓ Y) (Subgroup.centralizer ({z} : Set G) ⊓ Y) :=
    isSubnormal_inf hsubJ Y
  have hle : secMember A J ≤ J ⊓ Y := le_inf (secMember_le_left A J) hJY
  have hN : ((secMember A J).subgroupOf (J ⊓ Y)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hle).mpr ?_
    intro h k hh hk
    have hkC := hYC hk.2
    have := conj_mem_conjSub (n := k) hh
    rwa [conjSub_secMember_of_mem hk.1 hkC] at this
  have h2 : IsSubnormal (secMember A J) (J ⊓ Y) := isSubnormal_of_normal_subgroupOf hle hN
  exact ⟨⟨z, hJY hzM.mem⟩, isClassicalMember_subgroupOf_of_subnormal hJY hzM.mem hz2
    (secMember_perfect hΩ hA hJ.1 hJ.2) (isSubnormal_trans h2 h1)
    (nonempty_equiv_secMember hΩ hA hJ.1 hJ.2)⟩


theorem hypOmegaMod_sectionFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {A : Subgroup G} (hA : IsPGroup 2 ↥A) :
    HypOmegaMod p f (restrictFamily (sectionFamily Ω A) (sectionHull Ω A)) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    refine ⟨conjSub (n : G) L, conjSub_mem_sectionFamily hΩ
      (sectionHull_le_centralizer Ω A n.2) hL, ?_, conjSub_subgroupOf _ n L⟩
    have := conjSub_mono (n := (n : G)) hLY
    rwa [conjSub_eq_self_of_mem n.2] at this
  classical := by
    rintro _ ⟨_, ⟨J, hJ, rfl⟩, hJY, rfl⟩
    obtain ⟨z', hz'⟩ := exists_isClassicalMember_secMember hp hq hΩ hA hJ
      (sectionHull_le_centralizer Ω A) hJY
    exact ⟨z', hz'⟩
  omega4 := by
    rintro _ ⟨_, ⟨K, hK, rfl⟩, hKY, rfl⟩ _ ⟨_, ⟨J, hJ, rfl⟩, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 K hK.1 J hJ.1 hKJ
    have hcard : Nat.card ↥((secMember A K).subgroupOf (sectionHull Ω A) ⊓
        (secMember A J).subgroupOf (sectionHull Ω A)) =
        Nat.card ↥(secMember A K ⊓ secMember A J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    have hdvd : Nat.card ↥(secMember A K ⊓ secMember A J) ∣ Nat.card ↥(K ⊓ J) :=
      Subgroup.card_dvd_of_le (inf_le_inf (secMember_le_left A K) (secMember_le_left A J))
    have hN0 : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
    have hval : padicValNat 2 (Nat.card ↥(secMember A K ⊓ secMember A J)) ≤
        padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
      (padicValNat_dvd_iff_le hN0).mp (pow_padicValNat_dvd.trans hdvd)
    rw [hcard]
    refine ⟨hval.trans h1, fun h => ?_⟩
    have h3 : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 := le_antisymm h1 (h ▸ hval)
    have hle := h2 h3
    have hJN : secMember A J ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_commutator_le_oddCoreOf
        ((Subgroup.commutator_mono (secMember_le_left A J) le_rfl).trans
          (by rw [Subgroup.commutator_comm]; exact hle.trans inf_le_left))
    have hKN : secMember A K ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_commutator_le_oddCoreOf
        ((Subgroup.commutator_mono (secMember_le_left A K) le_rfl).trans
          (hle.trans inf_le_right))
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY, oddCoreOf_secMember hΩ hA hK.1 hK.2,
      oddCoreOf_secMember hΩ hA hJ.1 hJ.2]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haG : (a : G) ∈ secMember A K := Subgroup.mem_subgroupOf.mp ha
    have hbG : (b : G) ∈ secMember A J := Subgroup.mem_subgroupOf.mp hb
    have hab : ⁅(a : G), (b : G)⁆ ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (secMember_le_left A K haG) (secMember_le_left A J hbG)
    have haC := secMember_le_centralizer A K haG
    have hbC := secMember_le_centralizer A J hbG
    have hK' : ⁅(a : G), (b : G)⁆ ∈ secMember A K := by
      have e : ⁅(a : G), (b : G)⁆ = (a : G) * ((b : G) * (a : G)⁻¹ * (b : G)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      have h4 : (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ conjSub (b : G) (secMember A K) :=
        conj_mem_conjSub ((secMember A K).inv_mem haG)
      rw [conjSub_secMember_of_normalizer hbC (hJN hbG)] at h4
      exact (secMember A K).mul_mem haG h4
    have hJ' : ⁅(a : G), (b : G)⁆ ∈ secMember A J := by
      have e : ⁅(a : G), (b : G)⁆ = ((a : G) * (b : G) * (a : G)⁻¹) * (b : G)⁻¹ := by
        rw [commutatorElement_def]
      rw [e]
      have h4 : (a : G) * (b : G) * (a : G)⁻¹ ∈ conjSub (a : G) (secMember A J) :=
        conj_mem_conjSub hbG
      rw [conjSub_secMember_of_normalizer haC (hKN haG)] at h4
      exact (secMember A J).mul_mem h4 ((secMember A J).inv_mem hbG)
    exact ⟨Subgroup.mem_subgroupOf.mpr ⟨hK', (hle hab).1⟩,
      Subgroup.mem_subgroupOf.mpr ⟨hJ', (hle hab).2⟩⟩
  omega5 := by
    rintro _ ⟨_, ⟨K, hK, rfl⟩, hKY, rfl⟩ _ ⟨_, ⟨J, hJ, rfl⟩, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzKA : IsUniqueInvolution (secMember A K) (z' : G) :=
      isUniqueInvolution_of_subgroupOf hz' hKY
    obtain ⟨z₀, hz₀⟩ := hΩ.exists_uniqueInvolution hp hq hK.1
    have hzz : (z' : G) = z₀ := hzKA.eq (isUniqueInvolution_secMember hp hΩ hA hK.1 hK.2 hz₀)
    have hzK : IsUniqueInvolution K (z' : G) := hzz ▸ hz₀
    have hvJ' : (v : G) ∈ secMember A J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (secMember_le_left A J (Subgroup.mem_subgroupOf.mp hw')))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K hK.1 J hJ.1 hKJ (z' : G) hzK (v : G) (secMember_le_left A J hvJ') hnc'
      hv2' (congrArg Subtype.val hvz)
    have hvC : (v : G) ∈ Subgroup.centralizer (A : Set G) := sectionHull_le_centralizer Ω A v.2
    have : (v : G) ∈ Subgroup.normalizer ((secMember A K : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_secMember hvC,
        mem_normalizer_iff_conjSub_eq.mp hn]
    exact (mem_normalizer_subgroupOf_iff hKY).mp this

end CFSG.ClassicalInvolution.Asc77.AscE184Sect
