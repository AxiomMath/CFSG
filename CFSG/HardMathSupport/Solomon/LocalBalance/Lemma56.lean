module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma57
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6B67
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Sporadic.Bridge.M22
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Basic

variable {G : Type*} [Group G]

theorem gLBConj_bClosure_le {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) ≤ bClosure B L := by
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  unfold bClosure
  refine iSup₂_le fun b hb => ?_
  intro z hz
  rw [Subgroup.mem_comap]
  have e : (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := by
    simp
  rw [e]
  have hm : g⁻¹ * z * g ∈ GLBConj (b * g) L := by
    rw [mem_gLBConj]
    have e2 : b * g * (g⁻¹ * z * g) * (b * g)⁻¹ = b * z * b⁻¹ := by group
    rw [e2]
    exact mem_gLBConj.1 hz
  exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c L) (b * g)
    (B.mul_mem hb hg)) hm

theorem glbConj_bClosure_eq {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) = bClosure B L := by
  refine le_antisymm (gLBConj_bClosure_le hg) ?_
  have h0 : GLBConj g⁻¹ (bClosure B L) ≤ bClosure B L :=
    gLBConj_bClosure_le (B.inv_mem hg)
  have h1 : GLBConj g (GLBConj g⁻¹ (bClosure B L)) ≤ GLBConj g (bClosure B L) :=
    gLBConj_mono g h0
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1

theorem bClosure_le {B L K : Subgroup G} (h : ∀ b ∈ B, GLBConj b L ≤ K) :
    bClosure B L ≤ K :=
  iSup₂_le fun b hb => h b hb

theorem bClosure_ne_of_not_le {B L : Subgroup G} (h : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    bClosure B L ≠ L := by
  intro heq
  apply h
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  have := glbConj_bClosure_eq (L := L) hg
  rwa [heq] at this

end Basic


section Gen

variable {G : Type*} [Group G]


theorem mk_comm_of_mem {X : Subgroup G} {u v : G} (hu : u ∈ X) (hv : v ∈ X)
    (h : u * v * u⁻¹ * v⁻¹ ∈ GLAPPrimeCoreOf 3 X) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨u, hu⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨v, hv⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨v, hv⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨u, hu⟩ := by
  obtain ⟨c, hc1, hc2⟩ := h
  have hcc : c = ⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ := Subtype.ext (by simpa using hc2)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c = 1 := (QuotientGroup.eq_one_iff _).2 hc1
  rw [hcc, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

variable [Finite G] in
theorem mem_centralizerQuot_of_comm {X I : Subgroup G} (hI : GLAPComponent 3 X I) {y : G}
    (hy : y ∈ X) (h : ∀ ℓ ∈ I, ℓ * y * ℓ⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 3 X) :
    y ∈ centralizerQuot I (GLAPPrimeCoreOf 3 I) := by
  have hX : GLBConj y X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hy)
  have hI' : GLAPComponent 3 X (GLBConj y I) := by
    have := glaPComponent_gLBConj (p := 3) y hI
    rwa [hX] at this
  have hbar : barX 3 X (GLBConj y I) = barX 3 X I := by
    ext w
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hz : (c : G) ∈ GLBConj y I := (Subgroup.mem_subgroupOf).1 hc
      rw [mem_gLBConj] at hz
      have hℓX : y * (c : G) * y⁻¹ ∈ X := hI.1 hz
      have hcomm := mk_comm_of_mem hℓX hy (by
        have := h _ hz
        simpa using this)
      refine ⟨⟨y * (c : G) * y⁻¹, hℓX⟩, (Subgroup.mem_subgroupOf).2 hz, ?_⟩
      have e : (⟨y * (c : G) * y⁻¹, hℓX⟩ : ↥X) = ⟨y, hy⟩ * c * ⟨y, hy⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv] at hcomm ⊢
      set t := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨y, hy⟩ : ↥X)
      set d := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c
      have h3 : t * d = t * (t * d * t⁻¹) := by
        calc t * d = t * d * t⁻¹ * t := by group
          _ = _ := hcomm
      exact (mul_left_cancel h3).symm
    · rintro ⟨c, hc, rfl⟩
      have hcI : (c : G) ∈ I := (Subgroup.mem_subgroupOf).1 hc
      have hcX : (c : G) ∈ X := c.2
      have hc' : y⁻¹ * (c : G) * y ∈ X :=
        X.mul_mem (X.mul_mem (X.inv_mem hy) hcX) hy
      have hcomm := mk_comm_of_mem hcX hy (h _ hcI)
      refine ⟨⟨y⁻¹ * (c : G) * y, hc'⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
      · rw [mem_gLBConj]
        simpa [mul_assoc] using hcI
      · have e : (⟨y⁻¹ * (c : G) * y, hc'⟩ : ↥X) = ⟨y, hy⟩⁻¹ * c * ⟨y, hy⟩ := rfl
        rw [e, map_mul, map_mul, map_inv] at *
        set t := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨y, hy⟩ : ↥X)
        set d := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c
        have h3 : d * t = t * d := hcomm
        calc t⁻¹ * d * t = t⁻¹ * (d * t) := by group
          _ = t⁻¹ * (t * d) := by rw [h3]
          _ = d := by group
  have heq : GLBConj y I = I := glaPComponent_unique hI' hI hbar
  have hN : y ∈ Subgroup.normalizer (I : Set G) := mem_normalizer_iff_gLBConj_eq.2 heq
  refine ⟨hN, ?_, ?_⟩
  · rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, heq]
  · intro x hx
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ I := by
      have h2 := (Subgroup.mem_normalizer_iff.1 hN x⁻¹).1 (I.inv_mem hx)
      have := I.mul_mem hx h2
      simpa [mul_assoc] using this
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three X I
    rw [inf_eq_right.2 hI.1] at h3
    exact h3 ⟨h x hx, h1⟩




theorem inducesFieldAut_of_mem_cq {J : Subgroup G} {y : G}
    (hy : y ∈ centralizerQuot J (GLAPPrimeCoreOf 3 J)) : InducesFieldAut 3 J y := by
  obtain ⟨hN, -, hc⟩ := hy
  refine ⟨hN, Or.inl ?_⟩
  ext w
  induction w using QuotientGroup.induction_on with | _ x => ?_
  have e1 := barAut_mk 3 J ⟨y, hN⟩ x
  simp only [MulAut.one_apply]
  rw [e1]
  have hxc := hc x.1 x.2
  rw [QuotientGroup.eq]
  obtain ⟨c', hc', hc'eq⟩ := hxc
  have hN' : (GLAPPrimeCore 3 ↥J).Normal := inferInstance
  have h3 := hN'.conj_mem c' hc' x⁻¹
  convert h3 using 1
  apply Subtype.ext
  have hc'eq' : (c' : G) = (x : G) * y * (x : G)⁻¹ * y⁻¹ := hc'eq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc'eq']
  show ((y * (x : G) * y⁻¹)⁻¹ * x : G) = _
  group

variable [Finite G]


theorem isSubnormal_sSup_of_forall {X : Subgroup G} (S : Set (Subgroup G))
    (hS : ∀ K ∈ S, K ≤ X ∧ IsSubnormal K X) : IsSubnormal (sSup S) X := by
  have hle : sSup S ≤ X := sSup_le fun K hK => (hS K hK).1
  rw [CFSG.Quasithin.isSubnormal_iff_subgroupOf hle]
  set 𝒮 : Set (Subgroup ↥X) := (fun K : Subgroup G => K.subgroupOf X) '' S with h𝒮
  have h1 : ∀ A ∈ 𝒮, A.IsSubnormal := by
    rintro _ ⟨K, hK, rfl⟩
    exact (CFSG.Quasithin.isSubnormal_iff_subgroupOf (hS K hK).1).1 (hS K hK).2
  have h2 := (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 h1).1
  have h3 : (sSup S).subgroupOf X = Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) := by
    have hc : Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) = sSup 𝒮 := by
      refine le_antisymm ((Subgroup.closure_le _).2 (Set.iUnion₂_subset fun A hA => ?_)) ?_
      · exact (le_sSup hA : A ≤ sSup 𝒮)
      · exact sSup_le fun A hA x hx => Subgroup.subset_closure (Set.mem_biUnion hA hx)
    rw [hc]
    refine le_antisymm ?_ (sSup_le ?_)
    · have h4 : sSup S ≤ (sSup 𝒮).map X.subtype := by
        refine sSup_le fun K hK => ?_
        rw [← Subgroup.map_subgroupOf_eq_of_le (hS K hK).1]
        exact Subgroup.map_mono (le_sSup ⟨K, hK, rfl⟩)
      have := Subgroup.comap_mono (f := X.subtype) h4
      rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at this
    · rintro _ ⟨K, hK, rfl⟩
      exact Subgroup.comap_mono (le_sSup hK)
  rwa [h3]

abbrev cq (J : Subgroup G) : Subgroup G := centralizerQuot J (GLAPPrimeCoreOf 3 J)

theorem le_cq_of_ne {X J J' : Subgroup G} (hJ : GLAPComponent 3 X J) (hJ' : GLAPComponent 3 X J')
    (hne : J ≠ J') : J' ≤ cq J := by
  intro y hy
  refine mem_centralizerQuot_of_comm hJ (hJ'.1 hy) (fun ℓ hℓ => ?_)
  have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hJ hJ' hne
    (Subgroup.commutator_mem_commutator hℓ hy)
  simpa [commutatorElement_def] using this

theorem b_mem_cq {b : G} {J : Subgroup G}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) J) : b ∈ cq J := by
  refine mem_centralizerQuot_of_comm hJ (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    (fun ℓ hℓ => ?_)
  have h1 : ℓ * b = b * ℓ := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hℓ)
  have : ℓ * b * ℓ⁻¹ * b⁻¹ = 1 := by
    rw [h1]; group
  rw [this]
  exact one_mem _

theorem mem_oPrimePOf_of_mem_cq {J : Subgroup G} {e : G} (he : e ∈ J) (hcq : e ∈ cq J) :
    e ∈ oPrimePOf 3 J := by
  refine mem_oPrimePOf_of_forall_commutator_mem Nat.prime_three he (fun y hy => ?_)
  have := (GLAPPrimeCoreOf 3 J).inv_mem (hcq.2.2 y hy)
  simpa [mul_assoc] using this

theorem exists_card_eq_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E) :
    ∃ k, Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  exact hp.exists_card_eq

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hF : IsElemAbelian 3 F) (h : E ≤ F) :
    IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hF h

section Main

variable {G : Type*} [Group G] [Finite G]

theorem exists_rank_three {b : G} {B' J J' J'' : Subgroup G} (hB' : IsElemAbelian 3 B')
    (hbB' : b ∈ B') (hb1 : b ≠ 1)
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) J)
    (hJ' : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) J')
    (hJ'' : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) J'')
    (h1 : J ≠ J') (h2 : J ≠ J'') (h3 : J' ≠ J'') {e' e'' : G} (he' : e' ∈ B' ⊓ J')
    (he'' : e'' ∈ B' ⊓ J'') (hn' : e' ∉ oPrimePOf 3 J') (hn'' : e'' ∉ oPrimePOf 3 J'') :
    ∃ A : Subgroup G, A ≤ B' ∧ A ≤ cq J ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
  have hcomm : ∀ {x y : G}, x ∈ B' → y ∈ B' → x * y = y * x := fun {x y} hx hy => by
    have := hB'.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hb3 : b ^ 3 = 1 := hB'.2 b hbB'
  have hy3 : e' ^ 3 = 1 := hB'.2 e' he'.1
  have hz3 : e'' ^ 3 = 1 := hB'.2 e'' he''.1
  have hbJ' : Subgroup.zpowers b ≤ cq J' := Subgroup.zpowers_le.2 (b_mem_cq hJ')
  have hbJ'' : Subgroup.zpowers b ≤ cq J'' := Subgroup.zpowers_le.2 (b_mem_cq hJ'')
  have hbJ : Subgroup.zpowers b ≤ cq J := Subgroup.zpowers_le.2 (b_mem_cq hJ)
  have hyx : e' ∉ Subgroup.zpowers b := fun h =>
    hn' (mem_oPrimePOf_of_mem_cq he'.2 (hbJ' h))
  have hzxy : e'' ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers e' := by
    intro h
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers e' ≤ cq J'' :=
      sup_le hbJ'' (Subgroup.zpowers_le.2 (le_cq_of_ne hJ'' hJ' h3.symm he'.2))
    exact hn'' (mem_oPrimePOf_of_mem_cq he''.2 (hle h))
  obtain ⟨hel, hcard⟩ := exists_isElemAbelian_card_three_of_independent
    (hcomm hbB' he'.1) (hcomm hbB' he''.1) (hcomm he'.1 he''.1) hb3 hy3 hz3 hb1 hyx hzxy
  refine ⟨Subgroup.zpowers b ⊔ Subgroup.zpowers e' ⊔ Subgroup.zpowers e'', ?_, ?_, hel, hcard⟩
  · exact sup_le (sup_le (Subgroup.zpowers_le.2 hbB') (Subgroup.zpowers_le.2 he'.1))
      (Subgroup.zpowers_le.2 he''.1)
  · exact sup_le (sup_le hbJ (Subgroup.zpowers_le.2 (le_cq_of_ne hJ hJ' h1 he'.2)))
      (Subgroup.zpowers_le.2 (le_cq_of_ne hJ hJ'' h2 he''.2))

theorem glaPComponent_conj_of_mem {b : G} {B L : Subgroup G} (hBel : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) {g : G} (hg : g ∈ B) :
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g L) := by
  have hc : g * b = b * g := by
    have := hBel.1.is_comm.comm ⟨g, hg⟩ ⟨b, hbB⟩
    simpa using congrArg Subtype.val this
  have := glaPComponent_gLBConj (p := 3) g hL
  rwa [gLBConj_centralizer_singleton_of_commute hc] at this

theorem coprime_card_gLAPPrimeCoreOf (I : Subgroup G) :
    Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 I)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective I.subtype_injective]
  exact coprime_card_gLAPPrimeCore_aux 3 ↥I

theorem exists_fixed_in_coset {I : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hc : ∀ ℓ ∈ I, ℓ * b * ℓ⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf 3 I) {g : G} (hg : g ∈ I) :
    ∃ y, y ∈ I ∧ b * y * b⁻¹ = y ∧ g⁻¹ * y ∈ GLAPPrimeCoreOf 3 I := by
  classical
  set R := GLAPPrimeCoreOf 3 I with hR
  have hbNR : b ∈ Subgroup.normalizer (R : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, hR, ← glaPPrimeCoreOf_gLBConj,
      mem_normalizer_iff_gLBConj_eq.1 hbN]
  have hbR : ∀ r ∈ R, b * r * b⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.1 hbNR r).1 hr
  have hRI : R ≤ I := Subgroup.map_subtype_le _
  let S := {t : G // g⁻¹ * t ∈ R}
  have hf : ∀ t : S, g⁻¹ * (b * t.1 * b⁻¹) ∈ R := by
    intro t
    have h1 := hc g⁻¹ (I.inv_mem hg)
    have h2 := hbR _ t.2
    have : g⁻¹ * (b * t.1 * b⁻¹) = (g⁻¹ * b * g * b⁻¹) * (b * (g⁻¹ * t.1) * b⁻¹) := by group
    rw [this]
    exact R.mul_mem (by simpa using h1) h2
  let f : Function.End S := fun t => ⟨b * t.1 * b⁻¹, hf t⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext t
    apply Subtype.ext
    show b * (b * (b * t.1 * b⁻¹) * b⁻¹) * b⁻¹ = t.1
    have h : b * b * b = 1 := by simpa [pow_succ, mul_assoc] using hb3
    calc b * (b * (b * t.1 * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * t.1 * (b * b * b)⁻¹ := by group
      _ = t.1 := by rw [h]; group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := S) hf3
  have hcardS : Fintype.card S = Nat.card R := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun t => ⟨g⁻¹ * t.1, t.2⟩, fun r => ⟨g * r.1, by simp⟩, ?_, ?_⟩
    · intro t; apply Subtype.ext; simp
    · intro r; apply Subtype.ext; simp
  have hne : 0 < Fintype.card f.fixedPoints := by
    by_contra h0
    have h0' : Fintype.card f.fixedPoints = 0 := by omega
    rw [h0', hcardS] at hmod
    have h3 : 3 ∣ Nat.card R := (Nat.modEq_zero_iff_dvd.1 hmod)
    have := Nat.Coprime.eq_one_of_dvd (coprime_card_gLAPPrimeCoreOf I) h3
    omega
  obtain ⟨⟨t, ht⟩⟩ := Fintype.card_pos_iff.1 hne
  have htf : f t = t := ht
  have hbt : b * t.1 * b⁻¹ = t.1 := congrArg Subtype.val htf
  refine ⟨t.1, ?_, hbt, t.2⟩
  have : t.1 = g * (g⁻¹ * t.1) := by group
  rw [this]
  exact I.mul_mem hg (hRI t.2)


theorem cover_ne_bot {X I : Subgroup G} (hI : GLAPComponent 3 X I) {b : G} (hb3 : b ^ 3 = 1)
    (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hc : ∀ ℓ ∈ I, ℓ * b * ℓ⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf 3 I) :
    GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G)) ≠ ⊥ := by
  set Y : Subgroup G := I ⊓ Subgroup.centralizer ({b} : Set G) with hY
  have hYI : Y ≤ I := inf_le_left
  let φ : ↥Y →* barOf 3 I :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)).comp (Subgroup.inclusion hYI)
  have hmemR : ∀ z : ↥I, z ∈ GLAPPrimeCore 3 ↥I ↔ (z : G) ∈ GLAPPrimeCoreOf 3 I := fun z =>
    (Subgroup.mem_map_iff_mem I.subtype_injective).symm
  have hφsurj : Function.Surjective φ := by
    intro w
    induction w using QuotientGroup.induction_on with | _ g => ?_
    obtain ⟨y, hyI', hby, hgy⟩ := exists_fixed_in_coset hb3 hbN hc g.2
    have hyC : y ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * b = (b * y * b⁻¹) * b := by rw [hby]
        _ = b * y := by group
    refine ⟨⟨y, hyI', hyC⟩, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) ⟨y, hyI'⟩ = QuotientGroup.mk' _ g
    refine QuotientGroup.eq.2 ((hmemR _).2 ?_)
    have := (GLAPPrimeCoreOf 3 I).inv_mem hgy
    simpa using this
  have hkerR : ∀ x : ↥Y, x ∈ φ.ker → (x : G) ∈ GLAPPrimeCoreOf 3 I := by
    intro x hx
    have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) (Subgroup.inclusion hYI x) = 1 := hx
    exact (hmemR _).1 ((QuotientGroup.eq_one_iff _).1 this)
  have hker : φ.ker = GLAPPrimeCore 3 ↥Y := by
    apply le_antisymm
    · have hcop : Nat.Coprime 3 (Nat.card φ.ker) := by
        have hle : φ.ker.map Y.subtype ≤ GLAPPrimeCoreOf 3 I := by
          rintro _ ⟨x, hx, rfl⟩
          exact hkerR x hx
        rw [← Subgroup.card_map_of_injective Y.subtype_injective]
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
          (coprime_card_gLAPPrimeCoreOf I)
      exact le_sSup ⟨inferInstance, hcop⟩
    · have hN : ((GLAPPrimeCore 3 ↥Y).map φ).Normal := Subgroup.Normal.map inferInstance φ hφsurj
      have hcop : Nat.Coprime 3 (Nat.card ((GLAPPrimeCore 3 ↥Y).map φ)) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ φ)
          (coprime_card_gLAPPrimeCore_aux 3 ↥Y)
      have h1 : (GLAPPrimeCore 3 ↥Y).map φ ≤ GLAPPrimeCore 3 (barOf 3 I) :=
        le_sSup ⟨hN, hcop⟩
      rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff _).1 h1
  let e : (↥Y ⧸ GLAPPrimeCore 3 ↥Y) ≃* barOf 3 I :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have hq : CFSG.Open.IsQuasisimple (barOf 3 I) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent
      Nat.prime_three hI
  have hq' : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore 3 ↥Y) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_of_mulEquiv' e.symm hq
  have hcomp : IsComponentOf (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) ⊤ :=
    ⟨le_top, IsSubnormal.refl _,
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_of_mulEquiv'
        Subgroup.topEquiv.symm hq'⟩
  obtain ⟨J, hJ, hJbar⟩ := exists_glaPComponent_barX_eq (p := 3) Y hcomp
  have hnt : Nontrivial (↥Y ⧸ GLAPPrimeCore 3 ↥Y) := by
    have := hq'.2.toNontrivial
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton ((↥Y ⧸ GLAPPrimeCore 3 ↥Y) ⧸ Subgroup.center (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) :=
      (QuotientGroup.mk_surjective).subsingleton
    exact not_subsingleton _ this
  intro hbot
  have hJle : J ≤ GLAPLayer 3 Y := le_sSup hJ
  rw [hbot, le_bot_iff] at hJle
  rw [hJle] at hJbar
  have : barX 3 Y ⊥ = ⊥ := by
    unfold barX
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [this] at hJbar
  exact bot_ne_top hJbar


theorem mem_cq_of_upsilon {B : Subgroup G} {x b : G} {I : Subgroup G}
    (hI : IsUpsilonComponent B x I) (hbx : b ∈ Subgroup.centralizer ({x} : Set G))
    (h : ⁅upsilonOf B x, Subgroup.zpowers b⁆ ≤ GLAPPrimeCoreOf 3 (upsilonOf B x)) : b ∈ cq I := by
  refine mem_centralizerQuot_of_comm hI.1 hbx (fun ℓ hℓ => ?_)
  have hΥ : IsSubnormal (upsilonOf B x) (Subgroup.centralizer ({x} : Set G)) :=
    isSubnormal_sSup_of_forall _ (fun K hK => ⟨hK.1.1, hK.1.2.1⟩)
  have hℓΥ : ℓ ∈ upsilonOf B x := (le_sSup hI : I ≤ upsilonOf B x) hℓ
  have hmem : ℓ * b * ℓ⁻¹ * b⁻¹ ∈ ⁅upsilonOf B x, Subgroup.zpowers b⁆ := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator hℓΥ (Subgroup.mem_zpowers b)
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hΥ (h hmem)

end Main

section Exc

theorem exc_false (h210 : Lemma210) (h52 : Lemma52) (h53 : Lemma53) (h54 : Lemma54)
    (h55 : Lemma55) {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hexc : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L))
    (hidx : (Subgroup.normalizer (L : Set G)).relIndex B = 3) : False := by
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hnot : ¬ B ≤ Subgroup.normalizer (L : Set G) :=
    not_le_normalizer_of_relIndex_eq_three hidx
  have hK : bClosure B L ≠ L := bClosure_ne_of_not_le hnot
  obtain ⟨L₂, L₃, hc₂, hc₃, h12, h13, h23, hall⟩ := exists_three_conjugates hBel.1 hidx
  obtain ⟨B', hB'max, hbB', hB'K, hnot', hrank, hA⟩ :=
    h210 G m hS hC.2.1 B hB b hbB hb1 L hL hexc hK L₂ L₃ hc₂ hc₃ h12 h13 h23
  have hB'el : IsElemAbelian 3 B' := hB'max.1.1
  have hcomp₂ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L₂ := by
    obtain ⟨g, hg, rfl⟩ := hc₂
    exact glaPComponent_conj_of_mem hBel hbB hL hg
  have hcomp₃ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L₃ := by
    obtain ⟨g, hg, rfl⟩ := hc₃
    exact glaPComponent_conj_of_mem hBel hbB hL hg
  have hB'card : Nat.card B' = 3 ^ 4 := by
    have := hB'max.1.2.1
    rwa [hC.2.1] at this
  have hrk4 : CFSG.Open.pRank 3 B' = 4 := pRank_eq_of_card Nat.prime_three hB'el hB'card
  have hrefl : IsBConjugate B L L := ⟨1, B.one_mem, (gLBConj_one L).symm⟩
  obtain ⟨e₁, he₁, hn₁⟩ := IsConcreteLE.not_le_iff_exists.1 (hnot' L hrefl)
  obtain ⟨e₂, he₂, hn₂⟩ := IsConcreteLE.not_le_iff_exists.1 (hnot' L₂ hc₂)
  obtain ⟨e₃, he₃, hn₃⟩ := IsConcreteLE.not_le_iff_exists.1 (hnot' L₃ hc₃)
  have h1B' : IsBOneMax 3 B' :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB'max
  have hup_b : ∀ J, ¬ IsUpsilonComponent B' b J := by
    intro J hJU
    have hJ := hJU.1
    have key : ∀ A : Subgroup G, A ≤ B' → A ≤ cq J → 2 < CFSG.Open.pRank 3 A → False :=
      fun A hAB hAcq hr =>
        absurd (h54 G m hS hC B' h1B' b hbB' hb1 J hJU A hAB
          (fun a ha => inducesFieldAut_of_mem_cq (hAcq ha))) (by omega)
    by_cases hJ1 : J = L
    · obtain ⟨A, hAB, hAcq, hAel, hAcard⟩ := exists_rank_three hB'el hbB' hb1 hL hcomp₂ hcomp₃
        h12 h13 h23 he₂ he₃ hn₂ hn₃
      exact key A hAB (hJ1 ▸ hAcq)
        (by rw [pRank_eq_of_card Nat.prime_three hAel hAcard]; norm_num)
    by_cases hJ2 : J = L₂
    · obtain ⟨A, hAB, hAcq, hAel, hAcard⟩ := exists_rank_three hB'el hbB' hb1 hcomp₂ hL hcomp₃
        h12.symm h23 h13 he₁ he₃ hn₁ hn₃
      exact key A hAB (hJ2 ▸ hAcq)
        (by rw [pRank_eq_of_card Nat.prime_three hAel hAcard]; norm_num)
    by_cases hJ3 : J = L₃
    · obtain ⟨A, hAB, hAcq, hAel, hAcard⟩ := exists_rank_three hB'el hbB' hb1 hcomp₃ hL hcomp₂
        h13.symm h23.symm h12 he₁ he₂ hn₁ hn₂
      exact key A hAB (hJ3 ▸ hAcq)
        (by rw [pRank_eq_of_card Nat.prime_three hAel hAcard]; norm_num)
    · refine key B' le_rfl ?_ (by rw [hrk4]; norm_num)
      refine hB'K.trans (bClosure_le fun g hg => ?_)
      rcases hall _ ⟨g, hg, rfl⟩ with h | h | h
      · rw [h]; exact le_cq_of_ne hJ hL hJ1
      · rw [h]; exact le_cq_of_ne hJ hcomp₂ hJ2
      · rw [h]; exact le_cq_of_ne hJ hcomp₃ hJ3
  have hup0 : upsilonOf B' b = ⊥ :=
    le_bot_iff.1 (sSup_le fun K hK => absurd hK (hup_b K))
  have hAel : IsElemAbelian 3 (B' ⊓ (L₂ ⊔ L₃)) := isElemAbelian_of_le hB'el inf_le_left
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hAel
  have hk3 : k = 3 := by
    rw [pRank_eq_of_card Nat.prime_three hAel hk] at hrank
    exact hrank
  have hAek : IsEkIn 3 3 B' (B' ⊓ (L₂ ⊔ L₃)) := ⟨inf_le_left, hAel, by rw [hk, hk3]⟩
  have hfa : ∀ a ∈ B' ⊓ (L₂ ⊔ L₃), InducesFieldAut 3 L a := fun a ha =>
    inducesFieldAut_of_mem_cq
      ((sup_le (le_cq_of_ne hL hcomp₂ h12) (le_cq_of_ne hL hcomp₃ h13)) ha.2)
  obtain ⟨-, hii⟩ := h55 G m hS hC B' hB'el (by omega) b hbB' hb1 _ hAek L hL hfa
    (fun a ha ha1 => hA a ha ha1)
  obtain ⟨y, hyB', hy1, hyup⟩ := h52 G m hS hC B' hB'max
  obtain ⟨I, hI⟩ : ∃ I, IsUpsilonComponent B' y I := by
    by_contra hno
    push Not at hno
    exact hyup (le_bot_iff.1 (sSup_le fun K hK => absurd hK (hno K)))
  have hby : b ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hB'el.1.is_comm.comm ⟨b, hbB'⟩ ⟨y, hyB'⟩
    simpa using congrArg Subtype.val this
  have hbcq : b ∈ cq I := mem_cq_of_upsilon hI hby (hii y hyB' hy1)
  have h53' := h53 G m hS hC B' h1B' y hyB' hy1 I hI b hbB' hb1
    (inducesFieldAut_of_mem_cq hbcq)
  have hle : GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G)) ≤ ⊥ := by
    calc GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G))
        ≤ ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({b} : Set G)),
            GLBConj g (GLAPLayer 3 (I ⊓ Subgroup.centralizer ({b} : Set G))) :=
          le_iSup₂_of_le (1 : G) (one_mem _) (by rw [gLBConj_one])
      _ ≤ upsilonOf B' b := h53'
      _ = ⊥ := hup0
  exact cover_ne_bot hI.1 (hB'el.2 b hbB') hbcq.1 (fun ℓ hℓ => hbcq.2.2 ℓ hℓ)
    (le_bot_iff.1 hle)

end Exc

section TypeSep

open Matrix

section Cards

theorem natCard_statedSL_three {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 3 K) = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
  (CFSG.Open.StatedAPI.card_statedSL_three K).trans (mul_assoc _ _ _).symm

theorem natCard_statedSU_three {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

theorem natCard_statedSL_two {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem natCard_hatSix {X : Type*} [Group X] (h : IsHatSix X) : Nat.card X = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem natCard_hatSeven {X : Type*} [Group X] (h : IsHatSeven X) : Nat.card X = 7560 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem natCard_m22 : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  omega

theorem natCard_hatM22 {X : Type*} [Group X] (h : IsHatMTwentyTwo X) : Nat.card X = 1330560 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv]
  have h22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 :=
    natCard_m22
  rw [h22]

end Cards

section Arith

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem arith_small : ∀ q < 11, 2 ≤ q → ∀ c < 100, c ∣ q ^ 2 - 1 → ∀ j < 13,
    ∀ t ∈ [1080, 7560, 1330560],
      3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) ≠ c * t ∧
      3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ≠ c * t := by
  decide +kernel

theorem arith_hat {q c j t : ℕ} (hq : 2 ≤ q) (hc : c ∣ q ^ 2 - 1) (hj : 3 ^ j ≤ t)
    (ht : t = 1080 ∨ t = 7560 ∨ t = 1330560) :
    3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) ≠ c * t ∧
      3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ≠ c * t := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hcle : c ≤ q ^ 2 - 1 := Nat.le_of_dvd (by omega) hc
  have htle : t ≤ 1330560 := by omega
  have htpos : 0 < t := by omega
  by_cases hq11 : q < 11
  · have hj13 : j < 13 := by
      by_contra h
      push Not at h
      have : 3 ^ 13 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hcl : c < 100 := by
      have : q ^ 2 ≤ 100 := by nlinarith
      omega
    have := arith_small q hq11 hq c hcl hc j hj13 t (by rcases ht with h | h | h <;> simp [h])
    exact this
  · push Not at hq11
    have h3 : 1331 ≤ q ^ 3 := by
      calc 1331 = 11 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq11 3
    have hbig : 1330560 < q ^ 3 * (q ^ 3 - 1) := by
      have : 1331 * 1330 ≤ q ^ 3 * (q ^ 3 - 1) := Nat.mul_le_mul h3 (by omega)
      omega
    have hge : 0 < 3 ^ j := by positivity
    have key : (q ^ 2 - 1) * 1330560 < (q ^ 2 - 1) * (q ^ 3 * (q ^ 3 - 1)) :=
      Nat.mul_lt_mul_of_pos_left hbig (by omega)
    have e1 : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = (q ^ 2 - 1) * (q ^ 3 * (q ^ 3 - 1)) := by ring
    have e2 : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≥ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul le_rfl (by omega)
    have hct : c * t ≤ (q ^ 2 - 1) * 1330560 := Nat.mul_le_mul hcle htle
    constructor
    · intro h
      have : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≤ 3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.le_mul_of_pos_left _ hge
      omega
    · intro h
      have : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≤ 3 ^ j * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) :=
        Nat.le_mul_of_pos_left _ hge
      omega

theorem pow_two_mul_odd_inj {a b u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  wlog hab : a ≤ b generalizing a b u v
  · exact (this hv hu h.symm (by omega)).symm
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hab hne
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h2 : 2 ^ a * u = 2 ^ a * (2 ^ (k + 1) * v) := by
    rw [h]; ring
  have h3 : u = 2 ^ (k + 1) * v := Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have : 2 ∣ u := by
    rw [h3]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  omega

theorem odd_pow_two_mul_sub {Q : ℕ} (hQ : Q % 2 = 0) (hQ2 : 2 ≤ Q) (k : ℕ) (hk : 1 ≤ k) :
    (Q ^ k - 1) % 2 = 1 ∧ (Q ^ k + 1) % 2 = 1 := by
  have h1 : Q ^ k % 2 = 0 := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ, Nat.mul_mod, hQ]; simp
  have h2 : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
  omega

theorem arith_two_pow_core {c Q n m : ℕ} (hc : c % 2 = 1) (hQ : Q % 2 = 0) (hQ2 : 2 ≤ Q)
    (f : ℕ) (hQf : Q = 2 ^ f) (hn : 1 ≤ n) (hm : m = Q ^ 3 - 1 ∨ m = Q ^ 3 + 1) :
    c * (2 ^ n * (4 ^ n - 1)) ≠ Q ^ 3 * (Q ^ 2 - 1) * m := by
  intro h
  have hf : 1 ≤ f := by
    by_contra h0
    have : f = 0 := by omega
    subst this
    simp at hQf
    omega
  have hmodd : m % 2 = 1 := by
    rcases hm with rfl | rfl
    · exact (odd_pow_two_mul_sub hQ hQ2 3 (by norm_num)).1
    · exact (odd_pow_two_mul_sub hQ hQ2 3 (by norm_num)).2
  have h4 : (4 ^ n - 1) % 2 = 1 := (odd_pow_two_mul_sub (Q := 4) (by norm_num) (by norm_num) n hn).1
  have hQ2' : ((Q ^ 2 - 1)) % 2 = 1 := (odd_pow_two_mul_sub hQ hQ2 2 (by norm_num)).1
  have hu : (c * (4 ^ n - 1)) % 2 = 1 := by
    rw [Nat.mul_mod, hc, h4]
  have hv : ((Q ^ 2 - 1) * m) % 2 = 1 := by
    rw [Nat.mul_mod, hQ2', hmodd]
  have hQ3 : Q ^ 3 = 2 ^ (3 * f) := by
    rw [hQf, ← pow_mul, mul_comm]
  have h' : 2 ^ n * (c * (4 ^ n - 1)) = 2 ^ (3 * f) * ((Q ^ 2 - 1) * m) := by
    rw [← hQ3]
    calc 2 ^ n * (c * (4 ^ n - 1)) = c * (2 ^ n * (4 ^ n - 1)) := by ring
      _ = _ := by rw [h]; ring
  have hn3 : n = 3 * f := pow_two_mul_odd_inj hu hv h'
  subst hn3
  have h4n : 4 ^ (3 * f) = Q ^ 6 := by
    rw [hQf, ← pow_mul]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1; ring
  rw [h4n, ← hQ3] at h
  have hQpos : 0 < Q ^ 3 := by positivity
  have hc1 : 1 ≤ c := by omega
  have h1 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hQz : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
  have hz : (c : ℤ) * (Q ^ 3 * ((Q : ℤ) ^ 6 - 1)) = Q ^ 3 * ((Q : ℤ) ^ 2 - 1) * m := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at this
    simpa using this
  have hmz : (m : ℤ) = Q ^ 3 - 1 ∨ (m : ℤ) = Q ^ 3 + 1 := by
    rcases hm with rfl | rfl
    · left; push_cast [Nat.cast_sub h3]; ring
    · right; push_cast; ring
  have hc1z : (1 : ℤ) ≤ c := by exact_mod_cast hc1
  have hQ3pos : (0 : ℤ) < (Q : ℤ) ^ 3 := by positivity
  have hQ2pos : (0 : ℤ) < (Q : ℤ) ^ 2 - 1 := by nlinarith
  have hc' : (c : ℤ) * (Q ^ 4 + Q ^ 2 + 1) = m := by
    have h5 : (Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1) * (c * (Q ^ 4 + Q ^ 2 + 1) - m) = 0 := by
      linear_combination hz
    have h6 : (Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h5).resolve_left h6
    linarith
  have hpos : (0 : ℤ) < (Q : ℤ) ^ 4 + Q ^ 2 + 1 := by positivity
  have hge : (Q : ℤ) ^ 4 + Q ^ 2 + 1 ≤ m := by
    rw [← hc']
    nlinarith
  have hle : (m : ℤ) ≤ Q ^ 3 + 1 := by rcases hmz with h7 | h7 <;> linarith
  have h2Q : 2 * (Q : ℤ) ^ 3 ≤ (Q : ℤ) ^ 4 := by
    have := mul_le_mul_of_nonneg_right hQz hQ3pos.le
    nlinarith
  have hQ2' : (0 : ℤ) < (Q : ℤ) ^ 2 := by positivity
  nlinarith

theorem arith_two_pow {c f n : ℕ} (hc : c % 2 = 1) (hf : 1 ≤ f) (hn : 1 ≤ n) :
    c * (2 ^ n * (4 ^ n - 1)) ≠ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ∧
      c * (2 ^ n * (4 ^ n - 1)) ≠ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
  have hQ : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQe : (2 ^ f) % 2 = 0 := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [pow_succ, Nat.mul_mod]; simp
  exact ⟨arith_two_pow_core hc hQe hQ f rfl hn (Or.inl rfl),
    arith_two_pow_core hc hQe hQ f rfl hn (Or.inr rfl)⟩

end Arith



@[expose] def rotM (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]

theorem det_rotM (K : Type) [Field K] : (rotM K).det = 1 := by
  simp [rotM, Matrix.det_fin_three]

@[expose] noncomputable def rotGL (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM K) (by rw [det_rotM]; exact one_ne_zero)

theorem rotGL_val (K : Type) [Field K] : ((rotGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rotM K := rfl

theorem rotM_sq (K : Type) [Field K] : rotM K * rotM K = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  simp [rotM]

theorem rotGL_pow_four (K : Type) [Field K] : rotGL K ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, rotGL_val, show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, rotM_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


theorem rotGL_sq_val (K : Type) [Field K] :
    (((rotGL K ^ 2 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Units.val_pow_eq_pow_val, rotGL_val, pow_two, rotM_sq]

theorem rotGL_sq_not_scalar (K : Type) [Field K] (h : (-1 : K) ≠ 1) :
    rotGL K ^ 2 ∉ CFSG.Open.StatedScalars (Fin 3) K := by
  rintro ⟨u, hu⟩
  have hv := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K))) hu
  simp only [rotGL_sq_val] at hv
  have e00 := congrFun (congrFun hv 0) 0
  have e22 := congrFun (congrFun hv 2) 2
  simp at e00 e22
  exact h (by simpa using congrArg Units.val (e00.symm.trans e22))

theorem rotGL_mem_statedSL (K : Type) [Field K] : rotGL K ∈ CFSG.Open.StatedSL 3 K :=
  Subgroup.subset_closure (by simpa [rotGL_val] using det_rotM K)

theorem rotGL_mem_statedSU (K : Type) [Field K] (q : ℕ) (hq : Odd q) :
    rotGL K ∈ CFSG.Open.StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨by simpa [rotGL_val] using det_rotM K, ?_⟩
  rw [rotGL_val]
  have h0 : (0 : K) ^ q = 0 := zero_pow (by rintro rfl; simp at hq)
  have h1 : (-1 : K) ^ q = -1 := hq.neg_one_pow
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]


theorem exists_orderOf_four_proj (K : Type) [Field K] (h : (-1 : K) ≠ 1)
    {H : Subgroup (GL (Fin 3) K)} (hH : rotGL K ∈ H) :
    ∃ y : CFSG.Open.StatedProj H, orderOf y = 4 := by
  refine ⟨QuotientGroup.mk ⟨rotGL K, hH⟩, ?_⟩
  have h4 : (QuotientGroup.mk (⟨rotGL K, hH⟩ : ↥H) : CFSG.Open.StatedProj H) ^ (2 ^ (1 + 1)) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show rotGL K ^ (2 ^ (1 + 1)) ∈ CFSG.Open.StatedScalars (Fin 3) K
    rw [show 2 ^ (1 + 1) = 4 by norm_num, rotGL_pow_four]
    exact one_mem _
  have h2 : ¬ (QuotientGroup.mk (⟨rotGL K, hH⟩ : ↥H) : CFSG.Open.StatedProj H) ^ (2 ^ 1) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    intro hmem
    exact rotGL_sq_not_scalar K h hmem
  exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4

theorem exists_orderOf_four (K : Type) [Field K] (h : (-1 : K) ≠ 1)
    {H : Subgroup (GL (Fin 3) K)} (hH : rotGL K ∈ H) :
    ∃ x : ↥H, orderOf x = 4 := by
  refine ⟨⟨rotGL K, hH⟩, ?_⟩
  have h4 : (⟨rotGL K, hH⟩ : ↥H) ^ (2 ^ (1 + 1)) = 1 := by
    apply Subtype.ext
    show rotGL K ^ (2 ^ (1 + 1)) = 1
    rw [show 2 ^ (1 + 1) = 4 by norm_num, rotGL_pow_four]
  have h2 : ¬ (⟨rotGL K, hH⟩ : ↥H) ^ (2 ^ 1) = 1 := by
    intro hh
    have := congrArg Subtype.val hh
    exact rotGL_sq_not_scalar K h (by
      have h' : rotGL K ^ 2 = 1 := by simpa using this
      rw [h']; exact one_mem _)
  exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4



theorem det_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (h : A ∈ StatedSL n K) : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

theorem mat_pow_four {F : Type} [Field F] [CharP F 2] (a b c d : F) (hdet : a * d - b * c = 1)
    (h : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have e : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) ^ 4 = !![a, b; c, d] ^ 2 * !![a, b; c, d] ^ 2 := by
    rw [← pow_add]
  rw [e] at h
  simp only [pow_two, Matrix.mul_fin_two] at h ⊢
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  simp at e00 e11
  have ht4 : (a + d) ^ 4 = 0 := by
    linear_combination e00 + e11 + (4 * (a + d) ^ 2 - 2 * ((a * d - b * c) + 1)) * hdet + (2 * (a + d) ^ 2) * h2
  have ht : a + d = 0 := pow_eq_zero_iff (by norm_num) |>.1 ht4
  have h00 : a * a + b * c = 1 := by linear_combination (-1) * hdet + a * ht - h2
  have h11 : c * b + d * d = 1 := by linear_combination (-1) * hdet + d * ht - h2
  have h01 : a * b + b * d = 0 := by linear_combination b * ht
  have h10 : c * a + d * c = 0 := by linear_combination c * ht
  rw [h00, h01, h10, h11]
  exact (Matrix.one_fin_two).symm

theorem statedSL_two_orderOf_ne_four {F : Type} [Field F] [CharP F 2] (x : ↥(StatedSL 2 F)) :
    orderOf x ≠ 4 := by
  intro h
  have h4 : x ^ 4 = 1 := h ▸ pow_orderOf_eq_one x
  have hdet := det_of_mem_statedSL x.2
  set M : Matrix (Fin 2) (Fin 2) F := ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have hM4 : M ^ 4 = 1 := by
    have := congrArg (fun y : ↥(StatedSL 2 F) => ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h4
    simpa [hM, Units.val_pow_eq_pow_val] using this
  have heta : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  rw [heta] at hM4
  have hsq := mat_pow_four _ _ _ _ hdet' hM4
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← heta] at hsq
    simpa [hM, Units.val_pow_eq_pow_val] using hsq
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [h] at this
  omega



section Fields

theorem card_dichotomy (K : Type) [Field K] [Finite K] :
    (Nat.card K % 2 = 1 ∧ (-1 : K) ≠ 1) ∨ ∃ k, 1 ≤ k ∧ Nat.card K = 2 ^ k := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card] at hn
  by_cases h2 : ringChar K = 2
  · right
    exact ⟨n, n.pos, by rw [hn, h2]⟩
  · left
    have hodd : Odd (ringChar K) := hp.odd_of_ne_two h2
    refine ⟨?_, ?_⟩
    · rw [hn]
      exact Nat.odd_iff.1 (hodd.pow)
    · intro h
      have h2K : (2 : K) = 0 := by
        calc (2 : K) = 1 + 1 := one_add_one_eq_two.symm
          _ = -1 + 1 := by rw [h]
          _ = 0 := neg_add_cancel 1
      have hd : ringChar K ∣ 2 := by
        have := (CharP.cast_eq_zero_iff K (ringChar K) 2).1 (by exact_mod_cast h2K)
        exact this
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (h : Nat.card F = 2 ^ n) : CharP F 2 := by
  have := Fintype.ofFinite F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, h] at hm
  have hd : ringChar F ∣ 2 ^ n := by
    rw [hm]
    exact dvd_pow_self _ (by have := m.pos; omega)
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  exact (ringChar.eq_iff).1 this

theorem exists_two_pow_of_sq {q k : ℕ} (hk : q ^ 2 = 2 ^ k) (hq : 2 ≤ q) :
    ∃ f, 1 ≤ f ∧ q = 2 ^ f := by
  have hd : q ∣ 2 ^ k := ⟨q, by rw [← hk]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  refine ⟨f, ?_, hf⟩
  by_contra h0
  have : f = 0 := by omega
  subst this
  simp at hf
  omega

end Fields


section Proj

theorem scalar_injective (K : Type) [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K)) 0 0) h
  simp [Matrix.GeneralLinearGroup.coe_scalar] at this
  exact Units.ext this

theorem card_scalars_dvd {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 3) K)) :
    Nat.card ↥((StatedScalars (Fin 3) K).subgroupOf H) ∣ Nat.card K - 1 := by
  let f : ↥((StatedScalars (Fin 3) K).subgroupOf H) →* ↥(StatedScalars (Fin 3) K) :=
    { toFun := fun g => ⟨((g : ↥H) : GL (Fin 3) K), g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun g g' h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have h1 := Subgroup.card_dvd_of_injective f hf
  have h2 : Nat.card ↥(StatedScalars (Fin 3) K) = Nat.card Kˣ :=
    (Nat.card_congr (MonoidHom.ofInjective (scalar_injective K)).toEquiv).symm
  rw [h2, CFSG.SectionRank.OddCover.card_units_eq] at h1
  exact h1

theorem proj_data {K : Type} [Field K] [Finite K] (H : Subgroup (GL (Fin 3) K)) {Y : Type*}
    [Group Y] (e : Y ≃* StatedProj H) :
    ∃ c, c ∣ Nat.card K - 1 ∧ c * Nat.card Y = Nat.card ↥H := by
  refine ⟨Nat.card ↥((StatedScalars (Fin 3) K).subgroupOf H), card_scalars_dvd H, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((StatedScalars (Fin 3) K).subgroupOf H),
    Nat.card_congr e.toEquiv, mul_comm]

end Proj

section TS1

theorem sq_pos_aux {q K : ℕ} (hK : K = q ^ 2) (h2 : 2 ≤ K) : 2 ≤ q := by
  by_contra h
  have : q ≤ 1 := by omega
  have : q ^ 2 ≤ 1 := by nlinarith
  omega

theorem sl3_su3_data {X : Type*} [Group X] (h : IsSLThree X ∨ IsSUThree X) :
    ∃ q : ℕ, 2 ≤ q ∧
      (Nat.card X = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∨
          Nat.card X = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ∧
        ((∃ f, 1 ≤ f ∧ q = 2 ^ f) ∨ ∃ x : X, orderOf x = 4) := by
  rcases h with ⟨K, _, _, ⟨e⟩⟩ | ⟨K, _, _, q, hK, ⟨e⟩⟩
  · refine ⟨Nat.card K, Finite.one_lt_card, Or.inl (by rw [Nat.card_congr e.toEquiv,
      natCard_statedSL_three]), ?_⟩
    rcases card_dichotomy K with ⟨-, hm1⟩ | ⟨k, hk, hK⟩
    · right
      obtain ⟨x, hx⟩ := exists_orderOf_four K hm1 (rotGL_mem_statedSL K)
      exact ⟨e.symm x, by rw [MulEquiv.orderOf_eq]; exact hx⟩
    · exact Or.inl ⟨k, hk, hK⟩
  · have hq2 : 2 ≤ q := sq_pos_aux hK Finite.one_lt_card
    refine ⟨q, hq2, Or.inr (by rw [Nat.card_congr e.toEquiv, natCard_statedSU_three hK]), ?_⟩
    rcases card_dichotomy K with ⟨hodd, hm1⟩ | ⟨k, hk, hk2⟩
    · right
      have hqodd : Odd q := by
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        have h2 : Even (q ^ 2) := Nat.even_pow.2 ⟨hne, by norm_num⟩
        rw [← hK] at h2
        have := Nat.even_iff.1 h2
        omega
      obtain ⟨x, hx⟩ := exists_orderOf_four K hm1 (rotGL_mem_statedSU K q hqodd)
      exact ⟨e.symm x, by rw [MulEquiv.orderOf_eq]; exact hx⟩
    · left
      exact exists_two_pow_of_sq (by rw [← hK]; exact hk2) hq2

theorem sl2_data {X : Type*} [Group X] (h : IsLTwoOddPow X) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card X = 2 ^ n * (4 ^ n - 1) ∧ ∀ x : X, orderOf x ≠ 4 := by
  obtain ⟨F, _, _, n, -, hn1, hF, ⟨e⟩⟩ := h
  have : CharP F 2 := charP_two_of_card hF
  refine ⟨n, by omega, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, natCard_statedSL_two, hF]
    congr 2
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  · intro x hx
    exact statedSL_two_orderOf_ne_four (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)

theorem ts1 {X : Type*} [Group X] (h : IsSLThree X ∨ IsSUThree X) :
    ¬ (IsLTwoOddPow X ∨ IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X) := by
  obtain ⟨q, hq, hord, hcase⟩ := sl3_su3_data h
  intro hbad
  have hhat : ∀ t, Nat.card X = t → (t = 1080 ∨ t = 7560 ∨ t = 1330560) → False := by
    intro t ht htt
    have := arith_hat (q := q) (c := 1) (j := 0) hq (one_dvd _) (by
      simp; omega) htt
    rcases hord with h1 | h1
    · exact this.1 (by rw [← h1, ht]; simp)
    · exact this.2 (by rw [← h1, ht]; simp)
  rcases hbad with hL | h6 | h7 | h22
  · obtain ⟨n, hn, hcard, hno4⟩ := sl2_data hL
    rcases hcase with ⟨f, hf, rfl⟩ | ⟨x, hx⟩
    · rcases hord with h1 | h1
      · exact (arith_two_pow (c := 1) (f := f) (n := n) (by norm_num) hf hn).1
          (by rw [← h1, hcard]; simp)
      · exact (arith_two_pow (c := 1) (f := f) (n := n) (by norm_num) hf hn).2
          (by rw [← h1, hcard]; simp)
    · exact hno4 x hx
  · exact hhat _ (natCard_hatSix h6) (by simp)
  · exact hhat _ (natCard_hatSeven h7) (by simp)
  · exact hhat _ (natCard_hatM22 h22) (by simp)

end TS1

section TS2

theorem sub_one_dvd_sq_sub_one {q : ℕ} (hq : 2 ≤ q) : q - 1 ∣ q ^ 2 - 1 := by
  refine ⟨q + 1, ?_⟩
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q := by omega
  zify [h1, h2]
  ring

theorem proj_ext_data {Y : Type*} [Group Y] (h : IsExtremalType Y) :
    ∃ q c : ℕ, 2 ≤ q ∧ c ∣ q ^ 2 - 1 ∧
      (c * Nat.card Y = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∨
        c * Nat.card Y = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ∧
      (((∃ f, 1 ≤ f ∧ q = 2 ^ f) ∧ c % 2 = 1) ∨ ∃ y : Y, orderOf y = 4) := by
  rcases h with ⟨K, _, _, -, ⟨e⟩⟩ | ⟨K, _, _, q, hK, -, -, ⟨e⟩⟩
  · obtain ⟨c, hc, hcard⟩ := proj_data (StatedSL 3 K) e
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    refine ⟨Nat.card K, c, hq, hc.trans (sub_one_dvd_sq_sub_one hq),
      Or.inl (by rw [hcard, natCard_statedSL_three]), ?_⟩
    rcases card_dichotomy K with ⟨-, hm1⟩ | ⟨k, hk, hK⟩
    · right
      obtain ⟨y, hy⟩ := exists_orderOf_four_proj K hm1 (rotGL_mem_statedSL K)
      exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy⟩
    · left
      refine ⟨⟨k, hk, hK⟩, ?_⟩
      have hodd : (2 ^ k - 1) % 2 = 1 := (odd_pow_two_mul_sub (Q := 2) (by norm_num) (by norm_num) k hk).1
      rw [hK] at hc
      exact Nat.odd_iff.1 (Odd.of_dvd_nat (Nat.odd_iff.2 hodd) hc)
  · obtain ⟨c, hc, hcard⟩ := proj_data (StatedSU 3 q K) e
    have hq2 : 2 ≤ q := sq_pos_aux hK Finite.one_lt_card
    rw [hK] at hc
    refine ⟨q, c, hq2, hc, Or.inr (by rw [hcard, natCard_statedSU_three hK]), ?_⟩
    rcases card_dichotomy K with ⟨hodd, hm1⟩ | ⟨k, hk, hk2⟩
    · right
      have hqodd : Odd q := by
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        have h2 : Even (q ^ 2) := Nat.even_pow.2 ⟨hne, by norm_num⟩
        rw [← hK] at h2
        have := Nat.even_iff.1 h2
        omega
      obtain ⟨y, hy⟩ := exists_orderOf_four_proj K hm1 (rotGL_mem_statedSU K q hqodd)
      exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy⟩
    · left
      obtain ⟨f, hf, hqf⟩ := exists_two_pow_of_sq (by rw [← hK]; exact hk2) hq2
      refine ⟨⟨f, hf, hqf⟩, ?_⟩
      have hodd : (q ^ 2 - 1) % 2 = 1 := by
        rw [hqf]
        have hQe : (2 ^ f) % 2 = 0 := by
          obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le' hf
          rw [pow_succ, Nat.mul_mod]; simp
        exact (odd_pow_two_mul_sub hQe (by simpa [hqf] using hq2) 2 (by norm_num)).1
      exact Nat.odd_iff.1 (Odd.of_dvd_nat (Nat.odd_iff.2 hodd) hc)

theorem sl2_isSimple {X : Type*} [Group X] (hL : IsLTwoOddPow X) : IsSimpleGroup X := by
  obtain ⟨F, _, _, n', hodd, hn1, hF, ⟨e⟩⟩ := hL
  have : CharP F 2 := charP_two_of_card hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo (F := F) h4
  exact @MulEquiv.isSimpleGroup X _ _ _ this e

theorem ts2a {X : Type*} [Group X] [Finite X]
    (h : IsLTwoOddPow X ∨ IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X) :
    ¬ IsExtremalType (X ⧸ CFSG.pCore 3 X) := by
  intro hext
  obtain ⟨q, c, hq, hc, hord, hcase⟩ := proj_ext_data hext
  have hhat : ∀ t, Nat.card X = t → (t = 1080 ∨ t = 7560 ∨ t = 1330560) → False := by
    intro t ht htt
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 3) (G := X)).exists_card_eq
    have hmul : t = Nat.card (X ⧸ CFSG.pCore 3 X) * 3 ^ j := by
      rw [← ht, Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 3 X), hj]
    have htpos : 0 < t := by omega
    have hjt : 3 ^ j ≤ t := by
      rw [hmul]
      exact Nat.le_mul_of_pos_left _ (Nat.card_pos)
    have key := arith_hat (q := q) (c := c) (j := j) hq hc hjt htt
    rcases hord with h1 | h1
    · apply key.1
      rw [← h1, hmul]; ring
    · apply key.2
      rw [← h1, hmul]; ring
  rcases h with hL | h6 | h7 | h22
  · obtain ⟨n, hn, hcard, hno4⟩ := sl2_data hL
    have hsimple : IsSimpleGroup X := sl2_isSimple hL
    have hbot : CFSG.pCore 3 X = ⊥ := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hn' : (CFSG.pCore 3 X).Normal := CFSG.pCore_normal
      rcases hsimple.eq_bot_or_eq_top_of_normal (CFSG.pCore 3 X) with h0 | h0
      · exact h0
      · exfalso
        have hp : IsPGroup 3 ↥(CFSG.pCore 3 X) := CFSG.pCore_isPGroup
        obtain ⟨m, hm⟩ := hp.exists_card_eq
        rw [h0, Subgroup.card_top, hcard] at hm
        have h2 : (2 ^ n * (4 ^ n - 1)) % 2 = 0 := by
          obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [pow_succ, Nat.mul_mod]; simp
        have h3 : (3 ^ m) % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
        omega
    let e' : X ⧸ CFSG.pCore 3 X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    have hcardY : Nat.card (X ⧸ CFSG.pCore 3 X) = 2 ^ n * (4 ^ n - 1) := by
      rw [Nat.card_congr e'.toEquiv, hcard]
    rcases hcase with ⟨⟨f, hf, rfl⟩, hcodd⟩ | ⟨y, hy⟩
    · rcases hord with h1 | h1
      · exact (arith_two_pow (c := c) (f := f) (n := n) hcodd hf hn).1 (by rw [← h1, hcardY])
      · exact (arith_two_pow (c := c) (f := f) (n := n) hcodd hf hn).2 (by rw [← h1, hcardY])
    · exact hno4 (e' y) (by rw [MulEquiv.orderOf_eq]; exact hy)
  · exact hhat _ (natCard_hatSix h6) (by simp)
  · exact hhat _ (natCard_hatSeven h7) (by simp)
  · exact hhat _ (natCard_hatM22 h22) (by simp)

@[expose] def InputONNotIso : Prop :=
  (¬ Nonempty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ≃*
      alternatingGroup (Fin 6))) ∧
  (¬ Nonempty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ≃*
      alternatingGroup (Fin 7))) ∧
  (¬ Nonempty ((TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group))

theorem ts2b (hON : InputONNotIso) {X : Type*} [Group X]
    (h : IsLTwoOddPow X ∨ IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X) : ¬ IsHatON X := by
  rintro ⟨-, hc, ⟨eo⟩⟩
  rcases h with hL | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩
  · obtain ⟨n, hn, hcard, -⟩ := sl2_data hL
    have hsimple := sl2_isSimple hL
    have hn' : (Subgroup.center X).Normal := inferInstance
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
    · rw [h0, Subgroup.card_bot] at hc
      omega
    · rw [h0, Subgroup.card_top, hcard] at hc
      have h2 : (2 ^ n * (4 ^ n - 1)) % 2 = 0 := by
        obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le' hn
        rw [pow_succ, Nat.mul_mod]; simp
      omega
  · exact hON.1 ⟨eo.symm.trans e⟩
  · exact hON.2.1 ⟨eo.symm.trans e⟩
  · exact hON.2.2 ⟨eo.symm.trans e⟩

end TS2


end TypeSep

section Types

@[expose] def InputUpsilonType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L →
        IsExtremalType (↥L ⧸ oPrimeP 3 ↥L) ∨ IsHatON (barOf 3 L)

theorem ts2 (hON : InputONNotIso) {X : Type*} [Group X] [Finite X]
    (h : IsLTwoOddPow X ∨ IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X) :
    ¬ IsExtremalType (X ⧸ CFSG.pCore 3 X) ∧ ¬ IsHatON X :=
  ⟨ts2a h, ts2b hON h⟩

universe u v

theorem isExtremalType_of_mulEquiv {Y : Type u} {Y' : Type v} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsExtremalType Y) : IsExtremalType Y' := by
  rcases h with ⟨K, hK, hf, h3, ⟨f⟩⟩ | ⟨K, hK, hf, q, h1, h2, h3, ⟨f⟩⟩
  · exact Or.inl ⟨K, hK, hf, h3, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨K, hK, hf, q, h1, h2, h3, ⟨e.symm.trans f⟩⟩

theorem isExtremalType_congr {Y : Type u} {Y' : Type v} [Group Y] [Group Y'] (e : Y ≃* Y') :
    IsExtremalType Y ↔ IsExtremalType Y' :=
  ⟨isExtremalType_of_mulEquiv e, isExtremalType_of_mulEquiv e.symm⟩

theorem isExtremalType_barOf_iff {G : Type*} [Group G] (L : Subgroup G) :
    IsExtremalType (↥L ⧸ oPrimeP 3 ↥L) ↔
      IsExtremalType (barOf 3 L ⧸ CFSG.pCore 3 (barOf 3 L)) := by
  have hle : GLAPPrimeCore 3 ↥L ≤ oPrimeP 3 ↥L := fun x hx => by
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) x ∈ CFSG.pCore 3 _
    rw [(QuotientGroup.eq_one_iff x).2 hx |> fun h => show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) x = 1 from h]
    exact one_mem _
  have hN : (GLAPPrimeCore 3 ↥L).Normal := inferInstance
  have hM : (oPrimeP 3 ↥L).Normal := inferInstance
  let e := QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore 3 ↥L) (oPrimeP 3 ↥L) hle
  have hmap : (oPrimeP 3 ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) =
      CFSG.pCore 3 (barOf 3 L) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact (isExtremalType_congr e.symm).trans (isExtremalType_congr (QuotientGroup.quotientMulEquivOfEq hmap))

end Types

section Final

variable {G : Type} [Group G] [Finite G]

theorem not_normal_cases (h210 : Lemma210) (h52 : Lemma52) (h53 : Lemma53) (h54 : Lemma54)
    (h55 : Lemma55) (h112 : Input11_2Full) {m : ℕ} (hS : GLStanding G m 3)
    (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hnot : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    IsLTwoOddPow (barOf 3 L) ∨ IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨
      IsHatMTwentyTwo (barOf 3 L) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem hBel hbB
  have hrk : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({b} : Set G)) ≤ CFSG.Open.pRank 3 B :=
    (glaTwoLocalRank_subgroup_le hp _).trans (hS.rank_eq.le.trans (hS.le_pRank' hB1))
  obtain ⟨-, hidx, -, -, hcases⟩ := h112 G m 3 hS _ B L hBel hBC hrk hL hnot
  rcases hcases with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (exc_false h210 h52 h53 h54 h55 hS hC hB hbB hb1 hL (Or.inl h) hidx).elim
  · exact (exc_false h210 h52 h53 h54 h55 hS hC hB hbB hb1 hL (Or.inr h) hidx).elim
  · exact (exc_false h210 h52 h53 h54 h55 hS hC hB hbB hb1 hL (Or.inr h.isSUThreeExc) hidx).elim

end Final

end Gen

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem lemma56_of_lemmas (h210 : Lemma210) (h52 : Lemma52) (h53 : Lemma53) (h54 : Lemma54)
    (h55 : Lemma55) (h112 : Input11_2Full) (hU : Lemma56Ns.InputUpsilonType)
    (hON : Lemma56Ns.InputONNotIso) : Lemma56 := by
  intro G _ _ m hS hC B hB b hb hb1
  refine ⟨fun L hL htype => ?_, fun L hLU => ?_⟩
  · by_contra hnot
    exact Lemma56Ns.ts1 htype
      (Lemma56Ns.not_normal_cases h210 h52 h53 h54 h55 h112 hS hC hB hb hb1 hL hnot)
  · by_contra hnot
    have hfour := Lemma56Ns.not_normal_cases h210 h52 h53 h54 h55 h112 hS hC hB hb hb1 hLU.1 hnot
    have h2 := Lemma56Ns.ts2 hON hfour
    rcases hU G m hS hC B hB b hb hb1 L hLU with h | h
    · exact h2.1 ((Lemma56Ns.isExtremalType_barOf_iff L).1 h)
    · exact h2.2 h

end CFSG.HardMathSupport.Solomon.LocalBalance
