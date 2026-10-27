module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FStmts
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniq
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DClaim
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem ia_comp_up {p : ℕ} (hp : p.Prime) {H M K : Subgroup G} (hK : GLAPComponent p H K)
    (hHM : H ≤ M) (hsnM : IsSubnormal K M) : GLAPComponent p M K := by
  obtain ⟨hKH, hsn, hcomp, hmin⟩ := hK
  have hKX : K ≤ M := hKH.trans hHM
  refine ⟨hKX, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p M K) ≃* ↥(barX p H K) :=
      (quotEquivBarX hp hKX hsnM).symm.trans (quotEquivBarX hp hKH hsn)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
  · intro J hJ hJsn heq
    have hJK : J ≤ K := hJ.le
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJK.trans hKH) hHM
    have hcoreK : K ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (barX_mono p hJK) ?_
    refine barX_le_of_forall (hJK.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hKX hk)
    exact ⟨j, hj, hcoreK ⟨K.mul_mem (K.inv_mem (hJK hj)) hk, hjk⟩⟩

omit [Finite G] in
theorem ia_exists_mul_of_mem_sup {J U : Subgroup G} (hJU : J ≤ Subgroup.normalizer (U : Set G))
    {k : G} (hk : k ∈ J ⊔ U) : ∃ j ∈ J, ∃ u ∈ U, k = j * u := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right J U hJU
  have hk' : k ∈ (J : Set G) * (U : Set G) := by rw [← h]; exact hk
  obtain ⟨j, hj, u, hu, rfl⟩ := hk'
  exact ⟨j, hj, u, hu, rfl⟩

omit [Finite G] in
theorem ia_layer_eq {p : ℕ} {Y J : Subgroup G} (hJ : GLAPComponent p Y J)
    (huniq : ∀ J' : Subgroup G, GLAPComponent p Y J' → J' = J) : GLAPLayer p Y = J :=
  le_antisymm (sSup_le fun L hL => (huniq L hL).le) (le_sSup hJ)

theorem ia_cover (hcov : CoverStmt) {X K E : Subgroup G} (hK : GLAPComponent 3 X K)
    (hE : IsPGroup 3 ↥E) (hEd : E ≤ dQ K) :
    ∃ J : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set G)) J ∧
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G)) = J ∧
      (∀ J' : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer (E : Set G)) J' → J' = J) ∧
      K ≤ J ⊔ GLAPPrimeCoreOf 3 K ∧ J ≤ K ⊓ Subgroup.centralizer (E : Set G) ∧
      Nonempty (barOf 3 J ≃* barOf 3 K) := by
  obtain ⟨J, hJ, hKJ, huniq, hcore⟩ := hcov G X K E hK hE hEd
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  refine ⟨J, hJ, ia_layer_eq hJ huniq, huniq, hKJ, hJ.1, ?_⟩
  let φ : ↥J →* ↥K ⧸ GLAPPrimeCore 3 ↥K :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hJK)
  have hker : φ.ker = GLAPPrimeCore 3 ↥J := by
    ext j
    rw [MonoidHom.mem_ker, ← mem_coreOf_iff, hcore]
    have h1 : φ j = QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hJK j) := rfl
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨j.2, (mem_coreOf_iff (Subgroup.inclusion hJK j)).2 h⟩
    · intro h
      exact (mem_coreOf_iff (Subgroup.inclusion hJK j)).1 h.2
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hkN : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) :=
      hJK.trans (le_normalizer_glaPPrimeCoreOf_of_le_normalizer (Subgroup.le_normalizer))
    obtain ⟨j, hj, u, hu, hjk⟩ := ia_exists_mul_of_mem_sup hkN (hKJ k.2)
    refine ⟨⟨j, hj⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hJK ⟨j, hj⟩) : ↥K ⧸ GLAPPrimeCore 3 ↥K) =
      QuotientGroup.mk k
    rw [QuotientGroup.eq]
    refine (mem_coreOf_iff _).1 ?_
    have : (((Subgroup.inclusion hJK ⟨j, hj⟩)⁻¹ * k : ↥K) : G) = u := by
      simp [hjk]
    rw [this]
    exact hu
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

private theorem ia_normalizer_le_glbCore {B E : Subgroup G} (hEB : E ≤ B)
    (h3 : 3 ≤ Open.pRank 3 E) : Subgroup.normalizer (E : Set G) ≤ GLBCore 3 3 B :=
  le_sSup ⟨E, hEB, h3, rfl⟩

private theorem ia_le_glbCore_of_coprime {B Y : Subgroup G} (hS : GLStanding G 4 3)
    (hB : IsBOneMax 3 B) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ 3 ∣ Nat.card Y) :
    Y ≤ GLBCore 3 3 B := by
  have hp := hS.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have := hS.nontrivial hB
  have hB' : Nat.card B = 3 ^ ((4 - 1) + 1) := hS.card_eq hB
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY hY).trans (iSup₂_le fun K hK => ?_)
  have hKcard := card_eq_of_index_eq hp hK.1 hK.2 hB'
  have hKel : IsElemAbelian 3 K := isElemAbelian_mono hB.1.1 hK.1
  have h3 : 3 ≤ Open.pRank 3 K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (ia_normalizer_le_glbCore hK.1 h3))

private theorem ia_open_pRank_le_pRank {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    Open.pRank p H ≤ CFSG.pRank p ↥H := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp H
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.le_pRank_of_injective hp (fun a b => ?_) (fun a => ?_) hcard
    (Subgroup.inclusion hEH) (Subgroup.inclusion_injective hEH) le_top
  · exact Subtype.ext (by simpa using congrArg Subtype.val (hE.1.is_comm.comm a b))
  · exact Subtype.ext (by simpa using hE.2 a a.2)

private theorem ia_pRank_le_open_pRank {p : ℕ} (hp : 1 < p) (E : Subgroup G) :
    CFSG.pRank p ↥E ≤ Open.pRank p E := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine (CFSG.SectionRank.pRank_le_map hp E.subtype E.subtype_injective ⊤).trans ?_
  rw [Subgroup.map_top, Subgroup.range_subtype]

private theorem ia_three_le_pRank_sub_one {B : Subgroup G} (hS : GLStanding G 4 3)
    (hB : IsBOneMax 3 B) : 3 ≤ CFSG.pRank 3 ↥B - 1 := by
  have := CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hB.1.1 (hS.card_eq hB)
  have := ia_open_pRank_le_pRank hS.prime.one_lt B
  omega

private theorem ia_glaPPrimeCoreOf_le_glbCore {B K : Subgroup G} (hS : GLStanding G 4 3)
    (hB : IsBOneMax 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    GLAPPrimeCoreOf 3 K ≤ GLBCore 3 3 B :=
  ia_le_glbCore_of_coprime hS hB (le_normalizer_glaPPrimeCoreOf_of_le_normalizer hBN)
    (not_dvd_card_glaPPrimeCoreOf hS.prime K)

private theorem ia_le_glbCore_of_gammaOne {B K : Subgroup G} (hS : GLStanding G 4 3)
    (hB : IsBOneMax 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (h : K ≤ gammaOneBelow B K ⊔ GLAPPrimeCoreOf 3 K) : K ≤ GLBCore 3 3 B := by
  refine h.trans (sup_le ?_ (ia_glaPPrimeCoreOf_le_glbCore hS hB hBN))
  refine iSup₂_le fun E hE => ?_
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (ia_normalizer_le_glbCore hE.1
      (((ia_three_le_pRank_sub_one hS hB).trans hE.2).trans
        (ia_pRank_le_open_pRank hS.prime.one_lt E))))

omit [Finite G] in
private theorem ia_centralizerQuot_eq {B K : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) : centralizerQuot B K = B ⊓ dQ K := by
  unfold centralizerQuot
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro b ⟨hb, hbU⟩
    refine ⟨hb, hBN hb, le_normalizer_glaPPrimeCoreOf_of_le_normalizer hBN hb, fun y hy => ?_⟩
    have h1 : y * b * y⁻¹ * b⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by group
    rw [h1]
    exact inv_mem (hbU y hy)
  · rintro b ⟨hb, hbN', hbU, hb2⟩
    refine Subgroup.subset_closure ⟨hb, fun k hk => ?_⟩
    have h1 : b * k * b⁻¹ * k⁻¹ = (k * b * k⁻¹ * b⁻¹)⁻¹ := by group
    rw [h1]
    exact inv_mem (hb2 k hk)

private theorem ia_isLThreeFour_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsLThreeFour X) : IsLThreeFour Y :=
  IsLThreeFour.of_mulEquiv e h

theorem ia_isLThreeFour_conj {X I : Subgroup G} (hI : GLAPComponent 3 X I) {g : G} (hg : g ∈ X)
    (h : IsLThreeFour (barOf 3 I)) : IsLThreeFour (barOf 3 (GLBConj g I)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hI' := comp_conj hI hg
  set gb := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨g, hg⟩ with hgb
  have e1 : barOf 3 I ≃* ↥(barX 3 X I) := quotEquivBarX hp hI.1 hI.2.1
  have e2 : barOf 3 (GLBConj g I) ≃* ↥(barX 3 X (GLBConj g I)) :=
    quotEquivBarX hp hI'.1 hI'.2.1
  have h3 : barX 3 X (GLBConj g I) = GLBConj gb (barX 3 X I) := barX_gLBConj_of_mem 3 hg I
  have e3 : ↥(barX 3 X I) ≃* ↥(GLBConj gb (barX 3 X I)) :=
    (MulAut.conj gb⁻¹).subgroupMap (barX 3 X I)
  have e4 : ↥(GLBConj gb (barX 3 X I)) ≃* ↥(barX 3 X (GLBConj g I)) :=
    MulEquiv.subgroupCongr h3.symm
  exact IsLThreeFour.of_mulEquiv (e1.trans (e3.trans (e4.trans e2.symm))) h

omit [Finite G] in
theorem ia_B_normalizes_layer {B K J : Subgroup G} {a : G} (haB : a ∈ B)
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) J)
    (huniq : ∀ J' : Subgroup G, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) J' →
      J' = J) : B ≤ Subgroup.normalizer (J : Set G) := by
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.LocalAnalysis.GLTheoremB.elemAbelian_comm hBel hb haB
  have hconj : GLBConj b (K ⊓ Subgroup.centralizer ({a} : Set G)) =
      K ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [gLBConj_inf, gLBConj_eq_of_mem_normalizer (hBN hb),
      gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hbC)]
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ b
  rw [hconj] at h
  exact huniq _ h

theorem ia_B_normalizes_comp {B J I : Subgroup G} {a : G} (hBel : IsElemAbelian 3 B)
    (haB : a ∈ B) (hI : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) I) (hJI : J ≤ I)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJ34 : IsLThreeFour (barOf 3 J)) :
    B ≤ Subgroup.normalizer (I : Set G) := by
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.LocalAnalysis.GLTheoremB.elemAbelian_comm hBel hb haB
  have hI' := comp_conj hI hbC
  have hJI' : J ≤ GLBConj b I := by
    have := gLBConj_mono b hJI
    rwa [gLBConj_eq_of_mem_normalizer (hBJ hb)] at this
  have hJC : J ≤ Subgroup.centralizer ({a} : Set G) := hJI.trans hI.1
  obtain ⟨hs, x, y, hxy⟩ := isSimpleGroup_of_isLThreeFour hJ34
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  apply hxy
  have hcomm : (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ ∈ GLAPPrimeCoreOf 3 J := by
    have h1 := Sec6C.commutator_mem_glaPPrimeCoreOf_of_ne hI hI' (Ne.symm hne) (hJI u.2) (hJI' v.2)
    refine inf_core_le 3 hJC ⟨?_, h1⟩
    exact J.mul_mem (J.mul_mem (J.mul_mem u.2 v.2) (J.inv_mem u.2)) (J.inv_mem v.2)
  have hmem : u * v * u⁻¹ * v⁻¹ ∈ GLAPPrimeCore 3 ↥J := (mem_coreOf_iff (u * v * u⁻¹ * v⁻¹)).1 hcomm
  have h2 : (QuotientGroup.mk (u * v * u⁻¹ * v⁻¹) : ↥J ⧸ GLAPPrimeCore 3 ↥J) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hmem
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
  calc (QuotientGroup.mk u : ↥J ⧸ GLAPPrimeCore 3 ↥J) * QuotientGroup.mk v
      = ((QuotientGroup.mk u : ↥J ⧸ GLAPPrimeCore 3 ↥J) * QuotientGroup.mk v *
          (QuotientGroup.mk u)⁻¹ * (QuotientGroup.mk v)⁻¹) * QuotientGroup.mk v *
          QuotientGroup.mk u := by group
    _ = QuotientGroup.mk v * QuotientGroup.mk u := by rw [h2, one_mul]

theorem ia_F_le {B K J : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJK : J ≤ K)
    (hKJ : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) : B ⊓ K ≤ J := by
  rintro f ⟨hfB, hfK⟩
  have hkN : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) :=
    hJK.trans (le_normalizer_glaPPrimeCoreOf_of_le_normalizer (Subgroup.le_normalizer))
  obtain ⟨j, hj, u, hu, hfju⟩ := ia_exists_mul_of_mem_sup hkN (hKJ hfK)
  have hfN : f ∈ Subgroup.normalizer (J : Set G) := hBJ hfB
  have hjN : j ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hj
  have huN : u ∈ Subgroup.normalizer (J : Set G) := by
    have : u = j⁻¹ * f := by rw [hfju]; group
    rw [this]
    exact (Subgroup.normalizer (J : Set G)).mul_mem ((Subgroup.normalizer (J : Set G)).inv_mem hjN) hfN
  set N := Subgroup.normalizer (J : Set G) with hN
  let f' : ↥N := ⟨f, hfN⟩
  let u' : ↥N := ⟨u, huN⟩
  have hmk : (QuotientGroup.mk u' : ↥N ⧸ J.subgroupOf N) = QuotientGroup.mk f' := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((u⁻¹ * f : G)) ∈ J
    have : u⁻¹ * f = f⁻¹ * j * f := by rw [hfju]; group
    rw [this]
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hfN : f⁻¹ ∈ N) j).1 hj
    simpa [mul_assoc] using this
  have h3 : (QuotientGroup.mk f' : ↥N ⧸ J.subgroupOf N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show f ^ 3 ∈ J
    rw [hBel.2 f hfB]
    exact J.one_mem
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_dvd_card_glaPPrimeCoreOf Nat.prime_three K)
  have hn : (QuotientGroup.mk f' : ↥N ⧸ J.subgroupOf N) ^ Nat.card (GLAPPrimeCoreOf 3 K) = 1 := by
    rw [← hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show u ^ Nat.card (GLAPPrimeCoreOf 3 K) ∈ J
    have : ((⟨u, hu⟩ : GLAPPrimeCoreOf 3 K) ^ Nat.card (GLAPPrimeCoreOf 3 K) : GLAPPrimeCoreOf 3 K) = 1 :=
      pow_card_eq_one'
    have h4 := congrArg Subtype.val this
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h4
    rw [h4]
    exact J.one_mem
  have hord : orderOf (QuotientGroup.mk f' : ↥N ⧸ J.subgroupOf N) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one h3
    have h2 := orderOf_dvd_of_pow_eq_one hn
    exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  have h5 : (QuotientGroup.mk f' : ↥N ⧸ J.subgroupOf N) = 1 := orderOf_eq_one_iff.1 hord
  have h6 := (QuotientGroup.eq_one_iff f').1 h5
  exact (Subgroup.mem_subgroupOf).1 h6

theorem ia_le_sup_of_cover {J I : Subgroup G} (hJI : J ≤ I)
    (hJ34 : IsLThreeFour (barOf 3 J)) (hI34 : IsLThreeFour (barOf 3 I)) :
    I ≤ J ⊔ GLAPPrimeCoreOf 3 I := by
  let ψ : ↥J →* barOf 3 I :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)).comp (Subgroup.inclusion hJI)
  have hker : ψ.ker ≤ GLAPPrimeCore 3 ↥J := by
    intro j hj
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) (Subgroup.inclusion hJI j) = 1 :=
      MonoidHom.mem_ker.1 hj
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (j : G) ∈ GLAPPrimeCoreOf 3 I := (mem_coreOf_iff (Subgroup.inclusion hJI j)).2 h1
    exact (mem_coreOf_iff j).1 (inf_core_le 3 hJI ⟨j.2, h2⟩)
  have hdvd : (GLAPPrimeCore 3 ↥J).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hker
  have hJc : (GLAPPrimeCore 3 ↥J).index = 20160 := by
    rw [Subgroup.index_eq_card]
    exact card_eq_of_isLThreeFour hJ34
  rw [Subgroup.index_ker, hJc] at hdvd
  have hIc : Nat.card (barOf 3 I) = 20160 := card_eq_of_isLThreeFour hI34
  have hle : Nat.card ψ.range ≤ 20160 := hIc ▸ Subgroup.card_le_card_group ψ.range
  have hpos : 0 < Nat.card ψ.range := Nat.card_pos
  have heq : Nat.card ψ.range = Nat.card (barOf 3 I) :=
    hIc ▸ le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ heq
  intro i hi
  have hz : (QuotientGroup.mk (⟨i, hi⟩ : ↥I) : barOf 3 I) ∈ ψ.range := by rw [htop]; trivial
  obtain ⟨j, hj⟩ := hz
  have h1 : QuotientGroup.mk (Subgroup.inclusion hJI j) = (QuotientGroup.mk (⟨i, hi⟩ : ↥I) : barOf 3 I) :=
    hj
  rw [QuotientGroup.eq] at h1
  have h2 : ((Subgroup.inclusion hJI j)⁻¹ * ⟨i, hi⟩ : ↥I).1 ∈ GLAPPrimeCoreOf 3 I :=
    (mem_coreOf_iff _).2 h1
  have h3 : (j : G)⁻¹ * i ∈ GLAPPrimeCoreOf 3 I := h2
  have : i = (j : G) * ((j : G)⁻¹ * i) := by group
  rw [this]
  exact Subgroup.mul_mem_sup j.2 h3

omit [Finite G] in
private theorem ia_glaPPrimeCoreOf_le {p : ℕ} (X : Subgroup G) : GLAPPrimeCoreOf p X ≤ X := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
private theorem ia_glaPLayer_le {p : ℕ} (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => hL.1

set_option linter.unusedVariables false in
theorem isIaFacts_of_inputs (hcov : CoverStmt) (h62 : Lemma62Stmt) (i1812 : Input18_3_12)
    (i254 : Input25_4)
    (hnotL2 : ∀ (M : Type) [Group M] [Finite M], IsLTwoOddPow M →
      ∀ (Z : Subgroup M) [Z.Normal], Z ≤ Subgroup.center M → ¬ IsLThreeFour (M ⧸ Z))
    (hS : GLStanding G 4 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsExtremal B)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) {K : Subgroup G}
    (hcomp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K)
    (hKM : ¬ K ≤ GLBCore 3 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hK34 : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K))
    (haK : IsEkIn 3 2 B (centralizerQuot B K)) (hfK : IsEkIn 3 2 B (B ⊓ K))
    (hsup : centralizerQuot B K ⊔ (B ⊓ K) = B) (hinf : centralizerQuot B K ⊓ (B ⊓ K) = ⊥)
    {a : G} (ha : a ∈ centralizerQuot B K) (ha1 : a ≠ 1)
    (hkZero : kZeroOf B K ≤ bClosureIa K a) : IsIaFacts B K a := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB1 : IsBOneMax 3 B := hB.1
  have hBel : IsElemAbelian 3 B := hB1.1.1
  have haB : a ∈ B := haK.1 ha
  have hAd : centralizerQuot B K ≤ dQ K := by
    rw [ia_centralizerQuot_eq hBN]
    exact inf_le_right
  have hadQ : a ∈ dQ K := hAd ha
  have ha3 : a ^ 3 = 1 := hBel.2 a haB
  have hx3 : x ^ 3 = 1 := hBel.2 x hx
  have hxa : x * a = a * x := CFSG.LocalAnalysis.GLTheoremB.elemAbelian_comm hBel hx haB
  have hBC : B ≤ Subgroup.centralizer ({a} : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.LocalAnalysis.GLTheoremB.elemAbelian_comm hBel hb haB
  have hzp : IsElemAbelian 3 (Subgroup.zpowers a) :=
    isElemAbelian_mono hBel (Subgroup.zpowers_le.2 haB)
  have hcz : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨J0, hJ0c, hK0, huniq0, hKJ0, hJ0le, ⟨e0⟩⟩ :=
    ia_cover hcov hcomp (isPGroup_of_isElemAbelian hzp) (Subgroup.zpowers_le.2 hadQ)
  rw [hcz] at hJ0c hK0 huniq0 hJ0le
  have hJ0K : J0 ≤ K := hJ0le.trans inf_le_left
  have hJ034 : IsLThreeFour (barOf 3 J0) := IsLThreeFour.of_mulEquiv e0.symm hK34
  have hBJ0 : B ≤ Subgroup.normalizer (J0 : Set G) :=
    ia_B_normalizes_layer haB hBel hBN hJ0c huniq0
  have hKP : CFSG.IsKProper G :=
    CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.2
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hS.kProper)
  have hLx : K ≤ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) := le_sSup hcomp
  have hsn1 : IsSubnormal (K ⊓ Subgroup.centralizer ({a} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) :=
    isSubnormal_inf hcomp.2.1 _
  have hJ0Cx : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({a} : Set G)) J0 :=
    ia_comp_up Nat.prime_three hJ0c (inf_le_inf_right _ hcomp.1)
      (isSubnormal_trans' hJ0c.2.1 hsn1)
  have hJ0L : GLAPComponent 3 (GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
      Subgroup.centralizer ({a} : Set G)) J0 :=
    glaPComponent_of_le Nat.prime_three hJ0Cx
      (le_inf ((hJ0K.trans hLx)) (hJ0le.trans inf_le_right))
      (inf_le_inf_right _ (ia_glaPLayer_le _))
  have hIdef : bClosureIa K a = ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)),
      GLBConj g J0 := by
    unfold bClosureIa
    rw [hK0]
  rcases i1812 G hKP x a hx1 ha1 hx3 ha3 hxa J0 hJ0L with
    ⟨hIcomp, -⟩ | ⟨M, hM, hxM1, -, -, Z, hZ, hZc, ⟨eMJ⟩⟩
  swap
  · exfalso
    have := hZ
    rcases h62 G 4 hS hC B hB a haB ha1 M hM with hBM | hL2
    · exact hxM1 (gLBConj_eq_of_mem_normalizer (hBM hx))
    · exact hnotL2 (barOf 3 M) hL2 Z hZc (IsLThreeFour.of_mulEquiv eMJ hJ034)
  rw [← hIdef] at hIcomp
  have hJ0I : J0 ≤ bClosureIa K a := by
    rw [hIdef]
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [gLBConj_one])
  have hBI : B ≤ Subgroup.normalizer (bClosureIa K a : Set G) :=
    ia_B_normalizes_comp hBel haB hIcomp hJ0I hBJ0 hJ034
  have hacent : a ∈ Subgroup.centralizer (bClosureIa K a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hIcomp.1 hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hadQI : a ∈ dQ (bClosureIa K a) := by
    refine ⟨Subgroup.centralizer_le_normalizer _ hacent, ?_, fun y hy => ?_⟩
    · refine Subgroup.centralizer_le_normalizer _ ?_
      exact (Subgroup.centralizer_le (ia_glaPPrimeCoreOf_le (bClosureIa K a))) hacent
    · have := Subgroup.mem_centralizer_iff.1 hacent y hy
      rw [this]
      simp
  have hXK : CFSG.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    hKP _ (centralizer_ne_top_of_simple hS ha1)
  have hrank : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({a} : Set G)) ≤ 4 := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_subgroup_le (G := G) (p := 3)
      (by norm_num) (Subgroup.centralizer ({a} : Set G))
    have h3 : GLATwoLocalRank 3 G = 4 := hC.2.1
    omega
  have hJ0Ix : GLAPComponent 3 (bClosureIa K a ⊓ Subgroup.centralizer ({x} : Set G)) J0 :=
    glaPComponent_of_le Nat.prime_three hJ0Cx
      (le_inf hJ0I (hJ0K.trans hcomp.1))
      (le_inf inf_le_right (inf_le_left.trans hIcomp.1))
  have hI34 : IsLThreeFour (barOf 3 (bClosureIa K a)) := by
    rcases i254 G (Subgroup.centralizer ({a} : Set G)) (bClosureIa K a) B hXK hIcomp hBel hBC
      hrank ⟨a, ⟨haB, hadQI⟩, ha1⟩ hBI ⟨x, hx, hx1, J0, hJ0Ix, hJ034⟩ with h | hγ
    · exact h
    · exfalso
      have hIM := ia_le_glbCore_of_gammaOne hS hB1 hBI hγ
      exact hKM (hKJ0.trans (sup_le (hJ0I.trans hIM) (ia_glaPPrimeCoreOf_le_glbCore hS hB1 hBN)))
  have hnot : ∀ (M : Type) [Group M] [Finite M], IsLThreeFour M → ¬ IsLTwoOddPow M :=
    fun M _ _ h h2 => hnotL2 M h2 ⊥ bot_le
      (IsLThreeFour.of_mulEquiv (QuotientGroup.quotientBot (G := M)).symm h)
  have hFle : B ⊓ K ≤ bClosureIa K a :=
    (ia_F_le hBel hBJ0 hJ0K hKJ0).trans hJ0I
  have hBIel : IsElemAbelian 3 (B ⊓ bClosureIa K a) := isElemAbelian_mono hBel inf_le_left
  have hFcard : IsEkIn 3 2 B (B ⊓ bClosureIa K a) := by
    refine ⟨inf_le_left, hBIel, ?_⟩
    have h1 := (Sec6C.card_le_nine_of_isPGroup (inf_le_right : B ⊓ bClosureIa K a ≤ bClosureIa K a)
      (isPGroup_of_isElemAbelian hBIel) hI34).1
    have h2 : Nat.card ↥(B ⊓ K) ≤ Nat.card ↥(B ⊓ bClosureIa K a) :=
      Subgroup.card_le_of_le (le_inf inf_le_left hFle)
    have h3 : Nat.card ↥(B ⊓ K) = 3 ^ 2 := hfK.2.2
    omega
  have huc := uniqComp_of_B1max hS hB1
  have hnormal : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (bClosureIa K a : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq]
    have hI' := comp_conj hIcomp hg
    have hI'34 := ia_isLThreeFour_conj hIcomp hg hI34
    have hBI' : B ≤ Subgroup.normalizer (GLBConj g (bClosureIa K a) : Set G) := by
      rcases h62 G 4 hS hC B hB a haB ha1 _ hI' with h | hL2
      · exact h
      · exact absurd hL2 (hnot _ hI'34)
    exact huc a haB ha1 _ _ hI' hIcomp hBI' hBI hI'34 hI34 hFcard
  obtain ⟨J1, -, hlay1, -, -, -, ⟨e1⟩⟩ :=
    ia_cover hcov hcomp (isPGroup_of_isElemAbelian (isElemAbelian_mono hBel haK.1)) hAd
  have hkz : kZeroOf B K = J1 := hlay1
  have hJ134 : IsLThreeFour (barOf 3 J1) := IsLThreeFour.of_mulEquiv e1.symm hK34
  refine ⟨hIcomp, hnormal, hI34, hkZero, ?_⟩
  rw [hkz]
  rw [hkz] at hkZero
  exact ia_le_sup_of_cover hkZero hJ134 hI34

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
