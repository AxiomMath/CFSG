module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.QuotientCentralizer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.PerfectXSub
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxGrp
import CFSG.LieType.SteinbergBRSmallAltSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenPower
import CFSG.Quasithin.Background.S1549CA0
import CFSG.GroupTheory.DedekindNormalizer
import CFSG.Quasithin.EmptyFaithful.S152He15A
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M H E Q J N : Subgroup G}

noncomputable abbrev Xhat (N A : Subgroup G) (hAN : A ≤ N)
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) : Subgroup G :=
  quotientCentralizer N A (CFSG.pPrimeCore 3 ↥A) hAN hNA

theorem S14Choice.hypCGen_of_le_isMaxTwoLocal (h : S14Choice G M H E Q J)
    (hL : PLayerNotLeAt M) (hN : CFSG.Open.rankThreeIsMaxTwoLocal N) (hJN : J ≤ N) (hQN : Q ≤ N) :
    HypCGen G M 3 E N ∧ N ∈ H2StarFam M Q := by
  have hNstar : N ∈ H2StarFam M E :=
    h.hypCGen.mem_H2StarFam_of_isMaxTwoLocal (K := J ⊔ E) le_sup_right
      (fun hKM => h.not_le_M hL (le_sup_left.trans hKM))
      (show CFSG.Open.IsMaxTwoLocalSubgroup N from hN)
      (sup_le hJN (h.E_le_Q.trans hQN))
  exact ⟨{ h.hypCGen with mem := hNstar }, mem_H2StarFam_of_le hNstar hQN⟩

private theorem pPrimeCore_kSub_le_pPrimeCore (h : HypCGen G M 3 E N) (hK : KNormalAt M) :
    (CFSG.pPrimeCore 3 ↥(kSub 3 M N)).map (kSub 3 M N).subtype ≤
      (CFSG.pPrimeCore 3 ↥N).map N.subtype := by
  have hrel := CFSG.LocalAnalysis.AGL81TheoremCD.Section14.pPrimeCore_map_le_relPPrimeCore
    (p := 3) (K := kSub 3 M N) (H := N) (kSub_le 3 M N) (hK 3 E N h)
  rwa [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    Nat.prime_three N] at hrel

private theorem quotientCentralizer_kSub_le_xSub (h : HypCGen G M 3 E N) (hK : KNormalAt M) :
    Xhat N (kSub 3 M N) (kSub_le 3 M N) (hK 3 E N h) ≤ xSub 3 M N := by
  let K : Subgroup G := kSub 3 M N
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let DN : Subgroup G := (CFSG.pPrimeCore 3 ↥N).map N.subtype
  let π : ↥N →* (↥N ⧸ CFSG.pPrimeCore 3 ↥N) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥N)
  have hKN : K ≤ N := kSub_le 3 M N
  have hDle : D ≤ DN := pPrimeCore_kSub_le_pPrimeCore h hK
  refine CFSG.AGLEmbedding.le_d1PlusCore_of_map_le (Y := Xhat N K (kSub_le 3 M N)
    (hK 3 E N h)) (K := kStar 3 M N) (quotientCentralizer_le N K _ _ _) ?_
  intro z hz
  obtain ⟨zN, hzN, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨kN, hkN, rfl⟩ := Subgroup.mem_map.mp hw
  have hkN' : (kN : G) ∈ K := Subgroup.mem_subgroupOf.mp hkN
  have hzY : (zN : G) ∈ Xhat N K (kSub_le 3 M N) (hK 3 E N h) :=
    Subgroup.mem_subgroupOf.mp hzN
  have hcommD : (zN : G) * (kN : G) * (zN : G)⁻¹ * (kN : G)⁻¹ ∈ D :=
    commutator_mem_map_of_mem_quotientCentralizer (Q := CFSG.pPrimeCore 3 ↥K)
      (kSub_le 3 M N) (hK 3 E N h) hzY hkN'
  have hcommDN : (zN : G) * (kN : G) * (zN : G)⁻¹ * (kN : G)⁻¹ ∈ DN := hDle hcommD
  have hcommN : zN * kN * zN⁻¹ * kN⁻¹ ∈ CFSG.pPrimeCore 3 ↥N := by
    obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hcommDN
    have heq : d = zN * kN * zN⁻¹ * kN⁻¹ := Subtype.ext (by simpa using hdeq)
    rwa [heq] at hd
  have hπ1 : π (zN * kN * zN⁻¹ * kN⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcommN
  have hπeq : π zN * π kN * (π zN)⁻¹ * (π kN)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using hπ1
  show π kN * π zN = π zN * π kN
  exact (commutatorElement_eq_one_iff_commute.mp (by
    simpa [commutatorElement_def] using hπeq)).symm.eq

theorem HypCGen.not_le_quotientCentralizer_kSub
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne) (h : HypCGen G M 3 E N)
    (hK : KNormalAt M) (hLN : ¬ pLayerIn 3 N ≤ M) {Y : Subgroup G} (hYM : ¬ Y ≤ M)
    (hY : Group.IsPerfect ↥Y) :
    ¬ Y ≤ Xhat N (kSub 3 M N) (kSub_le 3 M N) (hK 3 E N h) :=
  fun hYX => hYM (h.le_of_isPerfect_of_le_xSub h711 hLN hY
    (hYX.trans (quotientCentralizer_kSub_le_xSub h hK)))

private theorem isSolvable_outer_threeStar_of_star {A : Subgroup G} (hA : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A) :
    Group.IsSolvable (Outer (threeStar A)) := by
  have hcomp : IsPComponentIn 3 A (kSub 3 M N) := hA
  have hq : CFSG.IsQuasisimple (threeStar A) :=
    IsPComponentIn.isQuasisimple_quot Nat.prime_three hcomp
  haveI : Group.IsPerfect (threeStar A) := hq.1
  rcases htype with h34 | h34 | h11 | h6
  · obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h34.1
    haveI : Group.IsSolvable (Outer (projectiveSL 3 (GaloisField 2 2))) :=
      isSolvable_out_projectiveSL
        (K := GaloisField 2 2) (by norm_num)
    have hOutBar : Group.IsSolvable (Outer (threeStar A ⧸ Subgroup.center (threeStar A))) :=
      solvable_of_equiv (G := projectiveSL 3 (GaloisField 2 2))
        (H := threeStar A ⧸ Subgroup.center (threeStar A))
        ((e.trans (projSLEquivProjectiveSL 3 (GaloisField 2 2))).symm)
    haveI : Group.IsSolvable (Outer (threeStar A ⧸ (⊥ : Subgroup (threeStar A)))) :=
      outer_solvable_of_central_quotient
        (G := threeStar A) (Z₀ := ⊥) bot_le hOutBar
    have eBot : (threeStar A ⧸ (⊥ : Subgroup (threeStar A))) ≃* threeStar A :=
      QuotientGroup.quotientBot
    exact solvable_of_equiv (G := threeStar A ⧸ (⊥ : Subgroup (threeStar A)))
      (H := threeStar A) eBot
  · obtain ⟨e⟩ := nonempty_mulEquiv_projSL_of_isL34Type h34.1 h34.2
    haveI : Group.IsSolvable (Outer (projectiveSL 3 (GaloisField 2 2))) :=
      isSolvable_out_projectiveSL
        (K := GaloisField 2 2) (by norm_num)
    exact solvable_of_equiv (G := projectiveSL 3 (GaloisField 2 2)) (H := threeStar A)
      ((e.trans (projSLEquivProjectiveSL 3 (GaloisField 2 2))).symm)
  · obtain ⟨e⟩ := h11
    haveI : Group.IsSolvable (Outer (alternatingGroup (Fin 11))) :=
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (n := 11)
        (Or.inr (by norm_num))).1
    exact solvable_of_equiv (G := alternatingGroup (Fin 11)) (H := threeStar A) e.symm
  · obtain ⟨e⟩ := h6.1
    haveI : Group.IsNilpotent (Outer (alternatingGroup (Fin 6))) :=
      CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.isNilpotent
    have hOut6 : Group.IsSolvable (Outer (alternatingGroup (Fin 6))) := inferInstance
    have hOutBar : Group.IsSolvable (Outer (threeStar A ⧸ Subgroup.center (threeStar A))) :=
      solvable_of_equiv (G := alternatingGroup (Fin 6))
        (H := threeStar A ⧸ Subgroup.center (threeStar A)) e.symm
    haveI : Group.IsSolvable (Outer (threeStar A ⧸ (⊥ : Subgroup (threeStar A)))) :=
      outer_solvable_of_central_quotient
        (G := threeStar A) (Z₀ := ⊥) bot_le hOutBar
    have eBot : (threeStar A ⧸ (⊥ : Subgroup (threeStar A))) ≃* threeStar A :=
      QuotientGroup.quotientBot
    exact solvable_of_equiv (G := threeStar A ⧸ (⊥ : Subgroup (threeStar A)))
      (H := threeStar A) eBot

theorem le_sup_quotientCentralizer_of_star {N₁ A K : Subgroup G} (hA : IsKComp M N A)
    (htype : IsSL34Star A ∨ IsL34Star A ∨ IsA11Star A ∨ Is3A6Star A) (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) (hKN : K ≤ N₁) (hK : Group.IsPerfect ↥K) :
    K ≤ A ⊔ Xhat N₁ A hAN hNA :=
  perfect_le_sup_quotientCentralizer (pPrimeCore 3 ↥A) hAN hNA hKN hK
    (isSolvable_outer_threeStar_of_star hA htype)

private theorem oTwoZStar_le_quotientCentralizer {N₁ A : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) :
    oTwoZStar A ≤ Xhat N₁ A hAN hNA := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
  have hzA : (z : G) ∈ A := z.2
  have hzx' : (z : G) = x := by simpa using hzx
  have hxA : x ∈ A := hzx' ▸ hzA
  have hzcenter : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) z ∈
      Subgroup.center (threeStar A) := Subgroup.mem_comap.mp hz
  refine (mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥A) hAN hNA).mpr
    ⟨⟨x, hAN hxA⟩, rfl, ?_⟩
  apply MulEquiv.ext
  intro w
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥A) w
  let u : threeStar A := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) ⟨x, hxA⟩
  have hzxA : (⟨x, hxA⟩ : ↥A) = z := Subtype.ext (by simpa using hzx'.symm)
  have hzc : u ∈ Subgroup.center (threeStar A) := by
    simpa [u, hzxA] using hzcenter
  rw [conjQuotAction_apply_mem (N := N₁) (L := A) (CFSG.pPrimeCore 3 ↥A) hAN hNA hxA l]
  change MulAut.conj u (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) l) =
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) l
  rw [MulAut.conj_apply]
  have hcomm := Subgroup.mem_center_iff.mp hzc (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) l)
  rw [← hcomm]
  group

private theorem quotientCentralizer_inf_le_oTwoZStar {N₁ A : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) :
    Xhat N₁ A hAN hNA ⊓ A ≤ oTwoZStar A := by
  intro x hx
  obtain ⟨hxX, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hnx, hnker⟩ :=
    (mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥A) hAN hNA).mp hxX
  have hnA : (n : G) ∈ A := hnx ▸ hxA
  have hcenter : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) (⟨(n : G), hnA⟩ : ↥A) ∈
      Subgroup.center (threeStar A) := by
    let u : threeStar A := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) ⟨(n : G), hnA⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥A) y
    let w : threeStar A := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥A) l
    have h := congrArg (fun f : MulAut (threeStar A) => f w) hnker
    rw [conjQuotAction_apply_mem (N := N₁) (L := A) (CFSG.pPrimeCore 3 ↥A) hAN hNA hnA l] at h
    change MulAut.conj u w = w at h
    rw [MulAut.conj_apply] at h
    have huw : u * w = w * u := by
      calc u * w = (u * w * u⁻¹) * u := by group
        _ = w * u := by rw [h]
    exact huw.symm
  have hn_eq : (⟨(n : G), hnA⟩ : ↥A) = ⟨x, hxA⟩ := Subtype.ext hnx
  refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  simpa [hn_eq] using hcenter

theorem quotientCentralizer_inf_eq_oTwoZStar {N₁ A : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) :
    Xhat N₁ A hAN hNA ⊓ A = oTwoZStar A :=
  le_antisymm (quotientCentralizer_inf_le_oTwoZStar hAN hNA)
    (le_inf (oTwoZStar_le_quotientCentralizer hAN hNA) (Subgroup.map_subtype_le _))

private noncomputable def commHomOfCentral {Z S : Subgroup G}
    (hZc : Z ≤ Subgroup.centralizer (S : Set G)) {g : G} (hg : g ∈ S)
    (hcomm : ∀ s ∈ S, s * g * s⁻¹ * g⁻¹ ∈ Z) : ↥S →* ↥Z where
  toFun s := ⟨s * g * s⁻¹ * g⁻¹, hcomm s s.2⟩
  map_one' := by ext; simp
  map_mul' s t := by
    ext
    have hw : (t : G) * g * (t : G)⁻¹ * g⁻¹ ∈ Z := hcomm t t.2
    have hsw : (s : G) * ((t : G) * g * (t : G)⁻¹ * g⁻¹) =
        ((t : G) * g * (t : G)⁻¹ * g⁻¹) * s :=
      Subgroup.mem_centralizer_iff.mp (hZc hw) (s : G) s.2
    show (s : G) * t * g * ((s : G) * t)⁻¹ * g⁻¹ =
      ((s : G) * g * (s : G)⁻¹ * g⁻¹) * ((t : G) * g * (t : G)⁻¹ * g⁻¹)
    calc (s : G) * t * g * ((s : G) * t)⁻¹ * g⁻¹ =
        (s : G) * ((t : G) * g * (t : G)⁻¹ * g⁻¹) * g * (s : G)⁻¹ * g⁻¹ := by group
      _ = ((t : G) * g * (t : G)⁻¹ * g⁻¹) * s * g * (s : G)⁻¹ * g⁻¹ := by rw [hsw]
      _ = ((t : G) * g * (t : G)⁻¹ * g⁻¹) * ((s : G) * g * (s : G)⁻¹ * g⁻¹) := by group
      _ = ((s : G) * g * (s : G)⁻¹ * g⁻¹) * ((t : G) * g * (t : G)⁻¹ * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hZc hw) _
          (S.mul_mem (S.mul_mem (S.mul_mem s.2 hg) (S.inv_mem s.2)) (S.inv_mem hg))).symm

private theorem mem_ker_commHomOfCentral {Z S : Subgroup G}
    (hZc : Z ≤ Subgroup.centralizer (S : Set G)) {g : G} (hg : g ∈ S)
    (hcomm : ∀ s ∈ S, s * g * s⁻¹ * g⁻¹ ∈ Z) (s : ↥S) :
    s ∈ (commHomOfCentral hZc hg hcomm).ker ↔ (s : G) * g = g * (s : G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (s : G) * g * (s : G)⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h
    calc (s : G) * g = ((s : G) * g * (s : G)⁻¹ * g⁻¹) * g * s := by group
      _ = g * s := by rw [h1, one_mul]
  · intro h
    apply Subtype.ext
    show (s : G) * g * (s : G)⁻¹ * g⁻¹ = 1
    rw [h]
    group

private theorem exists_elemAbelian_nine_of_exp_three {R : Subgroup G}
    (hexp : ∀ x ∈ R, x ^ 3 = 1) (h81 : 81 ≤ Nat.card R) :
    ∃ F : Subgroup G, F ≤ R ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp' : ∀ x : ↥R, x ^ 3 = 1 := fun x => Subtype.ext (hexp x x.2)
  have hR3 : IsPGroup 3 ↥R := fun x => ⟨1, by simpa using hexp' x⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    have hpow : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    rw [hk] at h81
    omega
  have h9 : 9 ∣ Nat.card ↥R := by
    rw [hk]
    exact pow_dvd_pow 3 hk2
  obtain ⟨E, hEelem, hEcard⟩ :=
    CFSG.Quasithin.S1549C.exists_elemAbelian_nine (P := ↥R) hexp' h9
  refine ⟨E.map R.subtype, Subgroup.map_subtype_le E, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hEelem _
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hEcard]

private theorem card_eq_three_of_pow_three_eq_one {Z : Subgroup G}
    (hZexp : ∀ z ∈ Z, z ^ 3 = 1) (hZcard : Nat.card Z ≤ 3) (hZne : Z ≠ ⊥) :
    Nat.card Z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3g : IsPGroup 3 Z := fun z => ⟨1, by
    apply Subtype.ext
    simpa using hZexp z z.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3g
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have hdvd : 9 ∣ Nat.card Z := by
      rw [hk]
      exact pow_dvd_pow 3 h2
    have h9le : 9 ≤ Nat.card Z := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hk0 : k ≠ 0 := by
    intro h0
    apply hZne
    apply Subgroup.eq_bot_of_card_eq
    rw [hk, h0]
    simp
  have hk1' : k = 1 := by omega
  rw [hk, hk1']
  norm_num

private theorem exists_cube_kernel_large {R Z : Subgroup G}
    (hZc : Z ≤ Subgroup.centralizer (R : Set G))
    (hZexp : ∀ z ∈ Z, z ^ 3 = 1) (hZcard : Nat.card Z = 3)
    (hcomm : ⁅R, R⁆ ≤ Z) (hcube : ∀ x ∈ R, x ^ 3 ∈ Z)
    (hbig : 81 * Nat.card Z ≤ Nat.card R) :
    ∃ Ω : Subgroup G, Ω ≤ R ∧ (∀ y ∈ Ω, y ^ 3 = 1) ∧ 81 ≤ Nat.card Ω := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ s ∈ R, ∀ t ∈ R, s * t * s⁻¹ * t⁻¹ ∈ Z := fun s hs t ht =>
    hcomm (Subgroup.commutator_mem_commutator hs ht)
  let ω : ↥R →* ↥Z :=
    { toFun := fun r => ⟨(r : G) ^ 3, hcube r r.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (by
        have hxy : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ Z :=
          hc y y.2 x x.2
        have hxc : Commute ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹) (x : G) :=
          (Subgroup.mem_centralizer_iff.mp (hZc hxy) (x : G) x.2).symm
        have hyc : Commute ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹) (y : G) :=
          (Subgroup.mem_centralizer_iff.mp (hZc hxy) (y : G) y.2).symm
        have h3 : ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹) ^ 3 = 1 :=
          hZexp _ hxy
        have hpow := CFSG.AGLEmbedding.ThompsonGen.mul_pow_prime_of_commutator
          Nat.prime_three (by norm_num) hxc hyc h3
        simpa [Subgroup.coe_mul, Subgroup.coe_pow] using hpow) }
  have hωcard := Subgroup.card_ker_mul_card_range ω
  have hωrange : Nat.card ω.range ≤ 3 :=
    (Subgroup.card_le_card_group _).trans (by rw [hZcard])
  have hωker : 81 ≤ Nat.card ω.ker := by
    have hNle : Nat.card ↥R ≤ Nat.card ω.ker * Nat.card ω.range := by
      rw [hωcard]
    have hNle' : Nat.card ↥R ≤ Nat.card ω.ker * 3 :=
      hNle.trans (Nat.mul_le_mul_left _ hωrange)
    have hbig' : 81 * 3 ≤ Nat.card ↥R := by
      simpa [hZcard] using hbig
    have h243 : 81 * 3 ≤ Nat.card ω.ker * 3 := hbig'.trans hNle'
    exact Nat.le_of_mul_le_mul_right h243 (by norm_num)
  let Ω : Subgroup G := ω.ker.map R.subtype
  have hΩcard : Nat.card Ω = Nat.card ω.ker :=
    Subgroup.card_map_of_injective R.subtype_injective
  have hΩmem : ∀ y ∈ Ω, y ∈ R ∧ y ^ 3 = 1 := by
    rintro y ⟨r, hr, rfl⟩
    exact ⟨r.2, congrArg Subtype.val (MonoidHom.mem_ker.mp hr)⟩
  refine ⟨Ω, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro y hy
    exact (hΩmem y hy).2
  · rw [hΩcard]
    exact hωker

private theorem exists_commuting_subgroup_large {R Z Ω : Subgroup G} {x : G}
    (hΩR : Ω ≤ R) (hZc : Z ≤ Subgroup.centralizer (R : Set G))
    (hcomm : ⁅R, R⁆ ≤ Z) (hZcard : Nat.card Z = 3)
    (hxΩ : x ∈ Ω) (hΩ81 : 81 ≤ Nat.card Ω) :
    ∃ K : Subgroup G, K ≤ Ω ∧ 27 ≤ Nat.card K ∧ (∀ y ∈ K, y * x = x * y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ s ∈ R, ∀ t ∈ R, s * t * s⁻¹ * t⁻¹ ∈ Z := fun s hs t ht =>
    hcomm (Subgroup.commutator_mem_commutator hs ht)
  have hcx : ∀ s ∈ Ω, s * x * s⁻¹ * x⁻¹ ∈ Z := fun s hs =>
    hc s (hΩR hs) x (hΩR hxΩ)
  have hZcΩ : Z ≤ Subgroup.centralizer (Ω : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (hZc hz) s (hΩR hs)
  let χ : ↥Ω →* ↥Z := commHomOfCentral hZcΩ hxΩ hcx
  have hχcard := Subgroup.card_ker_mul_card_range χ
  have hχrange : Nat.card χ.range ≤ 3 :=
    (Subgroup.card_le_card_group _).trans (by rw [hZcard])
  have hχker : 27 ≤ Nat.card χ.ker := by
    have hΩle : Nat.card Ω ≤ Nat.card χ.ker * Nat.card χ.range := by
      rw [hχcard]
    have hΩle' : Nat.card Ω ≤ Nat.card χ.ker * 3 :=
      hΩle.trans (Nat.mul_le_mul_left _ hχrange)
    have h81 : 81 ≤ Nat.card χ.ker * 3 := hΩ81.trans hΩle'
    have h27 : 27 * 3 ≤ Nat.card χ.ker * 3 := by simpa using h81
    exact Nat.le_of_mul_le_mul_right h27 (by norm_num)
  let K : Subgroup G := χ.ker.map Ω.subtype
  have hKcard : Nat.card K = Nat.card χ.ker :=
    Subgroup.card_map_of_injective Ω.subtype_injective
  refine ⟨K, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [hKcard]
    exact hχker
  · intro y hy
    obtain ⟨yΩ, hyker, rfl⟩ := Subgroup.mem_map.mp hy
    exact (mem_ker_commHomOfCentral hZcΩ hxΩ hcx yΩ).mp hyker

private theorem exists_commuting_elem_not_mem {Z K : Subgroup G} {x : G}
    (hKcard : 27 ≤ Nat.card K) (hZcard : Nat.card Z = 3)
    (hxZ : x ∉ Z) (hx3 : x ^ 3 = 1) (hZx : ∀ z ∈ Z, z * x = x * z)
    (hKx : ∀ y ∈ K, y * x = x * y) (hKexp : ∀ y ∈ K, y ^ 3 = 1) :
    ∃ y ∈ K, y ∉ Subgroup.zpowers x ⊔ Z ∧ y * x = x * y ∧ y ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h1 => hxZ (h1 ▸ Z.one_mem)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hxord]
  let H : Subgroup G := Subgroup.zpowers x ⊔ Z
  have hinf : Subgroup.zpowers x ⊓ Z = ⊥ := by
    by_contra hne
    have hne1 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ≠ 1 := fun h =>
      hne (Subgroup.eq_bot_of_card_eq _ h)
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Z) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hZcard] at hdvd
    have hcard3 : Nat.card ↥(Subgroup.zpowers x ⊓ Z) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hZle : Z ≤ Subgroup.zpowers x := by
      have hEq : Subgroup.zpowers x ⊓ Z = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard3, hZcard])
      calc Z = Subgroup.zpowers x ⊓ Z := hEq.symm
        _ ≤ Subgroup.zpowers x := inf_le_left
    have hxle : Subgroup.zpowers x ≤ Z := by
      have hEq : Subgroup.zpowers x ⊓ Z = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard3, Nat.card_zpowers, hxord])
      calc Subgroup.zpowers x = Subgroup.zpowers x ⊓ Z := hEq.symm
        _ ≤ Z := inf_le_right
    exact hxZ (hxle (Subgroup.mem_zpowers x))
  have hcommZX : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbx : Commute b x := hZx b hb
    exact (hbx.zpow_right n).eq.symm
  have hHcard : Nat.card H = 9 := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) Z hcommZX).1
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hxord, hZcard] at hcard
    simpa [H] using hcard
  have hKH : ¬ K ≤ H := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hHcard] at hcard
    omega
  obtain ⟨y, hyK, hyH⟩ := SetLike.not_le_iff_exists.mp hKH
  exact ⟨y, hyK, hyH, hKx y hyK, hKexp y hyK⟩

private theorem exists_elemAbelian_nine_inf_eq_bot_of_central {R Z : Subgroup G}
    (hZc : Z ≤ Subgroup.centralizer (R : Set G))
    (hZexp : ∀ z ∈ Z, z ^ 3 = 1) (hZcard : Nat.card Z ≤ 3)
    (hcomm : ⁅R, R⁆ ≤ Z) (hcube : ∀ x ∈ R, x ^ 3 ∈ Z)
    (hbig : 81 * Nat.card Z ≤ Nat.card R) :
    ∃ F : Subgroup G, F ≤ R ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ F ⊓ Z = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZbot : Z = ⊥
  · have hRexp : ∀ x ∈ R, x ^ 3 = 1 := fun x hx => by
      have := hcube x hx
      rwa [hZbot, Subgroup.mem_bot] at this
    obtain ⟨F, hFR, hFelem, hFcard⟩ :=
      exists_elemAbelian_nine_of_exp_three hRexp (by simpa [hZbot] using hbig)
    exact ⟨F, hFR, hFelem, hFcard, by rw [hZbot, inf_bot_eq]⟩
  · have hZcard3 : Nat.card Z = 3 :=
      card_eq_three_of_pow_three_eq_one hZexp hZcard hZbot
    obtain ⟨Ω, hΩR, hΩexp, hΩ81⟩ :=
      exists_cube_kernel_large hZc hZexp hZcard3 hcomm hcube hbig
    have hx : ∃ x ∈ Ω, x ∉ Z := by
      by_contra h
      push Not at h
      have hle : Ω ≤ Z := h
      have hcard := Subgroup.card_le_of_le hle
      rw [hZcard3] at hcard
      omega
    obtain ⟨x, hxΩ, hxZ⟩ := hx
    have hxR : x ∈ R := hΩR hxΩ
    have hx3 : x ^ 3 = 1 := hΩexp x hxΩ
    have hZx : ∀ z ∈ Z, z * x = x * z := fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZc hz) x hxR).symm
    obtain ⟨K, hKΩ, hKcard, hKx⟩ :=
      exists_commuting_subgroup_large hΩR hZc hcomm hZcard3 hxΩ hΩ81
    have hKexp : ∀ y ∈ K, y ^ 3 = 1 := fun y hy => hΩexp y (hKΩ hy)
    let H : Subgroup G := Subgroup.zpowers x ⊔ Z
    obtain ⟨y, hyK, hyH, hyx, hy3⟩ :=
      exists_commuting_elem_not_mem hKcard hZcard3 hxZ hx3 hZx hKx hKexp
    have hyH' : y ∉ H := hyH
    have hyR : y ∈ R := hΩR (hKΩ hyK)
    have hxH : x ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hZH : Z ≤ H := le_sup_right
    obtain ⟨F, hFelem, hFcard, -, -, hFZ, hFmin⟩ :=
      CFSG.Quasithin.He15.exists_elemAbelian_nine (C := H) (L := Z) (x := y) (a := x)
        hy3 hx3 hyH' hxH hxZ hZH hyx
    exact ⟨F, hFmin R hyR hxR, hFelem, hFcard, hFZ⟩

theorem le_normalizer_quotientCentralizer {N L : Subgroup G} (Q : Subgroup ↥L)
    [Q.Characteristic] (hLN : L ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    N ≤ Subgroup.normalizer (quotientCentralizer N L Q hLN hNL : Set G) := by
  let K : Subgroup ↥N := (conjQuotAction N L Q hLN hNL).ker
  have hXN : quotientCentralizer N L Q hLN hNL ≤ N := quotientCentralizer_le N L Q hLN hNL
  have hsub : (quotientCentralizer N L Q hLN hNL).subgroupOf N = K := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨n, hnx, hnker⟩ := (mem_quotientCentralizer Q hLN hNL).mp hx
      have hnx' : n = x := Subtype.ext hnx
      rwa [← hnx']
    · intro hx
      exact (mem_quotientCentralizer Q hLN hNL).mpr ⟨x, rfl, hx⟩
  haveI : K.Normal := MonoidHom.normal_ker _
  have hnorm : ((quotientCentralizer N L Q hLN hNL).subgroupOf N).Normal :=
    hsub ▸ inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mp hnorm

private theorem pow_three_eq_one_of_isPGroup_card_le_three {H : Subgroup G}
    (hH : IsPGroup 3 H) (hcard : Nat.card H ≤ 3) : ∀ z ∈ H, z ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have hdvd : 9 ∣ Nat.card H := by
      rw [hk]
      exact pow_dvd_pow 3 h2
    have h9le : 9 ≤ Nat.card H := Nat.le_of_dvd (by norm_num) hdvd
    omega
  intro z hz
  interval_cases k
  · have hcard1 : Nat.card H = 1 := by
      rw [hk]
      norm_num
    haveI : Subsingleton ↥H := (Nat.card_eq_one_iff_unique.mp hcard1).1
    have hz1 : (⟨z, hz⟩ : ↥H) = 1 := Subsingleton.elim _ _
    have hz1' : z = 1 := congrArg Subtype.val hz1
    rw [hz1']
    norm_num
  · have hcard3 : Nat.card H = 3 := by
      rw [hk]
      norm_num
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : ↥H))
    simpa [hcard3] using congrArg Subtype.val h

private theorem le_centralizer_of_isPGroup_card_le_three {R R0 : Subgroup G}
    (hR0R : R0 ≤ R) (hR : IsPGroup 3 R) (hR0 : IsPGroup 3 R0)
    (hnormal : (R0.subgroupOf R).Normal) (hcard : Nat.card R0 ≤ 3) :
    R0 ≤ Subgroup.centralizer (R : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR0
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have hdvd : 9 ∣ Nat.card R0 := by
      rw [hk]
      exact pow_dvd_pow 3 h2
    have h9le : 9 ≤ Nat.card R0 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  intro x hx
  interval_cases k
  · have hbot : R0 = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [hk]
      norm_num
    rw [hbot] at hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact Subgroup.one_mem _
  · have hcard3 : Nat.card R0 = 3 := by
      rw [hk]
      norm_num
    haveI : Fact (IsPGroup 3 ↥R) := ⟨hR⟩
    have hcent : R0.subgroupOf R ≤ Subgroup.center ↥R :=
      CFSG.normal_subgroup_card_eq_prime_le_center (G := ↥R) (R0.subgroupOf R)
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0R).toEquiv, hcard3])
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hx' : (⟨x, hR0R hx⟩ : ↥R) ∈ R0.subgroupOf R := hx
    have hcomm := Subgroup.mem_center_iff.mp (hcent hx') (⟨r, hr⟩ : ↥R)
    exact congrArg Subtype.val hcomm

private theorem sup_eq_of_isPGroup_relIndex {R L Z : Subgroup G} (hRZ : R ≤ Z) (hLZ : L ≤ Z)
    (hR3 : ¬ 3 ∣ R.relIndex Z) (hL3 : ∃ k, L.relIndex Z = 3 ^ k) : R ⊔ L = Z := by
  obtain ⟨k, hk⟩ := hL3
  let M : Subgroup G := R ⊔ L
  have hRM : R ≤ M := le_sup_left
  have hLM : L ≤ M := le_sup_right
  have hMZ : M ≤ Z := sup_le hRZ hLZ
  have hmulR := Subgroup.relIndex_mul_relIndex (H := R) (K := M) (L := Z) hRM hMZ
  have hmulL := Subgroup.relIndex_mul_relIndex (H := L) (K := M) (L := Z) hLM hMZ
  have hdvdR : M.relIndex Z ∣ R.relIndex Z := ⟨R.relIndex M, by rw [← hmulR, mul_comm]⟩
  have hdvdL : M.relIndex Z ∣ L.relIndex Z := ⟨L.relIndex M, by rw [← hmulL, mul_comm]⟩
  have hcop3 : Nat.Coprime (R.relIndex Z) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hR3).symm
  have hcop : Nat.Coprime (R.relIndex Z) (L.relIndex Z) := by
    rw [hk]
    exact hcop3.pow_right k
  have hgcd : Nat.gcd (R.relIndex Z) (L.relIndex Z) = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hcop
  have hM1 : M.relIndex Z = 1 :=
    Nat.dvd_one.mp (by rw [← hgcd]; exact Nat.dvd_gcd hdvdR hdvdL)
  exact le_antisymm hMZ (Subgroup.relIndex_eq_one.mp hM1)

private theorem sup_P_A_eq_sup_A_inf {A X P : Subgroup G} (hPle : P ≤ A ⊔ X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    P ⊔ A = A ⊔ ((P ⊔ A) ⊓ X) := by
  have hPAle : P ⊔ A ≤ A ⊔ X := sup_le hPle le_sup_left
  have hd := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer
    (S := A) (T := X) (U := P ⊔ A) (le_sup_right : A ≤ P ⊔ A) hAX
  have hXR : (P ⊔ A) ⊓ (A ⊔ X) = P ⊔ A := inf_eq_left.mpr hPAle
  simpa only [hXR] using hd

theorem exists_elemAbelian_nine_inf_eq_bot {N₁ A P : Subgroup G} (hAN : A ≤ N₁)
    (hNA : N₁ ≤ Subgroup.normalizer (A : Set G)) (hP : IsPGroup 3 P)
    (hPle : P ≤ A ⊔ Xhat N₁ A hAN hNA) (hcube : ∀ x ∈ P, x ^ 3 ∈ A)
    (hcomm : ⁅P, P⁆ ≤ A) (h81 : 81 * Nat.card ↥(P ⊓ A) ≤ Nat.card P)
    (h9 : ¬ 9 ∣ Nat.card (oTwoZStar A)) :
    ∃ F : Subgroup G, F ≤ Xhat N₁ A hAN hNA ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      F ⊓ A = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let PA : Subgroup G := P ⊔ A
  let X : Subgroup G := Xhat N₁ A hAN hNA
  let Z0 : Subgroup G := PA ⊓ X
  let L : Subgroup G := A ⊓ X
  have hXleN1 : X ≤ N₁ := quotientCentralizer_le N₁ A _ hAN hNA
  have hXN : N₁ ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_quotientCentralizer (N := N₁) (L := A) (CFSG.pPrimeCore 3 ↥A) hAN hNA
  have hPleN1 : P ≤ N₁ := hPle.trans (sup_le hAN hXleN1)
  have hPAN1 : PA ≤ N₁ := sup_le hPleN1 hAN
  have hXNA : X ≤ Subgroup.normalizer (A : Set G) := hXleN1.trans hNA
  have hPNA : P ≤ Subgroup.normalizer (A : Set G) :=
    hPle.trans (sup_le Subgroup.le_normalizer hXNA)
  have hZ0N1 : Z0 ≤ N₁ := inf_le_left.trans hPAN1
  have hZ0NA : Z0 ≤ Subgroup.normalizer (A : Set G) := hZ0N1.trans hNA
  have hPAeq : PA = A ⊔ Z0 := by
    have hAX : A ≤ Subgroup.normalizer (X : Set G) := hAN.trans hXN
    simpa [PA, Z0] using sup_P_A_eq_sup_A_inf (X := X) hPle hAX
  have hAnormPA : PA ≤ Subgroup.normalizer (A : Set G) := hPAN1.trans hNA
  haveI hAnormPA' : (A.subgroupOf PA).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : A ≤ PA)).mpr hAnormPA
  haveI hP0norm' : ((A ⊓ P).subgroupOf P).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hPNA g.2) n).mp hn.1,
      P.mul_mem (P.mul_mem g.2 hn.2) (P.inv_mem g.2)⟩
  have hLZ0 : L ≤ Z0 := le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hLZ0norm : Z0 ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hZ0NA hz) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hXN (hZ0N1 hz)) x).mp hx.2⟩
  haveI : (L.subgroupOf Z0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLZ0).mpr hLZ0norm
  have hZ0A : Z0 ⊔ A = PA := by
    rw [sup_comm]
    exact hPAeq.symm
  have hLsub : L.subgroupOf Z0 = A.subgroupOf Z0 := by
    ext x
    change (x : G) ∈ L ↔ (x : G) ∈ A
    simp only [L, Subgroup.mem_inf]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, (Subgroup.mem_inf.mp x.2).2⟩
  haveI hA0norm : (A.subgroupOf Z0).Normal := hLsub ▸ inferInstance
  have hLZ0 : L ≤ Z0 := le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hZ0A : Z0 ⊔ A = PA := by
    rw [sup_comm]
    exact hPAeq.symm
  have hZ0Ainf : Z0 ⊓ A = L := by
    ext x
    constructor
    · rintro ⟨hxZ, hxA⟩
      exact ⟨hxA, (Subgroup.mem_inf.mp hxZ).2⟩
    · intro hx
      exact ⟨⟨Subgroup.mem_sup_right hx.1, hx.2⟩, hx.1⟩
  have hrelPA : L.relIndex Z0 = (A ⊓ P).relIndex P := by
    have h1 := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := Z0) (K := A) hZ0NA
    have h2 := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := P) (K := A) hPNA
    have h1' : A.relIndex PA = L.relIndex Z0 := by
      rw [← hZ0Ainf, ← h1.2, hZ0A]
    have h2' : A.relIndex PA = (A ⊓ P).relIndex P := by
      rw [show A ⊓ P = P ⊓ A from inf_comm A P, ← h2.2]
    exact h1'.symm.trans h2'
  have hP0rel3 : ∃ k, (A ⊓ P).relIndex P = 3 ^ k := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hdvd : (A ⊓ P).relIndex P ∣ Nat.card P := by
      refine ⟨Nat.card ↥(A ⊓ P), ?_⟩
      have := Subgroup.relIndex_mul_card (A ⊓ P) P
      rw [inf_eq_left.mpr inf_le_right] at this
      exact this.symm
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (by simpa [hn] using hdvd)
    exact ⟨k, hk⟩
  obtain ⟨R, hRsyl, -⟩ :=
    CFSG.Quasithin.exists_isSylowIn_ge 3 (H := Z0) (P := ⊥) bot_le IsPGroup.of_bot
  have hRleZ0 : R ≤ Z0 := hRsyl.le
  have hRpgroup : IsPGroup 3 R := hRsyl.isPGroup
  have hRnot3 : ¬ 3 ∣ R.relIndex Z0 := hRsyl.not_dvd_relIndex
  have hRlePA : R ≤ PA := hRleZ0.trans inf_le_left
  have hRleX : R ≤ X := hRleZ0.trans inf_le_right
  have hRleN1 : R ≤ N₁ := hRleZ0.trans hZ0N1
  have hRA : R ≤ Subgroup.normalizer (A : Set G) := hRleN1.trans hNA
  let R0 : Subgroup G := R ⊓ A
  have hR0leR : R0 ≤ R := inf_le_left
  have hR0leA : R0 ≤ A := inf_le_right
  have hR0leX : R0 ≤ X := hR0leR.trans hRleX
  have hR0L : R0 = R ⊓ L := by
    ext x
    constructor
    · rintro ⟨hxR, hxA⟩
      exact ⟨hxR, ⟨hxA, hRleX hxR⟩⟩
    · rintro ⟨hxR, hxL⟩
      exact ⟨hxR, hxL.1⟩
  have hL3 : ∃ k, L.relIndex Z0 = 3 ^ k := by
    rw [hrelPA]
    exact hP0rel3
  have hM0eq : R ⊔ L = Z0 := sup_eq_of_isPGroup_relIndex hRleZ0 hLZ0 hRnot3 hL3
  let M0 : Subgroup G := R ⊔ L
  have hM0Z0 : M0 ≤ Z0 := by
    rw [show M0 = R ⊔ L from rfl, hM0eq]
  have hRLnorm : R ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro r hr x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hRA hr) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hXN (hRleN1 hr)) x).mp hx.2⟩
  have hrelR : L.relIndex M0 = R0.relIndex R := by
    have h := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := R) (K := L) hRLnorm
    rw [show M0 = R ⊔ L from rfl, h.2, ← hR0L]
  have hRcard : Nat.card ↥R = L.relIndex M0 * Nat.card ↥R0 := by
    have hmul := Subgroup.relIndex_mul_card R0 R
    rw [inf_eq_left.mpr hR0leR] at hmul
    calc Nat.card ↥R = R0.relIndex R * Nat.card ↥R0 := hmul.symm
      _ = L.relIndex M0 * Nat.card ↥R0 := by rw [← hrelR]
  have hLidxM0 : L.relIndex Z0 = L.relIndex M0 := by
    rw [← hM0eq]
  have hP0rel81 : 81 ≤ (A ⊓ P).relIndex P := by
    have hPcard : Nat.card ↥P = (A ⊓ P).relIndex P * Nat.card ↥(A ⊓ P) := by
      have hmul := Subgroup.relIndex_mul_card (A ⊓ P) P
      rw [inf_eq_left.mpr inf_le_right] at hmul
      exact hmul.symm
    rw [hPcard, inf_comm] at h81
    exact Nat.le_of_mul_le_mul_right h81 Nat.card_pos
  have hLidx81 : 81 ≤ L.relIndex M0 := by
    rw [← hLidxM0, hrelPA]
    exact hP0rel81
  have hRbig : 81 * Nat.card R0 ≤ Nat.card R := by
    rw [hRcard]
    exact Nat.mul_le_mul_right _ hLidx81
  have hR0leOA : R0 ≤ oTwoZStar A := by
    rw [← quotientCentralizer_inf_eq_oTwoZStar hAN hNA]
    exact le_inf hR0leX hR0leA
  have hR0pg : IsPGroup 3 R0 :=
    (hRpgroup.to_subgroup (R0.subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hR0leR)
  have hR0card : Nat.card R0 ≤ 3 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR0pg
    have hm1 : m ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ m := by omega
      have hdvd : 9 ∣ Nat.card R0 := by
        rw [hm]
        exact pow_dvd_pow 3 h2
      have h9dvd : 9 ∣ Nat.card (oTwoZStar A) :=
        hdvd.trans (Subgroup.card_dvd_of_le hR0leOA)
      exact h9 h9dvd
    rw [hm]
    have hpow : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
    simpa using hpow
  have hR0exp : ∀ z ∈ R0, z ^ 3 = 1 :=
    pow_three_eq_one_of_isPGroup_card_le_three hR0pg hR0card
  have hR0normal : (R0.subgroupOf R).Normal := by
    have hRnormR0 : R ≤ Subgroup.normalizer (R0 : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro r hr x hx
      exact ⟨R.mul_mem (R.mul_mem hr (hR0leR hx)) (R.inv_mem hr),
        (Subgroup.mem_normalizer_iff.mp (hRA hr) x).mp (hR0leA hx)⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hR0leR).mpr hRnormR0
  have hR0cent : R0 ≤ Subgroup.centralizer (R : Set G) :=
    le_centralizer_of_isPGroup_card_le_three hR0leR hRpgroup hR0pg hR0normal hR0card
  let πA : ↥PA →* (↥PA ⧸ A.subgroupOf PA) := QuotientGroup.mk' (A.subgroupOf PA)
  let φ : ↥R →* (↥PA ⧸ A.subgroupOf PA) := πA.comp (Subgroup.inclusion hRlePA)
  have hφker : φ.ker = R0.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (⟨(r : G), hRlePA r.2⟩ : ↥PA) : ↥PA ⧸ A.subgroupOf PA) = 1 ↔
      (r : G) ∈ R0
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨r.2, h⟩
    · intro h
      exact h.2
  have hPAexp : ∀ g : ↥PA, (QuotientGroup.mk' (A.subgroupOf PA) g) ^ 3 = 1 := by
    intro g
    have hset : (g : G) ∈ (P : Set G) * (A : Set G) := by
      have hsup : ((P ⊔ A : Subgroup G) : Set G) = (P : Set G) * (A : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right P A hPNA
      rw [← hsup]
      exact g.2
    obtain ⟨p, hp, a, ha, hpa⟩ := hset
    let pPA : ↥PA := ⟨p, Subgroup.mem_sup_left hp⟩
    have hpg : pPA⁻¹ * g ∈ A.subgroupOf PA := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((pPA⁻¹ * g : ↥PA) : G) = p⁻¹ * (g : G) := rfl
      rw [hcoe]
      have ha' : p⁻¹ * (g : G) = a := by rw [← hpa]; group
      rw [ha']
      exact ha
    have hg : QuotientGroup.mk' (A.subgroupOf PA) pPA =
        QuotientGroup.mk' (A.subgroupOf PA) g := (QuotientGroup.eq).mpr hpg
    change (QuotientGroup.mk pPA : ↥PA ⧸ A.subgroupOf PA) =
      (QuotientGroup.mk g : ↥PA ⧸ A.subgroupOf PA) at hg
    change (QuotientGroup.mk g : ↥PA ⧸ A.subgroupOf PA) ^ 3 = 1
    rw [← hg, ← QuotientGroup.mk_pow]
    change (QuotientGroup.mk (pPA ^ 3) : ↥PA ⧸ A.subgroupOf PA) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hcube p hp
  have hPAbelian : ∀ g h : ↥PA,
      (QuotientGroup.mk' (A.subgroupOf PA) g) * (QuotientGroup.mk' (A.subgroupOf PA) h) =
      (QuotientGroup.mk' (A.subgroupOf PA) h) * (QuotientGroup.mk' (A.subgroupOf PA) g) := by
    intro g h
    have hsetg : (g : G) ∈ (P : Set G) * (A : Set G) := by
      have hsup : ((P ⊔ A : Subgroup G) : Set G) = (P : Set G) * (A : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right P A hPNA
      rw [← hsup]
      exact g.2
    have hseth : (h : G) ∈ (P : Set G) * (A : Set G) := by
      have hsup : ((P ⊔ A : Subgroup G) : Set G) = (P : Set G) * (A : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right P A hPNA
      rw [← hsup]
      exact h.2
    obtain ⟨p, hp, a, ha, hpa⟩ := hsetg
    obtain ⟨q, hq, b, hb, hqb⟩ := hseth
    let pPA : ↥PA := ⟨p, Subgroup.mem_sup_left hp⟩
    let qPA : ↥PA := ⟨q, Subgroup.mem_sup_left hq⟩
    have hgp : QuotientGroup.mk' (A.subgroupOf PA) pPA =
        QuotientGroup.mk' (A.subgroupOf PA) g := by
      apply (QuotientGroup.eq).mpr
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((pPA⁻¹ * g : ↥PA) : G) = p⁻¹ * (g : G) := rfl
      rw [hcoe]
      have ha' : p⁻¹ * (g : G) = a := by rw [← hpa]; group
      rw [ha']
      exact ha
    have hhq : QuotientGroup.mk' (A.subgroupOf PA) qPA =
        QuotientGroup.mk' (A.subgroupOf PA) h := by
      apply (QuotientGroup.eq).mpr
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((qPA⁻¹ * h : ↥PA) : G) = q⁻¹ * (h : G) := rfl
      rw [hcoe]
      have hb' : q⁻¹ * (h : G) = b := by rw [← hqb]; group
      rw [hb']
      exact hb
    rw [← hgp, ← hhq]
    have hpqA : ⁅p, q⁆ ∈ A := hcomm (Subgroup.commutator_mem_commutator hp hq)
    have hcommmk : ⁅QuotientGroup.mk' (A.subgroupOf PA) pPA,
        QuotientGroup.mk' (A.subgroupOf PA) qPA⁆ = 1 := by
      rw [← map_commutatorElement]
      change (QuotientGroup.mk ⁅pPA, qPA⁆ : ↥PA ⧸ A.subgroupOf PA) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hpqA
    exact (commutatorElement_eq_one_iff_commute.mp hcommmk).eq
  have hRcube : ∀ x ∈ R, x ^ 3 ∈ R0 := by
    intro x hx
    have hxφ : φ ⟨x, hx⟩ ^ 3 = 1 := by
      have hcoe : (Subgroup.inclusion hRlePA ⟨x, hx⟩ : ↥PA) = ⟨x, hRlePA hx⟩ :=
        Subtype.ext rfl
      have := hPAexp ⟨x, hRlePA hx⟩
      simpa [φ, πA, hcoe] using this
    have hmem : (⟨x, hx⟩ : ↥R) ^ 3 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hxφ]
    rw [hφker] at hmem
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hRcomm : ⁅R, R⁆ ≤ R0 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxyR : ⁅x, y⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
    have hmem : (⟨⁅x, y⁆, hxyR⟩ : ↥R) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hEq : (⟨⁅x, y⁆, hxyR⟩ : ↥R) =
          ⁅(⟨x, hx⟩ : ↥R), (⟨y, hy⟩ : ↥R)⁆ := by
        apply Subtype.ext
        rfl
      rw [hEq, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (hPAbelian ⟨x, hRlePA hx⟩ ⟨y, hRlePA hy⟩)
    rw [hφker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨F, hFR, hFelem, hFcard, hFZ⟩ :=
    exists_elemAbelian_nine_inf_eq_bot_of_central hR0cent hR0exp hR0card hRcomm hRcube hRbig
  have hFX : F ≤ Xhat N₁ A hAN hNA := hFR.trans hRleX
  have hFA : F ⊓ A = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hzR0 : z ∈ R0 := ⟨hFR hz.1, hz.2⟩
    have hzFZ : z ∈ F ⊓ R0 := ⟨hz.1, hzR0⟩
    rw [hFZ, Subgroup.mem_bot] at hzFZ
    simpa using hzFZ
  exact ⟨F, hFX, hFelem, hFcard, hFA⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
