module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Layer

variable {H : Type} [Group H] [Finite H]

theorem le_of_pPrimePerfect_of_le_sup {p : ℕ} [Fact p.Prime] {Q I Θ : Subgroup H}
    (hQ : S10.PPrimePerfect p Q) (hQI : Q ≤ Subgroup.normalizer (I : Set H))
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set H)) (hΘ : Nat.Coprime (Nat.card Θ) p)
    (hQle : Q ≤ I ⊔ Θ) : Q ≤ I := by
  set Mx : Subgroup H := I ⊔ Q with hMx
  have hIM : I ≤ Mx := le_sup_left
  have hQM : Q ≤ Mx := le_sup_right
  have hMN : Mx ≤ Subgroup.normalizer (I : Set H) := sup_le Subgroup.le_normalizer hQI
  have hIn : (I.subgroupOf Mx).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).2 hMN
  have hMX : Mx ≤ I ⊔ Θ := sup_le le_sup_left hQle
  have hc1 := S10.coprime_relIndex_of_normal hIΘ hΘ hIM hMX hIn
  have hc2 : Nat.Coprime (I.relIndex Q) p :=
    Nat.Coprime.coprime_dvd_left (S10.relIndex_dvd_of_le_of_normal hQM hIn) hc1
  have hIQn : ((I ⊓ Q).subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro q hq
    exact S10.mem_normalizer_inf_of (hQI hq) (Subgroup.le_normalizer hq)
  have hc3 : Nat.Coprime ((I ⊓ Q).relIndex Q) p := by
    rw [Subgroup.inf_relIndex_right]
    exact hc2
  have h := hQ (I ⊓ Q) inf_le_right hIQn hc3
  rw [← h]
  exact inf_le_left

private theorem glaPLayer_eq_of_forall_le {p : ℕ} (hp : p.Prime) {Y Y' : Subgroup H} (hYY : Y ≤ Y')
    (hn : (Y.subgroupOf Y').Normal) (hall : ∀ Q, GLAPComponent p Y' Q → Q ≤ Y) :
    GLAPLayer p Y' = GLAPLayer p Y := by
  unfold GLAPLayer
  apply le_antisymm
  · exact sSup_le fun Q hQ => le_sSup (glaPComponent_of_le hp hQ (hall Q hQ) hYY)
  · exact sSup_le fun Q hQ =>
      le_sSup (CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp hYY hn hQ)

private theorem map_inf_comap {M : Type} [Group M] (π : H →* M) (A : Subgroup H) (B : Subgroup M) :
    (A ⊓ B.comap π).map π = A.map π ⊓ B := by
  apply le_antisymm
  · rintro _ ⟨a, ⟨ha, hb⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hb⟩
  · rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
    exact ⟨a, ⟨ha, hb⟩, rfl⟩

theorem map_glaPLayer_inf_normalizer {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (π : H →* M) (hkp : ¬ p ∣ Nat.card π.ker) {C I S : Subgroup H} (hIC : I ≤ C)
    (hCI : C ≤ Subgroup.normalizer (I : Set H))
    (hCN : (C ⊓ Subgroup.normalizer (S : Set H)).map π =
      C.map π ⊓ Subgroup.normalizer ((S.map π : Subgroup M) : Set M)) :
    (GLAPLayer p (I ⊓ Subgroup.normalizer (S : Set H))).map π =
      GLAPLayer p (I.map π ⊓ Subgroup.normalizer ((S.map π : Subgroup M) : Set M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set NS : Subgroup H := Subgroup.normalizer (S : Set H) with hNS
  set Y : Subgroup H := I ⊓ NS with hY
  set Y' : Subgroup H := (C ⊓ NS) ⊓ (I.map π).comap π with hY'
  set Θ : Subgroup H := C ⊓ π.ker with hΘ
  have hYY' : Y ≤ Y' :=
    le_inf (inf_le_inf_right _ hIC) (inf_le_left.trans (Subgroup.le_comap_map π I))
  have hY'C : Y' ≤ C := inf_le_left.trans inf_le_left
  have hY'N : Y' ≤ NS := inf_le_left.trans inf_le_right
  have hn : (Y.subgroupOf Y').Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYY']
    intro y hy
    exact S10.mem_normalizer_inf_of (hCI (hY'C hy)) (Subgroup.le_normalizer (hY'N hy))
  have hall : ∀ Q, GLAPComponent p Y' Q → Q ≤ Y := by
    intro Q hQ
    have hQY' : Q ≤ Y' := hQ.1
    have hIΘ : I ≤ Subgroup.normalizer (Θ : Set H) := by
      intro i hi
      exact S10.mem_normalizer_inf_of (Subgroup.le_normalizer (hIC hi))
        (by rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker π)]
            exact Subgroup.mem_top _)
    have hΘcop : Nat.Coprime (Nat.card Θ) p := by
      refine Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) ?_
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hkp))
    have hQle : Q ≤ I ⊔ Θ := by
      intro q hq
      have hqY' := hQY' hq
      obtain ⟨i, hi, hiq⟩ : π q ∈ I.map π := hqY'.2
      have hk : i⁻¹ * q ∈ Θ := ⟨C.mul_mem (C.inv_mem (hIC hi)) (hY'C hqY'), by
        show i⁻¹ * q ∈ π.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hiq, inv_mul_cancel]⟩
      have e : q = i * (i⁻¹ * q) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hi hk
    have hQI : Q ≤ I :=
      le_of_pPrimePerfect_of_le_sup (S10.pPrimePerfect_of_glaPComponent hQ)
        (hQY'.trans (hY'C.trans hCI)) hIΘ hΘcop hQle
    exact le_inf hQI (hQY'.trans hY'N)
  have hlayer : GLAPLayer p Y' = GLAPLayer p Y := glaPLayer_eq_of_forall_le hp hYY' hn hall
  have himg : Y'.map π = I.map π ⊓ Subgroup.normalizer ((S.map π : Subgroup M) : Set M) := by
    rw [hY', map_inf_comap, hCN]
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans (Subgroup.map_mono hIC)) inf_le_right) inf_le_left
  rw [← hlayer, S267.map_glaPLayer hp π hkp Y', himg]

end Layer

section Normal

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_centralizer_barX_of_le {p : ℕ} {X L : Subgroup G} (hLsn : IsSubnormal L X)
    {a : G} (ha : a ∈ X) (haL : (⁅L, Subgroup.zpowers a⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩ ∈
      Subgroup.centralizer (barX p X L : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  have hlL : (l : G) ∈ L := hl
  obtain ⟨w, hw, hwc⟩ :=
    HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hLsn
      (haL (Subgroup.commutator_mem_commutator hlL (Subgroup.mem_zpowers a)))
  have hw' : w = ⁅l, ⟨a, ha⟩⁆ := Subtype.ext (by simpa [commutatorElement_def] using hwc)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅l, ⟨a, ha⟩⁆ = 1 := by
    rw [← hw']
    exact (QuotientGroup.eq_one_iff _).mpr hw
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1

theorem centMod_of_mk_mem_centralizer {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) {a : G} (ha : a ∈ X)
    (hc : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩ ∈
      Subgroup.centralizer (barX p X L : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    CentMod p L a := by
  have hN : a ∈ Subgroup.normalizer (L : Set G) :=
    GLTheoremB.mem_normalizer_of_barX_normalizes hp le_rfl hL ha (Subgroup.le_normalizer ha)
      (Subgroup.centralizer_le_normalizer _ hc)
  refine ⟨hN, Subgroup.commutator_le.mpr fun l hl b hb => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hlX : l ∈ X := hL.1 hl
  have hcL : ⁅l, a ^ k⁆ ∈ L := by
    have h1 : a ^ k * l⁻¹ * (a ^ k)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hN k) _).mp (L.inv_mem hl)
    rw [commutatorElement_def]
    simpa only [mul_assoc] using L.mul_mem hl h1
  have hcO : ⁅l, a ^ k⁆ ∈ GLAPPrimeCoreOf p X := by
    refine ⟨⁅(⟨l, hlX⟩ : ↥X), ⟨a, ha⟩ ^ k⁆, (QuotientGroup.eq_one_iff _).mp ?_, ?_⟩
    · have hcomm' : Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩)
          (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩) :=
        Subgroup.mem_centralizer_iff.mp hc _ ⟨⟨l, hlX⟩, hl, rfl⟩
      show QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅(⟨l, hlX⟩ : ↥X), ⟨a, ha⟩ ^ k⁆ = 1
      rw [map_commutatorElement, map_zpow, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm'.zpow_right k
    · simp [commutatorElement_def]
  have h2 := HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp X L ⟨hcO, hcL⟩
  rwa [inf_eq_right.mpr hL.1] at h2

theorem centMod_of_glaPComponent_ne {p : ℕ} (hp : p.Prime) {X L J : Subgroup G}
    (hL : GLAPComponent p X L) (hJ : GLAPComponent p X J) (hne : J ≠ L) {j : G} (hj : j ∈ J) :
    CentMod p L j := by
  have hjX : j ∈ X := hJ.1 hj
  have hbar : barX p X L ≠ barX p X J := fun h => hne (glaPComponent_unique hL hJ h).symm
  have hcomm : ⁅barX p X L, barX p X J⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hL.2.2.1 hJ.2.2.1 hbar
  refine centMod_of_mk_mem_centralizer hp hL hjX ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hjb : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hjX⟩ ∈ barX p X J :=
    ⟨⟨j, hjX⟩, hj, rfl⟩
  have h1 := Subgroup.commutator_mem_commutator hl hjb
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem le_normalizer_of_elemAbelian {p : ℕ} (hp : p.Prime) {x : G} {L E : Subgroup G}
    (hL : GLAPComponent p (cx x) L) (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEp : p < Nat.card E)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p) :
    cx x ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  by_contra hgN
  have hX : GLBConj g (cx x) = cx x :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have hL' : GLAPComponent p (cx x) (GLBConj g L) := by
    have h := glaPComponent_gLBConj hL g
    rwa [hX] at h
  have hne : GLBConj g L ≠ L := fun h => hgN (mem_normalizer_iff_gLBConj_eq.2 h)
  have hE'L' : GLBConj g E ≤ GLBConj g L := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g hEL
  have hE' : IsElemAbelian p (GLBConj g E) := CFSG.SectionRank.isElemAbelian_map hE _
  have hcard : Nat.card (GLBConj g E) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have h := hrk1 (GLBConj g E) hE' (hE'L'.trans hL'.1)
    (fun a ha => centMod_of_glaPComponent_ne hp hL hL' hne (hE'L' ha))
  omega

end Normal

end CFSG.LocalAnalysis.GLTheoremA.H301
