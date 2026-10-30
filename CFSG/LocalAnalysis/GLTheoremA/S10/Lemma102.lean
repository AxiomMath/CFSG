module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S6.I183Diag
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Lemma102Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i1131 : I1131At G p
  i1122 : I1122IsoAt G p
  chev2 : Chev2DownAt G p
  dich : FieldDichotomyAt G p
  aut : AutCalcAt G p
  indep : FieldCentIndepAt G p
  cent : CentTD4At G
  i148 : I148At G
  i155 : I155At G p

theorem Lemma102Inputs.toR2 {G : Type} [Group G] [Finite G] {p : ℕ} (h : Lemma102Inputs G p) :
    R2Inputs G p := ⟨h.aut, h.indep, h.cent⟩

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma102_twoPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : twoPart a ≤ twoPart b := by
  have ha : a ≠ 0 := ne_zero_of_dvd_ne_zero hb h
  unfold twoPart
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.factorization_le_iff_dvd ha hb).2 h 2)

@[expose] def lemma102_conjHomL {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L where
  toFun l := ⟨g⁻¹ * (l : G) * g, by
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (l : G)).1 l.2
    rwa [inv_inv] at h⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem lemma102_conjHomL_val {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    ((lemma102_conjHomL hg l : ↥L) : G) = g⁻¹ * (l : G) * g := rfl

theorem lemma102_mem_glaPPrimeCore_iff {p : ℕ} {H : Subgroup G} {x : G} (hx : x ∈ H) :
    (⟨x, hx⟩ : ↥H) ∈ GLAPPrimeCore p ↥H ↔ x ∈ GLAPPrimeCoreOf p H := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = ⟨x, hx⟩ := Subtype.ext hzx
    rw [← this]
    exact hz

theorem lemma102_conjHomL_mem_glaPPrimeCore {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    GLAPPrimeCore p ↥L ≤ (GLAPPrimeCore p ↥L).comap (lemma102_conjHomL hg) := by
  intro m hm
  rw [Subgroup.mem_comap]
  have hmO : (m : G) ∈ GLAPPrimeCoreOf p L := (lemma102_mem_glaPPrimeCore_iff m.2).1 hm
  have hN : g⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    Subgroup.inv_mem _ (normalizer_le_normalizer_glaPPrimeCoreOf p L hg)
  have hc : g⁻¹ * (m : G) * g ∈ GLAPPrimeCoreOf p L := by
    have h := (Subgroup.mem_normalizer_iff.1 hN (m : G)).1 hmO
    rwa [inv_inv] at h
  have hy : ((lemma102_conjHomL hg m : ↥L) : G) = g⁻¹ * (m : G) * g := lemma102_conjHomL_val hg m
  exact (lemma102_mem_glaPPrimeCore_iff (lemma102_conjHomL hg m : ↥L).2).2 (by rw [hy]; exact hc)

@[expose] def lemma102_conjQ (p : ℕ) {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    PQuot p L →* PQuot p L :=
  QuotientGroup.map (GLAPPrimeCore p ↥L) (GLAPPrimeCore p ↥L) (lemma102_conjHomL hg)
    (lemma102_conjHomL_mem_glaPPrimeCore hg)

theorem lemma102_conjQ_mk {p : ℕ} {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (l : ↥L) : lemma102_conjQ p hg (QuotientGroup.mk l) = QuotientGroup.mk (lemma102_conjHomL hg l) := rfl

theorem lemma102_indRel_iff_conjQ {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (q q' : PQuot p L) :
    indRel p L g q q' ↔ lemma102_conjQ p hg q = q' := by
  constructor
  · rintro ⟨l, l', rfl, rfl, hll⟩
    rw [lemma102_conjQ_mk]
    congr 1
    exact Subtype.ext (by rw [lemma102_conjHomL_val]; exact hll.symm)
  · intro h
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l, lemma102_conjHomL hg l, rfl, ?_, lemma102_conjHomL_val hg l⟩
    rw [← h, lemma102_conjQ_mk]

@[expose] def lemma102_fixSub (p : ℕ) {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    Subgroup (PQuot p L) :=
  MonoidHom.eqLocus (lemma102_conjQ p hg) (MonoidHom.id _)

theorem lemma102_centCard2_eq_fixSub (p : ℕ) {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    centCard2 p L g = twoPart (Nat.card (lemma102_fixSub p hg)) := by
  unfold centCard2
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
  rw [lemma102_indRel_iff_conjQ hg q q]
  exact Iff.rfl

theorem lemma102_centCard2_le_card2 (p : ℕ) {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : centCard2 p L g ≤ card2 p L := by
  rw [lemma102_centCard2_eq_fixSub p hg]
  exact lemma102_twoPart_le_of_dvd (Nat.card_pos (α := PQuot p L)).ne' (Subgroup.card_subgroup_dvd_card _)

theorem r2_le_card2 (p : ℕ) (B L : Subgroup G) : r2 p B L ≤ card2 p L := by
  classical
  unfold r2
  by_cases h1 : R2TD4 p B L
  · rw [if_pos h1]
    obtain ⟨hp3, -⟩ := h1
    subst hp3
    exact Nat.sqrt_le_self _
  · rw [if_neg h1]
    by_cases h2 : ∃ b ∈ B, FieldOn p b L
    · rw [dif_pos h2]
      exact lemma102_centCard2_le_card2 p h2.choose_spec.2.1
    · rw [dif_neg h2]

theorem exists_r2prop_of_lt {B L : Subgroup G} (h : r2 p B L < card2 p L) : ∃ b ∈ B, R2Prop p b L := by
  classical
  unfold r2 at h
  by_cases h1 : R2TD4 p B L
  · obtain ⟨hp3, htd, b, hbB, -, hbn⟩ := h1
    subst hp3
    exact ⟨b, hbB, Or.inr ⟨rfl, htd, hbn⟩⟩
  · rw [if_neg h1] at h
    by_cases h2 : ∃ b ∈ B, FieldOn p b L
    · obtain ⟨b, hbB, hbf⟩ := h2
      exact ⟨b, hbB, Or.inl hbf⟩
    · rw [dif_neg h2] at h
      exact absurd h (lt_irrefl _)

theorem ne_one_of_nonInner {g : G} {L : Subgroup G} (h : NonInner p g L) : g ≠ 1 := by
  rintro rfl
  refine h.2 ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
  simp [Subgroup.one_mem]

theorem r2_ge_cent (hin : R2Inputs G p) {X L B : Subgroup G} (hL : GLAPComponent p X L)
    (hch : IsChevSimple 2 (PSimple p L)) (hB : IsElemAbelian p B) {b : G} (hbB : b ∈ B)
    (hprop : R2Prop p b L) : centCard2 p L b ≤ r2 p B L := by
  classical
  unfold r2
  by_cases h1 : R2TD4 p B L
  · rw [if_pos h1]
    obtain ⟨hp3, htd, -⟩ := h1
    subst hp3
    rcases hprop with hf | ⟨-, -, hn⟩
    · exact absurd hf (hin.aut.td4_not_field X L b hL rfl htd)
    · exact hin.cent X L b hL hch htd (hB.2 b hbB) hn
  · rw [if_neg h1]
    have hf : FieldOn p b L := by
      rcases hprop with hf | ⟨hp3, htd, hn⟩
      · exact hf
      · exact absurd ⟨hp3, htd, b, hbB, ne_one_of_nonInner hn, hn⟩ h1
    have h2 : ∃ b ∈ B, FieldOn p b L := ⟨b, hbB, hf⟩
    rw [dif_pos h2]
    exact (hin.indep X L B hL hch hB b hbB _ h2.choose_spec.1 hf h2.choose_spec.2).le

theorem r2_eq_cent (hin : R2Inputs G p) {X L B : Subgroup G} (hL : GLAPComponent p X L)
    (hch : IsChevSimple 2 (PSimple p L)) (hB : IsElemAbelian p B) {b : G} (hbB : b ∈ B)
    (hf : FieldOn p b L) (hn : ¬ R2TD4 p B L) : r2 p B L = centCard2 p L b := by
  classical
  unfold r2
  rw [if_neg hn]
  have h2 : ∃ b ∈ B, FieldOn p b L := ⟨b, hbB, hf⟩
  rw [dif_pos h2]
  exact hin.indep X L B hL hch hB _ h2.choose_spec.1 b hbB h2.choose_spec.2 hf

theorem lemma102_closureIn_mono_right {I H H' : Subgroup G} (h : H ≤ H') : closureIn I H ≤ closureIn I H' := by
  rw [closureIn_eq_iSup_gLBConj, closureIn_eq_iSup_gLBConj]
  exact iSup₂_le fun g hg => le_biSup (fun g => GLBConj g I) (h hg)

theorem lemma102_glaPLayer_le {p : ℕ} (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ h => h.1

theorem lemma102_I_le {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {B B' L L' : Subgroup G}
    {x x' : G} (hrel : PumpRel p (B, x, L) (B', x', L')) :
    Ipart p L x' ≤ closureIn L' (Subgroup.zpowers x) ∧
      (x ∈ Subgroup.normalizer (L' : Set G) → Ipart p L x' ≤ L') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hx, hL⟩, ⟨hB', hx', hL'c⟩, hxB', -, hx'B', hx'L, hL'⟩ := hrel
  have hB'Cx' : B' ≤ Subgroup.centralizer ({x'} : Set G) :=
    isElemAbelian_le_centralizer hB'.1 hx'B'
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, -, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := Ipart p L x' with hI
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hICx : I ≤ Subgroup.centralizer ({x} : Set G) := hIL.trans hL.1
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Subgroup.centralizer ({x'} : Set G) ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf _) hIc
  have hKx' : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1)
  have hxCx' : Subgroup.zpowers x ≤ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.zpowers_le.2 (hB'Cx' hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G _ hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'.1 hxB') I hI2
  set J := closureIn I (GLAPLayer p (Subgroup.centralizer ({x'} : Set G))) with hJdef
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj _ _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Subgroup.centralizer ({x'} : Set G) :=
    hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p J K := fun K hK =>
    glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hL'𝒞 : L' ∈ 𝒞 := by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL' ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'.1
  have hconj : ∀ K ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e L' = K :=
    fun K hK => h𝒞tr L' hL'𝒞 K hK
  refine ⟨?_, fun hxN => ?_⟩
  · refine hIJ.trans ?_
    rw [hJ]
    refine iSup₂_le fun K hK => ?_
    obtain ⟨e, he, rfl⟩ := hconj K hK
    rw [closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun b => GLBConj b L') he
  · have huniq : ∀ K ∈ 𝒞, K = L' := fun K hK => by
      obtain ⟨e, he, hee⟩ := hconj K hK
      have heN : e ∈ Subgroup.normalizer (L' : Set G) := Subgroup.zpowers_le.2 hxN he
      rw [← hee, mem_normalizer_iff_gLBConj_eq.1 heN]
    have hJL' : J ≤ L' := by
      rw [hJ]
      exact iSup₂_le fun K hK => (huniq K hK).le
    exact hIJ.trans hJL'

theorem lemma102_ker_le {p : ℕ} (hp : p.Prime) {I K : Subgroup G} (hIK : I ≤ K) :
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK)).ker ≤
      GLAPPrimeCore p ↥I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set ψ : ↥I →* PQuot p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK) with hψ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (Subgroup.inclusion hIK) ≤ GLAPPrimeCore p ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have : ψ y = 1 := hy
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hcard : Nat.card (ψ.ker.map (Subgroup.inclusion hIK)) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIK)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  exact le_sSup ⟨inferInstance, hcop⟩

theorem lemma102_inf_le {p : ℕ} (hp : p.Prime) {H K : Subgroup G} (hHK : H ≤ K) :
    H ⊓ GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p H := by
  rintro x ⟨hxH, hxO⟩
  have hmem : (⟨x, hxH⟩ : ↥H) ∈ ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp
      (Subgroup.inclusion hHK)).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact (lemma102_mem_glaPPrimeCore_iff (hHK hxH)).2 hxO
  exact (lemma102_mem_glaPPrimeCore_iff hxH).1 (lemma102_ker_le hp hHK hmem)

theorem lemma102_closureIn_mono_left {I I' H : Subgroup G} (h : I ≤ I') : closureIn I H ≤ closureIn I' H := by
  rw [closureIn_eq_iSup_gLBConj, closureIn_eq_iSup_gLBConj]
  exact iSup₂_le fun g hg => (gLBConj_mono (g := g) h).trans (le_biSup (fun g => GLBConj g I') hg)

theorem lemma102_closureIn_le_of {L H K : Subgroup G} (hLK : L ≤ K) (hHK : H ≤ K) : closureIn L H ≤ K := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun g hg => ?_
  intro y hy
  have h1 : g * y * g⁻¹ ∈ L := mem_gLBConj.1 hy
  have h2 : g⁻¹ * (g * y * g⁻¹) * g ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem (hHK hg)) (hLK h1)) (hHK hg)
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h2

theorem lemma102_card_dvd_range {p : ℕ} (hp : p.Prime) {I K : Subgroup G} (hIK : I ≤ K) :
    Nat.card (PQuot p I) ∣ Nat.card
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK)).range := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set ψ : ↥I →* PQuot p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK) with hψ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (Subgroup.inclusion hIK) ≤ GLAPPrimeCore p ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have : ψ y = 1 := hy
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hcard : Nat.card (ψ.ker.map (Subgroup.inclusion hIK)) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIK)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  have hker : ψ.ker ≤ GLAPPrimeCore p ↥I := le_sSup ⟨inferInstance, hcop⟩
  have h1 : Nat.card (PQuot p I) ∣ Nat.card (↥I ⧸ ψ.ker) := Subgroup.index_dvd_of_le hker
  have h2 : Nat.card (↥I ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  exact h1.trans (h2 ▸ dvd_refl _)

theorem lemma102_card_dvd_of_le {p : ℕ} (hp : p.Prime) {I K : Subgroup G} (hIK : I ≤ K) :
    Nat.card (PQuot p I) ∣ Nat.card (PQuot p K) :=
  (lemma102_card_dvd_range hp hIK).trans (Subgroup.card_subgroup_dvd_card _)

theorem step_I_comp (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) :
    GLAPComponent p (closureIn L' (Subgroup.zpowers x) ⊓ cx x) (Ipart p L x') := by
  obtain ⟨hIJ, -⟩ := lemma102_I_le hc.ctx.prime hin.i183 hc.ctx.kProper hc.ctx.simple
    hc.ctx.nonabelian hrel
  have hP := (pumpRel_facts hc.ctx.prime hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian
    hrel).2.1
  have hIC : Ipart p L x' ≤ cx x :=
    (lemma102_glaPLayer_le _).trans (inf_le_left.trans (hrel.1.2.2).1)
  exact glaPComponent_of_le hc.ctx.prime hP (le_inf hIJ hIC)
    (inf_le_inf_right _ (lemma102_closureIn_mono_right (Subgroup.zpowers_le.2 hrel.2.2.1)))

theorem step_chev2 (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) (h2 : IsChevSimple 2 (PSimple p L')) :
    IsChevSimple 2 (PSimple p L) := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := hrel.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hS' := hrel.2.1
  have hL'c : GLAPComponent p (Subgroup.centralizer ({x'} : Set G)) L' := hS'.2.2
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hS'.1.1 hx'B'
  obtain ⟨-, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hIdiag := (pumpRel_facts hp hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian
    hrel).2.1
  obtain ⟨eS⟩ := nonempty_pSimple_congr eIL
  suffices hI : IsChevSimple 2 (PSimple p (Ipart p L x')) from
    chev_isChevSimple_of_mulEquiv eS.symm hI
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  ·
    have hJ : GLAPComponent p (L' ⊓ Subgroup.centralizer ({x} : Set G)) (Ipart p L x') := by
      have h := step_I_comp hc hin hrel
      rwa [closureIn_eq_self (Subgroup.zpowers_le.2 hxN)] at h
    have hKx' : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) :=
      isKGroup_of_isKProper hc.ctx.kProper
        (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hS'.2.1.2.1)
    have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1.1
    exact hin.chev2 hp hc.ctx.odd (Subgroup.centralizer ({x'} : Set G)) L' x hKx' hL'c hxp hxN h2
      (Ipart p L x') hJ
  ·
    obtain ⟨e1⟩ := hin.i1122 B' x' L' x hS'.1 hS'.2.1 hL'c hxB' hxN (Ipart p L x') hIdiag
    obtain ⟨hsimp, hnab⟩ := chev_pSimple_simple_nonabelian hp hL'c
    haveI := hsimp
    have hZ : Subgroup.center (PSimple p L') = ⊥ := chev_center_eq_bot_of_simple_nonabelian hnab
    have hcard : Nat.card (Subgroup.center (PQuot p (Ipart p L x'))) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr e1).toEquiv, hZ]
      simp
    have hZI : Subgroup.center (PQuot p (Ipart p L x')) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
    have e2 : PSimple p (Ipart p L x') ≃* PQuot p (Ipart p L x') :=
      (QuotientGroup.quotientMulEquivOfEq hZI).trans QuotientGroup.quotientBot
    exact chev_isChevSimple_of_mulEquiv (e2.trans e1) h2

theorem step_dvd (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) :
    Nat.card (PQuot p L) ∣ Nat.card (PQuot p L') := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := hrel.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hrel.2.1.1.1 hx'B'
  obtain ⟨-, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hPI : Nat.card (PQuot p L) = Nat.card (PQuot p (Ipart p L x')) :=
    Nat.card_congr eIL.symm.toEquiv
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  · rw [hPI]
    exact lemma102_card_dvd_of_le hp ((lemma102_I_le hp hin.i183 hc.ctx.kProper hc.ctx.simple
      hc.ctx.nonabelian hrel).2 hxN)
  · have hIdiag := (pumpRel_facts hp hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian hrel).2.1
    obtain ⟨e⟩ := hin.i1122 B' x' L' x hrel.2.1.1 hrel.2.1.2.1 hrel.2.1.2.2 hrel.2.2.1 hxN
      (Ipart p L x') hIdiag
    rw [hPI, Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card _

theorem step_card2 (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) : card2 p L ≤ card2 p L' :=
  lemma102_twoPart_le_of_dvd Nat.card_pos.ne' (step_dvd hc hin hrel)

theorem lemma102_perm_fixed {p : ℕ} (hp : p.Prime) {α : Type} [Finite α] (σ : Equiv.Perm α)
    (hσ : σ ^ p = 1) (hcop : ¬ p ∣ Nat.card α) : ∃ a, σ a = a := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hH : IsPGroup p (Subgroup.zpowers σ) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [_root_.pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, _root_.mul_comm,
      zpow_mul, zpow_natCast, hσ, one_zpow]
    rfl
  obtain ⟨a, ha⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card α hcop
  refine ⟨a, ?_⟩
  have := ha ⟨σ, Subgroup.mem_zpowers σ⟩
  simpa using this


theorem lemma102_coprime_lift {p : ℕ} (hp : p.Prime) {A : Type} [Group A] [Finite A] {b : A}
    (hb : b ^ p = 1) {N : Subgroup A} (hbN : ∀ n ∈ N, b⁻¹ * n * b ∈ N)
    (hbN' : ∀ n ∈ N, b * n * b⁻¹ ∈ N) (hN : ¬ p ∣ Nat.card N) {a : A}
    (ha : ∃ m ∈ N, b⁻¹ * a * b = a * m) : ∃ n ∈ N, b⁻¹ * (a * n) * b = a * n := by
  classical
  obtain ⟨m, hm, hbam⟩ := ha
  let σ : Equiv.Perm A :=
    { toFun := fun x => b⁻¹ * x * b, invFun := fun x => b * x * b⁻¹,
      left_inv := fun x => by simp [mul_assoc], right_inv := fun x => by simp [mul_assoc] }
  have hit : ∀ k : ℕ, ∀ x : A, (σ ^ k) x = b⁻¹ ^ k * x * b ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show b⁻¹ ^ k * (b⁻¹ * x * b) * b ^ k = _
      rw [pow_succ, pow_succ']
      group
  have hσp : σ ^ p = 1 := by
    ext x
    rw [hit, Equiv.Perm.one_apply]
    have hbinv : b⁻¹ ^ p = 1 := by rw [inv_pow, hb, inv_one]
    rw [hbinv, hb]
    group
  have ha' : a = b * (a * m) * b⁻¹ := by rw [← hbam]; group
  have hba : b * a * b⁻¹ = a * (b * m⁻¹ * b⁻¹) := by
    calc b * a * b⁻¹ = (b * (a * m) * b⁻¹) * (b * m⁻¹ * b⁻¹) := by group
      _ = a * (b * m⁻¹ * b⁻¹) := by rw [← ha']
  let P : A → Prop := fun g => ∃ n ∈ N, g = a * n
  have hP : ∀ g, P g ↔ P (σ g) := by
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨m * (b⁻¹ * n * b), N.mul_mem hm (hbN n hn), ?_⟩
      show b⁻¹ * (a * n) * b = a * (m * (b⁻¹ * n * b))
      rw [show b⁻¹ * (a * n) * b = (b⁻¹ * a * b) * (b⁻¹ * n * b) by group, hbam]
      group
    · rintro ⟨n, hn, h⟩
      have h' : b⁻¹ * g * b = a * n := h
      have hg2 : g = b * (a * n) * b⁻¹ := by rw [← h']; group
      have hbm : b * m⁻¹ * b⁻¹ ∈ N := hbN' m⁻¹ (N.inv_mem hm)
      have hbn : b * n * b⁻¹ ∈ N := hbN' n hn
      refine ⟨(b * m⁻¹ * b⁻¹) * (b * n * b⁻¹), N.mul_mem hbm hbn, ?_⟩
      rw [hg2]
      calc b * (a * n) * b⁻¹ = (b * a * b⁻¹) * (b * n * b⁻¹) := by group
        _ = a * ((b * m⁻¹ * b⁻¹) * (b * n * b⁻¹)) := by rw [hba]; group
  have hcard : Nat.card {x // P x} = Nat.card N := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun n : N => (⟨a * (n : A), (n : A), n.2, rfl⟩ : {x // P x})) ⟨?_, ?_⟩).symm
    · intro n₁ n₂ h
      have h2 := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel h2)
    · rintro ⟨x, hx⟩
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨⟨n, hn⟩, rfl⟩
  let τ : Equiv.Perm {x // P x} := σ.subtypePerm (fun x => (hP x).symm)
  have hτk : ∀ k : ℕ, ∀ x : {x // P x}, ((τ ^ k) x).1 = (σ ^ k) x.1 := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, Equiv.Perm.mul_apply]
      rfl
  have hτ : τ ^ p = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [hτk, hσp, Equiv.Perm.one_apply, Equiv.Perm.one_apply]
  obtain ⟨s, hs⟩ := lemma102_perm_fixed hp τ hτ (by rw [hcard]; exact hN)
  have hs' : σ s.1 = s.1 := by
    have := congrArg Subtype.val hs
    simpa [τ] using this
  obtain ⟨n, hn, hsn⟩ := s.2
  refine ⟨n, hn, ?_⟩
  have hfix : b⁻¹ * s.1 * b = s.1 := hs'
  rw [hsn] at hfix
  exact hfix

theorem lemma102_fix_dvd {p : ℕ} (hp : p.Prime) {I₀ L' : Subgroup G} {b : G}
    (hIL : I₀ ≤ L') (hb0 : b ∈ Subgroup.normalizer (L' : Set G))
    (hb1 : b ∈ Subgroup.normalizer (I₀ : Set G)) (hbp : b ^ p = 1) :
    Nat.card (lemma102_fixSub p hb1) ∣ Nat.card (lemma102_fixSub p hb0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set O : Subgroup G := GLAPPrimeCoreOf p I₀ with hOdef
  have hbO : b ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p I₀ hb1
  have hbO1 : ∀ n ∈ O, b⁻¹ * n * b ∈ O := fun n hn => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbO) n).1 hn
    rwa [inv_inv] at this
  have hbO2 : ∀ n ∈ O, b * n * b⁻¹ ∈ O := fun n hn =>
    (Subgroup.mem_normalizer_iff.1 hbO n).1 hn
  have hOcard : ¬ p ∣ Nat.card O := by
    have h1 : Nat.card O = Nat.card (GLAPPrimeCore p ↥I₀) :=
      Subgroup.card_map_of_injective (Subtype.val_injective)
    have h2 : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥I₀)) := CFSG.pPrimeCore_coprime_card
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h2
  have hOI : O ≤ I₀ := Subgroup.map_subtype_le _
  let Fix : Subgroup ↥I₀ := MonoidHom.eqLocus (lemma102_conjHomL hb1) (MonoidHom.id _)
  let ψ : ↥I₀ →* PQuot p L' :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L')).comp (Subgroup.inclusion hIL)
  have hker : ψ.ker ≤ GLAPPrimeCore p ↥I₀ := lemma102_ker_le hp hIL
  let ι : Fix →* PQuot p L' := ψ.comp Fix.subtype
  let θ : Fix →* PQuot p I₀ := (QuotientGroup.mk' (GLAPPrimeCore p ↥I₀)).comp Fix.subtype
  have hθfix : ∀ g : Fix, θ g ∈ lemma102_fixSub p hb1 := by
    intro g
    show lemma102_conjQ p hb1 (QuotientGroup.mk (g : ↥I₀)) = QuotientGroup.mk (g : ↥I₀)
    rw [lemma102_conjQ_mk]
    congr 1
    exact Subtype.ext (by rw [lemma102_conjHomL_val]; exact congrArg Subtype.val g.2)
  let θ' : Fix →* lemma102_fixSub p hb1 := θ.codRestrict (lemma102_fixSub p hb1) hθfix
  have hιle : ι.range ≤ lemma102_fixSub p hb0 := by
    rintro _ ⟨g, rfl⟩
    show lemma102_conjQ p hb0 (QuotientGroup.mk (Subgroup.inclusion hIL (g : ↥I₀))) =
      QuotientGroup.mk (Subgroup.inclusion hIL (g : ↥I₀))
    rw [lemma102_conjQ_mk]
    congr 1
    exact Subtype.ext (by rw [lemma102_conjHomL_val]; exact congrArg Subtype.val g.2)
  have hθs : Function.Surjective θ' := by
    rintro ⟨q, hq⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : lemma102_conjQ p hb1 (QuotientGroup.mk a) = QuotientGroup.mk a := hq
    rw [lemma102_conjQ_mk, QuotientGroup.eq] at hq'
    have hm : (((lemma102_conjHomL hb1 a)⁻¹ * a : ↥I₀) : G) ∈ GLAPPrimeCoreOf p I₀ :=
      (lemma102_mem_glaPPrimeCore_iff ((lemma102_conjHomL hb1 a)⁻¹ * a : ↥I₀).2).1 hq'
    have hm' : ((lemma102_conjHomL hb1 a : ↥I₀) : G)⁻¹ * (a : G) ∈ O := by
      have e : (((lemma102_conjHomL hb1 a)⁻¹ * a : ↥I₀) : G) = ((lemma102_conjHomL hb1 a : ↥I₀) : G)⁻¹ * (a : G) :=
        rfl
      rw [← e]
      exact hm
    rw [lemma102_conjHomL_val] at hm'
    have hfixeq : b⁻¹ * (a : G) * b = (a : G) * ((b⁻¹ * (a : G) * b)⁻¹ * (a : G))⁻¹ := by group
    obtain ⟨n, hn, hfix⟩ := lemma102_coprime_lift hp hbp hbO1 hbO2 hOcard
      ⟨((b⁻¹ * (a : G) * b)⁻¹ * (a : G))⁻¹, O.inv_mem hm', hfixeq⟩
    have hw : (a : G) * n ∈ I₀ := I₀.mul_mem a.2 (hOI hn)
    have hgF : (⟨(a : G) * n, hw⟩ : ↥I₀) ∈ Fix := by
      show lemma102_conjHomL hb1 ⟨(a : G) * n, hw⟩ = ⟨(a : G) * n, hw⟩
      exact Subtype.ext (by rw [lemma102_conjHomL_val]; exact hfix)
    refine ⟨⟨⟨(a : G) * n, hw⟩, hgF⟩, Subtype.ext ?_⟩
    show QuotientGroup.mk (⟨(a : G) * n, hw⟩ : ↥I₀) = QuotientGroup.mk a
    rw [QuotientGroup.eq]
    refine (lemma102_mem_glaPPrimeCore_iff ((⟨(a : G) * n, hw⟩ : ↥I₀)⁻¹ * a : ↥I₀).2).2 ?_
    show ((a : G) * n)⁻¹ * (a : G) ∈ GLAPPrimeCoreOf p I₀
    have e3 : ((a : G) * n)⁻¹ * (a : G) = n⁻¹ := by group
    rw [e3]
    exact O.inv_mem hn
  have hkerι : ι.ker ≤ θ'.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : (g : ↥I₀) ∈ ψ.ker := MonoidHom.mem_ker.2 hg
    have h2 := hker h1
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h2)
  let Θ : Fix ⧸ ι.ker →* lemma102_fixSub p hb1 := QuotientGroup.lift ι.ker θ' hkerι
  have hΘs : Function.Surjective Θ := by
    intro q
    obtain ⟨g, hg⟩ := hθs q
    exact ⟨(g : Fix ⧸ ι.ker), by rw [QuotientGroup.lift_mk]; exact hg⟩
  have h1 : Nat.card (lemma102_fixSub p hb1) ∣ Nat.card (Fix ⧸ ι.ker) := card_dvd_of_surjective Θ hΘs
  have h2 : Nat.card (Fix ⧸ ι.ker) = Nat.card ι.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv
  have h3 : Nat.card ι.range ∣ Nat.card (lemma102_fixSub p hb0) := Subgroup.card_dvd_of_le hιle
  rw [h2] at h1
  exact h1.trans h3
theorem lemma102_isPGroup_of_central {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hY : CFSG.pPrimeCore p Y = ⊥) (Z : Subgroup Y) (hZ : Z ≤ Subgroup.center Y) :
    IsPGroup p Z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  have hgc : g ∈ Subgroup.center Y := hZ hg
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  refine ⟨e, ?_⟩
  have hpe : 0 < p ^ e := pow_pos hp.pos e
  have hh : orderOf (g ^ p ^ e) = m := by
    rw [orderOf_pow' _ hpe.ne', hnm, Nat.gcd_eq_right (Dvd.intro m rfl)]
    exact Nat.mul_div_cancel_left m hpe
  set h : Y := g ^ p ^ e with hhdef
  have hcen : h ∈ Subgroup.center Y := Subgroup.pow_mem _ hgc _
  have hWn : (Subgroup.zpowers h).Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcm : Commute y h := (Subgroup.mem_center_iff.1 hcen) y
    have : y * h ^ k * y⁻¹ = h ^ k := by
      rw [(hcm.zpow_right k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) k
  have hcard : Nat.card (Subgroup.zpowers h) = m := by
    rw [Nat.card_zpowers, hh]
  have hcop : p.Coprime (Nat.card (Subgroup.zpowers h)) := by
    rw [hcard]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hle : Subgroup.zpowers h ≤ CFSG.pPrimeCore p Y := le_sSup ⟨hWn, hcop⟩
  rw [hY] at hle
  have hh1 : h = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers h))
  have hm1 : m = 1 := by rw [← hh, hh1, orderOf_one]
  rw [Subgroup.orderOf_mk, hnm, hm1, mul_one]

theorem lemma102_card_eq_card_quot_mul_card_inf {H : Type} [Group H] [Finite H] {A N : Subgroup H}
    [N.Normal] (h : A ⊔ N = ⊤) :
    Nat.card A = Nat.card (H ⧸ N) * Nat.card (A ⊓ N : Subgroup H) := by
  classical
  let f : A →* H ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ A ⊔ N := by rw [h]; exact Subgroup.mem_top y
    obtain ⟨a, ha, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk a = QuotientGroup.mk (a * n)
    rw [QuotientGroup.eq]
    simpa using hn
  have hkN : ∀ x : f.ker, (x.1 : H) ∈ N := fun x => by
    have h1 := x.2
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker : Nat.card f.ker = Nat.card (A ⊓ N : Subgroup H) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, hkN x⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, ?_⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
    rw [MonoidHom.mem_ker]
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_inf.1 y.2).2
  have hrange : Nat.card f.range = Nat.card (H ⧸ N) := by
    rw [MonoidHom.range_eq_top.2 hf]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at this
  rw [← this, mul_comm]



section Y9DiagH

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement


def lemma105NN (𝒞 : Set (Subgroup G)) (O K : Subgroup G) : Subgroup G :=
  (⨆ (C : Subgroup G) (_ : C ∈ 𝒞 ∧ C ≠ K), C) ⊔ O

theorem lemma102_core_le {p : ℕ} (H : Subgroup G) : GLAPPrimeCoreOf p H ≤ H := by
  unfold GLAPPrimeCoreOf
  exact Subgroup.map_subtype_le _

theorem lemma102_core_comp_le {p : ℕ} (hp : p.Prime) {X J C : Subgroup G} (hJX : J ≤ X)
    (hC : GLAPComponent p X C) (hCJ : C ≤ J) : GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p J := by
  have h1 : GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hC.2.1
  have h2 : GLAPPrimeCoreOf p C ≤ J := (lemma102_core_le C).trans hCJ
  exact (le_inf h1 h2).trans (idiag_core_inf_le hp hJX)

theorem lemma102_comm_mod {p : ℕ} (hp : p.Prime) {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJ : ∀ C ∈ 𝒞, C ≤ J)
    {C D : Subgroup G} (hC : C ∈ 𝒞) (hD : D ∈ 𝒞) (hne : C ≠ D) {c d : G} (hc : c ∈ C)
    (hd : d ∈ D) : ⁅d, c⁆ ∈ GLAPPrimeCoreOf p J := by
  have hle : C ≤ centModSubgroup p D := le_centModSubgroup_of_ne hp (hcomp C hC) (hcomp D hD) hne
  have h1 := (mem_centModSubgroup.1 (hle hc)).2 d hd
  exact lemma102_core_comp_le hp hJX (hcomp D hD) (hJ D hD) h1

theorem lemma102_O_normal {p : ℕ} {J : Subgroup G} {j n : G} (hj : j ∈ J)
    (hn : n ∈ GLAPPrimeCoreOf p J) : j * n * j⁻¹ ∈ GLAPPrimeCoreOf p J :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J hj) n).1 hn

theorem lemma102_comm_NN {p : ℕ} (hp : p.Prime) {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJ : ∀ C ∈ 𝒞, C ≤ J)
    {K : Subgroup G} (hK : K ∈ 𝒞) {k n : G} (hk : k ∈ K)
    (hn : n ∈ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K) :
    ⁅k, n⁆ ∈ GLAPPrimeCoreOf p J := by
  classical
  let T : Subgroup G :=
    { carrier := {n | n ∈ J ∧ ∀ k ∈ K, ⁅k, n⁆ ∈ GLAPPrimeCoreOf p J}
      one_mem' := ⟨J.one_mem, fun k _ => by
        rw [commutatorElement_one_right]; exact (GLAPPrimeCoreOf p J).one_mem⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨J.mul_mem ha.1 hb.1, fun k hk' => ?_⟩
        have e : ⁅k, a * b⁆ = ⁅k, a⁆ * (a * ⁅k, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (GLAPPrimeCoreOf p J).mul_mem (ha.2 k hk')
          (lemma102_O_normal ha.1 (hb.2 k hk'))
      inv_mem' := by
        intro a ha
        refine ⟨J.inv_mem ha.1, fun k hk' => ?_⟩
        have e : ⁅k, a⁻¹⁆ = a⁻¹ * ⁅a, k⁆ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h2 : ⁅a, k⁆ = (⁅k, a⁆)⁻¹ := (commutatorElement_inv k a).symm
        rw [h2]
        have := lemma102_O_normal (J.inv_mem ha.1) ((GLAPPrimeCoreOf p J).inv_mem (ha.2 k hk'))
        simpa [inv_inv] using this }
  have hle : lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K ≤ T := by
    refine sup_le ?_ ?_
    · refine iSup₂_le fun C hC => ?_
      intro n hnC
      refine ⟨hJ C hC.1 hnC, fun k hk' => ?_⟩
      exact lemma102_comm_mod hp hJX hcomp hJ hC.1 hK hC.2 hnC hk'  
    · intro n hn'
      have hnJ : n ∈ J := lemma102_core_le (p := p) J hn'
      refine ⟨hnJ, fun k hk' => ?_⟩
      have hkJ : k ∈ J := hJ K hK hk'
      have e : ⁅k, n⁆ = (k * n * k⁻¹) * n⁻¹ := by
        rw [commutatorElement_def]
      rw [e]
      exact (GLAPPrimeCoreOf p J).mul_mem (lemma102_O_normal hkJ hn') ((GLAPPrimeCoreOf p J).inv_mem hn')
  exact (hle hn).2 k hk


theorem lemma102_J_le_normalizer {p : ℕ} (hp : p.Prime) {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) {K : Subgroup G} (hK : K ∈ 𝒞) :
    (⨆ C ∈ 𝒞, C) ≤ Subgroup.normalizer (K : Set G) := by
  refine iSup₂_le fun C hC => ?_
  have h1 : C ≤ GLAPLayer p X := le_sSup (hcomp C hC)
  exact h1.trans (i183_glaPLayer_le_normalizer hp (hcomp K hK))

theorem lemma102_J_le_normalizer_NN {p : ℕ} (hp : p.Prime) {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJdef : J = ⨆ C ∈ 𝒞, C)
    (hJ : ∀ C ∈ 𝒞, C ≤ J) {K : Subgroup G} (hK : K ∈ 𝒞) :
    J ≤ Subgroup.normalizer ((lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K : Subgroup G) : Set G) := by
  set NN := lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K with hNN
  have hO : GLAPPrimeCoreOf p J ≤ NN := le_sup_right
  have hsub : ∀ c ∈ K, ∀ h ∈ NN, c * h * c⁻¹ ∈ NN := by
    intro c hc h hh
    have e : c * h * c⁻¹ = ⁅c, h⁆ * h := by
      rw [commutatorElement_def]; group
    rw [e]
    exact NN.mul_mem (hO (lemma102_comm_NN hp hJX hcomp hJ hK hc hh)) hh
  rw [hJdef]
  refine iSup₂_le fun C hC => ?_
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hCK : C = K
  · subst hCK
    refine ⟨fun hh => hsub c hc h hh, fun hh => ?_⟩
    have := hsub c⁻¹ (C.inv_mem hc) _ hh
    convert this using 1
    group
  · have hcN : c ∈ NN := (le_iSup₂ (f := fun (C' : Subgroup G) (_ : C' ∈ 𝒞 ∧ C' ≠ K) => C')
      C ⟨hC, hCK⟩).trans le_sup_left hc
    refine ⟨fun hh => NN.mul_mem (NN.mul_mem hcN hh) (NN.inv_mem hcN), fun hh => ?_⟩
    have := NN.mul_mem (NN.mul_mem (NN.inv_mem hcN) hh) hcN
    convert this using 1
    group


theorem lemma102_cm_conj {p : ℕ} {K : Subgroup G} {i m : G} (hi : i ∈ Subgroup.normalizer (K : Set G))
    (hm : m ∈ centModSubgroup p K) : i * m * i⁻¹ ∈ centModSubgroup p K := by
  have hN : i ∈ Subgroup.normalizer ((centModSubgroup p K : Subgroup G) : Set G) :=
    normalizer_le_normalizer_centModSubgroup p K hi
  exact (Subgroup.mem_normalizer_iff.1 hN m).1 hm

theorem lemma102_decomp {p : ℕ} {I K : Subgroup G} (hIN : I ≤ Subgroup.normalizer (K : Set G))
    (hcov : K ≤ I ⊔ centModSubgroup p K) :
    ∀ k ∈ K, ∃ i ∈ I, ∃ m ∈ centModSubgroup p K, k = i * m := by
  classical
  let S : Subgroup G :=
    { carrier := {x | ∃ i ∈ I, ∃ m ∈ centModSubgroup p K, x = i * m}
      one_mem' := ⟨1, I.one_mem, 1, (centModSubgroup p K).one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i₁, hi₁, m₁, hm₁, rfl⟩ ⟨i₂, hi₂, m₂, hm₂, rfl⟩
        have h2 : i₂⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ (hIN hi₂)
        have h3 := lemma102_cm_conj h2 hm₁
        rw [inv_inv] at h3
        refine ⟨i₁ * i₂, I.mul_mem hi₁ hi₂, i₂⁻¹ * m₁ * i₂ * m₂,
          (centModSubgroup p K).mul_mem h3 hm₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨i, hi, m, hm, rfl⟩
        have h2 : i ∈ Subgroup.normalizer (K : Set G) := hIN hi
        have h3 := lemma102_cm_conj h2 ((centModSubgroup p K).inv_mem hm)
        refine ⟨i⁻¹, I.inv_mem hi, i * m⁻¹ * i⁻¹, h3, ?_⟩
        group }
  have hle : K ≤ S := hcov.trans (sup_le
    (fun i hi => ⟨i, hi, 1, (centModSubgroup p K).one_mem, (mul_one i).symm⟩)
    (fun m hm => ⟨1, I.one_mem, m, hm, (one_mul m).symm⟩))
  intro k hk
  obtain ⟨i, hi, m, hm, hkeq⟩ := hle hk
  exact ⟨i, hi, m, hm, hkeq⟩


theorem lemma102_comm_mul_central_left {Y : Type} [Group Y] {a b z : Y} (hz : ∀ g : Y, g * z = z * g) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * (a * z)⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * (a * z)⁻¹ * b⁻¹ := by rw [hz b]
    _ = a * b * (z * (a * z)⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem lemma102_comm_mul_central_right {Y : Type} [Group Y] {a b z : Y} (hz : ∀ g : Y, g * z = z * g) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * (b * z) * a⁻¹ * (z⁻¹ * b⁻¹) := by group
    _ = a * b * (z * a⁻¹) * (z⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * z) * (z⁻¹ * b⁻¹) := by rw [← hz a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem lemma102_le_comm_sup {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    K ≤ ⁅K, K⁆ ⊔ GLAPPrimeCoreOf p K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  let f : K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmaptop : Subgroup.map f (⊤ : Subgroup K) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hf]
  have hmapcomm : Subgroup.map f ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    rw [Subgroup.map_commutator, hmaptop]
    exact hq.1
  intro k hk
  have hk' : f ⟨k, hk⟩ ∈ Subgroup.map f ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
    rw [hmapcomm]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.1 hk'
  have h1 : (QuotientGroup.mk x : PQuot p K) = QuotientGroup.mk ⟨k, hk⟩ := hfx
  have hy : x⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p K := QuotientGroup.eq.1 h1
  have hxK : x.1 ∈ ⁅K, K⁆ := by
    have hm : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e : Subgroup.map K.subtype ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⁅K, K⁆ := by
      rw [Subgroup.map_commutator, hm]
    rw [← e]
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hyO : (x⁻¹ * ⟨k, hk⟩ : K).1 ∈ GLAPPrimeCoreOf p K := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.mem_map.2 ⟨_, hy, rfl⟩
  have e : x.1 * (x⁻¹ * ⟨k, hk⟩ : K).1 = k := by simp
  have hmem := Subgroup.mul_mem _ (le_sup_left (a := ⁅K, K⁆) (b := GLAPPrimeCoreOf p K) hxK)
    (le_sup_right (a := ⁅K, K⁆) (b := GLAPPrimeCoreOf p K) hyO)
  rwa [e] at hmem


theorem lemma102_cover {p : ℕ} (hp : p.Prime) {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJdef : J = ⨆ C ∈ 𝒞, C)
    {K : Subgroup G} (hK : K ∈ 𝒞) {I : Subgroup G} (hIJ : I ≤ J)
    (hcov : K ≤ I ⊔ centModSubgroup p K) :
    J ≤ I ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJ : ∀ C ∈ 𝒞, C ≤ J := fun C hC => hJdef ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC
  have hOJ : GLAPPrimeCoreOf p J ≤ J := lemma102_core_le J
  have hNJ : lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K ≤ J :=
    sup_le (iSup₂_le fun C hC => hJ C hC.1) hOJ
  have hKJ : K ≤ J := hJ K hK
  have hOn : GLAPPrimeCoreOf p J ≤ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := le_sup_right
  have hJN : J ≤ K ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := by
    conv_lhs => rw [hJdef]
    refine iSup₂_le fun C hC => ?_
    by_cases hCK : C = K
    · subst hCK; exact le_sup_left
    · exact (((le_iSup₂ (f := fun (C' : Subgroup G) (_ : C' ∈ 𝒞 ∧ C' ≠ K) => C') C ⟨hC, hCK⟩).trans
        le_sup_left).trans le_sup_right)
  have hJnorm : J ≤ Subgroup.normalizer ((lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K : Subgroup G) : Set G) :=
    lemma102_J_le_normalizer_NN hp hJX hcomp hJdef hJ hK
  have hNn : ((lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 hJnorm
  haveI := hNn
  have hJI : J ≤ Subgroup.normalizer (K : Set G) := by
    rw [hJdef]; exact lemma102_J_le_normalizer hp hcomp hK
  have hIN : I ≤ Subgroup.normalizer (K : Set G) := hIJ.trans hJI
  have hsupJ : K.subgroupOf J ⊔ (lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K).subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKJ hNJ, Subgroup.subgroupOf_eq_top]
    exact hJN
  have hdec : ∀ x : J, ∃ c ∈ K.subgroupOf J, ∃ n ∈ (lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K).subgroupOf J,
      c * n = x := fun x =>
    Subgroup.mem_sup_of_normal_right.1 (by rw [hsupJ]; exact Subgroup.mem_top x)
  let Np : Subgroup J := (lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K).subgroupOf J
  let π : J →* J ⧸ Np := QuotientGroup.mk' Np
  have hπc : ∀ x : J, ∃ c : J, c.1 ∈ K ∧ π x = π c := by
    intro x
    obtain ⟨c, hc, n, hn, rfl⟩ := hdec x
    refine ⟨c, Subgroup.mem_subgroupOf.1 hc, ?_⟩
    have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [map_mul, h1, mul_one]
  have hcentral : ∀ m : G, m ∈ centModSubgroup p K → ∀ hmJ : m ∈ J,
      ∀ y : J ⧸ Np, y * π ⟨m, hmJ⟩ = π ⟨m, hmJ⟩ * y := by
    intro m hm hmJ y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨c, hc, hyc⟩ := hπc y'
    show π y' * π ⟨m, hmJ⟩ = π ⟨m, hmJ⟩ * π y'
    rw [hyc]
    have hmem : c.1⁻¹ ∈ K := K.inv_mem hc
    have hO1 : ⁅c.1⁻¹, m⁆ ∈ GLAPPrimeCoreOf p K := (mem_centModSubgroup.1 hm).2 c.1⁻¹ hmem
    have hO : ⁅c.1⁻¹, m⁆ ∈ GLAPPrimeCoreOf p J :=
      lemma102_core_comp_le hp hJX (hcomp K hK) hKJ hO1
    have hmInv : m⁻¹ ∈ J := J.inv_mem (hmJ)
    have hN1 : m⁻¹ * ⁅c.1⁻¹, m⁆ * m⁻¹⁻¹ ∈ (lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K) :=
      (Subgroup.mem_normalizer_iff.1 (hJnorm hmInv) _).1 (hOn hO)
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have key : ((c * ⟨m, hmJ⟩)⁻¹ * (⟨m, hmJ⟩ * c) : J).1 = m⁻¹ * ⁅c.1⁻¹, m⁆ * m⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [key]
    exact hN1
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ I ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := by
    intro a ha b hb
    obtain ⟨i, hi, m, hm, hae⟩ := lemma102_decomp hIN hcov a ha
    obtain ⟨i', hi', m', hm', hbe⟩ := lemma102_decomp hIN hcov b hb
    have hmJ : m ∈ J := by
      rw [show m = i⁻¹ * a by rw [hae]; group]
      exact J.mul_mem (J.inv_mem (hIJ hi)) (hKJ ha)
    have hmJ' : m' ∈ J := by
      rw [show m' = i'⁻¹ * b by rw [hbe]; group]
      exact J.mul_mem (J.inv_mem (hIJ hi')) (hKJ hb)
    have haJ : a ∈ J := hKJ ha
    have hbJ : b ∈ J := hKJ hb
    let aJ : J := ⟨a, haJ⟩
    let bJ : J := ⟨b, hbJ⟩
    let iJ : J := ⟨i, hIJ hi⟩
    let i'J : J := ⟨i', hIJ hi'⟩
    let mJ : J := ⟨m, hmJ⟩
    let m'J : J := ⟨m', hmJ'⟩
    have eA : aJ = iJ * mJ := Subtype.ext hae
    have eB : bJ = i'J * m'J := Subtype.ext hbe
    have hz : ∀ g : J ⧸ Np, g * π mJ = π mJ * g := hcentral m hm hmJ
    have hz' : ∀ g : J ⧸ Np, g * π m'J = π m'J * g := hcentral m' hm' hmJ'
    have hcomm_eq : ⁅π aJ, π bJ⁆ = ⁅π iJ, π i'J⁆ := by
      rw [eA, eB, map_mul, map_mul, lemma102_comm_mul_central_right hz', lemma102_comm_mul_central_left hz]
    have hpi : π ⁅aJ, bJ⁆ = π ⁅iJ, i'J⁆ := by
      rw [map_commutatorElement, map_commutatorElement, hcomm_eq]
    have hq : (⁅aJ, bJ⁆)⁻¹ * ⁅iJ, i'J⁆ ∈ Np := QuotientGroup.eq.1 hpi
    have hw : (⁅a, b⁆)⁻¹ * ⁅i, i'⁆ ∈ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := by
      have h := Subgroup.mem_subgroupOf.1 hq
      simpa [aJ, bJ, iJ, i'J, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hval : ⁅a, b⁆ = ⁅i, i'⁆ * ((⁅a, b⁆)⁻¹ * ⁅i, i'⁆)⁻¹ := by group
    have hII : ⁅i, i'⁆ ∈ I := by
      rw [commutatorElement_def]
      exact I.mul_mem (I.mul_mem (I.mul_mem hi hi') (I.inv_mem hi)) (I.inv_mem hi')
    rw [hval]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hII)
      (Subgroup.mem_sup_right ((lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K).inv_mem hw))
  have hK_comm : ⁅K, K⁆ ≤ I ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K :=
    Subgroup.commutator_le.2 fun a ha b hb => hcomm a ha b hb
  have hOK : GLAPPrimeCoreOf p K ≤ I ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := fun o ho =>
    Subgroup.mem_sup_right (hOn (lemma102_core_comp_le hp hJX (hcomp K hK) hKJ ho))
  have hKle : K ≤ I ⊔ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K :=
    (lemma102_le_comm_sup hp (hcomp K hK)).trans (sup_le hK_comm hOK)
  conv_lhs => rw [hJdef]
  refine iSup₂_le fun C hC => ?_
  by_cases hCK : C = K
  · subst hCK; exact hKle
  · intro x hx
    exact Subgroup.mem_sup_right
      (((le_iSup₂ (f := fun (C' : Subgroup G) (_ : C' ∈ 𝒞 ∧ C' ≠ K) => C') C ⟨hC, hCK⟩).trans
        le_sup_left) hx)


theorem lemma102_conj_J {𝒞 : Set (Subgroup G)} {x : G}
    (hperm : ∀ e ∈ Subgroup.zpowers x, ∀ C ∈ 𝒞, GLBConj e C ∈ 𝒞)
    {e : G} (he : e ∈ Subgroup.zpowers x) :
    GLBConj e (⨆ C ∈ 𝒞, C) ≤ ⨆ C ∈ 𝒞, C := by
  rw [idiag_gLBConj_iSup]
  refine iSup_le fun C => ?_
  rw [idiag_gLBConj_iSup]
  refine iSup_le fun hC => ?_
  exact le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) (GLBConj e C) (hperm e he C hC)

theorem lemma102_central {p : ℕ} (hp : p.Prime) {X J : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJdef : J = ⨆ C ∈ 𝒞, C)
    (hJ : ∀ C ∈ 𝒞, C ≤ J) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒞) {x : G}
    (hperm : ∀ e ∈ Subgroup.zpowers x, ∀ C ∈ 𝒞, GLBConj e C ∈ 𝒞)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C')
    {I : Subgroup G} (hIx : I ≤ Subgroup.centralizer ({x} : Set G)) {t : G} (htI : t ∈ I)
    (htN : t ∈ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K₀) :
    ∀ j ∈ J, ⁅j, t⁆ ∈ GLAPPrimeCoreOf p J := by
  classical
  have htx : ∀ e ∈ Subgroup.zpowers x, e * t = t * e := by
    intro e he
    have hc : Commute x t := (Subgroup.mem_centralizer_singleton_iff.1 (hIx htI)).symm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (hc.zpow_left k).eq
  have hJinv : ∀ e ∈ Subgroup.zpowers x, GLBConj e J = J := by
    intro e he
    apply le_antisymm
    · rw [hJdef]; exact lemma102_conj_J hperm he
    · have he' : e⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ he
      have h2 : GLBConj e⁻¹ (⨆ C ∈ 𝒞, C) ≤ ⨆ C ∈ 𝒞, C := lemma102_conj_J hperm he'
      rw [← hJdef] at h2
      calc J = GLBConj e (GLBConj e⁻¹ J) := (gLBConj_gLBConj_inv e J).symm
        _ ≤ GLBConj e J := gLBConj_mono (g := e) h2
  have hOinv : ∀ e ∈ Subgroup.zpowers x,
      GLBConj e (GLAPPrimeCoreOf p J) = GLAPPrimeCoreOf p J := by
    intro e he
    rw [← glaPPrimeCoreOf_gLBConj, hJinv e he]
  have hmem : ∀ K' ∈ 𝒞, ∀ k' ∈ K', ⁅k', t⁆ ∈ GLAPPrimeCoreOf p J := by
    intro K' hK' k' hk'
    obtain ⟨e, he, rfl⟩ := htrans K₀ hK₀ K' hK'
    have hk : e * k' * e⁻¹ ∈ K₀ := mem_gLBConj.1 hk'
    have hkt : ⁅e * k' * e⁻¹, t⁆ ∈ GLAPPrimeCoreOf p J :=
      lemma102_comm_NN hp hJX hcomp hJ hK₀ hk htN
    have hc : e * t = t * e := htx e he
    have hmapk : (MulAut.conj e⁻¹).toMonoidHom (e * k' * e⁻¹) = k' := by
      show e⁻¹ * (e * k' * e⁻¹) * e⁻¹⁻¹ = k'
      group
    have hmapt : (MulAut.conj e⁻¹).toMonoidHom t = t := by
      show e⁻¹ * t * e⁻¹⁻¹ = t
      rw [inv_inv]
      calc e⁻¹ * t * e = e⁻¹ * (t * e) := by group
        _ = e⁻¹ * (e * t) := by rw [← hc]
        _ = t := by group
    have key : (MulAut.conj e⁻¹).toMonoidHom ⁅e * k' * e⁻¹, t⁆ = ⁅k', t⁆ := by
      rw [map_commutatorElement, hmapk, hmapt]
    have hfin : (MulAut.conj e⁻¹).toMonoidHom ⁅e * k' * e⁻¹, t⁆ ∈
        GLBConj e (GLAPPrimeCoreOf p J) :=
      Subgroup.mem_map_of_mem (MulAut.conj e⁻¹).toMonoidHom hkt
    rw [hOinv e he, key] at hfin
    exact hfin
  let St : Subgroup G :=
    { carrier := {j | j ∈ J ∧ ⁅j, t⁆ ∈ GLAPPrimeCoreOf p J}
      one_mem' := ⟨J.one_mem, by
        rw [commutatorElement_one_left]; exact (GLAPPrimeCoreOf p J).one_mem⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨J.mul_mem ha.1 hb.1, ?_⟩
        have e : ⁅a * b, t⁆ = a * ⁅b, t⁆ * a⁻¹ * ⁅a, t⁆ := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
        rw [e]
        exact (GLAPPrimeCoreOf p J).mul_mem (lemma102_O_normal ha.1 hb.2) ha.2
      inv_mem' := by
        intro a ha
        refine ⟨J.inv_mem ha.1, ?_⟩
        have e : ⁅a⁻¹, t⁆ = a⁻¹ * (⁅a, t⁆)⁻¹ * a⁻¹⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [e]
        exact lemma102_O_normal (J.inv_mem ha.1) ((GLAPPrimeCoreOf p J).inv_mem ha.2) }
  have hJS : J ≤ St := by
    rw [hJdef]
    refine iSup₂_le fun C hC => fun j hj => ⟨hJ C hC hj, hmem C hC j hj⟩
  exact fun j hj => (hJS hj).2


theorem lemma102_card_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

theorem lemma102_card_inf_subgroupOf {J H K : Subgroup G} (hH : H ≤ J) (hK : K ≤ J) :
    Nat.card ↥(H.subgroupOf J ⊓ K.subgroupOf J) = Nat.card ↥(H ⊓ K : Subgroup G) := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2
        ⟨Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1,
          Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).2⟩⟩
      invFun := fun y => ⟨⟨y.1, hH (Subgroup.mem_inf.1 y.2).1⟩, Subgroup.mem_inf.2
        ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 y.2).1,
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 y.2).2⟩⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }

theorem lemma102_card_split {J A N : Subgroup G} (hAJ : A ≤ J) (hNJ : N ≤ J)
    [hN : (N.subgroupOf J).Normal] (hA : J ≤ A ⊔ N) :
    Nat.card ↥A = Nat.card (J ⧸ N.subgroupOf J) * Nat.card ↥(A ⊓ N : Subgroup G) := by
  have h1 : A.subgroupOf J ⊔ N.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAJ hNJ, Subgroup.subgroupOf_eq_top]
    exact hA
  have h2 := lemma102_card_eq_card_quot_mul_card_inf h1
  rw [lemma102_card_subgroupOf hAJ, lemma102_card_inf_subgroupOf hAJ hNJ] at h2
  exact h2

theorem lemma102_mem_core_iff {H : Subgroup G} {x : G} (hx : x ∈ H) (p : ℕ) :
    (⟨x, hx⟩ : ↥H) ∈ GLAPPrimeCore p ↥H ↔ x ∈ GLAPPrimeCoreOf p H := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = ⟨x, hx⟩ := Subtype.ext hzx
    rw [← this]
    exact hz

theorem lemma102_K0_card {p : ℕ} (hp : p.Prime) {X K₀ N : Subgroup G} (hK₀ : GLAPComponent p X K₀)
    (hON : GLAPPrimeCoreOf p K₀ ≤ N)
    (hcomm : ∀ k ∈ K₀, ∀ t ∈ K₀ ⊓ N, ⁅k, t⁆ ∈ GLAPPrimeCoreOf p K₀) :
    ∃ k : ℕ, Nat.card ↥K₀ = Nat.card (PSimple p K₀) * p ^ k * Nat.card ↥(K₀ ⊓ N : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O' : Subgroup ↥K₀ := GLAPPrimeCore p ↥K₀
  let Nt : Subgroup ↥K₀ := (K₀ ⊓ N).subgroupOf K₀
  let f : ↥K₀ →* PQuot p K₀ := QuotientGroup.mk' O'
  let g : ↥Nt →* PQuot p K₀ := f.comp Nt.subtype
  have hO'Nt : O' ≤ Nt := by
    intro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨y.2, hON ((lemma102_mem_core_iff y.2 p).1 hy)⟩
  have hTZ : g.range ≤ Subgroup.center (PQuot p K₀) := by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    have hzK : (z.1 : G) ∈ K₀ ⊓ N := Subgroup.mem_subgroupOf.1 z.2
    have h1 : ⁅k.1, (z.1 : G)⁆ ∈ GLAPPrimeCoreOf p K₀ := hcomm k.1 k.2 (z.1 : G) hzK
    have hcK : ⁅k.1, (z.1 : G)⁆ ∈ K₀ := by
      rw [commutatorElement_def]
      exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem k.2 z.1.2) (K₀.inv_mem k.2)) (K₀.inv_mem z.1.2)
    have h2 : (⟨⁅k.1, (z.1 : G)⁆, hcK⟩ : ↥K₀) ∈ O' := (lemma102_mem_core_iff hcK p).2 h1
    have hc : ⁅k, z.1⁆ ∈ O' := h2
    have key : ⁅f k, f z.1⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hc
    exact commutatorElement_eq_one_iff_mul_comm.1 key
  have hker : Nat.card g.ker = Nat.card O' := by
    apply Nat.card_congr
    exact
      { toFun := fun z => ⟨z.1.1, (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 z.2)⟩
        invFun := fun y => ⟨⟨y.1, hO'Nt y.2⟩, MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 y.2)⟩
        left_inv := fun z => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  have hgc : Nat.card g.ker * Nat.card g.range = Nat.card ↥Nt := Subgroup.card_ker_mul_card_range g
  rw [hker] at hgc
  have hNtN : Nat.card ↥Nt = Nat.card ↥(K₀ ⊓ N : Subgroup G) :=
    lemma102_card_subgroupOf (inf_le_left : K₀ ⊓ N ≤ K₀)
  have hZp : IsPGroup p (Subgroup.center (PQuot p K₀)) := by
    apply lemma102_isPGroup_of_central hp _ _ le_rfl
    exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K₀) p
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hZp
  have hTdvd : Nat.card g.range ∣ p ^ m := by
    rw [← hm]; exact Subgroup.card_dvd_of_le hTZ
  obtain ⟨j, hjm, hj⟩ := (Nat.dvd_prime_pow hp).1 hTdvd
  refine ⟨m - j, ?_⟩
  have hZcard : Nat.card ↥(Subgroup.center (PQuot p K₀)) = Nat.card g.range * p ^ (m - j) := by
    rw [hm, hj, ← pow_add, Nat.add_sub_cancel' hjm]
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot p K₀))
  have hK' : Nat.card ↥K₀ = Nat.card (PQuot p K₀) * Nat.card O' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O'
  have hPS : Nat.card (PSimple p K₀) = Nat.card (PQuot p K₀ ⧸ Subgroup.center (PQuot p K₀)) := rfl
  rw [← hNtN, ← hgc, hK', hQ, hZcard, ← hPS]
  ring

theorem lemma102_I_card {p : ℕ} (hp : p.Prime) {J I N : Subgroup G} (hIJ : I ≤ J) (hNJ : N ≤ J)
    (hON : GLAPPrimeCoreOf p J ≤ N)
    (hcent : ∀ t ∈ I ⊓ N, ∀ j ∈ J, ⁅j, t⁆ ∈ GLAPPrimeCoreOf p J) :
    ∃ r : ℕ, Nat.card ↥(I ⊓ N : Subgroup G) =
      Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) * p ^ r := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hIN : I ⊓ N ≤ J := inf_le_left.trans hIJ
  let O' : Subgroup ↥J := GLAPPrimeCore p ↥J
  let f : ↥J →* PQuot p J := QuotientGroup.mk' O'
  let ι : ↥(I ⊓ N : Subgroup G) →* ↥J := Subgroup.inclusion hIN
  let ζ : ↥(I ⊓ N : Subgroup G) →* PQuot p J := f.comp ι
  have hzker : ∀ z : ↥(I ⊓ N : Subgroup G), ζ z = 1 ↔ (z.1 : G) ∈ GLAPPrimeCoreOf p J := by
    intro z
    exact (QuotientGroup.eq_one_iff (⟨z.1, hIN z.2⟩ : ↥J)).trans
      (lemma102_mem_core_iff (hIN z.2) p)
  have hker : Nat.card ζ.ker = Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) := by
    apply Nat.card_congr
    refine
      { toFun := fun z => ⟨z.1.1, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 z.1.2).1,
          (hzker z.1).1 (MonoidHom.mem_ker.1 z.2)⟩⟩
        invFun := fun y => ⟨⟨y.1, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 y.2).1,
          hON (Subgroup.mem_inf.1 y.2).2⟩⟩, MonoidHom.mem_ker.2 ((hzker _).2 (Subgroup.mem_inf.1 y.2).2)⟩
        left_inv := fun z => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  have hTZ : ζ.range ≤ Subgroup.center (PQuot p J) := by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    have hc : ⁅j.1, z.1⁆ ∈ GLAPPrimeCoreOf p J := hcent z.1 z.2 j.1 j.2
    have hcJ : (⟨⁅j.1, z.1⁆, J.mul_mem (J.mul_mem (J.mul_mem j.2 (hIN z.2))
        (J.inv_mem j.2)) (J.inv_mem (hIN z.2))⟩ : ↥J) ∈ O' := by
      exact (lemma102_mem_core_iff _ p).2 hc
    have key : ⁅f j, f ⟨z.1, hIN z.2⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 (by exact hcJ)
    exact commutatorElement_eq_one_iff_mul_comm.1 key
  have hY : CFSG.pPrimeCore p (PQuot p J) = ⊥ := by
    exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥J) p
  have hZp : IsPGroup p ζ.range := lemma102_isPGroup_of_central hp hY ζ.range hTZ
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 hZp
  refine ⟨r, ?_⟩
  have h := Subgroup.card_ker_mul_card_range ζ
  rw [hker, hr] at h
  exact h.symm

theorem lemma102_O_le {p : ℕ} (hp : p.Prime) {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) {J : Subgroup G} (hJdef : J = ⨆ C ∈ 𝒞, C)
    {x : G}
    (hperm : ∀ e ∈ Subgroup.zpowers x, ∀ C ∈ 𝒞, GLBConj e C ∈ 𝒞)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C')
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒞) {I : Subgroup G} (hIJ : I ≤ J)
    (hIx : I ≤ Subgroup.centralizer ({x} : Set G))
    (hcov : K₀ ≤ I ⊔ centModSubgroup p K₀)
    (hcard : Nat.card (PQuot p I) = Nat.card (PSimple p K₀)) :
    GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJX : J ≤ X := hJdef ▸ iSup₂_le fun C hC => (hcomp C hC).1
  have hJ : ∀ C ∈ 𝒞, C ≤ J := fun C hC => hJdef ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC
  have hOJ : GLAPPrimeCoreOf p J ≤ J := lemma102_core_le J
  set N := lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K₀ with hN
  have hNJ : N ≤ J := sup_le (iSup₂_le fun C hC => hJ C hC.1) hOJ
  have hON : GLAPPrimeCoreOf p J ≤ N := le_sup_right
  have hKJ : K₀ ≤ J := hJ K₀ hK₀
  have hJN : J ≤ K₀ ⊔ N := by
    conv_lhs => rw [hJdef]
    refine iSup₂_le fun C hC => ?_
    by_cases hCK : C = K₀
    · subst hCK; exact le_sup_left
    · exact (((le_iSup₂ (f := fun (C' : Subgroup G) (_ : C' ∈ 𝒞 ∧ C' ≠ K₀) => C') C ⟨hC, hCK⟩).trans
        le_sup_left).trans le_sup_right)
  have hNnorm : J ≤ Subgroup.normalizer (N : Set G) := lemma102_J_le_normalizer_NN hp hJX hcomp hJdef hJ hK₀
  have hNn : (N.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 hNnorm
  haveI := hNn
  have hcovJ : J ≤ I ⊔ N := lemma102_cover hp hJX hcomp hJdef hK₀ hIJ hcov
  have hK0comm : ∀ k ∈ K₀, ∀ t ∈ K₀ ⊓ N, ⁅k, t⁆ ∈ GLAPPrimeCoreOf p K₀ := by
    intro k hk t ht
    have h1 : ⁅k, t⁆ ∈ GLAPPrimeCoreOf p J := lemma102_comm_NN hp hJX hcomp hJ hK₀ hk ht.2
    have h2 : ⁅k, t⁆ ∈ K₀ := by
      rw [commutatorElement_def]
      exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hk ht.1) (K₀.inv_mem hk)) (K₀.inv_mem ht.1)
    exact idiag_core_inf_le hp hKJ ⟨h1, h2⟩
  have hK0N : GLAPPrimeCoreOf p K₀ ≤ N :=
    (lemma102_core_comp_le hp hJX (hcomp K₀ hK₀) hKJ).trans hON
  obtain ⟨kk, hkk⟩ := lemma102_K0_card hp (hcomp K₀ hK₀) hK0N hK0comm
  have hIcent : ∀ t ∈ I ⊓ N, ∀ j ∈ J, ⁅j, t⁆ ∈ GLAPPrimeCoreOf p J := fun t ht j hj =>
    lemma102_central hp hJX hcomp hJdef hJ hK₀ hperm htrans hIx ht.1 ht.2 j hj
  obtain ⟨r, hr⟩ := lemma102_I_card hp hIJ hNJ hON hIcent
  have hQI : Nat.card ↥I = Nat.card (J ⧸ N.subgroupOf J) * Nat.card ↥(I ⊓ N : Subgroup G) :=
    lemma102_card_split hIJ hNJ hcovJ
  have hQK : Nat.card ↥K₀ = Nat.card (J ⧸ N.subgroupOf J) * Nat.card ↥(K₀ ⊓ N : Subgroup G) :=
    lemma102_card_split hKJ hNJ hJN
  have hQ : Nat.card (J ⧸ N.subgroupOf J) = Nat.card (PSimple p K₀) * p ^ kk := by
    have hpos : 0 < Nat.card ↥(K₀ ⊓ N : Subgroup G) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← hQK, hkk]
  let Pc : Subgroup ↥I := GLAPPrimeCore p ↥I
  have hIPc : Nat.card ↥I = Nat.card (PQuot p I) * Nat.card Pc :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Pc
  have hI2 : Nat.card ↥I = Nat.card (PSimple p K₀) *
      (Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) * p ^ (kk + r)) := by
    rw [hQI, hQ, hr]
    ring
  have hPc : Nat.card Pc = Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) * p ^ (kk + r) := by
    have hpos : 0 < Nat.card (PSimple p K₀) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hI2, hIPc, hcard]
  have hcop : p.Coprime (Nat.card Pc) := CFSG.pPrimeCore_coprime_card (G := ↥I) (p := p)
  have hdvd : p ^ (kk + r) ∣ Nat.card Pc := Dvd.intro_left _ hPc.symm
  have h1 : p ^ (kk + r) = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left _ hcop) hdvd
  have hPc' : Nat.card Pc = Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) := by
    rw [hPc, h1, mul_one]
  let OI : Subgroup ↥I := (I ⊓ GLAPPrimeCoreOf p J : Subgroup G).subgroupOf I
  have hOInorm : OI.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ I ⊓ GLAPPrimeCoreOf p J := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    have hg : (g : G) ∈ J := hIJ g.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact I.mul_mem (I.mul_mem g.2 (Subgroup.mem_inf.1 hn').1) (I.inv_mem g.2)
    · exact lemma102_O_normal hg (Subgroup.mem_inf.1 hn').2
  have hOIle : OI ≤ Pc := by
    have hcopO : p.Coprime (Nat.card OI) := by
      rw [show Nat.card OI = Nat.card ↥(I ⊓ GLAPPrimeCoreOf p J : Subgroup G) from
        lemma102_card_subgroupOf inf_le_left]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right :
        I ⊓ GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p J))
        (i183_coprime_card_glaPPrimeCoreOf hp J)
    exact le_sSup ⟨hOInorm, hcopO⟩
  have hOIeq : OI = Pc := Subgroup.eq_of_le_of_card_ge hOIle (by
    rw [hPc', lemma102_card_subgroupOf inf_le_left])
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hy' : y ∈ OI := by rw [hOIeq]; exact hy
  exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy')).2

end Y9DiagH

section Y9SingleH

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem lemma102_mem_sup_comm {G : Type} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  classical
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        have key : b₁ * a₂ = a₂ * b₁ := (hAB a₂ ha₂ b₁ hb₁).symm
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [key]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have key : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          have := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
          exact this
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := key.symm
          _ = a⁻¹ * b⁻¹ := rfl }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem lemma102_conj_zpowers_eq {G : Type} [Group G] {a u y : G} (hu : u ∈ Subgroup.zpowers a)
    (hy : a * y = y * a) : u * y * u⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hc : Commute a y := hy
  have := (hc.zpow_left k).eq
  rw [this]
  group

theorem lemma102_glbconj_zpowers_eq {G : Type} [Group G] {a u : G} {C : Subgroup G}
    (hC : C ≤ Subgroup.centralizer ({a} : Set G)) (hu : u ∈ Subgroup.zpowers a) :
    GLBConj u C = C := by
  have hfix : ∀ c ∈ C, ∀ w ∈ Subgroup.zpowers a, w * c * w⁻¹ = c := by
    intro c hc w hw
    have hac : a * c = c * a := Subgroup.mem_centralizer_singleton_iff.1 (hC hc) |>.symm
    exact lemma102_conj_zpowers_eq hw hac
  apply le_antisymm
  · intro y hy
    rw [mem_gLBConj] at hy
    have h1 := hfix _ hy u⁻¹ (Subgroup.inv_mem _ hu)
    have e : u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y := by group
    rw [e] at h1
    rw [h1]
    exact hy
  · intro y hy
    rw [mem_gLBConj, hfix y hy u hu]
    exact hy

theorem lemma102_index_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A D : Subgroup G} (hAD : A ≤ D) (hD : Nat.card ↥D = p ^ 2) (hA : Nat.card ↥A = p) :
    (A.subgroupOf D).index = p := by
  have h1 := Subgroup.index_mul_card (H := A.subgroupOf D)
  rw [lemma102_card_subgroupOf hAD, hA, hD] at h1
  have hp0 : 0 < p := hp.pos
  apply Nat.eq_of_mul_eq_mul_right hp0
  rw [h1]
  ring

theorem lemma102_card_zpowers_prime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {D : Subgroup G} (hD : IsElemAbelian p D) {a : G} (ha : a ∈ D) (ha1 : a ≠ 1) :
    Nat.card ↥(Subgroup.zpowers a) = p := by
  rw [Nat.card_zpowers]
  have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hD.2 a ha)
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) ha1
  · exact h

theorem lemma102_O_normalizes_sup {G : Type} [Group G] [Finite G] {p : ℕ} {J S : Subgroup G}
    (hSJ : S ≤ J) {o : G} (ho : o ∈ GLAPPrimeCoreOf p J) :
    o ∈ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ w ∈ GLAPPrimeCoreOf p J, ∀ y ∈ S ⊔ GLAPPrimeCoreOf p J,
      w * y * w⁻¹ ∈ S ⊔ GLAPPrimeCoreOf p J := by
    intro w hw y hy
    have hle : S ⊔ GLAPPrimeCoreOf p J ≤
        (S ⊔ GLAPPrimeCoreOf p J).comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (fun s hs => ?_) (fun o' ho' => ?_)
      · show w * s * w⁻¹ ∈ S ⊔ GLAPPrimeCoreOf p J
        have e : w * s * w⁻¹ = s * (s⁻¹ * w * s⁻¹⁻¹ * w⁻¹) := by group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right ?_)
        exact (GLAPPrimeCoreOf p J).mul_mem (lemma102_O_normal (J.inv_mem (hSJ hs)) hw)
          ((GLAPPrimeCoreOf p J).inv_mem hw)
      · show w * o' * w⁻¹ ∈ S ⊔ GLAPPrimeCoreOf p J
        exact Subgroup.mem_sup_right (lemma102_O_normal (lemma102_core_le (p := p) J hw) ho')
    exact hle hy
  intro y
  constructor
  · intro hy
    exact key o ho y hy
  · intro hy
    have := key o⁻¹ ((GLAPPrimeCoreOf p J).inv_mem ho) _ hy
    have e : o⁻¹ * (o * y * o⁻¹) * o⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this

end Y9SingleH

private theorem lemma102_cd_twoPart_mul_odd {m k : ℕ} (hk : Odd k) (hm : m ≠ 0) :
    twoPart (m * k) = twoPart m := by
  unfold twoPart
  have hk0 : k ≠ 0 := hk.pos.ne'
  have h2 : k.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (fun h =>
    (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 h))
  rw [Nat.factorization_mul hm hk0, Finsupp.add_apply, h2, add_zero]

private theorem lemma102_cd_fixA {A Q : Type} [Group A] [Group Q] [Finite A] [Finite Q]
    (α : A →* A) (β : Q →* Q) (θ : A →* Q) (hθ : ∀ a, θ (α a) = β (θ a))
    (hK : Odd (Nat.card θ.ker)) :
    twoPart (Nat.card (MonoidHom.eqLocus α (MonoidHom.id A))) ≤
      twoPart (Nat.card (MonoidHom.eqLocus β (MonoidHom.id Q))) := by
  set S : Subgroup A := MonoidHom.eqLocus α (MonoidHom.id A) with hS
  set Fb : Subgroup Q := MonoidHom.eqLocus β (MonoidHom.id Q) with hFb
  have hSfix : ∀ s : A, s ∈ S → α s = s := fun s hs => hs
  let f : S →* Q := θ.comp S.subtype
  have hrange : f.range ≤ Fb := by
    rintro _ ⟨s, rfl⟩
    show β (θ s) = θ s
    rw [← hθ, hSfix (s : A) s.2]
  have hker : Odd (Nat.card f.ker) := by
    have h1 : Nat.card (f.ker.map S.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective S)
    have h2 : f.ker.map S.subtype ≤ θ.ker := by
      rintro _ ⟨s, hs, rfl⟩
      exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hs)
    have h3 := Subgroup.card_dvd_of_le h2
    rw [h1] at h3
    exact hK.of_dvd_nat h3
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card S := Subgroup.card_ker_mul_card_range f
  have htwo : twoPart (Nat.card S) = twoPart (Nat.card f.range) := by
    rw [← hcard, mul_comm, lemma102_cd_twoPart_mul_odd hker Nat.card_pos.ne']
  rw [htwo]
  exact lemma102_twoPart_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le hrange)

private theorem lemma102_cd_fixB {A Q : Type} [Group A] [Group Q] [Finite A] [Finite Q]
    (α : A →* A) (β : Q →* Q) (π : A →* Q) (hπ : Function.Surjective π)
    (hπα : ∀ a, π (α a) = β (π a)) (hZc : π.ker ≤ Subgroup.center A)
    (hZo : Odd (Nat.card π.ker)) :
    twoPart (Nat.card (MonoidHom.eqLocus β (MonoidHom.id Q))) ≤
      twoPart (Nat.card (MonoidHom.eqLocus α (MonoidHom.id A))) := by
  classical
  set Fb : Subgroup Q := MonoidHom.eqLocus β (MonoidHom.id Q) with hFb
  set S : Subgroup A := MonoidHom.eqLocus α (MonoidHom.id A) with hS
  set Z : Subgroup A := π.ker with hZ
  have hFbmem : ∀ q : Q, q ∈ Fb ↔ β q = q := fun q => Iff.rfl
  set T : Subgroup A := Fb.comap π with hT
  have hTmem : ∀ a : A, a ∈ T ↔ β (π a) = π a := fun a => Iff.rfl
  have hZT : Z ≤ T := by
    intro z hz
    rw [hTmem]
    have h1 : π z = 1 := MonoidHom.mem_ker.1 hz
    rw [h1, map_one]
  have hST : S ≤ T := by
    intro s hs
    have hs' : α s = s := hs
    rw [hTmem, ← hπα, hs']
  let g : T →* Q := π.comp T.subtype
  have hgr : g.range = Fb := by
    ext q
    constructor
    · rintro ⟨t, rfl⟩
      exact (hFbmem _).2 ((hTmem _).1 t.2)
    · intro hq
      obtain ⟨a, rfl⟩ := hπ q
      exact ⟨⟨a, (hTmem a).2 ((hFbmem _).1 hq)⟩, rfl⟩
  have hgk : g.ker.map T.subtype = Z := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact MonoidHom.mem_ker.1 ht
    · intro ha
      exact ⟨⟨a, hZT ha⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 ha), rfl⟩
  have e1 : Nat.card (g.ker.map T.subtype) = Nat.card g.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective T)
  have hZk : Nat.card Z = Nat.card g.ker := by rw [← hgk]; exact e1
  have hT1 : Nat.card Z * Nat.card Fb = Nat.card T := by
    have e2 := Subgroup.card_ker_mul_card_range g
    rw [hgr] at e2
    rw [hZk]; exact e2
  have hδmem : ∀ t : T, (t : A)⁻¹ * α t ∈ Z := by
    intro t
    have ht : β (π t) = π t := (hTmem t).1 t.2
    show π ((t : A)⁻¹ * α t) = 1
    rw [map_mul, map_inv, hπα, ht, inv_mul_cancel]
  have hcen : ∀ g : A, g ∈ Z → ∀ h : A, h * g = g * h := fun g hg h =>
    (Subgroup.mem_center_iff.1 (hZc hg)) h
  let δ : T →* Z :=
    { toFun := fun t => ⟨(t : A)⁻¹ * α t, hδmem t⟩
      map_one' := by
        apply Subtype.ext
        show ((1 : T) : A)⁻¹ * α ((1 : T) : A) = 1
        simp
      map_mul' := by
        intro s t
        apply Subtype.ext
        show ((s * t : T) : A)⁻¹ * α ((s * t : T) : A) =
          ((s : A)⁻¹ * α s) * ((t : A)⁻¹ * α t)
        rw [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have hc := hcen ((s : A)⁻¹ * α s) (hδmem s) ((t : A)⁻¹)
        calc (t : A)⁻¹ * (s : A)⁻¹ * (α s * α t)
            = (t : A)⁻¹ * ((s : A)⁻¹ * α s) * α t := by group
          _ = ((s : A)⁻¹ * α s) * (t : A)⁻¹ * α t := by rw [hc]
          _ = ((s : A)⁻¹ * α s) * ((t : A)⁻¹ * α t) := by group }
  have hδk : δ.ker.map T.subtype = S := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : (t : A)⁻¹ * α t = 1 := by
        have h2 := congrArg Subtype.val (MonoidHom.mem_ker.1 ht)
        exact h2
      have h3 : α (t : A) = (t : A) := by
        calc α (t : A) = (t : A) * ((t : A)⁻¹ * α t) := by group
          _ = (t : A) := by rw [h1, mul_one]
      exact h3
    · intro ha
      have ha' : α a = a := ha
      refine ⟨⟨a, hST ha⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      apply Subtype.ext
      show (a : A)⁻¹ * α a = 1
      rw [ha', inv_mul_cancel]
  have hδc : Nat.card δ.ker = Nat.card S := by
    rw [← hδk]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective T)).symm
  have hδr : Odd (Nat.card δ.range) :=
    hZo.of_dvd_nat (Subgroup.card_subgroup_dvd_card δ.range)
  have hT2 : Nat.card δ.ker * Nat.card δ.range = Nat.card T :=
    Subgroup.card_ker_mul_card_range δ
  rw [hδc] at hT2
  have hEq : Nat.card Z * Nat.card Fb = Nat.card S * Nat.card δ.range := by
    rw [hT1, ← hT2]
  have hFbne : Nat.card Fb ≠ 0 := Nat.card_pos.ne'
  have hSne : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have h2 : twoPart (Nat.card Fb) = twoPart (Nat.card S) := by
    have e3 : twoPart (Nat.card Fb) = twoPart (Nat.card Z * Nat.card Fb) := by
      rw [mul_comm, lemma102_cd_twoPart_mul_odd hZo hFbne]
    rw [e3, hEq, lemma102_cd_twoPart_mul_odd hδr hSne]
  exact h2.le


private theorem lemma102_cd_centralizer_sup (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ a (ha | hb)
    · exact h1 a ha
    · exact h2 a hb

private theorem lemma102_cd_decomp {J A N : Subgroup G} (hAJ : A ≤ J) (hNJ : N ≤ J)
    [hN : (N.subgroupOf J).Normal] (hJ : J ≤ A ⊔ N) :
    ∀ j ∈ J, ∃ a ∈ A, ∃ n ∈ N, j = a * n := by
  intro j hj
  have hsup : A.subgroupOf J ⊔ N.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAJ hNJ, Subgroup.subgroupOf_eq_top]
    exact hJ
  have hmem : (⟨j, hj⟩ : J) ∈ A.subgroupOf J ⊔ N.subgroupOf J := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨a, ha, n, hn, hjan⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  refine ⟨a, Subgroup.mem_subgroupOf.1 ha, n, Subgroup.mem_subgroupOf.1 hn, ?_⟩
  have := congrArg Subtype.val hjan
  simpa using this.symm

private theorem lemma102_cd_comm_zpowers {x b e : G} (hxb : Commute x b) (he : e ∈ Subgroup.zpowers x) :
    e * b = b * e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  exact (hxb.zpow_left k).eq

private theorem lemma102_cd_gLBConj_sup (g : G) (A B : Subgroup G) :
    GLBConj g (A ⊔ B) = GLBConj g A ⊔ GLBConj g B := by
  unfold GLBConj
  exact Subgroup.map_sup _ _ _

private theorem lemma102_cd_gLBConj_join (b : G) (𝒞' : Set (Subgroup G))
    (h : ∀ C ∈ 𝒞', GLBConj b C = C) : GLBConj b (⨆ C ∈ 𝒞', C) = ⨆ C ∈ 𝒞', C := by
  have key : ∀ C : Subgroup G, (⨆ (_ : C ∈ 𝒞'), GLBConj b C) = ⨆ (_ : C ∈ 𝒞'), C := by
    intro C
    by_cases hC : C ∈ 𝒞'
    · rw [h C hC]
    · simp [hC]
  simp only [idiag_gLBConj_iSup, key]

private theorem lemma102_cd_quasi_false {X K : Subgroup G} (hp : p.Prime) (hK : GLAPComponent p X K)
    (hcomm : ∀ c ∈ K, ∀ c' ∈ K, ⁅c, c'⁆ ∈ GLAPPrimeCoreOf p K) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  let f : K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hOK : ∀ c c' : K, ⁅c, c'⁆ ∈ GLAPPrimeCore p ↥K := by
    intro c c'
    have hmem : ((⁅c, c'⁆ : K) : G) ∈ K := (⁅c, c'⁆ : K).2
    have h1 := (lemma102_mem_glaPPrimeCore_iff hmem).2 (by
      have e : ((⁅c, c'⁆ : K) : G) = ⁅(c : G), (c' : G)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact hcomm _ c.2 _ c'.2)
    exact h1
  have hcom_bot : Subgroup.map f (⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆) ≤ ⊥ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.commutator_le.2 fun c _ c' _ => ?_
    rw [Subgroup.mem_comap, Subgroup.mem_bot]
    show f ⁅c, c'⁆ = 1
    exact (QuotientGroup.eq_one_iff _).2 (hOK c c')
  have hmapt : Subgroup.map f (⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆) = ⊤ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hf]
    exact hq.1
  have htop : (⊤ : Subgroup (PQuot p K)) ≤ ⊥ := by
    rw [← hmapt]
    exact hcom_bot
  haveI : Nontrivial (PQuot p K ⧸ Subgroup.center (PQuot p K)) := hq.2.toNontrivial
  obtain ⟨y, hy⟩ := exists_ne (1 : PQuot p K ⧸ Subgroup.center (PQuot p K))
  apply hy
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  have hz : z = 1 := by
    have : z ∈ (⊥ : Subgroup (PQuot p K)) := htop (Subgroup.mem_top z)
    exact Subgroup.mem_bot.1 this
  simp [hz]


private theorem lemma102_cd_b (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G}
    {x x' : G} (hrel : PumpRel p (B, x, L) (B', x', L')) :
    ∃ 𝒞 : Set (Subgroup G), (∀ C ∈ 𝒞, GLAPComponent p (cx x') C) ∧
      (⨆ C ∈ 𝒞, C) = closureIn (Ipart p L x') (GLAPLayer p (cx x')) ∧
      (∀ C ∈ 𝒞, ∀ e ∈ Subgroup.zpowers x, GLBConj e C ∈ 𝒞) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C') ∧ L' ∈ 𝒞 := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p (cx x) L := hrel.1.2.2
  have hL'c : GLAPComponent p (cx x') L' := hrel.2.1.2.2
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hB'el : IsElemAbelian p B' := hrel.2.1.1.1
  have hx'1 : x' ≠ 1 := hrel.2.1.2.1.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'el hx'B'
  obtain ⟨hIc, -, -, -, -, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hI2 : GLAPComponent p (cx x' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G))
      (Ipart p L x') := by
    have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = cx x := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf _) hIc
  have hKx' : CFSG.Open.IsKGroup ↥(cx x') :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx'1)
  have hxCx' : Subgroup.zpowers x ≤ cx x' :=
    Subgroup.zpowers_le.2 ((isElemAbelian_le_centralizer hB'el hx'B') hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, h𝒞perm, h𝒞tr⟩ := hin.i183 G (cx x') hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'el hxB') (Ipart p L x') hI2
  have hJ : closureIn (Ipart p L x') (GLAPLayer p (cx x')) = ⨆ K ∈ 𝒞, K :=
    (closureIn_eq_iSup_gLBConj _ _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ closureIn (Ipart p L x') (GLAPLayer p (cx x')) := fun K hK => by
    rw [hJ]; exact le_biSup (fun K => K) hK
  have hJCx' : closureIn (Ipart p L x') (GLAPLayer p (cx x')) ≤ cx x' := by
    rw [hJ]; exact iSup₂_le fun K hK => (h𝒞c K hK).1
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p (closureIn (Ipart p L x') (GLAPLayer p (cx x'))) K :=
    fun K hK => glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hL'J : GLAPComponent p (closureIn (Ipart p L x') (GLAPLayer p (cx x'))) L' :=
    hrel.2.2.2.2.2.2
  have hL'𝒞 : L' ∈ 𝒞 := by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL'J ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'J.1
  exact ⟨𝒞, h𝒞c, hJ.symm, h𝒞perm, h𝒞tr, hL'𝒞⟩


private theorem lemma102_cd_comm_of_mod {J N : Subgroup G} (hNJ : N ≤ J) [hN : (N.subgroupOf J).Normal]
    {a₀ b₀ n₁ n₂ : G} (ha₀ : a₀ ∈ J) (hb₀ : b₀ ∈ J) (hn₁ : n₁ ∈ N) (hn₂ : n₂ ∈ N)
    (hc : ⁅a₀, b₀⁆ ∈ N) : ⁅a₀ * n₁, b₀ * n₂⁆ ∈ N := by
  classical
  let f : J →* J ⧸ N.subgroupOf J := QuotientGroup.mk' (N.subgroupOf J)
  have key : ∀ u : J, f u = 1 ↔ (u : G) ∈ N := fun u => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hn1J : n₁ ∈ J := hNJ hn₁
  have hn2J : n₂ ∈ J := hNJ hn₂
  have hfa : f ((⟨a₀, ha₀⟩ : J) * ⟨n₁, hn1J⟩) = f ⟨a₀, ha₀⟩ := by
    rw [map_mul, (key ⟨n₁, hn1J⟩).2 hn₁, mul_one]
  have hfb : f ((⟨b₀, hb₀⟩ : J) * ⟨n₂, hn2J⟩) = f ⟨b₀, hb₀⟩ := by
    rw [map_mul, (key ⟨n₂, hn2J⟩).2 hn₂, mul_one]
  have hcomm : f ⁅((⟨a₀, ha₀⟩ : J) * ⟨n₁, hn1J⟩), ((⟨b₀, hb₀⟩ : J) * ⟨n₂, hn2J⟩)⁆ = 1 := by
    rw [map_commutatorElement, hfa, hfb, ← map_commutatorElement]
    exact (key _).2 hc
  have := (key _).1 hcomm
  simpa [commutatorElement_def] using this

private theorem lemma102_cd_not_le_N {X : Subgroup G} {𝒞 : Set (Subgroup G)} (hp : p.Prime) {J : Subgroup G}
    (hJX : J ≤ X) (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) (hJdef : J = ⨆ C ∈ 𝒞, C) {K : Subgroup G}
    (hK : K ∈ 𝒞) : ¬ K ≤ lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := by
  intro hKN
  have hKJ : K ≤ J := hJdef ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) K hK
  have hJ : ∀ C ∈ 𝒞, C ≤ J := fun C hC => hJdef ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC
  refine lemma102_cd_quasi_false hp (hcomp K hK) fun c hc c' hc' => ?_
  have h1 : ⁅c, c'⁆ ∈ GLAPPrimeCoreOf p J :=
    lemma102_comm_NN hp hJX hcomp hJ hK hc (hKN hc')
  have h2 : ⁅c, c'⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hc hc') (K.inv_mem hc)) (K.inv_mem hc')
  exact lemma102_inf_le hp hKJ ⟨h2, h1⟩


private theorem lemma102_cd_a (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G}
    {x x' : G} (hrel : PumpRel p (B, x, L) (B', x', L')) :
    GLAPComponent p (cx x ⊓ cx x') (Ipart p L x') :=
  (pumpRel_facts hc.ctx.prime hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian hrel).1

private theorem lemma102_cd_c {X X₀ J N I K : Subgroup G} {b : G} (hp : p.Prime) (hNJ : N ≤ J)
    [hN : (N.subgroupOf J).Normal] (hIJ : I ≤ J) (hKJ : K ≤ J) (hJI : J ≤ I ⊔ N)
    (hbJn : b ∈ Subgroup.normalizer (J : Set G)) (hbN : GLBConj b N = N)
    (hI0 : GLAPComponent p X₀ I) (hbX₀ : GLBConj b X₀ = X₀) (hOIN : GLAPPrimeCoreOf p I ≤ N)
    (hKc : GLAPComponent p X K) (hOKN : GLAPPrimeCoreOf p K ≤ N) (hKnN : ¬ K ≤ N) :
    GLBConj b I = I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hbJ : GLBConj b J = J := mem_normalizer_iff_gLBConj_eq.1 hbJn
  have hbNn : b ∈ Subgroup.normalizer (N : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbN
  have hI'comp : GLAPComponent p X₀ (GLBConj b I) := by
    have := glaPComponent_gLBConj hI0 b
    rwa [hbX₀] at this
  have hI'O : GLAPPrimeCoreOf p (GLBConj b I) ≤ N := by
    rw [glaPPrimeCoreOf_gLBConj]
    exact (gLBConj_mono (g := b) hOIN).trans (le_of_eq hbN)
  have hI'J : GLBConj b I ≤ J := by
    have := gLBConj_mono (g := b) hIJ
    rwa [hbJ] at this
  have hI'cov : ∀ j ∈ J, ∃ i' ∈ GLBConj b I, ∃ n ∈ N, j = i' * n := by
    intro j hj
    have hbj : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hbJn j).1 hj
    obtain ⟨i, hi, n, hn, he⟩ := lemma102_cd_decomp hIJ hNJ hJI _ hbj
    refine ⟨b⁻¹ * i * b, mem_gLBConj.2 ?_, b⁻¹ * n * b, ?_, ?_⟩
    · rw [show b * (b⁻¹ * i * b) * b⁻¹ = i by group]; exact hi
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbNn) n).1 hn
      rwa [inv_inv] at this
    · calc j = b⁻¹ * (b * j * b⁻¹) * b := by group
        _ = b⁻¹ * (i * n) * b := by rw [he]
        _ = (b⁻¹ * i * b) * (b⁻¹ * n * b) := by group
  by_contra hne
  have hcen : I ≤ centModSubgroup p (GLBConj b I) :=
    le_centModSubgroup_of_ne hp hI0 hI'comp (Ne.symm hne)
  have hcommIN : ∀ i ∈ I, ∀ i' ∈ GLBConj b I, ⁅i, i'⁆ ∈ N := by
    intro i hi i' hi'
    have h1 := (mem_centModSubgroup.1 (hcen hi)).2 i' hi'
    have h2 : ⁅i, i'⁆ ∈ GLAPPrimeCoreOf p (GLBConj b I) := by
      rw [← commutatorElement_inv]
      exact (GLAPPrimeCoreOf p (GLBConj b I)).inv_mem h1
    exact hI'O h2
  have hcommJ : ∀ j ∈ J, ∀ j' ∈ J, ⁅j, j'⁆ ∈ N := by
    intro j hj j' hj'
    obtain ⟨i, hi, n, hn, rfl⟩ := lemma102_cd_decomp hIJ hNJ hJI j hj
    obtain ⟨i', hi', n', hn', rfl⟩ := hI'cov j' hj'
    exact lemma102_cd_comm_of_mod hNJ (hIJ hi) (hI'J hi') hn hn' (hcommIN i hi i' hi')
  have hKN : K ≤ N := by
    refine (lemma102_le_comm_sup hp hKc).trans (sup_le ?_ ?_)
    · exact Subgroup.commutator_le.2 fun c hc c' hc' => hcommJ c (hKJ hc) c' (hKJ hc')
    · exact hOKN
  exact hKnN hKN

private theorem lemma102_cd_core {X : Subgroup G} {𝒞 : Set (Subgroup G)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p X C) {K : Subgroup G} (hK : K ∈ 𝒞)
    {x : G} (hperm : ∀ e ∈ Subgroup.zpowers x, ∀ C ∈ 𝒞, GLBConj e C ∈ 𝒞)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C')
    {I : Subgroup G} (hIJ : I ≤ ⨆ C ∈ 𝒞, C) (hIx : I ≤ Subgroup.centralizer ({x} : Set G))
    (hcovK : K ≤ I ⊔ centModSubgroup p K)
    (hcard : Nat.card (PQuot p I) = Nat.card (PSimple p K))
    {X₀ : Subgroup G} (hI0 : GLAPComponent p X₀ I) {b : G} (hbX₀ : GLBConj b X₀ = X₀)
    (hbfix : ∀ C ∈ 𝒞, GLBConj b C = C) (hbK : b ∈ Subgroup.normalizer (K : Set G)) :
    b ∈ Subgroup.normalizer (I : Set G) ∧ centCard2 p I b ≤ centCard2 p K b := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨J, hJdef⟩ : ∃ J : Subgroup G, J = ⨆ C ∈ 𝒞, C := ⟨_, rfl⟩
  have hIJ' : I ≤ J := hJdef ▸ hIJ
  have hJX : J ≤ X := hJdef ▸ iSup₂_le fun C hC => (hcomp C hC).1
  have hJ : ∀ C ∈ 𝒞, C ≤ J := fun C hC => hJdef ▸ le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C hC
  have hKJ : K ≤ J := hJ K hK
  have hOJ : GLAPPrimeCoreOf p J ≤ J := lemma102_core_le J
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = lemma105NN 𝒞 (GLAPPrimeCoreOf p J) K := ⟨_, rfl⟩
  have hNJ : N ≤ J := by
    rw [hNdef]; exact sup_le (iSup₂_le fun C hC => hJ C hC.1) hOJ
  have hON : GLAPPrimeCoreOf p J ≤ N := by
    rw [hNdef]; exact le_sup_right
  have hJN : J ≤ K ⊔ N := by
    rw [hNdef]
    conv_lhs => rw [hJdef]
    refine iSup₂_le fun C hC => ?_
    by_cases hCK : C = K
    · subst hCK; exact le_sup_left
    · exact (((le_iSup₂ (f := fun (C' : Subgroup G) (_ : C' ∈ 𝒞 ∧ C' ≠ K) => C') C ⟨hC, hCK⟩).trans
        le_sup_left).trans le_sup_right)
  have hJI : J ≤ I ⊔ N := by
    rw [hNdef]; exact lemma102_cover hp hJX hcomp hJdef hK hIJ' hcovK
  have hNnorm : J ≤ Subgroup.normalizer (N : Set G) := by
    rw [hNdef]; exact lemma102_J_le_normalizer_NN hp hJX hcomp hJdef hJ hK
  have hNn : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 hNnorm
  haveI := hNn
  have hKnN : ¬ K ≤ N := fun h => lemma102_cd_not_le_N hp hJX hcomp hJdef hK (hNdef ▸ h)
  have hbJ : GLBConj b J = J := by
    rw [hJdef]; exact lemma102_cd_gLBConj_join b 𝒞 hbfix
  have hbJn : b ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbJ
  have hbO : GLBConj b (GLAPPrimeCoreOf p J) = GLAPPrimeCoreOf p J := by
    rw [← glaPPrimeCoreOf_gLBConj, hbJ]
  have hbN : GLBConj b N = N := by
    have h1 : GLBConj b (⨆ (C : Subgroup G) (_ : C ∈ 𝒞 ∧ C ≠ K), C) =
        ⨆ (C : Subgroup G) (_ : C ∈ 𝒞 ∧ C ≠ K), C :=
      lemma102_cd_gLBConj_join b {C | C ∈ 𝒞 ∧ C ≠ K} (fun C hC => hbfix C hC.1)
    rw [hNdef]
    unfold lemma105NN
    rw [lemma102_cd_gLBConj_sup, h1, hbO]
  have hbNn : b ∈ Subgroup.normalizer (N : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbN
  let mq : J →* J ⧸ N.subgroupOf J := QuotientGroup.mk' (N.subgroupOf J)
  have hmq : ∀ u : J, mq u = 1 ↔ (u : G) ∈ N := fun u => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hOI : GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p J :=
    lemma102_O_le hp hcomp hJdef hperm htrans hK hIJ' hIx hcovK hcard
  have hOIN : GLAPPrimeCoreOf p I ≤ N := hOI.trans hON
  have hOKN : GLAPPrimeCoreOf p K ≤ N :=
    (lemma102_core_comp_le hp hJX (hcomp K hK) hKJ).trans hON
  have hbI : GLBConj b I = I :=
    lemma102_cd_c hp hNJ hIJ' hKJ hJI hbJn hbN hI0 hbX₀ hOIN (hcomp K hK) hOKN hKnN
  have hbI_N : b ∈ Subgroup.normalizer (I : Set G) := mem_normalizer_iff_gLBConj_eq.2 hbI
  obtain ⟨c₀, hc₀K, hc₀N⟩ : ∃ c ∈ K, c ∉ N := by
    by_contra hcon
    exact hKnN fun c hc => by
      by_contra hcN
      exact hcon ⟨c, hc, hcN⟩
  have hkerI : GLAPPrimeCore p ↥I ≤ (mq.comp (Subgroup.inclusion hIJ')).ker := by
    intro o ho
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmq]
    exact hOIN ((lemma102_mem_glaPPrimeCore_iff o.2).1 ho)
  have hkerK : GLAPPrimeCore p ↥K ≤ (mq.comp (Subgroup.inclusion hKJ)).ker := by
    intro o ho
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hmq]
    exact hOKN ((lemma102_mem_glaPPrimeCore_iff o.2).1 ho)
  let θI : PQuot p I →* J ⧸ N.subgroupOf J :=
    QuotientGroup.lift (GLAPPrimeCore p ↥I) (mq.comp (Subgroup.inclusion hIJ')) hkerI
  let πK : PQuot p K →* J ⧸ N.subgroupOf J :=
    QuotientGroup.lift (GLAPPrimeCore p ↥K) (mq.comp (Subgroup.inclusion hKJ)) hkerK
  have hθs : Function.Surjective θI := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, n, hn, hjin⟩ := lemma102_cd_decomp hIJ' hNJ hJI j.1 j.2
    refine ⟨QuotientGroup.mk ⟨i, hi⟩, ?_⟩
    show mq (Subgroup.inclusion hIJ' ⟨i, hi⟩) = QuotientGroup.mk j
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    show i⁻¹ * (j : G) ∈ N
    rw [hjin, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hn
  have hπs : Function.Surjective πK := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, n, hn, hjkn⟩ := lemma102_cd_decomp hKJ hNJ hJN j.1 j.2
    refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
    show mq (Subgroup.inclusion hKJ ⟨k, hk⟩) = QuotientGroup.mk j
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    show k⁻¹ * (j : G) ∈ N
    rw [hjkn, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hn
  let conjJ : J →* J := lemma102_conjHomL hbJn
  have hβ : N.subgroupOf J ≤ (N.subgroupOf J).comap conjJ := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hu
    have hval : ((conjJ u : J) : G) = b⁻¹ * (u : G) * b := lemma102_conjHomL_val hbJn u
    rw [hval]
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbNn) (u : G)).1 hu
    rwa [inv_inv] at this
  let β : J ⧸ N.subgroupOf J →* J ⧸ N.subgroupOf J :=
    QuotientGroup.map (N.subgroupOf J) (N.subgroupOf J) conjJ hβ
  have E1 : ∀ i : PQuot p I, θI (lemma102_conjQ p hbI_N i) = β (θI i) := by
    intro i
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective i
    rw [lemma102_conjQ_mk]
    show mq (Subgroup.inclusion hIJ' (lemma102_conjHomL hbI_N a)) =
      mq (conjJ (Subgroup.inclusion hIJ' a))
    refine congrArg mq (Subtype.ext ?_)
    show ((lemma102_conjHomL hbI_N a : I) : G) = ((conjJ (Subgroup.inclusion hIJ' a)) : G)
    rw [lemma102_conjHomL_val hbI_N a, lemma102_conjHomL_val hbJn (Subgroup.inclusion hIJ' a)]
    rfl
  have E2 : ∀ k : PQuot p K, πK (lemma102_conjQ p hbK k) = β (πK k) := by
    intro k
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective k
    rw [lemma102_conjQ_mk]
    show mq (Subgroup.inclusion hKJ (lemma102_conjHomL hbK a)) =
      mq (conjJ (Subgroup.inclusion hKJ a))
    refine congrArg mq (Subtype.ext ?_)
    show ((lemma102_conjHomL hbK a : K) : G) = ((conjJ (Subgroup.inclusion hKJ a)) : G)
    rw [lemma102_conjHomL_val hbK a, lemma102_conjHomL_val hbJn (Subgroup.inclusion hKJ a)]
    rfl
  have hQpos : 0 < Nat.card (J ⧸ N.subgroupOf J) := Nat.card_pos
  have hθcard : Nat.card (PQuot p I) = Nat.card θI.ker * Nat.card (J ⧸ N.subgroupOf J) := by
    have := Subgroup.card_ker_mul_card_range θI
    rw [MonoidHom.range_eq_top.2 hθs, Subgroup.card_top] at this
    exact this.symm
  have hπcard : Nat.card (PQuot p K) = Nat.card πK.ker * Nat.card (J ⧸ N.subgroupOf J) := by
    have := Subgroup.card_ker_mul_card_range πK
    rw [MonoidHom.range_eq_top.2 hπs, Subgroup.card_top] at this
    exact this.symm
  have hPQ : Nat.card (PQuot p K) =
      Nat.card (PSimple p K) * Nat.card (Subgroup.center (PQuot p K)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hkey : Nat.card πK.ker = Nat.card θI.ker * Nat.card (Subgroup.center (PQuot p K)) := by
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [← hπcard, hPQ, ← hcard, hθcard]
    ring
  have hπne : πK.ker ≠ ⊤ := by
    intro htop
    have hmem : (QuotientGroup.mk ⟨c₀, hc₀K⟩ : PQuot p K) ∈ πK.ker := by
      rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h1 : mq (Subgroup.inclusion hKJ ⟨c₀, hc₀K⟩) = 1 := hmem
    exact hc₀N ((hmq _).1 h1)
  have hZc : πK.ker ≤ Subgroup.center (PQuot p K) :=
    le_center_of_normal_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp (hcomp K hK))
      (MonoidHom.normal_ker πK) hπne
  have hYK : CFSG.pPrimeCore p (PQuot p K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) p
  have hZp : IsPGroup p πK.ker := lemma102_isPGroup_of_central hp hYK πK.ker hZc
  obtain ⟨nZ, hnZ⟩ := IsPGroup.iff_card.1 hZp
  have hZo : Odd (Nat.card πK.ker) := by
    rw [hnZ]; exact hodd.pow
  have hθk : Odd (Nat.card θI.ker) := by
    have hdvd : Nat.card θI.ker ∣ p ^ nZ := by
      rw [← hnZ, hkey]; exact dvd_mul_right _ _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hm]; exact hodd.pow
  have FA := lemma102_cd_fixA (lemma102_conjQ p hbI_N) β θI E1 hθk
  have FB := lemma102_cd_fixB (lemma102_conjQ p hbK) β πK hπs E2 hZc hZo
  refine ⟨hbI_N, ?_⟩
  rw [lemma102_centCard2_eq_fixSub p hbI_N, lemma102_centCard2_eq_fixSub p hbK]
  exact FA.trans FB

private theorem lemma102_cd_main (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G}
    {x x' : G} (hrel : PumpRel p (B, x, L) (B', x', L')) {b : G} (hbB' : b ∈ B')
    (hbN : b ∈ Subgroup.normalizer (L' : Set G)) (hxN : x ∉ Subgroup.normalizer (L' : Set G)) :
    centCard2 p (closureIn (Ipart p L x') (Subgroup.zpowers b)) b ≤ centCard2 p L' b := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx1 : x ≠ 1 := hrel.1.2.1.2.1
  have hx'1 : x' ≠ 1 := hrel.2.1.2.1.2.1
  have hB'el : IsElemAbelian p B' := hrel.2.1.1.1
  have hL'c : GLAPComponent p (cx x') L' := hrel.2.1.2.2
  have hbx : Commute b x := idiag_commute hB'el hbB' hxB'
  have hbx' : Commute b x' := idiag_commute hB'el hbB' hx'B'
  have hxx' : Commute x x' := idiag_commute hB'el hxB' hx'B'
  have hI1 := lemma102_cd_a hc hin hrel
  obtain ⟨-, hI2, -⟩ := pumpRel_facts hp hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian hrel
  have hcard : Nat.card (PQuot p (Ipart p L x')) = Nat.card (PSimple p L') := by
    obtain ⟨eI⟩ := hin.i1122 B' x' L' x hrel.2.1.1 hrel.2.1.2.1 hrel.2.1.2.2 hxB' hxN
      (Ipart p L x') hI2
    exact Nat.card_congr eI.toEquiv
  obtain ⟨𝒞, h𝒞c, h𝒞sup, h𝒞perm, h𝒞tr, hL'𝒞⟩ := lemma102_cd_b hc hin hrel
  have hIJ : Ipart p L x' ≤ ⨆ C ∈ 𝒞, C := by
    rw [h𝒞sup]; exact le_closureIn_self _ _
  have hIx : Ipart p L x' ≤ cx x := hI1.1.trans inf_le_left
  have hbX₀ : GLBConj b (cx x ⊓ cx x') = cx x ⊓ cx x' := by
    have hbmem : b ∈ cx x ⊓ cx x' :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hbx.eq,
        Subgroup.mem_centralizer_singleton_iff.2 hbx'.eq⟩
    exact mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hbmem)
  have hbfix : ∀ C ∈ 𝒞, GLBConj b C = C := by
    intro C hC
    obtain ⟨e, he, rfl⟩ := h𝒞tr L' hL'𝒞 C hC
    have hbL' : GLBConj b L' = L' := mem_normalizer_iff_gLBConj_eq.1 hbN
    calc GLBConj b (GLBConj e L') = GLBConj (e * b) L' := gLBConj_gLBConj _ _ _
      _ = GLBConj (b * e) L' := by rw [lemma102_cd_comm_zpowers hbx.symm he]
      _ = GLBConj e (GLBConj b L') := (gLBConj_gLBConj _ _ _).symm
      _ = GLBConj e L' := by rw [hbL']
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = Subgroup.zpowers x ⊔ Subgroup.zpowers x' := ⟨_, rfl⟩
  have hD_le : D ≤ B' := by
    rw [hDdef]
    exact sup_le (Subgroup.zpowers_le.2 hxB') (Subgroup.zpowers_le.2 hx'B')
  have hDel : IsElemAbelian p D := isElemAbelian_mono hB'el hD_le
  have hzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = cx x := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hzx' : Subgroup.centralizer (Subgroup.zpowers x' : Set G) = cx x' := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcentD : Subgroup.centralizer (D : Set G) = cx x ⊓ cx x' := by
    rw [hDdef, lemma102_cd_centralizer_sup, hzx, hzx']
  have hcardx' : Nat.card (Subgroup.zpowers x') = p := lemma102_card_zpowers_prime hp hB'el hx'B' hx'1
  have hcardx : Nat.card (Subgroup.zpowers x) = p := lemma102_card_zpowers_prime hp hB'el hxB' hx1
  have hzx_le : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers x' : Set G) := by
    rw [hzx']
    exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hxx'.eq)
  have hinf : Subgroup.zpowers x' ⊓ Subgroup.zpowers x = ⊥ := by
    by_contra hne
    have hne1 : Nat.card ↥(Subgroup.zpowers x' ⊓ Subgroup.zpowers x) ≠ 1 :=
      fun h => hne (Subgroup.card_eq_one.1 h)
    have hdvd : Nat.card ↥(Subgroup.zpowers x' ⊓ Subgroup.zpowers x) ∣ p := by
      rw [← hcardx]; exact Subgroup.card_dvd_of_le inf_le_right
    have hp' : Nat.card ↥(Subgroup.zpowers x' ⊓ Subgroup.zpowers x) = p :=
      ((Nat.dvd_prime hp).1 hdvd).resolve_left hne1
    have heq : Subgroup.zpowers x' ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardx, hp'])
    have hxA : x ∈ Subgroup.zpowers x' := by
      have : Subgroup.zpowers x ≤ Subgroup.zpowers x' := by
        rw [← heq]; exact inf_le_left
      exact this (Subgroup.mem_zpowers x)
    apply hxN
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxA
    have hcomm : ∀ h ∈ L', h * x = x * h := by
      intro h hh
      have hc' : Commute h x' := Subgroup.mem_centralizer_singleton_iff.1 (hL'c.1 hh)
      rw [← hk]
      exact (hc'.zpow_right k).eq
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => hcomm h hh)
  have hBN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers x' : Set G) :=
    hzx_le.trans (Subgroup.centralizer_le_normalizer _)
  have hDcard : Nat.card D = p ^ 2 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hBN
    rw [hinf, Subgroup.card_bot, hcardx, hcardx', mul_one, sup_comm, ← hDdef] at h1
    rw [h1, sq]
  have hAD : Subgroup.zpowers x' ≤ D := by
    rw [hDdef]; exact le_sup_right
  have hidx : ((Subgroup.zpowers x').subgroupOf D).index = p :=
    lemma102_index_eq hp hAD hDcard hcardx'
  have hKg : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G)) := by
    rw [hzx']
    exact isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx'1)
  have hIdiag : GLAPComponent p (Subgroup.centralizer (D : Set G)) (Ipart p L x') := by
    rw [hcentD]; exact hI1
  have hcomp' : ∀ C ∈ 𝒞, GLAPComponent p
      (Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G)) C := by
    intro C hC; rw [hzx']; exact h𝒞c C hC
  have hsup' : (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer p
      (Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G)), GLBConj g (Ipart p L x') := by
    rw [hzx', h𝒞sup, closureIn_eq_iSup_gLBConj]
  have hcomm_AB : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ Subgroup.zpowers x', a * c = c * a := by
    intro a ha c hc'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    exact ((hxx'.zpow_left i).zpow_right j).eq
  have hstab : ∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞 := by
    intro C hC e he
    rw [hDdef] at he
    obtain ⟨u, hu, v, hv, rfl⟩ := lemma102_mem_sup_comm hcomm_AB he
    rw [← gLBConj_gLBConj, lemma102_glbconj_zpowers_eq
      (h𝒞c _ (h𝒞perm C hC u hu)).1 hv]
    exact h𝒞perm C hC u hu
  have htr' : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C' := by
    intro C hC C' hC'
    obtain ⟨e, he, h⟩ := h𝒞tr C hC C' hC'
    exact ⟨e, by rw [hDdef]; exact Subgroup.mem_sup_left he, h⟩
  have hne : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂ := by
    refine ⟨L', hL'𝒞, GLBConj x L', h𝒞perm L' hL'𝒞 x (Subgroup.mem_zpowers x), ?_⟩
    intro heq
    apply hxN
    exact mem_normalizer_iff_gLBConj_eq.2 heq.symm
  have hcov_all : ∀ C ∈ 𝒞, C ≤ Ipart p L x' ⊔ centModSubgroup p C :=
    i183DiagAt_holds G p hp hp2 (Subgroup.zpowers x') D (Ipart p L x') 𝒞 hDel hAD hidx hKg hIdiag
      hcomp' hsup' hstab htr' hne
  obtain ⟨hbI_N, hle⟩ := lemma102_cd_core hp hp2 h𝒞c hL'𝒞 (fun e he C hC => h𝒞perm C hC e he) h𝒞tr hIJ hIx
    (hcov_all L' hL'𝒞) hcard hI1 hbX₀ hbfix hbN
  rw [closureIn_eq_self (Subgroup.zpowers_le.2 hbI_N)]
  exact hle

theorem cent_le_diag (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) {b : G} (hbB' : b ∈ B')
    (hbN : b ∈ Subgroup.normalizer (L' : Set G)) :
    centCard2 p (closureIn (Ipart p L x') (Subgroup.zpowers b)) b ≤ centCard2 p L' b := by
  classical
  have hp := hc.ctx.prime
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  ·
    have hIL' : Ipart p L x' ≤ L' :=
      (lemma102_I_le hp hin.i183 hc.ctx.kProper hc.ctx.simple hc.ctx.nonabelian hrel).2 hxN
    have hI₀L' : closureIn (Ipart p L x') (Subgroup.zpowers b) ≤ L' := by
      refine (lemma102_closureIn_mono_left hIL').trans ?_
      rw [closureIn_eq_self (Subgroup.zpowers_le.2 hbN)]
    have hbp : b ^ p = 1 := hrel.2.1.1.1.2 b hbB'
    have hb1 : b ∈ Subgroup.normalizer
        ((closureIn (Ipart p L x') (Subgroup.zpowers b) : Subgroup G) : Set G) :=
      le_normalizer_closureIn _ _ (Subgroup.mem_zpowers b)
    have hdvd := lemma102_fix_dvd hp hI₀L' hbN hb1 hbp
    rw [lemma102_centCard2_eq_fixSub p hb1, lemma102_centCard2_eq_fixSub p hbN]
    exact lemma102_twoPart_le_of_dvd (Nat.card_pos (α := lemma102_fixSub p hbN)).ne' hdvd
  · exact lemma102_cd_main hc hin hrel hbB' hbN hxN

theorem lemma102_fix_card_eq {p : ℕ} (hp : p.Prime) {I₀ L₀ : Subgroup G} {b : G}
    (hIL₀ : I₀ ≤ L₀) (hsup : I₀ ⊔ GLAPPrimeCoreOf p L₀ = L₀)
    (hb0 : b ∈ Subgroup.normalizer (L₀ : Set G)) (hb1 : b ∈ Subgroup.normalizer (I₀ : Set G)) :
    Nat.card (lemma102_fixSub p hb1) = Nat.card (lemma102_fixSub p hb0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hO_eq : GLAPPrimeCoreOf p I₀ = I₀ ⊓ GLAPPrimeCoreOf p L₀ :=
    (cover_facts hp hIL₀ hsup).1
  have hOI : GLAPPrimeCore p ↥I₀ ≤ (GLAPPrimeCore p ↥L₀).comap (Subgroup.inclusion hIL₀) := by
    intro w hw
    rw [Subgroup.mem_comap]
    have hw' : (w : G) ∈ GLAPPrimeCoreOf p I₀ := (lemma102_mem_glaPPrimeCore_iff w.2).1 hw
    rw [hO_eq] at hw'
    exact (lemma102_mem_glaPPrimeCore_iff (hIL₀ w.2)).2 hw'.2
  set F : PQuot p I₀ →* PQuot p L₀ :=
    QuotientGroup.map (GLAPPrimeCore p ↥I₀) (GLAPPrimeCore p ↥L₀) (Subgroup.inclusion hIL₀) hOI
    with hF
  have hFmk : ∀ w : ↥I₀, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL₀ w) :=
    fun w => QuotientGroup.map_mk _ _ _ _ _
  have hIO' : I₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L₀ : Set G) :=
    hIL₀.trans (le_normalizer_glaPPrimeCoreOf p L₀)
  have hFbij : Function.Bijective F := by
    refine ⟨(injective_iff_map_eq_one F).2 ?_, ?_⟩
    · intro q hq
      induction q using QuotientGroup.induction_on with
      | H w =>
        rw [hFmk, QuotientGroup.eq_one_iff] at hq
        rw [QuotientGroup.eq_one_iff]
        have hwO : (w : G) ∈ GLAPPrimeCoreOf p I₀ := by
          rw [hO_eq]
          exact ⟨w.2, (lemma102_mem_glaPPrimeCore_iff (hIL₀ w.2)).1 hq⟩
        exact (lemma102_mem_glaPPrimeCore_iff w.2).2 hwO
    · intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl : (l : G) ∈ (I₀ ⊔ GLAPPrimeCoreOf p L₀ : Subgroup G) := hsup.symm ▸ l.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I₀ _ hIO'] at hl
      obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hl
      refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
      rw [hFmk, QuotientGroup.eq]
      have hXO : y⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L₀ := by
        rw [← hyz, inv_mul_cancel_left]
        exact hz
      exact (lemma102_mem_glaPPrimeCore_iff ((Subgroup.inclusion hIL₀ ⟨y, hy⟩)⁻¹ * l).2).2 hXO
  let e : PQuot p I₀ ≃ PQuot p L₀ := Equiv.ofBijective F hFbij
  have hequiv : ∀ q : PQuot p I₀, F (lemma102_conjQ p hb1 q) = lemma102_conjQ p hb0 (F q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [lemma102_conjQ_mk, hFmk, hFmk, lemma102_conjQ_mk]
      congr 1
  have hfix : ∀ q : PQuot p I₀, lemma102_conjQ p hb1 q = q ↔ lemma102_conjQ p hb0 (F q) = F q := by
    intro q
    rw [← hequiv q]
    exact hFbij.1.eq_iff.symm
  exact Nat.card_congr (Equiv.subtypeEquiv e (fun q => hfix q))

theorem cent_cover (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) {b : G} (hbB' : b ∈ B') :
    centCard2 p (closureIn L (Subgroup.zpowers b)) b ≤
      centCard2 p (closureIn (Ipart p L x') (Subgroup.zpowers b)) b := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := hrel.1
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hrel.2.1.1.1 hx'B'
  obtain ⟨hIc, -, -, -, hIsup, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hbx : b * x = x * b :=
    congrArg Subtype.val (hrel.2.1.1.1.1.is_comm.comm ⟨b, hbB'⟩ ⟨x, hxB'⟩)
  have hbC : Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hbx)
  set I := Ipart p L x' with hIdef
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hL₀C : closureIn L (Subgroup.zpowers b) ≤ Subgroup.centralizer ({x} : Set G) :=
    lemma102_closureIn_le_of hL.1 hbC
  set L₀ := closureIn L (Subgroup.zpowers b) with hL₀def
  set I₀ := closureIn I (Subgroup.zpowers b) with hI₀def
  have hIL₀ : I₀ ≤ L₀ := lemma102_closureIn_mono_left hIL
  have hb0 : b ∈ Subgroup.normalizer (L₀ : Set G) :=
    le_normalizer_closureIn L (Subgroup.zpowers b) (Subgroup.mem_zpowers b)
  have hb1 : b ∈ Subgroup.normalizer (I₀ : Set G) :=
    le_normalizer_closureIn I (Subgroup.zpowers b) (Subgroup.mem_zpowers b)
  have hcov0 : L₀ ≤ I₀ ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    closureIn_le_closureIn_sup hp hL hIsup hbC
  have hIC : I ≤ Subgroup.centralizer ({x} : Set G) := hIL.trans hL.1
  have hI₀C : I₀ ≤ Subgroup.centralizer ({x} : Set G) := lemma102_closureIn_le_of hIC hbC
  have hIO : I₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) : Set G) :=
    hI₀C.trans (le_normalizer_glaPPrimeCoreOf p _)
  have hcov : L₀ ≤ I₀ ⊔ GLAPPrimeCoreOf p L₀ := by
    intro l hl
    have hl' : (l : G) ∈ (I₀ ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) : Subgroup G) :=
      hcov0 hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I₀ _ hIO] at hl'
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hl'
    have hzL : z ∈ L₀ := by
      have := L₀.mul_mem (L₀.inv_mem (hIL₀ hy)) hl
      simpa using this
    exact Subgroup.mul_mem_sup hy (lemma102_inf_le hp hL₀C ⟨hzL, hz⟩)
  have hsup : I₀ ⊔ GLAPPrimeCoreOf p L₀ = L₀ :=
    le_antisymm (sup_le hIL₀ (Subgroup.map_subtype_le _)) hcov
  set ψ : ↥I₀ →* PQuot p L₀ :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L₀)).comp (Subgroup.inclusion hIL₀) with hψ
  have hIO' : I₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L₀ : Set G) :=
    hIL₀.trans (le_normalizer_glaPPrimeCoreOf p L₀)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl : (l : G) ∈ (I₀ ⊔ GLAPPrimeCoreOf p L₀ : Subgroup G) := hsup.symm ▸ l.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I₀ _ hIO'] at hl
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hl
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hXO : y⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L₀ := by
      rw [← hyz, inv_mul_cancel_left]
      exact hz
    exact (lemma102_mem_glaPPrimeCore_iff ((Subgroup.inclusion hIL₀ ⟨y, hy⟩)⁻¹ * l).2).2 hXO
  rw [lemma102_centCard2_eq_fixSub p hb0, lemma102_centCard2_eq_fixSub p hb1, lemma102_fix_card_eq hp hIL₀ hsup hb0 hb1]

theorem lemma102_conj_inv_mem {L : Subgroup G} {u y : G} (hu : u ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ L) : u⁻¹ * y * u ∈ L := by
  have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hu) y).1 hy
  rwa [inv_inv] at h

theorem lemma102_mem_glaPPrimeCoreOf_comm {p : ℕ} {L : Subgroup G} {c m : G} (hc : CentMod p L c)
    (hm : m ∈ L) : m⁻¹ * (c⁻¹ * m * c) ∈ GLAPPrimeCoreOf p L := by
  have h1 : ⁅m⁻¹, c⁻¹⁆ ∈ (⁅L, Subgroup.zpowers c⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hm)
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have h2 := hc.2 h1
  rw [commutatorElement_def] at h2
  simpa [mul_assoc] using h2

theorem lemma102_conjQ_eq_of_cent {p : ℕ} {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgc : g * c ∈ Subgroup.normalizer (L : Set G))
    (hc : CentMod p L c) : lemma102_conjQ p hgc = lemma102_conjQ p hg := by
  refine MonoidHom.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [lemma102_conjQ_mk, lemma102_conjQ_mk, QuotientGroup.eq]
    have hm : g⁻¹ * (l : G) * g ∈ L := (lemma102_conjHomL hg l).2
    have hO := lemma102_mem_glaPPrimeCoreOf_comm hc hm
    have hXO : ((lemma102_conjHomL hgc l : ↥L) : G)⁻¹ * ((lemma102_conjHomL hg l : ↥L) : G) ∈ GLAPPrimeCoreOf p L := by
      rw [lemma102_conjHomL_val, lemma102_conjHomL_val]
      have e : ((g * c)⁻¹ * (l : G) * (g * c))⁻¹ * (g⁻¹ * (l : G) * g) =
          ((g⁻¹ * (l : G) * g)⁻¹ * (c⁻¹ * (g⁻¹ * (l : G) * g) * c))⁻¹ := by
        group
      rw [e]
      exact Subgroup.inv_mem _ hO
    have hXL : ((lemma102_conjHomL hgc l : ↥L) : G)⁻¹ * ((lemma102_conjHomL hg l : ↥L) : G) ∈ L :=
      L.mul_mem (L.inv_mem (lemma102_conjHomL hgc l).2) (lemma102_conjHomL hg l).2
    exact (lemma102_mem_glaPPrimeCore_iff hXL).2 hXO

theorem lemma102_indRel_mul_cent {p : ℕ} {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgc : g * c ∈ Subgroup.normalizer (L : Set G))
    (hc : CentMod p L c) : indRel p L (g * c) = indRel p L g := by
  funext q q'
  apply propext
  rw [lemma102_indRel_iff_conjQ hgc, lemma102_indRel_iff_conjQ hg, lemma102_conjQ_eq_of_cent hg hgc hc]

theorem lemma102_inducesInnerMod_mul_cent {p : ℕ} {L : Subgroup G} {u v : G}
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (hv : CentMod p L v) :
    InducesInnerMod p L (u * v) ↔ InducesInnerMod p L u := by
  have key : ∀ y ∈ L, ((u * v)⁻¹ * y * (u * v)) =
      (u⁻¹ * y * u) * ((u⁻¹ * y * u)⁻¹ * (v⁻¹ * (u⁻¹ * y * u) * v)) := fun y _ => by group
  unfold InducesInnerMod
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨l, hl, fun y hy => ?_⟩
    have hw : u⁻¹ * y * u ∈ L := lemma102_conj_inv_mem hu hy
    have hO := lemma102_mem_glaPPrimeCoreOf_comm hv hw
    have h' := h y hy
    rw [key y hy, ← mul_assoc] at h'
    exact (Subgroup.mul_mem_cancel_right _ hO).1 (by simpa [mul_assoc] using h')
  · rintro ⟨l, hl, h⟩
    refine ⟨l, hl, fun y hy => ?_⟩
    have hw : u⁻¹ * y * u ∈ L := lemma102_conj_inv_mem hu hy
    have hO := lemma102_mem_glaPPrimeCoreOf_comm hv hw
    rw [key y hy, ← mul_assoc]
    exact (Subgroup.mul_mem_cancel_right _ hO).2 (h y hy)

theorem lemma102_innDiagOn_zpowers_congr {p : ℕ} {L : Subgroup G} {b u : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hu : u ∈ Subgroup.normalizer (L : Set G))
    (hk : ∀ k : ℤ, indRel p L (b ^ k) = indRel p L (u ^ k)) :
    InnDiagOn p (Subgroup.zpowers b) L ↔ InnDiagOn p (Subgroup.zpowers u) L := by
  have hpt : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R),
      (∀ a ∈ Subgroup.zpowers b, ∃ φ ∈ I, GLAInduces θ (indRel p L a) φ) ↔
        (∀ a ∈ Subgroup.zpowers u, ∃ φ ∈ I, GLAInduces θ (indRel p L a) φ) := by
    intro lab R _ I F θ
    constructor
    · intro h a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨φ, hφI, hφ⟩ := h (b ^ k) (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)
      exact ⟨φ, hφI, by rw [← hk k]; exact hφ⟩
    · intro h a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨φ, hφI, hφ⟩ := h (u ^ k) (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)
      exact ⟨φ, hφI, by rw [hk k]; exact hφ⟩
  unfold InnDiagOn
  constructor
  · rintro ⟨-, h⟩
    exact ⟨Subgroup.zpowers_le.2 hu, CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun lab R _ I F θ hP => (hpt lab R I F θ).1 hP) h⟩
  · rintro ⟨-, h⟩
    exact ⟨Subgroup.zpowers_le.2 hb, CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun lab R _ I F θ hP => (hpt lab R I F θ).2 hP) h⟩

theorem lemma102_act_congr_aux {L : Subgroup G} {u v b : G} (hb : b = u * v)
    (hcomm : u * v = v * u) (hv : CentMod p L v) (hbN : b ∈ Subgroup.normalizer (L : Set G)) :
    u ∈ Subgroup.normalizer (L : Set G) ∧ (NonInnDiag p b L ↔ NonInnDiag p u L) ∧
      (FieldOn p b L ↔ FieldOn p u L) ∧ (NonInner p b L ↔ NonInner p u L) ∧
      centCard2 p L b = centCard2 p L u := by
  subst hb
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hv.1
  have huN : u ∈ Subgroup.normalizer (L : Set G) := by
    have h := Subgroup.mul_mem _ hbN (Subgroup.inv_mem _ hvN)
    simpa using h
  have hcv : Commute u v := hcomm
  have hk : ∀ k : ℤ, indRel p L ((u * v) ^ k) = indRel p L (u ^ k) := fun k => by
    rw [hcv.mul_zpow k]
    exact lemma102_indRel_mul_cent (Subgroup.zpow_mem _ huN k)
      (by rw [← hcv.mul_zpow k]; exact Subgroup.zpow_mem _ hbN k)
      (centMod_iff.2 (Subgroup.zpow_mem _ (centMod_iff.1 hv) k))
  have hbu : indRel p L (u * v) = indRel p L u := by
    simpa using hk 1
  have hInn := lemma102_innDiagOn_zpowers_congr hbN huN hk
  refine ⟨huN, ⟨fun h => ⟨huN, fun h' => h.2 (hInn.2 h')⟩,
    fun h => ⟨hbN, fun h' => h.2 (hInn.1 h')⟩⟩, ?_, ?_, ?_⟩
  · unfold FieldOn
    rw [hbu]
    exact ⟨fun h => ⟨huN, h.2⟩, fun h => ⟨hbN, h.2⟩⟩
  · unfold NonInner
    exact ⟨fun h => ⟨huN, fun h' => h.2 ((lemma102_inducesInnerMod_mul_cent huN hv).2 h')⟩,
      fun h => ⟨hbN, fun h' => h.2 ((lemma102_inducesInnerMod_mul_cent huN hv).1 h')⟩⟩
  · unfold centCard2
    rw [hbu]

theorem lemma102_card_central_pPower {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.pPrimeCore p Y = ⊥) {M : Subgroup Y} (hM : M ≤ Subgroup.center Y) :
    ∃ k : ℕ, Nat.card M = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : Nat.card M ≠ 0 := by
    haveI : Finite M := inferInstance
    exact Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne ?_⟩
  intro q hq hqd
  by_contra hqp
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hwc : (w : Y) ∈ Subgroup.center Y := hM w.2
  have hnorm : (Subgroup.zpowers (w : Y)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute g (w : Y) := Subgroup.mem_center_iff.1 hwc g
    have : g * (w : Y) ^ k * g⁻¹ = (w : Y) ^ k := by
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
    rw [this]
    exact hn
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (w : Y))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
    exact (Nat.coprime_primes hp hq).2 (Ne.symm hqp)
  have hle : Subgroup.zpowers (w : Y) ≤ CFSG.pPrimeCore p Y := le_sSup ⟨hnorm, hcop⟩
  rw [hY, le_bot_iff] at hle
  have h1 : (w : Y) = 1 := by
    have := Subgroup.mem_zpowers (w : Y)
    rw [hle] at this
    exact this
  have h2 : orderOf (w : Y) = q := by rw [Subgroup.orderOf_coe, hw]
  rw [h1, orderOf_one] at h2
  exact hq.one_lt.ne' h2.symm


theorem lemma102_normalizer_of_pow {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G} (hbp : b ^ p = 1)
    {d : ℕ} (hd0 : 0 < d) (hdp : d < p) (hbd : b ^ d ∈ Subgroup.normalizer (L : Set G)) :
    b ∈ Subgroup.normalizer (L : Set G) := by
  have hcop : Nat.Coprime d p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      (fun h => absurd (Nat.le_of_dvd hd0 h) (not_le.2 hdp)))
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime).2 hcop
  have hb : b = (b ^ d) ^ u := by
    calc b = b ^ ((d : ℤ) * u + (p : ℤ) * v) := by
          rw [show (d : ℤ) * u + (p : ℤ) * v = u * d + v * p by ring, huv, zpow_one]
      _ = (b ^ d) ^ u * (b ^ p) ^ v := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (b ^ d) ^ u := by rw [hbp, one_zpow, mul_one]
  rw [hb]
  exact Subgroup.zpow_mem _ hbd u


theorem lemma102_twoPart_pow_mul {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : m ≠ 0) :
    twoPart (p ^ k * m) = twoPart m := by
  unfold twoPart
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization hp, Finsupp.single_apply]
  simp [hp2]

theorem lemma102_easy_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G} {b : G}
    (hL : GLAPComponent p X L) (hbX : b ∈ X) (hbp : b ^ p = 1)
    (hbL : b ∉ Subgroup.normalizer (L : Set G)) :
    card2 p L ≤ centCard2 p (closureIn L (Subgroup.zpowers b)) b := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K : ℕ → Subgroup G := fun i => GLBConj (b ^ i) L with hKdef
  set L₀ : Subgroup G := closureIn L (Subgroup.zpowers b) with hL₀def
  have hbXN : ∀ i : ℕ, b ^ i ∈ Subgroup.normalizer (X : Set G) := fun i =>
    Subgroup.le_normalizer (Subgroup.pow_mem X hbX i)
  have hKX : ∀ i : ℕ, GLAPComponent p X (K i) := fun i => by
    have h := glaPComponent_gLBConj hL (b ^ i)
    rwa [mem_normalizer_iff_gLBConj_eq.1 (hbXN i)] at h
  have hKL₀ : ∀ i : ℕ, K i ≤ L₀ := fun i => by
    rw [hL₀def, closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun g => GLBConj g L) (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i)
  have hL₀X : L₀ ≤ X := lemma102_closureIn_le_of hL.1 (Subgroup.zpowers_le.2 hbX)
  have hKsub : ∀ i : ℕ, GLAPComponent p L₀ (K i) := fun i =>
    glaPComponent_of_le hp (hKX i) (hKL₀ i) hL₀X
  have hOK : ∀ i : ℕ, GLAPPrimeCoreOf p (K i) ≤ GLAPPrimeCoreOf p L₀ := fun i => by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp (hKsub i).2.1]
    exact inf_le_right
  have hLsub : L ≤ L₀ := le_closureIn_self L _
  have hLcomp : GLAPComponent p L₀ L := glaPComponent_of_le hp hL hLsub hL₀X
  have hLO : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p L₀ := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hLcomp.2.1]
    exact inf_le_right
  have hL0 : K 0 = L := by
    show GLBConj (b ^ 0) L = L
    rw [pow_zero, gLBConj_one]
  have hKne : ∀ i j : ℕ, i < p → j < p → i ≠ j → K i ≠ K j := by
    intro i j hi hj hij hKij
    apply hbL
    have hmem : b ^ i * (b ^ j)⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
      have h1 : GLBConj ((b ^ j)⁻¹) (K j) = L := by
        rw [hKdef]
        simp only
        rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
      have h2 : GLBConj ((b ^ j)⁻¹) (K i) = GLBConj (b ^ i * (b ^ j)⁻¹) L := by
        rw [hKdef]
        simp only
        rw [gLBConj_gLBConj]
      rw [mem_normalizer_iff_gLBConj_eq, ← h2, hKij, h1]
    rcases lt_or_gt_of_ne hij with h | h
    · apply lemma102_normalizer_of_pow hp hbp (d := j - i) (by omega) (by omega)
      have e : b ^ (j - i) = (b ^ i * (b ^ j)⁻¹)⁻¹ := by
        rw [show b ^ j = b ^ (j - i) * b ^ i by rw [← pow_add, Nat.sub_add_cancel h.le]]
        group
      rw [e]
      exact Subgroup.inv_mem _ hmem
    · apply lemma102_normalizer_of_pow hp hbp (d := i - j) (by omega) (by omega)
      have e : b ^ (i - j) = b ^ i * (b ^ j)⁻¹ := by
        rw [show b ^ i = b ^ (i - j) * b ^ j by rw [← pow_add, Nat.sub_add_cancel h.le]]
        group
      rw [e]
      exact hmem
  have hcomm : ∀ i j : ℕ, i < p → j < p → i ≠ j → ∀ a ∈ K i, ∀ c ∈ K j,
      ⁅a, c⁆ ∈ GLAPPrimeCoreOf p L₀ := by
    intro i j hi hj hij a ha c hc
    have h1 : K j ≤ centModSubgroup p (K i) :=
      le_centModSubgroup_of_ne hp (hKX j) (hKX i) (hKne j i hj hi (Ne.symm hij))
    exact hOK i ((mem_centModSubgroup.1 (h1 hc)).2 a ha)
  have hcj_mem : ∀ (i : ℕ) (l : G), l ∈ L → (b ^ i)⁻¹ * l * b ^ i ∈ K i := fun i l hl =>
    mem_gLBConj.2 (by rw [show b ^ i * ((b ^ i)⁻¹ * l * b ^ i) * (b ^ i)⁻¹ = l by group]; exact hl)
  let φ : ℕ → (↥L →* ↥L₀) := fun i =>
    { toFun := fun l => ⟨(b ^ i)⁻¹ * (l : G) * b ^ i, hKL₀ i (hcj_mem i _ l.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a c => by ext; simp [mul_assoc] }
  let f : ℕ → (↥L →* PQuot p L₀) := fun i =>
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L₀)).comp (φ i)
  have hfc : ∀ i j : ℕ, i < p → j < p → i ≠ j → ∀ l m : ↥L, Commute (f i l) (f j m) := by
    intro i j hi hj hij l m
    have ha : (b ^ i)⁻¹ * (l : G) * b ^ i ∈ K i := hcj_mem i _ l.2
    have hc : (b ^ j)⁻¹ * (m : G) * b ^ j ∈ K j := hcj_mem j _ m.2
    show f i l * f j m = f j m * f i l
    simp only [f, φ, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul]
    rw [QuotientGroup.eq]
    refine (lemma102_mem_glaPPrimeCore_iff ((φ i l * φ j m)⁻¹ * (φ j m * φ i l) : ↥L₀).2).2 ?_
    show ((b ^ i)⁻¹ * (l : G) * b ^ i * ((b ^ j)⁻¹ * (m : G) * b ^ j))⁻¹ *
      ((b ^ j)⁻¹ * (m : G) * b ^ j * ((b ^ i)⁻¹ * (l : G) * b ^ i)) ∈ GLAPPrimeCoreOf p L₀
    have e : ((b ^ i)⁻¹ * (l : G) * b ^ i * ((b ^ j)⁻¹ * (m : G) * b ^ j))⁻¹ *
        ((b ^ j)⁻¹ * (m : G) * b ^ j * ((b ^ i)⁻¹ * (l : G) * b ^ i)) =
        ⁅((b ^ j)⁻¹ * (m : G) * b ^ j)⁻¹, ((b ^ i)⁻¹ * (l : G) * b ^ i)⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact hcomm j i hj hi (Ne.symm hij) _ ((K j).inv_mem hc) _ ((K i).inv_mem ha)
  let Pn : ℕ → (↥L → PQuot p L₀) := fun n l => ((List.range n).map (fun i => f i l)).prod
  have Pn_succ : ∀ n l, Pn (n + 1) l = Pn n l * f n l := fun n l => by
    simp only [Pn, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
  have Pn_one : ∀ n, Pn n 1 = 1 := fun n => by
    simp [Pn, map_one]
  have Pn_mul : ∀ n, n ≤ p → ∀ l m : ↥L, Pn n (l * m) = Pn n l * Pn n m := by
    intro n
    induction n with
    | zero => intro _ l m; simp [Pn]
    | succ n ih =>
      intro hn l m
      have ih' := ih (by omega) l m
      have hcm : Commute (f n l) (Pn n m) := by
        apply Commute.list_prod_right
        intro y hy
        simp only [List.mem_map, List.mem_range] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        exact hfc n i (by omega) (by omega) (by omega) l m
      rw [Pn_succ, Pn_succ, Pn_succ, ih', map_mul]
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc (f n l) (Pn n m) (f n m), hcm.eq, mul_assoc]
  let P : ↥L →* PQuot p L₀ :=
    { toFun := Pn p
      map_one' := Pn_one p
      map_mul' := fun l m => Pn_mul p le_rfl l m }
  have hbL₀ : b ∈ Subgroup.normalizer (L₀ : Set G) :=
    le_normalizer_closureIn L (Subgroup.zpowers b) (Subgroup.mem_zpowers b)
  have conjf : ∀ (i : ℕ) (l : ↥L), lemma102_conjQ p hbL₀ (f i l) = f (i + 1) l := by
    intro i l
    show lemma102_conjQ p hbL₀ (QuotientGroup.mk (φ i l)) = QuotientGroup.mk (φ (i + 1) l)
    rw [lemma102_conjQ_mk]
    congr 1
    apply Subtype.ext
    rw [lemma102_conjHomL_val]
    show b⁻¹ * ((b ^ i)⁻¹ * (l : G) * b ^ i) * b = (b ^ (i + 1))⁻¹ * (l : G) * b ^ (i + 1)
    rw [pow_succ]
    group
  have hdec : ∀ l : ↥L, ∃ R : PQuot p L₀, P l = f 0 l * R ∧
      lemma102_conjQ p hbL₀ (P l) = R * f 0 l ∧ ∀ m : ↥L, Commute (f 0 m) R := by
    intro l
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    have hrange : List.range p = List.range (q + 1) := by rw [hq]
    set R : PQuot p L₀ := ((List.range q).map (fun i => f (i + 1) l)).prod with hRdef
    have hPR : P l = f 0 l * R := by
      show ((List.range p).map (fun i => f i l)).prod = _
      rw [hrange, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      rfl
    have hf_p : f (q + 1) l = f 0 l := by
      show QuotientGroup.mk (φ (q + 1) l) = QuotientGroup.mk (φ 0 l)
      congr 1
      apply Subtype.ext
      show (b ^ (q + 1))⁻¹ * (l : G) * b ^ (q + 1) = (b ^ 0)⁻¹ * (l : G) * b ^ 0
      rw [← hq, hbp, pow_zero]
    have hcR : ∀ m : ↥L, Commute (f 0 m) R := by
      intro m
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact hfc 0 (i + 1) (by have := hp.one_lt; omega) (by omega) (by omega) m l
    refine ⟨R, hPR, ?_, hcR⟩
    have hconj : lemma102_conjQ p hbL₀ (P l) = ((List.range (q + 1)).map (fun i => f (i + 1) l)).prod := by
      show lemma102_conjQ p hbL₀ ((List.range p).map (fun i => f i l)).prod = _
      rw [map_list_prod, List.map_map, hrange]
      congr 1
      apply List.map_congr_left
      intro i _
      exact conjf i l
    rw [hconj, List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      hf_p]
  have hfixP : ∀ l : ↥L, lemma102_conjQ p hbL₀ (P l) = P l := by
    intro l
    obtain ⟨R, hPR, hconj, hcR⟩ := hdec l
    rw [hconj, hPR]
    exact (hcR l).eq.symm
  have hOker : ∀ l : ↥L, l ∈ GLAPPrimeCore p ↥L → P l = 1 := by
    intro l hl
    have hlO : (l : G) ∈ GLAPPrimeCoreOf p L := (lemma102_mem_glaPPrimeCore_iff l.2).1 hl
    have hf1 : ∀ i : ℕ, f i l = 1 := by
      intro i
      show QuotientGroup.mk (φ i l) = 1
      rw [QuotientGroup.eq_one_iff]
      refine (lemma102_mem_glaPPrimeCore_iff (φ i l).2).2 ?_
      show (b ^ i)⁻¹ * (l : G) * b ^ i ∈ GLAPPrimeCoreOf p L₀
      have hbi : b ^ i ∈ Subgroup.normalizer (L₀ : Set G) := Subgroup.pow_mem _ hbL₀ i
      have hn : (b ^ i)⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L₀ : Set G) :=
        Subgroup.inv_mem _ (normalizer_le_normalizer_glaPPrimeCoreOf p L₀ hbi)
      have h0 : (l : G) ∈ GLAPPrimeCoreOf p L₀ := hLO hlO
      have := (Subgroup.mem_normalizer_iff.1 hn (l : G)).1 h0
      rwa [inv_inv] at this
    show ((List.range p).map (fun i => f i l)).prod = 1
    apply List.prod_eq_one
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hf1 i
  have hPne : ∃ l : ↥L, P l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hcommL0 : ∀ l m : ↥L, Commute (f 0 l) (f 0 m) := by
      intro l m
      obtain ⟨R, hPR, -, hRc⟩ := hdec l
      have h1 : f 0 l = R⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hPR]; exact hcon l)
      have h2 : Commute (f 0 m) (f 0 l) := by rw [h1]; exact (hRc m).inv_right
      exact h2.symm
    have hφ0 : ∀ l : ↥L, ((φ 0 l : ↥L₀) : G) = (l : G) := fun l => by
      show (b ^ 0)⁻¹ * (l : G) * b ^ 0 = l
      simp
    have hcomL : ∀ l m : ↥L, ((l : G) * (m : G))⁻¹ * ((m : G) * (l : G)) ∈ GLAPPrimeCoreOf p L := by
      intro l m
      have h' : QuotientGroup.mk (φ 0 l) * QuotientGroup.mk (φ 0 m) =
          QuotientGroup.mk (φ 0 m) * QuotientGroup.mk (φ 0 l) := hcommL0 l m
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h'
      have hv : ((φ 0 l * φ 0 m)⁻¹ * (φ 0 m * φ 0 l) : ↥L₀).1 ∈ GLAPPrimeCoreOf p L₀ :=
        (lemma102_mem_glaPPrimeCore_iff _).1 h'
      have e2 : ((φ 0 l * φ 0 m)⁻¹ * (φ 0 m * φ 0 l) : ↥L₀).1 =
          ((l : G) * (m : G))⁻¹ * ((m : G) * (l : G)) := by
        simp [hφ0]
      rw [e2] at hv
      have hLm : ((l : G) * (m : G))⁻¹ * ((m : G) * (l : G)) ∈ L :=
        L.mul_mem (L.inv_mem (L.mul_mem l.2 m.2)) (L.mul_mem m.2 l.2)
      have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hLcomp.2.1
      rw [← hinf]
      exact ⟨hLm, hv⟩
    have hcomQ : ∀ x y : PQuot p L, x * y = y * x := by
      intro x y
      induction x using QuotientGroup.induction_on with
      | H l =>
        induction y using QuotientGroup.induction_on with
        | H m =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          exact (lemma102_mem_glaPPrimeCore_iff ((l * m)⁻¹ * (m * l) : ↥L).2).2 (hcomL l m)
    have hqs : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
    have hcommut : commutator (PQuot p L) ≤ ⊥ :=
      Subgroup.commutator_le.2 fun g _ h _ =>
        Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcomQ g h))
    rw [hqs.1] at hcommut
    haveI := isQuasisimple_nontrivial hqs
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (PQuot p L)
    exact hxy ((Subgroup.mem_bot.1 (hcommut (Subgroup.mem_top x))).trans
      (Subgroup.mem_bot.1 (hcommut (Subgroup.mem_top y))).symm)
  have hqs : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI := isQuasisimple_nontrivial hqs
  let Pbar : PQuot p L →* PQuot p L₀ :=
    QuotientGroup.lift (GLAPPrimeCore p ↥L) P (fun l hl => (MonoidHom.mem_ker).2 (hOker l hl))
  have hPbar : ∀ l : ↥L, Pbar (QuotientGroup.mk l) = P l := fun l => rfl
  have hkerTop : Pbar.ker ≠ ⊤ := by
    intro htop
    obtain ⟨l, hl⟩ := hPne
    apply hl
    have hmem : (QuotientGroup.mk l : PQuot p L) ∈ Pbar.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hPbar] at hmem
    exact hmem
  have hkerC : Pbar.ker ≤ Subgroup.center (PQuot p L) :=
    le_center_of_normal_of_isQuasisimple hqs inferInstance hkerTop
  have hY : CFSG.pPrimeCore p (PQuot p L) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  obtain ⟨k, hk⟩ := lemma102_card_central_pPower hp hY hkerC
  have hcard : Nat.card (PQuot p L) = Nat.card Pbar.ker * Nat.card Pbar.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Pbar.ker, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange Pbar).toEquiv
  have hrange : Pbar.range ≤ lemma102_fixSub p hbL₀ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    show lemma102_conjQ p hbL₀ (P l) = P l
    exact hfixP l
  have hrne : Nat.card Pbar.range ≠ 0 := (Nat.card_pos (α := Pbar.range)).ne'
  have hfne : Nat.card (lemma102_fixSub p hbL₀) ≠ 0 := (Nat.card_pos (α := lemma102_fixSub p hbL₀)).ne'
  unfold card2
  rw [lemma102_centCard2_eq_fixSub p hbL₀, hcard, hk, lemma102_twoPart_pow_mul hp hp2 hrne]
  exact lemma102_twoPart_le_of_dvd hfne (Subgroup.card_dvd_of_le hrange)


theorem step_easy (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) {b : G} (hbB' : b ∈ B')
    (hcase : ¬ (b ∈ Subgroup.normalizer (L : Set G) ∧ ¬ CentMod p L b)) :
    card2 p L ≤ centCard2 p (closureIn L (Subgroup.zpowers b)) b := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hrel.1.2.2
  have hbp : b ^ p = 1 := hrel.2.1.1.1.2 b hbB'
  have hbx : b * x = x * b :=
    congrArg Subtype.val (hrel.2.1.1.1.1.is_comm.comm ⟨b, hbB'⟩ ⟨x, hrel.2.2.1⟩)
  by_cases hbN : b ∈ Subgroup.normalizer (L : Set G)
  · have hcm : CentMod p L b := by
      by_contra h
      exact hcase ⟨hbN, h⟩
    rw [closureIn_eq_self (Subgroup.zpowers_le.2 hbN)]
    have hid : ∀ q : PQuot p L, lemma102_conjQ p hbN q = q := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H l =>
        rw [lemma102_conjQ_mk, QuotientGroup.eq]
        refine (lemma102_mem_glaPPrimeCore_iff ((lemma102_conjHomL hbN l)⁻¹ * l : ↥L).2).2 ?_
        show ((lemma102_conjHomL hbN l : ↥L) : G)⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L
        rw [lemma102_conjHomL_val]
        have e : (b⁻¹ * (l : G) * b)⁻¹ * (l : G) = ((l : G)⁻¹ * (b⁻¹ * (l : G) * b))⁻¹ := by
          group
        rw [e]
        exact Subgroup.inv_mem _ (lemma102_mem_glaPPrimeCoreOf_comm hcm l.2)
    have htop : lemma102_fixSub p hbN = ⊤ := (Subgroup.eq_top_iff' _).2 fun q => hid q
    rw [lemma102_centCard2_eq_fixSub p hbN, htop, Subgroup.card_top]
    rfl
  · exact lemma102_easy_core hp hc.ctx.odd hL (Subgroup.mem_centralizer_singleton_iff.2 hbx) hbp hbN


theorem x_innDiag (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L'))
    (hKx' : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G))) (h2 : IsChevSimple 2 (PSimple p L'))
    (hxprop : ¬ R2Prop p x L') (hxN : x ∈ Subgroup.normalizer (L' : Set G)) :
    InnDiagOn p (Subgroup.zpowers x) L' := by
  classical
  obtain ⟨-, hS', hxB', -⟩ := hrel
  by_contra hn
  have hnid : NonInnDiag p x L' := ⟨hxN, hn⟩
  rcases hin.dich B' x' L' hS' hKx' h2 x hxB' hnid with hf | ⟨hp3, htd⟩
  · exact hxprop (Or.inl hf)
  · subst hp3
    exact hxprop (Or.inr ⟨rfl, htd, hxN, fun hinn =>
      hn (hin.aut.inner_innDiag _ L' x hS'.2.2 h2 hxN hinn)⟩)

theorem r2Prop_mem_normalizer {g : G} {L : Subgroup G} (h : R2Prop p g L) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.1
  · exact h.1

theorem step_I148 (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) (hp3 : p = 3) (htd : IsTD4 3 L')
    (hxN : x ∈ Subgroup.normalizer (L' : Set G)) (hnc : ¬ CentMod 3 L' x)
    (hxinn : InnDiagOn 3 (Subgroup.zpowers x) L') (hR : R2TD4 p B' L') :
    r2 p B L ≤ r2 p B' L' := by
  classical
  subst hp3
  have hp : Nat.Prime 3 := hc.ctx.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS := hrel.1
  have hS' := hrel.2.1
  have hL : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hL'c : GLAPComponent 3 (Subgroup.centralizer ({x'} : Set G)) L' := hS'.2.2
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod 3 L x' := hrel.2.2.2.2.2.1
  have hx'p : IsPGroup 3 (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hS'.1.1 hx'B'
  obtain ⟨hIc, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  have hPI : Nat.card (PQuot 3 L) = Nat.card (PQuot 3 (Ipart 3 L x')) :=
    Nat.card_congr eIL.symm.toEquiv
  have hIL' : Ipart 3 L x' ≤ L' := (lemma102_I_le hp hin.i183 hc.ctx.kProper hc.ctx.simple
    hc.ctx.nonabelian hrel).2 hxN
  have hIC : Ipart 3 L x' ≤ Subgroup.centralizer ({x} : Set G) :=
    (lemma102_glaPLayer_le _).trans (inf_le_left.trans hL.1)
  have hrange : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L')).comp
      (Subgroup.inclusion hIL')).range ≤ lemma102_fixSub 3 hxN := by
    rintro _ ⟨i, rfl⟩
    show lemma102_conjQ 3 hxN _ = (MonoidHom.id _) _
    have hiC : (i : G) * x = x * (i : G) := Subgroup.mem_centralizer_singleton_iff.1 (hIC i.2)
    have hconj : lemma102_conjHomL hxN (Subgroup.inclusion hIL' i) = Subgroup.inclusion hIL' i := by
      apply Subtype.ext
      rw [lemma102_conjHomL_val]
      show x⁻¹ * (i : G) * x = (i : G)
      rw [mul_assoc, hiC, inv_mul_cancel_left]
    rw [MonoidHom.id_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, lemma102_conjQ_mk, hconj]
  have hdvd : Nat.card (PQuot 3 (Ipart 3 L x')) ∣ Nat.card (lemma102_fixSub 3 hxN) :=
    (lemma102_card_dvd_range hp hIL').trans (Subgroup.card_dvd_of_le hrange)
  have hcI : card2 3 (Ipart 3 L x') ≤ centCard2 3 L' x := by
    rw [lemma102_centCard2_eq_fixSub 3 hxN]
    exact lemma102_twoPart_le_of_dvd (Nat.card_pos (α := lemma102_fixSub 3 hxN)).ne' hdvd
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hS.2.1.1
  have hI148 : centCard2 3 L' x ^ 2 ≤ card2 3 L' := hin.i148 _ L' x hL'c htd hx3 hxinn hnc
  have hR' : r2 3 B' L' = Nat.sqrt (card2 3 L') := by
    unfold r2
    rw [if_pos hR]
  have hLI : card2 3 L = card2 3 (Ipart 3 L x') := by
    unfold card2
    rw [hPI]
  have hsq : centCard2 3 L' x ≤ Nat.sqrt (card2 3 L') := Nat.le_sqrt'.2 hI148
  rw [hR']
  calc r2 3 B L ≤ card2 3 L := r2_le_card2 3 B L
    _ = card2 3 (Ipart 3 L x') := hLI
    _ ≤ centCard2 3 L' x := hcI
    _ ≤ Nat.sqrt (card2 3 L') := hsq

theorem lemma102_marking_transport {X Y : Type} [Group X] [Group Y] (hY : commutator Y = ⊤)
    (e : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X)
    {P : CFSG.Assembly.LargeEvenMarkProp X} {P' : CFSG.Assembly.LargeEvenMarkProp Y}
    (h : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F (e.trans θ))
    (hM : CFSG.Assembly.LargeEvenMarking X P) : CFSG.Assembly.LargeEvenMarking Y P' := by
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  refine ⟨hY, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, e.trans θ, h lab R I F θ hθ⟩

theorem lemma102_innDiagOn_mono {p : ℕ} {A A' L : Subgroup G} (hAA : A ≤ A') (h : InnDiagOn p A' L) :
    InnDiagOn p A L := by
  refine ⟨hAA.trans h.1, CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h.2⟩
  intro lab R _ I F θ hP a ha
  exact hP a (hAA ha)


theorem lemma102_lift_inner {Y : Type} [Group Y] (hY : commutator Y = ⊤) (α : Y →* Y) {c : Y}
    (h : ∀ y : Y, (α y)⁻¹ * (c * y * c⁻¹) ∈ Subgroup.center Y) :
    ∀ y : Y, α y = c * y * c⁻¹ := by
  have hz : ∀ y : Y, y⁻¹ * (c⁻¹ * α y * c) ∈ Subgroup.center Y := by
    intro y
    set w := (α y)⁻¹ * (c * y * c⁻¹) with hw
    have hwc : w ∈ Subgroup.center Y := h y
    have hwi : w⁻¹ ∈ Subgroup.center Y := Subgroup.inv_mem _ hwc
    have hc' : c⁻¹ * w⁻¹ * c = w⁻¹ := by
      rw [Subgroup.mem_center_iff.1 hwi c⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    have e : y⁻¹ * (c⁻¹ * α y * c) = c⁻¹ * w⁻¹ * c := by
      rw [hw]
      group
    rw [e, hc']
    exact hwi
  let zh : Y →* Subgroup.center Y :=
    MonoidHom.mk' (fun y => (⟨y⁻¹ * (c⁻¹ * α y * c), hz y⟩ : Subgroup.center Y)) (by
      intro y₁ y₂
      apply Subtype.ext
      have hC : Commute y₂ (y₁⁻¹ * (c⁻¹ * α y₁ * c)) := Subgroup.mem_center_iff.1 (hz y₁) y₂
      show (y₁ * y₂)⁻¹ * (c⁻¹ * α (y₁ * y₂) * c) =
        (y₁⁻¹ * (c⁻¹ * α y₁ * c)) * (y₂⁻¹ * (c⁻¹ * α y₂ * c))
      rw [map_mul]
      have e1 : (y₁ * y₂)⁻¹ * (c⁻¹ * (α y₁ * α y₂) * c) =
          y₂⁻¹ * (y₁⁻¹ * (c⁻¹ * α y₁ * c)) * (c⁻¹ * α y₂ * c) := by group
      rw [e1, hC.inv_left.eq]
      group)
  have hcomm_center : ∀ u v : Subgroup.center Y, Commute u v := fun u v =>
    Subtype.ext (Subgroup.mem_center_iff.1 v.2 u.1)
  have hker : commutator Y ≤ zh.ker := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm_center _ _)
  have htop : (⊤ : Subgroup Y) ≤ zh.ker := hY ▸ hker
  intro y
  have hy : zh y = 1 := htop (Subgroup.mem_top y)
  have hy' : y⁻¹ * (c⁻¹ * α y * c) = 1 := congrArg Subtype.val hy
  have hcy : c⁻¹ * α y * c = y := by
    calc c⁻¹ * α y * c = y * (y⁻¹ * (c⁻¹ * α y * c)) := by group
      _ = y := by rw [hy', mul_one]
  calc α y = c * (c⁻¹ * α y * c) * c⁻¹ := by group
    _ = c * y * c⁻¹ := by rw [hcy]


theorem lemma102_cover_equiv {p : ℕ} (hp : p.Prime) {I L : Subgroup G} (hIL : I ≤ L)
    (hsup : I ⊔ GLAPPrimeCoreOf p L = L) :
    ∃ F : PQuot p I ≃* PQuot p L, ∀ w : ↥I,
      F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hO_eq : GLAPPrimeCoreOf p I = I ⊓ GLAPPrimeCoreOf p L := (cover_facts hp hIL hsup).1
  have hOI : GLAPPrimeCore p ↥I ≤ (GLAPPrimeCore p ↥L).comap (Subgroup.inclusion hIL) := by
    intro w hw
    rw [Subgroup.mem_comap]
    have hw' : (w : G) ∈ GLAPPrimeCoreOf p I := (lemma102_mem_glaPPrimeCore_iff w.2).1 hw
    rw [hO_eq] at hw'
    exact (lemma102_mem_glaPPrimeCore_iff (hIL w.2)).2 hw'.2
  set F : PQuot p I →* PQuot p L :=
    QuotientGroup.map (GLAPPrimeCore p ↥I) (GLAPPrimeCore p ↥L) (Subgroup.inclusion hIL) hOI
    with hF
  have hFmk : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w) :=
    fun w => QuotientGroup.map_mk _ _ _ _ _
  have hIO' : I ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    hIL.trans (le_normalizer_glaPPrimeCoreOf p L)
  have hFbij : Function.Bijective F := by
    refine ⟨(injective_iff_map_eq_one F).2 ?_, ?_⟩
    · intro q hq
      induction q using QuotientGroup.induction_on with
      | H w =>
        rw [hFmk, QuotientGroup.eq_one_iff] at hq
        rw [QuotientGroup.eq_one_iff]
        have hwO : (w : G) ∈ GLAPPrimeCoreOf p I := by
          rw [hO_eq]
          exact ⟨w.2, (lemma102_mem_glaPPrimeCore_iff (hIL w.2)).1 hq⟩
        exact (lemma102_mem_glaPPrimeCore_iff w.2).2 hwO
    · intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl : (l : G) ∈ (I ⊔ GLAPPrimeCoreOf p L : Subgroup G) := hsup.symm ▸ l.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIO'] at hl
      obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hl
      refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
      rw [hFmk, QuotientGroup.eq]
      have hXO : y⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L := by
        rw [← hyz, inv_mul_cancel_left]
        exact hz
      exact (lemma102_mem_glaPPrimeCore_iff ((Subgroup.inclusion hIL ⟨y, hy⟩)⁻¹ * l).2).2 hXO
  exact ⟨MulEquiv.ofBijective F hFbij, fun w => hFmk w⟩

theorem lemma102_cover_pSimple {p : ℕ} {I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} :
    Nonempty (PSimple p I ≃* PSimple p L) := nonempty_pSimple_congr F


theorem lemma102_cover_conj {p : ℕ} {I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} {hIL : I ≤ L}
    (hF : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w))
    {a : G} (haI : a ∈ Subgroup.normalizer (I : Set G)) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (q : PQuot p I) : F (lemma102_conjQ p haI q) = lemma102_conjQ p haL (F q) := by
  induction q using QuotientGroup.induction_on with
  | H w =>
    rw [lemma102_conjQ_mk, hF, hF, lemma102_conjQ_mk]
    congr 1

theorem lemma102_indRel_cover {p : ℕ} {I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} {hIL : I ≤ L}
    (hF : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w))
    {a : G} (haI : a ∈ Subgroup.normalizer (I : Set G)) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (q q' : PQuot p I) : indRel p L a (F q) (F q') ↔ indRel p I a q q' := by
  rw [lemma102_indRel_iff_conjQ haL, lemma102_indRel_iff_conjQ haI, ← lemma102_cover_conj hF haI haL q]
  exact F.injective.eq_iff

theorem lemma102_primeField_mono {p : ℕ} {lab : CFSG.Assembly.LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} {isα isβ : MulAut R → Prop} (h : GLAPrimeField p lab I F isα)
    (hi : ∀ φ, isα φ → isβ φ) : GLAPrimeField p lab I F isβ := by
  obtain ⟨h1, f, hf, u, hu, hord, hα⟩ := h
  exact ⟨h1, f, hf, u, hu, hord, hi _ hα⟩

theorem lemma102_innDiagOn_cover {p : ℕ} {A I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} {hIL : I ≤ L}
    (hF : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w))
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) (hY : commutator (PQuot p I) = ⊤)
    (h : InnDiagOn p A L) : InnDiagOn p A I := by
  let eS : PSimple p I ≃* PSimple p L := QuotientGroup.congr _ _ F (Subgroup.map_center_eq F)
  have hnat : ∀ q : PQuot p I, eS (QuotientGroup.mk q) = QuotientGroup.mk (F q) := fun q =>
    QuotientGroup.congr_mk _ _ _ _ q
  refine ⟨hAI, ?_⟩
  refine lemma102_marking_transport hY eS (fun lab R _ I' F' θ hP a ha => ?_) h.2
  obtain ⟨φ, hφ, hφ'⟩ := hP a ha
  refine ⟨φ, hφ, ?_⟩
  intro q q' hq
  have haL : a ∈ Subgroup.normalizer (L : Set G) := (h.1 ha)
  have haI : a ∈ Subgroup.normalizer (I : Set G) := hAI ha
  show φ (θ (eS (QuotientGroup.mk q))) = θ (eS (QuotientGroup.mk q'))
  rw [hnat q, hnat q']
  exact hφ' (F q) (F q') ((lemma102_indRel_cover hF haI haL q q').2 hq)


theorem lemma102_fieldOn_cover {p : ℕ} {b : G} {I L : Subgroup G} {F : PQuot p I ≃* PQuot p L} {hIL : I ≤ L}
    (hF : ∀ w : ↥I, F (QuotientGroup.mk w) = QuotientGroup.mk (Subgroup.inclusion hIL w))
    (hbI : b ∈ Subgroup.normalizer (I : Set G)) (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hY : commutator (PQuot p L) = ⊤) (h : FieldOn p b I) : FieldOn p b L := by
  let eS : PSimple p I ≃* PSimple p L := QuotientGroup.congr _ _ F (Subgroup.map_center_eq F)
  have hnat : ∀ q : PQuot p I, eS (QuotientGroup.mk q) = QuotientGroup.mk (F q) := fun q =>
    QuotientGroup.congr_mk _ _ _ _ q
  refine ⟨hbL, ?_⟩
  refine lemma102_marking_transport hY eS.symm (fun lab R _ I' F' θ hP => ?_) h.2
  refine lemma102_primeField_mono hP (fun φ hφ => ?_)
  intro r r' hr
  obtain ⟨q, rfl⟩ : ∃ q, F q = r := ⟨F.symm r, F.apply_symm_apply r⟩
  obtain ⟨q', rfl⟩ : ∃ q', F q' = r' := ⟨F.symm r', F.apply_symm_apply r'⟩
  have e1 : eS.symm (QuotientGroup.mk (F q)) = QuotientGroup.mk q := by
    rw [← hnat q, MulEquiv.symm_apply_apply]
  have e2 : eS.symm (QuotientGroup.mk (F q')) = QuotientGroup.mk q' := by
    rw [← hnat q', MulEquiv.symm_apply_apply]
  show φ (θ (eS.symm (QuotientGroup.mk (F q)))) = θ (eS.symm (QuotientGroup.mk (F q')))
  rw [e1, e2]
  exact hφ q q' ((lemma102_indRel_cover hF hbI hbL q q').1 hr)

theorem lemma102_graph_iso {p : ℕ} {R : Type} [Group R] {y : G} {I L : Subgroup G}
    (e : PSimple p I ≃* PSimple p L) (hIso : IsoPresAct p y I L e) {θ : PSimple p L ≃* R} {φ : MulAut R}
    (h : GLAInduces θ (indRel p L y) φ) : GLAInduces (e.trans θ) (indRel p I y) φ := by
  intro q q' hq
  obtain ⟨r, r', hr, hrq, hrq'⟩ := hIso (QuotientGroup.mk q) (QuotientGroup.mk q') ⟨q, q', hq, rfl, rfl⟩
  show φ (θ (e (QuotientGroup.mk q))) = θ (e (QuotientGroup.mk q'))
  rw [← hrq, ← hrq']
  exact h r r' hr

theorem lemma102_fieldOn_iso {p : ℕ} {b : G} {I L : Subgroup G} (e : PSimple p I ≃* PSimple p L)
    (hIso : IsoPresAct p b I L e) (hbI : b ∈ Subgroup.normalizer (I : Set G))
    (hY : commutator (PQuot p I) = ⊤) (h : FieldOn p b L) : FieldOn p b I := by
  refine ⟨hbI, ?_⟩
  refine lemma102_marking_transport hY e (fun lab R _ I' F' θ hP => ?_) h.2
  exact lemma102_primeField_mono hP (fun φ hφ => lemma102_graph_iso e hIso hφ)


theorem lemma102_inducesInnerMod_of_cover {p : ℕ} (hp : p.Prime) {I L : Subgroup G} {b : G} (hIL : I ≤ L)
    (hsup : I ⊔ GLAPPrimeCoreOf p L = L) (hbI : b ∈ Subgroup.normalizer (I : Set G))
    (h : InducesInnerMod p L b) : InducesInnerMod p I b := by
  obtain ⟨l₀, hl₀, hl⟩ := h
  have hl₀' : l₀ ∈ (I ⊔ GLAPPrimeCoreOf p L : Subgroup G) := hsup.symm ▸ hl₀
  have hIO : I ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    hIL.trans (le_normalizer_glaPPrimeCoreOf p L)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIO] at hl₀'
  obtain ⟨i₀, hi₀, o₀, ho₀, rfl⟩ := Set.mem_mul.mp hl₀'
  refine ⟨i₀, hi₀, fun y hy => ?_⟩
  have hyL : y ∈ L := hIL hy
  have hA := hl y hyL
  have hw : i₀⁻¹ * y * i₀ ∈ L := L.mul_mem (L.mul_mem (hIL (I.inv_mem hi₀)) hyL) (hIL hi₀)
  have hwN : (i₀⁻¹ * y * i₀)⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    Subgroup.inv_mem _ (le_normalizer_glaPPrimeCoreOf p L hw)
  have hB : (i₀⁻¹ * y * i₀)⁻¹ * ((i₀ * o₀)⁻¹ * y * (i₀ * o₀)) ∈ GLAPPrimeCoreOf p L := by
    have e : (i₀⁻¹ * y * i₀)⁻¹ * ((i₀ * o₀)⁻¹ * y * (i₀ * o₀)) =
        ((i₀⁻¹ * y * i₀)⁻¹ * o₀⁻¹ * (i₀⁻¹ * y * i₀)⁻¹⁻¹) * o₀ := by
      group
    rw [e]
    exact Subgroup.mul_mem _
      (by simpa using (Subgroup.mem_normalizer_iff.1 hwN o₀⁻¹).1 (Subgroup.inv_mem _ ho₀)) ho₀
  have hsum : (i₀⁻¹ * y * i₀)⁻¹ * (b⁻¹ * y * b) =
      ((i₀⁻¹ * y * i₀)⁻¹ * ((i₀ * o₀)⁻¹ * y * (i₀ * o₀))) *
        (((i₀ * o₀)⁻¹ * y * (i₀ * o₀))⁻¹ * (b⁻¹ * y * b)) := by
    group
  have hinI : (i₀⁻¹ * y * i₀)⁻¹ * (b⁻¹ * y * b) ∈ I :=
    I.mul_mem (I.inv_mem (I.mul_mem (I.mul_mem (I.inv_mem hi₀) hy) hi₀))
      (lemma102_conj_inv_mem hbI hy)
  rw [hsum] at hinI ⊢
  exact (lemma102_inf_le hp hIL) ⟨hinI, Subgroup.mul_mem _ hB hA⟩


theorem lemma102_conjQ_surjective {p : ℕ} {L : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (L : Set G)) : Function.Surjective (lemma102_conjQ p hu) := by
  intro r
  refine ⟨lemma102_conjQ p (Subgroup.inv_mem _ hu) r, ?_⟩
  induction r using QuotientGroup.induction_on with
  | H w =>
    rw [lemma102_conjQ_mk, lemma102_conjQ_mk]
    congr 1
    apply Subtype.ext
    rw [lemma102_conjHomL_val, lemma102_conjHomL_val]
    group

theorem lemma102_conjQ_mem_center {p : ℕ} {L : Subgroup G} {u : G} (hu : u ∈ Subgroup.normalizer (L : Set G))
    {z : PQuot p L} (hz : z ∈ Subgroup.center (PQuot p L)) :
    lemma102_conjQ p hu z ∈ Subgroup.center (PQuot p L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨s, rfl⟩ := lemma102_conjQ_surjective hu g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]

theorem lemma102_inducesInnerMod_iso {p : ℕ} {I L' : Subgroup G} {b : G}
    (e : PSimple p I ≃* PSimple p L') (hIso : IsoPresAct p b I L' e)
    (hbI : b ∈ Subgroup.normalizer (I : Set G)) (hbL : b ∈ Subgroup.normalizer (L' : Set G))
    (hY : commutator (PQuot p L') = ⊤) (h : InducesInnerMod p I b) : InducesInnerMod p L' b := by
  obtain ⟨i, hi, hi'⟩ := h
  let iu : ↥I := ⟨i⁻¹, I.inv_mem hi⟩
  let u : PQuot p I := QuotientGroup.mk iu
  let π : PQuot p I →* PSimple p I := QuotientGroup.mk' (Subgroup.center (PQuot p I))
  let π' : PQuot p L' →* PSimple p L' := QuotientGroup.mk' (Subgroup.center (PQuot p L'))
  have hA : ∀ q : PQuot p I, lemma102_conjQ p hbI q = u * q * u⁻¹ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hu1 : u * QuotientGroup.mk w * u⁻¹ = QuotientGroup.mk (iu * w * iu⁻¹) := by
        simp only [u, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hu1, lemma102_conjQ_mk, QuotientGroup.eq]
      have e1 : ((((lemma102_conjHomL hbI w)⁻¹ * (iu * w * iu⁻¹) : ↥I)) : G) =
          ((i⁻¹ * (w : G) * i)⁻¹ * (b⁻¹ * (w : G) * b))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, lemma102_conjHomL_val, iu, mul_inv_rev, inv_inv]
        try group
      refine (lemma102_mem_glaPPrimeCore_iff ((lemma102_conjHomL hbI w)⁻¹ * (iu * w * iu⁻¹) : ↥I).2).2 ?_
      rw [e1]
      exact (GLAPPrimeCoreOf p I).inv_mem (hi' (w : G) w.2)
  have hB : ∀ q : PQuot p I, e (π (lemma102_conjQ p hbI q)) = e (π u) * e (π q) * (e (π u))⁻¹ := by
    intro q
    rw [hA q]
    simp only [map_mul, map_inv]
  have hC : ∀ q : PQuot p I, ∃ r : PQuot p L', π' r = e (π q) ∧
      π' (lemma102_conjQ p hbL r) = e (π (lemma102_conjQ p hbI q)) := by
    intro q
    have hs : indRelS p I b (π q) (π (lemma102_conjQ p hbI q)) :=
      ⟨q, lemma102_conjQ p hbI q, (lemma102_indRel_iff_conjQ hbI q (lemma102_conjQ p hbI q)).2 rfl, rfl, rfl⟩
    obtain ⟨r, r', hr, hrq, hrq'⟩ := hIso _ _ hs
    have hrr : lemma102_conjQ p hbL r = r' := (lemma102_indRel_iff_conjQ hbL r r').1 hr
    refine ⟨r, hrq, ?_⟩
    rw [hrr]
    exact hrq'
  obtain ⟨rc, hrc⟩ := QuotientGroup.mk_surjective (e (π u))
  have hD : ∀ r' : PQuot p L', π' (lemma102_conjQ p hbL r') = π' rc * π' r' * (π' rc)⁻¹ := by
    intro r'
    obtain ⟨s, hs⟩ := e.surjective (π' r')
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨r, hr1, hr2⟩ := hC q
    have hsame : π' r = π' r' := by
      rw [hr1, ← hs]
      rfl
    have hz : r⁻¹ * r' ∈ Subgroup.center (PQuot p L') := QuotientGroup.eq.1 hsame
    have hsplit : lemma102_conjQ p hbL r' = lemma102_conjQ p hbL r * lemma102_conjQ p hbL (r⁻¹ * r') := by
      rw [← map_mul]
      congr 1
      group
    have hcz : π' (lemma102_conjQ p hbL (r⁻¹ * r')) = 1 := (QuotientGroup.eq_one_iff _).2 (lemma102_conjQ_mem_center hbL hz)
    rw [hsplit, map_mul, hcz, mul_one]
    have hr2' : π' (lemma102_conjQ p hbL r) = e (π (lemma102_conjQ p hbI q)) := hr2
    rw [hr2', hB q, ← hrc, ← hr1, ← hsame]
    rfl
  have hLift : ∀ y : PQuot p L', lemma102_conjQ p hbL y = rc * y * rc⁻¹ := by
    refine lemma102_lift_inner hY (lemma102_conjQ p hbL) (c := rc) (fun y => ?_)
    have h' : π' (lemma102_conjQ p hbL y) = π' (rc * y * rc⁻¹) := by
      rw [hD y]
      simp only [map_mul, map_inv]
    exact QuotientGroup.eq.1 h'
  obtain ⟨l₁, rfl⟩ := QuotientGroup.mk_surjective rc
  refine ⟨l₁⁻¹, L'.inv_mem l₁.2, fun y hy => ?_⟩
  have h1 := hLift (QuotientGroup.mk ⟨y, hy⟩)
  rw [lemma102_conjQ_mk] at h1
  have key : (QuotientGroup.mk (lemma102_conjHomL hbL ⟨y, hy⟩) : PQuot p L') =
      QuotientGroup.mk (l₁ * ⟨y, hy⟩ * l₁⁻¹) := by
    rw [h1]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h2 : ((lemma102_conjHomL hbL ⟨y, hy⟩)⁻¹ * (l₁ * ⟨y, hy⟩ * l₁⁻¹) : ↥L') ∈ GLAPPrimeCore p ↥L' :=
    QuotientGroup.eq.1 key
  have h3 := (lemma102_mem_glaPPrimeCore_iff _).1 h2
  have h4 := (GLAPPrimeCoreOf p L').inv_mem h3
  convert h4 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, lemma102_conjHomL_val, inv_inv]
  group


theorem lemma102_not_innDiagOn_of_R2Prop {p : ℕ} {X L' : Subgroup G} {b : G} (hin : AutCalcAt G p)
    (hL'c : GLAPComponent p X L') (h2 : IsChevSimple 2 (PSimple p L')) (hprop : R2Prop p b L') :
    ¬ InnDiagOn p (Subgroup.zpowers b) L' := by
  intro hI
  rcases hprop with hf | ⟨hp3, htd, hn⟩
  · exact (hin.field_nonInnDiag X L' b hL'c h2 hf).2 hI
  · subst hp3
    exact (hin.td4_nonInnDiag X L' b hL'c htd hn).2 hI

theorem lemma102_normalizer_I {p : ℕ} {L : Subgroup G} {x' b : G} (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbx' : b * x' = x' * b) :
    b ∈ Subgroup.normalizer (GLAPLayer p (L ⊓ Subgroup.centralizer ({x'} : Set G)) : Set G) := by
  apply mem_normalizer_glaPLayer (p := p)
  have hbC : b ∈ Subgroup.centralizer ({x'} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hbx'
  have hL' := Subgroup.mem_normalizer_iff.1 hbL
  have hC' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hbC)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hL' h) (hC' h)

theorem lemma102_not_mem_zpowers_of_R2Prop {p : ℕ} (hp : p.Prime) {X L' : Subgroup G} {x b : G}
    (hin : AutCalcAt G p) (hL'c : GLAPComponent p X L') (h2 : IsChevSimple 2 (PSimple p L'))
    (hprop : R2Prop p b L') (hbN' : b ∈ Subgroup.normalizer (L' : Set G)) (hx : x ^ p = 1)
    (hxcase : (x ∈ Subgroup.normalizer (L' : Set G) ∧ ¬ CentMod p L' x) →
      InnDiagOn p (Subgroup.zpowers x) L') :
    b ∉ Subgroup.zpowers x := by
  classical
  intro hbx
  haveI : Fact p.Prime := ⟨hp⟩
  have hF1 := lemma102_not_innDiagOn_of_R2Prop hin hL'c h2 hprop
  have hbc : b ∈ centModSubgroup p L' := by
    by_cases hb1 : b = 1
    · rw [hb1]
      exact Subgroup.one_mem _
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hb1
      simpa using hbx
    have hxo : orderOf x = p := orderOf_eq_prime hx hx1
    have hbo : orderOf b = p := by
      have hd : orderOf b ∣ orderOf x := orderOf_dvd_of_mem_zpowers hbx
      rw [hxo] at hd
      have hb1' : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.1 h)
      exact ((Nat.dvd_prime hp).1 hd).resolve_left hb1'
    have hzeq : Subgroup.zpowers b = Subgroup.zpowers x := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbx)
      simp only [Nat.card_zpowers, hbo, hxo, le_refl]
    have hxN : x ∈ Subgroup.normalizer (L' : Set G) :=
      Subgroup.zpowers_le.2 hbN' (by rw [hzeq]; exact Subgroup.mem_zpowers x)
    have hxcm : CentMod p L' x := by
      by_contra hnc
      exact hF1 (lemma102_innDiagOn_mono (le_of_eq hzeq) (hxcase ⟨hxN, hnc⟩))
    have hxm : x ∈ centModSubgroup p L' :=
      mem_centModSubgroup.2 ⟨hxcm.1, fun l hl =>
        hxcm.2 (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers x))⟩
    exact (Subgroup.zpowers_le.2 hxm) hbx
  have hinn : InducesInnerMod p L' b := by
    refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
    have h1 := (mem_centModSubgroup.1 (Subgroup.inv_mem _ hbc)).2 y⁻¹ (Subgroup.inv_mem _ hy)
    have e : (1⁻¹ * y * 1)⁻¹ * (b⁻¹ * y * b) = ⁅y⁻¹, b⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h1
  exact hF1 (hin.inner_innDiag X L' b hL'c h2 hbN' hinn)

theorem step_I155 (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G} {x x' : G}
    (hrel : PumpRel p (B, x, L) (B', x', L')) (h2 : IsChevSimple 2 (PSimple p L')) {b : G}
    (hbB' : b ∈ B') (hprop : R2Prop p b L') (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (hnc : ¬ CentMod p L b)
    (hxcase : (x ∈ Subgroup.normalizer (L' : Set G) ∧ ¬ CentMod p L' x) →
      InnDiagOn p (Subgroup.zpowers x) L' ∧ FieldOn p b L') :
    (NonInnDiag p b L ∧ ¬ (p = 3 ∧ IsTD4 3 L)) ∨
      ((FieldOn p b L' → FieldOn p b L) ∧
        (p = 3 → IsTD4 3 L' → NonInner 3 b L' → IsTD4 3 L ∧ NonInner 3 b L)) := by
  classical
  have hp := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hrel.1.2.2
  have hL'c : GLAPComponent p (Subgroup.centralizer ({x'} : Set G)) L' := hrel.2.1.2.2
  have hxB' : x ∈ B' := hrel.2.2.1
  have hx'B' : x' ∈ B' := hrel.2.2.2.2.1
  have hx'L : CentMod p L x' := hrel.2.2.2.2.2.1
  have hx'1 : x' ≠ 1 := hrel.2.1.2.1.2.1
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hrel.2.1.1.1 hx'B'
  have hx : x ^ p = 1 := hrel.2.1.1.1.2 x hxB'
  have hbp : b ^ p = 1 := hrel.2.1.1.1.2 b hbB'
  have hbx : b * x = x * b :=
    congrArg Subtype.val (hrel.2.1.1.1.1.is_comm.comm ⟨b, hbB'⟩ ⟨x, hxB'⟩)
  have hbx' : b * x' = x' * b :=
    congrArg Subtype.val (hrel.2.1.1.1.1.is_comm.comm ⟨b, hbB'⟩ ⟨x', hx'B'⟩)
  have hxX : x ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (hrel.2.1.1.1.1.is_comm.comm ⟨x, hxB'⟩ ⟨x', hx'B'⟩))
  have hbN' : b ∈ Subgroup.normalizer (L' : Set G) := r2Prop_mem_normalizer hprop
  have hYL : commutator (PQuot p L) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hL).1
  have hYL' : commutator (PQuot p L') = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hL'c).1
  have hJc := step_I_comp hc hin hrel
  have hJL : Ipart p L x' ≤ L := (lemma102_glaPLayer_le _).trans inf_le_left
  obtain ⟨-, -, -, -, hsup, -⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  obtain ⟨F, hF⟩ := lemma102_cover_equiv hp hJL hsup
  have hYJ : commutator (PQuot p (Ipart p L x')) = ⊤ :=
    (isQuasisimple_pQuot_of_glaPComponent hp hJc).1
  have hbJ : b ∈ Subgroup.normalizer (Ipart p L x' : Set G) := lemma102_normalizer_I hbN hbx'
  have hXne : Subgroup.centralizer ({x'} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx'1
  have hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXne
  have hnot : b ∉ Subgroup.zpowers x :=
    lemma102_not_mem_zpowers_of_R2Prop hp hin.aut hL'c h2 hprop hbN' hx (fun h => (hxcase h).1)
  have hI := hin.i155 hp hc.ctx.odd (Subgroup.centralizer ({x'} : Set G)) L' x b hX hL'c h2 hxX hx hbp
    hbx.symm hnot hbN' hxcase (Ipart p L x') hJc hbJ
  rcases hI with ⟨hnid, hnotTD⟩ | ⟨-, e, hIso⟩
  · left
    obtain ⟨-, hnI⟩ := hnid
    have hnidL : ¬ InnDiagOn p (Subgroup.zpowers b) L := fun h =>
      hnI (lemma102_innDiagOn_cover hF (Subgroup.zpowers_le.2 hbJ) hYJ h)
    refine ⟨⟨hbN, hnidL⟩, ?_⟩
    rintro ⟨hp3, hT⟩
    subst hp3
    obtain ⟨eS⟩ := lemma102_cover_pSimple (F := F)
    exact hnotTD ⟨rfl, (catalogIs_congr eS).2 hT⟩
  · right
    refine ⟨fun hF' => ?_, fun hp3 hT' hn' => ?_⟩
    · exact lemma102_fieldOn_cover hF hbJ hbN hYL (lemma102_fieldOn_iso e hIso hbJ hYJ hF')
    · subst hp3
      have hTJ : IsTD4 3 (Ipart 3 L x') := (catalogIs_congr e.symm).1 hT'
      obtain ⟨eS⟩ := lemma102_cover_pSimple (F := F)
      refine ⟨(catalogIs_congr eS).1 hTJ, hbN, fun hinL => hn'.2 ?_⟩
      exact lemma102_inducesInnerMod_iso e hIso hbJ hn'.1 hYL'
        (lemma102_inducesInnerMod_of_cover hp hJL hsup hbJ hinL)

theorem act_congr {X L : Subgroup G} (hL : GLAPComponent p X L) {u v b : G} (hb : b = u * v)
    (hcomm : u * v = v * u) (hv : CentMod p L v) (hbN : b ∈ Subgroup.normalizer (L : Set G)) :
    u ∈ Subgroup.normalizer (L : Set G) ∧ (NonInnDiag p b L ↔ NonInnDiag p u L) ∧
      (FieldOn p b L ↔ FieldOn p u L) ∧ (NonInner p b L ↔ NonInner p u L) ∧
      centCard2 p L b = centCard2 p L u :=
  lemma102_act_congr_aux hb hcomm hv hbN

theorem lemma102_step (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {B B' L L' : Subgroup G}
    {x x' : G} (hrel : PumpRel p (B, x, L) (B', x', L')) (h2 : IsChevSimple 2 (PSimple p L')) :
    IsChevSimple 2 (PSimple p L) ∧ r2 p B L ≤ r2 p B' L' := by
  classical
  have hch : IsChevSimple 2 (PSimple p L) := step_chev2 hc hin hrel h2
  refine ⟨hch, ?_⟩
  have hS : IsSTriple p B x L := hrel.1
  have hS' : IsSTriple p B' x' L' := hrel.2.1
  have hBel : IsElemAbelian p B := hS.1.1
  have hBel' : IsElemAbelian p B' := hS'.1.1
  have hxB' : x ∈ B' := hrel.2.2.1
  have hKx : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hS.2.1.2.1)
  have hKx' : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x'} : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hS'.2.1.2.1)
  have hcard := step_card2 hc hin hrel
  have hrle := r2_le_card2 p B L
  by_cases hbig : card2 p L' ≤ r2 p B' L'
  · exact hrle.trans (hcard.trans hbig)
  push Not at hbig
  obtain ⟨b0, hb0, hp0⟩ := exists_r2prop_of_lt hbig
  obtain ⟨b, hbB', hbprop, hbx⟩ : ∃ b ∈ B', R2Prop p b L' ∧ (R2Prop p x L' → b = x) := by
    by_cases hx : R2Prop p x L'
    · exact ⟨x, hxB', hx, fun _ => rfl⟩
    · exact ⟨b0, hb0, hp0, fun h => absurd h hx⟩
  have hr' : centCard2 p L' b ≤ r2 p B' L' := r2_ge_cent hin.toR2 hS'.2.2 h2 hBel' hbB' hbprop
  have hbN' : b ∈ Subgroup.normalizer (L' : Set G) := r2Prop_mem_normalizer hbprop
  have hchain : centCard2 p (closureIn L (Subgroup.zpowers b)) b ≤ r2 p B' L' :=
    (cent_cover hc hin hrel hbB').trans ((cent_le_diag hc hin hrel hbB' hbN').trans hr')
  by_cases hmain : b ∈ Subgroup.normalizer (L : Set G) ∧ ¬ CentMod p L b
  swap
  · exact hrle.trans ((step_easy hc hin hrel hbB' hmain).trans hchain)
  obtain ⟨hbN, hnc⟩ := hmain
  have hcl : closureIn L (Subgroup.zpowers b) = L := closureIn_eq_self (Subgroup.zpowers_le.2 hbN)
  rw [hcl] at hchain
  have hxL : CentMod p L x := centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hS.2.2.1 hl))
  have hbxne : b ≠ x := fun h => hnc (h ▸ hxL)
  have hxprop : ¬ R2Prop p x L' := fun h => hbxne (hbx h)
  have path : ((x ∈ Subgroup.normalizer (L' : Set G) ∧ ¬ CentMod p L' x) →
      InnDiagOn p (Subgroup.zpowers x) L' ∧ FieldOn p b L') → r2 p B L ≤ r2 p B' L' := by
    intro hxcase
    have hI := step_I155 hc hin hrel h2 hbB' hbprop hbN hnc hxcase
    obtain ⟨u, huBB', v, hvB', hv, hbuv⟩ := hrel.2.2.2.1 b hbB'
    have huB : u ∈ B := (Subgroup.mem_inf.1 huBB').1
    have huB' : u ∈ B' := (Subgroup.mem_inf.1 huBB').2
    have hcomm : u * v = v * u :=
      congrArg Subtype.val (hBel'.1.is_comm.comm (⟨u, huB'⟩ : ↥B') ⟨v, hvB'⟩)
    obtain ⟨huN, hc1, hc2, hc3, hc4⟩ := act_congr hS.2.2 hbuv hcomm hv hbN
    rcases hI with ⟨hnid, hnotTD⟩ | ⟨hF, hT⟩
    · have hnu : NonInnDiag p u L := hc1.1 hnid
      rcases hin.dich B x L hS hKx hch u huB hnu with hfu | ⟨hp3, htd⟩
      · have hnR : ¬ R2TD4 p B L := fun h => hnotTD ⟨h.1, h.2.1⟩
        rw [r2_eq_cent hin.toR2 hS.2.2 hch hBel huB hfu hnR, ← hc4]
        exact hchain
      · exact absurd ⟨hp3, htd⟩ hnotTD
    · rcases hbprop with hfb | ⟨hp3, htd, hnb⟩
      · have hfL : FieldOn p b L := hF hfb
        have hfu : FieldOn p u L := hc2.1 hfL
        have hnR : ¬ R2TD4 p B L := by
          rintro ⟨hp3, htd, -⟩
          subst hp3
          exact hin.aut.td4_not_field _ L u hS.2.2 rfl htd hfu
        rw [r2_eq_cent hin.toR2 hS.2.2 hch hBel huB hfu hnR, ← hc4]
        exact hchain
      · obtain ⟨htdL, hnbL⟩ := hT hp3 htd hnb
        have hnu : NonInner 3 u L := hp3 ▸ hc3.1 (hp3 ▸ hnbL)
        have hRB : R2TD4 p B L := ⟨hp3, htdL, u, huB, ne_one_of_nonInner hnu, hnu⟩
        have hRB' : R2TD4 p B' L' := ⟨hp3, htd, b, hbB', ne_one_of_nonInner hnb, hnb⟩
        unfold r2
        rw [if_pos hRB, if_pos hRB']
        subst hp3
        exact Nat.sqrt_le_sqrt hcard
  by_cases hxc : x ∈ Subgroup.normalizer (L' : Set G) ∧ ¬ CentMod p L' x
  · have hxinn := x_innDiag hin hrel hKx' h2 hxprop hxc.1
    rcases hbprop with hfb | ⟨hp3, htd, hnb⟩
    · exact path fun _ => ⟨hxinn, hfb⟩
    · subst hp3
      exact step_I148 hc hin hrel rfl htd hxc.1 hxc.2 hxinn
        ⟨rfl, htd, b, hbB', ne_one_of_nonInner hnb, hnb⟩
  · exact path fun h => absurd h hxc

theorem lemma102 (hc : S10Ctx G p) (hin : Lemma102Inputs G p) {t t' : Triple G}
    (ht2 : IsS2 p t'.1 t'.2.1 t'.2.2) (h : PumpLe p t t') :
    IsS2 p t.1 t.2.1 t.2.2 ∧ r2 p t.1 t.2.2 ≤ r2 p t'.1 t'.2.2 := by
  obtain ⟨-, -, hchain⟩ := h
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨ht2, le_rfl⟩
  | head hstep _ ih =>
    obtain ⟨hch, hr⟩ := lemma102_step hc hin hstep ih.1.2
    exact ⟨⟨hstep.1, hch⟩, hr.trans ih.2⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
