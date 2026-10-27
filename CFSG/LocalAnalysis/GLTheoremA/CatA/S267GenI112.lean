module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VTables
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore
import CFSG.GroupTheory.PLayer.PIndex
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267CenterMultiplier
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Final
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

section Transport

variable {Q : TauCeti.LieTypeIndex → Prop} {p q : ℕ} {S B : Subgroup Ω}

private theorem top_le_normalizer (H : GenHyp Q p q S B) :
    (⊤ : Subgroup Ω) ≤ Subgroup.normalizer (S : Set Ω) := by
  rw [Subgroup.normalizer_eq_top_iff.2 H.normal]

private noncomputable def actT (H : GenHyp Q p q S B) (b : Ω) :
    MulAut (↥S ⧸ Subgroup.center ↥S) :=
  CFSG.normalizerToCenterQuotientAut S ⊤ (top_le_normalizer H) ⟨b, Subgroup.mem_top b⟩

private theorem actT_pow (H : GenHyp Q p q S B) {b : Ω} (hb : b ^ p = 1) : actT H b ^ p = 1 := by
  unfold actT
  rw [← map_pow]
  have : (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup Ω)) ^ p = 1 := Subtype.ext (by simpa using hb)
  rw [this, map_one]

private theorem actT_ne_one (H : GenHyp Q p q S B) {b : Ω} (hb : b ∉ centModSubgroup p S) :
    actT H b ≠ 1 := by
  intro h
  have h1 := (CFSG.normalizerToCenterQuotientAut_eq_one_iff
    ⟨S267.perfect_of_commutator_self_eq H.perfect⟩ (top_le_normalizer H) _).1 h
  refine hb ⟨top_le_normalizer H (Subgroup.mem_top b), fun l hl => ?_⟩
  have h2 : ⁅l, b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 h1.2 l hl
  rw [h2]
  exact Subgroup.one_mem _

private theorem exists_comp_T (H : GenHyp Q p q S B) {b : Ω} {L : Subgroup Ω}
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (J : Subgroup (↥S ⧸ Subgroup.center ↥S)),
      OddLie p (↥S ⧸ Subgroup.center ↥S) d ∧ Q d.1 ∧ d.1.characteristic = q ∧
      GLAPComponent p (fixSubgroup (actT H b)) J ∧
      ∃ f : ↥L →* ↥J, Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥L := by
  obtain ⟨d, hdq, hQd, ⟨e⟩⟩ := H.lie
  have hp := H.pPrime
  have hodd : OddLie p (↥S ⧸ Subgroup.center ↥S) d :=
    ⟨hp, H.pOdd, ⟨(S267.BadExc.psimpleEquivCenterQuotOfCore H.core).symm.trans e⟩,
      by rw [hdq]; exact H.qOdd, by rw [hdq]; exact fun h => H.qp h.symm⟩
  have hLS : L ≤ S := hL.1.trans inf_le_left
  set α : MulAut ↥S :=
    CFSG.normalizerConjAutOfMem S ⊤ (top_le_normalizer H) ⟨b, Subgroup.mem_top b⟩ with hα
  have hfix : (fixSubgroup α).map S.subtype = S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    rw [hα, show CFSG.normalizerConjAutOfMem S ⊤ (top_le_normalizer H) ⟨b, Subgroup.mem_top b⟩ =
        (Subgroup.normalizerMonoidHom (H := S)) ⟨b, top_le_normalizer H (Subgroup.mem_top b)⟩
      from rfl]
    exact CFSG.map_eqLocus_normalizerMonoidHom S (top_le_normalizer H (Subgroup.mem_top b))
  rw [← hfix] at hL
  have hcop : p.Coprime (Nat.card ↥(fixSubgroup α ⊓ S.subtype.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 S.subtype_injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  obtain ⟨K₁, hK₁, hK₁L⟩ := exists_glaPComponent_map_eq hp S.subtype hcop hL
  set π : ↥S →* ↥S ⧸ Subgroup.center ↥S := QuotientGroup.mk' (Subgroup.center ↥S) with hπ
  have hJ : GLAPComponent p (fixSubgroup (actT H b)) (K₁.map π) :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π
      (by rw [hπ, QuotientGroup.ker_mk']) α (actT H b)
      (fun k => CFSG.normalizerConjAutOfMem_comp_mk S ⊤ (top_le_normalizer H) _ k)
      (QuotientGroup.mk'_surjective _) hp hK₁
  refine ⟨d, K₁.map π, hodd, hQd, hdq, hJ, ?_⟩
  have hmemK : ∀ l : ↥L, Subgroup.inclusion hLS l ∈ K₁ := by
    intro l
    have hl : (l : Ω) ∈ K₁.map S.subtype := by rw [hK₁L]; exact l.2
    obtain ⟨k, hk, hkl⟩ := hl
    have : k = Subgroup.inclusion hLS l := Subtype.ext hkl
    rw [← this]
    exact hk
  refine ⟨(π.comp (Subgroup.inclusion hLS)).codRestrict (K₁.map π)
    (fun l => ⟨_, hmemK l, rfl⟩), ?_, ?_⟩
  · rintro ⟨y, k, hk, rfl⟩
    have hkL : ((k : ↥S) : Ω) ∈ L := by rw [← hK₁L]; exact ⟨k, hk, rfl⟩
    refine ⟨⟨k, hkL⟩, Subtype.ext ?_⟩
    rfl
  · intro l hl
    have h1 : π (Subgroup.inclusion hLS l) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine Subgroup.mem_center_iff.2 fun l' => Subtype.ext ?_
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 (Subgroup.inclusion hLS l'))
    exact h2

theorem isQuasisimple_of_genCompQuasiOn (h2 : GenCompQuasiOn Q) (H : GenHyp Q p q S B) {b : Ω}
    (hbp : b ^ p = 1) (hbS : b ∉ centModSubgroup p S) {L : Subgroup Ω}
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L) :
    CFSG.Open.IsQuasisimple ↥L := by
  obtain ⟨d, J, hodd, hQd, -, hJ, f, hf, hker⟩ := exists_comp_T H hL
  have hc := h2 p _ d hodd hQd (actT H b) (actT_pow H hbp) (actT_ne_one H hbS) J hJ
  exact I142.isQuasisimple_of_surj_central f hf hker
    (S267.perfect_of_commutator_self_eq (glaPComponent_perfect hL)) hc.2.2

private theorem isChevSimple_of_genCompChevOn (h3 : GenCompChevOn Q) (H : GenHyp Q p q S B)
    {b : Ω} (hbp : b ^ p = 1) (hbS : b ∉ centModSubgroup p S) {L : Subgroup Ω}
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L) :
    IsChevSimple q (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨d, J, hodd, hQd, hdq, hJ, f, hf, hker⟩ := exists_comp_T H hL
  have hc := h3 p _ d hodd hQd (actT H b) (actT_pow H hbp) (actT_ne_one H hbS) J hJ
  rw [hdq] at hc
  haveI : Group.IsPerfect ↥L := ⟨S267.perfect_of_commutator_self_eq (glaPComponent_perfect hL)⟩
  rcases hc with ⟨i, hi, ⟨g⟩⟩ | ⟨i, hi, ⟨g⟩⟩
  · exact Or.inl ⟨i, hi, ⟨(CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
      f hf hker).trans g⟩⟩
  · exact Or.inr ⟨i, hi, ⟨(CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
      f hf hker).trans g⟩⟩

private theorem pow_mem_of_genHyp (H : GenHyp Q p q S B) (ω : Ω) : ω ^ p ∈ S := by
  haveI := H.normal
  have hω : ω ∈ S ⊔ B := H.sup ▸ Subgroup.mem_top ω
  obtain ⟨s, hs, β, hβ, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hω
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff s).2 hs, one_mul, ← QuotientGroup.mk_pow, H.elem.2 β hβ,
    QuotientGroup.mk_one]

private theorem glaPComponent_centralizer (H : GenHyp Q p q S B) {b : Ω} {L : Subgroup Ω}
    (hL : GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L) :
    GLAPComponent p (Subgroup.centralizer ({b} : Set Ω)) L := by
  set X : Subgroup Ω := Subgroup.centralizer ({b} : Set Ω) with hX
  have hnorm : ((S ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨H.normal.conj_mem _ hn.1 g, X.mul_mem (X.mul_mem g.2 hn.2) (X.inv_mem g.2)⟩
  have hquot : IsPGroup p (↥X ⧸ (S ⊓ X).subgroupOf X) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact ⟨pow_mem_of_genHyp H (x : Ω), X.pow_mem x.2 p⟩
  exact (CFSG.glaPComponent_iff_of_isPGroup_quotient H.pPrime inf_le_right hnorm hquot).2 hL

private theorem twoLocalRank_le_of_genHyp (H : GenHyp Q p q S B) {B' : Subgroup Ω}
    (hB' : IsElemAbelian p B') (hBB' : Nat.card B ≤ Nat.card B') (X : Subgroup Ω) :
    GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B' := by
  have hp := H.pPrime
  obtain ⟨k, hk⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_card_eq_of_isElemAbelian hp hB'
  rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_eq_of_card hp.one_lt hB' hk]
  have h2 : p ^ GLATwoLocalRank p ↥X ≤ p ^ k :=
    (Nat.pow_le_pow_right hp.pos (S11.twoLocalRank_le_top hp X)).trans
      (H.twoLocal.trans (hBB'.trans hk.le))
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h2

end Transport

section Helpers

private theorem glaPPrimeCore_ne_top {p : ℕ} (hp : p.Prime) {X L : Subgroup Ω}
    (hL : GLAPComponent p X L) : GLAPPrimeCore p ↥L ≠ ⊤ := by
  intro htop
  haveI : Nontrivial (PQuot p L) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hL)
  haveI : Subsingleton (↥L ⧸ GLAPPrimeCore p ↥L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (PQuot p L) inferInstance

private theorem mem_centralizer_of_centMod {p : ℕ} {L : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hne : GLAPPrimeCore p ↥L ≠ ⊤) {a : Ω}
    (ha : CentMod p L a) : a ∈ Subgroup.centralizer (L : Set Ω) := by
  have hle : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  have hcm := (centMod_iff.1 ha).2
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hφ := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (L.normalizerMonoidHom ⟨a, ha.1⟩).toMonoidHom fun x => by
      obtain ⟨c, hc, hcx⟩ := hcm _ (L.inv_mem x.2)
      have hcx' : (c : Ω) = ⁅(x : Ω)⁻¹, a⁆ := hcx
      have : x⁻¹ * (L.normalizerMonoidHom ⟨a, ha.1⟩).toMonoidHom x = c := by
        apply Subtype.ext
        rw [hcx']
        simp [Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def, mul_assoc]
      rw [this]
      exact hle hc
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := congrArg (fun ψ : ↥L →* ↥L => ((ψ ⟨l, hl⟩ : ↥L) : Ω)) hφ
  simp only [MulEquiv.coe_toMonoidHom, Subgroup.normalizerMonoidHom_apply_apply_coe,
    MonoidHom.id_apply] at h1
  calc l * a = a * l * a⁻¹ * a := by rw [h1]
    _ = a * l := by group

private theorem exists_pow_isPGroup (p : ℕ) [hp : Fact p.Prime] {K : Type} [Group K] [Finite K]
    (g : K) : ∃ m : ℕ, ¬ p ∣ m ∧ IsPGroup p (Subgroup.zpowers (g ^ m)) := by
  have hn : Nat.card K ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.card K / p ^ (Nat.card K).factorization p,
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 (Nat.coprime_ordCompl hp.out hn), ?_⟩
  have h1 : (g ^ (Nat.card K / p ^ (Nat.card K).factorization p)) ^
      p ^ (Nat.card K).factorization p = 1 := by
    rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_card_eq_one']
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

private theorem pow_eq_one_of_sylow {p : ℕ} [hp : Fact p.Prime] {K K' : Type} [Group K]
    [Finite K] [Group K'] [Finite K'] (ρ : K →* K') (hker : ¬ p ∣ Nat.card ρ.ker)
    (hS : ∀ R : Sylow p K', ∀ r ∈ (R : Subgroup K'), r ^ p = 1) {g : K}
    (hg : IsPGroup p (Subgroup.zpowers g)) : g ^ p = 1 := by
  have h1 : IsPGroup p (Subgroup.zpowers (ρ g)) := by
    rw [← MonoidHom.map_zpowers]
    exact hg.map ρ
  obtain ⟨R, hR⟩ := h1.exists_le_sylow
  have hmem : g ^ p ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hS R _ (hR (Subgroup.mem_zpowers _))
  obtain ⟨k, hk⟩ :=
    IsPGroup.iff_orderOf.1 hg ⟨g ^ p, Subgroup.pow_mem _ (Subgroup.mem_zpowers g) p⟩
  have hk' : orderOf (g ^ p) = p ^ k := (Subgroup.orderOf_coe _).trans hk
  have hdvd : orderOf (g ^ p) ∣ Nat.card ρ.ker := by
    have := orderOf_dvd_natCard (⟨g ^ p, hmem⟩ : ρ.ker)
    rwa [← Subgroup.orderOf_coe] at this
  have hk0 : k = 0 := by
    by_contra hk0
    exact hker ((dvd_pow_self p hk0).trans (hk' ▸ hdvd))
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.1 hk'

private theorem exists_two_subgroup_lift {K : Type} [Group K] [Finite K]
    {P : Subgroup (K ⧸ Subgroup.center K)} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) {e₀ : K}
    (he : (QuotientGroup.mk e₀ : K ⧸ Subgroup.center K) ∈ Subgroup.normalizer (P : Set _)) :
    ∃ R : Subgroup K, R ≠ ⊥ ∧ IsPGroup 2 R ∧ e₀ ∈ Subgroup.normalizer (R : Set K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  set Rh : Subgroup K := P.comap π with hRh
  let f : ↥Rh →* ↥P := (π.comp Rh.subtype).codRestrict P (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hfker : f.ker ≤ Subgroup.center ↥Rh := by
    intro x hx
    have h1 : π (x : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_center_iff.2 fun z => Subtype.ext (Subgroup.mem_center_iff.1 h1 (z : K))
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hnil : Group.IsNilpotent ↥Rh := isNilpotent_of_ker_le_center f hfker
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Rh) := inferInstance
  have hsyl : ∀ (r : ℕ), Fact (Nat.Prime r) → ∀ (P : Sylow r ↥Rh), (P : Subgroup ↥Rh).Normal :=
    (isNilpotent_of_finite_tfae.out 1 4).1 hnil
  have hTn : (T : Subgroup ↥Rh).Normal := hsyl 2 inferInstance T
  have hmemT : ∀ x : ↥Rh, IsPGroup 2 (Subgroup.zpowers x) → x ∈ (T : Subgroup ↥Rh) := by
    intro x hx
    obtain ⟨T', hT'⟩ := hx.exists_le_sylow
    have hTT : T' = T := by
      haveI := Sylow.unique_of_normal T hTn
      exact Subsingleton.elim _ _
    rw [← hTT]
    exact hT' (Subgroup.mem_zpowers x)
  have hconj : ∀ g : K, π g ∈ Subgroup.normalizer (P : Set _) →
      ∀ r ∈ (T : Subgroup ↥Rh).map Rh.subtype,
        g * r * g⁻¹ ∈ (T : Subgroup ↥Rh).map Rh.subtype := by
    rintro g hg _ ⟨t, ht, rfl⟩
    have hmem : g * (t : K) * g⁻¹ ∈ Rh := by
      show π (g * (t : K) * g⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hg (π t)).1 t.2
    refine ⟨⟨_, hmem⟩, hmemT _ ?_, rfl⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 T.isPGroup' ⟨t, ht⟩
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    have h1 : orderOf (g * (t : K) * g⁻¹) = orderOf (t : K) := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (t : K)
      simpa [MulAut.conj_apply] using this
    rw [show ((⟨g * (t : K) * g⁻¹, hmem⟩ : ↥Rh) : K) = g * (t : K) * g⁻¹ from rfl, h1,
      Subgroup.orderOf_coe, ← hn, ← Subgroup.orderOf_coe ⟨t, ht⟩]
  refine ⟨(T : Subgroup ↥Rh).map Rh.subtype, ?_, T.isPGroup'.map _, ?_⟩
  · have h2P : 2 ∣ Nat.card ↥P :=
      hP2.card_eq_or_dvd.resolve_left fun h => hP (Subgroup.card_eq_one.1 h)
    have h2R : 2 ∣ Nat.card ↥Rh := h2P.trans (Subgroup.card_dvd_of_surjective hf)
    intro h
    exact T.ne_bot_of_dvd_card h2R
      ((Subgroup.map_eq_bot_iff_of_injective _ Rh.subtype_injective).1 h)
  · rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hconj e₀ he r hr, fun hr => ?_⟩
    have he' : π e₀⁻¹ ∈ Subgroup.normalizer (P : Set _) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ he
    have := hconj e₀⁻¹ he' _ hr
    simpa [mul_assoc] using this

private theorem closureIn_eq_iSup (L B' : Subgroup Ω) :
    closureIn L B' = ⨆ g ∈ B', GLBConj g L := by
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    refine le_iSup₂_of_le (f := fun g (_ : g ∈ B') => GLBConj g L) a⁻¹ (B'.inv_mem ha) ?_
    show L.map (MulAut.conj a).toMonoidHom ≤ L.map (MulAut.conj a⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
  · refine iSup₂_le fun g hg => ?_
    exact le_iSup₂_of_le (f := fun a (_ : a ∈ B') => L.map (MulAut.conj a).toMonoidHom) g⁻¹
      (B'.inv_mem hg) le_rfl

private theorem barX_le_centralizer {p : ℕ} {X E J : Subgroup Ω}
    (hc : ∀ e ∈ E, ∀ j ∈ J, e * j = j * e) :
    barX p X E ≤ Subgroup.centralizer
      ((barX p X J : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  rintro _ ⟨e, he, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc e he j hj).symm

end Helpers

section Norm

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

private theorem le_range_lN {L B' : Subgroup Ω} {y : Ω} (hy3 : y ^ 3 = 1)
    (hc : LComm 3 y L) (hJ : closureIn L B' = (lPsi hc).range) {K : Subgroup Ω}
    (hK : GLAPComponent 3 (closureIn L B' ⊓ Subgroup.centralizer ({y} : Set Ω)) K) :
    K ≤ (lN hc).range := by
  have hdec : ∀ k ∈ K, ∃ n ∈ (lN hc).range, ∃ c ∈ (lPsi hc).range,
      (∀ j ∈ (lPsi hc).range, Commute c j) ∧ k = n * c := by
    intro k hk
    obtain ⟨hkJ, hky⟩ := hK.1 hk
    rw [hJ] at hkJ
    obtain ⟨f, rfl⟩ := hkJ
    have hcy : y⁻¹ * lPsi hc f * y = lPsi hc f := by
      have h1 : lPsi hc f * y = y * lPsi hc f := Subgroup.mem_centralizer_singleton_iff.1 hky
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨l, z, hz, hfz⟩ := lPsi_centralizer hy3 hc hcy
    refine ⟨lN hc l, ⟨l, rfl⟩, lPsi hc z, ⟨z, rfl⟩, ?_, hfz⟩
    rintro _ ⟨g, rfl⟩
    exact lPsi_central hc hz g
  have hNJ : ∀ n ∈ (lN hc).range, n ∈ (lPsi hc).range := by
    rintro _ ⟨l, rfl⟩
    exact ⟨fun _ => l, (lN_apply hc l).symm⟩
  rw [← glaPComponent_perfect hK, Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨n₁, hn₁, c₁, hc₁J, hc₁, rfl⟩ := hdec k₁ hk₁
  obtain ⟨n₂, hn₂, c₂, hc₂J, hc₂, rfl⟩ := hdec k₂ hk₂
  rw [CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
    (hc₁ n₂ (hNJ n₂ hn₂)) (hc₁ c₂ hc₂J) (hc₂ n₁ (hNJ n₁ hn₁)), commutatorElement_def]
  exact (lN hc).range.mul_mem ((lN hc).range.mul_mem ((lN hc).range.mul_mem hn₁ hn₂)
    ((lN hc).range.inv_mem hn₁)) ((lN hc).range.inv_mem hn₂)

private theorem ker_lN_ne_bot {L : Subgroup Ω} {y : Ω} (hy3 : y ^ 3 = 1) (hc : LComm 3 y L)
    {z : ↥L} (hzC : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hsmall : Nat.card ↥((Subgroup.pi Set.univ fun _ : ZMod 3 => Subgroup.zpowers z).map
      (lPsi hc)) < 27) : (lN hc).ker ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Pz : Subgroup (ZMod 3 → ↥L) :=
    Subgroup.pi Set.univ fun _ : ZMod 3 => Subgroup.zpowers z with hPz
  set D : Subgroup (ZMod 3 → ↥L) := (lPsi hc).ker ⊓ Pz with hD
  have hDne : D ≠ ⊥ := by
    intro hD0
    apply absurd hsmall
    rw [not_lt]
    let e : (ZMod 3 → ↥(Subgroup.zpowers z)) → ↥(Pz.map (lPsi hc)) :=
      fun g => ⟨lPsi hc (fun k => (g k : ↥L)), ⟨fun k => (g k : ↥L), fun k _ => (g k).2, rfl⟩⟩
    have he : Function.Injective e := by
      intro g g' hgg
      have h1 : lPsi hc (fun k => (g k : ↥L)) = lPsi hc (fun k => (g' k : ↥L)) :=
        congrArg Subtype.val hgg
      have h2 : (fun k => (g k : ↥L)) * (fun k => (g' k : ↥L))⁻¹ ∈ D := by
        refine ⟨?_, fun k _ => ?_⟩
        · show lPsi hc _ = 1
          rw [map_mul, map_inv, h1, mul_inv_cancel]
        · exact Subgroup.mul_mem _ (g k).2 (Subgroup.inv_mem _ (g' k).2)
      rw [hD0, Subgroup.mem_bot] at h2
      funext k
      apply Subtype.ext
      exact mul_inv_eq_one.1 (congrFun h2 k)
    have hcard := Nat.card_le_card_of_injective e he
    have hz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    rwa [Nat.card_fun, Nat.card_zpowers, hz, Nat.card_zmod] at hcard
  have hDs : ∀ f ∈ D, lshift 3 L f ∈ D := by
    intro f hf
    refine ⟨?_, fun k _ => hf.2 (k - 1) (Set.mem_univ _)⟩
    have hf1 : lPsi hc f = 1 := hf.1
    show lPsi hc (lshift 3 L f) = 1
    rw [← lPsi_conj hy3 hc, hf1]
    group
  have hDp : ∀ f ∈ D, f ^ 3 = 1 := by
    intro f hf
    funext k
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hf.2 k (Set.mem_univ _))
    show (f k) ^ 3 = 1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  obtain ⟨f, hfD, hf1, hfs⟩ := exists_fixed_of_shift_stable D hDs hDp hDne
  have hconst : f = fun _ => f 0 := funext (eq_const_of_lshift_eq f hfs)
  intro hbot
  have hN1 : f 0 ∈ (lN hc).ker := by
    rw [MonoidHom.mem_ker, lN_apply, ← hconst]
    exact hfD.1
  rw [hbot, Subgroup.mem_bot] at hN1
  exact hf1 (by rw [hconst, hN1]; rfl)

end Norm

section Main

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem genStepI112On_of_leaves {Q : TauCeti.LieTypeIndex → Prop} (h2 : GenCompQuasiOn Q)
    (h3 : GenCompChevOn Q) (h6 : GenChevThreeLocal) (T : Tables112)
    (TT : CFSG.HardMathSupport.Solomon.Coordinator.Tables112Types)
    (TM : CFSG.HardMathSupport.Solomon.Coordinator.Tables112More) : GenStepI112On Q := by
  intro p q Ω _ _ S B H B' b L hB'el hBB' hbB' hbS hL hnL
  have hp := H.pPrime
  have hp2 := H.pOdd
  haveI : Fact p.Prime := ⟨hp⟩
  have hbp : b ^ p = 1 := hB'el.2 b hbB'
  have hLq := isQuasisimple_of_genCompQuasiOn h2 H hbp hbS hL
  have hLchev := isChevSimple_of_genCompChevOn h3 H hbp hbS hL
  set X : Subgroup Ω := Subgroup.centralizer ({b} : Set Ω) with hX
  have hB'X : B' ≤ X := fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hB'el.comm hg hbB')
  have hLX : GLAPComponent p X L := glaPComponent_centralizer H hL
  have hXK : CFSG.Open.IsKGroup ↥X :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.isKGroup_of_le H.kGroup X
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B' := twoLocalRank_le_of_genHyp H hB'el hBB' X
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hQK : CFSG.Open.IsKGroup (↥X ⧸ N) := isKGroup_quotient' hXK N
  have hQcore : GLAPPrimeCore p (↥X ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBp : IsPGroup p B' := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB'el.2 g.1 g.2)⟩
  have hBel : IsElemAbelian p (barX p X B') := isElemAbelian_barX hB'el
  have hrankQ : GLATwoLocalRank p (↥X ⧸ N) ≤ CFSG.Open.pRank p (barX p X B') := by
    rw [rank_barX_of_isPGroup hp hBp hB'X]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  have hLbar : GLAPComponent p ⊤ (barX p X L) :=
    i112b_glaPComponent_of_isComponentOf hQcore hLX.2.2.1
  have hnLQ : ¬ barX p X B' ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) :
      Set (↥X ⧸ N)) := by
    intro hle
    apply hnL
    intro g hg
    have h1 : QuotientGroup.mk' N ⟨g, hB'X hg⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨g, hB'X hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
    have h2 : (⟨g, hB'X hg⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set Ω)).subgroupOf X := by
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.i112f_comap_normalizer_barX hLX]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2
  obtain ⟨hidx, hz, hmZ⟩ := i112_ok_of_tables T hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  have hp3 : p = 3 := hz.elim (fun h => h.2.1) (fun h => h.1)
  subst hp3
  have hrel : (Subgroup.normalizer (L : Set Ω)).relIndex B' = 3 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i112f_relIndex_barX hLX hB'X).symm.trans hidx
  set Lb : Subgroup (↥X ⧸ N) := barX 3 X L with hLb
  have eLb : (↥L ⧸ GLAPPrimeCore 3 ↥L) ≃* ↥Lb := quotEquivBarX hp hLX.1 hLX.2.1
  set ρ : ↥L →* ↥Lb := eLb.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hρ
  have hρs : Function.Surjective ρ := eLb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρker : ρ.ker = GLAPPrimeCore 3 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eLb.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hOne : GLAPPrimeCore 3 ↥L ≠ ⊤ := glaPPrimeCore_ne_top hp hLX
  have hOZ : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hLq inferInstance hOne
  haveI : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have eL : (↥L ⧸ Subgroup.center ↥L) ≃* (↥Lb ⧸ Subgroup.center ↥Lb) :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence ρ hρs (hρker ▸ hOZ)
  have hqLb : CFSG.Open.IsQuasisimple ↥Lb := i116e_isQuasisimple hQcore hLbar
  have hKLb : CFSG.Open.IsKGroup ↥Lb :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.isKGroup_of_le hQK Lb
  rcases hz with ⟨hZ1, -, -, hw0⟩ | ⟨-, hZ3⟩
  ·
    exfalso
    have hZb : Subgroup.center ↥Lb = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    have e₁ : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* ↥Lb :=
      (QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot
    haveI : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hqLb.2
    haveI : IsSimpleGroup ↥Lb := MulEquiv.isSimpleGroup e₁.symm
    have hchev : IsChevSimple q ↥Lb := by
      rcases hLchev with ⟨i, hi, ⟨g⟩⟩ | ⟨i, hi, ⟨g⟩⟩
      · exact Or.inl ⟨i, hi, ⟨(eL.trans e₁).symm.trans g⟩⟩
      · exact Or.inr ⟨i, hi, ⟨(eL.trans e₁).symm.trans g⟩⟩
    have h1 := h6 q H.qPrime H.qOdd H.qp ↥Lb inferInstance hchev
    omega
  have htype := CFSG.HardMathSupport.Solomon.Coordinator.i112f_types_three T TT hQK hQcore hBel
    hrankQ hLbar hnLQ hidx hZ3 hmZ
  have hS3 := TM.T10_10S ↥Lb hqLb hKLb htype
  have hexp : ∀ g : ↥L, IsPGroup 3 (Subgroup.zpowers g) → g ^ 3 = 1 := fun g hg =>
    pow_eq_one_of_sylow ρ (by
      rw [hρker]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card)
      (fun R r hr => (hS3 R).2.2 r hr) hg
  refine ⟨rfl, hrel, ?_, ?_, ?_⟩
  ·
    have haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥Lb)) ≤ 2 := by
      rcases htype with h6' | h7 | h22 | hSL | hSU
      · exact CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_hatSix h6'
      · exact CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_hatSeven h7
      · exact TT.T10_10 ↥Lb hqLb hKLb (Or.inl h22)
      · obtain ⟨F, hF, hfin, hq9, he⟩ := hSL
        by_cases h4 : Nat.card F = 4
        · exact pRank_mulAut_le_two_of_isSLThreeFour ⟨F, hF, hfin, h4, he⟩ hqLb.1
        · exact TT.T10_10 ↥Lb hqLb hKLb (Or.inr (Or.inl ⟨F, hF, hfin, ⟨hq9, h4⟩, he⟩))
      · exact TT.T10_10 ↥Lb hqLb hKLb (Or.inr (Or.inr hSU))
    set A : Subgroup Ω := B' ⊓ Subgroup.normalizer (L : Set Ω) with hA
    set ψ : ↥A →* MulAut (↥L ⧸ GLAPPrimeCore 3 ↥L) :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L).comp
        (Subgroup.inclusion (inf_le_right : A ≤ _)) with hψ
    have hrangeE : IsElemAbelian 3 ψ.range := by
      refine ⟨⟨⟨fun a c => ?_⟩⟩, fun w hw => ?_⟩
      · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 c.2
        apply Subtype.ext
        change (a : MulAut (↥L ⧸ GLAPPrimeCore 3 ↥L)) * c = c * a
        rw [← hx, ← hz, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hB'el.comm x.2.1 z.2.1)
      · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hw
        rw [← map_pow]
        have : x ^ 3 = 1 := Subtype.ext (hB'el.2 x x.2.1)
        rw [this, map_one]
    obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hrangeE
    have hk2 : k ≤ 2 := by
      refine (CFSG.SectionRank.le_pRank hp.one_lt le_top hrangeE hk).trans ?_
      rw [CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_of_mulEquiv eLb]
      exact haut
    have hrange9 : Nat.card ψ.range ≤ 9 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 9 := by norm_num
    have hker : Nat.card ψ.ker ≤ Nat.card ↥(B' ⊓ Subgroup.centralizer (L : Set Ω)) := by
      have hle : ψ.ker.map A.subtype ≤ B' ⊓ Subgroup.centralizer (L : Set Ω) := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨a.2.1, mem_centralizer_of_centMod hLq hOne ?_⟩
        exact (chev_barAut_eq_one_iff_centMod a.2.2).1 (MonoidHom.mem_ker.1 ha)
      calc Nat.card ψ.ker = Nat.card (ψ.ker.map A.subtype) :=
            (Subgroup.card_map_of_injective A.subtype_injective).symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    have hmul := Subgroup.card_ker_mul_card_range ψ
    calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
      _ ≤ Nat.card ↥(B' ⊓ Subgroup.centralizer (L : Set Ω)) * 9 := Nat.mul_le_mul hker hrange9
      _ = 9 * Nat.card ↥(B' ⊓ Subgroup.centralizer (L : Set Ω)) := mul_comm _ _
  ·
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
    have h1 := h6 q H.qPrime H.qOdd H.qp (↥L ⧸ Subgroup.center ↥L) hLq.2 hLchev
    obtain ⟨P, hP, hP2, et, het3, hetN⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.threeTwoWitness_of_one_le h1
    obtain ⟨e₀, rfl⟩ := QuotientGroup.mk_surjective et
    obtain ⟨R, hR, hR2, he₀R⟩ := exists_two_subgroup_lift hP hP2 hetN
    obtain ⟨m, hm, hm3⟩ := exists_pow_isPGroup 3 e₀
    have he3 : (e₀ ^ m) ^ 3 = 1 := hexp _ hm3
    have heZ : (QuotientGroup.mk (e₀ ^ m) : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := by
      rw [QuotientGroup.mk_pow]
      intro h
      exact hm (het3 ▸ orderOf_dvd_of_pow_eq_one h)
    refine ⟨((e₀ ^ m : ↥L) : Ω), (e₀ ^ m).2, ?_, ?_, R.map L.subtype,
      Subgroup.map_subtype_le R, ?_, hR2.map _, ?_⟩
    · rw [← Subgroup.coe_pow, he3, Subgroup.coe_one]
    · intro hC
      apply heZ
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_center_iff.2 fun w =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 hC w w.2)
    · intro h
      exact hR ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h)
    · exact Subgroup.le_normalizer_map L.subtype ⟨e₀ ^ m, Subgroup.pow_mem _ he₀R m, rfl⟩
  ·
    intro y hyB hyn K hK
    have hy3 : y ^ 3 = 1 := hB'el.2 y hyB
    have hcompM : ∀ g ∈ B', CFSG.Open.IsComponentOf (GLBConj g L)
        (S ⊓ Subgroup.centralizer ({b} : Set Ω)) := by
      intro g hg
      have hgM : g ∈ Subgroup.normalizer
          ((S ⊓ Subgroup.centralizer ({b} : Set Ω) : Subgroup Ω) : Set Ω) :=
        mem_normalizer_inf (top_le_normalizer H (Subgroup.mem_top g))
          (Subgroup.le_normalizer (hB'X hg))
      have hJ' : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) (GLBConj g L) := by
        have := glaPComponent_gLBConj hL g
        rwa [mem_normalizer_iff_gLBConj_eq.1 hgM] at this
      exact ⟨hJ'.1, hJ'.2.1, isQuasisimple_of_genCompQuasiOn h2 H hbp hbS hJ'⟩
    have hlbp : ∀ k : ZMod 3, lbp 3 y k ∈ B' := fun k => by
      unfold lbp
      exact B'.pow_mem hyB _
    have hc : LComm 3 y L := by
      intro i j hij x x'
      have hmem : ∀ k : ZMod 3, ∀ x : ↥L, lphi 3 y L k x ∈ GLBConj (lbp 3 y k) L := by
        intro k x
        rw [mem_gLBConj, lphi_apply]
        have : lbp 3 y k * ((lbp 3 y k)⁻¹ * (x : Ω) * lbp 3 y k) * (lbp 3 y k)⁻¹ = x := by group
        rw [this]
        exact x.2
      rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (hcompM _ (hlbp i))
          (hcompM _ (hlbp j)) with h | h
      · exact absurd h (gLBConj_lbp_ne hp hy3 hyn hij)
      · exact h _ (hmem i x) _ (hmem j x')
    have hJ : closureIn L B' = (lPsi hc).range := by
      rw [closureIn_eq_iSup]
      exact J_eq_range hp hyB hy3 hyn hrel hc
    have hKle := le_range_lN hy3 hc hJ hK
    obtain ⟨z, hzC, hz1, hz3⟩ : ∃ z ∈ Subgroup.center ↥L, z ≠ 1 ∧ z ^ 3 = 1 := by
      haveI : Nontrivial ↥(Subgroup.center ↥Lb) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [hZ3]; norm_num)
      obtain ⟨w, hw⟩ := exists_ne (1 : ↥(Subgroup.center ↥Lb))
      have hw3 : (w : ↥Lb) ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥(Subgroup.center ↥Lb)) (x := w)
        rw [hZ3] at this
        exact congrArg Subtype.val this
      have hw1 : (w : ↥Lb) ≠ 1 := fun h => hw (Subtype.ext h)
      have hwo : orderOf (w : ↥Lb) = 3 := orderOf_eq_prime hw3 hw1
      obtain ⟨z₀, hz₀⟩ := hρs (w : ↥Lb)
      have hz₀C : z₀ ∈ Subgroup.center ↥L := by
        have hcm : CentMod 3 L (z₀ : Ω) := by
          refine centMod_iff.2 ⟨Subgroup.le_normalizer z₀.2, fun l hl => ?_⟩
          have hk : ⁅(⟨l, hl⟩ : ↥L), z₀⁆ ∈ GLAPPrimeCore 3 ↥L := by
            rw [← hρker, MonoidHom.mem_ker, map_commutatorElement, hz₀,
              commutatorElement_eq_one_iff_mul_comm]
            exact Subgroup.mem_center_iff.1 w.2 _
          exact ⟨_, hk, rfl⟩
        have hzC' := mem_centralizer_of_centMod hLq hOne hcm
        exact Subgroup.mem_center_iff.2 fun l =>
          Subtype.ext (Subgroup.mem_centralizer_iff.1 hzC' l l.2)
      obtain ⟨m, hm, hm3⟩ := exists_pow_isPGroup 3 z₀
      refine ⟨z₀ ^ m, Subgroup.pow_mem _ hz₀C m, fun h => ?_, hexp _ hm3⟩
      have h1 : (w : ↥Lb) ^ m = 1 := by rw [← hz₀, ← map_pow, h, map_one]
      exact hm (hwo ▸ orderOf_dvd_of_pow_eq_one h1)
    have hsmall : Nat.card ↥((Subgroup.pi Set.univ fun _ : ZMod 3 => Subgroup.zpowers z).map
        (lPsi hc)) < 27 := by
      set E : Subgroup Ω := (Subgroup.pi Set.univ fun _ : ZMod 3 => Subgroup.zpowers z).map
        (lPsi hc) with hE
      by_contra hge
      push Not at hge
      have hzpow : ∀ w ∈ Subgroup.zpowers z, w ∈ Subgroup.center ↥L := by
        intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        exact Subgroup.zpow_mem _ hzC n
      have hEcen : ∀ e ∈ E, ∀ j ∈ (lPsi hc).range, e * j = j * e := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨g, rfl⟩
        exact lPsi_central hc (fun k => hzpow _ (hf k (Set.mem_univ _))) g
      have hEel : IsElemAbelian 3 E := by
        refine ⟨⟨⟨fun a c => Subtype.ext (hEcen a a.2 c ?_)⟩⟩, ?_⟩
        · obtain ⟨f, -, hf⟩ := c.2
          exact ⟨f, hf⟩
        · rintro _ ⟨f, hf, rfl⟩
          rw [← map_pow]
          have : f ^ 3 = 1 := by
            funext k
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hf k (Set.mem_univ _))
            show (f k) ^ 3 = 1
            rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3,
              one_zpow]
          rw [this, map_one]
      obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hEel
      have hk3 : 3 ≤ k := by
        rw [hk] at hge
        by_contra hlt
        push Not at hlt
        have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hJX : closureIn L B' ≤ X := by
        rw [closureIn_eq_iSup]
        refine iSup₂_le fun g hg => ?_
        rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hB'X hg))]
        exact CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g hLX.1
      have hEJ : E ≤ closureIn L B' := by
        rw [hJ]
        rintro _ ⟨f, -, rfl⟩
        exact ⟨f, rfl⟩
      have hEX : E ≤ X := hEJ.trans hJX
      have hrk : CFSG.Open.pRank 3 (barX 3 X E) = k := by
        rw [rank_barX_of_isPGroup hp (IsPGroup.of_card hk) hEX]
        exact pRank_eq_of_card hp.one_lt hEel hk
      have hJbar : barX 3 X (closureIn L B') = i112J (barX 3 X B') (barX 3 X L) := by
        rw [closureIn_eq_iSup]
        exact CFSG.HardMathSupport.Solomon.Coordinator.i112f_barX_bClosure hB'X hLX.1
      have hbarle : barX 3 X E ≤ i112J (barX 3 X B') (barX 3 X L) ⊓
          Subgroup.centralizer (i112J (barX 3 X B') (barX 3 X L) : Set (↥X ⧸ N)) := by
        refine le_inf ((CFSG.HardMathSupport.Solomon.Coordinator.i112f_barX_mono hEJ).trans
          hJbar.le) ?_
        rw [← hJbar]
        exact barX_le_centralizer fun e he j hj => hEcen e he j (hJ ▸ hj)
      have h3le : 3 ≤ CFSG.Open.pRank 3 (i112J (barX 3 X B') (barX 3 X L) ⊓
          Subgroup.centralizer (i112J (barX 3 X B') (barX 3 X L) : Set (↥X ⧸ N))) :=
        (hk3.trans hrk.symm.le).trans (CFSG.SectionRank.pRank_mono hp.one_lt hbarle)
      exact absurd hmZ (not_lt.2 h3le)
    have hker := ker_lN_ne_bot hy3 hc hzC hz1 hz3 hsmall
    have hmul := Subgroup.card_ker_mul_card_range (lN hc)
    have hk1 : 1 < Nat.card (lN hc).ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hker
    have hr0 : 0 < Nat.card (lN hc).range := Nat.card_pos
    calc Nat.card K ≤ Nat.card (lN hc).range := Subgroup.card_le_of_le hKle
      _ < Nat.card (lN hc).ker * Nat.card (lN hc).range := lt_mul_of_one_lt_left hr0 hk1
      _ = Nat.card ↥L := hmul

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
