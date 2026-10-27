module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsInner
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTargets
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsE1
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneOf
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem exists_conj_of_pow {L : Type*} [Group L]
    (hout : Nat.Coprime 3 (Nat.card (Outer L))) {α : MulAut L} {n : ℕ} (hα : α ^ 3 ^ n = 1) :
    ∃ g : L, α = MulAut.conj g := by
  set q := QuotientGroup.mk' (inner L) α with hq
  have hq3 : q ^ 3 ^ n = 1 := by rw [hq, ← map_pow, hα, map_one]
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n hout)]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  rw [Nat.dvd_one, orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hd
  obtain ⟨g, hg⟩ := hd
  exact ⟨g, hg.symm⟩

private theorem exists_inv_mul_mem_centralizer {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]
    (hout : Nat.Coprime 3 (Nat.card (Outer K))) {y : Y} {n : ℕ}
    (hy : y ^ 3 ^ n ∈ centralizer (K : Set Y)) :
    ∃ g ∈ K, g⁻¹ * y ∈ centralizer (K : Set Y) := by
  have h1 : (MulAut.conjNormal y : MulAut K) ^ 3 ^ n = 1 := by
    rw [← map_pow]
    refine MulEquiv.ext fun m => Subtype.ext ?_
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← mem_centralizer_iff.mp hy m m.2]
    group
  obtain ⟨g, hg⟩ := exists_conj_of_pow hout h1
  refine ⟨g, g.2, mem_centralizer_iff.mpr fun m hm => ?_⟩
  have h2 := congrArg (fun a : MulAut K => ((a ⟨m, hm⟩ : K) : Y)) hg
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h2
  calc m * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * m * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h2]
    _ = (g : Y)⁻¹ * y * m := by group

private theorem mem_of_pow_eq_one {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]
    (hout : Nat.Coprime 3 (Nat.card (Outer K))) (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hC : Nat.Coprime 3 (Nat.card (centralizer (K : Set Y)))) {y : Y} {n : ℕ}
    (hy : y ^ 3 ^ n = 1) : y ∈ K := by
  obtain ⟨g, hg, hc⟩ :=
    exists_inv_mul_mem_centralizer hout (n := n) (by rw [hy]; exact one_mem _)
  have hgc : g * (g⁻¹ * y) = (g⁻¹ * y) * g := mem_centralizer_iff.mp hc g hg
  have h1 : g ^ 3 ^ n * (g⁻¹ * y) ^ 3 ^ n = 1 := by
    rw [← (Commute.mul_pow hgc _), mul_inv_cancel_left, hy]
  have hc3 : (g⁻¹ * y) ^ 3 ^ n = 1 := by
    have h2 : (g⁻¹ * y) ^ 3 ^ n ∈ K ⊓ centralizer (K : Set Y) := by
      refine ⟨?_, Subgroup.pow_mem _ hc _⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem hg _)
    rwa [hKC, Subgroup.mem_bot] at h2
  have hco : orderOf (g⁻¹ * y) ∣ 1 := by
    have h3 : orderOf (g⁻¹ * y) ∣ Nat.card (centralizer (K : Set Y)) := by
      have := orderOf_dvd_natCard (⟨g⁻¹ * y, hc⟩ : centralizer (K : Set Y))
      rwa [Subgroup.orderOf_mk] at this
    rw [← Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n hC)]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) h3
  rw [Nat.dvd_one, orderOf_eq_one_iff, inv_mul_eq_one] at hco
  rw [← hco]
  exact hg

private theorem pow_three_mem_of_mem_sup {Y : Type*} [Group Y] {J C : Subgroup Y} [C.Normal]
    (hJ : ∀ j ∈ J, j ^ 3 ∈ C) {x : Y} (hx : x ∈ J ⊔ C) : x ^ 3 ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal J C] at hx
  obtain ⟨j, hj, c, hc, rfl⟩ := Set.mem_mul.mp hx
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff c).mpr hc, mul_one, ← QuotientGroup.mk_pow,
    QuotientGroup.eq_one_iff]
  exact hJ j hj

private theorem commute_of_central {G : Type*} [Group G] [Finite G] {T F : Subgroup G}
    (hFT : F ≤ T) (hT : Nat.card T = 3 ^ 3) (hF : Nat.card F = 3 ^ 2)
    (hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hcen : ∀ a ∈ F, ∀ t ∈ T, t * a = a * t) :
    ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  obtain ⟨t, htT, htF⟩ : ∃ t ∈ T, t ∉ F := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show T ≤ F from h)
    rw [hT, hF] at this
    norm_num at this
  have hrc : ((F : Set G) ∪ {t}).Pairwise Commute := by
    rintro x (hx | hx) y (hy | hy) hxy
    · exact hFcomm x hx y hy
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (hcen x hx t htT).symm
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hcen y hy t htT
    · rw [Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  have hBcomm := Subgroup.isMulCommutative_closure hrc
  set B := Subgroup.closure ((F : Set G) ∪ {t}) with hB
  have hFB : F ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have htB : t ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hBT : B ≤ T := by
    rw [hB, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hFT hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact htT
  have hd1 : Nat.card F ∣ Nat.card B := Subgroup.card_dvd_of_le hFB
  have hd2 : Nat.card B ∣ 3 ^ 3 := hT ▸ Subgroup.card_dvd_of_le hBT
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd2
  rw [hF, hm] at hd1
  have hm2 : 2 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd1
  have hBT' : B = T := by
    rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · exact absurd ((Subgroup.eq_of_le_of_card_ge hFB (by rw [hF, hm])) ▸ htB) htF
    · exact Subgroup.eq_of_le_of_card_ge hBT (by rw [hT, hm])
  intro x hx y hy
  rw [← hBT'] at hx hy
  exact congrArg Subtype.val (hBcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem map_conj_eq_of_mem_normalizer {Y : Type*} [Group Y] {J : Subgroup Y} {n : Y}
    (hn : n ∈ normalizer (J : Set Y)) : J.map (MulAut.conj n).toMonoidHom = J := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (mem_normalizer_iff.mp hn j).mp hj
  · intro hx
    refine ⟨n⁻¹ * x * n, (mem_normalizer_iff.mp hn _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_mul {Y : Type*} [Group Y] (J : Subgroup Y) (a b : Y) :
    J.map (MulAut.conj (a * b)).toMonoidHom =
      (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem exists_conj_eq_or_eq {Y : Type*} [Group Y] [Finite Y] {Y₀ J : Subgroup Y}
    (hh : ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 2) :
    ∃ g : Y, ∀ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom = J ∨
      J.map (MulAut.conj y).toMonoidHom = J.map (MulAut.conj g).toMonoidHom := by
  set M := (normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀ with hM
  have hidx : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show M.index = 1 ∨ M.index = 2 by omega) with h1 | h2
  · refine ⟨1, fun y hy => Or.inl ?_⟩
    have hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M := (Subgroup.index_eq_one.mp h1) ▸ Subgroup.mem_top _
    exact map_conj_eq_of_mem_normalizer (Subgroup.mem_subgroupOf.mp hyM).1
  · obtain ⟨g, hgM⟩ : ∃ g : ↥Y₀, g ∉ M := by
      by_contra h
      push Not at h
      have : M = ⊤ := eq_top_iff.mpr fun x _ => h x
      rw [this, Subgroup.index_top] at h2
      omega
    refine ⟨g, fun y hy => ?_⟩
    by_cases hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M
    · exact Or.inl (map_conj_eq_of_mem_normalizer (Subgroup.mem_subgroupOf.mp hyM).1)
    · right
      have hgyM : g⁻¹ * ⟨y, hy⟩ ∈ M := by
        rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff]
        exact iff_of_false hgM hyM
      have hN' : (g : Y)⁻¹ * y ∈ normalizer (J : Set Y) := by
        simpa using (Subgroup.mem_subgroupOf.mp hgyM).1
      calc J.map (MulAut.conj y).toMonoidHom
          = J.map (MulAut.conj ((g : Y) * ((g : Y)⁻¹ * y))).toMonoidHom := by
            rw [mul_inv_cancel_left]
        _ = (J.map (MulAut.conj ((g : Y)⁻¹ * y)).toMonoidHom).map
              (MulAut.conj (g : Y)).toMonoidHom := map_conj_mul J _ _
        _ = J.map (MulAut.conj (g : Y)).toMonoidHom := by
            rw [map_conj_eq_of_mem_normalizer hN']

theorem ThreeFourSolvThreeNoneAt.of_coreE1 {X : Type*} [Group X]
    (hX : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* X) →
      IsSimpleGroup L ∧
        Nat.Coprime 3 (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L)) ∧
        (∀ T : Sylow 3 L, CFSG.Open.GLBCore 3 2 (T : Subgroup L) = ⊤) ∧
        CFSG.AGLEmbedding.CoreE1.Datum L) :
    ThreeFourSolvThreeNoneAt X := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ _ hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    _ hdir
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsimple, hout, hΓ, hdatum⟩ := hX ↥K hKX
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ
  have hKC : K ⊓ C = ⊥ :=
    CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTcard, hTnc, hTE⟩ := hdatum T
  have hT27 : Nat.card (T : Subgroup K) = 3 ^ 3 := hTcard.trans (by norm_num)
  have hKcomp : IsComponentOf K ⊤ := by
    obtain ⟨a, -, b, -, hab⟩ := hTnc
    haveI := hsimple
    haveI : Group.IsPerfect ↥K :=
      ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K ⟨a, b, hab⟩⟩
    exact ⟨le_top, CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩
  have hCcop : Nat.Coprime 3 (Nat.card C) :=
    SolvNone.coprime_three_card_centralizer R hZ hΓ hKcomp hcomp hER hE hEc hcore
  have hRY₀ : (R : Subgroup Y) ≤ Y₀ :=
    (sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  have h3K : ∀ P : Subgroup Y, IsPGroup 3 P → P ≤ K := fun P hP x hx => by
    obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
    exact mem_of_pow_eq_one hout hKC hCcop (n := n) (by simpa using congrArg Subtype.val hn)
  have hRK : (R : Subgroup Y) ≤ K := h3K _ R.isPGroup'
  have hTR : (T : Subgroup K).map K.subtype = R := by rw [hT, inf_eq_left.mpr hRK]
  have hTRmem : ∀ t ∈ (T : Subgroup K), (t : Y) ∈ (R : Subgroup Y) := fun t ht =>
    hTR ▸ Subgroup.mem_map_of_mem K.subtype ht
  have hR3 : ¬ 3 ≤ CFSG.pRank 3 (R : Subgroup Y) := by
    intro h3
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    obtain ⟨F, hFR, hF, hFc⟩ :=
      CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (R : Subgroup Y)
    have hRcard : Nat.card (R : Subgroup Y) = 3 ^ 3 := by
      rw [← hTR, Subgroup.card_map_of_injective K.subtype_injective, hT27]
    have hFR' : F = R := Subgroup.eq_of_le_of_card_ge hFR (by
      rw [hRcard, hFc]
      exact Nat.pow_le_pow_right (by norm_num) h3)
    obtain ⟨a, ha, b, hb, hab⟩ := hTnc
    have haF : (a : Y) ∈ F := hFR' ▸ hTRmem a ha
    have hbF : (b : Y) ∈ F := hFR' ▸ hTRmem b hb
    have h1 : (a : Y) * b = b * a := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, haF⟩ ⟨_, hbF⟩)
    exact hab (Subtype.ext (by simpa using h1))
  have hcore1 : GLBCore 3 1 E ≤ Y₀ := by rwa [if_neg hR3] at hcore
  have hEK : E ≤ K := hER.trans hRK
  set E' : Subgroup K := E.subgroupOf K
  have hE'el : IsElemAbelian 3 E' := hE.subgroupOf K
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hE'T : E' ≤ T := by
    intro e he
    obtain ⟨t, ht, hte⟩ : (e : Y) ∈ (T : Subgroup K).map K.subtype :=
      hTR ▸ hER (Subgroup.mem_subgroupOf.mp he)
    rwa [Subtype.ext hte] at ht
  have hE'r : 1 ≤ CFSG.Open.pRank 3 E' :=
    le_trans (by norm_num) (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hE'el hE'c)
  have hcore' : GLBCore 3 1 E' ≤ Y₀.comap K.subtype := by
    apply sSup_le
    rintro N ⟨Q, hQE', hQr, rfl⟩ n hn
    have hQE : Q.map K.subtype ≤ E := by
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hQE' hq)
    have hQr' : 1 ≤ CFSG.Open.pRank 3 (Q.map K.subtype) := by
      rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three K.subtype
        K.subtype_injective]
    have hN : normalizer ((Q.map K.subtype : Subgroup Y) : Set Y) ≤ GLBCore 3 1 E :=
      le_sSup ⟨Q.map K.subtype, hQE, hQr', rfl⟩
    exact hcore1 (hN (Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩))
  have hTY₀ : (T : Subgroup K) ≤ Y₀.comap K.subtype := fun t ht => hRY₀ (hTRmem t ht)
  set W₀ : Subgroup K := pCoreOf 3 (Y₀.comap K.subtype)
  have hW₀N : Y₀.comap K.subtype ≤ normalizer (W₀ : Set K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 3 _
  have hW₀p : IsPGroup 3 W₀ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 3 _
  have hW₀T : W₀ ≤ T := by
    have hp := hW₀p.to_sup_of_normal_left' T.isPGroup' (hTY₀.trans hW₀N)
    exact le_sup_left.trans (T.is_maximal' hp le_sup_right).le
  have hJ3 : ∀ x ∈ J, x ^ 3 ∈ C := cube_mem_of_pCoreOf_le σ hσs hO2 hb
  have hJsub : CFSG.Open.IsSubnormal J Y₀ := isSubnormal_oUpperTwo_map σ hσs
  have hJCsub : CFSG.Open.IsSubnormal (J ⊔ C) Y₀ := by
    have h1 := (hJsub.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C)
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr hC] at h1
  have hA : (J ⊔ C).comap K.subtype ≤ W₀ := by
    refine CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
      (hJCsub.comap K.subtype) ?_
    rintro ⟨x, hx⟩
    have h1 : (x : Y) ^ 3 ∈ K ⊓ C := ⟨K.pow_mem x.2 3, pow_three_mem_of_mem_sup hJ3 hx⟩
    rw [hKC, Subgroup.mem_bot] at h1
    have h2 : x ^ 3 = 1 := Subtype.ext (by simpa using h1)
    refine ⟨1, ?_⟩
    rw [Subtype.ext_iff, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact h2
  have hbot : W₀ = ⊥ → J ≤ C := by
    intro hW j hj
    obtain ⟨g, hgK, hgc⟩ :=
      exists_inv_mul_mem_centralizer hout (n := 1) (by rw [pow_one]; exact hJ3 j hj)
    have hgA : (⟨g, hgK⟩ : K) ∈ (J ⊔ C).comap K.subtype := by
      change g ∈ J ⊔ C
      simpa using mul_mem_sup hj (C.inv_mem hgc)
    have hg1 := hA hgA
    rw [hW, Subgroup.mem_bot] at hg1
    have hg : g = 1 := congrArg Subtype.val hg1
    rw [hg, inv_one, one_mul] at hgc
    exact hgc
  have hcen : W₀ ≠ ⊥ → ∃ w ∈ W₀, w ≠ 1 ∧ ∀ t ∈ (T : Subgroup K), t * w = w * t := fun hW =>
    CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal Nat.prime_three T.isPGroup' hW₀T
      (fun g hg u hu => (mem_normalizer_iff.mp (hW₀N (hTY₀ hg)) u).mp hu) hW
  rcases hTE E' hE'T hE'el hE'c with hmove | htrans
  ·
    obtain ⟨z, hzT, hz1, hzc, hzgen, h, hh, hc1, hcop⟩ := hmove
    refine hbot ?_
    by_contra hW
    obtain ⟨w, hwW, hw1, hwc⟩ := hcen hW
    have hzE : z ∈ E' :=
      CFSG.AGLEmbedding.CoreD2.mem_of_central Nat.prime_three hT27 hTnc hE'T hE'el hE'c hzT hzc
    have hzo : orderOf z = 3 := orderOf_eq_prime (hE'el.2 z hzE) hz1
    have hzW : z ∈ W₀ := by
      have hle : zpowers w ≤ zpowers z := zpowers_le.mpr (hzgen w (hW₀T hwW) hwc)
      have hcz : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
      have hcw : Nat.card (zpowers w) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp (hcz ▸ Subgroup.card_dvd_of_le hle) with h1 | h1
        · rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
          exact absurd h1 hw1
        · exact h1
      have heq : zpowers w = zpowers z := Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcw])
      exact zpowers_le.mpr hwW (heq ▸ mem_zpowers z)
    have hcW : z * (h * z * h⁻¹) ∈ W₀ :=
      W₀.mul_mem hzW ((mem_normalizer_iff.mp (hW₀N (hcore' hh)) z).mp hzW)
    obtain ⟨m, hm⟩ := hW₀p ⟨_, hcW⟩
    have hm' : (z * (h * z * h⁻¹)) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    exact hc1 (orderOf_eq_one_iff.mp
      ((hcop.symm.pow_right m).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hm')))
  have hNE' : normalizer (E' : Set K) ≤ Y₀.comap K.subtype :=
    (le_sSup ⟨E', le_rfl, hE'r, rfl⟩ : normalizer (E' : Set K) ≤ GLBCore 3 1 E').trans hcore'
  have hW : W₀ = ⊥ ∨ W₀ = E' := by
    by_cases hW : W₀ = ⊥
    · exact Or.inl hW
    right
    obtain ⟨w, hwW, hw1, hwc⟩ := hcen hW
    have hwE : w ∈ E' := CFSG.AGLEmbedding.CoreD2.mem_of_central Nat.prime_three hT27 hTnc hE'T
      hE'el hE'c (hW₀T hwW) hwc
    have hE'W : E' ≤ W₀ := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]
        exact W₀.one_mem
      obtain ⟨n, hn, rfl⟩ := htrans w hwE v hv hw1 hv1
      exact (mem_normalizer_iff.mp (hW₀N (hNE' hn)) w).mp hwW
    have hWT : W₀ ≠ T := by
      intro hWT
      have hcenE : ∀ v ∈ E', ∀ t ∈ (T : Subgroup K), t * v = v * t := by
        intro v hv t ht
        by_cases hv1 : v = 1
        · rw [hv1, mul_one, one_mul]
        obtain ⟨n, hn, rfl⟩ := htrans w hwE v hv hw1 hv1
        have hnT : n ∈ normalizer ((T : Subgroup K) : Set K) := hWT ▸ hW₀N (hNE' hn)
        have ht' : n⁻¹ * t * n ∈ (T : Subgroup K) := by
          have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hnT) t).mp ht
          simpa using this
        have h1 := hwc _ ht'
        calc t * (n * w * n⁻¹) = n * ((n⁻¹ * t * n) * w) * n⁻¹ := by group
          _ = n * (w * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
          _ = n * w * n⁻¹ * t := by group
      obtain ⟨a, ha, b, hb, hab⟩ := hTnc
      exact hab (commute_of_central hE'T hT27 hE'c
        (fun x hx y hy => congrArg Subtype.val (hE'el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hcenE
        a ha b hb)
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (hT27 ▸ Subgroup.card_dvd_of_le hW₀T)
    have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
      (hE'c ▸ hk ▸ Subgroup.card_dvd_of_le hE'W)
    rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
    · exact (Subgroup.eq_of_le_of_card_ge hE'W (by rw [hk, hE'c])).symm
    · exact absurd (Subgroup.eq_of_le_of_card_ge hW₀T (by rw [hk, hT27])) hWT
  rcases hW with hW | hW
  · exact hbot hW
  have hAE : ∀ x ∈ J ⊔ C, x ∈ K → x ∈ E := fun x hx hxK => by
    have h1 : (⟨x, hxK⟩ : K) ∈ W₀ := hA hx
    rw [hW] at h1
    exact h1
  have hinner : ∀ α : MulAut K, α ^ 3 = 1 → ∃ g : K, α = MulAut.conj g := fun α hα =>
    exists_conj_of_pow hout (n := 1) (by rwa [pow_one])
  have hKcomm : ∀ Q : Subgroup Y, Q ≤ K → Q ≤ J ⊔ C → (∀ x ∈ Q, x ^ 3 = 1) →
      ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun Q hQK hQJ _ x hx y hy =>
    congrArg Subtype.val
      (hE.1.is_comm.comm ⟨x, hAE x (hQJ hx) (hQK hx)⟩ ⟨y, hAE y (hQJ hy) (hQK hy)⟩)
  rcases SolvNone.le_centralizer_or_le_of_inner σ hZ
      (fun _ _ hy => exists_mul_of_pow_three hinner hy) hKcomm hrkC hC hO2 hker hσY hσs hb with
    h | ⟨hJK, y₀, -, hy₀3, hJy₀⟩
  · exact h
  by_contra hJC
  have hJ3' : ∀ x ∈ J, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hJy₀ hx)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₀3, one_zpow]
  have hJp : IsPGroup 3 J := fun x => ⟨1, Subtype.ext (by simpa using hJ3' x x.2)⟩
  have hJE : J ≤ E := fun x hx => hAE x (mem_sup_left hx) (hJK hx)
  have hJne : J ≠ ⊥ := fun h => hJC (by rw [h]; exact bot_le)
  have hJcard : Nat.card J = 3 := by
    have h1 : Nat.card J ∣ orderOf y₀ := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hJy₀
    have h3 : Nat.card J ∣ 3 := h1.trans (orderOf_dvd_of_pow_eq_one hy₀3)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq J h) hJne
    · exact h
  have hO2J : CFSG.pCore 2 ↥J = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥J) := (hJp.of_equiv Subgroup.topEquiv.symm)
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot ⟨hx, Subgroup.mem_top _⟩
  have hcardJq : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 3 := by
    rw [hO2J, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hJcard]
  have hPp : IsPGroup 3 (pCoreOf 3 Y₀) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 3 Y₀
  have hPK : pCoreOf 3 Y₀ ≤ K := h3K _ hPp
  have hPE : pCoreOf 3 Y₀ ≤ E := by
    have hPsub : CFSG.Open.IsSubnormal (pCoreOf 3 Y₀) Y₀ := CFSG.Open.IsSubnormal.step
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 3 Y₀)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 3 Y₀) (CFSG.Open.IsSubnormal.refl Y₀)
    have h1 : (pCoreOf 3 Y₀).comap K.subtype ≤ W₀ :=
      CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal (hPsub.comap K.subtype)
        (hPp.comap_of_injective K.subtype K.subtype_injective)
    intro x hx
    have h2 : (⟨x, hPK hx⟩ : K) ∈ W₀ := h1 hx
    rw [hW] at h2
    exact h2
  have hJP : J ≤ pCoreOf 3 Y₀ :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hJsub hJp
  have hD'E : (⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) ≤ E := iSup₂_le fun y hy => by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (mem_normalizer_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 3 Y₀ hy) x).mp
      (hJP hx)
    simpa [MulAut.conj_apply] using hPE h1
  have hh : ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 2 := by
    have hd := hdir
    unfold SolvThreeDirectCond at hd
    rw [hcardJq] at hd
    have h9 : 3 ^ ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 3 ^ 2 := by
      rw [← hd]
      calc _ ≤ Nat.card ↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
        _ ≤ Nat.card E := Subgroup.card_le_of_le hD'E
        _ = 3 ^ 2 := hEc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  obtain ⟨g, hg⟩ := exists_conj_eq_or_eq hh
  obtain ⟨j, hjJ, hj1⟩ : ∃ j ∈ J, j ≠ 1 := by
    by_contra h
    push Not at h
    exact hJne (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx))
  have hjE' : (⟨j, hJK hjJ⟩ : K) ∈ E' := hJE hjJ
  have hjK1 : (⟨j, hJK hjJ⟩ : K) ≠ 1 := fun h => hj1 (congrArg Subtype.val h)
  have hcover : (E : Set Y) ⊆ (J : Set Y) ∪ (J.map (MulAut.conj g).toMonoidHom : Set Y) := by
    intro e he
    by_cases he1 : e = 1
    · left
      rw [he1]
      exact J.one_mem
    obtain ⟨n, hnN, hne⟩ := htrans _ hjE' ⟨e, hEK he⟩ he hjK1
      (fun h => he1 (congrArg Subtype.val h))
    have hemem : e ∈ J.map (MulAut.conj (n : Y)).toMonoidHom := by
      refine ⟨j, hjJ, ?_⟩
      have h1 := congrArg Subtype.val hne
      simpa [MulAut.conj_apply] using h1
    rcases hg n (hNE' hnN) with h | h
    · left
      rw [h] at hemem
      exact hemem
    · right
      rw [h] at hemem
      exact hemem
  have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
  have h2 := Set.ncard_union_le (J : Set Y) (J.map (MulAut.conj g).toMonoidHom : Set Y)
  have h3 : (E : Set Y).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hEc
  have h4 : (J : Set Y).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hJcard
  have h5 : (J.map (MulAut.conj g).toMonoidHom : Set Y).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (J.map (MulAut.conj g).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hJcard]
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
