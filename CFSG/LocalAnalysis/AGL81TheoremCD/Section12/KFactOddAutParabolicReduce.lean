module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactClass
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabBase
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedLift
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def KFactOddAutParabolicFixSimple : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsClassicalTwoOrG2 Y →
    ∀ P : Subgroup Y, IsParabolicTwo ⊤ P →
    ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ Nat.card P →
    ∀ (α : MulAut Y) (k : ℕ), orderOf α = r ^ k →
      Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner Y = ⊥ →
      ∃ y : Y, (P.map (MulAut.conj y).toMonoidHom).map α.toMonoidHom =
        P.map (MulAut.conj y).toMonoidHom

@[expose] def OddAutSylowFixAt (r : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ (α : MulAut Y) (k : ℕ), orderOf α = r ^ k →
    Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner Y = ⊥ →
    ∃ S : Sylow 2 Y, (S : Subgroup Y).map α.toMonoidHom = S

@[expose] def KFactOddAutSylowFix : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsClassicalTwoOrG2 Y →
    ∀ r : ℕ, r.Prime → 5 ≤ r →
    (∃ T : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ ∧
      ¬ r ∣ Nat.card (Subgroup.normalizer (T : Set Y))) →
    OddAutSylowFixAt r Y

theorem exists_map_conj_eq_of_map_sylow_eq {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsParabolicTwo ⊤ P) (α : MulAut Y)
    (hcl : ∀ y : Y, ∃ z : Y, (P.map (MulAut.conj y).toMonoidHom).map α.toMonoidHom =
      (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj z).toMonoidHom)
    (S : Sylow 2 Y) (hS : (S : Subgroup Y).map α.toMonoidHom = S) :
    ∃ y : Y, (P.map (MulAut.conj y).toMonoidHom).map α.toMonoidHom =
      P.map (MulAut.conj y).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_isParabolicTwo S rfl hP
  obtain ⟨z, hz⟩ := hcl g
  set Q : Subgroup Y := P.map (MulAut.conj g).toMonoidHom with hQ
  have hSQ : (S : Subgroup Y) ≤ Q := Subgroup.le_normalizer.trans hg
  have hSZ : (S : Subgroup Y) ≤ Q.map (MulAut.conj z).toMonoidHom := by
    rw [← hz, ← hS]
    exact Subgroup.map_mono (f := α.toMonoidHom) hSQ
  have hconj : (S : Subgroup Y).map (MulAut.conj z⁻¹).toMonoidHom ≤ Q := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨q, hq, hqs⟩ := Subgroup.mem_map.mp (hSZ hs)
    rw [← hqs]
    simpa [MulAut.conj_apply, mul_assoc] using hq
  have hzQ : z ∈ Q := by
    have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.mem_of_conj_le S hg (g := z⁻¹)
      (fun s hs => by
        have hmem := hconj (Subgroup.mem_map_of_mem (MulAut.conj z⁻¹).toMonoidHom hs)
        simpa [MulAut.conj_apply, mul_assoc] using hmem)
    simpa using Subgroup.inv_mem Q h
  have hzfix : Q.map (MulAut.conj z).toMonoidHom = Q := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hzQ) : Q.map (MulAut.conj z) = Q)
  exact ⟨g, hz.trans hzfix⟩

theorem kFactOddAutParabolicFixSimple_of_sylowFix (hPC : KFactLieParabolicClass)
    (hS : KFactOddAutSylowFix) : KFactOddAutParabolicFixSimple := by
  intro Y _ _ hsimple hclass P hP r hr hr5 hnotdvd α k hα hinn
  have hP' := hP
  obtain ⟨-, T, ⟨-, hT2, hTi⟩, hTP⟩ := hP
  have hNT : Subgroup.normalizer (T : Set Y) ≤ P := by simpa using hTP
  have hnotdvdNT : ¬ r ∣ Nat.card (Subgroup.normalizer (T : Set Y)) :=
    fun h => hnotdvd (h.trans (Subgroup.card_dvd_of_le hNT))
  obtain ⟨S, hSfix⟩ :=
    hS Y hsimple hclass r hr hr5 ⟨T, ⟨le_top, hT2, hTi⟩, hnotdvdNT⟩ α k hα hinn
  have hcop : Nat.Coprime (orderOf α) 6 := by
    have hr6 : Nat.Coprime r 6 := by
      rw [hr.coprime_iff_not_dvd]
      intro hdvd
      have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases r
      · norm_num at hdvd
      · norm_num at hr
    rw [hα]
    exact hr6.pow_left k
  refine exists_map_conj_eq_of_map_sylow_eq hP' α ?_ S hSfix
  intro y
  exact hPC Y hsimple hclass (P.map (MulAut.conj y).toMonoidHom)
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.isParabolicTwo_map_mulEquiv
      (MulAut.conj y) hP') α hcop

theorem _root_.CFSG.AGLEmbedding.IsParabolicTwo.map_center_quotient {L : Type} [Group L]
    [Finite L] {P : Subgroup L} (hP : IsParabolicTwo ⊤ P) :
    IsParabolicTwo ⊤ (P.map (QuotientGroup.mk' (Subgroup.center L))) := by
  obtain ⟨-, T, hT, hNT⟩ := hP
  refine ⟨le_top, T.map (QuotientGroup.mk' (Subgroup.center L)),
    isSylowTwoOf_map_top_of_surjective hT (QuotientGroup.mk'_surjective _), ?_⟩
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) z
  exact Subgroup.mem_map_of_mem _ (hNT (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_top x,
      mem_normalizer_of_mk_center_mem_normalizer hT (Subgroup.mem_inf.mp hz).2⟩))

theorem centerQuotientHom_zpowers_inf_inner {L : Type} [Group L] [Group.IsPerfect L]
    (α : MulAut L)
    (h : Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner L = ⊥) :
    orderOf (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α) =
        orderOf α ∧
      Subgroup.zpowers (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α) ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner (L ⧸ Subgroup.center L) = ⊥ := by
  let φ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L
  have hφ : Function.Injective φ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective L
  constructor
  · exact orderOf_injective φ hφ α
  · rw [eq_bot_iff]
    intro β hβ
    obtain ⟨hβz, hβi⟩ := Subgroup.mem_inf.mp hβ
    rw [Subgroup.mem_bot]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hβz
    obtain ⟨g, hg⟩ := hβi
    have hconj : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (α ^ n) =
        MulAut.conj g := by
      rw [show CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (α ^ n) =
          φ (α ^ n) from rfl, map_zpow φ α n, hn, ← hg]
    obtain ⟨y, hy⟩ := CFSG.LocalAnalysis.WeakClosure81.isInner_of_onCenterQuotient_inner
      (α ^ n) ⟨g, fun x => by rw [hconj]; exact MulAut.conj_apply g x⟩
    have hmem : α ^ n ∈ Subgroup.zpowers α ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner L :=
      Subgroup.mem_inf.mpr ⟨Subgroup.zpow_mem_zpowers α n,
        ⟨y, MulEquiv.ext fun x => (hy x).symm⟩⟩
    rw [h] at hmem
    have hpow : α ^ n = 1 := Subgroup.mem_bot.mp hmem
    calc β = φ (α ^ n) := by rw [← hn, ← map_zpow]
      _ = 1 := by rw [hpow, map_one]

private theorem quotient_ker_le_map_of_map_quotient {L : Type} [Group L] {N Q : Subgroup L}
    [N.Normal] (hNQ : N ≤ Q) (α : MulAut L) {γ : MulAut (L ⧸ N)}
    (hγ : ∀ x : L, γ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (α x)) :
    (QuotientGroup.mk' N).ker ≤ Q.map α.toMonoidHom := by
  have hmemN : ∀ x : L, α x ∈ N ↔ x ∈ N := by
    intro x
    constructor
    · intro hx
      have h1 : γ ((QuotientGroup.mk' N) x) = 1 := by
        rw [hγ x]
        exact (QuotientGroup.eq_one_iff (α x)).mpr hx
      have h2 : (QuotientGroup.mk' N) x = 1 := (map_eq_one_iff γ γ.injective).mp h1
      exact (QuotientGroup.eq_one_iff x).mp h2
    · intro hx
      have h1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      have h2 : γ ((QuotientGroup.mk' N) x) = 1 := by rw [h1, map_one]
      have h3 : (QuotientGroup.mk' N) (α x) = 1 := by rw [← hγ x]; exact h2
      exact (QuotientGroup.eq_one_iff (α x)).mp h3
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hx
  have hpre : α.symm x ∈ N := by
    refine (hmemN (α.symm x)).mp ?_
    simpa using hxN
  have h := Subgroup.mem_map_of_mem α.toMonoidHom (hNQ hpre)
  simpa using h

private theorem quotient_ker_le_map_conj {L : Type} [Group L] {N Q : Subgroup L} [N.Normal]
    (hNQ : N ≤ Q) (b : L) :
    (QuotientGroup.mk' N).ker ≤ Q.map (MulAut.conj b).toMonoidHom := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hx
  have hmem : b⁻¹ * x * b ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem x hxN b⁻¹
  have h := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom (hNQ hmem)
  simpa [MulAut.conj_apply, mul_assoc] using h

theorem map_eq_map_conj_of_map_quotient_eq_map_conj {L : Type} [Group L] {N Q : Subgroup L}
    [N.Normal] (hNQ : N ≤ Q) (α : MulAut L) {γ : MulAut (L ⧸ N)}
    (hγ : ∀ x : L, γ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (α x)) (b : L)
    (hb : (Q.map (QuotientGroup.mk' N)).map γ.toMonoidHom =
      (Q.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N b)).toMonoidHom) :
    Q.map α.toMonoidHom = Q.map (MulAut.conj b).toMonoidHom := by
  have hkerα := quotient_ker_le_map_of_map_quotient hNQ α hγ
  have hkerb := quotient_ker_le_map_conj hNQ b
  have hcompα : (QuotientGroup.mk' N).comp α.toMonoidHom =
      γ.toMonoidHom.comp (QuotientGroup.mk' N) := by
    ext x
    exact (hγ x).symm
  have hcompb : (QuotientGroup.mk' N).comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (QuotientGroup.mk' N b)).toMonoidHom.comp (QuotientGroup.mk' N) := by
    ext x
    change QuotientGroup.mk' N (b * x * b⁻¹) =
      QuotientGroup.mk' N b * QuotientGroup.mk' N x * (QuotientGroup.mk' N b)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hαmap : (Q.map α.toMonoidHom).map (QuotientGroup.mk' N) =
      (Q.map (QuotientGroup.mk' N)).map γ.toMonoidHom := by
    rw [Subgroup.map_map, hcompα, ← Subgroup.map_map]
  have hbmap : (Q.map (MulAut.conj b).toMonoidHom).map (QuotientGroup.mk' N) =
      (Q.map (QuotientGroup.mk' N)).map
        (MulAut.conj (QuotientGroup.mk' N b)).toMonoidHom := by
    rw [Subgroup.map_map, hcompb, ← Subgroup.map_map]
  have hcomapα : ((Q.map α.toMonoidHom).map (QuotientGroup.mk' N)).comap
      (QuotientGroup.mk' N) = Q.map α.toMonoidHom :=
    Subgroup.comap_map_eq_self hkerα
  have hcomapb : ((Q.map (MulAut.conj b).toMonoidHom).map (QuotientGroup.mk' N)).comap
      (QuotientGroup.mk' N) = Q.map (MulAut.conj b).toMonoidHom :=
    Subgroup.comap_map_eq_self hkerb
  calc Q.map α.toMonoidHom
      = ((Q.map α.toMonoidHom).map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N) := hcomapα.symm
    _ = ((Q.map (MulAut.conj b).toMonoidHom).map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N) := by rw [hαmap, hbmap, hb]
    _ = Q.map (MulAut.conj b).toMonoidHom := hcomapb

private theorem map_eq_self_of_map_quotient_eq_self {L : Type} [Group L] {N Q : Subgroup L}
    [N.Normal] (hNQ : N ≤ Q) (α : MulAut L) {γ : MulAut (L ⧸ N)}
    (hγ : ∀ x : L, γ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (α x))
    (hQ : (Q.map (QuotientGroup.mk' N)).map γ.toMonoidHom = Q.map (QuotientGroup.mk' N)) :
    Q.map α.toMonoidHom = Q := by
  have hb : (Q.map (QuotientGroup.mk' N)).map
      (MulAut.conj (QuotientGroup.mk' N (1 : L))).toMonoidHom = Q.map (QuotientGroup.mk' N) := by
    rw [map_one, show MulAut.conj (1 : L ⧸ N) = 1 from map_one _, MulAut.one_def]
    exact Subgroup.map_id _
  have h := map_eq_map_conj_of_map_quotient_eq_map_conj hNQ α hγ 1 (hQ.trans hb.symm)
  rw [show MulAut.conj (1 : L) = 1 from map_one _, MulAut.one_def] at h
  have hmap : Q.map (MulEquiv.refl L).toMonoidHom = Q := Subgroup.map_id _
  rwa [hmap] at h

theorem kFactOddAutParabolicFix_of_simple (h : KFactOddAutParabolicFixSimple) :
    KFactOddAutParabolicFix := by
  intro L _ _ hL hLY P hP r hr hr5 hrP α k hα hinn
  classical
  let Z : Subgroup L := Subgroup.center L
  let π : L →* L ⧸ Z := QuotientGroup.mk' Z
  have hperf : Group.IsPerfect L := ⟨hL.1⟩
  have hZP : Z ≤ P := by
    obtain ⟨-, T, -, hNT⟩ := hP
    intro z hz
    refine hNT (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top z, ?_⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← Subgroup.mem_center_iff.mp hz t, mul_assoc, mul_inv_cancel, mul_one]
  have hpar : IsParabolicTwo ⊤ (P.map π) := hP.map_center_quotient
  have hquot := centerQuotientHom_zpowers_inf_inner (L := L) α hinn
  have hdiv : ¬ r ∣ Nat.card (P.map π) := fun hd =>
    hrP (hd.trans (Subgroup.card_map_dvd P π))
  obtain ⟨ybar, hybar⟩ := h (L ⧸ Z) hL.2 hLY (P.map π) hpar r hr hr5 hdiv
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α) k
    (hquot.1.trans hα) hquot.2
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective Z ybar
  refine ⟨b, ?_⟩
  have hNQ : Z ≤ P.map (MulAut.conj b).toMonoidHom := by
    change Subgroup.center L ≤ Subgroup.map (MulAut.conj b).toMonoidHom P
    rw [← Subgroup.map_center_eq (MulAut.conj b)]
    exact Subgroup.map_mono hZP
  have hQmap : (P.map (MulAut.conj b).toMonoidHom).map π =
      (P.map π).map (MulAut.conj ybar).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    change π (b * x * b⁻¹) = ybar * π x * ybar⁻¹
    rw [map_mul, map_mul, map_inv, hb]
  have hγ : ∀ x : L,
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α) (π x) =
        π (α x) := fun x =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α x
  have hfix : ((P.map (MulAut.conj b).toMonoidHom).map π).map
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α).toMonoidHom =
      (P.map (MulAut.conj b).toMonoidHom).map π := by
    rw [hQmap, hybar]
  exact map_eq_self_of_map_quotient_eq_self hNQ α hγ hfix

theorem pow_orderOf_eq_one_of_mul {G : Type*} [Group G] {H D : Subgroup G} {r k : ℕ}
    (hDr : ∀ δ ∈ D, ∀ j : ℕ, δ ^ (r ^ j) ∈ H → δ ∈ H)
    {d f : G} (hd : d ∈ D) (hf : ∀ g ∈ D, f * g * f⁻¹ ∈ D)
    (hαk : (d * f) ^ (r ^ k) = 1) (hinn : Subgroup.zpowers (d * f) ⊓ H = ⊥) :
    (d * f) ^ orderOf f = 1 := by
  have key : ∀ m : ℕ, ∃ δ ∈ D, (d * f) ^ m = δ * f ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, D.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨δ, hδ, hm⟩ := ih
      refine ⟨d * (f * δ * f⁻¹), D.mul_mem hd (hf δ hδ), ?_⟩
      rw [pow_succ', hm]
      group
  obtain ⟨δ, hδ, hm⟩ := key (orderOf f)
  rw [pow_orderOf_eq_one, mul_one] at hm
  have hδH : δ ∈ H := by
    refine hDr δ hδ k ?_
    rw [← hm, ← pow_mul, mul_comm, pow_mul, hαk, one_pow]
    exact H.one_mem
  have hmem : (d * f) ^ orderOf f ∈ Subgroup.zpowers (d * f) ⊓ H :=
    Subgroup.mem_inf.mpr ⟨Subgroup.npow_mem_zpowers _ _, hm ▸ hδH⟩
  rw [hinn] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem OddAutSylowFixAt.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : OddAutSylowFixAt r Y) : OddAutSylowFixAt r Y' := by
  intro α' k hα' hinn'
  let α : MulAut Y := (MulAut.congr e).symm α'
  have hφα : MulAut.congr e α = α' := MulEquiv.apply_symm_apply (MulAut.congr e) α'
  have hφα' : (MulAut.congr e).toMonoidHom α = α' := hφα
  have horder : orderOf α = r ^ k := by
    rw [← MulEquiv.orderOf_eq (MulAut.congr e) α, hφα, hα']
  have hinner : Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner Y = ⊥ := by
    have hmap : (Subgroup.zpowers α ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner Y).map
          (MulAut.congr e).toMonoidHom =
        Subgroup.zpowers α' ⊓
          CFSG.ComponentClassification.OuterAutomorphisms.inner Y' := by
      rw [Subgroup.map_inf _ _ _ (MulAut.congr e).injective, MonoidHom.map_zpowers,
        CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e, hφα']
    have hbot : (Subgroup.zpowers α ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner Y).map
          (MulAut.congr e).toMonoidHom = ⊥ := by
      rw [hmap, hinn']
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.zpowers α ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner Y)
      (MulAut.congr e).injective).mp hbot
  obtain ⟨S, hS⟩ := h α k horder hinner
  obtain ⟨Q, hQ⟩ := S.exists_comap_eq_of_injective (f := e.toMonoidHom) e.injective
  refine ⟨Q, ?_⟩
  have hQmap : Q = S.map e.toMonoidHom := by
    rw [← hQ, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  have hcomp : α'.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
    ext x
    have hx := congrArg (fun f : MulAut Y' => f (e x)) hφα
    simpa [MulAut.congr, MulEquiv.trans_apply, MonoidHom.comp_apply] using hx.symm
  rw [hQmap, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact congrArg (fun T : Subgroup Y => T.map e.toMonoidHom) hS

theorem OddAutSylowFixAt.of_conj {r : ℕ} {Y : Type} [Group Y] [Finite Y] (S₀ : Sylow 2 Y)
    (h : ∀ (α : MulAut Y) (k : ℕ), orderOf α = r ^ k →
      Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner Y = ⊥ →
      ∃ γ ψ : MulAut Y, α = γ * ψ * γ⁻¹ ∧ (S₀ : Subgroup Y).map ψ.toMonoidHom = S₀) :
    OddAutSylowFixAt r Y := by
  intro α k hα hinn
  obtain ⟨γ, ψ, rfl, hψ⟩ := h α k hα hinn
  have hsurj : Function.Surjective (γ.toMonoidHom : Y →* Y) := fun y => ⟨γ.symm y, by simp⟩
  refine ⟨Sylow.mapSurjective hsurj S₀, ?_⟩
  change ((S₀ : Subgroup Y).map γ.toMonoidHom).map (γ * ψ * γ⁻¹).toMonoidHom =
    (S₀ : Subgroup Y).map γ.toMonoidHom
  rw [Subgroup.map_map]
  have hcomp : (γ * ψ * γ⁻¹).toMonoidHom.comp γ.toMonoidHom =
      γ.toMonoidHom.comp ψ.toMonoidHom := by
    ext x
    simp
  rw [hcomp, ← Subgroup.map_map, hψ]

theorem OddAutSylowFixAt.of_card_outer_le_four {r : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hr : r.Prime) (hr5 : 5 ≤ r) (hY : Nat.card (Outer Y) ≤ 4) : OddAutSylowFixAt r Y := by
  intro α k hα hinn
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) fun f g hfg => MulEquiv.ext (congrFun hfg)
  change Nat.card (MulAut Y ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner Y) ≤ 4 at hY
  let π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Y)
  have h1 : orderOf (π α) ∣ r ^ k := hα ▸ orderOf_map_dvd π α
  have h2 : orderOf (π α) ∣ Nat.card (MulAut Y ⧸
      CFSG.ComponentClassification.OuterAutomorphisms.inner Y) := orderOf_dvd_natCard _
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hr).mp h1
  have hle : orderOf (π α) ≤ 4 := (Nat.le_of_dvd Nat.card_pos h2).trans hY
  have hj0 : j = 0 := by
    by_contra hne
    have : r ≤ r ^ j := Nat.le_self_pow hne r
    omega
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hjeq
  have hαinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
    (QuotientGroup.eq_one_iff α).mp hjeq
  have hα1 : α = 1 := by
    have hmem : α ∈ Subgroup.zpowers α ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers α, hαinn⟩
    rw [hinn] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  refine ⟨S, ?_⟩
  subst hα1
  ext x
  simp [Subgroup.mem_map]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
