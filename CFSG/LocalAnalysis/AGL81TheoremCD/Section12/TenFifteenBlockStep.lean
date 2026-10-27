module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase
import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbParabSelfNorm
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceGlue
import CFSG.LocalAnalysis.AGLEmbedding.ParabolicTwoTransport
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOddQuot
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2 (NoXBlockFor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem not_dvd_card_outer_of_isOrthogonalTwo_or_alternating {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L)
    (hOA : IsOrthogonalTwo L ∨ ∃ m : ℕ, Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin m)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) : ¬ d ∣ Nat.card (Outer L) := by
  have : Group.IsPerfect L := hL.1
  have : Nontrivial (L ⧸ Subgroup.center L) := hL.2.1.toNontrivial
  have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have hd2 : d ≠ 2 := by omega
  rcases hOA with hO | ⟨m, hm⟩
  · rcases hO with ⟨i, hi, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.kFactOutOrthTwoPrime_holds i hi d hd hd5
    · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n (by omega) d hd hd2
  · rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup m
        (CFSG.AGLEmbedding.five_le_of_isPerfect_mulEquiv_alternatingGroup e) d hd hd2
    · obtain ⟨e⟩ := hm
      intro hdvd
      refine CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup m
        (CFSG.AGLEmbedding.five_le_of_isPerfect_mulEquiv_alternatingGroup e) d hd hd2 ?_
      rw [← Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact hdvd.trans (CFSG.AGLEmbedding.card_outer_dvd_card_outer_centerQuotient L)

omit [Finite X] in
theorem exists_mem_mul_mem_centralizer_of_not_dvd_card_outer {B : Subgroup X} {d k : ℕ}
    (hd : d.Prime) (hout : ¬ d ∣ Nat.card (Outer ↥B)) {z : X}
    (hz : z ∈ Subgroup.normalizer (B : Set X))
    (hzk : z ^ d ^ k ∈ Subgroup.centralizer (B : Set X)) :
    ∃ l ∈ B, z * l ∈ Subgroup.centralizer (B : Set X) := by
  set a : MulAut ↥B := B.normalizerMonoidHom ⟨z, hz⟩ with ha
  have hpow : (⟨z, hz⟩ : Subgroup.normalizer (B : Set X)) ^ d ^ k =
      ⟨z ^ d ^ k, Subgroup.pow_mem _ hz _⟩ := Subtype.ext (by rw [Subgroup.coe_pow])
  have hak : a ^ d ^ k = 1 := by
    rw [ha, ← map_pow, hpow, ← MonoidHom.mem_ker, B.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
    exact hzk
  have hcop : Nat.Coprime (d ^ k) (Nat.card (Outer ↥B)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hd).mpr hout)
  have hcop' : Nat.Coprime (orderOf a) (Nat.card (Outer ↥B)) :=
    hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hak)
  have hψ : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥B)
      a = 1 :=
    (pow_eq_one_iff_of_coprime hcop').mp
      ⟨by rw [← map_pow, pow_orderOf_eq_one, map_one], pow_card_eq_one'⟩
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  refine ⟨l⁻¹, B.inv_mem l.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : (l : X)⁻¹ * y * l ∈ B := B.mul_mem (B.mul_mem (B.inv_mem l.2) hy) l.2
  have h3 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨(l : X)⁻¹ * y * l, hy'⟩)
  change (l : X) * ((l : X)⁻¹ * y * l) * (l : X)⁻¹ =
    z * ((l : X)⁻¹ * y * l) * z⁻¹ at h3
  have h4 : y = z * ((l : X)⁻¹ * y * l) * z⁻¹ := by rw [← h3]; group
  calc y * (z * (l : X)⁻¹) = (z * ((l : X)⁻¹ * y * l) * z⁻¹) * (z * (l : X)⁻¹) := by
        conv_lhs => rw [h4]
    _ = (z * (l : X)⁻¹) * y := by group

private theorem exists_map_eq_map_conj_of_map_center_quotient {L : Type} [Group L]
    {P : Subgroup L} (hZP : Subgroup.center L ≤ P) (α : MulAut L)
    {γ : MulAut (L ⧸ Subgroup.center L)}
    (hγ : ∀ x : L, γ (QuotientGroup.mk' (Subgroup.center L) x) =
      QuotientGroup.mk' (Subgroup.center L) (α x))
    {ybar : L ⧸ Subgroup.center L}
    (hy : (P.map (QuotientGroup.mk' (Subgroup.center L))).map γ.toMonoidHom =
      (P.map (QuotientGroup.mk' (Subgroup.center L))).map
        (MulAut.conj ybar).toMonoidHom) :
    ∃ b : L, P.map α.toMonoidHom = P.map (MulAut.conj b).toMonoidHom := by
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) ybar
  let f : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hcompα : f.comp α.toMonoidHom = γ.toMonoidHom.comp f := by
    ext x
    exact (hγ x).symm
  have hcompb : f.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj ybar).toMonoidHom.comp f := by
    ext x
    change f (b * x * b⁻¹) = ybar * f x * ybar⁻¹
    rw [map_mul, map_mul, map_inv, hb]
  have hαmap : (P.map α.toMonoidHom).map f = (P.map f).map γ.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcompα]
  have hbmap : (P.map (MulAut.conj b).toMonoidHom).map f =
      (P.map f).map (MulAut.conj ybar).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcompb]
  have hcenterα : Subgroup.center L ≤ P.map α.toMonoidHom := by
    rw [← Subgroup.map_center_eq α]
    exact Subgroup.map_mono hZP
  have hcenterb : Subgroup.center L ≤ P.map (MulAut.conj b).toMonoidHom := by
    rw [← Subgroup.map_center_eq (MulAut.conj b)]
    exact Subgroup.map_mono hZP
  have hker : f.ker = Subgroup.center L := QuotientGroup.ker_mk' _
  have hkerα : f.ker ≤ P.map α.toMonoidHom := hker.trans_le hcenterα
  have hkerb : f.ker ≤ P.map (MulAut.conj b).toMonoidHom := hker.trans_le hcenterb
  have hcomapα : ((P.map α.toMonoidHom).map f).comap f = P.map α.toMonoidHom :=
    Subgroup.comap_map_eq_self hkerα
  have hcomapb : ((P.map (MulAut.conj b).toMonoidHom).map f).comap f =
      P.map (MulAut.conj b).toMonoidHom :=
    Subgroup.comap_map_eq_self hkerb
  refine ⟨b, ?_⟩
  calc P.map α.toMonoidHom
      = ((P.map α.toMonoidHom).map f).comap f := hcomapα.symm
    _ = ((P.map (MulAut.conj b).toMonoidHom).map f).comap f := by rw [hαmap, hbmap, hy]
    _ = P.map (MulAut.conj b).toMonoidHom := hcomapb

theorem exists_map_eq_map_conj_of_isParabolicTwo (hPC : KFactLieParabolicClass) {L : Type}
    [Group L] [Finite L] (hL : IsQuasisimple L)
    (hLY : IsClassicalTwoOrG2 (L ⧸ Subgroup.center L))
    (hZ : Odd (Nat.card (Subgroup.center L))) {P : Subgroup L} (hP : IsParabolicTwo ⊤ P)
    (α : MulAut L) (hα : Nat.Coprime (orderOf α) 6) :
    ∃ b : L, P.map α.toMonoidHom = P.map (MulAut.conj b).toMonoidHom := by
  classical
  let Z : Subgroup L := Subgroup.center L
  let π : L →* L ⧸ Z := QuotientGroup.mk' Z
  have hZP : Z ≤ P := by
    obtain ⟨-, T, -, hNT⟩ := hP
    intro z hz
    refine hNT (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top z, ?_⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [← Subgroup.mem_center_iff.mp hz t, mul_assoc, mul_inv_cancel, mul_one]
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hpar : IsParabolicTwo ⊤ (P.map π) :=
    hP.map_top_of_surjective_of_odd_ker π (QuotientGroup.mk'_surjective Z)
      (by rw [hker]; exact hZ)
  let β : MulAut (L ⧸ Z) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L α
  have hβ : Nat.Coprime (orderOf β) 6 :=
    hα.coprime_dvd_left (orderOf_map_dvd
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L) α)
  obtain ⟨ybar, hybar⟩ := hPC (L ⧸ Z) hL.2.1 hLY (P.map π) hpar β hβ
  exact exists_map_eq_map_conj_of_map_center_quotient hZP α (γ := β)
    (fun x => CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α x)
    hybar

omit [Finite X] in
private theorem map_subgroupOf_map_conj_of_apply {B P : Subgroup X} (hP : P ≤ B)
    {ψ : MulAut ↥B} {w : X} (hw : ∀ y : ↥B, (ψ y : X) = w * (y : X) * w⁻¹) :
    ((P.subgroupOf B).map ψ.toMonoidHom).map B.subtype =
      P.map (MulAut.conj w).toMonoidHom := by
  rw [Subgroup.map_map]
  have hcomp : B.subtype.comp ψ.toMonoidHom =
      (MulAut.conj w).toMonoidHom.comp B.subtype := by
    ext y
    exact hw y
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP]

theorem exists_mem_mul_mem_normalizer_of_isParabolicTwo (hPC : KFactLieParabolicClass)
    {B : Subgroup X} (hB : IsComponentOf B ⊤)
    (hBY : IsClassicalTwoOrG2 (↥B ⧸ Subgroup.center ↥B))
    (hZ : Odd (Nat.card (Subgroup.center ↥B))) {P : Subgroup X} (hP : IsParabolicTwo B P)
    {z : X} (hz : z ∈ Subgroup.normalizer (B : Set X)) {n : ℕ} (hn : Nat.Coprime n 6)
    (hzn : z ^ n ∈ Subgroup.centralizer (B : Set X)) :
    ∃ l ∈ B, z * l ∈ Subgroup.normalizer (P : Set X) := by
  classical
  let a : MulAut ↥B := Subgroup.normalizerMonoidHom B ⟨z, hz⟩
  have hpow : a ^ n = 1 := by
    change (Subgroup.normalizerMonoidHom B ⟨z, hz⟩) ^ n = 1
    ext y
    rw [← map_pow]
    change z ^ n * (y : X) * (z ^ n)⁻¹ = (y : X)
    have hcomm : (y : X) * z ^ n = z ^ n * (y : X) :=
      (Subgroup.mem_centralizer_iff.mp hzn) (y : X) y.2
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have ha6 : Nat.Coprime (orderOf a) 6 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hpow) hn
  obtain ⟨b, hb⟩ := exists_map_eq_map_conj_of_isParabolicTwo hPC
    (CFSG.AGLEmbedding.ToralReduce.isQuasisimple_of_isQuasisimple_open hB.2.2) hBY hZ
    hP.subgroupOf_top a ha6
  refine ⟨z⁻¹ * (b : X)⁻¹ * z, ?_, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hz)) ((b : X)⁻¹)
    simpa using h.mp (B.inv_mem b.2)
  · have hzl : z * (z⁻¹ * (b : X)⁻¹ * z) = (b : X)⁻¹ * z := by group
    rw [hzl, Subgroup.mem_normalizer_iff_map_conj_eq]
    change P.map (MulAut.conj ((b : X)⁻¹ * z)).toMonoidHom = P
    have hconj : P.map (MulAut.conj z).toMonoidHom =
        P.map (MulAut.conj (b : X)).toMonoidHom := by
      have h := congrArg (fun Q : Subgroup ↥B => Q.map B.subtype) hb
      rwa [map_subgroupOf_map_conj_of_apply hP.1 (fun _ => rfl),
        map_subgroupOf_map_conj_of_apply hP.1 (fun _ => rfl)] at h
    have hmul : MulAut.conj ((b : X)⁻¹ * z) =
        (MulAut.conj (b : X))⁻¹ * MulAut.conj z := by
      rw [map_mul, map_inv]
    rw [hmul]
    calc P.map (((MulAut.conj (b : X))⁻¹ * MulAut.conj z)).toMonoidHom
        = (P.map (MulAut.conj z).toMonoidHom).map
            ((MulAut.conj (b : X))⁻¹).toMonoidHom :=
          (Subgroup.map_map P ((MulAut.conj (b : X))⁻¹).toMonoidHom
            (MulAut.conj z).toMonoidHom).symm
      _ = (P.map (MulAut.conj (b : X)).toMonoidHom).map
            ((MulAut.conj (b : X))⁻¹).toMonoidHom := by rw [hconj]
      _ = P := by
          rw [Subgroup.map_map]
          have hone : ((MulAut.conj (b : X))⁻¹).toMonoidHom.comp
              (MulAut.conj (b : X)).toMonoidHom = MonoidHom.id X := by
            ext y
            exact MulAut.inv_apply_self X (MulAut.conj (b : X)) y
          rw [hone]
          simp

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem nineThreeTwo_or_isOrthogonalTwo_or_alternating {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M) (h93 : Asc81bNineThree)
    (hD2 : NoXBlockFor G) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    NineThreeTwo M (pCoreOf 2 H) L ∨
      (IsOrthogonalTwo ↥(barM M L) ∨ ∃ m : ℕ,
        Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) := by
  rcases h.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (hD2 M L h.maxTwoLocal_M hL.le hL.subnormal h1).elim
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3.2.1)
  · exact Or.inr (Or.inr ⟨6, Or.inr h4.2.2.1⟩)
  · exact Or.inr (Or.inr ⟨7, Or.inl h5.2.1⟩)
  · obtain ⟨-, n, hn, -⟩ := h6
    exact Or.inr (Or.inr ⟨2 * n, Or.inr hn⟩)
  · obtain ⟨-, n, hn, -⟩ := h7
    exact Or.inr (Or.inr ⟨4 * n, Or.inl hn⟩)
  · obtain ⟨-, N, r, -, -, -, -, -, hN, -⟩ := h8
    exact Or.inr (Or.inr ⟨N, Or.inl hN⟩)

omit [Finite G] in
theorem barM_normalizer_eq_normalizer_barM {M S : Subgroup G} (hSM : S ≤ M)
    (hQS : pCoreOf 2 M ≤ S) :
    barM M (Subgroup.normalizer (S : Set G)) =
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine le_antisymm (barM_le_normalizer_barM (L := Subgroup.normalizer (S : Set G)) le_rfl) ?_
  exact fun x hx => CFSG.AGLEmbeddingD2.mem_barM_normalizer_of_mem_normalizer_barM hSM hQS hx

theorem mem_normalizer_barM_twoCore_of_conj_mem_sup_centralizer {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    {l : ↥M ⧸ CFSG.pCore 2 ↥M} (hl : l ∈ barM M L)
    (hlS : ∀ s ∈ barM M (pCoreOf 2 H), l * s * l⁻¹ ∈
      barM M (pCoreOf 2 H) ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    l ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set S := pCoreOf 2 H with hS
  set Sb := barM M S with hSb
  set Lb := barM M L with hLb
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  obtain ⟨hSL, -⟩ := h.weakSBlock_asc81bHyp hK h86 hL
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM hSL
  have hSbC : Sb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hSbL.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer Lb)
  have hlP : l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    refine h.blockInnerNormalizer hK h84 h86 hD2 hL l hl ?_
    intro s hs
    have hs1 : l * s * l⁻¹ ∈ (↑(Sb ⊔ C) : Set _) := hlS s hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Sb C hSbC] at hs1
    obtain ⟨s', hs', c, hc, hsc⟩ := hs1
    refine ⟨s', hs', fun y hy => ?_⟩
    have hcy : c * y * c⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_iff.mp hc y hy]
      group
    calc (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹
        = (s' * c) * y * (s' * c)⁻¹ := by rw [← hsc]
      _ = s' * (c * y * c⁻¹) * s'⁻¹ := by group
      _ = s' * y * s'⁻¹ := by rw [hcy]
  exact (barM_le_normalizer_barM (L := Subgroup.normalizer (S : Set G)) (S := S) le_rfl)
    (barM_mono inf_le_left hlP)

theorem exists_mem_barM_mul_mem_centralizer_or_normalizer (hPC : KFactLieParabolicClass)
    {M H : Subgroup G} (h : TwoLocalPhaseThree M H) (hK : CFSG.Open.IsKGroup ↥M)
    (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {z : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hz : z ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) {k : ℕ}
    (hzk : z ^ d ^ k ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ l ∈ barM M L, z * l ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      (z * l ∈ Subgroup.normalizer ((barM M L ⊓ Subgroup.normalizer
          (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
            Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        ∀ l' ∈ barM M L, l' ∈ Subgroup.normalizer ((barM M L ⊓ Subgroup.normalizer
            (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
              Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          l' ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  set S := pCoreOf 2 H with hS
  set Lb := barM M L with hLb
  set Sb := barM M S with hSb
  have hweak : IsWeakSBlock M S L := hL
  have hPeq : barM M (Subgroup.normalizer (S : Set G) ⊓ L) =
      Lb ⊓ Subgroup.normalizer (Sb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [CFSG.HardMathSupport.Cooperstein.StructureLie.barM_normalizer_inf
      (h.twoCore_M_le h.twoCore_inf) h.twoCore_le, inf_comm]
  rcases nineThreeTwo_or_isOrthogonalTwo_or_alternating h hK h93 hD2 hL with h2 | hOA
  · have hZ : Odd (Nat.card (Subgroup.center ↥Lb)) :=
      CFSG.AGLEmbedding.ToralReduce.odd_card_center_barM hweak.toIsTwoPrimeComponent
    have h6 : Nat.Coprime d 6 := by
      rw [Nat.Prime.coprime_iff_not_dvd hd]
      intro hdvd
      have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases d
      · norm_num at hdvd
      · norm_num at hd
    obtain ⟨l, hlL, hlN⟩ := exists_mem_mul_mem_normalizer_of_isParabolicTwo hPC
      hweak.component h2.1 hZ h2.2.1 hz (Nat.Coprime.pow_left k h6) hzk
    refine ⟨l, hlL, Or.inr ⟨?_, ?_⟩⟩
    · rw [← hPeq]
      exact hlN
    · intro l' hl'L hl'N
      have hpar : IsParabolicTwo Lb (Lb ⊓ Subgroup.normalizer
          (Sb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := hPeq ▸ h2.2.1
      exact (CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo
        hpar hl'L hl'N).2
  · have hqs : CFSG.IsQuasisimple ↥Lb := by
      have hperf : Group.IsPerfect ↥Lb := ⟨hweak.component.2.2.1⟩
      have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hweak.component.2.2.2
      refine ⟨hperf, hsimple, ?_⟩
      have hperfQ : Group.IsPerfect (↥Lb ⧸ Subgroup.center ↥Lb) :=
        @Group.IsPerfect.instQuotientSubgroup ↥Lb _ (Subgroup.center ↥Lb) _ hperf
      have hnc : ¬ IsMulCommutative (↥Lb ⧸ Subgroup.center ↥Lb) :=
        @Group.IsPerfect.not_isMulCommutative (↥Lb ⧸ Subgroup.center ↥Lb) _
          hsimple.toNontrivial hperfQ
      rw [isMulCommutative_iff] at hnc
      obtain ⟨a, ha⟩ := not_forall.mp hnc
      exact ⟨a, not_forall.mp ha⟩
    have hout : ¬ d ∣ Nat.card (Outer ↥Lb) :=
      not_dvd_card_outer_of_isOrthogonalTwo_or_alternating hqs hOA hd hd5
    obtain ⟨l, hlL, hlC⟩ :=
      exists_mem_mul_mem_centralizer_of_not_dvd_card_outer hd hout hz hzk
    exact ⟨l, hlL, Or.inl hlC⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
