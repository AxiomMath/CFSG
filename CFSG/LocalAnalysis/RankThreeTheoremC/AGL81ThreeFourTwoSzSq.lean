module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveSz
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.AutL2Facts
open CFSG.AGLEmbedding.KFactProofs.Sz32Local (Sz32Data)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (IsSz32Type sz32_data sz32_outer)

section OuterProd

variable {L : Type*} [Group L]

private theorem simpleCentreless_of_nonabelian [IsSimpleGroup L]
    (hLnab : ∃ a b : L, a * b ≠ b * a) : SimpleCentreless L := by
  obtain ⟨a, b, hab⟩ := hLnab
  refine ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N, fun z hz => ?_, ⟨a, ?_⟩⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · have hz' : z ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
      rwa [h, Subgroup.mem_bot] at hz'
    · have ha : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  · rintro rfl
    exact hab (by rw [one_mul, mul_one])

private theorem mem_inner_prod_of_fstHom_sndHom [Finite L] (φ : presSub L)
    (h1 : fstHom φ ∈ inner L) (h2 : sndHom φ ∈ inner L) :
    (φ : MulAut (L × L)) ∈ inner (L × L) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(a, b), MulEquiv.ext fun x => ?_⟩
  obtain ⟨s, t⟩ := x
  rw [presSub_apply, ← ha, ← hb]
  simp [MulAut.conj_apply]

theorem isSolvable_outer_prod_self_of_comm [Finite L] [IsSimpleGroup L]
    (hLnab : ∃ a b : L, a * b ≠ b * a) (hOut : ∀ a b : Outer L, a * b = b * a) :
    Group.IsSolvable (Outer (L × L)) := by
  have hS : SimpleCentreless L := simpleCentreless_of_nonabelian hLnab
  set P : Subgroup (MulAut (L × L)) := presSub L with hP
  have hIP : inner (L × L) ≤ P := by
    rintro _ ⟨g, rfl⟩
    exact ⟨fun s => by simp [MulAut.conj_apply], fun t => by simp [MulAut.conj_apply]⟩
  have hidx : P.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨swapAut L, fun b => ?_⟩
    by_cases hb : b ∈ P
    · refine Or.inr ⟨hb, fun hbs => ?_⟩
      obtain ⟨s, hs⟩ := hS.nontriv
      have h1 : (b (1, s)).2 = 1 := by simpa [swapAut] using hbs.1 s
      have h3 : b (1, s) = b 1 := by
        rw [map_one]
        exact Prod.ext (hb.2 s) h1
      exact hs (by simpa using congrArg Prod.snd (b.injective h3))
    · refine Or.inl ⟨?_, hb⟩
      rcases hS.fst_or b with h | h
      · exact absurd ⟨h, hS.snd_of_fst h⟩ hb
      · have h' := hS.snd_of_swap h
        exact ⟨fun s => by simpa [swapAut] using h' s, fun t => by simpa [swapAut] using h t⟩
  haveI hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  set Q : Subgroup (Outer (L × L)) := P.map (QuotientGroup.mk' (inner (L × L))) with hQ
  haveI : Q.Normal := hPn.map _ (QuotientGroup.mk'_surjective _)
  have hcomm : ∀ x y : MulAut L, (x * y)⁻¹ * (y * x) ∈ inner L := by
    intro x y
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hOut _ _
  haveI : Group.IsSolvable Q := by
    refine isSolvable_of_comm ?_
    rintro ⟨_, φ, hφ, rfl⟩ ⟨_, ψ, hψ, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := mem_inner_prod_of_fstHom_sndHom
      ((⟨φ, hφ⟩ * ⟨ψ, hψ⟩ : P)⁻¹ * (⟨ψ, hψ⟩ * ⟨φ, hφ⟩))
      (by rw [map_mul, map_inv, map_mul, map_mul]; exact hcomm _ _)
      (by rw [map_mul, map_inv, map_mul, map_mul]; exact hcomm _ _)
    simpa using h
  haveI : Group.IsSolvable (Outer (L × L) ⧸ Q) := by
    have hcard : Nat.card (Outer (L × L) ⧸ Q) = 2 := by
      rw [← Subgroup.index_eq_card, hQ, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact hIP), hidx]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite (Outer (L × L) ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    haveI : Group.IsNilpotent (Outer (L × L) ⧸ Q) :=
      (IsPGroup.of_card (p := 2) (n := 1) (by rw [hcard]; norm_num)).isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient Q

end OuterProd

section Factors

variable {A : Type} [Group A] {Y : Type} [Group Y] {K : Subgroup Y}

private noncomputable def fstEmb (e : K ≃* A × A) : A →* Y :=
  K.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A A))

private theorem fstEmb_apply (e : K ≃* A × A) (a : A) : fstEmb e a = (e.symm (a, 1) : Y) := rfl

private theorem fstEmb_injective (e : K ≃* A × A) : Function.Injective (fstEmb e) :=
  K.subtype_injective.comp (e.symm.injective.comp fun a b h => congrArg Prod.fst h)

private theorem range_fstEmb_le (e : K ≃* A × A) : (fstEmb e).range ≤ K := by
  rintro _ ⟨a, rfl⟩
  exact (e.symm (a, 1)).2

private theorem fstEmb_conj (e : K ≃* A × A) (k : K) (a : A) :
    (k : Y) * fstEmb e a * (k : Y)⁻¹ = fstEmb e ((e k).1 * a * ((e k).1)⁻¹) := by
  have h1 : k * e.symm (a, 1) * k⁻¹ = e.symm ((e k).1 * a * ((e k).1)⁻¹, 1) := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    ext <;> simp
  rw [fstEmb_apply, fstEmb_apply, ← h1]
  simp

private theorem fstEmb_commute (e : K ≃* A × A) (a b : A) :
    fstEmb e a * fstEmb (e.trans MulEquiv.prodComm) b =
      fstEmb (e.trans MulEquiv.prodComm) b * fstEmb e a := by
  have h2 : (e.trans MulEquiv.prodComm).symm (b, 1) = e.symm (1, b) := rfl
  have h : e.symm (a, 1) * e.symm (1, b) = e.symm (1, b) * e.symm (a, 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  rw [fstEmb_apply, fstEmb_apply, h2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h]

private theorem range_fstEmb_inf_eq_bot (e : K ≃* A × A) :
    (fstEmb e).range ⊓ (fstEmb (e.trans MulEquiv.prodComm)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  have h2 : (e.trans MulEquiv.prodComm).symm (b, 1) = e.symm (1, b) := rfl
  rw [fstEmb_apply, h2, fstEmb_apply] at hb
  have h3 : ((1 : A), b) = (a, 1) := e.symm.injective (Subtype.ext hb)
  have ha : a = 1 := (congrArg Prod.fst h3).symm
  subst ha
  rw [Subgroup.mem_bot, fstEmb_apply, show ((1 : A), (1 : A)) = 1 from rfl, map_one]
  rfl

private theorem isComponentOf_range_fstEmb [IsSimpleGroup A] (hAnab : ∃ a b : A, a * b ≠ b * a)
    [K.Normal] (e : K ≃* A × A) : CFSG.Open.IsComponentOf (fstEmb e).range ⊤ := by
  let eA : A ≃* (fstEmb e).range := MonoidHom.ofInjective (fstEmb_injective e)
  haveI : IsSimpleGroup (fstEmb e).range := eA.symm.isSimpleGroup
  have hnab' : ∃ a b : (fstEmb e).range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAnab
    exact ⟨eA a, eA b, fun h => hab (eA.injective (by rw [map_mul, map_mul, h]))⟩
  haveI : Group.IsPerfect (fstEmb e).range :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top _ hnab'⟩
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Quasisimple.simple_of_perfect _⟩
  refine CFSG.Open.IsSubnormal.step (range_fstEmb_le e) ⟨fun n hn g => ?_⟩
    (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤))
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha⟩ := hn
  refine ⟨(e g).1 * a * ((e g).1)⁻¹, ?_⟩
  rw [← fstEmb_conj e g a, ha]
  simp

private theorem sylow_le_normalizer_range_fstEmb [Finite A] (hS : SimpleCentreless A)
    [Finite Y] [K.Normal] (R : Sylow 5 Y) (e : K ≃* A × A) :
    (R : Subgroup Y) ≤ normalizer ((fstEmb e).range : Set Y) := by
  have hfwd : ∀ r ∈ (R : Subgroup Y), ∀ a : A, r * fstEmb e a * r⁻¹ ∈ (fstEmb e).range := by
    intro r hr a
    set φ : MulAut (A × A) := MulAut.congr e (MulAut.conjNormal r) with hφ
    have hodd : Odd (orderOf φ) := by
      obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
      have hrn : r ^ 5 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have h1 : orderOf φ ∣ 5 ^ n :=
        (orderOf_map_dvd ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) r).trans
          (orderOf_dvd_of_pow_eq_one hrn)
      exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
    have h2 : ((φ (a, 1)).1, (1 : A)) = φ (a, 1) := Prod.ext rfl (hS.presFst_of_odd hodd a).symm
    refine ⟨(φ (a, 1)).1, ?_⟩
    rw [fstEmb_apply, fstEmb_apply, h2, hφ, MulAut.congr_apply]
    simp [MulAut.conjNormal_apply]
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨a, rfl⟩
    exact hfwd r hr a
  · rintro ⟨a, ha⟩
    have h := hfwd r⁻¹ (inv_mem hr) a
    rw [ha] at h
    simpa [mul_assoc] using h

private theorem fst_mem_normalizer_comap (e : K ≃* A × A) {Y₀ : Subgroup Y} (k : K)
    (hk : (k : Y) ∈ Y₀) :
    (e k).1 ∈ normalizer ((Y₀.comap (fstEmb e) : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  simp only [Subgroup.mem_comap]
  rw [← fstEmb_conj e k a]
  constructor
  · intro h
    exact Y₀.mul_mem (Y₀.mul_mem hk h) (Y₀.inv_mem hk)
  · intro h
    have := Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem hk) h) hk
    simpa [mul_assoc] using this

end Factors

section Entry


private theorem isSz32Type_of_mulEquiv' {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {A : Type} [Group A] (e : A ≃* (TauCeti.CFSGIndex.lie d).Group) : IsSz32Type 5 A := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .suzuki 2 := hd
  subst hd'
  exact ⟨rfl, hv, ⟨e⟩⟩

private theorem factor_data {A : Type} [Group A] [Finite A] (hA : IsSz32Type 5 A) {Y : Type}
    [Group Y] [Finite Y] (R : Sylow 5 Y) (ι : A →* Y) (hι : Function.Injective ι)
    (hRι : (R : Subgroup Y) ≤ normalizer (ι.range : Set Y)) :
    ∃ (P : Sylow 5 A) (z : A), z ∈ (P : Subgroup A) ∧ orderOf z = 5 ∧
      (∀ g ∈ (R : Subgroup Y), g * ι z = ι z * g) ∧
      (P : Subgroup A).map ι = (R : Subgroup Y) ⊓ ι.range := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨T⟩ : Nonempty (Sylow 5 A) := inferInstance
  have hAc : Nat.card A = 32537600 := (sz32_data A hA T).card_group
  have hfac : (Nat.card A).factorization 5 = 2 := by
    rw [hAc]
    exact CFSG.RankThree.PartOne.K159.SzAbs.factorization_five
  have hrange : Nat.card ι.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hcard : Nat.card ((R : Subgroup Y) ⊓ ι.range : Subgroup Y) = 5 ^ 2 := by
    rw [card_inf_sylow_of_le_normalizer R hRι, hrange, hfac]
  set P₀ : Subgroup A := (R : Subgroup Y).comap ι with hP₀
  have hmap : P₀.map ι = (R : Subgroup Y) ⊓ ι.range := by
    rw [hP₀, Subgroup.map_comap_eq, inf_comm]
  have hP₀c : Nat.card P₀ = 5 ^ (Nat.card A).factorization 5 := by
    rw [hfac, ← hcard, ← hmap, Subgroup.card_map_of_injective hι]
  let P : Sylow 5 A := Sylow.ofCard P₀ hP₀c
  have hRι' : (R : Subgroup Y) ≤ normalizer (((R : Subgroup Y) ⊓ ι.range : Subgroup Y) : Set Y) :=
    (le_inf Subgroup.le_normalizer hRι).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hne : (R : Subgroup Y) ⊓ ι.range ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨w, hw, hw5, hwR⟩ :=
    exists_orderOf_eq_mem_center_of_le_sylow R.isPGroup' inf_le_left hRι' hne
  obtain ⟨z, hz⟩ := (Subgroup.mem_inf.mp hw).2
  refine ⟨P, z, ?_, ?_, ?_, hmap⟩
  · show z ∈ P₀
    rw [hP₀, Subgroup.mem_comap, hz]
    exact (Subgroup.mem_inf.mp hw).1
  · rw [← orderOf_injective ι hι z, hz, hw5]
  · rw [hz]
    exact hwR

private theorem normalizer_normalizer_sz32 {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    {P : Subgroup A} (D : Sz32Data A P) :
    normalizer ((normalizer (P : Set A) : Subgroup A) : Set A) = normalizer (P : Set A) := by
  rcases D.maximal (Subgroup.le_normalizer (H := normalizer (P : Set A))) with h | h
  · exact h
  · exfalso
    haveI : (normalizer (P : Set A)).Normal := Subgroup.normalizer_eq_top_iff.mp h
    have h100 := D.card_normalizer
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalizer (P : Set A)) with h1 | h1
    · rw [h1, Subgroup.card_bot] at h100
      norm_num at h100
    · rw [h1, Subgroup.card_top, D.card_group] at h100
      norm_num at h100

private theorem szSq_inf_isSolvable {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hA : IsSz32Type 5 A) (hAnab : ∃ a b : A, a * b ≠ b * a) {Y : Type} [Group Y] [Finite Y]
    {K Y₀ E : Subgroup Y} [K.Normal] (R : Sylow 5 Y) (e : K ≃* A × A)
    (hcomp : ∀ L : Subgroup Y, CFSG.Open.IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) (hER : E ≤ R)
    (hE : CFSG.Open.IsElemAbelian 5 E) (hEc : Nat.card E = 5 ^ 2)
    (hcore : (if 3 ≤ CFSG.pRank 5 (R : Subgroup Y) then
      CFSG.Open.GLBWeakCore 5 (R : Subgroup Y) else CFSG.Open.GLBCore 5 1 E) ≤ Y₀) :
    Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hS : SimpleCentreless A := simpleCentreless_of_nonabelian hAnab
  set e' : K ≃* A × A := e.trans MulEquiv.prodComm with he'
  obtain ⟨P₁, z₁, hz₁P, hz₁5, hz₁R, hP₁⟩ := factor_data hA R (fstEmb e) (fstEmb_injective e)
    (sylow_le_normalizer_range_fstEmb hS R e)
  obtain ⟨P₂, z₂, hz₂P, hz₂5, hz₂R, hP₂⟩ := factor_data hA R (fstEmb e') (fstEmb_injective e')
    (sylow_le_normalizer_range_fstEmb hS R e')
  have D₁ : Sz32Data A (P₁ : Subgroup A) := sz32_data A hA P₁
  have D₂ : Sz32Data A (P₂ : Subgroup A) := sz32_data A hA P₂
  have hnz : ∀ (f : K ≃* A × A) (P : Sylow 5 A) (z : A), Sz32Data A (P : Subgroup A) →
      z ∈ (P : Subgroup A) → ∀ a ∈ normalizer ((P : Subgroup A) : Set A),
        fstEmb f a ∈ normalizer ((zpowers (fstEmb f z) : Subgroup Y) : Set Y) := by
    intro f P z D hz a ha
    haveI := D.isCyclic
    have h1 := mem_normalizer_zpowers_of_cyclic_normalizer D.isCyclic hz ha
    have h2 := Subgroup.le_normalizer_map (fstEmb f) (Subgroup.mem_map_of_mem (fstEmb f) h1)
    rwa [MonoidHom.map_zpowers] at h2
  have hK₁ : ¬ (fstEmb e).range ≤ Y₀ :=
    hcomp _ (isComponentOf_range_fstEmb hAnab e) (range_fstEmb_le e)
  have hK₂ : ¬ (fstEmb e').range ≤ Y₀ :=
    hcomp _ (isComponentOf_range_fstEmb hAnab e') (range_fstEmb_le e')
  have hz₁R' : fstEmb e z₁ ∈ (R : Subgroup Y) := by
    have h := Subgroup.mem_map_of_mem (fstEmb e) hz₁P
    rw [hP₁] at h
    exact (Subgroup.mem_inf.mp h).1
  have hz₂R' : fstEmb e' z₂ ∈ (R : Subgroup Y) := by
    have h := Subgroup.mem_map_of_mem (fstEmb e') hz₂P
    rw [hP₂] at h
    exact (Subgroup.mem_inf.mp h).1
  by_cases h3 : 3 ≤ CFSG.pRank 5 (R : Subgroup Y)
  · rw [if_pos h3] at hcore
    have h3' : 3 ≤ CFSG.Open.pRank 5 (R : Subgroup Y) := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    set X : Subgroup Y := zpowers (fstEmb e z₁) ⊔ zpowers (fstEmb e' z₂) with hXdef
    have hXR : X ≤ (R : Subgroup Y) := sup_le (zpowers_le.mpr hz₁R') (zpowers_le.mpr hz₂R')
    have hcomm12 : ∀ a ∈ zpowers (fstEmb e z₁), ∀ b ∈ zpowers (fstEmb e' z₂), a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_left (fstEmb_commute e z₁ z₂) i).zpow_right j).eq
    have hbot12 : zpowers (fstEmb e z₁) ⊓ zpowers (fstEmb e' z₂) = ⊥ := by
      rw [eq_bot_iff, ← range_fstEmb_inf_eq_bot e]
      exact inf_le_inf (zpowers_le.mpr ⟨z₁, rfl⟩) (zpowers_le.mpr ⟨z₂, rfl⟩)
    have hz₁o : orderOf (fstEmb e z₁) = 5 := by
      rw [orderOf_injective _ (fstEmb_injective e) z₁, hz₁5]
    have hz₂o : orderOf (fstEmb e' z₂) = 5 := by
      rw [orderOf_injective _ (fstEmb_injective e') z₂, hz₂5]
    have h2X : 1 + 1 ≤ CFSG.Open.pRank 5 X :=
      le_openPRank_sup_of_commute (by norm_num)
        (CFSG.Open.isElemAbelian_zpowers (hz₁o ▸ pow_orderOf_eq_one (fstEmb e z₁)))
        (CFSG.Open.isElemAbelian_zpowers (hz₂o ▸ pow_orderOf_eq_one (fstEmb e' z₂)))
        hcomm12 hbot12 (by rw [Nat.card_zpowers, hz₁o, pow_one])
        (by rw [Nat.card_zpowers, hz₂o, pow_one]) le_rfl
    have hRX : (R : Subgroup Y) ≤ centralizer (X : Set Y) := by
      rw [← Subgroup.le_centralizer_iff]
      exact sup_le (zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => hz₁R g hg))
        (zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => hz₂R g hg))
    have h3X : 3 ≤ CFSG.Open.pRank 5 (X ⊔ ((R : Subgroup Y) ⊓ centralizer (X : Set Y))) := by
      rw [inf_eq_left.mpr hRX]
      exact h3'.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_right)
    have hNX : normalizer (X : Set Y) ≤ Y₀ :=
      (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 5 hXR h2X h3X).trans hcore
    have hcent : ∀ g w : Y, g * w = w * g →
        g ∈ normalizer ((zpowers w : Subgroup Y) : Set Y) := by
      intro g w hgw
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hgw j).symm.eq
    have hB₁ : Y₀.comap (fstEmb e) = normalizer ((P₁ : Subgroup A) : Set A) := by
      have hle : normalizer ((P₁ : Subgroup A) : Set A) ≤ Y₀.comap (fstEmb e) := by
        intro a ha
        exact hNX (Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨hnz e P₁ z₁ D₁ hz₁P a ha, hcent _ _ (fstEmb_commute e a z₂)⟩)
      rcases D₁.maximal hle with h | h
      · exact h
      · exfalso
        apply hK₁
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Y₀.comap (fstEmb e) := h ▸ Subgroup.mem_top a
        exact ha
    have hB₂ : Y₀.comap (fstEmb e') = normalizer ((P₂ : Subgroup A) : Set A) := by
      have hle : normalizer ((P₂ : Subgroup A) : Set A) ≤ Y₀.comap (fstEmb e') := by
        intro a ha
        exact hNX (Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨hcent _ _ (fstEmb_commute e z₁ a).symm, hnz e' P₂ z₂ D₂ hz₂P a ha⟩)
      rcases D₂.maximal hle with h | h
      · exact h
      · exfalso
        apply hK₂
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Y₀.comap (fstEmb e') := h ▸ Subgroup.mem_top a
        exact ha
    have hmem : ∀ x : ↥(K ⊓ Y₀), e ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ ∈
        (normalizer ((P₁ : Subgroup A) : Set A)).prod (normalizer ((P₂ : Subgroup A) : Set A)) := by
      intro x
      have hx := (Subgroup.mem_inf.mp x.2).2
      refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
      · have h1 := fst_mem_normalizer_comap e ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ hx
        rwa [hB₁, normalizer_normalizer_sz32 D₁] at h1
      · have h1 := fst_mem_normalizer_comap e' ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ hx
        rwa [hB₂, normalizer_normalizer_sz32 D₂] at h1
    haveI := D₁.isSolvable_normalizer
    haveI := D₂.isSolvable_normalizer
    let φ : ↥(K ⊓ Y₀) →* ↥(normalizer ((P₁ : Subgroup A) : Set A)) ×
        ↥(normalizer ((P₂ : Subgroup A) : Set A)) :=
      (Subgroup.prodEquiv _ _).toMonoidHom.comp
        ((e.toMonoidHom.comp (Subgroup.inclusion inf_le_left)).codRestrict _ hmem)
    refine Group.isSolvable_of_isSolvable_injective (f := φ) fun a b hab => ?_
    have h1 : e.toMonoidHom (Subgroup.inclusion inf_le_left a) =
        e.toMonoidHom (Subgroup.inclusion inf_le_left b) := by
      have := congrArg (Subgroup.prodEquiv _ _).symm hab
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        at this
      exact congrArg Subtype.val this
    exact Subgroup.inclusion_injective inf_le_left (e.injective h1)
  · exfalso
    rw [if_neg h3] at hcore
    have h2 : CFSG.Open.pRank 5 (R : Subgroup Y) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      omega
    have hz₁o : orderOf (fstEmb e z₁) = 5 := by
      rw [orderOf_injective _ (fstEmb_injective e) z₁, hz₁5]
    have hz₁E : fstEmb e z₁ ∈ E :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two
        Nat.prime_five h2 hER hE hEc hz₁R' (hz₁o ▸ pow_orderOf_eq_one _) hz₁R
    refine hK₂ ?_
    rintro _ ⟨b, rfl⟩
    refine hcore (normalizer_zpowers_le_glbCoreOne (by norm_num) hz₁E hz₁o ?_)
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (fstEmb_commute e z₁ b) j).eq

theorem threeFourTwoSzSq_holds : ThreeFourTwoSzSq := by
  intro d hd
  obtain ⟨hAfin, hAs, hAnab, -⟩ := sz32_finite_simple_outer hd (MulEquiv.refl _)
  haveI := hAfin
  haveI := hAs
  have hA : IsSz32Type 5 (TauCeti.CFSGIndex.lie d).Group := isSz32Type_of_mulEquiv' hd
    (MulEquiv.refl _)
  have hZA : center (TauCeti.CFSGIndex.lie d).Group = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot _ hAnab
  have hOutA : ∀ a b : Outer (TauCeti.CFSGIndex.lie d).Group, a * b = b * a := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie d).Group) :=
      isCyclic_of_prime_card (sz32_outer _ hA)
    exact fun a b => (IsCyclic.commutative.is_comm.comm a b)
  refine threeFourTwoNoneAt_of_forall_of_center_eq_bot
    (by rw [Subgroup.center_prod, hZA, Subgroup.bot_prod_bot])
    (isSolvable_outer_prod_self_of_comm hAnab hOutA) ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ hcomp hER hE hEc hcore _ J hJ hne hJp _ _
  haveI := hKn
  obtain ⟨e⟩ := hKX
  have hsolv := szSq_inf_isSolvable hA hAnab R e hcomp hER hE hEc hcore
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ)
  haveI : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJp
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hne
  exact Group.IsPerfect.not_isSolvable J inferInstance

end Entry

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
