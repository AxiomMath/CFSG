module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourInner
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit

theorem isSemisimple_map_of_injective {Q Q' : Type*} [Group Q] [Group Q'] (f : Q →* Q')
    (hf : Function.Injective f) (X : Subgroup Q) (hX : aschbacherThm5IsSemisimple X) :
    aschbacherThm5IsSemisimple (X.map f) := by
  obtain ⟨k, K, hk, hK, hcomm, hgen⟩ := hX
  refine ⟨k, fun l => (K l).map f, hk, fun l => ⟨Subgroup.map_mono (hK l).1,
    Components.quasisimple_of_equiv ((K l).equivMapOfInjective f hf).symm (hK l).2⟩, ?_, ?_⟩
  · rintro l m hlm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, hcomm l m hlm x hx y hy, map_mul]
  · rw [← hgen, Subgroup.map_iSup]

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace FieldHyps

variable {t g : G}

theorem false_of_inner (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {y : Abar i}
    (hy : ∀ x : Abar i, hF.alpha i x = y * x * y⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := hF.alpha i with hαdef
  have hα2 : α ^ 2 = 1 := hF.alpha_sq i
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hpow : ∀ n : ℕ, ∀ x : Abar i, (α ^ n) x = y ^ n * x * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hy, ih, pow_succ]
      group
  have hαb : α ^ b = α := by
    obtain ⟨c, rfl⟩ := hb
    rw [pow_succ, pow_mul, hα2, one_pow, one_mul]
  set y₂ := y ^ b with hy₂
  have hy₂act : ∀ x : Abar i, α x = y₂ * x * y₂⁻¹ := by
    intro x
    rw [← hpow b x, hαb]
  have hy₂2 : IsPGroup 2 (Subgroup.zpowers y₂) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    refine ⟨a, ?_⟩
    rw [hy₂, orderOf_pow' y (by obtain ⟨c, rfl⟩ := hb; omega), hab,
      Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ (by obtain ⟨c, rfl⟩ := hb; omega)]
  have hfix : ∀ x : Abar i, α x = x ↔ y₂ * x = x * y₂ := by
    intro x
    rw [hy₂act]
    exact mul_inv_eq_iff_eq_mul
  have hy₂sq : ∀ x : Abar i, y₂ ^ 2 * x = x * y₂ ^ 2 := by
    intro x
    have h1 : (α ^ 2) x = x := by rw [hα2]; rfl
    rw [pow_two, MulAut.mul_apply, hy₂act, hy₂act] at h1
    rw [sq]
    calc y₂ * y₂ * x = (y₂ * (y₂ * x * y₂⁻¹) * y₂⁻¹) * (y₂ * y₂) := by group
      _ = x * (y₂ * y₂) := by rw [h1]
  have huniq := fun {s u : Abar i} (hs : orderOf s = 2) (hu : orderOf u = 2)
      (hsu : s * u = u * s) (hfs : α s = s) (hfu : α u = u) =>
    hF.fixed_involution_eq hin hC hii' hs hu hsu hfs hfu
  have hrank1 : ∀ E : Subgroup (Abar i), E ≤ Subgroup.centralizer ({y₂} : Set (Abar i)) →
      IsElemAbelian 2 E → 2 ≤ CFSG.Open.pRank 2 E → False := by
    intro E hEC hE hE2
    obtain ⟨s, hsE, u, huE, hs, hu, hsu⟩ := exists_two_involutions hE2
    have hcomm : s * u = u * s := by
      have := hE.1
      exact congrArg Subtype.val (mul_comm' (⟨s, hsE⟩ : E) ⟨u, huE⟩)
    exact hsu (huniq hs hu hcomm ((hfix s).mpr (Subgroup.mem_centralizer_singleton_iff.mp
      (hEC hsE)).symm) ((hfix u).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hEC huE)).symm))
  have hXrank : 2 ≤ CFSG.Open.pRank 2 (Abar i) :=
    (hF.two_le_pRank hin hC i).trans (pRank_preimage_le _)
  have hy₂nc : ∃ x ∈ Abar i, (y₂ : D ⧸ aschbacherThm5OddCore D) * x ≠ x * y₂ := by
    by_contra hcen
    push Not at hcen
    obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 2) (H := (⊤ : Subgroup (Abar i))) (k := 2) (hF.two_le_pRank_top hin hC i)
    apply hrank1 E (fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (hcen x x.2).symm)) hE
    exact CFSG.SectionRank.le_pRank one_lt_two le_rfl hE hcard
  have hR : CFSG.Open.pRank 2 (Abar i ⊓ Subgroup.centralizer
      ({(y₂ : D ⧸ aschbacherThm5OddCore D)} : Set (D ⧸ aschbacherThm5OddCore D))) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 2) (k := 2) hcon
    set E' := E.subgroupOf (Abar i)
    have hE'C : E' ≤ Subgroup.centralizer ({y₂} : Set (Abar i)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hEX hx).2)
    have hE' : IsElemAbelian 2 E' := by
      have hc := hE.1
      refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun x hx => Subtype.ext (hE.2 _ hx)⟩
      have := congrArg Subtype.val (mul_comm' (⟨(u : Abar i), u.2⟩ : E) ⟨(v : Abar i), v.2⟩)
      exact Subtype.ext this
    apply hrank1 E' hE'C hE'
    refine CFSG.SectionRank.le_pRank one_lt_two le_rfl hE' ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEX.trans inf_le_left)).toEquiv, hcard]
  have hy₂2' : IsPGroup 2 (Subgroup.zpowers (y₂ : D ⧸ aschbacherThm5OddCore D)) := by
    have := hy₂2.map (Abar i).subtype
    rwa [MonoidHom.map_zpowers] at this
  obtain ⟨P, hPcyc, hPcard⟩ := inner_case_cyclic_four (Abar i) (hC.hyp.hsemisimple i) hXrank hnd
    y₂.2 hy₂2' (fun x hx => congrArg Subtype.val (hy₂sq ⟨x, hx⟩)) hy₂nc hR
  set ι := quotientEmbedding D
  have hι := quotientEmbedding_injective D
  set t' : Subgroup.normalizer (D : Set G) := ⟨t, hF.mem⟩
  have hS : (Abar i ⊓ Subgroup.centralizer
      ({(y₂ : D ⧸ aschbacherThm5OddCore D)} : Set (D ⧸ aschbacherThm5OddCore D))).map ι =
      (Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D)) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨⟨x, hxX, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := quotientEmbedding_onQuotient (D := D) t' x
      have hαx : α ⟨x, hxX⟩ = ⟨x, hxX⟩ := (hfix ⟨x, hxX⟩).mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm)
      have h2 : onQuotient D t' x = x := congrArg Subtype.val hαx
      rw [h2] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
    · intro z hz
      obtain ⟨⟨x, hxX, rfl⟩, hzc⟩ := Subgroup.mem_inf.mp hz
      refine ⟨x, Subgroup.mem_inf.mpr ⟨hxX, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hzc ⊢
      have h1 := quotientEmbedding_onQuotient (D := D) t' x
      rw [← hzc, mul_inv_cancel_right] at h1
      have h2 : onQuotient D t' x = x := hι h1
      have hαx : α ⟨x, hxX⟩ = ⟨x, hxX⟩ := Subtype.ext h2
      exact congrArg Subtype.val ((hfix ⟨x, hxX⟩).mp hαx).symm
  let e := (Subgroup.equivMapOfInjective (Abar i ⊓ Subgroup.centralizer
      ({(y₂ : D ⧸ aschbacherThm5OddCore D)} : Set (D ⧸ aschbacherThm5OddCore D)))
      ι hι).trans (MulEquiv.subgroupCongr hS)
  have hsemi : aschbacherThm5IsSemisimple ((Abar i).map ι) :=
    isSemisimple_map_of_injective ι hι (Abar i) (hC.hyp.hsemisimple i)
  have htN : toBar D t' ∈
      Subgroup.normalizer (((Abar i).map ι : Subgroup (Bar D)) : Set (Bar D)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, hxX, rfl⟩, rfl⟩
      refine ⟨onQuotient D t' x, ?_, ?_⟩
      · have := hF.map_onQuotient i
        rw [← this]
        exact ⟨x, hxX, rfl⟩
      · rw [quotientEmbedding_onQuotient]
        rfl
    · intro z hz
      have hz' : z ∈ ((Abar i).map ι).map (MulAut.conj (toBar D t')).toMonoidHom := by
        obtain ⟨x, hxX, rfl⟩ := hz
        have hmem : onQuotient D t' (onQuotient D t' x) = x :=
          onQuotient_involutive (h := t') (by rw [← hF.two]; exact pow_orderOf_eq_one t) x
        refine ⟨ι (onQuotient D t' x), ⟨onQuotient D t' x, ?_, rfl⟩, ?_⟩
        · have := hF.map_onQuotient i
          rw [← this]
          exact ⟨x, hxX, rfl⟩
        · change toBar D t' * ι (onQuotient D t' x) * (toBar D t')⁻¹ = ι x
          rw [← quotientEmbedding_onQuotient, hmem]
      exact hz'
  have ht2 : toBar D t' ^ 2 = 1 := by
    rw [← map_pow]
    have : t' ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hF.two]; exact pow_orderOf_eq_one t)
    rw [this, map_one]
  have hP3 : ∃ R : Sylow 2 ↥((Abar i).map ι ⊓ Subgroup.centralizer ({toBar D t'} : Set (Bar D))),
      IsCyclic (R : Subgroup ↥((Abar i).map ι ⊓
        Subgroup.centralizer ({toBar D t'} : Set (Bar D)))) ∧ Nat.card R = 4 := by
    refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_⟩
    · change IsCyclic ((P : Subgroup _).map e.toMonoidHom)
      have := hPcyc
      exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap (P : Subgroup _))
        (e.toMonoidHom.subgroupMap_surjective _)
    · change Nat.card ((P : Subgroup _).map e.toMonoidHom) = 4
      rw [Subgroup.card_map_of_injective e.injective]
      exact hPcard
  have h37 := AschbacherKnownGroup.lemma_3_7 hin.knownGroups (Bar D) ((Abar i).map ι)
    (toBar D t') hsemi htN ht2 hP3
  have hrankmap := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two ι hι (Abar i)
  omega

theorem false_of_centralizes_inv_mul (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {a : G}
    (ha : a ∈ aschbacherThm5Preimage D (Abar i))
    (hat : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i))
      (a⁻¹ * t)) : False := by
  set d : D := ⟨a, preimage_le D (Abar i) ha⟩
  have hdA : QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈ Abar i :=
    (mem_preimage_iff D (Abar i) d).mp ha
  have htcore : t ∈ Subgroup.normalizer (aschbacherThm5Core D : Set G) :=
    normalizer_le_normalizer_core D hF.mem
  apply hF.false_of_inner hin hC hii' hnd (y := ⟨_, hdA⟩)
  rintro ⟨x, hxA⟩
  apply Subtype.ext
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) x
  have hcA : (c : G) ∈ aschbacherThm5Preimage D (Abar i) := (mem_preimage_iff D (Abar i) c).mpr hxA
  rw [hF.alpha_apply, onQuotient_mk]
  show QuotientGroup.mk' _ (onD D ⟨t, hF.mem⟩ c) =
    QuotientGroup.mk' _ d * QuotientGroup.mk' _ c * (QuotientGroup.mk' _ d)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, ← mem_core_iff]
  have hu := hat c hcA
  have htu := (Subgroup.mem_normalizer_iff.mp htcore _).mp hu
  have h1 := (aschbacherThm5Core D).inv_mem htu
  convert h1 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, onD_apply, show ((d : D) : G) = a from rfl]
  group

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
