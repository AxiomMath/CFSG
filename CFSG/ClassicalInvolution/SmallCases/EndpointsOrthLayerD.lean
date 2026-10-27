module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDNodes
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair spinMinusModel minusLongBlock
  four_le_card_shortField')
open CFSG.ClassicalInvolution.ModelFacts.OddCover (NoCover)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

section Bridge

@[expose] def SU4SpinMinus (p f : ℕ) [Fact p.Prime] {b c : GaloisField p f}
    (_hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) : Prop :=
  ∃ e : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) ≃*
      Su (GaloisField p (2 * f)) p f 4,
    (minusLongBlock b c).range.map e.toMonoidHom ∈
      longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4)

theorem twistedB2BlockPair_perfect {F : Type} [Field F] [Finite F] {b c : F}
    {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    {W U V : Subgroup X} (h : TwistedB2BlockPair hirr W U V) : U ≤ ⁅U, U⁆ ∧ V ≤ ⁅V, V⁆ := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  obtain ⟨θ, -, -, -, hU, hV⟩ := h
  refine ⟨?_, ?_⟩
  · have := range_perfect_of_sl2 h4 (θ.comp (spinMinusModel hirr).lb)
    rwa [MonoidHom.range_comp, hU] at this
  · have := range_perfect_of_sl2 (four_le_card_shortField' (b := b) (c := c))
      (θ.comp (spinMinusModel hirr).sb)
    rwa [MonoidHom.range_comp, hV] at this

theorem injective_minusLongBlock {F : Type} [Field F] [Finite F] {b c : F}
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) : Function.Injective (spinMinusModel hirr).lb := by
  have := finite_shortField (b := b) (c := c)
  obtain ⟨θ, -, hθ, -, -⟩ := exists_twistedB2_minusDatum_inj (n := 4) hirr h2 (le_refl 4)
    (i := (⟨1, by norm_num⟩ : Fin (4 - 1))) (j := (⟨2, by norm_num⟩ : Fin (4 - 1))) rfl rfl
  exact Function.Injective.of_comp hθ

theorem SU4SpinMinus.exists_pair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {b c : GaloisField p f}
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hb : SU4SpinMinus p f hirr)
    (hg6 : SpinMinus6Generated hirr) {X : Type}
    [Group X] (ψ : Su (GaloisField p (2 * f)) p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4))
    {R : Subgroup (Su (GaloisField p (2 * f)) p f 4)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4)) :
    ∃ (S : Subgroup (Su (GaloisField p (2 * f)) p f 4)) (W : Subgroup X),
      TwistedB2BlockPair hirr W (R.map ψ) (S.map ψ) ∧ R ⊔ S = ⊤ := by
  have := fact_shortField hirr
  have hF := typeU_card_field (p := p) (f := f) hq
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨e, he⟩ := hb
  obtain ⟨i, hi⟩ := hR
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp ⟨i, hi⟩
  obtain ⟨g₂, hg₂⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp he
  let h : Su (GaloisField p (2 * f)) p f 4 := g₁ * g₂⁻¹
  let θ : spinGroup (Spin.quadMinus 3 (GaloisField p f) b c) →* Su (GaloisField p (2 * f)) p f 4 :=
    (MulAut.conj h).toMonoidHom.comp e.toMonoidHom
  have hθinj : Function.Injective θ := (MulAut.conj h).injective.comp e.injective
  have hh : h * g₂ = g₁ := by simp [h]
  have hlb : (spinMinusModel hirr).lb.range.map θ = R := by
    have e1 : (spinMinusModel hirr).lb.range.map θ =
        ((minusLongBlock b c).range.map e.toMonoidHom).map (MulAut.conj h).toMonoidHom :=
      (Subgroup.map_map _ _ _).symm
    rw [e1, hg₂, hg₁]
    change conjSub h (conjSub g₂ _) = conjSub g₁ _
    rw [← conjSub_mul, hh]
  refine ⟨(spinMinusModel hirr).sb.range.map θ, (ψ.comp θ).range,
    ⟨ψ.comp θ, rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hy1 : θ y ∈ ψ.ker := hy
    have hc := hker hy1
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro w
    apply hθinj
    rw [map_mul, map_mul]
    exact hc (θ w)
  · intro a b hab
    apply injective_minusLongBlock hirr h2
    apply hθinj
    have hab' : ψ (θ ((spinMinusModel hirr).lb a)) = ψ (θ ((spinMinusModel hirr).lb b)) := hab
    have ha : θ ((spinMinusModel hirr).lb a) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
    have hb : θ ((spinMinusModel hirr).lb b) ∈ R := by
      rw [← hlb]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
    have hw : (θ ((spinMinusModel hirr).lb a))⁻¹ * θ ((spinMinusModel hirr).lb b) ∈ R :=
      R.mul_mem (R.inv_mem ha) hb
    have hwk : (θ ((spinMinusModel hirr).lb a))⁻¹ * θ ((spinMinusModel hirr).lb b) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    exact inv_mul_eq_one.mp (Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hF hp2 hq
      (by norm_num : 3 ≤ 4) hi hker _ hw hwk)
  · rw [← Subgroup.map_map, hlb]
  · exact (Subgroup.map_map _ _ _).symm
  · rw [← hlb, ← Subgroup.map_sup, hg6, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr ((MulAut.conj h).surjective.comp e.surjective)

end Bridge

structure SuLayer (p f a : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (x : G) where
  D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)
  card_eq : D.card = a + 1
  i₁ : Fin D.card
  tag_eq : D.tag i₁ = .PSU
  rank_eq : D.rank i₁ = 4
  rest : ∀ i, i ≠ i₁ → D.tag i = .PSL ∧ D.rank i = 2

theorem LocalShapeT.nonempty_suLayer {a : ℕ} (h : LocalShapeT p f a .PSU 4 Ω x) :
    Nonempty (SuLayer p f a Ω x) := by
  obtain ⟨D, hcard, i₁, ht, hr, hrest⟩ := h
  exact ⟨⟨D, hcard, i₁, ht, hr, hrest⟩⟩

namespace SuLayer

variable {a : ℕ} (Λ : SuLayer p f a Ω x)

noncomputable def ψ (hp2 : p ≠ 2) : Su (GaloisField p (2 * f)) p f 4 →* locQuot Ω x :=
  (exists_psu_hom hp2 Λ.D Λ.i₁ Λ.tag_eq (n := 4) Λ.rank_eq (by norm_num)).choose

theorem ψ_spec (hp2 : p ≠ 2) :
    (Λ.ψ hp2).ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) ∧
    (Λ.ψ hp2).range = (Λ.D.hom Λ.i₁).range ∧
    ∀ K : Subgroup (locQuot Ω x), (∃ R ∈ fundamentalSubgroups (Λ.D.tag Λ.i₁)
        (modelUniv (Λ.D.tag Λ.i₁) (Λ.D.rank Λ.i₁) p (Λ.D.exp Λ.i₁) Fact.out).D,
          K = R.map (Λ.D.hom Λ.i₁)) ↔
      ∃ L ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4),
        K = L.map (Λ.ψ hp2) :=
  (exists_psu_hom hp2 Λ.D Λ.i₁ Λ.tag_eq (n := 4) Λ.rank_eq (by norm_num)).choose_spec

theorem exists_longRoot_of_mem [Finite G] (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 4),
      locImg Ω x M = R.map (Λ.ψ hp2) := by
  have hmem : locImg Ω x M ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨M, hM, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := Λ.D.fundamental _ hmem
  by_cases hi : i = Λ.i₁
  · subst hi
    exact (Λ.ψ_spec hp2).2.2 _ |>.mp ⟨R, hR, hMR⟩
  · exfalso
    have h1 : locImg Ω x M ≤ (Λ.D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
    have h2 : ∀ w ∈ locImg Ω x M, w ∈ Subgroup.center (locQuot Ω x) := fun w hw =>
      range_inf_le_center Λ.D hi ⟨h1 hw, hMi hw⟩
    have hc : Commutes (locImg Ω x M) (locImg Ω x M) := fun u hu v _ =>
      (Subgroup.mem_center_iff.mp (h2 u hu) v).symm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact not_commutes_self_of_isClassicalMember hz
      (commutes_of_commutes_locImg_perfect hP1 (le_centralizingLayer hM) (le_centralizingLayer hM)
        (commutator_eq_of_isClassicalMember hz).ge hc)

theorem exists_other_of_self [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (hK : K ∈ Ω) (hz : IsClassicalMember p f K x) :
    ∃ j, j ≠ Λ.i₁ ∧ locImg Ω x K ≤ (Λ.D.hom j).range := by
  have hF := typeU_card_field (p := p) (f := f) hq
  have hn3 : 3 ≤ 4 := by norm_num
  have hKx : K ∈ centralizingMembers Ω {x} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω x K ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := Λ.D.fundamental _ hmem
  by_cases hi : i = Λ.i₁
  · exfalso
    subst hi
    obtain ⟨L, hL, hLK⟩ := ((Λ.ψ_spec hp2).2.2 _).mp ⟨R, hR, hKR⟩
    let zY : ↥(locLayer Ω x) := ⟨x, le_centralizingLayer hKx hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY ∈
        locImg Ω x K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hLK] at hzK
    obtain ⟨r, hrR, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω x,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {x} w'.2)
    have hrc : r ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
      have := isPerfect_su (p := p) (f := f) hq hn3
      refine mem_center_of_comm_mem_center fun s => (Λ.ψ_spec hp2).1 ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (Λ.ψ hp2 s), mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨i', hi'⟩ := hL
    have hr1 : r = 1 := by
      have hker : (QuotientGroup.mk' (Subgroup.center
          (Su (GaloisField p (2 * f)) p f 4))).ker ≤
          Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
        rw [QuotientGroup.ker_mk']
      exact Transfer.eq_one_of_mem_ker_of_isLongRootSU2 hF hp2 hq hn3 hi' hker r hrR
        (by rw [QuotientGroup.ker_mk']; exact hrc)
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω x)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)
  · exact ⟨i, hi, hKR ▸ Subgroup.map_le_range _ _⟩

@[expose] def IsShortNode {b c : GaloisField p f}
    (hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) (M Us : Subgroup G) : Prop :=
  Us ≤ locLayer Ω x ∧ ⁅Us, Us⁆ = Us ∧ locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range ∧
    (∃ W, TwistedB2BlockPair hirr W M Us) ∧
    (∀ N ∈ centralizingMembers Ω {x}, ∀ j, j ≠ Λ.i₁ → locImg Ω x N ≤ (Λ.D.hom j).range →
      Commutes N Us) ∧
    locImg Ω x M ⊔ locImg Ω x Us = (Λ.D.hom Λ.i₁).range

theorem exists_shortNode [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {b c : GaloisField p f}
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (hb : SU4SpinMinus p f hirr)
    (hg6 : SpinMinus6Generated hirr)
    (hcov : NoCover.{0} Odd (spinGroup (Spin.quadMinus 3 (GaloisField p f) b c)))
    {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {x})
    (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode hirr M Us := by
  have := fact_shortField hirr
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
  obtain ⟨R, hR, hMR⟩ := Λ.exists_longRoot_of_mem hp2 hΩ hP1 hM hMi
  obtain ⟨S, W, hpairX, hRS⟩ := hb.exists_pair hp2 hq hg6 (Λ.ψ hp2) (Λ.ψ_spec hp2).1 hR
  have hSperf : S.map (Λ.ψ hp2) ≤ ⁅S.map (Λ.ψ hp2), S.map (Λ.ψ hp2)⁆ :=
    (twistedB2BlockPair_perfect h4 hpairX).2
  obtain ⟨A, hAperf, hAmap⟩ := exists_perfect_lift hP1 hSperf
  set Yl : Subgroup G := locLayer Ω x with hYl
  let Us : Subgroup G := A.map Yl.subtype
  have hUsimg : locImg Ω x Us = S.map (Λ.ψ hp2) := by
    show locImg Ω x (A.map Yl.subtype) = _
    rw [locImg_map_subtype, hAmap]
  have hUsY : Us ≤ Yl := Subgroup.map_subtype_le _
  have hUsperf : Us ≤ ⁅Us, Us⁆ := by
    show A.map Yl.subtype ≤ ⁅A.map Yl.subtype, A.map Yl.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAperf
  have hMY : M ≤ Yl := le_centralizingLayer hM
  have hMperf : M ≤ ⁅M, M⁆ := by
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact (commutator_eq_of_isClassicalMember hz).ge
  have hUsrange : locImg Ω x Us ≤ (Λ.D.hom Λ.i₁).range := by
    rw [hUsimg, ← (Λ.ψ_spec hp2).2.1]
    exact Subgroup.map_le_range _ _
  have hW : TwistedB2BlockPair hirr W (locImg Ω x M) (locImg Ω x Us) := by
    rw [hMR, hUsimg]
    exact hpairX
  refine ⟨Us, hUsY, le_antisymm (commutator_self_le _) hUsperf, hUsrange,
    twistedB2BlockPair_of_locImg_perfect hirr hg6 hcov h4 hP1 hMY hUsY hMperf hUsperf hW, ?_, ?_⟩
  · intro N hN j hj hNj
    have hNY : N ≤ Yl := le_centralizingLayer hN
    have hNperf : N ≤ ⁅N, N⁆ := by
      obtain ⟨z, hz⟩ := hΩ.classical N hN.1
      exact (commutator_eq_of_isClassicalMember hz).ge
    refine commutes_of_commutes_locImg_perfect hP1 hNY hUsY hNperf ?_
    intro u hu w hw
    exact range_commute_of_ne Λ.D hj u (hNj hu) w (hUsrange hw)
  · rw [hMR, hUsimg, ← Subgroup.map_sup, hRS, Subgroup.map_top, (Λ.ψ_spec hp2).2.1]

theorem range_eq_top (ha : a = 0) : (Λ.D.hom Λ.i₁).range = ⊤ := by
  have hall : ∀ i : Fin Λ.D.card, i = Λ.i₁ := fun i => Fin.ext (by
    have h1 := i.2
    have h2 := Λ.i₁.2
    have hc : Λ.D.card = 1 := by rw [Λ.card_eq, ha]
    omega)
  rw [eq_top_iff, ← Λ.D.generate]
  exact iSup_le fun i => by rw [hall i]

theorem layer_le_sup [Finite G] {b c : GaloisField p f}
    {hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0} (ha : a = 0) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x})
    {M Us : Subgroup G} (hsn : Λ.IsShortNode hirr M Us) :
    locLayer Ω x ≤ M ⊔ Us := by
  set Y : Subgroup G := locLayer Ω x with hY
  have hperfY : Y ≤ ⁅Y, Y⁆ := iSup₂_le fun L hL => by
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    exact (commutator_eq_of_isClassicalMember hz).ge.trans
      (Subgroup.commutator_mono (le_centralizingLayer hL) (le_centralizingLayer hL))
  have hperfT : (⊤ : Subgroup ↥Y) ≤ ⁅(⊤ : Subgroup ↥Y), ⊤⁆ := by
    have := perfect_subgroupOf (le_refl Y) hperfY
    rwa [Subgroup.subgroupOf_self] at this
  set O := classicalInvolutionOddCore ↥Y with hO
  set N' : Subgroup ↥Y := M.subgroupOf Y ⊔ Us.subgroupOf Y with hN'
  have hTop : (⊤ : Subgroup ↥Y) ≤ N' ⊔ O := by
    intro y _
    have hrange : QuotientGroup.mk' O y ∈ locImg Ω x M ⊔ locImg Ω x Us := by
      rw [hsn.2.2.2.2.2, Λ.range_eq_top ha]
      trivial
    have himg : locImg Ω x M ⊔ locImg Ω x Us = N'.map (QuotientGroup.mk' O) := by
      unfold locImg
      rw [Subgroup.map_sup]
    rw [himg] at hrange
    obtain ⟨w, hw, hwy⟩ := hrange
    have hmem : w⁻¹ * y ∈ O := QuotientGroup.eq.mp hwy
    have hyw : y = w * (w⁻¹ * y) := by group
    rw [hyw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hmem)
  have hTop' := le_of_perfect_of_le_sup_center hP1 hperfT hTop
  intro g hg
  have h1 : (⟨g, hg⟩ : ↥Y) ∈ N' := hTop' (Subgroup.mem_top _)
  have h2 : N' ≤ (M ⊔ Us).subgroupOf Y := sup_le
    (fun u hu => Subgroup.mem_subgroupOf.mpr
      ((show M ≤ M ⊔ Us from le_sup_left) (Subgroup.mem_subgroupOf.mp hu)))
    (fun u hu => Subgroup.mem_subgroupOf.mpr
      ((show Us ≤ M ⊔ Us from le_sup_right) (Subgroup.mem_subgroupOf.mp hu)))
  exact Subgroup.mem_subgroupOf.mp (h2 h1)

end SuLayer

end CFSG.ClassicalInvolution.RouteD
