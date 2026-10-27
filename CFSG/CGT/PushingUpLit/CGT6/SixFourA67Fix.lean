module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourMod
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} {T : Sylow 2 G}

omit [Finite G] in
theorem inf_centralizer_jIn_eq_of_le {A : Subgroup G}
    (hAJ : A ≤ jIn (T : Subgroup G)) (hJA : jIn (T : Subgroup G) ≤ A ⊔ R) :
    omegaOneCenterIn R ⊓ Subgroup.centralizer (jIn (T : Subgroup G) : Set G) =
      omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAJ))
  · intro v hv
    obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
    have hAR : A ⊔ R ≤ Subgroup.centralizer ({v} : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (Subgroup.mem_centralizer_iff.mp hvA a ha).symm
      · intro r hr
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact ((mem_omegaOneCenterIn_iff.mp hvV).2.1 r hr).symm
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have := Subgroup.mem_centralizer_iff.mp (hAR (hJA hj)) v (Set.mem_singleton v)
    exact this.symm

namespace EightCtx

theorem vAct_injective (h : EightCtx Y T R) [R.Normal] : Function.Injective h.vAct := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ Subgroup.centralizer (omegaOneCenterIn R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : h.vAct (QuotientGroup.mk g) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hq]; rfl
    have h2 := congrArg Subtype.val h1
    rw [h.vAct_mk] at h2
    calc v * g = (g * v * g⁻¹) * g := by rw [h2]
      _ = g * v := by group
  rw [h.hC] at hg
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem jBar_fix (h : EightCtx Y T R) [R.Normal] {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) :
    (∀ a ∈ jBar R T, a ≠ 1 → autFixSub (h.vAct a) = h.cV (jBar R T)) ∧
      ∀ a ∈ jBar R T, ∀ v : ↥(omegaOneCenterIn R), h.vAct a v * v⁻¹ ∈ h.cV (jBar R T) := by
  classical
  obtain ⟨A, hA, hnot, hJA, -⟩ := eight_sl_nine h hn hnat
  obtain ⟨𝔘, -, hmain⟩ := eight_sl_main h hn hnat
  obtain ⟨-, -, -, -, hcent, hquad⟩ := hmain A hA hnot
  have hAJ : A ≤ jIn (T : Subgroup G) := by
    rw [jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hCV := inf_centralizer_jIn_eq_of_le (R := R) (T := T) hAJ hJA
  have hfixJ : ∀ w : ↥(omegaOneCenterIn R), (w : G) ∈ Subgroup.centralizer (A : Set G) →
      w ∈ h.cV (jBar R T) := by
    intro w hw
    have hwJ : (w : G) ∈ Subgroup.centralizer (jIn (T : Subgroup G) : Set G) := by
      have : (w : G) ∈ omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) := ⟨w.2, hw⟩
      rw [← hCV] at this
      exact this.2
    rw [h.mem_cV]
    rintro _ ⟨j, hj, rfl⟩
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, h.vAct_mk]
    have := Subgroup.mem_centralizer_iff.mp hwJ j hj
    show j * (w : G) * j⁻¹ = w
    rw [this]
    group
  have hrep : ∀ a ∈ jBar R T, ∃ a₀ ∈ A, QuotientGroup.mk' R a₀ = a := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨a₀, ha₀, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hj)
    have hr1 : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    exact ⟨a₀, ha₀, by rw [map_mul, hr1, mul_one]⟩
  refine ⟨fun a ha ha1 => ?_, fun a ha v => ?_⟩
  · obtain ⟨a₀, ha₀, rfl⟩ := hrep a ha
    have ha₀R : a₀ ∉ R := fun hr => ha1 ((QuotientGroup.eq_one_iff a₀).mpr hr)
    ext v
    rw [mem_autFixSub]
    constructor
    · intro hv
      have hv' : (v : G) ∈ omegaOneCenterIn R ⊓ Subgroup.centralizer ({a₀} : Set G) := by
        refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have h2 := congrArg Subtype.val hv
        rw [QuotientGroup.mk'_apply, h.vAct_mk] at h2
        calc a₀ * (v : G) = (a₀ * v * a₀⁻¹) * a₀ := by group
          _ = v * a₀ := by rw [h2]
      rw [hcent a₀ ha₀ ha₀R] at hv'
      exact hfixJ v hv'.2
    · intro hv
      exact (h.mem_cV.mp hv) _ ha
  · obtain ⟨a₀, ha₀, rfl⟩ := hrep a ha
    have hw : ((h.vAct (QuotientGroup.mk' R a₀) v * v⁻¹ : ↥(omegaOneCenterIn R)) : G) =
        ⁅a₀, (v : G)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, QuotientGroup.mk'_apply, h.vAct_mk,
        commutatorElement_def]
    apply hfixJ
    rw [hw]
    exact hquad a₀ ha₀ v v.2

end EightCtx

section L2Four

open CFSG.CGT.Timmesfeld75

theorem isSimpleGroup_of_sl2_four {M : Type*} [Group M] (e : M ≃* SL(2, GaloisField 2 2)) :
    IsSimpleGroup M := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : IsSimpleGroup PSL(2, GaloisField 2 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans pslMulEquivSL.symm).isSimpleGroup

theorem card_sl2_four {M : Type*} [Group M] (e : M ≃* SL(2, GaloisField 2 2)) :
    Nat.card M = 60 := by
  rw [Nat.card_congr e.toEquiv, card_SL2_eq, GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem l2_four_facts {Γ : Type} [Group Γ] {J Y₀ : Subgroup Γ} (hJY : J ≤ Y₀) (hJ4 : Nat.card J = 4)
    (e : Y₀ ≃* SL(2, GaloisField 2 2)) :
    (∃ g ∈ Y₀, J ⊔ J.map (MulAut.conj g).toMonoidHom = Y₀) ∧
      (∀ a ∈ J, a ≠ 1 → ∀ g ∈ Y₀, g * a = a * g → g ∈ J) := by
  classical
  have h60 : Nat.card Y₀ = 60 := card_sl2_four e
  have hfin : Finite Y₀ := Nat.finite_of_card_ne_zero (by rw [h60]; norm_num)
  set S : Subgroup Y₀ := J.subgroupOf Y₀ with hS
  have hScard : Nat.card S = 4 := by
    rw [hS, ← hJ4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv
  have hSp : IsPGroup 2 S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 2) (by rw [hScard]; norm_num)
  have hidx : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hScard, h60] at h1
    have : S.index = 15 := by omega
    rw [this]
    norm_num
  have hpair : IsL2Pair ↥Y₀ S (2 ^ 2) :=
    IsL2Pair.of_psl_isPGroup (f := 2) (by norm_num) ⟨e.trans pslMulEquivSL.symm⟩ hSp hidx
  refine ⟨?_, ?_⟩
  ·
    have hN : Nat.card (Subgroup.normalizer (S : Set Y₀)) = 2 ^ 2 * (2 ^ 2 - 1) := hpair.card_normalizer
    have hex : ∃ g : Y₀, g ∉ Subgroup.normalizer (S : Set Y₀) := by
      by_contra hall
      push Not at hall
      have : Subgroup.normalizer (S : Set Y₀) = ⊤ := eq_top_iff.mpr fun g _ => hall g
      rw [this, Subgroup.card_top, h60] at hN
      omega
    obtain ⟨g, hg⟩ := hex
    have hne : Timmesfeld75.conjSubgroup 1 S ≠ Timmesfeld75.conjSubgroup g S := by
      intro hcon
      rw [Timmesfeld75.conjSubgroup_eq_conjSubgroup_iff, inv_one, one_mul] at hcon
      exact hg hcon
    have htop := hpair.sup_conj_eq_top hne
    refine ⟨(g : Γ), g.2, ?_⟩
    have h1 := congrArg (Subgroup.map Y₀.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
    have hS' : S.map Y₀.subtype = J := by
      rw [hS, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJY]
    have h2 : (Timmesfeld75.conjSubgroup 1 S).map Y₀.subtype = J := by
      rw [Timmesfeld75.conjSubgroup_one, hS']
    have h3 : (Timmesfeld75.conjSubgroup g S).map Y₀.subtype = J.map (MulAut.conj (g : Γ)).toMonoidHom := by
      unfold Timmesfeld75.conjSubgroup
      rw [Subgroup.map_map, ← hS', Subgroup.map_map]
      congr 1
    rw [h2, h3] at h1
    exact h1
  · intro a haJ ha1 g hgY hgc
    have haY : a ∈ Y₀ := hJY haJ
    have hs : (⟨a, haY⟩ : Y₀) ∈ S := haJ
    have hs1 : (⟨a, haY⟩ : Y₀) ≠ 1 := fun hh => ha1 (congrArg Subtype.val hh)
    have hcen := hpair.centralizer_eq hs hs1
    have hg : (⟨g, hgY⟩ : Y₀) ∈ Subgroup.centralizer ({(⟨a, haY⟩ : Y₀)} : Set Y₀) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hgc
    rw [hcen] at hg
    exact hg

end L2Four

end CFSG.CGT.PushingUpLit.CGT6
