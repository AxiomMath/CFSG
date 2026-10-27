module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBarTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveExclusion

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

open BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace Factor

theorem overlap_alt_one (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G))) (hT1 : T ≠ ⊥) :
    IsCyclic T ∧ ∃ R : Subgroup (Bar D),
      IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))) ∧
        (AschbacherTheorem3.IsQuaternionTwoGroup R ∨ AschbacherTheorem3.IsDihedralTwoGroup R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hAb : A ≤ centralizing D (Abar b) := factor_le_centralizing hC.hyp.hcomm (Ne.symm hab)
  have hTH : T ≤ Subgroup.normalizer (D : Set G) := hT.le.trans inf_le_right
  obtain ⟨S, hS, -, -, -, -, halt⟩ := overlap_alternatives hC h3 le_rfl hAb hHa hg hT hT1
  rcases halt with ⟨hTc, hSQ, -⟩ | halt
  · have hSbar : IsSylowOf 2 (bar D S) (bar D A ⊔ bar D T) := by
      rw [← bar_sup hAH hTH]
      exact isSylowOf_bar hS (sup_le hAH hTH)
    have hR : IsSylowOf 2 (bar D S ⊓ bar D A) (bar D A) :=
      hSbar.inf_of_le_normalizer le_sup_left
        (sup_le Subgroup.le_normalizer (bar_le_normalizer (hTH.trans hHa) hAH))
    refine ⟨(isCyclic_bar_iff hT.isPGroup hTH).mp hTc, bar D S ⊓ bar D A, hR, ?_⟩
    rcases hSQ with hc | hq | hd
    · exact absurd hc (sylow_not_cyclic_of_perfect (bar_factor_perfect hC.hyp a)
        (bar_factor_ne_bot hC.hyp a) hR)
    · exact Or.inl hq
    · exact Or.inr hd
  · exact absurd halt (not_altThree hC h3 hab hHa haq hg hT hT1)

theorem factor_type (hC : Counterexample G D r Abar) (h3 : AschbacherTheorem3.Theorem3Statement)
    (hin : SectionSixInputs) {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a)))) :
    ∃ R : Subgroup (Bar D), IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))) ∧
      (AschbacherTheorem3.IsQuaternionTwoGroup R ∨ AschbacherTheorem3.IsDihedralTwoGroup R) := by
  have hAb := factor_le_centralizing hC.hyp.hcomm (Ne.symm hab)
  obtain ⟨g, hg, T, hT, hT1⟩ := exists_nontrivial_overlap hC hin le_rfl hAb hHa
  exact (overlap_alt_one hC h3 hab hHa haq hg hT hT1).2

omit [Finite G] in
theorem isCyclic_bot : IsCyclic (⊥ : Subgroup G) := by
  have : Subsingleton (⊥ : Subgroup G) :=
    ⟨fun x y => Subtype.ext ((Subgroup.mem_bot.mp x.2).trans (Subgroup.mem_bot.mp y.2).symm)⟩
  exact isCyclic_of_subsingleton

theorem conj_inter_isCyclic (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPA : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G)) : IsCyclic P := by
  obtain ⟨T, hT, hPT⟩ := AschbacherTheorem3.exists_isSylowOf_le hP2 hPA
  have hTc : IsCyclic T := by
    by_cases hT1 : T = ⊥
    · rw [hT1]
      exact isCyclic_bot
    · exact (overlap_alt_one hC h3 hab hHa haq hg hT hT1).1
  exact Strong.isCyclic_of_le hPT hTc

theorem inter_isCyclic (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPA : P ≤ aschbacherThm5Preimage D (Abar a) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g) : IsCyclic P := by
  set H := Subgroup.normalizer (D : Set G)
  have hg' : g⁻¹ ∉ H := fun h => hg (by simpa using H.inv_mem h)
  have hP' : rightConjugate P g⁻¹ ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) g⁻¹ ⊓ H := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹⁻¹).toMonoidHom) hPA
    change rightConjugate P g⁻¹ ≤
      rightConjugate (aschbacherThm5Preimage D (Abar a) ⊓ rightConjugate H g) g⁻¹ at h1
    rwa [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one] at h1
  have hc := conj_inter_isCyclic hC h3 hab hHa haq hg'
    (AschbacherTheorem3.isPGroup_rightConjugate hP2 g⁻¹) hP'
  exact isCyclic_of_equiv (P.equivMapOfInjective _ (MulAut.conj g⁻¹⁻¹).injective).symm hc

theorem pRank_le_one_of_quaternion {Y : Subgroup G} (hYH : Y ≤ Subgroup.normalizer (D : Set G))
    {R : Subgroup (Bar D)} (hR : IsSylowOf 2 R (bar D Y))
    (hRq : AschbacherTheorem3.IsQuaternionTwoGroup R) : CFSG.Open.pRank 2 Y ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) Y
  by_contra hlt
  push Not at hlt
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 Y := Nat.pow_le_pow_right (by norm_num) hlt
  obtain ⟨u, hu, v, hv, hu1, hv1, hvu⟩ := AschbacherTheorem3.exists_two_ne_one h4
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  have hEH : E ≤ Subgroup.normalizer (D : Set G) := hEY.trans hYH
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
    (isPGroup_bar hE2) (bar_mono D hEY)
  set e := barEquiv hE2 hEH
  have hord : ∀ w (hw : w ∈ E), w ≠ 1 →
      orderOf (c⁻¹ * ((e ⟨w, hw⟩ : bar D E) : Bar D) * c) = 2 := by
    intro w hw hw1
    rw [show c⁻¹ * ((e ⟨w, hw⟩ : bar D E) : Bar D) * c =
        MulAut.conj c⁻¹ ((e ⟨w, hw⟩ : bar D E) : Bar D) by simp, MulEquiv.orderOf_eq,
      Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hE.2 w hw) hw1
  have hmem : ∀ w (hw : w ∈ E), c⁻¹ * ((e ⟨w, hw⟩ : bar D E) : Bar D) * c ∈ R := fun w hw =>
    hc (AschbacherTheorem3.conj_mem_rightConjugate (e ⟨w, hw⟩).2 c)
  have heq := quaternion_unique_involution hRq (hmem u hu) (hmem v hv) (hord u hu hu1)
    (hord v hv hv1)
  have h1 : ((e ⟨u, hu⟩ : bar D E) : Bar D) = ((e ⟨v, hv⟩ : bar D E) : Bar D) := by
    simpa using heq
  have h2 : (⟨u, hu⟩ : E) = ⟨v, hv⟩ := e.injective (Subtype.ext h1)
  exact hvu (congrArg Subtype.val h2).symm

theorem exists_central_involution (hyp : Hyp61 G D r Abar) (a : Fin r) {R : Subgroup (Bar D)}
    (hR : IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))))
    (hRq : AschbacherTheorem3.IsQuaternionTwoGroup R) :
    ∃ z ∈ aschbacherThm5Preimage D (Abar a), orderOf z = 2 ∧
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar a)) z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set L := bar D A with hLdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hDA : D ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
      (canonical_preimage_normal D Abar hyp.hcomm hyp.hgen a)
  have hO : CFSG.oddCore L = ⊥ := oddCore_bar_eq_bot (preimage_le D _) hDA
  have hR2 := hR.isPGroup
  have hRL := hR.le
  have hR1 : R ≠ ⊥ := by
    have : Group.IsPerfect L := bar_factor_perfect hyp a
    have : Nontrivial L := L.nontrivial_iff_ne_bot.mpr (bar_factor_ne_bot hyp a)
    exact isSylowOf_ne_bot_of_even hR even_card_of_perfect
  obtain ⟨n, hn, ⟨e⟩⟩ := hRq
  obtain ⟨P', hP'⟩ := hR
  have hquat : Nonempty ((P' : Subgroup L) ≃* QuaternionGroup (2 ^ (n - 2))) :=
    ⟨(((P' : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hP')).trans e⟩
  obtain ⟨t, htR, ht⟩ := exists_orderOf_eq_two hR2 hR1
  have htL : t ∈ L := hRL htR
  have ht'P : (⟨t, htL⟩ : L) ∈ (P' : Subgroup L) := by
    have h1 : t ∈ (P' : Subgroup L).map L.subtype := hP' ▸ htR
    obtain ⟨w, hw, hwt⟩ := h1
    have hw' : w = ⟨t, htL⟩ := Subtype.ext hwt
    rwa [← hw']
  have ht'o : orderOf (⟨t, htL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hBS := CFSG.BrauerSuzuki.brauer_suzuki n hn P' hquat ⟨t, htL⟩ ht'P ht'o
  have htC : t ∈ Subgroup.centralizer (L : Set (Bar D)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcomm := Subgroup.mem_center_iff.mp hBS (QuotientGroup.mk ⟨c, hc⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hO, Subgroup.mem_bot,
      inv_mul_eq_one] at hcomm
    exact congrArg Subtype.val hcomm
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two ht
  obtain ⟨V, hVA, hV2, hVt⟩ := lift_two_subgroup hAH hzp (Subgroup.zpowers_le.mpr htL)
  have htV : t ∈ bar D V := hVt ▸ Subgroup.mem_zpowers t
  obtain ⟨z, hzV, hzt⟩ := (mem_bar_iff D V t).mp htV
  have hz2 : z ^ 2 = 1 := by
    apply toBar_injOn_of_isPGroup hV2 (V.pow_mem hzV 2) V.one_mem
    rw [map_pow, hzt, ← ht, pow_orderOf_eq_one, map_one]
  have hz1 : (z : G) ≠ 1 := by
    intro h
    have hz : z = 1 := Subtype.ext h
    rw [hz, map_one] at hzt
    exact TwoGroups.ne_one_of_orderOf ht hzt.symm
  have hzo : orderOf (z : G) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    have := congrArg Subtype.val hz2
    simpa using this
  refine ⟨z, hVA hzV, hzo, (centralizes_iff_mem_centralizer D A (preimage_le D _) z).mpr ?_⟩
  rw [hzt]
  exact htC

theorem eq_top_of_perfect {L : Type} [Group L] (hL : commutator L = ⊤) (N : Subgroup L) [N.Normal]
    (hcomm : ∀ x y : L ⧸ N, x * y = y * x) : N = ⊤ := by
  rw [eq_top_iff, ← hL, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    hcomm (x : L ⧸ N) (y : L ⧸ N)]
  group

theorem index_ne_of_perfect {L : Type} [Group L] [Finite L] (hL : commutator L = ⊤)
    (N : Subgroup L) [N.Normal] : N.index ≠ 2 ∧ N.index ≠ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ k, N.index = k → (k = 2 ∨ k = 4) → False := by
    intro k hk hk24
    have hcard : Nat.card (L ⧸ N) = k := by rw [← Subgroup.index_eq_card]; exact hk
    have hcomm : ∀ x y : L ⧸ N, x * y = y * x := by
      rcases hk24 with rfl | rfl
      · have hsq : ∀ x : L ⧸ N, x ^ 2 = 1 := fun x => by rw [← hcard]; exact pow_card_eq_one'
        exact fun x y => TwoGroups.mul_comm_of_sq_eq_one (hsq x) (hsq y) (hsq (x * y))
      · exact fun x y => (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
          (by rw [hcard]; norm_num)).is_comm.comm x y
    have htop := eq_top_of_perfect hL N hcomm
    rw [htop, Subgroup.index_top] at hk
    rcases hk24 with rfl | rfl <;> omega
  exact ⟨fun h => key 2 h (Or.inl rfl), fun h => key 4 h (Or.inr rfl)⟩

theorem no_central_involution (hyp : Hyp61 G D r Abar) (a : Fin r) {R : Subgroup (Bar D)}
    (hR : IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))))
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) {t : Bar D}
    (htA : t ∈ bar D (aschbacherThm5Preimage D (Abar a)))
    (htC : t ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)))
    (ht2 : t ^ 2 = 1) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := bar D (aschbacherThm5Preimage D (Abar a)) with hLdef
  have hperf : commutator L = ⊤ := (bar_factor_perfect hyp a).commutator_eq_top
  by_contra ht1
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  have hGW : CFSG.GorensteinWalter.HasDihedralSylowTwo L := by
    intro S
    have hS : IsSylowOf 2 ((S : Subgroup L).map L.subtype) L := ⟨S, rfl⟩
    obtain ⟨f⟩ := sylow_equiv hR hS
    exact ⟨n - 1, by omega,
      ⟨(((S : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans f).trans e⟩⟩
  rcases CFSG.GorensteinWalter.gw_lemma_2_1 hGW with ⟨-, hconj, -⟩ | ⟨⟨N, hN, hidx⟩, -⟩ |
      ⟨⟨N, hN, hidx⟩, -⟩
  · have ht' : BenderSuzuki.PFAppendixIII.IsInvolution (⟨t, htA⟩ : L) :=
      ⟨fun h => ht1 (congrArg Subtype.val h), Subtype.ext ht2⟩
    have hcen : ∀ y : L, BenderSuzuki.PFAppendixIII.IsInvolution y → y = ⟨t, htA⟩ := by
      intro y hy
      obtain ⟨c, hc⟩ := hconj ⟨t, htA⟩ y ht' hy
      rw [← hc]
      have hct : c * ⟨t, htA⟩ = ⟨t, htA⟩ * c :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp htC) c c.2)
      rw [hct, mul_inv_cancel_right]
    have hinv : ∀ i : ZMod (2 ^ (n - 1)), BenderSuzuki.PFAppendixIII.IsInvolution
        (⟨((e.symm (DihedralGroup.sr i) : R) : Bar D),
          hR.le (e.symm (DihedralGroup.sr i)).2⟩ : L) := by
      intro i
      refine ⟨fun h => ?_, ?_⟩
      · have h0 := congrArg Subtype.val h
        have h1 : e.symm (DihedralGroup.sr i) = 1 := Subtype.ext h0
        have h2 := congrArg e h1
        rw [MulEquiv.apply_symm_apply, map_one, DihedralGroup.one_def] at h2
        cases h2
      · have h1 : (e.symm (DihedralGroup.sr i)) ^ 2 = 1 := by
          rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
        have h2 := congrArg Subtype.val h1
        exact Subtype.ext h2
    have h01 : (0 : ZMod (2 ^ (n - 1))) ≠ 1 := by
      intro h
      have h' : ((1 : ℕ) : ZMod (2 ^ (n - 1))) = 0 := by rw [Nat.cast_one]; exact h.symm
      rw [ZMod.natCast_eq_zero_iff] at h'
      have h2 : 2 ≤ 2 ^ (n - 1) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd one_pos h'
      omega
    have heq := (hcen _ (hinv 0)).trans (hcen _ (hinv 1)).symm
    have heq0 := congrArg Subtype.val heq
    have heq' : e.symm (DihedralGroup.sr 0) = e.symm (DihedralGroup.sr 1) := Subtype.ext heq0
    have h3 := e.symm.injective heq'
    exact h01 (DihedralGroup.sr.inj h3)
  · exact (index_ne_of_perfect hperf N).1 hidx
  · exact (index_ne_of_perfect hperf N).2 hidx

theorem isSimpleGroup_of_dihedral (hyp : Hyp61 G D r Abar) (a : Fin r)
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {R : Subgroup (Bar D)} (hR : IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))))
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) :
    IsSimpleGroup (bar D (aschbacherThm5Preimage D (Abar a))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set L := bar D A with hLdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hDA : D ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
      (canonical_preimage_normal D Abar hyp.hcomm hyp.hgen a)
  set Z := (Subgroup.center L).map L.subtype with hZdef
  have hZodd : Odd (Nat.card Z) := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
    obtain ⟨z, hz, hzx⟩ := x.2
    have hzL : (x : Bar D) ∈ L := hzx ▸ z.2
    have hxC : (x : Bar D) ∈ Subgroup.centralizer (L : Set (Bar D)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨c, hc⟩)
      rw [← hzx]
      exact h1
    have hx2 : (x : Bar D) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      rw [← hx]
      exact pow_orderOf_eq_one _
    have hx1 := no_central_involution hyp a hR hRd hzL hxC hx2
    rw [← Subgroup.orderOf_coe, hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hZD : Z ≤ bar D D := (Subgroup.map_subtype_le _).trans (bar_mono D (preimage_le D _))
  have hDZ : bar D D ≤ Subgroup.normalizer (Z : Set (Bar D)) := by
    intro y hy
    have hyL : y ∈ Subgroup.normalizer (L : Set (Bar D)) := bar_le_normalizer hDA hAH hy
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    rintro _ ⟨z, hz, rfl⟩
    have hyzL : y * (z : Bar D) * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL z).mp z.2
    refine ⟨⟨y * z * y⁻¹, hyzL⟩, ?_, rfl⟩
    rw [SetLike.mem_coe] at hz ⊢
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk' : y⁻¹ * (k : Bar D) * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set (Bar D))).inv_mem hyL) k).mp k.2
      simpa using this
    have hzc' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y⁻¹ * k * y, hk'⟩)
    change (y⁻¹ * (k : Bar D) * y) * z = z * (y⁻¹ * k * y) at hzc'
    change (k : Bar D) * (y * z * y⁻¹) = (y * z * y⁻¹) * k
    calc (k : Bar D) * (y * z * y⁻¹) = y * ((y⁻¹ * k * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * k * y)) * y⁻¹ := by rw [hzc']
      _ = y * z * y⁻¹ * k := by group
  have hle := AschbacherTheorem3.le_map_oddCore hZD hDZ hZodd
  rw [oddCore_bar_D, Subgroup.map_bot, le_bot_iff] at hle
  have hZbot : Subgroup.center L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hle
  have : Nontrivial L := L.nontrivial_iff_ne_bot.mpr (bar_factor_ne_bot hyp a)
  refine { toNontrivial := inferInstance, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  have := hN
  rcases Quasisimple.normal_le_center_or_eq_top haq N with h | h
  · left
    rw [hZbot] at h
    exact le_bot_iff.mp h
  · exact Or.inr h

omit [Finite G] in
theorem hasDihedralSylowTwo_of_isSylowOf {X : Type} [Group X] {K R : Subgroup X}
    (hR : IsSylowOf 2 R K) (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) :
    AschbacherKnownGroup.HasDihedralSylowTwo K := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  obtain ⟨P', hP'⟩ := hR
  exact ⟨P', n, hn, ⟨((P' : Subgroup K).equivMapOfInjective _ K.subtype_injective).trans
    ((MulEquiv.subgroupCongr hP').trans e)⟩⟩

omit [Finite G] in
theorem hasDihedralSylowTwo_of_equiv {X Y : Type} [Group X] [Group Y] [Finite Y] (E : X ≃* Y)
    (h : AschbacherKnownGroup.HasDihedralSylowTwo Y) :
    AschbacherKnownGroup.HasDihedralSylowTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨f⟩⟩ := h
  exact ⟨S.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective, n, hn,
    ⟨((S : Subgroup Y).equivMapOfInjective E.symm.toMonoidHom E.symm.injective).symm.trans f⟩⟩

omit [Finite G] in
@[expose] noncomputable def conjBarEquiv (D : Subgroup G)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (a : Fin r) (g : G) :
    bar (rightConjugate D g)
        (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g a)) ≃*
      bar D (aschbacherThm5Preimage D (Abar a)) :=
  let e2 : Abar a ≃* conjFactors D Abar g a :=
    (Abar a).equivMapOfInjective _ (Conj.quotientEquiv (MulAut.conj g⁻¹) D).injective
  (factorEquiv (rightConjugate D g) (conjFactors D Abar g a)).symm.trans
    (e2.symm.trans (factorEquiv D (Abar a)))

end Factor

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
