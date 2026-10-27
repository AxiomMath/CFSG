module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveFactor
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

open BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace Cases

theorem normalizer_le_normalizer_centralizing {x : Fin r}
    (hHx : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar x) : Set G)) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (centralizing D (Abar x) : Set G) := by
  intro h hh
  apply AschbacherToolkit.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨hyD, hyc⟩ := (mem_centralizing_iff _ y).mp hy
  refine (mem_centralizing_iff _ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hh y).mp hyD, ?_⟩
  intro w hw
  have hw' : h⁻¹ * w * h ∈ aschbacherThm5Preimage D (Abar x) := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem (hHx hh)) w).mp hw
    simpa using this
  have h1 := hyc _ hw'
  have h2 := (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_core D hh) _).mp h1
  have h3 : h * (y⁻¹ * (h⁻¹ * w * h)⁻¹ * y * (h⁻¹ * w * h)) * h⁻¹ =
      (h * y * h⁻¹)⁻¹ * w⁻¹ * (h * y * h⁻¹) * w := by group
  rwa [h3] at h2

theorem not_central_outside (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs) {x y : Fin r}
    (hxy : x ≠ y)
    (hHx : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar x) : Set G))
    (hHy : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar y) : Set G))
    (hyq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar y))))
    {z : G} (hzx : z ∈ aschbacherThm5Preimage D (Abar x)) (hz : orderOf z = 2)
    (hzc : aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar x)) z)
    (hzy : z ∉ aschbacherThm5Preimage D (Abar y)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ax := aschbacherThm5Preimage D (Abar x) with hAxdef
  set Ay := aschbacherThm5Preimage D (Abar y) with hAydef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set Zs := Ax ⊓ centralizing D (Abar x) with hZsdef
  set Q := Ay ⊔ Zs with hQdef
  have hAxH : Ax ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hAyH : Ay ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hZsH : Zs ≤ H := inf_le_left.trans hAxH
  have hQH : Q ≤ H := sup_le hAyH hZsH
  have hkQ : Ay ≤ Q := le_sup_left
  have hQj : Q ≤ centralizing D (Abar x) :=
    sup_le (factor_le_centralizing hC.hyp.hcomm hxy) inf_le_right
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    have hZs : h ∈ Subgroup.normalizer (Zs : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hHx hh, normalizer_le_normalizer_centralizing hHx hh⟩
    exact Subgroup.inf_normalizer_le_normalizer_sup Ay Zs ⟨hHy hh, hZs⟩
  obtain ⟨g, hg, T, hT, hT1⟩ := exists_nontrivial_overlap hC hin hkQ hQj hHQ
  obtain ⟨S, hS, -, -, -, -, halt⟩ := overlap_alternatives hC h3 hkQ hQj hHQ hg hT hT1
  have hTH : T ≤ H := hT.le.trans inf_le_right
  have hzH : z ∈ H := hAxH hzx
  set zb := toBar D ⟨z, hzH⟩ with hzbdef
  have hzZs : z ∈ Zs := ⟨hzx, (mem_centralizing_iff _ z).mpr ⟨preimage_le D _ hzx, hzc⟩⟩
  have hzbQ : zb ∈ bar D Q := toBar_mem_bar D ((le_sup_right : Zs ≤ Q) hzZs)
  have hzbY : zb ∉ bar D Ay := fun h => hzy (mem_of_toBar_mem_bar (core_le_preimage D _) h)
  have hzb1 : zb ≠ 1 := fun h => hzbY (h ▸ (bar D Ay).one_mem)
  have hzb2 : zb ^ 2 = 1 := by
    rw [hzbdef, ← map_pow, show (⟨z, hzH⟩ : H) ^ 2 = 1 from
      Subtype.ext (TwoGroups.sq_eq_one_of_orderOf hz), map_one]
  have hzbAy : zb ∈ Subgroup.centralizer (bar D Ay : Set (Bar D)) :=
    (centralizes_iff_mem_centralizer D Ay (preimage_le D _) ⟨z, hzH⟩).mp
      (centralizes_of_mem_centralizing (factor_le_centralizing hC.hyp.hcomm (Ne.symm hxy) hzx))
  have hzbZs : zb ∈ Subgroup.centralizer (bar D Zs : Set (Bar D)) :=
    Subgroup.centralizer_le (bar_mono D inf_le_left)
      ((centralizes_iff_mem_centralizer D Ax (preimage_le D _) ⟨z, hzH⟩).mp hzc)
  have hzbC : zb ∈ Subgroup.centralizer (bar D Q : Set (Bar D)) := by
    have hle : bar D Q ≤ Subgroup.centralizer ({zb} : Set (Bar D)) := by
      rw [hQdef, bar_sup hAyH hZsH]
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hzbAy) w hw)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hzbZs) w hw)
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hQAy : Q ≤ Subgroup.normalizer (Ay : Set G) := by
    have hDA : D ≤ Subgroup.normalizer (Ay : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
        (canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen y)
    exact (sup_le (preimage_le D _) (inf_le_left.trans (preimage_le D _))).trans hDA
  rcases halt with ⟨-, hSQ, -⟩ | ⟨n, hn, -, -, -, -, -, ⟨e⟩⟩
  ·
    have hSbar : IsSylowOf 2 (bar D S) (bar D Q ⊔ bar D T) := by
      rw [← bar_sup hQH hTH]
      exact isSylowOf_bar hS (sup_le hQH hTH)
    have hR : IsSylowOf 2 (bar D S ⊓ bar D Q) (bar D Q) :=
      hSbar.inf_of_le_normalizer le_sup_left
        (sup_le Subgroup.le_normalizer (bar_le_normalizer (hTH.trans hHQ) hQH))
    set R := bar D S ⊓ bar D Q with hRdef
    have hRtype : IsCyclic R ∨ AschbacherTheorem3.IsDihedralTwoGroup R ∨
        AschbacherTheorem3.IsQuaternionTwoGroup R := by
      rcases hSQ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    have hzbR : zb ∈ R := by
      have hz2 : IsPGroup 2 (Subgroup.zpowers zb) :=
        AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two (orderOf_eq_prime hzb2 hzb1)
      have hsup : IsPGroup 2 (R ⊔ Subgroup.zpowers zb : Subgroup (Bar D)) := by
        refine isPGroup_sup_of_commute hR.isPGroup hz2 fun u hu v hv => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        have hc : u * zb = zb * u := (Subgroup.mem_centralizer_iff.mp hzbC) u (hR.le hu)
        exact ((Commute.zpow_right hc k)).eq
      have heq := hR.eq_of_le le_sup_left (sup_le hR.le (Subgroup.zpowers_le.mpr hzbQ)) hsup
      rw [← heq]
      exact (le_sup_right : Subgroup.zpowers zb ≤ R ⊔ Subgroup.zpowers zb)
        (Subgroup.mem_zpowers zb)
    have hP : IsSylowOf 2 (R ⊓ bar D Ay) (bar D Ay) :=
      hR.inf_of_le_normalizer (bar_mono D hkQ) (bar_le_normalizer hQAy hAyH)
    have hPc : ¬ IsCyclic (R ⊓ bar D Ay : Subgroup (Bar D)) :=
      sylow_not_cyclic_of_perfect (bar_factor_perfect hC.hyp y) (bar_factor_ne_bot hC.hyp y) hP
    have hPn : ((R ⊓ bar D Ay).subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun w hw =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hw, bar_le_normalizer hQAy hAyH (hR.le hw)⟩
    have hzc' : ∀ w ∈ R, zb * w = w * zb := fun w hw =>
      ((Subgroup.mem_centralizer_iff.mp hzbC) w (hR.le hw)).symm
    exact hzbY (mem_of_normal_noncyclic hRtype hzbR hzb1 hzb2 hzc' inf_le_left hPn hPc).2
  ·
    set M := AschbacherTheorem3.oTwoPrime (bar D Q) with hMdef
    have : IsSimpleGroup PSL(2, GaloisField 2 n) := Exclusion.psl_simple hn
    have : IsSimpleGroup M := e.isSimpleGroup
    have hzbM : zb ∈ M := Linear.le_oTwoPrime (Subgroup.zpowers_le.mpr hzbQ)
      (AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two (orderOf_eq_prime hzb2 hzb1))
      (Subgroup.mem_zpowers zb)
    have hMQ : M ≤ bar D Q := Linear.oTwoPrime_le _
    have hzZ : (⟨zb, hzbM⟩ : M) ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzbC) w (hMQ w.2))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
    · rw [h, Subgroup.mem_bot] at hzZ
      exact hzb1 (congrArg Subtype.val hzZ)
    ·
      have hAyM : bar D Ay ≤ M := by
        rw [← Linear.oTwoPrime_eq_of_quasisimple hyq]
        exact Subgroup.closure_mono fun w hw => ⟨bar_mono D hkQ hw.1, hw.2⟩
      have : Group.IsPerfect (bar D Ay) := bar_factor_perfect hC.hyp y
      have : Nontrivial (bar D Ay) :=
        (bar D Ay).nontrivial_iff_ne_bot.mpr (bar_factor_ne_bot hC.hyp y)
      apply Group.IsPerfect.not_isMulCommutative (bar D Ay)
      refine ⟨⟨fun u v => Subtype.ext ?_⟩⟩
      have hu : (⟨u, hAyM u.2⟩ : M) ∈ Subgroup.center M := h ▸ Subgroup.mem_top _
      have h' := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hu) ⟨v, hAyM v.2⟩).symm
      exact h'

theorem not_dihedral (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs) {a b : Fin r}
    (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hHb : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar b) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {R : Subgroup (Bar D)} (hR : IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar a))))
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set B := aschbacherThm5Preimage D (Abar b) with hBdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hBH : B ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hAb : A ≤ centralizing D (Abar b) := factor_le_centralizing hC.hyp.hcomm (Ne.symm hab)
  have hBa : B ≤ centralizing D (Abar a) := factor_le_centralizing hC.hyp.hcomm hab
  have : IsSimpleGroup (bar D A) := Factor.isSimpleGroup_of_dihedral hC.hyp a haq hR hRd
  obtain ⟨g, hg, T, hT, hT1⟩ := exists_nontrivial_overlap hC hin le_rfl hAb hHa
  have hTH : T ≤ H := hT.le.trans inf_le_right
  have hTAg : T ≤ rightConjugate A g := hT.le.trans inf_le_left
  obtain ⟨t, htT, ht⟩ := exists_orderOf_eq_two hT.isPGroup hT1
  have htH : t ∈ H := hTH htT
  have hzt := AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two ht
  obtain ⟨xa, hxaA, hxa, hxat⟩ := exists_involution_centralized hzt
    (Subgroup.zpowers_le.mpr (hHa htH)) (factor_even hC.hyp a)
  have hcta : t * xa = xa * t := hxat t (Subgroup.mem_zpowers t)
  have hzxa := AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two hxa
  have hW : IsPGroup 2 (Subgroup.zpowers t ⊔ Subgroup.zpowers xa : Subgroup G) := by
    refine isPGroup_sup_of_commute hzt hzxa fun u hu v hv => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow hcta m k).eq
  obtain ⟨xb, hxbB, hxb, hxbW⟩ := exists_involution_centralized hW
    (sup_le (Subgroup.zpowers_le.mpr (hHb htH)) (Subgroup.zpowers_le.mpr (hHb (hAH hxaA))))
    (factor_even hC.hyp b)
  have hctb : t * xb = xb * t := hxbW t ((le_sup_left : Subgroup.zpowers t ≤ _)
    (Subgroup.mem_zpowers t))
  have hcab : xa * xb = xb * xa := hxbW xa ((le_sup_right : Subgroup.zpowers xa ≤ _)
    (Subgroup.mem_zpowers xa))
  have hxaH : xa ∈ H := hAH hxaA
  have hxbH : xb ∈ H := hBH hxbB
  have hCa : Subgroup.centralizer ({xa} : Set G) ≤ H :=
    centralizer_le hC b ⟨1, by rw [pow_one]; exact TwoGroups.sq_eq_one_of_orderOf hxa⟩
      (TwoGroups.ne_one_of_orderOf hxa) (centralizes_of_mem_centralizing (hAb hxaA))
  have hCb : Subgroup.centralizer ({xb} : Set G) ≤ H :=
    centralizer_le hC a ⟨1, by rw [pow_one]; exact TwoGroups.sq_eq_one_of_orderOf hxb⟩
      (TwoGroups.ne_one_of_orderOf hxb) (centralizes_of_mem_centralizing (hBa hxbB))
  have hxab1 : toBar D ⟨xa, hxaH⟩ ≠ 1 := by
    intro h
    have hO := (toBar_eq_one_iff D _).mp h
    exact TwoGroups.ne_one_of_orderOf hxa
      (Strong.eq_one_of_mem_core_of_sq hO (TwoGroups.sq_eq_one_of_orderOf hxa))
  have hxab2 : toBar D ⟨xa, hxaH⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨xa, hxaH⟩ : H) ^ 2 = 1 from
      Subtype.ext (TwoGroups.sq_eq_one_of_orderOf hxa), map_one]
  have hxbC : toBar D ⟨xb, hxbH⟩ ∈ Subgroup.centralizer (bar D A : Set (Bar D)) :=
    (centralizes_iff_mem_centralizer D A (preimage_le D _) ⟨xb, hxbH⟩).mp
      (centralizes_of_mem_centralizing (hBa hxbB))
  set D' := rightConjugate D g with hD'def
  set Abar' := conjFactors D Abar g with hAbar'def
  have hC' : Counterexample G D' r Abar' := hC.conj g
  set A' := aschbacherThm5Preimage D' (Abar' a) with hA'def
  have hA'eq : A' = rightConjugate A g := preimage_conjFactors D Abar g a
  have hH'eq : Subgroup.normalizer (D' : Set G) = rightConjugate H g :=
    normalizer_rightConjugate D g
  have hA'H' : A' ≤ Subgroup.normalizer (D' : Set G) :=
    (preimage_le D' _).trans Subgroup.le_normalizer
  have hA'b : A' ≤ centralizing D' (Abar' b) := factor_le_centralizing hC'.hyp.hcomm (Ne.symm hab)
  have hHa' : Subgroup.normalizer (D' : Set G) ≤ Subgroup.normalizer (A' : Set G) := by
    rw [hH'eq, hA'eq, ← AschbacherTheorem3.rightConjugate_normalizer]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hHa g
  have hg' : g⁻¹ ∉ Subgroup.normalizer (D' : Set G) := by
    rw [hH'eq, mem_rightConjugate_iff, show g * g⁻¹ * g⁻¹ = g⁻¹ by group]
    intro h
    exact hg (by simpa using H.inv_mem h)
  have htA' : t ∈ A' := by
    rw [hA'eq]
    exact hTAg htT
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (D' : Set G) :=
    centralizer_le hC' b ⟨1, by rw [pow_one]; exact TwoGroups.sq_eq_one_of_orderOf ht⟩
      (TwoGroups.ne_one_of_orderOf ht) (centralizes_of_mem_centralizing (hA'b htA'))
  have hxaH' : xa ∈ Subgroup.normalizer (D' : Set G) :=
    hCt (Subgroup.mem_centralizer_singleton_iff.mpr hcta.symm)
  have hxbH' : xb ∈ Subgroup.normalizer (D' : Set G) :=
    hCt (Subgroup.mem_centralizer_singleton_iff.mpr hctb.symm)
  have : IsSimpleGroup (bar D' A') := (Factor.conjBarEquiv D Abar a g).isSimpleGroup
  have hKd : AschbacherKnownGroup.HasDihedralSylowTwo (bar D' A') :=
    Factor.hasDihedralSylowTwo_of_equiv (Factor.conjBarEquiv D Abar a g)
      (Factor.hasDihedralSylowTwo_of_isSylowOf hR hRd)
  have hcyc : ∀ x (hxH' : x ∈ Subgroup.normalizer (D' : Set G)), orderOf x = 2 →
      Subgroup.centralizer ({x} : Set G) ≤ H →
      AschbacherKnownGroup.HasCyclicSylowTwo (bar D' A' ⊓
        Subgroup.centralizer ({toBar D' ⟨x, hxH'⟩} : Set (Bar D')) : Subgroup (Bar D')) := by
    intro x hxH' hx hCx
    rw [← bar_inf_centralizer (core_le_preimage D' _) hxH' hx]
    set W := A' ⊓ Subgroup.centralizer ({x} : Set G) with hWdef
    have hWH' : W ≤ Subgroup.normalizer (D' : Set G) := inf_le_left.trans hA'H'
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (bar D' W)))
    refine ⟨P, ?_⟩
    have hPb : IsPGroup 2 ((P : Subgroup (bar D' W)).map (bar D' W).subtype) :=
      P.isPGroup'.map _
    obtain ⟨V, hVW, hV2, hVP⟩ := lift_two_subgroup hWH' hPb (Subgroup.map_subtype_le _)
    have hVc : IsCyclic V := Factor.conj_inter_isCyclic hC h3 hab hHa haq hg hV2
      (le_inf (hVW.trans (inf_le_left.trans hA'eq.le)) (hVW.trans (inf_le_right.trans hCx)))
    have h1 : IsCyclic (bar D' V) := (isCyclic_bar_iff hV2 (hVW.trans hWH')).mpr hVc
    rw [hVP] at h1
    exact isCyclic_of_equiv ((P : Subgroup (bar D' W)).equivMapOfInjective _
      (bar D' W).subtype_injective).symm h1
  have hgen : ¬ bar D' A' ≤
      (bar D' A' ⊓ Subgroup.centralizer ({toBar D' ⟨xa, hxaH'⟩} : Set (Bar D'))) ⊔
        (bar D' A' ⊓ Subgroup.centralizer ({toBar D' ⟨xb, hxbH'⟩} : Set (Bar D'))) := by
    intro hle
    rw [← bar_inf_centralizer (core_le_preimage D' _) hxaH' hxa,
      ← bar_inf_centralizer (core_le_preimage D' _) hxbH' hxb,
      ← bar_sup (inf_le_left.trans hA'H') (inf_le_left.trans hA'H')] at hle
    have hAX := le_sup_core_of_bar_le hA'H' hle
    apply hg'
    refine mem_normalizer_of_le_sup hC' a g⁻¹ _ ?_
      (sup_le (inf_le_left.trans hA'H') (inf_le_left.trans hA'H')) hAX
    rw [hH'eq, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    exact sup_le (inf_le_right.trans hCa) (inf_le_right.trans hCb)
  have hxa'N : toBar D' ⟨xa, hxaH'⟩ ∈ Subgroup.normalizer (bar D' A' : Set (Bar D')) :=
    bar_le_normalizer (Y := Subgroup.normalizer (D' : Set G)) hHa' hA'H'
      (toBar_mem_bar D' (h := ⟨xa, hxaH'⟩) hxaH')
  have hxb'N : toBar D' ⟨xb, hxbH'⟩ ∈ Subgroup.normalizer (bar D' A' : Set (Bar D')) :=
    bar_le_normalizer (Y := Subgroup.normalizer (D' : Set G)) hHa' hA'H'
      (toBar_mem_bar D' (h := ⟨xb, hxbH'⟩) hxbH')
  have hsq : ∀ x (hxH' : x ∈ Subgroup.normalizer (D' : Set G)), orderOf x = 2 →
      toBar D' ⟨x, hxH'⟩ ^ 2 = 1 := by
    intro x hxH' hx
    rw [← map_pow, show (⟨x, hxH'⟩ : Subgroup.normalizer (D' : Set G)) ^ 2 = 1 from
      Subtype.ext (TwoGroups.sq_eq_one_of_orderOf hx), map_one]
  have hcomm' : toBar D' ⟨xa, hxaH'⟩ * toBar D' ⟨xb, hxbH'⟩ =
      toBar D' ⟨xb, hxbH'⟩ * toBar D' ⟨xa, hxaH'⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcab
  have h39 := AschbacherKnownGroup.lemma_3_9 hin.knownGroups (bar D' A') hKd hxa'N hxb'N
    (hsq xa hxaH' hxa) (hsq xb hxbH' hxb) hcomm' (hcyc xa hxaH' hxa hCa)
    (hcyc xb hxbH' hxb hCb) hgen
  set y := xa * xb with hydef
  have hy2 : y ^ 2 = 1 := by
    have hid : xa * xb * (xa * xb) = (xa * xa) * (xb * xb) := by
      calc xa * xb * (xa * xb) = xa * (xb * xa) * xb := by group
        _ = xa * (xa * xb) * xb := by rw [← hcab]
        _ = (xa * xa) * (xb * xb) := by group
    rw [hydef, pow_two, hid, ← pow_two, ← pow_two, TwoGroups.sq_eq_one_of_orderOf hxa,
      TwoGroups.sq_eq_one_of_orderOf hxb, one_mul]
  have hy1 : y ≠ 1 := by
    intro h
    have hxab : xb = xa := by
      have h' : xa * xb = 1 := h
      have h1 : xb = xa⁻¹ := eq_inv_of_mul_eq_one_right h'
      have hxa1 : xa * xa = 1 := by
        rw [← pow_two]
        exact TwoGroups.sq_eq_one_of_orderOf hxa
      rw [h1, inv_eq_of_mul_eq_one_left hxa1]
    apply hxab1
    refine Factor.no_central_involution hC.hyp a hR hRd (toBar_mem_bar D hxaA) ?_ hxab2
    have := hxbC
    simp only [hxab] at this
    exact this
  have hyH' : y ∈ Subgroup.normalizer (D' : Set G) :=
    (Subgroup.normalizer (D' : Set G)).mul_mem hxaH' hxbH'
  have hyc : aschbacherThm5Centralizes (aschbacherThm5Core D') A' y := by
    refine (centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨y, hyH'⟩).mpr ?_
    have : toBar D' ⟨y, hyH'⟩ = toBar D' ⟨xa, hxaH'⟩ * toBar D' ⟨xb, hxbH'⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact h39
  have hCy : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (D' : Set G) :=
    centralizer_le hC' a ⟨1, by rw [pow_one]; exact hy2⟩ hy1 hyc
  have hyH : y ∈ H := H.mul_mem hxaH hxbH
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  set xab := toBar D ⟨xa, hxaH⟩ with hxabdef
  have hxabo : orderOf xab = 2 := orderOf_eq_prime hxab2 hxab1
  obtain ⟨R'', hR'', hxR''⟩ := AschbacherTheorem3.exists_isSylowOf_le
    (AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two hxabo)
    (Subgroup.zpowers_le.mpr (toBar_mem_bar D (h := ⟨xa, hxaH⟩) hxaA))
  obtain ⟨f⟩ := sylow_equiv hR hR''
  have hR''d : AschbacherTheorem3.IsDihedralTwoGroup R'' := isDihedral_of_equiv f.symm hRd
  obtain ⟨Vb, hVbR, -, hVbc, hVbel, hVb4⟩ := dihedral_centralizer_four hR''d
    (hxR'' (Subgroup.mem_zpowers xab)) hxab1 hxab2
  have hVbW : Vb ≤ bar D (A ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [bar_inf_centralizer (core_le_preimage D _) hyH hyo]
    refine le_inf (hVbR.trans hR''.le) fun v hv => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvA : v ∈ bar D A := hR''.le (hVbR hv)
    have h1 : v * xab = xab * v := hVbc v hv
    have h2 : v * toBar D ⟨xb, hxbH⟩ = toBar D ⟨xb, hxbH⟩ * v :=
      (Subgroup.mem_centralizer_iff.mp hxbC) v hvA
    have h3 : toBar D ⟨y, hyH⟩ = xab * toBar D ⟨xb, hxbH⟩ := by
      rw [hxabdef, ← map_mul]
      rfl
    rw [h3]
    calc v * (xab * toBar D ⟨xb, hxbH⟩) = (v * xab) * toBar D ⟨xb, hxbH⟩ := by group
      _ = xab * (v * toBar D ⟨xb, hxbH⟩) := by rw [h1]; group
      _ = xab * toBar D ⟨xb, hxbH⟩ * v := by rw [h2]; group
  have hVb2 : IsPGroup 2 Vb := IsPGroup.of_card (n := 2) (by rw [hVb4]; norm_num)
  obtain ⟨V, hVW, hV2, hVV⟩ := lift_two_subgroup (inf_le_left.trans hAH) hVb2 hVbW
  have hVc : IsCyclic V := Factor.inter_isCyclic hC h3 hab hHa haq hg hV2
    (le_inf (hVW.trans inf_le_left)
      (hVW.trans (inf_le_right.trans (hCy.trans hH'eq.le))))
  have hVbc' : IsCyclic Vb := by
    rw [← hVV]
    exact (isCyclic_bar_iff hV2 ((hVW.trans inf_le_left).trans hAH)).mpr hVc
  have := Exclusion.card_le_two_of_isCyclic hVbc' hVbel.2
  omega

end Cases

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
