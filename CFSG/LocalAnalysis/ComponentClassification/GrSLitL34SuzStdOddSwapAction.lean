module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSmall
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwapDeviation
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
theorem mul_comm_of_mem_of_l34SuzOdd (hD : L34SuzOddData A V K y) {v w : G} (hv : v ∈ V)
    (hw : w ∈ V) : v * w = w * v := by
  have hv2 : v * v = 1 := hD.mul_self v hv
  have hw2 : w * w = 1 := hD.mul_self w hw
  have hvw2 : (v * w) * (v * w) = 1 := hD.mul_self (v * w) (V.mul_mem hv hw)
  have h1 : v * (w * v) * w = 1 := by
    calc v * (w * v) * w = (v * w) * (v * w) := by group
      _ = 1 := hvw2
  have h2 : w * v = v * w := by
    calc w * v = 1 * (w * v) * 1 := by simp
      _ = (v * v) * (w * v) * (w * w) := by rw [hv2, hw2]
      _ = v * (v * (w * v) * w) * w := by group
      _ = v * 1 * w := by rw [h1]
      _ = v * w := by simp
  exact h2.symm

theorem not_mem_of_l34SuzOdd (hS : L34SuzOddSetting A t) : t ∉ A := by
  intro htA
  have htZ : (⟨t, htA⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hS.t_mem (a : G) a.2)
  have h2 : 2 ∣ Nat.card (center ↥A) := by
    have hd := orderOf_dvd_natCard (⟨⟨t, htA⟩, htZ⟩ : ↥(center ↥A))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hS.orderOf_t] at hd
  exact hS.odd_card_center.not_two_dvd_nat h2

theorem mem_of_mem_sup_zpowers_of_mem_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {e : G} (he : e ∈ V ⊔ zpowers t) (heA : e ∈ A) : e ∈ V := by
  have htV : t ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
  have hzN : zpowers t ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr htV).trans (Subgroup.centralizer_le_normalizer _)
  have hsup : ((V ⊔ zpowers t : Subgroup G) : Set G) = (V : Set G) * (zpowers t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left V (Subgroup.zpowers t) hzN
  have he' : e ∈ ((V ⊔ zpowers t : Subgroup G) : Set G) := he
  rw [hsup, Set.mem_mul] at he'
  obtain ⟨v, hv, w, hw, hvw⟩ := he'
  rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t
    hS.orderOf_t w).1 hw with hw1 | hwt
  · rw [hw1, mul_one] at hvw
    rwa [← hvw]
  · exfalso
    apply not_mem_of_l34SuzOdd hS
    have hvA : v ∈ A := hD.le_A hv
    have heA' : v * w ∈ A := by rwa [← hvw] at heA
    have hprod : v * t ∈ A := by rw [← hwt]; exact heA'
    have ht : t = v⁻¹ * (v * t) := by group
    rw [ht]
    exact A.mul_mem (A.inv_mem hvA) hprod

theorem odd_card_center_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) : Odd (Nat.card (center ↥K)) := by
  let ZA : Subgroup ↥A := center ↥A
  let C : Subgroup G := K ⊓ ZA.map A.subtype
  let f : ↥K →* (↥A ⧸ ZA) :=
    (QuotientGroup.mk' ZA).comp (Subgroup.inclusion (le_A_of_l34SuzOddData hD))
  have hfker : f.ker = C.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    dsimp only [f, C, ZA]
    rw [MonoidHom.comp_apply]
    constructor
    · intro h
      have h1 : (Subgroup.inclusion (le_A_of_l34SuzOddData hD) k : ↥A) ∈ center ↥A :=
        (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at h)
      exact ⟨k.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion _ k, h1, rfl⟩⟩
    · rintro ⟨-, hkZ⟩
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hkZ
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hincl : Subgroup.inclusion (le_A_of_l34SuzOddData hD) k = a := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion]
        exact haeq.symm
      rw [hincl]
      exact ha
  have hfrange : Nat.card ↥f.range = 20160 := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hD.card_image
  have hCcard : Nat.card ↥f.ker = Nat.card ↥C := by
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hKcard : Nat.card ↥K = Nat.card ↥f.ker * 20160 := by
    rw [← Subgroup.card_ker_mul_card_range f, hfrange]
  have hZcard : Nat.card (center ↥K) * 20160 = Nat.card ↥K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥K),
      CFSG.Blueprint.LieModel.card_psl_three_four hD.l34, mul_comm]
  have hmul : Nat.card ↥f.ker * 20160 = Nat.card (center ↥K) * 20160 := by
    rw [← hKcard, hZcard]
  have hEq : Nat.card ↥f.ker = Nat.card (center ↥K) :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) hmul
  have hdvd : Nat.card (center ↥K) ∣ Nat.card (center ↥A) := by
    rw [← hEq, hCcard]
    have h1 : Nat.card ↥C ∣ Nat.card ↥(ZA.map A.subtype) :=
      Subgroup.card_dvd_of_le inf_le_right
    rwa [Subgroup.card_map_of_injective A.subtype_injective] at h1
  exact Odd.of_dvd_nat hS.odd_card_center hdvd

omit [Finite G] in
theorem exists_ne_of_l34SuzOdd (hD : L34SuzOddData A V K y) :
    ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcomm : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h b hb a ha
  have hKbot : K = ⊥ := by
    rw [← hD.perfect]
    exact hcomm
  have hcard : Nat.card ↥((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) = 1 := by
    rw [hKbot]
    simp
  have himg := hD.card_image
  rw [hcard] at himg
  exact absurd himg (by norm_num)

theorem map_conj_eq_or_of_l34SuzOdd (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hK : K = (HarrisLit.swapDiag P t hc).range) {g : G} (hgu : g * u = u * g)
    (hgt : g * t = t * g) (hgK : g ∈ centralizer (K : Set G)) :
    P.map (MulAut.conj g).toMonoidHom = P ∨
      P.map (MulAut.conj g).toMonoidHom = P.map (MulAut.conj t).toMonoidHom := by
  have _ := hu1
  let X : Subgroup G := centralizer ({u} : Set G)
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hS.orderOf_t] at h
  have huA : u ∈ A := hD.le_A hu
  have htu : u * t = t * u := Subgroup.mem_centralizer_iff.1 hS.t_mem u huA
  have hXmap : X.map (MulAut.conj g).toMonoidHom = X := by
    have h := CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton g u
    rw [show g * u * g⁻¹ = u by rw [hgu]; group] at h
    simpa only [X] using h
  have hgX : g ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hXmap
  have htX : t ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change X.map (MulAut.conj t).toMonoidHom = X
    have h := CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton t u
    rw [show t * u * t⁻¹ = u by rw [← htu]; group] at h
    simpa only [X] using h
  have hPcomp := HarrisLit.isCompIn_of_isComponent hPu hcomp
  have hPgComp : CFSG.CGT.PushingUpLit.CGT6.Nine7.IsCompIn
      (P.map (MulAut.conj g).toMonoidHom) X := by
    have hcX : CFSG.conjugate X g⁻¹ = X := by
      change X.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom = X
      rw [inv_inv]
      exact hXmap
    have h := hPcomp.cj g⁻¹
    rw [hcX] at h
    change CFSG.CGT.PushingUpLit.CGT6.Nine7.IsCompIn
      (P.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) X at h
    rwa [inv_inv] at h
  have hcQ : P.map (MulAut.conj g).toMonoidHom ≤
      centralizer (((P.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    HarrisLit.map_conj_le_centralizer_map hgt hc
  have heq : (HarrisLit.swapDiag (P.map (MulAut.conj g).toMonoidHom) t hcQ).range =
      (HarrisLit.swapDiag P t hc).range := by
    rw [HarrisLit.range_swapDiag_map_conj hgt hc]
    have hgN : g ∈ Subgroup.normalizer ((HarrisLit.swapDiag P t hc).range : Set G) := by
      rw [← hK]
      exact Subgroup.centralizer_le_normalizer _ hgK
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hnab : ∃ a ∈ (HarrisLit.swapDiag P t hc).range,
      ∃ b ∈ (HarrisLit.swapDiag P t hc).range, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := exists_ne_of_l34SuzOdd hD
    exact ⟨a, by rw [← hK]; exact ha, b, by rw [← hK]; exact hb, hab⟩
  exact HarrisLit.eq_or_eq_map_of_range_swapDiag_eq ht2 htX hPcomp hPgComp hc hcQ heq hnab

theorem mem_sup_zpowers_of_mem_center_of_l34SuzOdd
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hK : K = (HarrisLit.swapDiag P t hc).range) {z : G} (hzP : z ∈ P)
    (hzc : z ∈ centralizer (P : Set G)) (hz : z * z = 1) : z ∈ V ⊔ zpowers t := by
  let M : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  let E : Subgroup G := V ⊔ zpowers t
  have hEM : E ≤ M := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD
  have hEcard : Nat.card E = 8 := card_sup_zpowers_of_l34SuzOdd hS hD
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  have hEsq : ∀ x ∈ E, x * x = 1 := mul_self_eq_one_of_isPGroup_of_l34SuzOdd hS hD hEM hE2
  have hPperf : Group.IsPerfect ↥P := by
    have hq : Group.IsPerfect ↥(P.subgroupOf (centralizer ({u} : Set G))) := hcomp.1.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPu).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPu).surjective
  have hoddR : Odd (Nat.card (center ↥(HarrisLit.swapDiag P t hc).range)) := by
    rw [← hK]
    exact odd_card_center_of_l34SuzOdd hS hD
  have hzt : t * z * t⁻¹ = z :=
    HarrisLit.conj_eq_of_mem_center_of_odd hc hoddR hzP hzc hz
  have hzt' : z * t = t * z := by
    calc z * t = (t * z * t⁻¹) * t := by rw [hzt]
      _ = t * z := by group
  have hzK : z ∈ centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [hK] at hk
    obtain ⟨p, rfl⟩ := hk
    rw [HarrisLit.swapDiag_apply]
    have hzp : z * (p : G) = (p : G) * z :=
      (Subgroup.mem_centralizer_iff.mp hzc (p : G) p.2).symm
    have hztp : MulAut.conj t (p : G) * z = z * MulAut.conj t (p : G) :=
      Subgroup.mem_centralizer_iff.mp (hc hzP) _ ⟨p, p.2, rfl⟩
    calc (p : G) * MulAut.conj t (p : G) * z
        = (p : G) * (MulAut.conj t (p : G) * z) := by group
      _ = (p : G) * (z * MulAut.conj t (p : G)) := by rw [hztp]
      _ = ((p : G) * z) * MulAut.conj t (p : G) := by group
      _ = (z * (p : G)) * MulAut.conj t (p : G) := by rw [hzp]
      _ = z * ((p : G) * MulAut.conj t (p : G)) := by group
  have hzCt : z ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt'
  have hzM : z ∈ M := Subgroup.mem_inf.2 ⟨hzCt, hzK⟩
  have hVtcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have htV : t ∈ centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.1 hS.t_mem v (hD.le_A hv)
    have hb' : b ∈ centralizer (V : Set G) := (Subgroup.zpowers_le.mpr htV) hb
    exact Subgroup.mem_centralizer_iff.1 hb' a ha
  have hzV : ∀ v ∈ V, v * z = z * v := by
    intro v hv
    have hvM : v ∈ M := hEM (Subgroup.mem_sup_left hv)
    have hvt : v * t = t * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvM).1
    have hvK : v ∈ centralizer (K : Set G) := (Subgroup.mem_inf.mp hvM).2
    have hvKr : v ∈ centralizer ((HarrisLit.swapDiag P t hc).range : Set G) := by
      rw [← hK]
      exact hvK
    rcases map_conj_eq_or_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK
      (mul_comm_of_mem_of_l34SuzOdd hD hv hu) hvt hvK with hfix | hswap
    · have hvC : v ∈ centralizer (P : Set G) :=
        HarrisLit.mem_centralizer_of_map_conj_eq hc hPperf hfix hvt hvKr
      exact (Subgroup.mem_centralizer_iff.mp hvC z hzP).symm
    · have htv : t * v ∈ centralizer (P : Set G) :=
        HarrisLit.mul_mem_centralizer_of_map_conj_eq_map
          (show t ^ 2 = 1 from by
            have h := pow_orderOf_eq_one t
            rwa [hS.orderOf_t] at h)
          hc hPperf hswap hvt hvKr
      have h1 : z * (t * v) = (t * v) * z := Subgroup.mem_centralizer_iff.mp htv z hzP
      have h2 : t * (z * v) = t * (v * z) := by
        calc t * (z * v) = (t * z) * v := by group
          _ = (z * t) * v := by rw [hzt']
          _ = z * (t * v) := by group
          _ = (t * v) * z := h1
          _ = t * (v * z) := by group
      exact (mul_left_cancel h2).symm
  have hzE : z ∈ centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hVtcomm he
    have haz : a * z = z * a := hzV a ha
    have hbz : b * z = z * b := by
      rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution t
        hS.orderOf_t b).1 hb with rfl | rfl
      · simp
      · exact hzt'.symm
    calc (a * b) * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [hbz]
      _ = (a * z) * b := by group
      _ = (z * a) * b := by rw [haz]
      _ = z * (a * b) := by group
  have hcommEz : ∀ e ∈ E, ∀ f ∈ zpowers z, e * f = f * e := by
    have hzEcent : zpowers z ≤ centralizer (E : Set G) := Subgroup.zpowers_le.mpr hzE
    intro e he f hf
    exact Subgroup.mem_centralizer_iff.mp (hzEcent hf) e he
  have hQsq : ∀ x ∈ E ⊔ zpowers z, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommEz hx
    have ha2 : a * a = 1 := hEsq a ha
    have hb2 : b * b = 1 := by
      by_cases hz1 : z = 1
      · have hb1 : b = 1 := by simpa [hz1] using hb
        rw [hb1, mul_one]
      · have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
        rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution z
          hzord b).1 hb with rfl | rfl
        · simp
        · exact hz
    have hab : a * b = b * a := hcommEz a ha b hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hQ2 : IsPGroup 2 ↥(E ⊔ zpowers z) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨1, ?_⟩
    have hgpow : g ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hQsq (g : G) g.2
    simpa using orderOf_dvd_of_pow_eq_one hgpow
  have hQleM : (E ⊔ zpowers z : Subgroup G) ≤ M :=
    sup_le hEM (Subgroup.zpowers_le.mpr hzM)
  have hQcard : Nat.card ↥(E ⊔ zpowers z) ≤ 8 :=
    card_le_eight_of_isPGroup_of_l34SuzOdd hS hD hQleM hQ2
  by_cases hzmem : z ∈ E
  · exact hzmem
  · exfalso
    have hzne : z ≠ 1 := fun h => hzmem (h ▸ Subgroup.one_mem E)
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hzne
    have hdisj : Disjoint E (zpowers z) := by
      rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxE, hxz⟩ := Subgroup.mem_inf.mp hx
      rcases (CFSG.Semidihedral.OddCentralizerSylowTwo.mem_zpowers_involution z
        hzord x).1 hxz with rfl | rfl
      · exact Subgroup.one_mem ⊥
      · exact absurd hxE hzmem
    have hnorm : zpowers z ≤ Subgroup.normalizer (E : Set G) :=
      (Subgroup.zpowers_le.mpr hzE).trans (Subgroup.centralizer_le_normalizer _)
    have hcard16 : Nat.card ↥(E ⊔ zpowers z) = 16 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers z)
        hnorm hdisj, hEcard, Nat.card_zpowers, hzord]
    omega

theorem eq_one_or_eq_of_map_conj_eq_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {P : Subgroup G}
    (hPu : P ≤ centralizer ({u} : Set G)) (hne : P.map (MulAut.conj t).toMonoidHom ≠ P)
    {v : G} (hv : v ∈ V)
    (hvP : P.map (MulAut.conj v).toMonoidHom = P.map (MulAut.conj t).toMonoidHom) {w : G}
    (hw : w ∈ V) (hwP : P.map (MulAut.conj w).toMonoidHom = P) : w = 1 ∨ w = u := by
  have _ := hS
  by_contra h
  push Not at h
  obtain ⟨hw1, hwu⟩ := h
  have hu2 : u * u = 1 := hD.mul_self u hu
  have hw2 : w * w = 1 := hD.mul_self w hw
  have huw : u * w = w * u := mul_comm_of_mem_of_l34SuzOdd hD hu hw
  have huwN : u ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer (P : Set G) (by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPu hp))
  have hUle : Subgroup.closure ({u, w} : Set G) ≤ V ⊓ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_inf.2 ⟨hu, huwN⟩
    · exact Subgroup.mem_inf.2 ⟨hw, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hwP⟩
  have hclos : Nat.card ↥(Subgroup.closure ({u, w} : Set G)) = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions hu2 hw2 huw hu1 hw1 hwu
  have hVinf : V ⊓ Subgroup.normalizer (P : Set G) = V := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [hD.card_V]
    calc 4 = Nat.card ↥(Subgroup.closure ({u, w} : Set G)) := hclos.symm
      _ ≤ Nat.card ↥(V ⊓ Subgroup.normalizer (P : Set G)) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hUle)
  have hvN : v ∈ Subgroup.normalizer (P : Set G) := by
    have hvV : v ∈ V ⊓ Subgroup.normalizer (P : Set G) := by
      rw [hVinf]
      exact hv
    exact (Subgroup.mem_inf.mp hvV).2
  have hvfix : P.map (MulAut.conj v).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hvN
  exact hne (hvP.symm.trans hvfix)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
