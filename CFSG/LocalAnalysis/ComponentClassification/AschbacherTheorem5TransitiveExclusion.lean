module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveLift
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveSpread
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveConj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveLinear

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace Exclusion

@[expose] def centralizerIn (D A : Subgroup G) : Subgroup G :=
  ((Subgroup.centralizer (bar D A : Set (Bar D))).comap (toBar D)).map
    (Subgroup.normalizer (D : Set G)).subtype

omit [Finite G] in
theorem mem_centralizerIn_iff (D A : Subgroup G) (x : G) :
    x ∈ centralizerIn D A ↔ ∃ hx : x ∈ Subgroup.normalizer (D : Set G),
      toBar D ⟨x, hx⟩ ∈ Subgroup.centralizer (bar D A : Set (Bar D)) := by
  rw [centralizerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, hc, rfl⟩

omit [Finite G] in
theorem core_le_centralizerIn (D A : Subgroup G) : aschbacherThm5Core D ≤ centralizerIn D A := by
  intro x hx
  rw [mem_centralizerIn_iff]
  refine ⟨core_le_normalizer D hx, ?_⟩
  rw [(toBar_eq_one_iff D ⟨x, core_le_normalizer D hx⟩).mpr hx]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem bar_centralizerIn (D A : Subgroup G) :
    bar D (centralizerIn D A) = Subgroup.centralizer (bar D A : Set (Bar D)) := by
  have hsub : (centralizerIn D A).subgroupOf (Subgroup.normalizer (D : Set G)) =
      (Subgroup.centralizer (bar D A : Set (Bar D))).comap (toBar D) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.normalizer (D : Set G)).subtype_injective _
  change ((centralizerIn D A).subgroupOf (Subgroup.normalizer (D : Set G))).map (toBar D) = _
  rw [hsub, Subgroup.map_comap_eq_self_of_surjective (toBar_surjective D)]

omit [Finite G] in
theorem card_le_two_of_isCyclic {P : Subgroup G} (hP : IsCyclic P) (hsq : ∀ x ∈ P, x ^ 2 = 1) :
    Nat.card P ≤ 2 := by
  obtain ⟨x, hx⟩ := hP.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hx]
  apply orderOf_le_of_pow_eq_one (by norm_num)
  exact Subtype.ext (hsq x x.2)

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hq : CFSG.Open.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_characteristic |> fun h =>
    IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : Group.IsPerfect X := ⟨hq.1⟩
    have : Nontrivial X := Quasisimple.nontrivial hq
    apply Group.IsPerfect.not_isMulCommutative X
    exact ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)⟩⟩

theorem psl_simple {n : ℕ} (hn : 2 ≤ n) : IsSimpleGroup PSL(2, GaloisField 2 n) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)

omit [Finite G] in
theorem product_mem_of_sup {X : Type*} [Group X] {Ob Pb : Subgroup X}
    (hPO : Pb ≤ Subgroup.normalizer (Ob : Set X)) {x : X} (hx : x ∈ Ob ⊔ Pb) :
    ∃ o ∈ Ob, ∃ p ∈ Pb, x = o * p := by
  have hx' : x ∈ ((Ob ⊔ Pb : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Ob Pb hPO] at hx'
  obtain ⟨o, ho, p, hp, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨o, ho, p, hp, rfl⟩

theorem lifted_config {a : Fin r} {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTH : T ≤ Subgroup.normalizer (D : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {n : ℕ} (hn : 2 ≤ n) (e : bar D (aschbacherThm5Preimage D (Abar a)) ≃* PSL(2, GaloisField 2 n))
    {Ob Pb : Subgroup (Bar D)} (hOb : IsElemAbelian 2 Ob) (hObcard : Nat.card Ob = 2 ^ n)
    (hObC : Ob ≤ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)))
    (hObA : Ob ⊓ bar D (aschbacherThm5Preimage D (Abar a)) = ⊥)
    (hPb : IsSylowOf 2 Pb (bar D (aschbacherThm5Preimage D (Abar a))))
    (hPbcard : Nat.card Pb = 2 ^ n) (hTOP : bar D T ≤ Ob ⊔ Pb)
    (hTcard : Nat.card (bar D T) = 2 ^ n)
    (hTC : bar D T ⊓
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)) = ⊥) :
    ∃ V : Subgroup G, T ≤ V ∧ V ≤ Subgroup.normalizer (D : Set G) ∧ IsElemAbelian 2 V ∧
      Nat.card V = 2 ^ n * 2 ^ n ∧ bar D V = Ob ⊔ Pb ∧
      Nat.card (V ⊓ aschbacherThm5Preimage D (Abar a) : Subgroup G) = 2 ^ n ∧
      Nat.card (V ⊓ centralizerIn D (aschbacherThm5Preimage D (Abar a)) : Subgroup G) = 2 ^ n ∧
      Nat.card T = 2 ^ n ∧
      (V ⊓ centralizerIn D (aschbacherThm5Preimage D (Abar a))) ⊓
        (V ⊓ aschbacherThm5Preimage D (Abar a)) = ⊥ ∧
      T ⊓ (V ⊓ centralizerIn D (aschbacherThm5Preimage D (Abar a))) = ⊥ ∧
      (∀ y ∈ aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer (V : Set G),
        ∀ u ∈ V ⊓ centralizerIn D (aschbacherThm5Preimage D (Abar a)), y * u * y⁻¹ = u) ∧
      (∀ p ∈ V ⊓ aschbacherThm5Preimage D (Abar a), ∀ q ∈ V ⊓ aschbacherThm5Preimage D (Abar a),
        p ≠ 1 → q ≠ 1 → ∃ y ∈ aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer (V : Set G),
          y * p * y⁻¹ = q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G)
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  obtain ⟨hPbel, hPbtrans, -⟩ := Linear.psl_sylow_structure hn e hPb
  have : IsSimpleGroup (bar D A) := by
    have := psl_simple hn
    exact e.isSimpleGroup
  have hZ := center_eq_bot_of_simple haq
  have hPbA : Pb ≤ bar D A := hPb.le
  have hcommOP : ∀ o ∈ Ob, ∀ p ∈ Pb, o * p = p * o := fun o ho p hp =>
    ((Subgroup.mem_centralizer_iff.mp (hObC ho)) p (hPbA hp)).symm
  have hPO : Pb ≤ Subgroup.normalizer (Ob : Set (Bar D)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    exact fun o ho => hcommOP o ho p hp
  have hOPbot : Ob ⊓ Pb = ⊥ := le_bot_iff.mp ((inf_le_inf_left Ob hPbA).trans hObA.le)
  set Vb := Ob ⊔ Pb with hVbdef
  have hVbcard : Nat.card Vb = 2 ^ n * 2 ^ n := by
    rw [AschbacherTheorem3.card_sup_of_le_normalizer hPO hOPbot, hObcard, hPbcard]
  have hVb2 : IsPGroup 2 Vb := IsPGroup.of_card (n := n + n) (by rw [hVbcard, pow_add])
  have hVbel : ∀ x ∈ Vb, ∀ y ∈ Vb, x * y = y * x ∧ x ^ 2 = 1 := by
    intro x hx y hy
    obtain ⟨o, ho, p, hp, rfl⟩ := product_mem_of_sup hPO hx
    obtain ⟨o', ho', p', hp', rfl⟩ := product_mem_of_sup hPO hy
    have hoo : o * o' = o' * o := congrArg Subtype.val (hOb.1.is_comm.comm ⟨o, ho⟩ ⟨o', ho'⟩)
    have hpp : p * p' = p' * p := congrArg Subtype.val (hPbel.1.is_comm.comm ⟨p, hp⟩ ⟨p', hp'⟩)
    refine ⟨?_, ?_⟩
    · calc o * p * (o' * p') = (o * o') * (p * p') := by
            rw [mul_assoc, ← mul_assoc p, ← hcommOP o' ho' p hp]; group
        _ = (o' * o) * (p' * p) := by rw [hoo, hpp]
        _ = o' * p' * (o * p) := by
            rw [mul_assoc, ← mul_assoc o, hcommOP o ho p' hp']; group
    · rw [pow_two, show o * p * (o * p) = (o * o) * (p * p) by
          rw [mul_assoc, ← mul_assoc p, ← hcommOP o ho p hp]; group,
        ← pow_two, ← pow_two, hOb.2 o ho, hPbel.2 p hp, one_mul]
  obtain ⟨V, hTV, hVH, hV2, hVbar⟩ := exists_lift_isPGroup hVb2 hT2 hTH hTOP
  have hinj : ∀ {x y : G}, x ∈ V → y ∈ V → ∀ (hx : x ∈ H) (hy : y ∈ H),
      toBar D ⟨x, hx⟩ = toBar D ⟨y, hy⟩ → x = y := by
    intro x y hxV hyV hx hy hxy
    exact congrArg Subtype.val (toBar_injOn_of_isPGroup hV2 (u := ⟨x, hx⟩) (v := ⟨y, hy⟩) hxV
      hyV hxy)
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := by
    rw [← card_bar_of_isPGroup hV2 hVH, hVbar, hVbcard]
  have hVel : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · apply hinj (V.mul_mem x.2 y.2) (V.mul_mem y.2 x.2) (H.mul_mem (hVH x.2) (hVH y.2))
        (H.mul_mem (hVH y.2) (hVH x.2))
      have hx' : toBar D ⟨x, hVH x.2⟩ ∈ Vb := hVbar ▸ toBar_mem_bar D x.2
      have hy' : toBar D ⟨y, hVH y.2⟩ ∈ Vb := hVbar ▸ toBar_mem_bar D y.2
      have h1 := (hVbel _ hx' _ hy').1
      change toBar D (⟨x, hVH x.2⟩ * ⟨y, hVH y.2⟩) = toBar D (⟨y, hVH y.2⟩ * ⟨x, hVH x.2⟩)
      rw [map_mul, map_mul, h1]
    · have hx' : toBar D ⟨x, hVH hx⟩ ∈ Vb := hVbar ▸ toBar_mem_bar D hx
      have h1 := (hVbel _ hx' _ hx').2
      apply hinj (V.pow_mem hx 2) V.one_mem (H.pow_mem (hVH hx) 2) H.one_mem
      change toBar D (⟨x, hVH hx⟩ ^ 2) = toBar D 1
      rw [map_pow, h1, map_one]
  have hVbA : Vb ⊓ bar D A = Pb := by
    apply le_antisymm _ (le_inf le_sup_right hPbA)
    rintro x ⟨hx, hxA⟩
    obtain ⟨o, ho, p, hp, rfl⟩ := product_mem_of_sup hPO hx
    have hoA : o ∈ bar D A := by
      have := (bar D A).mul_mem hxA ((bar D A).inv_mem (hPbA hp))
      simpa using this
    have ho1 : o = 1 := by
      have hmem : o ∈ Ob ⊓ bar D A := ⟨ho, hoA⟩
      rwa [hObA, Subgroup.mem_bot] at hmem
    rw [ho1, one_mul]
    exact hp
  have hVbC : Vb ⊓ Subgroup.centralizer (bar D A : Set (Bar D)) = Ob := by
    apply le_antisymm _ (le_inf le_sup_left hObC)
    rintro x ⟨hx, hxC⟩
    obtain ⟨o, ho, p, hp, rfl⟩ := product_mem_of_sup hPO hx
    have hpC : p ∈ Subgroup.centralizer (bar D A : Set (Bar D)) := by
      have := (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem (hObC ho)) hxC
      simpa using this
    have hp1 : p = 1 := by
      have hc : (⟨p, hPbA hp⟩ : bar D A) ∈ Subgroup.center (bar D A) := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpC) y y.2)
      rw [hZ, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    rw [hp1, mul_one]
    exact ho
  set P := V ⊓ A with hPdef
  set U := V ⊓ centralizerIn D A with hUdef
  have hP2 : IsPGroup 2 P := hV2.to_le inf_le_left
  have hU2 : IsPGroup 2 U := hV2.to_le inf_le_left
  have hPbar : bar D P = Pb := by
    rw [hPdef, bar_inf_of_core_le hOA, hVbar, hVbA]
  have hUbar : bar D U = Ob := by
    rw [hUdef, bar_inf_of_core_le (core_le_centralizerIn D A), hVbar, bar_centralizerIn, hVbC]
  have hPcard : Nat.card P = 2 ^ n := by
    rw [← card_bar_of_isPGroup hP2 (inf_le_left.trans hVH), hPbar, hPbcard]
  have hUcard : Nat.card U = 2 ^ n := by
    rw [← card_bar_of_isPGroup hU2 (inf_le_left.trans hVH), hUbar, hObcard]
  have hTcard' : Nat.card T = 2 ^ n := by rw [← card_bar_of_isPGroup hT2 hTH, hTcard]
  have hUP : U ⊓ P = ⊥ := by
    rw [← bar_eq_bot_iff_of_isPGroup (hU2.to_le inf_le_left) (inf_le_left.trans
      (inf_le_left.trans hVH)), eq_bot_iff]
    refine (le_inf (bar_mono D inf_le_left) (bar_mono D inf_le_right)).trans ?_
    rw [hUbar, hPbar, hOPbot]
  have hTU : T ⊓ U = ⊥ := by
    rw [← bar_eq_bot_iff_of_isPGroup (hT2.to_le inf_le_left) (inf_le_left.trans hTH), eq_bot_iff,
      ← hTC]
    refine le_inf (bar_mono D inf_le_left) ((bar_mono D inf_le_right).trans ?_)
    rw [hUbar]
    exact hObC
  refine ⟨V, hTV, hVH, hVel, hVcard, hVbar, hPcard, hUcard, hTcard', hUP, hTU, ?_, ?_⟩
  ·
    rintro y ⟨hyA, hyN⟩ u ⟨huV, huC⟩
    obtain ⟨huH, huc⟩ := (mem_centralizerIn_iff D A u).mp huC
    have hyH := hAH hyA
    have hyuV : y * u * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN u).mp huV
    apply hinj hyuV huV (H.mul_mem (H.mul_mem hyH huH) (H.inv_mem hyH)) huH
    change toBar D (⟨y, hyH⟩ * ⟨u, huH⟩ * ⟨y, hyH⟩⁻¹) = toBar D ⟨u, huH⟩
    rw [map_mul, map_mul, map_inv,
      (Subgroup.mem_centralizer_iff.mp huc) _ (toBar_mem_bar D (h := ⟨y, hyH⟩) hyA)]
    group
  ·
    rintro p ⟨hpV, hpA⟩ q ⟨hqV, hqA⟩ hp1 hq1
    have hpH := hAH hpA
    have hqH := hAH hqA
    have hpb : toBar D ⟨p, hpH⟩ ∈ Pb := hPbar ▸ toBar_mem_bar D (h := ⟨p, hpH⟩) ⟨hpV, hpA⟩
    have hqb : toBar D ⟨q, hqH⟩ ∈ Pb := hPbar ▸ toBar_mem_bar D (h := ⟨q, hqH⟩) ⟨hqV, hqA⟩
    have hpb1 : toBar D ⟨p, hpH⟩ ≠ 1 := by
      intro h
      apply hp1
      exact hinj hpV V.one_mem hpH H.one_mem (h.trans (map_one _).symm)
    have hqb1 : toBar D ⟨q, hqH⟩ ≠ 1 := by
      intro h
      apply hq1
      exact hinj hqV V.one_mem hqH H.one_mem (h.trans (map_one _).symm)
    obtain ⟨yb, ⟨hybA, hybN⟩, hyb⟩ := hPbtrans _ hpb _ hqb hpb1 hqb1
    have hybV : yb ∈ Subgroup.normalizer (Vb : Set (Bar D)) := by
      have hybO : yb ∈ Subgroup.normalizer (Ob : Set (Bar D)) := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro o ho
        exact ((Subgroup.mem_centralizer_iff.mp (hObC ho)) yb hybA).symm
      exact Subgroup.inf_normalizer_le_normalizer_sup Ob Pb ⟨hybO, hybN⟩
    rw [← hVbar, normalizer_bar hV2 hVH] at hybV
    obtain ⟨y, hyN, hyy⟩ := (mem_bar_iff D _ yb).mp hybV
    have hyA : (y : G) ∈ A := mem_of_toBar_mem_bar hOA (hyy ▸ hybA)
    refine ⟨y, ⟨hyA, hyN⟩, ?_⟩
    have hypV : (y : G) * p * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN p).mp hpV
    apply hinj hypV hqV (H.mul_mem (H.mul_mem y.2 hpH) (H.inv_mem y.2)) hqH
    change toBar D (y * ⟨p, hpH⟩ * y⁻¹) = _
    rw [map_mul, map_mul, map_inv, hyy]
    exact hyb

omit [Finite G] in
theorem quasisimple_conj {a : Fin r}
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a)))) (g : G) :
    CFSG.Open.IsQuasisimple (bar (rightConjugate D g)
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g a))) := by
  have e2 : Abar a ≃* conjFactors D Abar g a :=
    (Abar a).equivMapOfInjective _ (Conj.quotientEquiv (MulAut.conj g⁻¹) D).injective
  exact Components.quasisimple_of_equiv
    ((factorEquiv (rightConjugate D g) (conjFactors D Abar g a)).symm.trans
      (e2.symm.trans (factorEquiv D (Abar a)))) haq

theorem eq_one_of_mem_core_of_isPGroup {V : Subgroup G} (hV : IsPGroup 2 V) {x : G} (hxV : x ∈ V)
    (hxO : x ∈ aschbacherThm5Core D) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : V ⊓ aschbacherThm5Core D = ⊥ :=
    CFSG.ComponentClassification.AschbacherToolkit.inf_eq_bot_of_isPGroup_of_coprime hV
      (fun h => (Nat.not_even_iff_odd.mpr (core_odd D)) (even_iff_two_dvd.mpr h))
  have hmem : x ∈ V ⊓ aschbacherThm5Core D := ⟨hxV, hxO⟩
  rwa [hinf, Subgroup.mem_bot] at hmem

theorem inner_of_overlap (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {P : Subgroup G}
    (hP : IsSylowOf 2 P (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G))) (hPsq : ∀ x ∈ P, x ^ 2 = 1) (hPcard : 2 < Nat.card P) :
    ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (bar D (aschbacherThm5Preimage D (Abar a)) ≃* PSL(2, GaloisField 2 n)) ∧
      ∃ Ob Pb : Subgroup (Bar D),
        Ob ≤ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)) ∧
        Pb ≤ Ob ⊔ bar D P ∧ IsSylowOf 2 Pb (bar D (aschbacherThm5Preimage D (Abar a))) ∧
        bar D (aschbacherThm5Preimage D (Abar a)) ⊓ Subgroup.centralizer (Pb : Set (Bar D)) ≤
          Pb ∧
        bar D P ≤ Ob ⊔ Pb ∧ Nat.card Pb = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hAb : A ≤ centralizing D (Abar b) := factor_le_centralizing hC.hyp.hcomm (Ne.symm hab)
  have hPH : P ≤ H := hP.le.trans inf_le_right
  have hP2 := hP.isPGroup
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    omega
  obtain ⟨S, -, -, hPA, -, -, halt⟩ := overlap_alternatives hC h3 le_rfl hAb hHa hg hP hP1
  have hcardbar : Nat.card (bar D P) = Nat.card P := card_bar_of_isPGroup hP2 hPH
  rcases halt with ⟨hcyc, -, -⟩ | halt
  · exfalso
    have hsq : ∀ x ∈ bar D P, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff D P x).mp hx
      rw [← map_pow, show h ^ 2 = 1 from Subtype.ext (hPsq h hh), map_one]
    have := card_le_two_of_isCyclic hcyc hsq
    omega
  have hPC := bar_overlap_inf_centralizer hC hAb hg (hP.le.trans inf_le_left) hP2 a
  have hPAbar : bar D P ⊓ bar D A = ⊥ := by
    rw [← bar_inf_of_core_le hOA, hPA, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨n, hn, ⟨e⟩, Ob, Pb, -, -, hObC, -, hPbdef, hPb, hPbcard, hPOP, hPcard'⟩ :=
    Linear.decode_altThree haq (bar_le_normalizer (hPH.trans hHa) hAH) (isPGroup_bar hP2) hPAbar
      hPC halt
  obtain ⟨-, -, hself⟩ := Linear.psl_sylow_structure hn e hPb
  refine ⟨n, hn, ⟨e⟩, Ob, Pb, hObC, hPbdef ▸ inf_le_left, hPb, hself, hPOP, ?_⟩
  rw [hPbcard, ← hPcard', hcardbar]

end Exclusion

open Exclusion in
theorem not_altThree (hC : Counterexample G D r Abar) (h3 : AschbacherTheorem3.Theorem3Statement)
    {a b : Fin r} (hab : a ≠ b)
    (hHa : Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (haq : CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))))
    {g : G} (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G))) (hT1 : T ≠ ⊥) :
    ¬ Thm3AltThree (bar D (aschbacherThm5Preimage D (Abar a))) (bar D T) := by
  intro halt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hAH : A ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hAb : A ≤ centralizing D (Abar b) := factor_le_centralizing hC.hyp.hcomm (Ne.symm hab)
  obtain ⟨hNA, htightA⟩ := tightlyEmbedded_of_le_centralizing hC le_rfl hAb hHa
  have hTH : T ≤ H := hT.le.trans inf_le_right
  have hTAg : T ≤ rightConjugate A g := hT.le.trans inf_le_left
  have hT2 := hT.isPGroup
  have hgA : g ∉ Subgroup.normalizer (A : Set G) := hNA ▸ hg
  have hTA : T ⊓ A = ⊥ := two_subgroup_inf_conjugate_eq_bot A T htightA hT2 g hgA hTAg
  have hTC := bar_overlap_inf_centralizer hC hAb hg hTAg hT2 a
  have hTAbar : bar D T ⊓ bar D A = ⊥ := by
    rw [← bar_inf_of_core_le hOA, hTA, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨n, hn, ⟨e⟩, Ob, Pb, hOb, hObcard, hObC, hObA, -, hPb, hPbcard, hTOP, hTcard⟩ :=
    Linear.decode_altThree haq (bar_le_normalizer (hTH.trans hHa) hAH) (isPGroup_bar hT2) hTAbar
      hTC halt
  obtain ⟨V, hTV, hVH, hVel, hVcard, -, hPcard, hUcard, hTcard', hUP, hTU, hYU, htrans⟩ :=
    lifted_config hT2 hTH haq hn e hOb hObcard hObC hObA hPb hPbcard hTOP hTcard hTC
  set P := V ⊓ A with hPdef
  set U := V ⊓ centralizerIn D A with hUdef
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := n + n) (by rw [hVcard, pow_add])
  have hP2 : IsPGroup 2 P := hV2.to_le inf_le_left
  have hTP : T ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left T inf_le_right).trans hTA.le)
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPHg : P ≤ rightConjugate H g := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hgtA : g * t * g⁻¹ ∈ A := (mem_rightConjugate_iff A g t).mp (hTAg t.2)
    obtain ⟨k, hk⟩ := hT2 t
    have hCH := centralizer_le hC b (t := g * t * g⁻¹) ⟨k, by
        rw [conj_pow, show ((t : G) ^ 2 ^ k) = 1 from congrArg Subtype.val hk]; group⟩
      (fun h => ht1' (by
        calc (t : G) = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group))
      (centralizes_of_mem_centralizing (hAb hgtA))
    intro x hx
    rw [mem_rightConjugate_iff]
    apply hCH
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxt := hVcomm x hx.1 t (hTV t.2)
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  have hPS : IsSylowOf 2 P (A ⊓ rightConjugate H g) := by
    obtain ⟨PS, hPS⟩ := exists_isSylowOf 2 (A ⊓ rightConjugate H g)
    have h1 := card_le_of_overlap hC le_rfl hAb hHa hg hT hPS.le hPS.isPGroup
    have h2 := AschbacherTheorem3.card_le_of_isSylowOf hPS hP2 (le_inf inf_le_right hPHg)
    refine isSylowOf_of_card (le_inf inf_le_right hPHg) ?_
    rw [← hPS.card_eq]
    omega
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
  have haq' : CFSG.Open.IsQuasisimple (bar D' A') := quasisimple_conj haq g
  have hg' : g⁻¹ ∉ Subgroup.normalizer (D' : Set G) := by
    rw [hH'eq, mem_rightConjugate_iff, show g * g⁻¹ * g⁻¹ = g⁻¹ by group]
    intro h
    exact hg (by simpa using H.inv_mem h)
  have hP' : IsSylowOf 2 P (rightConjugate A' g⁻¹ ⊓ Subgroup.normalizer (D' : Set G)) := by
    rw [hA'eq, rightConjugate_mul, mul_inv_cancel, rightConjugate_one, hH'eq]
    exact hPS
  have hPsq : ∀ x ∈ P, x ^ 2 = 1 := fun x hx => hVel.2 x hx.1
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hPcard2 : 2 < Nat.card P := by
    have : Nat.card P = 2 ^ n := hPcard
    omega
  obtain ⟨n', hn', ⟨e'⟩, Ob', Pb', hOb'C, hPb'le, hPb', hself, hPOP', hPb'card⟩ :=
    inner_of_overlap hC' h3 hab hHa' haq' hg' hP' hPsq hPcard2
  have hTA' : T ≤ A' := by
    rw [hA'eq]
    exact hTAg
  have hTH' : T ≤ Subgroup.normalizer (D' : Set G) := hTA'.trans hA'H'
  have hPH' : P ≤ Subgroup.normalizer (D' : Set G) := by
    rw [hH'eq]
    exact hPHg
  have hTbar : bar D' T = Pb' := by
    have hOT' : Ob' ≤ Subgroup.centralizer (bar D' T : Set (Bar D')) :=
      hOb'C.trans (Subgroup.centralizer_le (bar_mono D' hTA'))
    have hPT' : bar D' P ≤ Subgroup.centralizer (bar D' T : Set (Bar D')) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := (mem_bar_iff D' P x).mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨t, ht, rfl⟩ := (mem_bar_iff D' T z).mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVcomm _ (hTV ht) _ hp.1)
    have hTC' : bar D' T ≤ Subgroup.centralizer (Pb' : Set (Bar D')) :=
      Subgroup.le_centralizer_iff.mpr (hPb'le.trans (sup_le hOT' hPT'))
    have hle : bar D' T ≤ Pb' := (le_inf (bar_mono D' hTA') hTC').trans hself
    apply Subgroup.eq_of_le_of_card_ge hle
    refine le_of_eq ?_
    rw [hPb'card, card_bar_of_isPGroup hT2 hTH', hTcard', hPcard]
  set R := V ⊓ centralizerIn D' A' with hRdef
  have hPO' : Pb' ≤ Subgroup.normalizer (Ob' : Set (Bar D')) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact ((Subgroup.mem_centralizer_iff.mp (hOb'C ho)) q (hPb'.le hq)).symm
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard2
    omega
  have hR1 : R ≠ ⊥ := by
    obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
    have hpH' : p ∈ Subgroup.normalizer (D' : Set G) := hPH' hp
    obtain ⟨o, ho, q, hq, hpoq⟩ :=
      product_mem_of_sup hPO' (hPOP' (toBar_mem_bar D' (h := ⟨p, hpH'⟩) hp))
    rw [← hTbar] at hq
    obtain ⟨t₀, ht₀, rfl⟩ := (mem_bar_iff D' T _).mp hq
    have hxH' : p * (t₀ : G)⁻¹ ∈ Subgroup.normalizer (D' : Set G) :=
      (Subgroup.normalizer (D' : Set G)).mul_mem hpH'
        ((Subgroup.normalizer (D' : Set G)).inv_mem t₀.2)
    have hx : toBar D' ⟨p * (t₀ : G)⁻¹, hxH'⟩ = o := by
      change toBar D' (⟨p, hpH'⟩ * t₀⁻¹) = o
      rw [map_mul, map_inv, hpoq, mul_inv_cancel_right]
    intro hbot
    have hmem : p * (t₀ : G)⁻¹ ∈ R :=
      ⟨V.mul_mem hp.1 (V.inv_mem (hTV ht₀)),
        (mem_centralizerIn_iff D' A' _).mpr ⟨hxH', hx ▸ hOb'C ho⟩⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    have hpTP : p ∈ T ⊓ P := ⟨by rw [hmem]; exact ht₀, hp⟩
    rw [hTP, Subgroup.mem_bot] at hpTP
    exact hp1' hpTP
  have hRU : R ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvV, hvR⟩, -, hvU⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' v).mp hvR
    obtain ⟨hvH, hvc⟩ := (mem_centralizerIn_iff D A v).mp hvU
    have hc' := (centralizes_conj_iff D Abar g a v).mp
      ((centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨v, hvH'⟩).mpr hvc')
    have hc := (centralizes_iff_mem_centralizer D A (preimage_le D _) ⟨v, hvH⟩).mpr hvc
    obtain ⟨k, hk⟩ := hV2 ⟨v, hvV⟩
    apply hg
    refine mem_normalizer_of_fusion hC a a (t := g * v * g⁻¹) (g := g) ⟨k, ?_⟩ ?_ hc' ?_
    · rw [conj_pow, show v ^ 2 ^ k = 1 from congrArg Subtype.val hk]
      group
    · intro h
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
  have hRP : R ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvV, hvR⟩, -, hvA⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' v).mp hvR
    have hc' := (centralizes_conj_iff D Abar g a v).mp
      ((centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨v, hvH'⟩).mpr hvc')
    have hc := centralizes_of_mem_centralizing (hAb hvA)
    obtain ⟨k, hk⟩ := hV2 ⟨v, hvV⟩
    apply hg
    refine mem_normalizer_of_fusion hC a b (t := g * v * g⁻¹) (g := g) ⟨k, ?_⟩ ?_ hc' ?_
    · rw [conj_pow, show v ^ 2 ^ k = 1 from congrArg Subtype.val hk]
      group
    · intro h
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
  have : IsSimpleGroup (bar D' A') := by
    have := psl_simple hn'
    exact e'.isSimpleGroup
  have hZ' := center_eq_bot_of_simple haq'
  have hRT : ∀ y ∈ ((A ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G), ∀ t ∈ T,
      y * t * y⁻¹ ∈ R → y * t * y⁻¹ = 1 := by
    rintro y ⟨-, -⟩ t htT ⟨hvV, hvR⟩
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' _).mp hvR
    have hc'v := (centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨_, hvH'⟩).mpr hvc'
    have hgtA : g * t * g⁻¹ ∈ A := (mem_rightConjugate_iff A g t).mp (hTAg htT)
    have hct : aschbacherThm5Centralizes (aschbacherThm5Core D')
        (aschbacherThm5Preimage D' (Abar' b)) t :=
      (centralizes_conj_iff D Abar g b t).mpr (centralizes_of_mem_centralizing (hAb hgtA))
    obtain ⟨k, hk⟩ := hV2 ⟨_, hvV⟩
    have hyH' : y ∈ Subgroup.normalizer (D' : Set G) :=
      mem_normalizer_of_fusion hC' a b (t := y * t * y⁻¹) (g := y) ⟨k, congrArg Subtype.val hk⟩
        hv1 hc'v (by rwa [show y⁻¹ * (y * t * y⁻¹) * y = t by group])
    have hvA' : y * t * y⁻¹ ∈ A' := (Subgroup.mem_normalizer_iff.mp (hHa' hyH') t).mp (hTA' htT)
    have hc : (⟨toBar D' ⟨_, hvH'⟩, toBar_mem_bar D' hvA'⟩ : bar D' A') ∈
        Subgroup.center (bar D' A') := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hvc') z z.2)
    rw [hZ', Subgroup.mem_bot] at hc
    have h1 : toBar D' ⟨_, hvH'⟩ = 1 := congrArg Subtype.val hc
    exact hv1 (eq_one_of_mem_core_of_isPGroup hV2 hvV ((toBar_eq_one_iff D' _).mp h1))
  have hTcardP : Nat.card T * Nat.card P = Nat.card V := by
    rw [hTcard', hPcard, hVcard]
  have hUcardP : Nat.card U * Nat.card P = Nat.card V := by
    rw [hUcard, hPcard, hVcard]
  exact hR1 (spread_exclusion (Y := ((A ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G))
    hVel inf_le_left inf_le_left hTV hUcardP hTcardP hUP hTU hTP hYU htrans inf_le_left hRU hRP
    hRT)

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
