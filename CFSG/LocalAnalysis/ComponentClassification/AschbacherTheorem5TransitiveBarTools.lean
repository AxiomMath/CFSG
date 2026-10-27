module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

namespace BarTools

section TwoGroups

variable {X : Type} [Group X] [Finite X]

theorem exists_orderOf_eq_two {M : Subgroup X} (hM : IsPGroup 2 M) (hM1 : M ≠ ⊥) :
    ∃ x ∈ M, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hM1 (Subgroup.eq_bot_of_card_eq M hn)
  have h2 : 2 ∣ Nat.card M := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem sylow_equiv {K P R : Subgroup X} (hP : IsSylowOf 2 P K) (hR : IsSylowOf 2 R K) :
    Nonempty (R ≃* P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP hR.isPGroup hR.le
  have heq : rightConjugate R c = P := by
    apply Subgroup.eq_of_le_of_card_ge hc
    rw [rightConjugate_card, hP.card_eq, hR.card_eq]
  exact ⟨(R.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).trans (MulEquiv.subgroupCongr heq)⟩

omit [Finite X] in
theorem isDihedral_of_equiv {Y : Type} [Group Y] {P : Subgroup X} {Q : Subgroup Y} (e : P ≃* Q)
    (hP : AschbacherTheorem3.IsDihedralTwoGroup P) : AschbacherTheorem3.IsDihedralTwoGroup Q := by
  obtain ⟨n, hn, ⟨f⟩⟩ := hP
  exact ⟨n, hn, ⟨e.symm.trans f⟩⟩

omit [Finite X] in
theorem isQuaternion_of_equiv {Y : Type} [Group Y] {P : Subgroup X} {Q : Subgroup Y}
    (e : P ≃* Q) (hP : AschbacherTheorem3.IsQuaternionTwoGroup P) :
    AschbacherTheorem3.IsQuaternionTwoGroup Q := by
  obtain ⟨n, hn, ⟨f⟩⟩ := hP
  exact ⟨n, hn, ⟨e.symm.trans f⟩⟩

omit [Finite X] in
theorem isCyclic_of_equiv {Y : Type} [Group Y] {P : Subgroup X} {Q : Subgroup Y} (e : P ≃* Q)
    (hP : IsCyclic P) : IsCyclic Q :=
  isCyclic_of_surjective e.toMonoidHom e.surjective

theorem exists_involution_centralized {Y E : Subgroup X} (hE : IsPGroup 2 E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set X)) (hY : Even (Nat.card Y)) :
    ∃ y ∈ Y, orderOf y = 2 ∧ ∀ e ∈ E, e * y = y * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hES⟩ := AschbacherTheorem3.exists_isSylowOf_le hE (le_sup_right : E ≤ Y ⊔ E)
  have hYn : Y ⊔ E ≤ Subgroup.normalizer (Y : Set X) := sup_le Subgroup.le_normalizer hEY
  have hP : IsSylowOf 2 (S ⊓ Y) Y := hS.inf_of_le_normalizer le_sup_left hYn
  have hPne : S ⊓ Y ≠ ⊥ := by
    intro hbot
    have h1 := hP.card_eq
    rw [hbot, Subgroup.card_bot] at h1
    have hf : (Nat.card Y).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
        (even_iff_two_dvd.mp hY)).ne'
    have := Nat.one_lt_two_pow hf
    omega
  set N : Subgroup S := Y.subgroupOf S with hNdef
  have hSN : S ≤ Subgroup.normalizer (Y : Set X) := hS.le.trans hYn
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hSN hx, Subgroup.le_normalizer hx⟩)
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hPne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : S) ∈ N := hx.2
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  have : Group.IsNilpotent S := hS.isPGroup.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  have hZ2 : IsPGroup 2 (N ⊓ Subgroup.center (↥S) : Subgroup (↥S)) :=
    hS.isPGroup.to_subgroup _
  obtain ⟨w, hw, hw2⟩ := exists_orderOf_eq_two hZ2 hZ
  refine ⟨w, hw.1, by rw [Subgroup.orderOf_coe, hw2], fun e he => ?_⟩
  have hc := Subgroup.mem_center_iff.mp hw.2 ⟨e, hES he⟩
  exact congrArg Subtype.val hc

end TwoGroups

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

@[expose] noncomputable def barEquiv {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) : P ≃* bar D P :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun p => ⟨toBar D ⟨p, hPH p.2⟩, toBar_mem_bar D (h := ⟨p, hPH p.2⟩) p.2⟩)
      (fun p q => Subtype.ext (map_mul (toBar D) ⟨p, hPH p.2⟩ ⟨q, hPH q.2⟩)))
    ⟨fun p q h => by
      have h' := toBar_injOn_of_isPGroup hP (u := ⟨p, hPH p.2⟩) (v := ⟨q, hPH q.2⟩) p.2 q.2
        (congrArg Subtype.val h)
      have h'' := congrArg Subtype.val h'
      exact Subtype.ext h'',
     fun x => by
      obtain ⟨h, hh, hx⟩ := (mem_bar_iff D P x).mp x.2
      exact ⟨⟨h, hh⟩, Subtype.ext hx⟩⟩

theorem barEquiv_apply {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) (p : P) :
    ((barEquiv hP hPH p : bar D P) : Bar D) = toBar D ⟨p, hPH p.2⟩ :=
  rfl

theorem isCyclic_bar_iff {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) : IsCyclic (bar D P) ↔ IsCyclic P :=
  ⟨isCyclic_of_equiv (barEquiv hP hPH).symm, isCyclic_of_equiv (barEquiv hP hPH)⟩

theorem lift_two_subgroup {W : Subgroup G} (hWH : W ≤ Subgroup.normalizer (D : Set G))
    {Pb : Subgroup (Bar D)} (hPb : IsPGroup 2 Pb) (hPW : Pb ≤ bar D W) :
    ∃ V : Subgroup G, V ≤ W ∧ IsPGroup 2 V ∧ bar D V = Pb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := W ⊓ (Pb.comap (toBar D)).map (Subgroup.normalizer (D : Set G)).subtype with hYdef
  have hYH : Y ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans hWH
  have hbarY : bar D Y = Pb := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff D Y x).mp hx
      obtain ⟨h', hh', hh'eq⟩ := hh.2
      have : h' = h := Subtype.ext hh'eq
      rw [← this]
      exact hh'
    · intro x hx
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff D W x).mp (hPW hx)
      exact toBar_mem_bar D ⟨hh, ⟨h, hx, rfl⟩⟩
  obtain ⟨V, hV⟩ := exists_isSylowOf 2 Y
  have hsyl := isSylowOf_bar (D := D) hV hYH
  rw [hbarY] at hsyl
  exact ⟨V, hV.le.trans inf_le_left, hV.isPGroup, (hsyl.eq_of_le hsyl.le le_rfl hPb).symm⟩

theorem bar_inf_centralizer {Y : Subgroup G} (hOY : aschbacherThm5Core D ≤ Y) {x : G}
    (hxH : x ∈ Subgroup.normalizer (D : Set G)) (hx : orderOf x = 2) :
    bar D (Y ⊓ Subgroup.centralizer ({x} : Set G)) =
      bar D Y ⊓ Subgroup.centralizer ({toBar D ⟨x, hxH⟩} : Set (Bar D)) := by
  apply le_antisymm
  · refine le_inf (bar_mono D inf_le_left) ?_
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_bar_iff D _ y).mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
  · rintro y ⟨hyY, hyC⟩
    have hu : orderOf (⟨x, hxH⟩ : Subgroup.normalizer (D : Set G)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hx
    have hcop := AschbacherToolkit.centralizer_quotient_odd (coreIn D) (coreIn_odd D) _ hu
    have hyC' : y ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (coreIn D) ⟨x, hxH⟩} : Set (Bar D)) := hyC
    rw [hcop] at hyC'
    obtain ⟨c, hc, rfl⟩ := hyC'
    obtain ⟨y₀, hy₀, hy₀c⟩ := (mem_bar_iff D Y _).mp hyY
    have hmem : (c : G)⁻¹ * y₀ ∈ aschbacherThm5Core D := by
      have h1 : toBar D (c⁻¹ * y₀) = 1 := by
        rw [map_mul, map_inv, hy₀c]
        exact inv_mul_cancel _
      exact (toBar_eq_one_iff D _).mp h1
    have hcY : (c : G) ∈ Y := by
      have := Y.mul_mem hy₀ (Y.inv_mem (hOY hmem))
      simpa [mul_assoc] using this
    have hcx : (c : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    exact toBar_mem_bar D (h := c) ⟨hcY, hcx⟩

omit [Finite G] in
theorem le_sup_core_of_bar_le {Y Z : Subgroup G} (hYH : Y ≤ Subgroup.normalizer (D : Set G))
    (h : bar D Y ≤ bar D Z) : Y ≤ Z ⊔ aschbacherThm5Core D := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := (mem_bar_iff D Z _).mp (h (toBar_mem_bar D (h := ⟨y, hYH hy⟩) hy))
  have hmem : (z : G)⁻¹ * y ∈ aschbacherThm5Core D := by
    have h1 : toBar D (z⁻¹ * ⟨y, hYH hy⟩) = 1 := by
      rw [map_mul, map_inv, hzy]
      exact inv_mul_cancel _
    exact (toBar_eq_one_iff D _).mp h1
  have := Subgroup.mul_mem_sup hz hmem
  simpa using this

end BarTools

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
