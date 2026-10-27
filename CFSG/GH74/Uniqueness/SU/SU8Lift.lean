module

public import CFSG.GH74.Uniqueness.SU.SU8LocA
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.LocA
open scoped commutatorElement

namespace Lift

variable {X : Type} [Group X] [Finite X] {O L A : Subgroup X} [O.Normal] [L.Normal] {n i e : ℕ}

structure LiftHyp (O L A : Subgroup X) [O.Normal] [L.Normal] (n i e : ℕ) : Prop where
  odd : Odd (Nat.card O)
  exp : ∀ a ∈ A, a * a = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  split : ∀ a ∈ A, ∃ l ∈ L, ∃ c : X, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c
  omega : ∃ S : Sylow 2 X, ∀ s ∈ (S : Subgroup X) ⊓ L, s * s = 1 → s ∈ A
  bender : BenderType ↥(L.map (QuotientGroup.mk' O)) n i e

theorem exists_sylow_image (S : Sylow 2 X) :
    ∃ P : Sylow 2 ↥(L.map (QuotientGroup.mk' O)), ∀ g : ↥(L.map (QuotientGroup.mk' O)),
      g ∈ (P : Subgroup ↥(L.map (QuotientGroup.mk' O))) ↔
        ∃ s ∈ (S : Subgroup X) ⊓ L, (g : X ⧸ O) = QuotientGroup.mk' O s := by
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal S (N := L)
  let φ : ↥L →* ↥(L.map (QuotientGroup.mk' O)) :=
    ((QuotientGroup.mk' O).comp L.subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  refine ⟨Q.mapSurjective hφ, fun g => ?_⟩
  rw [Sylow.coe_mapSurjective hφ Q]
  constructor
  · intro hg
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨(q : X), ?_, rfl⟩
    have hq' : q ∈ (Q : Subgroup ↥L) := hq
    rw [hQ] at hq'
    exact Subgroup.mem_subgroupOf.mp hq'
  · rintro ⟨s, hs, hsg⟩
    refine Subgroup.mem_map.mpr ⟨⟨s, hs.2⟩, ?_, Subtype.ext hsg.symm⟩
    show (⟨s, hs.2⟩ : ↥L) ∈ (Q : Subgroup ↥L)
    rw [hQ]
    exact Subgroup.mem_subgroupOf.mpr hs

theorem LiftHyp.locHyp (h : LiftHyp O L A n i e) :
    LocHyp (L.map (QuotientGroup.mk' O)) (A.map (QuotientGroup.mk' O)) n i e := by
  refine LocHyp.of_benderType h.bender ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, h.exp a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.comm a ha b hb]
  · obtain ⟨S, hS⟩ := h.omega
    obtain ⟨P, hP⟩ := exists_sylow_image (O := O) (L := L) S
    refine ⟨P, fun g hg hgg => ?_⟩
    obtain ⟨s, hs, hsg⟩ := (hP g).mp hg
    have hss1 : QuotientGroup.mk' O (s * s) = 1 := by
      rw [map_mul, ← hsg]
      have := congrArg Subtype.val hgg
      simpa using this
    have hssO : s * s ∈ O := (QuotientGroup.eq_one_iff _).mp hss1
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs.1⟩
    have hk' : (s * s) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
      calc (s * s) ^ (2 ^ k) = (s ^ (2 ^ k)) ^ 2 := by
            rw [← sq, ← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [this]; simp
    have hss : s * s = 1 := eq_one_of_mem_odd h.odd hssO hk'
    have hsA := hS s hs hss
    rw [hsg]
    exact ⟨s, hsA, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨l, hl, c, hc, rfl⟩ := h.split a ha
    refine ⟨QuotientGroup.mk' O l, ⟨l, hl, rfl⟩, QuotientGroup.mk' O c, ?_, by rw [map_mul]⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    have := hc m hm
    have h1 : QuotientGroup.mk' O ⁅c, m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr this
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem LiftHyp.split_lift (h : LiftHyp O L A n i e) {Y : Subgroup (X ⧸ O)}
    (hY : LocOut (L.map (QuotientGroup.mk' O)) (A.map (QuotientGroup.mk' O)) Y n) :
    ∀ a ∈ A, ∃ l ∈ A ⊓ L, ∃ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c := by
  intro a ha
  obtain ⟨u, hu, c', hc', hac⟩ := hY.split (QuotientGroup.mk' O a) ⟨a, ha, rfl⟩
  obtain ⟨l₀, hl₀A, rfl⟩ := (Subgroup.mem_inf.mp hu).1
  have hl₀K := (Subgroup.mem_inf.mp hu).2
  obtain ⟨c₀, hc₀A, rfl⟩ := (Subgroup.mem_inf.mp hc').1
  have hc₀C := (Subgroup.mem_inf.mp hc').2
  have hl₀L : l₀ ∈ L :=
    mem_of_mk_mem_map h.odd (k := 1) (by simpa [pow_one, sq] using h.exp l₀ hl₀A) hl₀K
  have hae : a = l₀ * c₀ := by
    refine mk_inj_of_exp_two h.odd h.exp ha (A.mul_mem hl₀A hc₀A) ?_
    rw [map_mul]; exact hac
  refine ⟨l₀, ⟨hl₀A, hl₀L⟩, c₀, hc₀A, fun m hm => ?_, hae⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hc₀C (QuotientGroup.mk' O m) ⟨m, hm, rfl⟩
  have h2 : QuotientGroup.mk' O ⁅c₀, m⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]; exact h1.symm
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem LiftHyp.lift_normalizer (h : LiftHyp O L A n i e)
    (hsplit : ∀ a ∈ A, ∃ l ∈ A ⊓ L, ∃ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c)
    {y : X ⧸ O} (hyK : y ∈ L.map (QuotientGroup.mk' O))
    (hyN : y ∈ normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O))) :
    ∃ g ∈ L ⊓ normalizer (A : Set X), QuotientGroup.mk' O g = y := by
  obtain ⟨m₀, hm₀, rfl⟩ := hyK
  have hmA : ∀ a ∈ A, m₀⁻¹ * a * m₀ ∈ A ⊔ O := by
    intro a ha
    have h1 : (QuotientGroup.mk' O m₀)⁻¹ * QuotientGroup.mk' O a * QuotientGroup.mk' O m₀ ∈
        A.map (QuotientGroup.mk' O) := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hyN)
        (QuotientGroup.mk' O a)).mp ⟨a, ha, rfl⟩
      simpa using this
    obtain ⟨a', ha', h'⟩ := h1
    have h2 : a'⁻¹ * (m₀⁻¹ * a * m₀) ∈ O :=
      QuotientGroup.eq.mp (by simpa [map_mul, map_inv] using h')
    have e : m₀⁻¹ * a * m₀ = a' * (a'⁻¹ * (m₀⁻¹ * a * m₀)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ha' h2
  obtain ⟨r, hr, hrN⟩ := exists_mul_mem_normalizer h.odd h.exp hsplit hm₀ hmA
  have hr1 : QuotientGroup.mk' O r = 1 := (QuotientGroup.eq_one_iff r).mpr hr.2
  exact ⟨m₀ * r, ⟨L.mul_mem hm₀ hr.1, hrN⟩, by rw [map_mul, hr1, mul_one]⟩

structure LiftOut (O L A : Subgroup X) [O.Normal] [L.Normal] (n : ℕ) : Prop where
  two_le : 2 ≤ n
  card_AL : Nat.card ↥(A ⊓ L) = 2 ^ n
  split : ∀ a ∈ A, ∃ l ∈ A ⊓ L, ∃ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c
  inf_bot : ∀ x ∈ A ⊓ L, (∀ m ∈ L, ⁅x, m⁆ ∈ O) → x = 1
  act_C : ∀ g ∈ L ⊓ normalizer (A : Set X), ∀ c ∈ A, (∀ m ∈ L, ⁅c, m⁆ ∈ O) → g * c * g⁻¹ = c
  trans : ∀ u ∈ A ⊓ L, u ≠ 1 → ∀ v ∈ A ⊓ L, v ≠ 1 →
    ∃ g ∈ L ⊓ normalizer (A : Set X), g * u * g⁻¹ = v
  cyclic : ∃ g₀ ∈ L ⊓ normalizer (A : Set X),
    (∀ g ∈ L ⊓ normalizer (A : Set X), ∃ j : ℤ, ∀ a ∈ A, g * a * g⁻¹ = g₀ ^ j * a * (g₀ ^ j)⁻¹) ∧
    ∃ k : ℕ, Odd k ∧ ∀ a ∈ A, g₀ ^ k * a * (g₀ ^ k)⁻¹ = a
  free : ∀ g ∈ L ⊓ normalizer (A : Set X), ∀ u ∈ A ⊓ L, u ≠ 1 → g * u * g⁻¹ = u →
    ∀ a ∈ A, g * a * g⁻¹ = a

theorem LiftHyp.out (h : LiftHyp O L A n i e) : LiftOut O L A n := by
  have hloc := h.locHyp
  obtain ⟨Y, hY⟩ := hloc.exists_out
  have hsplit := h.split_lift hY
  have hbarN : ∀ g ∈ L ⊓ normalizer (A : Set X), QuotientGroup.mk' O g ∈
      L.map (QuotientGroup.mk' O) ∧ QuotientGroup.mk' O g ∈
        normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
    intro g hg
    refine ⟨⟨g, hg.1, rfl⟩, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg.2 a).mp ha, by simp [map_mul]⟩
    · rintro ⟨a, ha, hax⟩
      refine ⟨g⁻¹ * a * g, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hg.2 _).mpr (by simpa [mul_assoc] using ha)
      · rw [map_mul, map_mul, map_inv, hax]; group
  have hconj : ∀ g ∈ L ⊓ normalizer (A : Set X), ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp hg.2 a).mp ha
  have hbarA : ∀ a ∈ A, a ≠ 1 → QuotientGroup.mk' O a ≠ 1 := fun a ha ha1 h1 =>
    ha1 (mk_inj_of_exp_two h.odd h.exp ha A.one_mem (by rw [h1, map_one]))
  refine ⟨hloc.two_le, ?_, hsplit, ?_, ?_, ?_, ?_, ?_⟩
  · have hcard : Nat.card ↥(A ⊓ L) =
        Nat.card ↥(A.map (QuotientGroup.mk' O) ⊓ L.map (QuotientGroup.mk' O)) := by
      apply Nat.card_congr
      refine Equiv.ofBijective (fun x => ⟨QuotientGroup.mk' O x.1,
        Subgroup.mem_inf.mpr ⟨⟨x.1, x.2.1, rfl⟩, ⟨x.1, x.2.2, rfl⟩⟩⟩) ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact mk_inj_of_exp_two h.odd h.exp x.2.1 y.2.1 (congrArg Subtype.val hxy)
      · rintro ⟨u, hu⟩
        obtain ⟨⟨a, ha, rfl⟩, hK⟩ := Subgroup.mem_inf.mp hu
        have haL : a ∈ L :=
          mem_of_mk_mem_map h.odd (k := 1) (by simpa [pow_one, sq] using h.exp a ha) hK
        exact ⟨⟨a, Subgroup.mem_inf.mpr ⟨ha, haL⟩⟩, rfl⟩
    rw [hcard]; exact hY.card_Z
  · intro x hx0 hx
    have hxK : QuotientGroup.mk' O x ∈ L.map (QuotientGroup.mk' O) :=
      ⟨x, (Subgroup.mem_inf.mp hx0).2, rfl⟩
    have hxc : QuotientGroup.mk' O x ∈
        centralizer ((L.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, hm, rfl⟩
      have h2 : QuotientGroup.mk' O ⁅x, m⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hx m hm)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2.symm
    have h1 := hloc.eq_one_of_mem_centralizer hxK hxc
    exact eq_one_of_mem_odd h.odd ((QuotientGroup.eq_one_iff x).mp h1) (k := 1)
      (by simpa [pow_one, sq] using h.exp x (Subgroup.mem_inf.mp hx0).1)
  · intro g hg c hcA hc
    have hd : g * c * g⁻¹ ∈ A := hconj g hg c hcA
    have h1 : ⁅c, g⁆ ∈ O := hc g hg.1
    have h2 : (g * c * g⁻¹) * c⁻¹ ∈ O := by
      have : (g * c * g⁻¹) * c⁻¹ = ⁅g, c⁆ := by simp [commutatorElement_def, mul_assoc]
      rw [this, ← commutatorElement_inv]
      exact O.inv_mem h1
    have h3 : (g * c * g⁻¹) * c⁻¹ = 1 := by
      refine eq_one_of_mem_odd h.odd h2 (k := 1) ?_
      have hm : (g * c * g⁻¹) * c⁻¹ ∈ A := A.mul_mem hd (A.inv_mem hcA)
      simpa [pow_one, sq] using h.exp _ hm
    exact mul_inv_eq_one.mp h3
  · intro u hu hu1 v hv hv1
    have hbu : QuotientGroup.mk' O u ∈
        A.map (QuotientGroup.mk' O) ⊓ L.map (QuotientGroup.mk' O) :=
      Subgroup.mem_inf.mpr ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
    have hbv : QuotientGroup.mk' O v ∈
        A.map (QuotientGroup.mk' O) ⊓ L.map (QuotientGroup.mk' O) :=
      Subgroup.mem_inf.mpr ⟨⟨v, hv.1, rfl⟩, ⟨v, hv.2, rfl⟩⟩
    obtain ⟨y, hyY, hyuv⟩ := hY.trans _ hbu (hbarA u hu.1 hu1) _ hbv (hbarA v hv.1 hv1)
    obtain ⟨g, hg, hgy⟩ := h.lift_normalizer hsplit (hY.le hyY) (hY.norm hyY)
    refine ⟨g, hg, ?_⟩
    refine mk_inj_of_exp_two h.odd h.exp (hconj g hg u hu.1) hv.1 ?_
    rw [map_mul, map_mul, map_inv, hgy]; exact hyuv
  · have : IsCyclic ↥Y := hY.cyclic
    obtain ⟨y₀, hy₀⟩ := IsCyclic.exists_generator (α := ↥Y)
    obtain ⟨g₀, hg₀, hg₀y⟩ := h.lift_normalizer hsplit (hY.le y₀.2) (hY.norm y₀.2)
    refine ⟨g₀, hg₀, fun g hg => ?_, Nat.card ↥Y, hY.odd, ?_⟩
    · obtain ⟨hgK, hgN⟩ := hbarN g hg
      obtain ⟨y, hyY, hact⟩ := hY.action _ hgK hgN
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hy₀ ⟨y, hyY⟩)
      have hjy : (QuotientGroup.mk' O g₀) ^ j = y := by
        rw [hg₀y]; exact congrArg Subtype.val hj
      refine ⟨j, fun a ha => ?_⟩
      have hg₀j : g₀ ^ j ∈ L ⊓ normalizer (A : Set X) := zpow_mem hg₀ j
      refine mk_inj_of_exp_two h.odd h.exp (hconj g hg a ha) (hconj _ hg₀j a ha) ?_
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_zpow, hjy]
      exact hact _ ⟨a, ha, rfl⟩
    · intro a ha
      have hg₀k : g₀ ^ Nat.card ↥Y ∈ L ⊓ normalizer (A : Set X) := pow_mem hg₀ _
      refine mk_inj_of_exp_two h.odd h.exp (hconj _ hg₀k a ha) ha ?_
      have : (QuotientGroup.mk' O g₀) ^ Nat.card ↥Y = 1 := by
        rw [hg₀y]
        have := pow_card_eq_one' (G := ↥Y) (x := y₀)
        exact congrArg Subtype.val this
      rw [map_mul, map_mul, map_inv, map_pow, this]; simp
  · intro g hg u hu hu1 hgu a ha
    obtain ⟨hgK, hgN⟩ := hbarN g hg
    obtain ⟨y, hyY, hact⟩ := hY.action _ hgK hgN
    have hbu : QuotientGroup.mk' O u ∈
        A.map (QuotientGroup.mk' O) ⊓ L.map (QuotientGroup.mk' O) :=
      Subgroup.mem_inf.mpr ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
    have hy1 : y = 1 := by
      by_contra hy1
      refine hY.free y hyY hy1 _ hbu (hbarA u hu.1 hu1) ?_
      rw [← hact _ ⟨u, hu.1, rfl⟩, ← map_inv, ← map_mul, ← map_mul, hgu]
    refine mk_inj_of_exp_two h.odd h.exp (hconj g hg a ha) ha ?_
    rw [map_mul, map_mul, map_inv, hact _ ⟨a, ha, rfl⟩, hy1]; simp

end Lift

end CFSG.GH74.Uniqueness.SU.SU8
