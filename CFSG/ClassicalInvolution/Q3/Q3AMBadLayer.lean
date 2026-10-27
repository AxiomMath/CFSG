module

public import CFSG.ClassicalInvolution.Q3.Q3CHLift
public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups

section Parity

theorem exists_fixed_of_involutive_odd {α : Type} [Finite α] (σ : α → α)
    (hσ : Function.Involutive σ) (hodd : Odd (Nat.card α)) : ∃ a, σ a = a := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End α := σ
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext a
    exact hσ a
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  by_contra hno
  push Not at hno
  have hempty : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨a, ha⟩ => hno a ha⟩
  rw [hempty] at h
  have h2 : 2 ∣ Fintype.card α := (Nat.modEq_zero_iff_dvd).mp h
  rw [← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

variable {G : Type} [Group G]

theorem exists_mul_centralizes_of_odd [Finite G] {s : G} (hs2 : s * s = 1) {O : Subgroup G}
    (hO : Odd (Nat.card O)) (hsO : ∀ o ∈ O, s * o * s⁻¹ ∈ O) {y : G}
    (hy : y⁻¹ * (s * y * s⁻¹) ∈ O) : ∃ o ∈ O, s * (y * o) * s⁻¹ = y * o := by
  set u : G := y⁻¹ * (s * y * s⁻¹) with hu
  have hss : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs2, inv_one]
  have key : s * u * s⁻¹ = (s * y * s⁻¹)⁻¹ * y := by
    calc s * u * s⁻¹ = (s * y⁻¹ * s⁻¹) * ((s * s) * y * (s⁻¹ * s⁻¹)) := by rw [hu]; group
      _ = (s * y * s⁻¹)⁻¹ * y := by rw [hs2, hss]; group
  have h1 : u * (s * u * s⁻¹) = 1 := by rw [key, hu]; group
  let φ : O → O := fun o => ⟨u * (s * o * s⁻¹), O.mul_mem hy (hsO o o.2)⟩
  have hφ : Function.Involutive φ := by
    intro o
    apply Subtype.ext
    show u * (s * (u * (s * (o : G) * s⁻¹)) * s⁻¹) = o
    calc u * (s * (u * (s * (o : G) * s⁻¹)) * s⁻¹)
        = (u * (s * u * s⁻¹)) * ((s * s) * (o : G) * (s⁻¹ * s⁻¹)) := by group
      _ = o := by rw [h1, hs2, hss]; group
  obtain ⟨o, ho⟩ := exists_fixed_of_involutive_odd φ hφ hO
  refine ⟨o, o.2, ?_⟩
  have h2 : u * (s * (o : G) * s⁻¹) = o := congrArg Subtype.val ho
  calc s * (y * o) * s⁻¹ = (s * y * s⁻¹) * (s * o * s⁻¹) := by group
    _ = y * (u * (s * o * s⁻¹)) := by rw [hu]; group
    _ = y * o := by rw [h2]

end Parity

section OddCore

variable {G : Type} [Group G]

theorem conj_mem_oddCoreOf_of_mem_normalizer {Y : Subgroup G} {g : G}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hg' : ∀ y ∈ Y, g⁻¹ * y * g ∈ Y) {o : G}
    (ho : o ∈ oddCoreOf Y) : g * o * g⁻¹ ∈ oddCoreOf Y := by
  let e : ↥Y ≃* ↥Y :=
    { toFun := fun y => ⟨g * y * g⁻¹, hg y y.2⟩
      invFun := fun y => ⟨g⁻¹ * y * g, hg' y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinv : (classicalInvolutionOddCore ↥Y).map e.toMonoidHom = classicalInvolutionOddCore ↥Y :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  obtain ⟨hoY, ho'⟩ := mem_oddCoreOf_iff.mp ho
  refine mem_oddCoreOf_iff.mpr ⟨hg o hoY, ?_⟩
  rw [← hinv]
  exact ⟨⟨o, hoY⟩, ho', rfl⟩

theorem mk'_eq_of_mul_inv_mem {Y : Subgroup G} {a b : G} (ha : a ∈ Y) (hb : b ∈ Y)
    (h : a * b⁻¹ ∈ oddCoreOf Y) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨a, ha⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨b, hb⟩ := by
  have h1 : a⁻¹ * b ∈ oddCoreOf Y := by
    have h2 := conj_mem_oddCoreOf_of_mem_normalizer (g := a⁻¹) (Y := Y)
      (fun y hy => Y.mul_mem (Y.mul_mem (Y.inv_mem ha) hy) (by simpa using ha))
      (fun y hy => Y.mul_mem (Y.mul_mem (by simpa using ha) hy) (Y.inv_mem ha))
      ((oddCoreOf Y).inv_mem h)
    have e : a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * b := by group
    rwa [e] at h2
  obtain ⟨hab, hmem⟩ := mem_oddCoreOf_iff.mp h1
  exact (QuotientGroup.eq).mpr hmem

theorem inv_mul_mem_of_mk'_eq {Y : Subgroup G} {a b : G} (ha : a ∈ Y) (hb : b ∈ Y)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨a, ha⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨b, hb⟩) : a⁻¹ * b ∈ oddCoreOf Y := by
  have h1 := (QuotientGroup.eq).mp h
  exact mem_oddCoreOf_iff.mpr ⟨Y.mul_mem (Y.inv_mem ha) hb, h1⟩

theorem inf_le_oddCoreOf_of_normalized [Finite G] {X Y : Subgroup G} (hX : Odd (Nat.card X))
    (hn : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) : X ⊓ Y ≤ oddCoreOf Y := by
  have hN : ((X ⊓ Y).subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact ⟨hn k hk h hh.1, Y.mul_mem (Y.mul_mem hk hh.2) (Y.inv_mem hk)⟩
  have hcard : Nat.card ((X ⊓ Y).subgroupOf Y) = Nat.card ↥(X ⊓ Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hodd : Odd (Nat.card ((X ⊓ Y).subgroupOf Y)) := by
    rw [hcard]
    exact hX.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hle : (X ⊓ Y).subgroupOf Y ≤ classicalInvolutionOddCore ↥Y := le_sSup ⟨hN, hodd⟩
  intro x hx
  exact mem_oddCoreOf_iff.mpr ⟨hx.2, hle (show (⟨x, hx.2⟩ : ↥Y) ∈ (X ⊓ Y).subgroupOf Y from hx)⟩

end OddCore

section Layer

variable {G : Type} [Group G] [Finite G]

theorem exists_layer_of_action {Y : Subgroup G} {z s w : G} (hz : orderOf z = 2)
    (hYC : Y ≤ Subgroup.centralizer ({z} : Set G))
    (hN : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hzY : z ∈ Y) (hwY : w ∈ Y) (hw : w * w = z) (hsz : s * z = z * s) (hs2 : s * s = 1)
    (hact : ∀ y ∈ Y, s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf Y)
    {Lb : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)}
    (hLc : Lb ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)))
    (hLn : ∀ x ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb)
    (hub : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩ ∈ Lb)
    (hLiso : Nonempty (↥Lb ≃* SL(2, ZMod 3))) :
    ∃ L : Subgroup G, IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L z := by
  classical
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set ub := π ⟨w, hwY⟩ with hub'
  have hsC : s ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsz
  have hNs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := hN s hsC
  have hNs' : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y := fun y hy => by
    simpa using hN s⁻¹ (Subgroup.inv_mem _ hsC) y hy
  have hsO : ∀ o ∈ oddCoreOf Y, s * o * s⁻¹ ∈ oddCoreOf Y := fun o ho =>
    conj_mem_oddCoreOf_of_mem_normalizer hNs hNs' ho
  have hπs : ∀ (y : G) (hy : y ∈ Y) (hy' : s * y * s⁻¹ ∈ Y), π ⟨s * y * s⁻¹, hy'⟩ =
      ub * π ⟨y, hy⟩ * ub⁻¹ := by
    intro y hy hy'
    have hwy : w * y * w⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hwY hy) (Y.inv_mem hwY)
    have h1 := mk'_eq_of_mul_inv_mem hy' hwy (hact y hy)
    rw [h1]
    have : (⟨w * y * w⁻¹, hwy⟩ : ↥Y) = ⟨w, hwY⟩ * ⟨y, hy⟩ * ⟨w, hwY⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hlift : ∀ b ∈ Lb, ∃ x : ↥Y, (x : G) ∈ Subgroup.centralizer ({s} : Set G) ∧ π x = b := by
    intro b hb
    obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) b
    have hsy : s * (y₀ : G) * s⁻¹ ∈ Y := hNs _ y₀.2
    have hbc : b * ub = ub * b := Subgroup.mem_centralizer_singleton_iff.mp (hLc hb)
    have h1 : π ⟨s * (y₀ : G) * s⁻¹, hsy⟩ = π y₀ := by
      rw [hπs _ y₀.2 hsy]
      have h0 : π ⟨(y₀ : G), y₀.2⟩ = b := hy₀
      rw [h0, ← hbc]
      group
    have h2 : (y₀ : G)⁻¹ * (s * (y₀ : G) * s⁻¹) ∈ oddCoreOf Y :=
      inv_mul_mem_of_mk'_eq y₀.2 hsy h1.symm
    obtain ⟨o, ho, hfix⟩ := exists_mul_centralizes_of_odd hs2 (oddCoreOf_odd_natCard Y) hsO h2
    have hoY : o ∈ Y := oddCoreOf_le_self Y ho
    obtain ⟨hoY', ho'⟩ := mem_oddCoreOf_iff.mp ho
    refine ⟨⟨(y₀ : G) * o, Y.mul_mem y₀.2 hoY⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show (y₀ : G) * o * s = s * ((y₀ : G) * o)
      have := hfix
      calc (y₀ : G) * o * s = (s * ((y₀ : G) * o) * s⁻¹) * s := by rw [this]
        _ = s * ((y₀ : G) * o) := by group
    · have hπo : π ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ho'
      have : (⟨(y₀ : G) * o, Y.mul_mem y₀.2 hoY⟩ : ↥Y) = y₀ * ⟨o, hoY⟩ := rfl
      rw [this, map_mul, hπo, mul_one, hy₀]
  let Lx : Subgroup ↥Y :=
    (Subgroup.centralizer ({s} : Set G)).subgroupOf Y ⊓ Lb.comap π
  have hmemLx : ∀ x : ↥Y, x ∈ Lx ↔ (x : G) ∈ Subgroup.centralizer ({s} : Set G) ∧ π x ∈ Lb :=
    fun x => Iff.rfl
  set L : Subgroup G := Lx.map Y.subtype with hL
  have hLY : ∀ y ∈ L, y ∈ Y ∧ y ∈ Subgroup.centralizer ({s} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, ((hmemLx x).mp hx).1⟩
  set R : Subgroup G := Y ⊓ Subgroup.centralizer ({s} : Set G) with hR
  have hLR : L ≤ R := fun y hy => hLY y hy
  have hRT : R ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) :=
    fun y hy => ⟨hYC hy.1, hy.2⟩
  have hcent : ∀ k : ↥Y, (k : G) ∈ Subgroup.centralizer ({s} : Set G) →
      π k ∈ Subgroup.centralizer ({ub} : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)) := by
    intro k hk
    have hks : s * (k : G) * s⁻¹ = k := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hk
      rw [← this]
      group
    have hsy : s * (k : G) * s⁻¹ ∈ Y := hNs _ k.2
    have h1 := hπs (k : G) k.2 hsy
    have h2 : π ⟨s * (k : G) * s⁻¹, hsy⟩ = π k := by
      congr 1
      exact Subtype.ext hks
    rw [h2] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc π k * ub = (ub * π k * ub⁻¹) * ub := by rw [← h1]
      _ = ub * π k := by group
  refine ⟨L, ?_⟩
  refine
    { le := fun y hy => (hLY y hy).2
      orderOf_eq_two := hz
      mem := ?_
      subnormal := ?_
      nonempty_equiv := ?_ }
  · refine ⟨⟨z, hzY⟩, (hmemLx _).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm, ?_⟩, rfl⟩
    have : (⟨z, hzY⟩ : ↥Y) = ⟨w, hwY⟩ * ⟨w, hwY⟩ := Subtype.ext hw.symm
    rw [this, map_mul]
    exact hub
  · refine IsSubnormal.step hLR ?_ (IsSubnormal.step hRT ?_ (IsSubnormal.refl _))
    · rw [Subgroup.normal_subgroupOf_iff hLR]
      rintro _ k ⟨x, hx, rfl⟩ hk
      have hkY : k ∈ Y := hk.1
      have hkx : (⟨k, hkY⟩ * x * ⟨k, hkY⟩⁻¹ : ↥Y) ∈ Lx := by
        refine (hmemLx _).mpr ⟨?_, ?_⟩
        · have hxc : (x : G) ∈ Subgroup.centralizer ({s} : Set G) := ((hmemLx x).mp hx).1
          exact (Subgroup.centralizer ({s} : Set G)).mul_mem
            ((Subgroup.centralizer ({s} : Set G)).mul_mem hk.2 hxc)
            ((Subgroup.centralizer ({s} : Set G)).inv_mem hk.2)
        · rw [map_mul, map_mul, map_inv]
          exact hLn _ (hcent ⟨k, hkY⟩ hk.2) _ ((hmemLx x).mp hx).2
      exact ⟨_, hkx, rfl⟩
    · rw [Subgroup.normal_subgroupOf_iff hRT]
      intro h k hh hk
      exact ⟨hN k hk.1 h hh.1, (Subgroup.centralizer ({s} : Set G)).mul_mem
        ((Subgroup.centralizer ({s} : Set G)).mul_mem hk.2 hh.2)
        ((Subgroup.centralizer ({s} : Set G)).inv_mem hk.2)⟩
  · obtain ⟨e⟩ := hLiso
    let φ0 : ↥Lx →* (↥Y ⧸ classicalInvolutionOddCore ↥Y) := π.comp Lx.subtype
    let φ : ↥Lx →* Lb := φ0.codRestrict Lb (fun x => ((hmemLx x.1).mp x.2).2)
    have hφ : Function.Surjective φ := by
      rintro ⟨b, hb⟩
      obtain ⟨x, hxc, hxb⟩ := hlift b hb
      exact ⟨⟨x, (hmemLx x).mpr ⟨hxc, by rw [hxb]; exact hb⟩⟩, Subtype.ext hxb⟩
    have hodd : Odd (Nat.card φ.ker) := by
      have hle : φ.ker.map Lx.subtype ≤ classicalInvolutionOddCore ↥Y := by
        rintro _ ⟨x, hx, rfl⟩
        have h1 : π (x : ↥Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact (QuotientGroup.ker_mk' _).le (MonoidHom.mem_ker.mpr h1)
      have hc : Nat.card (φ.ker.map Lx.subtype) = Nat.card φ.ker :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [← hc]
      exact (CFSG.ComponentClassification.OddCore.odd_card ↥Y).of_dvd_nat
        (Subgroup.card_dvd_of_le hle)
    obtain ⟨e'⟩ := nonempty_equiv_quotient_of_odd_ker φ hφ hodd e
    have iL : ↥Lx ≃* ↥L :=
      Subgroup.equivMapOfInjective Lx Y.subtype (Subgroup.subtype_injective Y)
    have hOL : (classicalInvolutionOddCore ↥Lx).map iL.toMonoidHom =
        classicalInvolutionOddCore ↥L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant iL
    exact ⟨((QuotientGroup.congr _ _ iL hOL).symm).trans e'⟩

end Layer

end CFSG.ClassicalInvolution.Q3.Q3AM
