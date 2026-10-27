module

public import CFSG.ClassicalInvolution.Q3.TL4ConnMu
public import CFSG.ClassicalInvolution.Q3.TL4Conn274B
public import CFSG.ClassicalInvolution.Q3.TL4Conn274A
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section FStar

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem genFittingFitting_le_center_of_selfGen (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hE2 : ¬ TightInO2 t) : genFittingFitting Y ≤ Subgroup.center Y := by
  have hFn : (genFittingFitting Y).Normal := genFittingFitting_normal
  have hF2 : IsPGroup 2 ↥(genFittingFitting Y) := isPGroup_two_genFittingFitting hO
  have htF : t ∉ genFittingFitting Y := fun h => hE2 ⟨_, hFn, hF2, h⟩
  have htop : Subgroup.centralizer (genFittingFitting Y : Set Y) = ⊤ :=
    hd.eq_top_of_conj hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ genFittingFitting Y := by simpa using hFn.conj_mem p hp y⁻¹
      have := hd.commute_of_normal_two hFn hF2 htF hx hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [← this]
        _ = x * p := by group
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (genFittingFitting Y : Set Y) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm

theorem center_genFittingFStar_le_of_selfGen (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (hO : TightOddFree Y) (hE2 : ¬ TightInO2 t) :
    (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype ≤
      Subgroup.center Y := by
  set F : Subgroup Y := genFittingFStar Y with hF
  have hFn : F.Normal := genFittingFStar_normal Y
  set Z : Subgroup Y := (Subgroup.center ↥F).map F.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz y => ?_⟩
    obtain ⟨c, hc'', rfl⟩ := hz
    have hc' : c ∈ Subgroup.center ↥F := hc''
    refine ⟨⟨y * c * y⁻¹, hFn.conj_mem _ c.2 y⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro f
    apply Subtype.ext
    have hf : y⁻¹ * (f : Y) * y ∈ F := by simpa using hFn.conj_mem _ f.2 y⁻¹
    have h' : y⁻¹ * (f : Y) * y * (c : Y) = (c : Y) * (y⁻¹ * (f : Y) * y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨_, hf⟩)
    show (f : Y) * (y * c * y⁻¹) = y * c * y⁻¹ * f
    calc (f : Y) * (y * c * y⁻¹) = y * ((y⁻¹ * f * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * f * y)) * y⁻¹ := by rw [h']
      _ = y * c * y⁻¹ * f := by group
  have hZcomm : ∀ a b : ↥Z, a * b = b * a := by
    rintro ⟨a, c₁, hc₁, rfl⟩ ⟨b, c₂, hc₂, rfl⟩
    apply Subtype.ext
    show (c₁ : Y) * c₂ = c₂ * c₁
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₁ c₂).symm
  have hZnil : Group.IsNilpotent ↥Z := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥Z →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hZcomm w z
  exact (le_sSup ⟨hZn, hZnil⟩ : Z ≤ genFittingFitting Y).trans
    (genFittingFitting_le_center_of_selfGen hd hgen hO hE2)

end FStar

section Cit3


variable {r n : ℕ}

theorem TightLargeHypR.isSimpleGroup_genFittingFStar {Y : Type} [Group Y] [Finite Y]
    {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y} (hL : TightLargeHypR r n Y Rd Sd z) :
    IsSimpleGroup ↥(genFittingFStar Y) ∧ (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) ∧
      Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ := by
  have hZ : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
    have h := center_genFittingFStar_le_of_selfGen hL.datum hL.cls.2.1 hL.cls.2.2 hL.notInO2
    rwa [hL.center, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar Y).subtype_injective] at h
  have hq : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y) := hL.fstar
  have hsq : IsSimpleGroup (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) := hq.2
  have hs : IsSimpleGroup ↥(genFittingFStar Y) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hcomm : commutator ↥(genFittingFStar Y) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hab y x
    obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(genFittingFStar Y)
    have h1 : ∀ w : ↥(genFittingFStar Y), w = 1 := by
      intro w
      have : w ∈ commutator ↥(genFittingFStar Y) := by
        rw [hq.1]
        exact Subgroup.mem_top w
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    exact hxy ((h1 x).trans (h1 y).symm)
  exact ⟨hs, hnab, centralizer_genFittingFStar_eq_bot hnab⟩

@[expose] def TightC27_4MR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ∀ S₂ : Sylow 2 Y, R ≤ (S₂ : Subgroup Y) →
          8 ≤ Nat.card {X : Subgroup Y //
            X ∈ RSet (CoreAssembly.conjClass (tightCore Rd)) ∧ X ≤ (S₂ : Subgroup Y)} →
            ∀ x : Y, x ∈ (S₂ : Subgroup Y) → x * x = 1 → x ≠ 1 →
              (∀ X ∈ RSet (CoreAssembly.conjClass (tightCore Rd)), X ≤ (S₂ : Subgroup Y) →
                ∀ y ∈ X, x * y = y * x) →
                Subgroup.centralizer ({x} : Set Y) ≤
                  H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z

@[expose] def TightC27_4aR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        FixesUniqueCoset (z * t) (H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z)

theorem tightC27_4aR_of_min (h2 : TightC27_2R r n) (hmin : TightC27_4MR r n) :
    TightC27_4aR r n :=
  fun Y _ _ Rd Sd z J S R T W t hs hdisc =>
    fixesUniqueCoset_zt_of_min hs.toStd8Core (h2 Y Rd Sd z J S R T W t hs hdisc)
      (hmin Y Rd Sd z J S R T W t hs hdisc)

@[expose] def TightC27_4R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z = ⊤

open CFSG.StronglyEmbedded.UniqueCoset CFSG.GH74.Uniqueness in
theorem tightC27_4R_of (h2 : TightC27_2R r n) (h4a : TightC27_4aR r n)
    (hB : TightBenderEndR) : TightC27_4R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc
  have hcomp := h2 Y Rd Sd z J S R T W t hs hdisc
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : Y ⧸ H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
      z • c = c := fixesUniqueCoset_z hs.toStd8Core hcomp
  have h2' : ∀ g : Y, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : Y ⧸ H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
        (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne hcomm
    rcases isConj_or_mem_omegaNbr_gen hs.hyp hs.mem (hs.large.datum.aEmpty _ hs.mem)
      hs.noTwins hz hne hcomm with hconj | hnbr
    · exact existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ (tightCore Rd)) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := TightLargeHypR.exists_std8 hs.large hnbr hb
      exact h4a Y Rd Sd z _ S' R' T' W' _ hstd hdisc
  obtain ⟨hFs, hFnab, hFc⟩ := TightLargeHypR.isSimpleGroup_genFittingFStar hs.large
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hTnab : ∃ x ∈ genFittingFStar Y, ∃ y ∈ genFittingFStar Y, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hFnab
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  obtain ⟨hLF, hLB, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz2 hFs hTnab hFc
    (L := Subgroup.closure (conjugatesOf z)) rfl
    (S_ZD_unconditional Y (conjugatesOf z) _ (isInvariantInvolutionSet hz2)
      (isProductDisconnected hH hz2 h1 h2'))
  exact hB Y Rd Sd z hs.large.datum (hLF ▸ hLB) hFc

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
