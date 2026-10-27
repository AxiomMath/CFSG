module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7Z

variable {Q : Type} [Group Q]

theorem centralizer_union_normal {A B : Subgroup Q}
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A)) :
    (Subgroup.centralizer ((A : Set Q) ∪ B)).Normal := by
  refine ⟨fun w hw q => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hconj : ∀ H : Subgroup Q, y ∈ H → q⁻¹ * y * q ∈ conjSub q⁻¹ H := fun H h => by
    have := conj_mem_conjSub (n := q⁻¹) h
    rwa [inv_inv] at this
  have hy' : q⁻¹ * y * q ∈ (A : Set Q) ∪ B := by
    rw [Set.mem_union, SetLike.mem_coe, SetLike.mem_coe] at hy ⊢
    rcases hperm q⁻¹ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with hy | hy
    · left; rw [← h1]; exact hconj A hy
    · right; rw [← h2]; exact hconj B hy
    · right; rw [← h1]; exact hconj A hy
    · left; rw [← h2]; exact hconj B hy
  have hc := Subgroup.mem_centralizer_iff.mp hw _ hy'
  calc y * (q * w * q⁻¹) = q * ((q⁻¹ * y * q) * w) * q⁻¹ := by group
    _ = q * (w * (q⁻¹ * y * q)) * q⁻¹ := by rw [hc]
    _ = q * w * q⁻¹ * y := by group

theorem mem_pCore_of_central_involution {M : Subgroup Q} (hMn : M.Normal) {x : Q} (hxM : x ∈ M)
    (hx2 : x * x = 1) (hcent : ∀ m ∈ M, m * x = x * m) : x ∈ CFSG.pCore 2 Q := by
  have hZ : Subgroup.zpowers (⟨x, hxM⟩ : ↥M) ≤ Subgroup.center ↥M :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hcent m m.2))
  have hle : Subgroup.zpowers (⟨x, hxM⟩ : ↥M) ≤ CFSG.pCore 2 ↥M :=
    le_sSup ⟨Subgroup.normal_of_le_center hZ,
      ExactLayer.isPGroup_zpowers_of_sq_eq_one (Subtype.ext hx2)⟩
  have := hMn
  have hle' : (CFSG.pCore 2 ↥M).map M.subtype ≤ CFSG.pCore 2 Q :=
    le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype⟩
  exact hle' ⟨⟨x, hxM⟩, hle (Subgroup.mem_zpowers _), rfl⟩

end F7Z


section E8ZO2

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_twin_perm (hc : P23Cfg n Y R S t K' W u e g) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y)) (q : ↥C ⧸ classicalInvolutionOddCore ↥C) :
    (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
        ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
      conjSub q ((K'.subgroupOf C).map (F7I.piC C)) = (K'.subgroupOf C).map (F7I.piC C)) ∨
    (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
        (K'.subgroupOf C).map (F7I.piC C) ∧
      conjSub q ((K'.subgroupOf C).map (F7I.piC C)) =
        ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
  subst hCdef
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore _) q
  change (conjSub (F7I.piC _ c) _ = _ ∧ conjSub (F7I.piC _ c) _ = _) ∨
    (conjSub (F7I.piC _ c) _ = _ ∧ conjSub (F7I.piC _ c) _ = _)
  rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
  rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
  · right; rw [h1, h2]; exact ⟨rfl, rfl⟩

theorem p23_mbar_normal (hc : P23Cfg n Y R S t K' W u e g) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y)) :
    (Subgroup.centralizer ((((tightCore R).subgroupOf C).map (F7I.piC C) :
      Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ∪ (K'.subgroupOf C).map (F7I.piC C))).Normal :=
  F7Z.centralizer_union_normal (p23_twin_perm hc hCdef)

theorem p23E8Z_e_mem_pCore_bar (hT : Thm4RTwinBelow 3 n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (heC : e ∈ Subgroup.centralizer ({t} : Set Y)) :
    F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ ∈
      CFSG.pCore 2 (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨-, -, -, -, -, -, -, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hMB := p23MBar_proved hcit hP Y R S t K' W u e g hc (R56.p23_zstar_cu hT hc hZ)
    ⟨e, heC⟩ rfl
  refine F7Z.mem_pCore_of_central_involution (p23_mbar_normal hc hCdef) ?_ ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    rintro a (ha | ha)
    · exact (heA a ha).symm
    · exact (heB a ha).symm
  · rw [← map_mul, show (⟨e, heC⟩ : ↥C) * ⟨e, heC⟩ = 1 from Subtype.ext hc.data.he2, map_one]
  · intro m hm
    rw [Subgroup.mem_centralizer_iff] at hm
    exact hMB m (fun a ha => (hm a (Or.inl ha)).symm) (fun a ha => (hm a (Or.inr ha)).symm)

theorem p23E8Z_e_mem_pCore (hT : Thm4RTwinBelow 3 n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hO : CFSG.ClassicalInvolution.Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    e ∈ (CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set Y))).map
      (Subgroup.centralizer ({t} : Set Y)).subtype := by
  have hd := hc.data
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW e (T7K.e_mem_inf hd).1 t hd.hzW)
  have hbar := p23E8Z_e_mem_pCore_bar hT hcit hP hc hZ heC
  set C := Subgroup.centralizer ({t} : Set Y)
  have hO' : classicalInvolutionOddCore ↥C = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hO
  have hinj : Function.Injective (F7I.piC C) := by
    rwa [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hle : (CFSG.pCore 2 (↥C ⧸ classicalInvolutionOddCore ↥C)).comap (F7I.piC C) ≤
      CFSG.pCore 2 ↥C :=
    le_sSup ⟨CFSG.pCore_normal.comap _, CFSG.pCore_isPGroup.comap_of_injective _ hinj⟩
  exact ⟨⟨e, heC⟩, hle (Subgroup.mem_comap.mpr hbar), rfl⟩

end E8ZO2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
