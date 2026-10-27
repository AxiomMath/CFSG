module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Abstract

variable {A B : Type} [Group A] [Group B] {ρ : A →* B}

theorem a6c_cover_layer_map [Finite A] (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal]
    (hE : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a) (hev : 2 ∣ Nat.card ↥E)
    (h2 : IsPGroup 2 (B ⧸ E)) : (CFSG.layer A).map ρ = E := by
  haveI : Finite B := Finite.of_surjective ρ hρ.surjective
  obtain ⟨hLBE, -⟩ := ff_layer_ffX_eq_of_normal_simple E hE hnc hev h2
  haveI hLAperf : Group.IsPerfect ↥(CFSG.layer A) := CFSG.LocalCores.layer_isPerfect
  apply le_antisymm
  · haveI : Group.IsPerfect ↥((CFSG.layer A).map ρ) := Group.IsPerfect.map (f := ρ)
    exact ff_perfect_le_of_quot_two E h2 ((CFSG.layer A).map ρ) inferInstance
  · have h := hρ.layer_le_map_layer
    rwa [hLBE] at h

theorem a6c_perfect_le_layer [Finite A] (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal]
    (hmap : (CFSG.layer A).map ρ = E) (h2 : IsPGroup 2 (B ⧸ E)) (X : Subgroup A)
    (hX : Group.IsPerfect ↥X) : X ≤ CFSG.layer A := by
  haveI := hX
  haveI : Finite B := Finite.of_surjective ρ hρ.surjective
  have hXE : X.map ρ ≤ E := by
    haveI : Group.IsPerfect ↥(X.map ρ) := Group.IsPerfect.map (f := ρ)
    exact ff_perfect_le_of_quot_two E h2 (X.map ρ) inferInstance
  haveI hLAchar : (CFSG.layer A).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLAnormal : (CFSG.layer A).Normal := inferInstance
  let q : A →* A ⧸ CFSG.layer A := QuotientGroup.mk' (CFSG.layer A)
  let f : ↥X →* A ⧸ CFSG.layer A := q.comp X.subtype
  have hcent : ∀ x : ↥X, f x ∈ Subgroup.center (A ⧸ CFSG.layer A) := by
    intro x
    have hρx : ρ (x : A) ∈ E := hXE (Subgroup.mem_map_of_mem ρ x.2)
    rw [← hmap] at hρx
    obtain ⟨l, hl, hlρ⟩ := Subgroup.mem_map.mp hρx
    have hk : l⁻¹ * (x : A) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlρ, inv_mul_cancel]
    have hkc : l⁻¹ * (x : A) ∈ Subgroup.center A := hρ.ker_le_center hk
    have hfx : f x = q (l⁻¹ * (x : A)) := by
      have hql : q l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      show q (x : A) = q (l⁻¹ * (x : A))
      rw [map_mul, map_inv, hql, inv_one, one_mul]
    rw [hfx, Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have hc := Subgroup.mem_center_iff.mp hkc a
    change q a * q (l⁻¹ * (x : A)) = q (l⁻¹ * (x : A)) * q a
    rw [← map_mul, ← map_mul, hc]
  have hker : commutator ↥X ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp (hcent a) (f b)).symm)
  have hXtop : commutator ↥X = ⊤ := Group.IsPerfect.commutator_eq_top (G := ↥X)
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥X) ∈ f.ker := hker (by rw [hXtop]; exact Subgroup.mem_top _)
  exact (QuotientGroup.eq_one_iff x).mp hmem

end Abstract

section Model

variable {G : Type} [Group G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_cover_data [Finite G] (h : IsOm6M L) {hQ : Q.Nondegenerate}
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x)
    (hss : s * s ∈ centralizer (L : Set G)) (hx : KM2 x) :
    ∃ (ρ : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ h2 x))
      (E : Subgroup ↥(ffFix hQ h2 x)) (_ : E.Normal),
      OddCentralCover ρ ∧
      (∀ c : ↥(L ⊓ centralizer ({s} : Set G)),
        ((ρ c : ↥(ffFix hQ h2 x)) : ↥(omegaProj hQ)) =
          ff6mPhi e ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩) ∧
      LieModel ↥E .PSp 2 3 1 ∧ IsPGroup 2 (↥(ffFix hQ h2 x) ⧸ E) ∧
      (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G))).map ρ = E := by
  obtain ⟨ρ, hρ, hρφ⟩ := a6c_exists_centCover hQ h2 e (ff6m_odd_center h) hs hss
  obtain ⟨E, hE, hlie, hp⟩ := ff6m_K2_layerModel hQ hdim hsgn hx
  haveI : E.Normal := hE
  obtain ⟨hsE, hnc⟩ := ff_simple_of_lieModel_psp hlie
  have hev : 2 ∣ Nat.card ↥E := by rw [ff_card_model_psp hlie]; norm_num
  exact ⟨ρ, E, hE, hρ, hρφ, hlie, hp, a6c_cover_layer_map hρ E hsE hnc hev hp⟩

end Model

end CFSG.OddStandard.SmallF3.Omega
