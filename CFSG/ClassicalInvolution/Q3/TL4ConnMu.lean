module

public import CFSG.ClassicalInvolution.Q3.TL4ConnStd
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)

theorem not_muIsoS3_of_std8Core {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8Core Ω K J S R T W z t) : ¬ MuIsoS3 Ω W := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : Q3CL.PartIHypG Ω := Q3CL.T8R.Loc.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hnot : ∀ {R' : Subgroup G}, R' ∈ DSet Ω W → ∃ r ∈ R', r ∉ W := by
    intro R' hR'
    by_contra h
    push Not at h
    have hle : R' ≤ W := h
    have h1 := Q3CL.Thompson.D_card hΩ hW hR'
    rw [inf_eq_left.mpr hle] at h1
    have h2 : 0 < Nat.card R' := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := hnot hRD
  obtain ⟨t', ht', htW⟩ := hnot hTD
  let ρ : Rep Ω W := ⟨K, R, r, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let x : ↥(muGroup Ω W) :=
    ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hRD hr))⟩
  let y : ↥(muGroup Ω W) :=
    ⟨piG W t', piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hTD ht'))⟩
  have hx : x ∈ muDelta Ω W := ⟨R, hRD, r, hr, hrW, rfl⟩
  have hy : y ∈ muDelta Ω W := ⟨T, hTD, t', ht', htW, rfl⟩
  have hxy : x ≠ y := by
    intro h
    have h' : ρ.img = σ.img := congrArg Subtype.val h
    exact hs.hJ.2.1 (c.K_eq_of_img_eq ρ σ h').symm
  have hcomm : x * y = y * x := Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  rintro ⟨φ⟩
  have h1 := Q3T8.Asc77.Thompson.muDelta_mul_self hΩ hW hx
  have h2 := Q3T8.Asc77.Thompson.muDelta_mul_self hΩ hW hy
  refine T8.perm3_not_comm_involutions (φ x) (φ y) (by rw [← map_mul, h1, map_one])
    (by rw [← map_mul, h2, map_one])
    (fun h => muDelta_ne_one hW hx (φ.injective (by rw [h, map_one])))
    (fun h => muDelta_ne_one hW hy (φ.injective (by rw [h, map_one])))
    (fun h => hxy (φ.injective h)) ?_
  rw [← map_mul, ← map_mul, hcomm]

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

@[expose] def TightC27_2R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
          dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)

theorem tightC27_2R_of (h2 : TightC26_2R r n) (h13 : TightC26_13R r n) : TightC27_2R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc
  by_contra hne
  have hP := hs.partIHypG
  have hW := hs.hW.1
  have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore Rd)) W :=
    Q3T6.Mu.thompsonGraphAll hP hs.mem hne hW
  rcases Q3T8.Asc77.l7_10_proved Y _ hP W hW hnc with h3 | h4 | h5
  · exact not_muIsoS3_of_std8Core hs.toStd8Core h3
  · exact h2 Y Rd Sd z J S R T W t hs hdisc h4
  · exact h13 Y Rd Sd z J S R T W t hs hdisc h5

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
