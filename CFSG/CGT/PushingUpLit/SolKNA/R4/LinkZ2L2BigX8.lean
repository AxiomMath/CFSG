module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX6
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX7

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Gen

variable {Y : Type} [Group Y]

theorem isSylow2In_conjSub_inf_centralizer {V L : Subgroup Y} {z : Y}
    (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set Y))) (d : Y) :
    IsSylow2In (conjSub d V) (conjSub d L ⊓ Subgroup.centralizer ({d * z * d⁻¹} : Set Y)) := by
  have h := hV.conj d
  have h2 : conjSub d (L ⊓ Subgroup.centralizer ({z} : Set Y)) =
      conjSub d L ⊓ Subgroup.centralizer ({d * z * d⁻¹} : Set Y) := by
    rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj d).injective]
    exact congrArg (conjSub d L ⊓ ·) (Balance.conjSub_centralizer_singleton d z)
  rwa [h2] at h

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.false_of_type3 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hyL : IsUniqueInvolution L y)
    (hyt : y ≠ t) {V : Subgroup Y} (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hVA : V ≤ edgeCent (P : Subgroup Y) t u) (hyV : y ∈ V)
    (hU : V ∈ USet (CoreAssembly.conjClass (tightCore R))) : False := by
  have hyA : y ∈ edgeCent (P : Subgroup Y) t u := hVA hyV
  obtain ⟨Ry, e, hRy, hVxc, -, hEN, hVc, hRyc⟩ :=
    hs.exists_Ry_data hr hL hyL hyA (hV.1.trans inf_le_left) hVA hyV hU
  have htN := Subgroup.mem_normalizer_iff.mp
    (hEN t (Subgroup.subset_closure (by simp)))
  have huN := Subgroup.mem_normalizer_iff.mp
    (hEN u (Subgroup.subset_closure (by simp)))
  have hxcA : ∀ x ∈ QSub.xc e, x ∈ edgeCent (P : Subgroup Y) t u := fun x hx => hVA (hVxc ▸ hx)
  have hxct : ∀ x ∈ QSub.xc e, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hxcA x hx).1.2).symm
  have hxcu : ∀ x ∈ QSub.xc e, u * x = x * u := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hxcA x hx).2).symm
  have hVlt : Nat.card ↥V < 2 ^ r := by
    rw [hVc]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hyu : y ≠ u := hs.ne_u_of_natCard_lt hr hL hyL hV hVlt
  rcases QSub.involution_cases e hr (fun q hq => (htN q).mp hq) hxct hs.t2 with ht0 | ht1
  · exact false_of_Ry_cent_t hr hV hRy hVc hRyc ht0
  · rcases QSub.involution_cases e hr (fun q hq => (huN q).mp hq) hxcu hs.u2 with hu0 | hu1
    · exact hs.false_of_Ry_cent_u hr hL hyL hyu hRy e hu0
        (hxct _ (QSub.zeta_mem_xc e)) ht1
    · exact hs.false_of_Ry_cent_a hr h1 hL hyL hyA.1.1 hyt hV hVc hRy hRyc
        (mul_centralizes_of_conj_zeta e hr ht1 hu1)

theorem z2BigNoType3_holds (r n : ℕ) :
    4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
      Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
        ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y → y ≠ t →
          y * t = t * y → ∀ V : Subgroup Y,
            IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set Y)) → y ∈ V →
              V ∈ USet (CoreAssembly.conjClass (tightCore R)) → False := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 L hL y hyL hyt _ V hV hyV hU
  obtain ⟨d, hd, hdA⟩ := hs.exists_conj_le_edgeCent_t hV.2.1 (hV.1.trans inf_le_right)
  have hdt : d * t * d⁻¹ = t := conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hd)
  have hV' := isSylow2In_conjSub_inf_centralizer hV d
  rw [hdt] at hV'
  refine hs.false_of_type3 hr h1 (hs.mem_cls_conj hL d) (hyL.conj d) ?_ hV' hdA
    (conj_mem_conjSub hyV d)
    (USet.conj hs.large.datum.hypOmegaGen.conjInvariant hU d)
  intro h
  exact hyt (mul_left_cancel (mul_right_cancel (h.trans hdt.symm)))

theorem z2BigNoType3U_holds (r n : ℕ) :
    4 ≤ r → ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (J : Subgroup Y) (u : Y) (R₀ T₀ : Subgroup Y) (P : Sylow 2 Y),
      Z2SetR r n R S t J u R₀ T₀ P → C264One (CoreAssembly.conjClass (tightCore R)) t u →
        ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y → y ≠ u →
          y * u = u * y → ∀ V : Subgroup Y,
            IsSylow2In V (L ⊓ Subgroup.centralizer ({u} : Set Y)) → y ∈ V →
              V ∈ USet (CoreAssembly.conjClass (tightCore R)) → False := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 L hL y hyL hyu hyc V hV hyV hU
  obtain ⟨g, -, hug, -⟩ := hs.exists_linkLayerAt_eq
  have hgu : g⁻¹ * u * g⁻¹⁻¹ = t := by
    rw [hug]
    group
  have hV' := isSylow2In_conjSub_inf_centralizer hV g⁻¹
  rw [hgu] at hV'
  refine z2BigNoType3_holds r n hr Y R S t J u R₀ T₀ P hs h1 _ (hs.mem_cls_conj hL g⁻¹) _
    (hyL.conj g⁻¹) ?_ ?_ _ hV' (conj_mem_conjSub hyV g⁻¹)
    (USet.conj hs.large.datum.hypOmegaGen.conjInvariant hU g⁻¹)
  · intro h
    apply hyu
    calc y = g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [h]
      _ = u := hug.symm
  · have h2 : (g⁻¹ * y * g⁻¹⁻¹) * (g⁻¹ * u * g⁻¹⁻¹) = (g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) := by
      calc (g⁻¹ * y * g⁻¹⁻¹) * (g⁻¹ * u * g⁻¹⁻¹) = g⁻¹ * (y * u) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (u * y) * g⁻¹⁻¹ := by rw [hyc]
        _ = (g⁻¹ * u * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) := by group
    rwa [hgu] at h2

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
