module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigC4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigQuatAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.hw_e0_center (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (e₀ : ↥R₀ ≃* QuaternionGroup (2 ^ (r - 2))) :
    ((e₀.symm (QuaternionGroup.a (2 ^ (r - 2) : ℕ)) : ↥R₀) : Y) = t := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have h2 : (QuaternionGroup.a (2 ^ (r - 2) : ℕ) : QuaternionGroup (2 ^ (r - 2))) *
      QuaternionGroup.a (2 ^ (r - 2) : ℕ) = 1 :=
    (QuatAutH.mul_self_eq_one_iff _).mpr (Or.inr rfl)
  have h21 : (QuaternionGroup.a (2 ^ (r - 2) : ℕ) : QuaternionGroup (2 ^ (r - 2))) ≠ 1 := by
    intro h
    rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h
    exact QuatAutH.n_ne_zero h
  refine (hs.large.datum.isUniqueInvolution_core.unique _ (hs.hR₀.1 (e₀.symm _).2)
    ?_).resolve_left ?_
  · rw [← Subgroup.coe_mul, ← map_mul, h2, map_one]
    rfl
  · intro h
    apply h21
    have : e₀.symm (QuaternionGroup.a (2 ^ (r - 2) : ℕ)) = 1 := Subtype.ext h
    simpa using congrArg e₀ this

theorem Z2SetR.hw_false_of_member_inv (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyP : y ∈ (P : Subgroup Y)) (hyA : y ∉ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y) : False := by
  have hF := TightLargeHypR.typeRFam hs.large
  obtain ⟨hsw, -⟩ := hs.aux_swap hyP hyA
  have hc := hs.aux_commutes
  have hT : ∀ x ∈ R₀, y * x * y⁻¹ ∈ T₀ := fun x hx => by
    rw [← hs.aux_conj_R₀ hyP hsw]
    exact conj_mem_conjSub hx y
  have hQ2 : IsPGroup 2 ↥(aux_diag R₀ T₀ y hT hc).range :=
    hs.hR₀.2.1.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hQy : (aux_diag R₀ T₀ y hT hc).range ≤ Subgroup.centralizer ({y} : Set Y) := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (aux_diag_comm hT hc hyL.sq x).symm
  have hCN := hF.tight L hL y hyL
  have hMN : (aux_diag R₀ T₀ y hT hc).range ⊔ L ≤ Subgroup.normalizer (L : Set Y) :=
    sup_le (hQy.trans hCN) Subgroup.le_normalizer
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ2
    (le_sup_left : (aux_diag R₀ T₀ y hT hc).range ≤ (aux_diag R₀ T₀ y hT hc).range ⊔ L)
  have hRL : IsSylow2In (V ⊓ L) L :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_right hMN
  have hQN : ∀ z ∈ (aux_diag R₀ T₀ y hT hc).range,
      z ∈ Subgroup.normalizer ((V ⊓ L : Subgroup Y) : Set Y) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have hzV : z ∈ V := hQV hz
    have hzL := Subgroup.mem_normalizer_iff.mp (hCN (hQy hz)) r
    constructor
    · intro hr
      obtain ⟨hrV, hrL⟩ := Subgroup.mem_inf.mp hr
      exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hzV hrV) (inv_mem hzV), hzL.mp hrL⟩
    · intro hr
      obtain ⟨hrV, hrL⟩ := Subgroup.mem_inf.mp hr
      refine Subgroup.mem_inf.mpr ⟨?_, hzL.mpr hrL⟩
      have h := mul_mem (mul_mem (inv_mem hzV) hrV) hzV
      simpa [mul_assoc] using h
  obtain ⟨eB⟩ : Nonempty (↥(V ⊓ L) ≃* QuaternionGroup (2 ^ (r - 2))) := hF.quat L hL _ hRL
  obtain ⟨e₀⟩ : Nonempty (↥R₀ ≃* QuaternionGroup (2 ^ (r - 2))) :=
    hF.quat _ (CoreAssembly.mem_conjClass_self _) R₀ hs.hR₀
  have hcent := QuatAutH.hom_centralizes_of_four_le hr (V ⊓ L) eB
    ((aux_diag R₀ T₀ y hT hc).comp e₀.symm.toMonoidHom) (fun q => hQN _ ⟨e₀.symm q, rfl⟩)
  have hfa : ((aux_diag R₀ T₀ y hT hc).comp e₀.symm.toMonoidHom)
      (QuaternionGroup.a (2 ^ (r - 2) : ℕ)) = t * u := by
    change aux_diag R₀ T₀ y hT hc (e₀.symm (QuaternionGroup.a (2 ^ (r - 2) : ℕ))) = t * u
    rw [aux_diag_apply, hs.hw_e0_center e₀, hsw]
  rw [hfa] at hcent
  have hRa : V ⊓ L ≤ Subgroup.centralizer ({t * u} : Set Y) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcent r hr).symm
  exact hyA (hs.aux_E_le (hs.mem_E_of_sylow_le h1 hL hyL hRL hRa hyP))

theorem Z2SetR.hw_t (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {g : Y}
    (hg : g⁻¹ * t * g ∈ (P : Subgroup Y)) : g⁻¹ * t * g ∈ edgeCent (P : Subgroup Y) t u := by
  by_contra hyA
  have hyL : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) (g⁻¹ * t * g) := by
    have h := hs.large.datum.isUniqueInvolution_core.conj g⁻¹
    rwa [inv_inv] at h
  exact hs.hw_false_of_member_inv hr h1 hg hyA ⟨g⁻¹, rfl⟩ hyL

theorem Z2SetR.hw_pow (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (hStar : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ y : Y, IsUniqueInvolution L y →
      2 < Nat.card ↥(L ⊓ (P : Subgroup Y)) → y = t ∨ y = u)
    {y : Y} (hy : y ∈ R₀) (hy2 : y * y ≠ 1) {g : Y} (hg : g⁻¹ * y * g ∈ (P : Subgroup Y)) :
    g⁻¹ * y * g ∈ edgeCent (P : Subgroup Y) t u := by
  have hK := hs.large.datum.isUniqueInvolution_core
  have hy1 : y ≠ 1 := fun h => hy2 (by rw [h]; group)
  have hL : conjSub g⁻¹ (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g⁻¹, rfl⟩
  have hyL : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) (g⁻¹ * t * g) := by
    have h := hK.conj g⁻¹
    rwa [inv_inv] at h
  obtain ⟨k, hk⟩ := hs.hR₀.2.1 ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm2, hm1⟩ := exists_pow_involution hk' hy1
  have hyt : y ^ m = t := (hK.unique _ (Subgroup.pow_mem _ (hs.hR₀.1 hy) m) hm2).resolve_left hm1
  have hy'L : g⁻¹ * y * g ∈ conjSub g⁻¹ (tightCore R) := by
    have h := conj_mem_conjSub (hs.hR₀.1 hy) g⁻¹
    rwa [inv_inv] at h
  have hcard : 2 < Nat.card ↥(conjSub g⁻¹ (tightCore R) ⊓ (P : Subgroup Y)) := by
    have hle : Subgroup.zpowers (g⁻¹ * y * g) ≤
        conjSub g⁻¹ (tightCore R) ⊓ (P : Subgroup Y) :=
      Subgroup.zpowers_le.mpr ⟨hy'L, hg⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h0 : orderOf (g⁻¹ * y * g) ≠ 0 := (orderOf_pos _).ne'
    have h1' : orderOf (g⁻¹ * y * g) ≠ 1 := by
      intro h
      apply hy1
      have hg1 : g⁻¹ * y * g = 1 := orderOf_eq_one_iff.mp h
      have := congrArg (fun z => g * z * g⁻¹) hg1
      simpa [mul_assoc] using this
    have h2' : orderOf (g⁻¹ * y * g) ≠ 2 := by
      intro h
      apply hy2
      have hsq : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
        rw [← pow_two, ← h, pow_orderOf_eq_one]
      have := congrArg (fun z => g * z * g⁻¹) hsq
      simpa [mul_assoc] using this
    have h3 : 3 ≤ orderOf (g⁻¹ * y * g) := by omega
    omega
  have hz := hStar (conjSub g⁻¹ (tightCore R)) hL (g⁻¹ * t * g) hyL hcard
  have hcomm : (g⁻¹ * y * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * y * g) := by
    have hconj : (g⁻¹ * y * g) ^ m = g⁻¹ * y ^ m * g := by
      have h := conj_pow (a := g⁻¹) (b := y) (i := m)
      rwa [inv_inv] at h
    rw [hyt] at hconj
    rw [← hconj]
    exact ((Commute.refl (g⁻¹ * y * g)).pow_right m).eq
  rw [hs.mem_edgeCent_iff]
  refine ⟨hg, ?_⟩
  rcases hs.perm hg with ⟨h, -⟩ | ⟨h, h'⟩
  · exact h
  · exfalso
    rcases hz with hz | hz
    · rw [hz] at hcomm
      have ht : (g⁻¹ * y * g) * t * (g⁻¹ * y * g)⁻¹ = t := by
        rw [hcomm]
        group
      exact hs.aux_t_ne_u (ht.symm.trans h)
    · rw [hz] at hcomm
      have hu : (g⁻¹ * y * g) * u * (g⁻¹ * y * g)⁻¹ = u := by
        rw [hcomm]
        group
      exact hs.aux_t_ne_u (h'.symm.trans hu)

theorem z2BigHweak_holds (r n : ℕ) : Z2BigHweak r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 y hy hy1 g hg
  by_cases h2 : y * y = 1
  · have hyt : y = t :=
      (hs.large.datum.isUniqueInvolution_core.unique y (hs.hR₀.1 hy) h2).resolve_left hy1
    rw [hyt] at hg ⊢
    exact hs.hw_t hr h1 hg
  · exact hs.hw_pow (C264.z2BigStar_of_models (z2BigModelArith_holds r)
      (z2BigModelPiCyc_holds r) hr Y R S t J u R₀ T₀ P hs) hy h2 hg

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
