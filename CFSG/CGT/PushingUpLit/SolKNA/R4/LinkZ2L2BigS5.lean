module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS4

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

theorem Z2SetR.T₀_actsTriv (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ∀ z ∈ T₀, ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) z := by
  classical
  have hJu : J ≤ Subgroup.centralizer ({u} : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).le_centralizer hs.hJ.1 hs.hu
  obtain ⟨g, hg⟩ := hs.exists_conj_u
  have hgu : g⁻¹ * u * g⁻¹⁻¹ = t := inv_conj_of_conj hg
  have hΛtu : conjSub g (linkLayer R t) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := hs.conjSub_Λt_swap hg
  intro z hz
  have hzc : z ∈ coreAt u J := Subgroup.subset_closure ⟨⟨hs.hT₀.1 hz, hJu (hs.hT₀.1 hz)⟩,
    hs.hT₀.2.1.to_le (Subgroup.zpowers_le.mpr hz)⟩
  have hzc' : g⁻¹ * z * g⁻¹⁻¹ ∈ coreAt t (tightCore R) := by
    have h1 := conj_mem_conjSub hzc g⁻¹
    rwa [conjSub_coreAt_conj, hgu, hs.conjSub_J_swap hgu] at h1
  have h2 := actsTriv_conj (fun y hy => commutator_mem_oddCoreOf_linkLayerR hs.large hzc' hy) g
  rwa [hΛtu, show g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z by group] at h2

theorem Z2SetR.exists_S2 (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hArith : Z2BigModelArith r) :
    ∃ S₂ : Subgroup Y, T₀ ≤ S₂ ∧ S₂ ≤ linkLayer R t ∧ IsPGroup 2 ↥S₂ ∧
      IsSylow2In ((S₂.subgroupOf (linkLayer R t)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayer R t)))) ⊤ ∧
      (∀ s ∈ S₂, s * s ∈ T₀) ∧ S₂ ≤ Subgroup.centralizer ({u} : Set Y) ∧
      S₂ ≤ Subgroup.centralizer ({t} : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTF := TightLargeHypR.typeRFam hs.large
  obtain ⟨Q, hQ⟩ := (hs.hT₀.2.1.comap_of_injective (linkLayer R t).subtype
    Subtype.val_injective).exists_le_sylow
  set S₂ : Subgroup Y := (Q : Subgroup ↥(linkLayer R t)).map (linkLayer R t).subtype with hS₂def
  have hS₂Λ : S₂ ≤ linkLayer R t := Subgroup.map_subtype_le _
  have hT₀S₂ : T₀ ≤ S₂ := fun z hz => ⟨⟨z, hs.T₀_le_linkLayer hz⟩, hQ hz, rfl⟩
  have hS₂2 : IsPGroup 2 ↥S₂ := Q.isPGroup'.map _
  obtain ⟨eT⟩ := hTF.quat J hs.hJ.1 T₀ hs.hT₀
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hT₀card : Nat.card ↥T₀ = 2 ^ r := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  let mk' : ↥(linkLayer R t) →*
      (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayer R t))
  have hmk : Function.Surjective mk' := QuotientGroup.mk'_surjective _
  have hLQ : Function.Injective (mk'.comp (Q : Subgroup ↥(linkLayer R t)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hq' : (q : ↥(linkLayer R t)) ∈
        classicalInvolutionOddCore ↥(linkLayer R t) := by
      rw [← QuotientGroup.ker_mk' (classicalInvolutionOddCore ↥(linkLayer R t)),
        MonoidHom.mem_ker]
      exact hq
    exact Subtype.ext (eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card ↥(linkLayer R t)) hq'
      (Q.isPGroup'.to_le (Subgroup.zpowers_le.mpr q.2)))
  have hrange : (mk'.comp (Q : Subgroup ↥(linkLayer R t)).subtype).range =
      (Q : Subgroup ↥(linkLayer R t)).map mk' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hQcard : Nat.card ↥(Q : Subgroup ↥(linkLayer R t)) ≤ 2 ^ (r + 1) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hLQ).toEquiv, hrange]
    exact Z2SetR.card_le_quot hs hr hArith (Q.isPGroup'.map mk')
  have hS₂card : Nat.card ↥S₂ ≤ 2 ^ (r + 1) := by
    rw [hS₂def, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hQcard
  have hidx : T₀.relIndex S₂ ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card T₀ S₂
    rw [inf_eq_left.mpr hT₀S₂, hT₀card] at h1
    have hle : T₀.relIndex S₂ * 2 ^ r ≤ 2 * 2 ^ r := by
      rw [h1]
      calc Nat.card ↥S₂ ≤ 2 ^ (r + 1) := hS₂card
        _ = 2 * 2 ^ r := by rw [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right hle (by positivity)
  have hS₂T : ∀ s ∈ S₂, s * s ∈ T₀ ∧ ∀ z ∈ T₀, s * z * s⁻¹ ∈ T₀ := by
    intro s hs₂
    have hpos : T₀.relIndex S₂ ≠ 0 := by
      intro h0
      have h1 := Subgroup.relIndex_mul_card T₀ S₂
      rw [h0, zero_mul] at h1
      exact absurd h1.symm Nat.card_pos.ne'
    rcases (by omega : T₀.relIndex S₂ = 1 ∨ T₀.relIndex S₂ = 2) with h1 | h2
    · have hsT : s ∈ T₀ := Subgroup.relIndex_eq_one.mp h1 hs₂
      exact ⟨T₀.mul_mem hsT hsT, fun z hz => T₀.mul_mem (T₀.mul_mem hsT hz) (T₀.inv_mem hsT)⟩
    · have h2' : (T₀.subgroupOf S₂).index = 2 := h2
      haveI := Subgroup.normal_of_index_eq_two h2'
      refine ⟨?_, fun z hz => ?_⟩
      · have h3 := Subgroup.sq_mem_of_index_two h2' ⟨s, hs₂⟩
        rw [Subgroup.mem_subgroupOf] at h3
        simpa [sq] using h3
      · have h3 := (inferInstance : (T₀.subgroupOf S₂).Normal).conj_mem ⟨z, hT₀S₂ hz⟩
          (Subgroup.mem_subgroupOf.mpr hz) ⟨s, hs₂⟩
        rw [Subgroup.mem_subgroupOf] at h3
        exact h3
  have hS₂N : ∀ s ∈ S₂, conjSub s T₀ = T₀ := by
    intro s hs₂
    refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · rw [mem_conjSub_iff] at hz
      have h1 := (hS₂T s hs₂).2 _ hz
      rwa [show s * (s⁻¹ * z * s) * s⁻¹ = z by group] at h1
    · rw [mem_conjSub_iff]
      have h1 := (hS₂T s⁻¹ (S₂.inv_mem hs₂)).2 z hz
      rwa [inv_inv] at h1
  have hS₂u : S₂ ≤ Subgroup.centralizer ({u} : Set Y) := fun s hs₂ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have huT : IsUniqueInvolution T₀ u :=
        ⟨hs.u_mem_T₀, hs.hu.ne_one, hs.hu.sq,
          fun y hy hy2 => hs.hu.unique y (hs.hT₀.1 hy) hy2⟩
      have h1 := huT.conj_eq (hS₂N s hs₂)
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [h1])
  have hS₂t : S₂ ≤ Subgroup.centralizer ({t} : Set Y) := hS₂Λ.trans linkLayerAt_le_centralizer
  have hsub : S₂.subgroupOf (linkLayer R t) = Q := by
    rw [hS₂def]
    exact Subgroup.comap_map_eq_self_of_injective (linkLayer R t).subtype_injective Q
  refine ⟨S₂, hT₀S₂, hS₂Λ, hS₂2, ?_, fun s hs₂ => (hS₂T s hs₂).1, hS₂u, hS₂t⟩
  rw [hsub]
  let Q' : Sylow 2 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
    Q.mapSurjective hmk
  exact ⟨le_top, Q'.isPGroup', fun V _ hV hle => Q'.is_maximal' hV hle⟩

theorem Z2SetR.exists_Rprime (hs : Z2SetR r n R S t J u R₀ T₀ P) {S₂ : Subgroup Y}
    (hS₂Λ : S₂ ≤ linkLayer R t) (hS₂2 : IsPGroup 2 ↥S₂)
    (hS₂u : S₂ ≤ Subgroup.centralizer ({u} : Set Y)) :
    ∃ R₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) ∧
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) ∧ t ∈ R₁ ∧
      R₁ ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u ∧
      ∀ s ∈ S₂, ∀ x ∈ R₁, s * x = x * s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hS₂t : S₂ ≤ Subgroup.centralizer ({t} : Set Y) := hS₂Λ.trans linkLayerAt_le_centralizer
  have hS₂M : S₂ ≤ Subgroup.normalizer
      ((tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) : Set Y) := by
    intro s hs₂
    rw [mem_normalizer_iff_conjSub_eq, conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]
    have h1 : conjSub s (tightCore R) = tightCore R := hs.conjSub_K_fix
      (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hS₂t hs₂)))
    have h2 : conjSub s (Subgroup.centralizer ({u} : Set Y)) =
        Subgroup.centralizer ({u} : Set Y) := by
      rw [Balance.conjSub_centralizer_singleton,
        conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hS₂u hs₂))]
    exact congrArg₂ (· ⊓ ·) h1 h2
  obtain ⟨X₀, hX₀, hS₂X₀⟩ := IsSylow2In.exists_ge hS₂2
    (le_sup_right : S₂ ≤ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) ⊔ S₂)
  have hR₀' := isSylow2In_inf_of_le_normalizer hX₀ le_sup_left
    (sup_le Subgroup.le_normalizer hS₂M)
  have hR₀M : IsSylow2In R₀ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) :=
    ⟨le_inf hs.hR₀.1 hs.hR₀u, hs.hR₀.2.1, fun V hVM hV2 hle =>
      hs.hR₀.2.2 V (hVM.trans inf_le_left) hV2 hle⟩
  obtain ⟨m, hm, hmR⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR₀M hR₀'
  have hR₀'K : IsSylow2In (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))
      (tightCore R) := by
    rw [← hmR]
    have h1 := hs.hR₀.conj m
    rwa [conjSub_eq_self_of_mem hm.1] at h1
  have hS₂R : ∀ s ∈ S₂, ∀ r ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)),
      s * r = r * s := by
    intro s hs₂ r hr
    have hsr : s * r * s⁻¹ ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) :=
      ⟨X₀.mul_mem (X₀.mul_mem (hS₂X₀ hs₂) hr.1) (X₀.inv_mem (hS₂X₀ hs₂)),
        (Subgroup.mem_normalizer_iff.mp (hS₂M hs₂) r).mp hr.2⟩
    have hc := Subgroup.mul_mem _ hsr (Subgroup.inv_mem _ hr)
    have hcO := linkLayer_commutator_mem_oddCoreOf_coreR hs.large (hS₂Λ hs₂) hr.2.1
    have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hcO
      (hR₀'K.2.1.to_le (Subgroup.zpowers_le.mpr hc))
    calc s * r = s * r * s⁻¹ * r⁻¹ * (r * s) := by group
      _ = r * s := by rw [h1, one_mul]
  have htR₁ : t ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) := by
    refine T3.mem_of_isPGroup ht hR₀'K.1 hR₀'K.2.1 ?_
    have h8 := Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
      (mem_RSet_of_isSylow2In hK hR₀'K)
    omega
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  have hR₁Λu : X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) ≤
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := fun r hr =>
    coreAt_le_linkLayerAt hKJ (Subgroup.subset_closure ⟨⟨hr.2.1, hr.2.2⟩,
      hR₀'K.2.1.to_le (Subgroup.zpowers_le.mpr hr)⟩)
  exact ⟨X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)), hR₀'K,
    fun x hx => hx.2.2, htR₁, hR₁Λu, hS₂R⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
