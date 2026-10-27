module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigS5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3

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

theorem Z2SetR.actsTriv_or_actsTriv_mul_t (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hArith : Z2BigModelArith r) (hCent : Z2BigModelCent r) {S₂ R₁ : Subgroup Y}
    (hS₂u : S₂ ≤ Subgroup.centralizer ({u} : Set Y)) (hS₂T : ∀ s ∈ S₂, s * s ∈ T₀)
    (hR₁ : IsSylow2In R₁ (tightCore R)) (htR₁ : t ∈ R₁)
    (hR₁Λ : R₁ ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
    (hcomm : ∀ s ∈ S₂, ∀ x ∈ R₁, s * x = x * s) :
    ∀ s ∈ S₂, ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) s ∨
      ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (s * t) := by
  classical
  intro s hs₂
  have ht := hs.large.datum.isUniqueInvolution_core
  have hTF := TightLargeHypR.typeRFam hs.large
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨g, hg⟩ := hs.exists_conj_u
  have hgu : g⁻¹ * u * g⁻¹⁻¹ = t := inv_conj_of_conj hg
  have hΛtu : conjSub g (linkLayer R t) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := hs.conjSub_Λt_swap hg
  have hΛut : conjSub g⁻¹ (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayer R t := hs.conjSub_Λu_swap hgu
  have hT₀triv := hs.T₀_actsTriv
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr hArith
  have hC0 : CentInvConcl r ↥(linkGrp R t) := centInvConcl_of_model hCent hr hm
  have hC : CentInvConcl r
      (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
    centInvConcl_congr (linkLayerEquiv hs.large) hC0
  obtain ⟨eR⟩ := hTF.quat (tightCore R) hK R₁ hR₁
  have hQΛ : conjSub g⁻¹ R₁ ≤ linkLayer R t := by
    have h1 := conjSub_mono (n := g⁻¹) hR₁Λ
    rwa [hΛut] at h1
  have hQ2 : IsPGroup 2 ↥(conjSub g⁻¹ R₁) := hR₁.2.1.map _
  let eQ : ↥(conjSub g⁻¹ R₁) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (R₁.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans eR
  have hd : quatInvolution r eQ = g⁻¹ * t * g⁻¹⁻¹ := by
    have h1 : quatInvolution r eR = t :=
      quatInvolution_eq_of_uniqueInvolution hr ht hR₁.1 eR
    have h2 := quatInvolution_equivMapOfInjective (MulAut.conj g⁻¹) R₁ eR
    change quatInvolution r ((R₁.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans eR) = g⁻¹ * t * g⁻¹⁻¹
    rw [h2, h1, MulAut.conj_apply]
  have hct : g⁻¹ * s * g⁻¹⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgu]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hS₂u hs₂)
    rw [show g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * u * g⁻¹⁻¹) = g⁻¹ * (s * u) * g⁻¹⁻¹ by group, h1]
    group
  have hcN : g⁻¹ * s * g⁻¹⁻¹ ∈ Subgroup.normalizer (linkLayer R t : Set Y) :=
    hs.mem_normalizer_linkLayer hct
  have hc2 : ActsTriv (linkLayer R t) (g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * s * g⁻¹⁻¹)) := by
    have h1 := actsTriv_conj (hT₀triv _ (hS₂T s hs₂)) g⁻¹
    rwa [hΛut, show g⁻¹ * (s * s) * g⁻¹⁻¹ =
      g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * s * g⁻¹⁻¹) by group] at h1
  have hcQ : ∀ q ∈ conjSub g⁻¹ R₁,
      g⁻¹ * s * g⁻¹⁻¹ * q * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ = q := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
    rw [← hxq]
    change g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ =
      g⁻¹ * x * g⁻¹⁻¹
    rw [show g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ =
      g⁻¹ * (s * x) * s⁻¹ * g⁻¹⁻¹ by group, hcomm s hs₂ x hx]
    group
  rcases actsTriv_or_actsLike_of_concl hQΛ hQ2 eQ hd hcN hc2 hcQ hC with h | h
  · left
    have h1 := actsTriv_conj h g
    rwa [hΛtu, show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s by group] at h1
  · right
    have hdΛ : g⁻¹ * t * g⁻¹⁻¹ ∈ linkLayer R t := hQΛ (conj_mem_conjSub htR₁ g⁻¹)
    have hdd : (g⁻¹ * t * g⁻¹⁻¹) * (g⁻¹ * t * g⁻¹⁻¹) = 1 := by
      rw [show g⁻¹ * t * g⁻¹⁻¹ * (g⁻¹ * t * g⁻¹⁻¹) = g⁻¹ * (t * t) * g⁻¹⁻¹ by group,
        hs.t2]
      group
    have h1 := actsTriv_conj (actsTriv_mul_of_actsLike hdΛ hdd h) g
    rwa [hΛtu, show g * (g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)) * g⁻¹ = s * t by group] at h1

theorem Z2SetR.exists_conj_sup_le (hs : Z2SetR r n R S t J u R₀ T₀ P) {S₂ : Subgroup Y}
    (hS₂2 : IsPGroup 2 ↥S₂) (hS₂t : S₂ ≤ Subgroup.centralizer ({t} : Set Y)) :
    ∃ k ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) ⊓
        actTrivSubgroup (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u),
      conjSub k ((S₂ ⊔ Subgroup.zpowers t) ⊓ (Subgroup.centralizer ({t} : Set Y) ⊓
          Subgroup.centralizer ({u} : Set Y) ⊓
            actTrivSubgroup (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u))) ≤
        edgeCent (P : Subgroup Y) t u ⊓
          actTrivSubgroup (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) := by
  let Λu : Subgroup Y := linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u
  let E : Subgroup Y :=
    Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y)
  let Ku : Subgroup Y := E ⊓ actTrivSubgroup Λu
  have hEN : E ≤ Subgroup.normalizer (Λu : Set Y) :=
    fun _ he => hs.mem_normalizer_linkLayerAt he.2
  have hKuN : E ≤ Subgroup.normalizer (Ku : Set Y) := le_normalizer_inf_actTrivSubgroup hEN
  have hKuE : Ku ≤ E := inf_le_left
  have hA2 : IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) :=
    P.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hAE : IsSylow2In (edgeCent (P : Subgroup Y) t u) E := by
    refine ⟨fun c hc => ⟨hc.1.2, hc.2⟩, hA2, fun V hVE hV2 hAV => ?_⟩
    obtain ⟨c, -, hcV⟩ := hs.exists_conj_le_edgeCent hV2 (hVE.trans inf_le_left)
      (hVE.trans inf_le_right)
    have hcard : Nat.card ↥V ≤ Nat.card ↥(edgeCent (P : Subgroup Y) t u) := by
      rw [← natCard_conjSub' c V]
      exact Subgroup.card_le_of_le hcV
    exact (Subgroup.eq_of_le_of_card_ge hAV hcard).symm
  have hB : IsSylow2In (edgeCent (P : Subgroup Y) t u ⊓ Ku) Ku :=
    Asc77.isSylow2In_inf_of_le_normalizer hAE hKuE hKuN
  have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    Balance.isPGroup_zpowers_of_mul_self_eq_one hs.t2
  have hS₂tN : S₂ ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Y) : Set Y) := by
    intro s hs₂
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain hst := Subgroup.mem_centralizer_singleton_iff.mp (hS₂t hs₂)
    have hc : ∀ w ∈ Subgroup.zpowers t, s * w * s⁻¹ = w := by
      rintro _ ⟨k, rfl⟩
      exact conj_eq_of_comm ((Commute.zpow_right (show Commute s t from hst) k).eq)
    constructor
    · intro hz
      rw [hc z hz]
      exact hz
    · intro hz
      have h1 : z = s⁻¹ * (s * z * s⁻¹) * s := by group
      rw [h1, show s⁻¹ * (s * z * s⁻¹) * s = s⁻¹ * (s * z * s⁻¹) * s⁻¹⁻¹ by group]
      have hs' : s⁻¹ * (s * z * s⁻¹) * s⁻¹⁻¹ = s * z * s⁻¹ := by
        have hst' : s⁻¹ * t = t * s⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.symm]
          exact Subgroup.inv_mem _ (hS₂t hs₂)
        obtain ⟨k, hk⟩ := hz
        rw [← hk]
        exact conj_eq_of_comm ((Commute.zpow_right (show Commute s⁻¹ t from hst') k).eq)
      rw [hs']
      exact hz
  have hH₀2 : IsPGroup 2 ↥((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku) :=
    (hS₂2.to_sup_of_normal_right' ht2 hS₂tN).to_le inf_le_left
  obtain ⟨H₁, hH₁, hH₀H₁⟩ := IsSylow2In.exists_ge hH₀2 inf_le_right
  obtain ⟨k, hk, hkB⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hH₁ hB
  have hH₀B : conjSub k ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku) ≤
      edgeCent (P : Subgroup Y) t u ⊓ Ku := by
    rw [← hkB]
    exact conjSub_mono hH₀H₁
  exact ⟨k, hk, hH₀B.trans (inf_le_inf_left _ inf_le_right)⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
