module

public import CFSG.ClassicalInvolution.Q3.Sec13End18B
public import CFSG.ClassicalInvolution.Q3.Sec13EndMin
public import CFSG.ClassicalInvolution.Q3.Sec13End15A

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)}

structure SectData (Ω : Set (Subgroup G)) (u : G) : Prop where
  mem : u ∈ zGroup Ω
  ne_one : u ≠ 1
  mem_span : u ∈ pSpan (Generic.centMembers Ω u)
  adj : ∃ R ∈ Generic.centMembers Ω u, ∃ T ∈ Generic.centMembers Ω u,
    T ∈ omegaStarNbr Ω R ∧ T ∉ KPerp Ω R
  bad : ∃ L ∈ Generic.centMembers Ω u, ∃ J ∈ Generic.centMembers Ω u,
    J ∉ KPerp Ω L ∧ J ∉ omegaStarNbr Ω L
  twin : ∃ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard = 2

namespace SectData

variable {u : G}

theorem ae8a_not_commutes (H : End18.Hyp Ω) {R T : Subgroup G} (hR : R ∈ Ω) (hT : T ∈ Ω)
    (hTV : T ∉ twinSet Ω R) : ¬ Commutes R T := fun hc => by
  obtain ⟨zR, hzR⟩ := (H.endHyp.thmD.hyp.omega1 R hR).1
  obtain ⟨zT, hzT⟩ := (H.endHyp.thmD.hyp.omega1 T hT).1
  exact hTV ⟨hT, zR, hzR, (H.perp9 R hR T hT hc zR zT hzR hzT) ▸ hzT⟩

theorem ae8a_twin_conj (H : End18.Hyp Ω) (g : G) {A B : Subgroup G}
    (hB : B ∈ twinSet Ω A) : conjSub g B ∈ twinSet Ω (conjSub g A) := by
  obtain ⟨hBΩ, z, hA, hBz⟩ := hB
  exact ⟨H.endHyp.thmD.hyp.conjInvariant g B hBΩ, g * z * g⁻¹, hA.conj g, hBz.conj g⟩

theorem ae8a_conjSub_mem (H : End18.Hyp Ω) {u x : G} (hx : Commute x u)
    {M : Subgroup G} (hM : M ∈ Generic.centMembers Ω u) :
    conjSub x M ∈ Generic.centMembers Ω u := by
  refine ⟨H.endHyp.thmD.hyp.conjInvariant x M hM.1, fun m hm => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxu : x * u = u * x := hx.eq
  have hxinv : x⁻¹ * u = u * x⁻¹ := (Commute.inv_left_iff.mpr hx).eq
  rw [mem_conjSub_iff] at hm
  obtain ⟨n, hn_def⟩ : ∃ n, n = x⁻¹ * m * x := ⟨_, rfl⟩
  have hn : n * u = u * n := by
    rw [hn_def]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hM.2 (hn_def ▸ hm))
  have hm' : m = x * n * x⁻¹ := by rw [hn_def]; group
  rw [hm']
  calc x * n * x⁻¹ * u = x * n * (x⁻¹ * u) := by group
    _ = x * n * (u * x⁻¹) := by rw [hxinv]
    _ = x * (n * u) * x⁻¹ := by group
    _ = x * (u * n) * x⁻¹ := by rw [hn]
    _ = (x * u) * n * x⁻¹ := by group
    _ = (u * x) * n * x⁻¹ := by rw [hxu]
    _ = u * (x * n * x⁻¹) := by group

theorem ae8a_conjSub_mem_iff (H : End18.Hyp Ω) {u x : G} (hx : Commute x u)
    {M : Subgroup G} :
    conjSub x M ∈ Generic.centMembers Ω u ↔ M ∈ Generic.centMembers Ω u := by
  refine ⟨fun h => ?_, ae8a_conjSub_mem H hx⟩
  have h' := ae8a_conjSub_mem H (Commute.inv_left_iff.mpr hx) h
  rwa [conjSub_inv_conjSub] at h'

theorem ae8a_conj_symm {P : Set (Subgroup G)} {A B : Subgroup G}
    (h : ∃ x ∈ pSpan P, conjSub x A = B) : ∃ x ∈ pSpan P, conjSub x B = A := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x⁻¹, Subgroup.inv_mem _ hx, conjSub_inv_conjSub x A⟩

theorem ae8a_conj_trans {P : Set (Subgroup G)} {A B C : Subgroup G}
    (h₁ : ∃ x ∈ pSpan P, conjSub x A = B) (h₂ : ∃ x ∈ pSpan P, conjSub x B = C) :
    ∃ x ∈ pSpan P, conjSub x A = C := by
  obtain ⟨x, hx, rfl⟩ := h₁
  obtain ⟨y, hy, rfl⟩ := h₂
  exact ⟨y * x, Subgroup.mul_mem _ hy hx, by rw [conjSub_mul]⟩

theorem oneClass (H : End18.Hyp Ω) (hu : SectData Ω u) :
    ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
      ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x L = L' := by
  obtain ⟨R, hRP, T, hTP, -, hTK⟩ := hu.adj
  have hR : R ∈ Ω := hRP.1
  have hT : T ∈ Ω := hTP.1
  have hTV : T ∉ twinSet Ω R := by rwa [EndHyp.kPerp_eq_twinSet_of_perp9 H.endHyp H.perp9 hR] at hTK
  rcases StarHyp.sectionConcl_centMembers H.endHyp.toStarHyp hu.ne_one with
    ⟨-, hcomm⟩ | ⟨htrans, -, -⟩
  ·
    have hRT : ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x R = T := by
      by_contra hcon
      exact ae8a_not_commutes H hR hT hTV (hcomm R hRP T hTP hcon)
    have hall : ∀ L ∈ Generic.centMembers Ω u,
        ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x L = R := by
      intro L hL
      by_contra hcon
      have hLR : Commutes L R := hcomm L hL R hRP hcon
      have hLT : Commutes L T := hcomm L hL T hTP fun h =>
        hcon (ae8a_conj_trans h (ae8a_conj_symm hRT))
      obtain ⟨zL, hzL⟩ := (H.endHyp.thmD.hyp.omega1 L hL.1).1
      obtain ⟨zR, hzR⟩ := (H.endHyp.thmD.hyp.omega1 R hR).1
      obtain ⟨zT, hzT⟩ := (H.endHyp.thmD.hyp.omega1 T hT).1
      have e1 : zL = zR := H.perp9 L hL.1 R hR hLR zL zR hzL hzR
      have e2 : zL = zT := H.perp9 L hL.1 T hT hLT zL zT hzL hzT
      have e3 : zR = zT := e1.symm.trans e2
      exact hTV ⟨hT, zR, hzR, by rw [e3]; exact hzT⟩
    intro L hL L' hL'
    exact ae8a_conj_trans (hall L hL) (ae8a_conj_symm (hall L' hL'))
  · exact htrans

theorem ncard_twin (H : End18.Hyp Ω) (hu : SectData Ω u) :
    ∀ L ∈ Generic.centMembers Ω u,
      (twinSet Ω L ∩ Generic.centMembers Ω u).ncard = 2 := by
  obtain ⟨L₀, hL₀, h2⟩ := hu.twin
  intro L hL
  obtain ⟨x, hx, hxL⟩ := oneClass H hu L₀ hL₀ L hL
  have hxc : Commute x u :=
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) hx)
  have hpre : (fun M : Subgroup G => conjSub x M) ⁻¹' (twinSet Ω L ∩ Generic.centMembers Ω u)
      = twinSet Ω L₀ ∩ Generic.centMembers Ω u := by
    ext M
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2'⟩
      refine ⟨?_, (ae8a_conjSub_mem_iff H hxc).mp h2'⟩
      have h3 : conjSub x⁻¹ L = L₀ := by rw [← hxL]; exact conjSub_inv_conjSub x L₀
      have h4 := ae8a_twin_conj H x⁻¹ h1
      rwa [conjSub_inv_conjSub x M, h3] at h4
    · rintro ⟨h1, h2'⟩
      refine ⟨?_, (ae8a_conjSub_mem_iff H hxc).mpr h2'⟩
      have h4 := ae8a_twin_conj H x h1
      rwa [hxL] at h4
  have hsub : twinSet Ω L ∩ Generic.centMembers Ω u ⊆
      Set.range (fun M : Subgroup G => conjSub x M) := fun N _ =>
    ⟨conjSub x⁻¹ N, conjSub_conjSub_inv x N⟩
  calc (twinSet Ω L ∩ Generic.centMembers Ω u).ncard
      = ((fun M : Subgroup G => conjSub x M) ⁻¹'
          (twinSet Ω L ∩ Generic.centMembers Ω u)).ncard :=
        (Set.ncard_preimage_of_injective_subset_range (conjSub_injective x) hsub).symm
    _ = (twinSet Ω L₀ ∩ Generic.centMembers Ω u).ncard := by rw [hpre]
    _ = 2 := h2

end SectData

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
