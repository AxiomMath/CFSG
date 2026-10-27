module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Frame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} {F : PspFrame L} {t : G} {S : Subgroup G}
  (h : Setup107 L t S)

namespace Setup107

include h

theorem phiG_conj {g x : G} (hg : g ∈ S) (hx : x ∈ S) :
    F.phiG (g * x * g⁻¹) = F.phiG g * F.phiG x * (F.phiG g)⁻¹ := by
  have hN := h.S_le_N
  rw [F.phiG_mul ((normalizer (L : Set G)).mul_mem (hN hg) (hN hx))
    ((normalizer (L : Set G)).inv_mem (hN hg)), F.phiG_mul (hN hg) (hN hx), F.phiG_inv (hN hg)]

theorem normal_imgS {X : Subgroup G} (hn : (X.subgroupOf S).Normal) :
    ∀ g ∈ F.imgS S S, ∀ p ∈ F.imgS S X, g * p * g⁻¹ ∈ F.imgS S X := by
  intro g hg p hp
  obtain ⟨s, -, hsS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hg
  obtain ⟨x, hx, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hp
  have hc : s * x * s⁻¹ ∈ X :=
    Subgroup.mem_subgroupOf.1 (hn.conj_mem ⟨x, hxS⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨s, hsS⟩)
  rw [← h.phiG_conj hsS hxS]
  exact (F.mem_imgS h.S_le_N).2 ⟨s * x * s⁻¹, hc, S.mul_mem (S.mul_mem hsS hxS) (S.inv_mem hsS),
    rfl⟩

theorem normal_preS {K : Subgroup P45}
    (hn : ∀ g ∈ F.imgS S S, ∀ p ∈ K, g * p * g⁻¹ ∈ K) : ((F.preS S K).subgroupOf S).Normal := by
  refine ⟨fun n hn' g => ?_⟩
  have hn'' := (F.mem_preS h.S_le_N).1 (Subgroup.mem_subgroupOf.1 hn')
  rw [Subgroup.mem_subgroupOf, F.mem_preS h.S_le_N]
  refine ⟨S.mul_mem (S.mul_mem g.2 n.2) (S.inv_mem g.2), ?_⟩
  have e : F.phiG ((g : G) * (n : G) * (g : G)⁻¹) =
      F.phiG g * F.phiG n * (F.phiG g)⁻¹ := h.phiG_conj g.2 n.2
  change F.phiG ((g : G) * (n : G) * (g : G)⁻¹) ∈ K
  rw [e]
  exact hn _ ((F.mem_imgS h.S_le_N).2 ⟨g, g.2, g.2, rfl⟩) _ hn''.2

theorem imgS_eq_img {X : Subgroup G} (hXL : X ≤ L) (hXS : X ≤ S) : F.imgS S X = F.img X := by
  ext p
  rw [F.mem_imgS h.S_le_N, PspFrame.mem_img]
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact ⟨⟨x, hXL hx⟩, hx, (F.phiG_psi ⟨x, hXL hx⟩).symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, hXS hl, F.phiG_psi l⟩

theorem preS_eq_sup {K : Subgroup P45} (hK : K ≤ F.img (S ⊓ L)) :
    F.preS S K = F.pre K ⊔ zpowers t := by
  have hN := h.S_le_N
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxK⟩ := (F.mem_preS hN).1 hx
    obtain ⟨l, hl, hψ⟩ := PspFrame.mem_img.1 (hK hxK)
    have hlS : (l : G) ∈ S := (Subgroup.mem_inf.1 hl).1
    have hφ : F.phiG (l : G) = F.phiG x := by rw [F.phiG_psi, hψ]
    have hlK : (l : G) ∈ F.pre K :=
      PspFrame.mem_pre.2 ⟨l.2, by rw [show F.ψ ⟨(l : G), l.2⟩ = F.phiG x from hψ]; exact hxK⟩
    rcases (h.phiG_eq_iff hlS hxS).1 hφ with e | e
    · rw [e]
      exact Subgroup.mem_sup_left hlK
    · rw [e]
      exact Subgroup.mul_mem_sup hlK (Subgroup.mem_zpowers t)
  · refine sup_le (fun x hx => ?_) ?_
    · obtain ⟨hxL, hxK⟩ := PspFrame.mem_pre.1 hx
      obtain ⟨l, hl, hψ⟩ := PspFrame.mem_img.1 (hK hxK)
      have hl' : l = ⟨x, hxL⟩ := F.ψ_injective hψ
      have hxS : x ∈ S := by
        have := (Subgroup.mem_inf.1 hl).1
        rwa [hl'] at this
      refine (F.mem_preS hN).2 ⟨hxS, ?_⟩
      have e : F.phiG x = F.ψ ⟨x, hxL⟩ := F.phiG_psi ⟨x, hxL⟩
      rw [e]
      exact hxK
    · rw [Subgroup.zpowers_le]
      exact h.t_mem_preS K

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
