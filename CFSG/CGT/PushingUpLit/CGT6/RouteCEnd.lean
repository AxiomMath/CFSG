module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCSurv
public import CFSG.CGT.PushingUpLit.CGT6.RouteCBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.SectionRank.Ccomm
open scoped Matrix

@[expose] def Emb5Ten : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb5Cfg G T Y →
      ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
        ∃ g ∈ G, CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G

section End

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.false_of_routeC (hNL : NatLiftStatement) (hNR : NatRecogStatement)
    (hFin : ∀ n, 2 ≤ n → n ≤ 6 → FinC n (routeCSurvivors n)) (h510 : Emb5Ten)
    (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) : False := by
  obtain ⟨t, htT, ht1, ht2, -⟩ := exists_central_involution cfg.adm.hT1 cfg.adm.hT2
  have htG : t ∈ G := cfg.adm.hTG htT
  have htC : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) := cfg.adm.le_centralizer htT
  have ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) := ⟨htG, htC⟩
  obtain ⟨y, hy, hy3⟩ := exists_gen_of_card_three cfg.adm.h3
  obtain ⟨g, hgG, hgen⟩ := h510 V hV G T Y cfg t ht ht1 ht2
  have hyY : y ∈ Y := hy ▸ Subgroup.mem_zpowers y
  have htY : ∀ y' ∈ Y, t * y' = y' * t := fun y' hy' =>
    (Subgroup.mem_centralizer_iff.mp htC y' hy').symm
  obtain ⟨d, hd⟩ : ∃ d : MulAut V, d = g * y * g⁻¹ := ⟨_, rfl⟩
  have hconj : CGT6E.conjSub g Y = Subgroup.zpowers d := by
    rw [hy, hd]
    exact conjSub_zpowers g y
  have hgen' : Subgroup.zpowers d ⊔ Y ⊔ Subgroup.zpowers t = G := by
    rw [← hconj]
    exact hgen
  have hdN : d ∈ conjClosure Y G := hd ▸ mem_conjClosure_of_mem hgG hyY
  obtain ⟨n, ⟨e⟩⟩ := exists_coord hV
  have h64 := cfg.card_le_sixtyfour hV htY ht2 hgen
  have hn6 : n ≤ 6 := le_six_of_card_le e h64
  have hn2 : 2 ≤ n := two_le_of_card_commV e cfg.adm.h4
  have hhyp : RouteCHyp (elemAutEquivGL e y) (elemAutEquivGL e d) (elemAutEquivGL e t) := by
    rw [hd]
    exact cfg.routeCHyp e hy hy3 ht ht1 ht2 hgen
  obtain ⟨g₀, hg₀⟩ := hFin n hn2 hn6 _ _ _ hhyp
  obtain ⟨e', he'⟩ := exists_coord_of_conj e y d t
    (P := fun s => s ∈ routeCSurvivors n) ⟨g₀, hg₀⟩
  set σ := elemAutEquivGL e' with hσ
  have central : (σ y : Matrix (Fin n) (Fin n) (ZMod 2)) * σ d = σ d * σ y →
      (σ y : Matrix (Fin n) (Fin n) (ZMod 2)) * σ t = σ t * σ y → ∃ X, Lift5 G Y X := by
    intro h1 h2
    refine cfg.lift_of_central hV hy hgen' ?_ ?_
    · apply σ.injective
      rw [map_mul, map_mul]
      exact Units.ext h1
    · apply σ.injective
      rw [map_mul, map_mul]
      exact Units.ext h2
  have hnl := cfg.nolift
  have hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · rw [survivor_nil 2 (by norm_num) (by norm_num) (by norm_num)] at he'
    exact absurd he' (List.not_mem_nil)
  · rw [survivor_nil 3 (by norm_num) (by norm_num) (by norm_num)] at he'
    exact absurd he' (List.not_mem_nil)
  · rcases survivor4_ok _ he' with hc | ⟨x₁, x₂, x₃, u₁, u₂, u₃, v₁, v₂, v₃, hok⟩
    · exact hnl (central hc.1 hc.2)
    · exact hnl (Emb5Cfg.lift_of_alt hNL hNR hV cfg hy hdN htG ht2 hgen' (a := 2) (by norm_num)
        (by norm_num) (AltData.ofAltOK e' rfl rfl rfl ht2 hok))
  · exact hnl (central (survivor5_ok _ he').1 (survivor5_ok _ he').2)
  · rcases survivor6_ok _ he' with hc | ⟨x₁, x₂, x₃, u₁, u₂, u₃, v₁, v₂, v₃, hok⟩
    · exact hnl (central hc.1 hc.2)
    · exact hnl (Emb5Cfg.lift_of_alt hNL hNR hV cfg hy hdN htG ht2 hgen' (a := 3) (by norm_num)
        (by norm_num) (AltData.ofAltOK e' rfl rfl rfl ht2 hok))

end End

theorem emb5End_of_routeC (hNL : NatLiftStatement) (hNR : NatRecogStatement)
    (hFin : ∀ n, 2 ≤ n → n ≤ 6 → FinC n (routeCSurvivors n)) (h510 : Emb5Ten) : Emb5End :=
  fun _ _ _ hV _ _ _ cfg => cfg.false_of_routeC hNL hNR hFin h510 hV

end CFSG.CGT.PushingUpLit.CGT6
