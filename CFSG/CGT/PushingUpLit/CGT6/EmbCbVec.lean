module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.commV_zpowers_le_fixV {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m)
    {t : MulAut V} (htT : t ∈ T) (ht2 : t ^ 2 = 1) :
    commV (Subgroup.zpowers t) ≤ fixV Y := by
  obtain ⟨θ, hnat⟩ := h.exists_natSection hV hm hodd hY
  refine cb_commV_zpowers_le_fixV hV hm hodd θ hnat ht2 fun y hy => ?_
  exact Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2 t htT

omit [Finite V] in
private theorem cbvIsKGroup {G K : Subgroup (MulAut V)} (hG : CFSG.IsKGroup ↥G) (hKG : K ≤ G) :
    CFSG.IsKGroup ↥K :=
  isKGroup_of_surjective (isKGroup_subgroup hG (K.subgroupOf G))
    (Subgroup.subgroupOfEquivOfLe hKG).toMonoidHom (Subgroup.subgroupOfEquivOfLe hKG).surjective

theorem EndCfg4.exists_lift_vecStab {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m)
    {t : MulAut V} (htG : t ∈ G) (htT : t ∈ T) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    {u : V} (hu : u ∈ commV (Subgroup.zpowers t)) (hu1 : u ≠ 1) :
    ∃ X : Subgroup (MulAut V), Lift4 (vecStab G u) Y X := by
  classical
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have huY : u ∈ fixV Y := h.commV_zpowers_le_fixV hV hm hodd hY htT ht2 hu
  have hut : t u = u :=
    mem_fixV.mp (cb_commV_zpowers_le_fixV_self hV ht2 hu) t (Subgroup.mem_zpowers t)
  have htH : t ∈ vecStab G u := mem_vecStab.mpr ⟨htG, hut⟩
  have hYH : Y ≤ vecStab G u := fun y hy => mem_vecStab.mpr ⟨hYG hy, mem_fixV.mp huY y hy⟩
  have hHG : vecStab G u ≤ G := fun g hg => (mem_vecStab.mp hg).1
  obtain ⟨ε⟩ := hY
  have hYnt : Nontrivial ↥Y := by
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    exact ε.toEquiv.nontrivial
  have hne : vecStab G u ≠ G := by
    intro heq
    have hGu : ∀ g ∈ G, g u = u := fun g hg => (mem_vecStab.mp (heq ▸ hg)).2
    have hinv : GInv G (Subgroup.zpowers u) := by
      intro g hg a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [map_zpow, hGu g hg]
      exact Subgroup.zpow_mem_zpowers _ _
    rcases h.irr _ hinv with hbot | htop
    · exact hu1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers u))
    · obtain ⟨y₀, hy₀⟩ : ∃ y : ↥Y, y ≠ 1 := exists_ne 1
      apply hy₀
      apply Subtype.ext
      ext v
      have hv : v ∈ Subgroup.zpowers u := by rw [htop]; trivial
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [map_zpow, hGu (y₀ : MulAut V) (hYG y₀.2)]
      rfl
  have htY : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (Subgroup.mem_centralizer_iff.mp
      (h.adm.hYC hy).2 t htT).symm
  have hTcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (MulAut V)) :
      Set (MulAut V)) = Subgroup.centralizer ({t} : Set (MulAut V)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hadmG : Adm4 G (Subgroup.zpowers t) Y :=
    { hTG := Subgroup.zpowers_le.mpr htG
      hT1 := fun h0 => ht1 (Subgroup.zpowers_eq_bot.mp h0)
      hT2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
      hYC := le_inf hYG fun y hy => by
        rw [hTcent, Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff.mp hs]
        exact (Subgroup.mem_centralizer_iff.mp htY y hy).symm
      hsub := by
        rw [hTcent]
        exact h.cent t ⟨htG, htY⟩ ht1 ht2
      hperf := h.adm.hperf
      hcls := h.adm.hcls }
  have hadm : Adm4 (vecStab G u) (Subgroup.zpowers t) Y :=
    hadmG.restrict (Subgroup.zpowers_le.mpr htH) hHG hYH
  have hsmaller : Smaller (vecStab G u) G :=
    Or.inl (Subgroup.card_lt_of_lt (lt_of_le_of_ne hHG hne))
  obtain ⟨X, hX⟩ := h.ih V hV (vecStab G u) hsmaller (cbvIsKGroup h.kgroup hHG) _ Y hadm
  exact ⟨X, hX⟩

end CFSG.CGT.PushingUpLit.CGT6
