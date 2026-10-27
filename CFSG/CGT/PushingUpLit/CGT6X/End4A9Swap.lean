module

public import CFSG.CGT.PushingUpLit.CGT6X.End4A9Cfg

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem a9_swap_false (cfg : EndCfg4 G T Y) (hY2 : YSL Y 2)
    {θ : ↥(CGT6.conjClosure Y G) ≃* alternatingGroup (Fin 9)} {t : MulAut V} (htT : t ∈ T)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) {σ : Equiv.Perm (Fin 9)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((θ ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ : alternatingGroup (Fin 9)) :
        Equiv.Perm (Fin 9)) = σ * ((θ ⟨l, hl⟩ : alternatingGroup (Fin 9)) :
          Equiv.Perm (Fin 9)) * σ⁻¹)
    {a b : Fin 9} (hab : a ≠ b) (hσab : σ = Equiv.swap a b)
    (hY : ∀ h ∈ (Y.subgroupOf (CGT6.conjClosure Y G)).map θ.toMonoidHom,
      (h : Equiv.Perm (Fin 9)) a = a ∧ (h : Equiv.Perm (Fin 9)) b = b) : False := by
  have htG := cfg.adm.hTG htT
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hLG : CGT6.conjClosure Y G ≤ G := CGT6.conjClosure_le hYG
  have hY60 := card_Y_sixty hY2
  have hB := nonempty_layerPre_alt θ hab
  have hYB : Y ≤ layerPre θ (altStabilizer 9 {a, b}) := by
    refine le_layerPre_of_map_le hYL fun h hh => ?_
    obtain ⟨ha, hb⟩ := hY h hh
    rw [mem_altStabilizer_iff]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ha
    · rw [Finset.mem_singleton.mp hi]
      exact hb
  have hcomm : ∀ k ∈ layerPre θ (altStabilizer 9 {a, b}), t * k = k * t := by
    refine comm_layerPre (fun l hl => conj_mem_conjClosure htG hl) hσ fun g hg => ?_
    rw [mem_altStabilizer_iff] at hg
    have ha : (g : Equiv.Perm (Fin 9)) a = a := hg a (by simp)
    have hb : (g : Equiv.Perm (Fin 9)) b = b := hg b (by simp)
    have h1 := Equiv.swap_apply_apply (g : Equiv.Perm (Fin 9)) a b
    rw [ha, hb] at h1
    have h2 : (g : Equiv.Perm (Fin 9)) * σ = σ * g := by
      rw [hσab]
      exact mul_inv_eq_iff_eq_mul.mp h1.symm
    rw [← h2]
    group
  have hBle : layerPre θ (altStabilizer 9 {a, b}) ≤
      G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
    le_inf ((layerPre_le θ _).trans hLG) fun k hk => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm k hk
  have hsub := cfg.cent t ⟨htG, cfg.adm.le_centralizer htT⟩ ht1 (by rw [pow_two]; exact ht2)
  have hsubB : (Y.subgroupOf (layerPre θ (altStabilizer 9 {a, b}))).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hBle hsub
  have hsimple : IsSimpleGroup ↥(layerPre θ (altStabilizer 9 {a, b})) := by
    obtain ⟨e⟩ := hB
    have : IsSimpleGroup (alternatingGroup (Fin (9 - 2))) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hBcard : Nat.card ↥(layerPre θ (altStabilizer 9 {a, b})) = 2520 := by
    rw [card_layerPre_pair θ hab (by norm_num)]
    decide
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hsubB with hbot | htop
  · have hY1 : Y = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h1 : (⟨y, hYB hy⟩ : ↥(layerPre θ (altStabilizer 9 {a, b}))) ∈
          Y.subgroupOf (layerPre θ (altStabilizer 9 {a, b})) := hy
      rw [hbot, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    rw [hY1, Subgroup.card_bot] at hY60
    omega
  · have hBY := Subgroup.subgroupOf_eq_top.mp htop
    have h1 : layerPre θ (altStabilizer 9 {a, b}) = Y := le_antisymm hBY hYB
    rw [h1, hY60] at hBcard
    omega

end CFSG.CGT.PushingUpLit.CGT6X.End4
