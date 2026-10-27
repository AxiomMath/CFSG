module

public import CFSG.CGT.PushingUpLit.CGT6X.End4A9Swap
public import CFSG.CGT.PushingUpLit.CGT6X.End4Ih
public import CFSG.CGT.PushingUpLit.CGT6X.End4Irr
public import CFSG.CGT.PushingUpLit.CGT6X.End4Perm
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltRec
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLiftArrow

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem a9_four_false (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) (hY2 : YSL Y 2)
    {θ : ↥(CGT6.conjClosure Y G) ≃* alternatingGroup (Fin 9)} {t : MulAut V} (htT : t ∈ T)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) {σ : Equiv.Perm (Fin 9)}
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((θ ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ : alternatingGroup (Fin 9)) :
        Equiv.Perm (Fin 9)) = σ * ((θ ⟨l, hl⟩ : alternatingGroup (Fin 9)) :
          Equiv.Perm (Fin 9)) * σ⁻¹)
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) {F : Finset (Fin 9)} (hF : F.card = 4)
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map θ.toMonoidHom = altStabilizer 9 F)
    (hFσ : ∀ i, i ∉ F → σ i = i) : False := by
  have htG := cfg.adm.hTG htT
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hLG : CGT6.conjClosure Y G ≤ G := CGT6.conjClosure_le hYG
  have hLn : ((CGT6.conjClosure Y G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2 CGT6.le_normalizer_conjClosure
  have hY60 := card_Y_sixty hY2
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra h
    refine hσ1 (Equiv.ext fun i => ?_)
    by_contra hi
    exact h ⟨i, hi⟩
  have hσσ : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun f : Equiv.Perm (Fin 9) => f i) hσ2
    simpa using this
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hpF : p ∈ F := by
    by_contra hn
    exact hp (hFσ p hn)
  have hqF : σ p ∈ F := by
    by_contra hn
    have h1 := hFσ _ hn
    rw [hσσ] at h1
    exact hp h1.symm
  have hpq : p ≠ σ p := hp.symm
  have hKY : Y ≤ layerPre θ (altStabilizer 9 {p, σ p}) := by
    refine le_layerPre_of_map_le hYL ?_
    rw [hH]
    intro g hg
    rw [mem_altStabilizer_iff] at hg ⊢
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg _ hpF
    · rw [Finset.mem_singleton.mp hi]
      exact hg _ hqF
  have hKL : layerPre θ (altStabilizer 9 {p, σ p}) ≤ CGT6.conjClosure Y G := layerPre_le θ _
  have hKG : layerPre θ (altStabilizer 9 {p, σ p}) ≤ G := hKL.trans hLG
  have hKt : ∀ k ∈ layerPre θ (altStabilizer 9 {p, σ p}), t * k * t⁻¹ ∈
      layerPre θ (altStabilizer 9 {p, σ p}) := by
    refine conj_mem_layerPre (fun l hl => conj_mem_conjClosure htG hl) hσ ?_
    intro g hg g' hg'
    rw [mem_altStabilizer_iff] at hg ⊢
    have hg'i : ∀ i, (g' : Equiv.Perm (Fin 9)) i = σ ((g : Equiv.Perm (Fin 9)) (σ i)) := by
      intro i
      rw [hg', hσinv]
      rfl
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hg'i, hg _ (by simp), hσσ]
    · rw [Finset.mem_singleton.mp hi, hg'i, hσσ, hg _ (by simp)]
  have hKA7 := nonempty_layerPre_alt θ hpq
  have hKcard : Nat.card ↥(layerPre θ (altStabilizer 9 {p, σ p})) = 2520 := by
    rw [card_layerPre_pair θ hpq (by norm_num)]
    decide
  have hKneY : layerPre θ (altStabilizer 9 {p, σ p}) ≠ Y := by
    intro h
    rw [h, hY60] at hKcard
    omega
  have hsmall : Nat.card ↥(layerPre θ (altStabilizer 9 {p, σ p}) ⊔ Subgroup.zpowers t) <
      Nat.card ↥G := by
    have hle : layerPre θ (altStabilizer 9 {p, σ p}) ⊔ Subgroup.zpowers t ≤ G :=
      sup_le hKG (Subgroup.zpowers_le.mpr htT |>.trans cfg.adm.hTG)
    by_contra hnot
    have heq := Subgroup.eq_of_le_of_card_ge hle (not_lt.mp hnot)
    have hnorm : G ≤ Subgroup.normalizer (layerPre θ (altStabilizer 9 {p, σ p}) :
        Set (MulAut V)) :=
      heq.symm.le.trans (ih4_sup_le_normalizer ht2 hKt)
    have hKn : ((layerPre θ (altStabilizer 9 {p, σ p})).subgroupOf
        (CGT6.conjClosure Y G)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 (hLG.trans hnorm)
    have hsimpleL : IsSimpleGroup ↥(CGT6.conjClosure Y G) := by
      have : IsSimpleGroup (alternatingGroup (Fin 9)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact θ.isSimpleGroup
    rcases hKn.eq_bot_or_eq_top with hbot | htop
    · have hK1 : layerPre θ (altStabilizer 9 {p, σ p}) = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        have h1 : (⟨k, hKL hk⟩ : ↥(CGT6.conjClosure Y G)) ∈
            (layerPre θ (altStabilizer 9 {p, σ p})).subgroupOf (CGT6.conjClosure Y G) := hk
        rw [hbot, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
      rw [hK1, Subgroup.card_bot] at hKcard
      omega
    · have h1 : CGT6.conjClosure Y G ≤ layerPre θ (altStabilizer 9 {p, σ p}) :=
        Subgroup.subgroupOf_eq_top.mp htop
      have h2 : layerPre θ (altStabilizer 9 {p, σ p}) = CGT6.conjClosure Y G :=
        le_antisymm hKL h1
      have h3 := Nat.card_congr θ.toEquiv
      rw [card_alt9] at h3
      rw [h2, h3] at hKcard
      omega
  obtain ⟨θ₀, hnat⟩ := ih_natural_K hV cfg.toEmb4Cfg htT ht1 ht2 hKY hKG hKt hKA7 hY60 hKneY hsmall
  have hrec := rec418 (k := 7) hV (by decide) (le_refl 7) θ hpq hKL
    (map_subgroupOf_layerPre θ _) θ₀ hnat (fix_conjClosure_trivial hV cfg)
    (commV_conjClosure_eq_top hV cfg)
  have hlift := natLift_holds V hV (CGT6.conjClosure Y G) Y 4 2 (by norm_num) (by norm_num)
    (by norm_num) θ hrec F (by omega) hYL hH
  exact cfg.nolift ⟨CGT6.conjClosure Y G, hYL, hLG, hLn.isSubnormal, Or.inl hlift⟩

theorem end4Small_a9 : End4Small fun Q _ => Nonempty (Q ≃* alternatingGroup (Fin 9)) := by
  intro V _ _ hV G T Y cfg hY2 ⟨e⟩
  obtain ⟨t, htT, ht2, ht1⟩ := exists_involution_of_T cfg
  have htG := cfg.adm.hTG htT
  obtain ⟨σ, hσ⟩ := exists_sigma (by norm_num) (by norm_num) e htG
  have hσ1 := sigma_ne_one cfg e htG ht2 ht1 hσ
  have hσ2 := sigma_sq (by norm_num) e htG ht2 hσ
  have hσc := sigma_comm cfg e htT hσ
  obtain ⟨θ, hθ⟩ := exists_theta_a9 cfg e
  have hσθ := sigma_theta hθ htG hσ
  have := isSimpleGroup_piY hY2 e
  rcases a9_config _ (card_piY hY2 e) σ hσ1 hσ2 hσc with
    ⟨F, hF, hH, hFσ⟩ | ⟨a, b, hab, hσab, hfix⟩
  · rw [← hθ] at hH
    exact a9_four_false hV cfg hY2 htT ht1 ht2 hσθ hσ1 hσ2 hF hH hFσ
  · rw [← hθ] at hfix
    exact a9_swap_false cfg hY2 htT ht1 ht2 hσθ hab hσab hfix

end CFSG.CGT.PushingUpLit.CGT6X.End4
