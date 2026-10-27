module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.Quasithin.Vol2.KGFactC31M23

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M23

theorem KConfig.eq_of_orbSub_s
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) {y t c : G₀} (hy : y ∈ L) (ht : t ∈ V)
    (hU : orbSub y t = (eSub basis_s).map (MulAut.conj c).toMonoidHom) :
    V = (eSub basis_w).map (MulAut.conj c).toMonoidHom ∧
      L = Mw.map (MulAut.conj c).toMonoidHom := by
  let f : G₀ →* G₀ := (MulAut.conj c).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c).injective
  have hftop : f.range = ⊤ := MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective
  set Wt : Subgroup G₀ := (eSub basis_w).map f with hWt
  set Ut : Subgroup G₀ := (eSub basis_s).map f with hUt
  set Nt : Subgroup G₀ := Mw.map f with hNt
  have hU' : orbSub y t = Ut := hU
  have hUV : Ut ≤ V := hU' ▸ orbSub_le (h.le_normalizer hy) ht
  have hCS : Subgroup.centralizer (Ut : Set G₀) = Wt := by
    have h := map_centralizer_eq f hf (eSub basis_s)
    rw [hftop, top_inf_eq, centralizer_s_eq] at h
    exact h.symm
  have hCW0 : Subgroup.centralizer (eSub basis_w : Set G₀) = eSub basis_w :=
    le_antisymm cent_w fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => eSub_comm basis_w _ _ hy hx
  have hCW : Subgroup.centralizer (Wt : Set G₀) = Wt := by
    have h := map_centralizer_eq f hf (eSub basis_w)
    rw [hftop, top_inf_eq, hCW0] at h
    exact h.symm
  have hVC : V ≤ Subgroup.centralizer (V : Set G₀) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1
  have hCVle : Subgroup.centralizer (V : Set G₀) ≤ Wt := by
    rw [← hCS]
    exact Subgroup.centralizer_le hUV
  have hVW : V ≤ Wt := hVC.trans hCVle
  have hCV : Subgroup.centralizer (V : Set G₀) = Wt := by
    refine le_antisymm hCVle ?_
    rw [← hCW]
    exact Subgroup.centralizer_le hVW
  have hW2 : IsPGroup 2 ↥Wt := IsPGroup.of_card (n := 4) (by
    rw [hWt, Subgroup.card_map_of_injective hf, card_eSub])
  have hWne : Wt ≠ ⊥ := by
    intro hbot
    exact h.ne_bot (le_antisymm (hVW.trans (le_of_eq hbot)) bot_le)
  have hInv : ∀ σ : G₀ ≃* G₀, V.map σ.toMonoidHom = V → L.map σ.toMonoidHom = L →
      MK.map σ.toMonoidHom = MK → Wt.map σ.toMonoidHom = Wt := by
    intro σ hσV _ _
    have h := map_centralizer_eq σ.toMonoidHom σ.injective V
    rw [MonoidHom.range_eq_top.mpr σ.surjective, top_inf_eq] at h
    rw [hCV, hσV, hCV] at h
    exact h
  have hNWMK : Subgroup.normalizer (Wt : Set G₀) ≤ MK :=
    h.normalizer_le Wt hWne hW2 hInv
  have hNWNL : Subgroup.normalizer (Wt : Set G₀) ≤ Subgroup.normalizer (L : Set G₀) :=
    hNWMK.trans h.MK_le_normalizer
  have hLNW : L ≤ Subgroup.normalizer (Wt : Set G₀) := by
    rw [← hCV]
    exact h.le_normalizer.trans (normalizer_le_normalizer_centralizer V)
  have hNW : Subgroup.normalizer (Wt : Set G₀) = Nt := by
    have h := map_normalizer_eq f hf (eSub basis_w)
    rw [hftop, top_inf_eq] at h
    rw [← h, hNt, Mw_eq]
  have hN'L : Nt ≤ Subgroup.normalizer (L : Set G₀) := by
    rw [← hNW]
    exact hNWNL
  have hN'W : Nt ≤ Subgroup.normalizer (Wt : Set G₀) := le_of_eq hNW.symm
  have hsup_le : L ⊔ Wt ≤ Nt :=
    sup_le (hLNW.trans (le_of_eq hNW)) (Subgroup.le_normalizer.trans (le_of_eq hNW))
  have hNsup : Nt ≤ Subgroup.normalizer ((L ⊔ Wt : Subgroup G₀) : Set G₀) := by
    intro g hg
    exact mem_normalizer_sup (hN'L hg) (hN'W hg)
  have hdW : RefData Wt Nt := by
    rw [hWt, hNt]
    exact RefData.map_mulEquiv refData_w (MulAut.conj c)
  have hsup_case : L ⊔ Wt = Wt ∨ L ⊔ Wt = Nt :=
    hdW.simple (L ⊔ Wt) le_sup_right hsup_le hNsup
  rcases hsup_case with hsupW | hsupN
  · exfalso
    have hLle : L ≤ Wt := hsupW ▸ le_sup_left
    have hLbot : L = ⊥ := by
      rw [← h.perfect, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hdW.comm x (hLle hx) z (hLle hz)).symm
    have hVbot : V = ⊥ := by
      rw [h.eq_commutator, hLbot, Subgroup.commutator_bot_right]
    exact h.ne_bot hVbot
  ·
    have hNinf : Nt ≤ Subgroup.normalizer ((L ⊓ Wt : Subgroup G₀) : Set G₀) := by
      intro g hg
      exact mem_normalizer_inf (hN'L hg) (hN'W hg)
    have hInf_case : L ⊓ Wt = ⊥ ∨ L ⊓ Wt = Wt :=
      irr_map f hf inf_le_right hNinf
    have hVinf : V ≤ L ⊓ Wt :=
      le_inf (h.le_pCoreOf.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hVW
    have hWleL : Wt ≤ L := by
      rcases hInf_case with hbot | htop
      · exfalso
        have hVbot : V = ⊥ := le_antisymm (hVinf.trans (le_of_eq hbot)) bot_le
        exact h.ne_bot hVbot
      · exact htop.symm.le.trans inf_le_left
    have hL_eq : L = Nt := by
      rw [← hsupN, sup_eq_left.mpr hWleL]
    have hN'V : Nt ≤ Subgroup.normalizer (V : Set G₀) := by
      rw [← hL_eq]
      exact h.le_normalizer
    rcases irr_map f hf hVW hN'V with hVbot | hVWt
    · exact absurd hVbot h.ne_bot
    · exact ⟨hVWt.trans hWt, hL_eq.trans hNt⟩

theorem KConfig.m23_cases
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) :
    ∃ g : G₀,
      (V = (eSub basis_duad).map (MulAut.conj g).toMonoidHom ∧
        L = Mduad.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_w).map (MulAut.conj g).toMonoidHom ∧
        L = Mw.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_e8).map (MulAut.conj g).toMonoidHom ∧
        L = (eNorm basis_e8).map (MulAut.conj g).toMonoidHom) := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := h.elemAbelian.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have hpd : p ∣ 10200960 := by
    by_contra hpd
    have h1 : y = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Schreier.m23_card]) ⟨k, hyk⟩
    apply hyt
    rw [h1, one_mul, inv_one, mul_one]
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 10200960 / p → ∃ (g y₁ t₁ : G₀),
      y₁ ∈ Subgroup.zpowers x ∧ y₁ * t₁ * y₁⁻¹ ≠ t₁ ∧ orderOf t₁ = 2 ∧
        (∀ j : ℕ, t₁ * (y₁ ^ j * t₁ * y₁⁻¹ ^ j) = y₁ ^ j * t₁ * y₁⁻¹ ^ j * t₁) ∧
        orbSub y t = (orbSub y₁ t₁).map (MulAut.conj g).toMonoidHom := by
    intro x hx hpi
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨k, hyk⟩
    let f : G₀ →* G₀ := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    have hconj : ∀ z : G₀, f (g⁻¹ * z * g) = z := fun z => by
      change (MulAut.conj g).toMonoidHom (g⁻¹ * z * g) = z
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hfy : f (g⁻¹ * y * g) = y := hconj y
    have hft : f (g⁻¹ * t * g) = t := hconj t
    generalize g⁻¹ * y * g = y₁ at hg hfy
    generalize g⁻¹ * t * g = t₁ at hft
    refine ⟨g, y₁, t₁, hg, fun h => hyt ?_, ?_, fun j => hf ?_, ?_⟩
    · have := congrArg f h
      rwa [map_mul, map_mul, map_inv, hfy, hft] at this
    · rw [← ht2, ← hft, orderOf_injective f hf]
    · simp only [map_mul, map_pow, map_inv, hfy, hft]
      exact hcommA j
    · rw [orbSub_map, hfy, hft]
  have hcomp : ∀ a b : G₀, ((MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom) =
      (MulAut.conj (a * b)).toMonoidHom := by
    intro a b
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rcases prime_dvd_m23 hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    rcases orbSub_cases5 hg hord hmv (fun j _ => hcm j) with ⟨c, hcase⟩ | ⟨c, hcase⟩
    · rw [hcase, Subgroup.map_map, hcomp g c] at hU
      have hd : RefData ((eSub basis_duad).map (MulAut.conj (g * c)).toMonoidHom)
          (Mduad.map (MulAut.conj (g * c)).toMonoidHom) :=
        RefData.map_mulEquiv refData_duad (MulAut.conj (g * c))
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g * c, Or.inl ⟨hV, hL⟩⟩
    · rw [hcase, Subgroup.map_map, hcomp g c] at hU
      have hd : RefData ((eSub basis_w).map (MulAut.conj (g * c)).toMonoidHom)
          (Mw.map (MulAut.conj (g * c)).toMonoidHom) :=
        RefData.map_mulEquiv refData_w (MulAut.conj (g * c))
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g * c, Or.inr (Or.inl ⟨hV, hL⟩)⟩
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    rcases orbSub_cases7 hg hord hmv (fun j _ => hcm j) with ⟨c, hcase⟩ | ⟨c, hcase⟩ | ⟨c, hcase⟩
    · rw [hcase, Subgroup.map_map, hcomp g c] at hU
      have hd : RefData ((eSub basis_e8).map (MulAut.conj (g * c)).toMonoidHom)
          ((eNorm basis_e8).map (MulAut.conj (g * c)).toMonoidHom) :=
        RefData.map_mulEquiv refData_e8 (MulAut.conj (g * c))
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g * c, Or.inr (Or.inr ⟨hV, hL⟩)⟩
    · rw [hcase, Subgroup.map_map, hcomp g c] at hU
      have hd : RefData ((eSub basis_w).map (MulAut.conj (g * c)).toMonoidHom)
          (Mw.map (MulAut.conj (g * c)).toMonoidHom) :=
        RefData.map_mulEquiv refData_w (MulAut.conj (g * c))
      obtain ⟨hV, hL⟩ := KConfig.eq_of_refData h hd hy ht hU
      exact ⟨g * c, Or.inr (Or.inl ⟨hV, hL⟩)⟩
    · rw [hcase, Subgroup.map_map, hcomp g c] at hU
      obtain ⟨hV, hL⟩ := KConfig.eq_of_orbSub_s h hy ht hU
      exact ⟨g * c, Or.inr (Or.inl ⟨hV, hL⟩)⟩
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    exact (not_bad11 hg hord hmv fun j _ => hcm j).elim
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x23 orderOf_x23 (by norm_num)
    exact (not_bad23 hg hord hmv fun j _ => hcm j).elim

end CFSG.SectionRank.QTK.Insp443

end
