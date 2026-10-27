module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAltRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Equiv Equiv.Perm GSThmB.Catalog82A10

theorem card_altOn_le_sixty {n : ℕ} {T : Finset (Fin n)} (hT : T.card ≤ 5) :
    Nat.card (altOn T) ≤ 60 := by
  by_cases h2 : 2 ≤ T.card
  · rw [card_altOn T h2]
    have h120 : T.card.factorial ≤ 120 := by
      calc T.card.factorial ≤ (5 : ℕ).factorial := Nat.factorial_le hT
        _ = 120 := by decide
    omega
  · push Not at h2
    have hbot : altOn T = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [mem_bot]
      have hs := (mem_altOn.mp hg).2
      have hc : g.support.card ≤ 1 := (Finset.card_le_card hs).trans (by omega)
      have hc0 : g.support.card = 0 := by
        have := Perm.card_support_ne_one g
        omega
      exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hc0)
    rw [hbot, card_bot]
    omega

variable {Y : Type} [Group Y] [Finite Y]

theorem hinFor_alt :
    HinFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  intro Y _ _ _ ⟨n, hn5, ⟨e⟩⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  classical
  set C := fixedPoints τ with hCdef
  set L := GSThmB.layerIn C with hLdef
  have h168 : 168 ≤ Nat.card L := le_card_of_lieModel_psl2_sixteen hp2 h16 hL
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  have hnt : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcardY : Nat.card Y = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have hLY : Nat.card L ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card L
  by_cases hn6 : n ≤ 6
  · exfalso
    obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
    have hq7 := seven_le_of_sixteen_dvd hp hp2 hm h16
    have hLc : Nat.card L = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eL.toEquiv, GorensteinWalter.psl2_card_formula F'
        (AutL2Facts.isOddPrimePower_of hpP hp2 hm1 hF'), hF']
    interval_cases n
    · rw [hcardY] at hLY
      have := Nat.le_of_dvd (by decide) hLY
      norm_num at this
      omega
    · rw [hcardY] at hLY
      have hle := Nat.le_of_dvd (by decide) hLY
      norm_num at hle hLY
      set q := p ^ m with hqdef
      have hq9 : q ≤ 9 := by
        by_contra hgt
        push Not at hgt
        have h10' : 10 ≤ q := by omega
        have h10 : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
          apply Nat.mul_le_mul h10'
          have : 10 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h10' 2
          omega
        omega
      have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
      have hq : q = 7 ∨ q = 9 := by
        obtain ⟨j, hj⟩ := hqodd
        omega
      rcases hq with hq | hq
      · rw [hLc, hq] at hLY
        norm_num at hLY
      ·
        have hcard : Nat.card L = Nat.card Y := by
          rw [hLc, hq, hcardY]
          decide
        have htop : L = ⊤ := Subgroup.eq_top_of_card_eq L hcard
        apply hτ1
        ext y
        have hyL : y ∈ L := htop ▸ mem_top y
        exact (map_subtype_le _ hyL : y ∈ C)
  push Not at hn6
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega)
    (by omega)
  set κ : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal with hκ
  obtain ⟨σ, hσ⟩ := hbij.2 (MulAut.congr e τ)
  have hσσ : σ * σ = 1 := by
    apply hbij.1
    rw [map_mul, hσ, map_one, ← map_mul]
    have hsq : τ * τ = 1 := by
      have := pow_orderOf_eq_one τ
      rw [hτ, pow_two] at this
      exact this
    rw [hsq, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hτ1
    apply (MulAut.congr e).injective
    rw [← hσ, map_one, map_one]
  have hmemC : ∀ y : Y, y ∈ C ↔ (e y : Perm (Fin n)) * σ = σ * (e y : Perm (Fin n)) := by
    intro y
    have h1 : e (τ y) = κ σ (e y) := by
      rw [hσ]
      change e (τ y) = e (τ (e.symm (e y)))
      rw [MulEquiv.symm_apply_apply]
    have h2 : ((κ σ (e y) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        σ * (e y : Perm (Fin n)) * σ⁻¹ := MulAut.conjNormal_apply σ (e y)
    change τ y = y ↔ _
    constructor
    · intro hy
      have h3 : σ * (e y : Perm (Fin n)) * σ⁻¹ = (e y : Perm (Fin n)) := by
        rw [← h2, ← h1, hy]
      calc (e y : Perm (Fin n)) * σ = σ * (e y : Perm (Fin n)) * σ⁻¹ * σ := by rw [h3]
        _ = σ * (e y : Perm (Fin n)) := by group
    · intro hy
      apply e.injective
      apply Subtype.ext
      rw [h1, h2, ← hy, mul_inv_cancel_right]
  set LP : Subgroup (Perm (Fin n)) :=
    (L.map e.toMonoidHom).map (alternatingGroup (Fin n)).subtype with hLPdef
  let eLP : ↥L ≃* ↥LP := ((L.equivMapOfInjective _ e.injective).trans
    ((L.map e.toMonoidHom).equivMapOfInjective _ (alternatingGroup (Fin n)).subtype_injective))
  have hs := isSimpleGroup_pLayer hL
  have hLs : IsSimpleGroup ↥L := (layerInEquiv C).isSimpleGroup
  have hLPs : IsSimpleGroup ↥LP := eLP.symm.isSimpleGroup
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := nonabelian_of_lieModel_psl2 hL
  have hLPnab : ∃ a b : ↥LP, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eLP a, eLP b, fun h => hab (eLP.injective (by rw [map_mul, map_mul, h]))⟩
  have hLperf : ⁅L, L⁆ = L := by
    have hq := (LocalCores.isQuasisimple_of_isSimpleGroup hLnab).1
    have h := congrArg (Subgroup.map L.subtype) hq.1.commutator_eq_top
    rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  have hLPperf : ⁅LP, LP⁆ = LP := by
    rw [hLPdef, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hLperf]
  have hLPC : ∀ g ∈ LP, g * σ = σ * g := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact (hmemC l).mp (map_subtype_le _ hl)
  have hLPn : ∀ x ∈ pairSub hσσ, x ∈ alternatingGroup (Fin n) → ∀ g ∈ LP, x * g * x⁻¹ ∈ LP := by
    rintro x hx hxA _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    set y := e.symm ⟨x, hxA⟩ with hydef
    have hey : (e y : Perm (Fin n)) = x := by rw [hydef, MulEquiv.apply_symm_apply]
    have hyC : y ∈ C := by
      rw [hmemC, hey]
      exact mem_centralizer_singleton_iff.mp (pairSub_le_centralizer hσσ hx)
    refine ⟨e (y * l * y⁻¹), ⟨y * l * y⁻¹, conj_mem_layerIn hyC hl, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, Subgroup.coe_subtype, hey]
  have hLPalt := le_altOn_of_normal hσσ hLPperf hLPs hLPnab hLPC hLPn
  have hfix6 : 6 ≤ (σ.support)ᶜ.card := by
    by_contra hlt
    push Not at hlt
    have h60 := card_altOn_le_sixty (T := (σ.support)ᶜ) (by omega)
    have hle := Subgroup.card_le_of_le hLPalt
    rw [← Nat.card_congr eLP.toEquiv] at hle
    omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hfix6
  let f : Fin 6 → Fin n := fun i => t.orderEmbOfFin htc i
  have hf : Function.Injective f := (t.orderEmbOfFin htc).injective
  have hfσ : ∀ i, σ (f i) = f i := fun i => by
    have h1 : f i ∈ (σ.support)ᶜ := hts (t.orderEmbOfFin_mem htc i)
    rw [Finset.mem_compl, Perm.mem_support, not_not] at h1
    exact h1
  obtain ⟨a, ha⟩ : σ.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hσ1 (Perm.support_eq_empty_iff.mp h)
  have haσ : σ a ≠ a := Perm.mem_support.mp ha
  obtain ⟨E, hEle, hEc, hEsq, hE8, hE'⟩ := exists_elemAbelian_of_points hσσ f hf hfσ haσ
  have hpull : ∀ {E : Subgroup (Perm (Fin n))}, E ≤ alternatingGroup (Fin n) ⊓ centralizer {σ} →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) → ∀ r : ℕ, 2 ^ r < Nat.card E →
      ¬ GH74.SectionalTwoRankLE ↥C r := by
    intro E hE hc hsq r hr
    set EY : Subgroup Y := (E.subgroupOf (alternatingGroup (Fin n))).map e.symm.toMonoidHom
    have hEA : E ≤ alternatingGroup (Fin n) := fun x hx => (hE hx).1
    have hEY : Nat.card EY = Nat.card E := by
      rw [Subgroup.card_map_of_injective e.symm.injective,
        Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv]
    have hmemEY : ∀ y ∈ EY, (e y : Perm (Fin n)) ∈ E := by
      rintro _ ⟨z, hz, rfl⟩
      simpa [mem_subgroupOf] using hz
    refine not_sectionalTwoRankLE_of_le (E := EY) ?_ ?_ ?_ (hEY ▸ hr)
    · intro y hy
      rw [hmemC]
      exact mem_centralizer_singleton_iff.mp (hE (hmemEY y hy)).2
    · intro u hu v hv
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      exact hc _ (hmemEY u hu) _ (hmemEY v hv)
    · intro u hu
      apply e.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hsq _ (hmemEY u hu)
  refine hinConcl_of_rank (fun hinn => ?_) (fun _ => hpull hEle hEc hEsq 2 (by omega))
  obtain ⟨y, rfl⟩ := hinn
  have hσA : σ ∈ alternatingGroup (Fin n) := by
    have h1 : κ (e y : Perm (Fin n)) = MulAut.congr e (MulAut.conj y) := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hκ, MulAut.conjNormal_apply]
      change _ = ((e (y * e.symm z * y⁻¹) : alternatingGroup (Fin n)) : Perm (Fin n))
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    have h2 : σ = (e y : Perm (Fin n)) := hbij.1 (hσ.trans h1.symm)
    rw [h2]
    exact (e y).2
  obtain ⟨b, hb, hba, hbσa⟩ : ∃ b, σ b ≠ b ∧ b ≠ a ∧ b ≠ σ a := by
    have h2 : σ.support.card ≠ 2 := by
      intro h
      have hsw := Perm.card_support_eq_two.mp h
      have := hσA
      rw [mem_alternatingGroup, hsw.sign_eq] at this
      exact absurd this (by decide)
    have hσa : σ a ∈ σ.support := Perm.apply_mem_support.mpr ha
    have h3 : 3 ≤ σ.support.card := by
      have h1 := Perm.card_support_ne_one σ
      have h2' : 2 ≤ σ.support.card :=
        Finset.one_lt_card.mpr ⟨a, ha, σ a, hσa, fun h => haσ h.symm⟩
      omega
    obtain ⟨b, hb⟩ : ((σ.support.erase a).erase (σ a)).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.pred_card_le_card_erase (s := σ.support) (a := a)
      have := Finset.pred_card_le_card_erase (s := σ.support.erase a) (a := σ a)
      omega
    simp only [Finset.mem_erase] at hb
    exact ⟨b, Perm.mem_support.mp hb.2.2, hb.2.1, hb.1⟩
  obtain ⟨E', hE'le, hE'c, hE'sq, hE'16⟩ := hE' hσA b hb hba hbσa
  exact hpull hE'le hE'c hE'sq 3 (by omega)

end CFSG.ComponentClassification.HarrisLit.Hin
