module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitQuot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ExitTenCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section Perm

variable {m n : ℕ}

theorem viaEmbedding_mem_permSetStab (ι : Fin m ↪ Fin n) (σ : Perm (Fin m)) :
    viaEmbedding σ ι ∈ permSetStab (Set.range ι) := by
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [viaEmbedding_apply]
    exact ⟨fun _ => ⟨i, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  · rw [viaEmbedding_apply_of_notMem _ _ _ hx]

theorem conj_viaEmbedding (ι : Fin m ↪ Fin n) (g : ↥(permSetStab (Set.range ι)))
    (σ : Perm (Fin m)) :
    (g : Perm (Fin n)) * viaEmbedding σ ι * (g : Perm (Fin n))⁻¹ =
      viaEmbedding (restrictPerm ι g * σ * (restrictPerm ι g)⁻¹) ι := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    have h1 : (g : Perm (Fin n))⁻¹ (ι i) = ι ((restrictPerm ι g)⁻¹ i) := by
      have := restrictPerm_apply_apply ι g⁻¹ i
      rw [map_inv] at this
      exact this.symm
    rw [Perm.mul_apply, Perm.mul_apply, h1, viaEmbedding_apply, ← restrictPerm_apply_apply,
      viaEmbedding_apply, Perm.mul_apply, Perm.mul_apply]
  · have hgx : (g : Perm (Fin n))⁻¹ x ∉ Set.range ι := fun h => hx (((g⁻¹).2 x).1 h)
    rw [Perm.mul_apply, Perm.mul_apply, viaEmbedding_apply_of_notMem _ _ _ hgx,
      perm_apply_inv_apply, viaEmbedding_apply_of_notMem _ _ _ hx]

end Perm

theorem exitTenOdd : ExitTenOdd := by
  intro V _ _ hV H ψ hψ hAlt _ A hA hAL p q hpq horb hmin ι hι τ hτ hDW hC hex
  exfalso
  classical
  obtain ⟨hE1, hE2, hE3⟩ := hex
  have hrange := mem_range_of_not_le_altPre hAlt hA.1 hAL
  have hτ2 : (τ : MulAut V) ^ 2 = 1 := by
    have h1 : τ ^ 2 = 1 := hψ (by rw [map_pow, hτ, pow_two, swap_mul_self, map_one])
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hkerκ : ∀ k : ↥(preSub ψ (permSetStab (Set.range ι))),
      restrictHom ψ ι _ le_rfl k = 1 → (k : MulAut V) = 1 ∨ (k : MulAut V) = τ := fun k hk => by
    rcases eq_one_or_eq_swap_of_range_ne_ne hpq hι (apply_mem_permSetStab (hK := le_rfl) k)
        ((restrictHom_eq_one_iff k).1 hk) with h | h
    · exact Or.inl (congrArg Subtype.val (hψ (h.trans (map_one ψ).symm)))
    · exact Or.inr (congrArg Subtype.val (hψ (h.trans hτ.symm)))
  have hkerW : ∀ k : ↥(preSub ψ (permSetStab (Set.range ι))),
      restrictHom ψ ι _ le_rfl k = 1 →
        ∀ w ∈ fixV (Subgroup.zpowers (τ : MulAut V)), (k : MulAut V) w = w := fun k hk w hw => by
    rcases hkerκ k hk with h | h
    · rw [h]
      rfl
    · rw [h]
      exact hw _ (Subgroup.mem_zpowers _)
  have hψWinj := autSubLift_injective (hKW := hDW) (hC := hC) hkerW
  have hψWtop : (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC).range = ⊤ := by
    rw [range_autSubLift, eq_top_iff]
    intro σ _
    obtain ⟨h, hh⟩ := hrange (viaEmbedding σ ι)
    have hhD : (h : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
      coe_mem_preSub.2 (hh ▸ viaEmbedding_mem_permSetStab ι σ)
    refine ⟨⟨h, hhD⟩, (restrictHom_eq_iff _ σ).2 fun i => ?_⟩
    change ψ h (ι i) = ι (σ i)
    rw [hh, viaEmbedding_apply]
  have hψWA : alternatingGroup (Fin 8) ≤
      (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC).range := by
    rw [hψWtop]
    exact le_top
  have hAD : A ≤ preSub ψ (permSetStab (Set.range ι)) := fun a ha =>
    (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2 (mem_permSetStab_of_pair hι (horb ⟨a, hA.1 ha⟩ ha))
  have hAW : ∀ a ∈ A, ∀ w ∈ fixV (Subgroup.zpowers (τ : MulAut V)),
      a w ∈ fixV (Subgroup.zpowers (τ : MulAut V)) := fun a ha w hw => ((hDW (hAD ha)) w).2 hw
  have hfixA : ∀ i, ∃ a : ↥(preSub ψ (permSetStab (Set.range ι))), (a : MulAut V) ∈ A ∧
      restrictHom ψ ι _ le_rfl a i ≠ i := fun i => by
    obtain ⟨a, ha, hai⟩ := hmin (ι i)
    refine ⟨⟨a, hAD ha⟩, ha, fun h => hai ?_⟩
    have := restrictHom_apply_apply (hK := le_rfl) ⟨(a : MulAut V), hAD ha⟩ i
    rw [h] at this
    exact this.symm
  have hWA : commSub (fixV (Subgroup.zpowers (τ : MulAut V))) A ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, hai⟩ := hfixA 0
    exact hai (by rw [hC a fun w hw => (commSub_eq_bot_iff.1 hbot) hw _ ha]; rfl)
  have hoffW := isFFStarOffender_autSub hA hAW hWA (autSub_mono hAD _)
  have hW2 := B1.sq_eq_one_sub hV (fixV (Subgroup.zpowers (τ : MulAut V)))
  have hm : rk (autSub A (fixV (Subgroup.zpowers (τ : MulAut V)))) =
      rkIdx (fixV (autSub A (fixV (Subgroup.zpowers (τ : MulAut V))))) :=
    ((B1.card_eq_iff hW2 hoffW.2.2.1).1 (hE3 hψWtop _ hoffW)).symm
  have hCW : ∀ y : ↥(autSub (preSub ψ (permSetStab (Set.range ι)))
      (fixV (Subgroup.zpowers (τ : MulAut V)))),
      (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC y).IsThreeCycle →
        fixV (Subgroup.zpowers (y : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V))))) =
          fixV (altPre (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC)) :=
    fun y hy => fixV_zpowers_eq_of_exotic hE1 hE2 hy
  rcases B7_1_3 hV hA hAW hWA hm with ⟨hbot, htop⟩ | ⟨hoff0, -⟩
  ·
    have hτA : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ≠ swap p q := by
      intro a ha h
      have h1 : a = τ := hψ (h.trans hτ.symm)
      have h2 : (τ : MulAut V) ∈ A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V))) :=
        ⟨h1 ▸ ha, fun w hw => hw _ (Subgroup.mem_zpowers _)⟩
      rw [hbot, Subgroup.mem_bot] at h2
      have h3 : ψ τ = 1 := by rw [show τ = 1 from Subtype.ext h2, map_one]
      rw [hτ] at h3
      have h4 := congrArg (fun π : Perm (Fin 10) => π p) h3
      simp only [swap_apply_left, Perm.one_apply] at h4
      exact hpq h4.symm
    have hAq : ∀ a ∈ A, a ∈ centQuot (fixV (Subgroup.zpowers (τ : MulAut V))) := by
      intro a ha v
      have hv : v ∈ fixV (Subgroup.zpowers (τ : MulAut V)) ⊔ fixV A := htop ▸ Subgroup.mem_top v
      obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
      have hac : a c = c := hc a ha
      rw [map_mul, hac, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
      exact Subgroup.mul_mem _ (hAW a ha w hw) (Subgroup.inv_mem _ hw)
    let e₈ : alternatingGroup (Fin 8) →* ↥H := (altPreInv hψ hAlt).comp (altLift ι)
    have hψe₈ : ∀ σ, ψ (e₈ σ) = viaEmbedding (σ : Perm (Fin 8)) ι := fun σ =>
      (apply_altPreInv hψ hAlt _).trans (coe_altLift ι σ)
    have he₈D : ∀ σ, ((e₈ σ : ↥H) : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) := fun σ =>
      coe_mem_preSub.2 (by rw [hψe₈]; exact viaEmbedding_mem_permSetStab ι _)
    have hEW : ∀ σ : alternatingGroup (Fin 8), ((e₈ σ : ↥H) : MulAut V) ∈
        centQuot (fixV (Subgroup.zpowers (τ : MulAut V))) := by
      let N : Subgroup (alternatingGroup (Fin 8)) :=
        (centQuot (fixV (Subgroup.zpowers (τ : MulAut V)))).comap (H.subtype.comp e₈)
      have hN : N.Normal := ⟨fun σ hσ ρ => by
        change ((e₈ (ρ * σ * ρ⁻¹) : ↥H) : MulAut V) ∈ centQuot _
        rw [map_mul, map_mul, map_inv]
        exact conj_mem_centQuot (hDW (he₈D ρ)) hσ⟩
      have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
      rcases hN.eq_bot_or_eq_top with hNb | hNt
      · exfalso
        obtain ⟨a, haA, hai⟩ := hfixA 0
        have hacomm : ∀ σ : alternatingGroup (Fin 8),
            restrictHom ψ ι _ le_rfl a * (σ : Perm (Fin 8)) =
              σ * restrictHom ψ ι _ le_rfl a := by
          intro σ
          have hσ' : restrictHom ψ ι _ le_rfl a * (σ : Perm (Fin 8)) *
              (restrictHom ψ ι _ le_rfl a)⁻¹ ∈ alternatingGroup (Fin 8) :=
            alternatingGroup.normal.conj_mem _ σ.2 _
          have hconj : (a : MulAut V) * ((e₈ σ : ↥H) : MulAut V) * (a : MulAut V)⁻¹ =
              ((e₈ ⟨_, hσ'⟩ : ↥H) : MulAut V) := by
            refine coe_eq_coe_of_apply_eq hψ
              (h₁ := Subgroup.inclusion (le_rfl.trans preSub_le) a * e₈ σ *
                (Subgroup.inclusion (le_rfl.trans preSub_le) a)⁻¹) (h₂ := e₈ ⟨_, hσ'⟩) ?_
            rw [map_mul, map_mul, map_inv, hψe₈, hψe₈]
            exact conj_viaEmbedding ι ⟨_, apply_mem_permSetStab (hK := le_rfl) a⟩ σ
          have hmem : ((e₈ (⟨_, hσ'⟩ * σ⁻¹) : ↥H) : MulAut V) ∈
              centQuot (fixV (Subgroup.zpowers (τ : MulAut V))) := by
            rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, ← hconj]
            have h1 := hAq _ haA
            have h2 := conj_mem_centQuot (hDW (he₈D σ)) (Subgroup.inv_mem _ h1)
            have h3 := Subgroup.mul_mem _ h1 h2
            simpa only [mul_assoc] using h3
          have h1 : ⟨_, hσ'⟩ * σ⁻¹ ∈ N := hmem
          rw [hNb, Subgroup.mem_bot] at h1
          have h2 : restrictHom ψ ι _ le_rfl a * (σ : Perm (Fin 8)) *
              (restrictHom ψ ι _ le_rfl a)⁻¹ = σ :=
            congrArg Subtype.val (mul_inv_eq_one.1 h1)
          calc restrictHom ψ ι _ le_rfl a * (σ : Perm (Fin 8)) =
                restrictHom ψ ι _ le_rfl a * σ * (restrictHom ψ ι _ le_rfl a)⁻¹ *
                  restrictHom ψ ι _ le_rfl a := by group
            _ = σ * restrictHom ψ ι _ le_rfl a := by rw [h2]
        have hπ1 : restrictHom ψ ι _ le_rfl a = 1 :=
          eq_one_of_commute_alt (by norm_num) fun σ hσ => hacomm ⟨σ, hσ⟩
        exact hai (by rw [hπ1]; rfl)
      · intro σ
        have h1 : σ ∈ N := hNt ▸ Subgroup.mem_top σ
        exact h1
    have hEx : ∀ x : ↥H, (ψ x).IsThreeCycle → ψ x p = p → ψ x q = q →
        ∃ hxD : (x : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)),
          (restrictHom ψ ι _ le_rfl ⟨x, hxD⟩).IsThreeCycle ∧
          (x : MulAut V) ∈ centQuot (fixV (Subgroup.zpowers (τ : MulAut V))) := by
      intro x hx3 hxp hxq
      have hxD : (x : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
        coe_mem_preSub.2 (mem_permSetStab_of_pair hι (Or.inl ⟨hxp, hxq⟩))
      set k : ↥(preSub ψ (permSetStab (Set.range ι))) := ⟨x, hxD⟩ with hk
      have hinc : Subgroup.inclusion (le_rfl.trans preSub_le) k = x := Subtype.ext rfl
      have hfix : ∀ y, y ∉ Set.range ι →
          ψ (Subgroup.inclusion (le_rfl.trans preSub_le) k) y = y := by
        intro y hy
        rw [hι, not_and_or, not_not, not_not] at hy
        rw [hinc]
        rcases hy with rfl | rfl
        · exact hxp
        · exact hxq
      have hx3' : (ψ (Subgroup.inclusion (le_rfl.trans preSub_le) k)).IsThreeCycle := by
        rw [hinc]
        exact hx3
      have h3k := isThreeCycle_restrictHom (hK := le_rfl) k hx3' hfix
      refine ⟨hxD, h3k, ?_⟩
      have hve := viaEmbedding_restrictHom (hK := le_rfl) k hfix
      rw [hinc] at hve
      have hxe : e₈ ⟨_, h3k.mem_alternatingGroup⟩ = x := hψ (by rw [hψe₈]; exact hve)
      rw [← hxe]
      exact hEW _
    have hinv : ∀ w : V, w⁻¹ = w := fun w =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV w)
    have hEU : ∀ x : ↥H, (ψ x).IsThreeCycle → ψ x p = p → ψ x q = q →
        (∀ v, (x : MulAut V) v * v⁻¹ ∈
          (commV (altPre (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC))).map
            (fixV (Subgroup.zpowers (τ : MulAut V))).subtype) ∧
        (∀ w ∈ (commV (altPre (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC))).map
            (fixV (Subgroup.zpowers (τ : MulAut V))).subtype,
          (x : MulAut V) w = w → w = 1) := by
      intro x hx3 hxp hxq
      obtain ⟨hxD, h3k, hxW⟩ := hEx x hx3 hxp hxq
      set xW := autSubHom hDW (⟨x, hxD⟩ : ↥(preSub ψ (permSetStab (Set.range ι)))) with hxW_def
      have hxW3 : (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC xW).IsThreeCycle := by
        rw [hxW_def, autSubLift_apply]
        exact h3k
      have hxWL : (xW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V)))) ∈
          altPre (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC) :=
        coe_mem_altPre_iff.2 hxW3.mem_alternatingGroup
      have hx3V : (x : MulAut V) ^ 3 = 1 := by
        have h1 : x ^ 3 = 1 := hψ (by rw [map_pow, map_one, ← hx3.orderOf, pow_orderOf_eq_one])
        rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
      have hx3f : ∀ v, (x : MulAut V) ((x : MulAut V) ((x : MulAut V) v)) = v := fun v => by
        have h1 := congrArg (fun φ : MulAut V => φ v) hx3V
        simpa [pow_succ, MulAut.mul_apply] using h1
      refine ⟨fun v => ?_, fun w hw hxw => ?_⟩
      ·
        have hu : (x : MulAut V) ((x : MulAut V) v) * ((x : MulAut V) v)⁻¹ ∈
            fixV (Subgroup.zpowers (τ : MulAut V)) := hxW _
        have hxu : (x : MulAut V) v * v⁻¹ =
            (x : MulAut V) ((x : MulAut V) ((x : MulAut V) v) * ((x : MulAut V) v)⁻¹) *
              ((x : MulAut V) ((x : MulAut V) v) * ((x : MulAut V) v)⁻¹)⁻¹ := by
          rw [map_mul, map_inv, hx3f]
          simp only [hinv]
          have hsq : (x : MulAut V) ((x : MulAut V) v) * (x : MulAut V) ((x : MulAut V) v) = 1 := by
            rw [← pow_two]
            exact hV _
          calc (x : MulAut V) v * v =
                (x : MulAut V) v * v *
                  ((x : MulAut V) ((x : MulAut V) v) * (x : MulAut V) ((x : MulAut V) v)) := by
                rw [hsq, mul_one]
            _ = v * (x : MulAut V) ((x : MulAut V) v) *
                  ((x : MulAut V) ((x : MulAut V) v) * (x : MulAut V) v) := by ac_rfl
        rw [hxu]
        exact ⟨(xW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V)))) ⟨_, hu⟩ *
          (⟨_, hu⟩ : ↥(fixV (Subgroup.zpowers (τ : MulAut V))))⁻¹, mul_inv_mem_commV hxWL _, rfl⟩
      · obtain ⟨w', hw', rfl⟩ := hw
        have h1 : (xW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V)))) w' = w' :=
          Subtype.ext hxw
        have h2 : w' ∈ fixV (Subgroup.zpowers
            (xW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V))))) ⊓
              commV (altPre (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC)) :=
          ⟨mem_fixV_zpowers_iff.2 h1, hw'⟩
        rw [hE2 xW hxW3, Subgroup.mem_bot] at h2
        rw [h2]
        rfl
    have hfixeq : ∀ x z : ↥H, (ψ x).IsThreeCycle → ψ x p = p → ψ x q = q →
        (ψ z).IsThreeCycle → ψ z p = p → ψ z q = q → (x : MulAut V) * z = z * x →
        fixV (Subgroup.zpowers (x : MulAut V)) ≤ fixV (Subgroup.zpowers (z : MulAut V)) := by
      intro x z hx3 hxp hxq hz3 hzp hzq hxz c hc
      rw [mem_fixV_zpowers_iff] at hc ⊢
      have h1 := (hEU z hz3 hzp hzq).1 c
      have h2 : (x : MulAut V) ((z : MulAut V) c * c⁻¹) = (z : MulAut V) c * c⁻¹ := by
        have h3 : (x : MulAut V) ((z : MulAut V) c) = (z : MulAut V) ((x : MulAut V) c) := by
          have := congrArg (fun φ : MulAut V => φ c) hxz
          simpa only [MulAut.mul_apply] using this
        rw [map_mul, map_inv, h3, hc]
      exact mul_inv_eq_one.1 ((hEU x hx3 hxp hxq).2 _ h1 h2)
    have hξ := isThreeCycle_viaEmbedding ι (a := (0 : Fin 8)) (b := 1) (c := 2) (by decide)
      (by decide) (by decide)
    obtain ⟨x₀, hx₀⟩ := hrange (viaEmbedding (swap (0 : Fin 8) 1 * swap 0 2) ι)
    have hx₀3 : (ψ x₀).IsThreeCycle := hx₀ ▸ hξ
    have hx₀p : ψ x₀ p = p := by
      rw [hx₀]
      exact viaEmbedding_apply_of_notMem _ _ _ fun h => ((hι p).1 h).1 rfl
    have hx₀q : ψ x₀ q = q := by
      rw [hx₀]
      exact viaEmbedding_apply_of_notMem _ _ _ fun h => ((hι q).1 h).2 rfl
    have hall : ∀ y : ↥H, (ψ y).IsThreeCycle → (∀ i ∈ ({p, q} : Finset (Fin 10)), ψ y i = i) →
        fixV (Subgroup.zpowers (y : MulAut V)) = fixV (Subgroup.zpowers (x₀ : MulAut V)) := by
      intro y hy3 hyΔ
      have hyp : ψ y p = p := hyΔ p (by simp)
      have hyq : ψ y q = q := hyΔ q (by simp)
      obtain ⟨ρ, hρ3, hρΔ, hρx, hρy⟩ := exists_isThreeCycle_commute_commute_of_fix {p, q}
        (by simp [Finset.card_pair hpq]) hx₀3 hy3 fun i hi => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hx₀p
          · exact hx₀q
      obtain ⟨z, hz⟩ := hrange ρ
      have hz3 : (ψ z).IsThreeCycle := hz ▸ hρ3
      have hzp : ψ z p = p := hz ▸ hρΔ p (by simp)
      have hzq : ψ z q = q := hz ▸ hρΔ q (by simp)
      have hzx : (z : MulAut V) * x₀ = x₀ * z :=
        coe_eq_coe_of_apply_eq hψ (h₁ := z * x₀) (h₂ := x₀ * z)
          (by rw [map_mul, map_mul, hz]; exact hρx.eq)
      have hzy : (z : MulAut V) * y = y * z :=
        coe_eq_coe_of_apply_eq hψ (h₁ := z * y) (h₂ := y * z)
          (by rw [map_mul, map_mul, hz]; exact hρy.eq)
      have e1 := hfixeq z x₀ hz3 hzp hzq hx₀3 hx₀p hx₀q hzx
      have e2 := hfixeq x₀ z hx₀3 hx₀p hx₀q hz3 hzp hzq hzx.symm
      have e3 := hfixeq z y hz3 hzp hzq hy3 hyp hyq hzy
      have e4 := hfixeq y z hy3 hyp hyq hz3 hzp hzq hzy.symm
      exact (le_antisymm e4 e3).trans (le_antisymm e1 e2)
    have hcent : ∀ y : ↥H, (ψ y).IsThreeCycle →
        fixV (Subgroup.zpowers (y : MulAut V)) = fixV (Subgroup.zpowers (x₀ : MulAut V)) :=
      fun y hy => fixV_zpowers_eq_of_fix hAlt {p, q} (by simp [Finset.card_pair hpq]) hall hy
    have hL := fixV_altPre_eq_of_forall (by norm_num) hψ hAlt hcent
    obtain ⟨W, _, _, G, φ, e, hW, hφ, hφA, h3, -, hφe, -, hoff⟩ :=
      exists_quot hV (by norm_num) hψ hAlt fun y hy => (hcent y hy).trans hL.symm
    obtain ⟨B, hBG, -, hBel, hBcard, hBmem⟩ := hoff A hA
    refine absurd hBcard (not_le.2 (ten_core hW hφ hφA h3 hBG hBel hpq ?_ ?_ ?_))
    · intro b hb
      obtain ⟨a, haA, rfl⟩ := (hBmem b).1 hb
      rw [hφe]
      exact horb a haA
    · intro i
      obtain ⟨a, haA, hai⟩ := hmin i
      exact ⟨e a, (hBmem (e a)).2 ⟨a, haA, rfl⟩, by rw [hφe]; exact hai⟩
    · intro b hb
      obtain ⟨a, haA, rfl⟩ := (hBmem b).1 hb
      rw [hφe]
      exact hτA a haA
  ·
    have hA0 : ∀ a ∈ A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V))),
        a = 1 ∨ a = (τ : MulAut V) := fun a ha =>
      hkerκ ⟨a, hAD ha.1⟩ (hC ⟨a, hAD ha.1⟩ fun w hw => ha.2 w hw)
    have hVW : Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers (τ : MulAut V))) := by
      have h1 := hoff0.2.2.2 ⊥ bot_le
      rw [B1.card_bot_mul_card_fixV] at h1
      have hle1 : A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V))) ≤
          Subgroup.zpowers (τ : MulAut V) := fun a ha => by
        rcases hA0 a ha with rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      have hc1 : Nat.card ↥(A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V)))) ≤ 2 :=
        calc _ ≤ Nat.card (Subgroup.zpowers (τ : MulAut V)) := Subgroup.card_le_of_le hle1
          _ = orderOf (τ : MulAut V) := Nat.card_zpowers _
          _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hτ2
      have hτA0 : (τ : MulAut V) ∈ A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V))) := by
        obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hoff0.2.1
        rcases hA0 a ha with rfl | rfl
        · exact (ha1 rfl).elim
        · exact ha
      have hc2 : Nat.card (fixV (A ⊓ centSub (fixV (Subgroup.zpowers (τ : MulAut V))))) ≤
          Nat.card (fixV (Subgroup.zpowers (τ : MulAut V))) :=
        Subgroup.card_le_of_le (fixV_zpowers_le hτA0)
      exact h1.trans (Nat.mul_le_mul hc1 hc2)
    have hr₀ := (hι (ι 0)).1 ⟨0, rfl⟩
    have hr₁ := (hι (ι 1)).1 ⟨1, rfl⟩
    have hι01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
    obtain ⟨σ, hσ⟩ := hrange (swap (ι 0) (ι 1))
    obtain ⟨g, hg⟩ := hrange (swap p (ι 0) * swap q (ι 1))
    have hgσ : (g : MulAut V) * τ * (g : MulAut V)⁻¹ = σ := by
      refine coe_eq_coe_of_apply_eq hψ (h₁ := g * τ * g⁻¹) (h₂ := σ) ?_
      rw [map_mul, map_mul, map_inv, hτ, hg, hσ, ← swap_apply_apply]
      congr 1
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpq (Ne.symm hr₁.1), swap_apply_left]
      · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hr₁.1 (Ne.symm hι01)]
    have hcσ : Nat.card (fixV (Subgroup.zpowers (σ : MulAut V))) =
        Nat.card (fixV (Subgroup.zpowers (τ : MulAut V))) := by
      rw [← hgσ, card_fixV_zpowers_conj]
    have hσidx : (fixV (Subgroup.zpowers (σ : MulAut V))).index ≤ 2 := by
      have h1 := (fixV (Subgroup.zpowers (σ : MulAut V))).index_mul_card
      rw [hcσ] at h1
      refine Nat.le_of_mul_le_mul_right (by rw [h1]; exact hVW) Nat.card_pos
    have hσD : (σ : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
      coe_mem_preSub.2 (mem_permSetStab_of_pair hι (Or.inl
        ⟨by rw [hσ]; exact swap_apply_of_ne_of_ne (Ne.symm hr₀.1) (Ne.symm hr₁.1),
          by rw [hσ]; exact swap_apply_of_ne_of_ne (Ne.symm hr₀.2) (Ne.symm hr₁.2)⟩))
    set σW := autSubHom hDW (⟨σ, hσD⟩ : ↥(preSub ψ (permSetStab (Set.range ι)))) with hσW
    have hψWσ : autSubLift (restrictHom ψ ι _ le_rfl) hDW hC σW = swap 0 1 := by
      rw [hσW, autSubLift_apply]
      refine (restrictHom_eq_iff _ _).2 fun i => ?_
      change ψ σ (ι i) = ι (swap 0 1 i)
      rw [hσ, ι.injective.swap_apply]
    have hσWidx : (fixV (Subgroup.zpowers
        (σW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V)))))).index ≤ 2 := by
      have heq : fixV (Subgroup.zpowers
          (σW : MulAut ↥(fixV (Subgroup.zpowers (τ : MulAut V))))) =
          (fixV (Subgroup.zpowers (σ : MulAut V))).subgroupOf
            (fixV (Subgroup.zpowers (τ : MulAut V))) := by
        ext w
        rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf, mem_fixV_zpowers_iff]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      rw [heq]
      show (fixV (Subgroup.zpowers (σ : MulAut V))).relIndex
        (fixV (Subgroup.zpowers (τ : MulAut V))) ≤ 2
      exact (relIndex_fixV_le_index _ _).trans hσidx
    obtain ⟨W', _, _, G, φ, e, hW', hφ, hφA, h3, -, hφe, hidx, -⟩ :=
      exists_quot hW2 (by norm_num) hψWinj hψWA hCW
    have h16 := sixteen_le_card hW' le_rfl hφ hφA h3
    have hsq : (e σW : MulAut W') ^ 2 = 1 := by
      have h1 : (e σW) ^ 2 = 1 :=
        hφ (by rw [map_pow, hφe, hψWσ, pow_two, swap_mul_self, map_one])
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hc := card_fixV_sq_of_apply_ne hW' hφ hφA h3 (s := e σW) hsq (u := 0) (w := 2)
      (by rw [hφe, hψWσ, swap_apply_left]; decide) (by rw [hφe, hψWσ]; decide)
    have hidx' := (hidx σW).trans hσWidx
    have h1 := (fixV (Subgroup.zpowers (e σW : MulAut W'))).index_mul_card
    set c := Nat.card (fixV (Subgroup.zpowers (e σW : MulAut W')))
    have hle : Nat.card W' ≤ 2 * c := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ hidx'
    have hc4 : 4 ≤ c := by
      by_contra h
      have : c ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h2 : c * c ≤ 2 * c := by rw [← pow_two, hc]; exact hle
    have h3' := Nat.le_of_mul_le_mul_right h2 (by omega)
    omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
