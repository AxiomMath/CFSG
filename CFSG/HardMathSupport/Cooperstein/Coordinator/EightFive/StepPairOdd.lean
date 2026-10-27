module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.StepPairOddTau
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

@[expose] def ExitTenOdd : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin 10)), Function.Injective ψ →
      alternatingGroup (Fin 10) ≤ ψ.range → TPerm 9 →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A → ¬ A ≤ altPre ψ →
      ∀ p q : Fin 10, p ≠ q →
      (∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p) →
      (∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i) →
      ∀ ι : Fin 8 ↪ Fin 10, (∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) →
      ∀ τ : ↥H, ψ τ = swap p q →
      ∀ (hDW : preSub ψ (permSetStab (Set.range ι)) ≤
          stabSub (fixV (Subgroup.zpowers (τ : MulAut V))))
        (hC : ∀ k : ↥(preSub ψ (permSetStab (Set.range ι))),
          (∀ w ∈ fixV (Subgroup.zpowers (τ : MulAut V)), (k : MulAut V) w = w) →
            restrictHom ψ ι _ le_rfl k = 1),
        Exotic (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC) → NatVia ψ (commV H)

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {A : Subgroup (MulAut V)}

omit [Finite V] in
theorem mem_range_of_not_le_altPre (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hAH : A ≤ H)
    (hAL : ¬ A ≤ altPre ψ) (σ : Perm (Fin n)) : σ ∈ ψ.range := by
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.not_le_iff_exists.1 hAL
  have hodd : ψ ⟨a, hAH ha⟩ ∉ alternatingGroup (Fin n) := fun h => haL (coe_mem_altPre_iff.2 h)
  by_cases hσ : σ ∈ alternatingGroup (Fin n)
  · exact hAlt hσ
  · have h1 : (ψ ⟨a, hAH ha⟩)⁻¹ * σ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup] at hodd hσ ⊢
      rw [map_mul, map_inv, Int.units_ne_iff_eq_neg.1 hodd, Int.units_ne_iff_eq_neg.1 hσ]
      decide
    obtain ⟨h, hh⟩ := hAlt h1
    exact ⟨⟨a, hAH ha⟩ * h, by rw [map_mul, hh, mul_inv_cancel_left]⟩

theorem natVia_of_exitTenOdd (hexit : ExitTenOdd) (hn : n = 10) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (hT₁ : TPerm (n - 1)) (hA : IsFFStarOffender H A) (hAL : ¬ A ≤ altPre ψ) (p q : Fin n) (hpq : p ≠ q)
    (horb : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p)
    (hmin : ∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i)
    (ι : Fin (n - 2) ↪ Fin n) (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) (τ : ↥H)
    (hτ : ψ τ = swap p q)
    (hDW : preSub ψ (permSetStab (Set.range ι)) ≤ stabSub (fixV (Subgroup.zpowers (τ : MulAut V))))
    (hC : ∀ k : ↥(preSub ψ (permSetStab (Set.range ι))),
      (∀ w ∈ fixV (Subgroup.zpowers (τ : MulAut V)), (k : MulAut V) w = w) →
        restrictHom ψ ι _ le_rfl k = 1)
    (hex : Exotic (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC)) : NatVia ψ (commV H) := by
  subst hn
  exact hexit V hV H ψ hψ hAlt hT₁ A hA hAL p q hpq horb hmin ι hι τ hτ hDW hC hex

theorem step_pair_not_le (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 10 ≤ n)
    (hT : TPerm (n - 2)) (hT₁ : TPerm (n - 1)) (p q : Fin n) (hpq : p ≠ q) (hAL : ¬ A ≤ altPre ψ)
    (horb : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p)
    (hmin : ∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i) (hexit : ExitTenOdd) :
    NatVia ψ (commV H) := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne_ne (show n - 2 + 2 = n by omega) hpq
  obtain ⟨τ, hτ⟩ := mem_range_of_not_le_altPre hAlt hA.1 hAL (swap p q)
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
    fun h _ hh => coe_mem_preSub.2 hh
  have hκA : alternatingGroup (Fin (n - 2)) ≤
      (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl).range :=
    alternatingGroup_le_range_restrictHom hAlt hKmem
  have hτ1 : (τ : MulAut V) ≠ 1 := fun h => by
    have h1 : τ = 1 := Subtype.ext h
    have h2 : swap p q = 1 := by rw [← hτ, h1, map_one]
    have h3 := congrArg (fun g : Perm (Fin n) => g p) h2
    simp only [swap_apply_left, Perm.one_apply] at h3
    exact hpq h3.symm
  have hτ2 : τ ^ 2 = 1 := hψ (by rw [map_pow, hτ, pow_two, swap_mul_self, map_one])
  have ht2 : (τ : MulAut V) ^ 2 = 1 := by
    rw [← SubgroupClass.coe_pow, hτ2]
    rfl
  have htc : ∀ d ∈ preSub ψ (permSetStab (Set.range ι)), d * (τ : MulAut V) = τ * d :=
    fun d hd => by
      obtain ⟨hdH, hdS⟩ := mem_preSub.1 hd
      have h1 : ψ (⟨d, hdH⟩ * τ) = ψ (τ * ⟨d, hdH⟩) := by
        rw [map_mul, map_mul, hτ]
        exact mul_swap_eq_swap_mul hpq hι hdS
      exact congrArg Subtype.val (hψ h1)
  have hDQ : preSub ψ (permSetStab (Set.range ι)) ≤
      Subgroup.normalizer (Subgroup.zpowers (τ : MulAut V) : Set (MulAut V)) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute (τ : MulAut V) d from (htc d hd).symm) k).eq)
  have hDW := le_stabSub_fixV hDQ
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
  have hmemD : ∀ σ, ((altRho hψ hAlt).comp (altLift ι)) σ ∈
      preSub ψ (permSetStab (Set.range ι)) := fun σ =>
    (coe_mem_preSub (x := ⟨_, altRho_mem hψ hAlt _⟩)).2
      (by rw [apply_altRho]; exact altLift_mem_permSetStab ι σ)
  set e := ((altRho hψ hAlt).comp (altLift ι)).codRestrict _ hmemD with he_def
  have he : ∀ σ, restrictHom ψ ι _ le_rfl (e σ) = σ := fun σ =>
    restrictHom_eq_of_eq_altLift (apply_altRho hψ hAlt _)
  obtain ⟨σ₃, hσ₃⟩ := exists_isThreeCycle (m := n - 2) (by omega)
  have hQ : IsPGroup 2 (Subgroup.zpowers (τ : MulAut V)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht2 hτ1
  have hσ3 : σ₃ ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, ← hσ₃.orderOf, pow_orderOf_eq_one]; rfl)
  have hx3 : (e σ₃ : MulAut V) ^ 3 = 1 := by
    change ((altRho hψ hAlt).comp (altLift ι) σ₃) ^ 3 = 1
    rw [← map_pow, hσ3, map_one]
  have hx1 : (e σ₃ : MulAut V) ≠ 1 := fun h => by
    have h1 : altRho hψ hAlt (altLift ι σ₃) = altRho hψ hAlt (altLift ι 1) := by
      rw [map_one, map_one]
      exact h
    exact hσ₃.ne_one (congrArg Subtype.val (altLift_injective ι (altRho_injective hψ hAlt h1)))
  have hC := faithW hV (by omega) _ hκA hQ hDQ hkerW (e σ₃)
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)) hx1
    (by rw [he]; exact σ₃.2) fun q hq => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact (Commute.zpow_right (show Commute (e σ₃ : MulAut V) τ from htc _ (e σ₃).2) k).eq
  have hψWinj := autSubLift_injective (hKW := hDW) (hC := hC) hkerW
  have hψWA : alternatingGroup (Fin (n - 2)) ≤
      (autSubLift (restrictHom ψ ι _ le_rfl) hDW hC).range := by
    rw [range_autSubLift]
    exact hκA
  have hAD : A ≤ preSub ψ (permSetStab (Set.range ι)) := fun a ha =>
    (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2 (mem_permSetStab_of_pair hι (horb ⟨a, hA.1 ha⟩ ha))
  have hfixA : ∀ i, ∃ a : ↥(preSub ψ (permSetStab (Set.range ι))), (a : MulAut V) ∈ A ∧
      restrictHom ψ ι _ le_rfl a i ≠ i := fun i => by
    obtain ⟨a, ha, hai⟩ := hmin (ι i)
    refine ⟨⟨a, hAD ha⟩, ha, fun h => hai ?_⟩
    have := restrictHom_apply_apply (hK := le_rfl) ⟨(a : MulAut V), hAD ha⟩ i
    rw [h] at this
    exact this.symm
  have hWA : commSub (fixV (Subgroup.zpowers (τ : MulAut V))) A ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, hai⟩ := hfixA ⟨0, by omega⟩
    exact hai (by rw [hC a fun w hw => (commSub_eq_bot_iff.1 hbot) hw _ ha]; rfl)
  have hoffW := isFFStarOffender_autSub hA (fun a ha w hw => ((hDW (hAD ha)) w).2 hw) hWA
    (autSub_mono hAD _)
  rcases hT (↥(fixV (Subgroup.zpowers (τ : MulAut V))))
      (fun v => Subtype.ext (by rw [SubgroupClass.coe_pow, hV]; rfl)) _ _ hψWinj hψWA
      ⟨_, hoffW⟩ with hnat | ⟨h7, -⟩ | ⟨h8, hex⟩
  ·
    have hVW := commV_le_fixV_of_natVia hV (by omega) _ ht2 htc rfl hDW _
      (fun d => autSubLift_apply d) hnat e he hA hAD hkerκ hfixA
    have hshape := natShape_subtype_comp_of_natVia (by omega) _ hDW _
      (fun d => autSubLift_apply d) hnat e he hVW
    have heq : (preSub ψ (permSetStab (Set.range ι))).subtype.comp e =
        (altRho hψ hAlt).comp (altLift ι) :=
      MonoidHom.ext fun _ => rfl
    rw [heq] at hshape
    exact natVia_commV_of_natShape (by omega) hψ hAlt
      (natShape_of_stab₂ hV (by omega) ι (by omega) _ hshape)
  · omega
  · exact natVia_of_exitTenOdd hexit (by omega) hV hψ hAlt hT₁ hA hAL p q hpq horb hmin ι hι τ
      hτ hDW hC hex

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
