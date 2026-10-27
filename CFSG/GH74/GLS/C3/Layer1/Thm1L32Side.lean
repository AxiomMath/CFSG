module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h
public import CFSG.Assembly.GL83LieDefs

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

namespace Side

theorem mul_conj_mul_inv'' {G : Type*} [Group G] (φ : MulAut G) (k : G) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext a
  simp [MulAut.conj_apply]

theorem mem_centralizer_conj_of_fix {Kb : Type} [Group Kb] (I : Subgroup Kb) (γ : MulAut Kb)
    (hγ : ∀ i ∈ I, γ i = i) :
    γ ∈ centralizer ((I.map (MulAut.conj : Kb →* MulAut Kb) : Subgroup (MulAut Kb)) :
      Set (MulAut Kb)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨i, hi, rfl⟩
  have h := mul_conj_mul_inv'' γ i
  rw [hγ i hi] at h
  calc (MulAut.conj : Kb →* MulAut Kb) i * γ = (γ * MulAut.conj i * γ⁻¹) * γ := by rw [h]
    _ = γ * (MulAut.conj : Kb →* MulAut Kb) i := by group

theorem exists_not_mem_commutator {Kb : Type} [Group Kb] (C : Subgroup Kb)
    (h : ¬ Group.IsPerfect ↥C) :
    ∃ c ∈ C, c ∉ (_root_.commutator ↥C).map C.subtype := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [Group.isPerfect_def, eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := hcon x x.2
  have : y = x := Subtype.ext hxy
  rw [← this]
  exact hy

end Side

open Side

theorem kside_L2
    {Kb : Type} [Group Kb] [Finite Kb] {F : Type} [Field F] [Finite F]
    (hF : L2Field F) (hcard : Nat.card F = 25) (e : Kb ≃* L2 F) (α : MulAut Kb)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) (hαf : α ∈ fieldAutSub e) :
    (∀ β : MulAut Kb,
      (∀ i ∈ (_root_.commutator ↥(fixedSubgroup Kb α)).map (fixedSubgroup Kb α).subtype, β i = i) →
        β = 1 ∨ β = α) ∧
    α ∉ innAut Kb ∧
    ∃ c ∈ fixedSubgroup Kb α,
      c ∉ (_root_.commutator ↥(fixedSubgroup Kb α)).map (fixedSubgroup Kb α).subtype := by
  obtain ⟨τ, rfl⟩ := hαf
  have hτ1 : τ ≠ 1 := fun h => hα1 (by rw [h, map_one])
  have hαo : orderOf (fieldAutHom e τ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hτo : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) τ]
    exact hαo
  set C : Subgroup Kb := fixedSubgroup Kb (fieldAutHom e τ) with hC
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, ⟨ψ⟩⟩ :=
    (ivk_1_4a F hF Kb e τ).2.2 (by rw [hτo]; exact even_two)
  rw [hτo, hcard] at hcard₀
  have h5 : Nat.card F₀ = 5 :=
    Nat.pow_left_injective (by norm_num : 2 ≠ 0) (hcard₀.trans (by norm_num : 25 = 5 ^ 2))
  have hK : IsOddPrimePower (Nat.card F₀) := ⟨5, 1, Nat.prime_five, by norm_num, le_rfl, by rw [h5]; norm_num⟩
  have hq3 : 3 < Nat.card F₀ := by rw [h5]; norm_num
  refine ⟨?_, ?_, ?_⟩
  ·
    intro β hβ
    obtain ⟨eD⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three (Q := ↥C) F₀ hK hq3 ψ
    have hIL2 : IsL2 ↥((_root_.commutator ↥C).map C.subtype) (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) :=
      ⟨F₀, hF₀, hFin₀, ⟨by rw [h5]; exact ⟨2, rfl⟩, by rw [h5]; norm_num⟩,
        ⟨((_root_.commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
          (eD.trans (L2.equivPSL F₀).symm)⟩⟩
    obtain ⟨⟨e', -, hCle⟩, -⟩ := Proofs2.ivk_1_4h F hF Kb e _ hIL2
    have hIfix : ∀ i ∈ (_root_.commutator ↥C).map C.subtype, fieldAutHom e τ i = i := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have hβc := hCle (mem_centralizer_conj_of_fix _ β hβ)
    have hαc := hCle (mem_centralizer_conj_of_fix _ _ hIfix)
    have hcard2 : Nat.card ↥(fieldAutSub e') = 2 :=
      (ivk_1_2e F hF Kb e').2.2 5 2 Nat.prime_five (by rw [hcard]; norm_num)
    have hu := (Nat.card_eq_two_iff' (1 : ↥(fieldAutSub e'))).1 hcard2
    by_cases hb : β = 1
    · exact Or.inl hb
    · right
      have hx : (⟨β, hβc⟩ : ↥(fieldAutSub e')) ≠ 1 := fun h => hb (congrArg Subtype.val h)
      have hy : (⟨fieldAutHom e τ, hαc⟩ : ↥(fieldAutSub e')) ≠ 1 := fun h => hα1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (hu.unique hx hy)
  ·
    intro hinn
    have h1 := (mem_innDiagSub_iff e _).1 (innAut_le_innDiagSub e hinn)
    rw [fieldProj_fieldAutHom] at h1
    exact hτ1 h1
  ·
    apply exists_not_mem_commutator
    intro hperf
    have : Group.IsPerfect (PGL2 F₀) := Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
    exact (pgl2_commutator_ne_bot_ne_top F₀ hK).2 Group.IsPerfect.commutator_eq_top


section A7

open Equiv Equiv.Perm

theorem sign_swap_mul_swap (a b d e : Fin 7) (hab : a ≠ b) (hde : d ≠ e) :
    Equiv.Perm.sign (swap a b * swap d e) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hde]
  decide

theorem moves_of_commute {b w : Perm (Fin 7)} (h : b * w = w * b) {p : Fin 7} (hp : w p ≠ p) :
    w (b p) ≠ b p := by
  intro hc
  apply hp
  apply b.injective
  have h1 : b (w p) = w (b p) := by
    have := congrArg (fun f : Perm (Fin 7) => f p) h
    simpa using this
  rw [h1, hc]

@[expose] def tc (a b c d e : Fin 7) : Perm (Fin 7) :=
  ⁅(swap a b * swap d e : Perm (Fin 7)), (swap a c * swap d e : Perm (Fin 7))⁆

theorem tc_supp1 : ∀ p : Fin 7, tc 0 1 2 3 4 p ≠ p ↔ (p = 0 ∨ p = 1 ∨ p = 2) := by
  unfold tc; decide +kernel

theorem tc_supp2 : ∀ p : Fin 7, tc 0 3 4 1 2 p ≠ p ↔ (p = 0 ∨ p = 3 ∨ p = 4) := by
  unfold tc; decide +kernel

theorem tc_supp3 : ∀ p : Fin 7, tc 1 3 4 0 2 p ≠ p ↔ (p = 1 ∨ p = 3 ∨ p = 4) := by
  unfold tc; decide +kernel

theorem tc_supp4 : ∀ p : Fin 7, tc 2 3 4 0 1 p ≠ p ↔ (p = 2 ∨ p = 3 ∨ p = 4) := by
  unfold tc; decide +kernel

theorem tc_supp5 : ∀ p : Fin 7, tc 1 2 3 0 4 p ≠ p ↔ (p = 1 ∨ p = 2 ∨ p = 3) := by
  unfold tc; decide +kernel

theorem commute_swap56 (b : Perm (Fin 7))
    (hb : ∀ i ∈ ⁅(centralizer ({swap 5 6} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)),
      (centralizer ({swap 5 6} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))⁆,
      b * i = i * b) :
    b = 1 ∨ b = swap 5 6 := by
  set C₀ : Subgroup (Perm (Fin 7)) :=
    centralizer ({swap 5 6} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) with hC₀
  have hmemC : ∀ a c d e : Fin 7, a ≠ c → d ≠ e →
      swap a c * swap d e * swap 5 6 = swap 5 6 * (swap a c * swap d e) →
      (swap a c * swap d e : Perm (Fin 7)) ∈ C₀ := by
    intro a c d e hac hde hcomm
    exact Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hcomm,
      Equiv.Perm.mem_alternatingGroup.2 (sign_swap_mul_swap a c d e hac hde)⟩
  have step : ∀ a c₁ c₂ d e : Fin 7, a ≠ c₁ → a ≠ c₂ → d ≠ e →
      swap a c₁ * swap d e * swap 5 6 = swap 5 6 * (swap a c₁ * swap d e) →
      swap a c₂ * swap d e * swap 5 6 = swap 5 6 * (swap a c₂ * swap d e) →
      ∀ p, tc a c₁ c₂ d e p ≠ p → tc a c₁ c₂ d e (b p) ≠ b p := by
    intro a c₁ c₂ d e h1 h2 h3 hc1 hc2 p hp
    exact moves_of_commute (hb _ (Subgroup.commutator_mem_commutator
      (hmemC a c₁ d e h1 h3 hc1) (hmemC a c₂ d e h2 h3 hc2))) hp
  have h1 := step 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 := step 0 3 4 1 2 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 := step 1 3 4 0 2 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 := step 2 3 4 0 1 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 := step 1 2 3 0 4 (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hb0 : b 0 = 0 := by
    have a1 := (tc_supp1 (b 0)).1 (h1 0 ((tc_supp1 0).2 (Or.inl rfl)))
    have a2 := (tc_supp2 (b 0)).1 (h2 0 ((tc_supp2 0).2 (Or.inl rfl)))
    rcases a1 with h | h | h <;> rcases a2 with h' | h' | h' <;>
      first | exact h | exact h' | (exfalso; rw [h] at h'; revert h'; decide)
  have hb1 : b 1 = 1 := by
    have a1 := (tc_supp1 (b 1)).1 (h1 1 ((tc_supp1 1).2 (Or.inr (Or.inl rfl))))
    have a2 := (tc_supp3 (b 1)).1 (h3 1 ((tc_supp3 1).2 (Or.inl rfl)))
    rcases a1 with h | h | h <;> rcases a2 with h' | h' | h' <;>
      first | exact h | exact h' | (exfalso; rw [h] at h'; revert h'; decide)
  have hb2 : b 2 = 2 := by
    have a1 := (tc_supp1 (b 2)).1 (h1 2 ((tc_supp1 2).2 (Or.inr (Or.inr rfl))))
    have a2 := (tc_supp4 (b 2)).1 (h4 2 ((tc_supp4 2).2 (Or.inl rfl)))
    rcases a1 with h | h | h <;> rcases a2 with h' | h' | h' <;>
      first | exact h | exact h' | (exfalso; rw [h] at h'; revert h'; decide)
  have hb3 : b 3 = 3 := by
    have a1 := (tc_supp2 (b 3)).1 (h2 3 ((tc_supp2 3).2 (Or.inr (Or.inl rfl))))
    have a2 := (tc_supp5 (b 3)).1 (h5 3 ((tc_supp5 3).2 (Or.inr (Or.inr rfl))))
    rcases a1 with h | h | h <;> rcases a2 with h' | h' | h' <;>
      first | exact h | exact h' | (exfalso; rw [h] at h'; revert h'; decide)
  have hb4 : b 4 = 4 := by
    have a1 := (tc_supp2 (b 4)).1 (h2 4 ((tc_supp2 4).2 (Or.inr (Or.inr rfl))))
    rcases a1 with h | h | h
    · exfalso
      have : (4 : Fin 7) = 0 := b.injective (h.trans hb0.symm)
      revert this; decide
    · exfalso
      have : (4 : Fin 7) = 3 := b.injective (h.trans hb3.symm)
      revert this; decide
    · exact h
  have key : ∀ x : Fin 7, x ≠ 5 → x ≠ 6 → x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  have hlow : ∀ x : Fin 7, x ≠ 5 → x ≠ 6 → ∀ y : Fin 7, (y = 5 ∨ y = 6) → b y ≠ x := by
    intro x hx5 hx6 y hy hyx
    rcases key x hx5 hx6 with rfl | rfl | rfl | rfl | rfl
    · have : y = 0 := b.injective (hyx.trans hb0.symm)
      rcases hy with rfl | rfl <;> revert this <;> decide
    · have : y = 1 := b.injective (hyx.trans hb1.symm)
      rcases hy with rfl | rfl <;> revert this <;> decide
    · have : y = 2 := b.injective (hyx.trans hb2.symm)
      rcases hy with rfl | rfl <;> revert this <;> decide
    · have : y = 3 := b.injective (hyx.trans hb3.symm)
      rcases hy with rfl | rfl <;> revert this <;> decide
    · have : y = 4 := b.injective (hyx.trans hb4.symm)
      rcases hy with rfl | rfl <;> revert this <;> decide
  have hb5 : b 5 = 5 ∨ b 5 = 6 := by
    by_contra hcon
    push Not at hcon
    exact hlow (b 5) hcon.1 hcon.2 5 (Or.inl rfl) rfl
  have hb6 : b 6 = 5 ∨ b 6 = 6 := by
    by_contra hcon
    push Not at hcon
    exact hlow (b 6) hcon.1 hcon.2 6 (Or.inr rfl) rfl
  have hbne : b 5 ≠ b 6 := fun h => by
    have := b.injective h
    revert this; decide
  rcases hb5 with h5 | h5
  · left
    have h6 : b 6 = 6 := by
      rcases hb6 with h6 | h6
      · exact absurd (h5.trans h6.symm) hbne
      · exact h6
    ext x
    fin_cases x <;> simp [hb0, hb1, hb2, hb3, hb4, h5, h6]
  · right
    have h6 : b 6 = 5 := by
      rcases hb6 with h6 | h6
      · exact h6
      · exact absurd (h5.trans h6.symm) hbne
    ext x
    fin_cases x <;> simp [hb0, hb1, hb2, hb3, hb4, h5, h6, Equiv.swap_apply_def]

theorem commute_swap {τ : Perm (Fin 7)} (hτ : τ.IsSwap) (b : Perm (Fin 7))
    (hb : ∀ i ∈ ⁅(centralizer ({τ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)),
      (centralizer ({τ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7))⁆, b * i = i * b) :
    b = 1 ∨ b = τ := by
  obtain ⟨c, hc⟩ : ∃ c : Perm (Fin 7), c * τ * c⁻¹ = swap 5 6 := by
    have : IsConj τ (swap 5 6 : Perm (Fin 7)) := Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (by rw [Equiv.Perm.isSwap_iff_cycleType.mp hτ, IVK.A7.swap56_cycleType])
    exact isConj_iff.mp this
  have hmap := IVK.A7.map_conj_centralizer_inf_alternating c τ
  rw [hc] at hmap
  have hb' := commute_swap56 (c * b * c⁻¹) (by
    intro i' hi'
    rw [← hmap, ← Subgroup.map_commutator] at hi'
    obtain ⟨i, hi, rfl⟩ := hi'
    have h := hb i hi
    show c * b * c⁻¹ * (c * i * c⁻¹) = c * i * c⁻¹ * (c * b * c⁻¹)
    calc c * b * c⁻¹ * (c * i * c⁻¹) = c * (b * i) * c⁻¹ := by group
      _ = c * (i * b) * c⁻¹ := by rw [h]
      _ = c * i * c⁻¹ * (c * b * c⁻¹) := by group)
  rcases hb' with h | h
  · left
    have : c * b * c⁻¹ = c * 1 * c⁻¹ := by rw [h]; group
    simpa using this
  · right
    have h2 : c * b * c⁻¹ = c * τ * c⁻¹ := by rw [h, hc]
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3

end A7



open Equiv Equiv.Perm in
theorem kside_A7 {Kb : Type} [Group Kb] [Finite Kb] (e7 : Kb ≃* alternatingGroup (Fin 7))
    (α : MulAut Kb) (_hα2 : α * α = 1) (hct : (psiEquiv e7 α).cycleType = {2}) :
    (∀ β : MulAut Kb,
      (∀ i ∈ (_root_.commutator ↥(fixedSubgroup Kb α)).map (fixedSubgroup Kb α).subtype, β i = i) →
        β = 1 ∨ β = α) ∧
    α ∉ innAut Kb ∧
    ∃ c ∈ fixedSubgroup Kb α,
      c ∉ (_root_.commutator ↥(fixedSubgroup Kb α)).map (fixedSubgroup Kb α).subtype := by
  set ψ := psiEquiv e7 with hψ
  set τ : Perm (Fin 7) := ψ α with hτ
  have hτsw : τ.IsSwap := Equiv.Perm.isSwap_iff_cycleType.mpr hct
  set C : Subgroup Kb := fixedSubgroup Kb α with hC
  let ρ : Kb →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e7.toMonoidHom
  have hρ : ∀ (σ : MulAut Kb) (k : Kb), ρ (σ k) = ψ σ * ρ k * (ψ σ)⁻¹ :=
    fun σ k => psi_apply e7 σ k
  have hρinj : Function.Injective ρ := fun a b hab => e7.injective (Subtype.ext hab)
  have hfix : ∀ k : Kb, α k = k ↔ ρ k * τ = τ * ρ k := by
    intro k
    constructor
    · intro h
      have h1 := hρ α k
      rw [h] at h1
      calc ρ k * τ = (τ * ρ k * τ⁻¹) * τ := by rw [← h1]
        _ = τ * ρ k := by group
    · intro h
      apply hρinj
      rw [hρ α k]
      show τ * ρ k * τ⁻¹ = ρ k
      calc τ * ρ k * τ⁻¹ = ρ k * τ * τ⁻¹ := by rw [← h]
        _ = ρ k := by group
  set Ct : Subgroup (Perm (Fin 7)) :=
    centralizer ({τ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) with hCt
  have hρC : C.map ρ = Ct := by
    ext w
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.2 ((hfix k).1 hk), (e7 k).2⟩
    · rintro ⟨hw1, hw2⟩
      refine ⟨e7.symm ⟨w, hw2⟩, ?_, ?_⟩
      · have hρw : ρ (e7.symm ⟨w, hw2⟩) = w := by simp [ρ]
        show α (e7.symm ⟨w, hw2⟩) = e7.symm ⟨w, hw2⟩
        rw [hfix, hρw]
        exact mem_centralizer_singleton_iff.1 hw1
      · simp [ρ]
  have hI : (_root_.commutator ↥C).map C.subtype = ⁅C, C⁆ := Subgroup.map_subtype_commutator C
  have hρI : ((_root_.commutator ↥C).map C.subtype).map ρ = ⁅Ct, Ct⁆ := by
    rw [hI, Subgroup.map_commutator, hρC]
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    have hb : ∀ i ∈ ⁅Ct, Ct⁆, ψ β * i = i * ψ β := by
      intro i hi
      rw [← hρI] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have h1 := hρ β j
      rw [hβ j hj] at h1
      calc ψ β * ρ j = (ψ β * ρ j * (ψ β)⁻¹) * ψ β := by group
        _ = ρ j * ψ β := by rw [← h1]
    rcases commute_swap hτsw (ψ β) hb with h | h
    · left
      apply ψ.injective
      rw [h, map_one]
    · right
      exact ψ.injective h
  · intro hinn
    have hτA : τ ∈ alternatingGroup (Fin 7) := by
      have := psi_map_innAut e7
      rw [← this]
      exact ⟨α, hinn, rfl⟩
    obtain ⟨a, b, hab, hτab⟩ := hτsw
    have h1 : Equiv.Perm.sign τ = -1 := by rw [hτab, Equiv.Perm.sign_swap hab]
    have h2 : Equiv.Perm.sign τ = 1 := Equiv.Perm.mem_alternatingGroup.1 hτA
    rw [h1] at h2
    exact absurd h2 (by decide)
  · apply exists_not_mem_commutator
    intro hperf
    obtain ⟨e1⟩ := fixedSubgroup_equiv_A7 e7 α
    obtain ⟨e2⟩ := IVK.A7.centralizer_A7_swap_equiv hτsw
    have : Group.IsPerfect (Perm (Fin 5)) :=
      Group.IsPerfect.ofSurjective (f := (e1.trans e2).toMonoidHom) (e1.trans e2).surjective
    have h3 : _root_.commutator (Perm (Fin 5)) = ⊤ := Group.IsPerfect.commutator_eq_top
    have h4 : (swap (0 : Fin 5) 1) ∈ _root_.commutator (Perm (Fin 5)) := by rw [h3]; trivial
    have h5 := Equiv.Perm.mem_alternatingGroup.1 (alternatingGroup.commutator_perm_le h4)
    rw [Equiv.Perm.sign_swap (by decide)] at h5
    exact absurd h5 (by decide)

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
