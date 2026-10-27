module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerDetect

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

section Normal

variable [CharP k 2] [Finite V] [Finite X] (ρ : X →* (V ≃ₗ[k] V)) (H A : Subgroup X) [H.Normal]

theorem bestOffender_invariance_of_normal (hAel : CFSG.IsElementaryAbelian 2 A)
    (hHA : ⁅H, A⁆ = H) (hno : NoPQuotient 2 H) (hch : CentralPChief 2 H)
    (hmax : ∀ B : Subgroup X, B ≤ A → weight ρ B ≤ weight ρ A)
    {a : X} (ha : a ∈ A) (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    {I : Submodule k V} (hI : IsGoodModule ρ H I) : ∀ u ∈ I, ρ a u ∈ I := by
  by_contra hcon
  have hmove : ¬ I.map (ρ a : V →ₗ[k] V) ≤ I := fun h => hcon fun u hu => h ⟨u, hu, rfl⟩
  have hS := isSwap_bar ρ H A hAel hHA ha hq hI hmove
  obtain ⟨hWA, hWc⟩ := swap_invariant ρ H A hAel hHA ha hq hI hmove
  have hI₂ : IsGoodModule ρ H (I.map (ρ a : V →ₗ[k] V)) := hI.map (mem_normalizer_of_normal H a)
  have hWH : Offender.IsInvariant ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) :=
    isInvariant_sup' hI.inv hI₂.inv
  set S : Submodule k (V ⧸ fixSub ρ H) := I.map (bar ρ H) with hSdef
  set W : Submodule k V := I ⊔ I.map (ρ a : V →ₗ[k] V) with hWdef
  have hWbar : W.map (bar ρ H) = S ⊔ S.map (barHom ρ H a : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) := by
    rw [hWdef, Submodule.map_sup, map_map_bar]
  have hWbar_card : Nat.card ↥(W.map (bar ρ H)) = Nat.card ↥S * Nat.card ↥S := by
    rw [hWbar]; exact hS.natCard_sup
  have hWcard : Nat.card ↥(W.map (bar ρ H)) * Nat.card ↥(W ⊓ fixSub ρ H) = Nat.card ↥W :=
    natCard_map_mkQ_mul_natCard_inf (fixSub ρ H) W
  have hmaxA : ∀ B : Subgroup ↥A, weight (ρ.comp A.subtype) B ≤ weight (ρ.comp A.subtype) ⊤ := by
    intro B
    rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
    exact hmax _ (Subgroup.map_subtype_le B)
  have hidx : Nat.card ↥W ≤ (centSub (ρ.comp A.subtype) W).index * Nat.card ↥(W ⊓ fixSub ρ A) := by
    have h := restrict_ineq_weak (ρ.comp A.subtype) W hmaxA
      (B := centSub (ρ.comp A.subtype) W) le_rfl
    rw [Subgroup.relIndex_self, one_mul] at h
    have hWC : W ⊓ fixSub (ρ.comp A.subtype) (centSub (ρ.comp A.subtype) W) = W :=
      inf_eq_left.2 fun w hw b hb => hb w hw
    rw [hWC, fixSub_comp_subtype, map_subtype_top] at h
    exact h
  have hF : Nat.card ↥(W ⊓ fixSub ρ A) ≤ Nat.card ↥(W ⊓ fixSub ρ H) * Nat.card ↥S := by
    have hFbar : (W ⊓ fixSub ρ A).map (bar ρ H) ≤ swapD (barHom ρ H) a S := by
      rintro _ ⟨x, hx, rfl⟩
      refine hS.fixed_mem_swapD ?_ ?_
      · rw [← hWbar]; exact ⟨x, hx.1, rfl⟩
      · show barHom ρ H a (bar ρ H x) = bar ρ H x
        rw [barHom_bar, hx.2 a ha]
    have h1 := natCard_map_mkQ_mul_natCard_inf (fixSub ρ H) (W ⊓ fixSub ρ A)
    have h2 : Nat.card ↥((W ⊓ fixSub ρ A).map (bar ρ H)) ≤ Nat.card ↥S := by
      have := natCard_le_of_le' hFbar
      rwa [hS.natCard_swapD] at this
    have h3 : Nat.card ↥((W ⊓ fixSub ρ A) ⊓ fixSub ρ H) ≤ Nat.card ↥(W ⊓ fixSub ρ H) :=
      natCard_le_of_le' (inf_le_inf_right _ inf_le_left)
    calc Nat.card ↥(W ⊓ fixSub ρ A)
        = Nat.card ↥((W ⊓ fixSub ρ A).map (bar ρ H)) * Nat.card ↥((W ⊓ fixSub ρ A) ⊓ fixSub ρ H) :=
          h1.symm
      _ ≤ Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H) := Nat.mul_le_mul h2 h3
      _ = Nat.card ↥(W ⊓ fixSub ρ H) * Nat.card ↥S := mul_comm _ _
  have hle : Nat.card ↥S ≤ (centSub (ρ.comp A.subtype) W).index := by
    have hpos : 0 < Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have h1 : Nat.card ↥S * (Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H)) ≤
        (centSub (ρ.comp A.subtype) W).index * (Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H)) := by
      calc Nat.card ↥S * (Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H)) = Nat.card ↥W := by
            rw [← hWcard, hWbar_card]; ring
        _ ≤ (centSub (ρ.comp A.subtype) W).index * Nat.card ↥(W ⊓ fixSub ρ A) := hidx
        _ ≤ (centSub (ρ.comp A.subtype) W).index * (Nat.card ↥S * Nat.card ↥(W ⊓ fixSub ρ H)) :=
          Nat.mul_le_mul_left _ (by rw [mul_comm]; exact hF)
    exact Nat.le_of_mul_le_mul_right h1 hpos
  set C := centSub (ρ.comp A.subtype) W with hCdef
  let _ : Fintype (↥A ⧸ C) := Fintype.ofFinite _
  let g : (↥A ⧸ C) → X := fun q => ((Quotient.out q : ↥A) : X)
  have hgA : ∀ q, g q ∈ A := fun q => (Quotient.out q : ↥A).2
  have hfree : ∀ i j : ↥A ⧸ C, S.map (barHom ρ H (g i) : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) =
      S.map (barHom ρ H (g j) : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) → i = j := by
    intro i j hij
    set bA : ↥A := (Quotient.out i)⁻¹ * Quotient.out j with hbA
    have hb : (bA : X) = (g i)⁻¹ * g j := rfl
    have hbA' : (bA : X) ∈ A := bA.2
    have hstab : S.map (barHom ρ H (bA : X) : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) = S := by
      rw [hb, map_mul_eq, ← hij, map_inv_map]
    have hfix : ∀ w : V ⧸ fixSub ρ H, w ∈ S ⊔ S.map (barHom ρ H a :
        (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) → barHom ρ H (bA : X) w = w :=
      fun w hw => hS.fixes_of_stabilizes hbA' hstab hw
    have htriv : ∀ w ∈ W, ρ (bA : X) w - w ∈ fixSub ρ H := by
      intro w hw
      rw [← bar_eq_zero_iff ρ H, map_sub, ← barHom_bar,
        hfix _ (by rw [← hWbar]; exact ⟨w, hw, rfl⟩), sub_self]
    have hdet := detect_of_trivial_mod ρ H A (fun x _ => mem_normalizer_of_normal H x) hno hch W
      hWH hWA hWc hbA' htriv
    have hbC : bA ∈ C := by
      rw [hCdef, mem_centSub]
      exact fun w hw => hdet w hw
    have h2 : (↑(Quotient.out i) : ↥A ⧸ C) = ↑(Quotient.out j) := QuotientGroup.eq.2 hbC
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  have hcardι : Fintype.card (↥A ⧸ C) = C.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  have hinvA : Offender.IsInvariant (barHom ρ H) A
      (S ⊔ S.map (barHom ρ H a : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H))) := by
    rw [← hWbar]; exact isInvariant_map_bar ρ H hWA
  exact hS.false_of_many hinvA g hgA hfree (by rw [hcardι]; exact hle)

end Normal

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.IsElementaryAbelian p G') : CFSG.IsElementaryAbelian p G where
  toIsMulCommutative := ⟨⟨fun a b => e.injective (by
    rw [map_mul, map_mul]; exact h.toIsMulCommutative.is_comm.comm _ _)⟩⟩
  exponent_dvd_p :=
    (Monoid.exponent_dvd_of_monoidHom e.toMonoidHom e.injective).trans h.exponent_dvd_p

section General

variable [CharP k 2] [Finite V] [Finite X] (ρ : X →* (V ≃ₗ[k] V)) (H A : Subgroup X)

theorem bestOffender_invariance (hAn : A ≤ Subgroup.normalizer (H : Set X))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hHA : ⁅H, A⁆ = H) (hno : NoPQuotient 2 H)
    (hch : CentralPChief 2 H) (hmax : ∀ B : Subgroup X, B ≤ A → weight ρ B ≤ weight ρ A)
    {a : X} (ha : a ∈ A) (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    {I : Submodule k V} (hI : Offender.IsInvariant ρ H I) (hIc : commSub ρ H I = I)
    (hIirr : IsIrrQuot ρ H I) : ∀ u ∈ I, ρ a u ∈ I := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup X, N = Subgroup.normalizer (H : Set X) := ⟨_, rfl⟩
  have hHN : H ≤ N := hN ▸ Subgroup.le_normalizer
  have hAN : A ≤ N := hN ▸ hAn
  have hH'n : (H.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).2 (le_of_eq hN)
  have hfix : fixSub (ρ.comp N.subtype) (H.subgroupOf N) = fixSub ρ H := by
    ext v
    simp only [mem_fixSub]
    constructor
    · intro h x hx
      exact h ⟨x, hHN hx⟩ (Subgroup.mem_subgroupOf.2 hx)
    · intro h x hx
      exact h x (Subgroup.mem_subgroupOf.1 hx)
  have hcomm : ∀ U : Submodule k V, commSub (ρ.comp N.subtype) (H.subgroupOf N) U =
      commSub ρ H U := by
    intro U
    refine le_antisymm (commSub_le_iff.2 fun b hb u hu =>
      mem_commSub_of (Subgroup.mem_subgroupOf.1 hb) hu) (commSub_le_iff.2 fun b hb u hu => ?_)
    exact mem_commSub_of (ρ := ρ.comp N.subtype) (b := ⟨b, hHN hb⟩)
      (Subgroup.mem_subgroupOf.2 hb) hu
  have hinv : ∀ U : Submodule k V, Offender.IsInvariant (ρ.comp N.subtype) (H.subgroupOf N) U ↔
      Offender.IsInvariant ρ H U := by
    intro U
    constructor
    · intro h b hb u hu
      exact h ⟨b, hHN hb⟩ (Subgroup.mem_subgroupOf.2 hb) u hu
    · intro h b hb u hu
      exact h b (Subgroup.mem_subgroupOf.1 hb) u hu
  have hgood : IsGoodModule (ρ.comp N.subtype) (H.subgroupOf N) I := by
    refine ⟨(hinv I).2 hI, by rw [hcomm, hIc], ?_⟩
    obtain ⟨hnz, hirr⟩ := hIirr
    refine ⟨by rw [hfix]; exact hnz, fun U hU hlo hhi => ?_⟩
    rw [hfix] at hlo ⊢
    exact hirr U ((hinv U).1 hU) hlo hhi
  have hAmap : (A.subgroupOf N).map N.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.2 hAN
  have hHmap : (H.subgroupOf N).map N.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.2 hHN
  have hmax' : ∀ B : Subgroup ↥N, B ≤ A.subgroupOf N →
      weight (ρ.comp N.subtype) B ≤ weight (ρ.comp N.subtype) (A.subgroupOf N) := by
    intro B hB
    rw [weight_comp_subtype, weight_comp_subtype, hAmap]
    exact hmax _ (hAmap ▸ Subgroup.map_mono hB)
  have hHA' : ⁅H.subgroupOf N, A.subgroupOf N⁆ = H.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hAmap, hHmap, hHA]
  have hAel' : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf N) :=
    isElementaryAbelian_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAN) hAel
  have hno' : NoPQuotient 2 ↥(H.subgroupOf N) :=
    noPQuotient_of_surjective (Subgroup.subgroupOfEquivOfLe hHN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHN).symm.surjective hno
  have hch' : CentralPChief 2 ↥(H.subgroupOf N) :=
    centralPChief_of_surjective (Subgroup.subgroupOfEquivOfLe hHN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHN).symm.surjective hch
  have haN : (⟨a, hAN ha⟩ : ↥N) ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 ha
  have hq' : ∀ b ∈ A.subgroupOf N, ∀ v, (ρ.comp N.subtype) b ((ρ.comp N.subtype) ⟨a, hAN ha⟩ v - v) =
      (ρ.comp N.subtype) ⟨a, hAN ha⟩ v - v := fun b hb v => hq b (Subgroup.mem_subgroupOf.1 hb) v
  have := hH'n
  exact bestOffender_invariance_of_normal (ρ.comp N.subtype) (H.subgroupOf N) (A.subgroupOf N)
    hAel' hHA' hno' hch' hmax' haN hq' hgood

theorem bestOffender_invariance_strict (hAn : A ≤ Subgroup.normalizer (H : Set X))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hHA : ⁅H, A⁆ = H) (hno : NoPQuotient 2 H)
    (hch : CentralPChief 2 H) (hmax : ∀ B : Subgroup X, B ≤ A → weight ρ B ≤ weight ρ A)
    (hstrict : ∀ B : Subgroup X, ⊥ < B → B < A → weight ρ B < weight ρ A)
    {I : Submodule k V} (hI : Offender.IsInvariant ρ H I) (hIc : commSub ρ H I = I)
    (hIirr : IsIrrQuot ρ H I) : Offender.IsInvariant ρ A I := by
  intro a ha u hu
  by_cases hA1 : A = ⊥
  · have : a = 1 := by rw [hA1] at ha; exact Subgroup.mem_bot.1 ha
    rw [this, map_one]; exact hu
  · have hnt : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
    have hoff : Nat.card V ≤ weight (ρ.comp A.subtype) ⊤ := by
      rw [weight_comp_subtype, map_subtype_top, ← weight_bot ρ]
      exact hmax ⊥ bot_le
    have hab : ∀ x y : ↥A, x * y = y * x := fun x y =>
      hAel.toIsMulCommutative.is_comm.comm x y
    have hp : IsPGroup 2 ↥A := by
      have := hAel
      exact CFSG.IsElementaryAbelian.isPGroup 2 A
    obtain ⟨B, hBbot, hwB, -, -, hquad, -⟩ :=
      abelian_prime_offender_quadratic_replacement (p := 2) (ρ.comp A.subtype) hab hp hoff
    have hBtop : B = ⊤ := by
      by_contra hne
      have hlt : B < ⊤ := lt_top_iff_ne_top.2 hne
      have h1 : ⊥ < B.map A.subtype := by
        rw [bot_lt_iff_ne_bot, Ne, Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective]
        exact hBbot
      have h2 : B.map A.subtype < A :=
        ((Subgroup.map_lt_map_iff_of_injective A.subtype_injective).2 hlt).trans_eq
          (map_subtype_top A)
      have h3 := hstrict _ h1 h2
      have hw : weight (ρ.comp A.subtype) ⊤ = weight ρ A := by
        rw [weight_comp_subtype, map_subtype_top]
      rw [← weight_comp_subtype, ← hw] at h3
      exact absurd hwB (not_le.2 h3)
    subst hBtop
    have hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v := fun b hb v =>
      hquad ⟨a, ha⟩ (Subgroup.mem_top _) ⟨b, hb⟩ (Subgroup.mem_top _) v
    exact bestOffender_invariance ρ H A hAn hAel hHA hno hch hmax ha hq hI hIc hIirr u hu

end General

end CFSG.QuasithinUnique.Setup.Layer
