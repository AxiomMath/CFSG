module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlane
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace OddAbelianSetting

variable [CharP k 2] [Finite V] {G N A : Subgroup (V ≃ₗ[k] V)} (h : OddAbelianSetting G N A)

private instance instFiniteGL' : Finite (V ≃ₗ[k] V) := finite_linearEquiv

include h

theorem threePlane : ∃ I : Submodule k V, ThreePlane G N A I := by
  classical
  obtain ⟨I, hI, hI0, hIA⟩ := h.exists_module
  have hIL : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ I := hI.inv
  have hInt : I ≠ ⊥ := fun hb => hI.irr.1 (hb ▸ bot_le)
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.2 hInt
  let rL := resSub (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ I hIL
  let rA := resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hIA
  have hirr₀ : IsIrrAct rL.range :=
    isIrrAct_range_resSub (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ I hIL (fun U hU hUI => by
      have := hI.irr.2 U hU (by rw [hI0]; exact bot_le) hUI
      rwa [hI0] at this)
  have hH₀ne : rL.range ≠ ⊥ := by
    intro hb
    apply hI.irr.1
    intro u hu l hl
    have h1 : rL ⟨l, hl⟩ = 1 := by
      have : rL ⟨l, hl⟩ ∈ rL.range := ⟨_, rfl⟩
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    have h2 := congrArg (fun f : I ≃ₗ[k] I => ((f ⟨u, hu⟩ : I) : V)) h1
    simpa [rL, resSub_apply] using h2
  have hH₀ab : ∀ x y : rL.range, x * y = y * x := by
    rintro ⟨_, l₁, rfl⟩ ⟨_, l₂, rfl⟩
    apply Subtype.ext
    exact resSub_mul_comm hIL hIL l₁.2 l₂.2 (by
      have hh := congrArg Subtype.val
        (h.N_abelian ⟨l₁, h.L_le_N l₁.2⟩ ⟨l₂, h.L_le_N l₂.2⟩)
      exact hh)
  have hH₀odd : Odd (Nat.card rL.range) :=
    Odd.of_dvd_nat h.L_odd (Subgroup.card_range_dvd rL)
  have hA₀ne : rA.range ≠ ⊥ := by
    intro hb
    have hAtriv : ∀ a ∈ A, ∀ u ∈ I, (a : V ≃ₗ[k] V) u = u := by
      intro a ha u hu
      have h1 : rA ⟨a, ha⟩ = 1 := by
        have : rA ⟨a, ha⟩ ∈ rA.range := ⟨_, rfl⟩
        rw [hb] at this
        exact Subgroup.mem_bot.1 this
      have h2 := congrArg (fun f : I ≃ₗ[k] I => ((f ⟨u, hu⟩ : I) : V)) h1
      simpa [rA, resSub_apply] using h2
    have hLC : ⁅⁅N, A⁆, A⁆ ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) I := by
      refine Subgroup.commutator_le.2 fun l hl a ha u hu => ?_
      have hu1 : (a : V ≃ₗ[k] V)⁻¹ u = u := hAtriv _ (A.inv_mem ha) u hu
      have hu2 : (l : V ≃ₗ[k] V)⁻¹ u ∈ I := hIL _ (Subgroup.inv_mem _ hl) u hu
      have hu3 : (a : V ≃ₗ[k] V) ((l : V ≃ₗ[k] V)⁻¹ u) = (l : V ≃ₗ[k] V)⁻¹ u := hAtriv a ha _ hu2
      show ((⁅l, a⁆ : V ≃ₗ[k] V)) u = u
      rw [commutatorElement_def]
      show (l : V ≃ₗ[k] V) ((a : V ≃ₗ[k] V) ((l : V ≃ₗ[k] V)⁻¹ ((a : V ≃ₗ[k] V)⁻¹ u))) = u
      rw [hu1, hu3]
      exact ρ_apply_inv (MonoidHom.id (V ≃ₗ[k] V)) l u
    rw [h.comm_comm] at hLC
    apply hI.irr.1
    intro u hu l hl
    exact hLC hl u hu
  have hBN : rA.range ≤ Subgroup.normalizer (rL.range : Set (I ≃ₗ[k] I)) := by
    rintro _ ⟨y, rfl⟩
    exact resSub_mem_normalizer_range hIL hIA h.A_le_normalizer_L y
  have : CFSG.IsElementaryAbelian 2 rA.range := isElementaryAbelian_range rA h.A_elem
  have hoff₀ : Nat.card ↥I ≤ Nat.card rA.range * Nat.card (fixGL rA.range) :=
    natCard_le_weight_res (MonoidHom.id (V ≃ₗ[k] V)) A I hIA h.hmax
  obtain ⟨hk, hdim, hH3, hB2, hHB, hwt⟩ :=
    irreducible_odd_abelian_offender_forces_binary_natural_three_actor (W := ↥I) rL.range hirr₀
      hH₀ne hH₀ab hH₀odd rA.range hBN hA₀ne hoff₀
  have hW' : ∀ a : ↥A, ∀ w ∈ I, ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) a w ∈ I :=
    fun a w hw => hIA a a.2 w hw
  have hmaxA : ∀ B : Subgroup ↥A, weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) B ≤
      weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤ := by
    intro B
    rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
    exact h.hmax _ (Subgroup.map_subtype_le B)
  have hw : weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤ =
      weight (MonoidHom.id (V ≃ₗ[k] V)) A := by
    rw [weight_comp_subtype, map_subtype_top]
  have hstrictA : ∀ B : Subgroup ↥A, ⊥ < B → B < ⊤ →
      weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) B <
        weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤ := by
    intro B hB1 hB2
    have h1 : ⊥ < B.map A.subtype := by
      rw [bot_lt_iff_ne_bot, Ne, Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective]
      exact bot_lt_iff_ne_bot.1 hB1
    have h2 : B.map A.subtype < A :=
      ((Subgroup.map_lt_map_iff_of_injective A.subtype_injective).2 hB2).trans_eq
        (map_subtype_top A)
    have h3 := h.strict _ h1 h2
    rw [weight_comp_subtype, hw]
    exact h3
  have hWAne : commSub ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤ I ≠ ⊥ := by
    intro hb
    apply hA₀ne
    rw [eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    have h1 := (commSub_eq_bot_iff _ ⊤ I).1 hb a (Subgroup.mem_top a) u u.2
    simpa [rA, resSub_apply] using h1
  have heq : (centSub ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) I).index *
      Nat.card ↥(I ⊓ fixSub ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤) = Nat.card ↥I := by
    have h1 := weightId_range ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) I hW'
    rw [← h1]
    exact hwt
  obtain ⟨hCA, hVsup⟩ := (minimal_fixedWeight_restriction_faithful_splitting
    ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) I hW' hmaxA hstrictA hWAne).2.2 heq
  have hfixA : fixSub ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤ = fixGL A := by
    rw [fixSub_comp_subtype, map_subtype_top]
  have hVeq : I ⊔ fixGL A = ⊤ := by rw [← hfixA]; exact hVsup
  have hinjA : Function.Injective rA := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have := ker_resHom ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) I hW'
    rw [← hCA]
    exact this
  have hcardA : Nat.card A = 2 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinjA).toEquiv]; exact hB2
  have hAtriv' : ∀ a ∈ A, ∀ v : V, (a : V ≃ₗ[k] V) v - v ∈ I := by
    intro a ha v
    have hv : v ∈ I ⊔ fixGL A := by rw [hVeq]; exact Submodule.mem_top
    obtain ⟨i, hi, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hc' : (a : V ≃ₗ[k] V) c = c := hc a ha
    have : (a : V ≃ₗ[k] V) (i + c) - (i + c) = (a : V ≃ₗ[k] V) i - i := by
      rw [map_add, hc']; abel
    rw [this]
    exact I.sub_mem (hIA a ha i hi) hi
  have hIsup : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I :=
    isInvariant_sup_subgroup hIL hIA
  have htriv := triv_of_commutator (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ A I hIsup hAtriv'
    h.comm_comm
  have hIeq : I = commGL ⁅N, A⁆ ⊤ := by
    refine le_antisymm ?_ (commSub_le_iff.2 fun l hl u _ => htriv l (Subgroup.mem_sup_left hl) u)
    calc I = commSub (MonoidHom.id (V ≃ₗ[k] V)) ⁅N, A⁆ I := hI.comm.symm
      _ ≤ commGL ⁅N, A⁆ ⊤ := commSub_mono_right _ le_top
  have hIeq' : I = commGL (⁅N, A⁆ ⊔ A) ⊤ := by
    refine le_antisymm ?_ (commSub_le_iff.2 fun g hg u _ => htriv g hg u)
    exact hIeq.le.trans (commSub_mono_left _ le_sup_left)
  have hCL : centSub ((MonoidHom.id (V ≃ₗ[k] V)).comp (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)).subtype) I =
      ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    have hl' : ∀ u ∈ I, (l : V ≃ₗ[k] V) u = u := hl
    have hodd : Odd (orderOf (l : V ≃ₗ[k] V)) :=
      Odd.of_dvd_nat h.L_odd (Subgroup.orderOf_dvd_natCard _ l.2)
    have hq : ∀ u ∈ (⊤ : Submodule k V),
        (l : V ≃ₗ[k] V) ((l : V ≃ₗ[k] V) u - u) = (l : V ≃ₗ[k] V) u - u := fun u _ =>
      hl' _ (htriv l (Subgroup.mem_sup_left l.2) u)
    have hfix := fix_of_quadratic_oddOrder (MonoidHom.id (V ≃ₗ[k] V)) (x := (l : V ≃ₗ[k] V))
      hodd hq
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hfix v Submodule.mem_top
  have hinjL : Function.Injective rL := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have := ker_resHom ((MonoidHom.id (V ≃ₗ[k] V)).comp (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)).subtype) I
      (fun a w hw => hIL a a.2 w hw)
    rw [← hCL]
    exact this
  have hcardL : Nat.card (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) = 3 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinjL).toEquiv]; exact hH3
  have hbot : rL.range ⊓ rA.range = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(rL.range ⊓ rA.range) ∣ 3 := hH3 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(rL.range ⊓ rA.range) ∣ 2 := hB2 ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 := Nat.dvd_gcd h1 h2
    exact Nat.eq_one_of_dvd_one (by simpa using h3)
  have hbij : Function.Bijective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hIsup) := by
    have hL_r : ∀ (l : V ≃ₗ[k] V) (hl : l ∈ (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))),
        rL ⟨l, hl⟩ = resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hIsup
          ⟨l, Subgroup.mem_sup_left hl⟩ := by
      intro l hl
      apply LinearEquiv.ext; intro u; apply Subtype.ext
      simp only [rL, resSub_apply]
    have hA_r : ∀ (a : V ≃ₗ[k] V) (ha : a ∈ A),
        rA ⟨a, ha⟩ = resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hIsup
          ⟨a, Subgroup.mem_sup_right ha⟩ := by
      intro a ha
      apply LinearEquiv.ext; intro u; apply Subtype.ext
      simp only [rA, resSub_apply]
    have hsurj : Function.Surjective
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hIsup) := by
      have h1 : rL.range ⊔ rA.range ≤
          (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅N, A⁆ ⊔ A) I hIsup).range := by
        refine sup_le ?_ ?_
        · rintro _ ⟨l, rfl⟩
          exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, (hL_r l l.2).symm⟩
        · rintro _ ⟨a, rfl⟩
          exact ⟨⟨a, Subgroup.mem_sup_right a.2⟩, (hA_r a a.2).symm⟩
      rw [hHB] at h1
      exact MonoidHom.range_eq_top.1 (top_le_iff.1 h1)
    refine ⟨?_, hsurj⟩
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    obtain ⟨l, hl, a, ha, hga⟩ := mem_sup_mul h.A_le_normalizer_L g.2
    have h1 : rL ⟨l, hl⟩ * rA ⟨a, ha⟩ = 1 := by
      rw [hL_r l hl, hA_r a ha, ← map_mul]
      have : (⟨l, Subgroup.mem_sup_left hl⟩ * ⟨a, Subgroup.mem_sup_right ha⟩ :
          ↥(⁅N, A⁆ ⊔ A)) = g := Subtype.ext hga.symm
      rw [this]; exact hg
    have h2 : rL ⟨l, hl⟩ = (rA ⟨a, ha⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : rL ⟨l, hl⟩ ∈ rL.range ⊓ rA.range :=
      ⟨⟨_, rfl⟩, by rw [h2]; exact Subgroup.inv_mem _ ⟨_, rfl⟩⟩
    rw [hbot, Subgroup.mem_bot] at h3
    have hl1 : (⟨l, hl⟩ : ↥(⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))) = 1 :=
      hinjL (h3.trans (map_one rL).symm)
    have ha1 : rA ⟨a, ha⟩ = 1 := by
      rw [h3, one_mul] at h1; exact h1
    have ha2 : (⟨a, ha⟩ : ↥A) = 1 := hinjA (ha1.trans (map_one rA).symm)
    have hl2 : l = 1 := congrArg Subtype.val hl1
    have ha3 : a = 1 := congrArg Subtype.val ha2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hga, hl2, ha3, mul_one]
    rfl
  have hinvN : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) N I := by
    intro n hn u hu
    have hcomm : ∀ l ∈ (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)), n * l = l * n := by
      intro l hl
      have hh := congrArg Subtype.val (h.N_abelian ⟨n, hn⟩ ⟨l, h.L_le_N hl⟩)
      exact hh
    rw [hIeq] at hu ⊢
    exact map_mem_commSub_top_of_commute (MonoidHom.id _) _ hcomm hu
  have h4 : Nat.card ↥I = 4 := by
    have : Module.Finite k ↥I := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := k) (V := ↥I), hk, hdim]
    norm_num
  have hfix2 : Nat.card (fixGL rA.range) = 2 := by
    have h5 := hwt
    rw [hB2, h4] at h5
    omega
  have hCN : N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)) =
      N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) I := by
    apply le_antisymm
    · intro n hn
      refine ⟨hn.1, ?_⟩
      have hHc : ∀ x ∈ rL.range,
          resSub (MonoidHom.id (V ≃ₗ[k] V)) N I hinvN ⟨n, hn.1⟩ * x =
            x * resSub (MonoidHom.id (V ≃ₗ[k] V)) N I hinvN ⟨n, hn.1⟩ := by
        rintro _ ⟨l, rfl⟩
        refine resSub_mul_comm hinvN hIL hn.1 l.2 ?_
        have hh := congrArg Subtype.val (h.N_abelian ⟨n, hn.1⟩ ⟨l, h.L_le_N l.2⟩)
        exact hh
      have hAc : ∀ x ∈ rA.range,
          resSub (MonoidHom.id (V ≃ₗ[k] V)) N I hinvN ⟨n, hn.1⟩ * x =
            x * resSub (MonoidHom.id (V ≃ₗ[k] V)) N I hinvN ⟨n, hn.1⟩ := by
        rintro _ ⟨a, rfl⟩
        exact resSub_mul_comm hinvN hIA hn.1 a.2 (Subgroup.mem_centralizer_iff.1 hn.2 a a.2).symm
      have h1 := eq_one_of_commutes rL.range rA.range hirr₀ hfix2 _ hHc hAc
      intro u hu
      have h2 := congrArg (fun f : I ≃ₗ[k] I => ((f ⟨u, hu⟩ : I) : V)) h1
      simpa [resSub_apply] using h2
    · intro n hn
      refine ⟨hn.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      have hn' : ∀ u ∈ I, (n : V ≃ₗ[k] V) u = u := hn.2
      have hc1 : ⁅n, a⁆ ∈ (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) :=
        Subgroup.commutator_mem_commutator hn.1 ha
      have hc2 : ∀ u ∈ I, ((⁅n, a⁆ : V ≃ₗ[k] V)) u = u := by
        intro u hu
        have h1 : (a : V ≃ₗ[k] V)⁻¹ u ∈ I := hIA a⁻¹ (A.inv_mem ha) u hu
        have h2 : (n : V ≃ₗ[k] V)⁻¹ ((a : V ≃ₗ[k] V)⁻¹ u) = (a : V ≃ₗ[k] V)⁻¹ u := by
          have h3 : (n : V ≃ₗ[k] V) ((a : V ≃ₗ[k] V)⁻¹ u) = (a : V ≃ₗ[k] V)⁻¹ u := hn' _ h1
          calc (n : V ≃ₗ[k] V)⁻¹ ((a : V ≃ₗ[k] V)⁻¹ u)
              = (n : V ≃ₗ[k] V)⁻¹ ((n : V ≃ₗ[k] V) ((a : V ≃ₗ[k] V)⁻¹ u)) := by rw [h3]
            _ = (a : V ≃ₗ[k] V)⁻¹ u := ρ_inv_apply (MonoidHom.id (V ≃ₗ[k] V)) n _
        rw [commutatorElement_def]
        show (n : V ≃ₗ[k] V) ((a : V ≃ₗ[k] V) ((n : V ≃ₗ[k] V)⁻¹ ((a : V ≃ₗ[k] V)⁻¹ u))) = u
        have h7 : (a : V ≃ₗ[k] V) ((a : V ≃ₗ[k] V)⁻¹ u) = u :=
          ρ_apply_inv (MonoidHom.id (V ≃ₗ[k] V)) a u
        rw [h2, h7]
        exact hn' u hu
      have h5 : (⟨⁅n, a⁆, hc1⟩ : ↥(⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))) ∈
          centSub ((MonoidHom.id (V ≃ₗ[k] V)).comp (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)).subtype) I :=
        hc2
      rw [hCL, Subgroup.mem_bot] at h5
      have h6 : ⁅n, a⁆ = 1 := congrArg Subtype.val h5
      rw [commutatorElement_eq_one_iff_mul_comm] at h6
      exact h6.symm
  have hNeq : N = (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) ⊔
      (N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V))) := by
    rw [sup_comm]
    exact (coprime_abelian_decomp N A h.A_le_normalizer_N h.N_abelian h.coprime_AN).1.symm
  have hdisj : Disjoint (⁅N, A⁆ : Subgroup (V ≃ₗ[k] V))
      (N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V))) :=
    (coprime_abelian_decomp N A h.A_le_normalizer_N h.N_abelian h.coprime_AN).2.symm
  have hweight : weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V := by
    have hcard := natCard_sup_mul_natCard_inf I (fixGL A)
    rw [hVeq] at hcard
    have htop : Nat.card ↥(⊤ : Submodule k V) = Nat.card V :=
      Nat.card_congr (Submodule.topEquiv (R := k) (M := V)).toEquiv
    have hfx : Nat.card ↥(fixGL rA.range) = Nat.card ↥(I ⊓ fixGL A) := by
      have h1 := card_fixSub_id_map ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) I hW' ⊤
      rw [← MonoidHom.range_eq_map, hfixA] at h1
      exact h1
    rw [htop, ← hfx, hfix2, h4] at hcard
    show Nat.card ↥A * Nat.card ↥(fixGL A) = Nat.card V
    rw [hcardA]
    omega
  have hLnormal : ((⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)).subgroupOf N).Normal := by
    have : IsMulCommutative ↥N := ⟨⟨h.N_abelian⟩⟩
    exact Subgroup.normal_of_isMulCommutative _
  exact ⟨I, ⟨hk, hcardA, hcardL, h.L_le_N, hLnormal, h.N_normal, hIeq, hIA, hinvN, hdim, h4,
    ⟨hIsup, hbij⟩, hVeq, hNeq, hdisj, hCN, hIeq', hweight⟩⟩

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
