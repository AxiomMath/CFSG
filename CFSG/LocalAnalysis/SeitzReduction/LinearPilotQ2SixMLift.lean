module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveMLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMFix
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESplit

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Fix

variable {G : Type} [Group G] [Finite G] {W : Subgroup G}

theorem le_card_of_inf_centralizer_barLift_eq_bot {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A)
    (hsimp : ∀ M : Subgroup (seitzBar W), M ≤ A → A ≤ normalizer (M : Set (seitzBar W)) →
      M = ⊥ ∨ M = A)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {b : ℕ}
    (hfact : ∀ k, k ∣ Nat.card W → Nat.card A ∣ (k - 1).factorial → b ≤ k)
    (hfix : W ⊓ centralizer (barLift A : Set G) = ⊥) (U : Subgroup G) (hUW : U ≤ W)
    (hXU : barLift A ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) : b ≤ Nat.card U := by
  have hXN : barLift A ≤ normalizer (W : Set G) := barLift_le_normalizer A
  have hX : barImg W (barLift A) = A := barImg_barLift hA
  have hXcard : Nat.card (barLift A) = Nat.card A * Nat.card (barLift A ⊓ W : Subgroup G) := by
    rw [card_eq_card_barImg_mul hXN, hX]
  rcases le_centralizer_or_inf_le_of_simple hA hsimp hW hUW hXU with h | h
  · exfalso
    apply hU
    rw [eq_bot_iff, ← hfix]
    intro u hu
    exact mem_inf.2 ⟨hUW hu, mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (h hx) u hu).symm⟩
  · exact hfact _ (Subgroup.card_dvd_of_le hUW)
      (dvd_factorial_of_card_eq_mul hXU (le_inf inf_le_left h) hXcard)

theorem ne_bot_inf_centralizer_barLift_of_dvd {t : G} (htN : t ∈ normalizer (W : Set G))
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1) {b : ℕ}
    (hWc : Nat.card W = b * b) (hb1 : b ≠ 1) {s : seitzBar W}
    (hs : QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨t, htN⟩ = s)
    (hs2 : s * s = 1) {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A)
    (hsimp : ∀ M : Subgroup (seitzBar W), M ≤ A → A ≤ normalizer (M : Set (seitzBar W)) →
      M = ⊥ ∨ M = A)
    (hfact : ∀ k, k ∣ Nat.card W → Nat.card A ∣ (k - 1).factorial → b ≤ k)
    (hcomm : ⁅A, A.map (MulAut.conj s).toMonoidHom⁆ = ⊥)
    (hinf : A ⊓ A.map (MulAut.conj s).toMonoidHom = ⊥)
    {ι : Type*} (τ : ι → G) (hτN : ∀ i, τ i ∈ normalizer (W : Set G))
    (hτA : ∀ i, QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨τ i, hτN i⟩ ∈
      A ⊔ A.map (MulAut.conj s).toMonoidHom)
    (hτs : ∀ i, s * QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨τ i, hτN i⟩ =
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨τ i, hτN i⟩ * s)
    (hτ2 : ∀ i, τ i * τ i = 1) (hτW : ∀ i, τ i ∉ W)
    (R : ι → ι → Prop) (hR : ∀ i j, R i j → τ i * τ j = τ j * τ i)
    (hconn : ∀ i j, ∃ k, R i k ∧ R k j) (i₀ : ι)
    (hgen : Nat.card A ≤ Nat.card (closure (Set.range fun i =>
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨τ i, hτN i⟩))) :
    W ⊓ centralizer (barLift A : Set G) ≠ ⊥ := by
  set N := normalizer (W : Set G) with hNdef
  set q := QuotientGroup.mk' (W.subgroupOf N) with hq
  have hXN : barLift A ≤ N := barLift_le_normalizer A
  have hX : barImg W (barLift A) = A := barImg_barLift hA
  have hcomm' : ⁅A, A.map (MulAut.conj (q ⟨t, htN⟩)).toMonoidHom⁆ = ⊥ := by rw [hs]; exact hcomm
  have hXY := commutator_barLift_map_conj_le htN hA hcomm'
  intro hfix
  have hAs : A.map (MulAut.conj s).toMonoidHom ≤ centralizer (A : Set (seitzBar W)) :=
    commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hcomm)
  have hbig : ∀ U : Subgroup G, U ≤ W → barLift A ≤ normalizer (U : Set G) → U ≠ ⊥ →
      b ≤ Nat.card U := le_card_of_inf_centralizer_barLift_eq_bot hA hsimp hW hfact hfix
  have hfac : ∀ i, ∃ f ∈ A, f * (s * f * s⁻¹) = q ⟨τ i, hτN i⟩ := fun i =>
    exists_mem_mul_conj_eq_of_mem_sup hs2 hAs hinf (hτA i) (hτs i)
  choose f hfA hfδ using hfac
  have hδinj := linearSwapDiag_injective hAs hinf
  have hδf : ∀ i, linearSwapDiag hAs ⟨f i, hfA i⟩ = q ⟨τ i, hτN i⟩ := fun i => hfδ i
  have hf2 : ∀ i, f i * f i = 1 := by
    intro i
    have h1 : linearSwapDiag hAs (⟨f i, hfA i⟩ * ⟨f i, hfA i⟩) = linearSwapDiag hAs 1 := by
      have h2 : (⟨τ i, hτN i⟩ : N) * ⟨τ i, hτN i⟩ = 1 := Subtype.ext (hτ2 i)
      rw [map_mul, hδf, map_one, ← map_mul, h2, map_one]
    exact congrArg Subtype.val (hδinj h1)
  have hfR : ∀ i j, R i j → f i * f j = f j * f i := by
    intro i j hij
    have h1 : linearSwapDiag hAs (⟨f i, hfA i⟩ * ⟨f j, hfA j⟩) =
        linearSwapDiag hAs (⟨f j, hfA j⟩ * ⟨f i, hfA i⟩) := by
      have h2 : (⟨τ i, hτN i⟩ : N) * ⟨τ j, hτN j⟩ = ⟨τ j, hτN j⟩ * ⟨τ i, hτN i⟩ :=
        Subtype.ext (hR i j hij)
      rw [map_mul, map_mul, hδf, hδf, ← map_mul, ← map_mul, h2]
    exact congrArg Subtype.val (hδinj h1)
  have hf1 : ∀ i, f i ≠ 1 := by
    intro i h
    apply hτW i
    have h1 : q ⟨τ i, hτN i⟩ = 1 := by
      rw [← hδf, show (⟨f i, hfA i⟩ : A) = 1 from Subtype.ext h, map_one]
    exact (mk_eq_one_iff_mem (hτN i)).1 h1
  have hlift : ∀ i, ∃ x ∈ barLift A, ∃ hxN : x ∈ N, q ⟨x, hxN⟩ = f i := fun i =>
    exists_of_mem_barImg (hX.symm ▸ hfA i)
  choose x hxX hxN hxf using hlift
  have hyN : ∀ i, t * x i * t⁻¹ ∈ N := fun i => mul_mem (mul_mem htN (hxN i)) (inv_mem htN)
  have hyq : ∀ i, q ⟨t * x i * t⁻¹, hyN i⟩ = s * f i * s⁻¹ := by
    intro i
    rw [← hs, ← hxf i, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hmemW : ∀ g (hg : g ∈ N), q ⟨g, hg⟩ = 1 → g ∈ centralizer (W : Set G) := by
    intro g hg h1
    have hgW := (mk_eq_one_iff_mem hg).1 h1
    exact mem_centralizer_iff.2 fun w hw => hW w hw g hgW
  have hy2 : ∀ i, (t * x i * t⁻¹) * (t * x i * t⁻¹) ∈ centralizer (W : Set G) := by
    intro i
    apply hmemW _ (mul_mem (hyN i) (hyN i))
    show q (⟨t * x i * t⁻¹, hyN i⟩ * ⟨t * x i * t⁻¹, hyN i⟩) = 1
    rw [map_mul, hyq]
    calc s * f i * s⁻¹ * (s * f i * s⁻¹) = s * (f i * f i) * s⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have hXy : ∀ i, ∀ x' ∈ barLift A, x' * (t * x i * t⁻¹) * x'⁻¹ * (t * x i * t⁻¹)⁻¹ ∈
      centralizer (W : Set G) := by
    intro i x' hx'
    have hc : ⁅x', t * x i * t⁻¹⁆ ∈ W :=
      hXY (commutator_mem_commutator hx' ⟨x i, hxX i, rfl⟩)
    rw [commutatorElement_def] at hc
    exact mem_centralizer_iff.2 fun w hw => hW w hw _ hc
  have hyR : ∀ i j, R i j → (t * x i * t⁻¹) * (t * x j * t⁻¹) * (t * x i * t⁻¹)⁻¹ *
      (t * x j * t⁻¹)⁻¹ ∈ centralizer (W : Set G) := by
    intro i j hij
    apply hmemW _ (mul_mem (mul_mem (mul_mem (hyN i) (hyN j)) (inv_mem (hyN i))) (inv_mem (hyN j)))
    show q (⟨t * x i * t⁻¹, hyN i⟩ * ⟨t * x j * t⁻¹, hyN j⟩ * (⟨t * x i * t⁻¹, hyN i⟩)⁻¹ *
      (⟨t * x j * t⁻¹, hyN j⟩)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyq, hyq]
    calc s * f i * s⁻¹ * (s * f j * s⁻¹) * (s * f i * s⁻¹)⁻¹ * (s * f j * s⁻¹)⁻¹
        = s * (f i * f j * (f j * f i)⁻¹) * s⁻¹ := by group
      _ = 1 := by rw [hfR i j hij]; group
  have hyW : ∀ i, ¬ W ≤ centralizer ({t * x i * t⁻¹} : Set G) := by
    intro i h
    have hxC : x i ∈ barLift A ⊓ centralizer (W : Set G) := by
      refine mem_inf.2 ⟨hxX i, mem_centralizer_iff.2 fun w hw => ?_⟩
      have hw' : t * w * t⁻¹ ∈ W := (mem_normalizer_iff.1 htN w).1 hw
      have h1 : (t * w * t⁻¹) * (t * x i * t⁻¹) = (t * x i * t⁻¹) * (t * w * t⁻¹) :=
        mem_centralizer_singleton_iff.1 (h hw')
      calc w * x i = t⁻¹ * ((t * w * t⁻¹) * (t * x i * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * x i * t⁻¹) * (t * w * t⁻¹)) * t := by rw [h1]
        _ = x i * w := by group
    rcases le_centralizer_or_inf_le_of_simple hA hsimp hW le_rfl hXN with h2 | h2
    · have hWX : W ≤ W ⊓ centralizer (barLift A : Set G) := fun w hw =>
        mem_inf.2 ⟨hw, mem_centralizer_iff.2 fun x' hx' =>
          (mem_centralizer_iff.1 (h2 hx') w hw).symm⟩
      rw [hfix, le_bot_iff] at hWX
      rw [hWX, card_bot] at hWc
      exact hb1 (Nat.eq_one_of_mul_eq_one_right hWc.symm)
    · apply hf1 i
      rw [← hxf i]
      exact (mk_eq_one_iff_mem (hxN i)).2 (h2 hxC)
  have hgenA : A ≤ closure (Set.range f) := by
    set C' : Subgroup A := closure (Set.range fun i => (⟨f i, hfA i⟩ : A)) with hC'
    have hmap : C'.map (linearSwapDiag hAs) = closure (Set.range fun i => q ⟨τ i, hτN i⟩) := by
      rw [hC', MonoidHom.map_closure, ← Set.range_comp]
      congr 2
      funext i
      exact hδf i
    have hcard : Nat.card A ≤ Nat.card C' := by
      calc Nat.card A ≤ _ := hgen
        _ = Nat.card (C'.map (linearSwapDiag hAs)) := by rw [hmap]
        _ = Nat.card C' := Subgroup.card_map_of_injective hδinj
    have htop : C' = ⊤ := Subgroup.eq_top_of_le_card C' hcard
    intro a ha
    have h1 : (⟨a, ha⟩ : A) ∈ C' := htop ▸ mem_top _
    have h2 : ((⟨a, ha⟩ : A) : seitzBar W) ∈ C'.map A.subtype := mem_map_of_mem _ h1
    rw [hC', MonoidHom.map_closure, ← Set.range_comp] at h2
    exact h2
  have hgenY : barImg W ((barLift A).map (MulAut.conj t).toMonoidHom) ≤
      barImg W (closure (Set.range fun i => t * x i * t⁻¹)) := by
    rw [barImg_map_conj hXN htN, hX, hs]
    refine (map_mono hgenA).trans ?_
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have h1 := mem_barImg_of_mem (subset_closure ⟨i, rfl⟩ :
      t * x i * t⁻¹ ∈ closure (Set.range fun i => t * x i * t⁻¹)) (hyN i)
    rw [hyq] at h1
    exact h1
  have hYN : (barLift A).map (MulAut.conj t).toMonoidHom ≤ N := by
    rintro _ ⟨x', hx', rfl⟩
    exact mul_mem (mul_mem htN (hXN hx')) (inv_mem htN)
  have hgenX : (barLift A).map (MulAut.conj t).toMonoidHom ≤
      closure (Set.range fun i => t * x i * t⁻¹) ⊔ W := le_sup_of_barImg_le hYN hgenY
  obtain ⟨U, hUW, hUb, hUy⟩ := exists_le_centralizer_of_chain_of_mul_self hW hW2 hWc hb1 hXN
    hbig (fun i => t * x i * t⁻¹) hyN hy2 hXy hyW R hyR hconn i₀
  have hUX : ∀ u ∈ U, ∀ z ∈ (barLift A).map (MulAut.conj t).toMonoidHom, z * u = u * z := by
    intro u hu z hz
    have hcl : closure (Set.range fun i => t * x i * t⁻¹) ⊔ W ≤ centralizer ({u} : Set G) := by
      refine sup_le ?_ fun w hw => ?_
      · rw [closure_le]
        rintro _ ⟨i, rfl⟩
        have h1 := mem_centralizer_singleton_iff.1 (hUy i hu)
        exact mem_centralizer_singleton_iff.2 h1.symm
      · exact mem_centralizer_singleton_iff.2 (hW w hw u (hUW hu))
    exact mem_centralizer_singleton_iff.1 (hcl (hgenX hz))
  have hUbot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [mem_bot]
    have hu' : t⁻¹ * u * t ∈ W ⊓ centralizer (barLift A : Set G) := by
      refine mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun x' hx' => ?_⟩
      · have h1 := (mem_normalizer_iff.1 (inv_mem htN) u).1 (hUW hu)
        rwa [inv_inv] at h1
      · have h1 := hUX u hu (t * x' * t⁻¹) ⟨x', hx', rfl⟩
        calc x' * (t⁻¹ * u * t) = t⁻¹ * ((t * x' * t⁻¹) * u) * t := by group
          _ = t⁻¹ * (u * (t * x' * t⁻¹)) * t := by rw [h1]
          _ = t⁻¹ * u * t * x' := by group
    rw [hfix, mem_bot] at hu'
    calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
      _ = 1 := by rw [hu']; group
  rw [hUbot, card_bot] at hUb
  exact hb1 hUb.symm

end Fix

end CFSG.SeitzReduction.LinearPilot
