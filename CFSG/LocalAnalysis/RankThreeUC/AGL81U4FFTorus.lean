module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusC
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_of_normal_closure {L Θ N : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L) (hΘL : Θ ≤ L)
    (hΘ : Θ ≠ ⊥) (hNL : N ≤ L) (hN : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N) (hΘN : Θ ≤ N) :
    N = L := by
  let N' : Subgroup ↥L := N.subgroupOf L
  have hnorm : N'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN g g.2 n hn⟩
  haveI := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal N' with h | h
  · exfalso
    apply hΘ
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hΘL hx⟩ : ↥L) ∈ N' := by
      rw [Subgroup.mem_subgroupOf]
      exact hΘN hx
    rw [h, Subgroup.mem_bot] at hx'
    simpa using congrArg Subtype.val hx'
  · refine le_antisymm hNL fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ N' := by rw [h]; exact Subgroup.mem_top _
    exact this

theorem commV_le_of_commSub_le {L Θ : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥L)
    (hna : ∃ a b : ↥L, a * b ≠ b * a) (hΘL : Θ ≤ L) (hΘ : Θ ≠ ⊥) {C : Subgroup V}
    (hCL : ∀ l ∈ L, ∀ x ∈ C, l x ∈ C) (hCΘ : commSub (commV L) Θ ≤ C) : commV L ≤ C := by
  have hUL : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := fun g hg u hu =>
    (commV_stab (le_normalizer_self L hg) u).2 hu
  let N : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ L ∧ ∀ u ∈ commV L, g u * u⁻¹ ∈ C}
      one_mem' := ⟨L.one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgL, hg⟩ ⟨hhL, hh⟩
        refine ⟨L.mul_mem hgL hhL, fun u hu => ?_⟩
        have e : (g * h) u * u⁻¹ = g (h u * u⁻¹) * (g u * u⁻¹) := by
          apply cg_eq_of_add
          simp only [MulAut.mul_apply, map_mul, map_inv, ofMul_mul, ofMul_inv]
          abel
        rw [e]
        exact C.mul_mem (hCL g hgL _ (hh u hu)) (hg u hu)
      inv_mem' := by
        rintro g ⟨hgL, hg⟩
        refine ⟨L.inv_mem hgL, fun u hu => ?_⟩
        have hu' : g⁻¹ u ∈ commV L := hUL _ (L.inv_mem hgL) u hu
        have e : g⁻¹ u * u⁻¹ = (g (g⁻¹ u) * (g⁻¹ u)⁻¹)⁻¹ := by
          apply cg_eq_of_add
          simp only [MulAut.apply_inv_self, ofMul_mul, ofMul_inv]
          abel
        rw [e]
        exact C.inv_mem (hg _ hu') }
  have hNL : N ≤ L := fun g hg => hg.1
  have hN : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N := by
    rintro l hl x ⟨hxL, hx⟩
    refine ⟨L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl), fun u hu => ?_⟩
    have hu' : l⁻¹ u ∈ commV L := hUL _ (L.inv_mem hl) u hu
    have e : (l * x * l⁻¹) u * u⁻¹ = l (x (l⁻¹ u) * (l⁻¹ u)⁻¹) := by
      apply cg_eq_of_add
      simp only [MulAut.mul_apply, map_mul, map_inv, ofMul_mul, ofMul_inv, MulAut.apply_inv_self]
      try abel
    rw [e]
    exact hCL l hl _ (hx _ hu')
  have hΘN : Θ ≤ N := fun θ hθ =>
    ⟨hΘL hθ, fun u hu => hCΘ (Subgroup.subset_closure ⟨θ, hθ, u, hu, rfl⟩)⟩
  have hNeq := eq_of_normal_closure hs hΘL hΘ hNL hN hΘN
  have hUU := commSub_commV (commutator_eq_top_of_simple hs hna)
  rw [← hUU, commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, u, hu, rfl⟩
  have hgN : g ∈ N := hNeq ▸ hg
  exact hgN.2 u hu

theorem forall_of_trans {L Θ : Subgroup (MulAut V)} {c : ℕ} {Θi : Fin c → Subgroup (MulAut V)}
    {w θ₀ : MulAut V} {π : Equiv.Perm (Fin c)} (hT : IsTorusData L c Θ Θi w θ₀ π)
    {P : Fin c → Prop} (i₀ : Fin c) (h₀ : P i₀) (hstep : ∀ i, P i → P (π i)) : ∀ i, P i := by
  intro i
  obtain ⟨k, hk⟩ := hT.π_trans i₀ i
  rw [← hk]
  clear hk
  induction k with
  | zero => simpa using h₀
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hstep _ ih

theorem iSup_univ_eq {c : ℕ} (f : Fin c → Subgroup V) :
    (⨆ i ∈ (Finset.univ : Finset (Fin c)), f i) = ⨆ i, f i :=
  le_antisymm (iSup₂_le fun i _ => le_iSup f i)
    (iSup_le fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl)

theorem rk_eq_of_card_eq {W : Subgroup V} {n : ℕ} (hV : ∀ v : V, v ^ 2 = 1)
    (h : Nat.card W = 2 ^ n) : rk W = n := by
  have := card_eq_two_pow hV W
  rw [h] at this
  exact (Nat.pow_right_injective (le_refl 2) this).symm

section Main

variable [IsF2Space V] {L D Θ : Subgroup (MulAut V)} {c : ℕ} {Θi : Fin c → Subgroup (MulAut V)}
  {w θ₀ : MulAut V} {π : Equiv.Perm (Fin c)}

theorem torus_main (hT : IsTorusData L c Θ Θi w θ₀ π) (hc : 3 ≤ c) (i₀ : Fin c)
    (hs : IsSimpleGroup ↥L) (hna : ∃ a b : ↥L, a * b ≠ b * a)
    (hDcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (hD2 : ∀ d ∈ D, d * d = 1)
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d)
    {m : Polynomial (ZMod 2)} (hm : Irreducible m) (hd : 2 ≤ m.natDegree)
    (hP : ∀ x ∈ Rsub Θ (Θi i₀) (commV L ⊓ fixV D), polyAct θ₀ m x = 1)
    (hQ : ∀ x ∈ commSub (commV L ⊓ fixV D) Θ, EE Θi x = x)
    (hT2 : Nat.card ↥(Rsub Θ (Θi i₀) (commV L ⊓ fixV D)) ≤ 2 ^ m.natDegree)
    {e : ℕ} (he : e ≤ 2)
    (hcount : Nat.card (commV L) ≤
      e * Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D)) :
    commV L ≤ fixV D := by
  have hV : ∀ v : V, v ^ 2 = 1 := IsF2Space.sq_eq_one
  have hΘ : IsThetaFamily Θ Θi := hT.isThetaFamily
  have hΘL := hT.le_L
  have hwL : w ∈ L := hT.w_mem
  have hUL : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := fun g hg u hu =>
    (commV_stab (le_normalizer_self L hg) u).2 hu
  have hDnorm : D ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    Subgroup.le_set_normalizer_iff.mpr fun d hd' l hl => by
      have : d * l = l * d := hDL d hd' l hl
      rw [this, mul_inv_cancel_right]
      exact hl
  have hUD : ∀ d ∈ D, ∀ u ∈ commV L, d u ∈ commV L := fun d hd' u hu =>
    (commV_stab (hDnorm hd') u).2 hu
  have hgd : ∀ d ∈ D, ∀ g ∈ L, ∀ y : V, d (g y) = g (d y) := by
    intro d hd' g hg y
    have := congrArg (fun φ : MulAut V => φ y) (hDL d hd' g hg)
    simpa using this
  have hYL : ∀ g ∈ L, ∀ y ∈ commV L ⊓ fixV D, g y ∈ commV L ⊓ fixV D := by
    intro g hg y hy
    refine ⟨hUL g hg y hy.1, fun d hd' => ?_⟩
    rw [hgd d hd' g hg y, hy.2 d hd']
  have hUΘ : ∀ g ∈ Θ, ∀ x ∈ commV L, g x ∈ commV L := fun g hg => hUL g (hΘL hg)
  have hYΘ : ∀ g ∈ Θ, ∀ x ∈ commV L ⊓ fixV D, g x ∈ commV L ⊓ fixV D :=
    fun g hg => hYL g (hΘL hg)
  have hθN : θ₀ ^ Nat.card ↥Θ = 1 := by
    have h1 : ((⟨θ₀, hT.θ₀_mem⟩ : ↥Θ) ^ Nat.card ↥Θ : ↥Θ) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hss : ∀ x : V, polyAct θ₀ (m * m) x = 1 → polyAct θ₀ m x = 1 := fun x hx =>
    polyAct_semisimple hT.odd hθN m hx
  have hPU : ∀ x ∈ Rsub Θ (Θi i₀) (commV L), polyAct θ₀ m x = 1 :=
    layerP hDcomm hD2 hDL hΘL hT.odd hT.comm (hT.Θi_le i₀) hT.θ₀_mem hUL hUD m hss hP
  have hQU : ∀ x ∈ commSub (commV L) Θ, EE Θi x = x :=
    layerQ hΘ hDcomm hD2 hDL hΘL hUL hUD hQ
  have hS : commSub (commV L) Θ = ⨆ i, Rsub Θ (Θi i) (commV L) :=
    commSub_eq_iSup_Rsub hΘ hUΘ hQU
  suffices hsuff : commSub (commV L) Θ ≤ commV L ⊓ fixV D by
    exact (commV_le_of_commSub_le hs hna hΘL hT.ne_bot hYL hsuff).trans inf_le_right
  have hwM : ∀ M : Subgroup V, (∀ g ∈ L, ∀ x ∈ M, g x ∈ M) →
      ∀ x ∈ M, w x ∈ M ∧ w⁻¹ x ∈ M := fun M hM x hx =>
    ⟨hM w hwL x hx, hM w⁻¹ (L.inv_mem hwL) x hx⟩
  have hcardR : ∀ i, Nat.card ↥(Rsub Θ (Θi i) (commV L)) =
      Nat.card ↥(Rsub Θ (Θi i₀) (commV L)) :=
    forall_of_trans hT i₀ rfl fun i hi => by
      rw [card_Rsub_eq hT.w_Θ (hT.w_Θi i) (hwM _ hUL)]
      exact hi
  by_cases hR0 : Rsub Θ (Θi i₀) (commV L) = ⊥
  · have hRall : ∀ i, Rsub Θ (Θi i) (commV L) = ⊥ := fun i => by
      have h1 := hcardR i
      rw [hR0, Subgroup.card_bot] at h1
      exact Subgroup.card_eq_one.mp h1
    rw [hS]
    exact iSup_le fun i => by rw [hRall i]; exact bot_le
  ·
    set R₀ := Rsub Θ (Θi i₀) (commV L) with hR₀
    have hR₀U : R₀ ≤ commV L := Rsub_le hUΘ
    have hstabΘ : ∀ g ∈ Θ, g ∈ stabSub R₀ := by
      have key : ∀ g ∈ Θ, ∀ x ∈ R₀, g x ∈ R₀ := by
        intro g hg x hx
        refine ⟨commSub_stable (fun θ hθ => ?_) (fun u hu => hUΘ g hg u hu) x hx.1,
          fun θ hθ => ?_⟩
        · exact Θ.mul_mem (Θ.mul_mem hg hθ) (Θ.inv_mem hg)
        · have := hT.comm θ (hT.Θi_le i₀ hθ) g hg
          calc θ (g x) = (θ * g) x := rfl
            _ = (g * θ) x := by rw [this]
            _ = g (θ x) := rfl
            _ = g x := by rw [hx.2 θ hθ]
      exact fun g hg => mem_stabSub_of_inv (key g hg) (key g⁻¹ (Θ.inv_mem hg))
    have hRD : D ≤ stabSub R₀ := by
      have key : ∀ d ∈ D, ∀ x ∈ R₀, d x ∈ R₀ := by
        intro d hdD x hx
        refine ⟨commSub_stable (fun θ hθ => ?_) (fun u hu => hUD d hdD u hu) x hx.1,
          fun θ hθ => ?_⟩
        · have : d * θ = θ * d := hDL d hdD θ (hΘL hθ)
          rw [this, mul_inv_cancel_right]
          exact hθ
        · have := hDL d hdD θ (hΘL (hT.Θi_le i₀ hθ))
          calc θ (d x) = (θ * d) x := rfl
            _ = (d * θ) x := by rw [this]
            _ = d (θ x) := rfl
            _ = d x := by rw [hx.2 θ hθ]
      exact fun d hd' => mem_stabSub_of_inv (key d hd') (key d⁻¹ (D.inv_mem hd'))
    have hθR : θ₀ ∈ stabSub R₀ := hstabΘ θ₀ hT.θ₀_mem
    have hDθ : ∀ d ∈ D, d * θ₀ = θ₀ * d := fun d hd' => hDL d hd' θ₀ (hΘL hT.θ₀_mem)
    have hfix : Nat.card ↥(R₀ ⊓ fixV D) ≤ 2 ^ m.natDegree := by
      have e1 : R₀ ⊓ fixV D = Rsub Θ (Θi i₀) (commV L ⊓ fixV D) := by
        rw [← Rsub_inf_of_le hT.odd hUΘ hYΘ inf_le_left, ← inf_assoc, inf_eq_left.mpr hR₀U]
      rw [e1]
      exact hT2
    obtain ⟨k, hk1, hRcard, hTcard, hautcard⟩ :=
      lemma52_transfer hDcomm hD2 hRD hθR hDθ hm hPU hfix hR0
    have hRi : ∀ i, Nat.card ↥(Rsub Θ (Θi i) (commV L)) = 2 ^ (m.natDegree * k) := fun i =>
      (hcardR i).trans hRcard
    have hTi : ∀ i, Nat.card ↥(Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D)) =
        2 ^ m.natDegree := by
      refine forall_of_trans hT i₀ ?_ ?_
      · have : R₀ ⊓ (commV L ⊓ fixV D) = R₀ ⊓ fixV D := by
          rw [← inf_assoc, inf_eq_left.mpr hR₀U]
        rw [this]
        exact hTcard
      · intro i hi
        rw [card_Rsub_inf_eq hT.w_Θ (hT.w_Θi i) (hwM _ hUL) (hwM _ hYL)]
        exact hi
    have hrkR : ∀ i, rk ↥(Rsub Θ (Θi i) (commV L)) = m.natDegree * k := fun i =>
      rk_eq_of_card_eq hV (hRi i)
    have hrkT : ∀ i, rk ↥(Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D)) = m.natDegree :=
      fun i => rk_eq_of_card_eq hV (hTi i)
    have hindR : iSupIndep fun i => Rsub Θ (Θi i) (commV L) := iSupIndep_Rsub hΘ hUΘ
    have hindT : iSupIndep fun i => Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D) :=
      hindR.mono fun i => inf_le_left
    have hrkS : rk ↥(⨆ i, Rsub Θ (Θi i) (commV L)) = c * (m.natDegree * k) := by
      have h := rk_iSup_biSup_eq_sum (fun i => Rsub Θ (Θi i) (commV L)) hindR Finset.univ
      rw [iSup_univ_eq] at h
      simpa [hrkR] using h
    have hrkT' : rk ↥(⨆ i, Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D)) =
        c * m.natDegree := by
      have h := rk_iSup_biSup_eq_sum (fun i => Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D))
        hindT Finset.univ
      rw [iSup_univ_eq] at h
      simpa [hrkT] using h
    have hSY : (⨆ i, Rsub Θ (Θi i) (commV L)) ⊓ (commV L ⊓ fixV D) =
        ⨆ i, (Rsub Θ (Θi i) (commV L) ⊓ (commV L ⊓ fixV D)) := iSup_Rsub_inf hΘ hUΘ hYΘ
    have hS_le : (⨆ i, Rsub Θ (Θi i) (commV L)) ≤ commV L :=
      iSup_le fun i => Rsub_le hUΘ
    have hrkU : rk ↥(⨆ i, Rsub Θ (Θi i) (commV L)) + rk ↥(commV L ⊓ fixV D) ≤
        rk ↥(commV L) + c * m.natDegree := by
      have h1 := rk_sup_add_rk_inf (⨆ i, Rsub Θ (Θi i) (commV L)) (commV L ⊓ fixV D)
      rw [hSY, hrkT'] at h1
      have h2 : rk ↥((⨆ i, Rsub Θ (Θi i) (commV L)) ⊔ (commV L ⊓ fixV D)) ≤
          rk ↥(commV L) := rk_mono (sup_le hS_le inf_le_left)
      omega
    have hautU : Nat.card (autSub D (commV L)) ≤ Nat.card (autSub D R₀) := by
      have hDU : D ≤ stabSub (commV L) := fun d hd' =>
        mem_stabSub_of_inv (hUD d hd') (hUD d⁻¹ (D.inv_mem hd'))
      have e1 := card_autSub_mul hDU
      have e2 := card_autSub_mul hRD
      have hle : D ⊓ centSub R₀ ≤ D ⊓ centSub (commV L) := by
        rintro d ⟨hdD, hdc⟩
        refine ⟨hdD, ?_⟩
        have hcz : ∀ i, ∀ x ∈ Rsub Θ (Θi i) (commV L), d x = x := by
          refine forall_of_trans hT i₀ (fun x hx => hdc x hx) ?_
          intro i hi x hx
          rw [← map_Rsub hT.w_Θ (hT.w_Θi i) (hwM _ hUL)] at hx
          obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
          show d (w x') = w x'
          rw [hgd d hdD w hwL x', hi x' hx']
        have hCL : ∀ l ∈ L, ∀ x ∈ commV L ⊓ fixV (Subgroup.zpowers d),
            l x ∈ commV L ⊓ fixV (Subgroup.zpowers d) := by
          intro l hl x hx
          refine ⟨hUL l hl x hx.1, mem_fixV_zpowers_iff.mpr ?_⟩
          rw [hgd d hdD l hl x, mem_fixV_zpowers_iff.mp hx.2]
        have hCΘ : commSub (commV L) Θ ≤ commV L ⊓ fixV (Subgroup.zpowers d) := by
          rw [hS]
          exact iSup_le fun i => le_inf (Rsub_le hUΘ) fun x hx =>
            mem_fixV_zpowers_iff.mpr (hcz i x hx)
        have hUC := commV_le_of_commSub_le hs hna hΘL hT.ne_bot hCL hCΘ
        intro u hu
        exact mem_fixV_zpowers_iff.mp (hUC hu).2
      have h3 : Nat.card ↥(D ⊓ centSub R₀) ≤ Nat.card ↥(D ⊓ centSub (commV L)) :=
        Subgroup.card_le_of_le hle
      have hpos : 0 < Nat.card ↥(D ⊓ centSub (commV L)) := Nat.card_pos
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc Nat.card (autSub D (commV L)) * Nat.card ↥(D ⊓ centSub (commV L)) = Nat.card D := e1
        _ = Nat.card (autSub D R₀) * Nat.card ↥(D ⊓ centSub R₀) := e2.symm
        _ ≤ Nat.card (autSub D R₀) * Nat.card ↥(D ⊓ centSub (commV L)) :=
            Nat.mul_le_mul_left _ h3
    have hup : rk ↥(commV L) ≤ 1 + m.natDegree * (k - 1) + rk ↥(commV L ⊓ fixV D) := by
      have h1 : Nat.card (commV L) ≤
          2 * 2 ^ (m.natDegree * (k - 1)) * Nat.card ↥(commV L ⊓ fixV D) := by
        calc Nat.card (commV L)
            ≤ e * Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D) := hcount
          _ ≤ 2 * 2 ^ (m.natDegree * (k - 1)) * Nat.card ↥(commV L ⊓ fixV D) := by
            apply Nat.mul_le_mul_right
            exact Nat.mul_le_mul he (hautU.trans hautcard)
      rw [card_eq_two_pow hV (commV L), card_eq_two_pow hV (commV L ⊓ fixV D)] at h1
      have h2 : 2 ^ rk ↥(commV L) ≤
          2 ^ (1 + m.natDegree * (k - 1) + rk ↥(commV L ⊓ fixV D)) := by
        calc 2 ^ rk ↥(commV L)
            ≤ 2 * 2 ^ (m.natDegree * (k - 1)) * 2 ^ rk ↥(commV L ⊓ fixV D) := h1
          _ = 2 ^ (1 + m.natDegree * (k - 1) + rk ↥(commV L ⊓ fixV D)) := by
            rw [pow_add, pow_add, pow_one]
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    have hk : k = 1 := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hrkS] at hrkU
      simp only [Nat.add_sub_cancel] at hup
      by_contra hne
      have hk'pos : 1 ≤ k' := by omega
      have h3 : 3 * (m.natDegree * k') ≤ c * (m.natDegree * k') := Nat.mul_le_mul_right _ hc
      have h4 : 2 * 1 ≤ m.natDegree * k' := Nat.mul_le_mul hd hk'pos
      nlinarith
    subst hk
    have hRY : R₀ ≤ commV L ⊓ fixV D := by
      have h1 : R₀ ⊓ (commV L ⊓ fixV D) = R₀ := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hRi i₀, hTi i₀, mul_one]
      exact inf_eq_left.mp h1
    have hRYall : ∀ i, Rsub Θ (Θi i) (commV L) ≤ commV L ⊓ fixV D :=
      forall_of_trans hT i₀ hRY fun i hi =>
        Rsub_le_of_le hT.w_Θ (hT.w_Θi i) (hwM _ hUL) (hwM _ hYL) hi
    rw [hS]
    exact iSup_le hRYall

end Main

end CFSG.LocalAnalysis.RankThreeUC
