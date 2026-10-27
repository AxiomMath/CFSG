module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Irr
public import CFSG.CGT.PushingUpLit.CGT6.Diag.SelSchur

public section

namespace CFSG.CGT.PushingUpLit.CGT6

namespace Diag.Sel

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Stab

variable {V : Type} [CommGroup V]

@[expose] def stabSub (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ w ∈ W, g w ∈ W ∧ g⁻¹ w ∈ W}
  one_mem' := fun w hw => ⟨hw, hw⟩
  mul_mem' := by
    intro a b ha hb w hw
    exact ⟨(ha _ (hb w hw).1).1, (hb _ (ha w hw).2).2⟩
  inv_mem' := by
    intro a ha w hw
    exact ⟨(ha w hw).2, by simpa using (ha w hw).1⟩

theorem mem_stabSub_of_le [Finite V] {W : Subgroup V} {g : MulAut V} (h : ∀ w ∈ W, g w ∈ W) :
    g ∈ stabSub W := by
  have hle : diagImg g W ≤ W := fun _ ⟨w, hw, e⟩ => e ▸ h w hw
  have hcard : Nat.card ↥W ≤ Nat.card ↥(diagImg g W) := by
    rw [diagImg, Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
  have heq : diagImg g W = W := Subgroup.eq_of_le_of_card_ge hle hcard
  refine fun w hw => ⟨h w hw, ?_⟩
  have : w ∈ diagImg g W := by
    rw [heq]
    exact hw
  obtain ⟨w', hw', rfl⟩ := this
  simpa using hw'

theorem ginv_sup {K₁ K₂ : Subgroup (MulAut V)} {A : Subgroup V} (h₁ : GInv K₁ A)
    (h₂ : GInv K₂ A) : GInv (K₁ ⊔ K₂) A := by
  have hK₁ : K₁ ≤ stabSub A := fun k hk a ha => ⟨h₁ k hk a ha, h₁ k⁻¹ (K₁.inv_mem hk) a ha⟩
  have hK₂ : K₂ ≤ stabSub A := fun k hk a ha => ⟨h₂ k hk a ha, h₂ k⁻¹ (K₂.inv_mem hk) a ha⟩
  exact fun g hg a ha => ((sup_le hK₁ hK₂) hg a ha).1

theorem ne_bot_of_isQuasisimple {K : Subgroup (MulAut V)} (hK : CFSG.Open.IsQuasisimple ↥K) :
    K ≠ ⊥ := by
  intro hbot
  have hnt : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hK.2.toNontrivial
  have hone : ∀ k : ↥K, k = 1 := fun k => Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ k.2))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hone k₁, hone k₂])

end Stab

section Pair

variable {V : Type} [CommGroup V] [Finite V] {K K' Y : Subgroup (MulAut V)} {t : MulAut V}

omit [Finite V] in
theorem mem_K'_iff (h : DiagPre K K' Y t) {x : MulAut V} :
    x ∈ K' ↔ ∃ k ∈ K, x = t * k * t⁻¹ := by
  rw [h.Kconj]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [MulAut.conj_apply]⟩

omit [Finite V] in
theorem K'_ne_bot (h : DiagPre K K' Y t) : K' ≠ ⊥ := by
  intro hbot
  apply ne_bot_of_isQuasisimple h.quasi
  rw [h.Kconj] at hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t).injective).mp hbot

omit [Finite V] in
theorem K_perfect (h : DiagPre K K' Y t) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.mp ⟨h.quasi.1⟩

omit [Finite V] in
theorem K'_perfect (h : DiagPre K K' Y t) : ⁅K', K'⁆ = K' := by
  rw [h.Kconj, ← Subgroup.map_commutator, K_perfect h]

end Pair

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem diagImg_mul (a b : MulAut V) (W : Subgroup V) :
    diagImg (a * b) W = diagImg a (diagImg b W) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨b w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem K'_stab_false {K K' Y : Subgroup (MulAut V)} {t : MulAut V} (h : DiagPair K K' Y t)
    {W : Subgroup V} (hW : DiagMinInv K W) (hstab : K' ≤ stabSub W) : False := by
  have hKW : GInv K W := hW.2.1
  have hK'W : GInv K' W := fun a ha w hw => (hstab ha w hw).1
  have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW.1
  let ρ : ↥K →* MulAut ↥W := resG K W hKW
  have hsimple : ∀ B : Subgroup ↥W, (∀ g : ↥K, ∀ b ∈ B, ρ g b ∈ B) → B = ⊥ ∨ B = ⊤ := by
    intro B hB
    have hinv : GInv K (B.map W.subtype) := by
      rintro k hk _ ⟨b, hb, rfl⟩
      exact ⟨ρ ⟨k, hk⟩ b, hB ⟨k, hk⟩ b hb, rfl⟩
    rcases hW.2.2 _ hinv (by rintro _ ⟨b, -, rfl⟩; exact b.2) with h0 | h0
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp h0
    · right
      apply Subgroup.map_injective W.subtype_injective
      rw [h0, Subgroup.map_top, Subgroup.range_subtype]
  have hcommW : ∀ a ∈ K', ∀ b ∈ K', ∀ w ∈ W, a (b w) = b (a w) := by
    intro a ha b hb w hw
    have hφ : ∀ (g : ↥K) (u : ↥W), (resG K' W hK'W ⟨a, ha⟩).toMonoidHom (ρ g u) =
        ρ g ((resG K' W hK'W ⟨a, ha⟩).toMonoidHom u) := by
      intro g u
      apply Subtype.ext
      show a ((g : MulAut V) (u : V)) = (g : MulAut V) (a (u : V))
      have h1 := congrArg (fun φ : MulAut V => φ (u : V)) (h.comm g g.2 a ha)
      simpa [MulAut.mul_apply] using h1.symm
    have hψ : ∀ (g : ↥K) (u : ↥W), (resG K' W hK'W ⟨b, hb⟩).toMonoidHom (ρ g u) =
        ρ g ((resG K' W hK'W ⟨b, hb⟩).toMonoidHom u) := by
      intro g u
      apply Subtype.ext
      show b ((g : MulAut V) (u : V)) = (g : MulAut V) (b (u : V))
      have h1 := congrArg (fun φ : MulAut V => φ (u : V)) (h.comm g g.2 b hb)
      simpa [MulAut.mul_apply] using h1.symm
    have := endo_comm_of_simple ρ hsimple _ _ hφ hψ ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hcomm : ⁅K', K'⁆ ≤ fixW W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb w hw
    have hw₁ : b⁻¹ w ∈ W := (hstab hb w hw).2
    have hw₂ : a⁻¹ (b⁻¹ w) ∈ W := (hstab ha _ hw₁).2
    have h1 := hcommW a ha b hb _ hw₂
    show (a * b * a⁻¹ * b⁻¹) w = w
    simp only [MulAut.mul_apply]
    rw [h1]
    simp
  rw [K'_perfect h.toDiagPre] at hcomm
  have hWfix : W ≤ fixV K' := fun w hw a ha => hcomm ha w hw
  have hinv : GInv (K ⊔ K') (fixV K') := by
    refine ginv_sup (fun k hk v hv a ha => ?_) (fun g hg v hv a ha => ?_)
    · have h1 : a * k = k * a := (h.comm k hk a ha).symm
      have := congrArg (fun φ : MulAut V => φ v) h1
      simp only [MulAut.mul_apply] at this
      rw [this, (mem_fixV.mp hv) a ha]
    · rw [(mem_fixV.mp hv) g hg]
      exact (mem_fixV.mp hv) a ha
  rcases h.irr (fixV K') hinv with h0 | h0
  · exact hW.1 (le_bot_iff.mp (h0 ▸ hWfix))
  · apply K'_ne_bot h.toDiagPre
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    ext v
    have : v ∈ fixV K' := h0 ▸ Subgroup.mem_top v
    exact (mem_fixV.mp this) a ha

theorem sel_one {K K' Y : Subgroup (MulAut V)} {t : MulAut V} (h : DiagPair K K' Y t)
    {W : Subgroup V} (hW : DiagMinInv K W) (S : Set (MulAut V)) (_hSY : S ⊆ (Y : Set (MulAut V)))
    (hcl : Subgroup.closure S = Y) : ∃ y ∈ S, ∃ w ∈ W, y w ∉ W := by
  by_contra hno
  push Not at hno
  have hSstab : S ⊆ (stabSub W : Set (MulAut V)) := fun y hy => mem_stabSub_of_le (hno y hy)
  have hYstab : Y ≤ stabSub W := by
    rw [← hcl]
    exact (Subgroup.closure_le (stabSub W)).mpr hSstab
  have hKstab : K ≤ stabSub W := fun k hk w hw =>
    ⟨hW.2.1 k hk w hw, hW.2.1 k⁻¹ (K.inv_mem hk) w hw⟩
  refine K'_stab_false h hW (fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := (mem_K'_iff h.toDiagPre).mp hx
  have hy : k * (t * k * t⁻¹) ∈ Y := (h.Y_mem _).mpr ⟨k, hk, rfl⟩
  have := (stabSub W).mul_mem ((stabSub W).inv_mem (hKstab hk)) (hYstab hy)
  simpa using this

theorem sel_two {K K' Y : Subgroup (MulAut V)} {t : MulAut V} (h : DiagPair K K' Y t)
    {W : Subgroup V} (hW : DiagMinInv K W) {y : MulAut V} (hy : y ∈ Y)
    (hmove : ∃ w ∈ W, y w ∉ W) :
    W ⊓ diagImg y W = ⊥ ∧ Nat.card ↥W ≤ Nat.card ↥(commV (Subgroup.zpowers y)) := by
  obtain ⟨k, hk, hyk⟩ := (h.Y_mem y).mp hy
  have hkt : t * k * t⁻¹ ∈ K' := (mem_K'_iff h.toDiagPre).mpr ⟨k, hk, rfl⟩
  have hinvKt : GInv K (diagImg (t * k * t⁻¹) W) := by
    rintro k' hk' _ ⟨w, hw, rfl⟩
    refine ⟨k' w, hW.2.1 k' hk' w hw, ?_⟩
    have h1 := congrArg (fun φ : MulAut V => φ w) (h.comm k' hk' _ hkt)
    simpa [MulAut.mul_apply] using h1.symm
  have hyW : diagImg y W = diagImg (t * k * t⁻¹) W := by
    rw [hyk, diagImg_mul]
    exact Diag.Irr.diagImg_eq_of_inv hinvKt hk
  have hinf : W ⊓ diagImg y W = ⊥ := by
    have hinv : GInv K (W ⊓ diagImg y W) := fun k' hk' a ha =>
      ⟨hW.2.1 k' hk' a ha.1, by rw [hyW]; exact hinvKt k' hk' a (hyW ▸ ha.2)⟩
    rcases hW.2.2 _ hinv inf_le_left with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨w₀, hw₀, hyw₀⟩ := hmove
      have hle : W ≤ diagImg y W := fun w hw => by
        have : w ∈ W ⊓ diagImg y W := by
          rw [h0]
          exact hw
        exact this.2
      have hcard : Nat.card ↥(diagImg y W) ≤ Nat.card ↥W := by
        rw [diagImg, Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective]
      have heq : W = diagImg y W := Subgroup.eq_of_le_of_card_ge hle hcard
      exact hyw₀ (heq ▸ ⟨w₀, hw₀, rfl⟩)
  refine ⟨hinf, ?_⟩
  let ε : ↥W →* V := MonoidHom.mk' (fun w => (w : V) * (y (w : V))⁻¹) (fun a b => by
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    ac_rfl)
  have hmem : ∀ w : ↥W, ε w ∈ commV (Subgroup.zpowers y) := by
    intro w
    have h1 : y (w : V) * (w : V)⁻¹ ∈ commV (Subgroup.zpowers y) :=
      Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, w, rfl⟩
    have h2 := Subgroup.inv_mem _ h1
    have h3 : ε w = (y (w : V) * (w : V)⁻¹)⁻¹ := by
      show (w : V) * (y (w : V))⁻¹ = (y (w : V) * (w : V)⁻¹)⁻¹
      simp [mul_comm]
    rw [h3]
    exact h2
  let ε' : ↥W →* ↥(commV (Subgroup.zpowers y)) := ε.codRestrict _ hmem
  have hinj : Function.Injective ε' := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : ε w = 1 := congrArg Subtype.val hw
    have h2 : (w : V) = y (w : V) := by
      have : (w : V) * (y (w : V))⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp this
    have h3 : (w : V) ∈ W ⊓ diagImg y W := ⟨w.2, ⟨(w : V), w.2, h2.symm⟩⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  exact Nat.card_le_card_of_injective ε' hinj

end Main

end Diag.Sel

theorem diagModSel_holds : DiagMod_sel := by
  intro V _ _ hV K K' Y t h W hW
  exact ⟨fun S hSY hcl => Diag.Sel.sel_one h hW S hSY hcl,
    fun y hy hmove => Diag.Sel.sel_two h hW hy hmove⟩

end CFSG.CGT.PushingUpLit.CGT6
