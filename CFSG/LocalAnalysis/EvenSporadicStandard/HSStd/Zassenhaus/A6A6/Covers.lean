module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.CoversHalf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

theorem nonempty_config {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (e : egaLayer (G ⧸ fusionOddCore G) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (d : Decomp ρ e) : Nonempty (Config ρ) := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hNodd := odd_card_fusionOddCore G
  have hE : Nat.card (egaLayer (G ⧸ fusionOddCore G)) = 129600 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_alternatingGroup_six]
  have hN5 : ¬ 5 ∣ Nat.card (fusionOddCore G) := by
    intro h5
    have hgl := CFSG.EvenSporadicStandard.M22Std.card_dvd_gl8 hc hs hV ρ hρ
    have h1 : 129600 ∣ Nat.card (G ⧸ fusionOddCore G) := by
      rw [← hE]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fusionOddCore G)
    have h3 : 129600 * 5 ∣ Nat.card G := by
      rw [h2]
      exact mul_dvd_mul h1 h5
    have h4 := h3.trans hgl
    revert h4
    unfold CFSG.EvenSporadicStandard.M22Std.gl8
    norm_num
  obtain ⟨ι, hι⟩ : ∃ ι : alternatingGroup (Fin 6) × alternatingGroup (Fin 6) →*
      G ⧸ fusionOddCore G, ∀ x, ι x = ((e.symm x : egaLayer (G ⧸ fusionOddCore G)) :
        G ⧸ fusionOddCore G) :=
    ⟨(egaLayer (G ⧸ fusionOddCore G)).subtype.comp e.symm.toMonoidHom, fun _ => rfl⟩
  have hιinj : Function.Injective ι := fun x y h =>
    e.symm.injective (Subtype.ext ((hι x).symm.trans (h.trans (hι y))))
  have hperf : commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : Subgroup (G ⧸ fusionOddCore G),
      Y₁ = (ι.comp (MonoidHom.inl _ _)).range := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : Subgroup (G ⧸ fusionOddCore G),
      Y₂ = (ι.comp (MonoidHom.inr _ _)).range := ⟨_, rfl⟩
  have hinj1 : Function.Injective (ι.comp (MonoidHom.inl (alternatingGroup (Fin 6))
      (alternatingGroup (Fin 6)))) := hιinj.comp (fun x y h => congrArg Prod.fst h)
  have hinj2 : Function.Injective (ι.comp (MonoidHom.inr (alternatingGroup (Fin 6))
      (alternatingGroup (Fin 6)))) := hιinj.comp (fun x y h => congrArg Prod.snd h)
  have hY1perf : ⁅Y₁, Y₁⁆ = Y₁ := by rw [hY₁]; exact commutator_range_eq_self hperf _
  have hY2perf : ⁅Y₂, Y₂⁆ = Y₂ := by rw [hY₂]; exact commutator_range_eq_self hperf _
  have hY1card : Nat.card Y₁ = 360 := by
    rw [hY₁, Nat.card_congr (MonoidHom.ofInjective hinj1).toEquiv.symm]
    exact card_alternatingGroup_six
  have hY2card : Nat.card Y₂ = 360 := by
    rw [hY₂, Nat.card_congr (MonoidHom.ofInjective hinj2).toEquiv.symm]
    exact card_alternatingGroup_six
  have hmka : QuotientGroup.mk' (fusionOddCore G) d.a = ι (c5, 1) := d.mk_a.trans (hι _).symm
  have hmkb : QuotientGroup.mk' (fusionOddCore G) d.b = ι (1, c5) := d.mk_b.trans (hι _).symm
  have hY1comm : ∀ y ∈ Y₁, y * QuotientGroup.mk' (fusionOddCore G) d.b =
      QuotientGroup.mk' (fusionOddCore G) d.b * y := by
    intro y hy
    rw [hY₁] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [hmkb]
    change ι (g, 1) * ι (1, c5) = ι (1, c5) * ι (g, 1)
    rw [← map_mul, ← map_mul]
    congr 1
  have hY2comm : ∀ y ∈ Y₂, y * QuotientGroup.mk' (fusionOddCore G) d.a =
      QuotientGroup.mk' (fusionOddCore G) d.a * y := by
    intro y hy
    rw [hY₂] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [hmka]
    change ι (1, g) * ι (c5, 1) = ι (c5, 1) * ι (1, g)
    rw [← map_mul, ← map_mul]
    congr 1
  have hYsup : Y₁ ⊔ Y₂ = egaLayer (G ⧸ fusionOddCore G) := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rw [hY₁]
      rintro _ ⟨g, rfl⟩
      exact (hι (g, 1)) ▸ (e.symm (g, 1)).2
    · rw [hY₂]
      rintro _ ⟨g, rfl⟩
      exact (hι (1, g)) ▸ (e.symm (1, g)).2
    · intro z hz
      have hw : ι (e ⟨z, hz⟩) = z := by
        rw [hι, MulEquiv.symm_apply_apply]
      have hmul : (e ⟨z, hz⟩) = ((e ⟨z, hz⟩).1, 1) * (1, (e ⟨z, hz⟩).2) := by
        ext <;> simp
      rw [← hw, hmul, map_mul]
      refine mul_mem_sup ?_ ?_
      · rw [hY₁]
        exact ⟨_, rfl⟩
      · rw [hY₂]
        exact ⟨_, rfl⟩
  have hinfU : d.U₂ ⊓ d.U₁ = ⊥ := by rw [inf_comm]; exact d.inf_U
  obtain ⟨D, hDY, hDinf, hDtriv, hDmem, hDfix⟩ := exists_cover_half hc hs hV ρ hρ hNodd hN5
    d.orderOf_a d.card_U₂ d.card_U₁ hinfU d.fix_a d.mem_U₁ hY2perf hY2card hY2comm
  obtain ⟨C, hCY, hCinf, hCtriv, hCmem, hCfix⟩ := exists_cover_half hc hs hV ρ hρ hNodd hN5
    d.orderOf_b d.card_U₁ d.card_U₂ d.inf_U d.fix_b d.mem_U₂ hY1perf hY1card hY1comm
  obtain ⟨eC0⟩ := nonempty_mulEquiv_map (QuotientGroup.mk' (fusionOddCore G)) (D := C)
    (by rw [QuotientGroup.ker_mk']; exact hCinf)
  obtain ⟨eD0⟩ := nonempty_mulEquiv_map (QuotientGroup.mk' (fusionOddCore G)) (D := D)
    (by rw [QuotientGroup.ker_mk']; exact hDinf)
  let eC : C ≃* alternatingGroup (Fin 6) :=
    eC0.trans (((MulEquiv.subgroupCongr (hCY.trans hY₁)).trans
      (MonoidHom.ofInjective hinj1).symm))
  let eD : D ≃* alternatingGroup (Fin 6) :=
    eD0.trans (((MulEquiv.subgroupCongr (hDY.trans hY₂)).trans
      (MonoidHom.ofInjective hinj2).symm))
  have hdec := exists_mul_of_card_sixteen hc hV d.card_U₁ d.card_U₂ d.inf_U
  have hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    apply hρ
    rw [map_mul, map_mul]
    ext v
    obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := hdec v
    simp only [MulAut.mul_apply, map_mul, hDtriv y hy u₁ h₁, hCtriv x hx u₂ h₂,
      hCtriv x hx (ρ y u₂) (hDmem y hy u₂ h₂), hDtriv y hy (ρ x u₁) (hCmem x hx u₁ h₁)]
  have hinfCD : C ⊓ D = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun x hx =>
      eq_one_of_fix_both hρ hdec (hDtriv x hx.2) (hCtriv x hx.1)
  have hcardX : Nat.card ↥(C ⊔ D) = 129600 := by
    rw [card_sup_of_comm hcomm hinfCD, Nat.card_congr eC.toEquiv, Nat.card_congr eD.toEquiv,
      card_alternatingGroup_six]
  have hmapX : (C ⊔ D).map (QuotientGroup.mk' (fusionOddCore G)) =
      egaLayer (G ⧸ fusionOddCore G) := by
    rw [Subgroup.map_sup, hCY, hDY, hYsup]
  have hinfodd : (C ⊔ D) ⊓ fusionOddCore G = ⊥ := by
    have h := card_eq_card_map_mul_card_inf (QuotientGroup.mk' (fusionOddCore G)) (C ⊔ D)
    rw [hmapX, hE, hcardX, QuotientGroup.ker_mk'] at h
    exact Subgroup.card_eq_one.1 (by omega)
  exact ⟨⟨C, D, d.U₁, d.U₂, eC, eD, d.card_U₁, d.card_U₂, d.inf_U, hCmem, hDmem, hCfix, hDfix,
    hcomm, hinfCD, hinfodd, hmapX⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
