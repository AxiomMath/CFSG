module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D1Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D1Pair
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitAlt6

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

private theorem sec8t84d1_trans_aux {E : Type} [Group E] [Finite E]
    {A : Subgroup (MulAut E)} (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    {E1 E2 : Subgroup E}
    (hE2 : ∀ a ∈ A, orderOf a = 5 → fixSub a = E2)
    (hsup : E1 ⊔ E2 = ⊤)
    (hcard1 : Nat.card E1 = 2 ^ 4)
    (hinv : ∀ a ∈ A, ∀ x ∈ E1, a x ∈ E1)
    (htriv : ∀ a ∈ A, ∀ x ∈ E2, a x = x) :
    ∀ v ∈ E1, v ≠ 1 → ∀ w ∈ E1, w ≠ 1 → ∃ a ∈ A, a v = w := by
  classical
  obtain ⟨e1⟩ := hA
  have hU : ∀ h : ↥A, ∀ u ∈ E1, A.subtype h u ∈ E1 :=
    fun h u hu => hinv (A.subtype h) h.2 u hu
  let ρ : ↥A →* MulAut ↥E1 := restrictAut A.subtype E1 hU
  let ψ : ↥A →* alternatingGroup (Fin 6) := e1.toMonoidHom
  have hψ : Function.Surjective ψ := e1.surjective
  have hker : ∀ g : ↥A, ψ g = 1 ↔ ρ g = 1 := by
    intro g
    constructor
    · intro hg
      have hg1 : g = 1 := e1.injective (by rw [map_one]; exact hg)
      rw [hg1, map_one]
    · intro hg
      have hval : (g : MulAut E) = 1 := by
        apply MulEquiv.ext
        intro v
        have hF : E1 ⊔ E2 ≤ fixSub (g : MulAut E) := by
          rw [sup_le_iff]
          constructor
          · intro x hx
            rw [mem_fixSub]
            have h1 := congrArg (fun φ : MulAut ↥E1 => ((φ ⟨x, hx⟩ : ↥E1) : E)) hg
            simp only [MulAut.one_apply] at h1
            dsimp only [ρ] at h1
            rw [restrictAut_apply] at h1
            exact h1
          · intro x hx
            rw [mem_fixSub]
            exact htriv g g.2 x hx
        have hv : v ∈ E1 ⊔ E2 := by rw [hsup]; exact Subgroup.mem_top v
        simpa using mem_fixSub.mp (hF hv)
      have hg1 : g = 1 := Subtype.ext hval
      rw [hg1, map_one]
  intro v hv hv1 w hw hw1
  obtain ⟨g, hg⟩ :=
    CFSG.OddStandard.HigherRank.YamadaG23.lit_alt6_transitive_group (V := ↥E1)
      (by rw [hcard1]; norm_num) ρ ψ hψ hker ⟨v, hv⟩ ⟨w, hw⟩
      (fun h => hv1 (by simpa using congrArg Subtype.val h))
      (fun h => hw1 (by simpa using congrArg Subtype.val h))
  refine ⟨g, g.2, ?_⟩
  exact congrArg Subtype.val hg

theorem sec8t84d1_lemma33 {E : Type} [Group E] [Finite E] (hc : ∀ x y : E, x * y = y * x)
    (hs : ∀ x : E, x * x = 1) (hcard : Nat.card E = 2 ^ 8) (A1 A2 : Subgroup (MulAut E))
    (hcomm : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a)
    (h1 : Nonempty (↥A1 ≃* alternatingGroup (Fin 6)))
    (h2 : Nonempty (↥A2 ≃* alternatingGroup (Fin 6))) :
    ∃ E1 E2 : Subgroup E, Sec8T84Dec33 A1 A2 E1 E2 := by
  classical
  obtain ⟨δ0, hδ0A1, hδ0⟩ := sec8t84d1_exists_order5 (A := A1) h1
  obtain ⟨γ0, hγ0A2, hγ0⟩ := sec8t84d1_exists_order5 (A := A2) h2
  have hδ05 : δ0 ^ 5 = 1 := hδ0 ▸ pow_orderOf_eq_one δ0
  obtain ⟨hinf0, hnorm1, hnorm2⟩ :=
    sec8t84d1_pair hc hs hcard h1 h2 hcomm hδ0A1 hγ0A2 hδ0 hγ0
  have hE2 : ∀ δ ∈ A1, orderOf δ = 5 → fixSub δ = fixSub δ0 := by
    intro δ hδA hδ
    have hp := sec8t84d1_pair hc hs hcard h1 h2 hcomm hδA hγ0A2 hδ hγ0
    rw [hp.2.2, ← hnorm2]
  have hE1 : ∀ γ ∈ A2, orderOf γ = 5 → fixSub γ = fixSub γ0 := by
    intro γ hγB hγ
    have hp := sec8t84d1_pair hc hs hcard h1 h2 hcomm hδ0A1 hγB hδ0 hγ
    rw [hp.2.1, ← hnorm1]
  have hcard1 : Nat.card (fixSub γ0) = 2 ^ 4 := by
    have h := sec8t84d1_card_fixSub (A := A2) (B := A1) hc hs hcard h1
      (fun a ha b hb => (hcomm b hb a ha).symm) hγ0A2 hγ0
    rw [h]; norm_num
  have hcard2 : Nat.card (fixSub δ0) = 2 ^ 4 := by
    have h := sec8t84d1_card_fixSub (A := A1) (B := A2) hc hs hcard h2 hcomm hδ0A1 hδ0
    rw [h]; norm_num
  have hsup : fixSub γ0 ⊔ fixSub δ0 = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro v
    obtain ⟨u, hu, w, hw, huw⟩ := exists_fixSub_mul_normSub hc hs hδ05 v
    rw [← hnorm1] at hw
    rw [← huw, hc u w]
    exact Subgroup.mul_mem_sup hw hu
  have hinv1 : ∀ a ∈ A1, ∀ x ∈ fixSub γ0, a x ∈ fixSub γ0 := by
    intro a ha x hx
    exact apply_mem_fixSub_of_comm (α := γ0) (β := a) (hcomm a ha γ0 hγ0A2).symm hx
  have hinv2 : ∀ b ∈ A2, ∀ x ∈ fixSub δ0, b x ∈ fixSub δ0 := by
    intro b hb x hx
    exact apply_mem_fixSub_of_comm (α := δ0) (β := b) (hcomm δ0 hδ0A1 b hb) hx
  have htriv1 : ∀ a ∈ A1, ∀ x ∈ fixSub δ0, a x = x := by
    intro a ha x hx
    have hle : A1 ≤ fixingSub (MonoidHom.id (MulAut E)) (fixSub δ0) :=
      sec8t84d1_le_of_order5 h1 (fun a ha ha5 => by
        rw [mem_fixingSub]
        intro u hu
        show a u = u
        rw [← mem_fixSub, hE2 a ha ha5]
        exact hu)
    simpa using (mem_fixingSub.1 (hle ha)) x hx
  have htriv2 : ∀ b ∈ A2, ∀ x ∈ fixSub γ0, b x = x := by
    intro b hb x hx
    have hle : A2 ≤ fixingSub (MonoidHom.id (MulAut E)) (fixSub γ0) :=
      sec8t84d1_le_of_order5 h2 (fun b hb hb5 => by
        rw [mem_fixingSub]
        intro u hu
        show b u = u
        rw [← mem_fixSub, hE1 b hb hb5]
        exact hu)
    simpa using (mem_fixingSub.1 (hle hb)) x hx
  have hfix1 : ∀ x : E, (∀ a ∈ A1, a x = x) → x ∈ fixSub δ0 := by
    intro x hx
    rw [mem_fixSub]
    exact hx δ0 hδ0A1
  have hfix2 : ∀ x : E, (∀ b ∈ A2, b x = x) → x ∈ fixSub γ0 := by
    intro x hx
    rw [mem_fixSub]
    exact hx γ0 hγ0A2
  have hfpf1 : ∀ a ∈ A1, orderOf a = 5 → ∀ x ∈ fixSub γ0, a x = x → x = 1 := by
    intro a ha ha5 x hx hax
    have hx2 : x ∈ fixSub a := by rw [mem_fixSub]; exact hax
    rw [hE2 a ha ha5] at hx2
    have hx' : x ∈ fixSub γ0 ⊓ fixSub δ0 := ⟨hx, hx2⟩
    rw [inf_comm, hinf0] at hx'
    exact Subgroup.mem_bot.1 hx'
  have hfpf2 : ∀ b ∈ A2, orderOf b = 5 → ∀ x ∈ fixSub δ0, b x = x → x = 1 := by
    intro b hb hb5 x hx hbx
    have hx2 : x ∈ fixSub b := by rw [mem_fixSub]; exact hbx
    rw [hE1 b hb hb5] at hx2
    have hx' : x ∈ fixSub δ0 ⊓ fixSub γ0 := ⟨hx, hx2⟩
    rw [hinf0] at hx'
    exact Subgroup.mem_bot.1 hx'
  have htrans1 := sec8t84d1_trans_aux h1 hE2 hsup hcard1 hinv1 htriv1
  have htrans2 := sec8t84d1_trans_aux h2 hE1 (by rw [sup_comm]; exact hsup) hcard2 hinv2 htriv2
  exact ⟨fixSub γ0, fixSub δ0, hcard1, hcard2, by rw [inf_comm]; exact hinf0, hsup,
    hinv1, hinv2, htriv1, htriv2, hfix1, hfix2, hfpf1, hfpf2, htrans1, htrans2⟩

end CFSG.OddStandard.SmallF3.Omega
