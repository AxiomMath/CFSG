module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W4
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K9
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W3

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

section W5

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem mem_Zzs_cases (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {c : ↥d.s56V} (hc : c ∈ Zzs d z₀) :
    c = 1 ∨ c = zV h49 hd ∨ c = z0V hz ∨ c = zV h49 hd * z0V hz := by
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzz₀ : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have hmem : (c : G) ∈ zpowers d.z ⊔ zpowers z₀ := hc
  rcases (CFSG.LocalAnalysis.EvenBN.Tits.N.mem_sup_zpowers_iff hzz hz₀z₀ hzz₀ _).1 hmem with
    h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem star_x5_zpow_fixes_Zzs (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h10 : Node10 d z₀) (n : ℤ) {c : ↥d.s56V} (hc : c ∈ Zzs d z₀) :
    (star d d.x₅ ^ n) c = c := by
  have hx : star d d.x₅ c = c :=
    (star_x5_fix_iff h49 hd hz h10 c).2 (mem_Zzs_cases h49 hd hz h10 hc)
  have hmem : star d d.x₅ ∈ MulAction.stabilizer (MulAut ↥d.s56V) c := hx
  exact Subgroup.zpow_mem _ hmem n

theorem Ws_eq_W1s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    Ws d = W1s hz := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  have hxK : star d d.x₅ ∈ Ks d := star_x5_mem_Ks h49 hd
  have hxX : star d d.x₅ ∈ img d (Xg d) := by
    rw [img_Xg h49 hd]
    exact mem_zpowers _
  have hxP := star_x5_normalizes_W1s h49 hd hz h09 h10 h17s h17 h18
  have hcommA := (W1s_elemAb h49 hd hz h09 h10 h17s h17 h18).1
  show ⁅W0s d, img d (Xg d)⁆ = W1s hz
  apply le_antisymm
  ·
    refine Subgroup.commutator_le.2 fun w hw y hy => ?_
    rw [img_Xg h49 hd] at hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hyK : star d d.x₅ ^ n ∈ Ks d := zpow_mem hxK n
    rw [commutatorElement_def]
    refine (mem_W1s_iff hz).2 ⟨?_, ?_⟩
    · have e : w * star d d.x₅ ^ n * w⁻¹ * (star d d.x₅ ^ n)⁻¹ =
          w * ((star d d.x₅ ^ n) * w⁻¹ * (star d d.x₅ ^ n)⁻¹) := by group
      rw [e]
      exact mul_mem hw (hWst _ hyK w⁻¹ (inv_mem hw))
    · have hz0 : z0V hz ∈ Zzs d z₀ := mem_sup_right (mem_zpowers z₀)
      have h1 : (star d d.x₅ ^ n)⁻¹ (z0V hz) = z0V hz := by
        rw [← zpow_neg]
        exact star_x5_zpow_fixes_Zzs h49 hd hz h10 (-n) hz0
      have h2 : w⁻¹ (z0V hz) ∈ Zzs d z₀ :=
        (Ks_Zzs_forward h49 hd hz h10 h17 h18 (inv_mem (hWK hw)) (z0V hz) hz0)
      show w ((star d d.x₅ ^ n) (w⁻¹ ((star d d.x₅ ^ n)⁻¹ (z0V hz)))) = z0V hz
      rw [h1, star_x5_zpow_fixes_Zzs h49 hd hz h10 n h2]
      simp
  ·
    let φ : ↥(W1s hz) →* ↥(W1s hz) :=
      { toFun := fun a => ⟨star d d.x₅ * a * (star d d.x₅)⁻¹ * a⁻¹,
          mul_mem (hxP a a.2) (inv_mem a.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          have hc : (a : MulAut ↥d.s56V)⁻¹ *
              (star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹) =
              (star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹) *
                (a : MulAut ↥d.s56V)⁻¹ :=
            hcommA _ (inv_mem a.2) _ (mul_mem (hxP b b.2) (inv_mem b.2))
          show star d d.x₅ * ((a : MulAut ↥d.s56V) * b) * (star d d.x₅)⁻¹ *
              ((a : MulAut ↥d.s56V) * b)⁻¹ =
            (star d d.x₅ * a * (star d d.x₅)⁻¹ * (a : MulAut ↥d.s56V)⁻¹) *
              (star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹)
          calc star d d.x₅ * ((a : MulAut ↥d.s56V) * b) * (star d d.x₅)⁻¹ *
                ((a : MulAut ↥d.s56V) * b)⁻¹
              = star d d.x₅ * a * (star d d.x₅)⁻¹ *
                  ((star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹) *
                    (a : MulAut ↥d.s56V)⁻¹) := by group
            _ = star d d.x₅ * a * (star d d.x₅)⁻¹ *
                  ((a : MulAut ↥d.s56V)⁻¹ *
                    (star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹)) := by rw [hc]
            _ = (star d d.x₅ * a * (star d d.x₅)⁻¹ * (a : MulAut ↥d.s56V)⁻¹) *
                  (star d d.x₅ * b * (star d d.x₅)⁻¹ * (b : MulAut ↥d.s56V)⁻¹) := by group) }
    have hinj : Function.Injective φ := by
      refine (injective_iff_map_eq_one φ).2 fun a ha => ?_
      have h1 : star d d.x₅ * (a : MulAut ↥d.s56V) * (star d d.x₅)⁻¹ * (a : MulAut ↥d.s56V)⁻¹ = 1 :=
        congrArg Subtype.val ha
      have h2 := mul_inv_eq_one.1 h1
      have h3 : star d d.x₅ * (a : MulAut ↥d.s56V) = (a : MulAut ↥d.s56V) * star d d.x₅ := by
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      exact Subtype.ext (W1s_centralizer_x h49 hd hz h09 h10 h17s h17 h18 a.2 h3)
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro b hb
    obtain ⟨a, ha⟩ := hsurj ⟨b, hb⟩
    have h1 : star d d.x₅ * (a : MulAut ↥d.s56V) * (star d d.x₅)⁻¹ * (a : MulAut ↥d.s56V)⁻¹ = b :=
      congrArg Subtype.val ha
    have hcomm : ⁅(a : MulAut ↥d.s56V), star d d.x₅⁆ ∈ ⁅W0s d, img d (Xg d)⁆ :=
      Subgroup.commutator_mem_commutator (W1s_le_W0s hz a.2) hxX
    have e : b = (⁅(a : MulAut ↥d.s56V), star d d.x₅⁆)⁻¹ := by
      rw [← h1, commutatorElement_def]
      group
    rw [e]
    exact inv_mem hcomm

theorem img_Wg_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    img d (Wg d z₀) = W1s hz := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  apply le_antisymm
  · intro k hk
    obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hk
    obtain ⟨hgW, hgz⟩ := Subgroup.mem_inf.1 hg
    have hgW' := (mem_preIn_iff d.s56V (W0s d)).1 hgW
    refine (mem_W1s_iff hz).2 ⟨hgW'.2, ?_⟩
    exact (actFun_fixes_iff d.s56V hgN (z0V hz)).2 (mem_centralizer_iff.1 hgz z₀ rfl).symm
  · intro w hw
    obtain ⟨hwW, hwz⟩ := (mem_W1s_iff hz).1 hw
    obtain ⟨g, hg, hgw⟩ := exists_star_of_mem_Ks (hWK hwW)
    have hgN : g ∈ normalizer (d.s56V : Set G) := hg
    have hgW : g ∈ Wg d z₀ := by
      refine Subgroup.mem_inf.2 ⟨(mem_preIn_iff d.s56V (W0s d)).2 ⟨hgN, ?_⟩,
        mem_centralizer_iff.2 fun h hh => ?_⟩
      · rw [← star_eq, hgw]
        exact hwW
      · rw [Set.mem_singleton_iff.1 hh]
        have := (actFun_fixes_iff d.s56V hgN (z0V hz)).1 (by rw [← star_eq, hgw]; exact hwz)
        exact this.symm
    have := actFun_mem_imgIn (S := d.s56V) hgW hgN
    rw [← star_eq, hgw] at this
    exact this

theorem node19_conj5 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    img d (Wg d z₀) = Ws d ∧ IsElemAbQuot (Ws d) (Us d) 4 ∧ IsElemAbelian 2 (Ws d) ∧
      Nat.card (Ws d) = 2 ^ 8 := by
  have hWs := Ws_eq_W1s h49 hd hz h09 h10 h17s h17 h18
  obtain ⟨hcomm, hsq⟩ := W1s_elemAb h49 hd hz h09 h10 h17s h17 h18
  have hcard := card_W1s h49 hd hz h09 h10 h17s h17 h18
  have hU16 : Nat.card ↥(Us d) = 16 := h17s.2.1
  have hUW := Us_le_W1s h49 hd hz h09 h10 h17s h17 h18
  rw [hWs, img_Wg_eq h49 hd hz h09 h10 h17s h17 h18]
  refine ⟨rfl, ?_, ?_, by rw [hcard]; norm_num⟩
  · refine isElemAbQuot_of_comm_sq hUW (fun k hk => by rw [hsq k hk]; exact one_mem _)
      (fun a ha b hb => ?_) ?_
    · have : a * b * a⁻¹ * b⁻¹ = 1 := by rw [hcomm a ha b hb]; group
      rw [this]
      exact one_mem _
    · have h := Subgroup.relIndex_mul_card (H := Us d) (K := W1s hz)
      rw [inf_eq_left.2 hUW, hU16, hcard] at h
      omega
  · refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun w hw => ?_⟩
    rw [pow_two]
    exact hsq w hw

end W5

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
