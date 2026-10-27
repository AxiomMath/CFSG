module

public import CFSG.GF2Type.SmithTypeE.E7.KcGeom
public import CFSG.GF2Type.SmithTypeE.E7.IdGramRel
public import Certificates.Certificate38935

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

section Cert

theorem q12_of_mem_lineSet {k : Fin 365211} {x : V12} (hx : x ∈ lineSet k.val) : q12 x = 0 := by
  obtain ⟨hq1, hq2, hb⟩ := tsPair_linePair k.2
  simp only [lineSet, lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hq1
  · exact hq2
  · rw [q12_add, hq1, hq2, hb]
    decide

theorem tvP_mem_UFix_iff (Y : Submodule (ZMod 2) V12) (k : Fin 365211) :
    (⟨tvP k, tvP_mem k⟩ : TD6) ∈ UFix Y ↔ ∀ x ∈ lineSet k.val, ∀ y ∈ Y, B12 x y = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, u = dec12 (linePair k.val).1 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = dec12 (linePair k.val).2 := ⟨_, rfl⟩
  have hts : TsPair u w := by
    rw [hu, hw]
    exact tsPair_linePair k.2
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact (linePair_ne k.2).1
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact (linePair_ne k.2).2.1
  have huw : u ≠ w := by
    rw [hu, hw]
    exact (linePair_ne k.2).2.2
  have hline : lineSet k.val = {u, w, u + w} := by rw [hu, hw]; rfl
  have hsig : sig (⟨tvP k, tvP_mem k⟩ : TD6) = siegelEquiv u w := by
    rw [sig_tvP, hu, hw]
    rfl
  rw [mem_UFix, hsig, hline]
  have hfix : ∀ y : V12, siegelEquiv u w y = y ↔ B12 y w = 0 ∧ B12 y u = 0 := by
    intro y
    rw [siegelEquiv_apply hts]
    constructor
    · intro h
      have h1 : B12 y w • u + B12 y u • w = 0 := by
        have h2 : y + B12 y w • u + B12 y u • w = y + 0 := by rw [add_zero]; exact h
        rw [add_assoc] at h2
        exact add_left_cancel h2
      have hc : ∀ a b : ZMod 2, a = 0 ∨ a = 1 → b = 0 ∨ b = 1 → True := fun _ _ _ _ => trivial
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (B12 y w) with ha | ha <;>
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (B12 y u) with hb | hb
      · exact ⟨ha, hb⟩
      · rw [ha, hb, zero_smul, one_smul, zero_add] at h1
        exact absurd h1 hw0
      · rw [ha, hb, zero_smul, one_smul, add_zero] at h1
        exact absurd h1 hu0
      · rw [ha, hb, one_smul, one_smul] at h1
        have : u = w := by
          have h3 : u + w + w = 0 + w := by rw [h1]
          rw [add_assoc, V12_add_self_eq_zero, add_zero, zero_add] at h3
          exact h3
        exact absurd this huw
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      simp
  constructor
  · intro h x hx y hy
    have := (hfix y).mp (h y hy)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [B12_comm]; exact this.2
    · rw [B12_comm]; exact this.1
    · rw [B12_add_left, B12_comm u y, B12_comm w y, this.2, this.1, add_zero]
  · intro h y hy
    refine (hfix y).mpr ⟨?_, ?_⟩
    · rw [B12_comm]
      exact h w (by simp) y hy
    · rw [B12_comm]
      exact h u (by simp) y hy

theorem tvP_mem_UFix_Cc_iff (k : Fin 365211) :
    (⟨tvP k, tvP_mem k⟩ : TD6) ∈ UFix Cc ↔ ∀ x ∈ lineSet k.val, x ∈ Cc ∧ q12 x = 0 := by
  rw [tvP_mem_UFix_iff]
  constructor
  · intro h x hx
    exact ⟨Cc_perp x fun y hy => h x hx y hy, q12_of_mem_lineSet hx⟩
  · intro h x hx y hy
    exact Cc_isotropic (h x hx).1 hy

theorem mem_map_sig {c : TD6} {Y : Submodule (ZMod 2) V12} {z : V12} :
    z ∈ Y.map (sig c).toLinearMap ↔ (sig c).symm z ∈ Y :=
  Submodule.mem_map_equiv Y

theorem B12_sig_symm_left (c : TD6) (x y : V12) :
    B12 ((sig c).symm x) y = B12 x (sig c y) := by
  have h := B12_of_isometry (iso_sig c) ((sig c).symm x) y
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem q12_sig_symm (c : TD6) (x : V12) : q12 ((sig c).symm x) = q12 x := by
  have h := iso_sig c ((sig c).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem perp_map_Cc (c : TD6) (x : V12) :
    (∀ y ∈ Cc.map (sig c).toLinearMap, B12 x y = 0) ↔ x ∈ Cc.map (sig c).toLinearMap := by
  rw [mem_map_sig]
  constructor
  · intro h
    refine Cc_perp _ fun y hy => ?_
    rw [B12_sig_symm_left]
    exact h _ (Submodule.mem_map_of_mem hy)
  · intro hx y hy
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
    show B12 x ((sig c) y') = 0
    rw [← B12_sig_symm_left c x y']
    exact Cc_isotropic hx hy'

theorem tvP_mem_conj_iff (k : Fin 365211) (c : TD6) :
    (⟨tvP k, tvP_mem k⟩ : TD6) ∈ (UFix Cc).map (MulAut.conj c).toMonoidHom ↔
      ∀ x ∈ lineSet k.val, x ∈ C0.map (sig c).toLinearMap := by
  rw [map_UFix, tvP_mem_UFix_iff]
  constructor
  · intro h x hx
    have hx1 : x ∈ Cc.map (sig c).toLinearMap := (perp_map_Cc c x).1 fun y hy => h x hx y hy
    rw [mem_map_sig] at hx1 ⊢
    exact (Cc_singular_iff_C0 _).1 ⟨hx1, by rw [q12_sig_symm]; exact q12_of_mem_lineSet hx⟩
  · intro h x hx y hy
    have hx1 : x ∈ Cc.map (sig c).toLinearMap := Submodule.map_mono C0_le_Cc (h x hx)
    exact (perp_map_Cc c x).2 hx1 y hy

theorem exists_line_through {c : TD6} {v : V12} (hv : v ∈ C0.map (sig c).toLinearMap)
    (hv0 : v ≠ 0) : ∃ k : Fin 365211, v ∈ lineSet k.val ∧
      ∀ x ∈ lineSet k.val, x ∈ C0.map (sig c).toLinearMap := by
  obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
  obtain ⟨hv₀1, hv₀2⟩ := (mem_C0_iff v₀).1 hv₀
  obtain ⟨y', hy'5, hy'0, hy'y⟩ : ∃ y' : Fin 6 → ZMod 2, y' 5 = 0 ∧ y' ≠ 0 ∧ y' ≠ v₀.2 := by
    by_cases h : v₀.2 = Pi.single 0 1
    · refine ⟨Pi.single 1 1, by simp [Pi.single_apply], fun h0 => ?_, fun h0 => ?_⟩
      · have := congrFun h0 1
        simp at this
      · rw [h] at h0
        have := congrFun h0 1
        simp [Pi.single_apply] at this
    · refine ⟨Pi.single 0 1, by simp [Pi.single_apply], fun h0 => ?_, fun h0 => h h0.symm⟩
      have := congrFun h0 0
      simp at this
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V12, w₀ = ((0 : Fin 6 → ZMod 2), y') := ⟨_, rfl⟩
  have hw₀C : w₀ ∈ C0 := by rw [hw₀]; exact ⟨rfl, hy'5⟩
  have hq1 : q12 v₀ = 0 := by simp [q12_apply, hv₀1]
  have hq2 : q12 w₀ = 0 := by simp [q12_apply, hw₀]
  have hb : B12 v₀ w₀ = 0 := by simp [B12, hv₀1, hw₀]
  have hts := tsPair_map (iso_sig c) (show TsPair v₀ w₀ from ⟨hq1, hq2, hb⟩)
  have hu0 : (sig c) v₀ ≠ 0 := hv0
  have hw0 : (sig c) w₀ ≠ 0 := by
    intro h
    have h' : w₀ = 0 := (sig c).injective (by rw [h, map_zero])
    rw [hw₀] at h'
    exact hy'0 (congrArg Prod.snd h')
  have huw : (sig c) v₀ ≠ (sig c) w₀ := by
    intro h
    have h' : v₀ = w₀ := (sig c).injective h
    rw [hw₀] at h'
    exact hy'y (congrArg Prod.snd h').symm
  obtain ⟨p, hp, -⟩ := exists_line_siegel hu0 hw0 huw hts
  refine ⟨p, ?_, ?_⟩
  · rw [hp]
    simp [lineOfPair]
  · intro x hx
    rw [hp] at hx
    simp only [lineOfPair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Submodule.mem_map_of_mem hv₀
    · exact Submodule.mem_map_of_mem hw₀C
    · rw [← map_add]
      exact Submodule.mem_map_of_mem (C0.add_mem hv₀ hw₀C)

theorem Psi_le_of_Phi_eq {c c' : TD6}
    (h : (UFix Cc).map (MulAut.conj c).toMonoidHom = (UFix Cc).map (MulAut.conj c').toMonoidHom) :
    C0.map (sig c).toLinearMap ≤ C0.map (sig c').toLinearMap := by
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    exact Submodule.zero_mem _
  obtain ⟨k, hkv, hk⟩ := exists_line_through hv hv0
  have h1 := (tvP_mem_conj_iff k c).2 hk
  rw [h] at h1
  exact (tvP_mem_conj_iff k c').1 h1 v hkv

theorem Psi_eq_of_Phi_eq {c c' : TD6}
    (h : (UFix Cc).map (MulAut.conj c).toMonoidHom = (UFix Cc).map (MulAut.conj c').toMonoidHom) :
    C0.map (sig c).toLinearMap = C0.map (sig c').toLinearMap :=
  le_antisymm (Psi_le_of_Phi_eq h) (Psi_le_of_Phi_eq h.symm)

theorem Phi_eq_of_Psi_eq {c c' : TD6}
    (h : C0.map (sig c).toLinearMap = C0.map (sig c').toLinearMap) :
    (UFix Cc).map (MulAut.conj c).toMonoidHom = (UFix Cc).map (MulAut.conj c').toMonoidHom := by
  rw [map_UFix, map_UFix]
  have key : ∀ d : TD6, (Cc.map (sig d).toLinearMap : Set V12) =
      {z | (∀ y ∈ C0.map (sig d).toLinearMap, B12 z y = 0) ∧
        (z ∈ C0.map (sig d).toLinearMap ∨ q12 z = 1)} := by
    intro d
    ext z
    rw [SetLike.mem_coe, mem_map_sig, mem_Cc_iff_perp]
    show _ ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, ?_⟩
      · obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.mp hy
        show B12 z ((sig d) y') = 0
        rw [← B12_sig_symm_left]
        exact h1 y' hy'
      · rcases h2 with h2 | h2
        · exact Or.inl (mem_map_sig.2 h2)
        · exact Or.inr (by rw [← q12_sig_symm d]; exact h2)
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [B12_sig_symm_left]
        exact h1 _ (Submodule.mem_map_of_mem hy)
      · rcases h2 with h2 | h2
        · exact Or.inl (mem_map_sig.1 h2)
        · exact Or.inr (by rw [q12_sig_symm]; exact h2)
  have hCC : Cc.map (sig c).toLinearMap = Cc.map (sig c').toLinearMap := by
    refine SetLike.coe_injective ?_
    rw [key c, key c', h]
  rw [hCC]

theorem finrank_planeSub (i : Fin 75735) : Module.finrank (ZMod 2) (planeSub i.val) = 6 := by
  have h := meetCnt_eq_card i.2 i.2
  rw [inf_idem, meetCnt_self i.2] at h
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := planeSub i.val)
  rw [Nat.card_zmod, ← h] at h2
  exact Nat.pow_right_injective (le_refl 2) (h2.symm.trans (by norm_num : (64 : ℕ) = 2 ^ 6))

theorem card_of_finrank_five {H : Submodule (ZMod 2) V12} (h : Module.finrank (ZMod 2) H = 5) :
    Nat.card H = 32 := by
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := H)
  rw [Nat.card_zmod, h] at h2
  rw [h2]
  norm_num

section Kc

theorem kcMeetCheck_holds : CFSG.SmithD6.chkKcMeet = true := Certificates.certificate38935.1

theorem kcThroughCheck_holds : CFSG.SmithD6.chkKcThrough = true :=
  Certificates.certificate38935.2

theorem meetCnt_zero_le {j : ℕ} (hj : j < 75735) (hj0 : j ≠ 0) : meetCnt 0 j ≤ 16 := by
  have h := kcMeetCheck_holds
  unfold chkKcMeet at h
  rw [List.all_eq_true] at h
  have := h j (List.mem_range.mpr hj)
  simpa [hj0] using this

theorem plane_unique {i j : Fin 75735} {H : Submodule (ZMod 2) V12} (hi : H ≤ planeSub i.val)
    (hj : H ≤ planeSub j.val) (hfin : Module.finrank (ZMod 2) H = 5) : i = j := by
  by_contra hne
  obtain ⟨g, hg⟩ := exists_smul_planes_eq i 0
  have hgj : g • j ≠ 0 := by
    intro h
    apply hne
    have : g • j = g • i := h.trans hg.symm
    exact (MulAction.injective g this).symm
  have h1 := meetCnt_smul g i j
  rw [hg] at h1
  have h2 : meetCnt 0 (g • j).val ≤ 16 := meetCnt_zero_le (g • j).2 (fun h => hgj (Fin.ext h))
  have h3 : meetCnt i.val j.val = Nat.card ↥(planeSub i.val ⊓ planeSub j.val) :=
    meetCnt_eq_card i.2 j.2
  have h4 : Nat.card H ≤ Nat.card ↥(planeSub i.val ⊓ planeSub j.val) :=
    Nat.card_le_card_of_injective (Submodule.inclusion (le_inf hi hj))
      (Submodule.inclusion_injective _)
  have h5 := card_of_finrank_five hfin
  have h6 : meetCnt (0 : Fin 75735).val (g • j).val = meetCnt i.val j.val := h1
  have h7 : meetCnt 0 (g • j).val = meetCnt i.val j.val := h6
  omega

end Kc

theorem Psi_le_plane (c : TD6) :
    C0.map (sig c).toLinearMap ≤ planeSub (c • (0 : Fin 75735)).val := by
  have h := map_planeSub_smul c 0
  rw [← h]
  exact Submodule.map_mono C0_le_F

theorem finrank_Psi (c : TD6) : Module.finrank (ZMod 2) (C0.map (sig c).toLinearMap) = 5 := by
  rw [LinearEquiv.finrank_map_eq (sig c) C0, finrank_C0]

theorem exists_Psi_eq {H : Submodule (ZMod 2) V12} {i : Fin 75735}
    (hH : H ≤ planeSub i.val) (hfin : Module.finrank (ZMod 2) H = 5) :
    ∃ c : TD6, C0.map (sig c).toLinearMap = H := by
  obtain ⟨g, hg⟩ := exists_smul_zero_eq i
  have h2 : g⁻¹ • i = 0 := by
    rw [← hg]
    exact inv_smul_smul g 0
  have h1 := map_planeSub_smul g⁻¹ i
  rw [h2] at h1
  have hH' : H.map (sig g⁻¹).toLinearMap ≤ planeSub 0 :=
    (Submodule.map_mono hH).trans h1.le
  have hfin' : Module.finrank (ZMod 2) (H.map (sig g⁻¹).toLinearMap) = 5 := by
    rw [LinearEquiv.finrank_map_eq (sig g⁻¹) H, hfin]
  obtain ⟨τ, hτ⟩ := exists_stab0_map_C0 hH' hfin'
  have hgg : ∀ y, sig g (sig g⁻¹ y) = y := fun y => by
    have := sig_inv_apply_apply g⁻¹ y
    rwa [inv_inv] at this
  refine ⟨g * τ.1, ?_⟩
  have hmul : ∀ v, sig (g * τ.1) v = sig g (sig τ.1 v) := fun v => by
    rw [sig_mul]
    rfl
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : sig τ.1 v ∈ H.map (sig g⁻¹).toLinearMap := by
      rw [← hτ]
      exact Submodule.mem_map_of_mem hv
    obtain ⟨h, hh, hhe⟩ := Submodule.mem_map.mp hv'
    show sig (g * τ.1) v ∈ H
    rw [hmul, ← hhe]
    show sig g (sig g⁻¹ h) ∈ H
    rw [hgg]
    exact hh
  · intro hz
    have hz' : (sig g⁻¹).toLinearMap z ∈ C0.map (sig τ.1).toLinearMap := by
      rw [hτ]
      exact Submodule.mem_map_of_mem hz
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hz'
    refine Submodule.mem_map.mpr ⟨v, hv, ?_⟩
    show sig (g * τ.1) v = z
    rw [hmul]
    have hve' : sig τ.1 v = sig g⁻¹ z := hve
    rw [hve', hgg]

theorem mem_planeSub_iff_memR {i : ℕ} (hi : i < 75735) {c : ℕ} (hc : c < 4096) :
    dec12 c ∈ planeSub i ↔ memR pbArr[i]! ppArr[i]! c = true := by
  have Fi := planeFacts hi
  constructor
  · intro h
    obtain ⟨d, hd, hdc⟩ := mem_planeSpan_iff.1 (show dec12 c ∈ planeSpan pbArr[i]! from h)
    have : c = xorComb pbArr[i]! d := eq_of_dec12_eq hc (xorComb_lt Fi.lt d) hdc
    rw [this]
    exact Fi.complete d hd
  · intro h
    exact dec12_mem_planeSpan_of_memR h

theorem Lin01_le_planeSub_iff {i : Fin 75735} :
    Lin01 ≤ planeSub i.val ↔
      (memR pbArr[i.val]! ppArr[i.val]! 64 && memR pbArr[i.val]! ppArr[i.val]! 128) = true := by
  rw [Bool.and_eq_true, ← mem_planeSub_iff_memR i.2 (by norm_num : 64 < 4096),
    ← mem_planeSub_iff_memR i.2 (by norm_num : 128 < 4096), dec12_64, dec12_128]
  unfold Lin01
  rw [Submodule.span_le]
  constructor
  · intro h
    exact ⟨h (by simp), h (by simp)⟩
  · rintro ⟨h1, h2⟩ v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact h1
    · exact h2

theorem card_fin_filter (n : ℕ) (p : ℕ → Bool) :
    Nat.card {i : Fin n // p i.val = true} = ((List.range n).filter p).length := by
  rw [← ncard_filter_range p n, ← Nat.card_coe_set_eq]
  exact Nat.card_congr ⟨fun i => ⟨i.1.val, i.1.2, i.2⟩, fun d => ⟨⟨d.1, d.2.1⟩, d.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem card_planes_through :
    Nat.card {i : Fin 75735 // Lin01 ≤ planeSub i.val} = 135 := by
  have h := kcThroughCheck_holds
  unfold chkKcThrough at h
  have h135 : ((List.range 75735).filter fun i =>
      memR pbArr[i]! ppArr[i]! 64 && memR pbArr[i]! ppArr[i]! 128).length = 135 := by
    simpa using h
  rw [← h135, ← card_fin_filter]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i => Lin01_le_planeSub_iff)

theorem ncard_hyperplane_family :
    {H : Submodule (ZMod 2) V12 | Lin01 ≤ H ∧ ∃ i : Fin 75735, H ≤ planeSub i.val ∧
      Module.finrank (ZMod 2) H = 5}.ncard = 2025 := by
  haveI : Finite (Submodule (ZMod 2) V12) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) V12 => (H : Set V12)) SetLike.coe_injective
  let I := {i : Fin 75735 // Lin01 ≤ planeSub i.val}
  haveI : Fintype I := Fintype.ofFinite I
  let Hyp : I → Type := fun i => {H : Submodule (ZMod 2) V12 //
    Lin01 ≤ H ∧ H ≤ planeSub i.1.val ∧ Module.finrank (ZMod 2) H = 5}
  have hfib : ∀ i : I, Nat.card (Hyp i) = 15 := fun i =>
    card_hyperplanes i.2 (finrank_planeSub i.1) finrank_Lin01
  let T := {H : Submodule (ZMod 2) V12 | Lin01 ≤ H ∧ ∃ i : Fin 75735, H ≤ planeSub i.val ∧
    Module.finrank (ZMod 2) H = 5}
  let e : (Σ i : I, Hyp i) → T := fun p => ⟨p.2.1, p.2.2.1, p.1.1, p.2.2.2.1, p.2.2.2.2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨⟨i₁, hi₁⟩, ⟨H₁, hL₁, hH₁, hf₁⟩⟩ ⟨⟨i₂, hi₂⟩, ⟨H₂, hL₂, hH₂, hf₂⟩⟩ h
      have hH : H₁ = H₂ := congrArg (fun t : T => (t : Submodule (ZMod 2) V12)) h
      subst hH
      have hi : i₁ = i₂ := plane_unique hH₁ hH₂ hf₁
      subst hi
      rfl
    · rintro ⟨H, hL, i, hHi, hfin⟩
      exact ⟨⟨⟨i, hL.trans hHi⟩, ⟨H, hL, hHi, hfin⟩⟩, rfl⟩
  rw [← Nat.card_coe_set_eq]
  show Nat.card T = 2025
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_planes_through]

theorem Lin01_le_iff {k : Fin 365211}
    (hl : lineSet k.val = {((0 : Fin 6 → ZMod 2), Pi.single 0 1), (0, Pi.single 1 1),
      (0, Pi.single 0 1 + Pi.single 1 1)}) {H : Submodule (ZMod 2) V12} :
    Lin01 ≤ H ↔ ∀ x ∈ lineSet k.val, x ∈ H := by
  rw [hl]
  unfold Lin01
  rw [Submodule.span_le]
  constructor
  · intro h x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h (by simp)
    · exact h (by simp)
    · have h1 := h (show ((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)) ∈
        ({((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
          ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))} : Set V12) by simp)
      have h2 := h (show ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2)) ∈
        ({((0 : Fin 6 → ZMod 2), (Pi.single 0 1 : Fin 6 → ZMod 2)),
          ((0 : Fin 6 → ZMod 2), (Pi.single 1 1 : Fin 6 → ZMod 2))} : Set V12) by simp)
      have h3 := H.add_mem h1 h2
      simpa [Prod.mk_add_mk] using h3
  · intro h v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact h _ (by simp)
    · exact h _ (by simp)

theorem ncard_image_eq_of_iff {α β γ : Type*} (f : α → β) (g : α → γ) (S : Set α)
    (h : ∀ a b, f a = f b ↔ g a = g b) : (f '' S).ncard = (g '' S).ncard := by
  refine Set.ncard_congr (fun y hy => g (Classical.choose hy)) ?_ ?_ ?_
  · intro y hy
    exact ⟨Classical.choose hy, (Classical.choose_spec hy).1, rfl⟩
  · intro y z hy hz hyz
    have h1 := (h _ _).2 hyz
    rw [(Classical.choose_spec hy).2, (Classical.choose_spec hz).2] at h1
    exact h1
  · rintro _ ⟨a, ha, rfl⟩
    have hfa : f a ∈ f '' S := ⟨a, ha, rfl⟩
    refine ⟨f a, hfa, ?_⟩
    exact ((h _ _).1 (Classical.choose_spec hfa).2)

theorem ncard_conj_Kc (t₀ : TD6)
    (ht₀ : ∃ k : Fin 365211, (t₀ : Equiv.Perm (Fin 365211)) = tvP k ∧
      lineSet k.val = {((0 : Fin 6 → ZMod 2), Pi.single 0 1), (0, Pi.single 1 1),
        (0, Pi.single 0 1 + Pi.single 1 1)}) :
    {Y : Subgroup TD6 | ∃ c : TD6, Y = (UFix Cc).map (MulAut.conj c).toMonoidHom ∧
      t₀ ∈ Y}.ncard = 2025 := by
  obtain ⟨k, hk, hl⟩ := ht₀
  have ht : t₀ = ⟨tvP k, tvP_mem k⟩ := Subtype.ext hk
  let Φ : TD6 → Subgroup TD6 := fun c => (UFix Cc).map (MulAut.conj c).toMonoidHom
  let Ψ : TD6 → Submodule (ZMod 2) V12 := fun c => C0.map (sig c).toLinearMap
  let S : Set TD6 := {c | ∀ x ∈ lineSet k.val, x ∈ Ψ c}
  have h1 : {Y : Subgroup TD6 | ∃ c : TD6, Y = Φ c ∧ t₀ ∈ Y} = Φ '' S := by
    ext Y
    constructor
    · rintro ⟨c, rfl, hc⟩
      refine ⟨c, ?_, rfl⟩
      rw [ht] at hc
      exact (tvP_mem_conj_iff k c).1 hc
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c, rfl, ?_⟩
      rw [ht]
      exact (tvP_mem_conj_iff k c).2 hc
  show {Y : Subgroup TD6 | ∃ c : TD6, Y = Φ c ∧ t₀ ∈ Y}.ncard = 2025
  rw [h1, ncard_image_eq_of_iff Φ Ψ S fun a b => ⟨Psi_eq_of_Phi_eq, Phi_eq_of_Psi_eq⟩]
  have h2 : Ψ '' S = {H : Submodule (ZMod 2) V12 | Lin01 ≤ H ∧ ∃ i : Fin 75735,
      H ≤ planeSub i.val ∧ Module.finrank (ZMod 2) H = 5} := by
    ext H
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(Lin01_le_iff hl).2 hc, c • 0, Psi_le_plane c, finrank_Psi c⟩
    · rintro ⟨hL, i, hH, hfin⟩
      obtain ⟨c, rfl⟩ := exists_Psi_eq hH hfin
      exact ⟨c, (Lin01_le_iff hl).1 hL, rfl⟩
  rw [h2]
  exact ncard_hyperplane_family

end Cert

end CFSG.GF2Type.SmithTypeE.E7
