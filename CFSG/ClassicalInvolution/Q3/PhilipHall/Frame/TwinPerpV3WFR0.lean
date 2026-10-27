module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section R0




variable {n : ℕ}

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem WFIn.exists_twins (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∃ M : Fin 4 → Subgroup Y, Function.Injective M ∧
      (∀ i, M i ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) ∧
      ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, ∃ i, M i = J := by
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  exact ⟨M, hfr.inj, hfr.mem, hfr.surj⟩

private theorem inj4 {i j k l : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j) (hlk : l ≠ k) : Function.Injective ![i, j, k, l] := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp_all

private theorem fin4_exists_fourth : ∀ i j k : Fin 4, i ≠ j → k ≠ i → k ≠ j →
    ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  decide


theorem eq_or_mul_t_of_comm {J : Subgroup Y} {a b : Y} (hq : Q8Facts J t) (ha : a ∈ J) (hb : b ∈ J)
    (ha2 : a * a = t) (hb2 : b * b = t) (hab : a * b = b * a) : b = a ∨ b = a * t := by
  rcases hq.cent_cyc a ha ha2 b hb hab.symm with h | h | h | h
  · exfalso; rw [h, one_mul] at hb2; exact hq.z_ne hb2.symm
  · exact Or.inl h
  · exfalso; rw [h, hq.z_sq] at hb2; exact hq.z_ne hb2.symm
  · exact Or.inr h

theorem WFIn.exists_fuse_pair (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {W' : Subgroup Y}
    (hW' : W' ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW' : t ∈ W')
    {L L' : Subgroup Y} (hL : L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hL' : L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : L ≠ L') {a a' : Y}
    (ha : a ∈ L ⊓ W') (ha' : a' ∈ L' ⊓ W') (oa : orderOf a = 4) (oa' : orderOf a' = 4) :
    ∃ y ∈ Subgroup.centralizer ({a * a'} : Set Y),
      y * t * y⁻¹ ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W' := by
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := h.exit
  have hd := hStd.datum
  have hLz := h.uniqInv hL
  have hL'z := h.uniqInv hL'
  have hLsyl : IsSylow2In L L := ⟨le_rfl, h2g L hL.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hL'syl : IsSylow2In L' L' :=
    ⟨le_rfl, h2g L' hL'.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨L₃, w, hd''⟩ := hd.exists_datum_of_pair hL hL' (Ne.symm hne) hLsyl hL'syl
    (h.comm hL hL' hne) ha.1 ha'.1 oa oa'
  have htwL : twinSet (CoreAssembly.conjClass (tightCore R)) L =
      twinSet (CoreAssembly.conjClass (tightCore R)) K := twinSet_eq_of_mem_twinSet hd.hz hL
  obtain ⟨M, hMinj, hMmem, hMsurj⟩ := h.exists_twins
  have hL₃K : L₃ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := htwL ▸ hd''.hK₃
  obtain ⟨i, hi⟩ := hMsurj L hL
  obtain ⟨j, hj⟩ := hMsurj L' hL'
  obtain ⟨k, hk⟩ := hMsurj L₃ hL₃K
  have hij : i ≠ j := fun e => hne (by rw [← hi, ← hj, e])
  have hki : k ≠ i := fun e => hd''.hK₃K (by rw [← hk, ← hi, e])
  have hkj : k ≠ j := fun e => hd''.hK₃K' (by rw [← hk, ← hj, e])
  obtain ⟨l, hli, hlj, hlk⟩ := fin4_exists_fourth i j k hij hki hkj
  have hK₄L : M l ∈ twinSet (CoreAssembly.conjClass (tightCore R)) L := htwL ▸ hMmem l
  have hperp := kPerp_datum hStd.perp hL.1 hLz
  obtain ⟨a₁, a₂, a₃, a₄, y, ha₁, ho₁, ha₂, ho₂, ha₃, ho₃, ha₄, ho₄, -, -, -, -, -, -, hy, -,
    hW₁, hW₂, hW₃, hW₄, hyC, j', hj₁, hj₂, hj₃, hj₄⟩ :=
    exists_fuse_cent2W h.partI hd'' hperp hK₄L
      (fun e => hli (hMinj (by rw [e, hi])))
      (fun e => hlj (hMinj (by rw [e, hj])))
      (fun e => hlk (hMinj (by rw [e, hk]))) hStd.wyl hW' htW'
  have hsqL := T7A.sq_eq_of_orderOf_four hLz ha.1 oa
  have hsqL' := T7A.sq_eq_of_orderOf_four hL'z ha'.1 oa'
  have hsq₁ := T7A.sq_eq_of_orderOf_four hLz ha₁ ho₁
  have hsq₂ := T7A.sq_eq_of_orderOf_four hL'z ha₂ ho₂
  have habW := Q3.Q3T6.abelian_of_mem_WSet3 h.hyp hW'
  have hc₁ := eq_or_mul_t_of_comm (h.q8 hL) ha.1 ha₁ hsqL hsq₁ (habW _ ha.2 _ hW₁)
  have hc₂ := eq_or_mul_t_of_comm (h.q8 hL') ha'.1 ha₂ hsqL' hsq₂ (habW _ ha'.2 _ hW₂)
  have ht2 := (h.q8 hL).z_sq
  have htc₂ : t * a₂ = a₂ * t := (h.q8 hL').z_central a₂ ha₂
  have htc' : t * a' = a' * t := (h.q8 hL').z_central a' ha'.1
  have htc₁ : t * a₁ = a₁ * t := (h.q8 hL).z_central a₁ ha₁
  have hprod : a₁ * a₂ = a * a' ∨ a₁ * a₂ = a * a' * t := by
    rcases hc₁ with e₁ | e₁ <;> rcases hc₂ with e₂ | e₂ <;> rw [e₁, e₂]
    · exact Or.inl rfl
    · right; group
    · right
      calc a * t * a' = a * (t * a') := mul_assoc _ _ _
        _ = a * (a' * t) := by rw [htc']
        _ = a * a' * t := (mul_assoc _ _ _).symm
    · left
      calc a * t * (a' * t) = a * (t * a') * t := by group
        _ = a * (a' * t) * t := by rw [htc']
        _ = a * a' * (t * t) := by group
        _ = a * a' := by rw [ht2, mul_one]
  have hinj4 : Function.Injective ![i, j, k, l] := inj4 hij hki hkj hli hlj hlk
  have hJ : ∀ r, M (![i, j, k, l] r) ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K :=
    fun r => hMmem _
  have hLi : M i = L := hi
  have hLj : M j = L' := hj
  have hLk : M k = L₃ := hk
  rcases hprod with hp | hp
  · refine ⟨y, ?_, ?_⟩
    · rw [← hp]; exact hyC
    · rw [hy]
      refine ⟨fun r => M (![i, j, k, l] r), ![a₁, a₂, a₃, a₄], hMinj.comp hinj4, hJ, ?_, ?_⟩
      · intro r
        fin_cases r
        · exact ⟨Subgroup.mem_inf.mpr ⟨by simpa [hLi] using ha₁, hW₁⟩, ho₁⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨by simpa [hLj] using ha₂, hW₂⟩, ho₂⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨by simpa [hLk] using ha₃, hW₃⟩, ho₃⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨ha₄, hW₄⟩, ho₄⟩
      · simp
  · refine ⟨j' * y * j'⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y * (a₁ * a₂) = (a₁ * a₂) * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have e1 : j' * (a₁ * a₂) * j'⁻¹ = a * a' := by
        have : j' * (a₁ * a₂) * j'⁻¹ = (j' * a₁ * j'⁻¹) * (j' * a₂ * j'⁻¹) := by group
        rw [this, hj₁, hj₂]
        have hinv : a₁⁻¹ = a₁ * t := by
          apply inv_eq_of_mul_eq_one_right
          calc a₁ * (a₁ * t) = (a₁ * a₁) * t := (mul_assoc _ _ _).symm
            _ = t * t := by rw [hsq₁]
            _ = 1 := ht2
        rw [hinv]
        calc a₁ * t * a₂ = a₁ * (t * a₂) := mul_assoc _ _ _
          _ = a₁ * (a₂ * t) := by rw [htc₂]
          _ = (a₁ * a₂) * t := (mul_assoc _ _ _).symm
          _ = a * a' := by rw [hp, mul_assoc, ht2, mul_one]
      have e2 : j' * y * j'⁻¹ * (j' * (a₁ * a₂) * j'⁻¹) = j' * (a₁ * a₂) * j'⁻¹ * (j' * y * j'⁻¹) := by
        calc j' * y * j'⁻¹ * (j' * (a₁ * a₂) * j'⁻¹) = j' * (y * (a₁ * a₂)) * j'⁻¹ := by group
          _ = j' * ((a₁ * a₂) * y) * j'⁻¹ := by rw [hyc]
          _ = j' * (a₁ * a₂) * j'⁻¹ * (j' * y * j'⁻¹) := by group
      rw [e1] at e2
      exact e2
    · have hjt : j' * t * j'⁻¹ = t := by
        rw [← hsq₁]
        calc j' * (a₁ * a₁) * j'⁻¹ = (j' * a₁ * j'⁻¹) * (j' * a₁ * j'⁻¹) := by group
          _ = a₁⁻¹ * a₁⁻¹ := by rw [hj₁]
          _ = (a₁ * a₁)⁻¹ := by group
          _ = a₁ * a₁ := by rw [hsq₁, inv_eq_of_mul_eq_one_right ht2]
      have e3 : j' * y * j'⁻¹ * t * (j' * y * j'⁻¹)⁻¹ = j' * (y * t * y⁻¹) * j'⁻¹ := by
        calc j' * y * j'⁻¹ * t * (j' * y * j'⁻¹)⁻¹ = j' * y * (j'⁻¹ * t * j') * y⁻¹ * j'⁻¹ := by group
          _ = j' * y * t * y⁻¹ * j'⁻¹ := by
              have : j'⁻¹ * t * j' = t := by
                have := congrArg (fun g => j'⁻¹ * g * j') hjt
                simpa [mul_assoc] using this.symm
              rw [this]
          _ = j' * (y * t * y⁻¹) * j'⁻¹ := by group
      rw [e3, hy]
      have e4 : j' * (a₁ * a₂ * a₃ * a₄) * j'⁻¹ = a₁⁻¹ * a₂ * a₃ * a₄ := by
        calc j' * (a₁ * a₂ * a₃ * a₄) * j'⁻¹
            = (j' * a₁ * j'⁻¹) * (j' * a₂ * j'⁻¹) * (j' * a₃ * j'⁻¹) * (j' * a₄ * j'⁻¹) := by group
          _ = a₁⁻¹ * a₂ * a₃ * a₄ := by rw [hj₁, hj₂, hj₃, hj₄]
      rw [e4]
      refine ⟨fun r => M (![i, j, k, l] r), ![a₁⁻¹, a₂, a₃, a₄], hMinj.comp hinj4, hJ, ?_, ?_⟩
      · intro r
        fin_cases r
        · show a₁⁻¹ ∈ M i ⊓ W' ∧ orderOf a₁⁻¹ = 4
          exact ⟨Subgroup.mem_inf.mpr ⟨by rw [hLi]; exact L.inv_mem ha₁, W'.inv_mem hW₁⟩, by rw [orderOf_inv]; exact ho₁⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨by simpa [hLj] using ha₂, hW₂⟩, ho₂⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨by simpa [hLk] using ha₃, hW₃⟩, ho₃⟩
        · exact ⟨Subgroup.mem_inf.mpr ⟨ha₄, hW₄⟩, ho₄⟩
      · simp

end R0

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
