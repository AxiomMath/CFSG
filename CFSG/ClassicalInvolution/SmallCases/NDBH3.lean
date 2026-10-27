module

public import CFSG.ClassicalInvolution.SmallCases.NDBH2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R

namespace T8R.Loc

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q Q' : Subgroup G}


theorem eq_of_conj_mul_inv_mem_odd {P : Subgroup G} (hP : IsPGroup 2 ↥P) {u v : G} (hu : u ∈ P)
    (hv : v ∈ P) (hQ : Odd (Nat.card ↥Q)) (n : G) (h : n⁻¹ * (u * v⁻¹) * n ∈ Q) : u = v :=
  eq_of_mul_inv_mem_odd hP hu hv (N := conjSub n Q) (by rw [natCard_conjSub']; exact hQ)
    (mem_conjSub_iff.mpr h)

theorem conj_zt_mul_inv_mem_of_conj (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ Q := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  rcases hn with hn | hn
  · refine hX.zt ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hs.hz.conj_eq hn
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h1]
  · have hzt : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
    have hNΩ : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
    have hKN : K ∈ omegaNbr Ω (conjSub n K) := by
      have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
      rwa [hn] at this
    have hN : conjSub n K ∈ omegaNbr Ω K :=
      T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hNΩ hK hKN
    have hy : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hs.hz.conj n
    have h1 := hX.invol hN hy
    have hnt : n * t * n⁻¹ = z := by
      have := hs.ht.conj n
      rw [hn] at this
      exact (hs.hz.eq this).symm
    have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * t⁻¹ := by
      calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
        _ = (n * z * n⁻¹) * z * (t⁻¹ * z⁻¹) := by rw [hnt]; group
        _ = (n * z * n⁻¹) * (z * t⁻¹ * z⁻¹) := by group
        _ = (n * z * n⁻¹) * t⁻¹ := by
          have : z * t⁻¹ * z⁻¹ = t⁻¹ := by
            have h2 : z * t⁻¹ = t⁻¹ * z := by
              have h3 : t * z = z * t := hzt.symm
              calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
                _ = t⁻¹ * (z * t) * t⁻¹ := by rw [h3]
                _ = t⁻¹ * z := by group
            rw [h2]; group
          rw [this]
    rw [e]
    exact h1

theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hV : ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ Q := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨n', hn'c, hxn'⟩ := exists_conj_sylow_of_centralizes S haS hx2 hxc
  rw [← hn'c]
  have key : ∀ m : G, (conjSub m K = K ∨ conjSub m J = K) →
      m * (z * t) * m⁻¹ = n' * (z * t) * n'⁻¹ →
      n' * (z * t) * n'⁻¹ * (z * t)⁻¹ ∈ Q := fun m hm hmc => by
    rw [← hmc]
    exact conj_zt_mul_inv_mem_of_conj hs hX hm
  set M : Subgroup G := conjSub n'⁻¹ K with hMdef
  have hMΩ : M ∈ Ω := hΩ.conjInvariant n'⁻¹ K hK
  have hKM : conjSub n' M = K := by rw [hMdef, conjSub_conjSub_inv]
  have hx'M : n'⁻¹ * x * n' ∈ M := by
    rw [hMdef, mem_conjSub_iff]
    have e : (n'⁻¹)⁻¹ * (n'⁻¹ * x * n') * n'⁻¹ = x := by group
    rw [e]
    exact hxK
  have hx'S : n'⁻¹ * x * n' ∈ (S : Subgroup G) := (mem_conjSub_iff.mp hxn')
  have hx'o : orderOf (n'⁻¹ * x * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x
    rw [MulAut.conj_apply, hx4] at this
    simpa using this
  have h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have hle : Subgroup.zpowers (n'⁻¹ * x * n') ≤ M ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hx'M) (Subgroup.zpowers_le.mpr hx'S)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hx'o] at this
  have hKS : K ⊓ (S : Subgroup G) = R :=
    hRsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hRK hRS)
  have hJS : J ⊓ (S : Subgroup G) = T :=
    hTsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hTJ hTS)
  by_cases hSyl : IsSylow2In (M ⊓ (S : Subgroup G)) M
  · have hMR : M ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hSyl
    rcases hX.rset hMR inf_le_right with h | h
    · have hRM : R ≤ M := h ▸ inf_le_left
      have hMK : M = K :=
        hΩ.eq_of_le_of_le hMΩ hK hRsyl.2.1 (by omega) hRM hRK
      refine key n' (Or.inl ?_) rfl
      have h' := hKM
      rw [hMK] at h'
      exact h'
    · have hTM : T ≤ M := h ▸ inf_le_left
      have hMJ : M = J :=
        hΩ.eq_of_le_of_le hMΩ hJΩ hTsyl.2.1 (by omega) hTM hTJ
      refine key n' (Or.inr ?_) rfl
      have h' := hKM
      rw [hMJ] at h'
      exact h'
  · have hMK : M ≠ K := by
      intro h
      exact hSyl (by rw [h, hKS]; exact hRsyl)
    have hMJ : M ≠ J := by
      intro h
      exact hSyl (by rw [h, hJS]; exact hTsyl)
    obtain ⟨c₁, hc₁, hc₁K⟩ := hV M hMΩ h4 hMK hMJ
    have hc₁a : c₁ * (z * t) * c₁⁻¹ = z * t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₁
      calc c₁ * (z * t) * c₁⁻¹ = ((z * t) * c₁) * c₁⁻¹ := by rw [this]
        _ = z * t := by group
    refine key (n' * c₁) ?_ ?_
    · rcases hc₁K with h | h
      · left
        rw [conjSub_mul, h, hKM]
      · right
        rw [conjSub_mul, h, hKM]
    · calc n' * c₁ * (z * t) * (n' * c₁)⁻¹ = n' * (c₁ * (z * t) * c₁⁻¹) * n'⁻¹ := by group
        _ = n' * (z * t) * n'⁻¹ := by rw [hc₁a]

theorem extraTrans (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') : ExtraTrans Ω K J S z t := by
  intro M hM h4 hMK hMJ
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have hc := ctxOf hP hW
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  have hU : M ⊓ W ∈ η := by
    have := l6_11_proved p f hp hq G Ω hΩ S η hηG hηS M hM (by omega)
    rwa [← hWη] at this
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hUU : M ⊓ W ∈ USet Ω := (hη.1 hU).1
  obtain ⟨RM, hRMD, hRMsyl⟩ := exists_sylow_mem_DSet hp hq hΩ hW hWS hM hUU inf_le_left
    (inf_le_right.trans hWS)
  obtain ⟨ρK, hρK, hρKR⟩ : ∃ ρ : Rep Ω W, ρ.K = K ∧ ρ.R = R := ⟨stdRepK hs, rfl, rfl⟩
  obtain ⟨ρJ, hρJ, -⟩ : ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T := ⟨stdRepJ hs, rfl, rfl⟩
  obtain ⟨ρM, hρM, -⟩ : ∃ ρ : Rep Ω W, ρ.K = M ∧ ρ.R = RM :=
    ⟨mkRep hP hW hM hRMD hRMsyl, rfl, rfl⟩
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hp hq hM
  have hMnK : M ∉ omegaNbr Ω K := hX.four hM h4 hMJ
  have hMnJ : M ∉ omegaNbr Ω J :=
    (hXs).four hM h4 hMK
  have hKnM : K ∉ omegaNbr Ω M := fun h =>
    hMnK (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hM hK h)
  have hJnM : J ∉ omegaNbr Ω M := fun h =>
    hMnJ (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hM hJΩ h)
  have hzK : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hs.hz
  have htJ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact hs.ht
  have hzMρ : IsUniqueInvolution ρM.K zM := by rw [hρM]; exact hzM
  have hsz : ρM.r * z * ρM.r⁻¹ = zM * z :=
    hc.conj_involution ρM ρK (by rw [hρK, hρM]; exact hMK) (by rw [hρK, hρM]; exact hKnM) hzMρ hzK
  have hst : ρM.r * t * ρM.r⁻¹ = zM * t :=
    hc.conj_involution ρM ρJ (by rw [hρJ, hρM]; exact hMJ) (by rw [hρJ, hρM]; exact hJnM) hzMρ htJ
  have hzW : z ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW ρK.hK ρK.hR ρK.hRK hzK).2
  have hzMW : zM ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW ρM.hK ρM.hR ρM.hRK hzMρ).2
  have hzzM : zM * z = z * zM := hc.comm_W zM hzMW z hzW
  have hrC : ρK.r ∈ Subgroup.centralizer ({z * t} : Set G) :=
    le_centralizer_mul hs (hρKR ▸ ρK.hr)
  have hrN : ρK.r ∈ Subgroup.normalizer (W : Set G) := ρK.r_mem_normalizer
  have hsN : ρM.r ∈ Subgroup.normalizer (W : Set G) := ρM.r_mem_normalizer
  have hr2 : ρK.r * ρK.r ∈ W := D_sq_mem hp hq hΩ hW ρK.hR ρK.hr
  have hs2 : ρM.r * ρM.r ∈ W := D_sq_mem hp hq hΩ hW ρM.hR ρM.hr
  have hne : ρK.K ≠ ρM.K := by rw [hρK, hρM]; exact Ne.symm hMK
  have hnot : ρM.K ∉ omegaNbr Ω ρK.K := by rw [hρK, hρM]; exact hMnK
  have hcube : (piG W ρK.r * piG W ρM.r) ^ 3 = 1 := by
    rcases thompsonCube G Ω hP W hW ρK.R ρK.hR ρM.R ρM.hR ρK.r ρK.hr ρM.r ρM.hr ρK.hrW ρM.hrW with
      h | h
    · exact absurd ((piG_comm_iff hrN hsN).mpr h) (hc.noncomm ρK ρM hne hnot)
    · exact (piG_cube_iff hrN hsN).mpr h
  obtain ⟨c, hcC, hcK⟩ := CFSG.ClassicalInvolution.Asc77.T8R.extraTrans_core hcl ρK ρM hzM.sq hsz hst hzzM hrC hr2 hs2 hcube
    (fun ρ' h => hc.K_eq_of_img_eq ρ' ρM h)
  exact ⟨c, hcC, Or.inl (by rw [← hρK, ← hρM]; exact hcK)⟩


end Cert

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77
