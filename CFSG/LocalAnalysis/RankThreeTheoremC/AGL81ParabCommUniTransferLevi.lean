module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelRes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniRange
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock

section Residual

variable {f : ℕ} {K : Type} [Field K] {s ε : ℕ}

theorem eq_bot_of_isPGroup_of_normalized_hypSU (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {T : Subgroup (GL (HypIndex s ε) K)} (hT : IsPGroup 2 T)
    (hSN : ∀ B : hypSU h s ε, ∀ t ∈ T, (B : GL (HypIndex s ε) K) * t *
      (B : GL (HypIndex s ε) K)⁻¹ ∈ T) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  rcases isEmpty_or_nonempty (HypIndex s ε) with hι | ⟨⟨i₀⟩⟩
  · refine (Subgroup.eq_bot_iff_forall _).2 fun t _ => ?_
    exact Units.ext (Matrix.ext fun i => (hι.false i).elim)
  haveI : Nonempty (HypIndex s ε) := ⟨i₀⟩
  let W : Submodule K (HypIndex s ε → K) :=
    { carrier := {v | ∀ t ∈ T, (t : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ v = v}
      add_mem' := fun {a b} ha hb t ht => by rw [Matrix.mulVec_add, ha t ht, hb t ht]
      zero_mem' := fun t _ => by simp
      smul_mem' := fun c v hv t ht => by rw [Matrix.mulVec_smul, hv t ht] }
  have hdvd : 2 ∣ Nat.card (HypIndex s ε → K) := by
    rw [Nat.card_fun, h.card]
    refine dvd_pow (dvd_pow_self 2 (by have := h.one_le; omega)) ?_
    exact (Nat.card_pos (α := HypIndex s ε)).ne'
  have hfix0 : (0 : HypIndex s ε → K) ∈ MulAction.fixedPoints T (HypIndex s ε → K) := by
    intro t
    exact smul_zero _
  obtain ⟨w₀, hw₀, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (HypIndex s ε → K) hdvd hfix0
  have hw₀W : w₀ ∈ W := fun t ht => hw₀ ⟨t, ht⟩
  have hw₀ne : w₀ ≠ 0 := fun h0 => hne h0.symm
  have hWtop : W = ⊤ := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    ·
      haveI hsub : Subsingleton (HypIndex 0 ε) := subsingleton_hypIndex (by omega)
      obtain ⟨i, hi⟩ : ∃ i, w₀ i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hw₀ne (funext hall)
      rw [eq_top_iff]
      intro v _
      have : v = (v i * (w₀ i)⁻¹) • w₀ := by
        funext k
        obtain rfl : k = i := Subsingleton.elim _ _
        simp [hi]
      rw [this]
      exact W.smul_mem _ hw₀W
    · refine eq_top_of_invariant h hs W (fun v hv w hw => ?_) w₀ hw₀W hw₀ne
      obtain ⟨B, hB⟩ := exists_tv_mem (h := h) hv (a := 1) (by
        rw [map_one]
        exact CharTwo.add_self_eq_zero 1)
      have hBw : (B : GL (HypIndex s ε) K) • w ∈ W := fun t ht => by
        have h1 := hSN B⁻¹ t ht
        have e : (t : GL (HypIndex s ε) K) * (B : GL (HypIndex s ε) K) =
            (B : GL (HypIndex s ε) K) * ((B : GL (HypIndex s ε) K)⁻¹ * t *
              (B : GL (HypIndex s ε) K)) := by group
        have h2 : ((B⁻¹ : hypSU h s ε) : GL (HypIndex s ε) K) * t *
            ((B⁻¹ : hypSU h s ε) : GL (HypIndex s ε) K)⁻¹ =
            (B : GL (HypIndex s ε) K)⁻¹ * t * (B : GL (HypIndex s ε) K) := by
          rw [Subgroup.coe_inv, inv_inv]
        rw [h2] at h1
        have h3 := hw _ h1
        change (t : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ
          ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ w =
          ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ w
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, e, Units.val_mul, ← Matrix.mulVec_mulVec, h3]
      have h4 : ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ w =
          w + (1 * hypForm h s ε v w) • v := by
        rw [hB, tvMat_mulVec]
      have h5 := W.sub_mem hBw hw
      change ((B : GL (HypIndex s ε) K) : Matrix (HypIndex s ε) (HypIndex s ε) K) *ᵥ w - w ∈ W
        at h5
      rwa [h4, add_sub_cancel_left, one_mul] at h5
  refine (Subgroup.eq_bot_iff_forall _).2 fun t ht => ?_
  refine Units.ext ?_
  rw [Units.val_one]
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [Matrix.one_mulVec]
  have hv : v ∈ W := by rw [hWtop]; exact Submodule.mem_top
  exact hv t ht

end Residual

section Levi

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ}

theorem le_ker_uniLeviHom_of_normal_isPGroup (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : IsTopCut I t) (R : Subgroup ↥(flagStabilizer h (t + s) ε ↑I))
    [R.Normal] (hR : IsPGroup 2 R) : R ≤ (uniLeviHom (s := s) h hε hI).ker := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  intro r hr
  rw [MonoidHom.mem_ker]
  funext j
  rcases j with _ | b
  · show resBlockHom h hε (Finset.mem_coe.mpr hI.mem) r = 1
    have hT : R.map (resBlockHom h hε (Finset.mem_coe.mpr hI.mem)) = ⊥ := by
      refine eq_bot_of_isPGroup_of_normalized_hypSU h hε (hR.map _) fun B t' ht' => ?_
      have hmem : (Pi.mulSingle (M := uniBlockGroup K s ε I) none (B : GL (HypIndex s ε) K) :
          ∀ k, uniBlockGroup K s ε I k) ∈ (uniLeviHom (s := s) h hε hI).range := by
        refine pi_uniBlockSub_le_range h hε hI ((Subgroup.mem_pi _).mpr fun k _ => ?_)
        by_cases hk : k = none
        · subst hk
          rw [Pi.mulSingle_eq_same]
          exact B.2
        · rw [Pi.mulSingle_eq_of_ne hk]
          exact one_mem _
      obtain ⟨x, hx⟩ := hmem
      have hxB : resBlockHom h hε (Finset.mem_coe.mpr hI.mem) x = (B : GL (HypIndex s ε) K) := by
        have := congrFun hx none
        rw [Pi.mulSingle_eq_same] at this
        exact this
      obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp ht'
      refine ⟨x * r' * x⁻¹, Subgroup.Normal.conj_mem inferInstance r' hr' x, ?_⟩
      rw [map_mul, map_mul, map_inv, hxB]
    have : resBlockHom h hε (Finset.mem_coe.mpr hI.mem) r ∈
        R.map (resBlockHom h hε (Finset.mem_coe.mpr hI.mem)) := ⟨r, hr, rfl⟩
    rw [hT] at this
    exact this
  · have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
    have hb1 : 1 ≤ b.1 := (hI.le b.1 b.2).1
    show eBlockHom h hε b.2 hb1 hbr r = 1
    have hT : R.map (eBlockHom h hε b.2 hb1 hbr) = ⊥ := by
      refine Lin.eq_bot_of_isPGroup_of_normalized_range_toGL (hR.map _) ?_
      rintro σ hσ _ ⟨r', hr', rfl⟩
      have hmem : (Pi.mulSingle (M := uniBlockGroup K s ε I) (some b) σ :
          ∀ k, uniBlockGroup K s ε I k) ∈ (uniLeviHom (s := s) h hε hI).range := by
        refine pi_uniBlockSub_le_range h hε hI ((Subgroup.mem_pi _).mpr fun k _ => ?_)
        by_cases hk : k = some b
        · subst hk
          rw [Pi.mulSingle_eq_same]
          exact hσ
        · rw [Pi.mulSingle_eq_of_ne hk]
          exact one_mem _
      obtain ⟨x, hx⟩ := hmem
      have hxB : eBlockHom h hε b.2 hb1 hbr x = σ := by
        have := congrFun hx (some b)
        rw [Pi.mulSingle_eq_same] at this
        exact this
      refine ⟨x * r' * x⁻¹, Subgroup.Normal.conj_mem inferInstance r' hr' x, ?_⟩
      rw [map_mul, map_mul, map_inv, hxB]
    have : eBlockHom h hε b.2 hb1 hbr r ∈ R.map (eBlockHom h hε b.2 hb1 hbr) := ⟨r, hr, rfl⟩
    rw [hT] at this
    exact this

end Levi

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
