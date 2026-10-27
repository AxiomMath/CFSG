module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUTools
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (compInd compInd_mul_apply mul_compInd_apply
  compInd_apply commute_compInd_iff commute_compInd_compl signMat commute_signMat_iff
  commutator_eq_self_of_isQuasisimple mul_conj_mul_inv)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ClU.split_core (hgen : ClU.UBlockThreeGen) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J)
    {R : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * uConjAut h (by omega) (uSign h J) = uConjAut h (by omega) (uSign h J) * y)
    (hRc : ∀ s, uConjAut h (by omega) (uSign h J) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    {y : MulAut (StatedProj (StatedSU n (p ^ f) K))} (hy : y ∈ R) :
    ∃ (α β : Kˣ) (hα : h.norm (α : K) = 1) (hβ : h.norm (β : K) = 1),
      y = uConjAut h (by omega) (uDiagJ h J α β hα hβ) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  have hcard : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  have hyBC := hRi _ hy
  obtain ⟨D, φ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq y
  have hφm : φ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) φ) = 1 :=
    fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
  have hlift : ∀ g : StatedSU n (p ^ f) K,
      (uConjAut h (by omega) (uSign h J)) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) (uLift h (uSign h J) 1 g) := by
    intro g
    rw [← uLift_proj h (by omega) (uSign h J) 1 g, map_one, mul_one]
  have hliftinj : Function.Injective (uLift h (uSign h J) 1) := by
    intro g₁ g₂ e
    have e' : ((uSign h J : uU h n) : GL (Fin n) K) * (g₁ : GL (Fin n) K) *
        ((uSign h J : uU h n) : GL (Fin n) K)⁻¹ = ((uSign h J : uU h n) : GL (Fin n) K) *
        (g₂ : GL (Fin n) K) * ((uSign h J : uU h n) : GL (Fin n) K)⁻¹ := by
      apply Units.ext
      have := congrArg (fun g : StatedSU n (p ^ f) K =>
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e
      simpa only [coe_uLift, map_one_ringEquiv, Units.val_mul] using this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel e'))
  have hmiss : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → ∃ k, k ∉ I := by
    rintro I (rfl | rfl)
    · exact ⟨b, hb⟩
    · exact ⟨a, by simpa using ha⟩
  have hQF : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      uBlock p f K I ≤
        MonoidHom.eqLocus (uLift h (uSign h J) 1) (MonoidHom.id (StatedSU n (p ^ f) K)) := by
    intro I hI g hg
    exact (uLift_sign_eq_iff h h2 J g).2
      (commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg))
  have hQn : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      ∀ x ∈ MonoidHom.eqLocus (uLift h (uSign h J) 1) (MonoidHom.id (StatedSU n (p ^ f) K)),
        ∀ g ∈ uBlock p f K I,
        x * g * x⁻¹ ∈ uBlock p f K I := by
    intro I hI x hx g hg
    have hxc := commute_compInd_of_or hI ((uLift_sign_eq_iff h h2 J x).1 hx)
    refine conj_mem_uBlock (D := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Di := (((x⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      ?_ ?_ hxc hg ?_
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hcomp : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → 2 ≤ I.card →
      (3 ≤ I.card ∨ 5 ≤ p ^ f) → ∀ g ∈ uBlock p f K I,
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ *
          (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro I hI h2I hqI g hg
    have hQ := isQuasisimple_uBlock h hp2 h2I hqI
    exact uSemilinear_eq_of_fix h (by omega) (commutator_eq_self_of_isQuasisimple hQ)
      (fun g' hg' => ClU.fix_of_lift hinj hRodd hRi hRc (uLift h (uSign h J) 1) hliftinj hlift
        (hQF hI) (hQn hI) hQ hy hg') hg
  have hφ : φ = 1 := by
    refine eq_one_of_odd_of_fix h hodd hφm ?_
    rcases hcard with h3 | h5
    · intro c hc
      rcases mem_three_of_bar h h3 hc with rfl | rfl | rfl <;> simp
    · obtain ⟨I, hI, h2I⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ 2 ≤ I.card := by
        have hsum : J.card + Jᶜ.card = n := by
          rw [Finset.card_compl, Fintype.card_fin]
          have := Finset.card_le_univ J
          rw [Fintype.card_fin] at this
          omega
        by_cases hJ : 2 ≤ J.card
        · exact ⟨J, Or.inl rfl, hJ⟩
        · exact ⟨Jᶜ, Or.inr rfl, by omega⟩
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h2I
      obtain ⟨μ, hμ⟩ := exists_norm_neg_one h
      obtain ⟨η, hη0, hη⟩ := exists_skew h
      set v : Fin n → K := Pi.single i 1 + Pi.single j μ with hv
      have hvI : ∀ x, x ∉ I → v x = 0 := by
        intro x hx
        have hxi : x ≠ i := fun e => hx (e ▸ hi)
        have hxj : x ≠ j := fun e => hx (e ▸ hj)
        simp [hv, hxi, hxj]
      have hiso : (fun k => h.bar (v k)) ⬝ᵥ v = 0 := by
        rw [dotProduct, Finset.sum_eq_add i j hij (fun c _ hc => by
          simp [hv, hc.1, hc.2]) (by simp) (by simp)]
        simp only [hv, Pi.add_apply, Pi.single_apply, Ne.symm hij, hij, ↓reduceIte, add_zero,
          zero_add, map_one, mul_one]
        rw [mul_comm, ← UnitaryFieldData.norm, hμ]
        ring
      set N : Matrix (Fin n) (Fin n) K := η • vecMulVec v (fun k => h.bar (v k)) with hN
      have hNii : N i i ≠ 0 := by
        simp only [hN, Matrix.smul_apply, vecMulVec_apply, hv, Pi.add_apply, Pi.single_apply,
          hij, ↓reduceIte, add_zero, map_one, mul_one, smul_eq_mul]
        exact hη0
      refine fix_of_conj_family h (D := (D : GL (Fin n) K)) (a := i) (b := i) hNii
        fun c hc => ?_
      obtain ⟨g, hg⟩ := exists_uTr h hiso (η := c * η) (by rw [map_mul, hc, hη]; ring)
      have hgI : g ∈ uBlock p f K I := by
        rw [mem_uBlock_iff]
        intro x z hxz
        rw [hg, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply]
        rcases hxz with hx | hz
        · rw [hvI x hx]
          simp [one_apply]
        · rw [hvI z hz]
          simp [one_apply]
      have e := hcomp hI h2I (Or.inr h5) g hgI
      rw [hg] at e
      have e' : (1 : Matrix (Fin n) (Fin n) K) + (c * η) • vecMulVec v (fun k => h.bar (v k)) =
          1 + c • N := by rw [hN, smul_smul]
      rwa [e'] at e
  subst hφ
  simp only [map_one, mul_one] at hodd hyBC hy ⊢
  set Dm := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDm
  set Dmi := (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDmi
  have hDD : Dm * Dmi = 1 := by rw [hDm, hDmi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : Dmi * Dm = 1 := by rw [hDm, hDmi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcD : D * uSign h J = uSign h J * D :=
    uCommute_of_odd h hn (by rw [uSign_mul_self, map_one]) hodd
      hyBC
  have hcJ : compInd K J * Dm = Dm * compInd K J := by
    have e := congrArg (fun x : uU h n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hcD
    simp only [Subgroup.coe_mul, Units.val_mul, coe_uSign] at e
    exact (commute_signMat_iff h2 J _).1 e.symm
  have hblock : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) → ∀ x ∈ I, ∀ z ∈ I,
      (x ≠ z → Dm x z = 0) ∧ Dm x x = Dm z z := by
    intro I hI x hx z hz
    by_cases hxz : x = z
    · subst hxz
      exact ⟨fun e => absurd rfl e, rfl⟩
    have h2I : 2 ≤ I.card := Finset.one_lt_card.2 ⟨x, hx, z, hz, hxz⟩
    by_cases hqI : 3 ≤ I.card ∨ 5 ≤ p ^ f
    · have hc : ∀ g ∈ uBlock p f K I, Dm * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Dm := by
        intro g hg
        have e := hcomp hI h2I hqI g hg
        rw [map_one_ringEquiv] at e
        calc Dm * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            Dm * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Dmi * Dm) := by
              rw [hDiD, Matrix.mul_one]
          _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Dm := by
              rw [← Matrix.mul_assoc, e]
      obtain ⟨hoff, hdiag⟩ := eq_of_commute_uBlock h h2I hc
      exact ⟨fun _ => (hoff x hx z (Ne.symm hxz)).1, hdiag x hx z hz⟩
    · push Not at hqI
      have h3 : p ^ f = 3 := by omega
      have hIxz : I = {x, z} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hx
          · rw [Finset.mem_singleton.1 hw]
            exact hz
        · rw [Finset.card_pair hxz]
          omega
      subst hIxz
      have hcI := commute_compInd_of_or hI hcJ
      obtain ⟨k, hk⟩ := hmiss hI
      have hoddc : ∀ w ∈ uBlock p f K {x, z},
          Odd (orderOf ((⟨_, uConjSU_mem h D w⟩ : StatedSU n (p ^ f) K) * w⁻¹)) := by
        intro w hw
        have hwT : projH (StatedSU n (p ^ f) K) w ∈
            closure {s | uConjAut h (by omega) (uSign h J) s = s ∧ Odd (orderOf s)} := by
          have hw' := hgen h h3 x z hxz hw
          have hle : (closure {g | g ∈ uBlock p f K {x, z} ∧ Odd (orderOf g)}).map
              (projH (StatedSU n (p ^ f) K)) ≤
              closure {s | uConjAut h (by omega) (uSign h J) s = s ∧ Odd (orderOf s)} := by
            rw [MonoidHom.map_closure, closure_le]
            rintro _ ⟨g, ⟨hgB, hgo⟩, rfl⟩
            refine subset_closure ⟨?_, Odd.of_dvd_nat hgo (orderOf_map_dvd _ g)⟩
            rw [hlift]
            exact congrArg _ (hQF hI hgB)
          exact hle ⟨w, hw', rfl⟩
        have hmem := ClU.commutator_mem hRc hwT hy
        change uConjAut h (by omega) D * conjProjH (StatedSU n (p ^ f) K) w *
          (uConjAut h (by omega) D)⁻¹ * (conjProjH (StatedSU n (p ^ f) K) w)⁻¹ ∈ R at hmem
        have hz : uConjAut h (by omega) D * conjProjH (StatedSU n (p ^ f) K) w *
            (uConjAut h (by omega) D)⁻¹ * (conjProjH (StatedSU n (p ^ f) K) w)⁻¹ =
            conjProjH (StatedSU n (p ^ f) K)
              ((⟨_, uConjSU_mem h D w⟩ : StatedSU n (p ^ f) K) * w⁻¹) := by
          have e1 : uConjAut h (by omega) D * conjProjH (StatedSU n (p ^ f) K) w *
              (uConjAut h (by omega) D)⁻¹ =
                conjProjH (StatedSU n (p ^ f) K) ⟨_, uConjSU_mem h D w⟩ := by
            change uConjAut h (by omega) D * MulAut.conj (projH _ w) *
              (uConjAut h (by omega) D)⁻¹ = MulAut.conj (projH _ _)
            rw [mul_conj_mul_inv, uConjAut_proj]
          rw [e1, map_mul, map_inv]
        rw [hz] at hmem
        have ho := ClSp.odd_orderOf_of_mem hRodd hmem
        have hzm : (⟨_, uConjSU_mem h D w⟩ : StatedSU n (p ^ f) K) * w⁻¹ ∈
            uBlock p f K {x, z} :=
          mul_mem (conj_mem_uBlock hDD hDiD hcI hw rfl) (inv_mem hw)
        have e := orderOf_injective _ (conjProjH_uBlock_injective hk hinj)
          (⟨_, hzm⟩ : uBlock p f K {x, z})
        rw [Subgroup.orderOf_mk] at e
        rw [← e]
        exact ho
      obtain ⟨e1, -, e3⟩ := uThree_block h h3 hxz hcI hoddc
      exact ⟨fun _ => e1, e3⟩
  have hJ : J = J ∨ J = Jᶜ := Or.inl rfl
  have hJc : Jᶜ = J ∨ Jᶜ = Jᶜ := Or.inr rfl
  have hcross : ∀ x z, (x ∈ J ↔ z ∉ J) → Dm x z = 0 := (commute_compInd_iff J Dm).1 hcJ
  have hdiag : Dm = diagonal fun k => if k ∈ J then Dm a a else Dm b b := by
    ext x z
    by_cases hxz : x = z
    · subst hxz
      rw [diagonal_apply_eq]
      split_ifs with hx
      · exact (hblock hJ x hx a ha).2
      · exact (hblock hJc x (Finset.mem_compl.2 hx) b (Finset.mem_compl.2 hb)).2
    · rw [diagonal_apply_ne _ hxz]
      by_cases hx : x ∈ J <;> by_cases hz : z ∈ J
      · exact (hblock hJ x hx z hz).1 hxz
      · exact hcross x z (iff_of_true hx hz)
      · exact hcross x z (iff_of_false hx (not_not.2 hz))
      · exact (hblock hJc x (Finset.mem_compl.2 hx) z (Finset.mem_compl.2 hz)).1 hxz
  have hU : (Dm.map h.bar)ᵀ * Dm = 1 := (mem_uU h).1 D.2
  have hnorm : ∀ k, h.norm (if k ∈ J then Dm a a else Dm b b) = 1 := by
    intro k
    have e := congrFun (congrFun hU k) k
    rw [hdiag, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq] at e
    rw [UnitaryFieldData.norm, mul_comm]
    exact e
  have hna : h.norm (Dm a a) = 1 := by simpa [ha] using hnorm a
  have hnb : h.norm (Dm b b) = 1 := by simpa [hb] using hnorm b
  have h0 : ∀ c : K, h.norm c = 1 → c ≠ 0 := fun c hc h0 => by
    rw [h0, UnitaryFieldData.norm, zero_mul] at hc
    exact zero_ne_one hc
  refine ⟨Units.mk0 (Dm a a) (h0 _ hna), Units.mk0 (Dm b b) (h0 _ hnb), hna, hnb, ?_⟩
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_uDiagJ]
  simp only [Units.val_mk0]
  exact hdiag

end CFSG.ComponentClassification.Foote5.OddLieCore
