module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOSgn
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QO2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL)

variable {K : Type} [Field K] {d : ℕ}

theorem mem_center_of_coe_eq_smul {H : Subgroup (GL (Fin d) K)} {s : H} {μ : K}
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = μ • 1) : s ∈ center H := by
  rw [mem_center_iff]
  intro t
  apply Subtype.ext
  apply Units.ext
  simp only [coe_mul, Units.val_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem exists_eq_smul_one_of_card_eq_one {n : ℕ} (hn : n = 1) (Y : Matrix (Fin n) (Fin n) K) :
    ∃ ν : K, Y = ν • 1 := by
  subst hn
  refine ⟨Y 0 0, ?_⟩
  ext a b
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
  simp

theorem sq_eq_one_of_smul_one_isometry {n : ℕ} (hn : 0 < n) {w : Fin n → K}
    (hw : ∀ i, w i ≠ 0) {ν : K}
    (h : (ν • (1 : Matrix (Fin n) (Fin n) K))ᵀ * diagonal w * (ν • 1) = diagonal w) :
    ν ^ 2 = 1 := by
  have e := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul] at e
  have h' : (ν ^ 2 - 1) * w ⟨0, hn⟩ = 0 := by linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right (hw _))

theorem det_smul_one_of_two {n : ℕ} (hn : n = 2) (ν : K) :
    (ν • (1 : Matrix (Fin n) (Fin n) K)).det = ν ^ 2 := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, hn]

theorem card_insert_four_le {β : Type*} [DecidableEq β] (a b c e : β) :
    ({a, b, c, e} : Finset β).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, e} : Finset β)
  have h2 := Finset.card_insert_le b ({c, e} : Finset β)
  have h3 := Finset.card_insert_le c ({e} : Finset β)
  rw [Finset.card_singleton] at h3
  omega

theorem exists_signMat_eq_blkScal {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) :
    ∃ ε c : K, signMat K J = blkScal K Iᶜ (ε • 1) c := by
  rcases hI with rfl | rfl
  · exact ⟨1, -1, by rw [one_smul]; exact signMat_eq_blkScal_compl _⟩
  · refine ⟨-1, 1, ?_⟩
    have h1 : signMat K J = (-1 : K) • signMat K Jᶜ := by
      ext x y
      simp only [signMat, diagonal_apply, Matrix.smul_apply, Finset.mem_compl, smul_eq_mul]
      split_ifs <;> simp_all
    rw [h1, signMat_eq_blkScal_compl Jᶜ, smul_blkScal, mul_neg, mul_one, neg_neg]

variable [Finite K]

theorem famF_concl_sign_of_block (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIc : Iᶜ.Nonempty) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    {X : Type} [Group X] [Finite X] (π : matrixDerived (oQ (diagGL hw)) →* X)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ∃ μ : K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = μ • 1)
    {P : Subgroup X} (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({π ⟨signGL K J, hJ⟩} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧
        ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π ⟨signGL K J, hJ⟩) ∧ ¬ ∀ q ∈ P, q * q = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hne1 : (-1 : K) ≠ 1 := fun e => h2 (by linear_combination -e)
  have hker' : ∀ s, π s = 1 → s ∈ center (matrixDerived (oQ (diagGL hw))) := fun s hs => by
    obtain ⟨μ, hμ⟩ := hker s hs
    exact mem_center_of_coe_eq_smul hμ
  set ℓ := Function.surjInv hπ with hℓdef
  have hℓ : ∀ g, π (ℓ g) = g := Function.surjInv_eq hπ
  have hinj : Function.Injective (fun s : matrixDerived (oQ (diagGL hw)) =>
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
    fun s t h => Subtype.ext (Units.ext h)
  have hlift : ∀ g ∈ P, ∃ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
      ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c ∧
        Yᵀ * diagonal (wRes w Iᶜ) * Y = diagonal (wRes w Iᶜ) ∧ c ^ 2 = 1 ∧
          Y.det * c ^ I.card = 1 := fun g hg =>
    lift_eq_blkScal hK hK3 hw hI hI3 hJ π hπ hker' (fun L hL he k hk => hP L hL he k hk g hg)
      (hℓ g)
  have hwR : ∀ i, wRes w Iᶜ i ≠ 0 := wRes_ne_zero hw Iᶜ
  have hcpos : 0 < Iᶜ.card := Finset.card_pos.2 hIc
  have hIcc : Iᶜᶜ.Nonempty := by
    rw [compl_compl]
    exact Finset.card_pos.1 (by omega)
  have hsq1 : ∀ {c : K}, c ^ 2 = 1 → c = 1 ∨ c = -1 := fun hc =>
    mul_self_eq_one_iff.1 (by rw [← sq]; exact hc)
  set T₀ : Finset (Matrix (Fin d) (Fin d) K) := {blkScal K Iᶜ 1 1, blkScal K Iᶜ 1 (-1),
    blkScal K Iᶜ (-1) 1, blkScal K Iᶜ (-1) (-1)} with hT₀
  have hT₀mem : ∀ {Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K} {c : K}, (Y = 1 ∨ Y = -1) →
      c ^ 2 = 1 → blkScal K Iᶜ Y c ∈ T₀ := by
    intro Y c hY hc
    rcases hY with rfl | rfl <;> rcases hsq1 hc with rfl | rfl <;> simp [hT₀]
  have hcard4 : ∀ T : Finset (Matrix (Fin d) (Fin d) K), T.card ≤ 4 →
      (∀ g ∈ P, ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈ T) → False := by
    intro T hT hmem
    have := card_le_of_forall_lift_mem π hinj T (fun g hg => ⟨ℓ g, hℓ g, hmem g hg⟩)
    omega
  have hscal : (∀ g ∈ P, ∀ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
      ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c → ∃ ν : K, Y = ν • 1) →
        False := by
    intro hs
    apply hcard4 T₀ (card_insert_four_le _ _ _ _)
    intro g hg
    obtain ⟨Y, c, hD, hY, hc, -⟩ := hlift g hg
    obtain ⟨ν, rfl⟩ := hs g hg Y c hD
    have hν := sq_eq_one_of_smul_one_isometry hcpos hwR hY
    rw [hD]
    refine hT₀mem ?_ hc
    rcases hsq1 hν with h | h
    · left
      rw [h, one_smul]
    · right
      rw [h, neg_one_smul]
  by_cases hn2 : Iᶜ.card ≠ 2
  · exfalso
    apply hscal
    intro g hg Y c hD
    rcases Nat.lt_or_ge Iᶜ.card 3 with h3 | h3
    · exact exists_eq_smul_one_of_card_eq_one (by omega) Y
    · have hIc' : Iᶜ = J ∨ Iᶜ = Jᶜ := by
        rcases hI with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (compl_compl _)
      obtain ⟨c', hc'⟩ := eq_of_commute_oBlock hK hw h3
        (commute_oBlock_of_lift hK hK3 hw hIc' h3 hJ π hπ hker'
          (fun L hL he k hk => hP L hL he k hk g hg) (hℓ g))
      refine ⟨c', ?_⟩
      ext a b
      have e := (hc' _ (Iᶜ.equivFin.symm a).2 (Iᶜ.equivFin.symm b)).1
      rw [hD, blkScal_apply_mem _ _ (Iᶜ.equivFin.symm a).2 (Iᶜ.equivFin.symm b).2] at e
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at e
      rw [e, Matrix.smul_apply, one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [ite_eq_right (fun h => hab (Iᶜ.equivFin.symm.injective (Subtype.ext h))),
          ite_eq_right hab, smul_zero]
  rw [not_not] at hn2
  have hdet1 : ∀ {Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K},
      Yᵀ * diagonal (wRes w Iᶜ) * Y = diagonal (wRes w Iᶜ) → Y.det = 1 ∨ Y.det = -1 :=
    fun hY => hsq1 (det_sq_eq_one_of_isometry hwR hY)
  have hz_scal : ∀ t ∈ P, (t = 1 ∨ t = π ⟨signGL K J, hJ⟩) →
      ∀ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
        ((ℓ t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c →
          Yᵀ * diagonal (wRes w Iᶜ) * Y = diagonal (wRes w Iᶜ) → Y.det = 1 := by
    intro t _ ht Y c hD hY
    obtain ⟨ν, c', hν⟩ : ∃ ν c' : K,
        ((ℓ t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ (ν • 1) c' := by
      rcases ht with rfl | rfl
      · obtain ⟨μ, hμ⟩ := hker _ (hℓ 1)
        exact ⟨μ, μ, by rw [hμ, smul_one_eq_blkScal]⟩
      · have h1 : π (ℓ (π ⟨signGL K J, hJ⟩) * (⟨signGL K J, hJ⟩)⁻¹) = 1 := by
          rw [map_mul, map_inv, hℓ, mul_inv_cancel]
        obtain ⟨μ, hμ⟩ := hker _ h1
        obtain ⟨ε, c₀, hε⟩ := exists_signMat_eq_blkScal (K := K) hI
        refine ⟨μ * ε, μ * c₀, ?_⟩
        have e : ((ℓ (π ⟨signGL K J, hJ⟩) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            μ • signMat K J := by
          have e2 : ℓ (π ⟨signGL K J, hJ⟩) =
              (ℓ (π ⟨signGL K J, hJ⟩) * (⟨signGL K J, hJ⟩)⁻¹) * ⟨signGL K J, hJ⟩ := by group
          rw [e2, Subgroup.coe_mul, Units.val_mul, hμ, Matrix.smul_mul, Matrix.one_mul,
            Subgroup.coe_mk, coe_signGL]
        rw [e, hε, smul_blkScal, smul_smul]
    obtain ⟨hY', -⟩ := blkScal_inj hIcc (hD.symm.trans hν)
    rw [hY'] at hY ⊢
    rw [det_smul_one_of_two hn2]
    exact sq_eq_one_of_smul_one_isometry hcpos hwR hY
  refine ⟨fun ⟨⟨u, hu, v, hv, huv⟩, huniq⟩ => ?_, fun hall => ?_⟩
  ·
    obtain ⟨Yu, cu, hDu, hYu, hcu, -⟩ := hlift u hu
    obtain ⟨Yv, cv, hDv, hYv, hcv, -⟩ := hlift v hv
    have hrefl : ∀ t ∈ P, ∀ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
        ((ℓ t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c →
          Yᵀ * diagonal (wRes w Iᶜ) * Y = diagonal (wRes w Iᶜ) → c ^ 2 = 1 → Y.det = -1 →
            False := by
      intro t ht Y c hD hY hc hd
      have hY2 := mul_self_eq_one_of_det_eq_neg_one hn2 hwR hY hd
      have htt : ℓ t * ℓ t = 1 := by
        refine Subtype.ext (Units.ext ?_)
        rw [Subgroup.coe_mul, Units.val_mul, hD, blkScal_mul, hY2, ← sq, hc, ← one_eq_blkScal,
          OneMemClass.coe_one, Units.val_one]
      have ht2 : t * t = 1 := by rw [← hℓ t, ← map_mul, htt, map_one]
      have h1 := hz_scal t ht (huniq t ht ht2) Y c hD hY
      rw [hd] at h1
      exact hne1 h1
    have hcomm : Yu * Yv ≠ Yv * Yu := by
      intro h
      apply huv
      rw [← hℓ u, ← hℓ v, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext (Units.ext ?_)
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hDu, hDv,
        blkScal_mul, blkScal_mul, h, mul_comm cu cv]
    rcases hdet1 hYu with hdu | hdu
    · rcases hdet1 hYv with hdv | hdv
      · exact hcomm (commute_of_det_eq_one hn2 hwR hYu hYv hdu hdv)
      · exact hrefl v hv Yv cv hDv hYv hcv hdv
    · exact hrefl u hu Yu cu hDu hYu hcu hdu
  ·
    have hsq : ∀ g ∈ P, ∀ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
        ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c → c ^ 2 = 1 →
          Y * Y = 1 := by
      intro g hg Y c hD hc
      have h1 : π (ℓ g * ℓ g) = 1 := by rw [map_mul, hℓ, hall g hg]
      obtain ⟨μ, hμ⟩ := hker _ h1
      have e : blkScal K Iᶜ (Y * Y) (c * c) = blkScal K Iᶜ (μ • 1) μ := by
        rw [← blkScal_mul, ← hD, ← smul_one_eq_blkScal, ← hμ, Subgroup.coe_mul, Units.val_mul]
      obtain ⟨hYY, hcc⟩ := blkScal_inj hIcc e
      rw [← sq, hc] at hcc
      rw [hYY, ← hcc, one_smul]
    have hcomm : ∀ g ∈ P, ∀ h ∈ P, ∀ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K)
        (Y' : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c' : K),
        ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c →
          ((ℓ h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y' c' →
            c ^ 2 = 1 → c' ^ 2 = 1 → Y * Y' = Y' * Y := by
      intro g hg h hh Y c Y' c' hD hD' hc hc'
      have hgh : g * h = h * g := by
        have hg1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hall g hg)
        have hh1 : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hall h hh)
        have hgh1 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right (hall _ (mul_mem hg hh))
        rw [← hgh1, _root_.mul_inv_rev, hg1, hh1]
      have h1 : π (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hℓ, hℓ, hgh, mul_inv_cancel]
      obtain ⟨μ, hμ⟩ := hker _ h1
      have e2 : ℓ g * ℓ h = (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹) * (ℓ h * ℓ g) := by group
      have e3 : ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((ℓ h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            μ • (((ℓ h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              ((ℓ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, e2,
          Subgroup.coe_mul _ (ℓ g * ℓ h * (ℓ h * ℓ g)⁻¹), Units.val_mul, hμ, Matrix.smul_mul,
          Matrix.one_mul, Subgroup.coe_mul, Units.val_mul]
      rw [hD, hD', blkScal_mul, blkScal_mul, smul_blkScal] at e3
      obtain ⟨hY, hcμ⟩ := blkScal_inj hIcc e3
      have hc0 : c * c' ≠ 0 := mul_ne_zero (fun h0 => by rw [h0] at hc; norm_num at hc)
        (fun h0 => by rw [h0] at hc'; norm_num at hc')
      have hμ1 : μ = 1 := by
        have h' : (1 - μ) * (c * c') = 0 := by linear_combination hcμ
        exact (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hc0)).symm
      rw [hY, hμ1, one_smul]
    by_cases hB : ∃ g₀ ∈ P, ∃ (Y₀ : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c₀ : K),
        ((ℓ g₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y₀ c₀ ∧
          Y₀ᵀ * diagonal (wRes w Iᶜ) * Y₀ = diagonal (wRes w Iᶜ) ∧ c₀ ^ 2 = 1 ∧
            Y₀.det * c₀ ^ I.card = 1 ∧ Y₀.det = -1
    · obtain ⟨g₀, hg₀, Y₀, c₀, hD₀, hY₀, hc₀, hdet₀, hd₀⟩ := hB
      have hodd : Odd I.card := by
        rcases Nat.even_or_odd I.card with hev | hodd
        · exfalso
          obtain ⟨k, hk⟩ := hev
          rw [hd₀, hk, ← two_mul, pow_mul, hc₀, one_pow, mul_one] at hdet₀
          exact hne1 hdet₀
        · exact hodd
      apply hcard4 {blkScal K Iᶜ 1 1, blkScal K Iᶜ (-1) 1, blkScal K Iᶜ Y₀ (-1),
        blkScal K Iᶜ (-Y₀) (-1)} (card_insert_four_le _ _ _ _)
      intro g hg
      obtain ⟨Y, c, hD, hY, hc, hdet⟩ := hlift g hg
      have hY2 := hsq g hg Y c hD hc
      have hcY := hcomm g hg g₀ hg₀ Y c Y₀ c₀ hD hD₀ hc hc₀
      have hcodd : c ^ I.card = c := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk, pow_succ, pow_mul, hc, one_pow, one_mul]
      rw [hcodd] at hdet
      rw [hD]
      rcases hdet1 hY with hd | hd
      · have hc1 : c = 1 := by rw [hd, one_mul] at hdet; exact hdet
        rcases eq_one_or_eq_neg_one_of_det_eq_one hn2 h2 hd hY2 with h | h <;> rw [h, hc1] <;>
          simp
      · have hc1 : c = -1 := by rw [hd] at hdet; linear_combination -hdet
        rcases eq_or_eq_neg_of_commute hn2 h2 hwR hY₀ hY hd₀ hd hcY.symm with h | h <;>
          rw [h, hc1] <;> simp
    · apply hcard4 T₀ (card_insert_four_le _ _ _ _)
      intro g hg
      obtain ⟨Y, c, hD, hY, hc, hdet⟩ := hlift g hg
      rw [hD]
      refine hT₀mem ?_ hc
      rcases hdet1 hY with hd | hd
      · exact eq_one_or_eq_neg_one_of_det_eq_one hn2 h2 hd (hsq g hg Y c hD hc)
      · exact absurd ⟨g, hg, Y, c, hD, hY, hc, hdet, hd⟩ hB

theorem famF_concl_sign (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3) (hd : 5 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hJne : J.Nonempty)
    (hJcne : Jᶜ.Nonempty) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    {X : Type} [Group X] [Finite X] (π : matrixDerived (oQ (diagGL hw)) →* X)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ∃ μ : K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = μ • 1)
    {P : Subgroup X} (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({π ⟨signGL K J, hJ⟩} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧
        ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π ⟨signGL K J, hJ⟩) ∧ ¬ ∀ q ∈ P, q * q = 1 := by
  by_cases h3 : 3 ≤ J.card
  · exact famF_concl_sign_of_block hK hK3 hw (Or.inl rfl) h3 hJcne hJ π hπ hker h8 hP
  · have h3' : 3 ≤ Jᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    exact famF_concl_sign_of_block hK hK3 hw (Or.inr rfl) h3' (by rwa [compl_compl]) hJ π hπ
      hker h8 hP

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
