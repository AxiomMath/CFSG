module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidComm

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

theorem eq_bot_of_normal_isPGroup_two {Q : Type*} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) (hs : IsSimpleGroup (Q ⧸ center Q))
    (hZ : Odd (Nat.card (center Q))) {N : Subgroup Q} [hN : N.Normal] (h2 : IsPGroup 2 N) :
    N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Q) with hπ
  have hNmap : (N.map π).Normal := hN.map _ (QuotientGroup.mk'_surjective _)
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  ·
    have hle : N ≤ center Q := by
      rw [← QuotientGroup.ker_mk' (center Q), ← Subgroup.map_eq_bot_iff]
      exact hbot
    rw [← Subgroup.card_eq_one]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    have hdvd : Nat.card N ∣ Nat.card (center Q) := Subgroup.card_dvd_of_le hle
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exfalso
      have : 2 ∣ Nat.card (center Q) := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr this)
  ·
    exfalso
    have h2' : IsPGroup 2 (Q ⧸ center Q) := by
      have := h2.map π
      rw [htop] at this
      exact this.of_equiv Subgroup.topEquiv
    have : Nontrivial (Q ⧸ center Q) := hs.toNontrivial
    have hc := h2'.center_nontrivial
    have hctop : center (Q ⧸ center Q) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left
        ((Subgroup.nontrivial_iff_ne_bot _).mp hc)
    have hcomm : commutator Q ≤ center Q := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_commutatorElement]
      have hb : π b ∈ center (Q ⧸ center Q) := by rw [hctop]; trivial
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hb (π a))
    rw [hperf] at hcomm
    obtain ⟨x, y, hxy⟩ := hs.toNontrivial.exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center Q) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center Q) y
    apply hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hcomm trivial

variable {K : Type} [Field K] {ε f : ℕ}

@[expose] def zBlock (g : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) : Matrix (Fin ε) (Fin ε) K :=
  Matrix.of fun k l => g (.inr (.inl k)) (.inr (.inl l))

theorem zBlock_eichM_mul_blkZM (σ : K →+* K) (a : Fin ε → K) (c : K)
    (C : Matrix (Fin ε) (Fin ε) K) : zBlock (eichM σ a c * blkZM C) = C := by
  ext k l
  simp [zBlock, eichM, blkZM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero]

variable (h : UnitaryFieldData 2 f K)

theorem zBlock_mul [CharP K 2] {g g' : hypSU h 1 ε} (hg : g ∈ stabE h) (hg' : g' ∈ stabE h) :
    zBlock (((g * g' : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
      Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
      zBlock ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) *
        zBlock ((g' : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) := by
  obtain ⟨a, c, hc, C, rfl⟩ := exists_eq_eich_mul_blkZHom h hg
  obtain ⟨a', c', hc', C', rfl⟩ := exists_eq_eich_mul_blkZHom h hg'
  have hCu := ((mem_unitarySU_iff h).mp C.2).2
  simp only [Subgroup.coe_mul, Units.val_mul, coe_eich, coe_blkZHom]
  rw [show eichM h.bar a c * blkZM ((C : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *
      (eichM h.bar a' c' * blkZM ((C' : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K)) =
      eichM h.bar a c * (blkZM ((C : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) *
        eichM h.bar a' c') * blkZM ((C' : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) by
    simp only [Matrix.mul_assoc]]
  rw [blkZM_mul_eichM h.bar hCu, ← Matrix.mul_assoc, eichM_mul, Matrix.mul_assoc, blkZM_mul,
    zBlock_eichM_mul_blkZM, zBlock_eichM_mul_blkZM, zBlock_eichM_mul_blkZM]

theorem zBlock_one :
    zBlock (1 : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = 1 := by
  ext k l
  simp [zBlock, one_apply]

theorem exists_zBlock_eq [CharP K 2] {g : hypSU h 1 ε} (hg : g ∈ stabE h) :
    ∃ C : StatedSU ε (2 ^ f) K, ((C : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) =
      zBlock ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) := by
  obtain ⟨a, c, hc, C, rfl⟩ := exists_eq_eich_mul_blkZHom h hg
  refine ⟨C, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, coe_eich, coe_blkZHom]
  rw [zBlock_eichM_mul_blkZM]

@[expose] noncomputable def zBlockGL [CharP K 2] (g : stabE (ε := ε) h) : GL (Fin ε) K :=
  ⟨zBlock (((g : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix _ _ K),
    zBlock ((((g : hypSU h 1 ε)⁻¹ : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix _ _ K),
    by rw [← zBlock_mul h g.2 (inv_mem g.2), mul_inv_cancel]; exact zBlock_one,
    by rw [← zBlock_mul h (inv_mem g.2) g.2, inv_mul_cancel]; exact zBlock_one⟩

theorem zBlockGL_mem [CharP K 2] (g : stabE (ε := ε) h) :
    zBlockGL h g ∈ StatedSU ε (2 ^ f) K := by
  obtain ⟨C, hC⟩ := exists_zBlock_eq h g.2
  convert C.2 using 1
  exact Units.ext hC.symm

@[expose] noncomputable def zBlockHom [CharP K 2] : stabE (ε := ε) h →* StatedSU ε (2 ^ f) K where
  toFun g := ⟨zBlockGL h g, zBlockGL_mem h g⟩
  map_one' := Subtype.ext (Units.ext zBlock_one)
  map_mul' g g' := Subtype.ext (Units.ext (zBlock_mul h g.2 g'.2))

theorem coe_zBlockHom [CharP K 2] (g : stabE (ε := ε) h) :
    (((zBlockHom h g : StatedSU ε (2 ^ f) K) : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) =
      zBlock (((g : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix _ _ K) := rfl

theorem zBlockHom_blkZHom [CharP K 2] (C : StatedSU ε (2 ^ f) K) :
    zBlockHom h ⟨blkZHom h C, blkZHom_mem_stabE h C⟩ = C := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_zBlockHom, coe_blkZHom]
  ext k l
  simp [zBlock, blkZM]

theorem zBlockHom_surjective [CharP K 2] : Function.Surjective (zBlockHom (ε := ε) h) :=
  fun C => ⟨_, zBlockHom_blkZHom h C⟩

theorem mem_ker_zBlockHom [CharP K 2] (g : stabE (ε := ε) h) :
    g ∈ (zBlockHom h).ker ↔ (g : hypSU h 1 ε) ∈ eichSub h := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    obtain ⟨a, c, hc, C, hgC⟩ := exists_eq_eich_mul_blkZHom h g.2
    have h1 := congrArg (fun x : StatedSU ε (2 ^ f) K =>
      ((x : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K)) hg
    simp only [coe_zBlockHom, OneMemClass.coe_one, Units.val_one] at h1
    rw [hgC] at h1
    simp only [Subgroup.coe_mul, Units.val_mul, coe_eich, coe_blkZHom,
      zBlock_eichM_mul_blkZM] at h1
    refine ⟨a, c, ?_⟩
    rw [hgC]
    simp only [Subgroup.coe_mul, Units.val_mul, coe_eich, coe_blkZHom, h1, blkZM_one,
      Matrix.mul_one]
  · rintro ⟨a, c, hac⟩
    refine Subtype.ext (Units.ext ?_)
    rw [coe_zBlockHom, hac]
    simpa [blkZM_one] using zBlock_eichM_mul_blkZM h.bar a c 1

include h in
theorem eq_bot_of_normal_statedSU [Finite K] [CharP K 2] (hf : 2 ≤ f) (hε : 2 ≤ ε)
    {N : Subgroup (StatedSU ε (2 ^ f) K)} [N.Normal] (h2 : IsPGroup 2 N) : N = ⊥ :=
  eq_bot_of_normal_isPGroup_two (commutator_statedSU h.card_eq_sq hf hε)
    (isQuasisimple_statedSU_of_two_le h.card_eq_sq hf hε).2.1
    (odd_card_center_statedSU h.card_eq_sq hf hε) h2

abbrev smat (g : stabE (ε := ε) h) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K :=
  (((g : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K)

noncomputable abbrev rmat [CharP K 2] (g : stabE (ε := ε) h) : Matrix (Fin ε) (Fin ε) K :=
  (((zBlockHom h g : StatedSU ε (2 ^ f) K) : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K)

@[expose] def avec (g : stabE (ε := ε) h) : Fin ε → K :=
  fun k => smat h g (.inr (.inl k)) hF

omit [Field K] in
theorem eichM_mul_blkZM_apply_z_f [Field K] (σ : K →+* K) (a : Fin ε → K) (c : K)
    (C : Matrix (Fin ε) (Fin ε) K) (k : Fin ε) :
    (eichM σ a c * blkZM C) (.inr (.inl k)) hF = a k := by
  simp [eichM, blkZM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero]

theorem exists_eq_eichM_avec [CharP K 2] (g : stabE (ε := ε) h) :
    ∃ c : K, smat h g = eichM h.bar (avec h g) c * blkZM (rmat h g) := by
  obtain ⟨a, c, hc, C, hgC⟩ := exists_eq_eich_mul_blkZHom h g.2
  have hM : smat h g =
      eichM h.bar a c * blkZM ((C : GL (Fin ε) K) : Matrix (Fin ε) (Fin ε) K) := by
    rw [smat, hgC]
    rfl
  refine ⟨c, ?_⟩
  have ha : avec h g = a := funext fun k => by
    simp only [avec, hM, eichM_mul_blkZM_apply_z_f]
  rw [ha, rmat, coe_zBlockHom, ← smat, hM, zBlock_eichM_mul_blkZM]

theorem smat_mul (g g' : stabE (ε := ε) h) : smat h (g * g') = smat h g * smat h g' := rfl

theorem avec_mul [CharP K 2] (g g' : stabE (ε := ε) h) :
    avec h (g * g') = avec h g + rmat h g *ᵥ avec h g' := by
  obtain ⟨c, hc⟩ := exists_eq_eichM_avec h g
  obtain ⟨c', hc'⟩ := exists_eq_eichM_avec h g'
  have hCu := ((mem_unitarySU_iff h).mp (zBlockHom h g).2).2
  funext k
  simp only [avec, smat_mul, hc, hc']
  rw [show eichM h.bar (avec h g) c * blkZM (rmat h g) *
      (eichM h.bar (avec h g') c' * blkZM (rmat h g')) =
      eichM h.bar (avec h g) c * (blkZM (rmat h g) * eichM h.bar (avec h g') c') *
        blkZM (rmat h g') by simp only [Matrix.mul_assoc],
    blkZM_mul_eichM h.bar hCu, ← Matrix.mul_assoc, eichM_mul, Matrix.mul_assoc, blkZM_mul,
    eichM_mul_blkZM_apply_z_f, Pi.add_apply]

section Avec

variable [CharP K 2]

omit [CharP K 2] in
theorem avec_one : avec h (1 : stabE (ε := ε) h) = 0 := by
  funext k
  simp [avec, smat, one_apply]

theorem avec_inv (g : stabE (ε := ε) h) : avec h g⁻¹ = -(rmat h g⁻¹ *ᵥ avec h g) := by
  have h1 := avec_mul h g⁻¹ g
  rw [inv_mul_cancel, avec_one] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

theorem avec_conj {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker) (s : stabE (ε := ε) h) :
    avec h (s * x * s⁻¹) = rmat h s *ᵥ avec h x := by
  have hx1 : rmat h x = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hx]
    rfl
  have hss := avec_mul h s s⁻¹
  rw [mul_inv_cancel, avec_one] at hss
  have hrm : rmat h (s * x) = rmat h s := by
    rw [rmat, map_mul, Subgroup.coe_mul, Units.val_mul, ← rmat, ← rmat, hx1, Matrix.mul_one]
  rw [avec_mul, avec_mul, hrm, add_right_comm, ← hss, zero_add]

theorem avec_mul_of_mem_ker {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    (y : stabE (ε := ε) h) : avec h (x * y) = avec h x + avec h y := by
  have hx1 : rmat h x = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hx]
    rfl
  rw [avec_mul, hx1, one_mulVec]

theorem exists_mem_ker_avec_eq (v : Fin ε → K) :
    ∃ x ∈ (zBlockHom (ε := ε) h).ker, avec h x = v := by
  obtain ⟨c, hc⟩ := exists_valid h v
  refine ⟨⟨eich h hc, eich_mem_stabE h hc⟩, (mem_ker_zBlockHom h _).mpr (eich_mem_eichSub h hc),
    ?_⟩
  funext k
  simp [avec, smat, coe_eich, eichM]

theorem exists_eichM_zero_of_avec {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    (hx0 : avec h x = 0) : ∃ c : K, smat h x = eichM h.bar 0 c := by
  obtain ⟨c, hc⟩ := exists_eq_eichM_avec h x
  refine ⟨c, ?_⟩
  rw [hc, hx0]
  have hx1 : rmat h x = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hx]
    rfl
  rw [hx1, blkZM_one, Matrix.mul_one]

theorem commute_of_avec_eq_zero {x : stabE (ε := ε) h} (hx : x ∈ (zBlockHom h).ker)
    (hx0 : avec h x = 0) (g : stabE (ε := ε) h) : x * g = g * x := by
  obtain ⟨c, hc⟩ := exists_eichM_zero_of_avec h hx hx0
  obtain ⟨c', hc'⟩ := exists_eq_eichM_avec h g
  have hCu := ((mem_unitarySU_iff h).mp (zBlockHom h g).2).2
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change smat h x * smat h g = smat h g * smat h x
  rw [hc, hc', Matrix.mul_assoc (eichM h.bar (avec h g) c'), blkZM_mul_eichM h.bar hCu,
    mulVec_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc, eichM_mul, eichM_mul]
  congr 2
  · simp
  · simp only [Pi.zero_apply, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    ring

@[expose] def tvSub : Subgroup (stabE (ε := ε) h) where
  carrier := {x | x ∈ (zBlockHom h).ker ∧ avec h x = 0}
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    exact ⟨mul_mem hx hy, by rw [avec_mul_of_mem_ker h hx, hx0, hy0, add_zero]⟩
  one_mem' := ⟨one_mem _, avec_one h⟩
  inv_mem' := by
    rintro x ⟨hx, hx0⟩
    exact ⟨inv_mem hx, by rw [avec_inv, hx0, mulVec_zero, neg_zero]⟩

theorem centralizer_inf_ker_eq_tvSub :
    centralizer ((zBlockHom (ε := ε) h).ker : Set (stabE (ε := ε) h)) ⊓ (zBlockHom h).ker =
      tvSub h := by
  apply le_antisymm
  · rintro x ⟨hxc, hx⟩
    refine ⟨hx, ?_⟩
    obtain ⟨d, hd⟩ := exists_eq_eichM_avec h x
    have hx1 : rmat h x = 1 := by
      rw [rmat, MonoidHom.mem_ker.mp hx]
      rfl
    rw [hx1, blkZM_one, Matrix.mul_one] at hd
    have key : ∀ v : Fin ε → K, ∑ k, h.bar (avec h x k) * v k = ∑ k, h.bar (v k) * avec h x k := by
      intro v
      obtain ⟨y, hy, hyv⟩ := exists_mem_ker_avec_eq h v
      obtain ⟨c, hc⟩ := exists_eq_eichM_avec h y
      have hy1 : rmat h y = 1 := by
        rw [rmat, MonoidHom.mem_ker.mp hy]
        rfl
      rw [hy1, blkZM_one, Matrix.mul_one, hyv] at hc
      have hxy := (mem_centralizer_iff.mp hxc) y hy
      have hm := congrArg (smat h) hxy
      rw [smat_mul, smat_mul, hc, hd, eichM_mul, eichM_mul] at hm
      have := congrFun (congrFun hm hE) hF
      simp only [eichM, of_apply] at this
      linear_combination -this
    funext k
    obtain ⟨θ, hθ⟩ := h.exists_bar_ne
    have h1 := key (Pi.single k 1)
    have h2 := key (Pi.single k θ)
    simp only [Pi.single_apply, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul] at h1 h2
    rw [h1] at h2
    have : (θ - h.bar θ) * avec h x k = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hθ))
  · rintro x ⟨hx, hx0⟩
    exact ⟨mem_centralizer_iff.mpr fun g _ => (commute_of_avec_eq_zero h hx hx0 g).symm, hx⟩

end Avec

end CFSG.ComponentClassification.RankTwoClassical.URigid
