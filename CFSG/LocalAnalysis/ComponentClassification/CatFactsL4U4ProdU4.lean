module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ProdL4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3T
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIProdDefs

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.HarrisLit.C3
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  UnitaryOut StabU DiagU HBlocks
open scoped MatrixGroups

theorem cfL4U4Prod_U4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq3 : ¬ (p = 3 ∧ f = 1)) (hU : Blueprint.LieModel Y .PSU 4 p f)
    (hq : p ^ f % 4 = 1) {t w : Y} (ht : orderOf t = 2) (hw : orderOf w = 2) (hwt : w ≠ t)
    {M : Subgroup Y} (hMt : M ≤ centralizer ({t} : Set Y))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))))
    (hMLie : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p (2 * f)) (hwM : w ∈ M) :
    ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ p' ^ n = p ^ f := by
  classical
  obtain ⟨-, K, _, _, hK', ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
  have : Finite K := h.finite
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    omega
  have htw : t * w = w * t := (mem_centralizer_singleton_iff.mp (hMt hwM)).symm
  have htw1 : t * w ≠ 1 := by
    intro h1
    apply hwt
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right ht2]
  have htw2 : t * w * (t * w) = 1 := by
    calc t * w * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [← htw]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht2, hw2, one_mul]
  obtain ⟨-, ⟨s, hs, hs2, hsq, -, hsM⟩, -⟩ := Cover82.jdata hp hp2 hf (Or.inl hMLie)
  have := Fact.mk hs
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) s hsM
  have hMp : ⁅M, M⁆ = M := commutator_eq_self_of_isPComponent hMt hM
  have hu1 : e t ≠ 1 := by rw [Ne, MulEquiv.map_eq_one_iff]; exact ht1
  have hu2 : e t ^ 2 = 1 := by rw [← map_pow, sq, ht2, map_one]
  have hv' : orderOf (e (v : Y)) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hv]
  have huv : e t * e (v : Y) = e (v : Y) * e t := by
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hMt v.2)).symm]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e t)
  have hkk := sq_eq_neg_one_of_comm_orderOf_U4 h hp2 hu1 hu2 hs hs2 hsq hv' huv k hk
  have hJ'k : M.map e.toMonoidHom ≤
      centralizer {(QuotientGroup.mk k : StatedProj (StatedSU 4 (p ^ f) K))} := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff, hk]
    change e m * e t = e t * e m
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hMt hm)]
  have hJ'p : ⁅M.map e.toMonoidHom, M.map e.toMonoidHom⁆ = M.map e.toMonoidHom := by
    rw [← map_commutator, hMp]
  have hw'J : e w ∈ M.map e.toMonoidHom := mem_map_of_mem _ hwM
  have hw'2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  have hw'1 : e w ≠ 1 := by rw [Ne, MulEquiv.map_eq_one_iff]; exact hw1
  obtain ⟨X, hXw, hXX⟩ :=
    exists_lift_sq_eq_neg_one_of_perfect_U4 h hp2 hq k hkk hJ'k hJ'p hw'J hw'2 hw'1
  have hXk : X * k = k * X :=
    ProdL4U4.comm_of_mk_mem_perfect (fun z hz => mem_center_of_mem_scal hz) hJ'k hJ'p
      (by rw [hXw]; exact hw'J)
  set Km := ((k : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hKm
  set Xm := ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hXm
  have hXk' : Xm * Km = Km * Xm := by
    have h1 := congrArg (fun A : unitarySU p f K 4 => ((A : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) hXk
    simpa using h1
  set T : unitarySU p f K 4 := k * X with hT
  have htt : ((T : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (T : GL (Fin 4) K) = 1 := by
    change Km * Xm * (Km * Xm) = 1
    calc Km * Xm * (Km * Xm) = Km * (Xm * Km) * Xm := by simp only [Matrix.mul_assoc]
      _ = Km * (Km * Xm) * Xm := by rw [hXk']
      _ = Km * Km * (Xm * Xm) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hkk, hXX, neg_mul_neg, Matrix.one_mul]
  set θ : unitarySU p f K 4 →* ↥(⊤ : Subgroup Y) :=
    (Subgroup.topEquiv.symm.toMonoidHom).comp (e.symm.toMonoidHom.comp (thU p f K)) with hθ
  have hθs : Function.Surjective θ :=
    Subgroup.topEquiv.symm.surjective.comp (e.symm.surjective.comp thU_surjective)
  have hθk : θ.ker ≤ center (unitarySU p f K 4) := by
    intro s hs
    have h1 : Subgroup.topEquiv.symm (e.symm (thU p f K s)) = 1 := MonoidHom.mem_ker.mp hs
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact mem_center_of_mem_scal h1
  have hθ1 : θ (negOneU h) = 1 := by
    change Subgroup.topEquiv.symm (e.symm (thU p f K (negOneU h))) = 1
    rw [thU_negOneU h, map_one, map_one]
  have hθT : ((θ T : ↥(⊤ : Subgroup Y)) : Y) = t * w := by
    change ((Subgroup.topEquiv.symm (e.symm (QuotientGroup.mk (k * X))) : ↥(⊤ : Subgroup Y)) :
      Y) = t * w
    rw [QuotientGroup.mk_mul, hk, hXw, ← map_mul, MulEquiv.symm_apply_apply]
    rfl
  have hns : ∀ c : Kˣ, ((T : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ (c : K) • 1 := by
    intro c hc
    have hmem : T ∈ scal p f K := by
      show (T : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
      refine ⟨c, Units.ext ?_⟩
      rw [GeneralLinearGroup.coe_scalar, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have h1 : θ T = 1 := by
      change Subgroup.topEquiv.symm (e.symm (thU p f K T)) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff T).mpr hmem, map_one, map_one]
    apply htw1
    rw [← hθT, h1]
    rfl
  have ht1' : ((T : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1 := fun h1 =>
    hns 1 (by rw [h1, Units.val_one, one_smul])
  have htm1' : ((T : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1 := fun h1 =>
    hns (-1) (by rw [h1, Units.val_neg, Units.val_one, neg_smul, one_smul])
  obtain ⟨R, s₀, hs0, -, hR, hXR⟩ := exists_frame_t2 h hp2 T htt ht1' htm1'
  have hF2 : ringChar h.fixedField ≠ 2 :=
    LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 h.card_fixedField
  have h2 : (2 : h.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  have hk2 : (-1 : SpecialLinearGroup (Fin 2) h.fixedField) ≠ 1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2
    linear_combination -this
  have hu1' : (uOne : SpecialLinearGroup (Fin 2) h.fixedField) ≠ 1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 1
    simp [uOne] at this
  have hun : (uOne : SpecialLinearGroup (Fin 2) h.fixedField) ≠ -1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
    simp only [uOne, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at this
    apply h2
    linear_combination this
  have hinter : ∀ a b, θ (blU h hR a) = θ (brU h hR b) →
      (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
    intro a b hab
    exact eq_of_bl_br_scalar h hR (e.symm.injective (Subgroup.topEquiv.symm.injective hab))
  have hn₁ : θ (blU h hR (-1)) = θ T ∧ θ (brU h hR (-1)) = θ T := by
    rw [blU_neg_one h hR hXR, brU_neg_one h hR hXR, map_mul, hθ1, one_mul]
    exact ⟨rfl, rfl⟩
  obtain ⟨X₁, X₂, -, h₁, -, hs₁, -, -, hi, ⟨e₁⟩, -⟩ :=
    x_alternative_abs hθs hθk (blU h hR) (brU h hR) (blU_comm h hR hXR) (brU_comm h hR hXR)
      (blU_mul_brU h hR) (fun n hn a => conj_mem_range_bl h hR hXR hp2 hs0 hn a)
      (fun n hn b => conj_mem_range_br h hR hXR hp2 hs0 hn b) hinter hn₁ hk2 hu1' hun
  rw [hθT, top_inf_eq] at h₁ hs₁
  rw [hθT] at hi
  have htwX : t * w ∈ X₁ := by
    have h1 : t * w ∈ X₁ ⊓ X₂ := by
      rw [hi]
      exact mem_zpowers _
    exact (mem_inf.mp h1).1
  have hF'n : Nat.card h.fixedField = p ^ f := h.card_fixedField
  obtain ⟨hpc, p', n, hp', hp'2, hn, he, hpn⟩ := ProdL4U4.exists_of_isSubnormal_sl2_card htw2
    htw1 h₁ hs₁ htwX hF2
    (by rw [hF'n]; exact (ProdL4U4.five_le_pow hp hp2 hf hq3).trans' (by norm_num)) e₁
  exact ⟨X₁, h₁, hpc, htwX, p', n, hp', hp'2, hn, he, hpn.trans hF'n⟩

theorem cfL4U4ProdCard : CFL4U4ProdCard := by
  intro Y _ _ p f hp hp2 hf hq3 hY t w ht hw hwt M hMt hM hMLie hwM
  rcases hY with ⟨hL, hq⟩ | ⟨hU, hq⟩
  · exact cfL4U4Prod_L4 hp hp2 hf hq3 hL hq ht hw hwt hMt hM hMLie hwM
  · exact cfL4U4Prod_U4 hp hp2 hf hq3 hU hq ht hw hwt hMt hM hMLie hwM

theorem cfL4U4Prod : CFL4U4Prod :=
  cfL4U4Prod_of_card cfL4U4ProdCard

end CFSG.ComponentClassification.CatFactsL4U4
