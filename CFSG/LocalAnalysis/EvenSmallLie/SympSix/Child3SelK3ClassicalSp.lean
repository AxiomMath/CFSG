module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3ClassicalSylow
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.EvenSmallLie.Child3.SelK3Classical

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem diag_eq_of_mem_statedScalars {M : GL ι K} (hM : M ∈ StatedScalars ι K) (i j : ι) :
    (M : Matrix ι ι K) i i = (M : Matrix ι ι K) j j := by
  obtain ⟨c, rfl⟩ := hM
  simp [Matrix.scalar_apply]

theorem offDiag_eq_zero_of_mem_statedScalars {M : GL ι K} (hM : M ∈ StatedScalars ι K)
    {i j : ι} (hij : i ≠ j) : (M : Matrix ι ι K) i j = 0 := by
  obtain ⟨c, rfl⟩ := hM
  simp [Matrix.scalar_apply, hij]

theorem glCongr_statedSp {L : Type} [Field L] (e : K ≃+* L) (n : ℕ) :
    (StatedSp n K).map (glCongr (ι := Fin n ⊕ Fin n) e).toMonoidHom = StatedSp n L :=
  CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp e n

end Scalars

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem statedProj_mk_eq_one_iff (x : H) :
    (x : StatedProj H) = 1 ↔ (x : GL ι K) ∈ StatedScalars ι K := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem statedProj_mk_eq_mk_iff (x y : H) :
    (x : StatedProj H) = y ↔ ((x⁻¹ * y : H) : GL ι K) ∈ StatedScalars ι K := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]

theorem orderOf_statedProj_mk {p : ℕ} [Fact p.Prime] {x : H}
    (hp : ((x ^ p : H) : GL ι K) ∈ StatedScalars ι K)
    (hx : (x : GL ι K) ∉ StatedScalars ι K) : orderOf (x : StatedProj H) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, statedProj_mk_eq_one_iff]
    exact hp
  · rwa [Ne, statedProj_mk_eq_one_iff]

theorem orderOf_statedProj_mk_eq_four {x : H} (h4 : x ^ 4 = 1)
    (h2 : ((x ^ 2 : H) : GL ι K) ∉ StatedScalars ι K) : orderOf (x : StatedProj H) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (x : StatedProj H)) ?_ ?_
  · simpa using h
  · rwa [pow_one, ← QuotientGroup.mk_pow, statedProj_mk_eq_one_iff]
  · rw [show 2 ^ (1 + 1) = 4 by rfl, ← QuotientGroup.mk_pow, h4, QuotientGroup.mk_one]

theorem statedProj_mk_eq_of_eq_mul {x y s : H} (h : x = y * s)
    (hs : (s : GL ι K) ∈ StatedScalars ι K) : (x : StatedProj H) = y := by
  rw [h, QuotientGroup.mk_mul, (statedProj_mk_eq_one_iff s).mpr hs, mul_one]

end Proj

section Concrete

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev M7 : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 7)

@[expose] def sp7 (A B : M7) (h1 : A * B = 1) (h2 : B * A = 1)
    (h : Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0) :
    StatedSp 2 (ZMod 7) :=
  ⟨⟨A, B, h1, h2⟩, Subgroup.subset_closure h⟩

@[expose] def mT1 : M7 := Matrix.fromBlocks !![2, 0; 0, 1] 0 0 !![4, 0; 0, 1]
@[expose] def mT1i : M7 := Matrix.fromBlocks !![4, 0; 0, 1] 0 0 !![2, 0; 0, 1]
@[expose] def mT2 : M7 := Matrix.fromBlocks !![1, 0; 0, 2] 0 0 !![1, 0; 0, 4]
@[expose] def mT2i : M7 := Matrix.fromBlocks !![1, 0; 0, 4] 0 0 !![1, 0; 0, 2]
@[expose] def mW1 : M7 :=
  Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, -1] !![1, 0; 0, 0]
@[expose] def mW1i : M7 :=
  Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, -1] !![0, 0; 0, 1] !![1, 0; 0, 0]
@[expose] def mW2 : M7 :=
  Matrix.fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0] !![-1, 0; 0, 0] !![0, 0; 0, 1]
@[expose] def mW2i : M7 :=
  Matrix.fromBlocks !![0, 0; 0, 1] !![-1, 0; 0, 0] !![1, 0; 0, 0] !![0, 0; 0, 1]
@[expose] def mU : M7 := Matrix.fromBlocks !![-1, 0; 0, 1] 0 0 !![-1, 0; 0, 1]
@[expose] def mV : M7 := Matrix.fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]
@[expose] def mV' : M7 := Matrix.fromBlocks 0 !![0, -1; -1, 0] !![0, 1; 1, 0] 0
@[expose] def mV'i : M7 := Matrix.fromBlocks 0 !![0, 1; 1, 0] !![0, -1; -1, 0] 0

@[expose] def spT1 : StatedSp 2 (ZMod 7) := sp7 mT1 mT1i (by decide) (by decide) (by decide)
@[expose] def spT2 : StatedSp 2 (ZMod 7) := sp7 mT2 mT2i (by decide) (by decide) (by decide)
@[expose] def spW1 : StatedSp 2 (ZMod 7) := sp7 mW1 mW1i (by decide) (by decide) (by decide)
@[expose] def spW2 : StatedSp 2 (ZMod 7) := sp7 mW2 mW2i (by decide) (by decide) (by decide)
@[expose] def spU : StatedSp 2 (ZMod 7) := sp7 mU mU (by decide) (by decide) (by decide)
@[expose] def spV : StatedSp 2 (ZMod 7) := sp7 mV mV (by decide) (by decide) (by decide)
@[expose] def spV' : StatedSp 2 (ZMod 7) := sp7 mV' mV'i (by decide) (by decide) (by decide)

@[expose] def spNeg : StatedSp 2 (ZMod 7) := sp7 (-1) (-1) (by decide) (by decide) (by decide)

theorem spNeg_mem_scalars : (spNeg : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) ∈
    StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 7) :=
  ⟨-1, Units.ext (by decide)⟩

abbrev PSp47 : Type := StatedProj (StatedSp 2 (ZMod 7))

theorem sp7_not_mem_scalars_of_diag {x : StatedSp 2 (ZMod 7)} (i j : Fin 2 ⊕ Fin 2)
    (h : ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) : M7) i i ≠
      ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) : M7) j j) :
    (x : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) ∉ StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 7) :=
  fun hx => h (diag_eq_of_mem_statedScalars hx i j)

theorem sp7_not_mem_scalars_of_offDiag {x : StatedSp 2 (ZMod 7)} (i j : Fin 2 ⊕ Fin 2)
    (hij : i ≠ j) (h : ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) : M7) i j ≠ 0) :
    (x : GL (Fin 2 ⊕ Fin 2) (ZMod 7)) ∉ StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 7) :=
  fun hx => h (offDiag_eq_zero_of_mem_statedScalars hx hij)

theorem card_PSp47 : Nat.card PSp47 = 138297600 := by
  have hT : StatedClassicalModel PSp47 .PSp 2 7 1 :=
    ⟨⟨by norm_num, le_rfl, le_rfl, by decide⟩, ZMod 7, inferInstance, inferInstance,
      by rw [Nat.card_zmod, pow_one], ⟨MulEquiv.refl _⟩⟩
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hT]
  decide

theorem orderOf_spT1 : orderOf (spT1 : PSp47) = 3 :=
  orderOf_statedProj_mk (by rw [(by decide : spT1 ^ 3 = 1)]; exact one_mem _)
    (sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide))

theorem orderOf_spT2 : orderOf (spT2 : PSp47) = 3 :=
  orderOf_statedProj_mk (by rw [(by decide : spT2 ^ 3 = 1)]; exact one_mem _)
    (sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide))

theorem commute_spT1_spT2 : Commute (spT1 : PSp47) (spT2 : PSp47) := by
  change (spT1 : PSp47) * spT2 = spT2 * spT1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (by decide : spT1 * spT2 = spT2 * spT1)]

theorem spT2_not_mem_zpowers : (spT2 : PSp47) ∉ zpowers (spT1 : PSp47) := by
  rw [mem_zpowers_of_orderOf_eq_three orderOf_spT1]
  rintro (h | h | h)
  · exact sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide)
      ((statedProj_mk_eq_one_iff _).mp h)
  · exact sp7_not_mem_scalars_of_diag (x := spT2⁻¹ * spT1) (.inl 0) (.inl 1) (by decide)
      ((statedProj_mk_eq_mk_iff _ _).mp h)
  · rw [← QuotientGroup.mk_pow] at h
    exact sp7_not_mem_scalars_of_diag (x := spT2⁻¹ * spT1 ^ 2) (.inl 0) (.inr 0) (by decide)
      ((statedProj_mk_eq_mk_iff _ _).mp h)

theorem sp7_mul_comm {x y : StatedSp 2 (ZMod 7)} (h : x * y = y * x) :
    (x : PSp47) * y = y * x := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem four_dvd_card_centralizer_spT1 :
    4 ∣ Nat.card (centralizer ({(spT1 : PSp47)} : Set PSp47)) :=
  four_dvd_card_centralizer_of_orderOf_four (w := (spW1 : PSp47))
    (orderOf_statedProj_mk_eq_four (by decide)
      (sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide)))
    (sp7_mul_comm (by decide))

theorem four_dvd_card_centralizer_spT2 :
    4 ∣ Nat.card (centralizer ({(spT2 : PSp47)} : Set PSp47)) :=
  four_dvd_card_centralizer_of_orderOf_four (w := (spW2 : PSp47))
    (orderOf_statedProj_mk_eq_four (by decide)
      (sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide)))
    (sp7_mul_comm (by decide))

theorem orderOf_spU : orderOf (spU : PSp47) = 2 :=
  orderOf_statedProj_mk (by rw [(by decide : spU ^ 2 = 1)]; exact one_mem _)
    (sp7_not_mem_scalars_of_diag (.inl 0) (.inl 1) (by decide))

theorem four_dvd_card_centralizer_spT1_mul_spT2 :
    4 ∣ Nat.card (centralizer ({(spT1 : PSp47) * spT2} : Set PSp47)) := by
  rw [← QuotientGroup.mk_mul]
  refine four_dvd_card_centralizer_of_klein (u := (spU : PSp47)) (v := (spV : PSp47))
    orderOf_spU ?_ ?_ ?_ (sp7_mul_comm (by decide)) (sp7_mul_comm (by decide))
  · exact orderOf_statedProj_mk (by rw [(by decide : spV ^ 2 = 1)]; exact one_mem _)
      (sp7_not_mem_scalars_of_offDiag (.inl 0) (.inl 1) (by decide) (by decide))
  · intro h
    exact sp7_not_mem_scalars_of_offDiag (x := spU⁻¹ * spV) (.inl 0) (.inl 1) (by decide)
      (by decide) ((statedProj_mk_eq_mk_iff _ _).mp h)
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact statedProj_mk_eq_of_eq_mul (s := spNeg) (by decide) spNeg_mem_scalars

theorem four_dvd_card_centralizer_spT1_sq_mul_spT2 :
    4 ∣ Nat.card (centralizer ({(spT1 : PSp47) ^ 2 * spT2} : Set PSp47)) := by
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
  refine four_dvd_card_centralizer_of_klein (u := (spU : PSp47)) (v := (spV' : PSp47))
    orderOf_spU ?_ ?_ ?_ (sp7_mul_comm (by decide)) (sp7_mul_comm (by decide))
  · exact orderOf_statedProj_mk (by rw [(by decide : spV' ^ 2 = spNeg)]; exact spNeg_mem_scalars)
      (sp7_not_mem_scalars_of_offDiag (.inl 0) (.inr 1) (by decide) (by decide))
  · intro h
    exact sp7_not_mem_scalars_of_offDiag (x := spU⁻¹ * spV') (.inl 0) (.inr 1) (by decide)
      (by decide) ((statedProj_mk_eq_mk_iff _ _).mp h)
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact statedProj_mk_eq_of_eq_mul (s := spNeg) (by decide) spNeg_mem_scalars

theorem four_dvd_card_centralizer_PSp47 (x : PSp47) (hx : orderOf x = 3) :
    4 ∣ Nat.card (centralizer {x}) :=
  four_dvd_card_centralizer_of_sylow (by rw [card_PSp47]; norm_num)
    (by rw [card_PSp47]; norm_num) orderOf_spT1 orderOf_spT2 commute_spT1_spT2
    spT2_not_mem_zpowers four_dvd_card_centralizer_spT1 four_dvd_card_centralizer_spT2
    four_dvd_card_centralizer_spT1_mul_spT2 four_dvd_card_centralizer_spT1_sq_mul_spT2 x hx

theorem four_dvd_card_centralizer_of_PSp_two_seven {T : Type} [Group T]
    (hT : StatedClassicalModel T .PSp 2 7 1) (x : T) (hx : orderOf x = 3) :
    4 ∣ Nat.card (centralizer {x}) := by
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  set φ := FiniteField.ringEquivOfCardEq hcard
  set e : T ≃* PSp47 := eT.trans
    (statedProjCongr (glCongr φ) (glCongr_statedSp φ 2) (glCongr_statedScalars φ))
  rw [← card_centralizer_mulEquiv e x]
  exact four_dvd_card_centralizer_PSp47 (e x) (by rw [MulEquiv.orderOf_eq]; exact hx)

end Concrete

end CFSG.EvenSmallLie.Child3.SelK3Classical
