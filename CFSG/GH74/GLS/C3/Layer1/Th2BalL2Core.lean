module

public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14e
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

section K

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem ivk_1_2k_b_same (hF : L2Field F) (e : K ≃* L2 F) (E : Subgroup (MulAut K))
    (hE : IsElementaryAbelian 2 ↥E) (hE8 : Nat.card ↥E = 8) :
    ∃ x ∈ E, orderOf x = 2 ∧ ∃ e' : K ≃* L2 F, x ∈ fieldAutSub e' := by
  have := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
    rwa [pow_two] at this
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hE2 : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 E
  obtain ⟨T', hT'⟩ := hE2.exists_le_sylow
  have hnot : ¬ E ≤ innDiagSub e := by
    intro hsub
    have := card_le_four_of_le_inf e hF T' E hT' hsub hcomm hsq
    omega
  obtain ⟨y, hyE, hyG⟩ := Set.not_subset.mp hnot
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyG (innDiagSub e).one_mem
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq y hyE) hy1
  refine ⟨y, hyE, hy2, ?_⟩
  have hproj : fieldProj e y ≠ 1 := fun h => hyG ((mem_innDiagSub_iff e y).mpr h)
  have hord : orderOf (thetaAut e y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord
    (by rw [← fieldProj_apply]; exact hproj)
  set σ := (thetaAut e y).right with hσ
  have hΘφ : thetaAut e (fieldAutHom e σ) = SemidirectProduct.inr σ := thetaAut_fieldAutHom e σ
  set a : MulAut K := innDiagHom e C with ha
  have hΘa : thetaAut e a = SemidirectProduct.inl C := thetaAut_innDiagHom e C
  have hconj : a⁻¹ * y * a = fieldAutHom e σ := by
    apply (thetaAut e).injective
    rw [map_mul, map_mul, map_inv, hΘa, hΘφ]
    exact hC
  have hy : y = a * fieldAutHom e σ * a⁻¹ := by
    rw [← hconj]; group
  refine ⟨twistEquiv e a⁻¹, σ, ?_⟩
  rw [fieldAutHom_twist, inv_inv, hy]


theorem oResidual_pgl2_eq_range {F₀ : Type} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀))
    (h3 : 3 ≤ Nat.card F₀) :
    oResidual 2 (PGL2 F₀) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range := by
  have hpp : IsOddPrimePower (Nat.card F₀) := by
    have := Fintype.ofFinite F₀
    obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F₀
    have hq : Nat.card F₀ = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
    refine ⟨p, n, hp, ?_, n.pos, hq⟩
    by_contra hpo
    have h2 : p = 2 := by
      rcases hp.eq_two_or_odd' with h2 | h2
      · exact h2
      · exact absurd h2 hpo
    have hq2 : Even (Nat.card F₀) := by
      rw [hq, h2]
      exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) hq2
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup (PGL2 F₀),
      J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range := ⟨_, rfl⟩
  rw [← hJ]
  have hJidx : J.index = 2 := hJ ▸ pgl2_psl2Range_index_eq_two F₀ hpp
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJidx
  have hquot : IsPGroup 2 (PGL2 F₀ ⧸ J) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.index, hJidx]
    norm_num
  have hle : oResidual 2 (PGL2 F₀) ≤ J := CFSG.GH74.GLS.Stage1.Thm6.Prod.oResidual_le_of_isPGroup_quotient hquot
  have hidx := index_oResidual_pgl2_le_two hodd h3
  have hidx' : J.index ≤ (oResidual 2 (PGL2 F₀)).index := Subgroup.index_antitone hle
  have hc1 := Subgroup.card_mul_index (oResidual 2 (PGL2 F₀))
  have hc2 := Subgroup.card_mul_index J
  have hpos : 0 < Nat.card (PGL2 F₀) := Nat.card_pos
  have heq : (oResidual 2 (PGL2 F₀)).index = 2 := by omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [heq] at hc1
  rw [hJidx] at hc2
  omega

theorem isL2_oResidual_fixedSubgroup (hF : L2Field F) (e : K ≃* L2 F) (σ' : F ≃+* F)
    (hσ2 : orderOf σ' = 2) :
    IsL2 ↥((oResidual 2 ↥(fixedSubgroup K (fieldAutHom e σ'))).map
      (fixedSubgroup K (fieldAutHom e σ')).subtype) (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) := by
  obtain ⟨-, -, heven⟩ := ivk_1_4a F hF K e σ'
  obtain ⟨F₀, _, _, hq₀, ⟨φ⟩⟩ := heven (by rw [hσ2]; exact even_two)
  rw [hσ2] at hq₀
  have hq₀odd : Odd (Nat.card F₀) := by
    have : Odd (Nat.card F₀ ^ 2) := by rw [hq₀]; exact hF.1
    exact (Nat.odd_mul.mp (by simpa [pow_two] using this)).1
  have hq₀ge : 3 ≤ Nat.card F₀ := by
    have h2 : 2 ≤ Nat.card F₀ := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hq₀odd
    omega
  refine ⟨F₀, inferInstance, inferInstance, ⟨hq₀odd, hq₀ge⟩, ?_⟩
  set C := fixedSubgroup K (fieldAutHom e σ')
  have hmap := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual φ.toMonoidHom φ.surjective (p := 2)
    Nat.prime_two
  rw [oResidual_pgl2_eq_range hq₀odd hq₀ge] at hmap
  exact ⟨(Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
        ((MulEquiv.subgroupCongr hmap).trans
          ((psl2EquivToPGLRange F₀).symm.trans (L2.equivPSL F₀).symm)))⟩


theorem pPrimeCoreOf_fieldInvolution_eq_bot
    (hF : L2Field F) (e : K ≃* L2 F) (H : Subgroup (MulAut K)) (hH : innAut K ≤ H)
    (σ' : F ≃+* F) (hσ2 : orderOf σ' = 2) :
    pPrimeCoreOf 2 (H ⊓ centralizer ({fieldAutHom e σ'} : Set (MulAut K))) = ⊥ := by
  have hinj := conj_injective_of_L2 e
  set x : MulAut K := fieldAutHom e σ' with hx
  set C : Subgroup (MulAut K) := H ⊓ centralizer ({x} : Set (MulAut K)) with hC
  set W : Subgroup (MulAut K) := pPrimeCoreOf 2 C with hW
  have hWodd : Odd (Nat.card ↥W) := TwoThin.card_pPrimeCoreOf_odd C
  have hWnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := fun c hc w hw =>
    TwoThin.pPrimeCoreOf_normalized C hc hw
  have hxo : orderOf x = 2 := by
    rw [hx, orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ', hσ2]
  have hconjC : ∀ c ∈ fixedSubgroup K x, MulAut.conj c ∈ C := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨hH ⟨c, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h2 : MulAut.conj (x c) = MulAut.conj c := by rw [show x c = c from hc]
    have h3 : x * MulAut.conj c * x⁻¹ = MulAut.conj c := by rw [mul_conj_mul_inv, h2]
    calc MulAut.conj c * x = (x * MulAut.conj c * x⁻¹) * x := by rw [h3]
      _ = x * MulAut.conj c := by group
  set W₀ : Subgroup K := W.comap (MulAut.conj : K →* MulAut K) with hW₀
  have hW₀odd : Odd (Nat.card ↥W₀) := by
    have hle : W₀.map (MulAut.conj : K →* MulAut K) ≤ W := Subgroup.map_comap_le _ _
    have hc : Nat.card ↥(W₀.map (MulAut.conj : K →* MulAut K)) = Nat.card ↥W₀ :=
      Subgroup.card_map_of_injective hinj
    rw [← hc]
    exact Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le hle)
  have hW₀bot : W₀ = ⊥ := by
    by_contra hne
    obtain ⟨c, hc, k, hk, hck⟩ := ivk_1_4e F hF K e σ' W₀ hne hW₀odd
    apply hck
    have hk' : MulAut.conj k ∈ W := hk
    have := hWnorm _ (hconjC c hc) _ hk'
    show MulAut.conj (c * k * c⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact this
  have hfix : ∀ w ∈ W, ∀ c ∈ fixedSubgroup K x, w c = c := by
    intro w hw c hc
    have h1 : MulAut.conj c * w * (MulAut.conj c)⁻¹ ∈ W := hWnorm _ (hconjC c hc) w hw
    have h2 : (MulAut.conj c * w * (MulAut.conj c)⁻¹) * w⁻¹ ∈ W := W.mul_mem h1 (W.inv_mem hw)
    have h3 : (MulAut.conj c * w * (MulAut.conj c)⁻¹) * w⁻¹ = MulAut.conj (c * (w c)⁻¹) := by
      have := mul_conj_mul_inv w c⁻¹
      calc (MulAut.conj c * w * (MulAut.conj c)⁻¹) * w⁻¹
          = MulAut.conj c * (w * MulAut.conj c⁻¹ * w⁻¹) := by rw [map_inv]; group
        _ = MulAut.conj c * (MulAut.conj (w c⁻¹)) := by rw [this]
        _ = MulAut.conj (c * (w c)⁻¹) := by rw [← map_mul, map_inv w c]
    have h4 : c * (w c)⁻¹ ∈ W₀ := by
      show MulAut.conj (c * (w c)⁻¹) ∈ W
      rw [← h3]
      exact h2
    rw [hW₀bot, Subgroup.mem_bot] at h4
    have h5 : c = w c := by
      have := mul_inv_eq_one.1 h4
      exact this
    exact h5.symm
  obtain ⟨I, hI⟩ : ∃ I : Subgroup K, I = (oResidual 2 ↥(fixedSubgroup K x)).map
      (fixedSubgroup K x).subtype := ⟨_, rfl⟩
  have hIL2 : IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) := by
    rw [hI]
    exact isL2_oResidual_fixedSubgroup hF e σ' hσ2
  have hcen := centralizer_eq_zpowers hF e I hIL2 σ' hσ2 hI
  have hIfix : I ≤ fixedSubgroup K x := by
    rw [hI]
    exact Subgroup.map_subtype_le _
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  have hwc : w ∈ centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
      Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨i, hi, rfl⟩
    have h1 := mul_conj_mul_inv w i
    rw [hfix w hw i (hIfix hi)] at h1
    calc MulAut.conj i * w = (w * MulAut.conj i * w⁻¹) * w := by rw [h1]
      _ = w * MulAut.conj i := by group
  rw [hcen] at hwc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwc
  have hdvd : orderOf (x ^ n) ∣ Nat.card ↥W := Subgroup.orderOf_dvd_natCard W hw
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hsq : (x ^ n) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have h2 : orderOf (x ^ n) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hodd : Odd (orderOf (x ^ n)) := Odd.of_dvd_nat hWodd hdvd
  have h1 : orderOf (x ^ n) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

end K

end CFSG.GH74.GLS.Th2.Bal
