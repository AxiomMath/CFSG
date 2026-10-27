module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28NormalSection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

section Torus

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {A : Subgroup Kˣ}

@[expose] def uniTorusVec (r : ℕ) {n : ℕ} (x : Fin n → A) (i : Fin r) : Kˣ :=
  if hi : (i : ℕ) < n then (x ⟨i, hi⟩ : Kˣ) else 1

theorem uniTorusVec_mem {n : ℕ} (x : Fin n → A) (i : Fin r) : uniTorusVec r x i ∈ A := by
  unfold uniTorusVec
  split_ifs
  exacts [(x _).2, A.one_mem]

theorem uniTorusVec_mul {n : ℕ} (x y : Fin n → A) :
    uniTorusVec r (x * y) = uniTorusVec r x * uniTorusVec r y := by
  funext i
  simp only [uniTorusVec, Pi.mul_apply, Subgroup.coe_mul]
  split_ifs <;> simp

theorem uniTorusVec_apply_of_lt {n : ℕ} (x : Fin n → A) {j : ℕ} (hj : j < n) (hjr : j < r) :
    uniTorusVec r x ⟨j, hjr⟩ = (x ⟨j, hj⟩ : Kˣ) := by
  simp [uniTorusVec, hj]

theorem uniTorusRatio_eq_one (h : UnitaryFieldData p f K) (hA : ∀ x ∈ A, h.bar (x : K) = x)
    {n : ℕ} (x : Fin n → A) : torusRatio (ε := ε) h (uniTorusVec r x) 1 = 1 := by
  unfold torusRatio
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun k : Fin ε => (((1 : Fin ε → Kˣ) k : Kˣ) : K))
      (fun k _ => by simp), mul_one]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [hA _ (uniTorusVec_mem x i)]
  exact div_self (Units.ne_zero _)

@[expose] noncomputable def uniTorusFix (h : UnitaryFieldData p f K)
    (hA : ∀ x ∈ A, h.bar (x : K) = x) (r ε n : ℕ) : (Fin n → A) →* hypSU h r ε :=
  MonoidHom.mk' (fun x => mkHypSU h (diagonal (torusEntries h (uniTorusVec r x) 1))
      (diagonal_torusEntries_isometry h _ fun k => by simp [UnitaryFieldData.norm])
      (by rw [det_diagonal_torusEntries, uniTorusRatio_eq_one h hA]))
    fun x y => Subtype.ext (Units.ext (by
      change diagonal _ = diagonal _ * diagonal _
      rw [diagonal_mul_diagonal, uniTorusVec_mul]
      congr 1
      funext a
      rcases a with i | k | i <;> simp [torusEntries, mul_comm]))

theorem uniEq_one_of_torusFix_mem_hypScalars (h : UnitaryFieldData p f K)
    (hA : ∀ x ∈ A, h.bar (x : K) = x) (hodd : ∀ x ∈ A, x ^ 2 = 1 → x = 1) {n : ℕ} (hn : n ≤ r)
    {x : Fin n → A} (hx : uniTorusFix h hA r ε n x ∈ hypScalars h r ε) : x = 1 := by
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hx
  have hM : diagonal (torusEntries h (uniTorusVec r x) (1 : Fin ε → Kˣ)) =
      Matrix.scalar _ (c : K) := congrArg Units.val hc
  funext j
  have hjr : (j : ℕ) < r := lt_of_lt_of_le j.isLt hn
  have e1 := congrFun (congrFun hM (.inl ⟨j, hjr⟩)) (.inl ⟨j, hjr⟩)
  have e2 := congrFun (congrFun hM (.inr (.inr ⟨j, hjr⟩))) (.inr (.inr ⟨j, hjr⟩))
  simp [torusEntries] at e1 e2
  rw [uniTorusVec_apply_of_lt x j.isLt hjr] at e1 e2
  have hbar : h.bar ((x j : Kˣ) : K) = (x j : Kˣ) := hA _ (x j).2
  rw [Fin.eta, hbar] at e2
  rw [Fin.eta] at e1
  have hy2 : ((x j : Kˣ) : K) ^ 2 = 1 := by
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv₀ (Units.ne_zero _)).2 (e1.trans e2.symm)
  have hy : (x j : Kˣ) = 1 :=
    hodd _ (x j).2 (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hy2))
  exact Subtype.ext hy

theorem uniBar_eq_of_pow_seven (h : UnitaryFieldData 2 3 K) {x : Kˣ} (hx : x ^ 7 = 1) :
    h.bar (x : K) = x := by
  have h7 : (x : K) ^ 7 = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  rw [UnitaryFieldData.bar_apply]
  calc (x : K) ^ 2 ^ 3 = (x : K) ^ 7 * x := by ring
    _ = (x : K) := by rw [h7, one_mul]

theorem uniExists_sevenSubgroup (hK : Nat.card K = 64) : ∃ μ : Subgroup Kˣ, Nat.card μ = 7 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hU : Nat.card Kˣ = 63 := by rw [Nat.card_units, hK]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 7 (by rw [hU]; norm_num)
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

theorem uniPow_seven_of_mem {μ : Subgroup Kˣ} (hμ : Nat.card μ = 7) {x : Kˣ} (hx : x ∈ μ) :
    x ^ 7 = 1 :=
  orderOf_dvd_iff_pow_eq_one.1 (hμ ▸ Subgroup.orderOf_dvd_natCard μ hx)

theorem uniEq_one_of_sq_of_mem {μ : Subgroup Kˣ} (hμ : Nat.card μ = 7) {x : Kˣ} (hx : x ∈ μ)
    (hx2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 7 := hμ ▸ Subgroup.orderOf_dvd_natCard μ hx
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h3 : orderOf x ∣ Nat.gcd 7 2 := Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h3))

end Torus

theorem uniSq_pow_ne_eight (f : ℕ) : (2 ^ f) ^ 2 ≠ 8 := by
  intro h8
  have h3 : 2 ^ (f * 2) = 2 ^ 3 := by rw [pow_mul, h8]; norm_num
  have := Nat.pow_right_injective le_rfl h3
  omega

theorem uniOrdA_ne_504 (f k : ℕ) : ordA k ((2 ^ f) ^ 2) ≠ 504 := fun hk =>
  uniSq_pow_ne_eight f
    ((ordA_eq_504_iff (f := 2 * f) (by rw [← pow_mul, mul_comm])).1 hk).2

section Blocks

variable {f t s ε : ℕ} {K : Type} [Field K]

theorem uniBlock_eq_none_of_504 (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : LeviBlock.IsTopCut I t) (j : Option ↥I)
    (hq : CFSG.Open.IsQuasisimple (LeviBlock.uniBlockSub (s := s) (ε := ε) h I j))
    (h504 : Nat.card (↥(LeviBlock.uniBlockSub (s := s) (ε := ε) h I j) ⧸
      Subgroup.center ↥(LeviBlock.uniBlockSub (s := s) (ε := ε) h I j)) = 504) : j = none := by
  rcases j with _ | b
  · rfl
  · exfalso
    rw [(LeviBlock.uniBlockSub_facts (s := s) h hε hI (some b)).2 hq] at h504
    exact uniOrdA_ne_504 f _ h504

end Blocks

theorem kFactCompParabL28RankOn_twistedA :
    KFactCompParabL28RankOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC N hNP hPN d' ψ hd hψ
  obtain ⟨d, hdA, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, -, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hdA e
  have : Finite K := h.finite
  have h504 := card_mem_of_l28Section hCP.parab.1 ρ hρ (hasLeviBlocks_hypStab h hε hI g hJ) hNP
    hPN ψ hd hψ
  have hres : 2 * s + ε - 1 = 1 ∧ 2 ^ f = 8 := by
    rcases h504 with ⟨k, hk⟩ | hk
    · exact absurd hk.symm (uniOrdA_ne_504 f k)
    · exact (ordTwistedA_eq_504_iff (f := f) rfl).1 hk.symm
  obtain ⟨hse, hf8⟩ := hres
  obtain rfl : f = 3 := Nat.pow_right_injective le_rfl (hf8.trans (by norm_num))
  have hs : s = 1 := by omega
  have hr : 2 ≤ t + s := by have := (hI.le t hI.mem).1; omega
  obtain ⟨μ, hμ⟩ := uniExists_sevenSubgroup (K := K) (by rw [h.card]; norm_num)
  have hA : ∀ x ∈ μ, h.bar (x : K) = x := fun x hx =>
    uniBar_eq_of_pow_seven h (uniPow_seven_of_mem hμ hx)
  have hodd : ∀ x ∈ μ, x ^ 2 = 1 → x = 1 := fun x hx hx2 => uniEq_one_of_sq_of_mem hμ hx hx2
  set φ₀ := uniTorusFix h hA (t + s) ε 2
  have hc : ∀ a, (L.subtype.comp (ρ.comp φ₀)) a ∈ Subgroup.centralizer (L : Set Y) → a = 1 := by
    intro a ha
    refine uniEq_one_of_torusFix_mem_hypScalars h hA hodd hr ((hZ _).1 ?_)
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp ha l l.2)
  refine l28_E_of_torus (M := μ) hμ (L.subtype.comp (ρ.comp φ₀)) ?_ ?_ hc
  · rw [injective_iff_map_eq_one]
    exact fun a ha => hc a (by rw [ha]; exact Subgroup.one_mem _)
  · rintro _ ⟨a, rfl⟩
    exact (ρ (φ₀ a)).2

theorem kFactCompParabL28TwoRankOn_twistedA :
    KFactCompParabL28TwoRankOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC N hNP hPN d₁ d₂ ψ hd₁ hd₂ hψ
  obtain ⟨d, hdA, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, -, hρ, -, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hdA e
  have : Finite K := h.finite
  set β := LeviBlock.uniLeviHom (s := s) h hε hI
  set e' := LeviBlock.stabMulEquiv g hJ
  have hrange : (β.comp e'.toMonoidHom).range = β.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map (e'.toMonoidHom),
      Subgroup.map_top_of_surjective _ e'.surjective, ← MonoidHom.range_eq_map]
  obtain ⟨j₁, j₂, hne, hq₁, hq₂, h₁, h₂⟩ := two_blocks_of_l28Section hCP.parab.1 ρ hρ
    (β.comp e'.toMonoidHom)
    ((LeviBlock.isPGroup_ker_uniLeviHom h hε hI).comap_of_injective e'.toMonoidHom e'.injective)
    (hrange ▸ LeviBlock.pi_uniBlockSub_le_range h hε hI)
    (hrange ▸ LeviBlock.commutator_range_le_pi h hε hI)
    (fun j => (LeviBlock.uniBlockSub_facts h hε hI j).1) hNP hPN ψ hd₁ hd₂ hψ
  exact absurd ((uniBlock_eq_none_of_504 h hε hI j₁ hq₁ h₁).trans
    (uniBlock_eq_none_of_504 h hε hI j₂ hq₂ h₂).symm) hne

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
