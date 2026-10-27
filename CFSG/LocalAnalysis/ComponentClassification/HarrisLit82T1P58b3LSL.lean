module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3M
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagLinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

namespace P58b3L

variable {F : Type} [Field F] {n : ℕ}

theorem even_card_coordBlockSL [Finite F] (h2 : (2 : F) ≠ 0) {J : Finset (Fin n)}
    (hJ : 2 ≤ J.card) : Even (Nat.card (coordBlockSL F J)) := by
  classical
  obtain ⟨J₂, hJ₂J, hJ₂⟩ := Finset.exists_subset_card_eq hJ
  set d : Fin n → F := fun i => if i ∈ J₂ then -1 else 1 with hd
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal, hd, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
      mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter, hJ₂]
    norm_num
  set D : SL(n, F) := ⟨Matrix.diagonal d, hdet⟩ with hD
  have hDJ : D ∈ coordBlockSL F J := by
    rw [mem_coordBlockSL_iff]
    intro i j hij
    change Matrix.diagonal d i j = _
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      have hi : i ∉ J₂ := fun hi => by
        rcases hij with h' | h' <;> exact h' (hJ₂J hi)
      rw [hd]
      simp [hi]
    · rfl
  have hDD : D * D = 1 := by
    apply Subtype.ext
    change Matrix.diagonal d * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    rw [hd]
    by_cases hi : i ∈ J₂ <;> simp [hi]
  obtain ⟨i₀, hi₀⟩ : J₂.Nonempty := Finset.card_pos.mp (by omega)
  have hD1 : D ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : SL(n, F) => (A : Matrix (Fin n) (Fin n) F) i₀ i₀) h
    change Matrix.diagonal d i₀ i₀ = (1 : Matrix (Fin n) (Fin n) F) i₀ i₀ at h1
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hd] at h1
    simp only [hi₀, ↓reduceIte] at h1
    apply h2
    linear_combination -h1
  have hord : orderOf (⟨D, hDJ⟩ : coordBlockSL F J) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change D ^ 2 = 1
      rw [pow_two, hDD]
    · intro h
      exact hD1 (congrArg Subtype.val h)
  have := orderOf_dvd_natCard (⟨D, hDJ⟩ : coordBlockSL F J)
  rw [hord] at this
  exact even_iff_two_dvd.mpr this

theorem false_of_block {X : Type} [Group X] [Finite X] [Finite F] (hF : Nat.card F = 3)
    (Ψ : SL(n, F) →* X) (hΨi : Function.Injective Ψ) (hΨs : Function.Surjective Ψ) {t : X}
    {σ : Fin n → Bool} (hf : ∀ y, t * Ψ y * t⁻¹ = Ψ (slConjugation n F (signGL F σ) y))
    {b₀ : Bool} (hJ : 3 ≤ (coordSet σ b₀).card) {Q : Subgroup X}
    (hQt : Q ≤ centralizer {t}) (hQsub : (Q.subgroupOf (centralizer {t})).IsSubnormal)
    (hQsolv : Group.IsSolvable (↥Q ⧸ pPrimeCore 2 ↥Q)) {a b : X} (ha : a ∈ Q) (hb : b ∈ Q)
    {c : X} (hc : ∀ y : SL(n, F), Ψ y = c → (y : Matrix (Fin n) (Fin n) F) = -1)
    (haa : a * a = c) (hbb : b * b = c) (hab : a * b = c * (b * a)) : False := by
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  set J := coordSet σ b₀ with hJdef
  have hker : Ψ.ker ≤ center SL(n, F) := by
    rw [(MonoidHom.ker_eq_bot_iff Ψ).mpr hΨi]
    exact bot_le
  have hcomp := Foote5.OddLieCore.isComponentOf_block_centralizer_three h2 Ψ hker t σ hf b₀ hJ
  rw [MonoidHom.range_eq_top.mpr hΨs, top_inf_eq] at hcomp
  set N := (coordBlockSL F J).map Ψ with hN
  have hNC : N ≤ centralizer {t} := hcomp.1
  have hNcomp : IsComponent (N.subgroupOf (centralizer {t})) :=
    (isComponentOf_iff_isComponent_subgroupOf hNC).mp
      ((AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hcomp)
  have hNeven : Even (Nat.card (N.subgroupOf (centralizer {t}))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv, hN,
      Subgroup.card_map_of_injective hΨi]
    exact even_card_coordBlockSL h2 (by omega)
  have hcomm := P51Q.commute_of_isComponent hQt hQsub hQsolv hNcomp hNeven
  have hT : ∀ y : SL(n, F), Ψ y ∈ Q → ∀ i ∈ J, ∀ j ∈ J, ∀ hij : i ≠ j,
      (y : Matrix (Fin n) (Fin n) F) *
          (Matrix.SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) =
        (Matrix.SpecialLinearGroup.transvection hij (1 : F) : Matrix (Fin n) (Fin n) F) * y := by
    intro y hy i hi j hj hij
    have hTN : Ψ (Matrix.SpecialLinearGroup.transvection hij (1 : F)) ∈ N :=
      ⟨_, transvection_mem_coordBlockSL hi hj hij 1, rfl⟩
    have h1 := hcomm ⟨_, hNC hTN⟩ (mem_subgroupOf.mpr hTN) (Ψ y) hy
    have h3 : Matrix.SpecialLinearGroup.transvection hij (1 : F) * y =
        y * Matrix.SpecialLinearGroup.transvection hij (1 : F) := hΨi (by
      rw [map_mul, map_mul]
      exact h1)
    have h4 := congrArg (fun z : SL(n, F) => (z : Matrix (Fin n) (Fin n) F)) h3
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h4
    exact h4.symm
  obtain ⟨aa, rfl⟩ := hΨs a
  obtain ⟨bb, rfl⟩ := hΨs b
  obtain ⟨l, hl⟩ := Foote5.OddLieCore.block_scalar_of_transvections (by omega) (hT aa ha)
  obtain ⟨m, hm⟩ := Foote5.OddLieCore.block_scalar_of_transvections (by omega) (hT bb hb)
  obtain ⟨i₀, hi₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  have hrow : ∀ (B C : Matrix (Fin n) (Fin n) F) (κ : F),
      (∀ a b, (a ∈ J ∨ b ∈ J) → B a b = if a = b then κ else 0) → (B * C) i₀ i₀ = κ * C i₀ i₀ := by
    intro B C κ hB
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rw [hB i₀ i₀ (Or.inl hi₀)]
      simp
    · intro k _ hk
      rw [hB i₀ k (Or.inl hi₀)]
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hdiag : ∀ (B : Matrix (Fin n) (Fin n) F) (κ : F),
      (∀ a b, (a ∈ J ∨ b ∈ J) → B a b = if a = b then κ else 0) → B i₀ i₀ = κ := by
    intro B κ hB
    rw [hB i₀ i₀ (Or.inl hi₀)]
    simp
  have e1 : ((aa * aa : SL(n, F)) : Matrix (Fin n) (Fin n) F) = -1 :=
    hc _ (by rw [map_mul]; exact haa)
  have e2 : ((bb * bb : SL(n, F)) : Matrix (Fin n) (Fin n) F) = -1 :=
    hc _ (by rw [map_mul]; exact hbb)
  have e3 : aa * bb = aa * aa * (bb * aa) :=
    hΨi (by rw [map_mul, map_mul, map_mul, map_mul, hab, haa])
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e1 e2
  have hab' : (aa : Matrix (Fin n) (Fin n) F) * bb = -((bb : Matrix (Fin n) (Fin n) F) * aa) := by
    have h := congrArg (fun z : SL(n, F) => (z : Matrix (Fin n) (Fin n) F)) e3
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [h, e1, neg_one_mul]
  have k1 : ((aa : Matrix (Fin n) (Fin n) F) * bb) i₀ i₀ = l * m := by
    rw [hrow _ _ l hl, hdiag _ m hm]
  have k2 : ((bb : Matrix (Fin n) (Fin n) F) * aa) i₀ i₀ = m * l := by
    rw [hrow _ _ m hm, hdiag _ l hl]
  have k3 : ((aa : Matrix (Fin n) (Fin n) F) * aa) i₀ i₀ = l * l := by
    rw [hrow _ _ l hl, hdiag _ l hl]
  have k4 : ((bb : Matrix (Fin n) (Fin n) F) * bb) i₀ i₀ = m * m := by
    rw [hrow _ _ m hm, hdiag _ m hm]
  rw [e1] at k3
  rw [e2] at k4
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at k3 k4
  have k5 : l * m = -(m * l) := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) F => A i₀ i₀) hab'
    simp only [Matrix.neg_apply] at h
    rw [k1, k2] at h
    exact h
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_mul] at k3
    exact one_ne_zero (neg_eq_zero.mp k3)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_mul] at k4
    exact one_ne_zero (neg_eq_zero.mp k4)
  have k6 : 2 * (l * m) = 0 := by linear_combination k5
  exact mul_ne_zero h2 (mul_ne_zero hl0 hm0) k6

theorem exists_sl_iso {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hO : pPrimeCore 2 X = ⊥) (hn : 2 ≤ n)
    (hm : Blueprint.LieModel (X ⧸ center X) .PSL n 3 1) {c : X} (hc1 : c ≠ 1)
    (hcZ : c ∈ center X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Ψ : SL(n, F) →* X), Nat.card F = 3 ∧
      Function.Injective Ψ ∧ Function.Surjective Ψ ∧
      ∀ y, Ψ y = c → (y : Matrix (Fin n) (Fin n) F) = -1 := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have hF : Nat.card F = 3 := by rw [hFc, pow_one]
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hFc)
  have hFr : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set β : SL(m + 1, F) →* X ⧸ center X :=
    θ.symm.toMonoidHom.comp (LinearFlag.proj (m + 1) F) with hβdef
  have hβ : Function.Surjective β :=
    θ.symm.surjective.comp (LinearFlag.proj_surjective (m + 1) F)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(m + 1, F)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(m + 1, F) →* E, ∀ x, π (s x) = x := fun E _ _ π hπ hker h2 => by
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.sl_central_two_extension_splitting m hFr hπ hker h2
    exact ⟨s, hs⟩
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  have hβ1 : ∀ z, β z = 1 → (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 ∨
      (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = -1 := by
    intro z hz
    rw [hβdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hz
    obtain ⟨ζ, -, hzζ⟩ := (QuotientGroup.eq_one_iff z).mp hz
    rcases Foote5.OddLieCore.eq_zero_or_one_or_neg_one hF (ζ : F) with h | h | h
    · exact absurd h (Units.ne_zero ζ)
    · left
      rw [hzζ, h, map_one]
    · right
      rw [hzζ, h, map_neg, map_one]
  obtain ⟨z₀, hz₀c, hz₀⟩ : ∃ z₀, α z₀ = c ∧ (z₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = -1 := by
    have hc' : c ∈ (QuotientGroup.mk' (center X)).ker := by rw [hη]; exact hcZ
    rw [hker] at hc'
    obtain ⟨z, hz, hzc⟩ := hc'
    rcases hβ1 z hz with h | h
    · exfalso
      have hz1 : z = 1 := Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])
      exact hc1 (by rw [← hzc, hz1, map_one])
    · exact ⟨z, hzc, h⟩
  have hinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hβw : β w = 1 := by rw [← hαβ, hw, map_one]
    rcases hβ1 w hβw with h | h
    · exact Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])
    · exfalso
      have hwz : w = z₀ := Subtype.ext (h.trans hz₀.symm)
      exact hc1 (by rw [← hz₀c, ← hwz, hw])
  refine ⟨F, inferInstance, inferInstance, α, hF, hinj, hαs, fun y hy => ?_⟩
  have hyz : y = z₀ := hinj (hy.trans hz₀c.symm)
  rw [hyz, hz₀]

theorem exists_sign_chart {X : Type} [Group X] (h2 : (2 : F) ≠ 0) (hn : 0 < n)
    (Ψ : SL(n, F) →* X) (hΨi : Function.Injective Ψ) (hΨs : Function.Surjective Ψ) {t : X}
    (ht : t * t = 1) :
    ∃ (P : SL(n, F)) (σ : Fin n → Bool), ∀ y,
      t * (Ψ.comp (MulAut.conj P).toMonoidHom) y * t⁻¹ =
        (Ψ.comp (MulAut.conj P).toMonoidHom) (slConjugation n F (signGL F σ) y) := by
  obtain ⟨g, rfl⟩ := hΨs t
  have hgg : g * g = 1 := hΨi (by rw [map_mul, ht, map_one])
  have hx : ∀ y, Ψ g * Ψ y * (Ψ g)⁻¹ =
      Ψ (slConjugation n F (Matrix.SpecialLinearGroup.toGL g) y) := by
    intro y
    rw [slConjugation_toGL, map_mul, map_mul, map_inv]
  have hsq : Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL g = 1 := by
    rw [← map_mul, hgg, map_one]
  obtain ⟨P, σ₁, -, hP₁, -⟩ := exists_chart_gl hn h2 Ψ hx hx hsq hsq rfl
  refine ⟨P, σ₁, fun y => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hP₁ y

theorem conj_preimage {X : Type} [Group X] (Ψ : SL(n, F) →* X) {c : X}
    (hc : ∀ y, Ψ y = c → (y : Matrix (Fin n) (Fin n) F) = -1) (P : SL(n, F)) :
    ∀ y, (Ψ.comp (MulAut.conj P).toMonoidHom) y = c → (y : Matrix (Fin n) (Fin n) F) = -1 := by
  intro y hy
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy
  have h1 := hc _ hy
  have e : y = P⁻¹ * (P * y * P⁻¹) * P := by group
  calc (y : Matrix (Fin n) (Fin n) F) =
      ((P⁻¹ * (P * y * P⁻¹) * P : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        congrArg (fun z : SL(n, F) => (z : Matrix (Fin n) (Fin n) F)) e
    _ = (P⁻¹ : SL(n, F)) * ((P * y * P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) * P := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    _ = -1 := by
        rw [h1, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem exists_large_block (hn : 6 ≤ n) (σ : Fin n → Bool) :
    ∃ b₀, 3 ≤ (coordSet σ b₀).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => σ i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hfalse : Finset.univ.filter (fun i : Fin n => ¬ σ i = true) = coordSet σ false := by
    ext i
    simp [coordSet]
  have htrue : Finset.univ.filter (fun i : Fin n => σ i = true) = coordSet σ true := rfl
  rw [hfalse, htrue] at h
  by_cases h3 : 3 ≤ (coordSet σ true).card
  · exact ⟨true, h3⟩
  · exact ⟨false, by omega⟩

end P58b3L

open P58b3L in
theorem harris82Lemma58bThreeRow_PSL_of_six_le (h51E4 : Harris82Lemma51E4) {n : ℕ} (hn : 6 ≤ n) :
    Harris82Lemma58bThreeRow .PSL n := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ he₁ hKc hO₁ _ _ hz₂K hz₂Z f hm
  obtain rfl := field_eq_one h51E4 hz₁ hz₂ hL₁ hz₁L he₁ hKc hO₁ hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  obtain ⟨Q, hQt, hQsub, -, hQsolv, a, ha, b, hb, haa, hbb, hab⟩ :=
    exists_quat_config hz₁ hz₂ hL₁ hz₁L he₁ hKc.1 hO₁ hz₁K hz₂K
  obtain ⟨F, _, _, Ψ, hF, hΨi, hΨs, hΨc⟩ := exists_sl_iso hX hO (by omega) hmX
    (mk_ne_one hz₁ hz₁K) (mk_mem_center hKc.1 hz₁K)
  have h2 : (2 : F) ≠ 0 := Foote5.OddLieCore.two_ne_zero_of_card hF
  obtain ⟨P, σ, hf⟩ := exists_sign_chart h2 (by omega) Ψ hΨi hΨs (mk_mul_self hz₂ hz₂K)
  obtain ⟨b₀, hb₀⟩ := exists_large_block hn σ
  exact false_of_block hF (Ψ.comp (MulAut.conj P).toMonoidHom)
    (hΨi.comp (MulAut.conj P).injective) (hΨs.comp (MulAut.conj P).surjective) hf hb₀ hQt hQsub
    hQsolv ha hb (conj_preimage Ψ hΨc P) haa hbb hab

end CFSG.ComponentClassification.HarrisLit.T1
