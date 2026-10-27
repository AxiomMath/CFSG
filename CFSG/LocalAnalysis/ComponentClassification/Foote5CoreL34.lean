module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreBal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement

@[expose] def FooteCoreL34Input : Prop :=
  ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀], Group.IsPerfect Y₀ →
    Blueprint.LieModel (Y₀ ⧸ center Y₀) .PSL 3 2 2 →
    ∀ α : MulAut Y₀, (∀ y, α (α y) = y) →
    ∀ A : Subgroup (MulAut Y₀), Odd (Nat.card A) → (∀ β ∈ A, β * α = α * β) →
      (∀ c : Y₀, α c = c → ∀ β ∈ A, MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A) →
      (∀ β ∈ A, ∀ z ∈ center Y₀, α z = z → (∃ k : ℕ, orderOf z = 2 ^ k) → β z = z) →
      ∀ β₁ ∈ A, ∀ β₂ ∈ A, ∀ y : Y₀, (β₁ * β₂ * β₁⁻¹ * β₂⁻¹) y * y⁻¹ ∈ center Y₀

theorem exists_fixed_mem_coset_of_involutive {Y : Type*} [Group Y] (N : Subgroup Y)
    (hN : Odd (Nat.card N)) {α : MulAut Y} (hα : ∀ y, α (α y) = y) {y : Y}
    (hy : y⁻¹ * α y ∈ N) : ∃ c : Y, α c = c ∧ y⁻¹ * c ∈ N := by
  have hyx : α y = y * (y⁻¹ * α y) := by group
  have hαx : α (y⁻¹ * α y) = (y⁻¹ * α y)⁻¹ := by
    rw [map_mul, map_inv, hα]
    group
  have hxodd : Odd (orderOf (y⁻¹ * α y)) := by
    have : Finite N := Nat.finite_of_card_ne_zero (by rcases hN with ⟨k, hk⟩; omega)
    exact Odd.of_dvd_nat hN (N.orderOf_dvd_natCard hy)
  set x := y⁻¹ * α y
  set k := (orderOf x + 1) / 2
  have h2k : 2 * k = orderOf x + 1 := by
    have := Nat.odd_iff.mp hxodd
    omega
  refine ⟨y * x ^ k, ?_, by simpa using pow_mem hy k⟩
  rw [map_mul, map_pow, hαx, inv_pow, hyx, mul_assoc]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, ← pow_add, ← two_mul, h2k, pow_succ, pow_orderOf_eq_one, one_mul]

theorem oddAut_conj {Y : Type*} [Group Y] (c : Y) :
    oddAut Y (MulAut.conj c) = MulAut.conj (QuotientGroup.mk c) := by
  ext s
  induction s using QuotientGroup.induction_on
  simp [MulAut.conj_apply]

theorem exists_two_pow_orderOf_mul_inv {G : Type*} [Group G] {u v : G} (huv : Commute u v)
    {k l : ℕ} (hu : orderOf u = 2 ^ k) (hv : orderOf v = 2 ^ l) :
    ∃ m : ℕ, orderOf (u * v⁻¹) = 2 ^ m := by
  have h1 : u ^ (2 ^ (k + l)) = 1 := by
    rw [pow_add, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]
  have h2 : v⁻¹ ^ (2 ^ (k + l)) = 1 := by
    rw [inv_pow, add_comm, pow_add, pow_mul, ← hv, pow_orderOf_eq_one, one_pow, inv_one]
  have hdvd : orderOf (u * v⁻¹) ∣ 2 ^ (k + l) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(huv.inv_right).mul_pow, h1, h2, one_mul]
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨m, hm⟩

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_L34 (hL34 : FooteCoreL34Input) (hLB : FooteLBalanceInput) {a : K}
    (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (hm : Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 3 2 2) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  have hWW := commutator_self_le W
  by_cases hswap : conjugate Y a ≠ Y
  · exact ((commutator_mono hWW le_rfl).trans (hcent (Or.inl hswap))).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set ψ := Y.normalizerMonoidHom
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hone : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
  set α := ψ ⟨a, haN⟩ with hαdef
  have hα : ∀ y, α (α y) = y := fun y => by
    rw [← MulAut.mul_apply, hαdef, ← map_mul, hone, map_one, MulAut.one_apply]
  set O := Open.fusionOddCore ↥Y with hO
  have hOodd : Odd (Nat.card O) := by
    rw [hO, UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 Y hY
  have hq₁ : IsQuasisimple (↥Y ⧸ O) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (UnbalancingLocal.fusionOddCore_eq_pPrimeCore ↥Y)).symm hq
  have hmap : (Open.fusionZStar ↥Y).map (QuotientGroup.mk' O) = center (↥Y ⧸ O) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  let e : (↥Y ⧸ O) ⧸ center (↥Y ⧸ O) ≃* ↥Y ⧸ Open.fusionZStar ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (Open.fusionZStar ↥Y)
        fusionOddCore_le_fusionZStar)
  have hm₀ : Blueprint.LieModel ((↥Y ⧸ O) ⧸ center (↥Y ⧸ O)) .PSL 3 2 2 :=
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  set α₀ := oddAut ↥Y α with hα₀def
  have hα₀ : ∀ y, α₀ (α₀ y) = y := fun y => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hα₀def, oddAut_mk, oddAut_mk, hα]
  set A := (W.subgroupOf (normalizer (Y : Set K))).map ψ with hA
  set A₀ := A.map (oddAut ↥Y) with hA₀
  have hlift : ∀ y : ↥Y, α₀ (QuotientGroup.mk y) = QuotientGroup.mk y →
      ∃ c : ↥Y, α c = c ∧ (QuotientGroup.mk c : ↥Y ⧸ O) = QuotientGroup.mk y := by
    intro y hy
    rw [hα₀def, oddAut_mk] at hy
    obtain ⟨c, hc, hyc⟩ :=
      exists_fixed_mem_coset_of_involutive O hOodd hα (QuotientGroup.eq.mp hy.symm)
    exact ⟨c, hc, (QuotientGroup.eq.mpr hyc).symm⟩
  have hA₀odd : Odd (Nat.card A₀) :=
    Odd.of_dvd_nat (odd_card_map_oddCore hWN) (card_map_dvd _ _)
  have hA₀comm : ∀ β ∈ A₀, β * α₀ = α₀ * β := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [hα₀def, ← map_mul, ← map_mul, map_oddCore_commute haN β hβ]
  have hA₀conj : ∀ c : ↥Y ⧸ O, α₀ c = c → ∀ β ∈ A₀,
      MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A₀ := by
    rintro c hc _ ⟨β, hβ, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨c', hc', hmk⟩ := hlift y hc
    refine ⟨MulAut.conj c' * β * (MulAut.conj c')⁻¹, map_oddCore_conj haN c' hc' β hβ, ?_⟩
    rw [map_mul, map_mul, map_inv, oddAut_conj, hmk]
  have hA₀fix : ∀ β ∈ A₀, ∀ z ∈ center (↥Y ⧸ O), α₀ z = z → (∃ k : ℕ, orderOf z = 2 ^ k) →
      β z = z := by
    rintro _ ⟨_, ⟨⟨w, hwN⟩, hw, rfl⟩, rfl⟩ z hz hzα ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨c, hc, hmk⟩ := hlift y hzα
    rw [← hmk] at hz hk ⊢
    have hcK : (c : K) ∈ centralizer ({a} : Set K) := by
      have h := congrArg Subtype.val hc
      rw [hαdef, normalizerMonoidHom_apply_apply_coe] at h
      apply mem_centralizer_singleton_iff.mpr
      calc (c : K) * a = a * c * a⁻¹ * a := by rw [h]
        _ = a * c := by group
    have hwW : w ∈ W := mem_subgroupOf.mp hw
    set u : ↥Y := ψ ⟨w, hwN⟩ c * c⁻¹ with hu
    have huK : (u : K) = w * c * w⁻¹ * (c : K)⁻¹ := by
      rw [hu, coe_mul, normalizerMonoidHom_apply_apply_coe, coe_inv]
    have huW : (u : K) ∈ W := by
      rw [huK, mul_assoc (w * c), mul_assoc w]
      exact mul_mem hwW (by
        have h := conj_mem_oddCoreOfCentralizer hcK (inv_mem hwW)
        simpa [mul_assoc] using h)
    have hWodd : Odd (Nat.card W) := by
      have h : Nat.card W = Nat.card (pPrimeCore 2 ↥(centralizer ({a} : Set K))) :=
        card_map_of_injective (subtype_injective _)
      rw [h]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have huodd : Odd (orderOf (QuotientGroup.mk u : ↥Y ⧸ O)) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' O) u)
      rw [← Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hWodd (W.orderOf_dvd_natCard huW)
    set β := oddAut ↥Y (ψ ⟨w, hwN⟩) with hβ
    have himage : (QuotientGroup.mk u : ↥Y ⧸ O) = β (QuotientGroup.mk c) *
        (QuotientGroup.mk c)⁻¹ := by
      rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hβ, oddAut_mk]
    have hβz : β (QuotientGroup.mk c) ∈ center (↥Y ⧸ O) := by
      refine mem_center_iff.mpr fun g => ?_
      obtain ⟨g', rfl⟩ := β.surjective g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz g')]
    obtain ⟨m, hm2⟩ := exists_two_pow_orderOf_mul_inv
      (mem_center_iff.mp hz (β (QuotientGroup.mk c)))
      (by rw [MulEquiv.orderOf_eq]; exact hk) hk
    rw [← himage] at hm2
    have h1 : orderOf (QuotientGroup.mk u : ↥Y ⧸ O) = 1 := by
      rw [hm2] at huodd ⊢
      rcases m with _ | m
      · rfl
      · exact absurd huodd (Nat.not_odd_iff_even.mpr (by rw [pow_succ]; exact even_two.mul_left _))
    rw [orderOf_eq_one_iff, himage, mul_inv_eq_one] at h1
    exact h1
  have hres := hL34 (↥Y ⧸ O) hq₁.1 hm₀ α₀ hα₀ A₀ hA₀odd hA₀comm hA₀conj hA₀fix
  have hmemA₀ : ∀ w (h : w ∈ W), oddAut ↥Y (ψ ⟨w, hWN h⟩) ∈ A₀ := fun w h =>
    ⟨ψ ⟨w, hWN h⟩, ⟨⟨w, hWN h⟩, mem_subgroupOf.mpr h, rfl⟩, rfl⟩
  have hker : ⁅W, W⁆ ≤ ((zStarAut ↥Y).comp ψ).ker.map (normalizer (Y : Set K)).subtype := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    refine ⟨⁅(⟨w₁, hWN hw₁⟩ : normalizer (Y : Set K)), ⟨w₂, hWN hw₂⟩⁆, ?_,
      by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext s
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
    have h := hres _ (hmemA₀ w₁ hw₁) _ (hmemA₀ w₂ hw₂) (QuotientGroup.mk y)
    have hσ : oddAut ↥Y (ψ ⁅(⟨w₁, hWN hw₁⟩ : normalizer (Y : Set K)), ⟨w₂, hWN hw₂⟩⁆) =
        oddAut ↥Y (ψ ⟨w₁, hWN hw₁⟩) * oddAut ↥Y (ψ ⟨w₂, hWN hw₂⟩) *
          (oddAut ↥Y (ψ ⟨w₁, hWN hw₁⟩))⁻¹ * (oddAut ↥Y (ψ ⟨w₂, hWN hw₂⟩))⁻¹ := by
      rw [map_commutatorElement, map_commutatorElement, commutatorElement_def]
    rw [← hσ, oddAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h
    have h' := (QuotientGroup.eq_one_iff _).mpr ((mem_fusionZStar_iff _).mpr h)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h'
    rw [MonoidHom.comp_apply, zStarAut_mk, MulAut.one_apply]
    exact h'
  rw [commutator_le]
  intro g hg y hy
  obtain ⟨n, hn, rfl⟩ := hker hg
  exact hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY n.2 (by simpa using hn) hy)

end CFSG.ComponentClassification.Foote5
