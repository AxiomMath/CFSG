module

public import CFSG.ClassicalInvolution.Q3.Q3T6YLift
public import CFSG.ClassicalInvolution.Q3.Q3T6BTwinP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem exists_mul_mem_zpowers_pow_two_eq_one {N : Subgroup F} {h : F} {e : ℕ}
    (hodd : Odd (Nat.card N)) (hh : h ^ 2 ^ e ∈ N) :
    ∃ n ∈ Subgroup.zpowers (h ^ 2 ^ e), (h * n) ^ 2 ^ e = 1 := by
  have hz : Odd (Nat.card (Subgroup.zpowers (h ^ 2 ^ e))) := by
    refine hodd.of_dvd_nat ?_
    exact Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hh)
  exact exists_mul_mem_pow_two_eq_one hz (Subgroup.mem_zpowers _)

theorem twinProd_act_mem_inn3' {K J : Subgroup F} {t : F} (hJ : Mem3 J t)
    (htK : ∀ k ∈ K, k * t = t * k)
    (e : J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3)) {p : F}
    (hp : p ∈ twinProd K J) :
    ∃ hpN : p ∈ Subgroup.normalizer (J : Set F),
      Q3T6.normalizerToAutSL3 e ⟨p, hpN⟩ ∈ Q3T6.inn3 := by
  have hJK : J ∈ twinClass K J := ⟨1, K.one_mem, (conjSub_one J).symm⟩
  let Kin : Subgroup F :=
    (Q3T6.inn3.comap (Q3T6.normalizerToAutSL3 e)).map (Subgroup.normalizer (J : Set F)).subtype
  have hle : twinProd K J ≤ Kin := by
    refine iSup₂_le fun L hL l hl => ?_
    have hlN : l ∈ Subgroup.normalizer (J : Set F) :=
      le_normalizer_of_mem_twinClass hJ htK hJK hL hl
    refine ⟨⟨l, hlN⟩, ?_, rfl⟩
    show Q3T6.normalizerToAutSL3 e ⟨l, hlN⟩ ∈ Q3T6.inn3
    by_cases hLJ : J = L
    · subst hLJ
      rw [Q3T6.normalizerToAutSL3_of_mem e hl]
      exact Q3T6.conj_mem_inn3 _
    · have h1 : Q3T6.normalizerToAutSL3 e ⟨l, hlN⟩ = 1 := by
        rw [Q3T6.normalizerToAutSL3_eq_one_iff]
        intro y hy
        exact Mem3.commutator_mem_of_twin hJ (mem3_of_mem_twinClass hJ htK hL) hLJ hl y hy
      rw [h1]
      exact Q3T6.inn3.one_mem
  obtain ⟨n, hn, rfl⟩ := hle hp
  exact ⟨n.2, hn⟩

theorem oddCoreOf_conj_mem {Y : Subgroup F} {a n : F} (ha : a ∈ Y) (hn : n ∈ oddCoreOf Y) :
    a * n * a⁻¹ ∈ oddCoreOf Y :=
  (Subgroup.mem_normalizer_iff.mp
    (AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer ha)) n).mp hn

theorem not_mem_inn3_of_outer' {Y : Subgroup F} {y x : F} (hY : Mem3 Y y)
    (eY : Y ⧸ classicalInvolutionOddCore Y ≃* SL(2, ZMod 3))
    (hxY : x ∈ Subgroup.normalizer (Y : Set F)) (hx2 : x * x = 1)
    (hρ1 : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ ≠ 1)
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) :
    Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ ∉ Q3T6.inn3 := by
  classical
  rintro ⟨b, hb⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eY.symm b)
  have hbk : eY (QuotientGroup.mk k) = b := by rw [hk, MulEquiv.apply_symm_apply]
  have hkN : (k : F) ∈ Subgroup.normalizer (Y : Set F) := Subgroup.le_normalizer k.2
  have hτk : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ =
      Q3T6.normalizerToAutSL3 eY ⟨(k : F), hkN⟩ := by
    rw [Q3T6.normalizerToAutSL3_of_mem eY k.2, hbk, hb]
  have hxk : ∀ l ∈ Y, ⁅x * (k : F)⁻¹, l⁆ ∈ oddCoreOf Y := by
    intro l hl
    have h1 : Q3T6.normalizerToAutSL3 eY (⟨x, hxY⟩ * ⟨(k : F), hkN⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hτk, mul_inv_cancel]
    exact (Q3T6.normalizerToAutSL3_eq_one_iff eY _).mp h1 l hl
  have hτ2 : Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ * Q3T6.normalizerToAutSL3 eY ⟨x, hxY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : Subgroup.normalizer (Y : Set F)) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hkk1 : Q3T6.normalizerToAutSL3 eY (⟨(k : F), hkN⟩ * ⟨(k : F), hkN⟩) = 1 := by
    rw [map_mul, ← hτk]
    exact hτ2
  have hkkc : ∀ l ∈ Y, ⁅(k : F) * k, l⁆ ∈ oddCoreOf Y :=
    (Q3T6.normalizerToAutSL3_eq_one_iff eY _).mp hkk1
  have hmkk : (QuotientGroup.mk k : OddQuot Y) * QuotientGroup.mk k =
      QuotientGroup.mk ⟨(k : F) * k, Y.mul_mem k.2 k.2⟩ := by
    rw [← QuotientGroup.mk_mul]
    rfl
  have hyy : (QuotientGroup.mk (⟨y, hY.mem⟩ : ↥Y) : OddQuot Y) *
      QuotientGroup.mk (⟨y, hY.mem⟩ : ↥Y) = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨y, hY.mem⟩ * ⟨y, hY.mem⟩ : ↥Y) = 1 := Subtype.ext hY.mul_self
    rw [this, QuotientGroup.mk_one]
  rcases (hY.mem_center_oddQuot_iff _).mp (mk_mem_center_of_forall (Y.mul_mem k.2 k.2) hkkc)
    with h1 | h1
  ·
    exfalso
    apply hρ1
    have hw : (QuotientGroup.mk k : OddQuot Y) * QuotientGroup.mk k = 1 := by rw [hmkk]; exact h1
    have hmkc : (QuotientGroup.mk k : OddQuot Y) ∈ Subgroup.center (OddQuot Y) := by
      rcases hY.oddQuot_eq_one_or_eq hw with h2 | h2
      · rw [h2]
        exact Subgroup.one_mem _
      · rw [h2]
        exact hY.mk_mem_center
    rw [hτk, Q3T6.normalizerToAutSL3_eq_one_iff]
    exact forall_comm_of_mk_mem_center k.2 hmkc
  ·
    have hxkc : ⁅x, (k : F)⁆ ∈ oddCoreOf Y := by
      have := hxk k k.2
      have e1 : ⁅x * (k : F)⁻¹, (k : F)⁆ = ⁅x, (k : F)⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [e1] at this
    have hx0 : (k : F)⁻¹ * (x * (k : F) * x⁻¹) ∈ oddCoreOf Y := by
      have h2 := oddCoreOf_conj_mem (Y.inv_mem k.2) hxkc
      have e2 : (k : F)⁻¹ * ⁅x, (k : F)⁆ * ((k : F)⁻¹)⁻¹ = (k : F)⁻¹ * (x * (k : F) * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rwa [e2] at h2
    have hxO : ∀ n ∈ oddCoreOf Y, x * n * x⁻¹ ∈ oddCoreOf Y := fun n hn =>
      (Subgroup.mem_normalizer_iff.mp
        (AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' hxY) n).mp hn
    obtain ⟨n, hn, hfix⟩ :=
      exists_fixed_mul_mem hx2 (oddCoreOf_odd_natCard Y) hxO hx0
    set k₁ : F := (k : F) * n with hk₁
    have hk₁Y : k₁ ∈ Y := Y.mul_mem k.2 (oddCoreOf_le_self Y hn)
    have hk₁x : k₁ * x = x * k₁ := by
      have h3 : x * k₁ * x⁻¹ = k₁ := hfix
      calc k₁ * x = (x * k₁ * x⁻¹) * x := by rw [h3]
        _ = x * k₁ := by group
    have hk₁4 : k₁ ^ 2 ^ 2 ∈ oddCoreOf Y := by
      have hmk₁ : (QuotientGroup.mk k : OddQuot Y) = QuotientGroup.mk (⟨k₁, hk₁Y⟩ : ↥Y) := by
        rw [QuotientGroup.eq]
        have : k⁻¹ * (⟨k₁, hk₁Y⟩ : ↥Y) = ⟨n, oddCoreOf_le_self Y hn⟩ := by
          apply Subtype.ext
          show (k : F)⁻¹ * ((k : F) * n) = n
          group
        rw [this]
        exact (mem_oddCoreOf_iff.mp hn).2
      have h4 : (QuotientGroup.mk (⟨k₁, hk₁Y⟩ : ↥Y) : OddQuot Y) ^ 2 ^ 2 = 1 := by
        rw [← hmk₁, show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two, hmkk, h1, hyy]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h4
      exact mem_oddCoreOf_iff.mpr ⟨Y.pow_mem hk₁Y _, h4⟩
    obtain ⟨n', hn', hk₂⟩ :=
      exists_mul_mem_zpowers_pow_two_eq_one (oddCoreOf_odd_natCard Y) hk₁4
    have hn'O : n' ∈ oddCoreOf Y := (Subgroup.zpowers_le.mpr hk₁4) hn'
    have hk₂Y : k₁ * n' ∈ Y := Y.mul_mem hk₁Y (oddCoreOf_le_self Y hn'O)
    have hk₂x : (k₁ * n') * x = x * (k₁ * n') := by
      have hn'x : n' * x = x * n' := by
        have hc : Subgroup.zpowers (k₁ ^ 2 ^ 2) ≤ Subgroup.centralizer ({x} : Set F) := by
          rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Commute.pow_left (show Commute k₁ x from hk₁x) _).eq
        exact Subgroup.mem_centralizer_singleton_iff.mp (hc hn')
      calc (k₁ * n') * x = k₁ * (n' * x) := mul_assoc _ _ _
        _ = k₁ * (x * n') := by rw [hn'x]
        _ = (k₁ * x) * n' := (mul_assoc _ _ _).symm
        _ = (x * k₁) * n' := by rw [hk₁x]
        _ = x * (k₁ * n') := mul_assoc _ _ _
    have hmk₂ : (QuotientGroup.mk k : OddQuot Y) = QuotientGroup.mk (⟨k₁ * n', hk₂Y⟩ : ↥Y) := by
      rw [QuotientGroup.eq]
      have hmem : (k : F)⁻¹ * (k₁ * n') = n * n' := by rw [hk₁]; group
      have : k⁻¹ * (⟨k₁ * n', hk₂Y⟩ : ↥Y) =
          ⟨n * n', Y.mul_mem (oddCoreOf_le_self Y hn) (oddCoreOf_le_self Y hn'O)⟩ :=
        Subtype.ext hmem
      rw [this]
      exact (mem_oddCoreOf_iff.mp ((oddCoreOf Y).mul_mem hn hn'O)).2
    have hk₂1 : ¬ (k₁ * n') ^ 2 ^ 1 = 1 := by
      intro h2
      have h3 : (QuotientGroup.mk (⟨k₁ * n', hk₂Y⟩ : ↥Y) : OddQuot Y) ^ 2 ^ 1 = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨k₁ * n', hk₂Y⟩ : ↥Y) ^ 2 ^ 1 = 1 := Subtype.ext h2
        rw [this, QuotientGroup.mk_one]
      rw [← hmk₂, pow_one, pow_two, hmkk, h1] at h3
      exact hY.mk_ne_one h3
    have hk₂4 : orderOf (k₁ * n') = 4 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 := orderOf_eq_prime_pow hk₂1 (show (k₁ * n') ^ 2 ^ (1 + 1) = 1 from hk₂)
      rwa [show (2 : ℕ) ^ (1 + 1) = 4 from rfl] at h2
    exact hout (k₁ * n') hk₂Y hk₂4 hk₂x

end CFSG.ClassicalInvolution.Q3.Q3T6Y
