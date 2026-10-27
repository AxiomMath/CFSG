module

public import CFSG.Certificates.Kernel.Fin76bAut.Pos
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E615Def
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69
open scoped Pointwise

theorem ptK_pos {G T PL POS SRT SRI : ℕ → ℕ} {k cnt i : ℕ}
    (h : penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true) :
    ∀ j < k, ∃ q < cnt, T q = eC (G j) (T i) := by
  intro j hj
  unfold penumPtK at h
  rw [strictB_eq] at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, hp, -⟩ := h
  have h1 := allN_iff.1 hp j hj
  rw [strictB_eq] at h1
  simp only [bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨_, Nat.le_of_ble_eq_true h1.1, beq_t.1 h1.2.1⟩

theorem eSylHdK_spec {cnt kS cntS : ℕ} {T SP ST SPL : ℕ → ℕ}
    (h : eSylHdK cnt T SP kS cntS ST SPL = true) : (∀ j < kS, SP j < cnt) ∧ ST 0 = eId := by
  unfold eSylHdK penumHdK at h
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff] at h
  obtain ⟨hsp, -, -, h0, -⟩ := h
  exact ⟨fun j hj => Nat.le_of_ble_eq_true (hsp j hj), beq_t.1 h0⟩

section Syl

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  {Φ : ℕ → MulAut H}

include hM in
theorem ea_le_of_checks (pd : PosData R T cnt Φ) (hcard : Nat.card (MulAut H) = 1920)
    {GN kg f c : ℕ} (htup : eTupK ET GN kg f c = true) {SP ST SPL SPOS SSRT SSRI : ℕ → ℕ}
    {kS : ℕ} (hhd : eSylHdK cnt T SP kS 128 ST SPL = true)
    (hsl : ∀ i < 128, penumPtK 32 6 63 192 false (fun j => T (SP j)) (fun j => T (SP j)) kS 128
      ST SPL SPOS SSRT SSRI i = true)
    (he : e615K GN kg 128 ST = true) (A : Subgroup (MulAut H))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 16 := by
  classical
  have := finite_mulAut R
  obtain ⟨hSP, hST0⟩ := eSylHdK_spec hhd
  have hex : ∀ i < 128, ∃ ψ : MulAut H, Acts R ψ (ST i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        exact ⟨1, by rw [hST0]; exact acts_one R⟩
      · obtain ⟨h1, h2, h3⟩ := (ptK_spec (hsl i hi)).2.1 (by omega)
        obtain ⟨ψ, hψ⟩ := ih _ h1 (by omega)
        exact ⟨Φ (SP (labOf SPL i)) * ψ, by rw [h3]; exact (pd.acts _ (hSP _ h2)).mul hψ⟩
  choose! Ψ hΨ using hex
  have hΨinj : ∀ i < 128, ∀ j < 128, Ψ i = Ψ j → i = j := fun i hi j hj e =>
    rec_inj hsl i hi j hj fun a ha => by rw [← hΨ i hi a ha, ← hΨ j hj a ha, e]
  have hΨ0 : Ψ 0 = 1 := (hΨ 0 (by norm_num)).ext (acts_one R) fun a _ => by rw [hST0]
  have hcan : ∀ i < 128, canonK 32 6 63 192 (ST i) = true := fun i hi => (ptK_spec (hsl i hi)).1
  let S : Subgroup (MulAut H) := Subgroup.closure {x | ∃ j < kS, Φ (SP j) = x}
  have hmemS : ∀ i < 128, Ψ i ∈ S := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hΨ0]
        exact one_mem S
      · obtain ⟨h1, h2, h3⟩ := (ptK_spec (hsl i hi)).2.1 (by omega)
        have e : Ψ i = Φ (SP (labOf SPL i)) * Ψ (parOf SPL i) :=
          (hΨ i hi).ext ((pd.acts _ (hSP _ h2)).mul (hΨ _ (by omega))) fun a _ => by rw [h3]
        rw [e]
        exact mul_mem (Subgroup.subset_closure ⟨_, h2, rfl⟩) (ih _ h1 (by omega))
  have hmulS : ∀ x ∈ S, ∀ i < 128, ∃ i' < 128, Ψ i' = x * Ψ i := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      obtain ⟨q, hq, e⟩ := ptK_pos (hsl i hi) j hj
      exact ⟨q, hq, (hΨ q hq).ext ((pd.acts _ (hSP j hj)).mul (hΨ i hi)) fun a _ => by rw [e]⟩
    | one => exact fun i hi => ⟨i, hi, (one_mul _).symm⟩
    | mul x y _ _ hx hy =>
      intro i hi
      obtain ⟨i', hi', e'⟩ := hy i hi
      obtain ⟨i'', hi'', e''⟩ := hx i' hi'
      exact ⟨i'', hi'', by rw [e'', e', mul_assoc]⟩
    | inv x _ hx =>
      choose! g hg using hx
      have hinj : Set.InjOn g (Finset.range 128) := by
        intro i hi j hj e
        have hi' := Finset.mem_range.1 hi
        have hj' := Finset.mem_range.1 hj
        have e2 : x * Ψ i = x * Ψ j := by rw [← (hg i hi').2, ← (hg j hj').2, e]
        exact hΨinj i hi' j hj' (mul_left_cancel e2)
      have himg : (Finset.range 128).image g = Finset.range 128 :=
        Finset.eq_of_subset_of_card_le (fun y hy => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
          exact Finset.mem_range.2 (hg i (Finset.mem_range.1 hi)).1)
          (by rw [Finset.card_image_of_injOn hinj])
      intro i hi
      have hmem : i ∈ (Finset.range 128).image g := by
        rw [himg]
        exact Finset.mem_range.2 hi
      obtain ⟨i'', hi'', e⟩ := Finset.mem_image.1 hmem
      refine ⟨i'', Finset.mem_range.1 hi'', ?_⟩
      have e2 := (hg i'' (Finset.mem_range.1 hi'')).2
      rw [e] at e2
      rw [e2, inv_mul_cancel_left]
  have hS : ∀ x, x ∈ S ↔ ∃ i < 128, Ψ i = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i', hi', e⟩ := hmulS x hx 0 (by norm_num)
      exact ⟨i', hi', by rw [e, hΨ0, mul_one]⟩
    · rintro ⟨i, hi, rfl⟩
      exact hmemS i hi
  have hSset : (S : Set (MulAut H)) = ↑((Finset.range 128).image Ψ) := by
    ext x
    rw [SetLike.mem_coe, hS, Finset.coe_image, Finset.coe_range]
    simp only [Set.mem_image, Set.mem_Iio]
  have hcS : Nat.card S = 128 := by
    have e2 : Nat.card S = (S : Set (MulAut H)).ncard := Nat.card_coe_set_eq _
    rw [e2, hSset, Set.ncard_coe_finset, Finset.card_image_of_injOn (fun i hi j hj e =>
      hΨinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e), Finset.card_range]
  have hidx : S.index = 15 := by
    have h1 := S.card_mul_index
    rw [hcS, hcard] at h1
    omega
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [hcS]; norm_num)
  let P : Sylow 2 (MulAut H) := hSp.toSylow (by rw [hidx]; norm_num)
  by_contra hgt
  rw [not_le] at hgt
  have hAp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
    exact hsq x x.2)⟩
  have hA32 : 32 ≤ Nat.card A := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hAp
    rw [hn] at hgt ⊢
    by_contra hlt
    have h4 : n ≤ 4 := by
      by_contra h5
      exact hlt (by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    omega
  obtain ⟨Q, hQ⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut H) P Q
  let γ : MulAut H ≃* MulAut H := MulAut.conj g⁻¹
  have hγS : ∀ x ∈ A, γ x ∈ S := by
    intro x hx
    have hx' : x ∈ MulAut.conj g • S := by
      have := hQ hx
      rw [← hg] at this
      exact this
    obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) S).1 hx'
    have e : γ (MulAut.conj g • y) = y := by
      rw [MulAut.smul_def, ← MulAut.mul_apply]
      change (MulAut.conj g⁻¹ * MulAut.conj g) y = y
      rw [← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [e]
    exact hy
  let Y : Set ℕ := {i | i < 128 ∧ Ψ i ∈ γ '' ((A : Set (MulAut H)) \ {1})}
  have hYimg : Ψ '' Y = γ '' ((A : Set (MulAut H)) \ {1}) := by
    ext z
    constructor
    · rintro ⟨i, ⟨-, hz⟩, rfl⟩
      exact hz
    · intro hz
      obtain ⟨x, ⟨hxA, hx1⟩, rfl⟩ := hz
      obtain ⟨i, hi, e⟩ := (hS _).1 (hγS x hxA)
      exact ⟨i, ⟨hi, by rw [e]; exact ⟨x, ⟨hxA, hx1⟩, rfl⟩⟩, e⟩
  have hY31 : 31 ≤ Y.ncard := by
    have h1 : Y.ncard = (Ψ '' Y).ncard :=
      (Set.InjOn.ncard_image fun i hi j hj e => hΨinj i hi.1 j hj.1 e).symm
    have h2 : (γ '' ((A : Set (MulAut H)) \ {1})).ncard = ((A : Set (MulAut H)) \ {1}).ncard :=
      Set.ncard_image_of_injective _ γ.injective
    have h3 : ((A : Set (MulAut H)) \ {1}).ncard = Nat.card A - 1 := by
      rw [Set.ncard_diff_singleton_of_mem (one_mem A)]
      rfl
    rw [h1, hYimg, h2, h3]
    omega
  have hYinv : ∀ i ∈ Y, Ψ i * Ψ i = 1 ∧ Ψ i ≠ 1 := by
    rintro i ⟨-, x, ⟨hxA, hx1⟩, e⟩
    rw [← e]
    refine ⟨by rw [← map_mul, hsq x hxA, map_one], fun h => hx1 ?_⟩
    rw [← map_one γ] at h
    exact γ.injective h
  have hYcomm : ∀ i ∈ Y, ∀ j ∈ Y, Ψ i * Ψ j = Ψ j * Ψ i := by
    rintro i ⟨-, x, ⟨hxA, -⟩, e⟩ j ⟨-, y, ⟨hyA, -⟩, e'⟩
    rw [← e, ← e', ← map_mul, ← map_mul, hcomm x hxA y hyA]
  have hlt := Nat.blt_eq.mp he
  rw [eCnt_eq_card] at hlt
  refine absurd hlt (not_lt.2 (le_trans hY31 ?_))
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun i hi => ?_) (Finset.finite_toSet _)
  have hi128 : i < 128 := hi.1
  rw [Finset.coe_filter]
  refine ⟨Finset.mem_range.2 hi128, ?_⟩
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true]
  refine ⟨((hΨ i hi128).eInvG_iff hM htup (hcan i hi128)).2 (hYinv i hi), Nat.ble_eq.mpr ?_⟩
  rw [eCnt_eq_card]
  refine le_trans hY31 ?_
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun j hj => ?_) (Finset.finite_toSet _)
  have hj128 : j < 128 := hj.1
  rw [Finset.coe_filter]
  refine ⟨Finset.mem_range.2 hj128, ?_⟩
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true]
  exact ⟨((hΨ j hj128).eInvG_iff hM htup (hcan j hj128)).2 (hYinv j hj),
    ((hΨ i hi128).comm_iff hM htup (hΨ j hj128)).1 (hYcomm i hi j hj)⟩

end Syl

theorem eFacts615_of_checks {G : Type u} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ}
    {eltE : ℕ → G} {ET : ℕ → ℕ} (hL : ELabelling E t mulE 21 eltE)
    (hET : ∀ a < 32, ∀ b < 32, mulE a b = eMul ET a b) {T : ℕ → ℕ} {GN kg f c : ℕ}
    (hrec : RecOK.{u} ET 1920 T) (htup : eTupK ET GN kg f c = true)
    {SP ST SPL SPOS SSRT SSRI : ℕ → ℕ} {kS : ℕ} (hhd : eSylHdK 1920 T SP kS 128 ST SPL = true)
    (hsl : ∀ i < 128, penumPtK 32 6 63 192 false (fun j => T (SP j)) (fun j => T (SP j)) kS 128
      ST SPL SPOS SSRT SSRI i = true)
    (he : e615K GN kg 128 ST = true) : EFacts615 E t := by
  obtain ⟨elt, R, -⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  obtain ⟨Φ, pd⟩ := exists_posData R hM hrec
  exact ⟨fun A hcomm hsq => ea_le_of_checks R hM pd (hrec _ _ _ R hM).2.2 htup hhd hsl he A
    hcomm hsq⟩

end CFSG.KS.EAut

end
