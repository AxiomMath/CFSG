module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Hyp
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCJ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open scoped Matrix

variable {G : Type} [Group G]

section J

variable {A : Subgroup G}

theorem le_pCoreIn_two {X H : Subgroup G} (hXH : X ≤ H) (hnorm : H ≤ normalizer (X : Set G))
    (hX : IsPGroup 2 X) : X ≤ CFSG.ABGTheoremB.pCoreIn 2 H := by
  have hnormal : (X.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hle : X.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hnormal, hX.comap_subtype⟩
  intro k hk
  exact ⟨⟨k, hXH hk⟩, hle hk, rfl⟩

theorem isPGroup_pCoreIn_two (H : Subgroup G) : IsPGroup 2 (CFSG.ABGTheoremB.pCoreIn 2 H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem DeltaNormal.le_jGroup {p : G} {Z : Subgroup G} (h : DeltaNormal A p Z) :
    Z ≤ jGroup A p :=
  le_inf (le_pCoreIn_two h.le h.le_normalizer h.isPGroup) h.le_centralizer

theorem DeltaNormal.jGroup_eq {p : G} {Z : Subgroup G} (hN : DeltaNormal A p Z)
    (hC : DeltaCentral A p Z) : jGroup A p = Z := by
  refine le_antisymm (fun x hx => ?_) hN.le_jGroup
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hxC : x ∈ A ⊓ centralizer ({p} : Set G) := CFSG.ABGTheoremB.pCoreIn_le 2 _ hx1
  obtain ⟨k, hk⟩ := isPGroup_pCoreIn_two _ ⟨x, hx1⟩
  exact hC x hxC hx2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem DeltaNormal.jSylowAt {p : G} {Z : Subgroup G} (hN : DeltaNormal A p Z)
    (hC : DeltaCentral A p Z) : JSylowAt A p := fun x hx hxD h2 =>
  le_pCoreIn_two hN.le hN.le_normalizer hN.isPGroup (hC x hx hxD h2)

end J

section Alpha

variable {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem sq_eq_one_of_represents_unip [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {y : G}
    {k : ℕ} (hk : y ^ 2 ^ k = 1) {M N : GL ι K} (hMsq : M ^ 2 = 1) (hyN : Represents e y N)
    {a : K} (ha : (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1)) : y ^ 2 = 1 := by
  have hN : (N : Matrix ι ι K) = 1 + a • ((M : Matrix ι ι K) - 1) := by
    rw [← ha, add_sub_cancel]
  have hNN : N * N = 1 := by
    apply Units.ext
    have hE := sub_one_mul_self hMsq
    set E := (M : Matrix ι ι K) - 1
    have h : (1 + a • E) * (1 + a • E) = 1 + (a • E + a • E) + (a • E) * (a • E) := by
      rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul]
      abel
    rw [Units.val_mul, hN, Units.val_one, h, matrix_add_self, smul_mul_smul_comm, hE, smul_zero,
      add_zero, add_zero]
  have hrep : Represents e (y * y) 1 := by
    have h := hyN.mul hyN
    rwa [hNN] at h
  rw [sq]
  exact eq_of_represents hZ hrep represents_one (k := k) (k' := 0)
    (by rw [← sq, ← pow_mul, mul_comm, pow_mul, hk, one_pow]) (by simp)

theorem alphaGroup_le_centralizer [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2) :
    alphaGroup e p ≤ centralizer ((A ⊓ centralizer ({p} : Set G) : Subgroup G) : Set G) := by
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  rw [alphaGroup, closure_le]
  rintro y ⟨⟨k, hk⟩, M', N, hM', hM'2, hyN, a, ha⟩
  obtain rfl := hpM.eq_of_orderOf_eq_two hM' hM2 hM'2
  have hN : (N : Matrix ι ι K) = 1 + a • ((M : Matrix ι ι K) - 1) := by
    rw [← ha, add_sub_cancel]
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_represents_unip hZ hk hMsq hyN ha
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro x hx
  obtain ⟨X, hX⟩ := exists_represents e hx.1
  have hXM := hX.mul_comm_of_commute hpM hMsq (mem_centralizer_singleton_iff.mp hx.2)
  have hXN : X * N = N * X := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hN, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
      smul_mul_assoc, mul_sub, sub_mul, hXM, mul_one, one_mul]
  exact commute_of_represents hZ hX hyN hy2 hXN

theorem deltaNormal_alphaGroup [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2) :
    DeltaNormal A p (alphaGroup e p) := by
  have hcen := alphaGroup_le_centralizer hZ hpM hM2
  have hpC : p ∈ A ⊓ centralizer ({p} : Set G) := ⟨hpM.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have hle : alphaGroup e p ≤ A ⊓ centralizer ({p} : Set G) := by
    have hA : alphaGroup e p ≤ A := by
      rw [alphaGroup, closure_le]
      rintro y ⟨-, -, N, -, -, hyN, -⟩
      exact hyN.1
    intro y hy
    refine mem_inf.mpr ⟨hA hy, mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((mem_centralizer_iff.mp (hcen hy)) p hpC).symm
  have hcomm : ∀ x ∈ alphaGroup e p, ∀ y ∈ alphaGroup e p, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (hcen hy)) x (hle hx)
  refine ⟨hle, fun x hx => ?_, ?_, ?_⟩
  · refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro y hy
    exact ((mem_centralizer_iff.mp (hcen hy)) x hx).symm
  ·
    have hsq : ∀ y ∈ alphaGroup e p, y ^ 2 = 1 := by
      intro y hy
      induction hy using closure_induction with
      | mem y hy =>
        obtain ⟨⟨k, hk⟩, M', N, hM', hM'2, hyN, a, ha⟩ := hy
        obtain rfl := hpM.eq_of_orderOf_eq_two hM' hM2 hM'2
        have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
        exact sq_eq_one_of_represents_unip hZ hk hMsq hyN ha
      | one => exact one_pow 2
      | mul x y hx hy ihx ihy =>
        rw [(show Commute x y from hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
      | inv x hx ih => rw [inv_pow, ih, inv_one]
    intro y
    exact ⟨1, Subtype.ext (by simpa using hsq y y.2)⟩
  · intro y hy
    rw [mem_centralizer_iff]
    rintro d ⟨b, hb, rfl, hdp⟩
    have hdC : b * p * b⁻¹ ∈ A ⊓ centralizer ({p} : Set G) :=
      mem_inf.mpr ⟨mul_mem (mul_mem hb hpM.1) (inv_mem hb), mem_centralizer_singleton_iff.mpr hdp⟩
    exact (mem_centralizer_iff.mp (hcen hy)) _ hdC

end Alpha

namespace ClassicalModel

variable {A : Subgroup G}

theorem mem_of_hasRank (D : ClassicalModel A) {x : G} {ℓ : ℕ} (h : D.HasRank x ℓ) :
    x ∈ A ∧ orderOf x = 2 := by
  cases D with
  | linear => exact ⟨h.2.choose_spec.1.1, h.1⟩
  | unitary => exact ⟨h.2.choose_spec.1.1, h.1⟩
  | symplectic => exact ⟨h.2.choose_spec.1.1, h.1⟩
  | orthPlus => exact ⟨h.2.choose_spec.1.1, h.1⟩
  | orthMinus => exact ⟨h.2.choose_spec.1.1, h.1⟩

theorem deltaNormal_alpha (D : ClassicalModel A) (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hp : p ∈ A) (hp2 : orderOf p = 2) : DeltaNormal A p (D.alpha p) := by
  have hpZ := not_mem_center_of_orderOf_eq_two hZ hp hp2
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact deltaNormal_alphaGroup hZ hM hM2
  | unitary n m hn hm K hK e =>
    have := charP_two_of_card (k := 2 * m) (by rw [hK, ← pow_mul, mul_comm])
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact deltaNormal_alphaGroup hZ hM hM2
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact deltaNormal_alphaGroup hZ hM hM2
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact deltaNormal_alphaGroup hZ hM hM2
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM, hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    exact deltaNormal_alphaGroup hZ hM hM2

theorem exists_suzukiType_of_family (D : ClassicalModel A)
    (hfam : D.family = .symplectic ∨ D.family = .orthPlus ∨ D.family = .orthMinus)
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp : p ∈ A) (hp2 : orderOf p = 2) :
    ∃ (L : Letter) (ℓ : ℕ), D.SuzukiType p L ℓ := by
  have hpZ := not_mem_center_of_orderOf_eq_two hZ hp hp2
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  cases D with
  | linear => simp [family] at hfam
  | unitary => simp [family] at hfam
  | symplectic n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M)
      (fun v => sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v))
    exact ⟨L, _, hp2, M, hM', hM2, rfl, hLM⟩
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadPlus n K
        (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v)
    exact ⟨L, _, hp2, M, hM', hM2, rfl, hLM⟩
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨M, hM', hM2⟩ := exists_represents_orderOf_eq_two e hp hp2' hpZ
    obtain ⟨L, hLM⟩ := exists_letterHolds (commRank M) fun v =>
      Assembly.LowTwoRank.StatedQuadMinus n K b c
        (((M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          K) - 1) *ᵥ v)
    exact ⟨L, _, hp2, M, hM', hM2, rfl, hLM⟩

end ClassicalModel

namespace Hyp221

variable {A T : Subgroup G} (hH : Hyp221 A T) (hZ : Odd (Nat.card (center ↥A)))
include hH hZ

theorem eq_of_isAPart {t t' p : G} (ht : t ∈ T) (ht' : t' ∈ T) (hp : IsAPart A t p)
    (hp' : IsAPart A t' p) : t = t' := by
  have h := hH.isAPart_mul hZ ht ht' hp hp'
  rw [← sq, hH.aPart_sq hZ ht hp] at h
  by_contra hne
  have htt : t * t' ≠ 1 := by
    intro h1
    apply hne
    have ht2 : t * t = 1 := by rw [← sq]; exact hH.sq_eq_one ht
    calc t = t * (t * t') := by rw [h1, mul_one]
      _ = t' := by rw [← mul_assoc, ht2, one_mul]
  exact hH.aPart_ne_one (mul_mem ht ht') htt h rfl

theorem card_le_of_forall_mem [Finite G] {Z : Subgroup G}
    (hmem : ∀ t ∈ T, ∀ p, IsAPart A t p → p ∈ Z) : Nat.card T ≤ Nat.card Z := by
  choose f hf using fun t : T => hH.exists_aPart hZ t.2
  refine Nat.card_le_card_of_injective (fun t => ⟨f t, hmem t t.2 (f t) (hf t)⟩) ?_
  intro t t' h
  have h' : f t = f t' := congrArg Subtype.val h
  exact Subtype.ext (hH.eq_of_isAPart hZ t.2 t'.2 (hf t) (h' ▸ hf t'))

theorem card_le_of_sup [Finite G] {U W : Subgroup G} (hWU : W ≤ normalizer (U : Set G))
    (hmem : ∀ t ∈ T, ∀ p, IsAPart A t p → p ∈ U ⊔ W)
    (hU : ∀ t ∈ T, t ≠ 1 → ∀ p, IsAPart A t p → p ∉ U) : Nat.card T ≤ Nat.card W := by
  choose f hf using fun t : T => hH.exists_aPart hZ t.2
  choose u hu w hw huw using fun t : T =>
    exists_mul_of_mem_sup_of_le_normalizer hWU (hmem t t.2 (f t) (hf t))
  refine Nat.card_le_card_of_injective (fun t => ⟨w t, hw t⟩) ?_
  intro t t' h
  have h' : w t = w t' := congrArg Subtype.val h
  by_contra hne
  have hne' : (t : G) ≠ t' := fun h => hne (Subtype.ext h)
  have htt : (t : G) * t' ≠ 1 := by
    intro h1
    apply hne'
    have ht2 : (t : G) * t = 1 := by rw [← sq]; exact hH.sq_eq_one t.2
    calc (t : G) = t * (t * t') := by rw [h1, mul_one]
      _ = t' := by rw [← mul_assoc, ht2, one_mul]
  have hmul := hH.isAPart_mul hZ t.2 t'.2 (hf t) (hf t')
  apply hU _ (mul_mem t.2 t'.2) htt _ hmul
  have hf2 : f t' * f t' = 1 := by rw [← sq]; exact hH.aPart_sq hZ t'.2 (hf t')
  have hfinv : f t' = (f t')⁻¹ := (inv_eq_of_mul_eq_one_right hf2).symm
  have e : f t * f t' = u t * (u t')⁻¹ := by
    rw [hfinv, huw t, huw t', h']
    group
  rw [e]
  exact mul_mem (hu t) (inv_mem (hu t'))

variable (h212 : ∀ x ∈ T ⊔ A, rightConjugate T x ⊓ normalizer (T : Set G) ≤
  centralizer (T : Set G))
include h212

theorem conjCommuting_le_centralizer {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : IsAPart A t p)
    {d : G} (hd : d ∈ conjCommuting A p) : d ∈ centralizer (T : Set G) := by
  obtain ⟨b, hb, rfl, hdp⟩ := hd
  obtain ⟨c, hcC, ht'⟩ : ∃ c ∈ centralizer (A : Set G), t = p * c⁻¹ :=
    ⟨t⁻¹ * p, hp.2.2, by group⟩
  have hcb : Commute b c := (mem_centralizer_iff.mp hcC) b hb
  have hcp : Commute c p := ((mem_centralizer_iff.mp hcC) p hp.1).symm
  have hcd : Commute c (b * p * b⁻¹) :=
    ((mem_centralizer_iff.mp hcC) _ (mul_mem (mul_mem hb hp.1) (inv_mem hb))).symm
  set t₁ := b * t * b⁻¹ with ht₁
  have hbc : b * c⁻¹ * b⁻¹ = c⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcb.inv_right.eq
  have ht₁' : t₁ = (b * p * b⁻¹) * c⁻¹ := by
    have e1 : t₁ = b * (p * c⁻¹) * b⁻¹ := by rw [ht₁, ← ht']
    rw [e1, show b * (p * c⁻¹) * b⁻¹ = b * p * b⁻¹ * (b * c⁻¹ * b⁻¹) by group, hbc]
  have hcomm : t₁ * t = t * t₁ := by
    have h1 : c⁻¹ * p = p * c⁻¹ := hcp.inv_left.eq
    have h2 : (b * p * b⁻¹) * c⁻¹ = c⁻¹ * (b * p * b⁻¹) := hcd.inv_left.eq.symm
    have h3 : (b * p * b⁻¹) * p = p * (b * p * b⁻¹) := hdp
    rw [ht₁', ht']
    calc b * p * b⁻¹ * c⁻¹ * (p * c⁻¹) = b * p * b⁻¹ * (c⁻¹ * p) * c⁻¹ := by group
      _ = (b * p * b⁻¹) * p * c⁻¹ * c⁻¹ := by rw [h1]; group
      _ = p * (b * p * b⁻¹) * c⁻¹ * c⁻¹ := by rw [h3]
      _ = p * ((b * p * b⁻¹) * c⁻¹) * c⁻¹ := by group
      _ = p * (c⁻¹ * (b * p * b⁻¹)) * c⁻¹ := by rw [h2]
      _ = p * c⁻¹ * (b * p * b⁻¹ * c⁻¹) := by group
  have ht₁TA : t₁ ∈ T ⊔ A :=
    mul_mem (mul_mem (mem_sup_right hb) (mem_sup_left ht)) (mem_sup_right (inv_mem hb))
  have ht₁N : t₁ ∈ normalizer (T : Set G) :=
    hH.mem_normalizer ht₁TA ht ht1 (by rw [hcomm, mul_inv_cancel_right]; exact ht)
  have ht₁R : t₁ ∈ rightConjugate T b⁻¹ := by
    rw [mem_rightConjugate_iff, inv_inv, ht₁]
    have h : b⁻¹ * (b * t * b⁻¹) * b = t := by group
    rw [h]
    exact ht
  have ht₁C := h212 b⁻¹ (mem_sup_right (inv_mem hb)) (mem_inf.mpr ⟨ht₁R, ht₁N⟩)
  have hd : b * p * b⁻¹ = t₁ * (t⁻¹ * p) := by
    rw [ht₁', show t⁻¹ * p = c by rw [ht']; group]
    group
  rw [hd]
  exact mul_mem ht₁C (hH.cPart_mem_centralizer hZ ht hp)

theorem aPart_mem_centralizer_conjCommuting {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hp : IsAPart A t p) {t' p' : G} (ht' : t' ∈ T) (hp' : IsAPart A t' p') :
    p' ∈ centralizer (conjCommuting A p) := by
  rw [mem_centralizer_iff]
  intro d hd
  have hdT := hH.conjCommuting_le_centralizer hZ h212 ht ht1 hp hd
  have hdA : d ∈ A := by
    obtain ⟨b, hb, rfl, -⟩ := hd
    exact mul_mem (mul_mem hb hp.1) (inv_mem hb)
  exact (hp'.commute_iff hdA).mp ((mem_centralizer_iff.mp hdT) t' ht').symm

theorem aPart_mem_of_deltaCentral {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : IsAPart A t p)
    {Z : Subgroup G} (hC : DeltaCentral A p Z) {t' p' : G} (ht' : t' ∈ T)
    (hp' : IsAPart A t' p') : p' ∈ Z :=
  hC p' (mem_inf.mpr ⟨hp'.1, mem_centralizer_singleton_iff.mpr
    (hH.commute_aPart hZ ht' ht hp' hp)⟩)
    (hH.aPart_mem_centralizer_conjCommuting hZ h212 ht ht1 hp ht' hp')
    ⟨1, by rw [pow_one]; exact hH.aPart_sq hZ ht' hp'⟩

end Hyp221

end CFSG.ComponentClassification.RankTwoClassical
