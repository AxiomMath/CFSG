module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup

@[expose] def NoPQuotient (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤

theorem NoPQuotient.of_surjective {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hX : NoPQuotient p X) : NoPQuotient p Y := by
  intro N _ hN
  have hinj : Function.Injective (QuotientGroup.map (N.comap f) N f le_rfl) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    simpa [QuotientGroup.eq_one_iff] using hx
  have hp : IsPGroup p (X ⧸ N.comap f) := hN.of_injective _ hinj
  have := hX _ hp
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have : x ∈ N.comap f := this ▸ mem_top x
  exact this

private theorem orderOf_conj' {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

private theorem closure_pPrime_normal {X : Type*} [Group X] (p : ℕ) :
    (Subgroup.closure {x : X | ¬ p ∣ orderOf x}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    show ¬ p ∣ orderOf (g * x * g⁻¹)
    rw [orderOf_conj']
    exact hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have := mul_mem ihx ihy
    simpa [mul_assoc] using this
  | inv x _ ih =>
    have := inv_mem ih
    simpa [mul_assoc] using this

theorem NoPQuotient.closure_eq_top {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : NoPQuotient p X) : Subgroup.closure {x : X | ¬ p ∣ orderOf x} = ⊤ := by
  have hn := closure_pPrime_normal (X := X) p
  apply hX
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
  refine ⟨(orderOf x).factorization p, ?_⟩
  have hpos : 0 < orderOf x := orderOf_pos x
  have hdvd : p ^ (orderOf x).factorization p ∣ orderOf x := Nat.ordProj_dvd _ _
  have hne : p ^ (orderOf x).factorization p ≠ 0 := (pow_pos (Fact.out : p.Prime).pos _).ne'
  have hord : orderOf (x ^ (p ^ (orderOf x).factorization p)) =
      orderOf x / p ^ (orderOf x).factorization p := orderOf_pow_of_dvd hne hdvd
  have hmem : x ^ (p ^ (orderOf x).factorization p) ∈
      Subgroup.closure {x : X | ¬ p ∣ orderOf x} := by
    apply Subgroup.subset_closure
    show ¬ p ∣ orderOf (x ^ (p ^ (orderOf x).factorization p))
    rw [hord]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_ordCompl Fact.out hpos.ne')
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hmem

theorem NoPQuotient.closure_eq_ambient {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {L : Subgroup G} (hL : NoPQuotient p L) :
    Subgroup.closure {x : G | x ∈ L ∧ ¬ p ∣ orderOf x} = L := by
  have h := hL.closure_eq_top
  have h2 := congrArg (Subgroup.map L.subtype) h
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at h2
  have hset : {x : G | x ∈ L ∧ ¬ p ∣ orderOf x} = L.subtype '' {x : L | ¬ p ∣ orderOf x} := by
    ext x
    constructor
    · rintro ⟨hxL, hx⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      change ¬ p ∣ orderOf (⟨x, hxL⟩ : L)
      rw [Subgroup.orderOf_mk]; exact hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      change ¬ p ∣ orderOf (y : G)
      rw [Subgroup.orderOf_coe]; exact hy
  rw [hset]
  exact h2

private theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {U W : Subgroup G} [Finite G]
    (hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) {e : G} (he : e ∈ U) {m : ℕ}
    (hcop : Nat.Coprime m (Nat.card U)) (hm : e ^ m ∈ W) : e ∈ W := by
  set W' : Subgroup U := W.subgroupOf U with hW'
  have hnorm : W'.Normal := ⟨fun w hw u => by
    have hw' : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
    exact Subgroup.mem_subgroupOf.mpr (hWn u u.2 w hw')⟩
  have h1 : orderOf (QuotientGroup.mk (s := W') ⟨e, he⟩) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hm
  have h2 : orderOf (QuotientGroup.mk (s := W') ⟨e, he⟩) ∣ Nat.card U :=
    (_root_.orderOf_dvd_natCard _).trans (Subgroup.card_quotient_dvd_card W')
  have h3 : orderOf (QuotientGroup.mk (s := W') ⟨e, he⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact Subgroup.mem_subgroupOf.mp h3

theorem coprime_conj_mem {G : Type*} [Group G] [Finite G] {Q U W : Subgroup G} {x : G}
    (hUQ : U ≤ Q) (hWU : W ≤ U)
    (hWQ : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ W)
    (hxQ' : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ U)
    (hcop : Nat.Coprime (orderOf x) (Nat.card U)) :
    ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ W := by
  intro q hq
  set e : G := x * q * x⁻¹ * q⁻¹ with he
  have heU : e ∈ U := hxQ' q hq
  have heQ : e ∈ Q := hUQ heU
  have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro w hw
    have := mul_mem (hxU w (hWU hw)) hw
    simpa [mul_assoc] using this
  have hpow : ∀ (w : G), w ∈ W → ∀ j : ℕ, ∃ w' ∈ W, (w * e) ^ j = w' * e ^ j := by
    intro w hw j
    induction j with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨w', hw', h⟩ := ih
      refine ⟨w' * (e ^ j * w * (e ^ j)⁻¹), mul_mem hw' ?_, ?_⟩
      · exact hWQ _ (pow_mem heQ j) w hw
      · rw [pow_succ, h]; group
  have hmain : ∀ j : ℕ, ∃ w ∈ W, x ^ j * q * (x ^ j)⁻¹ = w * e ^ j * q := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨w, hw, h⟩ := ih
      have hw₂ : x * e * x⁻¹ * e⁻¹ ∈ W := hxU e heU
      obtain ⟨w', hw', hp⟩ := hpow (x * e * x⁻¹ * e⁻¹) hw₂ j
      have hxe : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
      have hxq : x * q * x⁻¹ = e * q := by rw [he]; group
      refine ⟨(x * w * x⁻¹) * w', mul_mem (hxW w hw) hw', ?_⟩
      have h1 : x ^ (j + 1) * q * (x ^ (j + 1))⁻¹ = x * (x ^ j * q * (x ^ j)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      rw [h1, h]
      calc x * (w * e ^ j * q) * x⁻¹
          = (x * w * x⁻¹) * ((x * e * x⁻¹) ^ j) * (x * q * x⁻¹) := by
            rw [show (x * e * x⁻¹) ^ j = x * e ^ j * x⁻¹ by rw [← conj_pow]]
            group
        _ = (x * w * x⁻¹) * (((x * e * x⁻¹ * e⁻¹) * e) ^ j) * (e * q) := by rw [← hxe, hxq]
        _ = (x * w * x⁻¹) * (w' * e ^ j) * (e * q) := by rw [hp]
        _ = ((x * w * x⁻¹) * w') * e ^ (j + 1) * q := by rw [pow_succ']; group
  obtain ⟨w, hw, h⟩ := hmain (orderOf x)
  rw [pow_orderOf_eq_one] at h
  have hew : e ^ orderOf x ∈ W := by
    have h' : w * e ^ orderOf x * q = 1 * q := by simpa using h.symm
    have h'' : w * e ^ orderOf x = 1 := mul_right_cancel h'
    have : e ^ orderOf x = w⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc e ^ orderOf x * w = w⁻¹ * (w * e ^ orderOf x) * w := by group
        _ = 1 := by rw [h'']; group
    rw [this]; exact inv_mem hw
  exact mem_of_pow_mem_of_coprime (fun u hu w hw => hWQ u (hUQ hu) w hw) heU hcop hew

private def actsTrivMod {G : Type*} [Group G] (Q W : Subgroup G) (hW : W ≤ Q) : Subgroup G where
  carrier := {x | x ∈ normalizer (Q : Set G) ∧ ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ W}
  one_mem' := ⟨one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxn, hx⟩ ⟨hyn, hy⟩
    refine ⟨mul_mem hxn hyn, fun q hq => ?_⟩
    have hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
      intro w hw
      have := mul_mem (hx w (hW hw)) hw
      simpa [mul_assoc] using this
    have h1 := hxW _ (hy q hq)
    have h2 := hx q hq
    have := mul_mem h1 h2
    convert this using 1
    group
  inv_mem' := by
    rintro x ⟨hxn, hx⟩
    refine ⟨inv_mem hxn, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x ∈ Q := (Subgroup.mem_normalizer_iff''.mp hxn q).mp hq
    have := hx _ hq'
    have h2 := inv_mem this
    convert h2 using 1
    group

theorem commutator_le_of_gen {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q U W L : Subgroup G} (hUQ : U ≤ Q) (hWU : W ≤ U) (hUp : IsPGroup p U)
    (hWQ : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W)
    (hgen : Subgroup.closure {x | x ∈ L ∧ ¬ p ∣ orderOf x} = L)
    (hLU : ⁅U, L⁆ ≤ W) (hLQ : ⁅Q, L⁆ ≤ U) (hL : L ≤ normalizer (Q : Set G)) :
    ⁅Q, L⁆ ≤ W := by
  have hLK : L ≤ actsTrivMod Q W (hWU.trans hUQ) := by
    rw [← hgen, Subgroup.closure_le]
    rintro x ⟨hxL, hxp⟩
    refine ⟨hL hxL, ?_⟩
    have hcop : Nat.Coprime (orderOf x) (Nat.card U) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hUp
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hxp).symm
    refine coprime_conj_mem hUQ hWU hWQ (fun u hu => ?_) (fun q hq => ?_) hcop
    · have := Subgroup.commutator_le.mp hLU u hu x hxL
      have h2 := inv_mem this
      simpa [commutatorElement_def, mul_assoc] using h2
    · have := Subgroup.commutator_le.mp hLQ q hq x hxL
      have h2 := inv_mem this
      simpa [commutatorElement_def, mul_assoc] using h2
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have := (hLK hl).2 q hq
  have h2 := inv_mem this
  simpa [commutatorElement_def, mul_assoc] using h2

theorem commutator_le_left_of_normalizes {G : Type*} [Group G] {Q L : Subgroup G}
    (hL : L ≤ normalizer (Q : Set G)) : ⁅Q, L⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have h1 : l * q⁻¹ * l⁻¹ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hL hl) q⁻¹).mp (inv_mem hq)
    exact this
  have := mul_mem hq h1
  simpa [commutatorElement_def, mul_assoc] using this

theorem le_normalizer_commutator {G : Type*} [Group G] {Q L : Subgroup G}
    (hL : L ≤ normalizer (Q : Set G)) : L ≤ normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) := by
  have key : ∀ l ∈ L, ∀ x ∈ (⁅Q, L⁆ : Subgroup G), l * x * l⁻¹ ∈ (⁅Q, L⁆ : Subgroup G) := by
    intro l hl x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, hq, l', hl', rfl⟩ := hx
      have h1 : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hL hl) q).mp hq
      have h2 : l * l' * l⁻¹ ∈ L := mul_mem (mul_mem hl hl') (inv_mem hl)
      have := Subgroup.commutator_mem_commutator h1 h2
      convert this using 1
      simp only [commutatorElement_def]; group
    | one => simp
    | mul x y _ _ ihx ihy =>
      have := mul_mem ihx ihy
      simpa [mul_assoc] using this
    | inv x _ ih =>
      have := inv_mem ih
      simpa [mul_assoc] using this
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key l hl x, fun hx => ?_⟩
  have := key l⁻¹ (inv_mem hl) _ hx
  simpa [mul_assoc] using this

theorem prime_residual_central_commutator_saturation {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Q L : Subgroup G} (hQ : IsPGroup p Q) (hL : L ≤ normalizer (Q : Set G))
    (hno : NoPQuotient p L) (hU : ⁅Q, L⁆ ≤ Subgroup.centralizer (Q : Set G)) :
    ⁅⁅Q, L⁆, L⁆ = ⁅Q, L⁆ := by
  have hUQ : ⁅Q, L⁆ ≤ Q := commutator_le_left_of_normalizes hL
  have hWU : ⁅⁅Q, L⁆, L⁆ ≤ ⁅Q, L⁆ :=
    commutator_le_left_of_normalizes (le_normalizer_commutator hL)
  refine le_antisymm hWU ?_
  refine commutator_le_of_gen (p := p) (U := ⁅Q, L⁆) hUQ hWU (hQ.to_le hUQ) ?_
    hno.closure_eq_ambient le_rfl le_rfl hL
  intro q hq w hw
  have hwc : w ∈ Subgroup.centralizer (Q : Set G) := hU (hWU hw)
  have h1 := Subgroup.mem_centralizer_iff.mp hwc q hq
  have : q * w * q⁻¹ = w := by rw [h1]; group
  rw [this]; exact hw

theorem prime_residual_commutator_through_normal_layer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {E Q K : Subgroup G} [E.Normal] [Q.Normal] [K.Normal] (hEQ : E ≤ Q)
    (hQ : IsPGroup p Q) (hK : Subgroup.closure {x | x ∈ K ∧ ¬ p ∣ orderOf x} = K)
    (hQK : ⁅Q, K⁆ ≤ E) :
    ⁅Q, K⁆ = ⁅E, K⁆ ∧
      ∀ (Q' : Subgroup G) [Q'.Normal], IsPGroup p Q' → ⁅⁅Q', K⁆, K⁆ = ⁅Q', K⁆ := by
  have key : ∀ (E Q : Subgroup G) [E.Normal] [Q.Normal], E ≤ Q → IsPGroup p Q → ⁅Q, K⁆ ≤ E →
      ⁅Q, K⁆ = ⁅E, K⁆ := by
    intro E Q _ _ hEQ hQ hQK
    refine le_antisymm ?_ (Subgroup.commutator_mono hEQ le_rfl)
    refine commutator_le_of_gen (p := p) (U := E) hEQ (Subgroup.commutator_le_left _ _)
      (hQ.to_le hEQ) ?_ hK le_rfl hQK ?_
    · intro q _ w hw
      exact (inferInstance : (⁅E, K⁆ : Subgroup G).Normal).conj_mem w hw q
    · intro k _
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · exact (inferInstance : Q.Normal).conj_mem x hx k
      · have := (inferInstance : Q.Normal).conj_mem _ hx k⁻¹
        simpa [mul_assoc] using this
  refine ⟨key E Q hEQ hQ hQK, fun Q' _ hQ' => ?_⟩
  have h := key ⁅Q', K⁆ Q' (Subgroup.commutator_le_left _ _) hQ' le_rfl
  exact h.symm

theorem isQuasisimple_of_central_quotient {E : Type*} [Group E] (A : Subgroup E) [A.Normal]
    (hA : A ≤ center E) (hE : Group.IsPerfect E) (hq : CFSG.IsQuasisimple (E ⧸ A)) :
    CFSG.IsQuasisimple E := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  have hc : center E = (center (E ⧸ A)).comap (QuotientGroup.mk' A) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A y
      simpa using congrArg (QuotientGroup.mk' A) (Subgroup.mem_center_iff.mp hz x)
    · intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at hz
      have hfA : ∀ e : E, z * e * z⁻¹ * e⁻¹ ∈ A := by
        intro e
        have hcomm : (QuotientGroup.mk' A) z * (QuotientGroup.mk' A) e =
            (QuotientGroup.mk' A) e * (QuotientGroup.mk' A) z := (hz _).symm
        have : QuotientGroup.mk' A (z * e * z⁻¹ * e⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [hcomm]; group
        exact (QuotientGroup.eq_one_iff _).mp this
      let f : E →* A :=
        { toFun := fun e => ⟨z * e * z⁻¹ * e⁻¹, hfA e⟩
          map_one' := by ext; simp
          map_mul' := fun e₁ e₂ => by
            apply Subtype.ext
            have h1 : e₁ * (z * e₂ * z⁻¹ * e₂⁻¹) * e₁⁻¹ = z * e₂ * z⁻¹ * e₂⁻¹ := by
              have := Subgroup.mem_center_iff.mp (hA (hfA e₂)) e₁
              rw [this]; group
            show z * (e₁ * e₂) * z⁻¹ * (e₁ * e₂)⁻¹ =
              (z * e₁ * z⁻¹ * e₁⁻¹) * (z * e₂ * z⁻¹ * e₂⁻¹)
            calc z * (e₁ * e₂) * z⁻¹ * (e₁ * e₂)⁻¹
                = (z * e₁ * z⁻¹ * e₁⁻¹) * (e₁ * (z * e₂ * z⁻¹ * e₂⁻¹) * e₁⁻¹) := by group
              _ = _ := by rw [h1] }
      have hAc : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext
        (Subgroup.mem_center_iff.mp (hA y.2) x)
      have hker : commutator E ≤ f.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        rw [MonoidHom.mem_ker, commutatorElement_def]
        simp only [map_mul, map_inv]
        rw [hAc (f x) (f y)]
        group
      have hperfE := Group.isPerfect_def.mp hE
      have hkertop : f.ker = ⊤ := eq_top_iff.mpr (hperfE ▸ hker)
      rw [Subgroup.mem_center_iff]
      intro e
      have h1 : f e = 1 := by rw [← MonoidHom.mem_ker, hkertop]; exact mem_top _
      have h2 : z * e * z⁻¹ * e⁻¹ = 1 := congrArg Subtype.val h1
      have : z * e = e * z := by
        calc z * e = z * e * z⁻¹ * e⁻¹ * (e * z) := by group
          _ = e * z := by rw [h2]; group
      exact this.symm
  have hmap : (center E).map (QuotientGroup.mk' A) = center (E ⧸ A) := by
    rw [hc, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)]
  let e : (E ⧸ A) ⧸ center (E ⧸ A) ≃* E ⧸ center E :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient A (center E) hA)
  refine ⟨hE, e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem not_dvd_card_of_abelian {E : Type*} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hab : ∀ x y : E, x * y = y * x) (hno : NoPQuotient p E) : ¬ p ∣ Nat.card E := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) p hdvd
  let P : Subgroup E :=
    { carrier := {y | ∃ z : E, z ^ p = y}
      one_mem' := ⟨1, one_pow p⟩
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, (Commute.mul_pow (hab a b) p)⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a⁻¹, inv_pow a p⟩ }
  have hPn : P.Normal := ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    refine ⟨g * z * g⁻¹, ?_⟩
    simp [conj_pow]⟩
  have hPtop : P = ⊤ := by
    refine hno P ?_
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨y, rfl⟩
  have hsurj : Function.Surjective (fun z : E => z ^ p) := by
    intro y
    have : y ∈ P := hPtop ▸ mem_top y
    exact this
  have hinj : Function.Injective (fun z : E => z ^ p) := Finite.injective_iff_surjective.mpr hsurj
  have h1 : x ^ p = (1 : E) ^ p := by rw [← hx, pow_orderOf_eq_one, one_pow]
  have := hinj h1
  have hp1 : orderOf x = 1 := by rw [this]; exact orderOf_one
  rw [hx] at hp1
  exact (Fact.out : p.Prime).one_lt.ne' hp1

theorem isPerfect_of_quotient {L : Type*} [Group L] {p : ℕ} (Q : Subgroup L) [Q.Normal]
    (hQ : IsPGroup p Q) (hno : NoPQuotient p L) (hperfQ : Group.IsPerfect (L ⧸ Q)) :
    Group.IsPerfect L := by
  rw [Group.isPerfect_def]
  have hsup : commutator L ⊔ Q = ⊤ := by
    have h1 : (commutator L).map (QuotientGroup.mk' Q) = ⊤ := by
      have := Group.isPerfect_def.mp hperfQ
      rw [commutator_def] at this ⊢
      rw [Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
      exact this
    have := Subgroup.comap_map_eq (QuotientGroup.mk' Q) (commutator L)
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm
  refine hno (commutator L) ?_
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  have hx : x ∈ commutator L ⊔ Q := hsup ▸ mem_top x
  obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  refine ⟨k, ?_⟩
  have hqk : q ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul, ← QuotientGroup.mk_pow,
    hqk]
  rfl

theorem prime_residual_core_commutator_quotient {L : Type*} [Group L] [Finite L] {p : ℕ}
    [Fact p.Prime] (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup p Q) (hno : NoPQuotient p L) :
    (CFSG.IsQuasisimple (L ⧸ Q) →
        Group.IsPerfect L ∧ CFSG.IsQuasisimple (L ⧸ ⁅Q, (⊤ : Subgroup L)⁆)) ∧
    ∀ m : ℕ, IsCyclic (L ⧸ Q) → Nat.card (L ⧸ Q) = m → Nat.Coprime m p →
      Q = ⁅Q, (⊤ : Subgroup L)⁆ ∧ IsCyclic (L ⧸ ⁅Q, (⊤ : Subgroup L)⁆) ∧
        Nat.card (L ⧸ ⁅Q, (⊤ : Subgroup L)⁆) = m := by
  set U : Subgroup L := ⁅Q, (⊤ : Subgroup L)⁆ with hU
  have hUQ : U ≤ Q := Subgroup.commutator_le_left _ _
  have hUn : U.Normal := inferInstance
  have hAcent : Q.map (QuotientGroup.mk' U) ≤ center (L ⧸ U) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective U y
    have hc : q * l * q⁻¹ * l⁻¹ ∈ U := Subgroup.commutator_mem_commutator hq (mem_top l)
    have : QuotientGroup.mk' U (q * l * q⁻¹ * l⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [map_mul, map_inv] at this
    calc (QuotientGroup.mk' U) l * (QuotientGroup.mk' U) q
        = ((QuotientGroup.mk' U) q * (QuotientGroup.mk' U) l * ((QuotientGroup.mk' U) q)⁻¹ *
          ((QuotientGroup.mk' U) l)⁻¹)⁻¹ *
            ((QuotientGroup.mk' U) q * (QuotientGroup.mk' U) l) := by group
      _ = (QuotientGroup.mk' U) q * (QuotientGroup.mk' U) l := by rw [this]; group
  have hAn : (Q.map (QuotientGroup.mk' U)).Normal := inferInstance
  let eQ : (L ⧸ U) ⧸ Q.map (QuotientGroup.mk' U) ≃* L ⧸ Q :=
    QuotientGroup.quotientQuotientEquivQuotient U Q hUQ
  refine ⟨fun hq => ?_, fun m hcyc hcard hm => ?_⟩
  · have hLperf : Group.IsPerfect L := isPerfect_of_quotient Q hQ hno hq.1
    refine ⟨hLperf, ?_⟩
    have hEperf : Group.IsPerfect (L ⧸ U) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective U)
    exact isQuasisimple_of_central_quotient _ hAcent hEperf
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hq)
  · let f : (L ⧸ U) →* L ⧸ Q :=
      eQ.toMonoidHom.comp (QuotientGroup.mk' (Q.map (QuotientGroup.mk' U)))
    have hker : f.ker ≤ center (L ⧸ U) := by
      intro x hx
      have : x ∈ Q.map (QuotientGroup.mk' U) := by
        have hx' : eQ (QuotientGroup.mk' (Q.map (QuotientGroup.mk' U)) x) = 1 := hx
        rw [MulEquiv.map_eq_one_iff] at hx'
        exact (QuotientGroup.eq_one_iff _).mp hx'
      exact hAcent this
    have := hcyc
    have habel : ∀ a b : L ⧸ U, a * b = b * a := by
      have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker
      exact fun a b => (IsMulCommutative.is_comm.comm a b)
    have hnoE : NoPQuotient p (L ⧸ U) :=
      NoPQuotient.of_surjective _ (QuotientGroup.mk'_surjective U) hno
    have hcop := not_dvd_card_of_abelian habel hnoE
    have hQU : Q ≤ U := by
      have hAcard : Nat.card (Q.map (QuotientGroup.mk' U)) = 1 := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
        have h1 : Nat.card (Q.map (QuotientGroup.mk' U)) ∣ p ^ k := hk ▸ Subgroup.card_map_dvd _ _
        have h2 : Nat.card (Q.map (QuotientGroup.mk' U)) ∣ Nat.card (L ⧸ U) :=
          Subgroup.card_subgroup_dvd_card _
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp h1
        rw [hj']
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · simp [h0]
        · exfalso
          apply hcop
          exact (dvd_pow_self p hpos.ne').trans (hj' ▸ h2)
      have : Q.map (QuotientGroup.mk' U) = ⊥ := Subgroup.eq_bot_of_card_eq _ hAcard
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
      exact this
    have hQUeq : U = Q := le_antisymm hUQ hQU
    let e : L ⧸ U ≃* L ⧸ Q := QuotientGroup.quotientMulEquivOfEq hQUeq
    exact ⟨hQUeq.symm, (MulEquiv.isCyclic e).mpr hcyc, by rw [Nat.card_congr e.toEquiv, hcard]⟩

end CFSG.QuasithinUnique.Setup.Campbell
