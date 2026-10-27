module

public import CFSG.CGT.T75O.AptHW
public import CFSG.CGT.T75O.Syl

public section

namespace CFSG.CGT.T75O

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH CFSG.Timmesfeld.ARS.Sec8Field
open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}
  {A A₀ P P' : Subgroup G}

namespace Apt

theorem M_le_normalizer (S : Setup R A A₀ P P') : M R A ≤ Subgroup.normalizer (A : Set G) := by
  have := S.hyp.finite
  exact (isPGroup_M S.hyp.root S.hA).2.1

theorem commutator_mem_A (S : Setup R A A₀ P P') {x y : G} (hx : x ∈ M R A) (hy : y ∈ M R A) :
    ⁅x, y⁆ ∈ A := by
  obtain ⟨-, -, hMM, -, -⟩ := Q_eq_M S.hyp S.hA
  rw [← hMM]
  exact Subgroup.commutator_mem_commutator hx hy

theorem proj_conj_of_mem_M (S : Setup R A A₀ P P') {m g : G} (hm : m ∈ M R A) (hg : g ∈ M R A) :
    S.proj ⟨m * g * m⁻¹, (M R A).mul_mem ((M R A).mul_mem hm hg) ((M R A).inv_mem hm)⟩ =
      S.proj ⟨g, hg⟩ := by
  have hc := commutator_mem_A S hm hg
  have e : (⟨m * g * m⁻¹, (M R A).mul_mem ((M R A).mul_mem hm hg) ((M R A).inv_mem hm)⟩ :
      ↥(M R A)) = ⟨⁅m, g⁆, QD.le_M_self hc⟩ * ⟨g, hg⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
  rw [e, map_mul, S.proj_A hc, one_mul]

theorem ad_of_mem_M (S : Setup R A A₀ P P') {m : G} (hm : m ∈ M R A)
    (hN : m ∈ Subgroup.normalizer (A : Set G)) (v : S.V) : S.ad hN v = v := by
  rw [S.ad_apply, proj_conj_of_mem_M S hm (S.lift v).2, S.proj_lift]

theorem card_M_apt (S : Setup R A A₀ P P') :
    Nat.card (M R A) = Nat.card A * (Nat.card A * (((linesThrough R A).ncard - 1) *
      (((linesThrough R A).ncard - 1) * Nat.card A))) := by
  have hh := S.hyp
  have := hh.finite
  have hR := hh.root
  have hPR : P ∈ R := S.hP.2.1
  have hP'R : P' ∈ R := S.hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, -⟩, ⟨hsAQ', -⟩, -, hQ'Ω, hQΩ⟩ :=
    apartment hh S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm S.hA S.hP'.1, S.hA, hsAQ.symm⟩
  have hQ : Nat.card (MQuot R A) = Nat.card (↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) ×
      ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P') := (Nat.card_congr S.prodEquiv.toEquiv).symm
  have hM : Nat.card (M R A) = Nat.card (MQuot R A) * Nat.card A := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (M R A)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe QD.le_M_self).toEquiv]
  rw [hM, hQ, Nat.card_prod, Nat.card_prod, Nat.card_prod, hR.card_eq hPR S.hA,
    hR.card_eq hP'R S.hA, card_shortRoot hh S.hH S.hT hP'R hQΩ hAs',
    card_shortRoot hh S.hH S.hT hPR hQ'Ω hAs, ncard_linesThrough_eq hh S.hA hP'R,
    ncard_linesThrough_eq hh S.hA hPR]
  ring

theorem card_M_mul_card_E (S : Setup R A A₀ P P') {E : Type} {n m : ℕ} (hq : Nat.card A = 2 ^ n)
    (hL : (linesThrough R A).ncard = 2 ^ m + 1) (hE : Nat.card E = 2 ^ m) :
    Nat.card (M R A) * Nat.card E = 2 ^ (3 * n + 3 * m) := by
  rw [card_M_apt S, hq, hL, hE, Nat.add_sub_cancel]
  ring

section Plain

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

theorem x1_inv (s : E) : (c.x1 s)⁻¹ = c.x1 (-s) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← c.x1_add, add_neg_cancel, c.x1_zero]

def X1 : Subgroup G where
  carrier := {g | ∃ s : E, g = c.x1 s}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (c.x1_add a b).symm⟩
  one_mem' := ⟨0, c.x1_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, x1_inv c a⟩

theorem X1_le_normalizer_M : X1 c ≤ Subgroup.normalizer (M R A : Set G) := by
  rintro _ ⟨s, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer s) hh,
    fun hh => ?_⟩
  have := conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer (-s)) hh
  rwa [← x1_inv c s, inv_inv, show (c.x1 s)⁻¹ * (c.x1 s * h * (c.x1 s)⁻¹) * c.x1 s = h by
    group] at this

variable (S) in
def MX : Subgroup G where
  carrier := {g | ∃ m ∈ M R A, ∃ s : E, g = m * c.x1 s}
  mul_mem' := by
    rintro _ _ ⟨m, hm, s, rfl⟩ ⟨m', hm', s', rfl⟩
    refine ⟨m * (c.x1 s * m' * (c.x1 s)⁻¹), (M R A).mul_mem hm
      (conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer s) hm'), s + s', ?_⟩
    rw [c.x1_add]
    group
  one_mem' := ⟨1, (M R A).one_mem, 0, by rw [c.x1_zero, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨m, hm, s, rfl⟩
    refine ⟨c.x1 (-s) * m⁻¹ * (c.x1 (-s))⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root
      (c.x1_mem_normalizer (-s)) ((M R A).inv_mem hm), -s, ?_⟩
    rw [mul_inv_rev, ← x1_inv c s]
    group

theorem MX_le_normalizer : MX S c ≤ Subgroup.normalizer (A : Set G) := by
  rintro _ ⟨m, hm, s, rfl⟩
  exact Subgroup.mul_mem _ (M_le_normalizer S hm) (c.x1_mem_normalizer s)

theorem MX_le_sup : MX S c ≤ X1 c ⊔ M R A := by
  rintro _ ⟨m, hm, s, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hm) (Subgroup.mem_sup_left ⟨s, rfl⟩)

end Plain

section Char

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] [CharP E 2] (c : Coords S F E)

theorem isPGroup_X1 : IsPGroup 2 (X1 c) := by
  rintro ⟨_, s, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change (c.x1 s) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two, ← c.x1_add, CharTwo.add_self_eq_zero, c.x1_zero]

theorem isPGroup_MX : IsPGroup 2 (MX S c) := by
  have := S.hyp.finite
  have hM : IsPGroup 2 (M R A) := (Q_eq_M S.hyp S.hA).2.2.2.2
  exact ((isPGroup_X1 c).to_sup_of_normal_right' hM (X1_le_normalizer_M c)).to_le (MX_le_sup c)

theorem proj_x6_eq_vc (u : F) :
    S.proj ⟨c.x6 u, S.P_le_M (c.x6_mem u)⟩ = c.vc u 0 0 0 := by
  rw [S.proj_P (c.x6_mem u)]
  exact Prod.ext rfl (Prod.ext (Subtype.ext c.x5_zero.symm)
    (Prod.ext (Subtype.ext c.x3_zero.symm) (Subtype.ext c.x2_zero.symm)))

omit [CharP E 2] in
theorem card_MX_ge (hint : ∀ s : E, c.x1 s ∈ M R A → s = 0) :
    Nat.card (M R A) * Nat.card E ≤ Nat.card (MX S c) := by
  have := S.hyp.finite
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥(M R A) × E => (⟨p.1 * c.x1 p.2, p.1, p.1.2, p.2, rfl⟩ : MX S c)) ?_
  rintro ⟨⟨m, hm⟩, s⟩ ⟨⟨m', hm'⟩, s'⟩ h
  have h' : m * c.x1 s = m' * c.x1 s' := congrArg Subtype.val h
  have h1 : c.x1 (s' + -s) ∈ M R A := by
    have : c.x1 s' * (c.x1 s)⁻¹ = m'⁻¹ * m := by
      calc c.x1 s' * (c.x1 s)⁻¹ = m'⁻¹ * (m' * c.x1 s') * (c.x1 s)⁻¹ := by group
        _ = m'⁻¹ * (m * c.x1 s) * (c.x1 s)⁻¹ := by rw [h']
        _ = m'⁻¹ * m := by group
    rw [c.x1_add, ← x1_inv c s, this]
    exact (M R A).mul_mem ((M R A).inv_mem hm') hm
  have h2 : s' + -s = 0 := hint _ h1
  have h3 : s = s' := by
    have := add_neg_eq_zero.1 h2
    exact this.symm
  subst h3
  have : m = m' := mul_right_cancel h'
  subst this
  rfl

theorem le_MX {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTN : ∀ x ∈ Subgroup.normalizer (A : Set G), x ∈ Subgroup.normalizer (T : Set G))
    (hint : ∀ s : E, c.x1 s ∈ M R A → s = 0) {k o : ℕ} (hodd : Odd o)
    (hG : Nat.card G = 2 ^ k * o) (hk : 2 ^ k ≤ Nat.card (M R A) * Nat.card E) :
    T ≤ MX S c := by
  have := S.hyp.finite
  refine le_of_normalizes_of_card_le hT2 (isPGroup_MX c)
    (fun x hx => hTN x (MX_le_normalizer c hx)) fun K hK => ?_
  exact (card_le_of_isPGroup_two hodd hG hK).trans (hk.trans (card_MX_ge c hint))

variable [CharP F 2] [Finite F] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)

include he in
theorem eq_zero_of_ad_fixed {s : E}
    (h : S.ad (c.x1_mem_normalizer s) (c.vc 1 0 0 0) = c.vc 1 0 0 0) : s = 0 := by
  have := S.hyp.finite
  rw [c.ad_x1 e he] at h
  have h2 := (c.vc_injective h).2.1
  simpa using h2

include he in
theorem x1_eq_zero_of_mem_M {s : E} (hs : c.x1 s ∈ M R A) : s = 0 :=
  eq_zero_of_ad_fixed c e he (ad_of_mem_M S hs (c.x1_mem_normalizer s) _)

include he in
theorem eq_zero_of_mem_T {T : Subgroup G}
    (hTN : ∀ x ∈ Subgroup.normalizer (A : Set G), x ∈ Subgroup.normalizer (T : Set G))
    (hTM : ∀ t ∈ T, t ∈ M R A → t ∈ A) {m : G} (hm : m ∈ M R A) {s : E}
    (ht : m * c.x1 s ∈ T) : s = 0 := by
  have := S.hyp.finite
  have hmN := M_le_normalizer S hm
  have hxN := c.x1_mem_normalizer s
  have htN : m * c.x1 s ∈ Subgroup.normalizer (A : Set G) := Subgroup.mul_mem _ hmN hxN
  have hy : c.x6 1 ∈ M R A := S.P_le_M (c.x6_mem 1)
  have hty : m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹ ∈ M R A :=
    conj_mem_M_of_mem_normalizer S.hyp.root htN ((M R A).inv_mem hy)
  have hz : c.x6 1 * (m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹) ∈ M R A :=
    (M R A).mul_mem hy hty
  have hzT : c.x6 1 * (m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹) ∈ T := by
    have hyT : c.x6 1 ∈ Subgroup.normalizer (T : Set G) := hTN _ (M_le_normalizer S hy)
    have h1 : c.x6 1 * (m * c.x1 s) * (c.x6 1)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hyT _).1 ht
    have : c.x6 1 * (m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹) =
        (c.x6 1 * (m * c.x1 s) * (c.x6 1)⁻¹) * (m * c.x1 s)⁻¹ := by group
    rw [this]
    exact T.mul_mem h1 (T.inv_mem ht)
  have hzA := hTM _ hzT hz
  have h1 : S.proj ⟨_, hz⟩ = 1 := S.proj_A hzA
  have e2 : ∀ v : S.V, S.ad htN v = S.ad hxN v := fun v => by
    have := S.ad_mul hmN hxN v
    rw [ad_of_mem_M S hm hmN] at this
    exact this
  have e1 : S.proj ⟨c.x6 1 * (m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹), hz⟩ =
      c.vc 1 0 0 0 * (S.ad hxN (c.vc 1 0 0 0))⁻¹ := by
    have hsplit : (⟨c.x6 1 * (m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹), hz⟩ : ↥(M R A)) =
        ⟨c.x6 1, hy⟩ * ⟨m * c.x1 s * (c.x6 1)⁻¹ * (m * c.x1 s)⁻¹, hty⟩ := rfl
    rw [hsplit, map_mul, proj_x6_eq_vc c 1]
    congr 1
    have h2 := S.proj_conj_eq_ad htN ⟨(c.x6 1)⁻¹, (M R A).inv_mem hy⟩ hty
    rw [h2]
    have h3 : S.proj ⟨(c.x6 1)⁻¹, (M R A).inv_mem hy⟩ = (c.vc 1 0 0 0)⁻¹ := by
      rw [← proj_x6_eq_vc c 1, ← map_inv]
      rfl
    rw [h3, map_inv, e2]
  rw [h1] at e1
  have e3 : S.ad hxN (c.vc 1 0 0 0) = c.vc 1 0 0 0 := by
    have := e1.symm
    rw [mul_inv_eq_one] at this
    exact this.symm
  exact eq_zero_of_ad_fixed c e he e3

include he in
theorem le_A
    (hfix : ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (c.x1_mem_normalizer s) (c.vc u w r v) = c.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0)
    {T : Subgroup G} (hAT : A ≤ T) (hT2 : IsPGroup 2 T)
    (hTN : ∀ x ∈ Subgroup.normalizer (A : Set G), x ∈ Subgroup.normalizer (T : Set G))
    (hTP' : ∀ v : F, c.x2 v ∈ T → v = 0) {k o : ℕ} (hodd : Odd o)
    (hG : Nat.card G = 2 ^ k * o) (hk : 2 ^ k ≤ Nat.card (M R A) * Nat.card E) : T ≤ A := by
  have := S.hyp.finite
  have hint : ∀ s : E, c.x1 s ∈ M R A → s = 0 := fun s hs => x1_eq_zero_of_mem_M c e he hs
  have hTM : ∀ t ∈ T, t ∈ M R A → t ∈ A := by
    intro t ht htM
    have hle : T ⊓ M R A ≤ A := le_of_fixed c hfix (T := T ⊓ M R A)
      (le_inf hAT QD.le_M_self) inf_le_right hT2.to_inf_left
      (fun s t ht => ⟨(Subgroup.mem_normalizer_iff.1 (hTN _ (c.x1_mem_normalizer s)) t).1 ht.1,
        conj_mem_M_of_mem_normalizer S.hyp.root (c.x1_mem_normalizer s) ht.2⟩)
      (fun v hv => hTP' v hv.1)
    exact hle ⟨ht, htM⟩
  have hTMX := le_MX c hT2 hTN hint hodd hG hk
  intro t ht
  obtain ⟨m, hm, s, rfl⟩ := hTMX ht
  have hs := eq_zero_of_mem_T c e he hTN hTM hm ht
  subst hs
  rw [c.x1_zero, mul_one] at ht ⊢
  exact hTM _ ht hm

end Char

end Apt

end CFSG.CGT.T75O
