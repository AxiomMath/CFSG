module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

section TwoPart

variable (G : Type*) [Group G] [Finite G]

theorem exists_twoPartExp : ∃ e : ℕ, e ≡ 1 [MOD 2 ^ (Nat.card G).factorization 2] ∧
    (∀ x : G, (x ^ e) ^ 2 ^ (Nat.card G).factorization 2 = 1) ∧
    (∀ x : G, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ^ e = x) ∧
    (∀ x : G, Odd (orderOf x) → x ^ e = 1) := by
  set n := Nat.card G with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set E := n.factorization 2 with hE
  set o := n / 2 ^ E with ho
  have hno : 2 ^ E * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ E) o :=
    (Nat.coprime_ordCompl Nat.prime_two hn0).pow_left E
  obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hcop 1 0
  have hoe : o ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
  refine ⟨e, he1, fun x => ?_, fun x k hx => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc⟩ := hoe
    rw [← pow_mul, hc, show o * c * 2 ^ E = 2 ^ E * o * c by ring, hno, pow_mul,
      pow_card_eq_one', one_pow]
  · have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hjn : 2 ^ j ∣ n := hj ▸ orderOf_dvd_natCard x
    have hjE : j ≤ E := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).1 hjn
    have hmod : e ≡ 1 [MOD orderOf x] := by
      rw [hj]
      exact Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hjE) he1
    calc x ^ e = x ^ 1 := pow_eq_pow_iff_modEq.2 hmod
      _ = x := pow_one x
  · have hdvd : orderOf x ∣ 2 ^ E * o := hno ▸ orderOf_dvd_natCard x
    have hco : Nat.Coprime (orderOf x) (2 ^ E) := (Odd.coprime_two_right hx).pow_right E
    have hxo : orderOf x ∣ o := hco.dvd_of_dvd_mul_left hdvd
    exact orderOf_dvd_iff_pow_eq_one.1 (hxo.trans hoe)

end TwoPart

theorem eq_one_of_odd_of_pow_two {G : Type*} [Group G] {x : G} (hodd : Odd (orderOf x)) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 :=
  UnbalancedCatalog.EvenLinearSL.eq_one_of_odd_orderOf hodd hk

theorem odd_orderOf_of_mem {G : Type*} [Group G] {H : Subgroup G} (hH : Odd (Nat.card H))
    {x : G} (hx : x ∈ H) : Odd (orderOf x) :=
  hH.of_dvd_nat (Subgroup.orderOf_dvd_natCard H hx)

theorem odd_card_center_of_psl3 {Q : Type} [Group Q] [Finite Q] (hQ : commutator Q = ⊤) {m : ℕ}
    (hm : 3 ≤ m)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Q ⧸ center Q) .PSL 3 2 m) :
    Odd (Nat.card (center Q)) := by
  set n := Nat.card Q with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set E := n.factorization 2 with hE
  set o := n / 2 ^ E with ho
  have hno : 2 ^ E * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hoodd : ¬ 2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two hn0
  let O : Subgroup Q :=
    { carrier := {z | z ∈ center Q ∧ z ^ o = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have hab : Commute a b := mem_center_iff.1 hb.1 a
        rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hOZ : O ≤ center Q := fun z hz => hz.1
  have : O.Normal := normal_of_le_center hOZ
  let η : Q ⧸ O →* Q ⧸ center Q := QuotientGroup.map O (center Q) (MonoidHom.id Q) hOZ
  have hη : Function.Surjective η := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(q : Q ⧸ O), rfl⟩
  have hker : ∀ q : Q, (q : Q ⧸ O) ∈ η.ker ↔ q ∈ center Q := by
    intro q
    rw [MonoidHom.mem_ker]
    change ((q : Q) : Q ⧸ center Q) = 1 ↔ _
    exact QuotientGroup.eq_one_iff q
  have hC : η.ker ≤ center (Q ⧸ O) := by
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq := (hker q).1 hx
    rw [mem_center_iff]
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hq r]
  have h2 : IsPGroup 2 η.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq := (hker q).1 hx
    refine ⟨E, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨pow_mem hq _, ?_⟩
    rw [← pow_mul, hno, hn, pow_card_eq_one']
  have : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ
  have hperf : Group.IsPerfect (Q ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hJ : CFSG.Blueprint.LieModel (Q ⧸ center Q) .PSL 3 2 m :=
    Or.inl ⟨by decide, h⟩
  obtain ⟨hbot, -⟩ :=
    LinearCover.even_linear_three_large_field_catalog_central_two_cover_trivial η hη hC h2 hm hJ
  have hZO : ∀ z ∈ center Q, z ^ o = 1 := by
    intro z hz
    have h1 : (z : Q ⧸ O) ∈ η.ker := (hker z).2 hz
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1.2
  by_contra hne
  have h2d : 2 ∣ Nat.card (center Q) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2 h2d
  have hzo : (z : Q) ^ o = 1 := hZO z z.2
  have h3 : orderOf (z : Q) ∣ o := orderOf_dvd_of_pow_eq_one hzo
  rw [Subgroup.orderOf_coe, hz] at h3
  exact hoodd h3

theorem map_center_eq_inf_centralizer {G : Type*} [Group G] (A : Subgroup G) :
    (center A).map A.subtype = A ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.1 ha ⟨y, hy⟩)
  · rintro ⟨hxA, hxC⟩
    refine ⟨⟨x, hxA⟩, mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.1 hxC y y.2

theorem card_inf_centralizer_eq {G : Type*} [Group G] (A : Subgroup G) :
    Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) = Nat.card (center A) := by
  rw [← map_center_eq_inf_centralizer, card_map_of_injective A.subtype_injective]

theorem pow_eq_self_of_dvd {G M : Type*} [Group G] [Finite G] [Group M] {e : ℕ}
    (he : e ≡ 1 [MOD 2 ^ (Nat.card G).factorization 2]) {y : M} {k : ℕ} (hy : y ^ 2 ^ k = 1)
    (hord : orderOf y ∣ Nat.card G) : y ^ e = y := by
  have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hjG : 2 ^ j ∣ Nat.card G := by rw [← hj]; exact hord
  have hjE : j ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hjG
  have hmod : e ≡ 1 [MOD orderOf y] := by
    rw [hj]
    exact Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hjE) he
  calc y ^ e = y ^ 1 := pow_eq_pow_iff_modEq.2 hmod
    _ = y := pow_one y

section Action

variable {G : Type*} [Group G] {F : Type} [Field F] {A : Subgroup G}
  {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}

theorem psi_mul {x y : G} (hx : x ∈ normalizer (A : Set G)) (hy : y ∈ normalizer (A : Set G)) :
    ψ ⟨x * y, mul_mem hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ :=
  map_mul ψ ⟨x, hx⟩ ⟨y, hy⟩

theorem psi_inv {x : G} (hx : x ∈ normalizer (A : Set G)) :
    ψ ⟨x⁻¹, inv_mem hx⟩ = (ψ ⟨x, hx⟩)⁻¹ :=
  map_inv ψ ⟨x, hx⟩

theorem psi_pow {x : G} (hx : x ∈ normalizer (A : Set G)) (n : ℕ) :
    ψ ⟨x ^ n, pow_mem hx n⟩ = (ψ ⟨x, hx⟩) ^ n :=
  map_pow ψ ⟨x, hx⟩ n

theorem psi_commutatorElement {x y : G} (hx : x ∈ normalizer (A : Set G))
    (hy : y ∈ normalizer (A : Set G)) :
    ψ ⟨⁅x, y⁆, by rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem hx hy)
      (inv_mem hx)) (inv_mem hy)⟩ = ⁅ψ ⟨x, hx⟩, ψ ⟨y, hy⟩⁆ :=
  map_commutatorElement ψ ⟨x, hx⟩ ⟨y, hy⟩

variable (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
include hψ

theorem inv_mul_mem_of_psi_eq {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩) :
    a⁻¹ * b ∈ A ⊓ centralizer (A : Set G) := by
  refine ⟨A.mul_mem (A.inv_mem ha) hb, ?_⟩
  refine (hψ.eq_one_iff ⟨a⁻¹ * b, le_normalizer (A.mul_mem (A.inv_mem ha) hb)⟩).1 ?_
  rw [psi_mul (inv_mem (le_normalizer ha)) (le_normalizer hb), psi_inv (le_normalizer ha), h,
    inv_mul_cancel]

theorem eq_of_psi_eq (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) {k : ℕ} (hak : a ^ 2 ^ k = 1) (hbk : b ^ 2 ^ k = 1)
    (h : ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩) : a = b := by
  have hz := inv_mul_mem_of_psi_eq hψ ha hb h
  have hcomm : Commute a (a⁻¹ * b) := (mem_centralizer_iff.1 hz.2 a ha)
  have hzk : (a⁻¹ * b) ^ 2 ^ k = 1 := by
    have h1 : b = a * (a⁻¹ * b) := by group
    rw [h1, hcomm.mul_pow, hak, one_mul] at hbk
    exact hbk
  have h1 := eq_one_of_odd_of_pow_two (odd_orderOf_of_mem hZ hz) hzk
  rw [inv_mul_eq_one] at h1
  exact h1

theorem exists_two_lift [Finite G] {x : MulAut (projectiveSL 3 F)}
    (hx : x ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) :
    ∃ a : G, ∃ ha : a ∈ A, a ^ 2 ^ (Nat.card G).factorization 2 = 1 ∧
      ψ ⟨a, le_normalizer ha⟩ = x := by
  obtain ⟨a₀, ha₀, h₀⟩ := hψ.exists_eq x hx
  obtain ⟨e, he1, he2, -, -⟩ := exists_twoPartExp G
  refine ⟨a₀ ^ e, pow_mem ha₀ e, he2 a₀, ?_⟩
  rw [psi_pow (le_normalizer ha₀), h₀]
  refine pow_eq_self_of_dvd he1 hxk ?_
  rw [← h₀]
  refine (orderOf_map_dvd ψ _).trans ?_
  rw [Subgroup.orderOf_mk]
  exact orderOf_dvd_natCard a₀

theorem commute_of_psi_commute (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {t : G} (htN : t ∈ normalizer (A : Set G)) (ht2 : t * t = 1)
    (htZ : ∀ z ∈ A ⊓ centralizer (A : Set G), t * z = z * t) {y : G} (hy : y ∈ A)
    (hc : ψ ⟨y, le_normalizer hy⟩ * ψ ⟨t, htN⟩ = ψ ⟨t, htN⟩ * ψ ⟨y, le_normalizer hy⟩) :
    y * t = t * y := by
  have hzA : y * t * y⁻¹ * t⁻¹ ∈ A := by
    have h1 : t * y⁻¹ * t⁻¹ ∈ A := (mem_normalizer_iff.1 htN y⁻¹).1 (A.inv_mem hy)
    have h2 := A.mul_mem hy h1
    simpa [mul_assoc] using h2
  have hzC : y * t * y⁻¹ * t⁻¹ ∈ centralizer (A : Set G) := by
    refine (hψ.eq_one_iff ⟨y * t * y⁻¹ * t⁻¹, le_normalizer hzA⟩).1 ?_
    rw [psi_mul (mul_mem (mul_mem (le_normalizer hy) htN) (inv_mem (le_normalizer hy)))
        (inv_mem htN), psi_mul (mul_mem (le_normalizer hy) htN) (inv_mem (le_normalizer hy)),
      psi_mul (le_normalizer hy) htN, psi_inv (le_normalizer hy), psi_inv htN, hc]
    group
  set z := y * t * y⁻¹ * t⁻¹ with hz
  have hzt : t * z = z * t := htZ z ⟨hzA, hzC⟩
  have hytz : y * t * y⁻¹ = z * t := by rw [hz]; group
  have hz2 : z ^ 2 ^ 1 = 1 := by
    have h1 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
      calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
    rw [hytz] at h1
    calc z ^ 2 ^ 1 = z * z * (t * t) := by rw [ht2, mul_one, pow_one, sq]
      _ = z * (z * t) * t := by group
      _ = z * (t * z) * t := by rw [hzt]
      _ = (z * t) * (z * t) := by group
      _ = 1 := h1
  have h1 := eq_one_of_odd_of_pow_two (odd_orderOf_of_mem hZ (show z ∈ _ from ⟨hzA, hzC⟩)) hz2
  rw [hz] at h1
  calc y * t = y * t * y⁻¹ * t⁻¹ * (t * y) := by group
    _ = t * y := by rw [h1, one_mul]

end Action

section Conj

variable {G : Type} [Group G] {F : Type} [Field F] {A : Subgroup G}

omit [Group G] in
theorem mem_centralizer_rightConjugate_iff [Group G] (A : Subgroup G) (g x : G) :
    x ∈ centralizer (rightConjugate A g : Set G) ↔ g * x * g⁻¹ ∈ centralizer (A : Set G) := by
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_rightConjugate_iff]
  constructor
  · intro h a ha
    have h1 := h (g⁻¹ * a * g) (by simpa [mul_assoc] using ha)
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * a := by group
  · intro h y hy
    have h1 := h _ hy
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group

@[expose] def conjAct (ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)) (g : G) :
    normalizer (rightConjugate A g : Set G) →* MulAut (projectiveSL 3 F) :=
  ψ.comp
    { toFun := fun x => ⟨g * x * g⁻¹, (AS76b.mem_normalizer_rightConjugate_iff A g x).1 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change g * (x * y : G) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
        group) }

theorem conjAct_apply (ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)) (g x : G)
    (hx : x ∈ normalizer (rightConjugate A g : Set G)) :
    conjAct ψ g ⟨x, hx⟩ =
      ψ ⟨g * x * g⁻¹, (AS76b.mem_normalizer_rightConjugate_iff A g x).1 hx⟩ :=
  rfl

theorem isActionHom_conjAct {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (g : G) :
    IsActionHom (rightConjugate A g)
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range (conjAct ψ g) := by
  refine ⟨fun a ha => ?_, fun x hx => ?_, fun n => ?_⟩
  · rw [conjAct_apply]
    exact hψ.map_mem _ ((mem_rightConjugate_iff A g a).1 ha)
  · obtain ⟨a, ha, h⟩ := hψ.exists_eq x hx
    have ha' : g⁻¹ * a * g ∈ rightConjugate A g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    refine ⟨g⁻¹ * a * g, ha', ?_⟩
    rw [conjAct_apply, ← h]
    congr 1
    apply Subtype.ext
    simp only
    group
  · obtain ⟨x, hx⟩ := n
    rw [conjAct_apply, hψ.eq_one_iff, mem_centralizer_rightConjugate_iff]

theorem inf_centralizer_rightConjugate (A : Subgroup G) (g : G) :
    rightConjugate A g ⊓ centralizer (rightConjugate A g : Set G) =
      rightConjugate (A ⊓ centralizer (A : Set G)) g := by
  ext x
  simp only [mem_inf, mem_rightConjugate_iff, mem_centralizer_rightConjugate_iff]

theorem card_inf_centralizer_rightConjugate [Finite G] (A : Subgroup G) (g : G) :
    Nat.card (rightConjugate A g ⊓ centralizer (rightConjugate A g : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) := by
  rw [inf_centralizer_rightConjugate, rightConjugate_card]

end Conj

theorem commute_of_mem_commutator {G : Type*} [Group G] {S Z : Subgroup G}
    (hZS : Z ≤ centralizer (S : Set G)) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {w : G}
    (hw : ∀ s ∈ S, w * s * w⁻¹ * s⁻¹ ∈ Z) {x : G} (hx : x ∈ ⁅S, S⁆) : w * x = x * w := by
  have hmul : ∀ s₁ ∈ S, ∀ s₂ ∈ S, w * (s₁ * s₂) * w⁻¹ * (s₁ * s₂)⁻¹ =
      (w * s₁ * w⁻¹ * s₁⁻¹) * (w * s₂ * w⁻¹ * s₂⁻¹) := by
    intro s₁ h₁ s₂ h₂
    have c : s₁ * (w * s₂ * w⁻¹ * s₂⁻¹) * s₁⁻¹ = w * s₂ * w⁻¹ * s₂⁻¹ := by
      rw [mem_centralizer_iff.1 (hZS (hw s₂ h₂)) s₁ h₁, mul_inv_cancel_right]
    calc w * (s₁ * s₂) * w⁻¹ * (s₁ * s₂)⁻¹
        = (w * s₁ * w⁻¹ * s₁⁻¹) * (s₁ * (w * s₂ * w⁻¹ * s₂⁻¹) * s₁⁻¹) := by group
      _ = (w * s₁ * w⁻¹ * s₁⁻¹) * (w * s₂ * w⁻¹ * s₂⁻¹) := by rw [c]
  have hinv : ∀ s ∈ S, w * s⁻¹ * w⁻¹ * s⁻¹⁻¹ = (w * s * w⁻¹ * s⁻¹)⁻¹ := by
    intro s hs
    have h := hmul s hs s⁻¹ (inv_mem hs)
    rw [mul_inv_cancel, mul_one, inv_one, mul_one, mul_inv_cancel] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hle : ⁅S, S⁆ ≤ centralizer ({w} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_centralizer_singleton_iff]
    have hc : (w * a * w⁻¹ * a⁻¹) * (w * b * w⁻¹ * b⁻¹) =
        (w * b * w⁻¹ * b⁻¹) * (w * a * w⁻¹ * a⁻¹) := hZ _ (hw a ha) _ (hw b hb)
    have hfab : w * ⁅a, b⁆ * w⁻¹ * ⁅a, b⁆⁻¹ = 1 := by
      rw [commutatorElement_def, hmul _ (mul_mem (mul_mem ha hb) (inv_mem ha)) _ (inv_mem hb),
        hmul _ (mul_mem ha hb) _ (inv_mem ha), hmul _ ha _ hb, hinv a ha, hinv b hb, hc]
      group
    have h1 : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := mul_inv_eq_one.1 hfab
    calc ⁅a, b⁆ * w = w * ⁅a, b⁆ * w⁻¹ * w := by rw [h1]
      _ = w * ⁅a, b⁆ := by group
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

end CFSG.ComponentClassification.RankTwoL3Even
