module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GL83PartI.I_20_1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Lift

variable {Z : Type} [Group Z] [Finite Z]

private theorem stepC_exists_lift {p : ℕ} (hp : p.Prime) (N : Subgroup Z) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {Ē : Subgroup (Z ⧸ N)} (hĒ : IsElemAbelian p Ē) :
    ∃ S : Subgroup Z, IsElemAbelian p S ∧ Nat.card S = Nat.card Ē ∧
      S ≤ Ē.comap (QuotientGroup.mk' N) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hĒ).exists_card_eq
  set F : Subgroup Z := Ē.comap (QuotientGroup.mk' N) with hF
  have hFcard : Nat.card F = Nat.card N * p ^ k := by
    rw [← hk]
    exact QuotientGroup.card_preimage_mk N (Ē : Set (Z ⧸ N))
  have hdvd : p ^ k ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_mul_left _ _
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  set S₀ : Subgroup Z := K.map F.subtype with hS₀
  have hS₀card : Nat.card S₀ = p ^ k := by
    rw [hS₀, Subgroup.card_map_of_injective F.subtype_injective, hK]
  have hS₀F : S₀ ≤ F := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hcopN : Nat.Coprime (Nat.card S₀) (Nat.card N) := by
    rw [hS₀card]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  have hinter : S₀ ⊓ N = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcopN)
  have hmem : ∀ x ∈ S₀, QuotientGroup.mk' N x ∈ Ē := fun x hx => hS₀F hx
  have hinj : ∀ x ∈ S₀, ∀ y ∈ S₀, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
    intro x hx y hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
    have h1 : x⁻¹ * y ∈ S₀ ⊓ N := ⟨S₀.mul_mem (S₀.inv_mem hx) hy, hxy⟩
    rw [hinter, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hcomm : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x := by
    intro x hx y hy
    apply hinj (x * y) (S₀.mul_mem hx hy) (y * x) (S₀.mul_mem hy hx)
    rw [map_mul, map_mul]
    have := congrArg Subtype.val (hĒ.1.1.comm ⟨_, hmem x hx⟩ ⟨_, hmem y hy⟩)
    simpa using this
  have hexp : ∀ x ∈ S₀, x ^ p = 1 := by
    intro x hx
    have h1 : QuotientGroup.mk' N (x ^ p) = 1 := by
      rw [map_pow]
      exact hĒ.2 _ (hmem x hx)
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : x ^ p ∈ S₀ ⊓ N := ⟨S₀.pow_mem hx p, (QuotientGroup.eq_one_iff _).1 h1⟩
    rw [hinter, Subgroup.mem_bot] at h2
    exact h2
  refine ⟨S₀, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => hexp x hx⟩,
    hS₀card.trans hk.symm, ?_⟩
  exact fun x hx => hS₀F hx

end Lift

section Abstract

variable {Z : Type} [Group Z] [Finite Z]

private theorem stepC_conj_into {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {M : Subgroup Y} (hM : IsPGroup p M) (hidx : ¬ p ∣ M.index) {E : Subgroup Y}
    (hE : IsPGroup p E) : ∃ g : Y, ∀ x ∈ E, g⁻¹ * x * g ∈ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₁, hEP₁⟩ := IsPGroup.exists_le_sylow hE
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (hM.toSylow hidx) P₁
  refine ⟨g, fun x hx => ?_⟩
  have hxP : x ∈ ((g • hM.toSylow hidx : Sylow p Y) : Subgroup Y) := by
    rw [hg]
    exact hEP₁ hx
  rw [Sylow.coe_subgroup_smul] at hxP
  obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hxP
  have hyeq : y = g⁻¹ * x * g := by
    rw [← hyx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hyeq]
  exact hy

private theorem stepC_card_eq_mul {Y : Type} [Group Y] [Finite Y] {R M : Subgroup Y}
    (h : ∀ y : Y, ∃ r ∈ R, ∃ m ∈ M, y = r * m) (hRM : R ⊓ M = ⊥) :
    Nat.card Y = Nat.card R * Nat.card M := by
  classical
  let f : R × M → Y := fun z => (z.1 : Y) * (z.2 : Y)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, m⟩ ⟨r', m'⟩ hrm
      have hrm' : (r : Y) * (m : Y) = (r' : Y) * (m' : Y) := hrm
      have hkey : (r' : Y)⁻¹ * (r : Y) ∈ R ⊓ M := by
        refine ⟨R.mul_mem (R.inv_mem r'.2) r.2, ?_⟩
        have hq : (r' : Y)⁻¹ * (r : Y) = (m' : Y) * (m : Y)⁻¹ := by
          calc (r' : Y)⁻¹ * (r : Y) = (r' : Y)⁻¹ * ((r : Y) * (m : Y)) * (m : Y)⁻¹ := by group
            _ = (r' : Y)⁻¹ * ((r' : Y) * (m' : Y)) * (m : Y)⁻¹ := by rw [hrm']
            _ = (m' : Y) * (m : Y)⁻¹ := by group
        rw [hq]
        exact M.mul_mem m'.2 (M.inv_mem m.2)
      rw [hRM, Subgroup.mem_bot, inv_mul_eq_one] at hkey
      have hm : (m : Y) = (m' : Y) := by
        rw [← hkey] at hrm'
        exact mul_left_cancel hrm'
      exact Prod.ext (Subtype.ext hkey.symm) (Subtype.ext hm)
    · intro y
      obtain ⟨r, hr, m, hm, rfl⟩ := h y
      exact ⟨(⟨r, hr⟩, ⟨m, hm⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at this
  exact this.symm

private theorem stepC_abstract {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q R B N : Subgroup Z}
    [Q.Normal] [N.Normal] (hNQ : N ≤ Q) (hNp : ¬ p ∣ Nat.card N)
    (hQp : ∀ x ∈ Q, ∃ n : ℕ, x ^ (p ^ n) ∈ N) (hR : IsPGroup 2 R) (hB : IsElemAbelian p B)
    (hBR : B ≤ Subgroup.normalizer (R : Set Z))
    (hdec : ∀ x : Z, ∃ q ∈ Q, ∃ r ∈ R, ∃ b ∈ B, x = q * r * b)
    (hbound : ∀ E : Subgroup Z, IsElemAbelian p E → E ≤ Q ⊔ B → Nat.card E ≤ Nat.card B) :
    (⁅Q, R⁆ : Subgroup Z) ≤ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 hp2.symm
  have h2p' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hpN : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd hp).2 hNp
  set π : Z →* Z ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set Qb : Subgroup (Z ⧸ N) := Q.map π with hQb
  set Rb : Subgroup (Z ⧸ N) := R.map π with hRb
  set Bb : Subgroup (Z ⧸ N) := B.map π with hBb
  haveI hQbn : Qb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hQbtop : Subgroup.normalizer (Qb : Set (Z ⧸ N)) = ⊤ := Subgroup.normalizer_eq_top Qb
  have hBQ : Bb ≤ Subgroup.normalizer (Qb : Set (Z ⧸ N)) := by
    rw [hQbtop]
    exact le_top
  have hQbp : IsPGroup p Qb := by
    intro g
    obtain ⟨x, hxQ, hx⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨n, hn⟩ := hQp x hxQ
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hx, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn
  have hRbp : IsPGroup 2 Rb := by
    intro g
    obtain ⟨x, hxR, hx⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨n, hn⟩ := hR ⟨x, hxR⟩
    have hn' : x ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hx, ← map_pow, hn', map_one]
  have hBbel : IsElemAbelian p Bb := CFSG.SectionRank.isElemAbelian_map hB π
  have hBbp : IsPGroup p Bb := isPGroup_of_isElemAbelian hBbel
  have hconjR : ∀ b ∈ B, ∀ r ∈ R, b * r * b⁻¹ ∈ R := fun b hb r hr =>
    (Subgroup.mem_normalizer_iff.1 (hBR hb) r).1 hr
  have hBconjRb : ∀ b ∈ B, ∀ h ∈ Rb, π b * h * (π b)⁻¹ ∈ Rb := by
    intro b hb h hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨b * r * b⁻¹, hconjR b hb r hr, ?_⟩
    simp only [map_mul, map_inv]
  have hBRb : Bb ≤ Subgroup.normalizer (Rb : Set (Z ⧸ N)) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hBconjRb b hb h
    · intro hh
      have := hBconjRb b⁻¹ (B.inv_mem hb) _ hh
      simpa [map_inv, mul_assoc] using this
  have hRBQ : Rb ⊔ Bb ≤ Subgroup.normalizer (Qb : Set (Z ⧸ N)) := by
    rw [hQbtop]
    exact le_top
  have hcover : ∀ y : Z ⧸ N, y ∈ Qb ⊔ (Rb ⊔ Bb) := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨q, hq, r, hr, b, hb, rfl⟩ := hdec x
    have e : π (q * r * b) = π q * (π r * π b) := by simp only [map_mul, mul_assoc]
    rw [e]
    refine Subgroup.mul_mem _ ((le_sup_left : Qb ≤ Qb ⊔ (Rb ⊔ Bb)) (Subgroup.mem_map_of_mem π hq))
      ((le_sup_right : Rb ⊔ Bb ≤ Qb ⊔ (Rb ⊔ Bb)) (Subgroup.mul_mem _
        ((le_sup_left : Rb ≤ Rb ⊔ Bb) (Subgroup.mem_map_of_mem π hr))
        ((le_sup_right : Bb ≤ Rb ⊔ Bb) (Subgroup.mem_map_of_mem π hb))))
  have hsolv : Group.IsSolvable (Z ⧸ N) := by
    haveI : Group.IsNilpotent Qb := hQbp.isNilpotent
    haveI : Group.IsNilpotent Rb := hRbp.isNilpotent
    haveI : IsMulCommutative Bb := hBbel.1
    haveI := isSolvable_sup Rb Bb hBRb
    haveI := isSolvable_sup Qb (Rb ⊔ Bb) hRBQ
    exact Group.isSolvable_of_surjective (f := (Qb ⊔ (Rb ⊔ Bb)).subtype)
      (fun y => ⟨⟨y, hcover y⟩, rfl⟩)
  have hfact : ∀ y : Z ⧸ N, ∃ r ∈ Rb, ∃ m ∈ Qb ⊔ Bb, y = r * m := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨q, hq, r, hr, b, hb, rfl⟩ := hdec x
    have hqr : r⁻¹ * q * r ∈ Q := by
      have := Subgroup.Normal.conj_mem inferInstance q hq r⁻¹
      simpa using this
    refine ⟨π r, Subgroup.mem_map_of_mem π hr, π (r⁻¹ * q * r) * π b,
      Subgroup.mul_mem _ ((le_sup_left : Qb ≤ Qb ⊔ Bb) (Subgroup.mem_map_of_mem π hqr))
        ((le_sup_right : Bb ≤ Qb ⊔ Bb) (Subgroup.mem_map_of_mem π hb)), ?_⟩
    simp only [map_mul, map_inv]
    group
  have hprod := card_sup_mul_card_inf_of_le_normalizer hBQ
  have hMp : ∃ d : ℕ, Nat.card (Qb ⊔ Bb : Subgroup (Z ⧸ N)) = p ^ d := by
    obtain ⟨c, hc⟩ := (IsPGroup.to_le hBbp (inf_le_right : Qb ⊓ Bb ≤ Bb)).exists_card_eq
    obtain ⟨a, ha⟩ := hQbp.exists_card_eq
    obtain ⟨b, hb⟩ := hBbp.exists_card_eq
    have hdvd : Nat.card (Qb ⊔ Bb : Subgroup (Z ⧸ N)) ∣ p ^ (a + b) := by
      rw [pow_add, ← ha, ← hb]
      exact ⟨Nat.card (Qb ⊓ Bb : Subgroup (Z ⧸ N)), hprod.symm⟩
    obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨d, hd⟩
  obtain ⟨d, hd⟩ := hMp
  have hMpgrp : IsPGroup p (Qb ⊔ Bb : Subgroup (Z ⧸ N)) := (IsPGroup.iff_card).2 ⟨d, hd⟩
  obtain ⟨e, he⟩ := hRbp.exists_card_eq
  have hRM : Rb ⊓ (Qb ⊔ Bb) = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [he, hd]
    exact Nat.Coprime.pow e d h2p
  have hcardY : Nat.card (Z ⧸ N) = Nat.card Rb * Nat.card (Qb ⊔ Bb : Subgroup (Z ⧸ N)) :=
    stepC_card_eq_mul hfact hRM
  have hidx : ¬ p ∣ (Qb ⊔ Bb : Subgroup (Z ⧸ N)).index := by
    have h1 := Subgroup.index_mul_card (H := (Qb ⊔ Bb : Subgroup (Z ⧸ N)))
    rw [hcardY] at h1
    have hpos : 0 < Nat.card (Qb ⊔ Bb : Subgroup (Z ⧸ N)) := Nat.card_pos
    have h2 : (Qb ⊔ Bb : Subgroup (Z ⧸ N)).index = Nat.card Rb := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, mul_comm]
    rw [h2, he]
    exact fun h => hp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e h2p') h)
  have hBN : Nat.Coprime (Nat.card B) (Nat.card N) := by
    obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hB).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k hpN
  have hBinter : B ⊓ N = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hBN)
  have hBle : Nat.card B ≤ Nat.card Bb := by
    refine Nat.card_le_card_of_injective
      (fun b : B => (⟨π b, Subgroup.mem_map_of_mem π b.2⟩ : Bb)) ?_
    intro a b hab
    have h1 : π a = π b := congrArg Subtype.val hab
    have h2 : (a : Z)⁻¹ * (b : Z) ∈ N := QuotientGroup.eq.1 h1
    have h3 : (a : Z)⁻¹ * (b : Z) ∈ B ⊓ N := ⟨B.mul_mem (B.inv_mem a.2) b.2, h2⟩
    rw [hBinter, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hClaimM : ∀ E : Subgroup (Z ⧸ N), IsElemAbelian p E → Nat.card E ≤ Nat.card B := by
    intro E hE
    obtain ⟨g, hg⟩ := stepC_conj_into hp hMpgrp hidx (isPGroup_of_isElemAbelian hE)
    set E' : Subgroup (Z ⧸ N) := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
    have hE'el : IsElemAbelian p E' := CFSG.SectionRank.isElemAbelian_map hE _
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hE'M : E' ≤ Qb ⊔ Bb := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      have := hg x hx
      simpa [MulAut.conj_apply] using this
    obtain ⟨S, hSel, hScard, hSle⟩ := stepC_exists_lift hp N hNp hE'el
    have hSQB : S ≤ Q ⊔ B := by
      intro x hx
      have h1 : π x ∈ (Q ⊔ B).map π := by
        rw [Subgroup.map_sup]
        exact hE'M (hSle hx)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
      have hyx' : y⁻¹ * x ∈ N := QuotientGroup.eq.1 hyx
      have hx' : x = y * (y⁻¹ * x) := by group
      rw [hx']
      exact Subgroup.mul_mem _ hy ((le_sup_left : Q ≤ Q ⊔ B) (hNQ hyx'))
    calc Nat.card E = Nat.card E' := hE'card.symm
      _ = Nat.card S := hScard.symm
      _ ≤ Nat.card B := hbound S hSel hSQB
  have hBmax : ∀ E : Subgroup (Z ⧸ N), IsElemAbelian p E → Bb ≤ E → E = Bb := by
    intro E hE hle
    exact (Subgroup.eq_of_le_of_card_ge hle ((hClaimM E hE).trans hBle)).symm
  have hlayer : GLAPLayer p (⊤ : Subgroup (Z ⧸ N)) = ⊥ := glaPLayer_top_eq_bot_of_isSolvable p
  have hI20 := GL83.I_20_1_proved (Z ⧸ N) p hp hp2 hlayer Bb hBbel hBmax
  have hcopRb : Nat.Coprime p (Nat.card Rb) := by
    rw [he]
    exact Nat.Coprime.pow_right e h2p'
  have hRbO : Rb ≤ GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N)) := by
    rw [← hI20]
    exact le_iSup_of_le Rb (le_iSup_of_le hcopRb (le_iSup_of_le hBRb le_rfl))
  have hOn : (GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N))).Normal :=
    Subgroup.normalizer_eq_top_iff.1
      (top_le_iff.1 (le_normalizer_glaPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N))))
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N))) :=
    not_dvd_card_glaPPrimeCoreOf hp _
  have hQRO : ⁅Qb, Rb⁆ ≤ GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N)) := by
    calc ⁅Qb, Rb⁆ ≤ ⁅(⊤ : Subgroup (Z ⧸ N)), GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N))⁆ :=
          Subgroup.commutator_mono le_top hRbO
      _ ≤ GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N)) := Subgroup.commutator_le_right _ _
  have hQRQ : ⁅Qb, Rb⁆ ≤ Qb := Subgroup.commutator_le_left _ _
  obtain ⟨a, ha⟩ := hQbp.exists_card_eq
  have hQO : Qb ⊓ GLAPPrimeCoreOf p (⊤ : Subgroup (Z ⧸ N)) = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hOp)
  have hQR0 : ⁅Qb, Rb⁆ ≤ ⊥ := (le_inf hQRQ hQRO).trans (le_of_eq hQO)
  rw [Subgroup.commutator_le]
  intro q hq r hr
  have h1 : ⁅π q, π r⁆ ∈ ⁅Qb, Rb⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hq)
      (Subgroup.mem_map_of_mem π hr)
  have h2 : ⁅π q, π r⁆ = 1 := Subgroup.mem_bot.1 (hQR0 h1)
  rw [← map_commutatorElement] at h2
  exact (QuotientGroup.eq_one_iff _).1 h2

end Abstract

section Bound

variable {G : Type} [Group G] [Finite G]

private theorem stepC_oPPrimeP_le (p : ℕ) (X : Subgroup G) : oPPrimeP p X ≤ X := by
  unfold oPPrimeP
  exact Subgroup.map_subtype_le _

private theorem stepC_conj_mem_oPPrimeP {p : ℕ} {X : Subgroup G} {x h : G} (hx : x ∈ X)
    (hh : h ∈ oPPrimeP p X) : x * h * x⁻¹ ∈ oPPrimeP p X := by
  unfold oPPrimeP at hh ⊢
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hh
  refine Subgroup.mem_map.2 ⟨(⟨x, hx⟩ : ↥X) * m * (⟨x, hx⟩ : ↥X)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_comap] at hm ⊢
    rw [map_mul, map_mul, map_inv]
    haveI : (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).Normal := CFSG.pCore_normal
    exact Subgroup.Normal.conj_mem inferInstance _ hm _
  · simp

private theorem stepC_le_normalizer_oPPrimeP (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oPPrimeP p X : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact stepC_conj_mem_oPPrimeP hx hh
  · intro hh
    have := stepC_conj_mem_oPPrimeP (X := X) (X.inv_mem hx) hh
    simpa [mul_assoc] using this

private theorem stepC_glaPPrimeCoreOf_le_oPPrimeP (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X ≤ oPPrimeP p X := by
  intro o ho
  unfold GLAPPrimeCoreOf at ho
  obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
  unfold oPPrimeP
  refine Subgroup.mem_map.2 ⟨o', ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) o' = 1 :=
    (QuotientGroup.eq_one_iff o').2 ho'
  rw [h1]
  exact Subgroup.one_mem _

private theorem stepC_oPPrimeP_pow_mem (p : ℕ) (X : Subgroup G) {q : G}
    (hq : q ∈ oPPrimeP p X) : ∃ n : ℕ, q ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  unfold oPPrimeP at hq
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hq
  rw [Subgroup.mem_comap] at hm
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨_, hm⟩ : ↥(CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)))
  refine ⟨n, ?_⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (m ^ (p ^ n)) = 1 := by
    rw [map_pow]
    have := congrArg Subtype.val hn
    simpa using this
  unfold GLAPPrimeCoreOf
  refine Subgroup.mem_map.2 ⟨m ^ (p ^ n), (QuotientGroup.eq_one_iff _).1 h1, ?_⟩
  simp

private def stepC_rZero (p : ℕ) (X R : Subgroup G) (hRX : R ≤ X) : Subgroup G where
  carrier := {r | r ∈ R ∧ ∀ q ∈ oPPrimeP p X, ⁅q, r⁆ ∈ GLAPPrimeCoreOf p X}
  one_mem' := ⟨R.one_mem, fun q _ => by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hLa⟩ ⟨hb, hLb⟩
    refine ⟨R.mul_mem ha hb, fun q hq => ?_⟩
    rw [commutatorElement_mul_right]
    refine Subgroup.mul_mem _ (hLa q hq) ?_
    exact (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p X (hRX ha)) _).1 (hLb q hq)
  inv_mem' := by
    rintro a ⟨ha, hLa⟩
    refine ⟨R.inv_mem ha, fun q hq => ?_⟩
    rw [commutatorElement_inv_right]
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p X (hRX (R.inv_mem ha))) ⁅q, a⁆⁻¹).1
      (Subgroup.inv_mem _ (hLa q hq))
    simpa [inv_inv] using this

private theorem stepC_card_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B R X : Subgroup G}
    (hB : GLAIsBmax p B) (hBX : B ≤ X) (hR2 : IsPGroup 2 R) (hRX : R ≤ X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hR₀ : ∃ r ∈ R, r ≠ 1 ∧ ∀ q ∈ oPPrimeP p X, ⁅q, r⁆ ∈ GLAPPrimeCoreOf p X)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEQ : E ≤ oPPrimeP p X ⊔ B) :
    Nat.card E ≤ Nat.card B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r₀, hr₀R, hr₀ne, hr₀O⟩ := hR₀
  set Q₀ := oPPrimeP p X with hQ₀
  set O := GLAPPrimeCoreOf p X with hO
  set R₀ := stepC_rZero p X R hRX with hR₀def
  have hr₀mem : r₀ ∈ R₀ := ⟨hr₀R, hr₀O⟩
  have hR₀R : R₀ ≤ R := fun _ hr => hr.1
  have hQX : Q₀ ≤ X := stepC_oPPrimeP_le p X
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hR₀N : R₀ ≤ Subgroup.normalizer (O : Set G) := fun r hr => hXN (hRX (hR₀R hr))
  have hmemK : ∀ h ∈ O ⊔ R₀, ∃ o ∈ O, ∃ r ∈ R₀, h = o * r := by
    intro h hh
    have hh' : h ∈ (↑(O ⊔ R₀) : Set G) := hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O R₀ hR₀N] at hh'
    obtain ⟨o, ho, r, hr, hor⟩ := hh'
    exact ⟨o, ho, r, hr, hor.symm⟩
  have hconjQ : ∀ q ∈ Q₀, ∀ h ∈ O ⊔ R₀, q * h * q⁻¹ ∈ O ⊔ R₀ := by
    intro q hq h hh
    obtain ⟨o, ho, r, hr, rfl⟩ := hmemK h hh
    have hqo : q * o * q⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hXN (hQX hq)) o).1 ho
    have hqr : ⁅q, r⁆ ∈ O := hr.2 q hq
    have key : q * (o * r) * q⁻¹ = (q * o * q⁻¹ * ⁅q, r⁆) * r := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Subgroup.mul_mem _ ((le_sup_left : O ≤ O ⊔ R₀) (Subgroup.mul_mem _ hqo hqr))
      ((le_sup_right : R₀ ≤ O ⊔ R₀) hr)
  have hbR : ∀ b ∈ B, ∀ r ∈ R₀, b * r * b⁻¹ ∈ R₀ := by
    intro b hb r hr
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hBR hb) r).1 hr.1, fun q hq => ?_⟩
    have hq' : b⁻¹ * q * b⁻¹⁻¹ ∈ Q₀ :=
      stepC_conj_mem_oPPrimeP (X := X) (X.inv_mem (hBX hb)) hq
    rw [inv_inv] at hq'
    have key : ⁅q, b * r * b⁻¹⁆ = b * ⁅b⁻¹ * q * b, r⁆ * b⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (Subgroup.mem_normalizer_iff.1 (hXN (hBX hb)) _).1 (hr.2 _ hq')
  have hconjB : ∀ b ∈ B, ∀ h ∈ O ⊔ R₀, b * h * b⁻¹ ∈ O ⊔ R₀ := by
    intro b hb h hh
    obtain ⟨o, ho, r, hr, rfl⟩ := hmemK h hh
    have hbo : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hXN (hBX hb)) o).1 ho
    have key : b * (o * r) * b⁻¹ = (b * o * b⁻¹) * (b * r * b⁻¹) := by group
    rw [key]
    exact Subgroup.mul_mem _ ((le_sup_left : O ≤ O ⊔ R₀) hbo)
      ((le_sup_right : R₀ ≤ O ⊔ R₀) (hbR b hb r hr))
  have hQN : Q₀ ≤ Subgroup.normalizer ((O ⊔ R₀ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjQ q hq h hh
    · intro hh
      have := hconjQ q⁻¹ (Q₀.inv_mem hq) _ hh
      simpa [mul_assoc] using this
  have hBN : B ≤ Subgroup.normalizer ((O ⊔ R₀ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjB b hb h hh
    · intro hh
      have := hconjB b⁻¹ (B.inv_mem hb) _ hh
      simpa [mul_assoc] using this
  have hEN : E ≤ Subgroup.normalizer ((O ⊔ R₀ : Subgroup G) : Set G) :=
    hEQ.trans (sup_le hQN hBN)
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp X
  have hR₀2 : IsPGroup 2 R₀ := IsPGroup.to_le hR2 hR₀R
  obtain ⟨n, hn⟩ := hR₀2.exists_card_eq
  have hR₀p : ¬ p ∣ Nat.card R₀ := by
    rw [hn]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hcop : ¬ p ∣ Nat.card (O ⊔ R₀ : Subgroup G) :=
    not_dvd_card_sup_of_le_normalizer hp hR₀N hOp hR₀p
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := fun g => by
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
    exact ⟨0, by simp [hg]⟩
  have hbotN : E ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    have : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top (⊥ : Subgroup G)
    intro x _
    rw [this]
    exact Subgroup.mem_top x
  obtain ⟨Q, -, hQK, hQ2, hQidx, hEQN⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.exists_invariant_sylow_containing_of_pGroup
      hp Nat.prime_two (isPGroup_of_isElemAbelian hE) hEN hcop bot_le hbot2 hbotN
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    rw [hQbot, Subgroup.relIndex_bot_left] at hQidx
    have hn0 : n ≠ 0 := by
      intro h0
      apply hr₀ne
      have h1 : Nat.card R₀ = 1 := by rw [hn, h0, pow_zero]
      have := Subgroup.eq_bot_of_card_eq R₀ h1
      rw [this] at hr₀mem
      exact (Subgroup.mem_bot).1 hr₀mem
    have h2 : 2 ∣ Nat.card R₀ := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact hQidx ((h2.trans (Subgroup.card_dvd_of_le le_sup_right)))
  have hfin := card_le_pow_glaTwoLocalRank hp hE hQne hQ2 hEQN
  rw [hB.2.1]
  exact hfin

private theorem stepC_decomp {Q₀ R B : Subgroup G}
    (hRBN : R ⊔ B ≤ Subgroup.normalizer (Q₀ : Set G))
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ Q₀ ⊔ (R ⊔ B)) :
    ∃ q ∈ Q₀, ∃ r ∈ R, ∃ b ∈ B, x = q * r * b := by
  have hx' : x ∈ (↑(Q₀ ⊔ (R ⊔ B)) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q₀ (R ⊔ B) hRBN,
    Subgroup.coe_mul_of_right_le_normalizer_left R B hBR] at hx'
  obtain ⟨q, hq, w, hw, rfl⟩ := hx'
  obtain ⟨r, hr, b, hb, rfl⟩ := hw
  exact ⟨q, hq, r, hr, b, hb, (mul_assoc _ _ _).symm⟩

private theorem stepC_isPGroup_subgroupOf {q : ℕ} {H K : Subgroup G} (hH : IsPGroup q H) :
    IsPGroup q (H.subgroupOf K) := by
  intro g
  obtain ⟨n, hn⟩ := hH ⟨(g : G), Subgroup.mem_subgroupOf.1 g.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

private theorem stepC_isElemAbelian_subgroupOf {p : ℕ} {H K : Subgroup G}
    (hH : IsElemAbelian p H) : IsElemAbelian p (H.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
  · have := hH.1.1.comm ⟨(a : G), Subgroup.mem_subgroupOf.1 a.2⟩
      ⟨(b : G), Subgroup.mem_subgroupOf.1 b.2⟩
    simpa using congrArg Subtype.val this
  · have := hH.2 (x : G) (Subgroup.mem_subgroupOf.1 hx)
    apply Subtype.ext
    simpa using this

end Bound

variable {G : Type} [Group G] [Finite G]

theorem commutator_oPPrimeP_le_of_exists {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B R X : Subgroup G} (hB : GLAIsBmax p B) (hBX : B ≤ X) (hR2 : IsPGroup 2 R) (hRX : R ≤ X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p X)))
    (hR₀ : ∃ r ∈ R, r ≠ 1 ∧ ∀ q ∈ oPPrimeP p X, ⁅q, r⁆ ∈ GLAPPrimeCoreOf p X) :
    (⁅oPPrimeP p X, R⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Q₀ := oPPrimeP p X with hQ₀
  set O := GLAPPrimeCoreOf p X with hO
  set X₁ : Subgroup G := Q₀ ⊔ (R ⊔ B) with hX₁
  have hQX : Q₀ ≤ X := stepC_oPPrimeP_le p X
  have hRBX : R ⊔ B ≤ X := sup_le hRX hBX
  have hX₁X : X₁ ≤ X := sup_le hQX hRBX
  have hXN : X ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hXQN : X ≤ Subgroup.normalizer (Q₀ : Set G) := stepC_le_normalizer_oPPrimeP p X
  have hRBN : R ⊔ B ≤ Subgroup.normalizer (Q₀ : Set G) := sup_le (hRX.trans hXQN) (hBX.trans hXQN)
  have hOX₁ : O ≤ X₁ := (stepC_glaPPrimeCoreOf_le_oPPrimeP p X).trans le_sup_left
  have hQX₁ : Q₀ ≤ X₁ := le_sup_left
  have hRX₁ : R ≤ X₁ := (le_sup_left : R ≤ R ⊔ B).trans le_sup_right
  have hBX₁ : B ≤ X₁ := (le_sup_right : B ≤ R ⊔ B).trans le_sup_right
  have hX₁N : X₁ ≤ Subgroup.normalizer (O : Set G) := hX₁X.trans hXN
  have hX₁Q : X₁ ≤ Subgroup.normalizer (Q₀ : Set G) := hX₁X.trans hXQN
  haveI hN'n : (O.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX₁).2 hX₁N
  haveI hQ'n : (Q₀.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX₁).2 hX₁Q
  have hNQ' : O.subgroupOf X₁ ≤ Q₀.subgroupOf X₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (stepC_glaPPrimeCoreOf_le_oPPrimeP p X (Subgroup.mem_subgroupOf.1 hx))
  have hNp' : ¬ p ∣ Nat.card (O.subgroupOf X₁) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX₁).toEquiv]
    exact not_dvd_card_glaPPrimeCoreOf hp X
  have hQp' : ∀ x ∈ Q₀.subgroupOf X₁, ∃ n : ℕ, x ^ (p ^ n) ∈ O.subgroupOf X₁ := by
    intro x hx
    obtain ⟨n, hn⟩ := stepC_oPPrimeP_pow_mem p X (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨n, Subgroup.mem_subgroupOf.2 (by simpa using hn)⟩
  have hR' : IsPGroup 2 (R.subgroupOf X₁) := stepC_isPGroup_subgroupOf hR2
  have hB' : IsElemAbelian p (B.subgroupOf X₁) := stepC_isElemAbelian_subgroupOf hB.1
  have hBR' : B.subgroupOf X₁ ≤ Subgroup.normalizer ((R.subgroupOf X₁ : Subgroup X₁) : Set X₁) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hBR (Subgroup.mem_subgroupOf.1 hb)) (h : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hdec' : ∀ x : X₁, ∃ q ∈ Q₀.subgroupOf X₁, ∃ r ∈ R.subgroupOf X₁,
      ∃ b ∈ B.subgroupOf X₁, x = q * r * b := by
    intro x
    obtain ⟨q, hq, r, hr, b, hb, hxq⟩ := stepC_decomp hRBN hBR x.2
    refine ⟨⟨q, hQX₁ hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨r, hRX₁ hr⟩,
      Subgroup.mem_subgroupOf.2 hr, ⟨b, hBX₁ hb⟩, Subgroup.mem_subgroupOf.2 hb, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hxq
  have hbound' : ∀ E : Subgroup X₁, IsElemAbelian p E → E ≤ Q₀.subgroupOf X₁ ⊔ B.subgroupOf X₁ →
      Nat.card E ≤ Nat.card (B.subgroupOf X₁) := by
    intro E hE hEQB
    have hE₀el : IsElemAbelian p (E.map X₁.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    have hsub : (Q₀.subgroupOf X₁ ⊔ B.subgroupOf X₁).map X₁.subtype ≤ Q₀ ⊔ B := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    have hE₀le : E.map X₁.subtype ≤ Q₀ ⊔ B := (Subgroup.map_mono hEQB).trans hsub
    have hcard₀ : Nat.card (E.map X₁.subtype) ≤ Nat.card B :=
      stepC_card_le hp hp2 hB hBX hR2 hRX hBR hR₀ hE₀el hE₀le
    have hcardE : Nat.card (E.map X₁.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective X₁.subtype_injective
    have hcardB : Nat.card (B.subgroupOf X₁) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX₁).toEquiv
    rw [hcardB, ← hcardE]
    exact hcard₀
  have hconc : (⁅Q₀.subgroupOf X₁, R.subgroupOf X₁⁆ : Subgroup X₁) ≤ O.subgroupOf X₁ :=
    stepC_abstract hp hp2 hNQ' hNp' hQp' hR' hB' hBR' hdec' hbound'
  rw [Subgroup.commutator_le]
  intro q hq r hr
  have hq' : (⟨q, hQX₁ hq⟩ : X₁) ∈ Q₀.subgroupOf X₁ := Subgroup.mem_subgroupOf.2 hq
  have hr' : (⟨r, hRX₁ hr⟩ : X₁) ∈ R.subgroupOf X₁ := Subgroup.mem_subgroupOf.2 hr
  have hc := hconc (Subgroup.commutator_mem_commutator hq' hr')
  rw [Subgroup.mem_subgroupOf] at hc
  simpa [commutatorElement_def] using hc

end CFSG.LocalAnalysis.GLTheoremA.P55
