module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedSwap

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x k : Y} {K₁ K₂ : Subgroup Y}

structure QData (P K₁ K₂ Q : Subgroup Y) (a b : Y) : Prop where
  Q_le : Q ≤ P
  P_norm : P ≤ normalizer (Q : Set Y)
  Q_ab : ∀ u ∈ Q, ∀ v ∈ Q, u * v = v * u
  Q_exp : ∀ u ∈ Q, u ^ 9 = 1
  Q_max : ∀ R : Subgroup Y, Q < R → R ≤ P → R = P
  Z_iff : ∀ w : Y, w ∈ L28Z P ↔ w ∈ Q ∧ w ^ 3 = 1
  Q_card : Nat.card Q = 3 ^ 4
  a_mem : a ∈ P ⊓ K₁
  b_mem : b ∈ P ⊓ K₂
  a_ord : orderOf a = 9
  b_ord : orderOf b = 9
  Q_eq : Q = zpowers a ⊔ zpowers b
  S₁_eq : P ⊓ K₁ = zpowers a
  S₂_eq : P ⊓ K₂ = zpowers b

theorem abelian_of_card_nine {S : Subgroup Y} (h : Nat.card S = 3 ^ 2) :
    ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq h
  intro u hu v hv
  exact setLike_mul_comm (s := S) hu hv

namespace TwoData

variable (htw : TwoData P K₁ K₂)

include htw

theorem sylow_inf : IsSylowOf 3 (P ⊓ K₁) K₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPD : P ≤ normalizer (K₁ : Set Y) := htw.hs.normalizes htw.c₁
  exact (htw.hs.sylow.of_le hPD le_top).inf_of_le_normalizer Subgroup.le_normalizer le_rfl

theorem card_sup : Nat.card (P ⊓ K₁ ⊔ P ⊓ K₂ : Subgroup Y) =
    Nat.card (P ⊓ K₁ : Subgroup Y) * Nat.card (P ⊓ K₂ : Subgroup Y) := by
  have hcomm : ∀ a ∈ P ⊓ K₁, ∀ b ∈ P ⊓ K₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (htw.le_cent ha.2) b hb.2).symm
  have h := e9_card_sup_mul_card_inf (GL83P3L28Aux.le_normalizer_of_comm hcomm)
  have hinf : P ⊓ K₁ ⊓ (P ⊓ K₂) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ K₁ ⊓ K₂ := ⟨hy.1.2, hy.2.2⟩
    rwa [htw.inf_bot] at this
  rw [hinf, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_pow (hz : Nat.card (L28Z P) = 3 ^ 2) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card (P ⊓ K₁ : Subgroup Y) = 3 ^ n := by
  obtain ⟨n, hn⟩ := (htw.hs.sylow.isPGroup.to_le (inf_le_left : P ⊓ K₁ ≤ P)).exists_card_eq
  refine ⟨n, ?_, hn⟩
  by_contra h0
  have hn0 : n = 0 := by omega
  obtain ⟨z₁, -, hz₁, -, hz₁1, -, -, -, -⟩ := htw.exists_Z hz
  have h1 : Nat.card (P ⊓ K₁ : Subgroup Y) = 1 := by rw [hn, hn0]; rfl
  have hbot : (P ⊓ K₁ : Subgroup Y) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  rw [hbot, mem_bot] at hz₁
  exact hz₁1 hz₁

theorem layer_eq : CFSG.layer Y = K₁ ⊔ K₂ := by
  refine le_antisymm (sSup_le fun L hL => ?_) (sup_le
    (le_sSup ((CFSG.isComponent_iff_open K₁).mpr htw.c₁))
    (le_sSup ((CFSG.isComponent_iff_open K₂).mpr htw.c₂)))
  rcases htw.all L ((CFSG.isComponent_iff_open L).mp hL) with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem cent_inf_bot : centralizer (K₁ : Set Y) ⊓ centralizer (K₂ : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hle : K₁ ⊔ K₂ ≤ centralizer ({w} : Set Y) := sup_le
    (fun u hu => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hw.1 u hu))
    (fun u hu => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hw.2 u hu))
  have hw' : w ∈ centralizer (CFSG.layer Y : Set Y) := by
    rw [mem_centralizer_iff]
    intro u hu
    rw [htw.layer_eq] at hu
    exact mem_centralizer_singleton_iff.mp (hle hu)
  rw [htw.hs.centralizer_layer] at hw'
  exact hw'

theorem le_sup_of_cent (h1 : ∀ p ∈ P, p ∈ K₁ ⊔ centralizer (K₁ : Set Y))
    (h2 : ∀ p ∈ P, p ∈ K₂ ⊔ centralizer (K₂ : Set Y)) : P ≤ K₁ ⊔ K₂ := by
  have hdec : ∀ {A : Subgroup Y}, (∀ p ∈ P, p ∈ A ⊔ centralizer (A : Set Y)) → ∀ p ∈ P,
      ∃ a ∈ A, ∃ c ∈ centralizer (A : Set Y), a * c = p := by
    intro A h p hp
    exact mem_sup_prod (GL83P3L28Aux.le_normalizer_of_comm fun a ha c hc' =>
      (mem_centralizer_iff.mp hc' a ha)) (h p hp)
  intro p hp
  obtain ⟨a, ha, c, hc, hac⟩ := hdec h1 p hp
  obtain ⟨b, hb, c', hc', hbc⟩ := hdec h2 p hp
  have hab : a * b = b * a := (mem_centralizer_iff.mp (htw.le_cent ha) b hb).symm
  have hw : (a * b)⁻¹ * p ∈ centralizer (K₁ : Set Y) ⊓ centralizer (K₂ : Set Y) := by
    refine ⟨?_, ?_⟩
    · have e : (a * b)⁻¹ * p = b⁻¹ * c := by rw [← hac]; group
      rw [e]
      exact (centralizer (K₁ : Set Y)).mul_mem
        ((centralizer (K₁ : Set Y)).inv_mem (htw.symm.le_cent hb)) hc
    · have e : (a * b)⁻¹ * p = a⁻¹ * c' := by
        have : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
          rw [hab, mul_inv_rev]
        rw [this, ← hbc]
        group
      rw [e]
      exact (centralizer (K₂ : Set Y)).mul_mem
        ((centralizer (K₂ : Set Y)).inv_mem (htw.le_cent ha)) hc'
  rw [htw.cent_inf_bot, mem_bot] at hw
  have hpab : p = a * b := (inv_mul_eq_one.mp hw).symm
  rw [hpab]
  exact Subgroup.mul_mem_sup ha hb

theorem le_sup_of_card_three (hd : ClosedData P x k) (hC : KFactOutThreeCoprime)
    (h1 : Nat.card (P ⊓ K₁ : Subgroup Y) = 3) (h2 : Nat.card (P ⊓ K₂ : Subgroup Y) = 3) :
    P ≤ K₁ ⊔ K₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : ∀ {A B : Subgroup Y}, TwoData P A B → Nat.card (P ⊓ A : Subgroup Y) = 3 →
      ∀ p ∈ P, p ∈ A ⊔ centralizer (A : Set Y) := by
    intro A B hAB hc p hp
    have hf : (Nat.card A).factorization 3 = 1 := by
      have := hAB.sylow_inf.card_eq
      rw [hc] at this
      have h3 : 3 ^ 1 = 3 ^ (Nat.card A).factorization 3 := by rw [pow_one]; exact this
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3).symm
    obtain ⟨n, hn⟩ := hAB.hs.sylow.isPGroup ⟨p, hp⟩
    exact hC Y A (hAB.hs.simple hAB.c₁).1 (hAB.hs.simple hAB.c₁).2
      (hd.catalog.simple_subgroup A (hAB.hs.simple hAB.c₁).1 (hAB.hs.simple hAB.c₁).2) hf p
      (hAB.hs.normalizes hAB.c₁ hp) ⟨n, congrArg Subtype.val hn⟩
  exact htw.le_sup_of_cent (hfac htw h1) (hfac htw.symm h2)

theorem factorization_eq (h : Nat.card (P ⊓ K₁ : Subgroup Y) = 3) :
    (Nat.card K₁).factorization 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := htw.sylow_inf.card_eq
  rw [h] at this
  have h3 : 3 ^ 1 = 3 ^ (Nat.card K₁).factorization 3 := by rw [pow_one]; exact this
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3).symm

theorem card_sup_comp : Nat.card (K₁ ⊔ K₂ : Subgroup Y) = Nat.card K₁ * Nat.card K₂ := by
  have h := e9_card_sup_mul_card_inf (GL83P3L28Aux.le_normalizer_of_comm fun a ha b hb =>
    (mem_centralizer_iff.mp (htw.le_cent ha) b hb).symm)
  rw [htw.inf_bot, Subgroup.card_bot, mul_one] at h
  exact h

end TwoData

theorem eq_Q_of_abelian (hd : ClosedData P x k) {Q B : Subgroup Y} (hQP : Q ≤ P)
    (hQmax : ∀ R : Subgroup Y, Q < R → R ≤ P → R = P) (hPQ : P ≤ normalizer (Q : Set Y))
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQc : Nat.card Q = 3 ^ 4) (hBP : B ≤ P)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBc : Nat.card B = 3 ^ 4) : B = Q := by
  by_contra hne
  have hBQ : ¬ B ≤ Q := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hQc, hBc]))
  have hlt : Q < B ⊔ Q := lt_of_le_of_ne le_sup_right (fun h => hBQ (h ▸ le_sup_left))
  have hsup : B ⊔ Q = P := hQmax _ hlt (sup_le hBP hQP)
  have hcard := e9_card_sup_mul_card_inf (A := B) (N := Q) (fun b hb => hPQ (hBP hb))
  rw [hsup, hd.shape.1, hBc, hQc] at hcard
  have h27 : Nat.card (B ⊓ Q : Subgroup Y) = 3 ^ 3 := by
    have : 3 ^ 5 * Nat.card (B ⊓ Q : Subgroup Y) = 3 ^ 5 * 3 ^ 3 := by rw [hcard]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hle : (B ⊓ Q : Subgroup Y) ≤ L28Z P := by
    intro a ha
    refine GL83P3L28Aux.mem_L28Z_iff.mpr ⟨hBP ha.1, fun p hp => ?_⟩
    have hP : B ⊔ Q ≤ centralizer ({a} : Set Y) := sup_le
      (fun b hb => mem_centralizer_singleton_iff.mpr (hBab b hb a ha.1))
      (fun q hq => mem_centralizer_singleton_iff.mpr (hQab q hq a ha.2))
    rw [hsup] at hP
    exact mem_centralizer_singleton_iff.mp (hP hp)
  have := Subgroup.card_le_of_le hle
  rw [h27, hd.z_card] at this
  norm_num at this

namespace TwoData

variable (htw : TwoData P K₁ K₂)

include htw

theorem exists_QData (hd : ClosedData P x k) (hC : KFactOutThreeCoprime) {t : Y}
    (ht : t ∈ normalizer (P : Set Y)) (hts : K₁.map (MulAut.conj t).toMonoidHom = K₂) :
    ∃ (Q : Subgroup Y) (a b : Y), QData P K₁ K₂ Q a b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQP, hQmax, hPQ, hQab, hQ9, hQc, hZ⟩ := GL83P3L28Aux.l28shape_K hd.shape
  have hPc : Nat.card P = 3 ^ 5 := hd.shape.1
  have hS12 : Nat.card (P ⊓ K₂ : Subgroup Y) = Nat.card (P ⊓ K₁ : Subgroup Y) := by
    have hPt : P.map (MulAut.conj t).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp ht
    have hm : (P ⊓ K₁).map (MulAut.conj t).toMonoidHom = P ⊓ K₂ := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hts, hPt]
    rw [← hm, Subgroup.card_map_of_injective (MulAut.conj t).injective]
  obtain ⟨n, hn1, hn⟩ := htw.card_pow hd.z_card
  have hn2 : Nat.card (P ⊓ K₂ : Subgroup Y) = 3 ^ n := hS12.trans hn
  have hprod := htw.card_sup
  have hle : (P ⊓ K₁ ⊔ P ⊓ K₂ : Subgroup Y) ≤ P := sup_le inf_le_left inf_le_left
  have hcardle := Subgroup.card_le_of_le hle
  rw [hprod, hn, hn2, hPc, ← pow_add] at hcardle
  have hn_le : n ≤ 2 := by
    by_contra h3
    have : 3 ^ 6 ≤ 3 ^ (n + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h35 : 3 ^ 6 ≤ 3 ^ 5 := this.trans hcardle
    norm_num at h35
  have hn_ne1 : n ≠ 1 := by
    intro h1
    have hc1 : Nat.card (P ⊓ K₁ : Subgroup Y) = 3 := by rw [hn, h1]; norm_num
    have hc2 : Nat.card (P ⊓ K₂ : Subgroup Y) = 3 := by rw [hn2, h1]; norm_num
    have hPL := htw.le_sup_of_card_three hd hC hc1 hc2
    have hdvd : 3 ^ 5 ∣ Nat.card K₁ * Nat.card K₂ := by
      rw [← htw.card_sup_comp, ← hPc]
      exact Subgroup.card_dvd_of_le hPL
    have hf1 := htw.factorization_eq hc1
    have hf2 := htw.symm.factorization_eq hc2
    have hne1 : Nat.card K₁ ≠ 0 := Nat.card_pos.ne'
    have hne2 : Nat.card K₂ ≠ 0 := Nat.card_pos.ne'
    have h5 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (Nat.mul_ne_zero hne1 hne2)).mp hdvd
    rw [Nat.factorization_mul hne1 hne2, Finsupp.add_apply, hf1, hf2] at h5
    omega
  have hn2' : n = 2 := by omega
  subst hn2'
  have hS1 : Nat.card (P ⊓ K₁ : Subgroup Y) = 3 ^ 2 := hn
  have hS2 : Nat.card (P ⊓ K₂ : Subgroup Y) = 3 ^ 2 := hn2
  have hnrm : P ⊓ K₁ ≤ normalizer ((P ⊓ K₂ : Subgroup Y) : Set Y) :=
    GL83P3L28Aux.le_normalizer_of_comm fun a ha b hb =>
      (mem_centralizer_iff.mp (htw.le_cent ha.2) b hb.2).symm
  have hBab : ∀ u ∈ P ⊓ K₁ ⊔ P ⊓ K₂, ∀ v ∈ P ⊓ K₁ ⊔ P ⊓ K₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_sup_prod hnrm hu
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := mem_sup_prod hnrm hv
    have c1 : u₁ * v₁ = v₁ * u₁ := abelian_of_card_nine hS1 u₁ hu₁ v₁ hv₁
    have c2 : u₂ * v₂ = v₂ * u₂ := abelian_of_card_nine hS2 u₂ hu₂ v₂ hv₂
    have c3 : u₂ * v₁ = v₁ * u₂ := (mem_centralizer_iff.mp (htw.le_cent hv₁.2) u₂ hu₂.2)
    have c4 : u₁ * v₂ = v₂ * u₁ := (mem_centralizer_iff.mp (htw.le_cent hu₁.2) v₂ hv₂.2).symm
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [c3]
      _ = (u₁ * v₁) * (u₂ * v₂) := by group
      _ = (v₁ * u₁) * (v₂ * u₂) := by rw [c1, c2]
      _ = v₁ * (u₁ * v₂) * u₂ := by group
      _ = v₁ * (v₂ * u₁) * u₂ := by rw [c4]
      _ = v₁ * v₂ * (u₁ * u₂) := by group
  have hBc : Nat.card (P ⊓ K₁ ⊔ P ⊓ K₂ : Subgroup Y) = 3 ^ 4 := by
    rw [hprod, hS1, hS2, ← pow_add]
  have hBQ : P ⊓ K₁ ⊔ P ⊓ K₂ = Q :=
    eq_Q_of_abelian hd hQP hQmax hPQ hQab hQc hle hBab hBc
  obtain ⟨z₁, z₂, hz₁, hz₂, hz₁1, hz₂1, -, -, hV⟩ := htw.exists_Z hd.z_card
  have hz₁Z : z₁ ∈ L28Z P := hV ▸ mem_sup_left (mem_zpowers z₁)
  have hz₂Z : z₂ ∈ L28Z P := hV ▸ mem_sup_right (mem_zpowers z₂)
  have hex : ∀ {A B : Subgroup Y}, TwoData P A B → Nat.card (P ⊓ A : Subgroup Y) = 3 ^ 2 →
      P ⊓ A ≤ Q → (∃ z : Y, z ∈ P ⊓ B ∧ z ≠ 1 ∧ z ∈ L28Z P) →
      ∃ a ∈ P ⊓ A, orderOf a = 9 ∧ P ⊓ A = zpowers a := by
    intro A B hAB hc hAQ hzex
    obtain ⟨z, hzB, hz1, hzZ⟩ := hzex
    have hex' : ∃ a ∈ P ⊓ A, a ^ 3 ≠ 1 := by
      by_contra hall
      push Not at hall
      have hsub : (P ⊓ A : Subgroup Y) ≤ L28Z P := fun a ha => (hZ a).mpr ⟨hAQ ha, hall a ha⟩
      have heq : (P ⊓ A : Subgroup Y) = L28Z P :=
        Subgroup.eq_of_le_of_card_ge hsub (by rw [hd.z_card, hc])
      have hzA' : z ∈ (P ⊓ A : Subgroup Y) := by rw [heq]; exact hzZ
      have : z ∈ A ⊓ B := ⟨hzA'.2, hzB.2⟩
      rw [hAB.inf_bot, mem_bot] at this
      exact hz1 this
    obtain ⟨a, ha, ha3⟩ := hex'
    have ha9 : a ^ 9 = 1 := hQ9 a (hAQ ha)
    have hord : orderOf a = 3 ^ (1 + 1) :=
      orderOf_eq_prime_pow (by simpa using ha3) (by simpa using ha9)
    norm_num at hord
    refine ⟨a, ha, hord, ?_⟩
    symm
    exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr ha)
      (by rw [Nat.card_zpowers, hord, hc]; norm_num)
  have hS1Q : P ⊓ K₁ ≤ Q := by rw [← hBQ]; exact le_sup_left
  have hS2Q : P ⊓ K₂ ≤ Q := by rw [← hBQ]; exact le_sup_right
  obtain ⟨a, ha, hao, haS⟩ := hex htw hS1 hS1Q ⟨z₂, hz₂, hz₂1, hz₂Z⟩
  obtain ⟨b, hb, hbo, hbS⟩ := hex htw.symm hS2 hS2Q ⟨z₁, hz₁, hz₁1, hz₁Z⟩
  refine ⟨Q, a, b, ⟨hQP, hPQ, hQab, hQ9, hQmax, hZ, hQc, ha, hb, hao, hbo, ?_, haS, hbS⟩⟩
  rw [← hBQ, haS, hbS]

end TwoData


end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
