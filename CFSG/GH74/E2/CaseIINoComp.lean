module

public import CFSG.GH74.E2.Cen
public import CFSG.GH74.E2.FrattiniRank2

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

@[expose] def Cl2Statement : Prop :=
  ∀ (X B : Type) [Group X] [Finite X] [Group B] [Finite B] (φ : B →* MulAut X),
    IsPGroup 2 X → Group.rank X = 4 → (∀ P : Subgroup X, Group.rank ↥P ≤ 4) →
    Function.Injective φ → (∀ a b : B, a * b = b * a) → (∀ a : B, a ^ 3 = 1) →
    Nat.card B = 9 → (∀ x : X, (∀ b : B, (φ b x) * x⁻¹ ∈ frattini X) → x ∈ frattini X) →
    ∀ x y z : X, ⁅⁅x, y⁆, z⁆ = 1

section Aux

variable {G : Type*} [Group G]

theorem eq_one_of_pgroup_of_pow {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hxn
  have hcop : Nat.Coprime (2 ^ k) n :=
    Nat.Coprime.pow_left k (Nat.coprime_comm.1 hn.coprime_two_right)
  have : orderOf x = 1 := (Nat.Coprime.coprime_dvd_left h2 hcop).eq_one_of_dvd h3
  exact orderOf_eq_one_iff.1 this

theorem eq_zpow_mul_of_mem {A B : Subgroup G} {a : G}
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcard : Nat.card A = 27) (hB : B ≤ A)
    (hBcard : Nat.card B = 9) (ha : a ∈ A) (hnaB : a ∉ B) :
    ∀ x ∈ A, ∃ (i : ℤ) (b : G), b ∈ B ∧ x = a ^ i * b := by
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩
  let : CommGroup A := IsMulCommutative.instCommGroup
  let N : Subgroup A := B.subgroupOf A
  have hNnormal : N.Normal := Subgroup.normal_of_isMulCommutative N
  have hcardQ : Nat.card (A ⧸ N) = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : Nat.card N = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
    rw [h2, hAcard, hBcard] at h1
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : (QuotientGroup.mk ⟨a, ha⟩ : A ⧸ N) ≠ 1 := by
    intro h
    have h1 := (QuotientGroup.eq_one_iff (N := N) (⟨a, ha⟩ : A)).1 h
    exact hnaB (by simpa [N, Subgroup.mem_subgroupOf] using h1)
  have htop := zpowers_eq_top_of_prime_card hcardQ hne
  intro x hx
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : A ⧸ N) ∈ Subgroup.zpowers
      (QuotientGroup.mk ⟨a, ha⟩ : A ⧸ N) := by
    rw [htop]; trivial
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨i, (a ^ i)⁻¹ * x, ?_, by group⟩
  have h2 : (QuotientGroup.mk ((⟨a, ha⟩ : A) ^ i) : A ⧸ N) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [QuotientGroup.mk_zpow]; exact hi
  have h3 := QuotientGroup.eq.1 h2
  simpa [N, Subgroup.mem_subgroupOf] using h3

theorem rank_le_four_of_subgroup {G : Type*} [Group G] [Finite G] (hG : Gen4 G) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (P : Subgroup Q) : Group.rank ↥P ≤ 4 := by
  have h1 : IsPGroup 2 ↥(P.map Q.subtype) := (hQ.to_subgroup P).map Q.subtype
  have h2 := Gen4.rank_le_four hG h1
  rwa [← Group.rank_congr (P.equivMapOfInjective Q.subtype Q.subtype_injective)] at h2

theorem commutator_le_center_of_class_two {X : Type*} [Group X]
    (h : ∀ x y z : X, ⁅⁅x, y⁆, z⁆ = 1) : commutator X ≤ center X := by
  rw [commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨x, -, y, -, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro z
  exact ((commutatorElement_eq_one_iff_mul_comm).1 (h x y z)).symm

theorem pCore_conj_mem {D : Subgroup G} {x : G} (hx : x ∈ normalizer (D : Set G)) {ω : G}
    (hω : ω ∈ (CFSG.pCore 2 ↥D).map D.subtype) :
    x * ω * x⁻¹ ∈ (CFSG.pCore 2 ↥D).map D.subtype := by
  obtain ⟨d, hd, rfl⟩ := hω
  let φ : MulAut D := D.normalizerMonoidHom ⟨x, hx⟩
  have hφ := Subgroup.characteristic_iff_map_eq.1
    (inferInstance : (CFSG.pCore 2 ↥D).Characteristic) φ
  have : φ d ∈ (CFSG.pCore 2 ↥D) := by
    rw [← hφ]
    exact ⟨d, hd, rfl⟩
  exact ⟨φ d, this, rfl⟩

theorem sq_eq_one_of_orderOf {x : G} (hx : orderOf x = 2) : x ^ 2 = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx] at this

theorem cube_eq_one_of_orderOf {x : G} (hx : orderOf x = 3) : x ^ 3 = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx] at this

end Aux

section Main

variable {G : Type} [Group G] [Finite G]

theorem Qt_not_comm_t' (hH : Hyp G) {t t' a : G} {A B : Subgroup G} (hc : CaseII t t' a A B)
    (hCQ : ∀ c ∈ Cen t, (∀ q ∈ Qt t, c * q = q * c) → c ∈ Qt t) :
    ¬ ∀ q ∈ Qt t, q * t' = t' * q := by
  intro hcomm
  have ht2 : t ^ 2 = 1 := sq_eq_one_of_orderOf hc.order_t
  have ht'2 : t' ^ 2 = 1 := sq_eq_one_of_orderOf hc.order_t'
  have htt' : t * t' = t' * t := hc.comm
  set D : Subgroup G := Cen t ⊓ Cen t' with hD
  set Ω : Subgroup G := (CFSG.pCore 2 ↥D).map D.subtype with hΩ
  have hΩ2 : IsPGroup 2 Ω := (CFSG.pCore_isPGroup (p := 2) (G := ↥D)).map D.subtype
  have hQΩ : Qt t ≤ Ω := by
    intro q hq
    have hqD : q ∈ D := ⟨Qt_le_Cen t hq, mem_Cen'.2 (hcomm q hq)⟩
    refine ⟨⟨q, hqD⟩, ?_, rfl⟩
    have hKn : ((Qt t).subgroupOf D).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact Qt_conj_mem t g.2.1 hn⟩
    have hKp : IsPGroup 2 ↥((Qt t).subgroupOf D) :=
      (Qt_isPGroup t).comap_of_injective D.subtype D.subtype_injective
    have : (Qt t).subgroupOf D ≤ CFSG.pCore 2 ↥D := le_sSup ⟨hKn, hKp⟩
    exact this (by rw [Subgroup.mem_subgroupOf]; exact hq)
  have hat : a * t * a⁻¹ = t' := hc.conj_t
  have hat' : a * t' * a⁻¹ = t * t' := hc.conj_t'
  have hb1 : a⁻¹ * t' * a = t := by
    calc a⁻¹ * t' * a = a⁻¹ * (a * t * a⁻¹) * a := by rw [hat]
      _ = t := by group
  have hb2 : a⁻¹ * (t * t') * a = t' := by
    calc a⁻¹ * (t * t') * a = a⁻¹ * (a * t' * a⁻¹) * a := by rw [hat']
      _ = t' := by group
  have hb3 : a * (t * t') * a⁻¹ = t := by
    calc a * (t * t') * a⁻¹ = (a * t * a⁻¹) * (a * t' * a⁻¹) := by group
      _ = t' * (t * t') := by rw [hat, hat']
      _ = t := by
        calc t' * (t * t') = t * (t' * t') := by
              rw [← mul_assoc, ← htt', mul_assoc]
          _ = t := by rw [← pow_two, ht'2, mul_one]
  have hb4 : a⁻¹ * t * a = t * t' := by
    have h4 : t = (t * t') * t' := by
      calc t = t * (t' * t') := by rw [← pow_two, ht'2, mul_one]
        _ = (t * t') * t' := by rw [mul_assoc]
    calc a⁻¹ * t * a = a⁻¹ * ((t * t') * t') * a := by rw [← h4]
      _ = (a⁻¹ * (t * t') * a) * (a⁻¹ * t' * a) := by group
      _ = t' * t := by rw [hb2, hb1]
      _ = t * t' := htt'.symm
  have hconjD : ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
    intro d hd
    have hdt : t * d = d * t := mem_Cen.1 hd.1
    have hdt' : t' * d = d * t' := mem_Cen.1 hd.2
    refine ⟨mem_Cen.2 ?_, mem_Cen.2 ?_⟩
    ·
      have h1 : t = a * (t * t') * a⁻¹ := hb3.symm
      calc t * (a * d * a⁻¹) = (a * (t * t') * a⁻¹) * (a * d * a⁻¹) := by rw [← h1]
        _ = a * (t * (t' * d)) * a⁻¹ := by group
        _ = a * (t * (d * t')) * a⁻¹ := by rw [hdt']
        _ = a * ((t * d) * t') * a⁻¹ := by group
        _ = a * ((d * t) * t') * a⁻¹ := by rw [hdt]
        _ = a * (d * (t * t')) * a⁻¹ := by group
        _ = (a * d * a⁻¹) * (a * (t * t') * a⁻¹) := by group
        _ = (a * d * a⁻¹) * t := by rw [hb3]
    · have h1 : t' = a * t * a⁻¹ := hat.symm
      calc t' * (a * d * a⁻¹) = (a * t * a⁻¹) * (a * d * a⁻¹) := by rw [← h1]
        _ = a * (t * d) * a⁻¹ := by group
        _ = a * (d * t) * a⁻¹ := by rw [hdt]
        _ = (a * d * a⁻¹) * (a * t * a⁻¹) := by group
        _ = (a * d * a⁻¹) * t' := by rw [hat]
  have hconjD' : ∀ d ∈ D, a⁻¹ * d * a ∈ D := by
    intro d hd
    have hdt : t * d = d * t := mem_Cen.1 hd.1
    have hdt' : t' * d = d * t' := mem_Cen.1 hd.2
    refine ⟨mem_Cen.2 ?_, mem_Cen.2 ?_⟩
    · have h1 : t = a⁻¹ * t' * a := hb1.symm
      calc t * (a⁻¹ * d * a) = (a⁻¹ * t' * a) * (a⁻¹ * d * a) := by rw [← h1]
        _ = a⁻¹ * (t' * d) * a := by group
        _ = a⁻¹ * (d * t') * a := by rw [hdt']
        _ = (a⁻¹ * d * a) * (a⁻¹ * t' * a) := by group
        _ = (a⁻¹ * d * a) * t := by rw [hb1]
    · have h1 : t' = a⁻¹ * (t * t') * a := hb2.symm
      calc t' * (a⁻¹ * d * a) = (a⁻¹ * (t * t') * a) * (a⁻¹ * d * a) := by rw [← h1]
        _ = a⁻¹ * (t * (t' * d)) * a := by group
        _ = a⁻¹ * (t * (d * t')) * a := by rw [hdt']
        _ = a⁻¹ * ((t * d) * t') * a := by group
        _ = a⁻¹ * ((d * t) * t') * a := by rw [hdt]
        _ = a⁻¹ * (d * (t * t')) * a := by group
        _ = (a⁻¹ * d * a) * (a⁻¹ * (t * t') * a) := by group
        _ = (a⁻¹ * d * a) * t' := by rw [hb2]
  have haN : a ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff]
    intro d
    exact ⟨fun hd => hconjD d hd, fun hd => by
      have := hconjD' _ hd
      simpa [mul_assoc] using this⟩
  have hBD : B ≤ D := fun b hb =>
    ⟨mem_Cen'.2 (hc.centralizes_t b hb), mem_Cen'.2 (hc.centralizes_t' b hb)⟩
  have hAN : ∀ x ∈ A, x ∈ normalizer (D : Set G) := by
    by_cases haB : a ∈ B
    ·
      exfalso
      have := hc.centralizes_t a haB
      have h2 : a * t * a⁻¹ = t := by rw [this]; group
      rw [hat] at h2
      exact hc.ne h2.symm
    · intro x hx
      obtain ⟨i, b, hb, rfl⟩ := eq_zpow_mul_of_mem hc.elemAb.1 hc.card_A hc.B_le hc.card_B hc.a_mem haB x hx
      exact mul_mem (Subgroup.zpow_mem _ haN i) (le_normalizer (hBD hb))
  have hAnormΩ : ∀ x ∈ A, ∀ ω ∈ Ω, x * ω * x⁻¹ ∈ Ω := fun x hx ω hω => pCore_conj_mem (hAN x hx) hω
  have hAnorm := le_normalizer_of_normalizes hAnormΩ
  have hfaith : ∀ x ∈ A, (∀ ω ∈ Ω, x * ω * x⁻¹ = ω) → x = 1 := by
    intro x hx h
    have htΩ : t ∈ Ω := hQΩ (t_mem_Qt hc.order_t)
    have hxt : x ∈ Cen t := by
      have := h t htΩ
      rw [mem_Cen']
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [this]
    have hxQ : x ∈ Qt t := hCQ x hxt (fun q hq => by
      have := h q (hQΩ hq)
      calc x * q = (x * q * x⁻¹) * x := by group
        _ = q * x := by rw [this])
    exact eq_one_of_pgroup_of_pow (Qt_isPGroup t) hxQ (n := 3) (by decide) (hc.elemAb.2 x hx)
  have hF1 := ord_mul_card_le_rank (A := A) (X := Ω) hΩ2 hAnorm hfaith (p := 3) (r := 3)
    Nat.prime_three (by norm_num) hc.elemAb.1 hc.elemAb.2 (by rw [hc.card_A]; norm_num)
  rw [orderOf_two_zmod_three] at hF1
  have hr4 := Gen4.rank_le_four hH.gen4 hΩ2
  omega

theorem false_of_caseII_noComponent (hCl2 : Cl2Statement) (hH : Hyp G) {t t' a : G}
    {A B : Subgroup G} (hc : CaseII t t' a A B) (hlayer : CFSG.layer ↥(Cen t) = ⊥) : False := by
  have ht := hc.order_t
  have hcore := hH.pPrimeCore_cen_bot ht
  have hCQ : ∀ c ∈ Cen t, (∀ q ∈ Qt t, c * q = q * c) → c ∈ Qt t :=
    fun c hc' h => centralizer_Qt_le hcore hlayer hc' h
  have hQ2 : IsPGroup 2 (Qt t) := Qt_isPGroup t
  have hBC : ∀ b ∈ B, b ∈ Cen t := fun b hb => mem_Cen'.2 (hc.centralizes_t b hb)
  have hBnorm : ∀ b ∈ B, ∀ q ∈ Qt t, b * q * b⁻¹ ∈ Qt t :=
    fun b hb q hq => Qt_conj_mem t (hBC b hb) hq
  have hBab : ElemAb 3 B :=
    ⟨fun a ha b hb => hc.elemAb.1 a (hc.B_le ha) b (hc.B_le hb),
      fun a ha => hc.elemAb.2 a (hc.B_le ha)⟩
  have hfaith : ∀ b ∈ B, (∀ q ∈ Qt t, b * q * b⁻¹ = q) → b = 1 := by
    intro b hb h
    have hbQ : b ∈ Qt t := hCQ b (hBC b hb) (fun q hq => by
      have := h q hq
      calc b * q = (b * q * b⁻¹) * b := by group
        _ = q * b := by rw [this])
    exact eq_one_of_pgroup_of_pow hQ2 hbQ (n := 3) (by decide) (hBab.2 b hb)
  have hnormB : B ≤ normalizer (Qt t : Set G) := le_normalizer_of_normalizes hBnorm
  let φ : B →* MulAut (Qt t) := conjAction B (Qt t) hnormB
  have hφapp : ∀ (b : B) (q : Qt t), ((φ b q : Qt t) : G) = (b : G) * q * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    apply Subtype.ext
    rw [Subgroup.coe_one]
    apply hfaith b b.2
    intro q hq
    have h2 := congrArg (fun f : MulAut (Qt t) => ((f ⟨q, hq⟩ : Qt t) : G)) hb
    have h3 : ((φ b ⟨q, hq⟩ : Qt t) : G) = (b : G) * q * (b : G)⁻¹ := rfl
    simpa [h3] using h2
  have hX4 : Group.rank ↥(Qt t) ≤ 4 := Gen4.rank_le_four hH.gen4 hQ2
  have hcommB : ∀ a b : B, a * b = b * a := fun a b => Subtype.ext (hBab.1 a a.2 b b.2)
  have hpowB : ∀ a : B, a ^ 3 = 1 := fun a => Subtype.ext (hBab.2 a a.2)
  obtain ⟨hrank4, hfix0⟩ := threeSquared_faithful hQ2 hX4 φ hφ hcommB hpowB hc.card_B
  have hcl := hCl2 ↥(Qt t) ↥B φ hQ2 hrank4 (rank_le_four_of_subgroup hH.gen4 hQ2) hφ hcommB hpowB
    hc.card_B hfix0
  have ht'2 : t' ^ 2 = 1 := sq_eq_one_of_orderOf hc.order_t'
  have htC' : t' ∈ Cen t := mem_Cen.2 hc.comm
  have ht'Q : t' ∈ Qt t :=
    mem_of_normalizing_involution hH.gen4 hQ2 hBnorm hBab hc.card_B hfaith ht'2
      (fun q hq => Qt_conj_mem t htC' hq) (fun b hb => hc.centralizes_t' b hb)
  have hfixt' : ∀ b : B, φ b ⟨t', ht'Q⟩ = ⟨t', ht'Q⟩ := by
    intro b
    apply Subtype.ext
    rw [hφapp]
    have := hc.centralizes_t' b b.2
    calc (b : G) * t' * (b : G)⁻¹ = (t' * (b : G)) * (b : G)⁻¹ := by rw [this]
      _ = t' := by group
  have hcomm := fixed_mem_commutator hQ2 φ hc.card_B hfix0 hfixt'
  have hcen := commutator_le_center_of_class_two hcl hcomm
  apply Qt_not_comm_t' hH hc hCQ
  intro q hq
  have := Subgroup.mem_center_iff.1 hcen ⟨q, hq⟩
  exact congrArg Subtype.val this

@[expose] def NoCaseIIComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t t' a : G) (A B : Subgroup G),
    CaseII t t' a A B → CFSG.layer ↥(Cen t) ≠ ⊥ → False

theorem noCaseII_of (hCl2 : Cl2Statement) (h : NoCaseIIComp) : NoCaseII := by
  intro G _ _ hH t t' a A B hc
  by_cases hl : CFSG.layer ↥(Cen t) = ⊥
  · exact false_of_caseII_noComponent hCl2 hH hc hl
  · exact h G hH t t' a A B hc hl

end Main

end CFSG.GH74.E2
