module

public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleBridge
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBFactors

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement

namespace Sec312

section Tools

variable {G : Type*} [Group G]

theorem pc {Z C : Subgroup G} (hZ : ⁅Z, Z⁆ = Z) (hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hCZ : C ≤ centralizer (Z : Set G)) {y : G} (hy : ∀ z ∈ Z, ⁅z, y⁆ ∈ C) :
    y ∈ centralizer (Z : Set G) := by
  have hcomm : ∀ c ∈ C, ∀ z ∈ Z, z * c = c * z := fun c hc z hz =>
    mem_centralizer_iff.1 (hCZ hc) z hz
  have h1 := commutatorElement_mem_of_perfect (K := Z) (F := C) (F₂ := ⊥) hZ hCc
    (fun k hk f hf => by rw [hcomm f hf k hk, mul_inv_cancel_right]; exact hf)
    (fun k hk f hf => by
      rw [hcomm f hf k hk, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _) hy
  refine mem_centralizer_iff.2 fun z hz => ?_
  have := h1 z hz
  rw [mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.1 this

def A (V C P : Subgroup G) (hCV : C ≤ V) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) : Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ r ∈ P, ⁅r, v⁆ ∈ C}
  mul_mem' := by
    rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
    refine ⟨mul_mem haV hbV, fun r hr => ?_⟩
    have e : ⁅r, a * b⁆ = ⁅r, a⁆ * (a * ⁅r, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have hc : a * ⁅r, b⁆ * a⁻¹ = ⁅r, b⁆ := by
      rw [hV a haV _ (hCV (hb r hr)), mul_inv_cancel_right]
    rw [e, hc]
    exact mul_mem (ha r hr) (hb r hr)
  one_mem' := ⟨one_mem V, fun r _ => by simpa using one_mem C⟩
  inv_mem' := by
    rintro a ⟨haV, ha⟩
    refine ⟨inv_mem haV, fun r hr => ?_⟩
    have e : ⁅r, a⁻¹⁆ = a⁻¹ * ⁅r, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅r, a⁆⁻¹ * a = ⁅r, a⁆⁻¹ := by
      rw [hV a⁻¹ (inv_mem haV) _ (hCV (inv_mem (ha r hr))), inv_mul_cancel_right]
    rw [e, hc]
    exact inv_mem (ha r hr)

theorem mem_A {V C P : Subgroup G} {hCV : C ≤ V} {hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a} {v : G} :
    v ∈ A V C P hCV hV ↔ v ∈ V ∧ ∀ r ∈ P, ⁅r, v⁆ ∈ C := Iff.rfl

def Stab (X C : Subgroup G) (hXC : X ≤ centralizer (C : Set G)) (v : G) : Subgroup G where
  carrier := {x | x ∈ X ∧ ⁅x, v⁆ ∈ C}
  mul_mem' := by
    rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
    refine ⟨mul_mem haX hbX, ?_⟩
    have e : ⁅a * b, v⁆ = (a * ⁅b, v⁆ * a⁻¹) * ⁅a, v⁆ := by
      simp only [commutatorElement_def]; group
    have hc : a * ⁅b, v⁆ * a⁻¹ = ⁅b, v⁆ := by
      rw [← mem_centralizer_iff.1 (hXC haX) _ hb, mul_inv_cancel_right]
    rw [e, hc]
    exact mul_mem hb ha
  one_mem' := ⟨one_mem X, by simpa using one_mem C⟩
  inv_mem' := by
    rintro a ⟨haX, ha⟩
    refine ⟨inv_mem haX, ?_⟩
    have e : ⁅a⁻¹, v⁆ = a⁻¹ * ⁅a, v⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅a, v⁆⁻¹ * a = ⁅a, v⁆⁻¹ := by
      have h2 : ⁅a, v⁆⁻¹ * a = a * ⁅a, v⁆⁻¹ := (mem_centralizer_iff.1 (hXC haX) _ (inv_mem ha))
      rw [mul_assoc, h2, inv_mul_cancel_left]
    rw [e, hc]
    exact inv_mem ha

theorem conj_comm {r y : G} (h : r * y = y * r) : y * r * y⁻¹ = r := by
  rw [← h, mul_inv_cancel_right]

theorem conj_of_centralizes {C : Subgroup G} {y c : G} (hy : y ∈ centralizer (C : Set G))
    (hc : c ∈ C) : y * c * y⁻¹ = c := by
  rw [← mem_centralizer_iff.1 hy c hc, mul_inv_cancel_right]

theorem map_conj_le_centralizer {H K : Subgroup G} (t' : G) (hHK : H ≤ centralizer (K : Set G)) :
    H.map (MulAut.conj t').toMonoidHom ≤
      centralizer ((K.map (MulAut.conj t').toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have := mem_centralizer_iff.1 (hHK hh) c hc
  change t' * c * t'⁻¹ * (t' * h * t'⁻¹) = t' * h * t'⁻¹ * (t' * c * t'⁻¹)
  calc t' * c * t'⁻¹ * (t' * h * t'⁻¹) = t' * (c * h) * t'⁻¹ := by group
    _ = t' * (h * c) * t'⁻¹ := by rw [this]
    _ = t' * h * t'⁻¹ * (t' * c * t'⁻¹) := by group

end Tools

section Counting

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] [CharP k 2] {m : ℕ}

theorem perfect_of_equiv {X : Subgroup G} (φ : X ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) : ⁅X, X⁆ = X := by
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k h4
  exact Subgroup.isPerfect_iff.1
    (Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective)

theorem card_inf_centralizer_le {V X : Subgroup G} (φ : X ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (hVsq : ∀ v ∈ V, v * v = 1) (hVcard : Nat.card V ≤ 2 ^ (4 * m))
    (hXV : X ≤ normalizer (V : Set G)) (hnt : ¬ X ≤ centralizer (V : Set G)) :
    Nat.card (V ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2 ^ (2 * m) := by
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self hVsq ha hb
  set C : Subgroup G := V ⊓ centralizer (X : Set G) with hC
  have hCV : C ≤ V := inf_le_left
  have hCc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => hVc a (hCV ha) b (hCV hb)
  have hCX : C ≤ centralizer (X : Set G) := inf_le_right
  have hXC : X ≤ centralizer (C : Set G) := fun x hx => mem_centralizer_iff.2 fun c hc =>
    (mem_centralizer_iff.1 (hCX hc) x hx).symm
  have hex : ∃ x ∈ X, ∃ v ∈ V, x * v * x⁻¹ * v⁻¹ ∉ C := by
    by_contra hne
    push Not at hne
    apply hnt
    have hall : ∀ v ∈ V, v ∈ centralizer (X : Set G) := fun v hv =>
      pc (perfect_of_equiv φ hk hm) hCc hCX (fun z hz => by
        have := hne z hz v hv
        rwa [← commutatorElement_def] at this)
    intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact (mem_centralizer_iff.1 (hall v hv) x hx).symm
  obtain ⟨x, hx, v, hv, hxv⟩ := hex
  have h1 := Common.sl2_card_sq_le_relIndex_of_not_mem φ hk hm hVsq hCV hXV
    (fun y hy => (centralizer_le_normalizer _) (hXC hy)) hx hv hxv
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := V)
  rw [inf_eq_left.2 hCV] at h2
  have h3 : 2 ^ (2 * m) * Nat.card C ≤ 2 ^ (2 * m) * 2 ^ (2 * m) := by
    calc 2 ^ (2 * m) * Nat.card C = Nat.card k ^ 2 * Nat.card C := by
          rw [hk, ← pow_mul, mul_comm m 2]
      _ ≤ C.relIndex V * Nat.card C := Nat.mul_le_mul_right _ h1
      _ = Nat.card V := h2
      _ ≤ 2 ^ (4 * m) := hVcard
      _ = 2 ^ (2 * m) * 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

theorem key_false {V X Y RX RY : Subgroup G} (t' : G) (φX : X ≃* SL(2, k)) (φY : Y ≃* SL(2, k))
    (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hVsq : ∀ v ∈ V, v * v = 1)
    (hVcard : Nat.card V ≤ 2 ^ (4 * m))
    (hXV : X ≤ normalizer (V : Set G)) (hYV : Y ≤ normalizer (V : Set G))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hRX : IsSylowOf 2 RX X) (hRY : IsSylowOf 2 RY Y)
    (hnt : ¬ X ≤ centralizer (V : Set G))
    (hC : 2 ^ (2 * m) ≤ Nat.card (V ⊓ centralizer ((RX ⊔ RY : Subgroup G) : Set G) : Subgroup G))
    (htV : t' ∈ normalizer (V : Set G)) (htX : X.map (MulAut.conj t').toMonoidHom = Y)
    (htY : Y.map (MulAut.conj t').toMonoidHom = X) (htR : RX.map (MulAut.conj t').toMonoidHom = RY)
    (hY : Y ≤ centralizer ((V ⊓ centralizer (X : Set G) : Subgroup G) : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := by omega
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self hVsq ha hb
  set NX : Subgroup G := V ⊓ centralizer (X : Set G) with hNX
  set NY : Subgroup G := V ⊓ centralizer (Y : Set G) with hNY
  have hτX : NX.map (MulAut.conj t').toMonoidHom = NY := by
    rw [hNX, hNY, ← Prelim.inf_centralizer_map_conj htV, htX]
  have hNXY : NX ≤ NY := fun v hv => ⟨hv.1, mem_centralizer_iff.2 fun y hy =>
    (mem_centralizer_iff.1 (hY hy) v hv).symm⟩
  have hNYX : NY ≤ NX := by
    have h1 : X ≤ centralizer ((NY : Subgroup G) : Set G) := by
      have := map_conj_le_centralizer t' hY
      rwa [htY, hτX] at this
    exact fun v hv => ⟨hv.1, mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (h1 hx) v hv).symm⟩
  have hNeq : NX = NY := le_antisymm hNXY hNYX
  have hCV : NX ≤ V := inf_le_left
  have hCc : ∀ a ∈ NX, ∀ b ∈ NX, a * b = b * a := fun a ha b hb => hVc a (hCV ha) b (hCV hb)
  have hCX : NX ≤ centralizer (X : Set G) := inf_le_right
  have hCY : NX ≤ centralizer (Y : Set G) := hNeq ▸ (inf_le_right : NY ≤ centralizer (Y : Set G))
  have hXC : X ≤ centralizer (NX : Set G) := fun x hx => mem_centralizer_iff.2 fun c hc =>
    (mem_centralizer_iff.1 (hCX hc) x hx).symm
  have hYC : Y ≤ centralizer (NX : Set G) := hY
  have hperX : ⁅X, X⁆ = X := perfect_of_equiv φX hk hm
  have hperY : ⁅Y, Y⁆ = Y := perfect_of_equiv φY hk hm
  have hVC : ¬ V ≤ NX := fun h => hnt fun x hx => mem_centralizer_iff.2 fun v hv =>
    ((mem_centralizer_iff.1 (h hv).2) x hx).symm
  set U : Subgroup G := A V NX RX hCV hVc with hU
  have hUV : U ≤ V := fun v hv => hv.1
  have hNU : NX ≤ U := fun c hc => ⟨hCV hc, fun r hr => by
    have : ⁅r, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (hCX hc) r (hRX.le hr))
    rw [this]
    exact one_mem _⟩
  obtain ⟨x, hxV, hxN, hxfix⟩ := Common.exists_mem_forall_conj_mem_of_isPGroup (p := 2) hRX.isPGroup
    (Common.isPGroup_two_of_mul_self hVsq) hCV hVC (hRX.le.trans hXV)
    (fun r hr => (centralizer_le_normalizer _) (hXC (hRX.le hr)))
    (Common.le_normalizer_of_mul_comm hCV hVc)
  have hxU : x ∈ U := ⟨hxV, fun r hr => by
    have hc := hxfix r hr
    have e : ⁅r, x⁆ = x * (x⁻¹ * (r * x * r⁻¹)) * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hVc x hxV _ (hCV hc), mul_inv_cancel_right]
    exact hc⟩
  have hYNU : Y ≤ normalizer (U : Set G) := by
    intro y hy
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨haV, ha'⟩ := ha
    refine ⟨(mem_normalizer_iff.1 (hYV hy) a).1 haV, fun r hr => ?_⟩
    have hry : r * y = y * r := hXY r (hRX.le hr) y hy
    have e : ⁅r, y * a * y⁻¹⁆ = y * ⁅r, a⁆ * y⁻¹ := by
      calc ⁅r, y * a * y⁻¹⁆ = ⁅y * r * y⁻¹, y * a * y⁻¹⁆ := by rw [conj_comm hry]
        _ = y * ⁅r, a⁆ * y⁻¹ := by simp only [commutatorElement_def]; group
    rw [e, conj_of_centralizes (hYC hy) (ha' r hr)]
    exact ha' r hr
  have hYNX : Y ≤ normalizer (NX : Set G) := fun y hy => (centralizer_le_normalizer _) (hYC hy)
  have hex : ∃ y ∈ Y, ∃ a ∈ U, y * a * y⁻¹ * a⁻¹ ∉ NX := by
    by_contra hne
    push Not at hne
    have hxy : x ∈ centralizer (Y : Set G) := pc hperY hCc hCY (fun z hz => by
      have := hne z hz x hxU
      rwa [← commutatorElement_def] at this)
    exact hxN (hNeq ▸ (⟨hxV, hxy⟩ : x ∈ NY))
  obtain ⟨y, hy, a, haU, hya⟩ := hex
  have h1 := Common.sl2_card_sq_le_relIndex_of_not_mem φY hk hm (fun v hv => hVsq v (mem_A.1 hv).1) hNU hYNU
    hYNX hy haU hya
  have h2 := Subgroup.relIndex_mul_card (H := NX) (K := U)
  rw [inf_eq_left.2 hNU] at h2
  have hUge : 2 ^ (2 * m) * Nat.card NX ≤ Nat.card U := by
    calc 2 ^ (2 * m) * Nat.card NX = Nat.card k ^ 2 * Nat.card NX := by
          rw [hk, ← pow_mul, mul_comm m 2]
      _ ≤ NX.relIndex U * Nat.card NX := Nat.mul_le_mul_right _ h1
      _ = Nat.card U := h2
  obtain ⟨P', hP', hne⟩ := exists_isSylowOf_ne hk hm1 φX RX
  obtain ⟨x₀, hx₀X, hP'eq⟩ := Prelim.exists_conj_of_isSylowOf hRX hP'
  set U' : Subgroup G := A V NX P' hCV hVc with hU'
  have hconjU : U.map (MulAut.conj x₀).toMonoidHom ≤ U' := by
    rintro _ ⟨a, ⟨haV, ha⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.1 (hXV hx₀X) a).1 haV, fun r' hr' => ?_⟩
    rw [hP'eq] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    have e : ⁅(MulAut.conj x₀).toMonoidHom r, (MulAut.conj x₀).toMonoidHom a⁆ =
        x₀ * ⁅r, a⁆ * x₀⁻¹ := by
      show ⁅x₀ * r * x₀⁻¹, x₀ * a * x₀⁻¹⁆ = _
      simp only [commutatorElement_def]; group
    rw [e, conj_of_centralizes (hXC hx₀X) (ha r hr)]
    exact ha r hr
  have hcardU' : Nat.card U ≤ Nat.card U' := by
    calc Nat.card U = Nat.card (U.map (MulAut.conj x₀).toMonoidHom) :=
          (Prelim.card_map_conj U x₀).symm
      _ ≤ Nat.card U' := Subgroup.card_le_of_le hconjU
  have hUU' : U ⊓ U' = NX := by
    refine le_antisymm (fun v hv => ?_) (le_inf hNU fun c hc => ⟨hCV hc, fun r hr => ?_⟩)
    · obtain ⟨⟨hvV, hv1⟩, -, hv2⟩ := hv
      have hsup : RX ⊔ P' ≤ Stab X NX hXC v := sup_le (fun r hr => ⟨hRX.le hr, hv1 r hr⟩)
        (fun r hr => ⟨hP'.le hr, hv2 r hr⟩)
      rw [Prelim.sup_eq_of_isSylowOf_ne hk hm1 φX hRX hP' hne] at hsup
      have hvX : v ∈ centralizer (X : Set G) := pc hperX hCc hCX (fun z hz => (hsup hz).2)
      exact ⟨hvV, hvX⟩
    · have : ⁅r, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 (hCX hc) r (hP'.le hr))
      rw [this]
      exact one_mem _
  have hU'V : U' ≤ V := fun v hv => (mem_A.1 hv).1
  have hprod : Nat.card (U ⊔ U' : Subgroup G) * Nat.card (U ⊓ U' : Subgroup G) =
      Nat.card U * Nat.card U' :=
    Common.card_sup_mul_card_inf_eq (hU'V.trans (Common.le_normalizer_of_mul_comm hUV hVc))
  have hsupV : Nat.card (U ⊔ U' : Subgroup G) ≤ Nat.card V :=
    Subgroup.card_le_of_le (sup_le hUV hU'V)
  rw [hUU'] at hprod
  have h44 : 2 ^ (4 * m) = 2 ^ (2 * m) * 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  have hNXcard : Nat.card NX = 1 := by
    have hpos : 0 < Nat.card NX := Nat.card_pos
    have h5 : (2 ^ (2 * m) * Nat.card NX) * (2 ^ (2 * m) * Nat.card NX) ≤
        2 ^ (4 * m) * Nat.card NX := by
      calc (2 ^ (2 * m) * Nat.card NX) * (2 ^ (2 * m) * Nat.card NX)
          ≤ Nat.card U * Nat.card U' := Nat.mul_le_mul hUge (hUge.trans hcardU')
        _ = Nat.card (U ⊔ U' : Subgroup G) * Nat.card NX := hprod.symm
        _ ≤ Nat.card V * Nat.card NX := Nat.mul_le_mul_right _ hsupV
        _ ≤ 2 ^ (4 * m) * Nat.card NX := Nat.mul_le_mul_right _ hVcard
    have h6 : 2 ^ (4 * m) * (Nat.card NX * Nat.card NX) ≤ 2 ^ (4 * m) * Nat.card NX := by
      calc 2 ^ (4 * m) * (Nat.card NX * Nat.card NX)
          = (2 ^ (2 * m) * Nat.card NX) * (2 ^ (2 * m) * Nat.card NX) := by rw [h44]; ring
        _ ≤ _ := h5
    have h7 : Nat.card NX * Nat.card NX ≤ Nat.card NX :=
      Nat.le_of_mul_le_mul_left h6 (by positivity)
    exact le_antisymm (by nlinarith) hpos
  have hNXbot : NX = ⊥ := Subgroup.card_eq_one.1 hNXcard
  have hUeq : U = V ⊓ centralizer (RX : Set G) := by
    ext v
    constructor
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, mem_centralizer_iff.2 fun r hr => ?_⟩
      have := hv r hr
      rw [hNXbot, mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, fun r hr => ?_⟩
      rw [hNXbot, mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hv r hr)
  have hUcard_ge : 2 ^ (2 * m) ≤ Nat.card U := by simpa [hNXcard] using hUge
  have hUcard_le : Nat.card U ≤ 2 ^ (2 * m) := by
    have h5 : Nat.card U * Nat.card U ≤ 2 ^ (2 * m) * 2 ^ (2 * m) := by
      calc Nat.card U * Nat.card U ≤ Nat.card U * Nat.card U' := Nat.mul_le_mul_left _ hcardU'
        _ = Nat.card (U ⊔ U' : Subgroup G) * Nat.card NX := hprod.symm
        _ ≤ Nat.card V * 1 := by rw [hNXcard]; exact Nat.mul_le_mul_right _ hsupV
        _ ≤ 2 ^ (4 * m) := by simpa using hVcard
        _ = _ := h44
    exact (Nat.mul_self_le_mul_self_iff).1 h5
  have hUcard : Nat.card U = 2 ^ (2 * m) := le_antisymm hUcard_le hUcard_ge
  have hW : V ⊓ centralizer (RY : Set G) = U.map (MulAut.conj t').toMonoidHom := by
    rw [hUeq, ← Prelim.inf_centralizer_map_conj htV, htR]
  have hUW : U ⊓ (V ⊓ centralizer (RY : Set G)) =
      V ⊓ centralizer ((RX ⊔ RY : Subgroup G) : Set G) := by
    rw [hUeq, Prelim.centralizer_sup_eq]
    ext z
    simp only [Subgroup.mem_inf]
    tauto
  have hUUW : U ⊓ (V ⊓ centralizer (RY : Set G)) = U := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hUW, hUcard]
    exact hC
  have hUW' : U ≤ V ⊓ centralizer (RY : Set G) := inf_eq_left.1 hUUW
  have hRYU : RY ≤ centralizer (U : Set G) := fun r hr => mem_centralizer_iff.2 fun u hu =>
    (mem_centralizer_iff.1 (hUW' hu).2 r hr).symm
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : IsSimpleGroup (SL(2, k)) := Common.sl2_isSimpleGroup_of_charTwo h4
  haveI : IsSimpleGroup Y := φY.isSimpleGroup
  haveI hHn := Prelim.normal_centralizer_subgroupOf hYNU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((centralizer (U : Set G)).subgroupOf Y) with hbot | htop
  ·
    have hRYcard := Prelim.card_of_isSylowOf hk hm1 φY hRY
    have hRYne : RY ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hRYcard
      have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
      omega
    obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hRYne
    have hmem : (⟨r, hRY.le hrR⟩ : Y) ∈ (centralizer (U : Set G)).subgroupOf Y :=
      Subgroup.mem_subgroupOf.2 (hRYU hrR)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hr' : r = 1 := congrArg Subtype.val hmem
    exact hr1 (Subtype.ext hr')
  · have hYU : Y ≤ centralizer (U : Set G) := Subgroup.subgroupOf_eq_top.1 htop
    have hUbot : U ≤ ⊥ := fun u hu => by
      have hu1 : u ∈ V ⊓ centralizer (Y : Set G) :=
        ⟨hUV hu, mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (hYU hy) u hu).symm⟩
      rw [← hNY, ← hNeq, hNXbot] at hu1
      exact hu1
    have := Subgroup.card_le_of_le hUbot
    rw [Subgroup.card_bot, hUcard] at this
    have h2 : 2 ≤ 2 ^ (2 * m) := Nat.le_self_pow (by omega) 2
    omega

theorem pairDecomp {V X Y RX RY : Subgroup G} (t' : G) (φX : X ≃* SL(2, k)) (φY : Y ≃* SL(2, k))
    (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hVsq : ∀ v ∈ V, v * v = 1)
    (hVcard : Nat.card V ≤ 2 ^ (4 * m))
    (hXV : X ≤ normalizer (V : Set G)) (hYV : Y ≤ normalizer (V : Set G))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hRX : IsSylowOf 2 RX X) (hRY : IsSylowOf 2 RY Y)
    (hnt : ¬ X ≤ centralizer (V : Set G))
    (hC : 2 ^ (2 * m) ≤ Nat.card (V ⊓ centralizer ((RX ⊔ RY : Subgroup G) : Set G) : Subgroup G))
    (htV : t' ∈ normalizer (V : Set G)) (htX : X.map (MulAut.conj t').toMonoidHom = Y)
    (htY : Y.map (MulAut.conj t').toMonoidHom = X) (htR : RX.map (MulAut.conj t').toMonoidHom = RY) :
    (V ⊓ centralizer (X : Set G)) ⊔ (V ⊓ centralizer (Y : Set G)) = V ∧
      (V ⊓ centralizer (X : Set G)) ⊓ (V ⊓ centralizer (Y : Set G)) = ⊥ ∧
      Nat.card (V ⊓ centralizer (X : Set G) : Subgroup G) = 2 ^ (2 * m) ∧
      Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ^ (2 * m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self hVsq ha hb
  set NX : Subgroup G := V ⊓ centralizer (X : Set G) with hNX
  set NY : Subgroup G := V ⊓ centralizer (Y : Set G) with hNY
  have hτX : NX.map (MulAut.conj t').toMonoidHom = NY := by
    rw [hNX, hNY, ← Prelim.inf_centralizer_map_conj htV, htX]
  have hNXV : NX ≤ V := inf_le_left
  have hNYV : NY ≤ V := inf_le_left
  have hYNX : Y ≤ normalizer (NX : Set G) := fun y hy =>
    Common.mem_normalizer_inf (hYV hy) (Prelim.normalizer_le_normalizer_centralizer X
      ((centralizer_le_normalizer _) (mem_centralizer_iff.2 fun x hx => hXY x hx y hy)))
  have hP3 : ¬ Y ≤ centralizer (NX : Set G) := fun hY =>
    key_false t' φX φY hk hm hVsq hVcard hXV hYV hXY hRX hRY hnt hC htV htX htY htR hY
  have hle := card_inf_centralizer_le φX hk hm hVsq hVcard hXV hnt
  have hge : 2 ^ (2 * m) ≤ Nat.card NX := by
    have := Common.sl2_card_sq_le_of_not_le_centralizer (V := NX) φY hk hm
      (fun v hv => hVsq v hv.1) hYNX hP3
    rwa [hk, ← pow_mul, mul_comm m 2] at this
  have hcardX : Nat.card NX = 2 ^ (2 * m) := le_antisymm hle hge
  have hbot : NX ⊓ centralizer (Y : Set G) = ⊥ :=
    Common.inf_centralizer_eq_bot_of_not_le hk hm φY
      (fun a ha b hb => hVc a (hNXV ha) b (hNXV hb)) hYNX
      (by rw [hcardX, ← pow_mul, mul_comm]) hP3
  have hinf : NX ⊓ NY = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h : z ∈ NX ⊓ centralizer (Y : Set G) := ⟨hz.1, hz.2.2⟩
    rw [hbot] at h
    exact h
  have hcardY : Nat.card NY = 2 ^ (2 * m) := by
    rw [← hτX, Prelim.card_map_conj]
    exact hcardX
  have hprod := Common.card_sup_mul_card_inf_eq (A := NX) (B := NY)
    (hNYV.trans (Common.le_normalizer_of_mul_comm hNXV hVc))
  rw [hinf, Subgroup.card_bot, mul_one, hcardX, hcardY, ← pow_add,
    show 2 * m + 2 * m = 4 * m by ring] at hprod
  have hsup : NX ⊔ NY = V :=
    Subgroup.eq_of_le_of_card_ge (sup_le hNXV hNYV) (by rw [hprod]; exact hVcard)
  exact ⟨hsup, hinf, hcardX, hcardY⟩

theorem comm_of_decomp {V X Y : Subgroup G} (φX : X ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (hm3 : m ≠ 3) (hVsq : ∀ v ∈ V, v * v = 1)
    (hXV : X ≤ normalizer (V : Set G)) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hsup : (V ⊓ centralizer (X : Set G)) ⊔ (V ⊓ centralizer (Y : Set G)) = V)
    (hinf : (V ⊓ centralizer (X : Set G)) ⊓ (V ⊓ centralizer (Y : Set G)) = ⊥)
    (hcard : Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ^ (2 * m)) :
    ⁅V ⊓ centralizer (Y : Set G), X⁆ = V ⊓ centralizer (Y : Set G) ∧
      ∀ v ∈ V, ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ V ⊓ centralizer (Y : Set G) := by
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self hVsq ha hb
  set V₁ : Subgroup G := V ⊓ centralizer (Y : Set G) with hV₁
  set V₂ : Subgroup G := V ⊓ centralizer (X : Set G) with hV₂
  have hXN : X ≤ normalizer (V₁ : Set G) := fun x hx => Common.mem_normalizer_inf (hXV hx)
    (Prelim.normalizer_le_normalizer_centralizer Y ((centralizer_le_normalizer _)
      (mem_centralizer_iff.2 fun y hy => (hXY x hx y hy).symm)))
  refine ⟨commutator_eq_of_card hk hm hm3 φX
    (Common.isPGroup_two_of_mul_self (V := V₁) (fun v hv => hVsq v hv.1)) hXN ?_ hcard, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have h : z ∈ V₂ ⊓ V₁ := ⟨⟨hz.1.1, hz.2⟩, hz.1⟩
    rw [hinf] at h
    exact h
  · intro v hv x hx
    have hV₁₂ : V₁ ⊔ V₂ = V := by rw [sup_comm]; exact hsup
    have hLE : V₁ ≤ normalizer (V₂ : Set G) :=
      (inf_le_left : V₁ ≤ V).trans (Common.le_normalizer_of_mul_comm (inf_le_left : V₂ ≤ V) hVc)
    have hv' : v ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by rw [hV₁₂]; exact hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ V₂ hLE] at hv'
    obtain ⟨a, ha, b, hb, rfl⟩ := hv'
    have hbx : x * b = b * x := mem_centralizer_iff.1 hb.2 x hx
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by
      calc a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ * x⁻¹ := by group
        _ = a * (x * b) * b⁻¹ * a⁻¹ * x⁻¹ := by rw [← hbx]
        _ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem ha ((mem_normalizer_iff.1 (hXN hx) a⁻¹).1 (inv_mem ha))

end Counting

section Lattice

variable {G : Type*} [Group G]

theorem sup_inf_decomp {V V₁ V₂ X Y : Subgroup G} (hV₁ : V₁ ≤ V) (hV₂ : V₂ ≤ V)
    (hsup : V₁ ⊔ V₂ = V) (hinf : V₁ ⊓ V₂ = ⊥) (hXY : X ⊓ Y = ⊥) (hVM : V ⊓ (X ⊔ Y) = ⊥)
    (hXN : X ≤ normalizer (V₁ : Set G)) (hYN : Y ≤ normalizer (V₂ : Set G)) :
    (V₁ ⊔ X) ⊔ (V₂ ⊔ Y) = V ⊔ (X ⊔ Y) ∧ (V₁ ⊔ X) ⊓ (V₂ ⊔ Y) = ⊥ := by
  refine ⟨by rw [← hsup]; exact sup_sup_sup_comm _ _ _ _, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  have hg1' : g ∈ ((V₁ ⊔ X : Subgroup G) : Set G) := hg1
  have hg2' : g ∈ ((V₂ ⊔ Y : Subgroup G) : Set G) := hg2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V₁ X hXN] at hg1'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V₂ Y hYN] at hg2'
  obtain ⟨a, ha, x, hx, hgax⟩ := hg1'
  obtain ⟨b, hb, y, hy, hgby⟩ := hg2'
  have hab : a * x = b * y := hgax.trans hgby.symm
  have e : b⁻¹ * a = y * x⁻¹ := by
    calc b⁻¹ * a = b⁻¹ * (a * x) * x⁻¹ := by group
      _ = b⁻¹ * (b * y) * x⁻¹ := by rw [hab]
      _ = y * x⁻¹ := by group
  have ha' : a ∈ V₁ := ha
  have hb' : b ∈ V₂ := hb
  have hx' : x ∈ X := hx
  have hy' : y ∈ Y := hy
  have h1 : b⁻¹ * a ∈ V := mul_mem (inv_mem (hV₂ hb')) (hV₁ ha')
  have h2 : b⁻¹ * a ∈ X ⊔ Y := by
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hy') (inv_mem (Subgroup.mem_sup_left hx'))
  have hmem : b⁻¹ * a ∈ V ⊓ (X ⊔ Y) := ⟨h1, h2⟩
  rw [hVM, mem_bot] at hmem
  have hyx : y * x⁻¹ = 1 := e ▸ hmem
  have hab' : a = b := by
    have : a = b * (b⁻¹ * a) := by group
    rw [this, hmem, mul_one]
  have hxy : x = y := by
    have : x = (y * x⁻¹)⁻¹ * y := by group
    rw [this, hyx, inv_one, one_mul]
  have ha1 : a ∈ V₁ ⊓ V₂ := ⟨ha', hab' ▸ hb'⟩
  have hx1 : x ∈ X ⊓ Y := ⟨hx', hxy ▸ hy'⟩
  rw [hinf, mem_bot] at ha1
  rw [hXY, mem_bot] at hx1
  rw [← hgax, ha1, hx1]
  simp

theorem normalizer_inf_centralizer [Finite G] {V X Y : Subgroup G}
    (hXV : X ≤ normalizer (V : Set G)) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ≤ normalizer ((V ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) := fun x hx =>
  Common.mem_normalizer_inf (hXV hx) (Prelim.normalizer_le_normalizer_centralizer Y
    ((centralizer_le_normalizer _) (mem_centralizer_iff.2 fun y hy => (hXY x hx y hy).symm)))

theorem normalizer_sup_of_comm [Finite G] {V V₁ X : Subgroup G} (hV₁ : V₁ ≤ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hXN : X ≤ normalizer (V₁ : Set G))
    (hVX : ∀ v ∈ V, ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ V₁) :
    V ≤ normalizer ((V₁ ⊔ X : Subgroup G) : Set G) := by
  intro v hv
  refine mem_normalizer_fintype fun y hy => ?_
  have hy' : y ∈ ((V₁ ⊔ X : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V₁ X hXN] at hy'
  obtain ⟨a, ha, x, hx, rfl⟩ := hy'
  have ha' : a ∈ V₁ := ha
  have hx' : x ∈ X := hx
  have e : v * (a * x) * v⁻¹ = a * ((v * x * v⁻¹ * x⁻¹) * x) := by
    calc v * (a * x) * v⁻¹ = (v * a * v⁻¹) * (v * x * v⁻¹) := by group
      _ = a * (v * x * v⁻¹) := by rw [hVc v hv a (hV₁ ha'), mul_inv_cancel_right]
      _ = a * ((v * x * v⁻¹ * x⁻¹) * x) := by group
  have h1 : v * x * v⁻¹ * x⁻¹ ∈ V₁ := hVX v hv x hx'
  have : a * ((v * x * v⁻¹ * x⁻¹) * x) ∈ V₁ ⊔ X :=
    mul_mem (Subgroup.mem_sup_left ha') (mul_mem (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right hx'))
  show v * (a * x) * v⁻¹ ∈ V₁ ⊔ X
  rw [e]
  exact this

end Lattice

section Setting

variable {G : Type*} [Group G]

structure Setting (m : ℕ) (V X Y RX RY : Subgroup G) (t' : G) : Prop where
  sq : ∀ v ∈ V, v * v = 1
  card : Nat.card V = 2 ^ (4 * m)
  normX : X ≤ normalizer (V : Set G)
  normY : Y ≤ normalizer (V : Set G)
  comm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x
  sylowX : IsSylowOf 2 RX X
  sylowY : IsSylowOf 2 RY Y
  nt : ¬ X ≤ centralizer (V : Set G)
  fixed : 2 ^ (2 * m) ≤ Nat.card (V ⊓ centralizer ((RX ⊔ RY : Subgroup G) : Set G) : Subgroup G)
  tNorm : t' ∈ normalizer (V : Set G)
  tMapX : X.map (MulAut.conj t').toMonoidHom = Y
  tMapY : Y.map (MulAut.conj t').toMonoidHom = X
  tMapR : RX.map (MulAut.conj t').toMonoidHom = RY

end Setting

section SettingDecomp

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] [CharP k 2] {m : ℕ}

theorem Setting.pairDecomp {V X Y RX RY : Subgroup G} {t' : G} (h : Setting m V X Y RX RY t')
    (φX : X ≃* SL(2, k)) (φY : Y ≃* SL(2, k)) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) :
    (V ⊓ centralizer (X : Set G)) ⊔ (V ⊓ centralizer (Y : Set G)) = V ∧
      (V ⊓ centralizer (X : Set G)) ⊓ (V ⊓ centralizer (Y : Set G)) = ⊥ ∧
      Nat.card (V ⊓ centralizer (X : Set G) : Subgroup G) = 2 ^ (2 * m) ∧
      Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ^ (2 * m) :=
  Sec312.pairDecomp t' φX φY hk hm h.sq h.card.le h.normX h.normY h.comm h.sylowX h.sylowY h.nt
    h.fixed h.tNorm h.tMapX h.tMapY h.tMapR

end SettingDecomp

end Sec312

end CFSG.LocalAnalysis.EvenBN.U5
