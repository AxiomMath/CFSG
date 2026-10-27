module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RA

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

variable {G : Type} [Group G]

structure Frame39 (x y : G) (K T V W : Subgroup G) (f z : G) (S : Subgroup G) (a : G)
    (P₀ : Subgroup G) (f₁ : G) : Prop where
  cfg : Cfg3 x y K T V W f z
  hle : Nat.card ↥V ≤ Nat.card ↥T
  h37a : thompsonJ2 T = (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x)
  h37b : (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) = ⊥
  h37c : zCenter (thompsonJ2 T) = zpowers z ⊔ zpowers f ⊔ zpowers x
  h37d : ∀ P₀' : Subgroup G, IsDihedralMaxIn P₀' (T ⊓ K) →
    T ⊓ centralizer ({f} : Set G) = T ⊓ normalizer (P₀' : Set G)
  hcard : Nat.card ↥T =
    2 * Nat.card ↥(T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G))
  hPgen : T ⊓ K = closure {u : G | u ∈ thompsonJ2 T ∧ IsConj z u}
  hS : IsSylowOf 2 S ⊤
  hTS : T ≤ S
  hTne : T ≠ S
  haS : a ∈ S
  haN : a ∈ normalizer (T : Set G)
  haT : a ∉ T
  ha2 : a ^ 2 ∈ T
  hP₀ : IsDihedralMaxIn P₀ (T ⊓ K)
  haP₀ : a ∈ normalizer (P₀ : Set G)
  hax : a * x * a⁻¹ = x * z
  haz : a * z * a⁻¹ = z
  hf₁ : f₁ = f ∨ f₁ = f * x
  haf₁ : a * f₁ * a⁻¹ = f₁

@[expose] def v₁ (T : Subgroup G) (f a : G) : Subgroup G :=
  (T ⊓ centralizer ({f} : Set G)) ⊔ zpowers a

namespace Frame39

variable {x y : G} {K T V W S P₀ : Subgroup G} {f z a f₁ : G}
  (F : Frame39 x y K T V W f z S a P₀ f₁)

include F

theorem hx2 : x * x = 1 := mul_self_of_orderOf_two F.cfg.hx2
theorem hf2 : f * f = 1 := mul_self_of_orderOf_two F.cfg.hf2
theorem hz1 : z ≠ 1 := fun h => by
  have := F.cfg.z_mem.2.1
  rw [h, orderOf_one] at this
  omega

theorem x_comm : ∀ t ∈ T, t * x = x * t := fun _ ht =>
  mem_centralizer_singleton_iff.1 (F.cfg.setup.sylowT.le ht)

theorem f₁_comm_iff {t : G} (ht : t ∈ T) : t * f₁ = f₁ * t ↔ t * f = f * t := by
  rcases F.hf₁ with rfl | rfl
  · exact Iff.rfl
  · have hx := F.x_comm t ht
    constructor
    · intro h
      calc t * f = t * (f * x) * x := by simp only [mul_assoc, F.hx2, mul_one]
        _ = f * x * t * x := by rw [h]
        _ = f * (x * t) * x := by simp only [mul_assoc]
        _ = f * (t * x) * x := by rw [← hx]
        _ = f * t := by simp only [mul_assoc, F.hx2, mul_one]
    · intro h
      calc t * (f * x) = (t * f) * x := (mul_assoc _ _ _).symm
        _ = f * t * x := by rw [h]
        _ = f * (t * x) := mul_assoc _ _ _
        _ = f * (x * t) := by rw [hx]
        _ = f * x * t := (mul_assoc _ _ _).symm

theorem C₀_eq : T ⊓ centralizer ({f₁} : Set G) = T ⊓ centralizer ({f} : Set G) := by
  ext t
  simp only [mem_inf, mem_centralizer_singleton_iff]
  exact and_congr_right fun ht => F.f₁_comm_iff ht

theorem a_comm_f₁ : a * f₁ = f₁ * a := mul_inv_eq_iff_eq_mul.1 F.haf₁

theorem a_not_mem_C₀ : a ∉ T ⊓ centralizer ({f} : Set G) := fun h => F.haT h.1

theorem v₁_le_C : v₁ T f a ≤ centralizer ({f₁} : Set G) := by
  refine sup_le (fun c hc => ?_) (zpowers_le.2 (mem_centralizer_singleton_iff.2 F.a_comm_f₁))
  rw [← F.C₀_eq] at hc
  exact hc.2

theorem v₁_le_S : v₁ T f a ≤ S := sup_le (inf_le_left.trans F.hTS) (zpowers_le.2 F.haS)

theorem v₁_le_normalizer : v₁ T f a ≤ normalizer (P₀ : Set G) := by
  refine sup_le (fun c hc => ?_) (zpowers_le.2 F.haP₀)
  rw [F.h37d P₀ F.hP₀] at hc
  exact hc.2

section Fin

variable [Finite G]

theorem x_mem : x ∈ T := F.cfg.x_mem_T

theorem isFMember_f₁ : IsFMember x K T f₁ := by
  rcases F.hf₁ with rfl | rfl
  · exact F.cfg.mem
  · obtain ⟨hfT, -, hfP, hfx, hlayer⟩ := F.cfg.mem
    have hxT := F.x_mem
    have hcomm : x * f = f * x := F.cfg.hxf
    have hf1 : f ≠ 1 := fun h => by
      have := F.cfg.hf2
      rw [h, orderOf_one] at this
      omega
    have hfx1 : f * x ≠ 1 := by
      intro h
      apply hfx
      have : f = x⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact inv_eq_of_mul_eq_one_right F.hx2
    have hord : orderOf (f * x) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ hfx1
      calc (f * x) ^ 2 = f * x * (f * x) := sq _
        _ = f * (x * f) * x := by simp only [mul_assoc]
        _ = f * (f * x) * x := by rw [hcomm]
        _ = (f * f) * (x * x) := by simp only [mul_assoc]
        _ = 1 := by rw [F.hf2, F.hx2, one_mul]
    refine ⟨T.mul_mem hfT hxT, hord, fun p hp => ?_, ?_, ?_⟩
    · have h1 := hfP p hp
      have h2 : p * x = x * p := mem_centralizer_singleton_iff.1 (F.cfg.hKx hp.2)
      calc f * x * p = f * (x * p) := mul_assoc _ _ _
        _ = f * (p * x) := by rw [h2]
        _ = f * p * x := (mul_assoc _ _ _).symm
        _ = p * f * x := by rw [h1]
        _ = p * (f * x) := mul_assoc _ _ _
    · intro h
      apply hf1
      calc f = f * x * x⁻¹ := by group
        _ = x * x⁻¹ := by rw [h]
        _ = 1 := by group
    · have : K ⊓ centralizer ({f * x} : Set G) = K ⊓ centralizer ({f} : Set G) := by
        ext k
        simp only [mem_inf, mem_centralizer_singleton_iff]
        refine and_congr_right fun hk => ?_
        have hkx : k * x = x * k := mem_centralizer_singleton_iff.1 (F.cfg.hKx hk)
        constructor
        · intro h
          calc k * f = k * (f * x) * x := by simp only [mul_assoc, F.hx2, mul_one]
            _ = f * x * k * x := by rw [h]
            _ = f * (x * k) * x := by simp only [mul_assoc]
            _ = f * (k * x) * x := by rw [← hkx]
            _ = f * k := by simp only [mul_assoc, F.hx2, mul_one]
        · intro h
          calc k * (f * x) = (k * f) * x := (mul_assoc _ _ _).symm
            _ = f * k * x := by rw [h]
            _ = f * (k * x) := mul_assoc _ _ _
            _ = f * (x * k) := by rw [hkx]
            _ = f * x * k := (mul_assoc _ _ _).symm
      rw [this]
      exact hlayer

omit [Finite G] in
theorem inf_centralizer_zCenter :
    T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G) =
      T ⊓ centralizer ({f} : Set G) := by
  ext t
  simp only [mem_inf]
  constructor
  · rintro ⟨htT, htc⟩
    refine ⟨htT, ?_⟩
    have hf : f ∈ zCenter (thompsonJ2 T) := by
      rw [F.h37c]; exact mem_sup_left (mem_sup_right (mem_zpowers f))
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htc f hf).symm
  · rintro ⟨htT, htf⟩
    refine ⟨htT, ?_⟩
    have hle : zpowers z ⊔ zpowers f ⊔ zpowers x ≤ centralizer ({t} : Set G) := by
      refine sup_le (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 (F.cfg.z_mem.2.2 t htT).symm
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 htf).symm
      · exact mem_centralizer_singleton_iff.2 (F.x_comm t htT).symm
    refine mem_centralizer_iff.2 fun g hg => ?_
    rw [F.h37c] at hg
    exact mem_centralizer_singleton_iff.1 (hle hg)

omit [Finite G] in
theorem card_C₀ : Nat.card ↥T = 2 * Nat.card ↥(T ⊓ centralizer ({f} : Set G)) := by
  rw [F.hcard, F.inf_centralizer_zCenter]

theorem card_v₁_ge : Nat.card ↥T ≤ Nat.card ↥(v₁ T f a) := by
  have hle : T ⊓ centralizer ({f} : Set G) ≤ v₁ T f a := le_sup_left
  have hnot : ¬ v₁ T f a ≤ T ⊓ centralizer ({f} : Set G) := fun h =>
    F.a_not_mem_C₀ (h (Subgroup.mem_sup_right (mem_zpowers a)))
  have h1 := Subgroup.relIndex_mul_card (H := T ⊓ centralizer ({f} : Set G)) (K := v₁ T f a)
  rw [inf_eq_left.2 hle] at h1
  have h2 : (T ⊓ centralizer ({f} : Set G)).relIndex (v₁ T f a) ≠ 1 := fun h =>
    hnot (Subgroup.relIndex_eq_one.1 h)
  have hpos : 0 < (T ⊓ centralizer ({f} : Set G)).relIndex (v₁ T f a) := by
    by_contra h0
    have h0' : (T ⊓ centralizer ({f} : Set G)).relIndex (v₁ T f a) = 0 := by omega
    rw [h0', zero_mul] at h1
    exact absurd h1.symm Nat.card_pos.ne'
  have h3 : 2 ≤ (T ⊓ centralizer ({f} : Set G)).relIndex (v₁ T f a) := by omega
  calc Nat.card ↥T = 2 * Nat.card ↥(T ⊓ centralizer ({f} : Set G)) := F.card_C₀
    _ ≤ (T ⊓ centralizer ({f} : Set G)).relIndex (v₁ T f a) *
        Nat.card ↥(T ⊓ centralizer ({f} : Set G)) := Nat.mul_le_mul_right _ h3
    _ = Nat.card ↥(v₁ T f a) := h1

omit [Finite G] in
theorem v₁_pGroup : IsPGroup 2 ↥(v₁ T f a) := F.hS.isPGroup.to_le F.v₁_le_S

theorem twoPart_f : twoPartCard (centralizer ({f} : Set G)) = Nat.card ↥V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact F.cfg.sylowV.card_eq.symm

omit [Finite G] in
theorem fmax2_of_mem {f' : G} (hf' : IsFMember x K T f') : FMax2 x y K f' :=
  ⟨⟨⟨F.cfg.hu2, T, F.cfg.setup, hf'⟩, F.cfg.fmax.1.1.2⟩, F.cfg.fmax.1.2⟩

theorem bound {f' : G} (hf' : IsFMember x K T f') :
    twoPartCard (centralizer ({f'} : Set G)) ≤ Nat.card ↥T := by
  have h1 := F.cfg.fmax.2 x y K f' (F.fmax2_of_mem hf')
  rw [F.twoPart_f] at h1
  exact h1.trans F.hle

theorem fmax3_of_card {f' : G} (hf' : IsFMember x K T f')
    (hge : Nat.card ↥T ≤ twoPartCard (centralizer ({f'} : Set G))) : FMax3 x y K f' := by
  refine ⟨F.fmax2_of_mem hf', fun x' y' K' f'' h'' => ?_⟩
  have h1 := F.cfg.fmax.2 x' y' K' f'' h''
  rw [F.twoPart_f] at h1
  exact h1.trans (F.hle.trans hge)

theorem twoPart_f₁ : twoPartCard (centralizer ({f₁} : Set G)) = Nat.card ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf (G := G) 2 (centralizer ({f₁} : Set G))
  have h1 : Nat.card ↥(v₁ T f a) ≤ Nat.card ↥Q :=
    Thm1L3.card_le_of_isPGroup_of_isSylowOf F.v₁_pGroup F.v₁_le_C hQ
  have h2 : Nat.card ↥Q = twoPartCard (centralizer ({f₁} : Set G)) := hQ.card_eq
  have h3 := F.bound F.isFMember_f₁
  have h4 := F.card_v₁_ge
  omega

theorem v₁_sylow : IsSylowOf 2 (v₁ T f a) (centralizer ({f₁} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf (G := G) 2 (centralizer ({f₁} : Set G))
  have h1 : Nat.card ↥(v₁ T f a) ≤ Nat.card ↥Q :=
    Thm1L3.card_le_of_isPGroup_of_isSylowOf F.v₁_pGroup F.v₁_le_C hQ
  have h2 : Nat.card ↥Q = twoPartCard (centralizer ({f₁} : Set G)) := hQ.card_eq
  have h4 := F.card_v₁_ge
  have h5 := F.twoPart_f₁
  refine isSylowOf_of_card F.v₁_le_C ?_
  have : Nat.card ↥(v₁ T f a) = twoPartCard (centralizer ({f₁} : Set G)) := by omega
  exact this

theorem card_v₁ : Nat.card ↥(v₁ T f a) = Nat.card ↥T := by
  have h1 := F.v₁_sylow.card_eq
  have h2 := F.twoPart_f₁
  unfold twoPartCard at h2
  omega

theorem v₁_ne_S : v₁ T f a ≠ S := by
  intro h
  have h1 : Nat.card ↥S = Nat.card ↥T := by rw [← h]; exact F.card_v₁
  have h2 : T = S := Subgroup.eq_of_le_of_card_ge F.hTS (by rw [h1])
  exact F.hTne h2

theorem cfg₂ : Cfg3 x y K T (v₁ T f a) S f₁ z where
  fmax := F.fmax3_of_card F.isFMember_f₁ (le_of_eq F.twoPart_f₁.symm)
  setup := F.cfg.setup
  mem := F.isFMember_f₁
  z_mem := F.cfg.z_mem
  sylowV := F.v₁_sylow
  CTf_le := fun t ht hc => Subgroup.mem_sup_left
    (show t ∈ T ⊓ centralizer ({f} : Set G) from
      ⟨ht, mem_centralizer_singleton_iff.2 ((F.f₁_comm_iff ht).1 hc.symm)⟩)
  sylowW := F.hS
  V_le_W := F.v₁_le_S

end Fin

end Frame39

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
