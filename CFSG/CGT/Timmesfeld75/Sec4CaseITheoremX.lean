module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIProps
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIKernel
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a x : G}

theorem Sec4Hyp.card_centralizer_le (h : Sec4Hyp T T₁ a T₂) (hx : x ∈ normD T) (hxT : x ∉ T) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card (normIn T T₁) := by
  obtain ⟨g, t, htT, ht1, hxg⟩ := hx.1
  have hxT' : x ∈ conjSubgroup g⁻¹ T := mem_conjSubgroup.2 (by
    rw [inv_inv, hxg]
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact htT)
  have hne : conjSubgroup g⁻¹ T ≠ T := fun h' => hxT (h' ▸ hxT')
  have hx1 : x ≠ 1 := fun h1 => ht1 (by
    have : t = g * x * g⁻¹ := by rw [hxg]; group
    rw [this, h1]
    group)
  have hxN : x ∈ normIn (conjSubgroup g⁻¹ T) T := mem_normIn.2 ⟨hxT', hx.2⟩
  have hL' : normIn (conjSubgroup g⁻¹ T) T ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨x, hxN⟩, fun h' => hx1 (congrArg Subtype.val h')⟩
  have hL : normIn T (conjSubgroup g⁻¹ T) ≠ ⊥ := normIn_ne_bot_of_conj h.pair.wc hne hL'
  have hc : Cfg T (conjSubgroup g⁻¹ T) :=
    cfg_of_conj_conj h.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne hL
  rw [hc.inf_centralizer_eq_normIn hxN hx1]
  exact h.pair.card_normIn_le ⟨1, (conjSubgroup_one T).symm⟩ ⟨g⁻¹, rfl⟩ hne

omit [Finite G] in
theorem inf_centralizer_mul_eq (hT : IsElemAbelian 2 T) {t : G} (ht : t ∈ T) :
    T ⊓ Subgroup.centralizer ({x * t} : Set G) = T ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext s
  constructor
  · rintro ⟨hs, hsc⟩
    refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hsc
    have hst : s * t = t * s := elemAbelian_mul_comm hT hs ht
    have : s * x * t = x * s * t := by
      calc s * x * t = (s * (x * t)) := by group
        _ = (x * t) * s := h1
        _ = x * (t * s) := by group
        _ = x * (s * t) := by rw [hst]
        _ = x * s * t := by group
    exact mul_right_cancel this
  · rintro ⟨hs, hsc⟩
    refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hsc
    have hst : s * t = t * s := elemAbelian_mul_comm hT hs ht
    calc s * (x * t) = (s * x) * t := by group
      _ = (x * s) * t := by rw [h1]
      _ = x * (s * t) := by group
      _ = x * (t * s) := by rw [hst]
      _ = (x * t) * s := by group

theorem Sec4Hyp.false_of_acts_like_t (h : Sec4Hyp T T₁ a T₂) (hxD : x ∈ classD T)
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hxT' : x ∉ T) {t : G} (ht : t ∈ T)
    (htL : t ∉ normIn T T₁) (hact : Sec4ActsTriv T T₁ T₂ (x * t))
    (hcomm : ∀ m ∈ sec4N T T₁ T₂, (x * t) * m * (x * t)⁻¹ = m) : False := by
  have hTab := h.pair.wc.1
  have hxx : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hxD
  have htt : t * t = 1 := elemAbelian_mul_self hTab ht
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hLC : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro l hl
    refine ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hcomm l (normIn_le_sec4N_left hl)
    have hl' : t * l * t⁻¹ = l := by
      rw [elemAbelian_mul_comm hTab ht (normIn_le _ _ hl)]
      group
    have h2 : x * l * x⁻¹ = l := by
      have e : (x * t) * l * (x * t)⁻¹ = x * (t * l * t⁻¹) * x⁻¹ := by group
      rw [e, hl'] at h1
      exact h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hCx : normIn T T₁ = T ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hLC (h.card_centralizer_le ⟨hxD, hxT⟩ hxT')
  have hxt : x * t ≠ t * x := fun hc => htL (by
    rw [hCx]
    exact ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩)
  have hs : (x * t) * (x * t) = (x * t * x⁻¹) * t := by
    rw [hxinv]
    group
  have hsT : (x * t) * (x * t) ∈ T := by
    rw [hs]
    exact T.mul_mem (conj_mem_of_mem_normalizer hxT ht) ht
  have hs1 : (x * t) * (x * t) ≠ 1 := fun h1 => hxt (by
    have h2 : x * t * x = t := by
      have h3 : (x * t * x) * t = 1 := by rw [← h1]; group
      rw [mul_eq_one_iff_eq_inv, htinv] at h3
      exact h3
    calc x * t = (x * t * x) * x := by rw [mul_assoc (x * t) x x, hxx, mul_one]
      _ = t * x := by rw [h2])
  have hsY : ∀ y ∈ sec4Y T T₁ T₂, ((x * t) * (x * t)) * y * ((x * t) * (x * t))⁻¹ = y := by
    intro y hy
    obtain ⟨κ, hκ, hwy⟩ := hact.conj_eq hy
    have hκκ : κ * κ = 1 := elemAbelian_mul_self h.isElemAbelian_sec4N hκ
    have e : ((x * t) * (x * t)) * y * ((x * t) * (x * t))⁻¹ =
        (x * t) * ((x * t) * y * (x * t)⁻¹) * (x * t)⁻¹ := by group
    rw [e, hwy]
    have e2 : (x * t) * (κ * y) * (x * t)⁻¹ =
        ((x * t) * κ * (x * t)⁻¹) * ((x * t) * y * (x * t)⁻¹) := by group
    rw [e2, hcomm κ hκ, hwy, ← mul_assoc, hκκ, one_mul]
  obtain ⟨x₁, hx₁⟩ := h.pair.conj
  have hle : conjSubgroup x₁ T ≤ Subgroup.centralizer ({(x * t) * (x * t)} : Set G) := by
    rw [← hx₁]
    intro u hu
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := hsY u (mid_le_sec4Y hu)
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  exact h.pair.ne (hx₁ ▸ (h.pair.wc.2 _ hsT hs1).2 x₁ hle)

theorem Sec4Hyp.exists_acts_like_t
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) (hxD : x ∈ classD T)
    (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxN : x ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) (hxR : x ∉ sec4R T T₁ T₂) :
    ∃ t ∈ T, t ∉ normIn T T₁ ∧ Sec4ActsTriv T T₁ T₂ (x * t) ∧
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) < Nat.card (normIn T T₁) := by
  have hTab := h.pair.wc.1
  have hxT' : x ∉ T := fun hx => hxR (left_le_sec4R hx)
  by_cases hI : ∃ t ∈ T, Sec4ActsTriv T T₁ T₂ (x * t)
  swap
  · exact (hC G hnab hind T T₁ T₂ a h hq h16 x hxD hxT hxN fun t ht hact => hI ⟨t, ht, hact⟩).elim
  obtain ⟨t, htT, hact⟩ := hI
  by_cases htL : t ∈ normIn T T₁
  · exfalso
    have hxK : x ∈ sec4Ker T T₁ T₂ := by
      have h1 : x * t ∈ sec4Ker T T₁ T₂ := hact
      have h2 : t ∈ sec4Ker T T₁ T₂ := h.sec4N_le_sec4Ker (normIn_le_sec4N_left htL)
      have := (sec4Ker T T₁ T₂).mul_mem h1 ((sec4Ker T T₁ T₂).inv_mem h2)
      simpa using this
    exact hxR (sec4N_le_sec4R (hA G hnab hind T T₁ T₂ a h hq h16 x hxD hxT hxK))
  refine ⟨t, htT, htL, hact, ?_⟩
  by_contra hge
  have hge' : Nat.card (normIn T T₁) ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) :=
    not_lt.1 hge
  have hwT : x * t ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem hxT (Subgroup.le_normalizer htT)
  have hC' : Nat.card (normIn T T₁) ≤
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x * t} : Set G)) := by
    rw [inf_centralizer_mul_eq hTab htT]
    exact hge'
  exact h.false_of_acts_like_t hxD hxT hxT' htT htL hact
    (h.commute_sec4N_of_actsTriv hAsc hq hact hwT hC')

end CFSG.CGT.Timmesfeld75
