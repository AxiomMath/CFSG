module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
import Mathlib.FieldTheory.Finite.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a x : G} {k : ℕ}

def IsCoprimePowerStable (A : Set G) : Prop :=
  ∀ ⦃m : ℕ⦄, 1 ≤ m → Nat.Coprime m (Nat.card G) → ∀ ⦃a : G⦄, a ∈ A → a ^ m ∈ A

theorem isCoprimePowerStable_iff :
    IsCoprimePowerStable A ↔
      ∀ ⦃m : ℕ⦄, 1 ≤ m → Nat.Coprime m (Nat.card G) → ∀ ⦃a : G⦄, a ∈ A → a ^ m ∈ A := Iff.rfl

theorem IsCoprimePowerStable.pow_mem (hA : IsCoprimePowerStable A) (hk1 : 1 ≤ k)
    (hk : Nat.Coprime k (Nat.card G)) (ha : a ∈ A) : a ^ k ∈ A := hA hk1 hk ha

@[simp]
theorem isCoprimePowerStable_empty : IsCoprimePowerStable (∅ : Set G) := by
  intro _ _ _ _ ha; exact ha.elim

theorem exists_coprime_pow_pow_eq_self [Finite G] (hk1 : 1 ≤ k)
    (hk : Nat.Coprime k (Nat.card G)) :
    ∃ b : ℕ, 1 ≤ b ∧ Nat.Coprime b (Nat.card G) ∧ ∀ y : G, (y ^ k) ^ b = y := by
  have hφ : 1 ≤ (Nat.card G).totient := Nat.totient_pos.2 Nat.card_pos
  refine ⟨k ^ ((Nat.card G).totient - 1), Nat.one_le_pow _ _ hk1, Nat.Coprime.pow_left _ hk,
    fun y => ?_⟩
  have hmul : k * k ^ ((Nat.card G).totient - 1) = k ^ (Nat.card G).totient := by
    rw [← pow_succ', Nat.sub_add_cancel hφ]
  rw [← pow_mul, hmul]
  have h1 : k ^ (Nat.card G).totient ≡ 1 [MOD orderOf y] :=
    (Nat.ModEq.pow_totient hk).of_dvd (orderOf_dvd_natCard y)
  simpa using pow_eq_pow_iff_modEq.2 h1

theorem IsCoprimePowerStable.mem_of_pow_mem [Finite G] (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) (hx : x ^ k ∈ A) : x ∈ A := by
  obtain ⟨b, hb1, hb, hbk⟩ := exists_coprime_pow_pow_eq_self (G := G) hk1 hk
  exact hbk x ▸ hA hb1 hb hx

theorem IsCoprimePowerStable.pow_mem_iff [Finite G] (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) : x ^ k ∈ A ↔ x ∈ A :=
  ⟨hA.mem_of_pow_mem hk1 hk, fun h => hA hk1 hk h⟩

theorem centralizer_singleton_pow_eq {b : ℕ} (hb : ∀ y : G, (y ^ k) ^ b = y) (a : G) :
    Subgroup.centralizer ({a ^ k} : Set G) = Subgroup.centralizer ({a} : Set G) := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have h : z * (a ^ k) ^ b = (a ^ k) ^ b * z := Commute.pow_right hz b
    rwa [hb a] at h
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact Commute.pow_right hz k

namespace IsDadeData

variable [Finite G]

theorem H_pow_eq (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A) (hk1 : 1 ≤ k)
    (hk : Nat.Coprime k (Nat.card G)) (ha : a ∈ A) : H (a ^ k) = H a := by
  obtain ⟨b, hb1, hb, hbk⟩ := exists_coprime_pow_pow_eq_self (G := G) hk1 hk
  have hcent : Subgroup.centralizer ({a ^ k} : Set G) = Subgroup.centralizer ({a} : Set G) :=
    centralizer_singleton_pow_eq hbk a
  refine (hD.eq_H_of_normal (hA hk1 hk ha) (N := H a) ?_ ?_ ?_ ?_).symm
  · rw [hcent]; exact hD.le_centralizer ha
  · rw [hcent]; exact hD.normal_subgroupOf ha
  · exact hD.isPiNumber_compl_card_H ha
  · rw [hcent, hD.index_subgroupOf_H ha]
    exact isPiNumber_card_inf_centralizer ha

theorem pow_mem_dadeSupport_pow (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) (ha : a ∈ A)
    (hx : x ∈ dadeSupport H a) : x ^ k ∈ dadeSupport H (a ^ k) := by
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 hx
  refine mem_dadeSupport_iff.2 ⟨y ^ k, ?_, hc.pow k⟩
  have huH : y * a⁻¹ ∈ H a := mem_dadeCoset_iff.1 hy
  have hcomm : Commute (y * a⁻¹) a :=
    Subgroup.mem_centralizer_singleton_iff.1 (hD.le_centralizer ha huH)
  have hyk : y ^ k = (y * a⁻¹) ^ k * a ^ k := by rw [← hcomm.mul_pow]; group
  rw [hyk]
  refine mem_dadeCoset_iff.2 ?_
  rw [hD.H_pow_eq hA hk1 hk ha]
  simpa using pow_mem huH k

theorem pow_mem_totalDadeSupport (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) (hx : x ∈ totalDadeSupport A H) :
    x ^ k ∈ totalDadeSupport A H := by
  obtain ⟨a, ha, hx⟩ := mem_totalDadeSupport_iff.1 hx
  exact mem_totalDadeSupport_iff.2
    ⟨a ^ k, hA hk1 hk ha, hD.pow_mem_dadeSupport_pow hA hk1 hk ha hx⟩

theorem pow_mem_totalDadeSupport_iff (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) :
    x ^ k ∈ totalDadeSupport A H ↔ x ∈ totalDadeSupport A H := by
  refine ⟨fun h => ?_, hD.pow_mem_totalDadeSupport hA hk1 hk⟩
  obtain ⟨b, hb1, hb, hbk⟩ := exists_coprime_pow_pow_eq_self (G := G) hk1 hk
  have := hD.pow_mem_totalDadeSupport hA hb1 hb h
  rwa [hbk x] at this

theorem preimage_pow_totalDadeSupport (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) :
    (fun y : G => y ^ k) ⁻¹' totalDadeSupport A H = totalDadeSupport A H :=
  Set.ext fun _ => hD.pow_mem_totalDadeSupport_iff hA hk1 hk

theorem image_pow_totalDadeSupport (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) :
    (fun y : G => y ^ k) '' totalDadeSupport A H = totalDadeSupport A H := by
  obtain ⟨b, hb1, hb, hbk⟩ := exists_coprime_pow_pow_eq_self (G := G) hk1 hk
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨y, hy, rfl⟩
    exact hD.pow_mem_totalDadeSupport hA hk1 hk hy
  · refine ⟨x ^ b, hD.pow_mem_totalDadeSupport hA hb1 hb hx, ?_⟩
    change (x ^ b) ^ k = x
    rw [← pow_mul, mul_comm b k, pow_mul, hbk x]

end IsDadeData

theorem powOp_mem_dadeDomain [Finite G] (hA : IsCoprimePowerStable A) (hk1 : 1 ≤ k)
    (hk : Nat.Coprime k (Nat.card G)) {f : ↥L → ℂ} (hf : f ∈ dadeDomain L A) :
    powOp k f ∈ dadeDomain L A := by
  obtain ⟨hf1, hf2⟩ := mem_dadeDomain.1 hf
  refine mem_dadeDomain.2 ⟨mem_classFun.2 fun z w hzw => ?_, fun z hz => ?_⟩
  · simp only [powOp_apply]
    exact (mem_classFun.1 hf1) (z ^ k) (w ^ k) (hzw.pow k)
  · simp only [powOp_apply]
    refine hf2 _ fun hmem => hz ?_
    exact hA.mem_of_pow_mem hk1 hk (x := (z : G)) (by simpa using hmem)

theorem dadeMap_powOp [Finite G] (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) (f : dadeDomain L A) :
    ((dadeMap hD ⟨powOp k (f : ↥L → ℂ), powOp_mem_dadeDomain hA hk1 hk f.2⟩ : classFun G) : G → ℂ)
      = powOp k ((dadeMap hD f : classFun G) : G → ℂ) := by
  funext x
  rw [powOp_apply]
  by_cases hx : x ∈ totalDadeSupport A H
  · set a := dadeRep A H x
    have ha : a ∈ A := dadeRep_mem hx
    have hxa : x ∈ dadeSupport H a := mem_dadeSupport_dadeRep hx
    rw [dadeMap_apply_of_mem_dadeSupport hD _ ha hxa,
      dadeMap_apply_of_mem_dadeSupport hD f (hA hk1 hk ha)
        (hD.pow_mem_dadeSupport_pow hA hk1 hk ha hxa)]
    change powOp k (f : ↥L → ℂ) ⟨a, hD.mem_of_mem ha⟩ = _
    rw [powOp_apply]
    congr 1
  · rw [dadeMap_eq_zero_of_notMem hD _ hx,
      dadeMap_eq_zero_of_notMem hD f
        (fun h => hx ((hD.pow_mem_totalDadeSupport_iff hA hk1 hk).1 h))]

theorem dadeMap_powOp_apply [Finite G] (hD : IsDadeData L A H) (hA : IsCoprimePowerStable A)
    (hk1 : 1 ≤ k) (hk : Nat.Coprime k (Nat.card G)) (f : dadeDomain L A) (x : G) :
    ((dadeMap hD ⟨powOp k (f : ↥L → ℂ), powOp_mem_dadeDomain hA hk1 hk f.2⟩ :
        classFun G) : G → ℂ) x
      = ((dadeMap hD f : classFun G) : G → ℂ) (x ^ k) := by
  have h := congrFun (dadeMap_powOp hD hA hk1 hk f) x
  rwa [powOp_apply] at h

end CFSG.FeitThompson
