module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
public import CFSG.Quasithin.Background.B1More8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

theorem eq_one_of_commute_alt {n : ℕ} (h4 : 4 ≤ n) {π : Perm (Fin n)}
    (h : ∀ σ ∈ alternatingGroup (Fin n), π * σ = σ * π) : π = 1 := by
  classical
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  set j := π i with hj
  have hji : j ≠ i := hne
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hcard' : ({i, j, k} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j, k} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  have hjk : j ≠ k := fun h => hk.2 h.symm
  have hkl : k ≠ l := fun h => hl.2.2 h.symm
  have hjl : j ≠ l := fun h => hl.2.1 h.symm
  have hτ : Equiv.swap j k * Equiv.swap k l ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hjk,
      Equiv.Perm.sign_swap hkl]
    decide
  have h1 := congrArg (fun f : Equiv.Perm (Fin n) => f i) (h _ hτ)
  simp only [Equiv.Perm.mul_apply] at h1
  have hτi : Equiv.swap k l i = i := Equiv.swap_apply_of_ne_of_ne (fun h => hk.1 h.symm)
    (fun h => hl.1 h.symm)
  have hτi' : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne (Ne.symm hji)
    (fun h => hk.1 h.symm)
  rw [hτi, hτi', ← hj] at h1
  have hτj : Equiv.swap j k (Equiv.swap k l j) = k := by
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, Equiv.swap_apply_left]
  rw [hτj] at h1
  exact hjk h1

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem eq_one_of_commute_altPre (h4 : 4 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {h : MulAut V} (hh : h ∈ H)
    (hc : ∀ l ∈ altPre ψ, h * l = l * h) : h = 1 := by
  have hπ : ψ ⟨h, hh⟩ = 1 := by
    refine eq_one_of_commute_alt h4 fun σ hσ => ?_
    obtain ⟨x, rfl⟩ := hA hσ
    have hx : (x : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 hσ
    have hcx : (⟨h, hh⟩ : ↥H) * x = x * ⟨h, hh⟩ := Subtype.ext (hc _ hx)
    rw [← map_mul, ← map_mul, hcx]
  have h1 : (⟨h, hh⟩ : ↥H) = 1 := hψ (hπ.trans (map_one ψ).symm)
  exact congrArg Subtype.val h1

@[expose] noncomputable def altPreEquiv (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) : ↥(altPre ψ) ≃* alternatingGroup (Fin n) :=
  MulEquiv.ofBijective (altPreHom ψ) ⟨altPreHom_injective hψ, altPreHom_surjective hA⟩

theorem coe_altPreEquiv (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (l : ↥(altPre ψ)) :
    (altPreEquiv hψ hA l : Perm (Fin n)) = ψ (Subgroup.inclusion altPre_le l) :=
  rfl

theorem commutator_altPre_eq_top (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) : commutator ↥(altPre ψ) = ⊤ := by
  have : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)⟩
  exact (Group.IsPerfect.ofSurjective (f := (altPreEquiv hψ hA).symm.toMonoidHom)
    (altPreEquiv hψ hA).symm.surjective).commutator_eq_top

theorem isSimpleGroup_altPre (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) : IsSimpleGroup ↥(altPre ψ) := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact (altPreEquiv hψ hA).isSimpleGroup

theorem exists_isChiefFac_altPre [Finite V] (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {Y : Subgroup V} (hY : H ≤ stabSub Y)
    (hYL : ¬ Y ≤ fixV (altPre ψ)) :
    ∃ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ ∧ Y₁ ≤ Y ∧ ¬ IsCentralSec (altPre ψ) Y₀ Y₁ :=
  exists_isChiefFac_of_perfect (commutator_altPre_eq_top h5 hψ hA) hY hYL

theorem inf_centSec_eq_bot (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (hH₀ : H ≤ stabSub Y₀)
    (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    H ⊓ centSec Y₁ Y₀ = ⊥ := by
  set L := altPre ψ with hLdef
  set K := H ⊓ centSec Y₁ Y₀ with hK
  have hKconj : ∀ g ∈ H, ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun g hg x hx =>
    ⟨H.mul_mem (H.mul_mem hg hx.1) (H.inv_mem hg), conj_mem_centSec (hH₁ hg) (hH₀ hg) hx.2⟩
  have : IsSimpleGroup ↥L := isSimpleGroup_altPre h5 hψ hA
  have hN : (K.subgroupOf L).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.2 (hKconj _ (altPre_le g.2) _
      (Subgroup.mem_subgroupOf.1 hx))⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.subgroupOf L) with hbot | htop
  · rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine eq_one_of_commute_altPre (by omega) hψ hA hk.1 fun l hl => ?_
    have hlH : l ∈ H := altPre_le hl
    have hcL : k * l * k⁻¹ * l⁻¹ ∈ L := L.mul_mem (conj_mem_altPre hk.1 hl) (L.inv_mem hl)
    have hcK : k * l * k⁻¹ * l⁻¹ ∈ K := by
      have h1 := hKconj l hlH k⁻¹ (K.inv_mem hk)
      have h2 := K.mul_mem hk h1
      simpa only [mul_assoc] using h2
    have hc1 : (⟨_, hcL⟩ : ↥L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.2 hcK
    rw [hbot, Subgroup.mem_bot] at hc1
    have hc2 : k * l * k⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hc1
    calc k * l = k * l * k⁻¹ * l⁻¹ * (l * k) := by group
      _ = l * k := by rw [hc2, one_mul]
  · exfalso
    apply hL
    intro l hl y hy
    have hl' : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hl').2.2 y hy

section Consequences

variable {B : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V}

theorem card_autSec_eq_card (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) (hBH : B ≤ H) :
    Nat.card (autSec B Y₁ Y₀) = Nat.card B := by
  have h1 := card_autSec_mul (hBH.trans hH₁) (hBH.trans hH₀)
  have h2 : B ⊓ centSec Y₁ Y₀ = ⊥ := by
    rw [eq_bot_iff, ← inf_centSec_eq_bot h5 hψ hA hH₀ hH₁ hL]
    exact inf_le_inf_right _ hBH
  rw [h2, Subgroup.card_bot, mul_one] at h1
  exact h1

theorem autSec_ne_bot (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) (hBH : B ≤ H) (hB : B ≠ ⊥) :
    autSec B Y₁ Y₀ ≠ ⊥ := by
  intro h
  have h1 := card_autSec_eq_card h5 hψ hA hH₀ hH₁ hL hBH
  rw [h, Subgroup.card_bot] at h1
  exact hB (Subgroup.card_eq_one.1 h1.symm)

theorem one_lt_index_fixV {W : Type*} [CommGroup W] [Finite W] {B : Subgroup (MulAut W)}
    (hB : B ≠ ⊥) : 1 < (fixV B).index := by
  obtain ⟨⟨b, hb⟩, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  have hne : fixV B ≠ ⊤ := by
    intro htop
    apply hb1
    ext w
    have hw : w ∈ fixV B := htop ▸ Subgroup.mem_top w
    exact hw b hb
  have h0 : (fixV B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (fixV B).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  omega

theorem one_lt_index_fixV_autSec [Finite V] (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) (hBH : B ≤ H) (hB : B ≠ ⊥) :
    1 < (fixV (autSec B Y₁ Y₀)).index :=
  one_lt_index_fixV (autSec_ne_bot h5 hψ hA hH₀ hH₁ hL hBH hB)

end Consequences

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
