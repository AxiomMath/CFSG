module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34Unitary
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34Lift
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34Group
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.Foote5.L34Real CFSG.ComponentClassification.Foote5.L34Group
open scoped commutatorElement

theorem isSimpleGroup_S : IsSimpleGroup S := by
  have := CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3)
    (K := F4) (by norm_num)
  exact theta.symm.isSimpleGroup

theorem commutator_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases (commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), ⊤⁆ := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · rw [_root_.commutator_def]
    exact h

theorem eq_bot_of_normalized {N C : Subgroup (Equiv.Perm (Fin 42))} [hC : IsSimpleGroup C]
    (heven : Even (Nat.card C)) (hNC : N ≤ C) (hodd : Odd (Nat.card N))
    (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N = ⊥ := by
  have hnormal : (N.subgroupOf C).Normal :=
    ⟨fun n hn c => by
      rw [Subgroup.mem_subgroupOf]
      push_cast
      exact hnorm _ c.2 _ hn⟩
  rcases hnormal.eq_bot_or_eq_top with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNC hx⟩ : C) ∈ N.subgroupOf C := hx
    rw [h, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hCN : C ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : C) ∈ N.subgroupOf C := h ▸ mem_top _
      exact this
    have heq : N = C := le_antisymm hNC hCN
    rw [heq] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven

variable {Y₀ : Type} [Group Y₀] [Finite Y₀]

theorem realHom_commute
    (hperf : commutator Y₀ = ⊤) {q : Y₀ →* Equiv.Perm (Fin 42)} (hqS : ∀ y, q y ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ y, q y = s) (hqker : q.ker = center Y₀)
    {ψ : MulAut Y₀ →* Equiv.Perm (Fin 42)} (hψR : ∀ β, ψ β ∈ R)
    (hψ : ∀ β y, q (β y) = ψ β * q y * (ψ β)⁻¹) {α : MulAut Y₀} (hα : ∀ y, α (α y) = y)
    {A : Subgroup (MulAut Y₀)} (hAodd : Odd (Nat.card A))
    (hAcomm : ∀ β ∈ A, β * α = α * β)
    (hAconj : ∀ c : Y₀, α c = c → ∀ β ∈ A, MulAut.conj c * β * (MulAut.conj c)⁻¹ ∈ A)
    (hAZ : ∀ β ∈ A, ∀ z ∈ center Y₀, α z = z → (∃ k : ℕ, orderOf z = 2 ^ k) → β z = z)
    (hρ : ψ α = 1 ∨ ψ α = r₁ ∨ ψ α = r₂ ∨ ψ α = r₃ ∨ ψ α = r₄) {β₁ β₂ : MulAut Y₀}
    (hβ₁ : β₁ ∈ A) (hβ₂ : β₂ ∈ A) : ψ β₁ * ψ β₂ = ψ β₂ * ψ β₁ := by
  set Â := A.map ψ with hÂdef
  have hÂR : Â ≤ R := by
    rintro _ ⟨β, -, rfl⟩
    exact hψR β
  have hÂodd : Odd (Nat.card Â) := Odd.of_dvd_nat hAodd (card_map_dvd _ _)
  have hÂρ : ∀ x ∈ Â, x * ψ α = ψ α * x := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [← map_mul, ← map_mul, hAcomm β hβ]
  have hÂnorm : ∀ c : Y₀, α c = c → ∀ x ∈ Â, q c * x * (q c)⁻¹ ∈ Â := by
    rintro c hc _ ⟨β, hβ, rfl⟩
    refine ⟨_, hAconj c hc β hβ, ?_⟩
    rw [map_mul, map_mul, map_inv, realHom_conj hqS hqsurj hψR hψ c]
  have hÂSodd : Odd (Nat.card ↥(Â ⊓ S)) :=
    Odd.of_dvd_nat hÂodd (card_dvd_of_le inf_le_left)
  have hmem₁ : ψ β₁ ∈ Â := mem_map_of_mem _ hβ₁
  have hmem₂ : ψ β₂ ∈ Â := mem_map_of_mem _ hβ₂
  have hfin : Â ⊓ S = ⊥ → ψ β₁ * ψ β₂ = ψ β₂ * ψ β₁ := fun h => by
    have hdvd := card_dvd_three_mul hÂR hÂodd
    rw [h, card_bot, mul_one] at hdvd
    exact commute_of_card_dvd_three hdvd hmem₁ hmem₂
  have hcent : ∀ {r : Equiv.Perm (Fin 42)}, ψ α = r →
      Â ⊓ S ≤ Subgroup.centralizer {r} ⊓ S := fun hr x hx => by
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, (mem_inf.mp hx).2⟩
    rw [← hr]
    exact hÂρ x (mem_inf.mp hx).1
  have hnormF : ∀ c ∈ (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y₀)).map q,
      ∀ n ∈ Â ⊓ S, c * n * c⁻¹ ∈ Â ⊓ S := by
    rintro _ ⟨c, hc, rfl⟩ n hn
    exact mem_inf.mpr ⟨hÂnorm c hc n (mem_inf.mp hn).1,
      mul_mem (mul_mem (hqS c) (mem_inf.mp hn).2) (inv_mem (hqS c))⟩
  rcases hρ with h1 | h1 | h2 | h3 | h4
  ·
    apply hfin
    have hα1 : α = 1 := eq_one_of_realHom_eq_one hperf hqker hψ h1
    have := isSimpleGroup_S
    refine eq_bot_of_normalized (C := S) (by rw [card_S]; decide) inf_le_right hÂSodd
      fun c hc n hn => ?_
    obtain ⟨c', rfl⟩ := hqsurj c hc
    exact hnormF _ ⟨c', by change α c' = c'; rw [hα1]; rfl, rfl⟩ n hn
  ·
    apply hfin
    have hle : Â ⊓ S ≤ C₁ := hcent h1
    have h64 : Nat.card ↥(Â ⊓ S) ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = Nat.card C₁ by rw [card_C₁]; norm_num]
      exact card_dvd_of_le hle
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h64
    have hi0 : i = 0 := by
      by_contra hi0
      rw [hi] at hÂSodd
      exact (Nat.not_even_iff_odd.mpr hÂSodd) ((Nat.even_pow' hi0).mpr even_two)
    rw [hi0, pow_zero] at hi
    exact card_eq_one.mp hi
  ·
    apply hfin
    have := isSimpleGroup_C₂
    have hF := le_map_fixed_of_perfect hqsurj hqker hψ α (C := C₂) (by rw [h2]; exact le_rfl)
      (commutator_eq_top_of_simple exists_mul_ne_C₂)
    exact eq_bot_of_normalized (C := C₂) (by rw [card_C₂]; decide) (hcent h2) hÂSodd
      fun c hc n hn => hnormF c (hF hc) n hn
  ·
    apply hfin
    have := isSimpleGroup_C₃
    have hF := le_map_fixed_of_perfect hqsurj hqker hψ α (C := C₃) (by rw [h3]; exact le_rfl)
      (commutator_eq_top_of_simple exists_mul_ne_C₃)
    exact eq_bot_of_normalized (C := C₃) (by rw [card_C₃]; decide) (hcent h3) hÂSodd
      fun c hc n hn => hnormF c (hF hc) n hn
  ·
    have hÂSD : Â ⊓ S ≤ ambientDerived C₄ 2 := le_derived_of_odd (hcent h4) hÂSodd
    have hÂS : Â ≤ S := by
      intro x hxÂ
      by_contra hxS
      obtain ⟨β, hβ, rfl⟩ := hxÂ
      have hβodd : Odd (orderOf β) := by
        have h := orderOf_dvd_natCard (⟨β, hβ⟩ : A)
        rw [Subgroup.orderOf_mk] at h
        exact Odd.of_dvd_nat hAodd h
      have hxodd : Odd (orderOf (ψ β)) := Odd.of_dvd_nat hβodd (orderOf_map_dvd ψ β)
      have hx945 : ψ β ^ 945 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        have hdvd : orderOf (ψ β) ∣ 2 ^ 8 * 945 := by
          have h := orderOf_dvd_natCard (⟨ψ β, hψR β⟩ : R)
          rwa [card_R, Subgroup.orderOf_mk] at h
        have hcop : Nat.Coprime (orderOf (ψ β)) (2 ^ 8) :=
          Nat.Coprime.pow_right 8 (Nat.coprime_two_left.mpr hxodd).symm
        exact hcop.dvd_of_dvd_mul_left hdvd
      have hxr : ψ β * r₄ = r₄ * ψ β := by
        rw [← h4]
        exact hÂρ _ (mem_map_of_mem _ hβ)
      obtain ⟨s, hs, hs8, hw⟩ := L34Unitary.exists_w_not_mem (hψR β) hxr hxS hx945
      have hsα : ψ α * s = s * ψ α := by
        rw [h4]
        exact (mem_centralizer_singleton_iff.mp (mem_inf.mp hs).1).symm
      obtain ⟨c, hc, hct⟩ := conj_comm_mem_map_fixed hqsurj hqker hψ hα (hAcomm β hβ) hβodd
        (hAZ β hβ) (mem_inf.mp hs).2 hsα hs8
      apply hw
      apply hÂSD
      set x := ψ β
      set t := s⁻¹ * x * s * x⁻¹ with htdef
      have htS : t ∈ S := by
        rw [← hct]
        exact hqS c
      have hxR : x ∈ R := hψR β
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : t * x * t⁻¹ ∈ Â := by
          rw [← hct]
          exact hÂnorm c hc x (mem_map_of_mem _ hβ)
        have h2 : x⁻¹ ∈ Â := inv_mem (mem_map_of_mem _ hβ)
        rw [show x⁻¹ * t * x * t⁻¹ = x⁻¹ * (t * x * t⁻¹) by group]
        exact mul_mem h2 h1
      · have h1 : x⁻¹ * t * x⁻¹⁻¹ ∈ S := conj_mem_S (R.inv_mem hxR) htS
        rw [inv_inv] at h1
        exact mul_mem h1 (inv_mem htS)
    have hÂD : Â ≤ ambientDerived C₄ 2 := fun x hx => hÂSD (mem_inf.mpr ⟨hx, hÂS hx⟩)
    exact commute_of_mem_derived (hÂD hmem₁) (hÂD hmem₂)

theorem footeCoreL34Input_holds :
    FooteCoreL34Input := by
  intro Y₀ _ _ hperf hm α hα A hAodd hAcomm hAconj hAZ β₁ hβ₁ β₂ hβ₂ y
  have hperf' : commutator Y₀ = ⊤ := hperf.commutator_eq_top
  obtain ⟨q, hqS, hqsurj, hqker⟩ := exists_frame hm
  obtain ⟨ψ, hψR, hψ⟩ := exists_realHom hqS hqsurj hqker
  have hαα : α * α = 1 := MulEquiv.ext fun y => hα y
  have hρ2 : ψ α * ψ α = 1 := by rw [← map_mul, hαα, map_one]
  by_cases hρ1 : ψ α = 1
  · exact mem_center_of_commute hqker hψ (realHom_commute hperf' hqS hqsurj hqker hψR hψ hα
      hAodd hAcomm hAconj hAZ (Or.inl hρ1) hβ₁ hβ₂) y
  have hord : orderOf (⟨ψ α, hψR α⟩ : R) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hρ1 (congrArg Subtype.val h)
    simp only [OneMemClass.coe_one, pow_two]
    exact hρ2
  obtain ⟨i, r, hri, hconj⟩ : ∃ i : Fin 4, ∃ r : R,
      (r : Equiv.Perm (Fin 42)) = ![r₁, r₂, r₃, r₄] i ∧ IsConj (⟨ψ α, hψR α⟩ : R) r := by
    rcases (orderOf_eq_two_iff _).mp hord with h | h | h | h
    · exact ⟨0, r₁R, rfl, h⟩
    · exact ⟨1, r₂R, rfl, h⟩
    · exact ⟨2, r₃R, rfl, h⟩
    · exact ⟨3, r₄R, rfl, h⟩
  obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj hconj
  obtain ⟨hqS', hqsurj', hqker'⟩ := conj_frame hqS hqsurj hqker hcR
  obtain ⟨ψ', hψR', hψ'⟩ := exists_realHom hqS' hqsurj' hqker'
  have hψα : ψ' α = r := by
    refine GrSLit.GrS4.realization_unique hqsurj' (hψR' α) (r.2) (hψ' α) fun e => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      hψ α e]
    change c⁻¹ * (ψ α * q e * (ψ α)⁻¹) * c =
      (r : Equiv.Perm (Fin 42)) * (c⁻¹ * q e * c) * (r : Equiv.Perm (Fin 42))⁻¹
    rw [show (ψ α) = c * r * c⁻¹ from hc]
    group
  have hρ' : ψ' α = 1 ∨ ψ' α = r₁ ∨ ψ' α = r₂ ∨ ψ' α = r₃ ∨ ψ' α = r₄ := by
    rw [hψα, hri]
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  exact mem_center_of_commute hqker' hψ' (realHom_commute hperf' hqS' hqsurj' hqker' hψR' hψ'
    hα hAodd hAcomm hAconj hAZ hρ' hβ₁ hβ₂) y

end CFSG.ComponentClassification.Foote5
