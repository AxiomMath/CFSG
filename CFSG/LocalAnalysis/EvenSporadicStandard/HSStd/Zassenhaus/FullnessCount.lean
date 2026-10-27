module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ClassCount

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

section General

variable {G : Type*} [Group G]

theorem two_mul_card_le_of_exists [Finite G] {K C : Subgroup G} (h : K ≤ C)
    (hne : ∃ c ∈ C, c ∉ K) : 2 * Nat.card K ≤ Nat.card C := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h
  have hC : 0 < Nat.card C := Nat.card_pos
  have hK : 0 < Nat.card K := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    obtain ⟨c, hcC, hcK⟩ := hne
    have : K = C := Subgroup.eq_of_le_of_card_ge h (by rw [hk, mul_one])
    exact hcK (this ▸ hcC)
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  calc 2 * Nat.card K ≤ k * Nat.card K := Nat.mul_le_mul_right _ hk2
    _ = Nat.card K * k := mul_comm _ _

theorem card_centralizer_le_card_ker_mul {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (f : H →* K) (h : H) :
    Nat.card (centralizer ({h} : Set H)) ≤
      Nat.card f.ker * Nat.card (centralizer ({f h} : Set K) ⊓ f.range : Subgroup K) := by
  let g : centralizer ({h} : Set H) →* (centralizer ({f h} : Set K) ⊓ f.range : Subgroup K) :=
    (f.comp (centralizer ({h} : Set H)).subtype).codRestrict
      (centralizer ({f h} : Set K) ⊓ f.range : Subgroup K) (by
        intro x
        refine ⟨?_, ⟨x.1, rfl⟩⟩
        show f x ∈ centralizer ({f h} : Set K)
        rw [mem_centralizer_singleton_iff]
        have hx : (x : H) * h = h * (x : H) := mem_centralizer_singleton_iff.mp x.2
        show f x * f h = f h * f x
        rw [← map_mul, ← map_mul, hx])
  have h1 : Nat.card g.ker * Nat.card g.range = Nat.card (centralizer ({h} : Set H)) :=
    Subgroup.card_ker_mul_card_range g
  have h2 : Nat.card g.range ≤
      Nat.card (centralizer ({f h} : Set K) ⊓ f.range : Subgroup K) :=
    Subgroup.card_le_card_group _
  have h3 : Nat.card g.ker ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : H), ?_⟩ : f.ker)) ?_
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h' := congrArg Subtype.val this
      exact h'
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
  rw [← h1]
  exact Nat.mul_le_mul h3 h2

@[expose] def subgroupConjClass (P : Subgroup G) (p : P) : Set G :=
  (Subtype.val : P → G) '' {x : P | IsConj p x}

theorem ncard_subgroupConjClass_mul_card_centralizer [Finite G] (P : Subgroup G) (p : P) :
    (subgroupConjClass P p).ncard * Nat.card (centralizer ({p} : Set P)) = Nat.card P := by
  rw [subgroupConjClass, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact ncard_isConj_mul_card_centralizer p

theorem disjoint_subgroupConjClass (P : Subgroup G) {p q : P} (h : ¬ IsConj p q) :
    Disjoint (subgroupConjClass P p) (subgroupConjClass P q) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have : y = x := Subtype.val_injective hyx
  subst this
  exact h (hx.trans hy.symm)

theorem two_classes [Finite G] {P : Subgroup G} {t : G} (htP : t ∈ P) (x : P)
    (hxc : IsConj t (t * (x : G)))
    (hnc : ¬ IsConj (⟨t, htP⟩ : P) (⟨t, htP⟩ * x)) :
    ∃ c₁ c₂ : ℕ, c₁ + c₂ ≤ {g : G | IsConj t g ∧ g ∈ P}.ncard ∧
      c₁ * Nat.card (centralizer ({(⟨t, htP⟩ : P)} : Set P)) = Nat.card P ∧
      c₂ * Nat.card (centralizer ({(⟨t, htP⟩ : P) * x} : Set P)) = Nat.card P := by
  refine ⟨(subgroupConjClass P ⟨t, htP⟩).ncard, (subgroupConjClass P (⟨t, htP⟩ * x)).ncard,
    ?_, ncard_subgroupConjClass_mul_card_centralizer P (⟨t, htP⟩ : P),
    ncard_subgroupConjClass_mul_card_centralizer P ((⟨t, htP⟩ : P) * x)⟩
  rw [← Set.ncard_union_eq (disjoint_subgroupConjClass P hnc) (Set.toFinite _) (Set.toFinite _)]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact ⟨MonoidHom.map_isConj P.subtype hy, y.2⟩
  · exact ⟨hxc.trans (MonoidHom.map_isConj P.subtype hy), y.2⟩

end General

section Main

variable {A : Type*} [Group A]

instance [Finite A] : Finite (Wr2 A) :=
  Finite.of_equiv _ (SemidirectProduct.equivProd : Wr2 A ≃ (A × A) × Multiplicative (ZMod 2)).symm

@[expose] def baseLeftHom : A →* Wr2 A :=
  (SemidirectProduct.inl : A × A →* Wr2 A).comp (MonoidHom.inl A A)

theorem base_mem_of_conj_tau {R : Subgroup (Wr2 A)} (ht : (tau : Wr2 A) ∈ R)
    (hdiag : ∀ d : A, base d d ∈ R) {a : A} {w : Wr2 A} (hw : w ∈ R)
    (h : w * tau * w⁻¹ = base a a * tau) : base a 1 ∈ R := by
  rcases eq_base_or_eq_base_mul_tau w with ⟨c, d, rfl⟩ | ⟨c, d, rfl⟩
  · rw [conj_base_tau, base_mul_tau_inj] at h
    have hcd : c * d⁻¹ = a := h.1.symm ▸ rfl
    have : base a 1 = base c d * (base d d)⁻¹ := by
      rw [base_inv, base_mul_base, ← hcd]
      simp
    rw [this]
    exact R.mul_mem hw (R.inv_mem (hdiag d))
  · have hb : base c d ∈ R := by
      have := R.mul_mem hw (R.inv_mem ht)
      rwa [mul_assoc, tau_inv, tau_mul_tau, mul_one] at this
    have h' : base c d * tau * (base c d)⁻¹ = base a a * tau := by
      rw [← h, mul_inv_rev, tau_inv]
      simp only [mul_assoc, tau_mul_tau, mul_one]
    rw [conj_base_tau, base_mul_tau_inj] at h'
    have hcd : c * d⁻¹ = a := h'.1
    have : base a 1 = base c d * (base d d)⁻¹ := by
      rw [base_inv, base_mul_base, ← hcd]
      simp
    rw [this]
    exact R.mul_mem hb (R.inv_mem (hdiag d))

theorem range_eq_top_of_conj_count {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {P : Subgroup G} {t : G} (htP : t ∈ P) (ρ : ↥P →* Wreath.Wr2 A)
    (hρt : ρ ⟨t, htP⟩ = Wreath.tau)
    (hker : Nat.card ρ.ker ≤ 4)
    (hA : Nat.card A = 1440)
    (hCA : ∀ a : A, a * a = 1 → a ≠ 1 → Nat.card (Subgroup.centralizer ({a} : Set A)) ≤ 48)
    (hgen : Subgroup.closure {a : A | a * a = 1} = ⊤)
    (hdiag : ∀ d : A, Wreath.base d d ∈ ρ.range)
    (hCt : Nat.card (Subgroup.centralizer ({(⟨t, htP⟩ : ↥P)} : Set ↥P)) ≤ 5760)
    (hx : ∀ a : A, a * a = 1 → a ≠ 1 → ∃ x : ↥P, IsConj t (t * (x : G)) ∧
        (ρ x = Wreath.base a a ∨ ρ x = Wreath.base a a * Wreath.tau))
    (hUB : {g : G | IsConj t g ∧ g ∈ P}.ncard * 3840 < Nat.card P) :
    ρ.range = ⊤ := by
  have htR : (tau : Wr2 A) ∈ ρ.range := ⟨⟨t, htP⟩, hρt⟩
  let T : Subgroup A := ρ.range.comap baseLeftHom
  have hmemT : ∀ a : A, a ∈ T ↔ base a 1 ∈ ρ.range := fun a => Iff.rfl
  have hinvol : ∀ a : A, a * a = 1 → a ∈ T := by
    intro a ha
    by_cases ha1 : a = 1
    · subst ha1; exact T.one_mem
    obtain ⟨x, hxc, hxρ⟩ := hx a ha ha1
    have hCa := hCA a ha ha1
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hsx : ρ (⟨t, htP⟩ * x) = tau * ρ x := by rw [map_mul, hρt]
    have hbound := card_centralizer_le_card_ker_mul ρ (⟨t, htP⟩ * x)
    rcases hxρ with h1 | h2
    ·
      by_cases hc : IsConj (⟨t, htP⟩ : P) (⟨t, htP⟩ * x)
      · obtain ⟨c, hc⟩ := isConj_iff.mp hc
        have h := congrArg ρ hc
        rw [map_mul, map_mul, map_inv, hρt, map_mul, hρt, h1, tau_mul_base] at h
        exact base_mem_of_conj_tau htR hdiag ⟨c, rfl⟩ h
      · obtain ⟨c₁, c₂, hle, hc₁, hc₂⟩ := two_classes htP x hxc hc
        exfalso
        rw [hsx, h1, tau_mul_base] at hbound
        have hcen : Nat.card (centralizer ({base a a * tau} : Set (Wr2 A)) ⊓ ρ.range :
            Subgroup (Wr2 A)) ≤ 2880 := by
          refine (Subgroup.card_le_of_le inf_le_left).trans ?_
          rw [card_centralizer_base_mul_tau, ha]
          have : centralizer ({(1 : A)} : Set A) = ⊤ := by
            rw [eq_top_iff]; intro y _; rw [mem_centralizer_singleton_iff]; simp
          rw [this, Subgroup.card_top, hA]
        have hC2 : Nat.card (centralizer ({(⟨t, htP⟩ : P) * x} : Set P)) ≤ 11520 := by
          calc _ ≤ _ := hbound
            _ ≤ 4 * 2880 := Nat.mul_le_mul hker hcen
        have e1 : Nat.card P ≤ c₁ * 5760 := by
          rw [← hc₁]; exact Nat.mul_le_mul_left _ hCt
        have e2 : Nat.card P ≤ c₂ * 11520 := by
          rw [← hc₂]; exact Nat.mul_le_mul_left _ hC2
        omega
    ·
      by_contra haT
      have hss' : (tau : Wr2 A) * (base a a * tau) = base a a := by
        rw [← mul_assoc, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
      have hcls : ¬ IsConj (⟨t, htP⟩ : P) (⟨t, htP⟩ * x) := by
        intro hc
        have := ρ.map_isConj hc
        rw [hsx, h2, hρt, hss'] at this
        exact not_isConj_base_tau a a 1 1 (by rw [base_one, one_mul]; exact this.symm)
      obtain ⟨c₁, c₂, hle, hc₁, hc₂⟩ := two_classes htP x hxc hcls
      have hss : ρ (⟨t, htP⟩ * x) = base a a := by
        rw [hsx, h2, hss']
      rw [hss] at hbound
      have hcen : Nat.card (centralizer ({base a a} : Set (Wr2 A)) ⊓ ρ.range :
          Subgroup (Wr2 A)) ≤ 2304 := by
        have h2le := two_mul_card_le_of_exists
          (K := centralizer ({base a a} : Set (Wr2 A)) ⊓ ρ.range)
          (C := centralizer ({base a a} : Set (Wr2 A))) inf_le_left
          ⟨base a 1, base_mem_centralizer_base_self a, fun h => haT h.2⟩
        rw [card_centralizer_base_self] at h2le
        have : Nat.card (centralizer ({a} : Set A)) ^ 2 ≤ 48 ^ 2 := Nat.pow_le_pow_left hCa 2
        omega
      have hC2 : Nat.card (centralizer ({(⟨t, htP⟩ : P) * x} : Set P)) ≤ 9216 := by
        calc _ ≤ _ := hbound
          _ ≤ 4 * 2304 := Nat.mul_le_mul hker hcen
      have e1 : Nat.card P ≤ c₁ * 5760 := by
        rw [← hc₁]; exact Nat.mul_le_mul_left _ hCt
      have e2 : Nat.card P ≤ c₂ * 9216 := by
        rw [← hc₂]; exact Nat.mul_le_mul_left _ hC2
      omega
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le T).mpr hinvol
  exact eq_top_of_tau_mem_of_base_mem htR (fun a => (hmemT a).mp (hT ▸ Subgroup.mem_top a))

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
