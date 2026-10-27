module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public noncomputable section

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem subsingleton_outer_of_inner (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) :
    Subsingleton (Outer G) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H α =>
    induction b using QuotientGroup.induction_on with
    | H β =>
      rw [QuotientGroup.eq]
      obtain ⟨g, hg⟩ := h (α⁻¹ * β)
      exact ⟨g, hg.symm⟩

theorem isSolvable_outer_of_inner (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) :
    Group.IsSolvable (Outer G) := by
  have := subsingleton_outer_of_inner h
  infer_instance

@[expose] def quotKerAut {J : Type*} [Group J] (E : Subgroup J) : Subgroup (MulAut J) where
  carrier := {α | ∀ j : J, (QuotientGroup.mk (α j) : J ⧸ E) = QuotientGroup.mk j}
  mul_mem' {α β} hα hβ j := (hα (β j)).trans (hβ j)
  one_mem' _ := rfl
  inv_mem' {α} hα j := by
    have h := hα (α⁻¹ j)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

theorem quotKerAut_of_inner {J : Type*} [Group J] {E : Subgroup J} [E.Normal]
    (hE : IsPGroup 2 E) (hZ : Subgroup.center (J ⧸ E) = ⊥)
    (h : ∀ α : MulAut J, ∃ g : J, α = MulAut.conj g) :
    (∀ α : MulAut J, ∃ g : J, ∃ r ∈ quotKerAut E, α = MulAut.conj g * r) ∧
      ∃ F : Subgroup (quotKerAut E), ∃ _ : F.Normal, IsPGroup 2 F ∧
        IsPGroup 3 (quotKerAut E ⧸ F) := by
  refine ⟨fun α => ?_, ⊤, inferInstance, ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := h α
    exact ⟨g, 1, Subgroup.one_mem _, (mul_one _).symm⟩
  ·
    rintro ⟨⟨r, hr⟩, -⟩
    obtain ⟨g, rfl⟩ := h r
    have hgZ : (QuotientGroup.mk g : J ⧸ E) ∈ Subgroup.center (J ⧸ E) := by
      rw [Subgroup.mem_center_iff]
      intro c
      induction c using QuotientGroup.induction_on with
      | H j =>
        have h1 := hr j
        rw [MulAut.conj_apply] at h1
        have h2 : (QuotientGroup.mk g : J ⧸ E) * QuotientGroup.mk j * (QuotientGroup.mk g)⁻¹ =
            QuotientGroup.mk j := h1
        calc (QuotientGroup.mk j : J ⧸ E) * QuotientGroup.mk g
            = QuotientGroup.mk g * QuotientGroup.mk j * (QuotientGroup.mk g)⁻¹ *
              QuotientGroup.mk g := by rw [h2]
          _ = QuotientGroup.mk g * QuotientGroup.mk j := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hgZ
    obtain ⟨k, hk⟩ := hE ⟨g, hgZ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, Subgroup.coe_one, ← map_pow, hk', map_one]
  · exact IsPGroup.of_card (n := 0) (by
      rw [pow_zero, Nat.card_eq_one_iff_unique]
      exact ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩)

theorem inner_of_equiv {T S : Type*} [Group T] [Group S] (e : T ≃* S)
    (h : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g) :
    ∀ α : MulAut T, ∃ g : T, α = MulAut.conj g := by
  intro α
  obtain ⟨s, hs⟩ := h ((e.symm.trans α).trans e)
  refine ⟨e.symm s, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun β : MulAut S => e.symm (β (e t))) hs
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem isSolvable_outer_of_mulEquiv {T S : Type*} [Group T] [Group S] (e : T ≃* S)
    (h : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g) : Group.IsSolvable (Outer T) :=
  isSolvable_outer_of_inner (inner_of_equiv e h)

theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (h : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem bijective_of_surjective_of_isSimpleGroup {F H : Type*} [Group F] [IsSimpleGroup F]
    [Group H] (f : F →* H) (hs : Function.Surjective f) (hne : ∃ x, f x ≠ 1) :
    Function.Bijective f := by
  refine ⟨?_, hs⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff f).1 h
  · exfalso
    obtain ⟨x, hx⟩ := hne
    exact hx (f.mem_ker.1 (h ▸ Subgroup.mem_top x))

theorem centralizer_sup_centralizer_conj_eq_top {x t : G}
    (hgen : Subgroup.closure ((Subgroup.centralizer ({x} : Set G) : Set G) ∪ {t}) = ⊤)
    {h : G} (hh : h ∈ Subgroup.centralizer ({x} : Set G)) (ht : h * (t * h * t⁻¹) = t) :
    Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({t * x * t⁻¹} : Set G) = ⊤ := by
  have hconj : t * h * t⁻¹ ∈ Subgroup.centralizer ({t * x * t⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    calc t * h * t⁻¹ * (t * x * t⁻¹) = t * (h * x) * t⁻¹ := by group
      _ = t * (x * h) * t⁻¹ := by rw [hh]
      _ = t * x * t⁻¹ * (t * h * t⁻¹) := by group
  have htmem : t ∈ Subgroup.centralizer ({x} : Set G) ⊔
      Subgroup.centralizer ({t * x * t⁻¹} : Set G) := by
    have hm := Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hconj)
    rwa [ht] at hm
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro g (hg | hg)
  · exact Subgroup.mem_sup_left hg
  · rw [Set.mem_singleton_iff.1 hg]
    exact htmem

theorem oddCore_eq_bot_of_selfCentralizing [Finite G] {R : Subgroup G} [R.Normal]
    (hR : IsPGroup 2 R) (hRc : Subgroup.centralizer (R : Set G) ≤ R) : CFSG.oddCore G = ⊥ := by
  set N := CFSG.oddCore G
  have hNodd : Odd (Nat.card N) := UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have hinf : N ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgN, hgR⟩
    obtain ⟨k, hk⟩ := hR ⟨g, hgR⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf g) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hgN)
    have hdvd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj] at hodd
      exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' hj0).2 even_two)
    have h1 : orderOf g = 1 := by rw [hj, hj0, pow_zero]
    exact (Subgroup.mem_bot).2 (orderOf_eq_one_iff.1 h1)
  have hc : ⁅N, R⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_le_inf N R).trans hinf.le)
  have hNR : N ≤ R := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans hRc
  exact le_bot_iff.1 ((le_inf le_rfl hNR).trans hinf.le)

theorem oddCore_eq_bot_of_quotient_monolith [Finite G] {Z : Subgroup G} [Z.Normal]
    (hZ : Nat.card Z = 2) {S : Subgroup (G ⧸ Z)} (hS : Even (Nat.card S))
    (hmono : ∀ N : Subgroup (G ⧸ Z), N.Normal → N ≠ ⊥ → S ≤ N) : CFSG.oddCore G = ⊥ := by
  set N := CFSG.oddCore G
  have hNodd : Odd (Nat.card N) := UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have hmapN : (N.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
  have hmap : N.map (QuotientGroup.mk' Z) = ⊥ := by
    by_contra hne
    have hSN := hmono _ hmapN hne
    have h1 : Nat.card S ∣ Nat.card (N.map (QuotientGroup.mk' Z)) :=
      Subgroup.card_dvd_of_le hSN
    have h2 : Nat.card (N.map (QuotientGroup.mk' Z)) ∣ Nat.card N := Subgroup.card_map_dvd _ _
    exact Nat.not_even_iff_odd.2 (hNodd.of_dvd_nat (h1.trans h2)) hS
  have hNZ : N ≤ Z := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  have hdvd : Nat.card N ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hNZ
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · rw [h2] at hNodd
    exact absurd hNodd (by decide)

end CFSG.ComponentClassification.BMCase
