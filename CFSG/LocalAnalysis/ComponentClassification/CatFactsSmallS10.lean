module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Equiv Subgroup

theorem eq_bot_of_perfect_of_isPGroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {R : Subgroup G} [Finite R] (hR : IsPGroup p R) (hperf : ⁅R, R⁆ = R) : R = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries R).1 hR.isNilpotent
  have : ∀ k, R.lowerCentralSeries k = R := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  rw [← this n, hn]

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_of_involution {τ : Perm α} (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    τ.cycleType = Multiset.replicate (τ.support.card / 2) 2 ∧ τ.support.card % 2 = 0 ∧
      0 < τ.support.card := by
  have ho : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two, hτ]) hτ1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hs : τ.support.card = 2 * (n + 1) := by
    rw [← Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  refine ⟨?_, by omega, by omega⟩
  rw [hn, hs]
  congr 1
  omega

theorem card_centralizer_involution {τ : Perm α} (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    Nat.card (centralizer {τ}) = (Fintype.card α - τ.support.card).factorial *
      2 ^ (τ.support.card / 2) * (τ.support.card / 2).factorial := by
  obtain ⟨hc, hpar, hpos⟩ := cycleType_of_involution hτ hτ1
  have hne : τ.support.card / 2 ≠ 0 := by omega
  rw [Perm.nat_card_centralizer, hc, Multiset.sum_replicate, Multiset.prod_replicate,
    Multiset.toFinset_replicate]
  simp only [hne, ↓reduceIte, Finset.prod_singleton, Multiset.count_replicate_self, smul_eq_mul]
  congr 3
  omega

theorem card_fix_inter_modEq {g h : Perm α} (hgh : g * h = h * g) {p n : ℕ} [Fact p.Prime]
    (hh : h ^ p ^ n = 1) :
    (g.supportᶜ ∩ h.supportᶜ).card ≡ (g.supportᶜ).card [MOD p] := by
  have hF : ∀ x, h x ∈ g.supportᶜ ↔ x ∈ g.supportᶜ := by
    intro x
    simp only [Finset.mem_compl, Perm.mem_support, not_not]
    constructor
    · intro hx
      apply h.injective
      rw [← Perm.mul_apply, ← hgh, Perm.mul_apply, hx]
    · intro hx
      rw [← Perm.mul_apply, hgh, Perm.mul_apply, hx]
  have hh' : (h.subtypePerm hF) ^ p ^ n = 1 := by
    rw [Perm.subtypePerm_pow]
    ext x
    simp [hh]
  have key := Perm.card_compl_support_modEq hh'
  rw [Fintype.card_coe] at key
  have hcard : ((h.subtypePerm hF).supportᶜ).card = (g.supportᶜ ∩ h.supportᶜ).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext x
    simp only [Finset.mem_map, Finset.mem_compl, Perm.mem_support, not_not,
      Function.Embedding.coe_subtype, Finset.mem_inter, Perm.subtypePerm_apply, Subtype.ext_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy2 := y.2
      simp only [Finset.mem_compl, Perm.mem_support, not_not] at hy2
      exact ⟨hy2, hy⟩
    · rintro ⟨hx, hxh⟩
      exact ⟨⟨x, by simpa using hx⟩, hxh, rfl⟩
  rw [← hcard]
  exact key

@[expose] def restrHom (L : Subgroup (Perm α)) (S : Finset α)
    (hS : ∀ l ∈ L, ∀ x, l x ∈ S ↔ x ∈ S) : L →* Perm {x // x ∈ S} where
  toFun l := (l : Perm α).subtypePerm (hS l l.2)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [DecidableEq α] in
theorem fix_of_perfect_of_two_group {L : Subgroup (Perm α)} (hperf : ⁅L, L⁆ = L)
    (S : Finset α) (hS : ∀ l ∈ L, ∀ x, l x ∈ S ↔ x ∈ S)
    (h2 : ∀ l : L, ∃ k : ℕ, restrHom L S hS l ^ 2 ^ k = 1) :
    ∀ l ∈ L, ∀ x ∈ S, l x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := restrHom L S hS
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  have hR2 : IsPGroup 2 r.range := by
    rintro ⟨_, l, rfl⟩
    obtain ⟨k, hk⟩ := h2 l
    exact ⟨k, Subtype.ext hk⟩
  have hRp : ⁅r.range, r.range⁆ = r.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hR := eq_bot_of_perfect_of_isPGroup hR2 hRp
  intro l hl x hx
  have h1 : r ⟨l, hl⟩ = 1 := by
    have : r ⟨l, hl⟩ ∈ r.range := ⟨_, rfl⟩
    rw [hR, mem_bot] at this
    exact this
  have h2 := congrArg (fun σ : Perm {x // x ∈ S} => (σ ⟨x, hx⟩ : α)) h1
  simpa [r, restrHom] using h2

theorem apply_mem_support_iff {τ l : Perm α} (hl : l * τ = τ * l) (x : α) :
    l x ∈ τ.support ↔ x ∈ τ.support := by
  simp only [Perm.mem_support]
  rw [← Perm.mul_apply, ← hl, Perm.mul_apply]
  exact l.injective.ne_iff

theorem fix_support_of_perfect {τ : Perm α} (hτ : τ * τ = 1) (hτ4 : τ.support.card ≤ 4)
    {L : Subgroup (Perm α)} (hperf : ⁅L, L⁆ = L) (hc : ∀ l ∈ L, l * τ = τ * l) :
    ∀ l ∈ L, ∀ x ∈ τ.support, l x = x := by
  by_cases hτ1 : τ = 1
  · intro l _ x hx
    simp [hτ1] at hx
  have hS : ∀ l ∈ L, ∀ x, l x ∈ τ.support ↔ x ∈ τ.support := fun l hl x =>
    apply_mem_support_iff (hc l hl) x
  refine fix_of_perfect_of_two_group hperf τ.support hS fun l => ⟨3, ?_⟩
  set τS := τ.subtypePerm (apply_mem_support_iff (Commute.refl τ).eq) with hτS
  have hτS2 : τS * τS = 1 := by
    ext x
    simp [τS, hτ]
  have hτSsupp : τS.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true, ne_eq, τS]
    intro h
    exact (Perm.mem_support.1 x.2) (congrArg Subtype.val h)
  have hτS1 : τS ≠ 1 := by
    intro h
    have : τS.support = ∅ := by rw [h, Perm.support_one]
    rw [hτSsupp] at this
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (cycleType_of_involution hτ hτ1).2.2
    exact absurd (this ▸ Finset.mem_univ (⟨y, hy⟩ : {x // x ∈ τ.support})) (Finset.notMem_empty _)
  obtain ⟨-, hpar, hpos⟩ := cycleType_of_involution hτ hτ1
  have hcardC := card_centralizer_involution hτS2 hτS1
  rw [hτSsupp, Finset.card_univ, Fintype.card_coe, Nat.sub_self] at hcardC
  have hC8 : Nat.card (centralizer {τS}) ∣ 8 := by
    rw [hcardC]
    have : τ.support.card = 2 ∨ τ.support.card = 4 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hmem : restrHom L τ.support hS l ∈ centralizer {τS} := by
    rw [mem_centralizer_singleton_iff]
    ext x
    simp only [restrHom, MonoidHom.coe_mk, OneHom.coe_mk, Perm.mul_apply,
      Perm.subtypePerm_apply, τS]
    rw [← Perm.mul_apply, ← Perm.mul_apply, hc l l.2]
  have hord := orderOf_dvd_natCard (⟨_, hmem⟩ : centralizer {τS})
  rw [Subgroup.orderOf_mk] at hord
  exact orderOf_dvd_iff_pow_eq_one.1 (hord.trans hC8)

theorem commute_of_fix_support {τ σ : Perm α} (hσ : ∀ x ∈ τ.support, σ x = x) :
    σ * τ = τ * σ := by
  have hd : Perm.Disjoint σ τ := fun x => by
    by_cases hx : x ∈ τ.support
    · exact Or.inl (hσ x hx)
    · exact Or.inr (by simpa using hx)
  exact hd.commute.eq

theorem exists_ofSubtype_of_fix {τ σ : Perm α} (hσ : ∀ x ∈ τ.support, σ x = x) :
    ∃ σ' : Perm {x // x ∈ τ.supportᶜ}, Perm.ofSubtype σ' = σ ∧ Perm.sign σ' = Perm.sign σ := by
  have h₁ : ∀ x, σ x ∈ τ.supportᶜ ↔ x ∈ τ.supportᶜ := by
    intro x
    by_cases hx : x ∈ τ.support
    · rw [hσ x hx]
    · have : σ x ∉ τ.support := by
        intro h
        apply hx
        have := hσ _ h
        rwa [σ.injective this] at h
      simp [hx, this]
  have h₂ : ∀ x, σ x ≠ x → x ∈ τ.supportᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    exact fun h => hx (hσ x h)
  exact ⟨σ.subtypePerm h₁, Perm.ofSubtype_subtypePerm h₁ h₂, by
    convert Perm.sign_subtypePerm σ h₁ h₂⟩

end Perm

section S10

theorem eq_alt_fix_of_normalized {τ : Perm (Fin 10)} (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    {L : Subgroup (Perm (Fin 10))} (hA : L ≤ alternatingGroup (Fin 10)) (hperf : ⁅L, L⁆ = L)
    (h360 : 360 ∣ Nat.card L) (hcore : Nat.card (L ⧸ pPrimeCore 2 L) = 360)
    (hc : ∀ l ∈ L, l * τ = τ * l)
    (hN : ∀ π : Perm (Fin 10), π ∈ alternatingGroup (Fin 10) → π * τ = τ * π →
      π ∈ normalizer (L : Set (Perm (Fin 10)))) :
    τ.support.card = 4 ∧
      (∀ l, l ∈ L ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x) ∧
      Nat.card L = 360 := by
  obtain ⟨-, hpar, hpos⟩ := cycleType_of_involution hτ hτ1
  have hle : τ.support.card ≤ 10 := by simpa using Finset.card_le_univ τ.support
  have hLC : L ≤ centralizer {τ} := fun l hl => by
    rw [mem_centralizer_singleton_iff]
    exact hc l hl
  have hdvd : Nat.card L ∣ Nat.card (centralizer {τ}) := card_dvd_of_le hLC
  rw [card_centralizer_involution hτ hτ1, Fintype.card_fin] at hdvd
  have h4 : τ.support.card ≤ 4 := by
    by_contra h
    have h360' := h360.trans hdvd
    have : τ.support.card = 6 ∨ τ.support.card = 8 ∨ τ.support.card = 10 := by omega
    rcases this with h | h | h <;> rw [h] at h360' <;> revert h360' <;> decide
  have hfix := fix_support_of_perfect hτ h4 hperf hc
  set F : Finset (Fin 10) := τ.supportᶜ with hF
  set M : Subgroup (Perm (Fin 10)) := (alternatingGroup {x // x ∈ F}).map Perm.ofSubtype with hM
  have hmemM : ∀ l, l ∈ M ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x := by
    intro l
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, fun x hx => Perm.ofSubtype_apply_of_not_mem a (by simpa [F] using hx)⟩
      rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup] at ha
      rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact ha
    · rintro ⟨hlA, hl⟩
      obtain ⟨l', hl', hsign⟩ := exists_ofSubtype_of_fix hl
      refine ⟨l', ?_, hl'⟩
      rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, hsign]
      exact hlA
  have hLM : L ≤ M := fun l hl => (hmemM l).2 ⟨hA hl, hfix l hl⟩
  have hFcard : Fintype.card {x // x ∈ F} = 10 - τ.support.card := by
    rw [Fintype.card_coe, hF, Finset.card_compl, Fintype.card_fin]
  have hMcard : Nat.card M = (10 - τ.support.card).factorial / 2 := by
    rw [hM, card_map_of_injective Perm.ofSubtype_injective]
    have : Nontrivial {x // x ∈ F} := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hFcard]
      omega
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hFcard]
  have hk : τ.support.card = 2 ∨ τ.support.card = 4 := by omega
  rcases hk with hk | hk
  ·
    exfalso
    rw [hk] at hMcard hFcard
    have hsimp : IsSimpleGroup (alternatingGroup {x // x ∈ F}) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, hFcard]; norm_num)
    set ι : alternatingGroup {x // x ∈ F} →* Perm (Fin 10) :=
      (Perm.ofSubtype : Perm {x // x ∈ F} →* Perm (Fin 10)).comp
        (alternatingGroup {x // x ∈ F}).subtype with hι
    have hnorm : (L.comap ι).Normal := ⟨fun n hn g => by
      rw [mem_comap] at hn ⊢
      have hgN : ι g ∈ normalizer (L : Set (Perm (Fin 10))) := by
        refine hN _ ?_ (commute_of_fix_support fun x hx => ?_)
        · rw [Equiv.Perm.mem_alternatingGroup, hι, MonoidHom.coe_comp, Function.comp_apply,
            Perm.sign_ofSubtype]
          exact g.2
        · exact Perm.ofSubtype_apply_of_not_mem _ (by simpa [F] using hx)
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 hgN _).1 hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.comap ι) with hbot | htop
    · have hL1 : L = ⊥ := by
        rw [eq_bot_iff]
        intro l hl
        obtain ⟨a, ha, rfl⟩ := hLM hl
        have : (⟨a, ha⟩ : alternatingGroup {x // x ∈ F}) ∈ L.comap ι := hl
        rw [hbot, mem_bot] at this
        rw [mem_bot]
        simp only [Subtype.ext_iff] at this
        simp [this]
      rw [hL1, card_bot] at h360
      norm_num at h360
    · have hML : M ≤ L := by
        rintro _ ⟨a, ha, rfl⟩
        have : (⟨a, ha⟩ : alternatingGroup {x // x ∈ F}) ∈ L.comap ι := by
          rw [htop]; exact mem_top _
        exact this
      have hLcard : Nat.card L = 20160 := by
        rw [le_antisymm hLM hML, hMcard]
        decide
      have hO := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 L)
      rw [hLcard, hcore] at hO
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 L)) := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact pPrimeCore_coprime_card
      have h56 : Nat.card (pPrimeCore 2 L) = 56 := by omega
      rw [h56] at hcop
      norm_num at hcop
  ·
    have hM360 : Nat.card M = 360 := by
      rw [hMcard, hk]
      decide
    have hLeq : L = M := eq_of_le_of_card_ge hLM (by
      rw [hM360]
      exact Nat.le_of_dvd Nat.card_pos h360)
    refine ⟨hk, fun l => ?_, by rw [hLeq, hM360]⟩
    rw [hLeq]
    exact hmemM l

theorem false_of_standard_s10 {L : Subgroup (Perm (Fin 10))} (hA : L ≤ alternatingGroup (Fin 10))
    (hperf : ⁅L, L⁆ = L) (h360 : 360 ∣ Nat.card L)
    (hcore : Nat.card (L ⧸ pPrimeCore 2 L) = 360)
    (hstd : ∀ π σ : Perm (Fin 10), σ ∈ centralizer (L : Set (Perm (Fin 10))) →
      π * σ * π⁻¹ ∈ centralizer (L : Set (Perm (Fin 10))) → σ * σ = 1 → σ ≠ 1 →
        π ∈ normalizer (L : Set (Perm (Fin 10))))
    (hinv : ∃ τ ∈ centralizer (L : Set (Perm (Fin 10))), τ * τ = 1 ∧ τ ≠ 1) : False := by
  obtain ⟨τ, hτC, hτ, hτ1⟩ := hinv
  have hc : ∀ l ∈ L, l * τ = τ * l := mem_centralizer_iff.1 hτC
  have hN : ∀ π : Perm (Fin 10), π * τ = τ * π → π ∈ normalizer (L : Set (Perm (Fin 10))) := by
    intro π hπ
    refine hstd π τ hτC ?_ hτ hτ1
    rw [hπ, mul_inv_cancel_right]
    exact hτC
  obtain ⟨h4, hL, -⟩ := eq_alt_fix_of_normalized hτ hτ1 hA hperf h360 hcore hc
    fun π _ hπ => hN π hπ
  obtain ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, h12, h13, h23⟩ :=
    Finset.two_lt_card_iff.1 (by omega : 2 < τ.support.card)
  have hFc : τ.supportᶜ.card = 6 := by rw [Finset.card_compl, Fintype.card_fin, h4]
  obtain ⟨j₁, j₂, j₃, hj₁, hj₂, hj₃, hj12, hj13, hj23⟩ :=
    Finset.two_lt_card_iff.1 (by omega : 2 < τ.supportᶜ.card)
  rw [Finset.mem_compl] at hj₁ hj₂ hj₃
  have hij : ∀ i ∈ τ.support, ∀ j, j ∉ τ.support → i ≠ j := fun i hi j hj h => hj (h ▸ hi)
  have hσC : swap i₁ i₂ ∈ centralizer (L : Set (Perm (Fin 10))) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hl1 := ((hL l).1 hl).2
    rw [mul_swap_eq_swap_mul, hl1 i₁ hi₁, hl1 i₂ hi₂]
  have hπσ : swap i₃ j₁ * swap i₁ i₂ * (swap i₃ j₁)⁻¹ = swap i₁ i₂ := by
    rw [← swap_apply_apply, swap_apply_of_ne_of_ne h13 (hij i₁ hi₁ j₁ hj₁),
      swap_apply_of_ne_of_ne h23 (hij i₂ hi₂ j₁ hj₁)]
  have hπN : swap i₃ j₁ ∉ normalizer (L : Set (Perm (Fin 10))) := by
    intro hπ
    have hl : swap j₁ j₂ * swap j₁ j₃ ∈ L := by
      refine (hL _).2 ⟨?_, fun x hx => ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hj12, Perm.sign_swap hj13]
        decide
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hij x hx j₁ hj₁) (hij x hx j₃ hj₃),
          swap_apply_of_ne_of_ne (hij x hx j₁ hj₁) (hij x hx j₂ hj₂)]
    have hconj := ((hL _).1 ((mem_normalizer_iff.1 hπ _).1 hl)).2 i₃ hi₃
    simp only [Perm.mul_apply, swap_inv, swap_apply_left] at hconj
    rw [swap_apply_of_ne_of_ne hj13.symm hj23.symm,
      swap_apply_of_ne_of_ne (hij i₃ hi₃ j₃ hj₃).symm hj13.symm] at hconj
    exact hij i₃ hi₃ j₃ hj₃ hconj.symm
  have hσ1 : swap i₁ i₂ ≠ 1 := by
    intro h
    have := congrArg (fun σ : Perm (Fin 10) => σ i₁) h
    simp only [swap_apply_left, Perm.one_apply] at this
    exact h12 this.symm
  exact hπN (hstd _ _ hσC (by rw [hπσ]; exact hσC) (swap_mul_self i₁ i₂) hσ1)

end S10

end CFSG.ComponentClassification.CatFactsSmall
