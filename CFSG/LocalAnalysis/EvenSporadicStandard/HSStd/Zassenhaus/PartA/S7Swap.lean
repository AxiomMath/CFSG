module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Xhat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Core

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

section Prod

theorem normal_prod_cases {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (K : Subgroup (S × S)) [hKn : K.Normal] :
    K = ⊥ ∨ K = ⊤ ∨ K = (⊤ : Subgroup S).prod ⊥ ∨ K = (⊥ : Subgroup S).prod ⊤ := by
  haveI : (K.comap (MonoidHom.inl S S)).Normal := Subgroup.Normal.comap hKn _
  haveI : (K.comap (MonoidHom.inr S S)).Normal := Subgroup.Normal.comap hKn _
  have hA : K.comap (MonoidHom.inl S S) = ⊥ → ∀ a b : S, (a, b) ∈ K → a = 1 := by
    intro h a b hab
    apply eq_one_of_forall_commute hS
    intro s
    have h1 := hKn.conj_mem _ hab (s, 1)
    have h2 := K.mul_mem h1 (K.inv_mem hab)
    have h3 : (s * a * s⁻¹ * a⁻¹, (1 : S)) ∈ K := by
      convert h2 using 1
      ext <;> simp
    have h4 : s * a * s⁻¹ * a⁻¹ ∈ K.comap (MonoidHom.inl S S) := h3
    rw [h] at h4
    have h5 : s * a * s⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.1 h4
    have h6 : s * a = a * s := by
      calc s * a = (s * a * s⁻¹ * a⁻¹) * (a * s) := by group
        _ = a * s := by rw [h5, one_mul]
    exact h6.symm
  have hB : K.comap (MonoidHom.inr S S) = ⊥ → ∀ a b : S, (a, b) ∈ K → b = 1 := by
    intro h a b hab
    apply eq_one_of_forall_commute hS
    intro s
    have h1 := hKn.conj_mem _ hab (1, s)
    have h2 := K.mul_mem h1 (K.inv_mem hab)
    have h3 : ((1 : S), s * b * s⁻¹ * b⁻¹) ∈ K := by
      convert h2 using 1
      ext <;> simp
    have h4 : s * b * s⁻¹ * b⁻¹ ∈ K.comap (MonoidHom.inr S S) := h3
    rw [h] at h4
    have h5 : s * b * s⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.1 h4
    have h6 : s * b = b * s := by
      calc s * b = (s * b * s⁻¹ * b⁻¹) * (b * s) := by group
        _ = b * s := by rw [h5, one_mul]
    exact h6.symm
  have hinl : ∀ a : S, a ∈ K.comap (MonoidHom.inl S S) → (a, (1 : S)) ∈ K := fun a h => h
  have hinr : ∀ b : S, b ∈ K.comap (MonoidHom.inr S S) → ((1 : S), b) ∈ K := fun b h => h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.comap (MonoidHom.inl S S)) with h1 | h1 <;>
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.comap (MonoidHom.inr S S)) with h2 | h2
  · left
    ext ⟨a, b⟩
    constructor
    · intro hab
      have ha := hA h1 a b hab
      have hb := hB h2 a b hab
      rw [Subgroup.mem_bot]
      exact Prod.ext ha hb
    · intro hab
      rw [Subgroup.mem_bot] at hab
      rw [hab]; exact one_mem _
  · right; right; right
    ext ⟨a, b⟩
    rw [Subgroup.mem_prod]
    constructor
    · intro hab
      exact ⟨Subgroup.mem_bot.2 (hA h1 a b hab), Subgroup.mem_top _⟩
    · rintro ⟨ha, -⟩
      have ha' : a = 1 := Subgroup.mem_bot.1 ha
      subst ha'
      exact hinr b (by rw [h2]; exact Subgroup.mem_top _)
  · right; right; left
    ext ⟨a, b⟩
    rw [Subgroup.mem_prod]
    constructor
    · intro hab
      exact ⟨Subgroup.mem_top _, Subgroup.mem_bot.2 (hB h2 a b hab)⟩
    · rintro ⟨-, hb⟩
      have hb' : b = 1 := Subgroup.mem_bot.1 hb
      subst hb'
      exact hinl a (by rw [h1]; exact Subgroup.mem_top _)
  · right; left
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have ha : (a, (1 : S)) ∈ K := hinl a (by rw [h1]; exact Subgroup.mem_top _)
    have hb : ((1 : S), b) ∈ K := hinr b (by rw [h2]; exact Subgroup.mem_top _)
    have := K.mul_mem ha hb
    simpa using this

end Prod

section Key

variable {X : Type} [Group X] [Finite X]

theorem card_alt6 : Nat.card A6 = 360 := by
  haveI := isSimple_alt6
  rw [← card_innA6]
  exact Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_simple alt6_nonabelian)).toEquiv

theorem swap_key {tt : X}
    (e : ↥(centralizer ({tt} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (N : Subgroup X) [N.Normal] (hNdef : N = normalClosureOf (centralizerDerived tt))
    (φ : ↥N ≃* A6 × A6) (M : Subgroup X) [M.Normal] (hMN : M ≤ N)
    (hM : ∀ g ∈ N, ⁅tt, g⁆ ∈ M)
    (hK : (M.subgroupOf N).map φ.toMonoidHom = (⊤ : Subgroup A6).prod ⊥) : False := by
  haveI := isSimple_alt6
  have hMφ : ∀ (m : X) (hm : m ∈ M), (φ ⟨m, hMN hm⟩).2 = 1 := by
    intro m hm
    have : φ ⟨m, hMN hm⟩ ∈ (M.subgroupOf N).map φ.toMonoidHom := ⟨_, hm, rfl⟩
    rw [hK, Subgroup.mem_prod] at this
    exact Subgroup.mem_bot.1 this.2
  have hMφ' : ∀ s : A6, ∃ (m : X) (hm : m ∈ M), φ ⟨m, hMN hm⟩ = (s, 1) := by
    intro s
    have : (s, (1 : A6)) ∈ (M.subgroupOf N).map φ.toMonoidHom := by
      rw [hK, Subgroup.mem_prod]
      exact ⟨Subgroup.mem_top _, one_mem _⟩
    obtain ⟨k, hk, hks⟩ := this
    exact ⟨k.1, hk, by rw [show (⟨k.1, hMN hk⟩ : ↥N) = k from Subtype.ext rfl]; exact hks⟩
  let P₂ : Subgroup (A6 × A6) := (⊥ : Subgroup A6).prod ⊤
  have hP₂ : P₂ = (⊤ : Subgroup A6).map (MonoidHom.inr A6 A6) := by
    ext ⟨a, b⟩
    constructor
    · intro h
      have ha : a = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 h).1
      exact ⟨b, Subgroup.mem_top _, by rw [ha]; rfl⟩
    · rintro ⟨x, -, hx⟩
      have h1 := congrArg Prod.fst hx
      have h2 : a = 1 := by simpa using h1.symm
      rw [Subgroup.mem_prod]
      exact ⟨Subgroup.mem_bot.2 h2, Subgroup.mem_top _⟩
  let R : Subgroup ↥N := P₂.comap φ.toMonoidHom
  let M₂ : Subgroup X := R.map N.subtype
  have hM₂ : M₂ = N ⊓ centralizer (M : Set X) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r.2, ?_⟩
      show N.subtype r ∈ centralizer (M : Set X)
      rw [mem_centralizer_iff]
      intro m hm
      have hr' : (φ r).1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hr).1
      have h1 : φ (⟨m, hMN hm⟩ * r) = φ (r * ⟨m, hMN hm⟩) := by
        rw [map_mul, map_mul]
        refine Prod.ext ?_ ?_
        · simp [hr']
        · simp [hMφ m hm]
      have h2 := congrArg Subtype.val (φ.injective h1)
      exact h2
    · rintro ⟨hxN, hxC⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      show (φ ⟨x, hxN⟩) ∈ P₂
      rw [Subgroup.mem_prod]
      refine ⟨?_, Subgroup.mem_top _⟩
      rw [Subgroup.mem_bot]
      apply eq_one_of_forall_commute alt6_nonabelian
      intro s
      obtain ⟨m, hm, hms⟩ := hMφ' s
      have h1 : (⟨m, hMN hm⟩ : ↥N) * ⟨x, hxN⟩ = ⟨x, hxN⟩ * ⟨m, hMN hm⟩ :=
        Subtype.ext (mem_centralizer_iff.1 hxC m hm)
      have h2 := congrArg (fun z => (φ z).1) h1
      simp only [map_mul, Prod.fst_mul, hms] at h2
      exact h2.symm
  haveI hM₂n : M₂.Normal := by rw [hM₂]; infer_instance
  have hMM₂ : ∀ x ∈ M, x ∈ M₂ → x = 1 := by
    intro x hx hx2
    obtain ⟨r, hr, rfl⟩ := hx2
    have h1 : (φ r).2 = 1 := by
      have := hMφ r.1 hx
      rwa [show (⟨r.1, hMN hx⟩ : ↥N) = r from Subtype.ext rfl] at this
    have h2 : (φ r).1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hr).1
    have : φ r = 1 := Prod.ext h2 h1
    have := φ.injective (this.trans (map_one φ).symm)
    rw [this]; rfl
  have hcent : M₂ ≤ centralizer ({tt} : Set X) := by
    intro m hm
    have hmN : m ∈ N := by rw [hM₂] at hm; exact hm.1
    have h1 : tt * m * tt⁻¹ * m⁻¹ ∈ M := hM m hmN
    have h2 : tt * m * tt⁻¹ * m⁻¹ ∈ M₂ :=
      M₂.mul_mem (hM₂n.conj_mem m hm tt) (M₂.inv_mem hm)
    have h3 := hMM₂ _ h1 h2
    rw [mem_centralizer_singleton_iff]
    calc m * tt = (tt * m * tt⁻¹ * m⁻¹) * (m * tt) := by rw [h3, one_mul]
      _ = tt * m := by group
  have hRperf : ⁅R, R⁆ = R := by
    have hmap : R.map φ.toMonoidHom = P₂ :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective P₂
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    show (⁅R, R⁆).map φ.toMonoidHom = R.map φ.toMonoidHom
    rw [Subgroup.map_commutator, hmap, hP₂, ← Subgroup.map_commutator]
    have htop : ⁅(⊤ : Subgroup A6), (⊤ : Subgroup A6)⁆ = ⊤ := by
      rw [← _root_.commutator_def]; exact commutator_alternatingGroup_eq_top (by simp)
    rw [htop]
  have hM₂perf : ⁅M₂, M₂⁆ = M₂ := by
    show ⁅R.map N.subtype, R.map N.subtype⁆ = R.map N.subtype
    rw [← Subgroup.map_commutator, hRperf]
  have hM₂L : M₂ ≤ centralizerDerived tt := perfect_le_derived hcent hM₂perf
  have hcardM₂ : Nat.card M₂ = 360 := by
    have h1 : Nat.card M₂ = Nat.card R :=
      Subgroup.card_map_of_injective N.subtype_injective
    have hmap : R.map φ.toMonoidHom = P₂ := Subgroup.map_comap_eq_self_of_surjective φ.surjective P₂
    have h2 : Nat.card (R.map φ.toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective φ.injective
    have h3 : Nat.card P₂ = 360 := by
      rw [hP₂, Subgroup.card_map_of_injective (fun a b h => (Prod.mk.inj h).2), Subgroup.card_top,
        card_alt6]
    rw [h1, ← h2, hmap, h3]
  have hcardL : Nat.card (centralizerDerived tt) = 360 := by
    obtain ⟨f⟩ := lhat_equiv e
    rw [Nat.card_congr f.toEquiv, card_alt6]
  have hM₂eq : M₂ = centralizerDerived tt :=
    Subgroup.eq_of_le_of_card_ge hM₂L (le_of_eq (by rw [hcardM₂, hcardL]))
  haveI hLn : (centralizerDerived tt).Normal := by rw [← hM₂eq]; exact hM₂n
  have hNM₂ : N = M₂ := by
    rw [hNdef, hM₂eq]
    unfold normalClosureOf
    exact Subgroup.normalClosure_eq_self _
  have hM1 : ∀ m ∈ M, m = 1 := fun m hm => hMM₂ m hm (by rw [← hNM₂]; exact hMN hm)
  obtain ⟨a, b, hab⟩ := alt6_nonabelian
  have hne : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h
    push Not at h
    rw [h.1] at hab
    simp at hab
  obtain ⟨s, hs⟩ : ∃ s : A6, s ≠ 1 := by
    rcases hne with h | h
    · exact ⟨a, h⟩
    · exact ⟨b, h⟩
  obtain ⟨m, hm, hms⟩ := hMφ' s
  have h1 := hM1 m hm
  have : φ ⟨m, hMN hm⟩ = 1 := by
    have : (⟨m, hMN hm⟩ : ↥N) = 1 := Subtype.ext h1
    rw [this, map_one]
  rw [this] at hms
  exact hs (congrArg Prod.fst hms).symm

end Key

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
