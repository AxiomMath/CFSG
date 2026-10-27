module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.SmallDimension

public section

namespace CFSG.UnitaryInvolutionIndex

open Module

section Group

variable {G : Type*} [Group G]

theorem eq_or_eq_top_of_index_eq_prime {p : ℕ} (hp : p.Prime) {H K : Subgroup G}
    (hH : H.index = p) (hHK : H ≤ K) : K = H ∨ K = ⊤ := by
  have h := Subgroup.relIndex_mul_index hHK
  rw [hH] at h
  rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ h) with h1 | h1
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · left
    rw [h1] at h
    have h2 : H.relIndex K = 1 := by
      have := hp.pos
      nlinarith
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hHK

theorem commutator_mem_of_index_eq_prime {p : ℕ} (hp : p.Prime) {N : Subgroup G} [N.Normal]
    (hN : N.index = p) (g h : G) : g⁻¹ * h⁻¹ * g * h ∈ N := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (by rw [← Subgroup.index_eq_card, hN])
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mul_comm' (g : G ⧸ N)⁻¹ (h : G ⧸ N)⁻¹, inv_mul_cancel_right, inv_mul_cancel]

theorem exists_map_eq_of_index_le {p : ℕ} (hp : p.Prime) [Finite G] (hG : IsPGroup p G)
    (τ : G →* G) (hτ : ∀ g, τ (τ g) = g) (A₀ : Subgroup G) [A₀.Normal]
    (hA₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hidx : A₀.index ≤ p) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.index ≤ p ∧
      A.map τ = A := by
  have : Fact p.Prime := ⟨hp⟩
  have hτs : Function.Surjective τ := fun g => ⟨τ g, hτ g⟩
  have hτi : Function.Injective τ := fun a b h => by rw [← hτ a, h, hτ b]
  have hmapmap : ∀ H : Subgroup G, (H.map τ).map τ = H := by
    intro H
    rw [Subgroup.map_map]
    convert Subgroup.map_id H
    exact MonoidHom.ext hτ
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · exact ⟨⊤, inferInstance, fun a _ b _ => hcomm a b, by rw [Subgroup.index_top]; exact hp.pos,
      Subgroup.map_top_of_surjective τ hτs⟩
  have hidx' : A₀.index = p := by
    obtain ⟨n, hn⟩ := hG.index A₀
    rcases n with _ | _ | n
    · rw [pow_zero, Subgroup.index_eq_one] at hn
      exact absurd (fun a b => hA₀ a (hn ▸ Subgroup.mem_top a) b (hn ▸ Subgroup.mem_top b))
        hcomm
    · rw [hn, pow_one]
    · have : p ^ (n + 2) ≤ p := hn ▸ hidx
      have h2 : p ^ 2 ≤ p ^ (n + 2) := Nat.pow_le_pow_right hp.pos (by omega)
      have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
  by_cases hinv : A₀.map τ = A₀
  · exact ⟨A₀, inferInstance, hA₀, hidx, hinv⟩
  set A₁ := A₀.map τ with hA₁def
  have : A₁.Normal := Subgroup.Normal.map inferInstance τ hτs
  have hA₁ : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA₀ a ha b hb]
  have hcard : Nat.card A₁ = Nat.card A₀ := Subgroup.card_map_of_injective hτi
  have hidx₁ : A₁.index = p := by
    have h1 := A₀.index_mul_card
    have h2 := A₁.index_mul_card
    rw [hcard] at h2
    rw [← hidx']
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)
  have hnot₀₁ : ¬A₀ ≤ A₁ := fun h => hinv (Subgroup.eq_of_le_of_card_ge h hcard.le).symm
  have hnot₁₀ : ¬A₁ ≤ A₀ := fun h => hinv (Subgroup.eq_of_le_of_card_ge h hcard.ge)
  have hsup : A₀ ⊔ A₁ = ⊤ := by
    rcases eq_or_eq_top_of_index_eq_prime hp hidx' (le_sup_left : A₀ ≤ A₀ ⊔ A₁) with h | h
    · exact absurd (h ▸ le_sup_right) hnot₁₀
    · exact h
  set Z := A₀ ⊓ A₁ with hZdef
  have hZc : ∀ z ∈ Z, ∀ g : G, g * z = z * g := by
    intro z hz g
    have hle : A₀ ⊔ A₁ ≤ Subgroup.centralizer {z} := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hA₀ a ha z hz.1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hA₁ a ha z hz.2)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hsup ▸ Subgroup.mem_top g))
  have hcomZ : ∀ g h : G, g⁻¹ * h⁻¹ * g * h ∈ Z := fun g h =>
    ⟨commutator_mem_of_index_eq_prime hp hidx' g h, commutator_mem_of_index_eq_prime hp hidx₁ g h⟩
  obtain ⟨a, ha₀, ha₁⟩ : ∃ a ∈ A₀, a ∉ A₁ := Set.not_subset.mp hnot₀₁
  have hτa : τ a ∈ A₁ := ⟨a, ha₀, rfl⟩
  set y := a * τ a with hydef
  have hyZ : y ∉ Z := by
    intro hy
    apply ha₁
    have : a = y * (τ a)⁻¹ := by rw [hydef, mul_inv_cancel_right]
    rw [this]
    exact A₁.mul_mem hy.2 (A₁.inv_mem hτa)
  set A := Z ⊔ Subgroup.zpowers y with hAdef
  have hZA : Z ≤ A := le_sup_left
  have hyA : y ∈ A := le_sup_right (a := Z) (Subgroup.mem_zpowers y)
  have hcentral : ∀ z ∈ Z, z ∈ Subgroup.centralizer (A : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun h _ => hZc z hz h
  have hAy : A ≤ Subgroup.centralizer {y} := sup_le
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hZc z hz y).symm)
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hAA : A ≤ Subgroup.centralizer (A : Set G) := sup_le hcentral
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hAy hh)))
  have hτy : τ y ∈ A := by
    have h1 : τ y = y * (y⁻¹ * τ y) := by rw [mul_inv_cancel_left]
    have h2 : y⁻¹ * τ y = (τ a)⁻¹ * a⁻¹ * τ a * a := by
      rw [hydef, map_mul, hτ a, mul_inv_rev]
      group
    rw [h1, h2]
    exact A.mul_mem hyA (hZA (hcomZ (τ a) a))
  have hτZ : Z.map τ ≤ Z := by
    refine (Subgroup.map_inf_le A₀ A₁ τ).trans ?_
    rw [← hA₁def, hmapmap A₀, inf_comm]
  have hle : A.map τ ≤ A := by
    rw [hAdef, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact sup_le (hτZ.trans hZA) (Subgroup.zpowers_le.mpr hτy)
  refine ⟨A, ⟨fun n hn g => ?_⟩, fun a ha b hb => ?_, ?_, le_antisymm hle ?_⟩
  · have h1 : g * n * g⁻¹ = n * (n⁻¹ * g⁻¹⁻¹ * n * g⁻¹) := by group
    rw [h1]
    exact A.mul_mem hn (hZA (hcomZ n g⁻¹))
  · exact (Subgroup.mem_centralizer_iff.mp (hAA hb) a ha)
  · have hZidx : Z.index ≤ p * p := by
      have := Subgroup.index_inf_le (H := A₀) (K := A₁)
      rwa [hidx', hidx₁] at this
    have hrel : p ≤ Z.relIndex A := by
      obtain ⟨n, hn⟩ := (hG.to_subgroup A).index (Z.subgroupOf A)
      have hn' : Z.relIndex A = p ^ n := hn
      have hne : Z.relIndex A ≠ 1 := fun h1 =>
        hyZ (Subgroup.relIndex_eq_one.mp h1 hyA)
      rw [hn'] at hne ⊢
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne (pow_zero p)
      exact Nat.le_self_pow hn0 p
    have hmul := Subgroup.relIndex_mul_index hZA
    have hpos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    by_contra hlt
    push Not at hlt
    have : p * p < Z.relIndex A * A.index :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hlt hp.pos) (Nat.mul_le_mul_right _ hrel)
    omega
  · calc A = (A.map τ).map τ := (hmapmap A).symm
      _ ≤ A.map τ := Subgroup.map_mono hle

end Group

section Conj

variable {M : Type*} [Group M]

@[expose] def conjRestrict (P : Subgroup M) {t : M} (ht : t ∈ Subgroup.normalizer (P : Set M)) :
    P →* P where
  toFun g := ⟨t * g * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht g).mp g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjRestrict (P : Subgroup M) {t : M} (ht : t ∈ Subgroup.normalizer (P : Set M))
    (g : P) : (conjRestrict P ht g : M) = t * g * t⁻¹ :=
  rfl

theorem conjRestrict_conjRestrict (P : Subgroup M) {t : M}
    (ht : t ∈ Subgroup.normalizer (P : Set M)) (ht2 : t ^ 2 = 1) (g : P) :
    conjRestrict P ht (conjRestrict P ht g) = g := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  apply Subtype.ext
  simp only [coe_conjRestrict, htinv]
  rw [show t * (t * ↑g * t) * t = (t * t) * ↑g * (t * t) by group, ← sq, ht2, one_mul, mul_one]

theorem mem_normalizer_map_subtype (P : Subgroup M) {t : M}
    (ht : t ∈ Subgroup.normalizer (P : Set M)) (ht2 : t ^ 2 = 1) {A : Subgroup P}
    (hA : A.map (conjRestrict P ht) = A) :
    t ∈ Subgroup.normalizer ((A.map P.subtype : Subgroup M) : Set M) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  have hfwd : ∀ h : M, h ∈ A.map P.subtype → t * h * t⁻¹ ∈ A.map P.subtype := by
    rintro _ ⟨a, ha, rfl⟩
    have : conjRestrict P ht a ∈ A := hA ▸ Subgroup.mem_map_of_mem _ ha
    exact ⟨_, this, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨hfwd h, fun hh => ?_⟩
  have := hfwd _ hh
  rwa [htinv, show t * (t * h * t) * t = (t * t) * h * (t * t) by group, ← sq, ht2, one_mul,
    mul_one] at this

end Conj

variable {k : Type*} [Field k]

@[expose] noncomputable def glRep {n : Type*} [Fintype n] [DecidableEq n]
    (P : Subgroup (GL n k)) : P →* End k (n → k) :=
  (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] End k (n → k)).toMonoidHom.comp
    ((Units.coeHom _).comp P.subtype)

theorem glRep_injective {n : Type*} [Fintype n] [DecidableEq n] (P : Subgroup (GL n k)) :
    Function.Injective (glRep P) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLinAlgEquiv'.injective hgh

theorem odd_three_dimensional_invariant_abelian_subgroup [IsAlgClosed k] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpk : ringChar k ≠ p) (P : Subgroup (GL (Fin 3) k)) [Finite P]
    (hP : IsPGroup p P) (t : GL (Fin 3) k) (ht : t ^ 2 = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set (GL (Fin 3) k))) :
    (∃ A : Subgroup (GL (Fin 3) k), A ≤ P ∧ (A.subgroupOf P).Normal ∧ IsMulCommutative A ∧
      t ∈ Subgroup.normalizer (A : Set (GL (Fin 3) k)) ∧ A.relIndex P ≤ 3) ∧
    (p ≠ 3 → IsMulCommutative P) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpk' : (p : k) ≠ 0 := fun h => hpk (CharP.ringChar_of_prime_eq_zero hp h)
  have hdim : finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  have hcomm_of : ∀ g h : P, Commute (glRep P g) (glRep P h) → g * h = h * g := by
    intro g h hgh
    apply glRep_injective P
    rw [map_mul, map_mul]
    exact hgh.eq
  have habel : p ≠ 3 → IsMulCommutative P := by
    intro hp3
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    refine isMulCommutative_iff.mpr fun g h => hcomm_of g h ?_
    exact commute_of_finrank_lt hpk' hP (glRep P) (by rw [hdim]; exact hp5) g h
  refine ⟨?_, habel⟩
  have hpass : ∀ A : Subgroup P, A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A.index ≤ 3 →
      A.map (conjRestrict P htP) = A →
      ∃ A' : Subgroup (GL (Fin 3) k), A' ≤ P ∧ (A'.subgroupOf P).Normal ∧
        IsMulCommutative A' ∧ t ∈ Subgroup.normalizer (A' : Set (GL (Fin 3) k)) ∧
        A'.relIndex P ≤ 3 := by
    intro A hAn hAc hAi hAτ
    have hsub : (A.map P.subtype).subgroupOf P = A :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective A
    refine ⟨A.map P.subtype, Subgroup.map_subtype_le A, by rw [hsub]; exact hAn, ?_,
      mem_normalizer_map_subtype P htP ht hAτ, ?_⟩
    · refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
      obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul,
        hAc a ha b hb]
    · rw [Subgroup.relIndex, hsub]
      exact hAi
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨A₀, hA₀n, hA₀i, hA₀c⟩ :=
      exists_normal_index_le_commute_of_finrank_eq hpk' hP (glRep P) hdim
    obtain ⟨A, hAn, hAc, hAi, hAτ⟩ := exists_map_eq_of_index_le hp hP (conjRestrict P htP)
      (conjRestrict_conjRestrict P htP ht) A₀
      (fun a ha b hb => hcomm_of a b (hA₀c a ha b hb)) hA₀i
    exact hpass A hAn hAc hAi hAτ
  · have := habel hp3
    refine hpass ⊤ inferInstance (fun a _ b _ => mul_comm' a b) (by rw [Subgroup.index_top]; omega)
      (Subgroup.map_top_of_surjective _ fun g =>
        ⟨_, conjRestrict_conjRestrict P htP ht g⟩)

end CFSG.UnitaryInvolutionIndex
