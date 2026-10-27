module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open

@[expose] def HasE9 (Y : Type*) [Group Y] : Prop :=
  ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2

@[expose] def Aut5Le (Y : Type*) [Group Y] : Prop :=
  ∀ W : Subgroup (MulAut Y), IsElemAbelian 5 W → Nat.card W ≤ 5

section Elem

variable {A B : Type*} [Group A] [Group B] {p : ℕ}

theorem isElemAbelian_map (f : A →* B) {E : Subgroup A} (h : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map h _

theorem not_isCyclic_of_isElemAbelian_sq {E : Subgroup A} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = 3 ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hc]
  have h3 : (g : A) ^ 3 = 1 := hE.2 g g.2
  have h4 : g ^ 3 = 1 := Subtype.ext h3
  have := orderOf_dvd_of_pow_eq_one h4
  rw [h1] at this
  omega

end Elem

theorem hasE9_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : HasE9 X) :
    HasE9 Y := by
  obtain ⟨E, hE, hc⟩ := h
  exact ⟨E.map e.toMonoidHom, isElemAbelian_map _ hE,
    by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

section Rank

variable {Q : Type*} [Group Q] [Finite Q]

theorem hasE9_of_not_isCyclic {P : Subgroup Q} (hP : IsPGroup 3 P) (hnc : ¬ IsCyclic P) :
    HasE9 Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨S, -, hS, hel⟩ := CFSG.lemma_4_5_a (by norm_num : (3 : ℕ) ≠ 2) hnc
  have := hel
  have : CFSG.IsElementaryAbelian 3 ↥(S.map P.subtype) := CFSG.IsElementaryAbelian.map_subtype
  refine ⟨S.map P.subtype,
    ⟨inferInstance, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, ?_⟩
  rw [Subgroup.card_map_of_injective P.subtype_injective, hS]

theorem hasE9_of_surjective {Y : Type*} [Group Y] {φ : Q →* Y} (hφ : Function.Surjective φ)
    (h : HasE9 Y) : HasE9 Q := by
  obtain ⟨E, hE, hEc⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Y := Finite.of_surjective φ hφ
  have hEp : IsPGroup 3 E := fun x => ⟨1, by
    have := hE.2 x x.2
    simpa [Subtype.ext_iff] using this⟩
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hφ 3 R
  have hPR : (P.mapSurjective hφ : Subgroup Y) = P.map φ := rfl
  refine hasE9_of_not_isCyclic P.isPGroup' (fun hcyc => ?_)
  have hcycR : IsCyclic (P.map φ) :=
    isCyclic_of_surjective (φ.subgroupMap P) (φ.subgroupMap_surjective P)
  have hER' : E ≤ P.map φ := by
    rw [← hPR, hP]
    exact hER
  have := hcycR
  exact not_isCyclic_of_isElemAbelian_sq hE hEc (Subgroup.isCyclic_of_le hER')


omit [Finite Q] in
theorem hasE9_of_two_elements {e₁ e₂ : Q} (hc : Commute e₁ e₂) (h₁ : e₁ ^ 3 = 1)
    (h₂ : e₂ ^ 3 = 1) (hi : ∀ i j : ℕ, i < 3 → j < 3 → e₁ ^ i * e₂ ^ j = 1 → i = 0 ∧ j = 0) :
    HasE9 Q := by
  have hmod : ∀ (e : Q), e ^ 3 = 1 → ∀ i : ℤ, e ^ i = e ^ (i % 3).toNat := by
    intro e he i
    have h3 : (0 : ℤ) ≤ i % 3 := Int.emod_nonneg _ (by norm_num)
    have hi3 : e ^ (3 : ℤ) = 1 := by exact_mod_cast he
    calc e ^ i = e ^ (3 * (i / 3) + i % 3) := by rw [Int.mul_ediv_add_emod]
      _ = e ^ (i % 3) := by rw [zpow_add, zpow_mul, hi3, one_zpow, one_mul]
      _ = e ^ (i % 3).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h3]
  have hne1 : e₁ ≠ 1 := by
    intro h
    have := (hi 1 0 (by norm_num) (by norm_num) (by rw [h]; simp)).1
    omega
  have hne2 : e₂ ≠ 1 := by
    intro h
    have := (hi 0 1 (by norm_num) (by norm_num) (by rw [h]; simp)).2
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho₁ : orderOf e₁ = 3 := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = 3 := orderOf_eq_prime h₂ hne2
  have hcomm : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : Q) (b : Q)
    rw [← hk, ← hl]
    exact hc.zpow_zpow k l
  let f : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* Q :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Q) * b = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← hl, hmod e₁ h₁ k, hmod e₂ h₂ l] at hab'
    have hk3 : (k % 3).toNat < 3 := by omega
    have hl3 : (l % 3).toNat < 3 := by omega
    obtain ⟨hk0, hl0⟩ := hi _ _ hk3 hl3 hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk, hmod e₁ h₁ k, hk0]
      simp
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl, hmod e₂ h₂ l, hl0]
      simp
    rw [ha, hb]
    rfl
  have hcard : Nat.card (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) = 3 ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    norm_num
  refine ⟨f.range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
    obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    obtain ⟨l', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact ((Commute.refl e₁).zpow_zpow k k')
    · exact ((Commute.refl e₂).zpow_zpow l l')
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have h1 : x ^ 3 = 1 := by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (e₁ ^ k) ^ 3 = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₁, one_zpow]
      · show (e₂ ^ l) ^ 3 = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₂, one_zpow]
    rw [h1, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, hcard]


end Rank

section Alt

theorem mem_alternatingGroup_of_pow_three {N : ℕ} {g : Equiv.Perm (Fin N)} (h : g ^ 3 = 1) :
    g ∈ alternatingGroup (Fin N) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h1 : Equiv.Perm.sign g ^ 3 = 1 := by
    rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

theorem hasE9_alternatingGroup {N : ℕ} (hN : 6 ≤ N) : HasE9 (alternatingGroup (Fin N)) := by
  let ι : Fin 6 ↪ Fin N := Fin.castLEEmb hN
  let f : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin N) := Equiv.Perm.viaEmbeddingHom ι
  have hf : Function.Injective f := Equiv.Perm.viaEmbeddingHom_injective ι
  let a₀ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2
  let b₀ : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5
  have ha3 : (f a₀) ^ 3 = 1 := by
    rw [← map_pow]
    have : a₀ ^ 3 = 1 := by decide
    rw [this, map_one]
  have hb3 : (f b₀) ^ 3 = 1 := by
    rw [← map_pow]
    have : b₀ ^ 3 = 1 := by decide
    rw [this, map_one]
  let a : alternatingGroup (Fin N) := ⟨f a₀, mem_alternatingGroup_of_pow_three ha3⟩
  let b : alternatingGroup (Fin N) := ⟨f b₀, mem_alternatingGroup_of_pow_three hb3⟩
  refine hasE9_of_two_elements (e₁ := a) (e₂ := b) ?_ ?_ ?_ ?_
  · apply Subtype.ext
    show f a₀ * f b₀ = f b₀ * f a₀
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  · exact Subtype.ext ha3
  · exact Subtype.ext hb3
  · intro i j hi hj hab
    have h1 : f (a₀ ^ i * b₀ ^ j) = f 1 := by
      have := congrArg (fun x : alternatingGroup (Fin N) => (x : Equiv.Perm (Fin N))) hab
      simpa [a, b, map_mul, map_pow] using this
    have h2 := hf h1
    interval_cases i <;> interval_cases j <;> first | exact ⟨rfl, rfl⟩ | exact absurd h2 (by decide)

end Alt

section Aut

theorem aut5Le_of_center_quotient {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (h : Aut5Le (Q ⧸ Subgroup.center Q)) : Aut5Le Q := by
  intro W hW
  have hinj := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q
  have h1 := h (W.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Q))
    (isElemAbelian_map _ hW)
  rwa [Subgroup.card_map_of_injective hinj] at h1

theorem relIndex_le_five_of_aut5Le {A : Type*} [Group A] {Q V : Subgroup A}
    (hV : V ≤ Subgroup.normalizer (Q : Set A)) (hVe : IsElemAbelian 5 V) (h : Aut5Le Q) :
    (V ⊓ Subgroup.centralizer (Q : Set A)).relIndex V ≤ 5 := by
  have hcomm := hVe.1
  let ρ : V →* MulAut Q := (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hV)
  have hker : ρ.ker = (V ⊓ Subgroup.centralizer (Q : Set A)).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      refine ⟨x.2, fun q hq => ?_⟩
      have := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : A)) hx
      simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply] at this
      change (x : A) * q * (x : A)⁻¹ = q at this
      calc q * (x : A) = ((x : A) * q * (x : A)⁻¹) * (x : A) := by rw [this]
        _ = (x : A) * q := by group
    · rintro ⟨-, hx⟩
      ext ⟨q, hq⟩
      simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply]
      change (x : A) * q * (x : A)⁻¹ = q
      rw [mul_inv_eq_iff_eq_mul]
      exact (hx q hq).symm
  have hrange : IsElemAbelian 5 ρ.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      show ρ x * ρ y = ρ y * ρ x
      rw [← map_mul, ← map_mul, mul_comm' x y]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 5 = 1 := Subtype.ext (hVe.2 x x.2)
      rw [this, map_one]
  have h1 := h ρ.range hrange
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact h1

end Aut


end CFSG.AGLEmbedding.BlockCyc
