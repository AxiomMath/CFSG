module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem max_of_odd_relIndex {G : Type*} [Group G] [Finite G] {Θ P₀ : Subgroup G}
    (_hP₀ : IsPGroup 2 P₀) (hodd : ¬ 2 ∣ P₀.relIndex Θ) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Θ → P₀ ≤ P → P ≤ P₀ := by
  intro P hP hPΘ hP₀P
  have h1 : P₀.relIndex P * P.relIndex Θ = P₀.relIndex Θ :=
    relIndex_mul_relIndex P₀ P Θ hP₀P hPΘ
  have h2 : P₀.relIndex P ∣ P₀.relIndex Θ := Dvd.intro _ h1
  have hP2 : IsPGroup 2 ↥P := hP
  obtain ⟨k, hk⟩ := hP2.index (P₀.subgroupOf P)
  have h3 : P₀.relIndex P = 2 ^ k := hk
  have hk0 : k = 0 := by
    by_contra hne
    exact hodd (dvd_trans (dvd_pow_self 2 hne) (h3 ▸ h2))
  rw [hk0, pow_zero] at h3
  exact (relIndex_eq_one.1 h3)

theorem isPGroup_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] {P₁ : Subgroup G₁}
    {P₂ : Subgroup G₂} (h₁ : IsPGroup 2 P₁) (h₂ : IsPGroup 2 P₂) :
    IsPGroup 2 (P₁.prod P₂) := by
  intro g
  obtain ⟨k₁, hk₁⟩ := h₁ ⟨g.1.1, g.2.1⟩
  obtain ⟨k₂, hk₂⟩ := h₂ ⟨g.1.2, g.2.2⟩
  refine ⟨k₁ + k₂, Subtype.ext (Prod.ext ?_ ?_)⟩
  · have := congrArg Subtype.val hk₁
    have h' : g.1.1 ^ 2 ^ k₁ = 1 := by simpa using this
    show g.1.1 ^ 2 ^ (k₁ + k₂) = 1
    rw [pow_add, pow_mul, h', one_pow]
  · have := congrArg Subtype.val hk₂
    have h' : g.1.2 ^ 2 ^ k₂ = 1 := by simpa using this
    show g.1.2 ^ 2 ^ (k₁ + k₂) = 1
    rw [add_comm, pow_add, pow_mul, h', one_pow]

theorem eq_prod_of_max {Γ : Type*} [Group Γ] {Θ₁ Θ₂ : Subgroup Γ} {H : Subgroup (Γ × Γ)}
    (hH : IsPGroup 2 H) (hHΘ : H ≤ Θ₁.prod Θ₂)
    (hmax : ∀ P : Subgroup (Γ × Γ), IsPGroup 2 P → P ≤ Θ₁.prod Θ₂ → H ≤ P → P ≤ H) :
    H = (H.map (MonoidHom.fst Γ Γ)).prod (H.map (MonoidHom.snd Γ Γ)) ∧
    IsPGroup 2 (H.map (MonoidHom.fst Γ Γ)) ∧ IsPGroup 2 (H.map (MonoidHom.snd Γ Γ)) ∧
    H.map (MonoidHom.fst Γ Γ) ≤ Θ₁ ∧ H.map (MonoidHom.snd Γ Γ) ≤ Θ₂ ∧
    (∀ P : Subgroup Γ, IsPGroup 2 P → P ≤ Θ₁ → H.map (MonoidHom.fst Γ Γ) ≤ P →
      P ≤ H.map (MonoidHom.fst Γ Γ)) ∧
    (∀ P : Subgroup Γ, IsPGroup 2 P → P ≤ Θ₂ → H.map (MonoidHom.snd Γ Γ) ≤ P →
      P ≤ H.map (MonoidHom.snd Γ Γ)) := by
  set S₁ := H.map (MonoidHom.fst Γ Γ) with hS₁
  set S₂ := H.map (MonoidHom.snd Γ Γ) with hS₂
  have hS₁p : IsPGroup 2 S₁ := hH.map _
  have hS₂p : IsPGroup 2 S₂ := hH.map _
  have hHle : H ≤ S₁.prod S₂ := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hS₁Θ : S₁ ≤ Θ₁ := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hHΘ hp).1
  have hS₂Θ : S₂ ≤ Θ₂ := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hHΘ hp).2
  have hprod : S₁.prod S₂ ≤ H :=
    hmax _ (isPGroup_prod hS₁p hS₂p) (fun p hp => ⟨hS₁Θ hp.1, hS₂Θ hp.2⟩) hHle
  have heq : H = S₁.prod S₂ := le_antisymm hHle hprod
  refine ⟨heq, hS₁p, hS₂p, hS₁Θ, hS₂Θ, ?_, ?_⟩
  · intro P hP hPΘ hle p hp
    have h1 : P.prod S₂ ≤ H :=
      hmax _ (isPGroup_prod hP hS₂p) (fun q hq => ⟨hPΘ hq.1, hS₂Θ hq.2⟩)
        (fun q hq => ⟨hle (hHle hq).1, (hHle hq).2⟩)
    have h2 : ((p, (1 : Γ)) : Γ × Γ) ∈ H := h1 ⟨hp, S₂.one_mem⟩
    exact (hHle h2).1
  · intro P hP hPΘ hle p hp
    have h1 : S₁.prod P ≤ H :=
      hmax _ (isPGroup_prod hS₁p hP) (fun q hq => ⟨hS₁Θ hq.1, hPΘ hq.2⟩)
        (fun q hq => ⟨(hHle hq).1, hle (hHle hq).2⟩)
    have h2 : (((1 : Γ), p) : Γ × Γ) ∈ H := h1 ⟨S₁.one_mem, hp⟩
    exact (hHle h2).2

theorem card_cent_prod_ge {Γ : Type*} [Group Γ] [Finite Γ] {S₁ S₂ : Subgroup Γ} {a b : Γ}
    {n m : ℕ} (hn : n ≤ Nat.card ↥(S₁ ⊓ centralizer ({a} : Set Γ)))
    (hm : m ≤ Nat.card ↥(S₂ ⊓ centralizer ({b} : Set Γ))) :
    n * m ≤ Nat.card ↥(S₁.prod S₂ ⊓ centralizer ({(a, b)} : Set (Γ × Γ))) := by
  have hmem : ∀ p : ↥(S₁ ⊓ centralizer ({a} : Set Γ)) × ↥(S₂ ⊓ centralizer ({b} : Set Γ)),
      (((p.1 : Γ), (p.2 : Γ)) : Γ × Γ) ∈ S₁.prod S₂ ⊓ centralizer ({(a, b)} : Set (Γ × Γ)) := by
    rintro ⟨⟨p, hp1, hp2⟩, ⟨q, hq1, hq2⟩⟩
    refine ⟨⟨hp1, hq1⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := mem_centralizer_singleton_iff.1 hp2
    have h2 := mem_centralizer_singleton_iff.1 hq2
    exact Prod.ext h1 h2
  have hle : Nat.card (↥(S₁ ⊓ centralizer ({a} : Set Γ)) × ↥(S₂ ⊓ centralizer ({b} : Set Γ))) ≤
      Nat.card ↥(S₁.prod S₂ ⊓ centralizer ({(a, b)} : Set (Γ × Γ))) := by
    refine Nat.card_le_card_of_injective
      (fun p => (⟨(((p.1 : Γ), (p.2 : Γ)) : Γ × Γ), hmem p⟩ :
        ↥(S₁.prod S₂ ⊓ centralizer ({(a, b)} : Set (Γ × Γ))))) ?_
    intro p p' hpp'
    have h1 := congrArg Subtype.val hpp'
    have h2 : ((p.1 : Γ), (p.2 : Γ)) = ((p'.1 : Γ), (p'.2 : Γ)) := h1
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  rw [Nat.card_prod] at hle
  exact le_trans (Nat.mul_le_mul hn hm) hle

end CFSG.EvenSporadicStandard.Fin76b
