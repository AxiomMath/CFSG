module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Assembly.OrderReductions.FixedPairSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial.Positive

open scoped Pointwise

open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

variable {G : Type*} [Group G]

theorem mem_map_conj_iff {P : Subgroup G} {g x : G} :
    x ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      change g⁻¹ * (g * y * g⁻¹) * g = y
      group
    rwa [this]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem conj_mem_normalizer_map {P : Subgroup G} {x : G} (g : G)
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    g * x * g⁻¹ ∈
      Subgroup.normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hx _

theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G} (hx : x ∈ X) :
    Odd (orderOf x) :=
  Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] (hpodd : Odd p) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : Odd (Nat.card Q) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [hk]
  exact hpodd.pow

theorem exists_isSylowOf_le [Finite G] {p : ℕ} [Fact p.Prime] {X K : Subgroup G} (hXK : X ≤ K)
    (hX : IsPGroup p X) : ∃ P : Subgroup G, IsSylowOf p P K ∧ X ≤ P := by
  obtain ⟨S, hS⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hXK hx⟩, hS hx, rfl⟩

theorem exists_sylow_eq_of_isSylowOf_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ : IsSylowOf p Q (Subgroup.normalizer (Q : Set G))) :
    ∃ T : Sylow p G, (T : Subgroup G) = Q := by
  obtain ⟨S, hS⟩ := hQ
  obtain ⟨T, hT⟩ :=
    CFSG.OrderReductions.FixedPairSylow.sylow_extension_of_normalizer_le p _ S (by rw [hS])
  exact ⟨T, hT.trans hS⟩

theorem coe_smul_sylow [Finite G] {p : ℕ} [Fact p.Prime] (g : G) (P : Sylow p G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_map_conj_iff, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem exists_le_conj_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] {K S : Subgroup G}
    (P₀ : Sylow p K) (hSK : S ≤ K) (hS : IsPGroup p S) :
    ∃ k ∈ K, S ≤ ((P₀ : Subgroup K).map K.subtype).map (MulAut.conj k).toMonoidHom := by
  obtain ⟨T, hT⟩ := (hS.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P₀ T
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hxT : (⟨x, hSK hx⟩ : K) ∈ (T : Subgroup K) := hT hx
  rw [← hk, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxT
  rw [mem_map_conj_iff]
  exact ⟨_, hxT, by simp [MulAut.smul_def]⟩

theorem comm_of_mem_sup {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    {x y : G} (hx : x ∈ A ⊔ B) (hy : y ∈ A ⊔ B) : x * y = y * x := by
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup hAB hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup hAB hy
  have h1 : Commute a₁ a₂ := hA a₁ ha₁ a₂ ha₂
  have h2 : Commute b₁ b₂ := hB b₁ hb₁ b₂ hb₂
  have h3 : Commute a₁ b₂ := hAB a₁ ha₁ b₂ hb₂
  have h4 : Commute b₁ a₂ := (hAB a₂ ha₂ b₁ hb₁).symm
  exact ((h1.mul_right h3).mul_left (h4.mul_right h2)).eq

theorem le_of_isSylowOf_of_comm [Finite G] {p : ℕ} [Fact p.Prime] {U A B : Subgroup G}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hA : IsSylowOf p A U) (hB : IsSylowOf p B U) :
    A ≤ B := by
  obtain ⟨SB, hSB⟩ := hB.exists_sylow_eq_subgroupOf
  have hAn : (A.subgroupOf U).Normal := ⟨fun n hn g => by
    have hgn : g * n * g⁻¹ = n := by
      apply Subtype.ext
      change (g : G) * n * (g : G)⁻¹ = n
      rw [hU g g.2 n n.2, mul_inv_cancel_right]
    rw [hgn]
    exact hn⟩
  have hAp : IsPGroup p (A.subgroupOf U) := hA.isPGroup.comap_subtype
  have hle := hAp.le_sylow_of_normal SB
  rw [hSB] at hle
  intro x hx
  exact hle (show (⟨x, hA.le hx⟩ : U) ∈ A.subgroupOf U from hx)

theorem mem_normalizer_of_isSylowOf_comm [Finite G] {p : ℕ} [Fact p.Prime] {U A : Subgroup G}
    (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hA : IsSylowOf p A U) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) : g ∈ Subgroup.normalizer (A : Set G) := by
  have hA' : IsSylowOf p (A.map (MulAut.conj g).toMonoidHom) U := by
    apply isSylowOf_of_card
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hA.le hy)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA.card_eq
  apply mem_normalizer_of_conj_mem
  intro x hx
  exact le_of_isSylowOf_of_comm hU hA' hA ⟨x, hx, rfl⟩

theorem exists_isSylowOf_invariant [Finite G] {p : ℕ} [hp : Fact p.Prime] {A V R : Subgroup G}
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV : Odd (Nat.card V))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) (hRV : R ≤ V) (hR : IsPGroup p R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    ∃ R₀ : Subgroup G, IsSylowOf p R₀ V ∧ R ≤ R₀ ∧ A ≤ Subgroup.normalizer (R₀ : Set G) := by
  let _ : MulDistribMulAction A V :=
    { smul := fun a v => ⟨(a : G) * v * (a : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by change (1 : G) * v * 1⁻¹ = v; group)
      mul_smul := fun a b v => Subtype.ext (by
        change (a * b : G) * v * (a * b : G)⁻¹ = a * (b * v * (b : G)⁻¹) * (a : G)⁻¹
        group)
      smul_mul := fun a v w => Subtype.ext (by
        change (a : G) * (v * w) * (a : G)⁻¹ = (a * v * (a : G)⁻¹) * (a * w * (a : G)⁻¹)
        group)
      smul_one := fun a => Subtype.ext (by change (a : G) * 1 * (a : G)⁻¹ = 1; group) }
  have hsolv : Group.IsSolvable V := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hV
  have hKπ : CFSG.IsPiSubgroup {(⟨p, hp.out⟩ : Nat.Primes)} (R.subgroupOf V) := by
    intro r hr
    have hcard : Nat.card (R.subgroupOf V) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    rw [hcard, hk] at hr
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 hp.out).mp (r.2.dvd_of_dvd_pow hr))
  have hKinv : CFSG.IsInvariant A V (R.subgroupOf V) := ⟨fun a g => by
    change (g : G) ∈ R ↔ (a : G) * g * (a : G)⁻¹ ∈ R
    exact Subgroup.mem_normalizer_iff.mp (hAR a.2) g⟩
  obtain ⟨H, hH, hHinv, hKH⟩ :=
    CFSG.exists_isHallSubgroup_isInvariant_of_isPiSubgroup hsolv hcop _ _ hKπ hKinv
  have hHcard :=
    CFSG.Semidihedral.Principal.PrimewiseScalar.card_eq_of_isHallSubgroup_singleton hp.out H hH
  refine ⟨H.map V.subtype, ⟨Sylow.ofCard H hHcard, by rw [Sylow.coe_ofCard]⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hRV hx⟩, hKH hx, rfl⟩
  · intro a ha
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, (hHinv.invariant ⟨a, ha⟩ v).mp hv, rfl⟩

theorem card_sup_le_of_le_normalizer [Finite G] {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B h
  let f : A × B → (A ⊔ B : Subgroup G) := fun q => ⟨q.1 * q.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ ((A : Set G) * (B : Set G)) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card (A × B) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem exists_kleinFour_le {P : Subgroup G} {a b : G} (ha : a * a = 1) (ha1 : a ≠ 1)
    (hb : b * b = 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) (haP : a ∈ P)
    (hbP : b ∈ P) : ∃ T : Subgroup G, T ≤ P ∧ IsKleinFour T := by
  obtain ⟨T, hTP, hT, -⟩ := CFSG.GorensteinWalter.exists_kleinFour_of_commuting_involutions_le
    P a b ⟨ha1, by rw [pow_two]; exact ha⟩ ⟨hb1, by rw [pow_two]; exact hb⟩ hab hc haP hbP
  exact ⟨T, hTP, hT⟩

theorem exists_kleinFour_le_of_conj {P : Subgroup G} {a b : G} (ha : a * a = 1) (ha1 : a ≠ 1)
    (hb : b * b = 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) (g : G)
    (haP : g * a * g⁻¹ ∈ P) (hbP : g * b * g⁻¹ ∈ P) : ∃ T : Subgroup G, T ≤ P ∧ IsKleinFour T := by
  refine exists_kleinFour_le (a := g * a * g⁻¹) (b := g * b * g⁻¹) ?_ ?_ ?_ ?_ ?_ ?_ haP hbP
  · rw [show g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha]
    group
  · intro h1
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [show g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ by group, hb]
    group
  · intro h1
    apply hb1
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · intro h1
    apply hab
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [h1]
      _ = b := by group
  · rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hc]
    group

theorem relIndex_map_pPrimeCore (F : Subgroup G) :
    ((CFSG.pPrimeCore 2 F).map F.subtype).relIndex F = (CFSG.pPrimeCore 2 F).index := by
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective]

theorem not_dvd_relIndex_map_pPrimeCore [Finite G] {F : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : IsPGroup 2 (F ⧸ CFSG.pPrimeCore 2 F)) :
    ¬ p ∣ ((CFSG.pPrimeCore 2 F).map F.subtype).relIndex F := by
  rw [relIndex_map_pPrimeCore]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF
  change ¬ p ∣ Nat.card (F ⧸ CFSG.pPrimeCore 2 F)
  rw [hk]
  intro hdvd
  have h2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)
  rw [h2] at hpodd
  exact absurd hpodd (by decide)

theorem le_normalizer_map_pPrimeCore [Finite G] (F : Subgroup G) :
    F ≤ Subgroup.normalizer (((CFSG.pPrimeCore 2 F).map F.subtype : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨o, ho, rfl⟩
  exact ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹,
    (CFSG.pPrimeCore_normal (p := 2) (G := F)).conj_mem o ho ⟨g, hg⟩, rfl⟩

theorem odd_card_map_pPrimeCore [Finite G] (F : Subgroup G) :
    Odd (Nat.card ((CFSG.pPrimeCore 2 F).map F.subtype : Subgroup G)) := by
  rw [Subgroup.card_map_of_injective F.subtype_injective]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := F))

theorem exists_sylow_isCyclic [Finite G] {p : ℕ} [Fact p.Prime] {S F : Subgroup G}
    (hS : IsSylowOf p S F) (hc : IsCyclic S) : ∃ S' : Sylow p F, IsCyclic (S' : Subgroup F) := by
  obtain ⟨S', hS'⟩ := hS.exists_sylow_eq_subgroupOf
  refine ⟨S', ?_⟩
  rw [hS']
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS.le).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem sl2_neg_one_ne_one {F₀ : Type*} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) F₀) ≠ 1 := by
  intro h
  have h1 : (-1 : F₀) = 1 := by
    simpa using congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F₀ => (A : Matrix (Fin 2) (Fin 2) F₀) 0 0) h
  have := Fintype.ofFinite F₀
  have h2 := FiniteField.even_card_iff_char_two.1 (neg_one_eq_one_iff.1 h1)
  rw [Nat.card_eq_fintype_card] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_iff.2 h2)

end CFSG.Semidihedral.FixedCoreNontrivial.Positive
