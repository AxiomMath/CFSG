module

public import CFSG.FeitThompson.Representations.PrimeFixedTICentralSectionSetup
public import CFSG.FeitThompson.Representations.PrimeTILocalTransporterTISet
public import CFSG.FeitThompson.Representations.CentralPrimeOrientedProjection

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeFixedTIPGroupTransport

open Subgroup Pointwise

variable {G : Type*} [Group G] {L : Subgroup G}

theorem subgroupOf_map_subtype_self (X : Subgroup ↥L) : (X.map L.subtype).subgroupOf L = X := by
  ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]

theorem map_subtype_inf (X Y : Subgroup ↥L) :
    (X ⊓ Y).map L.subtype = X.map L.subtype ⊓ Y.map L.subtype :=
  Subgroup.map_inf X Y L.subtype (Subgroup.subtype_injective L)

theorem map_subtype_eq_bot_iff {X : Subgroup ↥L} : X.map L.subtype = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective L)

theorem isCyclic_map_subtype {X : Subgroup ↥L} (hX : IsCyclic ↥X) :
    IsCyclic ↥(X.map L.subtype) :=
  isCyclic_of_surjective
    (X.equivMapOfInjective L.subtype (Subgroup.subtype_injective L)).toMonoidHom
    (X.equivMapOfInjective L.subtype (Subgroup.subtype_injective L)).surjective

theorem not_isMulCommutative_map_subtype {X : Subgroup ↥L} (hX : ¬ IsMulCommutative ↥X) :
    ¬ IsMulCommutative ↥(X.map L.subtype) := by
  intro hc
  refine hX ⟨⟨fun x y => ?_⟩⟩
  have e := X.equivMapOfInjective L.subtype (Subgroup.subtype_injective L)
  exact e.injective (by simpa [map_mul] using hc.is_comm.comm (e x) (e y))

theorem image_coe_sdiff_one (X : Subgroup ↥L) :
    (fun x : ↥L => (x : G)) '' ((X : Set ↥L) \ {1})
      = ((X.map L.subtype : Subgroup G) : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyX, hy1⟩, rfl⟩
    refine ⟨⟨y, hyX, rfl⟩, ?_⟩
    simp only [Set.mem_singleton_iff] at hy1 ⊢
    exact fun hc => hy1 (Subtype.ext hc)
  · rintro ⟨⟨y, hyX, rfl⟩, hx1⟩
    refine ⟨y, ⟨hyX, ?_⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    exact fun hc => hx1 (by rw [hc]; rfl)

theorem coe_mul_coe_map_subtype {X Y : Subgroup ↥L}
    (h : (X : Set ↥L) * (Y : Set ↥L) = Set.univ) :
    ((X.map L.subtype : Subgroup G) : Set G) * ((Y.map L.subtype : Subgroup G) : Set G)
      = (L : Set G) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, -, rfl⟩, v, ⟨b, -, rfl⟩, rfl⟩
    exact mul_mem a.2 b.2
  · intro hx
    have hmem : (⟨x, hx⟩ : ↥L) ∈ (X : Set ↥L) * (Y : Set ↥L) := by rw [h]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    exact ⟨(a : G), ⟨a, ha, rfl⟩, (b : G), ⟨b, hb, rfl⟩, by
      simpa using congrArg (fun w : ↥L => (w : G)) hab⟩

theorem sup_map_subtype_eq {X Y : Subgroup ↥L}
    (h : (X : Set ↥L) * (Y : Set ↥L) = Set.univ) :
    X.map L.subtype ⊔ Y.map L.subtype = L := by
  refine le_antisymm (sup_le (Subgroup.map_subtype_le X) (Subgroup.map_subtype_le Y)) ?_
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ (X : Set ↥L) * (Y : Set ↥L) := by rw [h]; trivial
  obtain ⟨b, hb, c, hc, hbc⟩ := hmem
  have heq : (b : G) * (c : G) = x := by simpa using congrArg (fun w : ↥L => (w : G)) hbc
  exact heq ▸ mul_mem (Subgroup.mem_sup_left ⟨b, hb, rfl⟩) (Subgroup.mem_sup_right ⟨c, hc, rfl⟩)

theorem commutator_map_subtype_self (X : Subgroup ↥L) :
    ⁅X.map L.subtype, X.map L.subtype⁆ = (⁅X, X⁆ : Subgroup ↥L).map L.subtype :=
  (Subgroup.map_commutator X X L.subtype).symm

theorem forall_mem_commutator_map_subtype {X Y : Subgroup ↥L}
    (h : ∀ u ∈ Y, u ≠ 1 → ∀ k ∈ X, k⁻¹ * (u⁻¹ * k * u) ∈ (⁅X, X⁆ : Subgroup ↥L) →
      k ∈ (⁅X, X⁆ : Subgroup ↥L)) :
    ∀ u ∈ Y.map L.subtype, u ≠ 1 → ∀ k ∈ X.map L.subtype,
      k⁻¹ * (u⁻¹ * k * u) ∈ (⁅X.map L.subtype, X.map L.subtype⁆ : Subgroup G) →
      k ∈ (⁅X.map L.subtype, X.map L.subtype⁆ : Subgroup G) := by
  rintro u ⟨v, hv, rfl⟩ hu1 k ⟨w, hw, rfl⟩ hfix
  have hv1 : v ≠ 1 := fun hc => hu1 (by rw [hc]; rfl)
  rw [commutator_map_subtype_self] at hfix ⊢
  have hfix' : (w⁻¹ * (v⁻¹ * w * v) : ↥L) ∈ (⁅X, X⁆ : Subgroup ↥L) := by
    obtain ⟨z, hz, hzeq⟩ := hfix
    exact (Subtype.ext hzeq : z = w⁻¹ * (v⁻¹ * w * v)) ▸ hz
  exact ⟨w, h v hv hv1 w hw hfix', rfl⟩

theorem map_subtype_inf_centralizer_singleton (X : Subgroup ↥L) (x : ↥L) :
    ((X ⊓ Subgroup.centralizer ({x} : Set ↥L)).map L.subtype : Subgroup G)
      = (X.map L.subtype) ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzX, hzc⟩, rfl⟩
    refine ⟨⟨z, hzX, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg (fun w : ↥L => (w : G)) (Subgroup.mem_centralizer_singleton_iff.1 hzc)
  · rintro ⟨⟨z, hzX, rfl⟩, hzc⟩
    refine ⟨z, ⟨hzX, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hzc

theorem subgroupOf_le_of_le_map {X : Subgroup ↥L} {Z : Subgroup G} (hZ : Z ≤ X.map L.subtype) :
    Z.subgroupOf L ≤ X := by
  intro z hz
  obtain ⟨y, hy, hyz⟩ := hZ (Subgroup.mem_subgroupOf.1 hz)
  exact (Subtype.ext hyz : y = z) ▸ hy

theorem subgroupOf_ne_bot_of_ne_bot {Z : Subgroup G} (hZL : Z ≤ L) (hZ : Z ≠ ⊥) :
    Z.subgroupOf L ≠ ⊥ := by
  intro hc
  refine hZ (le_bot_iff.1 fun z hz => ?_)
  have hmem : (⟨z, hZL hz⟩ : ↥L) ∈ Z.subgroupOf L := Subgroup.mem_subgroupOf.2 hz
  rw [hc, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (congrArg (fun w : ↥L => (w : G)) hmem)

theorem subgroupOf_le_centralizer {X : Subgroup ↥L} {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.centralizer ((X.map L.subtype : Subgroup G) : Set G)) :
    Z.subgroupOf L ≤ Subgroup.centralizer (X : Set ↥L) := by
  intro z hz
  refine Subgroup.mem_centralizer_iff.2 fun x hx => Subtype.ext ?_
  exact Subgroup.mem_centralizer_iff.1 (hZ (Subgroup.mem_subgroupOf.1 hz)) (x : G) ⟨x, hx, rfl⟩

theorem subgroupOf_inf_centralizer_singleton_eq_bot {u : ↥L} {Z : Subgroup G}
    (hZ : Z ⊓ Subgroup.centralizer ({(u : G)} : Set G) = ⊥) :
    Z.subgroupOf L ⊓ Subgroup.centralizer ({u} : Set ↥L) = ⊥ := by
  refine le_bot_iff.1 fun z hz => ?_
  obtain ⟨hzZ, hzc⟩ := Subgroup.mem_inf.1 hz
  have hmem : (z : G) ∈ Z ⊓ Subgroup.centralizer ({(u : G)} : Set G) :=
    ⟨Subgroup.mem_subgroupOf.1 hzZ, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg (fun w : ↥L => (w : G)) (Subgroup.mem_centralizer_singleton_iff.1 hzc))⟩
  rw [hZ, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (Subtype.ext hmem)

theorem normalizer_coe_eq_normalizer_sdiff_one (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) = Subgroup.normalizer ((X : Set G) \ {1}) := by
  ext g
  simp only [Subgroup.mem_set_normalizer_iff, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · intro hg x
    refine ⟨fun hx => ⟨(hg x).1 hx.1, ?_⟩, fun hx => ⟨(hg x).2 hx.1, ?_⟩⟩
    · intro hc
      refine hx.2 ?_
      have := congrArg (fun y => g⁻¹ * y * g) hc
      simpa [mul_assoc] using this
    · exact fun hc => hx.2 (by rw [hc]; group)
  · intro hg x
    by_cases hx1 : x = 1
    · subst hx1; simp
    · exact ⟨fun hx => ((hg x).1 ⟨hx, hx1⟩).1, fun hx => ((hg x).2 ⟨hx, by simpa using hx1⟩).1⟩

section Setup

variable {K W₁ W₂ : Subgroup ↥L} {p a : ℕ}

theorem isPrimeFixedTISetup_map_subtype
    (hprime : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hGodd : Odd (Nat.card G))
    (hcyc : IsPrimeCyclicTIHyp K W₁ W₂)
    (hna : ¬ IsMulCommutative ↥K) (hKcard : Nat.card ↥K = p ^ a)
    (hW₂card : Nat.card ↥W₂ = p) (hW₂comm : W₂ ≤ ⁅K, K⁆)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      = ((K.map L.subtype : Subgroup G) : Set G) \ {1}} = (L : Set G))
    (hdisj : ∀ g ∉ L, (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      ∩ ((fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})) = ∅) :
    IsPrimeFixedTISetup G p a L (K.map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) := by
  have hKn := hcyc.normal
  have hnormeq : Subgroup.normalizer ((K.map L.subtype : Subgroup G) : Set G) = L := by
    refine SetLike.ext' ?_
    rw [normalizer_coe_eq_normalizer_sdiff_one, ← hstab]
    exact Set.ext fun g => mem_normalizer_iff_conjInv_image_eq
  refine
  { prime := hprime
    odd_prime := hpodd
    one_le_exponent := ha
    odd_natCard := hGodd
    le_of_left := Subgroup.map_subtype_le K
    le_of_right := Subgroup.map_subtype_le W₁
    not_isMulCommutative := not_isMulCommutative_map_subtype hna
    natCard_eq_pow := by rw [Subgroup.card_subtype]; exact hKcard
    normal := ?_
    coe_mul_coe := coe_mul_coe_map_subtype hcyc.mul_eq_univ
    inf_eq_bot := ?_
    coprime := by rw [Subgroup.card_subtype, Subgroup.card_subtype]; exact hcyc.coprime_natCard
    ne_bot := fun h0 => hcyc.left_ne_bot (map_subtype_eq_bot_iff.1 h0)
    isCyclic := isCyclic_map_subtype hcyc.isCyclic_left
    le_commutator := ?_
    natCard_eq_prime := by rw [Subgroup.card_subtype]; exact hW₂card
    inf_centralizer_eq := ?_
    normalizer_eq := hnormeq
    inf_conj_eq_bot := ?_ }
  · rw [subgroupOf_map_subtype_self]; exact hKn
  · rw [← map_subtype_inf, hcyc.inf_eq_bot, Subgroup.map_bot]
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hW₂comm
  · rintro e ⟨u, hu, rfl⟩ he1
    have hu1 : u ≠ 1 := fun hc => he1 (by rw [hc]; rfl)
    rw [show (L.subtype u) = ((u : G)) from rfl, ← map_subtype_inf_centralizer_singleton,
      hcyc.centralizer_eq u hu hu1]
  · intro g hg
    refine le_bot_iff.1 fun z hz => ?_
    obtain ⟨hzK, hzconj⟩ := Subgroup.mem_inf.1 hz
    by_contra hz1
    rw [Subgroup.mem_bot] at hz1
    have hgi : g⁻¹ ∉ L := fun hc => hg (by simpa using inv_mem hc)
    have hw : g⁻¹ * z * g ∈ ((K.map L.subtype : Subgroup G) : Set G) \ {1} := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzconj
        simpa [MulAut.smul_def, mul_assoc] using hzconj
      · simp only [Set.mem_singleton_iff]
        intro hc
        refine hz1 ?_
        have := congrArg (fun y => g * y * g⁻¹) hc
        simpa [mul_assoc] using this
    have hmem : z ∈ (((K.map L.subtype : Subgroup G) : Set G) \ {1})
        ∩ ((fun x => (g⁻¹)⁻¹ * x * g⁻¹) ''
          (((K.map L.subtype : Subgroup G) : Set G) \ {1})) := by
      refine ⟨⟨hzK, by simpa using hz1⟩, g⁻¹ * z * g, hw, ?_⟩
      group
    rw [hdisj g⁻¹ hgi] at hmem
    exact hmem

theorem isFreeCentralSection_centralSection
    (hs : IsPrimeFixedTISetup G p a L (K.map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hQ : (W₂.map L.subtype) ⊓ ((K.map L.subtype) ⊓
      centralizer ((K.map L.subtype : Subgroup G) : Set G)) = ⊥)
    (hLodd : Odd (Nat.card ↥L))
    (hmul : (K : Set ↥L) * (W₁ : Set ↥L) = Set.univ)
    (hinf : K ⊓ W₁ = ⊥) (hW₁bot : W₁ ≠ ⊥)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      = ((K.map L.subtype : Subgroup G) : Set G) \ {1}} = (L : Set G))
    (hdisj : ∀ g ∉ L, (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      ∩ ((fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})) = ∅) :
    IsFreeCentralSection p a L (K.map L.subtype) (W₁.map L.subtype)
      (centralSection (K.map L.subtype) (W₂.map L.subtype)) where
  prime := hs.prime
  odd_prime := hs.odd_prime
  one_le_exponent := hs.one_le_exponent
  natCard_P := hs.natCard_eq_pow
  odd_natCard_L := hLodd
  P_le := hs.le_of_left
  le_normalizer_P := le_of_eq hs.normalizer_eq.symm
  E_le := hs.le_of_right
  sup_eq := sup_map_subtype_eq hmul
  inf_eq_bot := by rw [← map_subtype_inf, hinf, Subgroup.map_bot]
  E_ne_bot := fun h0 => hW₁bot (map_subtype_eq_bot_iff.1 h0)
  Z_ne_bot := hs.centralSection_ne_bot
  le_normalizer_Z := (Subgroup.normal_subgroupOf_iff_le_normalizer
    hs.centralSection_le_middle).1 hs.centralSection_normal_subgroupOf
  Z_le_center := hs.centralSection_le.trans inf_le_left
  inf_centralizer_eq_bot := fun u hu hu1 =>
    hs.inf_centralizer_singleton_centralSection_eq_bot hQ hu hu1
  stabilizer_punctured_eq := hstab
  inter_conj_eq_empty := hdisj

theorem isCentralPrimeInduction_centralSection [Fintype G]
    (hs : IsPrimeFixedTISetup G p a L (K.map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hQ : (W₂.map L.subtype) ⊓ ((K.map L.subtype) ⊓
      centralizer ((K.map L.subtype : Subgroup G) : Set G)) ≠ ⊥)
    (hmul : (K : Set ↥L) * (W₁ : Set ↥L) = Set.univ)
    (hinf : K ⊓ W₁ = ⊥) (hW₁bot : W₁ ≠ ⊥)
    (hfix : ∀ u ∈ W₁, u ≠ 1 → ∀ k ∈ K, k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup ↥L) →
      k ∈ (⁅K, K⁆ : Subgroup ↥L))
    (hstab : {g : G | (fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      = ((K.map L.subtype : Subgroup G) : Set G) \ {1}} = (L : Set G))
    (hdisj : ∀ g ∉ L, (((K.map L.subtype : Subgroup G) : Set G) \ {1})
      ∩ ((fun x => g⁻¹ * x * g) '' (((K.map L.subtype : Subgroup G) : Set G) \ {1})) = ∅) :
    CentralPrimeInduction.IsCentralPrimeInduction p a L (K.map L.subtype) (W₁.map L.subtype)
      (centralSection (K.map L.subtype) (W₂.map L.subtype)) where
  prime := hs.prime
  odd_prime := hs.odd_prime
  one_le_exponent := hs.one_le_exponent
  natCard_P := hs.natCard_eq_pow
  odd_natCard_G := hs.odd_natCard
  P_le := hs.le_of_left
  le_normalizer_P := le_of_eq hs.normalizer_eq.symm
  E_le := hs.le_of_right
  sup_eq := sup_map_subtype_eq hmul
  inf_eq_bot := by rw [← map_subtype_inf, hinf, Subgroup.map_bot]
  E_ne_bot := fun h0 => hW₁bot (map_subtype_eq_bot_iff.1 h0)
  isCyclic_E := hs.isCyclic
  coprime_natCard := hs.coprime
  not_isMulCommutative_P := hs.not_isMulCommutative
  Z_le_commutator := by rw [centralSection_of_inf_ne_bot hQ]; exact hs.le_commutator
  natCard_Z := by rw [centralSection_of_inf_ne_bot hQ]; exact hs.natCard_eq_prime
  Z_le_center := hs.centralSection_le_center_middle hQ
  inf_centralizer_eq := fun u hu hu1 => by
    rw [centralSection_of_inf_ne_bot hQ]; exact hs.inf_centralizer_eq u hu hu1
  fixes_only_commutator_coset := forall_mem_commutator_map_subtype hfix
  sylow_natCard_P := hs.natCard_eq_pow_factorization
  stabilizer_punctured_eq := hstab
  inter_conj_eq_empty := hdisj

end Setup

end PrimeFixedTIPGroupTransport

end CFSG.FeitThompson
