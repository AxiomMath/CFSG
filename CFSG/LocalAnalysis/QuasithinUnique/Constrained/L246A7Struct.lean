module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Rep

public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (D : Alt7Data L)

@[expose] def rhoPre (H : Subgroup G) (K : Subgroup S₇) : Subgroup G where
  carrier := {g | g ∈ H ∧ g ∈ Subgroup.normalizer (L : Set G) ∧ rho D g ∈ K}
  one_mem' := ⟨H.one_mem, Subgroup.one_mem _, by rw [rho_one]; exact K.one_mem⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨H.mul_mem ha.1 hb.1, Subgroup.mul_mem _ ha.2.1 hb.2.1, by
      rw [rho_mul D ha.2.1 hb.2.1]; exact K.mul_mem ha.2.2 hb.2.2⟩
  inv_mem' := fun {a} ha =>
    ⟨H.inv_mem ha.1, Subgroup.inv_mem _ ha.2.1, by
      rw [rho_inv D ha.2.1]; exact K.inv_mem ha.2.2⟩

theorem mem_rhoPre {H : Subgroup G} {K : Subgroup S₇} {g : G} :
    g ∈ rhoPre D H K ↔ g ∈ H ∧ g ∈ Subgroup.normalizer (L : Set G) ∧ rho D g ∈ K := Iff.rfl

theorem rhoPre_le (H : Subgroup G) (K : Subgroup S₇) : rhoPre D H K ≤ H := fun _ hg => hg.1

theorem rho_pow {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    rho D (g ^ n) = (rho D g) ^ n := by
  induction n with
  | zero => simpa using rho_one D
  | succ n ih =>
    rw [pow_succ, rho_mul D (Subgroup.pow_mem _ hg n) hg, ih, pow_succ]

variable {T : Subgroup G}

omit [Finite G] in
theorem sup_le_normalizer (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTN

omit [Finite G] in
theorem exists_mul_of_mem_sup (hTN : T ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g ∈ L ⊔ T) : ∃ ℓ ∈ L, ∃ t ∈ T, g = ℓ * t := by
  have hg' : g ∈ ((L ⊔ T : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTN] at hg'
  obtain ⟨ℓ, hℓ, t, ht, e⟩ := hg'
  exact ⟨ℓ, hℓ, t, ht, e.symm⟩

omit [Finite G] in
theorem exists_pow_mul (hTN : T ≤ Subgroup.normalizer (L : Set G)) {ℓ t : G} (hℓ : ℓ ∈ L)
    (ht : t ∈ T) (n : ℕ) : ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨ℓ', hℓ', e⟩ := ih
    have hn : t ^ n ∈ T := T.pow_mem ht n
    have hc : t ^ n * ℓ * (t ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTN hn) ℓ).1 hℓ
    refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' hc, ?_⟩
    rw [pow_succ, e]
    group

theorem mem_blockQ_iff_rho {ℓ : G} (hℓ : ℓ ∈ L) : ℓ ∈ blockQ L ↔ rho D ℓ = 1 := by
  rw [rho_of_mem D hℓ]
  constructor
  · intro h
    have : (⟨ℓ, hℓ⟩ : ↥L) ∈ D.α.ker := by
      rw [D.hker]
      exact (mem_pCore_iff_mem_blockQ _).2 h
    exact congrArg Subtype.val ((MonoidHom.mem_ker).1 this)
  · intro h
    have : D.α ⟨ℓ, hℓ⟩ = 1 := Subtype.ext h
    have h2 : (⟨ℓ, hℓ⟩ : ↥L) ∈ D.α.ker := this
    rw [D.hker] at h2
    exact (mem_pCore_iff_mem_blockQ _).1 h2

theorem isPGroup_kerRho (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 (rhoPre D (L ⊔ T) ⊥) := by
  intro k
  obtain ⟨k, hk, hkN, hk1⟩ := k
  obtain ⟨ℓ, hℓ, t, ht, rfl⟩ := exists_mul_of_mem_sup hTN hk
  obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
  have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
  obtain ⟨ℓ', hℓ', e⟩ := exists_pow_mul hTN hℓ ht (2 ^ m)
  rw [hm', mul_one] at e
  have hρ : rho D ℓ' = 1 := by
    rw [← e, rho_pow D hkN, Subgroup.mem_bot.1 hk1, one_pow]
  have hQ : ℓ' ∈ blockQ L := (mem_blockQ_iff_rho D hℓ').2 hρ
  obtain ⟨s, hs⟩ := (C1.blockQ_isPGroup L) ⟨ℓ', hQ⟩
  have hs' : ℓ' ^ 2 ^ s = 1 := congrArg Subtype.val hs
  refine ⟨m + s, Subtype.ext ?_⟩
  show (ℓ * t) ^ 2 ^ (m + s) = 1
  rw [pow_add, pow_mul, e, hs']

@[expose] def StdLabel (D : Alt7Data L) (T : Subgroup G) : Prop :=
  (∀ ℓ ∈ T ⊓ L, rho D ℓ ∈ Pstd) ∧ (∀ a ∈ Pstd, ∃ ℓ ∈ T ⊓ L, rho D ℓ = a)

theorem exists_stdLabel (D : Alt7Data L) (hS : IsSylowTwoOf (T ⊓ L) L) :
    ∃ σ : A₇, StdLabel (D.conj σ) T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 ↥L := hp.toSylow hS.2.2
  have hPc : (P : Subgroup ↥L) = (T ⊓ L).subgroupOf L := rfl
  let P₀ : Sylow 2 A₇ := Sylow.mapSurjective D.hα P
  have hP₀ : (P₀ : Subgroup A₇) = ((T ⊓ L).subgroupOf L).map D.α := by
    rw [Sylow.coe_mapSurjective, hPc]
  obtain ⟨σ, hσ⟩ := exists_conj_Pstd P₀
  rw [hP₀] at hσ
  refine ⟨σ, ?_, ?_⟩
  · intro ℓ hℓ
    have hLℓ : ℓ ∈ L := hℓ.2
    rw [rho_of_mem (D.conj σ) hLℓ]
    have hmem : D.α ⟨ℓ, hLℓ⟩ ∈ ((T ⊓ L).subgroupOf L).map D.α :=
      ⟨⟨ℓ, hLℓ⟩, Subgroup.mem_subgroupOf.2 hℓ, rfl⟩
    have h2 : (MulAut.conj σ).toMonoidHom (D.α ⟨ℓ, hLℓ⟩) ∈
        Pstd.subgroupOf A₇ := by
      rw [← hσ]
      exact ⟨_, hmem, rfl⟩
    exact Subgroup.mem_subgroupOf.1 h2
  · intro a ha
    have haA : a ∈ alternatingGroup (Fin 7) := Pstd_le_alt ha
    have h1 : (⟨a, haA⟩ : A₇) ∈ Pstd.subgroupOf A₇ := Subgroup.mem_subgroupOf.2 ha
    rw [← hσ] at h1
    obtain ⟨b, hb, hba⟩ := h1
    obtain ⟨ℓ', hℓ', hℓ'b⟩ := hb
    refine ⟨ℓ', Subgroup.mem_subgroupOf.1 hℓ', ?_⟩
    rw [rho_of_mem (D.conj σ) ℓ'.2]
    show (((D.conj σ).α ⟨ℓ', ℓ'.2⟩ : A₇) : S₇) = a
    have : (D.conj σ).α ⟨ℓ', ℓ'.2⟩ = (MulAut.conj σ).toMonoidHom (D.α ℓ') := rfl
    rw [this, hℓ'b, hba]

theorem rho_normalizes_Pstd (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hstd : StdLabel D T)
    {t : G} (ht : t ∈ T) : ∀ a ∈ Pstd, (rho D t)⁻¹ * a * rho D t ∈ Pstd := by
  intro a ha
  obtain ⟨ℓ, hℓ, rfl⟩ := hstd.2 a ha
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hTN ht
  have hinvN : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ htN
  have hℓN : ℓ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hℓ.2
  have h1 : t⁻¹ * ℓ * t ∈ T ⊓ L := by
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hℓ.1) ht, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 hinvN ℓ).1 hℓ.2
    simpa using this
  have h2 := hstd.1 _ h1
  have h3 : rho D (t⁻¹ * ℓ * t) = (rho D t)⁻¹ * rho D ℓ * rho D t := by
    rw [rho_mul D (Subgroup.mul_mem _ hinvN hℓN) htN, rho_mul D hinvN hℓN, rho_inv D htN]
  rwa [h3] at h2

theorem rho_T_fix6 (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hstd : StdLabel D T) {t : G}
    (ht : t ∈ T) : rho D t 6 = 6 :=
  (normalizer_Pstd (rho_normalizes_Pstd D hTN hstd ht)).1

theorem rho_T_pres45 (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hstd : StdLabel D T) {t : G}
    (ht : t ∈ T) :
    (rho D t 4 = 4 ∧ rho D t 5 = 5) ∨ (rho D t 4 = 5 ∧ rho D t 5 = 4) :=
  (normalizer_Pstd (rho_normalizes_Pstd D hTN hstd ht)).2

theorem rho_T_conj_cc (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hstd : StdLabel D T) {t : G}
    (ht : t ∈ T) :
    rho D t * cc * (rho D t)⁻¹ = cc ∨ rho D t * cc * (rho D t)⁻¹ = cc⁻¹ :=
  conj_cc_of_pres _ (rho_T_fix6 D hTN hstd ht) (rho_T_pres45 D hTN hstd ht)

end CFSG.QuasithinUnique.L246A7
