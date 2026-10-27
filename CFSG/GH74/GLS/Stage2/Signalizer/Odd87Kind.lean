module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SecL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OneCls
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L4G

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

@[expose] def KindFactor (k : Kind) (Y : Type) [Group Y] : Prop :=
  match k with
  | .g2 | .psp4 | .l4 _ => IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r)
  | .m12 => False
  | .mcl => ∃ n : ℕ, 8 ≤ n ∧ n ≤ 9 ∧ IsSection Y (alternatingGroup (Fin n))
  | .ly => ∃ n : ℕ, 10 ≤ n ∧ n ≤ 11 ∧ IsSection Y (alternatingGroup (Fin n))

@[expose] def KindFactorAll (k : Kind) (Y : Type) [Group Y] : Prop :=
  match k with
  | .g2 | .psp4 | .m12 => IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r)
  | .l4 _ => IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) ∨ IsSection Y (alternatingGroup (Fin 7))
  | .mcl => ∃ n : ℕ, 8 ≤ n ∧ n ≤ 9 ∧ IsSection Y (alternatingGroup (Fin n))
  | .ly => ∃ n : ℕ, 10 ≤ n ∧ n ≤ 11 ∧ IsSection Y (alternatingGroup (Fin n))

theorem KindFactor.all {k : Kind} {Y : Type} [Group Y] (h : KindFactor k Y) : KindFactorAll k Y := by
  cases k
  · exact h
  · exact absurd h id
  · exact h
  · exact Or.inl h
  · exact h
  · exact h

theorem card_alt_dvd_factorial (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial n := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = Nat.card (Equiv.Perm (Fin n)) :=
    two_mul_nat_card_alternatingGroup
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm, Fintype.card_fin] at h2
  exact Dvd.intro 2 (by omega)

theorem KindFactorAll.card_dvd {k : Kind} {Y : Type} [Group Y] (h : KindFactorAll k Y)
    (hk : k = Kind.mcl ∨ k = Kind.ly) : Nat.card Y ∣ Nat.factorial 11 := by
  rcases hk with rfl | rfl <;>
  · obtain ⟨n, hn1, hn2, hs⟩ := h
    exact (hs.card_dvd).trans ((card_alt_dvd_factorial n (by omega)).trans
      (Nat.factorial_dvd_factorial (by omega)))

theorem exists_mul_of_mem_sup' {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

theorem isSection_of_commuting_sup {B : Type*} [Group B] {Y : Type*} [Group Y] [IsSimpleGroup Y]
    {L₁ L₂ : Subgroup B} (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (h : IsSection Y ↥(L₁ ⊔ L₂)) : IsSection Y ↥L₁ ∨ IsSection Y ↥L₂ := by
  have hN : (L₁.subgroupOf (L₁ ⊔ L₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : b * x * b⁻¹ = x := by
        have := hcomm x hx b hb
        calc b * x * b⁻¹ = (b * x) * b⁻¹ := rfl
          _ = (x * b) * b⁻¹ := by rw [this]
          _ = x := by group
      rw [h1]; exact hx
    · intro hx
      have h2 : b⁻¹ * (b * x * b⁻¹) * b = x := by group
      have h3 := hcomm (b * x * b⁻¹) hx b⁻¹ (L₂.inv_mem hb)
      have h4 : b⁻¹ * (b * x * b⁻¹) * b = b * x * b⁻¹ := by
        calc b⁻¹ * (b * x * b⁻¹) * b = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by
            have h5 := hcomm (b * x * b⁻¹) hx b hb
            rw [h5]
          _ = b * x * b⁻¹ := by group
      rw [← h2, h4]; exact hx
  rcases h.dichotomy (L₁.subgroupOf (L₁ ⊔ L₂)) with h1 | h2
  · left
    exact IsSection.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_left : L₁ ≤ L₁ ⊔ L₂)).symm h1
  · right
    refine IsSection.of_surjective ((QuotientGroup.mk' (L₁.subgroupOf (L₁ ⊔ L₂))).comp
      (Subgroup.inclusion (le_sup_right : L₂ ≤ L₁ ⊔ L₂))) ?_ h2
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup' hcomm w.2
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(L₁ ⊔ L₂)) : ↥(L₁ ⊔ L₂) ⧸ L₁.subgroupOf (L₁ ⊔ L₂)) = _
    have hw : w = (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(L₁ ⊔ L₂)) * ⟨b, Subgroup.mem_sup_right hb⟩ := Subtype.ext hab
    rw [hw, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(L₁ ⊔ L₂)) : ↥(L₁ ⊔ L₂) ⧸ L₁.subgroupOf (L₁ ⊔ L₂)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
    rw [this, one_mul]

theorem isSolvable_sup_of_commute {B : Type*} [Group B] {A C : Subgroup B}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) [Group.IsSolvable ↥A] [Group.IsSolvable ↥C] :
    Group.IsSolvable ↥(A ⊔ C) := by
  let f : ↥A × ↥C →* B := (A.subtype).noncommCoprod C.subtype (fun a c => hcomm a a.2 c c.2)
  have hrange : f.range = A ⊔ C := by
    apply le_antisymm
    · rintro _ ⟨⟨a, c⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 c.2
    · intro x hx
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup' hcomm hx
      exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), rfl⟩
  have : Group.IsSolvable ↥f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  rw [← hrange]
  exact this

section Bar

variable {G : Type} [Group G] [Finite G]

theorem isSection_bar (z : G) {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y ↥(Cen z)) : IsSection Y (CentralizerBar z) := by
  rcases h.dichotomy (pPrimeCore 2 ↥(Cen z)) with h1 | h2
  · exact absurd (h1.isSolvable Stage2.Final.Thm4.pPrimeCore_solvable) hns
  · exact h2

theorem isSection_LBar (z : G) (hI : PerfInner z) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y (CentralizerBar z)) : IsSection Y ↥(LBar z) := by
  obtain ⟨P, hP, hPs⟩ := exists_perfect_section hns h
  have hle : P ≤ oPrimePResidual 2 (CentralizerBar z) ⊓ InnerE z :=
    le_inf (IVK.Proofs2.Ivk93Adapt.perfect_le_oPrimePResidual _ hP) (hI P hP)
  rw [← Stage1.Thm6.Prod.LBar_eq z] at hle
  exact IsSection.of_le_le hle hPs

omit [Finite G] in
theorem kindFactor_of_pair {z : G} {L₁ L₂ : Subgroup (CentralizerBar z)}
    {r₁ r₂ : ℕ} (hprod : IsCentralProd L₁ L₂ (LBar z)) (hr₁ : Odd r₁) (hr₂ : Odd r₂)
    (hS₁ : HasSL2Model ↥L₁ (fun q => q = r₁)) (hS₂ : HasSL2Model ↥L₂ (fun q => q = r₂))
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y) (h : IsSection Y ↥(LBar z)) :
    IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
  obtain ⟨hsup, hcomm, -⟩ := hprod
  rw [← hsup] at h
  rcases isSection_of_commuting_sup hcomm h with h1 | h2
  · exact simple_sec_of_SL2model hr₁ hS₁ hns h1
  · exact simple_sec_of_SL2model hr₂ hS₂ hns h2

omit [Finite G] in
theorem isSection_alt_of_cover {z : G} {n : ℕ} (hc : IsDoubleCoverOfAlt (CentralizerBar z) n)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y (CentralizerBar z)) : IsSection Y (alternatingGroup (Fin n)) := by
  obtain ⟨-, -, ⟨e⟩⟩ := hc
  rcases h.dichotomy (center (CentralizerBar z)) with h1 | h2
  · exact absurd (h1.isSolvable inferInstance) hns
  · exact IsSection.of_equiv e.symm h2

theorem isSolvable_cbar_m12 {z : G} {S : Subgroup G} (h : Stage1M12 G z S) :
    Group.IsSolvable (CentralizerBar z) := by
  obtain ⟨A, B, hprod, ⟨eA⟩, ⟨eB⟩, -⟩ := h.W_shape
  obtain ⟨hsup, hcomm, -⟩ := hprod
  obtain ⟨hWn, ⟨eq⟩⟩ := h.quot
  have hQ8 : Group.IsSolvable (QuaternionGroup 2) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (QuaternionGroup 2) :=
      IsPGroup.of_card (n := 3) (by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num)
    have := hp.isNilpotent
    infer_instance
  have hA : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective (f := eA.toMonoidHom) eA.injective
  have hB : Group.IsSolvable ↥B := Group.isSolvable_of_isSolvable_injective (f := eB.toMonoidHom) eB.injective
  have hW : Group.IsSolvable ↥(WBar z) := by
    rw [← hsup]
    exact isSolvable_sup_of_commute hcomm
  have := hWn
  have hP3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hq : Group.IsSolvable (CentralizerBar z ⧸ WBar z) :=
    Group.isSolvable_of_isSolvable_injective (f := eq.toMonoidHom) eq.injective
  exact Group.isSolvable_of_ker_le_range (WBar z).subtype (QuotientGroup.mk' (WBar z)) (by simp)

end Bar

theorem kindFactor_of_section_C {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y ↥(Cen z)) : KindFactor k Y := by
  have hbar := isSection_bar z hns h
  have hd := hctx.data
  cases hd with
  | g2 hg =>
    obtain ⟨r₁, r₂, L₁, L₂, hshape⟩ := hg.shape
    obtain ⟨hr₁, hr₂, -, hprod, hS₁, hS₂, -⟩ := hshape
    exact kindFactor_of_pair hprod hr₁ hr₂ hS₁ hS₂ hns (isSection_LBar z hg.perf hns hbar)
  | m12 hm => exact absurd (hbar.isSolvable (isSolvable_cbar_m12 hm)) hns
  | psp4 hp =>
    obtain ⟨q, L₁, L₂, hP⟩ := hp
    exact kindFactor_of_pair hP.pair.prod hP.pair.odd hP.pair.odd hP.pair.sl₁ hP.pair.sl₂ hns
      (isSection_LBar z (perfInner_of_pair hP.pair) hns hbar)
  | l4 ε hp =>
    obtain ⟨q, L₁, L₂, hP⟩ := hp
    exact kindFactor_of_pair hP.pair.prod hP.pair.odd hP.pair.odd hP.pair.sl₁ hP.pair.sl₂ hns
      (isSection_LBar z (perfInner_of_pair hP.pair) hns hbar)
  | mcl hs =>
    obtain ⟨n, hn, hS⟩ := hs
    exact ⟨n, by omega, by omega, isSection_alt_of_cover hS.cover hns hbar⟩
  | ly hs =>
    obtain ⟨n, hn, hS⟩ := hs
    exact ⟨n, by omega, by omega, isSection_alt_of_cover hS.cover hns hbar⟩

theorem kindFactor_of_section_sec {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀}
    [H₁.Normal] {hz : z ∈ H₀} {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y ↥(centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)))) : KindFactor k Y := by
  have hz2 : z * z = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hctx.orderOf_z)
    rwa [pow_two] at this
  obtain ⟨D, f, hD, hf⟩ := csec_of_sig4B H₁ hz hz2 hsig.odd
  exact kindFactor_of_section_C hctx hns (IsSection.of_le_le hD (IsSection.of_surjective f hf h))

@[expose] def InvSec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ x : G, orderOf x = 2 → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y], ¬ Group.IsSolvable Y →
      IsSection Y ↥(centralizer ({x} : Set G)) → KindFactorAll k Y

@[expose] def SecX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    (k = Kind.psp4 ∨ k = Kind.m12 ∨ ∃ ε : Bool, k = Kind.l4 ε) →
    ∀ x : G, IsNonCentralInvolution x → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y], ¬ Group.IsSolvable Y →
      IsSection Y ↥(centralizer ({x} : Set G)) → KindFactorAll k Y

section Conj

variable {G : Type} [Group G]

theorem cenConj_nonempty {z x : G} (c : G) (hc : c * z * c⁻¹ = x) :
    Nonempty (↥(centralizer ({z} : Set G)) ≃* ↥(centralizer ({x} : Set G))) := by
  have hmem : ∀ g : G, g ∈ centralizer ({z} : Set G) → c * g * c⁻¹ ∈ centralizer ({x} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc]
    calc c * g * c⁻¹ * (c * z * c⁻¹) = c * (g * z) * c⁻¹ := by group
      _ = c * (z * g) * c⁻¹ := by rw [hg]
      _ = c * z * c⁻¹ * (c * g * c⁻¹) := by group
  have hmem' : ∀ g : G, g ∈ centralizer ({x} : Set G) → c⁻¹ * g * c ∈ centralizer ({z} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc] at hg
    have : g * (c * z * c⁻¹) = (c * z * c⁻¹) * g := hg
    calc c⁻¹ * g * c * z = c⁻¹ * (g * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * g) * c := by rw [this]
      _ = z * (c⁻¹ * g * c) := by group
  exact ⟨{ toFun := fun g => ⟨c * g * c⁻¹, hmem g g.2⟩
           invFun := fun g => ⟨c⁻¹ * g * c, hmem' g g.2⟩
           left_inv := fun g => Subtype.ext (by simp [mul_assoc])
           right_inv := fun g => Subtype.ext (by simp [mul_assoc])
           map_mul' := fun g h => Subtype.ext (by simp [mul_assoc]) }⟩

end Conj

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_lift {H₀ : Subgroup G} (H₁ : Subgroup ↥H₀) [H₁.Normal]
    (hodd : Odd (Nat.card ↥H₁)) {t : Sec H₀ H₁} (ht : t * t = 1) :
    ∃ h : ↥H₀, h * h = 1 ∧ (QuotientGroup.mk h : Sec H₀ H₁) = t := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hmk : (QuotientGroup.mk (g ^ m) : Sec H₀ H₁) = QuotientGroup.mk g := by
    obtain ⟨j, rfl⟩ := hm
    rw [QuotientGroup.mk_pow, pow_succ, pow_mul, sq, ht, one_pow, one_mul]
  refine ⟨g ^ m, ?_, hmk⟩
  have hsq : (g ^ m) ^ 2 ∈ H₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, sq, ht]
  have hpow : ((g ^ m) ^ 2) ^ (2 ^ a) = 1 := by
    have h1 : (g ^ m) ^ (2 ^ a) = 1 := by
      rw [← pow_mul, mul_comm, ← hnm]; exact pow_orderOf_eq_one g
    calc ((g ^ m) ^ 2) ^ (2 ^ a) = ((g ^ m) ^ (2 ^ a)) ^ 2 := pow_right_comm _ _ _
      _ = 1 := by rw [h1, one_pow]
  have hd1 : orderOf (⟨(g ^ m) ^ 2, hsq⟩ : ↥H₁) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hpow
  have hd2 : orderOf (⟨(g ^ m) ^ 2, hsq⟩ : ↥H₁) ∣ Nat.card ↥H₁ := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ a) (Nat.card ↥H₁) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf (⟨(g ^ m) ^ 2, hsq⟩ : ↥H₁) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have h2 : (⟨(g ^ m) ^ 2, hsq⟩ : ↥H₁) = 1 := orderOf_eq_one_iff.mp h1
  have h3 : (g ^ m) ^ 2 = 1 := congrArg (fun x : ↥H₁ => (x : ↥H₀)) h2
  rwa [sq] at h3

end Lift

section Central

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem isConj_of_central (hctx : Stage2Ctx G z k S) {x : G} (hx : IsCentralInvolution x) :
    IsConj z x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hx2, S', hxS', hxc⟩ := hx
  have hS'G : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S'.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S'.not_dvd_index
  obtain ⟨c, -, hc⟩ := hctx.sylow_top.exists_mem_conj hS'G
  have hyS : c⁻¹ * x * c ∈ S := (hc x).1 hxS'
  have hycomm : ∀ s ∈ S, s * (c⁻¹ * x * c) = (c⁻¹ * x * c) * s := by
    intro s hs
    have hs' : c * s * c⁻¹ ∈ (S' : Subgroup G) :=
      (hc _).2 (by simpa [mul_assoc] using hs)
    have h1 := hxc _ hs'
    calc s * (c⁻¹ * x * c) = c⁻¹ * ((c * s * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * s * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * x * c) * s := by group
  have hy2 : orderOf (c⁻¹ * x * c) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) x
    rw [MulAut.conj_apply, show c⁻¹ * x * c⁻¹⁻¹ = c⁻¹ * x * c by simp] at this
    rw [this]; exact hx2
  have hyz : c⁻¹ * x * c = z := hctx.data.base.zcen _ hyS hycomm hy2
  exact isConj_iff.mpr ⟨c, by rw [← hyz]; group⟩

end Central

theorem invSec_of_secX (hX : SecX) : InvSec := by
  intro G _ _ z k S hctx x hx2 Y _ _ hns h
  have hz2 := hctx.orderOf_z
  have hdirect : IsConj z x → KindFactorAll k Y := by
    intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    obtain ⟨e⟩ := cenConj_nonempty c hc
    exact (kindFactor_of_section_C hctx hns (IsSection.of_equiv e h)).all
  have hd := hctx.data
  cases hd with
  | g2 hg => exact hdirect (hg.one_class z x hz2 hx2)
  | mcl hs =>
    obtain ⟨n, hn, hS⟩ := hs
    exact hdirect (hS.one_class z x hz2 hx2)
  | ly hs =>
    obtain ⟨n, hn, hS⟩ := hs
    exact hdirect (hS.one_class z x hz2 hx2)
  | m12 hm =>
    by_cases hxc : IsCentralInvolution x
    · exact hdirect (isConj_of_central hctx hxc)
    · exact hX G z _ S hctx (Or.inr (Or.inl rfl)) x ⟨hx2, hxc⟩ Y hns h
  | psp4 hp =>
    by_cases hxc : IsCentralInvolution x
    · exact hdirect (isConj_of_central hctx hxc)
    · exact hX G z _ S hctx (Or.inl rfl) x ⟨hx2, hxc⟩ Y hns h
  | l4 ε hp =>
    by_cases hxc : IsCentralInvolution x
    · exact hdirect (isConj_of_central hctx hxc)
    · exact hX G z _ S hctx (Or.inr (Or.inr ⟨ε, rfl⟩)) x ⟨hx2, hxc⟩ Y hns h

theorem layerBar_kindFactor (hInv : InvSec) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal]
    {hz : z ∈ H₀} {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (hsig : Sig4B G z H₀ H₁ hz p X)
    (hyp : Hyp42 (zSec z H₀ hz H₁) X) (hZ : center ↥(layer (Sec H₀ H₁)) ≠ ⊥) :
    KindFactorAll k (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) := by
  set A := Sec H₀ H₁ with hA
  set K : Subgroup A := layer A with hK
  have hq : IsQuasisimple ↥K := hyp.2.1
  have hZ2 : center ↥K = pCore 2 ↥K := hyp.2.2.1
  have hsimple : IsSimpleGroup (↥K ⧸ center ↥K) := hq.2.1
  have hns : ¬ Group.IsSolvable (↥K ⧸ center ↥K) := by
    intro hs
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (hcomm a b)
  obtain ⟨s, hsZ, hs2⟩ : ∃ s : ↥K, s ∈ center ↥K ∧ orderOf s = 2 := by
    have hp : IsPGroup 2 ↥(center ↥K) := by
      rw [hZ2]; exact pCore_isPGroup (p := 2) (G := ↥K)
    have hcn : Nontrivial ↥(center ↥K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
    obtain ⟨u, hu1⟩ : ∃ u : ↥(center ↥K), u ≠ 1 := exists_ne 1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hp) u
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hu1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have h2dvd : 2 ∣ orderOf u := by rw [hj]; exact dvd_pow_self 2 hj0
    refine ⟨((u ^ (orderOf u / 2) : ↥(center ↥K)) : ↥K), (u ^ (orderOf u / 2)).2, ?_⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos u).ne' h2dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs2, pow_two] at this
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    omega
  set sb : A := (s : A) with hsb
  have hsb2 : sb * sb = 1 := by simpa using congrArg (fun y : ↥K => (y : A)) hss
  have hsb1 : sb ≠ 1 := fun h1 => hs1 (Subtype.ext h1)
  obtain ⟨st, hst, hlift⟩ := exists_involution_lift H₁ hsig.odd hsb2
  set x : G := (st : G) with hx
  have hx2 : x * x = 1 := congrArg (fun y : ↥H₀ => (y : G)) hst
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : st = 1 := Subtype.ext h1
    apply hsb1
    rw [← hlift, h2]
    rfl
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨D, f, hD, hf⟩ := csec_of_sig4B (z := x) H₁ st.2 hx2 hsig.odd
  have hzs : zSec x H₀ st.2 H₁ = sb := by
    show (QuotientGroup.mk (⟨x, st.2⟩ : ↥H₀) : Sec H₀ H₁) = sb
    exact hlift
  have hKle : K ≤ centralizer ({sb} : Set A) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp hsZ ⟨k, hk⟩
    exact congrArg (fun y : ↥K => (y : A)) this
  have h1 : IsSection (↥K ⧸ center ↥K) ↥(centralizer ({sb} : Set A)) :=
    ⟨K.subgroupOf (centralizer ({sb} : Set A)),
      (QuotientGroup.mk' (center ↥K)).comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKle).surjective⟩
  rw [← hzs] at h1
  have h3 := IsSection.of_le_le hD (IsSection.of_surjective f hf h1)
  exact hInv G z k S hctx x hxord (↥K ⧸ center ↥K) hns h3

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
