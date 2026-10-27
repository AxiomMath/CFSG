module

public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LieType.BorelTits.Transfer

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

universe u v

variable {X : Type u} [Group X]

@[expose] def TitsConclusion (r : ℕ) (U : Subgroup X) : Prop :=
  ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
    Subgroup.normalizer (U : Set X) ≤ P ∧
    pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ pCoreOf r P ∧
    U ≤ pCoreOf r P ∧
    (S : Subgroup X) ≤ P

variable (X) in
@[expose] def HoldsTits (r : ℕ) : Prop :=
  ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup r U → TitsConclusion r U

theorem Holds.holdsTits {r : ℕ} (h : Holds X r) : HoldsTits X r := by
  intro U hU hUr
  obtain ⟨S, P, hP, hN, hcore, hUP, hS⟩ := h U hU hUr
  exact ⟨S, P, hP, hN, hcore, hUP, Subgroup.le_normalizer.trans hS⟩

theorem TitsConclusion.map_mulEquiv {Y : Type v} [Group Y] [Finite X] {r : ℕ} [Fact r.Prime]
    (e : X ≃* Y) {U : Subgroup X} (h : TitsConclusion r U) :
    TitsConclusion r (U.map e.toMonoidHom) := by
  obtain ⟨S, P, hP, hN, hcore, hU, hS⟩ := h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨Sylow.mapSurjective hsurj S, P.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro htop
    apply hP
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by ext x; simp
    rw [hid, Subgroup.map_id] at this
    rw [this]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hN
  · rw [← Subgroup.map_equiv_normalizer_eq, pCoreOf_map_mulEquiv, pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hcore
  · rw [pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hU
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hS

theorem HoldsTits.of_mulEquiv {Y : Type v} [Group Y] [Finite X] {r : ℕ} [Fact r.Prime]
    (e : X ≃* Y) (h : HoldsTits X r) : HoldsTits Y r := by
  intro V hV hVp
  have hVeq : (V.map e.symm.toMonoidHom).map e.toMonoidHom = V := by
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
    rw [hid, Subgroup.map_id]
  have hne : V.map e.symm.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVeq, hbot, Subgroup.map_bot]
  have := (h _ hne (hVp.map e.symm.toMonoidHom)).map_mulEquiv e
  rwa [hVeq] at this

theorem coprime_card_center_of_forall [Finite X] {r : ℕ} [Fact r.Prime]
    (h : ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup r U →
      ∃ P : Subgroup X, P ≠ ⊤ ∧ Subgroup.normalizer (U : Set X) ≤ P) :
    Nat.Coprime (Nat.card (Subgroup.center X)) r := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdvd
  set R : Subgroup X := Subgroup.zpowers (z : X) with hR
  have hord : orderOf (z : X) = r := by rw [Subgroup.orderOf_coe]; exact hz
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hz1 : (z : X) = 1 := by
      have : (z : X) ∈ R := Subgroup.mem_zpowers _
      rwa [hbot, Subgroup.mem_bot] at this
    rw [hz1, orderOf_one] at hord
    exact (Fact.out : r.Prime).one_lt.ne hord
  have hRp : IsPGroup r R := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨P, hP, hN⟩ := h R hRne hRp
  apply hP
  rw [eq_top_iff]
  refine le_trans (fun g _ => ?_) hN
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcomm : ∀ y : X, (z : X) * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp z.2 y).symm
  have hcen : ∀ y ∈ R, ∀ w : X, w * y * w⁻¹ = y := by
    intro y hy w
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute w ((z : X) ^ k) := (Commute.symm (hcomm w : Commute (z : X) w)).zpow_right k
    rw [this.eq, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hx
    rw [hcen x hx g]
    exact hx
  · intro hx
    have h1 := hcen _ hx g⁻¹
    rw [inv_inv] at h1
    rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h1]
    exact hx

theorem Holds.coprime_card_center [Finite X] {r : ℕ} [Fact r.Prime] (h : Holds X r) :
    Nat.Coprime (Nat.card (Subgroup.center X)) r :=
  coprime_card_center_of_forall fun U hU hUr => by
    obtain ⟨-, P, hP, hN, -⟩ := h U hU hUr
    exact ⟨P, hP, hN⟩

theorem HoldsTits.coprime_card_center [Finite X] {r : ℕ} [Fact r.Prime] (h : HoldsTits X r) :
    Nat.Coprime (Nat.card (Subgroup.center X)) r :=
  coprime_card_center_of_forall fun U hU hUr => by
    obtain ⟨-, P, hP, hN, -⟩ := h U hU hUr
    exact ⟨P, hP, hN⟩

theorem HoldsTits.quotient {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) (h : HoldsTits G r) : HoldsTits (G ⧸ Z) r := by
  intro U hU hUr
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨U₀, hU₀, hU₀U⟩ := exists_isPGroup_map_eq Z hUr
  have hne : U₀ ≠ ⊥ := by
    rintro rfl
    exact hU (by rw [← hU₀U, Subgroup.map_bot])
  obtain ⟨S₀, P₀, hP₀, hN₀, hcore₀, -, hS₀⟩ := h U₀ hne hU₀
  have hNU : Subgroup.normalizer (U₀ : Set G) =
      (Subgroup.normalizer (U : Set (G ⧸ Z))).comap (QuotientGroup.mk' Z) := by
    rw [normalizer_eq_comap_normalizer_map Z hZ hZr hU₀, hU₀U]
  have hle : ∀ V : Subgroup (G ⧸ Z), V.comap (QuotientGroup.mk' Z) ≤ P₀ →
      V ≤ P₀.map (QuotientGroup.mk' Z) := fun V hV =>
    (Subgroup.map_comap_eq_self_of_surjective hπ V).symm.le.trans (Subgroup.map_mono hV)
  have hcore : pCoreOf r (Subgroup.normalizer (U : Set (G ⧸ Z))) ≤
      pCoreOf r (P₀.map (QuotientGroup.mk' Z)) := by
    refine (pCoreOf_le_map_pCoreOf_comap Z hZ hZr _).trans ?_
    rw [← hNU]
    exact (Subgroup.map_mono hcore₀).trans (map_pCoreOf_le _ P₀)
  have hZP : Z ≤ P₀ := by
    refine le_trans ?_ hN₀
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : ∀ y : G, z * y * z⁻¹ = y := fun y => by
      rw [(Subgroup.mem_center_iff.mp (hZ hz) y).symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
  refine ⟨Sylow.mapSurjective hπ S₀, P₀.map (QuotientGroup.mk' Z), ?_,
    hle _ (hNU ▸ hN₀), hcore, (le_pCoreOf_normalizer r U hUr).trans hcore, ?_⟩
  · intro htop
    apply hP₀
    have hker : (QuotientGroup.mk' Z).ker ≤ P₀ := by
      rw [QuotientGroup.ker_mk']
      exact hZP
    rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hS₀

theorem Holds.center_quotient [Finite X] {r : ℕ} [Fact r.Prime] (h : Holds X r) :
    Holds (X ⧸ Subgroup.center X) r :=
  Holds.quotient _ le_rfl h.coprime_card_center h

theorem HoldsTits.center_quotient [Finite X] {r : ℕ} [Fact r.Prime] (h : HoldsTits X r) :
    HoldsTits (X ⧸ Subgroup.center X) r :=
  HoldsTits.quotient _ le_rfl h.coprime_card_center h

theorem holdsTits_of_normal_of_isPGroup_quotient [Finite X] {r : ℕ} [Fact r.Prime]
    {Y : Subgroup X} [Y.Normal] (hY : IsPGroup r (X ⧸ Y)) (h : Holds X r) : HoldsTits Y r :=
  fun V hV hVp => conclusion_of_normal_of_isPGroup_quotient hY h V hV hVp

end CFSG.LieType.BorelTits
