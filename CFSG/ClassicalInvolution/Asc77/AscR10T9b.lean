module

public import CFSG.ClassicalInvolution.Asc77.AscR10T9a
public import CFSG.ClassicalInvolution.AschTight.S1911SecE
public import CFSG.ClassicalInvolution.Uniform.UStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



open CFSG.ClassicalInvolution.Uniform

section Cross

variable {a : G}

theorem map_conjSub_crossIn (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    (conjSub c (crossIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  rw [conjSub_subgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left]
  calc conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G))
      ≤ conjSub (c : G) (Subgroup.centralizer ({a} : Set G)) := Subgroup.map_mono inf_le_right
    _ = Subgroup.centralizer ({a} : Set G) :=
        conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer c.2)

theorem conjSub_inf_centralizer {c : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G)) :
    conjSub c (K ⊓ Subgroup.centralizer ({a} : Set G)) =
      conjSub c K ⊓ Subgroup.centralizer ({a} : Set G) := by
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective]
  change conjSub c K ⊓ conjSub c (Subgroup.centralizer ({a} : Set G)) = _
  rw [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hc)]

theorem conjSub_cross_eq {c₁ c₂ : G} (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G)) (h : conjSub c₁ K = conjSub c₂ K) :
    conjSub c₁ (K ⊓ Subgroup.centralizer ({a} : Set G)) =
      conjSub c₂ (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  rw [conjSub_inf_centralizer hc₁, conjSub_inf_centralizer hc₂, h]

theorem conjSub_ne_of_ne_cross {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (hne : conjSub c₁ (crossIn K a) ≠ conjSub c₂ (crossIn K a)) :
    conjSub (c₁ : G) K ≠ conjSub (c₂ : G) K := by
  intro h
  apply hne
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_crossIn, map_conjSub_crossIn, conjSub_cross_eq c₁.2 c₂.2 h]

theorem mem_normalizer_conjSub_of_cross (c v : ↥(Subgroup.centralizer ({a} : Set G)))
    (hv : (v : G) ∈ Subgroup.normalizer ((conjSub (c : G) K : Subgroup G) : Set G)) :
    v ∈ Subgroup.normalizer ((conjSub c (crossIn K a) :
        Subgroup ↥(Subgroup.centralizer ({a} : Set G))) :
          Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [← conjSub_mul, map_conjSub_crossIn, map_conjSub_crossIn, Subgroup.coe_mul,
    conjSub_inf_centralizer (Subgroup.mul_mem _ v.2 c.2), conjSub_inf_centralizer c.2,
    conjSub_mul, conjSub_eq_of_mem_normalizer hv]

theorem le_conjSub_of_mem_cross (c : ↥(Subgroup.centralizer ({a} : Set G)))
    {x : ↥(Subgroup.centralizer ({a} : Set G))} (hx : x ∈ conjSub c (crossIn K a)) :
    (x : G) ∈ conjSub (c : G) K := by
  have h : (x : G) ∈
      (conjSub c (crossIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype := ⟨x, hx, rfl⟩
  rw [map_conjSub_crossIn, conjSub_inf_centralizer c.2] at h
  exact h.1

theorem commutator_le_oddCoreOf_conjFamily_cross (c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G)))
    (h : ⁅conjSub (c₁ : G) K, conjSub (c₂ : G) K⁆ ≤ oddCoreOf (conjSub (c₁ : G) K)) :
    ⁅conjSub c₁ (crossIn K a), conjSub c₂ (crossIn K a)⁆ ≤
      oddCoreOf (conjSub c₁ (crossIn K a)) := by
  have hOJ : oddCoreOf (conjSub (c₁ : G) K) ≤ conjSub (c₁ : G) K := Subgroup.map_subtype_le _
  have key : ∀ y ∈ conjSub (c₂ : G) K, ∀ w ∈ conjSub (c₁ : G) K,
      y * w * y⁻¹ ∈ conjSub (c₁ : G) K := by
    intro y hy w hw
    have hc : ⁅y, w⁆ ∈ conjSub (c₁ : G) K := hOJ (h (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy hw))
    have e : y * w * y⁻¹ = ⁅y, w⁆ * w := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hc hw
  have hJN : ∀ y ∈ conjSub (c₂ : G) K, y ∈ Subgroup.normalizer ((conjSub (c₁ : G) K : Subgroup G) :
      Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact key y hy w
    · intro hw
      have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hw
      simpa [mul_assoc] using this
  have hMN : ∀ y ∈ conjSub c₂ (crossIn K a), y ∈ Subgroup.normalizer
      ((conjSub c₁ (crossIn K a) : Subgroup ↥(Subgroup.centralizer ({a} : Set G))) :
        Set ↥(Subgroup.centralizer ({a} : Set G))) :=
    fun y hy => mem_normalizer_conjSub_of_cross c₁ y (hJN _ (le_conjSub_of_mem_cross c₂ hy))
  have hcomm : ⁅conjSub c₁ (crossIn K a), conjSub c₂ (crossIn K a)⁆ ≤
      conjSub c₁ (crossIn K a) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap (Subgroup.centralizer ({a} : Set G)).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨?_, ?_⟩
    · have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ conjSub c₁ (crossIn K a) :=
        (Subgroup.mem_normalizer_iff.mp (hMN g₂ hg₂) _).mp (Subgroup.inv_mem _ hg₁)
      have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hg₁ h1
    · have h2 := h (Subgroup.commutator_mem_commutator (le_conjSub_of_mem_cross c₁ hg₁)
        (le_conjSub_of_mem_cross c₂ hg₂))
      rw [commutatorElement_def] at h2 ⊢
      exact h2
  refine hcomm.trans (le_oddCoreOf_of_le_of_odd inf_le_left ?_ ?_)
  · intro m hm
    have hmN : (m : G) ∈ Subgroup.normalizer ((oddCoreOf (conjSub (c₁ : G) K) : Subgroup G) :
        Set G) :=
      mem_normalizer_oddCore_of_mem_normalizer
        (Subgroup.le_normalizer (le_conjSub_of_mem_cross c₁ hm))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx1) (Subgroup.inv_mem _ hm),
        (Subgroup.mem_normalizer_iff.mp hmN _).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hmN _).mpr hx2⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hx1) hm
      simpa [mul_assoc] using this
  · have hle : (conjSub c₁ (crossIn K a) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap (Subgroup.centralizer ({a} : Set G)).subtype).map
          (Subgroup.centralizer ({a} : Set G)).subtype ≤ oddCoreOf (conjSub (c₁ : G) K) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    exact (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le hle)

end Cross


theorem Std20.t9_isUniqueInvolution_conjSub (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (crossIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI := d.viol.hzK.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI.ne_one (congrArg Subtype.val h), Subtype.ext hI.sq, fun y hy hy2 => ?_⟩
  rcases hI.unique _ (le_conjSub_of_mem_cross c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem Std20.t9_coe_eq_of_isUniqueInvolution (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (c : ↥(Subgroup.centralizer ({a} : Set G))) {u : ↥(Subgroup.centralizer ({a} : Set G))}
    (hu : IsUniqueInvolution (conjSub c (crossIn K a)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hI := d.viol.hzK.conj (c : G)
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact (hI.unique _ (le_conjSub_of_mem_cross c hu.mem) hsq).resolve_left hne

theorem Std20.t9_omega5_conjFamily (d : Std20 p f K K' J S R R' W V z t) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a),
    ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hΩ := d.hyp
  have hI := d.viol.hzK
  have hJne := conjSub_ne_of_ne_cross hne
  have hu' := d.t9_coe_eq_of_isUniqueInvolution c₁ hu
  have hvJ := le_conjSub_of_mem_cross c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem_cross c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hJne _ (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of_cross c₁ v hN

theorem Std20.t9_omega4_conjFamily (d : Std20 p f K K' J S R R' W V z t) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a), ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := d.hyp
  have hJne := conjSub_ne_of_ne_cross hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hJne
  have hdvd : Nat.card ↥(conjSub c₁ (crossIn K a) ⊓ conjSub c₂ (crossIn K a)) ∣
      Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨le_conjSub_of_mem_cross c₁ hx.1, le_conjSub_of_mem_cross c₂ hx.2⟩
  have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ (crossIn K a) ⊓
      conjSub c₂ (crossIn K a))) ≤
        padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
  refine ⟨hval.trans h4a, fun h1 => ?_⟩
  have hc := h4b (le_antisymm h4a (h1 ▸ hval))
  refine le_inf (commutator_le_oddCoreOf_conjFamily_cross c₁ c₂ (hc.trans inf_le_left)) ?_
  rw [Subgroup.commutator_comm]
  refine commutator_le_oddCoreOf_conjFamily_cross c₂ c₁ ?_
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem Std20.t9_hypOmegaModU [IsSimpleGroup G] (d : Std20 3 2 K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) (hzA : z ∈ Subgroup.centralizer ({b} : Set G)) :
    HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K b)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, (d.t9_isClassicalMember c9 h8 hb hzA).conj g⟩
  omega4 := d.t9_omega4_conjFamily b
  omega5 := d.t9_omega5_conjFamily b

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
