module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionCount
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure
public import CFSG.GroupTheory.BurnsideNormalComplement

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
  {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)
include h

theorem not_isConj_modelCenter (hn : 2 ≤ n) {x : modelBase S e} (hxE : x ∉ h.exc) :
    ¬ ∃ z ∈ modelCenter S e, IsConj (x : G) z := by
  rintro ⟨z, hz, hxz⟩
  have hzB : z ∈ modelBase S e := modelCenter_le_modelBase S e (by omega) hz
  obtain ⟨φ, hφ, hφx⟩ := (isConj_iff_exists h hn x ⟨z, hzB⟩).mp hxz
  apply not_mem_exc_of_mem_closure h hφ hxE
  rw [hφx]
  rw [modelCenter_eq_zpowers] at hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Or.inl (Or.inl (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩))
  rw [Subgroup.coe_zpow, h.coe_left_mul_right]
  exact hk

omit [Finite G] h in
theorem modelBase_le_centralizer (x : modelBase S e) :
    modelBase S e ≤ Subgroup.centralizer {(x : G)} := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact modelBase_commute S e _ _ hy x.2

theorem exists_sylow_centralizer (hn : 2 ≤ n) {x : modelBase S e} (hxE : x ∉ h.exc) :
    ∃ P : Sylow 2 (Subgroup.centralizer {(x : G)}),
      (P : Subgroup (Subgroup.centralizer {(x : G)})).map
        (Subgroup.centralizer {(x : G)}).subtype = modelBase S e :=
  modelBase_sylow_centralizer_of_not_isConj S e hn x.2 (not_isConj_modelCenter h hn hxE)

theorem normalizer_inf_centralizer (hn : 2 ≤ n) {x : modelBase S e} (hxE : x ∉ h.exc) :
    Subgroup.normalizer (modelBase S e : Set G) ⊓ Subgroup.centralizer {(x : G)} =
      Subgroup.centralizer (modelBase S e : Set G) ⊓ Subgroup.centralizer {(x : G)} := by
  apply le_antisymm
  · rintro k ⟨hkN, hkx⟩
    refine ⟨?_, hkx⟩
    have hmem : (modelBase S e).normalizerMonoidHom ⟨k, hkN⟩ ∈
        Subgroup.closure {swapAut S e, h.aut} := by
      rw [← range_eq_closure h (by omega)]
      exact ⟨_, rfl⟩
    have hΛ : (modelBase S e).normalizerMonoidHom ⟨k, hkN⟩ = 1 := by
      apply eq_one_of_fixed_of_not_mem_exc h hn hmem hxE
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hkx' : k * (x : G) = x * k := Subgroup.mem_centralizer_singleton_iff.mp hkx
      change k * (x : G) * k⁻¹ = x
      rw [hkx', mul_inv_cancel_right]
    have hker : (⟨k, hkN⟩ : Subgroup.normalizer (modelBase S e : Set G)) ∈
        (modelBase S e).normalizerMonoidHom.ker := hΛ
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  · exact inf_le_inf_right _ (Subgroup.centralizer_le_normalizer _)

theorem centralizer_oddCore_complement (hn : 2 ≤ n) {x : modelBase S e} (hxE : x ∉ h.exc) :
    ((CFSG.oddCore (Subgroup.centralizer {(x : G)})).map
        (Subgroup.centralizer {(x : G)}).subtype : Set G) * (modelBase S e : Set G) =
      Subgroup.centralizer {(x : G)} ∧
    (CFSG.oddCore (Subgroup.centralizer {(x : G)})).map
        (Subgroup.centralizer {(x : G)}).subtype ⊓ modelBase S e = ⊥ ∧
    (CFSG.oddCore (Subgroup.centralizer {(x : G)})).index = (2 ^ n) ^ 2 ∧
    (∃ f : modelBase S e ≃* Subgroup.centralizer {(x : G)} ⧸
        CFSG.oddCore (Subgroup.centralizer {(x : G)}),
      ∀ (y : G) (hyU : y ∈ modelBase S e) (hyD : y ∈ Subgroup.centralizer {(x : G)}),
        f ⟨y, hyU⟩ = ((⟨y, hyD⟩ : Subgroup.centralizer {(x : G)}) :
          Subgroup.centralizer {(x : G)} ⧸ CFSG.oddCore (Subgroup.centralizer {(x : G)}))) ∧
    Odd (Nat.card (CFSG.oddCore (Subgroup.centralizer {(x : G)}))) ∧
    (CFSG.oddCore (Subgroup.centralizer {(x : G)})).IsComplement'
      ((modelBase S e).subgroupOf (Subgroup.centralizer {(x : G)})) ∧
    ∀ K' : Subgroup (Subgroup.centralizer {(x : G)}), K'.Normal → Odd (Nat.card K') →
      K'.IsComplement' ((modelBase S e).subgroupOf (Subgroup.centralizer {(x : G)})) →
        K' = CFSG.oddCore (Subgroup.centralizer {(x : G)}) := by
  have hodd_iff : ∀ k : ℕ, Odd k ↔ ¬ 2 ∣ k := fun k => by
    rw [Nat.odd_iff, Nat.two_dvd_ne_zero]
  have hBD := modelBase_le_centralizer (S := S) (e := e) x
  obtain ⟨P, hP⟩ := exists_sylow_centralizer h hn hxE
  have hPeq : (P : Subgroup (Subgroup.centralizer {(x : G)})) =
      (modelBase S e).subgroupOf (Subgroup.centralizer {(x : G)}) := by
    apply Subgroup.map_injective (Subgroup.centralizer {(x : G)}).subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBD]
  have hNC : Subgroup.normalizer (P : Set (Subgroup.centralizer {(x : G)})) ≤
      Subgroup.centralizer (P : Set (Subgroup.centralizer {(x : G)})) := by
    intro y hy
    change y ∈ Subgroup.normalizer
      ((P : Subgroup (Subgroup.centralizer {(x : G)})) : Set (Subgroup.centralizer {(x : G)}))
      at hy
    change y ∈ Subgroup.centralizer
      ((P : Subgroup (Subgroup.centralizer {(x : G)})) : Set (Subgroup.centralizer {(x : G)}))
    rw [hPeq, ← Subgroup.subgroupOf_normalizer_eq hBD, Subgroup.mem_subgroupOf] at hy
    have hyC : (y : G) ∈ Subgroup.centralizer (modelBase S e : Set G) := by
      have hmem : (y : G) ∈ Subgroup.normalizer (modelBase S e : Set G) ⊓
          Subgroup.centralizer {(x : G)} := ⟨hy, y.2⟩
      rw [normalizer_inf_centralizer h hn hxE] at hmem
      exact hmem.1
    rw [hPeq, Subgroup.mem_centralizer_iff]
    intro p hp
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC _ hp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₀, hK₀N, hK₀odd, hK₀index, hK₀uniq, -, hcomp, -, hinf, ⟨f₀, hf₀⟩, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hNC
  have hPcard : Nat.card P = (2 ^ n) ^ 2 := by
    have hc : Nat.card ((P : Subgroup (Subgroup.centralizer {(x : G)})).map
        (Subgroup.centralizer {(x : G)}).subtype) = Nat.card P :=
      Subgroup.card_map_of_injective (Subgroup.centralizer {(x : G)}).subtype_injective
    rw [hP] at hc
    rw [← hc, card_modelBase]
  have hq : IsPGroup 2 (Subgroup.centralizer {(x : G)} ⧸ K₀) := by
    apply IsPGroup.of_card (n := n * 2)
    rw [← Subgroup.index_eq_card, hK₀index, hPcard, ← pow_mul]
  have hKeq : K₀ = CFSG.oddCore (Subgroup.centralizer {(x : G)}) := by
    apply le_antisymm
    · exact le_sSup ⟨hK₀N, (hodd_iff _).mpr hK₀odd⟩
    · exact CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient K₀ _ hq
        ((hodd_iff _).mp (weakClosure_oddCore_card _))
  subst hKeq
  set K := CFSG.oddCore (Subgroup.centralizer {(x : G)}) with hK
  have hPmem : ∀ q : Subgroup.centralizer {(x : G)},
      q ∈ (P : Subgroup (Subgroup.centralizer {(x : G)})) ↔ (q : G) ∈ modelBase S e := by
    intro q
    rw [hPeq, Subgroup.mem_subgroupOf]
  have hmemP : ∀ y : modelBase S e, Subgroup.inclusion hBD y ∈
      (P : Subgroup (Subgroup.centralizer {(x : G)})) := fun y => (hPmem _).mpr y.2
  refine ⟨?_, ?_, ?_, ?_, (hodd_iff _).mpr hK₀odd, hPeq ▸ hcomp, ?_⟩
  ·
    ext y
    constructor
    · rintro ⟨_, ⟨k, -, rfl⟩, b, hb, rfl⟩
      exact Subgroup.mul_mem _ k.2 (hBD hb)
    · intro hy
      obtain ⟨⟨k, p⟩, hkp⟩ := (hcomp.existsUnique ⟨y, hy⟩).exists
      exact ⟨((k : Subgroup.centralizer {(x : G)}) : G), ⟨k, k.2, rfl⟩,
        ((p : Subgroup.centralizer {(x : G)}) : G), (hPmem _).mp p.2, congrArg Subtype.val hkp⟩
  ·
    have h' : K.map (Subgroup.centralizer {(x : G)}).subtype ⊓
        (P : Subgroup (Subgroup.centralizer {(x : G)})).map
          (Subgroup.centralizer {(x : G)}).subtype = ⊥ := by
      rw [← Subgroup.map_inf_eq _ _ _ (Subgroup.centralizer {(x : G)}).subtype_injective, hinf,
        Subgroup.map_bot]
    rwa [hP] at h'
  ·
    rw [hK₀index, hPcard]
  ·
    let f₁ : modelBase S e →* Subgroup.centralizer {(x : G)} ⧸ K :=
      (QuotientGroup.mk' K).comp (Subgroup.inclusion hBD)
    have hf₁ : ∀ y, f₁ y = f₀ ⟨Subgroup.inclusion hBD y, hmemP y⟩ := by
      intro y
      rw [hf₀]
      rfl
    have hbij : Function.Bijective f₁ := by
      constructor
      · intro y y' hyy'
        rw [hf₁, hf₁] at hyy'
        have h' := congrArg (fun p : (P : Subgroup (Subgroup.centralizer {(x : G)})) =>
          ((p : Subgroup.centralizer {(x : G)}) : G)) (f₀.injective hyy')
        exact Subtype.ext h'
      · intro q
        obtain ⟨⟨p, hp⟩, hpq⟩ := f₀.surjective q
        have hpB : (p : G) ∈ modelBase S e := (hPmem _).mp hp
        refine ⟨⟨p, hpB⟩, ?_⟩
        rw [hf₁, ← hpq]
        rfl
    exact ⟨MulEquiv.ofBijective f₁ hbij, fun y hyU hyD => rfl⟩
  ·
    intro K' hK'N hK'odd hK'comp
    rw [← hPeq] at hK'comp
    exact hK₀uniq K' hK'N ((hodd_iff _).mp hK'odd)
      (by rw [hK'comp.symm.index_eq_card])

end CFSG.Wreathed.AdaptedBaseFusion
