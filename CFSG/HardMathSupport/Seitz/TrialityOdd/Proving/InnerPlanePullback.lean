module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

variable {G : Type*} [Group G]

private theorem innerPullback_fixed_iff_comm (x k : G) :
    MulAut.conj x k = k ↔ k * x = x * k := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem innerPullback_conj_eq_one_iff
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) (x : G) :
    MulAut.conj x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply hinj
    rw [h, map_one]
  · rintro rfl
    exact map_one _

theorem planeGen_of_closure_centralizers
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) (E : Subgroup (MulAut G))
    (hin : E ≤ (MulAut.conj : G →* MulAut G).range)
    (h : Subgroup.closure {k : G | ∃ x ∈ E.comap (MulAut.conj : G →* MulAut G),
      x ≠ 1 ∧ k * x = x * k} = ⊤) :
    CFSG.LieType.SeitzGeneration.PlaneGen E := by
  unfold CFSG.LieType.SeitzGeneration.PlaneGen CFSG.LieType.SeitzGeneration.planeClosure
  have hset : {k : G | ∃ e ∈ E, e ≠ 1 ∧ e k = k} =
      {k : G | ∃ x ∈ E.comap (MulAut.conj : G →* MulAut G), x ≠ 1 ∧ k * x = x * k} := by
    ext k
    constructor
    · rintro ⟨e, he, he1, hek⟩
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hin he)
      subst hx
      refine ⟨x, Subgroup.mem_comap.mpr he, fun hx1 => he1 ?_, ?_⟩
      · rw [hx1, map_one]
      · exact (innerPullback_fixed_iff_comm x k).mp hek
    · rintro ⟨x, hx, hx1, hkx⟩
      exact ⟨MulAut.conj x, Subgroup.mem_comap.mp hx,
        fun h1 => hx1 ((innerPullback_conj_eq_one_iff hinj x).mp h1),
        (innerPullback_fixed_iff_comm x k).mpr hkx⟩
  rw [hset]
  exact h

theorem isElementaryAbelian_comap_conj {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) {E : Subgroup (MulAut G)}
    (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.IsElementaryAbelian p (E.comap (MulAut.conj : G →* MulAut G)) := by
  obtain ⟨hcomm, hpow⟩ := hE
  have hcomm' : ∀ a b : ↥(E.comap (MulAut.conj : G →* MulAut G)), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply hinj
    have hc : MulAut.conj a.1 * MulAut.conj b.1 = MulAut.conj b.1 * MulAut.conj a.1 :=
      congrArg Subtype.val
        (hcomm.is_comm.comm ⟨MulAut.conj a.1, Subgroup.mem_comap.mp a.2⟩
          ⟨MulAut.conj b.1, Subgroup.mem_comap.mp b.2⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hc
  have hpow' : ∀ g : ↥(E.comap (MulAut.conj : G →* MulAut G)), g ^ p = 1 := by
    intro g
    apply Subtype.ext
    have hg : MulAut.conj (g.1 ^ p) = 1 := by
      rw [map_pow]
      exact hpow _ (Subgroup.mem_comap.mp g.2)
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (innerPullback_conj_eq_one_iff hinj _).mp hg
  refine { toIsMulCommutative := ⟨⟨hcomm'⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow' }

theorem card_comap_conj
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) {E : Subgroup (MulAut G)}
    (hin : E ≤ (MulAut.conj : G →* MulAut G).range) :
    Nat.card (E.comap (MulAut.conj : G →* MulAut G)) = Nat.card E := by
  rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hin]

theorem not_le_normalizer_of_no_invariant {r : ℕ} {E : Subgroup (MulAut G)}
    (hin : E ≤ (MulAut.conj : G →* MulAut G).range)
    (hno : ¬ ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup r S ∧ ∀ β ∈ E, S.map β.toMonoidHom = S) :
    ∀ R : Subgroup G, IsPGroup r R → R ≠ ⊥ →
      ¬ E.comap (MulAut.conj : G →* MulAut G) ≤ Subgroup.normalizer (R : Set G) := by
  intro R hR hR0 hle
  apply hno
  refine ⟨R, hR0, hR, fun β hβ => ?_⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hin hβ)
  subst hx
  have hxN : ∀ h : G, h ∈ R ↔ x * h * x⁻¹ ∈ R := by
    intro h
    have hnorm := hle (Subgroup.mem_comap.mpr hβ)
    exact Subgroup.mem_normalizer_iff.mp hnorm h
  ext k
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyk⟩
    rw [← hyk]
    exact (hxN y).mp hy
  · intro hk
    refine ⟨x⁻¹ * k * x, (hxN _).mpr ?_, ?_⟩
    · have hcancel : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
      rw [hcancel]
      exact hk
    · show x * (x⁻¹ * k * x) * x⁻¹ = k
      group

theorem closure_centralizers_map_mulAut (β : MulAut G) (F : Subgroup G) :
    Subgroup.closure {k : G | ∃ x ∈ F.map β.toMonoidHom, x ≠ 1 ∧ k * x = x * k} =
      (Subgroup.closure {k : G | ∃ x ∈ F, x ≠ 1 ∧ k * x = x * k}).map β.toMonoidHom := by
  rw [MonoidHom.map_closure]
  congr 1
  ext k
  constructor
  · rintro ⟨x, hx, hx1, hkx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨β.symm k, ⟨y, hy, fun h => hx1 (by rw [h, map_one]), ?_⟩, by simp⟩
    apply β.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hkx
  · rintro ⟨z, ⟨x, hx, hx1, hzx⟩, rfl⟩
    refine ⟨β x, Subgroup.mem_map_of_mem _ hx, fun h => hx1 (β.map_eq_one_iff.mp h), ?_⟩
    show β z * β x = β x * β z
    rw [← map_mul, ← map_mul, hzx]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
