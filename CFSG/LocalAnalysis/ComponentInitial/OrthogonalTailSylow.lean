module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailStabilizerIndices
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentInvariant
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLeviPPrime

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Flags

variable (K A r) in
@[expose] def stdFlag : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A) :=
  fun i => tailFlag K A r (i + 1)

theorem smul_flag_apply (g : orthElementaryGroup (quadTail r qA))
    (W : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A)) (i : Fin r) :
    (g • W) i = (W i).map ((g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  rfl

theorem mem_stabilizer_flag_iff {g : orthElementaryGroup (quadTail r qA)}
    {W : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) W ↔
      ∀ i, (W i).map ((g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
        ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = W i := by
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

theorem tailBorel_subgroupOf_eq :
    (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) =
      MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) (stdFlag K A r) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_tailBorel, mem_stabilizer_flag_iff]
  constructor
  · rintro ⟨-, h⟩ i
    exact h (i + 1) (by omega) (by have := i.isLt; omega)
  · intro h
    refine ⟨g.2, fun k hk1 hkr => ?_⟩
    have := h ⟨k - 1, by omega⟩
    simp only [stdFlag] at this
    rwa [show k - 1 + 1 = k by omega] at this

theorem elemScalars_le_stabilizer_flag (W : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A)) :
    elemScalars (quadTail r qA) ≤ MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) W :=
  fun _ hg => mem_stabilizer_flag_iff.2 fun i => mem_stabilizer_iff_map.1
    (elemScalars_le_stabilizer (W i) hg)

variable [FiniteDimensional K A] (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0)
include hani hA

theorem orbit_stdFlag :
    MulAction.orbit (orthElementaryGroup (quadTail r qA)) (stdFlag K A r) =
      singularFlags (quadTail r qA) r := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hstd := tailFlag_mem_singularFlags (K := K) (A := A) (r := r) (qA := qA)
  ext W
  constructor
  · rintro ⟨g, rfl⟩
    dsimp only
    refine ⟨fun i => ?_, fun i j hij => ?_, fun i x hx => ?_⟩
    · rw [smul_flag_apply, LinearEquiv.finrank_map_eq]
      exact hstd.1 i
    · rw [smul_flag_apply, smul_flag_apply]
      exact Submodule.map_mono (hstd.2.1 hij)
    · rw [smul_flag_apply] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [LinearEquiv.coe_coe, map_of_mem (orthElementaryGroup_le _ g.2)]
      exact hstd.2.2 i y hy
  · intro hW
    obtain ⟨g, hg, hgW⟩ := exists_mem_map_eq_tailFlag hani ha₀ le_rfl hW
    refine ⟨⟨g, hg⟩⁻¹, funext fun i => ?_⟩
    dsimp only
    rw [smul_flag_apply, Subgroup.coe_inv]
    change (tailFlag K A r (i + 1)).map _ = W i
    rw [← hgW i, map_map_inv]

theorem index_tailBorel_subgroupOf :
    ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).index =
      Nat.card (singularFlags (quadTail r qA) r) := by
  rw [tailBorel_subgroupOf_eq, MulAction.index_stabilizer, orbit_stdFlag hani hA]
  exact (Nat.card_coe_set_eq _).symm

end Flags

section Sylow

theorem dvd_natCard_of_charP {K : Type*} [Field K] [Finite K] {p : ℕ} [CharP K p] :
    p ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff K p _).1 (FiniteField.cast_card_eq_zero K)

variable [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] [FiniteDimensional K A]

theorem not_dvd_card_singularFlags (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : 1 ≤ finrank K A) : ¬p ∣ Nat.card (singularFlags (quadTail r qA) r) := by
  set q := Nat.card K with hqdef
  have hq1 : (1 : ℚ) < q := by exact_mod_cast Finite.one_lt_card
  have hN : Nat.card (singularFlags (quadTail r qA) r) = ∏ j ∈ Finset.range r,
      ((∑ i ∈ Finset.range (r - j), q ^ i) * (q ^ (r + finrank K A - j - 1) + 1)) := by
    have h := card_singularFlags_tail hani hreg (le_refl r) (qA := qA)
    rw [← Nat.cast_inj (R := ℚ), h]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [geom_sum_eq hq1.ne' (r - j)]
    ring
  rw [hN, ← ZMod.natCast_eq_zero_iff]
  push_cast
  have hq0 : ((q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 dvd_natCard_of_charP
  rw [hq0, Finset.prod_eq_one]
  · exact one_ne_zero
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [zero_pow (by omega), zero_add, mul_one]
    obtain ⟨s, hs⟩ : ∃ s, r - j = s + 1 := ⟨r - j - 1, by omega⟩
    rw [hs, Finset.sum_range_succ', pow_zero]
    simp

omit hp in
theorem isPGroup_tailUnipotent (hani : qA.Anisotropic) :
    IsPGroup p ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  refine IsPGroup.of_card (n := n * (r * (r - 1) + r * finrank K A)) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tailUnipotent_le).toEquiv,
    card_tailUnipotent hani, Nat.card_eq_fintype_card, hn, ← pow_mul]

theorem not_dvd_index_tailUnipotent (hr : 3 ≤ r) (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (hm : finrank K A = 1 ∨ finrank K A = 2) :
    ¬p ∣ ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).index := by
  have hA : ∃ a : A, a ≠ 0 := by
    have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
    have : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
    exact exists_ne 0
  have hle : (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) ≤
      (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) :=
    fun x hx => tailUnipotent_le_tailBorel hani hx
  rw [← Subgroup.relIndex_mul_index hle, Subgroup.relIndex_subgroupOf tailBorel_le,
    index_tailBorel_subgroupOf hani hA]
  have hT : (tailUnipotent r qA).relIndex (tailBorel r qA) = Nat.card (tailTorus r qA) := by
    have := tailUnipotent_normal hani (r := r) (qA := qA)
    obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := r) (qA := qA)
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_congr e.toEquiv
  rw [hT]
  intro h
  rcases hp.out.dvd_mul.1 h with h1 | h2
  · exact orthogonal_geometry_tail_small_anisotropic_Levi_p_prime hr hani hreg hm h1
  · exact not_dvd_card_singularFlags hani hreg (by rcases hm with h | h <;> omega) h2

omit [Finite K] in
theorem normalizer_tailUnipotent (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0) :
    Subgroup.normalizer (((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) :
      Subgroup (orthElementaryGroup (quadTail r qA))) : Set (orthElementaryGroup (quadTail r qA))) =
      (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) := by
  apply le_antisymm
  · intro g hg
    rw [tailBorel_subgroupOf_eq]
    have hW : g • stdFlag K A r ∈ singularFlags (quadTail r qA) r := by
      rw [← orbit_stdFlag hani hA]
      exact ⟨g, rfl⟩
    refine mem_stabilizer_flag_iff.2 fun i => ?_
    have hinv : ∀ u ∈ tailUnipotent r qA, ((g • stdFlag K A r) i).map
        (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≤
          (g • stdFlag K A r) i := by
      intro u hu
      set û : orthElementaryGroup (quadTail r qA) := ⟨u, tailUnipotent_le hu⟩
      have hu' : g⁻¹ * û * g ∈
          (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) û).1 (Subgroup.mem_subgroupOf.2 hu)
        rwa [inv_inv] at this
      have hfix := map_tailFlag_of_mem_tailUnipotent hani (k := i + 1)
        (by have := i.isLt; omega) (Subgroup.mem_subgroupOf.1 hu')
      have he : u * (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) =
          (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) *
            ((g⁻¹ * û * g : orthElementaryGroup (quadTail r qA)) :
              ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, û]
        group
      rw [smul_flag_apply, ← map_mul_linearEquiv, he, map_mul_linearEquiv]
      change ((tailFlag K A r (i + 1)).map _).map _ ≤ _
      rw [hfix]
      exact le_rfl
    obtain ⟨k, -, hkr, hk⟩ := eq_tailFlag_of_invariant hani hA (W := (g • stdFlag K A r) i)
      (fun h => by
        have := hW.1 i
        rw [h, finrank_bot] at this
        omega) (hW.2.2 i) hinv
    have hd := hW.1 i
    rw [hk, finrank_tailFlag hkr] at hd
    rw [← smul_flag_apply, hk, hd]
    rfl
  · intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hN := tailUnipotent_normal hani (r := r) (qA := qA)
    have hbB : (b : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) ∈ tailBorel r qA := hb
    constructor
    · intro hh
      have := hN.conj_mem ⟨h, tailUnipotent_le_tailBorel hani hh⟩
        (Subgroup.mem_subgroupOf.2 hh) ⟨b, hbB⟩
      exact Subgroup.mem_subgroupOf.1 this
    · intro hh
      have hbhb : (b * h * b⁻¹ : orthElementaryGroup (quadTail r qA)).1 ∈ tailUnipotent r qA := hh
      have := hN.conj_mem ⟨_, tailUnipotent_le_tailBorel hani hbhb⟩
        (Subgroup.mem_subgroupOf.2 hbhb) ⟨_, inv_mem hbB⟩
      have e : ((⟨_, inv_mem hbB⟩ : tailBorel r qA) *
          ⟨_, tailUnipotent_le_tailBorel hani hbhb⟩ * (⟨_, inv_mem hbB⟩ : tailBorel r qA)⁻¹ :
            tailBorel r qA).1 = (h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      have hmem := Subgroup.mem_subgroupOf.1 this
      rw [e] at hmem
      exact hmem

theorem mem_tailUnipotent_of_pow_eq_one (hr : 3 ≤ r) (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (hm : finrank K A = 1 ∨ finrank K A = 2)
    {y : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hy : y ∈ tailBorel r qA)
    {k : ℕ} (hk : y ^ (p ^ k) = 1) : y ∈ tailUnipotent r qA := by
  have := tailUnipotent_normal hani (r := r) (qA := qA)
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := r) (qA := qA)
  set yb : tailBorel r qA ⧸ (tailUnipotent r qA).subgroupOf (tailBorel r qA) :=
    ((⟨y, hy⟩ : tailBorel r qA) : tailBorel r qA ⧸ (tailUnipotent r qA).subgroupOf (tailBorel r qA))
  have h1 : yb ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, show (⟨y, hy⟩ : tailBorel r qA) ^ (p ^ k) = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hk), QuotientGroup.mk_one]
  have hord : orderOf yb ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcard : orderOf yb ∣ Nat.card (tailTorus r qA) := by
    rw [← Nat.card_congr e.toEquiv]
    exact orderOf_dvd_natCard yb
  have hcop : Nat.Coprime (p ^ k) (Nat.card (tailTorus r qA)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (orthogonal_geometry_tail_small_anisotropic_Levi_p_prime hr hani hreg hm))
  have h1' : orderOf yb = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hord hcard)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1'
  exact h1'

end Sylow

section Quotient

variable (r qA) in
@[expose] noncomputable def stabFlagP (W : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A)) :
    Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)) :=
  (MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) W).map
    (QuotientGroup.mk' (elemScalars (quadTail r qA)))

theorem map_map_conj_mk {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (H : Subgroup G)
    (g : G) : (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) =
      (H.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem stabFlagP_smul (g : orthElementaryGroup (quadTail r qA))
    (W : Fin r → Submodule K ((Fin r ⊕ Fin r → K) × A)) :
    stabFlagP r qA (g • W) = (stabFlagP r qA W).map
      (MulAut.conj (QuotientGroup.mk' (elemScalars (quadTail r qA)) g)).toMonoidHom := by
  rw [stabFlagP, MulAction.stabilizer_smul_eq_stabilizer_map_conj, map_map_conj_mk, stabFlagP]

variable [FiniteDimensional K A] (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0)
include hani hA

theorem exists_conj_iff_stabFlagP
    (H : Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) :
    (∃ x, H = (((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
      (QuotientGroup.mk' (elemScalars (quadTail r qA)))).map (MulAut.conj x).toMonoidHom) ↔
    ∃ W ∈ singularFlags (quadTail r qA) r, H = stabFlagP r qA W := by
  rw [tailBorel_subgroupOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elemScalars (quadTail r qA)) x
    refine ⟨g • stdFlag K A r, ?_, ?_⟩
    · rw [← orbit_stdFlag hani hA]
      exact ⟨g, rfl⟩
    · rw [stabFlagP_smul]
      rfl
  · rintro ⟨W, hW, rfl⟩
    rw [← orbit_stdFlag hani hA] at hW
    obtain ⟨g, rfl⟩ := hW
    exact ⟨QuotientGroup.mk' _ g, by rw [stabFlagP_smul]; rfl⟩

end Quotient

theorem exists_map_normalizer_conj {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (S : Sylow p P) (σ : P ≃* P) (x : P) : ∃ z : P,
      ((Subgroup.normalizer ((S : Subgroup P) : Set P)).map (MulAut.conj x).toMonoidHom).map
        σ.toMonoidHom =
      (Subgroup.normalizer ((S : Subgroup P) : Set P)).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq P S (S.mapSurjective (f := σ.toMonoidHom) σ.surjective)
  have hσS : (S : Subgroup P).map σ.toMonoidHom =
      (S : Subgroup P).map (MulAut.conj y).toMonoidHom := by
    have h1 : MulAut.conj y • (S : Subgroup P) = (S : Subgroup P).map σ.toMonoidHom :=
      congrArg (fun T : Sylow p P => (T : Subgroup P)) hy
    rw [← h1]
    rfl
  have hσN : (Subgroup.normalizer ((S : Subgroup P) : Set P)).map σ.toMonoidHom =
      (Subgroup.normalizer ((S : Subgroup P) : Set P)).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hσS,
      ← Subgroup.map_equiv_normalizer_eq _ (MulAut.conj y)]
  refine ⟨σ x * y, ?_⟩
  rw [Subgroup.map_map]
  have e1 : σ.toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (σ x)).toMonoidHom.comp σ.toMonoidHom := by
    ext g
    simp
  rw [e1, ← Subgroup.map_map, hσN, Subgroup.map_map, map_mul]
  rfl

section NormalizerP

variable [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] [FiniteDimensional K A]
include hp

theorem normalizer_map_tailUnipotent (hr : 3 ≤ r) (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (hm : finrank K A = 1 ∨ finrank K A = 2) :
    Subgroup.normalizer
        ((((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
          (QuotientGroup.mk' (elemScalars (quadTail r qA))) :
            Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) :
          Set (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) =
      ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  have : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  have hA : ∃ a : A, a ≠ 0 := exists_ne 0
  have hN := normalizer_tailUnipotent hani hA (r := r)
  have hpg := isPGroup_tailUnipotent hani (r := r) (p := p)
  have hZB : elemScalars (quadTail r qA) ≤
      (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) := by
    rw [tailBorel_subgroupOf_eq]
    exact elemScalars_le_stabilizer_flag _
  have hUB : (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) ≤
      (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) :=
    fun x hx => tailUnipotent_le_tailBorel hani hx
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elemScalars (quadTail r qA)) x
    have key : ∀ g : orthElementaryGroup (quadTail r qA),
        QuotientGroup.mk' (elemScalars (quadTail r qA)) g ∈ Subgroup.normalizer
          ((((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
            (QuotientGroup.mk' (elemScalars (quadTail r qA))) : Subgroup _) :
              Set (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) →
        ∀ h ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)),
          g * h * g⁻¹ ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) := by
      intro g hg h hh
      have h1 : QuotientGroup.mk' (elemScalars (quadTail r qA)) (g * h * g⁻¹) ∈
          ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
            (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 hg _).1 ⟨h, hh, rfl⟩
      have h2 : g * h * g⁻¹ ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))
          ⊔ elemScalars (quadTail r qA) := by
        have := Subgroup.comap_map_eq (QuotientGroup.mk' (elemScalars (quadTail r qA)))
          ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)))
        rw [QuotientGroup.ker_mk'] at this
        rw [← this]
        exact h1
      have h3 : ((g * h * g⁻¹ : orthElementaryGroup (quadTail r qA)) :
          ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ∈ tailBorel r qA :=
        (sup_le hUB hZB) h2
      obtain ⟨k, hk⟩ := hpg ⟨h, hh⟩
      have hk' : ((g * h * g⁻¹ : orthElementaryGroup (quadTail r qA)) :
          ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ^ (p ^ k) = 1 := by
        have hk1 : h ^ (p ^ k) = 1 := by
          have := congrArg Subtype.val hk
          rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [← Subgroup.coe_pow, conj_pow, hk1, mul_one, mul_inv_cancel, Subgroup.coe_one]
      exact Subgroup.mem_subgroupOf.2 (mem_tailUnipotent_of_pow_eq_one hr hani hreg hm h3 hk')
    have hg1 := key g hx
    have hg2 := key g⁻¹ (by rw [map_inv]; exact inv_mem hx)
    have hgN : g ∈ Subgroup.normalizer (((tailUnipotent r qA).subgroupOf
        (orthElementaryGroup (quadTail r qA)) : Subgroup _) :
          Set (orthElementaryGroup (quadTail r qA))) :=
      Subgroup.mem_normalizer_iff.2 fun h => ⟨hg1 h, fun hh => by
        have := hg2 _ hh
        rwa [inv_inv, show g⁻¹ * (g * h * g⁻¹) * g = h by group] at this⟩
    rw [hN] at hgN
    exact ⟨g, hgN, rfl⟩
  · rw [← hN]
    exact Subgroup.le_normalizer_map _

end NormalizerP

theorem orthogonal_geometry_tail_Sylow_flag_normalizer {K : Type*} [Field K] [Finite K] {p : ℕ}
    [hp : Fact p.Prime] [CharP K p] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
    (hr : 3 ≤ r) {qA : QuadraticForm K A} (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate) (hm : finrank K A = 1 ∨ finrank K A = 2) :
    (∃ S : Sylow p (orthElementaryGroup (quadTail r qA)),
      (S : Subgroup (orthElementaryGroup (quadTail r qA))) =
        (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))) ∧
    Subgroup.normalizer (((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) :
        Subgroup (orthElementaryGroup (quadTail r qA))) :
          Set (orthElementaryGroup (quadTail r qA))) =
      (tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) ∧
    (∃ S : Sylow p (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)),
      (S : Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) =
        ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
          (QuotientGroup.mk' (elemScalars (quadTail r qA)))) ∧
    Subgroup.normalizer
        ((((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
          (QuotientGroup.mk' (elemScalars (quadTail r qA))) :
            Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) :
          Set (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) =
      ((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) ∧
    (∀ H : Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)),
      (∃ x, H = (((tailBorel r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA)))).map (MulAut.conj x).toMonoidHom) ↔
      ∃ W ∈ singularFlags (quadTail r qA) r, H = stabFlagP r qA W) ∧
    ∀ σ : (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)) ≃*
        (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA)),
      ∀ W ∈ singularFlags (quadTail r qA) r, ∃ W' ∈ singularFlags (quadTail r qA) r,
        (stabFlagP r qA W).map σ.toMonoidHom = stabFlagP r qA W' := by
  have hpos : 0 < finrank K A := by rcases hm with h | h <;> omega
  have : FiniteDimensional K A := Module.finite_of_finrank_pos hpos
  have : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  have hA : ∃ a : A, a ≠ 0 := exists_ne 0
  have : Finite A := Module.finite_of_finite K
  have : Finite (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _ =>
      (g : ((Fin r ⊕ Fin r → K) × A) → (Fin r ⊕ Fin r → K) × A)) DFunLike.coe_injective
  have hpg := isPGroup_tailUnipotent hani (r := r) (p := p)
  have hidx := not_dvd_index_tailUnipotent hr hani hreg hm (p := p)
  have hScoe : (hpg.toSylow hidx : Subgroup (orthElementaryGroup (quadTail r qA))) =
      (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)) :=
    IsPGroup.toSylow_coe _ _
  have hS'coe : ((hpg.toSylow hidx).mapSurjective (QuotientGroup.mk'_surjective
      (elemScalars (quadTail r qA))) :
        Subgroup (orthElementaryGroup (quadTail r qA) ⧸ elemScalars (quadTail r qA))) =
      ((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))).map
        (QuotientGroup.mk' (elemScalars (quadTail r qA))) := by
    rw [Sylow.coe_mapSurjective, hScoe]
  have hNP := normalizer_map_tailUnipotent hr hani hreg hm (p := p)
  refine ⟨⟨_, hScoe⟩, normalizer_tailUnipotent hani hA, ⟨_, hS'coe⟩, hNP,
    fun H => exists_conj_iff_stabFlagP hani hA H, fun σ W hW => ?_⟩
  obtain ⟨x, hx⟩ := (exists_conj_iff_stabFlagP hani hA (stabFlagP r qA W)).2 ⟨W, hW, rfl⟩
  obtain ⟨z, hz⟩ := exists_map_normalizer_conj ((hpg.toSylow hidx).mapSurjective
    (QuotientGroup.mk'_surjective (elemScalars (quadTail r qA)))) σ x
  rw [hS'coe, hNP] at hz
  obtain ⟨W', hW', hW'eq⟩ := (exists_conj_iff_stabFlagP hani hA _).1 ⟨z, rfl⟩
  exact ⟨W', hW', by rw [hx, hz, hW'eq]⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
