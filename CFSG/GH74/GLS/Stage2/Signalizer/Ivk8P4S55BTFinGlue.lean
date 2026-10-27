module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74.GLS FinGen
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def NoPerfLocal (G : Type) [Group G] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X I : Subgroup G), IsPGroup p ↥X → X ≠ ⊥ →
    I ≠ ⊥ → ⁅I, I⁆ = I → I ≤ normalizer (X : Set G) → False

@[expose] def NoFourPerf (G : Type) [Group G] : Prop :=
  ∀ (U Q I : Subgroup G), IVK.IsFourSubgroup U → IVK.IsFourSubgroup Q → Q ≤ I →
    ⁅I, I⁆ = I → I ≤ centralizer (U : Set G) → False

namespace FinGlue

variable {G H : Type} [Group G] [Group H]

theorem finCellA_of {Y : Type} [Group Y] (h : NoPerfLocal (MulAut Y)) : FinCellA Y := h

theorem finCellB_of {Y : Type} [Group Y] (h : NoFourPerf (MulAut Y)) : FinCellB Y := by
  intro p _ _ X U I Q _ hU hQ hQI _ hI hIU _ _ _ _ _
  exact (h U Q I hU hQ hQI hI hIU).elim

theorem isFourSubgroup_map (e : G ≃* H) {U : Subgroup G} (hU : IVK.IsFourSubgroup U) :
    IVK.IsFourSubgroup (U.map e.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.1
  exact ⟨IsElementaryAbelian.map e.toMonoidHom,
    by rw [Subgroup.card_map_of_injective e.injective, hU.2]⟩

theorem map_perfect (e : G ≃* H) {I : Subgroup G} (hI : ⁅I, I⁆ = I) :
    ⁅I.map e.toMonoidHom, I.map e.toMonoidHom⁆ = I.map e.toMonoidHom := by
  rw [← Subgroup.map_commutator, hI]

theorem map_le_normalizer (e : G ≃* H) {I X : Subgroup G} (h : I ≤ normalizer (X : Set G)) :
    I.map e.toMonoidHom ≤ normalizer ((X.map e.toMonoidHom : Subgroup H) : Set H) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx := (mem_normalizer_iff.mp (h hg)) x
  constructor
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨_, hx.mp hx', by simp⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = g * x * g⁻¹ := e.injective (by simpa using hxe)
    subst this
    have := hx.mpr hx'
    exact ⟨x, this, rfl⟩

theorem map_le_centralizer (e : G ≃* H) {I U : Subgroup G} (h : I ≤ centralizer (U : Set G)) :
    I.map e.toMonoidHom ≤ centralizer ((U.map e.toMonoidHom : Subgroup H) : Set H) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have := mem_centralizer_iff.mp (h hg) u hu
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, this]

theorem NoPerfLocal.of_equiv (e : G ≃* H) (h : NoPerfLocal H) : NoPerfLocal G := by
  intro p hp hp2 X I hX hX1 hI1 hI hIX
  refine h p hp hp2 (X.map e.toMonoidHom) (I.map e.toMonoidHom)
    (hX.map e.toMonoidHom) ?_ ?_ (map_perfect e hI) (map_le_normalizer e hIX)
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]

theorem NoFourPerf.of_equiv (e : G ≃* H) (h : NoFourPerf H) : NoFourPerf G := by
  intro U Q I hU hQ hQI hI hIU
  exact h (U.map e.toMonoidHom) (Q.map e.toMonoidHom) (I.map e.toMonoidHom)
    (isFourSubgroup_map e hU) (isFourSubgroup_map e hQ) (Subgroup.map_mono hQI)
    (map_perfect e hI) (map_le_centralizer e hIU)

theorem noPerfLocal_of [Finite G]
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, CFSG.IsElementaryAbelian p ↥E →
      Nat.card ↥E ≤ p ∨ (p = 3 ∧ Nat.card ↥E ≤ 9))
    (hcent : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x : G, orderOf x = p →
      Group.IsSolvable ↥(centralizer ({x} : Set G))) : NoPerfLocal G := by
  intro p hp hp2 X I hX hX1 hI1 hI hIX
  obtain ⟨x, -, hxp, hIx⟩ := exists_centralized hp hX hX1 hI hIX (hrank p hp hp2)
  exact hI1 (eq_bot_of_perfect_of_le hIx (hcent p hp hp2 x hxp) hI)

theorem rank_of_dvd [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ k : ℕ, p ^ k ∣ Nat.card G → k ≤ 1 ∨ (p = 3 ∧ k ≤ 2)) (E : Subgroup G)
    (hE : CFSG.IsElementaryAbelian p ↥E) : Nat.card ↥E ≤ p ∨ (p = 3 ∧ Nat.card ↥E ≤ 9) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := IsElementaryAbelian.isPGroup p ↥E
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hEp
  have hdvd : p ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card E
  rcases h k hdvd with hk1 | ⟨rfl, hk2⟩
  · left
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  · right
    refine ⟨rfl, ?_⟩
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num

theorem noFourPerf_of [Finite G]
    (h : ∀ U : Subgroup G, IVK.IsFourSubgroup U → Group.IsSolvable ↥(centralizer (U : Set G))) :
    NoFourPerf G := by
  intro U Q I hU hQ hQI hI hIU
  have hbot := eq_bot_of_perfect_of_le hIU (h U hU) hI
  have hQ1 : Q = ⊥ := le_bot_iff.mp (by rw [← hbot]; exact hQI)
  have h4 := hQ.2
  rw [hQ1, card_bot] at h4
  omega

theorem conj_injective_of_center' {Y : Type} [Group Y] (h : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← h, Subgroup.mem_center_iff]
  intro y
  have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) y
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * g = (g * y * g⁻¹) * g := by rw [h1]
    _ = g * y := by group

theorem noFourPerf_mulAut_of_cyclic {Y : Type} [Group Y] [Finite Y] (hZ : center Y = ⊥)
    (hcyc : IsCyclic (Outer Y))
    (hcent : ∀ y : Y, orderOf y = 2 → Group.IsSolvable ↥(centralizer ({y} : Set Y))) :
    NoFourPerf (MulAut Y) := by
  intro U Q I hU hQ hQI hI hIU
  have hInj := conj_injective_of_center' hZ
  have : (inner Y).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have hcomm : ∀ a b : Outer Y, a * b = b * a := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Outer Y)
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact ((Commute.refl g).zpow_zpow i j).eq
  have hker : ∀ φ : MulAut Y, π φ = 1 ↔ φ ∈ inner Y := fun φ => QuotientGroup.eq_one_iff φ
  have hIinn : I ≤ inner Y := by
    rw [← hI, Subgroup.commutator_le]
    intro a _ b _
    rw [← hker, map_commutatorElement, commutatorElement_def, hcomm (π a) (π b)]
    group
  obtain ⟨u, huU, hu1, huinn⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ∈ inner Y := by
    have := hU.1
    let πU : ↥U →* Outer Y := π.comp U.subtype
    have hr2 : Nat.card ↥πU.range ≤ 2 := by
      have hexp : Monoid.exponent ↥πU.range ∣ 2 := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
        rintro ⟨_, ⟨v, rfl⟩⟩
        apply Subtype.ext
        show πU v ^ 2 = 1
        have hv2 : v ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow]
          exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) _ v.2)
        rw [← map_pow, hv2, map_one]
      have : IsCyclic ↥πU.range := Subgroup.isCyclic _
      rw [IsCyclic.exponent_eq_card] at hexp
      exact Nat.le_of_dvd (by norm_num) hexp
    have hmul : Nat.card ↥πU.ker * Nat.card ↥πU.range = 4 := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index, hU.2]
    have hk2 : 2 ≤ Nat.card ↥πU.ker := by
      by_contra hk
      push Not at hk
      have := Nat.mul_le_mul (Nat.lt_succ_iff.mp hk) hr2
      omega
    obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).mp hk2 |>
      fun h => (Subgroup.ne_bot_iff_exists_ne_one).mp h
    refine ⟨v, (v : ↥U).2, fun h => hv1 (Subtype.ext (Subtype.ext h)), ?_⟩
    exact (hker _).mp hv
  obtain ⟨y, rfl⟩ := huinn
  have hy2 : orderOf y = 2 := by
    have := hU.1
    have hu2 : MulAut.conj y ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) _ huU
    have hy2 : y ^ 2 = 1 := hInj (by rw [map_pow, hu2, map_one])
    have hy1 : y ≠ 1 := fun h => hu1 (by rw [h, map_one])
    exact orderOf_eq_prime hy2 hy1
  set I' : Subgroup Y := I.comap (MulAut.conj : Y →* MulAut Y) with hI'
  have hmapI : I'.map (MulAut.conj : Y →* MulAut Y) = I := Subgroup.map_comap_eq_self hIinn
  have hI'perf : ⁅I', I'⁆ = I' := by
    apply Subgroup.map_injective hInj
    rw [Subgroup.map_commutator, hmapI, hI]
  have hI'le : I' ≤ centralizer ({y} : Set Y) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_iff.mp (hIU hw) _ huU
    apply hInj
    rw [map_mul, map_mul]
    exact this.symm
  have hbot := eq_bot_of_perfect_of_le hI'le (hcent y hy2) hI'perf
  have hIbot : I = ⊥ := by rw [← hmapI, hbot, Subgroup.map_bot]
  have hQ1 : Q = ⊥ := le_bot_iff.mp (by rw [← hIbot]; exact hQI)
  have h4 := hQ.2
  rw [hQ1, card_bot] at h4
  omega

end FinGlue

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
