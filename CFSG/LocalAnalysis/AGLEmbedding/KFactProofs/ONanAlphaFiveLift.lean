module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.RankThree.PartOne.K159.CoverLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

namespace CFSG.AGLEmbedding.KFactProofs.AlphaFive

open scoped commutatorElement
open CFSG.Open CFSG.RankThree.PartTwo.Sec4.Census

theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {a c y : G}
    (h : Commute c y) : ⁅a * c, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {x b d : G}
    (h : Commute d x) : ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (b * d) * x⁻¹ * (d⁻¹ * b⁻¹) = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [(h.inv_right).eq, mul_inv_cancel_right]

theorem eq_top_of_sup_center_eq_top {G : Type*} [Group G] (hG : commutator G = ⊤)
    {M : Subgroup G} (h : M ⊔ Subgroup.center G = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← hG, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  rw [commutatorElement_mul_left_of_commute (Subgroup.mem_center_iff.mp hz _).symm,
    commutatorElement_mul_right_of_commute (Subgroup.mem_center_iff.mp hz' _).symm,
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem pow_eq_one_zmod {p r : ℕ} (a : Multiplicative (Fin r → ZMod p)) : a ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    Pi.zero_apply]

theorem closure_range_basis {p r : ℕ} [NeZero p] {X : Type*} [Group X]
    (θ : Multiplicative (Fin r → ZMod p) →* X) :
    Subgroup.closure (Set.range fun j : Fin r => θ (Multiplicative.ofAdd (Pi.single j 1))) =
      θ.range := by
  have h1 : (Subgroup.closure (Set.range fun j : Fin r =>
      (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
        Multiplicative (Fin r → ZMod p)))).map θ =
      Subgroup.closure (Set.range fun j : Fin r => θ (Multiplicative.ofAdd (Pi.single j 1))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← h1, CFSG.RankThree.PartOne.K159.closure_range_ofAdd_single, ← MonoidHom.range_eq_map]

theorem range_le_of_basis {p r : ℕ} [NeZero p] {X : Type*} [Group X]
    (θ : Multiplicative (Fin r → ZMod p) →* X) {D : Subgroup X}
    (h : ∀ j : Fin r, θ (Multiplicative.ofAdd (Pi.single j 1)) ∈ D) : θ.range ≤ D := by
  rw [← closure_range_basis θ, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact h j

section Lift

variable {G X : Type*} [Group G] [Group X] {φ : G →* X}

theorem exists_lift_subgroup [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1) {r : ℕ}
    (θ : Multiplicative (Fin r → ZMod p) →* X) (hθ : Function.Injective θ)
    (hinv : ∀ j : Fin r, ∃ w : X, w * θ (.ofAdd (Pi.single j 1)) * w⁻¹ =
      (θ (.ofAdd (Pi.single j 1)))⁻¹)
    {D : Subgroup X} (hDθ : θ.range ≤ D)
    (hD : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) :
    ∃ Q : Subgroup G, Q ≤ TripleCoverLift.powOneSubgroup φ D p hD ∧ IsElemAbelian p Q ∧
      p ^ (r + 1) ≤ Nat.card Q ∧
      ∀ g : G, (∀ e ∈ θ.range, Commute (φ g) e) → g ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set E := θ.range with hEdef
  have hE : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x := fun x hx y hy =>
    hD x (hDθ hx) y (hDθ hy)
  set g0 : Fin r → X := fun j => θ (.ofAdd (Pi.single j 1)) with hg0
  have hgp : ∀ j, g0 j ^ p = 1 := fun j => by
    rw [hg0, ← map_pow, pow_eq_one_zmod, map_one]
  have hclosure : Subgroup.closure (Set.range g0) = E := closure_range_basis θ
  have hSE : Set.range g0 ⊆ (E : Set X) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩
  have hgen : ∀ s ∈ Set.range g0, ∃ y : G, φ y = s ∧ y ^ p = 1 := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨w, hw⟩ := hinv j
    exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd (hgp j) hw
  have hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1 := fun e he =>
    TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hE hSE hgen
      (by rw [hclosure]; exact he)
  set Q := TripleCoverLift.powOneSubgroup φ E p hE with hQ
  have hQmem : ∀ {y : G}, y ∈ Q ↔ φ y ∈ E ∧ y ^ p = 1 := TripleCoverLift.mem_powOneSubgroup
  refine ⟨Q, fun y hy => ?_, ?_, ?_, ?_⟩
  · exact TripleCoverLift.mem_powOneSubgroup.mpr ⟨hDθ (hQmem.mp hy).1, (hQmem.mp hy).2⟩
  · exact ⟨⟨⟨fun a b => Subtype.ext (hE _ (hQmem.mp a.2).1 _ (hQmem.mp b.2).1)⟩⟩,
      fun x hx => (hQmem.mp hx).2⟩
  · have hzQ : z ∈ Q := hQmem.mpr ⟨by rw [MonoidHom.mem_ker.mp hz]; exact E.one_mem, hzp⟩
    let ψ : Q →* X := φ.comp Q.subtype
    have hψr : ψ.range = E := by
      ext e
      constructor
      · rintro ⟨x, rfl⟩
        exact (hQmem.mp x.2).1
      · intro he
        obtain ⟨y, hy, hyp⟩ := hlift e he
        exact ⟨⟨y, hQmem.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
    have hcard := Subgroup.card_ker_mul_card_range ψ
    have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
    have hkerle : Subgroup.zpowers (⟨z, hzQ⟩ : Q) ≤ ψ.ker := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact hz
    have ho : orderOf (⟨z, hzQ⟩ : Q) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hzo
    have h1 : p ≤ Nat.card ψ.ker := by
      have := Subgroup.card_le_of_le hkerle
      rwa [Nat.card_zpowers, ho] at this
    have h2 : p ^ r ≤ Nat.card ψ.range := by
      rw [hψr, hEdef, ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    calc p ^ (r + 1) = p * p ^ r := by rw [pow_succ, mul_comm]
      _ ≤ Nat.card ψ.ker * Nat.card ψ.range := Nat.mul_le_mul h1 h2
      _ = Nat.card Q := hcard
  · intro g hg
    have hconj : ∀ g : G, (∀ e ∈ E, Commute (φ g) e) → ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := by
      intro g hg y hy
      obtain ⟨hyE, hyp⟩ := hQmem.mp hy
      refine hQmem.mpr ⟨?_, ?_⟩
      · rw [map_mul, map_mul, map_inv, (hg _ hyE).eq, mul_inv_cancel_right]
        exact hyE
      · rw [conj_pow, hyp, mul_one, mul_inv_cancel]
    have hg' : ∀ e ∈ E, Commute (φ g⁻¹) e := fun e he => by
      rw [map_inv]
      exact (hg e he).inv_left
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj g hg h hh, fun hh => ?_⟩
    have := hconj g⁻¹ hg' _ hh
    simpa [mul_assoc] using this

end Lift

section Core

variable {G X : Type*} [Group G] [Finite G] [Group X]

theorem glbCore_le_comap_conj (p k : ℕ) (hp : p.Prime) {P P' : Subgroup G} (l : G)
    (h : P.map (MulAut.conj l).toMonoidHom = P') :
    GLBCore p k P ≤ (GLBCore p k P').comap (MulAut.conj l).toMonoidHom := by
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p k _ _).mpr fun Q hQ hrank => ?_
  intro n hn
  rw [Subgroup.mem_comap]
  refine CFSG.AGLEmbeddingD2.normalizer_le_glbCore p k (Q := Q.map (MulAut.conj l).toMonoidHom)
    (by rw [← h]; exact Subgroup.map_mono hQ) ?_ ?_
  · rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _
      (MulAut.conj l).injective Q]
  · exact Subgroup.le_normalizer_map (MulAut.conj l).toMonoidHom ⟨n, hn, rfl⟩

theorem glbCore_eq_top_of_family {φ : G →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (hperf : commutator G = ⊤) {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) {ι : Type*} (hne : Nonempty ι) (Q : ι → Subgroup G)
    (hQP : ∀ i, Q i ≤ P) (hQr : ∀ i, 3 ≤ Open.pRank p (Q i)) (C : ι → Subgroup X)
    (hQC : ∀ i, ∀ g : G, φ g ∈ C i → g ∈ Subgroup.normalizer (Q i : Set G))
    (hC : Subgroup.closure (⋃ i, (C i : Set X)) = ⊤) (T : Sylow p G) :
    GLBCore p 3 (T : Subgroup G) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T0, hT0⟩ := hP.exists_le_sylow
  have h0 : GLBCore p 3 (T0 : Subgroup G) = ⊤ := by
    set M := GLBCore p 3 (T0 : Subgroup G) with hM
    have hmem : ∀ i, ∀ g : G, φ g ∈ C i → g ∈ M := fun i g hg =>
      CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 3 ((hQP i).trans hT0) (hQr i) (hQC i g hg)
    have hmap : (⊤ : Subgroup X) ≤ M.map φ := by
      rw [← hC, Subgroup.closure_le]
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨g, rfl⟩ := hφ x
      exact ⟨g, hmem i g hi, rfl⟩
    have hsup : M ⊔ Subgroup.center G = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨m, hm, hmg⟩ := hmap (Subgroup.mem_top (φ g))
      have hk : m⁻¹ * g ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
      have hg : g = m * (m⁻¹ * g) := by group
      rw [hg]
      exact Subgroup.mul_mem_sup hm (hker hk)
    exact eq_top_of_sup_center_eq_top hperf hsup
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G T0 T
    have h2 : ((x • T0 : Sylow p G) : Subgroup G) =
        (T0 : Subgroup G).map (MulAut.conj x).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    have h3 : (T0 : Subgroup G).map (MulAut.conj x).toMonoidHom = (T : Subgroup G) := by
      rw [← h2, hx]
    have h4 := glbCore_le_comap_conj p 3 hp x h3
    rw [h0] at h4
    rw [eq_top_iff]
    intro y _
    have h5 := h4 (Subgroup.mem_top (x⁻¹ * y * x))
    rw [Subgroup.mem_comap] at h5
    simpa [MulAut.conj_apply, mul_assoc] using h5
  · obtain ⟨i⟩ := hne
    exact (hQr i).trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top)

end Core

end CFSG.AGLEmbedding.KFactProofs.AlphaFive
