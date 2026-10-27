module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverCore

public section

namespace CFSG.AGLEmbedding

section Omega

variable {K : Type} [Group K]

@[expose] def omegaOf (H : Subgroup K) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (p : ℕ) :
    Subgroup K where
  carrier := {x | x ∈ H ∧ x ^ p = 1}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [(show Commute x y from hH x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem H, one_pow p⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

variable {H : Subgroup K} {hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x} {p : ℕ}

theorem mem_omegaOf {x : K} : x ∈ omegaOf H hH p ↔ x ∈ H ∧ x ^ p = 1 := Iff.rfl

theorem omegaOf_le : omegaOf H hH p ≤ H := fun _ hx => hx.1

theorem isElemAbelian_omegaOf : Open.IsElemAbelian p (omegaOf H hH p) :=
  ⟨⟨⟨fun a b => Subtype.ext (hH _ a.2.1 _ b.2.1)⟩⟩, fun _ hx => hx.2⟩

theorem le_normalizer_omegaOf {T : Subgroup K} (hT : T ≤ Subgroup.normalizer (H : Set K)) :
    T ≤ Subgroup.normalizer (omegaOf H hH p : Set K) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_omegaOf, mem_omegaOf, ← Subgroup.mem_normalizer_iff.mp (hT ht) x, conj_pow,
    conj_eq_one_iff]

end Omega

section Cover

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem ModuleSpec.pow_succ_le_card_omegaOf [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K))
    (hcomm : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x) (hF : D.NoFun) :
    p ^ (D.n + 1) ≤ Nat.card (omegaOf (D.span.comap π) hcomm p) := by
  have := Fact.mk hp
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  have hZÂ : ∀ z ∈ Subgroup.center K, z ∈ D.span.comap π := fun z hz => by
    rw [Subgroup.mem_comap, hπZ z hz]
    exact one_mem _
  set A := omegaOf (D.span.comap π) hcomm p
  have hmap : A.map π = D.span := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr omegaOf_le) fun u hu => ?_
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨z, hz, hxz⟩ := D.exists_pow_eq_pow_of_noFun π hp hp2 hπ hker hZp hZc hF x hu
    refine ⟨x * z⁻¹, ⟨mul_mem hu (hZÂ _ (inv_mem hz)), ?_⟩, ?_⟩
    · rw [(show Commute x z⁻¹ from Subgroup.mem_center_iff.mp (inv_mem hz) x).mul_pow, hxz,
        inv_pow, mul_inv_cancel]
    · rw [map_mul, hπZ _ (inv_mem hz), mul_one]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Subgroup.center K, orderOf z₀ = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hord : orderOf (z₀ : K) = p := (Subgroup.orderOf_coe z₀).trans hz₀
  have hz₀A : (z₀ : K) ∈ A := ⟨hZÂ _ z₀.2, hord ▸ pow_orderOf_eq_one _⟩
  have hkcard : p ≤ Nat.card (π.domRestrict A).ker := by
    have hmem : (⟨z₀, hz₀A⟩ : A) ∈ (π.domRestrict A).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      exact hπZ _ z₀.2
    calc p = orderOf (⟨z₀, hz₀A⟩ : A) := by rw [Subgroup.orderOf_mk, hord]
      _ = Nat.card (Subgroup.zpowers (⟨z₀, hz₀A⟩ : A)) := (Nat.card_zpowers _).symm
      _ ≤ Nat.card (π.domRestrict A).ker :=
        Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hmem)
  have h1 := Subgroup.card_mul_index (π.domRestrict A).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hmap, D.card_span hp] at h1
  rw [pow_succ, ← h1, mul_comm]
  exact Nat.mul_le_mul_right _ hkcard

end Cover

theorem coverModuleLemma : CoverModuleLemma := by
  intro K _ _ X _ π hπ hker p hp hp2 hZ1 hZp hZc hdat T
  obtain ⟨D, hn, hA, hF, P, hP⟩ := hdat
  have := Fact.mk hp
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P (T.mapSurjective hπ)
  let D' := D.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hPg : ((g • P : Sylow p X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hTN : (T : Subgroup K).map π ≤ Subgroup.normalizer (D'.span : Set X) := by
    rw [← Sylow.coe_mapSurjective hπ, ← hg, hPg, show D'.span = _ from D.map_span _ _]
    exact (Subgroup.map_mono hP).trans (Subgroup.le_normalizer_map _)
  have hcomm := D'.commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
  have hTÂ : (T : Subgroup K) ≤ Subgroup.normalizer ((D'.span.comap π : Subgroup K) : Set K) :=
    fun t ht => Subgroup.le_normalizer_comap π (hTN (Subgroup.mem_map_of_mem π ht))
  have hÂp : IsPGroup p (D'.span.comap π) := by
    refine IsPGroup.comap_of_ker_isPGroup (fun u => ⟨1, ?_⟩) π (hker ▸ hZp)
    rw [pow_one]
    exact Subtype.ext (D'.pow_eq_one_of_mem u.2)
  have hÂT : D'.span.comap π ≤ T :=
    sup_eq_right.mp (T.is_maximal' (hÂp.to_sup_of_normal_left' T.isPGroup' hTÂ) le_sup_right)
  refine ⟨omegaOf (D'.span.comap π) hcomm p, omegaOf_le.trans hÂT, le_normalizer_omegaOf hTÂ,
    isElemAbelian_omegaOf, ?_⟩
  calc p ^ (p + 1) ≤ p ^ (D'.n + 1) := Nat.pow_le_pow_right hp.pos (Nat.succ_le_succ hn)
    _ ≤ _ := D'.pow_succ_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hcomm hF

end CFSG.AGLEmbedding
