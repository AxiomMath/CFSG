module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ClassicalInvolution

theorem natCard_centralizer_singleton_mulEquiv {G M : Type*} [Group G] [Group M] (e : G ≃* M)
    (t : G) :
    Nat.card (centralizer ({t} : Set G)) = Nat.card (centralizer ({e t} : Set M)) := by
  have h : (centralizer ({t} : Set G)).map e.toMonoidHom = centralizer ({e t} : Set M) := by
    ext y
    simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← h]
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv)

theorem natCard_centralizer_subtype {P : Type*} [Group P] (M : Subgroup P) (x : M) :
    Nat.card (centralizer ({x} : Set M)) = Nat.card (centralizerIn M (x : P)) := by
  have h : (centralizer ({x} : Set M)).map M.subtype = centralizerIn M (x : P) := by
    ext y
    simp only [mem_map, mem_centralizer_singleton_iff, centralizerIn, mem_inf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hy, hc⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩
  rw [← h]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).toEquiv

theorem natCard_centralizerIn_conj {P : Type*} [Group P] (M : Subgroup P) {c : P} (hc : c ∈ M)
    (r : P) : Nat.card (centralizerIn M (c * r * c⁻¹)) = Nat.card (centralizerIn M r) := by
  have h : (centralizerIn M r).map (MulAut.conj c).toMonoidHom = centralizerIn M (c * r * c⁻¹) := by
    ext y
    simp only [mem_map, centralizerIn, mem_inf, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hz, hzc⟩, rfl⟩
      refine ⟨M.mul_mem (M.mul_mem hc hz) (M.inv_mem hc), ?_⟩
      calc c * z * c⁻¹ * (c * r * c⁻¹) = c * (z * r) * c⁻¹ := by group
        _ = c * (r * z) * c⁻¹ := by rw [hzc]
        _ = c * r * c⁻¹ * (c * z * c⁻¹) := by group
    · rintro ⟨hy, hyc⟩
      refine ⟨c⁻¹ * y * c, ⟨M.mul_mem (M.mul_mem (M.inv_mem hc) hy) hc, ?_⟩, by group⟩
      have : c⁻¹ * y * c * r = r * (c⁻¹ * y * c) := by
        calc c⁻¹ * y * c * r = c⁻¹ * (y * (c * r * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * r * c⁻¹) * y) * c := by rw [hyc]
          _ = r * (c⁻¹ * y * c) := by group
      exact this
  rw [← h]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).toEquiv).symm

theorem natCard_centralizer_of_cover {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}
    {r : Equiv.Perm (Fin n)} {K : Subgroup (Equiv.Perm (Fin n))}
    (hcov : ∀ u : Equiv.Perm (Fin n), (1 : Equiv.Perm (Fin n))⁻¹ * u ∈ M → orderOf u = 2 →
      ∃ c ∈ M, u = c * r * c⁻¹)
    (hcent : centralizerIn M r = K) {G : Type} [Group G] (e : G ≃* ↥M) {t : G}
    (ht : orderOf t = 2) : Nat.card (centralizer ({t} : Set G)) = Nat.card K := by
  have hu : orderOf ((e t : ↥M) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨c, hcM, hc⟩ := hcov _ (by simp) hu
  rw [natCard_centralizer_singleton_mulEquiv e t, natCard_centralizer_subtype, hc,
    natCard_centralizerIn_conj M hcM, hcent]

theorem natCard_centralizer_involution_M22
    {G : Type} [Group G]
    (e : G ≃* ↥NativeSporadic.M22) {t : G} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set G)) = 384 := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  obtain ⟨-, -, -, hK1, -⟩ := m22_rep_data1
  have e' : G ≃* ↥m22Certificate.originalSubgroup :=
    e.trans (MulEquiv.subgroupCongr m22Certificate_originalSubgroup.symm)
  rw [natCard_centralizer_of_cover (r := m22Rep1) (K := m22CentQ1.originalSubgroup)
    (fun u hu ho => by
      obtain ⟨d, hd, c, hc, hud⟩ := hcov u hu ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨c, hc, hud⟩)
    (hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)) e' ht, hK1]

theorem natCard_centralizer_involution_M23
    {G : Type} [Group G]
    (e : G ≃* ↥NativeSporadic.M23) {t : G} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set G)) = 2688 := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  obtain ⟨-, -, -, hK1, -⟩ := m23_rep_data1
  have e' : G ≃* ↥m23Certificate.originalSubgroup :=
    e.trans (MulEquiv.subgroupCongr m23Certificate_originalSubgroup.symm)
  rw [natCard_centralizer_of_cover (r := m23Rep1) (K := m23CentQ1.originalSubgroup)
    (fun u hu ho => by
      obtain ⟨d, hd, c, hc, hud⟩ := hcov u hu ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨c, hc, hud⟩)
    (hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)) e' ht, hK1]

end CFSG.OddStandard.Solomon75
