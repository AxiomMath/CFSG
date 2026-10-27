module

public import CFSG.LargeExtraspecial.S14SMHDefs
public import CFSG.LargeExtraspecial.S14SMHLevi
public import CFSG.LargeExtraspecial.S14SMFMain
public import CFSG.LargeExtraspecial.S14SMEFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open SME SMH

namespace SMH

variable {G : Type} [Group G]

theorem exists_commute_of_levi (h34a : SmithE34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {N : Subgroup G}
    (hNM : N ≤ S.M) (hN : Nonempty (N ≃* timmesfeldPSU 6)) {x w : G} (hx : IsConj S.z x)
    (hwc : IsConj S.z w) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) (hwN : w ∈ N) (hwQ : w ∉ S.QG)
    (hxw3 : (x * w) ^ 3 = 1) : ∃ x' ∈ N, IsConj S.z x' ∧ Commute x x' := by
  have hwM : w ∈ S.M := hNM hwN
  have hxx : x * x = 1 := SmithQ.mul_self_eq_one_of_isConj S hx
  have hww : w * w = 1 := SmithQ.mul_self_eq_one_of_isConj S hwc
  obtain ⟨hNQ, hrange⟩ := levi_of_le_M S hw hU hNM hN fun h => hwQ (h hwN)
  have hx0 : toMbarM S ⟨x, hxM⟩ ∈ (toMbar S hNM).range := by
    rw [hrange]
    have hW0 : toMbarM S ⟨w, hwM⟩ ∈ Mbar0 S := by
      rw [← hrange]
      exact ⟨⟨w, hwN⟩, rfl⟩
    have e : (⟨x, hxM⟩ : S.M) = ⟨w, hwM⟩ * ⟨x, hxM⟩ * ⟨w, hwM⟩ * (⟨w, hwM⟩ * ⟨x, hxM⟩)⁻¹ :=
      Subtype.ext (conj_eq_of_pow_three hxx hww hxw3).symm
    rw [e, map_mul, map_inv, map_mul]
    exact (timmesfeldFStar_normal S.Mbar).conj_mem _ hW0 _
  obtain ⟨n, hn⟩ := hx0
  have hρn : S.ρ ⟨n, hNM n.2⟩ = S.ρ ⟨x, hxM⟩ := congrArg Subtype.val hn
  have hx'M : (n : G) ∈ S.M := hNM n.2
  have hx'x' : (n : G) * n = 1 := by
    refine hNQ _ (N.mul_mem n.2 n.2) ((S.ρ_eq_one_iff (⟨n, hx'M⟩ * ⟨n, hx'M⟩)).mp ?_)
    rw [map_mul, hρn, ← map_mul, show (⟨x, hxM⟩ : S.M) * ⟨x, hxM⟩ = 1 from Subtype.ext hxx,
      map_one]
  have hx'w : ((n : G) * w) ^ 3 = 1 := by
    have h3 : (((⟨n, hx'M⟩ : S.M) * ⟨w, hwM⟩) ^ 3 : S.M) = ((n : G) * w) ^ 3 := by
      rw [Subgroup.coe_pow, Subgroup.coe_mul]
    refine hNQ _ (N.pow_mem (N.mul_mem n.2 hwN) 3) ?_
    rw [← h3]
    refine (S.ρ_eq_one_iff _).mp ?_
    have hXW : ((⟨x, hxM⟩ : S.M) * ⟨w, hwM⟩) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_mul]
      exact hxw3
    rw [map_pow, map_mul, hρn, ← map_mul, ← map_pow, hXW, map_one]
  have hx' : IsConj S.z (n : G) :=
    hwc.trans (isConj_iff.mpr ⟨w * n, conj_eq_of_pow_three hx'x' hww hx'w⟩)
  have hxx'Q : x⁻¹ * n ∈ S.QG := by
    refine (S.ρ_eq_one_iff (⟨x, hxM⟩⁻¹ * ⟨n, hx'M⟩)).mp ?_
    rw [map_mul, map_inv, hρn, inv_mul_cancel]
  obtain ⟨q, hq, hxq⟩ := exists_commutator_of_coset (smithE34b_of h34a) S hw hU hx hx' hxM hxQ
    hxx'Q
  have hsq := sq_eq_one_of_mem_commutator h34a S hw hU hx hxM hxQ (commutator_mem S x hq)
  rw [← hxq, inv_eq_of_isConj S hx] at hsq
  exact ⟨n, n.2, hx', commute_of_sq_eq_one S hx hx' hsq⟩

end SMH

theorem smithE421Three_of (h34a : SmithE34a) (h261 : SmithE261) : SmithE421Three := by
  intro G _ _ _ S hw hU x w y hx hwc hy hxz hzw hwy _ _ _ h3xw h3zy
  have hxM : x ∈ S.M := mem_centralizer_singleton_iff.mpr hxz.eq
  have hwM : w ∈ S.M := mem_centralizer_singleton_iff.mpr hzw.symm.eq
  have hxQ : x ∉ S.QG :=
    not_mem_QG_of_orderOf_eq_three S (SmithQ.mul_self_eq_one_of_isConj S hwc) hwM h3xw
  have hwQ : w ∉ S.QG := by
    refine not_mem_QG_of_orderOf_eq_three S (SmithQ.mul_self_eq_one_of_isConj S hx) hxM ?_
    rw [show w * x = x⁻¹ * (x * w) * x by group, orderOf_conj_inv]
    exact h3xw
  obtain ⟨k, hk⟩ := isConj_iff.mp hwc
  have hz1M : k⁻¹ * S.z * k ∈ S.M := (mem_M_conj_iff S k S.z).mpr (by rw [hk]; exact hzw)
  have hy1M : k⁻¹ * y * k ∈ S.M := (mem_M_conj_iff S k y).mpr (by rw [hk]; exact hwy.symm)
  have hz1 : IsConj S.z (k⁻¹ * S.z * k) := SmithGraph.isConj_conj (IsConj.refl _) k
  have hy1 : IsConj S.z (k⁻¹ * y * k) := SmithGraph.isConj_conj hy k
  have h3 : orderOf (k⁻¹ * S.z * k * (k⁻¹ * y * k)) = 3 := by
    rw [show k⁻¹ * S.z * k * (k⁻¹ * y * k) = k⁻¹ * (S.z * y) * k by group, orderOf_conj_inv]
    exact h3zy
  have hz1Q : k⁻¹ * S.z * k ∉ S.QG :=
    not_mem_QG_of_orderOf_eq_three S (SmithQ.mul_self_eq_one_of_isConj S hy1) hy1M h3
  have hy1Q : k⁻¹ * y * k ∉ S.QG := by
    refine not_mem_QG_of_orderOf_eq_three S (SmithQ.mul_self_eq_one_of_isConj S hz1) hz1M ?_
    rw [show k⁻¹ * y * k * (k⁻¹ * S.z * k) = (k⁻¹ * S.z * k)⁻¹ *
      (k⁻¹ * S.z * k * (k⁻¹ * y * k)) * (k⁻¹ * S.z * k) by group, orderOf_conj_inv]
    exact h3
  obtain ⟨N₁, hzN₁, hN₁C, ⟨e₁⟩⟩ := h261 G S hw hU _ _ hz1 hy1 hz1M hy1M hz1Q hy1Q h3
  have hmemN : ∀ g, g ∈ N₁.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * g * k ∈ N₁ := fun g => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hNM : N₁.map (MulAut.conj k).toMonoidHom ≤ S.M := fun g hg => by
    have h := (hN₁C _ ((hmemN g).mp hg)).1
    rw [SmithGraph.commute_conj_iff] at h
    exact S.mem_M_iff.mpr h.eq
  have hwN : w ∈ N₁.map (MulAut.conj k).toMonoidHom :=
    (hmemN w).mpr (by rw [← hk, conj_conj_inv]; exact hzN₁)
  obtain ⟨v, hvN, hv, hxv⟩ := exists_commute_of_levi h34a S hw hU hNM
    ⟨((MulAut.conj k).subgroupMap N₁).symm.trans e₁⟩ hx hwc hxM hxQ hwN hwQ
    (by rw [← h3xw]; exact pow_orderOf_eq_one _)
  exact ⟨v, hv, hxv, (SmithGraph.commute_conj_iff k v y).mp (hN₁C _ ((hmemN v).mp hvN)).2⟩

end CFSG.LargeExtraspecial.S14
