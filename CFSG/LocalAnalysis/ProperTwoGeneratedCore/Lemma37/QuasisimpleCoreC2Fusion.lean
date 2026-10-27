module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Quat
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Quasithin

theorem isWeaklyClosedIn_sylow_self {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) : IsWeaklyClosedIn (S : Subgroup G) S := by
  intro g hg
  refine Subgroup.eq_of_le_of_card_ge hg ?_
  rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem conjSet_inv_zpowers {G : Type} [Group G] (u g : G) :
    conjSet (Subgroup.zpowers u : Set G) g⁻¹ = (Subgroup.zpowers (g * u * g⁻¹) : Set G) := by
  ext x
  rw [mem_conjSet_iff, inv_inv, SetLike.mem_coe, SetLike.mem_coe, Subgroup.mem_zpowers_iff,
    Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow]
    group

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u : G}

theorem conj_not_mem_zpowers [Finite G] (hc : PartC T Q P₁ e u) (S : Sylow 2 G)
    (hST : (S : Subgroup G) = T) (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) (g : G) :
    g * u * g⁻¹ ∉ Subgroup.zpowers v := by
  intro hg
  subst hST
  have heq : Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers v := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
      hc.orderOf_eq_four_of_mul_self hvv, hc.orderOf_eq_four_of_mul_self hc.sq]
  have hA : ∀ w ∈ (S : Subgroup G), conjSet (Subgroup.zpowers u : Set G) w = Subgroup.zpowers u :=
    fun w hw => conjSet_eq_iff_mem_normalizer.2 (hnorm hw)
  have hB : ∀ w ∈ (S : Subgroup G), conjSet (Subgroup.zpowers v : Set G) w = Subgroup.zpowers v :=
    fun w hw => conjSet_eq_iff_mem_normalizer.2 (hTv hw)
  have hgAB : conjSet (Subgroup.zpowers u : Set G) g⁻¹ = Subgroup.zpowers v := by
    rw [conjSet_inv_zpowers, heq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hn'⟩ :=
    burnside_fusion_lemma S le_rfl (isWeaklyClosedIn_sylow_self S) hA hB hgAB
  rw [conjSet_eq_iff_mem_normalizer.2 (hNT hn)] at hn'
  have hvu : v ∈ Subgroup.zpowers u := by
    rw [← SetLike.mem_coe, hn']
    exact Subgroup.mem_zpowers v
  have hvP : v ∈ P₁ := Subgroup.zpowers_le.mpr hc.self_mem hvu
  rcases hc.mem_inf v hvQ hvP with h | h
  · rw [h, one_mul] at hvv
    exact hc.centralElt_ne_one hvv.symm
  · rw [h, hc.centralElt_mul_self] at hvv
    exact hc.centralElt_ne_one hvv.symm

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
