module

public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.SubgroupAutomorphismsFourQuaternion

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem proper_centric_radical_subgroups (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (T : Subgroup G) (hTS : T < S)
    (hcentric : (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) =
      (Subgroup.center T).map T.subtype)
    (hradical : ∀ R : Subgroup G, T ⊔ Subgroup.centralizer (T : Set G) ≤ R →
      R ≤ Subgroup.normalizer (T : Set G) →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (R : Set G) →
      (∃ k : ℕ, ((T ⊔ Subgroup.centralizer (T : Set G)).subgroupOf R).index = 2 ^ k) →
      R = T ⊔ Subgroup.centralizer (T : Set G)) :
    IsKleinFour T ∨ Nonempty (T ≃* QuaternionGroup 2) := by
  by_contra hcon
  obtain ⟨hK, hQ⟩ := not_or.mp hcon
  have hTS' : T ≤ S := hTS.le
  have hCN := Subgroup.centralizer_le_normalizer (T : Set G)
  have hAut : IsPGroup 2 (MulAut T) := by
    have e : T.subgroupOf S ≃* T := Subgroup.subgroupOfEquivOfLe hTS'
    have h := (Principal.subgroup_automorphisms_outside_four_and_quaternion_eight hn ⟨f⟩).1
      (T.subgroupOf S) (fun hK' => hK (@isKleinFour_of_mulEquiv _ _ _ _ hK' e))
      (fun ⟨e'⟩ => hQ ⟨e.symm.trans e'⟩)
    exact h.of_equiv (MulAut.congr e)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hAut.to_subgroup T.normalizerMonoidHom.range)
  have hidxC : ((Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))).index = 2 ^ a := by
    rw [← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker, ha]
  have hle : (Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) ≤
      (T ⊔ Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidxC] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hNeq := hradical _ (sup_le Subgroup.le_normalizer hCN) le_rfl Subgroup.le_normalizer ⟨k, hk⟩
  have hrange : T.normalizerMonoidHom.range =
      (T.subgroupOf (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom := by
    have htop : (⊤ : Subgroup (Subgroup.normalizer (T : Set G))) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊔
          (Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) := by
      rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hCN]
      conv_rhs => rw [← hNeq]
      exact (Subgroup.subgroupOf_self _).symm
    have hbot : ((Subgroup.centralizer (T : Set G)).subgroupOf
        (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, Subgroup.normalizerMonoidHom_ker]
    rw [MonoidHom.range_eq_map, htop, Subgroup.map_sup, hbot, sup_bot_eq]
  have hNS : (S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) ≤ T := by
    rintro y ⟨hyS, hyN⟩
    have hy : T.normalizerMonoidHom ⟨y, hyN⟩ ∈
        (T.subgroupOf (Subgroup.normalizer (T : Set G))).map T.normalizerMonoidHom :=
      hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨t, htT, ht⟩ := hy
    have hker : t⁻¹ * ⟨y, hyN⟩ ∈ T.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht, inv_mul_cancel]
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    have htT' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp htT
    have hc : (t : G)⁻¹ * y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTS' htT')) hyS, hker⟩
    rw [hcentric] at hc
    have hcT : (t : G)⁻¹ * y ∈ T := Subgroup.map_subtype_le _ hc
    have h := T.mul_mem htT' hcT
    rwa [mul_inv_cancel_left] at h
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact hTS.not_ge
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := S) (T.subgroupOf S) hlt
  rw [normalizer_subgroupOf_eq hTS'] at hgrow
  obtain ⟨y, hyN, hyT⟩ := IsConcreteLE.exists_of_lt hgrow
  exact hyT (Subgroup.mem_subgroupOf.mpr (hNS ⟨y.2, Subgroup.mem_subgroupOf.mp hyN⟩))

end CFSG.Semidihedral.Local
