module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_baum_of_thompsonJ_le {H T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T H)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∀ x ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (baum T : Set G),
      ∃ c ∈ H ⊓ Subgroup.centralizer (V : Set G), x = n * c := by
  have hHC : H ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    B2F.le_normalizer_centralizer hHN
  have hTH : T ≤ H := hT.1
  have hCN : H ≤
      Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer hHC
  have hRC : T ⊓ Subgroup.centralizer (V : Set G) ≤ H ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ hTH
  have hR2 : IsPGroup 2 (T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    hT.2.1.to_le inf_le_left
  have hodd : ¬ 2 ∣ (T ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (H ⊓ Subgroup.centralizer (V : Set G)) := by
    have h := not_two_dvd_relIndex_inf_of_normalizer (S := T)
      (D := H ⊓ Subgroup.centralizer (V : Set G)) (K := H) hTH inf_le_left hT.2.2
      (hTH.trans hCN)
    have heq : T ⊓ (H ⊓ Subgroup.centralizer (V : Set G)) =
        T ⊓ Subgroup.centralizer (V : Set G) :=
      le_antisymm (fun x hx => ⟨hx.1, hx.2.2⟩) (fun x hx => ⟨hx.1, hTH hx.1, hx.2⟩)
    rwa [heq] at h
  have hfrat := exists_mul_of_sylow inf_le_left hCN hRC hR2 hodd
  have hJR : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (thompsonJ_le_self T) hJ
  have hbeq : baum T = baum (T ⊓ Subgroup.centralizer (V : Set G)) :=
    baum_eq_baum_centralizer hV hVT hJR
  intro x hx
  obtain ⟨n, hn, c, hc, rfl⟩ := hfrat x hx
  refine ⟨n, ⟨hn.1, ?_⟩, c, hc, rfl⟩
  have := normalizer_le_normalizer_baum (T ⊓ Subgroup.centralizer (V : Set G)) hn.2
  rwa [← hbeq] at this

end CFSG.QuasithinUnique.L246.C123
