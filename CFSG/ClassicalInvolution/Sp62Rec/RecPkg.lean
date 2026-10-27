module

public import CFSG.ClassicalInvolution.Sp62Rec.Recognition
public import CFSG.ClassicalInvolution.Sp62Rec.Generation
public import CFSG.ClassicalInvolution.Sp62Rec.CE
public import CFSG.ClassicalInvolution.Sp62Rec.NA
public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1CE

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

theorem mem_iff_of_map_subgroupOf_eq {M N : Type} [Group M] [Group N] {H P : Subgroup M}
    {K S : Subgroup N} (φ : ↥H ≃* ↥K)
    (hφ : (P.subgroupOf H).map φ.toMonoidHom = S.subgroupOf K) (x : M) (hx : x ∈ H) :
    x ∈ P ↔ ((φ ⟨x, hx⟩ : ↥K) : N) ∈ S := by
  constructor
  · intro hxP
    have h1 : φ ⟨x, hx⟩ ∈ (P.subgroupOf H).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [hφ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hS
    have h1 : φ ⟨x, hx⟩ ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr hS
    rw [← hφ] at h1
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
    have hyx : y = ⟨x, hx⟩ := φ.injective hyeq
    have hy' : (y : M) ∈ P := Subgroup.mem_subgroupOf.mp hy
    rw [hyx] at hy'
    exact hy'


variable {G : Type} [Group G] [Finite G] {z e : G} {E B : Subgroup G} {T : Sylow 2 G}
  {A X : Subgroup G}

theorem E8ZPkg.lieModel_of_E0 (P : E8ZPkg z e E B T A X)
    (V : Subgroup ↥E0) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (↥E0 ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V, (∀ (x : ↥E0) (v : V),
      f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    (hCE0 : ∀ x ∈ Hhat, (∀ y ∈ E0, x * y = y * x) → x = 1 ∨ x = alpha)
    (hA0 : ∀ A' : Subgroup (StatedSp 3 (ZMod 2)), A' ≤ S0 → IsE64 A' → A' = A0) :
    CFSG.Blueprint.LieModel G .PSp 3 2 1 := by
  obtain ⟨-, -, hCEz, -, θ, hθe, hθT, hθA, -⟩ := P.ce card_S0 card_Hhat eq_of_mem_center_S0
    Hhat_le_centralizer_alpha (fun x hx => exists_four_conj hx) V hV hA6 hcomm hCE0 A0 hA0
  obtain ⟨-, -, -, ⟨n, hnA, hne⟩, ν, -, -, -, hθX, hνX⟩ := P.na (rho := rho28) θ hθe hθT hθA
    alpha_mem_A0 pi12_mem_A0 A0_le_S0 card_A0 mem_A0_of_commute le_A0_of_normal hA0
    N0_le_normalizer mem_X0_of_mem_normalizer mem_X0_of_commute_alpha rho28_mem_A0
    mem_orbN0_of_mem_A0 ncard_orbN0.1 ncard_orbN0.2.2.2 card_closure_orbN0_pi12
    exists_fpf_seven exists_rho_N0 card_S0 card_N0 card_X0 Hhat_le_centralizer_alpha
  have hgen := P.sup_normalizer_centralizer_eq_top hCEz.le P.e_mul_self hnA hne
  have hTH : (T : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := P.T_le.trans P.B_le
  have hrig := not_isConj_hhat_symm_pi12_pi3 T θ hTH
    (fun x hx => mem_iff_of_map_subgroupOf_eq θ hθT x hx)
  have hαe : θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ =
      ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact hθe.symm
  have hC : Subgroup.centralizer
      {((θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥(Subgroup.centralizer ({e} : Set G))) : G)} ≤
        Subgroup.centralizer ({e} : Set G) := by
    rw [hαe]
  exact lieModel_of_amalgam ν θ hνX hθX hrig hC hgen

theorem E8ZPkg.lieModel (P : E8ZPkg z e E B T A X) :
    CFSG.Blueprint.LieModel G .PSp 3 2 1 :=
  P.lieModel_of_E0 (V0.subgroupOf E0)
    (fun v hv => Subtype.ext (V0_mul_self _ (Subgroup.mem_subgroupOf.mp hv)))
    nonempty_quotient_V0 commutant_V0 eq_of_commute_E0 eq_A0_of_isE64

end CFSG.ClassicalInvolution.Sp62Rec
