module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer5
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

variable {t : ∀ i, MulAut ↥(planesIn W I i)}

include h

theorem card_map_rhoV_eq (X : Subgroup H) : Nat.card (X.map h.rhoV) = Nat.card (X.map h.rho) := by
  have h1 := card_map_mul_card_inf_ker h.rhoV X
  have h2 := card_map_mul_card_inf_ker h.rho X
  rw [h.ker_rhoV, ← h.ker_rho_eq_centralizer_V] at h1
  have hpos : 0 < Nat.card ↥(X ⊓ h.rho.ker) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

omit [Finite H] in
theorem centralizer_V_normal : (Subgroup.centralizer (V : Set H)).Normal := by
  rw [← h.ker_rho_eq_centralizer_V]
  exact MonoidHom.normal_ker h.rho

theorem sylow_centralizer_V : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set H))
    (Subgroup.centralizer (V : Set H)) := by
  have hn := h.centralizer_V_normal
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow le_top
    ((hn.subgroupOf (⊤ : Subgroup H)).isSubnormal)

theorem rho_NS_eq_B (ht : h.IsT0 t) :
    (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map h.rho = h.B := by
  let _ := h.cg
  rw [Subgroup.map_sup, h.rho_map_odd, h.rho_S_eq_T0 ht]
  exact le_antisymm (sup_le (cubeBase_le_baseGp h.planeFamily) inf_le_right)
    (baseGp_le_cubeBase_sup h.planeFamily ht)

theorem sylow_S_NS_rhoV (ht : h.IsT0 t) :
    IsSylowTwoOf ((elemBaumannIn 2 R).map h.rhoV)
      ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map h.rhoV) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : IsSylowTwoOf ((elemBaumannIn 2 R).map h.rho)
      ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map h.rho) := by
    rw [h.rho_S_eq_T0 ht, h.rho_NS_eq_B ht]
    exact h.T0_sylow
  have hfinW : Finite (MulAut ↥W) :=
    Finite.of_injective (fun g : MulAut ↥W => (g : ↥W → ↥W)) DFunLike.coe_injective
  have hfinV : Finite (MulAut ↥V) :=
    Finite.of_injective (fun g : MulAut ↥V => (g : ↥V → ↥V)) DFunLike.coe_injective
  rw [isSylowTwoOf_iff] at hW ⊢
  obtain ⟨-, -, hc⟩ := hW
  have hS2 : IsPGroup 2 ↥(elemBaumannIn 2 R) := h.sylow.2.1.to_le (elemBaumannIn_le 2 R)
  refine ⟨Subgroup.map_mono le_sup_right,
    hS2.of_surjective (h.rhoV.subgroupMap _) (h.rhoV.subgroupMap_surjective _), ?_⟩
  unfold twoPart at hc ⊢
  rw [h.card_map_rhoV_eq, h.card_map_rhoV_eq]
  exact hc

theorem NS_normal : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn := oddOrderSubgroup_top_normal (H := H)
  have hSR : elemBaumannIn 2 R ≤ R := elemBaumannIn_le 2 R
  have hchar := characteristic_elemBaumannIn R
  have hSnorm : ((elemBaumannIn 2 R).subgroupOf R).Normal := inferInstance
  have hSn : R ≤ Subgroup.normalizer ((elemBaumannIn 2 R : Subgroup H) : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mp hSnorm
  refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp fun x _ => ?_)
  obtain ⟨n, hn, r, hr, rfl⟩ := h.exists_mul_odd_R x
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_left hn)) ?_
  exact mem_normalizer_sup' (normal_le_normalizer' hNn R hr) (hSn hr)

end WreathHyp

structure TransferConclusion {H : Type*} [Group H] {R M V W F : Subgroup H} {r : ℕ}
    {I : Fin r → Subgroup H} {Pm : Subgroup (Equiv.Perm (Fin r))}
    (h : WreathHyp R M V W F I Pm) (t : ∀ i, MulAut ↥(planesIn W I i)) : Prop where
  H_eq : oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤
  rho_N : (oddOrderSubgroup (⊤ : Subgroup H)).map h.rho = h.D
  W_eq : ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ = W
  W_le_O2 : W ≤ blockQ (oddOrderSubgroup (⊤ : Subgroup H))
  F_eq : F = V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)
  cent_eq : Subgroup.centralizer (W : Set H) = Subgroup.centralizer (V : Set H)
  T0_eq : h.IsT0 t
  maxElem : ∀ A : Subgroup H, IsMaxElemAbelian R A →
    (A ⊓ Subgroup.centralizer (V : Set H)).relIndex A =
        (V ⊓ Subgroup.centralizer (A : Set H)).relIndex V ∧
      ∃ J : Finset (Fin r),
        @IsCoordProduct ↥W h.cg (Fin r) (planesIn W I) (A.map h.rho) J t
  rho_J : (thompsonJ R).map h.rho = h.T0
  rho_S : (elemBaumannIn 2 R).map h.rho = h.T0
  J_le_S : thompsonJ R ≤ elemBaumannIn 2 R
  S_char : ((elemBaumannIn 2 R).subgroupOf R).Characteristic
  J_S : elemThompsonIn 2 (elemBaumannIn 2 R) = thompsonJ R
  ell : ∀ i, Nat.card ↥(WreathHyp.ell t i) = 2 ∧ WreathHyp.ell t i ≤ elemCenterIn 2 R
  S_norm : ∀ i, elemBaumannIn 2 R ≤ Subgroup.normalizer ((I i : Subgroup H) : Set H)
  O2N_le_S : blockQ (oddOrderSubgroup (⊤ : Subgroup H)) ≤ elemBaumannIn 2 R
  W_le_S : W ≤ elemBaumannIn 2 R
  E_eq : elemCenterIn 2 R =
    (elemCenterIn 2 R ⊓
        Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)) ⊔
      (V ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H))
  syl_C : IsSylowTwoOf (elemBaumannIn 2 R ⊓ Subgroup.centralizer (V : Set H))
    ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓ Subgroup.centralizer (V : Set H))
  syl_S : IsSylowTwoOf (elemBaumannIn 2 R) (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)
  NS_normal : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).Normal
  rho_NS : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map h.rho = h.B

theorem internal_S3_wreath_transfer (h : WreathHyp R M V W F I Pm) :
    ∃ t : ∀ i, MulAut ↥(planesIn W I i), TransferConclusion h t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := h.exists_t
  obtain ⟨hPS, hE, hsyl⟩ := h.baumann_apply ht
  obtain ⟨hsylC, hsylS⟩ := hsyl h.sylow_centralizer_V
  have hO2 : blockQ (oddOrderSubgroup (⊤ : Subgroup H)) ≤ elemBaumannIn 2 R := by
    rw [blockQ_eq_map]
    exact hPS
  refine ⟨t, ?_⟩
  exact
    { H_eq := h.odd_sup_R
      rho_N := h.rho_map_odd
      W_eq := h.commutator_V_N
      W_le_O2 := h.W_le_blockQ_odd
      F_eq := h.F_eq_centralizer
      cent_eq := h.centralizer_W_eq_V
      T0_eq := ht
      maxElem := fun A hA => h.maxElem_structure ht hA
      rho_J := h.rho_J_eq_T0 ht
      rho_S := h.rho_S_eq_T0 ht
      J_le_S := thompsonJ_le_baumann
      S_char := characteristic_elemBaumannIn R
      J_S := elemThompsonIn_baumann
      ell := fun i => ⟨h.card_ell ht i, h.ell_le_E ht i⟩
      S_norm := fun i s hs => by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := h.S_normalizes_planes ht hs i
        have h2 : s * y * s⁻¹ ∈ (I i).map (MulAut.conj s).toMonoidHom ↔ y ∈ I i :=
          WreathHyp.mem_map_conj_iff
        rw [h1] at h2
        exact h2.symm
      O2N_le_S := hO2
      W_le_S := h.W_le_blockQ_odd.trans hO2
      E_eq := hE
      syl_C := hsylC
      syl_S := hsylS (h.sylow_S_NS_rhoV ht)
      NS_normal := h.NS_normal
      rho_NS := h.rho_NS_eq_B ht }

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
