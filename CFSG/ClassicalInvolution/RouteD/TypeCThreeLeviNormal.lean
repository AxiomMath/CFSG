module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLayers

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type} [Group G]

@[expose] def leviNode (M : Subgroup G) (d : G) : Subgroup G :=
  ⁅M ⊓ Subgroup.centralizer ({d} : Set G), M ⊓ Subgroup.centralizer ({d} : Set G)⁆

private theorem commutator_le_self_aux (A : Subgroup G) : ⁅A, A⁆ ≤ A :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem h₁ h₂) (A.inv_mem h₁)) (A.inv_mem h₂)

theorem leviNode_le_inf (M : Subgroup G) (d : G) :
    leviNode M d ≤ M ⊓ Subgroup.centralizer ({d} : Set G) :=
  commutator_le_self_aux _

theorem leviNode_le (M : Subgroup G) (d : G) : leviNode M d ≤ M :=
  (leviNode_le_inf M d).trans inf_le_left

theorem leviNode_le_centralizer (M : Subgroup G) (d : G) :
    leviNode M d ≤ Subgroup.centralizer ({d} : Set G) :=
  (leviNode_le_inf M d).trans inf_le_right

theorem conjSub_inf (y : G) (A B : Subgroup G) :
    conjSub y (A ⊓ B) = conjSub y A ⊓ conjSub y B :=
  Subgroup.map_inf _ _ _ (MulAut.conj y).injective

theorem conjSub_centralizer_singleton (y d : G) :
    conjSub y (Subgroup.centralizer ({d} : Set G)) =
      Subgroup.centralizer ({y * d * y⁻¹} : Set G) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (y * d * y⁻¹) = y * ((y⁻¹ * x * y) * d) * y⁻¹ := by group
      _ = y * (d * (y⁻¹ * x * y)) * y⁻¹ := by rw [h]
      _ = (y * d * y⁻¹) * x := by group
  · intro h
    calc y⁻¹ * x * y * d = y⁻¹ * (x * (y * d * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * d * y⁻¹) * x) * y := by rw [h]
      _ = d * (y⁻¹ * x * y) := by group

theorem conjSub_commutator (y : G) (A B : Subgroup G) :
    conjSub y ⁅A, B⁆ = ⁅conjSub y A, conjSub y B⁆ :=
  Subgroup.map_commutator _ _ _

theorem conjSub_leviNode {M : Subgroup G} {d k y : G} (hd : d ∈ M)
    (hk : ∀ m ∈ M, m * k = k * m) (hy : conjSub y M = M) (hyh : y * (d * k) * y⁻¹ = d * k) :
    conjSub y (leviNode M d) = leviNode M d := by
  have hyd : y * d * y⁻¹ ∈ M := by
    have := conj_mem_conjSub (n := y) (K := M) hd
    rwa [hy] at this
  have hM : ∀ m ∈ M, y⁻¹ * m * y ∈ M := fun m hm => by
    have : m ∈ conjSub y M := by rw [hy]; exact hm
    exact mem_conjSub_iff.mp this
  have hk' : ∀ m ∈ M, m * (y * k * y⁻¹) = (y * k * y⁻¹) * m := by
    intro m hm
    have h1 := hk _ (hM m hm)
    calc m * (y * k * y⁻¹) = y * ((y⁻¹ * m * y) * k) * y⁻¹ := by group
      _ = y * (k * (y⁻¹ * m * y)) * y⁻¹ := by rw [h1]
      _ = (y * k * y⁻¹) * m := by group
  obtain ⟨c, hc⟩ : ∃ c : G, c = d⁻¹ * (y * d * y⁻¹) := ⟨_, rfl⟩
  have hyd' : y * d * y⁻¹ = d * c := by rw [hc]; group
  have hce : c = k * (y * k * y⁻¹)⁻¹ := by
    have h1 : (y * d * y⁻¹) * (y * k * y⁻¹) = d * k := by
      calc (y * d * y⁻¹) * (y * k * y⁻¹) = y * (d * k) * y⁻¹ := by group
        _ = d * k := hyh
    have h2 : y * d * y⁻¹ = d * k * (y * k * y⁻¹)⁻¹ := by
      rw [← h1]
      group
    rw [hc, h2]
    group
  have hcm : ∀ m ∈ M, m * c = c * m := by
    intro m hm
    have hmk : Commute m k := hk m hm
    have hmk' : Commute m (y * k * y⁻¹) := hk' m hm
    rw [hce]
    exact hmk.mul_right hmk'.inv_right
  have hcent : M ⊓ Subgroup.centralizer ({y * d * y⁻¹} : Set G) =
      M ⊓ Subgroup.centralizer ({d} : Set G) := by
    ext m
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hm, h⟩
      refine ⟨hm, ?_⟩
      rw [hyd'] at h
      have h3 : m * d * c = d * m * c := by
        calc m * d * c = m * (d * c) := by rw [mul_assoc]
          _ = d * c * m := h
          _ = d * (c * m) := by rw [mul_assoc]
          _ = d * (m * c) := by rw [hcm m hm]
          _ = d * m * c := by rw [mul_assoc]
      exact mul_right_cancel h3
    · rintro ⟨hm, h⟩
      refine ⟨hm, ?_⟩
      rw [hyd']
      calc m * (d * c) = m * d * c := by rw [mul_assoc]
        _ = d * m * c := by rw [h]
        _ = d * (m * c) := by rw [mul_assoc]
        _ = d * (c * m) := by rw [hcm m hm]
        _ = d * c * m := by rw [mul_assoc]
  have hconj : conjSub y (M ⊓ Subgroup.centralizer ({d} : Set G)) =
      M ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [conjSub_inf, hy, conjSub_centralizer_singleton, hcent]
  unfold leviNode
  rw [conjSub_commutator, hconj]

end Generic

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem conjSub_Kf_eq_of_commute (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) (k : Fin 3)
    {y : G} (hy : y * Fr.zf k = Fr.zf k * y) : conjSub y (Fr.Kf k) = Fr.Kf k := by
  have hyz : y * Fr.zf k * y⁻¹ = Fr.zf k := mul_inv_eq_iff_eq_mul.mpr hy
  have hcl : IsClassicalMember p f (conjSub y (Fr.Kf k)) (Fr.zf k) := by
    have := (Fr.clsW S k).conj y
    rwa [hyz] at this
  have hL : conjSub y (Fr.Kf k) ∈ Ω := S.inClass.conjInvariant y _ (Fr.mem k)
  have hLc : conjSub y (Fr.Kf k) ∈ centralizingMembers Ω {Fr.zf k} :=
    ⟨hL, fun x hx => le_centralizer_of_isClassicalMember hcl hx⟩
  by_contra hne
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem k) (Fr.clsW S k)
    (S.shape.conj S.conjInvariant (Fr.gf k))
  refine typeC_not_mem_of_ne S.two_le S.five S.inClass S.exact (Fr.mem k) (Fr.clsW S k)
    (Fr.p1W S k) d hLc hne ?_
  have := conj_mem_conjSub (n := y) (Frame.zf_memW S k (Fr := Fr))
  rwa [hyz] at this

theorem fin_three_eq_of_ne {i j k k' : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hk'i : k' ≠ i) (hk'j : k' ≠ j) : k' = k := by
  revert i j k k'
  decide

theorem conjSub_Mf_le_of_commute (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z)
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {y : G}
    (hy : y * Fr.zf k = Fr.zf k * y) : conjSub y (Mf Fr i j) ≤ Mf Fr i j := by
  unfold Mf
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  have hmem : conjSub y (L : Subgroup G) ∈ memberSet Fr i j := by
    refine ⟨S.inClass.conjInvariant y _ L.2.1, fun k' hk'i hk'j => ?_⟩
    obtain rfl : k' = k := fin_three_eq_of_ne hij hki hkj hk'i hk'j
    have h1 : Commutes (conjSub y (L : Subgroup G)) (conjSub y (Fr.Kf k')) :=
      (commutes_conjSub_iff y).mpr (L.2.2 k' hk'i hk'j)
    rwa [conjSub_Kf_eq_of_commute S Fr k' hy] at h1
  exact le_Mf Fr hmem

theorem conjSub_Mf_eq_of_commute (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z)
    {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {y : G}
    (hy : y * Fr.zf k = Fr.zf k * y) : conjSub y (Mf Fr i j) = Mf Fr i j := by
  refine le_antisymm (conjSub_Mf_le_of_commute S Fr hij hki hkj hy) ?_
  have hy' : y⁻¹ * Fr.zf k = Fr.zf k * y⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy, mul_assoc, mul_inv_cancel, mul_one]
  have := conjSub_mono (n := y) (conjSub_Mf_le_of_commute S Fr hij hki hkj hy')
  rwa [conjSub_conjSub_inv] at this

end Frame

end CFSG.ClassicalInvolution.RouteD
