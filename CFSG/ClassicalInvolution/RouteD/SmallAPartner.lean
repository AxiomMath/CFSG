module

public import CFSG.ClassicalInvolution.RouteD.TypeAChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic Module Matrix
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Model

variable {F : Type} [Field F]

theorem coe_eq_neg_of_spaces (h2 : (2 : F) ≠ 0) {hn2 : 2 ≤ 3 + 1} {R₀ R₁ : Subgroup SL(3 + 1, F)}
    {i₀ i₁ : SL(3 + 1, F)} (h₀ : IsLongRootSL2 hn2 R₀ i₀) (h₁ : IsLongRootSL2 hn2 R₁ i₁)
    (hs1 : minusSpace i₀ ≤ fixSpace i₁) (hs2 : minusSpace i₁ ≤ fixSpace i₀) :
    (i₀ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) = -(i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) := by
  have hcompl := isCompl_eigSpace h2 h₁.coe_mul_self
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [Module.finrank_fin_fun] at hsum
  have hd₁ : finrank F (minusSpace i₁) = 2 := h₁.finrank_minusSpace h2
  have hd₀ : finrank F (minusSpace i₀) = 2 := h₀.finrank_minusSpace h2
  have hd₁' : finrank F (eigSpace (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) (-1)) = 2 := hd₁
  have hfix : finrank F (fixSpace i₁) = 2 := by
    have : finrank F (eigSpace (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 1) = 2 := by omega
    exact this
  have heq : minusSpace i₀ = fixSpace i₁ := Submodule.eq_of_le_of_finrank_eq hs1 (by omega)
  have hv : ∀ v : Fin (3 + 1) → F,
      (i₀ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ v =
        -((i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ v) := by
    intro v
    have hvt : v ∈ eigSpace (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) (-1) ⊔
        eigSpace (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 1 := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
    have ha' : (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ a = -a := mem_eigSpace_neg_one.mp ha
    have hb' : (i₁ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ b = b := mem_eigSpace_one.mp hb
    have ha0 : (i₀ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ a = a :=
      mem_eigSpace_one.mp (hs2 ha)
    have hb0 : (i₀ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *ᵥ b = -b := by
      have : b ∈ minusSpace i₀ := by rw [heq]; exact hb
      exact mem_eigSpace_neg_one.mp this
    rw [Matrix.mulVec_add, Matrix.mulVec_add, ha0, hb0, ha', hb']
    abel
  refine Matrix.ext fun a b => ?_
  have := congrFun (hv (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem exists_partner_one (h2 : (2 : F) ≠ 0) {hn2 : 2 ≤ 3 + 1} {R₀ R₁ : Subgroup SL(3 + 1, F)}
    {i₀ i₁ : SL(3 + 1, F)} (h₀ : IsLongRootSL2 hn2 R₀ i₀) (h₁ : IsLongRootSL2 hn2 R₁ i₁)
    (hne : i₀ ≠ i₁) (hR : Commutes R₀ R₁) :
    ∃ (B : Subgroup SL(3 + 1, F)) (iB : SL(3 + 1, F)), IsLongRootSL2 hn2 B iB ∧
      Commute iB i₀ ∧ iB ≠ i₀ ∧ ¬ Commutes B R₀ ∧ Commute iB i₁ ∧ iB ≠ i₁ ∧ ¬ Commutes B R₁ := by
  have hn3 : 3 ≤ 3 + 1 := by omega
  obtain ⟨hs1, hs2, -⟩ := spaces_of_commutes h2 hn3 h₀ h₁ hne hR
  have hmat := coe_eq_neg_of_spaces h2 h₀ h₁ hs1 hs2
  obtain ⟨g, hR1, hi1⟩ := h₁
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  set Tb : Pair (3 + 1) := natPair (3 + 1) 0 2 (by omega) (by omega) (by omega) with hTb
  have hrootInv : ((rootInv F hn2 : SL(3 + 1, F)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
      zMat F (3 + 1) T0.1 := by
    rw [coe_rootInv, negBlock_eq_zMat (by omega : 0 + 2 ≤ 3 + 1)]
    rfl
  have hneg : -(negBlock F (3 + 1) 0) = zMat F (3 + 1) T2.1 := by
    rw [negBlock_eq_diagonal, zMat]
    ext a b
    by_cases hab : a = b
    · subst hab
      fin_cases a <;> simp [hT2, nodePair, natPair]
    · simp [Matrix.diagonal_apply_ne _ hab]
  have hJ : (i₀ : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) *
      (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
      (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) * zMat F (3 + 1) T2.1 := by
    rw [hmat, hi1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_rootInv, ← hneg, Matrix.neg_mul, Matrix.mul_neg, neg_inj, Matrix.mul_assoc,
      coe_inv_mul_coe, Matrix.mul_one]
  have hcinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hi0 : i₀ = g * zElt F T2 * g⁻¹ := by
    have h' : i₀ * g = g * zElt F T2 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hJ
    exact eq_mul_inv_iff_mul_eq.mpr h'
  have hR0 : R₀ = (Lc F T2).map (MulAut.conj g).toMonoidHom := by
    rw [h₀.eq_longRootGroup h2, longRootGroup_eq_map_conj_of_mul_eq g hJ]
    rfl
  have hR1' : R₁ = (Lc F T0).map (MulAut.conj g).toMonoidHom := by
    rw [hR1, rootSL2_eq_longRootGroup h2 hn2, negBlock_eq_zMat (by omega : 0 + 2 ≤ 3 + 1)]
    rfl
  have hi1' : i₁ = g * zElt F T0 * g⁻¹ := by
    have : rootInv F hn2 = zElt F T0 := Subtype.ext hrootInv
    rw [hi1, this]
  have hcz : ∀ T' : Pair (3 + 1),
      Commute (g * zElt F Tb * g⁻¹) (g * zElt F T' * g⁻¹) := fun T' =>
    commute_conj (signGroup_comm (zElt_mem_signGroup Tb) (zElt_mem_signGroup T')) g
  have hmemb : ∀ {T' : Pair (3 + 1)} (x : Fin (3 + 1)), x ∈ Tb.1 → x ∉ T'.1 →
      g * zElt F Tb * g⁻¹ ≠ g * zElt F T' * g⁻¹ := fun {T'} x hx hx' h =>
    zElt_ne_of_mem h2 hx hx' (mul_left_cancel (mul_right_cancel h))
  refine ⟨(Lc F Tb).map (MulAut.conj g).toMonoidHom, g * zElt F Tb * g⁻¹,
    (isLongRootSL2_Lc h2 hn2 Tb).conj g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi0]; exact hcz T2
  · rw [hi0]
    exact hmemb ⟨0, by omega⟩ (by simp [hTb, natPair])
      (by simp [hT2, nodePair, natPair, Fin.ext_iff])
  · rw [hR0, commutes_map_iff _ hcinj]
    exact not_commutes_Lc_overlap h2 hn3 (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩)
      (k := ⟨3, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  · rw [hi1']; exact hcz T0
  · rw [hi1']
    exact hmemb ⟨2, by omega⟩ (by simp [hTb, natPair])
      (by simp [hT0, nodePair, natPair, Fin.ext_iff])
  · rw [hR1', commutes_map_iff _ hcinj]
    have hswap : Lc F Tb = Lc F (⟨{⟨2, by omega⟩, ⟨0, by omega⟩},
        Finset.card_pair (by simp)⟩ : Pair (3 + 1)) :=
      Lc_congr (Finset.pair_comm _ _)
    rw [hswap]
    exact not_commutes_Lc_overlap h2 hn3 (i := ⟨2, by omega⟩) (j := ⟨0, by omega⟩)
      (k := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) (by simp) (by simp)

end Model

section Partner

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx.exists_partner_three (c : ACtx p f 3 Ω K z) (nd : Nodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember p f β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      ¬ Commutes β (nd.j 0) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.j 0)) ∧
      Commutes β (nd.j 2) := by
  have h2 := c.two_ne_zero
  have hMΩ : nd.j 2 ∈ Ω := (nd.mem 2 (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hMΩ
  obtain ⟨hK'm, hK'ne, R₀, i₀, hR₀, hKR₀, hy₀, hi₀⟩ := c.exists_rootData_conj hg c.hK
    (nd.commK 2 (by omega)) (nd.ne_K 2 (by omega)).symm c.hz
  obtain ⟨hN0m, hN0ne, R₁, i₁, hR₁, hN0R, hy₁, hi₁⟩ := c.exists_rootData_conj hg
    (nd.mem 0 (by omega)).1 (nd.far 0 (by omega) 2 (by omega) (by omega))
    (nd.inj 0 (by omega) 2 (by omega) (by omega)) (nd.isCl 0 (by omega))
  have hKne : conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j 0) := fun h =>
    nd.ne_K 0 (by omega) ((conjSub_injective g⁻¹ h).symm)
  have hne : i₀ ≠ i₁ := c.ne_of_rootInv hK'm hN0m hKne hR₀ hR₁ hKR₀ hN0R
  have hR01 : Commutes R₀ R₁ :=
    (c.commutes_iff_root hK'm hN0m hR₀ hKR₀ hN0R).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK 0 (by omega)))
  obtain ⟨B, iB, hB, hc0, hne0, hnc0, hc1, hne1, hnc1⟩ := exists_partner_one h2 hR₀ hR₁ hne hR01
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := exists_member_of_root c.hm c.hodd c.hΩ c.hK c.hz c.hP1 c.d
    (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 0)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm hN0m hB hβ'img hN0R).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm hN0m hB hR₁ hβ'img hN0R hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    commutes_K_of_ne c.hm c.hodd c.hΩ c.hex c.hK c.hz c.hP1 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember.conj hwb g⟩, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro h
    rw [← conjSub_conjSub_inv g K] at h
    exact hnK' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W1, ?_⟩
    have := linearBlockStandardPair_conjSub hW1 g
    rwa [conjSub_conjSub_inv] at this
  · intro h
    rw [← conjSub_conjSub_inv g (nd.j 0)] at h
    exact hn0' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W2, ?_⟩
    have := linearBlockStandardPair_conjSub hW2 g
    rwa [conjSub_conjSub_inv] at this
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr hKβ'M.symm

end Partner

end CFSG.ClassicalInvolution.RouteD
