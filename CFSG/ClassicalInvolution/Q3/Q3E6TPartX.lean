module

public import CFSG.ClassicalInvolution.Q3.Q3E6TSplit
public import CFSG.ClassicalInvolution.Q3.Q3E8BShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Q3.Q3W Module
open scoped MatrixGroups commutatorElement
open Matrix

theorem mulVec_commute_of_split {K : Type*} [Field K] {n : ℕ}
    (X Y T : Matrix (Fin n) (Fin n) K) (M W : Submodule K (Fin n → K)) (hMW : M ⊔ W = ⊤)
    (hM : ∀ v, T *ᵥ v = -v → v ∈ M) (hW : ∀ v, T *ᵥ v = v → v ∈ W)
    (hTM : ∀ m ∈ M, T *ᵥ m = -m) (hTW : ∀ w ∈ W, T *ᵥ w = w)
    (hXT : X * T = T * X) (hYT : T * Y = Y * T)
    (hYM : ∀ m ∈ M, Y *ᵥ m = -m) (hXW : ∀ w ∈ W, X *ᵥ w = w) :
    X * Y = Y * X := by
  rw [Matrix.ext_iff_mulVec]
  intro u
  have hu : u ∈ M ⊔ W := by rw [hMW]; exact Submodule.mem_top
  obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
  have hxm : X *ᵥ m ∈ M := by
    refine hM _ ?_
    calc T *ᵥ (X *ᵥ m) = (T * X) *ᵥ m := by rw [Matrix.mulVec_mulVec]
      _ = (X * T) *ᵥ m := by rw [hXT]
      _ = X *ᵥ (T *ᵥ m) := by rw [Matrix.mulVec_mulVec]
      _ = -(X *ᵥ m) := by rw [hTM m hm, Matrix.mulVec_neg]
  have hyw : Y *ᵥ w ∈ W := by
    refine hW _ ?_
    calc T *ᵥ (Y *ᵥ w) = (T * Y) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = (Y * T) *ᵥ w := by rw [hYT]
      _ = Y *ᵥ (T *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = Y *ᵥ w := by rw [hTW w hw]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYM m hm, hYM _ hxm, hXW w hw, hXW _ hyw,
    Matrix.mulVec_neg]

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem le_centralizer_mul_of_overlap (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn3 : 3 ≤ n)
    {hn2 : 2 ≤ n} {R₁ R₂ B : Subgroup (Su K p f n)} {i₁ i₂ iB : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn2 R₁ i₁) (h₂ : IsLongRootSU2 K p f hn2 R₂ i₂)
    (hB : IsLongRootSU2 K p f hn2 B iB) (hne : i₁ ≠ i₂) (hc12 : Commutes R₁ R₂)
    (hB1 : Commute iB i₁) (hB2 : Commute iB i₂) (hnc1 : ¬ Commutes B R₁)
    (hnc2 : ¬ Commutes B R₂) :
    B ≤ Subgroup.centralizer ({i₁ * i₂} : Set (Su K p f n)) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  obtain ⟨hM1, hM2, hM12⟩ := spaces_of_commutes_su hK hp hn3 h₁ h₂ hne hc12
  have hL1 : minusSpaceSU iB ⊓ minusSpaceSU i₁ ≠ ⊥ :=
    inf_ne_bot_of_not_commutes_su h2 hB h₁ hB1 hnc1
  have hL2 : minusSpaceSU iB ⊓ minusSpaceSU i₂ ≠ ⊥ :=
    inf_ne_bot_of_not_commutes_su h2 hB h₂ hB2 hnc2
  have hdisj : (minusSpaceSU iB ⊓ minusSpaceSU i₁) ⊓ (minusSpaceSU iB ⊓ minusSpaceSU i₂) = ⊥ :=
    le_bot_iff.mp (le_of_le_of_eq (inf_le_inf inf_le_right inf_le_right) hM12)
  have hdimB : finrank K (minusSpaceSU iB) = 2 := hB.finrank_minusSpaceSU h2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (minusSpaceSU iB ⊓ minusSpaceSU i₁)
    (minusSpaceSU iB ⊓ minusSpaceSU i₂)
  have hpos1 : 1 ≤ finrank K ↥(minusSpaceSU iB ⊓ minusSpaceSU i₁) :=
    Submodule.one_le_finrank_iff.mpr hL1
  have hpos2 : 1 ≤ finrank K ↥(minusSpaceSU iB ⊓ minusSpaceSU i₂) :=
    Submodule.one_le_finrank_iff.mpr hL2
  have hbot : finrank K ↥((minusSpaceSU iB ⊓ minusSpaceSU i₁) ⊓
      (minusSpaceSU iB ⊓ minusSpaceSU i₂)) = 0 := by
    rw [hdisj]
    exact finrank_bot K _
  have hle : (minusSpaceSU iB ⊓ minusSpaceSU i₁) ⊔ (minusSpaceSU iB ⊓ minusSpaceSU i₂) ≤
      minusSpaceSU iB := sup_le inf_le_left inf_le_left
  have heq : (minusSpaceSU iB ⊓ minusSpaceSU i₁) ⊔ (minusSpaceSU iB ⊓ minusSpaceSU i₂) =
      minusSpaceSU iB := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hAle : minusSpaceSU iB ≤ minusSpaceSU i₁ ⊔ minusSpaceSU i₂ := by
    rw [← heq]
    exact sup_le_sup inf_le_right inf_le_right
  have hy : ∀ u ∈ minusSpaceSU i₁ ⊔ minusSpaceSU i₂,
      (suMat i₁ * suMat i₂) *ᵥ u = -u := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    have ha1 := mem_minusSpaceSU.mp ha
    have ha2 := mem_fixSpaceSU.mp (hM1 ha)
    have hb2 := mem_minusSpaceSU.mp hb
    have hb1 := mem_fixSpaceSU.mp (hM2 hb)
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_add, ha2, hb2, Matrix.mulVec_neg,
      ha1, hb1]
    abel
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_mul]
  have hxB : x ∈ longRootGroupSU K p f (suMat iB) := hB.eq_longRootGroupSU h2 ▸ hx
  obtain ⟨hxc, -⟩ := mem_longRootGroupSU.mp hxB
  have hxfix : ∀ w ∈ fixSpaceSU iB, suMat x *ᵥ w = w := (hB.mem_iff_fix hK hp).mp hx
  have hyB : suMat iB * (suMat i₁ * suMat i₂) = (suMat i₁ * suMat i₂) * suMat iB := by
    rw [← Matrix.mul_assoc, typeU_suMat_commute hB1, Matrix.mul_assoc, typeU_suMat_commute hB2,
      ← Matrix.mul_assoc]
  exact mulVec_commute_of_split (suMat x) (suMat i₁ * suMat i₂) (suMat iB) (minusSpaceSU iB)
    (fixSpaceSU iB) (hB.isCompl hp).sup_eq_top (fun v h => mem_minusSpaceSU.mpr h)
    (fun v h => mem_fixSpaceSU.mpr h) (fun m hm => mem_minusSpaceSU.mp hm)
    (fun w hw => mem_fixSpaceSU.mp hw) hxc hyB (fun m hm => hy m (hAle hm)) hxfix

end Model


section Transport

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem z_ne_w0 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hR : RouteD3Setup K z)
    (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) : z ≠ nd.w 0 := by
  intro h
  have h1 : nd.j 1 ∈ centralizingMembers (conjClass3 K) {nd.w 0} :=
    ⟨(nd.mem 1 (by norm_num)).1, by rw [← h]; exact (nd.mem 1 (by norm_num)).2⟩
  rcases cp_at_member3_of_hO3 hnab hR c.hO3 (nd.mem 0 (by norm_num)).1 (nd.isCl 0 (by norm_num))
    h1 with hc | heq
  · exact nd.adj 0 (by norm_num) hc
  · exact nd.inj 1 (by norm_num) 0 (by norm_num) (by norm_num) heq

theorem not_subset_center_mul3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hR : RouteD3Setup K z) (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) :
    ¬ ({z * nd.w 0} : Set G) ⊆ Subgroup.center G := by
  have hz2 : z * z = 1 := mul_self_of_isClassicalMember3 c.hz
  have hne := z_ne_w0 hnab hR c nd
  have hxne : z * nd.w 0 ≠ 1 := by
    intro h1
    apply hne
    have h2 : nd.w 0 = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, inv_eq_of_mul_eq_one_right hz2]
  exact CoreAssembly.singleton_not_subset_center hnab hxne

theorem partner_le_centralizer_mul3 (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c)
    {β : Subgroup G} (hβ : IsPartnerU3 c nd β) :
    β ≤ Subgroup.centralizer ({z * nd.w 0} : Set G) := by
  classical
  obtain ⟨t, ht⟩ := hβ.cl
  obtain ⟨g, hg0⟩ := id (nd.mem 4 (by norm_num)).1
  have hg : nd.j 4 = conjSub g K := hg0.symm
  have h0 : 0 < 5 := by norm_num
  have h4 : 4 < 5 := by norm_num
  obtain ⟨W₁, hW₁⟩ := hβ.pK
  obtain ⟨W₂, hW₂⟩ := hβ.p0
  have hzt : z * t = t * z := unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW₁
    c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have htw : t * nd.w 0 = nd.w 0 * t := unitaryStandardPair_involutions_commute card_gf9
    (by norm_num) hW₂ ht.mem (nd.isCl 0 h0).mem ht.orderOf_eq_two
    (nd.isCl 0 h0).orderOf_eq_two
  have hzw : z * nd.w 0 = nd.w 0 * z := (nd.wz 0 h0).symm
  have hβ4 : β ≠ nd.j 4 := by
    intro h
    have := hβ.last
    rw [h] at this
    exact not_commutes_self3 (nd.isCl 4 h4) this
  have hβK : β ≠ K := fun h => hβ.n0 (h ▸ nd.commK 0 h0)
  have hβj0 : β ≠ nd.j 0 := fun h => hβ.nK (h ▸ nd.commK 0 h0)
  obtain ⟨hKz, hKne, R_K, i_K, hRK, hKimg, hyK, hiK⟩ :=
    c.exists_rootData_conj hg c.hK (nd.commK 4 h4) (nd.ne_K 4 h4).symm c.hz
  obtain ⟨hβz, hβne, R_β, i_β, hRβ, hβimg, hyβ, hiβ⟩ :=
    c.exists_rootData_conj hg hβ.mem hβ.last hβ4 ht
  obtain ⟨hjz, hjne, R_0, i_0, hR0, hjimg, hy0, hi0⟩ :=
    c.exists_rootData_conj hg (nd.mem 0 h0).1 (nd.far 0 h0 4 h4 (by norm_num))
      (nd.inj 0 h0 4 h4 (by norm_num)) (nd.isCl 0 h0)
  have hconj : ∀ a b : G, a * b = b * a → (g⁻¹ * a * g) * (g⁻¹ * b * g) =
      (g⁻¹ * b * g) * (g⁻¹ * a * g) := fun a b h => by
    calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [h]
      _ = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by group
  have hKne' : conjSub g⁻¹ β ≠ conjSub g⁻¹ K := fun h => hβK (conjSub_injective g⁻¹ h)
  have hj0ne' : conjSub g⁻¹ β ≠ conjSub g⁻¹ (nd.j 0) := fun h =>
    hβj0 (conjSub_injective g⁻¹ h)
  have hKj0ne' : conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j 0) := fun h =>
    nd.ne_K 0 h0 (conjSub_injective g⁻¹ h).symm
  obtain ⟨hc1, hne1⟩ := c.commute_of_locElt hβz hKz hKne' hRβ hRK hβimg hKimg hyβ hyK hiβ hiK
    (hconj t z hzt.symm)
  obtain ⟨hc2, hne2⟩ := c.commute_of_locElt hβz hjz hj0ne' hRβ hR0 hβimg hjimg hyβ hy0 hiβ hi0
    (hconj t (nd.w 0) htw)
  obtain ⟨hc12, hne12⟩ := c.commute_of_locElt hKz hjz hKj0ne' hRK hR0 hKimg hjimg hyK hy0 hiK
    hi0 (hconj z (nd.w 0) hzw)
  have hcomm12 : Commutes R_K R_0 :=
    (c.commutes_iff_root hKz hjz hRK hKimg hjimg).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK 0 h0))
  have hnc1 : ¬ Commutes R_β R_K := fun h =>
    hβ.nK (Gaps.commutes_symm ((commutes_conjSub_iff g⁻¹).mp
      ((c.commutes_iff_root hβz hKz hRβ hβimg hKimg).mpr h)))
  have hnc2 : ¬ Commutes R_β R_0 := fun h =>
    hβ.n0 ((commutes_conjSub_iff g⁻¹).mp
      ((c.commutes_iff_root hβz hjz hRβ hβimg hjimg).mpr h))
  have hmodel := le_centralizer_mul_of_overlap card_gf9 (by norm_num) (by norm_num : 3 ≤ 5 + 1)
    hRK hR0 hRβ hne12 hcomm12 hc1 hc2 hnc1 hnc2
  have hy : g⁻¹ * z * g * (g⁻¹ * nd.w 0 * g) ∈ locLayer (conjClass3 K) z :=
    (locLayer _ z).mul_mem hyK hy0
  have hcent : conjSub g⁻¹ β ≤
      Subgroup.centralizer ({g⁻¹ * z * g * (g⁻¹ * nd.w 0 * g)} : Set G) := by
    refine (le_centralizer_iff_locImg3 c.hΩ c.hex c.hP1 c.hO3 hβz ⟨_, hy⟩).mpr ?_
    rw [hβimg]
    have h1 := (le_centralizer_iff_map3 c.d.ψ c.d.ker_le c.ker_cop (c.pow_three_root hRβ)
      (i_K * i_0)).mp hmodel
    have h2 : Gaps.locMk (conjClass3 K) z ⟨g⁻¹ * z * g * (g⁻¹ * nd.w 0 * g), hy⟩ =
        c.d.ψ (i_K * i_0) := by
      rw [map_mul, hiK, hi0]
      exact (locElt_mul hyK hy0).symm
    rw [h2]
    exact h1
  intro b hb
  have hb' : g⁻¹ * b * g ∈ conjSub g⁻¹ β := by
    simpa using conj_mem_conjSub (n := g⁻¹) hb
  have := Subgroup.mem_centralizer_singleton_iff.mp (hcent hb')
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc b * (z * nd.w 0) = g * (g⁻¹ * b * g * (g⁻¹ * z * g * (g⁻¹ * nd.w 0 * g))) * g⁻¹ := by group
    _ = g * (g⁻¹ * z * g * (g⁻¹ * nd.w 0 * g) * (g⁻¹ * b * g)) * g⁻¹ := by rw [this]
    _ = (z * nd.w 0) * b := by group

end Transport

end CFSG.ClassicalInvolution.Q3.Q3E6T
