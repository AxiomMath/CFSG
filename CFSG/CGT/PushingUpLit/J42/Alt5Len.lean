module

public import CFSG.CGT.PushingUpLit.SolK.FourA
public import CFSG.CGT.PushingUpLit.SolK.ThetaKer

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm

theorem perm_eq_one_of_fix_compl_two {d : ℕ} {I : Finset (Fin d)} (hI : I.card = 2)
    {σ : Perm (Fin d)} (hfix : ∀ y, y ∉ I → σ y = y) (hs : sign σ = 1) : σ = 1 := by
  classical
  have hsupp : σ.support ⊆ I := fun y hy => by
    by_contra hyI
    exact (Equiv.Perm.mem_support.1 hy) (hfix y hyI)
  have hcard : σ.support.card ≤ 2 := hI ▸ Finset.card_le_card hsupp
  by_contra hne
  have h0 : σ.support.card ≠ 0 := fun h =>
    hne (Equiv.Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 h))
  have h1 : σ.support.card ≠ 1 := Equiv.Perm.card_support_ne_one σ
  have h2 : σ.support.card = 2 := by omega
  obtain ⟨x, y, hxy, hσ⟩ := Equiv.Perm.card_support_eq_two.1 h2
  rw [hσ, Equiv.Perm.sign_swap hxy] at hs
  exact absurd hs (by decide)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

namespace SolCfg

include S

theorem theta_eq_one_of_len_two_alt
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) {w r : G} (hw : w ∈ S.D.W)
    (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) {t : G}
    (ht : t ∈ TOf M (w * r)) : ∃ htM : t ∈ M, S.θ ⟨t, htM⟩ = 1 := by
  classical
  have hUM : TOf M (w * r) ≤ M := TOf_le_M M _
  have hUC : TOf M (w * r) ≤ CMOf M (w * r) := TOf_le_C M _
  have hU2 : IsPGroup 2 (TOf M (w * r)) := isPGroup_TOf M _
  have hUn : ∀ k ∈ CMOf M (w * r), ∀ u ∈ TOf M (w * r), k * u * k⁻¹ ∈ TOf M (w * r) :=
    fun k hk u hu => normalized_TOf M (w * r) hk hu
  have hN2 := S.theta_isPGroup hUM hU2
  have hNI := S.theta_le_setStab hw hr hUC
  have hNI' : ((TOf M (w * r)).subgroupOf M).map S.θ ≤ setStab (vsupp (S.D.β ⟨w, hw⟩))ᶜ :=
    fun σ hσ x => by
    have := mem_setStab.1 (hNI hσ) x
    simp [this]
  have hfixc := block_fixes hN2 hNI'
    (fun τ hτ => S.theta_norm hw hr hUn
      (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
      (by
        intro x
        have := altOn_le_setStab (vsupp (S.D.β ⟨w, hw⟩))ᶜ hτ x
        rw [Finset.mem_compl, Finset.mem_compl] at this
        exact not_iff_not.1 this))
    (by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
      omega)
  have hσN : S.θ ⟨t, hUM ht⟩ ∈ ((TOf M (w * r)).subgroupOf M).map S.θ :=
    Subgroup.mem_map.2 ⟨⟨t, hUM ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  refine ⟨hUM ht, perm_eq_one_of_fix_compl_two hcard (fun y hy => ?_)
    (Equiv.Perm.mem_alternatingGroup.1 (hA _))⟩
  exact hfixc _ hσN y (Finset.mem_compl.2 hy)

theorem cgOf_le_M_of_len_two_alt (hT : TightData S)
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) {w r : G} (hw : w ∈ S.D.W)
    (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) : CGOf (w * r) ≤ M := by
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  have hO2 : pCoreOf 2 (M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (w * r) : Subgroup G) : Set G)) ≤ pCoreOf 2 M := by
    intro t ht
    obtain ⟨htM, hθ⟩ := S.theta_eq_one_of_len_two_alt hA hw hr hcard ht
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' (M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (w * r) : Subgroup G) : Set G)) ⟨t, ht⟩
    exact hT.ker_two ⟨t, htM⟩ hθ ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hB : Subgroup.zpowers (w * r) ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hx1
  have h := S.centralizer_le_M S.hyp.charTwo hT.abelian (Subgroup.zpowers_le.2 hxQ) hB hO2
  exact (Subgroup.centralizer_le_normalizer
    ((Subgroup.zpowers (w * r) : Subgroup G) : Set G)).trans h.2

theorem exists_len_four_of_not_centInM (hT : TightData S)
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) (hC : ¬ CentInM S) :
    ∃ (w : G) (hw : w ∈ S.D.W) (r : G), r ∈ rOf M X ∧
      (vsupp (S.D.β ⟨w, hw⟩)).card = 4 ∧ ¬ CGOf (w * r) ≤ M := by
  by_contra hcon
  refine hC fun x hx hx1 k hk => ?_
  have hkC : k ∈ CGOf x := by
    rw [CGOf, ← centralizer_singleton_eq_zpowers]
    exact hk
  obtain ⟨l, hl⟩ := S.exists_hasLen hx
  have hev := hl.even
  have hle := hl.le
  have hl' := hl
  obtain ⟨w, hw, r, hr, rfl, hcard⟩ := hl
  have hl6 : l = 0 ∨ l = 2 ∨ l = 4 := by
    obtain ⟨m, hm⟩ := hev
    omega
  rcases hl6 with rfl | rfl | rfl
  · have h := S.centralizer_eq_of_len S.hyp.charTwo hT hx hx1 hl' (by norm_num) (by norm_num)
    exact h.2 ((Subgroup.centralizer_le_normalizer
      ((Subgroup.zpowers (w * r) : Subgroup G) : Set G)) hkC)
  · exact S.cgOf_le_M_of_len_two_alt hT hA hw hr hcard hkC
  · by_contra hkM
    exact hcon ⟨w, hw, r, hr, hcard, fun hle' => hkM (hle' hkC)⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
