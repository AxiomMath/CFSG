module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6.Mu
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem mem_omegaNbr_of_commutes
  le_centralizer_of_commute commute_conjSub exists_sylow2In Indep3 not_indep3_z2 not_indep3_perm3
  not_indep3_klein not_indep3_perm4 not_ten_involutions natCard_invols_z2 natCard_invols_perm3
  natCard_invols_klein natCard_invols_perm4)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_zpowers_eq_inf_W (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : ∃ u : G, Subgroup.zpowers u = R ⊓ W := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hcyc := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hK hRK).2.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(R ⊓ W))
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact ⟨k, congrArg Subtype.val hk⟩

section Indep

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muTabElt_ne_mul (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K) : muTabElt ρ₃ ≠ muTabElt ρ₁ * muTabElt ρ₂ := by
  intro heq
  obtain ⟨u, hu⟩ := exists_zpowers_eq_inf_W hP.hyp hW ρ₃.hR
  obtain ⟨hRK, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hP.hyp hW ρ₃.hR ρ₃.hK ρ₃.hRK
  have huR : u ∈ ρ₃.R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have huKW : u ∈ ρ₃.K ⊓ W := hRK ▸ huR
  have hord : 4 ≤ orderOf u := by
    rw [← Nat.card_zpowers, hu]
    exact h4
  have hr1N := ρ₁.r_mem_normalizer
  have hr2N := ρ₂.r_mem_normalizer
  have hr3N := ρ₃.r_mem_normalizer
  have himg : piG W ρ₃.r = piG W (ρ₁.r * ρ₂.r) := by
    rw [piG_mul hr1N hr2N, ← MuTab.muTabElt_coe, ← MuTab.muTabElt_coe, ← MuTab.muTabElt_coe]
    exact congrArg Subtype.val heq
  have hx : ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r) ∈ W ⊔ OCW W :=
    (piG_eq_iff hr3N (Subgroup.mul_mem _ hr1N hr2N)).mp himg
  have hcentr : W ⊔ OCW W ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun w hw => ?_) ((OCW_le_centralizer W).trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr huKW.2)))
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW u huKW.2 w hw).symm
  have hxu : (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) * u = u * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcentr hx)
  have h1u : ρ₁.r * u = u * ρ₁.r :=
    Q3CL.Thompson.centralizes_inf_W_of_mem_omegaNbr Sec6Gen.l6_2Gen hP.hyp hW ρ₁.hK ρ₃.hK
      h13.2.1.symm ρ₁.hR ρ₃.hR ρ₁.hRK ρ₃.hRK h13 ρ₁.hr huKW
  have h2u : ρ₂.r * u = u * ρ₂.r :=
    Q3CL.Thompson.centralizes_inf_W_of_mem_omegaNbr Sec6Gen.l6_2Gen hP.hyp hW ρ₂.hK ρ₃.hK
      h23.2.1.symm ρ₂.hR ρ₃.hR ρ₂.hRK ρ₃.hRK h23 ρ₂.hr huKW
  have h3u : ρ₃.r * u * ρ₃.r⁻¹ = u⁻¹ :=
    Q3CL.Thompson.conj_eq_inv_of_mem_inf_W hP.hyp hW ρ₃.hK ρ₃.hR ρ₃.hRK ρ₃.hr ρ₃.hrW huKW
  have h12u : (ρ₁.r * ρ₂.r) * u = u * (ρ₁.r * ρ₂.r) := by
    rw [mul_assoc, h2u, ← mul_assoc, h1u, mul_assoc]
  have e1 : ρ₁.r * ρ₂.r = ρ₃.r * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) := by group
  have e2 : (ρ₁.r * ρ₂.r) * u = u⁻¹ * (ρ₁.r * ρ₂.r) := by
    calc (ρ₁.r * ρ₂.r) * u = ρ₃.r * ((ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) * u) := by
          rw [e1]; group
      _ = ρ₃.r * (u * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r))) := by rw [hxu]
      _ = (ρ₃.r * u * ρ₃.r⁻¹) * (ρ₁.r * ρ₂.r) := by group
      _ = u⁻¹ * (ρ₁.r * ρ₂.r) := by rw [h3u]
  have hinv : u = u⁻¹ := mul_right_cancel (h12u.symm.trans e2)
  have hsq : u * u = 1 := by
    calc u * u = u * u⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel u
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Indep

section Triple

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem exists_indep3 (K : Fin 3 → Subgroup G) (hK : ∀ i, K i ∈ Ω) (hinj : Function.Injective K)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a) :
    ∃ a b c : ↥(muGroup Ω W), Indep3 a b c := by
  choose R hR using fun i => exists_sylow2In (K i)
  have hRle : ∀ i j, i ≠ j → R i ≤ Subgroup.centralizer (R j : Set G) := fun i j hij =>
    le_centralizer_of_commute fun a ha b hb => hcomm i j hij a ((hR i).1 ha) b ((hR j).1 hb)
  have hN : ∀ {A B : Subgroup G}, A ≤ Subgroup.centralizer (B : Set G) →
      A ≤ Subgroup.normalizer (B : Set G) := fun h => h.trans (Subgroup.centralizer_le_normalizer _)
  have h01 : IsPGroup 2 ↥(R 0 ⊔ R 1) :=
    (hR 0).2.1.to_sup_of_normal_right' (hR 1).2.1 (hN (hRle 0 1 (by decide)))
  have hQ : IsPGroup 2 ↥(R 0 ⊔ R 1 ⊔ R 2) :=
    h01.to_sup_of_normal_right' (hR 2).2.1
      (hN (sup_le (hRle 0 2 (by decide)) (hRle 1 2 (by decide))))
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow hP hW K R hK hR (R 0 ⊔ R 1 ⊔ R 2) hQ (by
    intro i; fin_cases i
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right)
  choose ρ hρ using hg
  have hKne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := fun i j hij h => by
    rw [hρ i, hρ j] at h
    exact hij (hinj ((conjSub_inj g).mp h))
  have hmem : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := fun i j hij =>
    mem_omegaNbr_of_commutes (ρ j).hK (hKne j i (Ne.symm hij)) (by
      rw [hρ i, hρ j]
      exact commute_conjSub (hcomm i j hij) g)
  have hcom : ∀ i j, i ≠ j → muTabElt (ρ i) * muTabElt (ρ j) = muTabElt (ρ j) * muTabElt (ρ i) :=
    fun i j hij => (muTab_commute_iff hP hW (ρ i) (ρ j) (hKne i j hij)).mpr (hmem i j hij)
  have hsq : ∀ i, muTabElt (ρ i) * muTabElt (ρ i) = 1 := fun i =>
    muDelta_mul_self hP.hyp hW (muTabElt_mem _)
  have hne1 : ∀ i, muTabElt (ρ i) ≠ 1 := fun i => muDelta_ne_one hW (muTabElt_mem _)
  have hdne : ∀ i j, i ≠ j → muTabElt (ρ i) ≠ muTabElt (ρ j) := fun i j hij h =>
    hKne i j hij ((muTabElt_eq_iff hP hW _ _).mp h)
  refine ⟨muTabElt (ρ 0), muTabElt (ρ 1), muTabElt (ρ 2), hsq 0, hsq 1, hsq 2, hne1 0, hne1 1,
    hne1 2, hcom 0 1 (by decide), hcom 0 2 (by decide), hcom 1 2 (by decide),
    hdne 0 1 (by decide), hdne 2 0 (by decide), hdne 2 1 (by decide), ?_⟩
  exact muTabElt_ne_mul hP hW (ρ 0) (ρ 1) (ρ 2) (hmem 0 2 (by decide)) (hmem 1 2 (by decide))

theorem not_small_of_triple (K : Fin 3 → Subgroup G) (hK : ∀ i, K i ∈ Ω)
    (hinj : Function.Injective K)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a) :
    ¬ MuIsoZ2 Ω W ∧ ¬ MuIsoS3 Ω W ∧ ¬ MuIsoE4 Ω W ∧ ¬ MuIsoS4 Ω W := by
  obtain ⟨a, b, c, h⟩ := exists_indep3 hP hW K hK hinj hcomm
  exact ⟨fun ⟨φ⟩ => not_indep3_z2 φ h, fun ⟨φ⟩ => not_indep3_perm3 φ h,
    fun ⟨φ⟩ => not_indep3_klein φ h, fun ⟨φ⟩ => not_indep3_perm4 φ h⟩

end Triple

section Big10

variable {ι : Type}

theorem exists_rep_of_member_U (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) (K U : ι → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hU : ∀ i, U i ∈ USet Ω) (hUK : ∀ i, U i ≤ K i) (Q : Subgroup G)
    (hQ : IsPGroup 2 ↥Q) (hUQ : ∀ i, U i ≤ Q) :
    ∃ g : G, ∀ i, ∃ ρ : Rep Ω W, ρ.K = conjSub g (K i) := by
  obtain ⟨S₀, hS₀⟩ := hQ.exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S
  refine ⟨g, fun i => ?_⟩
  have hUi : conjSub g (U i) ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) ((hUQ i).trans hS₀)
    rwa [hg] at this
  obtain ⟨T, hT, hTK⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hP.hyp hW hWS
    (hP.hyp.conjInvariant g (K i) (hK i)) (USet.conj hP.hyp.conjInvariant (hU i) g)
    (conjSub_mono (hUK i)) hUi
  exact ⟨Q3CL.T8.mkRep hP hW (hP.hyp.conjInvariant g (K i) (hK i)) hT hTK, rfl⟩

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem not_small_of_big10 (K U : Fin 10 → Subgroup G) (hKinj : Function.Injective K)
    (hK : ∀ i, K i ∈ Ω) (hU : ∀ i, U i ∈ USet Ω) (hUK : ∀ i, U i ≤ K i) (Q : Subgroup G)
    (hQ : IsPGroup 2 ↥Q) (hUQ : ∀ i, U i ≤ Q) :
    ¬ MuIsoZ2 Ω W ∧ ¬ MuIsoS3 Ω W ∧ ¬ MuIsoE4 Ω W ∧ ¬ MuIsoS4 Ω W := by
  obtain ⟨g, hg⟩ := exists_rep_of_member_U hP hW K U hK hU hUK Q hQ hUQ
  choose ρ hρ using hg
  have hdinj : Function.Injective fun i => muTabElt (ρ i) := fun i j h =>
    hKinj ((conjSub_inj g).mp (by
      rw [← hρ i, ← hρ j]
      exact (muTabElt_eq_iff hP hW _ _).mp h))
  have hsq : ∀ i, muTabElt (ρ i) * muTabElt (ρ i) = 1 := fun i =>
    muDelta_mul_self hP.hyp hW (muTabElt_mem _)
  have hne1 : ∀ i, muTabElt (ρ i) ≠ 1 := fun i => muDelta_ne_one hW (muTabElt_mem _)
  exact ⟨fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_z2.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_perm3.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_klein.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ natCard_invols_perm4.le _ hdinj hsq hne1⟩

end Big10

end CFSG.ClassicalInvolution.Q3.Q3MT
