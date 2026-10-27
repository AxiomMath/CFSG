module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace MuTab

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem muIso_natCard {X : Type} [Group X] (h : MuIso Ω W X) :
    Nat.card ↥(muGroup Ω W) = Nat.card X := by
  obtain ⟨φ⟩ := h
  exact Nat.card_congr φ.toEquiv

section Indep

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muTabElt_ne_mul (ρ₁ ρ₂ ρ₃ : Rep Ω W) (h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K)
    (h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K) : muTabElt ρ₃ ≠ muTabElt ρ₁ * muTabElt ρ₂ := by
  have c := muTabCtx hP hW
  intro heq
  obtain ⟨u, hu⟩ := exists_zpowers_eq_inf_W hP.1 hP.2.1 hP.2.2.1 hW ρ₃.hR
  obtain ⟨hRK, -, -, h4, -⟩ := inf_W_of_mem_D hP.1 hP.2.1 hP.2.2.1 hW ρ₃.hR ρ₃.hK ρ₃.hRK
  have huR : u ∈ ρ₃.R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have huKW : u ∈ ρ₃.K ⊓ W := hRK ▸ huR
  have hord : 4 ≤ orderOf u := by
    rw [← Nat.card_zpowers, hu]
    exact h4
  have hr1N := ρ₁.r_mem_normalizer
  have hr2N := ρ₂.r_mem_normalizer
  have hr3N := ρ₃.r_mem_normalizer
  have himg : piG W ρ₃.r = piG W (ρ₁.r * ρ₂.r) := by
    rw [piG_mul hr1N hr2N, ← muTabElt_coe, ← muTabElt_coe, ← muTabElt_coe]
    exact congrArg Subtype.val heq
  have hx : ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r) ∈ W ⊔ OCW W :=
    (piG_eq_iff hr3N (Subgroup.mul_mem _ hr1N hr2N)).mp himg
  have hcentr : W ⊔ OCW W ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le (fun w hw => ?_) ((OCW_le_centralizer W).trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr huKW.2)))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W u huKW.2 w hw).symm
  have hxu : (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) * u = u * (ρ₃.r⁻¹ * (ρ₁.r * ρ₂.r)) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcentr hx)
  have h1u : ρ₁.r * u = u * ρ₁.r := c.centralizes ρ₁ ρ₃ h13 huKW
  have h2u : ρ₂.r * u = u * ρ₂.r := c.centralizes ρ₂ ρ₃ h23 huKW
  have h3u : ρ₃.r * u * ρ₃.r⁻¹ = u⁻¹ := c.conj_inv ρ₃ huKW
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

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

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
    muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (muTabElt_mem _)
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

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

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
    muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (muTabElt_mem _)
  have hne1 : ∀ i, muTabElt (ρ i) ≠ 1 := fun i => muDelta_ne_one hW (muTabElt_mem _)
  exact ⟨fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_z2.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_perm3.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ (natCard_invols_klein.le.trans (by norm_num))
      _ hdinj hsq hne1,
    fun ⟨φ⟩ => not_ten_involutions φ natCard_invols_perm4.le _ hdinj hsq hne1⟩

end Big10

end MuTab

end CFSG.ClassicalInvolution.Asc77
