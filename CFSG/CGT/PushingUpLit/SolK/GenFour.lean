module

public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.GH74 CFSG.Open CFSG.ComponentClassification.AschbacherKnownGroup

section Cyclic

variable {S : Type*} [Group S]

theorem exists_closure_two_of_cyclic_index_le_two (C : Subgroup S) [IsCyclic ↥C]
    (hC : C.index = 1 ∨ C.index = 2) (K : Subgroup S) :
    ∃ s : Finset S, s.card ≤ 2 ∧ Subgroup.closure (s : Set S) = K := by
  classical
  have hD : IsCyclic ↥(K ⊓ C) := Subgroup.isCyclic_of_le (inf_le_right : K ⊓ C ≤ C)
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (K ⊓ C)).1 hD
  have hdD : d ∈ K ⊓ C := hd ▸ Subgroup.mem_zpowers d
  by_cases hKC : K ≤ C
  · refine ⟨{d}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, hd]
    exact inf_eq_left.2 hKC
  · obtain ⟨h, hhK, hhC⟩ := Set.not_subset.1 hKC
    have hidx : C.index = 2 := by
      rcases hC with h1 | h2
      · exact absurd ((Subgroup.index_eq_one.1 h1) ▸ Subgroup.mem_top h) hhC
      · exact h2
    obtain ⟨a₀, ha₀⟩ := Subgroup.index_eq_two_iff.1 hidx
    have hout : ∀ b : S, b ∉ C → b * a₀ ∈ C := fun b hb => by
      rcases ha₀ b with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact h1
      · exact absurd h2 hb
    refine ⟨{d, h}, Finset.card_le_two, le_antisymm ?_ ?_⟩
    · refine (Subgroup.closure_le K).2 ?_
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hdD.1
      · exact hhK
    · intro k hk
      have hdc : d ∈ ((({d, h} : Finset S) : Set S) : Set S) := by simp
      have hhc : h ∈ ((({d, h} : Finset S) : Set S) : Set S) := by simp
      have hzp : Subgroup.zpowers d ≤ Subgroup.closure (({d, h} : Finset S) : Set S) :=
        Subgroup.zpowers_le.2 (Subgroup.subset_closure hdc)
      by_cases hkC : k ∈ C
      · exact hzp (hd ▸ (⟨hk, hkC⟩ : k ∈ K ⊓ C))
      · have h1 : k * a₀ ∈ C := hout k hkC
        have h2 : h * a₀ ∈ C := hout h hhC
        have h3 : k * h⁻¹ ∈ C := by
          have := C.mul_mem h1 (C.inv_mem h2)
          simpa [mul_assoc] using this
        have h4 : k * h⁻¹ ∈ K ⊓ C := ⟨K.mul_mem hk (K.inv_mem hhK), h3⟩
        have h5 : k * h⁻¹ ∈ Subgroup.closure (({d, h} : Finset S) : Set S) := hzp (hd ▸ h4)
        have := Subgroup.mul_mem _ h5 (Subgroup.subset_closure hhc)
        simpa using this

theorem sectionalTwoRankLE_two_of_cyclic_index (C : Subgroup S) [IsCyclic ↥C]
    (hC : C.index = 1 ∨ C.index = 2) : SectionalTwoRankLE S 2 := fun P _ =>
  exists_closure_two_of_cyclic_index_le_two C hC P

theorem sectionalTwoRankLE_four_of_cyclic_index (C : Subgroup S) [IsCyclic ↥C]
    (hC : C.index = 1 ∨ C.index = 2) : SectionalTwoRankLE S 4 :=
  (sectionalTwoRankLE_two_of_cyclic_index C hC).mono (by norm_num)

end Cyclic

theorem sectionalTwoRankLE_of_sylow {X : Type*} [Group X] [Finite X] {r : ℕ} (S : Sylow 2 X)
    (h : SectionalTwoRankLE (S : Subgroup X) r) : SectionalTwoRankLE X r := by
  classical
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  let f : (S : Subgroup X) →* X := (MulAut.conj g).toMonoidHom.comp (S : Subgroup X).subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.val_injective
  have hrange : P ≤ f.range := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup X) := hPQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨y, hy, rfl⟩ := hxQ
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨s, hs, hsP⟩ := h (P.comap f) (hP.comap_of_injective f hf)
  refine ⟨s.image f, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsP, Subgroup.map_comap_eq,
    inf_eq_right.mpr hrange]

theorem dihedral_cyclic_index (m : ℕ) [NeZero m] :
    ∃ C : Subgroup (DihedralGroup m), IsCyclic ↥C ∧ C.index = 2 := by
  refine ⟨Subgroup.zpowers (DihedralGroup.r 1), inferInstance, ?_⟩
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r (1 : ZMod m)))
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, Nat.card_eq_fintype_card,
    DihedralGroup.card] at h1
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  nlinarith

theorem zpowers_index_of_generated {G : Type*} [Group G] (a b : G) (hb2 : b ^ 2 = 1) (k : ℤ)
    (hconj : ∀ j : ℤ, b * a ^ j * b⁻¹ = a ^ (k * j))
    (hgen : ∀ H : Subgroup G, a ∈ H → b ∈ H → H = ⊤) :
    (Subgroup.zpowers a).index = 1 ∨ (Subgroup.zpowers a).index = 2 := by
  classical
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hb : ∀ j : ℤ, b * a ^ j = a ^ (k * j) * b := by
    intro j
    have h := hconj j
    rw [hbinv] at h
    calc b * a ^ j = (b * a ^ j * b) * b := by rw [mul_assoc (b * a ^ j) b b, hbb, mul_one]
      _ = a ^ (k * j) * b := by rw [h]
  let T : Subgroup G :=
    { carrier := {g | ∃ i : ℤ, g = a ^ i ∨ g = a ^ i * b}
      one_mem' := ⟨0, Or.inl (by simp)⟩
      mul_mem' := by
        rintro x y ⟨i, hx | hx⟩ ⟨j, hy | hy⟩
        · exact ⟨i + j, Or.inl (by rw [hx, hy, zpow_add])⟩
        · exact ⟨i + j, Or.inr (by rw [hx, hy, zpow_add, mul_assoc])⟩
        · refine ⟨i + k * j, Or.inr ?_⟩
          rw [hx, hy]
          calc a ^ i * b * a ^ j = a ^ i * (b * a ^ j) := by rw [mul_assoc]
            _ = a ^ i * (a ^ (k * j) * b) := by rw [hb j]
            _ = a ^ (i + k * j) * b := by rw [← mul_assoc, zpow_add]
        · refine ⟨i + k * j, Or.inl ?_⟩
          rw [hx, hy]
          calc a ^ i * b * (a ^ j * b) = a ^ i * (b * a ^ j) * b := by group
            _ = a ^ i * (a ^ (k * j) * b) * b := by rw [hb j]
            _ = a ^ (i + k * j) * (b * b) := by rw [zpow_add]; group
            _ = a ^ (i + k * j) := by rw [hbb, mul_one]
      inv_mem' := by
        rintro x ⟨i, hx | hx⟩
        · exact ⟨-i, Or.inl (by rw [hx, zpow_neg])⟩
        · refine ⟨k * (-i), Or.inr ?_⟩
          rw [hx, mul_inv_rev, hbinv, ← zpow_neg, hb (-i)] }
  have hT : T = ⊤ := hgen T ⟨1, Or.inl (by simp)⟩ ⟨0, Or.inr (by simp)⟩
  let C := Subgroup.zpowers a
  have hsurj : Function.Surjective
      (fun t : Bool => (QuotientGroup.mk (if t then b else 1) : G ⧸ C)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ T := hT ▸ Subgroup.mem_top g
    obtain ⟨i, hi | hi⟩ := hg
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [QuotientGroup.eq]
      exact ⟨i, by simp [hi]⟩
    · refine ⟨true, ?_⟩
      simp only [ite_true]
      rw [QuotientGroup.eq]
      refine ⟨k * i, ?_⟩
      show a ^ (k * i) = b⁻¹ * g
      rw [hi, hbinv, ← mul_assoc, hb i, mul_assoc, hbb, mul_one]
  have hfin : Finite (G ⧸ C) := Finite.of_surjective _ hsurj
  have hle : Nat.card (G ⧸ C) ≤ 2 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  have hpos : 0 < Nat.card (G ⧸ C) := Nat.card_pos
  show Nat.card (G ⧸ C) = 1 ∨ Nat.card (G ⧸ C) = 2
  omega

theorem semidihedral_cyclic_index (n : ℕ) :
    ∃ C : Subgroup (SemidihedralGroup n), IsCyclic ↥C ∧ (C.index = 1 ∨ C.index = 2) := by
  classical
  have hb2 : (PresentedGroup.of 1 : SemidihedralGroup n) ^ 2 = 1 := by
    have h := PresentedGroup.one_of_mem (rels := semidihedralRels n)
      (x := FreeGroup.of 1 ^ 2) (by simp [semidihedralRels])
    simpa [map_pow, PresentedGroup.of] using h
  have hbab : (PresentedGroup.of 1 : SemidihedralGroup n) * PresentedGroup.of 0 *
      (PresentedGroup.of 1)⁻¹ =
        (PresentedGroup.of 0 : SemidihedralGroup n) ^ (2 ^ (n - 2) - 1) := by
    have h := PresentedGroup.one_of_mem (rels := semidihedralRels n)
      (x := FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ *
        (FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))⁻¹) (by simp [semidihedralRels])
    simp only [map_mul, map_inv, map_pow] at h
    exact mul_inv_eq_one.1 h
  refine ⟨Subgroup.zpowers (PresentedGroup.of 0), inferInstance,
    zpowers_index_of_generated (PresentedGroup.of 0) (PresentedGroup.of 1) hb2
      ((2 ^ (n - 2) - 1 : ℕ) : ℤ) ?_ ?_⟩
  · intro j
    calc (PresentedGroup.of 1 : SemidihedralGroup n) * PresentedGroup.of 0 ^ j *
          (PresentedGroup.of 1)⁻¹
        = ((PresentedGroup.of 1 : SemidihedralGroup n) * PresentedGroup.of 0 *
            (PresentedGroup.of 1)⁻¹) ^ j := (conj_zpow).symm
      _ = ((PresentedGroup.of 0 : SemidihedralGroup n) ^ (2 ^ (n - 2) - 1)) ^ j := by rw [hbab]
      _ = (PresentedGroup.of 0 : SemidihedralGroup n) ^ (((2 ^ (n - 2) - 1 : ℕ) : ℤ) * j) := by
          rw [← zpow_natCast, ← zpow_mul]
  · intro H ha hb
    rw [eq_top_iff]
    intro x _
    exact PresentedGroup.generated_by _ H (fun j => by fin_cases j <;> assumption) x

theorem gen2_of_dihedral_or_semidihedral {G : Type*} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) : SectionalTwoRankLE G 2 := by
  rcases h with ⟨S, m, hm, ⟨e⟩⟩ | ⟨S, m, hm, ⟨e⟩⟩
  · have : NeZero (2 ^ (m - 1)) := ⟨by positivity⟩
    obtain ⟨C, hC, hidx⟩ := dihedral_cyclic_index (2 ^ (m - 1))
    refine sectionalTwoRankLE_of_sylow S ?_
    refine SectionalTwoRankLE.of_mulEquiv e.symm ?_
    exact sectionalTwoRankLE_two_of_cyclic_index C (Or.inr hidx)
  · obtain ⟨C, hC, hidx⟩ := semidihedral_cyclic_index m
    refine sectionalTwoRankLE_of_sylow S ?_
    refine SectionalTwoRankLE.of_mulEquiv e.symm ?_
    exact sectionalTwoRankLE_two_of_cyclic_index C hidx

theorem gen4_of_dihedral_or_semidihedral {G : Type*} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) : SectionalTwoRankLE G 4 :=
  (gen2_of_dihedral_or_semidihedral h).mono (by norm_num)

end CFSG.CGT.PushingUpLit.SolK
