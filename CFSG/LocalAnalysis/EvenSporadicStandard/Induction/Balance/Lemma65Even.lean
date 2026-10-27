module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Normal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Indep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Cover

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard CFSG.RankThree.PerfectCover

@[expose] def evenProducts {Γ : Type} [Group Γ] (e : Γ) : Set Γ :=
  {x | ∃ w ∈ omega e, ∃ w' ∈ omega e, x = w * w'}

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem inv_mul_e_mul {p : Γ} (hp : p ∈ H₁) : p⁻¹ * e * p = e := by
  have h1 := hS.commute_of_mem_H₁ hp
  calc p⁻¹ * e * p = p⁻¹ * (e * p) := by group
    _ = p⁻¹ * (p * e) := by rw [h1]
    _ = e := by group

theorem hB_all (hB : ∀ w ∈ omega e, w ≠ e → w * e ∈ H₁) : ∀ w ∈ omega e, w * e ∈ H₁ := by
  intro w hw
  by_cases hwe : w = e
  · rw [hwe, hS.e_mul_e]
    exact H₁.one_mem
  · exact hB w hw hwe

theorem mul_mem_E₁ (hB : ∀ w ∈ omega e, w * e ∈ H₁) {w w' : Γ} (hw : w ∈ omega e)
    (hw' : w' ∈ omega e) : w * w' ∈ E ⊓ H₁ := by
  have hwE := hS.omega_subset_E hw
  have hw'E := hS.omega_subset_E hw'
  refine ⟨E.mul_mem hwE hw'E, ?_⟩
  have h1 : w * w' = (w * e) * (w' * e) := by
    calc w * w' = w * (e * e) * w' := by rw [hS.e_mul_e, mul_one]
      _ = w * e * (e * w') := by group
      _ = w * e * (w' * e) := by rw [hS.comm_of_mem_E hS.mem hw'E]
  rw [h1]
  exact H₁.mul_mem (hB w hw) (hB w' hw')

theorem exists_mem_omega_ne : ∃ w ∈ omega e, w ≠ e := by
  have h : (omega e \ {e}).ncard ≠ 0 := by
    rw [hS.ncard_X]
    norm_num
  obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero h
  exact ⟨w, hw.1, hw.2⟩

section Finite

variable [Finite Γ]

theorem eps_dichotomy :
    (∀ w ∈ omega e, w ≠ e → w ∈ H₁) ∨ (∀ w ∈ omega e, w ≠ e → w * e ∈ H₁) := by
  obtain ⟨w₀, hw₀, hne₀⟩ := hS.exists_mem_omega_ne
  rcases hS.mem_H₁_or_mul_mem_H₁ (hS.omega_subset_E hw₀) with h | h
  · left
    intro w hw hne
    obtain ⟨p, hp, rfl⟩ := hS.transitive hw₀ hw hne₀ hne
    exact H₁.mul_mem (H₁.mul_mem hp h) (H₁.inv_mem hp)
  · right
    intro w hw hne
    obtain ⟨p, hp, rfl⟩ := hS.transitive hw₀ hw hne₀ hne
    have hpe := hS.inv_mul_e_mul hp
    have h1 : p * w₀ * p⁻¹ * e = p * (w₀ * e) * p⁻¹ := by
      calc p * w₀ * p⁻¹ * e = p * w₀ * (p⁻¹ * e * p) * p⁻¹ := by group
        _ = p * (w₀ * e) * p⁻¹ := by rw [hpe]; group
    rw [h1]
    exact H₁.mul_mem (H₁.mul_mem hp h) (H₁.inv_mem hp)

theorem not_forall_mem_H₁ : ¬ ∀ w ∈ omega e, w ≠ e → w ∈ H₁ := by
  intro hA
  have hind : ∀ w ∈ omega e, w ∉ Subgroup.closure (omega e \ {w}) := by
    intro w hw hwc
    obtain ⟨γ, rfl⟩ := hw
    have hφ : ∀ y : Γ, (MulAut.conj γ⁻¹).toMonoidHom y = γ⁻¹ * y * γ := fun y => by
      simp
    have hle : Subgroup.closure (omega e \ {γ * e * γ⁻¹}) ≤
        H₁.comap (MulAut.conj γ⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, mem_comap, hφ]
      apply hA
      · simpa using conj_mem_omega hy.1 γ⁻¹
      · intro hcon
        apply hy.2
        rw [Set.mem_singleton_iff]
        calc y = γ * (γ⁻¹ * y * γ) * γ⁻¹ := by group
          _ = γ * e * γ⁻¹ := by rw [hcon]
    have hmem := hle hwc
    rw [mem_comap, hφ] at hmem
    have he : γ⁻¹ * (γ * e * γ⁻¹) * γ = e := by group
    rw [he] at hmem
    exact hS.e_not_mem_H₁ hmem
  have hfin : (omega e).Finite := Set.toFinite _
  have hcard := pow_card_le_card_closure hind hfin.toFinset (by simp)
  rw [← Set.ncard_eq_toFinset_card (omega e) hfin, hS.ncard_omega] at hcard
  have hle : Nat.card (Subgroup.closure ((hfin.toFinset : Finset Γ) : Set Γ)) ≤ Nat.card E := by
    apply Subgroup.card_le_of_le
    rw [Subgroup.closure_le]
    intro x hx
    exact hS.omega_subset_E (by simpa using hx)
  rw [hS.card] at hle
  have h2412 := hcard.trans hle
  norm_num at h2412

theorem E₁_normal (hB : ∀ w ∈ omega e, w ≠ e → w * e ∈ H₁) : (E ⊓ H₁).Normal := by
  have hB' := hS.hB_all hB
  have hS₂ : evenProducts e ⊆ ((E ⊓ H₁ : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨w, hw, w', hw', rfl⟩
    exact hS.mul_mem_E₁ hB' hw hw'
  have hcs : Group.conjugatesOfSet (evenProducts e) ⊆ evenProducts e := by
    intro x hx
    obtain ⟨a, ⟨w, hw, w', hw', rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    exact ⟨c * w * c⁻¹, conj_mem_omega hw c, c * w' * c⁻¹, conj_mem_omega hw' c, by group⟩
  have hP : Subgroup.normalClosure (evenProducts e) ≤ E ⊓ H₁ := by
    show Subgroup.closure (Group.conjugatesOfSet (evenProducts e)) ≤ E ⊓ H₁
    rw [Subgroup.closure_le]
    exact hcs.trans hS₂
  obtain ⟨g, hgH, hg23, hg1⟩ := hS.exists_g
  have hP1 : Subgroup.normalClosure (evenProducts e) ≠ ⊥ := by
    obtain ⟨w, hw, hwe⟩ := hS.exists_mem_omega_ne
    have hws : w * e ∈ evenProducts e := ⟨w, hw, e, e_mem_omega e, rfl⟩
    have hmem : w * e ∈ Subgroup.normalClosure (evenProducts e) :=
      Subgroup.subset_normalClosure hws
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hwe
    rw [eq_inv_of_mul_eq_one_left hmem]
    exact inv_eq_of_mul_eq_one_right hS.e_mul_e
  have heq : Subgroup.normalClosure (evenProducts e) = E ⊓ H₁ :=
    hS.eq_E₁_of_invariant hgH hg23 hg1 hP
      (fun x hx => (inferInstance : (Subgroup.normalClosure (evenProducts e)).Normal).conj_mem
        x hx g) hP1
  rw [← heq]
  infer_instance

theorem exists_index_two [E.Normal] (hmult : Nat.card (hopfMultiplier (Γ ⧸ E)) = 1) :
    ∃ N₀ : Subgroup Γ, N₀.Normal ∧ N₀.index = 2 ∧ e ∉ N₀ := by
  have hB : ∀ w ∈ omega e, w ≠ e → w * e ∈ H₁ := by
    rcases hS.eps_dichotomy with hA | hB
    · exact absurd hA hS.not_forall_mem_H₁
    · exact hB
  have hB' := hS.hB_all hB
  have hE₁ : (E ⊓ H₁).Normal := hS.E₁_normal hB
  have hperf : Group.IsPerfect (Γ ⧸ E) :=
    isPerfect_of_isSimpleGroup_of_card_not_prime hS.isSimpleGroup_quot (by
      rw [hS.card_quot]
      intro hp
      have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
      omega)
  obtain ⟨ρ, hρmk⟩ : ∃ ρ : Γ ⧸ (E ⊓ H₁) →* Γ ⧸ E,
      ∀ x : Γ, ρ (QuotientGroup.mk x) = QuotientGroup.mk x :=
    ⟨QuotientGroup.map (E ⊓ H₁) E (MonoidHom.id Γ) (fun x hx => hx.1), fun x => rfl⟩
  have hρs : Function.Surjective ρ := by
    intro m
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
    exact ⟨QuotientGroup.mk x, hρmk x⟩
  have hez : ∀ δ : Γ, (QuotientGroup.mk (δ * e * δ⁻¹) : Γ ⧸ (E ⊓ H₁)) = QuotientGroup.mk e := by
    intro δ
    rw [eq_comm, QuotientGroup.eq]
    have hw : δ * e * δ⁻¹ ∈ omega e := ⟨δ, rfl⟩
    have hwE := hS.omega_subset_E hw
    have h1 : e⁻¹ * (δ * e * δ⁻¹) = (δ * e * δ⁻¹) * e := by
      rw [inv_eq_of_mul_eq_one_right hS.e_mul_e]
      exact hS.comm_of_mem_E hS.mem hwE
    rw [h1]
    exact ⟨E.mul_mem hwE hS.mem, hB' _ hw⟩
  have hecent : (QuotientGroup.mk e : Γ ⧸ (E ⊓ H₁)) ∈ center (Γ ⧸ (E ⊓ H₁)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
    calc (QuotientGroup.mk δ : Γ ⧸ (E ⊓ H₁)) * QuotientGroup.mk e
        = QuotientGroup.mk (δ * e) := (QuotientGroup.mk_mul _ _ _).symm
      _ = QuotientGroup.mk (δ * e * δ⁻¹ * δ) := by rw [inv_mul_cancel_right]
      _ = QuotientGroup.mk (δ * e * δ⁻¹) * QuotientGroup.mk δ := QuotientGroup.mk_mul _ _ _
      _ = QuotientGroup.mk e * QuotientGroup.mk δ := by rw [hez δ]
  have hcent : ρ.ker ≤ center (Γ ⧸ (E ⊓ H₁)) := by
    intro x hx
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    have hγ1 := MonoidHom.mem_ker.1 hx
    rw [hρmk] at hγ1
    have hγE : γ ∈ E := (QuotientGroup.eq_one_iff γ).1 hγ1
    rcases hS.mem_H₁_or_mul_mem_H₁ hγE with h | h
    · have h1 : (QuotientGroup.mk γ : Γ ⧸ (E ⊓ H₁)) = 1 :=
        (QuotientGroup.eq_one_iff γ).2 ⟨hγE, h⟩
      rw [h1]
      exact Subgroup.one_mem _
    · have h1 : (QuotientGroup.mk (γ * e) : Γ ⧸ (E ⊓ H₁)) = 1 :=
        (QuotientGroup.eq_one_iff _).2 ⟨E.mul_mem hγE hS.mem, h⟩
      rw [QuotientGroup.mk_mul] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ hecent
  obtain ⟨-, hbot, hcardJ⟩ := commutator_cover ρ hρs hcent hperf hmult
  have hQcard : Nat.card (Γ ⧸ (E ⊓ H₁)) = 2 * 244823040 := by
    have h := Subgroup.index_mul_card (H := E ⊓ H₁)
    rw [Subgroup.index_eq_card, hS.card_E₁, hS.card_Γ] at h
    have h4 : 0 < 2 ^ 11 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [h]; ring)
  refine ⟨(commutator (Γ ⧸ (E ⊓ H₁))).comap (QuotientGroup.mk' (E ⊓ H₁)),
    Subgroup.Normal.comap (inferInstance : (commutator (Γ ⧸ (E ⊓ H₁))).Normal) _, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have h1 := Subgroup.index_mul_card (H := commutator (Γ ⧸ (E ⊓ H₁)))
    rw [hcardJ, hQcard, hS.card_quot] at h1
    omega
  · intro he
    have h1 : (QuotientGroup.mk e : Γ ⧸ (E ⊓ H₁)) ∈ commutator (Γ ⧸ (E ⊓ H₁)) := he
    have h2 : (QuotientGroup.mk e : Γ ⧸ (E ⊓ H₁)) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hρmk]
      exact (QuotientGroup.eq_one_iff e).2 hS.mem
    have h3 : (QuotientGroup.mk e : Γ ⧸ (E ⊓ H₁)) ∈
        commutator (Γ ⧸ (E ⊓ H₁)) ⊓ ρ.ker := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact hS.e_not_mem_H₁ ((QuotientGroup.eq_one_iff e).1 h3).2

end Finite

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
