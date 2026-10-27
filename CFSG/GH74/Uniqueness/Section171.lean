module

public import CFSG.GH74.Uniqueness.Section171Invol
public import CFSG.GH74.Uniqueness.Section17Count
public import CFSG.GH74.Uniqueness.Section12BenderDict

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

@[expose] def Conf16.uClass (c : Conf16 Z M) : Set X := {v | IsConj c.u v}

theorem ZDSetup.mul_inv_mem_D_of_conj_eq (S : ZDSetup X Z M) (c : Conf16 Z M) {v : X}
    (hv2 : v * v = 1) (hv : conjugate M v = conjugate M c.t) : v * c.t⁻¹ ∈ c.D := by
  have ht2 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hβ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : conjugate M (v * c.t⁻¹) = M := by
      rw [← conjugate_conjugate, hv, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp h1
  · have h1 : conjugate (conjugate M c.t) v = M := by
      rw [← hv, conjugate_conjugate, hv2, conjugate_one]
    have h2 : conjugate (conjugate M c.t) (v * c.t⁻¹) = conjugate M c.t := by
      rw [← conjugate_conjugate, h1, hti]
    exact (S.prodDisc.conjugate_eq_iff_mem hβ).mp h2

theorem ZDSetup.ncard_pi_mul (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    {v | v ∈ c.uClass ∧ conjugate M v = conjugate M c.t}.ncard *
        Nat.card ↥(c.D ⊓ centralizer ({c.t * c.u} : Set X)) = Nat.card ↥c.D := by
  have hset : {v | v ∈ c.uClass ∧ conjugate M v = conjugate M c.t} =
      {y | ∃ a ∈ c.D, a * (c.t * c.u) * a⁻¹ = y} := by
    ext v
    constructor
    · rintro ⟨hvU, hv⟩
      have hvU' : IsConj c.u v := hvU
      obtain ⟨g, hg⟩ := isConj_iff.mp hvU'
      have hv2 : orderOf v = 2 := by rw [← hg]; exact orderOf_conj_eq c.hu2 g
      have hvv : v * v = 1 := mul_self_of_orderOf_eq_two hv2
      obtain ⟨d, hd, hvd⟩ := S.exists_conj_of_involution_dt h166 c hv2
        (S.mul_inv_mem_D_of_conj_eq c hvv hv) hvU'
      exact ⟨d⁻¹, c.D.inv_mem hd, by rw [hvd, inv_inv]⟩
    · rintro ⟨a, ha, rfl⟩
      have haM : a ∈ M := (Subgroup.mem_inf.mp ha).1
      have haβ : a ∈ conjugate M c.t := (Subgroup.mem_inf.mp ha).2
      have hβ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
      have huβ : c.u ∈ conjugate M c.t := (Subgroup.mem_inf.mp c.hu).2
      refine ⟨?_, ?_⟩
      · exact (S.isConj_u_tu h166 c hB).trans (isConj_iff.mpr ⟨a, rfl⟩)
      · have h1 : conjugate M a = M := (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr haM
        have h2 : conjugate (conjugate M c.t) c.u = conjugate M c.t :=
          (S.prodDisc.conjugate_eq_iff_mem hβ).mpr huβ
        have h3 : conjugate (conjugate M c.t) a⁻¹ = conjugate M c.t :=
          (S.prodDisc.conjugate_eq_iff_mem hβ).mpr (Subgroup.inv_mem _ haβ)
        calc conjugate M (a * (c.t * c.u) * a⁻¹)
            = conjugate (conjugate (conjugate (conjugate M a) c.t) c.u) a⁻¹ := by
              simp only [conjugate_conjugate, mul_assoc]
          _ = conjugate M c.t := by rw [h1, h2, h3]
  rw [hset]
  exact ncard_conjOrbit_mul_card_cent c.D (c.t * c.u)

theorem ZDSetup.ncard_pi'_mul (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M) :
    {v | v ∈ c.uClass ∧ conjugate M v = M ∧
        conjugate (conjugate M c.t) v = conjugate M c.t}.ncard *
        Nat.card ↥(c.D ⊓ centralizer ({c.u} : Set X)) = Nat.card ↥c.D := by
  have hβ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  have hset : {v | v ∈ c.uClass ∧ conjugate M v = M ∧
      conjugate (conjugate M c.t) v = conjugate M c.t} =
      {y | ∃ a ∈ c.D, a * c.u * a⁻¹ = y} := by
    ext v
    constructor
    · rintro ⟨hvU, hv1, hv2⟩
      have hvU' : IsConj c.u v := hvU
      obtain ⟨g, hg⟩ := isConj_iff.mp hvU'
      have hv2' : orderOf v = 2 := by rw [← hg]; exact orderOf_conj_eq c.hu2 g
      have hvD : v ∈ c.D := Subgroup.mem_inf.mpr
        ⟨(S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp hv1,
          (S.prodDisc.conjugate_eq_iff_mem hβ).mp hv2⟩
      obtain ⟨-, d, hd, hvd⟩ := S.exists_conj_of_involution_dGrp h166 c hvD hv2'
      exact ⟨d⁻¹, c.D.inv_mem hd, by rw [hvd, inv_inv]⟩
    · rintro ⟨a, ha, rfl⟩
      have hx : a * c.u * a⁻¹ ∈ c.D :=
        c.D.mul_mem (c.D.mul_mem ha c.hu) (c.D.inv_mem ha)
      refine ⟨isConj_iff.mpr ⟨a, rfl⟩, ?_, ?_⟩
      · exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (Subgroup.mem_inf.mp hx).1
      · exact (S.prodDisc.conjugate_eq_iff_mem hβ).mpr (Subgroup.mem_inf.mp hx).2
  rw [hset]
  exact ncard_conjOrbit_mul_card_cent c.D c.u

theorem ncard_pairs_moved {u : X} (hΩsub : omegaFix M ({u} : Set X) ⊆ omega M) :
    {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
        conjugate p.1 u = p.2}.ncard =
      (omega M).ncard - (omegaFix M ({u} : Set X)).ncard := by
  have himg : {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
      conjugate p.1 u = p.2} =
      (fun δ => (δ, conjugate δ u)) '' (omega M \ omegaFix M ({u} : Set X)) := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨p.1, ⟨h1, fun hfix => h3 ?_⟩, Prod.ext rfl h4⟩
      rw [← h4]
      exact (hfix.2 u (Set.mem_singleton u)).symm
    · rintro ⟨δ, ⟨hδ, hδfix⟩, rfl⟩
      refine ⟨hδ, conjugate_mem_omega hδ u, fun h => hδfix ⟨hδ, fun g hg => ?_⟩, rfl⟩
      rw [Set.mem_singleton_iff.mp hg]
      exact h.symm
  rw [himg, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h),
    Set.ncard_sdiff hΩsub (Set.toFinite _)]

theorem ncard_pairs_fixed {u : X} :
    {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
        (conjugate p.1 u = p.1 ∧ conjugate p.2 u = p.2)}.ncard =
      (omegaFix M ({u} : Set X)).ncard * ((omegaFix M ({u} : Set X)).ncard - 1) := by
  classical
  have hfin : (omegaFix M ({u} : Set X)).Finite := Set.toFinite _
  have himg : {p : Subgroup X × Subgroup X | p.1 ∈ omega M ∧ p.2 ∈ omega M ∧ p.1 ≠ p.2 ∧
      (conjugate p.1 u = p.1 ∧ conjugate p.2 u = p.2)} =
      ((hfin.toFinset.offDiag : Finset (Subgroup X × Subgroup X)) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨h1, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h4⟩,
        ⟨h2, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h5⟩, h3⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h3⟩
      exact ⟨h1, h2, h3, h4 u (Set.mem_singleton u), h5 u (Set.mem_singleton u)⟩
  rw [himg, Set.ncard_coe_finset, Finset.offDiag_card, ← Set.ncard_eq_toFinset_card _ hfin,
    Nat.mul_sub_one]

theorem ZDSetup.lemma171
    (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) : Lemma171Stmt Z M := by
  intro c n i e hB
  classical
  have hdt : DoublyTransitive M := S.theorem4.1
  have hαΩ : M ∈ omega M := self_mem_omega M
  have hβΩ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  have hαβ : M ≠ conjugate M c.t := by
    intro h
    apply c.htM
    have := conjugate_eq_iff_mem_normalizer.mp h.symm
    rwa [S.prodDisc.normalizer_eq_self] at this
  have huM : c.u ∈ M := (Subgroup.mem_inf.mp c.hu).1
  have hΩu : (omegaFix M ({c.u} : Set X)).ncard = (2 ^ n) ^ i + 1 :=
    S.ncard_omegaFix_of_benderSub c.hu2 huM hB
  have hΩsub : omegaFix M ({c.u} : Set X) ⊆ omega M := fun β hβ => hβ.1
  have hrq : (2 ^ n) ^ i + 1 ≤ (omega M).ncard :=
    hΩu ▸ Set.ncard_le_ncard hΩsub (Set.toFinite _)
  refine ⟨hrq, ?_⟩
  have hU : ∀ v ∈ c.uClass, ∀ g : X, g⁻¹ * v * g ∈ c.uClass := by
    intro v hv g
    exact (hv : IsConj c.u v).trans (isConj_iff.mpr ⟨g⁻¹, by simp⟩)
  have huU : c.u ∈ c.uClass := IsConj.refl _
  have hUu : ∀ v ∈ c.uClass, ∃ g : X, v = g⁻¹ * c.u * g := by
    intro v hv
    obtain ⟨g, hg⟩ := isConj_iff.mp (hv : IsConj c.u v)
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  have hQ₁ : ∀ (v : X) (δ δ' : Subgroup X) (g : X),
      (conjugate (conjugate δ g) (g⁻¹ * v * g) = conjugate δ' g) ↔ conjugate δ v = δ' := by
    intro v δ δ' g
    have e : conjugate (conjugate δ g) (g⁻¹ * v * g) = conjugate (conjugate δ v) g := by
      rw [conjugate_conjugate, conjugate_conjugate]
      congr 1
      group
    rw [e]
    exact ⟨fun h => conjugate_injective g h, fun h => by rw [h]⟩
  have hQ₂ : ∀ (v : X) (δ δ' : Subgroup X) (g : X),
      (conjugate (conjugate δ g) (g⁻¹ * v * g) = conjugate δ g ∧
        conjugate (conjugate δ' g) (g⁻¹ * v * g) = conjugate δ' g) ↔
        (conjugate δ v = δ ∧ conjugate δ' v = δ') := by
    intro v δ δ' g
    have e : ∀ ε : Subgroup X, conjugate (conjugate ε g) (g⁻¹ * v * g) =
        conjugate (conjugate ε v) g := by
      intro ε
      rw [conjugate_conjugate, conjugate_conjugate]
      congr 1
      group
    rw [e, e]
    exact and_congr ⟨fun h => conjugate_injective g h, fun h => by rw [h]⟩
      ⟨fun h => conjugate_injective g h, fun h => by rw [h]⟩
  have hA := ncard_pairs_identity hdt c.uClass
    (fun v δ δ' => conjugate δ v = δ') (fun v δ δ' g => hQ₁ v δ δ' g) hU huU hUu hαΩ hβΩ hαβ
  have hB' := ncard_pairs_identity hdt c.uClass
    (fun v δ δ' => conjugate δ v = δ ∧ conjugate δ' v = δ') (fun v δ δ' g => hQ₂ v δ δ' g)
    hU huU hUu hαΩ hβΩ hαβ
  have hFA := ncard_pairs_moved (M := M) (u := c.u) hΩsub
  have hFB := ncard_pairs_fixed (M := M) (u := c.u)
  have hP := S.ncard_pi_mul h166 c hB
  have hP' := S.ncard_pi'_mul h166 c
  rw [hΩu] at hFA hFB
  rw [hFA] at hA
  rw [hFB] at hB'
  have ha : 0 < c.uClass.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨c.u, huU⟩
  apply Nat.eq_of_mul_eq_mul_left ha
  set r := (omega M).ncard with hr
  set q := (2 ^ n) ^ i with hq
  set a := c.uClass.ncard with ha'
  set p := {v | v ∈ c.uClass ∧ conjugate M v = conjugate M c.t}.ncard with hp
  set p' := {v | v ∈ c.uClass ∧ conjugate M v = M ∧
    conjugate (conjugate M c.t) v = conjugate M c.t}.ncard with hp'
  set x := Nat.card ↥(c.D ⊓ centralizer ({c.t * c.u} : Set X)) with hx
  set y := Nat.card ↥(c.D ⊓ centralizer ({c.u} : Set X)) with hy
  set d := Nat.card ↥c.D with hd
  calc a * ((r - (q + 1)) * x) = (a * (r - (q + 1))) * x := by ring
    _ = (r * (r - 1) * p) * x := by rw [hA]
    _ = r * (r - 1) * (p * x) := by ring
    _ = r * (r - 1) * d := by rw [hP]
    _ = r * (r - 1) * (p' * y) := by rw [hP']
    _ = (r * (r - 1) * p') * y := by ring
    _ = (a * ((q + 1) * (q + 1 - 1))) * y := by rw [hB']
    _ = a * (q * (q + 1) * y) := by
      rw [Nat.add_sub_cancel]
      ring

end CFSG.GH74.Uniqueness
