module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInvCent
public import Certificates.Certificate27121
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzNormal

public noncomputable section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.EvenSporadicStandard.RuStd
open CFSG.Sporadic.Th (Rep)

section Elements

theorem borelChecks :
    kG x0Word * kG x0Word = 1 ∧ kG x0Word ≠ 1 ∧
    (∀ w ∈ borelGens, ∀ r ∈ K0, r * kG x0Word = kG x0Word * r →
      r * ((kG w)⁻¹ * kG x0Word * kG w) = ((kG w)⁻¹ * kG x0Word * kG w) * r) ∧
    (∀ w ∈ hBWords, kG w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) ∧
    (∀ p : Fin 4060, (∀ w ∈ hBWords, kG w p = p) → p.val ∈ [0, 1, 3645, 3692]) ∧
    kG k1Word ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ ∧
    (∀ g ∈ ruP, g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ → g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ →
      g * kG n1Word = kG n1Word * g → g * kG n2Word = kG n2Word * g → g = 1) :=
  Certificates.certificate27121

@[expose] def x0G : Equiv.Perm (Fin 4060) := kG x0Word

theorem x0G_mem : x0G ∈ K0 := kG_mem _

theorem x0G_sq : x0G * x0G = 1 := borelChecks.1

theorem x0G_ne_one : x0G ≠ 1 := borelChecks.2.1

theorem orderOf_x0G : orderOf x0G = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact x0G_sq) x0G_ne_one

@[expose] def R0 : Subgroup (Equiv.Perm (Fin 4060)) :=
  K0 ⊓ Subgroup.centralizer ({x0G} : Set (Equiv.Perm (Fin 4060)))

theorem card_R0 : Nat.card R0 = 64 := card_centK0 x0G_mem orderOf_x0G

end Elements

section Normalizer

@[expose] def yG (w : String) : Equiv.Perm (Fin 4060) := (kG w)⁻¹ * x0G * kG w

theorem comm_yG {w : String} (hw : w ∈ borelGens) :
    ∀ l ∈ K0, l * x0G = x0G * l → l * yG w = yG w * l :=
  borelChecks.2.2.1 w hw

theorem borel_normalizes {w : String} (hw : w ∈ borelGens) :
    ∀ r ∈ R0, kG w * r * (kG w)⁻¹ ∈ R0 := by
  intro r hr
  have hrK : r ∈ K0 := hr.1
  have hrc : r * x0G = x0G * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hY := comm_yG hw r hrK hrc
  refine ⟨K0.mul_mem (K0.mul_mem (kG_mem w) hrK) (K0.inv_mem (kG_mem w)),
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hY' : r * ((kG w)⁻¹ * x0G * kG w) = ((kG w)⁻¹ * x0G * kG w) * r := hY
  calc kG w * r * (kG w)⁻¹ * x0G
      = kG w * (r * ((kG w)⁻¹ * x0G * kG w)) * (kG w)⁻¹ := by group
    _ = kG w * (((kG w)⁻¹ * x0G * kG w) * r) * (kG w)⁻¹ := by rw [hY']
    _ = x0G * (kG w * r * (kG w)⁻¹) := by group

theorem kG_mem_normalizer {w : String} (hw : w ∈ borelGens) :
    kG w ∈ Subgroup.normalizer (R0 : Set (Equiv.Perm (Fin 4060))) := by
  have : Finite R0 := Nat.finite_of_card_ne_zero (by rw [card_R0]; norm_num)
  exact mem_normalizer_of_conj_mem (borel_normalizes hw)

@[expose] def N' : Subgroup (Equiv.Perm (Fin 4060)) :=
  closure {g | ∃ w ∈ borelGens, g = kG w}

theorem kG_mem_N' {w : String} (hw : w ∈ borelGens) : kG w ∈ N' := subset_closure ⟨w, hw, rfl⟩

theorem N'_le_normalizer : N' ≤ Subgroup.normalizer (R0 : Set (Equiv.Perm (Fin 4060))) := by
  rw [N', closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact kG_mem_normalizer hw

end Normalizer

section Omega

@[expose] def DN : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruP ⊓ Subgroup.centralizer (N' : Set (Equiv.Perm (Fin 4060)))

theorem mem_DN {g : Equiv.Perm (Fin 4060)} :
    g ∈ DN ↔ g ∈ ruP ∧ ∀ k ∈ N', k * g = g * k := by
  rw [DN, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem kG_h_zero {w : String} (hw : w ∈ hBWords) : kG w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  borelChecks.2.2.2.1 w hw

theorem kG_k1_zero : kG k1Word ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := borelChecks.2.2.2.2.2.1

theorem hBWords_sub : ∀ w ∈ hBWords, w ∈ borelGens := by
  intro w hw
  simp only [borelGens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inl (Or.inr hw)

theorem k1_mem : k1Word ∈ borelGens := by simp [borelGens]

theorem n1_mem : n1Word ∈ borelGens := by simp [borelGens]

theorem n2_mem : n2Word ∈ borelGens := by simp [borelGens]

theorem DN_image_mem_fix {g : Equiv.Perm (Fin 4060)} (hg : g ∈ DN) :
    (g ⟨0, by norm_num⟩).val ∈ [0, 1, 3645, 3692] := by
  obtain ⟨-, hcomm⟩ := mem_DN.1 hg
  refine borelChecks.2.2.2.2.1 _ fun w hw => ?_
  have hk := kG_mem_N' (hBWords_sub w hw)
  calc kG w (g ⟨0, by norm_num⟩) = (kG w * g) ⟨0, by norm_num⟩ := rfl
    _ = (g * kG w) ⟨0, by norm_num⟩ := by rw [hcomm (kG w) hk]
    _ = g (kG w ⟨0, by norm_num⟩) := rfl
    _ = g ⟨0, by norm_num⟩ := by rw [kG_h_zero hw]

theorem eq_one_of_fix01_comm {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (h0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) (h1 : g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩)
    (c1 : g * kG n1Word = kG n1Word * g) (c2 : g * kG n2Word = kG n2Word * g) : g = 1 :=
  borelChecks.2.2.2.2.2.2 g hg h0 h1 c1 c2

theorem fixes_of_comm {k g : Equiv.Perm (Fin 4060)} (hcomm : k * g = g * k) {a b : Fin 4060}
    (hk : k a = b) (hg : g a = a) : g b = b := by
  calc g b = g (k a) := by rw [hk]
    _ = (g * k) a := rfl
    _ = (k * g) a := by rw [hcomm]
    _ = k (g a) := rfl
    _ = b := by rw [hg, hk]

theorem card_DN_le : Nat.card DN ≤ 4 := by
  classical
  let T : Finset (Fin 4060) :=
    {⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨3645, by norm_num⟩, ⟨3692, by norm_num⟩}
  have hT : T.card = 4 := by decide
  have hmapsto : ∀ g : DN, (g : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ ∈ T := by
    intro g
    have h := DN_image_mem_fix g.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [T, Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  let f : DN → T := fun g => ⟨(g : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩, hmapsto g⟩
  have hinj : Function.Injective f := by
    intro g₁ g₂ h12
    have h0 : (g₁ : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ =
        (g₂ : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ := congrArg Subtype.val h12
    set g : Equiv.Perm (Fin 4060) := (g₁ : Equiv.Perm (Fin 4060))⁻¹ * g₂ with hg
    have hgD : g ∈ DN := DN.mul_mem (DN.inv_mem g₁.2) g₂.2
    have hg0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
      rw [hg, Equiv.Perm.mul_apply, ← h0]
      exact Equiv.symm_apply_apply _ _
    obtain ⟨hgP, hcomm⟩ := mem_DN.1 hgD
    have hg1 : g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
      fixes_of_comm (hcomm _ (kG_mem_N' k1_mem)) kG_k1_zero hg0
    have hg1' : g = 1 :=
      eq_one_of_fix01_comm hgP hg0 hg1 (hcomm _ (kG_mem_N' n1_mem)).symm
        (hcomm _ (kG_mem_N' n2_mem)).symm
    have : (g₁ : Equiv.Perm (Fin 4060)) = g₂ := by
      have := congrArg (fun y => (g₁ : Equiv.Perm (Fin 4060)) * y) hg1'
      simpa [hg] using this.symm
    exact Subtype.ext this
  calc Nat.card DN ≤ Nat.card T := Nat.card_le_card_of_injective f hinj
    _ = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT]

end Omega

end CFSG.EvenSporadicStandard.Induction.RuSz
