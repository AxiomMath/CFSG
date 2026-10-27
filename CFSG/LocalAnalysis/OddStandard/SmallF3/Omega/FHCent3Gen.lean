module

public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def FHOdd3Inner (X : Type) [Group X] : Prop :=
  ∀ σ : MulAut X, σ ^ 3 = 1 → ∃ s : X, σ = MulAut.conj s

theorem fh_mem_of_odd3_inner {A : Type} [Group A] (H : Subgroup A) [H.Normal]
    (hC : centralizer (H : Set A) = ⊥) (hin : FHOdd3Inner ↥H) {g : A} (hg : g ^ 3 = 1) :
    g ∈ H := by
  set σ : MulAut ↥H := MulAut.conjNormal g with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, hg, map_one]
  obtain ⟨s, hs⟩ := hin σ hσ3
  have hval : ∀ x : ↥H, g * (x : A) * g⁻¹ = (s : A) * (x : A) * (s : A)⁻¹ := by
    intro x
    have hx := congrArg (fun f : MulAut ↥H => f x) hs
    have hxval := congrArg Subtype.val hx
    rw [hσ] at hxval
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using hxval
  let t : A := (s : A)⁻¹ * g
  have htcent : t ∈ centralizer (H : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := hval ⟨x, hx⟩
    have h1 : (s : A)⁻¹ * g * x = x * ((s : A)⁻¹ * g) := by
      calc (s : A)⁻¹ * g * x
          = (s : A)⁻¹ * (g * x * g⁻¹) * g := by group
        _ = (s : A)⁻¹ * (s * x * (s : A)⁻¹) * g := by rw [hx']
        _ = x * ((s : A)⁻¹ * g) := by group
    dsimp only [t]
    exact h1.symm
  have ht1 : t = 1 := by
    have := htcent
    rw [hC] at this
    simpa using this
  have hsg : g = (s : A) := by
    have h1 : (s : A)⁻¹ * g = 1 := ht1
    calc g = (s : A) * ((s : A)⁻¹ * g) := by group
      _ = s := by rw [h1]; group
  rw [hsg]
  exact s.2

theorem fh_cent3_of_f1 {A : Type} [Group A] (H : Subgroup A) {a g : A}
    (hF1 : CFSG.inSubgroup (CFSG.pCore 3) (H ⊓ centralizer ({a} : Set A)) = ⊥)
    (hgH : g ∈ H) (hga : g * a = a * g) (hg3 : orderOf g = 3) :
    ¬ ∀ c ∈ H ⊓ centralizer ({a} : Set A), Odd (orderOf c) → g * c = c * g := by
  intro hall
  set D : Subgroup A := H ⊓ centralizer ({a} : Set A) with hD
  have hgD : g ∈ D := ⟨hgH, Subgroup.mem_centralizer_singleton_iff.2 hga⟩
  set g' : ↥D := ⟨g, hgD⟩ with hg'
  have hg3A : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hg'3 : g' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hg'] using hg3A
  have horder_g' : orderOf g' = 3 := by
    rw [← Subgroup.orderOf_coe g']
    simpa [hg'] using hg3
  have horder_conj : ∀ d o : ↥D, orderOf (d * o * d⁻¹) = orderOf o := by
    intro d o
    rw [← MulAut.conj_apply d o]
    exact orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective o
  have hallD : ∀ c : ↥D, Odd (orderOf c) → g' * c = c * g' := by
    intro c hc
    apply Subtype.ext
    have hodd : Odd (orderOf (c : A)) := by rw [Subgroup.orderOf_coe]; exact hc
    have hcD : (c : A) ∈ H ⊓ centralizer ({a} : Set A) := c.2
    have h1 := hall (c : A) hcD hodd
    simpa [hg'] using h1
  set O : Set ↥D := {c : ↥D | Odd (orderOf c)} with hO
  set S : Set ↥D := Group.conjugatesOfSet ({g'} : Set ↥D) with hS
  set T : Subgroup ↥D := Subgroup.normalClosure ({g'} : Set ↥D) with hT
  have hTclosure : T = Subgroup.closure S := by
    rw [hT, hS]
    rfl
  have hgen_mem : ∀ x ∈ S, ∃ c : ↥D, c * g' * c⁻¹ = x := by
    intro x hx
    rw [hS, Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨b, hb, hbc⟩ := hx
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [isConj_iff] at hbc
    obtain ⟨c, hc⟩ := hbc
    exact ⟨c, hc⟩
  have hgenO : ∀ x ∈ S, x ∈ O := by
    intro x hx
    obtain ⟨c, rfl⟩ := hgen_mem x hx
    show Odd (orderOf (c * g' * c⁻¹))
    rw [horder_conj c g', horder_g']
    exact ⟨1, by norm_num⟩
  have hgen3 : ∀ x ∈ S, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨c, rfl⟩ := hgen_mem x hx
    rw [← MulAut.conj_apply c g', ← map_pow, hg'3, map_one]
  have hgenCent : ∀ x ∈ S, x ∈ (Subgroup.centralizer O : Set ↥D) := by
    intro x hx
    obtain ⟨c, rfl⟩ := hgen_mem x hx
    change c * g' * c⁻¹ ∈ Subgroup.centralizer O
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hord : orderOf (c⁻¹ * o * c) = orderOf o := by
      have h := horder_conj c⁻¹ o
      simpa using h
    have ho' : c⁻¹ * o * c ∈ O := by
      show Odd (orderOf (c⁻¹ * o * c))
      rw [hord]
      exact ho
    have hcomm := hallD (c⁻¹ * o * c) ho'
    have key : c⁻¹ * (o * (c * g' * c⁻¹)) * c = c⁻¹ * ((c * g' * c⁻¹) * o) * c := by
      calc c⁻¹ * (o * (c * g' * c⁻¹)) * c
          = (c⁻¹ * o * c) * g' := by group
        _ = g' * (c⁻¹ * o * c) := hcomm.symm
        _ = c⁻¹ * ((c * g' * c⁻¹) * o) * c := by group
    exact mul_left_cancel (mul_right_cancel key)
  have hTcent : T ≤ Subgroup.centralizer O := by
    rw [hTclosure]
    exact (Subgroup.closure_le (Subgroup.centralizer O)).mpr hgenCent
  have hTclosureO : T ≤ Subgroup.closure O := by
    rw [hTclosure]
    exact Subgroup.closure_mono hgenO
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, y * x = x * y := by
    intro x hx y hy
    have hxcent : x ∈ Subgroup.centralizer (Subgroup.closure O) := by
      rw [Subgroup.centralizer_closure]
      exact hTcent hx
    exact (Subgroup.mem_centralizer_iff.1 hxcent) y (hTclosureO hy)
  have hcube : ∀ x ∈ T, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ Subgroup.closure S := by
      rwa [hTclosure] at hx
    refine Subgroup.closure_induction (k := S) (p := fun x _ => x ^ 3 = 1)
      (fun y hy => hgen3 y hy) (by simp) ?_ ?_ hx'
    · intro y z hy hz ihy ihz
      have hcomm : Commute y z :=
        (hcommT y (hTclosure.symm ▸ hy) z (hTclosure.symm ▸ hz)).symm
      rw [hcomm.mul_pow 3, ihy, ihz, mul_one]
    · intro y hy ihy
      simp [ihy]
  have hTnormal : T.Normal := by
    rw [hT]
    infer_instance
  have hT3 : IsPGroup 3 T := fun u => ⟨1, by
    apply Subtype.ext
    simpa using hcube (u : ↥D) u.2⟩
  have hTleCore : T ≤ CFSG.pCore 3 ↥D :=
    le_sSup (s := {K : Subgroup ↥D | K.Normal ∧ IsPGroup 3 K}) ⟨hTnormal, hT3⟩
  have hg'T : g' ∈ T := Subgroup.subset_normalClosure (Set.mem_singleton g')
  have hmap : g ∈ (CFSG.pCore 3 ↥D).map D.subtype := ⟨g', hTleCore hg'T, rfl⟩
  have hF1' : (CFSG.pCore 3 ↥D).map D.subtype = ⊥ := by
    simpa [CFSG.inSubgroup] using hF1
  rw [hF1'] at hmap
  have hgmem1 : g = 1 := Subgroup.mem_bot.mp hmap
  have hg'1 : g' = 1 := Subtype.ext (by simpa [hg'] using hgmem1)
  have hg1 : g = 1 := by
    have h := congrArg Subtype.val hg'1
    simpa [hg'] using h
  rw [hg1, orderOf_one] at hg3
  exact absurd hg3 (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
