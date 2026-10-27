module

public import CFSG.LocalAnalysis.Asc75.Swap
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

section SubgroupOf

theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (K : Subgroup G) : IsElemAbelian p (E.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hE K

variable [Finite G]

theorem two_le_pRank_subgroupOf {X K : Subgroup G} (hXK : X ≤ K) (h : 2 ≤ CFSG.Open.pRank 2 X) :
    2 ≤ CFSG.Open.pRank 2 (X.subgroupOf K) := by
  obtain ⟨E, hEX, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two X
  have hEK : E ≤ K := hEX.trans hXK
  have hcard' : Nat.card (E.subgroupOf K) = 2 ^ CFSG.Open.pRank 2 X := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hle : E.subgroupOf K ≤ X.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hEX (Subgroup.mem_subgroupOf.1 hx))
  have := CFSG.SectionRank.le_pRank one_lt_two hle (isElemAbelian_subgroupOf hE K) hcard'
  omega

omit [Finite G] in
theorem coe_conj_inf_ne_bot {K : Subgroup G} {X Y : Subgroup G} (k : ↥K)
    (h : conjugate ((X ⊓ K).subgroupOf K) k ⊓ ((Y ⊓ K).subgroupOf K) ≠ ⊥) :
    conjugate X (k : G) ⊓ Y ≠ ⊥ := by
  intro hbot
  apply h
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have h1 := Subgroup.mem_inf.1 hy
  have hyX : k * y * k⁻¹ ∈ (X ⊓ K).subgroupOf K := mem_conjugate_iff.1 h1.1
  have hyX' : (k : G) * y * (k : G)⁻¹ ∈ X :=
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hyX)).1
  have hyY' : (y : G) ∈ Y := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1.2)).1
  have hm : (y : G) ∈ conjugate X (k : G) ⊓ Y := ⟨mem_conjugate_iff.2 hyX', hyY'⟩
  rw [hbot, Subgroup.mem_bot] at hm
  exact hm

omit [Finite G] in
theorem coe_mem_genSet {K : Subgroup G} {A₁ A₂ : Subgroup G} {k : ↥K}
    (hk : k ∈ genSet ((A₁ ⊓ K).subgroupOf K) ((A₂ ⊓ K).subgroupOf K)) :
    (k : G) ∈ genSet A₁ A₂ := by
  rcases hk with hk | hk | hk | hk
  · exact Or.inl (coe_conj_inf_ne_bot k hk)
  · exact Or.inr (Or.inl (coe_conj_inf_ne_bot k hk))
  · exact Or.inr (Or.inr (Or.inl (coe_conj_inf_ne_bot k hk)))
  · exact Or.inr (Or.inr (Or.inr (coe_conj_inf_ne_bot k hk)))

end SubgroupOf

section Restrict

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.closure_genSet_le (h : Hyp S A₁ A₂ H) (K : Subgroup G) :
    Subgroup.closure (genSet ((A₁ ⊓ K).subgroupOf K) ((A₂ ⊓ K).subgroupOf K)) ≤
      H.comap K.subtype := by
  refine (Subgroup.closure_le _).2 (fun k hk => ?_)
  have hkg := coe_mem_genSet hk
  have : (k : G) ∈ H := by
    rw [h.hdef]
    exact Subgroup.subset_closure hkg
  exact this

theorem Hyp.restrict (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥) (K : Subgroup G)
    (hsyl : ¬ 2 ∣ (S ⊓ K).relIndex K) (h₁ : 2 ≤ CFSG.Open.pRank 2 (A₁ ⊓ K))
    (h₂ : 2 ≤ CFSG.Open.pRank 2 (A₂ ⊓ K)) :
    Hyp ((S ⊓ K).subgroupOf K) ((A₁ ⊓ K).subgroupOf K) ((A₂ ⊓ K).subgroupOf K)
      (Subgroup.closure (genSet ((A₁ ⊓ K).subgroupOf K) ((A₂ ⊓ K).subgroupOf K))) where
  pgroup := (h.pgroup.to_le inf_le_left).of_equiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ K ≤ K)).symm
  odd_index := hsyl
  le₁ := fun x hx => by
    obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_subgroupOf.2 ⟨h.le₁ hxA, hxK⟩
  le₂ := fun x hx => by
    obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    exact Subgroup.mem_subgroupOf.2 ⟨h.le₂ hxA, hxK⟩
  comm := fun a ha b hb => by
    obtain ⟨haA, -⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)
    obtain ⟨hbA, -⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hb)
    exact Subtype.ext (h.comm a haA b hbA)
  rank₁ := by
    have := two_le_pRank_subgroupOf (inf_le_right : A₁ ⊓ K ≤ K) h₁
    omega
  rank₂ := by
    have := two_le_pRank_subgroupOf (inf_le_right : A₂ ⊓ K ≤ K) h₂
    omega
  hdef := rfl
  closed_H := by
    intro a ha k hk hkS
    have hkH : (k : G) ∈ H := h.closure_genSet_le K hk
    have haU : (a : G) ∈ uSet A₁ A₂ := by
      rcases ha with ha | ha
      · exact Or.inl (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
      · exact Or.inr (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
    have hkS' : (k : G)⁻¹ * (a : G) * (k : G) ∈ S :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hkS)).1
    have hres := h.closed_H (a : G) haU (k : G) hkH hkS'
    rcases hres with hA | hA
    · exact Or.inl (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
    · exact Or.inr (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
  closed₁ := by
    intro a ha k hk
    obtain ⟨hkS, hkN⟩ := Subgroup.mem_inf.1 hk
    have haU : (a : G) ∈ uSet A₁ A₂ := by
      rcases ha with ha | ha
      · exact Or.inl (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
      · exact Or.inr (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
    have hsS : (k : G)⁻¹ * (a : G) * (k : G) ∈ S :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hkS)).1
    rcases swap_dichotomy_disjoint hdisj h.ne_bot₁ h.ne_bot₂ (h.S_le_stab hsS) with
      ⟨hn1, -⟩ | ⟨hs1, -⟩
    · have hres := h.closed₁ (a : G) haU (k : G) ⟨hsS, hn1⟩
      rcases hres with hA | hA
      · exact Or.inl (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
      · exact Or.inr (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
    · exfalso
      obtain ⟨x₀', hx₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
        (ne_bot_of_one_lt_pRank (A := A₁ ⊓ K) (by omega))
      have hx₀ : (x₀' : G) ∈ A₁ ⊓ K := x₀'.2
      have hx₀1 : (x₀' : G) ≠ 1 := fun e => hx₀' (Subtype.ext e)
      set s : ↥K := k⁻¹ * a * k with hs
      have hsG : (s : G) = (k : G)⁻¹ * (a : G) * (k : G) := rfl
      rw [← hsG] at hs1
      have hxX : (⟨(x₀' : G), hx₀.2⟩ : ↥K) ∈ (A₁ ⊓ K).subgroupOf K :=
        Subgroup.mem_subgroupOf.2 hx₀
      have hinv := (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (((A₁ ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K)).inv_mem hkN)
        ⟨(x₀' : G), hx₀.2⟩).1 hxX
      have hA₁ : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₁ := by
        have := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hinv)).1
        simpa using this
      have hA₂ : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₂ := by
        have := conj_mem_conjugate (Subgroup.mem_inf.1 hx₀).1 (s : G)
        rwa [hs1] at this
      have hmem : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₁ ⊓ A₂ := ⟨hA₁, hA₂⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      apply hx₀1
      calc (x₀' : G) = (s : G) * ((s : G)⁻¹ * (x₀' : G) * (s : G)) * (s : G)⁻¹ := by group
        _ = 1 := by rw [hmem]; group
  closed₂ := by
    intro a ha k hk
    obtain ⟨hkS, hkN⟩ := Subgroup.mem_inf.1 hk
    have haU : (a : G) ∈ uSet A₁ A₂ := by
      rcases ha with ha | ha
      · exact Or.inl (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
      · exact Or.inr (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ha)).1
    have hsS : (k : G)⁻¹ * (a : G) * (k : G) ∈ S :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hkS)).1
    rcases swap_dichotomy_disjoint hdisj h.ne_bot₁ h.ne_bot₂ (h.S_le_stab hsS) with
      ⟨-, hn2⟩ | ⟨-, hs2⟩
    · have hres := h.closed₂ (a : G) haU (k : G) ⟨hsS, hn2⟩
      rcases hres with hA | hA
      · exact Or.inl (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
      · exact Or.inr (Subgroup.mem_subgroupOf.2 ⟨hA, (k⁻¹ * a * k).2⟩)
    · exfalso
      obtain ⟨x₀', hx₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
        (ne_bot_of_one_lt_pRank (A := A₂ ⊓ K) (by omega))
      have hx₀ : (x₀' : G) ∈ A₂ ⊓ K := x₀'.2
      have hx₀1 : (x₀' : G) ≠ 1 := fun e => hx₀' (Subtype.ext e)
      set s : ↥K := k⁻¹ * a * k with hs
      have hsG : (s : G) = (k : G)⁻¹ * (a : G) * (k : G) := rfl
      rw [← hsG] at hs2
      have hxX : (⟨(x₀' : G), hx₀.2⟩ : ↥K) ∈ (A₂ ⊓ K).subgroupOf K :=
        Subgroup.mem_subgroupOf.2 hx₀
      have hinv := (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer (((A₂ ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K)).inv_mem hkN)
        ⟨(x₀' : G), hx₀.2⟩).1 hxX
      have hA₂ : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₂ := by
        have := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hinv)).1
        simpa using this
      have hA₁ : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₁ := by
        have := conj_mem_conjugate (Subgroup.mem_inf.1 hx₀).1 (s : G)
        rwa [hs2] at this
      have hmem : (s : G)⁻¹ * (x₀' : G) * (s : G) ∈ A₁ ⊓ A₂ := ⟨hA₁, hA₂⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      apply hx₀1
      calc (x₀' : G) = (s : G) * ((s : G)⁻¹ * (x₀' : G) * (s : G)) * (s : G)⁻¹ := by group
        _ = 1 := by rw [hmem]; group

end Restrict

end CFSG.Asc75
