module

public import CFSG.GH74.Uniqueness.Section1214Semi

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.eq_one_of_fixes_omega
    (S : ZDSetup X Z M) {g : X}
    (hg : ∀ β ∈ omega M, conjugate β g = β) : g = 1 := by
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  have hmem : g ∈ M.normalCore := by
    intro b
    exact mem_conjugate_iff.mp ((S.prodDisc.conjugate_eq_iff_mem ⟨b, rfl⟩).mp (hg _ ⟨b, rfl⟩))
  rcases hsimple.eq_bot_or_eq_top_of_normal M.normalCore with h | h
  · rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    have : M = ⊤ := top_le_iff.mp (h ▸ M.normalCore_le)
    exact S.prodDisc.1 this

theorem ZDSetup.omegaFix_subset_orbit (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M)
    {c : Ctx12 Z M} {n i : ℕ} (hL : LData c n i) {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2)
    (hLu : cenHull Z u = c.L) {β : Subgroup X} (hβ : β ∈ omegaFix M ({u} : Set X)) :
    ∃ l ∈ c.L, conjugate M l = β := by
  have hβu : conjugate β u = β := hβ.2 u (Set.mem_singleton u)
  have hMu : conjugate M u = M :=
    (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (Subgroup.mem_inf.mp hu).1
  obtain ⟨g, hgC, hg⟩ := S.exists_centralizer_conj hu2 (self_mem_omega M) hβ.1 hMu hβu
  have hdecomp := (h124 c n i hL u hu hu2).2.2.2.2
  have h2 : g⁻¹ ∈ ((centralizer ({u} : Set X) : Subgroup X) : Set X) :=
    (centralizer ({u} : Set X)).inv_mem hgC
  rw [hdecomp] at h2
  obtain ⟨l₁, hl₁, d₁, hd₁, hld⟩ := Set.mem_mul.mp h2
  have hg' : g = d₁⁻¹ * l₁⁻¹ := by
    rw [← inv_inv g, ← hld]
    simp [mul_inv_rev]
  have hd₁M : d₁⁻¹ ∈ M := M.inv_mem (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hd₁).2).1
  refine ⟨l₁⁻¹, c.L.inv_mem (hLu ▸ hl₁), ?_⟩
  rw [← hg, hg', ← conjugate_conjugate,
    (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hd₁M]

theorem ZDSetup.lemma1214
    (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M)
    (h1210 : Lemma1210Stmt Z M) (h1212 : Lemma1212Stmt Z M) (h1213 : Prop1213Stmt Z M) :
    Lemma1214Stmt Z M := by
  intro c n i hL u hu hu2 hLu
  have hcomm : ∀ x ∈ c.L, u * x = x * u := fun x hx => mul_comm_of_mem_cenHull (hLu ▸ hx)
  have hΩu : ∀ β ∈ omega M, conjugate β u = β → β ∈ omegaFix M ({u} : Set X) :=
    fun β hβ h => ⟨hβ, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h⟩
  have hsemi : ∀ x ∈ c.L, x ≠ 1 → ∀ β ∈ omega M, β ∉ omegaFix M ({u} : Set X) →
      conjugate β x ≠ β := by
    intro x hx hx1 β hβ hβΓ hfix
    exact S.semiregular h1212 h1213 hL hu hLu hx hx1 hβ (fun h => hβΓ (hΩu β hβ h)) hfix
  have hstable : ∀ l ∈ c.L, ∀ β ∈ omega M, β ∉ omegaFix M ({u} : Set X) →
      conjugate β l ∈ omega M ∧ conjugate β l ∉ omegaFix M ({u} : Set X) := by
    intro l hl β hβ hβΓ
    refine ⟨conjugate_mem_omega hβ l, fun h => hβΓ ?_⟩
    have hfix : conjugate (conjugate β l) u = conjugate β l := h.2 u (Set.mem_singleton u)
    exact hΩu β hβ ((conjugate_fixed_iff (hcomm l hl)).mp hfix)
  have hcardL : Nat.card ↥c.L + (omegaFix M ({u} : Set X)).ncard = (omega M).ncard := by
    rcases h1210 c n i hL with ⟨-, -, hall, -⟩ | ⟨-, -, hall, -⟩ | ⟨-, -, hall, -⟩
    · exact (hall u hu hu2).2.2
    · exact (hall u hu hu2).2.2
    · exact absurd hLu (hall u hu hu2).1.ne'
  have hΓcard : (omega M \ omegaFix M ({u} : Set X)).ncard = Nat.card ↥c.L := by
    rw [Set.ncard_sdiff (omegaFix_subset_omega _)]
    omega
  have htrans : ∀ β ∈ omega M, β ∉ omegaFix M ({u} : Set X) → ∀ γ ∈ omega M,
      γ ∉ omegaFix M ({u} : Set X) → ∃ x ∈ c.L, conjugate β x = γ := by
    intro β hβ hβΓ γ hγ hγΓ
    set O : Set (Subgroup X) := Set.range (fun l : ↥c.L => conjugate β (l : X)) with hO
    have hinj : Function.Injective (fun l : ↥c.L => conjugate β (l : X)) := by
      intro l l' h
      have h1 : conjugate β ((l : X) * (l' : X)⁻¹) = β := by
        rw [← conjugate_conjugate]
        have : conjugate β (l : X) = conjugate β (l' : X) := h
        rw [this, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      by_contra hne
      refine hsemi ((l : X) * (l' : X)⁻¹) (c.L.mul_mem l.2 (c.L.inv_mem l'.2)) ?_ β hβ hβΓ h1
      intro h0
      exact hne (Subtype.ext (mul_inv_eq_one.mp h0))
    have hOsub : O ⊆ omega M \ omegaFix M ({u} : Set X) := by
      rintro _ ⟨l, rfl⟩
      exact hstable l l.2 β hβ hβΓ
    have hOcard : O.ncard = Nat.card ↥c.L := by
      rw [hO, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    have hOeq : O = omega M \ omegaFix M ({u} : Set X) :=
      Set.eq_of_subset_of_ncard_le hOsub (by rw [hΓcard, hOcard])
    have hγO : γ ∈ O := hOeq ▸ (⟨hγ, hγΓ⟩ : γ ∈ omega M \ omegaFix M ({u} : Set X))
    obtain ⟨l, hl⟩ := hγO
    exact ⟨l, l.2, hl⟩
  refine ⟨⟨hsemi, htrans⟩, ?_⟩
  have hΓne : (omega M \ omegaFix M ({u} : Set X)).Nonempty := by
    have : 0 < (omega M \ omegaFix M ({u} : Set X)).ncard := by
      rw [hΓcard]
      exact Nat.card_pos
    exact Set.nonempty_of_ncard_ne_zero this.ne'
  obtain ⟨β₀, hβ₀Ω, hβ₀u⟩ := hΓne
  have hJM : ∀ g ∈ centralizer (c.L : Set X), g ∈ M := fun g hg =>
    (Subgroup.mem_inf.mp (hL.centralizer_le hg)).1
  have hJL : ∀ g ∈ centralizer (c.L : Set X), ∀ l ∈ c.L, l * g = g * l := fun g hg l hl =>
    Subgroup.mem_centralizer_iff.mp hg l hl
  have hJfix : ∀ g ∈ centralizer (c.L : Set X), ∀ β ∈ omegaFix M ({u} : Set X),
      conjugate β g = β := by
    intro g hg β hβ
    obtain ⟨l, hl, rfl⟩ := S.omegaFix_subset_orbit h124 hL hu hu2 hLu hβ
    have hgM : conjugate M g = M :=
      (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (hJM g hg)
    rw [conjugate_conjugate, hJL g hg l hl, ← conjugate_conjugate, hgM]
  have hJΓ : ∀ g ∈ centralizer (c.L : Set X), ∀ β ∈ omega M,
      β ∉ omegaFix M ({u} : Set X) → conjugate β g ∈ omega M ∧
        conjugate β g ∉ omegaFix M ({u} : Set X) := by
    intro g hg β hβ hβΓ
    refine ⟨conjugate_mem_omega hβ g, fun h => hβΓ ?_⟩
    have h1 := hJfix g⁻¹ ((centralizer (c.L : Set X)).inv_mem hg) _ h
    have h2 : conjugate (conjugate β g) g⁻¹ = β := by
      rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
    have h3 : β = conjugate β g := h2.symm.trans h1
    rw [h3]
    exact h
  have hex : ∀ g : ↥(centralizer (c.L : Set X)), ∃! l : ↥c.L,
      conjugate β₀ (l : X) = conjugate β₀ (g : X) := by
    intro g
    obtain ⟨hgΩ, hgΓ⟩ := hJΓ g g.2 β₀ hβ₀Ω hβ₀u
    obtain ⟨l, hl, hlg⟩ := htrans β₀ hβ₀Ω hβ₀u _ hgΩ hgΓ
    refine ⟨⟨l, hl⟩, hlg, fun l' hl' => ?_⟩
    have h1 : conjugate β₀ ((l' : X) * l⁻¹) = β₀ := by
      rw [← conjugate_conjugate, hl', ← hlg, conjugate_conjugate, mul_inv_cancel, conjugate_one]
    by_contra hne
    refine hsemi ((l' : X) * l⁻¹) (c.L.mul_mem l'.2 (c.L.inv_mem hl)) ?_ β₀ hβ₀Ω hβ₀u h1
    intro h0
    exact hne (Subtype.ext (mul_inv_eq_one.mp h0))
  let lf : ↥(centralizer (c.L : Set X)) → ↥c.L := fun g => Classical.choose (hex g).exists
  have lf_spec : ∀ g, conjugate β₀ ((lf g : ↥c.L) : X) = conjugate β₀ (g : X) := fun g =>
    Classical.choose_spec (hex g).exists
  have lf_unique : ∀ (g : ↥(centralizer (c.L : Set X))) (l : ↥c.L),
      conjugate β₀ (l : X) = conjugate β₀ (g : X) → l = lf g :=
    fun g l h => (hex g).unique h (lf_spec g)
  let φ : ↥(centralizer (c.L : Set X)) →* ↥c.L :=
    { toFun := fun g => (lf g)⁻¹
      map_one' := by
        have : lf 1 = 1 := (lf_unique 1 1 (by simp)).symm
        simp [this]
      map_mul' := by
        intro g g'
        have h1 : lf (g * g') = lf g' * lf g := by
          symm
          apply lf_unique
          calc conjugate β₀ (((lf g' * lf g : ↥c.L)) : X)
              = conjugate (conjugate β₀ ((lf g' : ↥c.L) : X)) ((lf g : ↥c.L) : X) := by
                rw [Subgroup.coe_mul, conjugate_conjugate]
            _ = conjugate (conjugate β₀ (g' : X)) ((lf g : ↥c.L) : X) := by rw [lf_spec g']
            _ = conjugate β₀ ((g' : X) * ((lf g : ↥c.L) : X)) := conjugate_conjugate _ _ _
            _ = conjugate β₀ (((lf g : ↥c.L) : X) * (g' : X)) := by
                rw [← hJL g' g'.2 _ (lf g).2]
            _ = conjugate (conjugate β₀ ((lf g : ↥c.L) : X)) (g' : X) :=
                (conjugate_conjugate _ _ _).symm
            _ = conjugate (conjugate β₀ (g : X)) (g' : X) := by rw [lf_spec g]
            _ = conjugate β₀ ((g * g' : ↥(centralizer (c.L : Set X))) : X) := by
                rw [Subgroup.coe_mul, conjugate_conjugate]
        show (lf (g * g'))⁻¹ = (lf g)⁻¹ * (lf g')⁻¹
        rw [h1, mul_inv_rev] }
  refine ⟨φ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hlf : lf g = 1 := inv_eq_one.mp hg
  have hfix0 : conjugate β₀ (g : X) = β₀ := by
    rw [← lf_spec g, hlf]
    exact conjugate_one β₀
  apply Subtype.ext
  show (g : X) = 1
  refine S.eq_one_of_fixes_omega (fun β hβ => ?_)
  by_cases hβu : β ∈ omegaFix M ({u} : Set X)
  · exact hJfix g g.2 β hβu
  · obtain ⟨l, hl, hlβ⟩ := htrans β₀ hβ₀Ω hβ₀u β hβ hβu
    rw [← hlβ, conjugate_conjugate, hJL g g.2 l hl, ← conjugate_conjugate, hfix0]

end CFSG.GH74.Uniqueness
