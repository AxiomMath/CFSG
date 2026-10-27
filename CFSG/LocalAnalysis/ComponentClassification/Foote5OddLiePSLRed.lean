module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {S T : Type} [Group S] [Group T]

theorem congr_conj (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  simp [MulAut.congr_apply]

theorem congr_eq_conj (g x : MulAut S) : MulAut.congr g x = g * x * g⁻¹ := rfl

theorem commute_of_congr (e : S ≃* T) {i : MulAut S}
    (h : ∀ R' : Subgroup (MulAut T), Odd (Nat.card R') →
      (∀ r ∈ R', r * MulAut.congr e i = MulAut.congr e i * r) →
      (∀ s : T, MulAut.congr e i s = s → Odd (orderOf s) → ∀ r ∈ R',
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R') →
      ∀ r₁ ∈ R', ∀ r₂ ∈ R', r₁ * r₂ = r₂ * r₁)
    {R : Subgroup (MulAut S)} (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set φ : MulAut S →* MulAut T := (MulAut.congr e).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.congr e).injective
  have hφapp : ∀ x, φ x = MulAut.congr e x := fun x => rfl
  set R' := R.map φ with hR'
  have hR'odd : Odd (Nat.card R') := by
    rw [hR', Subgroup.card_map_of_injective hinj]
    exact hRodd
  have hR'i : ∀ r ∈ R', r * MulAut.congr e i = MulAut.congr e i * r := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hφapp, ← map_mul, ← map_mul, hRi r hr]
  have hR'c : ∀ s : T, MulAut.congr e i s = s → Odd (orderOf s) → ∀ r ∈ R',
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R' := by
    rintro s hs hso _ ⟨r, hr, rfl⟩
    have hs' : i (e.symm s) = e.symm s := by
      have := congrArg e.symm hs
      simpa [MulAut.congr_apply] using this
    have hso' : Odd (orderOf (e.symm s)) := by rwa [MulEquiv.orderOf_eq]
    refine ⟨_, hRc _ hs' hso' r hr, ?_⟩
    rw [hφapp, map_mul, map_mul, map_inv, congr_conj, MulEquiv.apply_symm_apply, hφapp]
  intro r₁ h₁ r₂ h₂
  apply hinj
  have := h R' hR'odd hR'i hR'c (φ r₁) ⟨r₁, h₁, rfl⟩ (φ r₂) ⟨r₂, h₂, rfl⟩
  rw [map_mul, map_mul]
  exact this

theorem center_eq_bot_of_simple [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) :
    center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ center S := h ▸ mem_top b
    exact hab (mem_center_iff.mp hb a)

theorem center_eq_bot_of_mulEquiv (e : S ≃* T) (h : center S = ⊥) : center T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ center S := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.mp hz (e g)
  rw [h, mem_bot] at hz'
  rw [mem_bot, ← e.apply_symm_apply z, hz', map_one]

theorem oddLieCoreFamilyInput_psl_of
    (h : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f → ∀ n : ℕ, 3 ≤ n →
      center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥ →
      ∀ i : MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)), orderOf i = 2 →
      ∀ R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))),
        Odd (Nat.card R) → (∀ r ∈ R, r * i = i * r) →
        (∀ s, i s = s → Odd (orderOf s) → ∀ r ∈ R,
          MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
        ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁) :
    OddLieCoreFamilyInput .PSL := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi R hRodd hRi hRc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hf, hn2, -, -⟩ := hadm
  have hn : 3 ≤ n := by
    by_contra hlt
    have hn' : n = 2 := by omega
    subst hn'
    exact hL2 ⟨p, f, hp, hp2, hf, hm⟩
  have hcl : StatedClassicalModel S .PSL n p f := by
    rcases hm with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S n p f hcl
  have hZ := center_eq_bot_of_mulEquiv e (center_eq_bot_of_simple hna)
  refine commute_of_congr e (fun R' hR'odd hR'i hR'c =>
    h p f hp2 hf n hn hZ _ ?_ R' hR'odd hR'i hR'c) hRodd hRi hRc
  rw [MulEquiv.orderOf_eq]
  exact hi

end CFSG.ComponentClassification.Foote5.OddLieCore
