module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinAlg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinAdd

public section

namespace CFSG.OddStandard.SmallF3.FritzII.FzL59BLin

variable {G : Type} [Group G] {ε : Bool} {fn : N →* G} {y u : G}

theorem LinData.phi_keq (D : LinData ε fn y u) {x x' : X} (h : KEq x x') :
    phi fn y u x = phi fn y u x' := by
  rcases h with h | h
  · rw [h]
  · rw [h, D.phi_ktr]

@[expose] noncomputable def LinData.rangeSubgroup [Finite G] (D : LinData ε fn y u) : Subgroup G :=
  subgroupOfIdempotent (Set.range (phi fn y u)) ⟨phi fn y u oneX, oneX, rfl⟩
    (Set.Subset.antisymm
      (by
        rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨z, rfl⟩, rfl⟩
        exact ⟨star ε x z, D.phi_star x z⟩)
      (fun g hg => ⟨g, hg, 1, ⟨oneX, phi_one fn y u⟩, mul_one g⟩))

theorem LinData.mem_rangeSubgroup [Finite G] (D : LinData ε fn y u) {g : G} :
    g ∈ D.rangeSubgroup ↔ ∃ x : X, phi fn y u x = g := Iff.rfl

theorem card_inH_subtype : Nat.card {a : X // inH a = true} = 2 ^ 10 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem LinData.phi_inj (D : LinData ε fn y u) {T₃ : Subgroup G}
    (hmem : ∀ x : X, phi fn y u x ∈ T₃) (hcov : ∀ g ∈ T₃, ∃ x : X, phi fn y u x = g)
    (hcard : Nat.card T₃ = 2 ^ 10) {x x' : X} (h : phi fn y u x = phi fn y u x') : KEq x x' := by
  haveI : Finite T₃ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrep : ∀ z : X, ∃ r : X, inH r = true ∧ phi fn y u r = phi fn y u z ∧
      (z = r ∨ z = ktr r) := by
    intro z
    by_cases hz : inH z = true
    · exact ⟨z, hz, rfl, Or.inl rfl⟩
    · refine ⟨ktr z, ?_, D.phi_ktr z, Or.inr (ktr_ktr z).symm⟩
      rw [inH_ktr]
      simpa using hz
  obtain ⟨r, hr, hrz, hzr⟩ := hrep x
  obtain ⟨r', hr', hrz', hzr'⟩ := hrep x'
  let f : {a : X // inH a = true} → T₃ := fun a => ⟨phi fn y u a.1, hmem a.1⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := hcov g hg
    obtain ⟨r'', hr'', hrz'', -⟩ := hrep a
    exact ⟨⟨r'', hr''⟩, Subtype.ext (hrz''.trans ha)⟩
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (by rw [card_inH_subtype, hcard])
  have hrr : r = r' :=
    congrArg Subtype.val (hbij.1 (a₁ := ⟨r, hr⟩) (a₂ := ⟨r', hr'⟩)
      (Subtype.ext (show phi fn y u r = phi fn y u r' by rw [hrz, hrz', h])))
  subst hrr
  rcases hzr with h1 | h1 <;> rcases hzr' with h2 | h2
  · exact Or.inl (h1.trans h2.symm)
  · exact Or.inr (by rw [h2, ktr_ktr]; exact h1)
  · exact Or.inr (by rw [h2]; exact h1)
  · exact Or.inl (h1.trans h2.symm)

theorem fz59_linear_aux {T₃ : Subgroup G} (D : LinData ε fn y u)
    (hmem : ∀ x : X, phi fn y u x ∈ T₃) (hcov : ∀ g ∈ T₃, ∃ x : X, phi fn y u x = g)
    (hcard : Nat.card T₃ = 2 ^ 10) : Fz59Linear T₃ := by
  intro χ hconj hpar
  have hinj : ∀ {x x' : X}, phi fn y u x = phi fn y u x' → KEq x x' :=
    fun h => D.phi_inj hmem hcov hcard h
  obtain ⟨f, hf⟩ := lin_core ε (fun x => χ (phi fn y u x))
    (fun g x z hgxz => by
      have h1 : phi fn y u g * phi fn y u x = phi fn y u z * phi fn y u g := by
        rw [← D.phi_star, ← D.phi_star]
        exact D.phi_keq hgxz
      have h2 : phi fn y u g * phi fn y u x * (phi fn y u g)⁻¹ = phi fn y u z := by
        rw [h1, mul_inv_cancel_right]
      have h3 := hconj _ (hmem g) _ (hmem x)
      rw [h2] at h3
      exact h3.symm)
    (fun a c ha hc hac hne => by
      have hA2 : phi fn y u a * phi fn y u a = 1 := by
        rw [← D.phi_star, D.phi_keq ha.2, phi_one]
      have hC2 : phi fn y u c * phi fn y u c = 1 := by
        rw [← D.phi_star, D.phi_keq hc.2, phi_one]
      have hA1 : phi fn y u a ≠ 1 := fun h1 => ha.1 (hinj (h1.trans (phi_one fn y u).symm))
      have hC1 : phi fn y u c ≠ 1 := fun h1 => hc.1 (hinj (h1.trans (phi_one fn y u).symm))
      have hAC : phi fn y u a * phi fn y u c = phi fn y u c * phi fn y u a := by
        rw [← D.phi_star, ← D.phi_star]
        exact D.phi_keq hac
      have hne' : phi fn y u a ≠ phi fn y u c := fun h1 => hne (hinj h1)
      show Xor (χ (phi fn y u a)) (χ (phi fn y u c)) ↔ χ (phi fn y u (star ε a c))
      rw [D.phi_star]
      exact hpar _ (hmem a) _ (hmem c) hA2 hC2 hAC hA1 hC1 hne')
  have hwd : ∀ x x' : X, phi fn y u x = phi fn y u x' → lin f x = lin f x' := by
    intro x x' h
    rcases hinj h with h' | h'
    · rw [h']
    · rw [h', lin_ktr]
  let M : Subgroup G :=
    { carrier := {g | ∃ x : X, phi fn y u x = g ∧ lin f x = false}
      one_mem' := ⟨oneX, phi_one fn y u, lin_one f⟩
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨z, rfl, hz⟩
        exact ⟨star ε x z, D.phi_star x z, by rw [lin_star, hx, hz]; rfl⟩
      inv_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        obtain ⟨z, hz⟩ := hcov _ (inv_mem (hmem x))
        refine ⟨z, hz, ?_⟩
        have h1 : phi fn y u (star ε x z) = phi fn y u oneX := by
          rw [D.phi_star, hz, phi_one, mul_inv_cancel]
        have h2 := hwd _ _ h1
        rw [lin_star, lin_one, hx] at h2
        simpa using h2 }
  have hmemM : ∀ x : X, phi fn y u x ∈ M ↔ lin f x = false := by
    intro x
    constructor
    · rintro ⟨x', hx', hl⟩
      exact (hwd x x' hx'.symm).trans hl
    · intro hl
      exact ⟨x, rfl, hl⟩
  have hMle : M ≤ T₃ := by
    rintro _ ⟨x, rfl, -⟩
    exact hmem x
  refine ⟨M, hMle, ?_, ?_⟩
  · by_cases hex : ∃ x : X, lin f x = true
    · right
      obtain ⟨x₀, hx₀⟩ := hex
      rw [Subgroup.relIndex_eq_two_iff]
      refine ⟨phi fn y u x₀, hmem x₀, fun b hb => ?_⟩
      obtain ⟨xb, hxb⟩ := hcov b hb
      rw [← hxb, ← D.phi_star, hmemM, hmemM, lin_star, hx₀]
      cases lin f xb <;> simp [Xor]
    · left
      refine le_antisymm hMle fun g hg => ?_
      obtain ⟨x, hx⟩ := hcov g hg
      rw [← hx, hmemM]
      by_contra hne
      exact hex ⟨x, by simpa using hne⟩
  · intro v hv hv2 hv1
    obtain ⟨x, hx⟩ := hcov v hv
    have hinv : IsInv ε x := by
      refine ⟨fun h1 => hv1 ?_, hinj ?_⟩
      · rw [← hx, D.phi_keq h1, phi_one]
      · rw [D.phi_star, hx, hv2, phi_one]
    rw [← hx, hmemM]
    have h3 := hf x hinv
    rw [h3]
    simp

end CFSG.OddStandard.SmallF3.FritzII.FzL59BLin
