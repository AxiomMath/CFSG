module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2

@[expose] def Sec8 (G : Type) [Group G] : Prop :=
  ∀ (B E : Type) [Group B] [Group E] [Finite B] [Finite E] (ι : B →* G) (f : B →* E),
    Function.Injective ι → Function.Surjective f → (∀ x : E, x * x = 1) → Nat.card E ≤ 8

theorem Sec8.of_injective {G G' : Type} [Group G] [Group G'] (φ : G' →* G)
    (hφ : Function.Injective φ) (h : Sec8 G) : Sec8 G' :=
  fun B E _ _ _ _ ι f hι hf hE => h B E (φ.comp ι) f (hφ.comp hι) hf hE

theorem Sec8.of_surjective {G G' : Type} [Group G] [Group G'] [Finite G] (π : G →* G')
    (hπ : Function.Surjective π) (h : Sec8 G) : Sec8 G' := by
  intro B E _ _ _ _ ι f hι hf hE
  let R : Subgroup G' := ι.range
  let S : Subgroup G := R.comap π
  let e : R ≃* B := (MonoidHom.ofInjective hι).symm
  let p : S →* R := MonoidHom.codRestrict (π.comp S.subtype) R (fun s => s.2)
  let g : S →* E := f.comp (e.toMonoidHom.comp p)
  refine h S E S.subtype g S.subtype_injective ?_ hE
  intro x
  obtain ⟨b, rfl⟩ := hf x
  obtain ⟨s, hs⟩ := hπ (ι b)
  have hsS : s ∈ S := ⟨b, hs.symm⟩
  refine ⟨⟨s, hsS⟩, ?_⟩
  show f (e (p ⟨s, hsS⟩)) = f b
  congr 1
  have : p ⟨s, hsS⟩ = e.symm b := by
    apply Subtype.ext
    show π s = ι b
    exact hs
  rw [this, MulEquiv.apply_symm_apply]

theorem Sec8.of_two {G : Type} [Group G]
    (h : ∀ (B E : Type) [Group B] [Group E] [Finite B] [Finite E] (ι : B →* G) (f : B →* E),
      IsPGroup 2 B → Function.Injective ι → Function.Surjective f → (∀ x : E, x * x = 1) →
      Nat.card E ≤ 8) : Sec8 G := by
  intro B E _ _ _ _ ι f hι hf hE
  obtain ⟨P⟩ : Nonempty (Sylow 2 B) := inferInstance
  have hEp : IsPGroup 2 E := fun x => ⟨1, by simpa [pow_two] using hE x⟩
  have hidx : (P.toSubgroup.map f).index = 1 := by
    have h1 : (P.toSubgroup.map f).index ∣ P.toSubgroup.index :=
      Subgroup.index_map_dvd (H := P.toSubgroup) hf
    obtain ⟨k, hk⟩ := hEp.index (P.toSubgroup.map f)
    have h2 : ¬ 2 ∣ P.toSubgroup.index := P.not_dvd_index
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · rfl
    · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h1) h2
  have hsurj : Function.Surjective (f.comp P.toSubgroup.subtype) := by
    intro x
    have : P.toSubgroup.map f = ⊤ := Subgroup.index_eq_one.mp hidx
    have hx : x ∈ P.toSubgroup.map f := this ▸ Subgroup.mem_top x
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  exact h P.toSubgroup E (ι.comp P.toSubgroup.subtype) (f.comp P.toSubgroup.subtype)
    P.isPGroup' (hι.comp P.toSubgroup.subtype_injective) hsurj hE

theorem exists_index_stabilizer_le_two {T X : Type} [Group T] [Finite T] [MulAction T X]
    [Finite X] (hT : IsPGroup 2 T) (hX : Nat.card X % 4 = 2) :
    ∃ x : X, (MulAction.stabilizer T x).index ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hdvd : ∀ x : X, 4 ∣ (MulAction.stabilizer T x).index := by
    intro x
    obtain ⟨k, hk⟩ := hT.index (MulAction.stabilizer T x)
    have := hcon x
    rw [hk] at this ⊢
    rcases k with _ | _ | k
    · simp at this
    · simp at this
    · exact ⟨2 ^ k, by ring⟩
  have : Finite (MulAction.orbitRel.Quotient T X) := Quotient.finite _
  have : Fintype (MulAction.orbitRel.Quotient T X) := Fintype.ofFinite _
  have hcard : Nat.card X = ∑ ω : MulAction.orbitRel.Quotient T X, Nat.card ω.orbit := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' T X), Nat.card_sigma]
  have h4 : 4 ∣ Nat.card X := by
    rw [hcard]
    refine Finset.dvd_sum fun ω _ => ?_
    obtain ⟨x, rfl⟩ := ω.exists_rep
    have h := hdvd x
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
    rwa [MulAction.orbitRel.Quotient.orbit_mk]
  omega

theorem card_le_card_sq_eq_one {A F : Type} [Group A] [Finite A] [Group F]
    (hcomm : ∀ a b : A, a * b = b * a) (g : A →* F) (hg : Function.Surjective g)
    (hF : ∀ x : F, x * x = 1) : Nat.card F ≤ Nat.card {a : A // a * a = 1} := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  let sq : A →* A := powMonoidHom 2
  have hker : Nat.card sq.ker = Nat.card {a : A // a * a = 1} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun a => by simp [sq, pow_two]
  have h1 := Subgroup.card_ker_mul_card_range sq
  have h2 := Subgroup.card_ker_mul_card_of_surjective hg
  have hle : sq.range ≤ g.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [sq, powMonoidHom_apply, pow_two, map_mul]
    exact hF _
  have h3 : Nat.card sq.range ≤ Nat.card g.ker := Nat.card_mono (Set.toFinite _) hle
  have hpos : 0 < Nat.card g.ker := Nat.card_pos
  rw [← hker]
  by_contra hlt
  push Not at hlt
  have : Nat.card sq.ker * Nat.card sq.range < Nat.card F * Nat.card g.ker :=
    calc Nat.card sq.ker * Nat.card sq.range ≤ Nat.card sq.ker * Nat.card g.ker :=
          Nat.mul_le_mul_left _ h3
      _ < Nat.card F * Nat.card g.ker := Nat.mul_lt_mul_of_pos_right hlt hpos
  have h2' : Nat.card F * Nat.card g.ker = Nat.card A := by rw [mul_comm]; exact h2
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
