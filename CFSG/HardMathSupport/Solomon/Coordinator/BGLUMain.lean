module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUFieldFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem mem_fixGL_iff {F : Type*} [Field F] (σ : F ≃+* F) (g : Matrix.GeneralLinearGroup (Fin 3) F) :
    g ∈ fixGL σ ↔ ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) F) i j) = (g : Matrix (Fin 3) (Fin 3) F) i j := by
  show (GeneralLinearGroup.map σ.toRingHom) g = (MonoidHom.id _) g ↔ _
  constructor
  · intro h i j
    have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin 3) F =>
      (z : Matrix (Fin 3) (Fin 3) F) i j) h
    simpa using this
  · intro h
    apply Units.ext
    ext i j
    simpa using h i j

theorem su3SubfieldJoin_holds :
    SU3SubfieldJoin := by
  intro F _ _ q hcard hq3 hq8 σ hσ h hunit hnot
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have := Fintype.ofFinite F
  obtain ⟨n, hpn, hcn⟩ := FiniteField.card F p
  have h1 : q ^ 2 = p ^ (n : ℕ) := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact hcn
  have h2 : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← h1]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpn).1 h2
  subst hf
  have hF : Nat.card F = (p ^ f) ^ 2 := hcard
  set ι := unitaryInvolution F p f with hιdef
  have hι : IsUnitaryInvolution ι := isUnitaryInvolution_unitaryInvolution hF
  have hιx : ∀ x, ι x = x ^ p ^ f := fun x => unitaryInvolution_apply F p f x
  have hcomm : ∀ x, σ (ι x) = ι (σ x) := fun x => by rw [hιx, hιx, map_pow]
  have hρ3 : orderOf (σ : RingAut F) = 3 := hσ
  have hcount := galois_counts ι σ hι.invol hι.exists_ne hρ3 hcomm
  have hE : Nat.card (Efix ι) = p ^ f := by
    have := hcount.2.2
    rw [hF] at this
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this.symm
  have three : (3 : F) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := by
      have : ((3 : ℕ) : F) = 0 := by exact_mod_cast h0
      exact (CharP.cast_eq_zero_iff F p 3).mp this
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp hdvd
    subst hp3
    have hf0 : f ≠ 0 := by
      rintro rfl
      have h := Finite.one_lt_card (α := F)
      rw [hF] at h
      simp at h
    exact hq3 (Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 hf0))
  have FH : FieldHyp ι σ := ⟨hι, hρ3, hcomm, three, by rw [hE]; exact hq8⟩
  have hk3 := FH.card_k_ge
  have hq2 : p ^ f ≠ 2 := by
    intro h2'
    have h5 := FH.counts.1
    rw [hE, h2'] at h5
    have h6 : 3 ^ 3 ≤ Nat.card (kfix ι σ) ^ 3 := Nat.pow_le_pow_left hk3 3
    omega
  have h3 : ∃ s : F, s ≠ 0 ∧ ι s * s ≠ 1 := exists_norm_ne_one hF hq2
  have hiso : ∀ x y, herm ι ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
      ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = herm ι x y := by
    intro x y
    rw [herm_mulVec ι]
    have e : conjTr ι (h : Matrix (Fin 3) (Fin 3) F) =
        ((h : Matrix (Fin 3) (Fin 3) F).map (· ^ p ^ f))ᵀ := by
      unfold conjTr
      congr 2
    rw [e, hunit, Matrix.one_mulVec]
  have hGeq : CFSG.Open.StatedSU 3 (p ^ f) F = SUid ι 3 := (SUid_eq_statedSU hF 3).symm
  rw [hGeq]
  let H : Subgroup (SUid ι 3) :=
    ((SUid ι 3 ⊓ fixGL σ) ⊔ (SUid ι 3 ⊓ fixGL σ).map (MulAut.conj h).toMonoidHom).comap
      (SUid ι 3).subtype
  have hrat : ∀ g : SUid ι 3, RatM σ ((g.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →
      g ∈ H := by
    intro g hg
    refine Subgroup.mem_sup_left ?_
    exact Subgroup.mem_inf.mpr ⟨g.2, (mem_fixGL_iff σ _).mpr hg⟩
  have hconj : ∀ g g' : SUid ι 3, RatM σ ((g.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →
      (g'.1 : GL (Fin 3) F) = h * g.1 * h⁻¹ → g' ∈ H := by
    intro g g' hg hg'
    refine Subgroup.mem_sup_right ?_
    refine ⟨g.1, Subgroup.mem_inf.mpr ⟨g.2, (mem_fixGL_iff σ _).mpr hg⟩, ?_⟩
    exact hg'.symm
  have hH : H = ⊤ :=
    su3_core hι h3 FH.uctx three FH.exists_u FH.exists_ω (FieldHyp.kE ι σ) (fun e => FieldHyp.mem_kE e) FH.hcard FH.hk2
      FH.span h hiso hnot H hrat hconj
  intro g hg
  have : (⟨g, hg⟩ : SUid ι 3) ∈ H := by rw [hH]; trivial
  exact this

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
