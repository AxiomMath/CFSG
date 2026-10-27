module

public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.Exceptional.TwistedE6

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

universe w

noncomputable abbrev bnRootSystem (L : LieUniversal) : RootSystem (Fin L.D.rank) :=
  RootSystem.ofCartan L.D.isFiniteType L.D.divisible

@[expose] def IsUntwistedTag : StatedLieTag → Prop
  | .PSL | .PSp | .POmegaOdd | .POmegaPlus | .F4 | .E6 | .E7 | .E8 => True
  | _ => False

@[expose] def castParam {F : Type*} {L L' : LieUniversal} (h : L = L')
    (x : (Fin L.D.rank → ℤ) → F → L.K) : (Fin L'.D.rank → ℤ) → F → L'.K :=
  h ▸ x

theorem lieUniversal_POmegaPlus {n p f : ℕ} (hp : p.Prime) [Fact p.Prime] (hn : 3 ≤ n) :
    (⟨_, Spin.plusDatum n (GaloisField p f) hn⟩ : LieUniversal) =
      lieUniversal .POmegaPlus n p f hp := by
  rw [lieUniversal]
  simp only [hn, ↓reduceDIte]

@[expose] noncomputable def plusParam (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] :
    (Fin (lieUniversal .POmegaPlus n p f hp).D.rank → ℤ) → GaloisField p f →
      (lieUniversal .POmegaPlus n p f hp).K :=
  if hn : 3 ≤ n then castParam (lieUniversal_POmegaPlus hp hn) (SpinPlus.x n (GaloisField p f) hn)
  else fun _ _ => 1

theorem plusParam_eq {n p f : ℕ} (hp : p.Prime) [Fact p.Prime] (hn : 3 ≤ n) :
    plusParam n p f hp =
      castParam (lieUniversal_POmegaPlus hp hn) (SpinPlus.x n (GaloisField p f) hn) := by
  rw [plusParam]
  simp only [hn, ↓reduceDIte]

@[expose] noncomputable def untwistedParam (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    [Fact p.Prime] :
    (Fin (lieUniversal t n p f hp).D.rank → ℤ) → GaloisField p f → (lieUniversal t n p f hp).K :=
  match t, n with
  | .PSL, m + 1 => SL.x m (GaloisField p f)
  | .PSp, n => Sp.x n (GaloisField p f)
  | .POmegaOdd, n => SpinOdd.x n (GaloisField p f)
  | .POmegaPlus, n => plusParam n p f hp
  | .F4, _ => Adjoint.f4Par (GaloisField p f)
  | .E6, _ => Minuscule.e6Data_valid.xm (GaloisField p f)
  | .E7, _ => Minuscule.e7Data_valid.xm (GaloisField p f)
  | .E8, _ => Adjoint.e8Par (GaloisField p f)
  | _, _ => fun _ _ => 1

@[expose] def StatementFor (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] : Prop :=
  PresentationA.{0, 0, w} (bnRootSystem (lieUniversal t n p f hp))
      (lieUniversal t n p f hp).D.rootGroup ∧
    (IsUntwistedTag t →
      IsParametrization (Φ := bnRootSystem (lieUniversal t n p f hp))
          (lieUniversal t n p f hp).D.rootGroup (untwistedParam t n p f hp) ∧
        Nonempty (CommOrder (bnRootSystem (lieUniversal t n p f hp))) ∧
        PresentationB (Φ := bnRootSystem (lieUniversal t n p f hp))
          (untwistedParam t n p f hp) ∧
        RedundantR2 (bnRootSystem (lieUniversal t n p f hp))
          (lieUniversal t n p f hp).D.rootGroup)

theorem presentationA_congr {L L' : LieUniversal} (h : L = L')
    (hA : PresentationA.{0, 0, w} (bnRootSystem L') L'.D.rootGroup) :
    PresentationA.{0, 0, w} (bnRootSystem L) L.D.rootGroup := by
  subst h
  exact hA

theorem conclusionB_castParam {F : Type} [Field F] {L L' : LieUniversal} (h : L = L')
    {x : (Fin L.D.rank → ℤ) → F → L.K} (hB : ConclusionB L.D F x) :
    ConclusionB L'.D F (castParam h x) := by
  subst h
  exact hB

theorem two_ne_zero_galoisField {p : ℕ} [Fact p.Prime] (f : ℕ) (h : p ≠ 2) :
    (2 : GaloisField p f) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

theorem statementFor_PSL (m p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hm : 2 ≤ m) :
    StatementFor.{w} .PSL (m + 1) p f hp :=
  ⟨(sl_conclusionA.{w} m _).1, fun _ => sl_conclusionB m _ hm⟩

theorem statementFor_PSU (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hf : 1 ≤ f) (hn : 2 ≤ n) :
    StatementFor.{w} .PSU n p f hp := by
  have hL : lieUniversal .PSU n p f hp =
      ⟨_, Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ := by
    rw [lieUniversal]
    simp only [hf, ↓reduceDIte]
  exact ⟨presentationA_congr hL (su_conclusionA.{w} (card_galoisField_two_mul p f hf) n hn).1,
    fun h => h.elim⟩

theorem statementFor_PSp (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hn : 2 ≤ n) :
    StatementFor.{w} .PSp n p f hp :=
  ⟨(sp_conclusionA.{w} n _).1, fun _ => sp_conclusionB n _ hn⟩

theorem statementFor_POmegaOdd (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (h2 : p ≠ 2)
    (hn : 3 ≤ n) : StatementFor.{w} .POmegaOdd n p f hp :=
  ⟨(spinOdd_conclusionA.{w} n _ (two_ne_zero_galoisField f h2) hn).1,
    fun _ => spinOdd_conclusionB n _ (two_ne_zero_galoisField f h2) hn⟩

theorem statementFor_POmegaPlus (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hn : 3 ≤ n) :
    StatementFor.{w} .POmegaPlus n p f hp := by
  refine ⟨presentationA_congr (lieUniversal_POmegaPlus hp hn).symm
    (spinPlus_conclusionA.{w} n _ hn).1, fun _ => ?_⟩
  change ConclusionB _ _ (plusParam n p f hp)
  rw [plusParam_eq hp hn]
  exact conclusionB_castParam _ (spinPlus_conclusionB n _ hn)

theorem statementFor_POmegaMinus (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hn : 4 ≤ n) :
    StatementFor.{w} .POmegaMinus n p f hp :=
  ⟨(spinMinus_conclusionA.{w} n (minusCoeffs_irr p f) hn).1, fun h => h.elim⟩

theorem statementFor_F4 (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] :
    StatementFor.{w} .F4 n p f hp :=
  ⟨(Adjoint.f4_conclusionA.{w} _).1, fun _ => Adjoint.f4_conclusionB _⟩

theorem statementFor_E6 (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] :
    StatementFor.{w} .E6 n p f hp :=
  ⟨(e6_conclusionA.{w} _).1, fun _ => e6_conclusionB _⟩

theorem statementFor_E7 (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] :
    StatementFor.{w} .E7 n p f hp :=
  ⟨(e7_conclusionA.{w} _).1, fun _ => e7_conclusionB _⟩

theorem statementFor_E8 (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] :
    StatementFor.{w} .E8 n p f hp :=
  ⟨(Adjoint.e8_conclusionA.{w} _).1, fun _ => Adjoint.e8_conclusionB _⟩

theorem statementFor_twistedE6 (n p f : ℕ) (hp : p.Prime) [Fact p.Prime] (hf : 1 ≤ f) :
    StatementFor.{w} .twistedE6 n p f hp :=
  ⟨(twistedE6_conclusionA.{w} p f hf).1, fun h => h.elim⟩

theorem steinberg_presentation (t : StatedLieTag) (n p f : ℕ) [Fact p.Prime]
    (hadm : StatedLieAdmissible t n p f) (hrank : 3 ≤ bnRank t n) :
    StatementFor.{w} t n p f hadm.1 := by
  obtain ⟨hp, hf, hcond⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only at hcond; omega⟩
    exact statementFor_PSL m p f hp (by simp only [bnRank] at hrank; omega)
  | PSU => exact statementFor_PSU n p f hp hf (by simp only [bnRank] at hrank; omega)
  | PSp => exact statementFor_PSp n p f hp (by simp only [bnRank] at hrank; omega)
  | POmegaOdd =>
    simp only at hcond
    exact statementFor_POmegaOdd n p f hp hcond.2 hcond.1
  | POmegaPlus => exact statementFor_POmegaPlus n p f hp (by simp only [bnRank] at hrank; omega)
  | POmegaMinus => exact statementFor_POmegaMinus n p f hp (by simp only [bnRank] at hrank; omega)
  | F4 => exact statementFor_F4 n p f hp
  | E6 => exact statementFor_E6 n p f hp
  | E7 => exact statementFor_E7 n p f hp
  | E8 => exact statementFor_E8 n p f hp
  | twistedE6 => exact statementFor_twistedE6 n p f hp hf
  | G2 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    simp only [bnRank] at hrank
    omega

end CFSG.LieType.Steinberg
