module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5Cnt

public section

namespace CFSG.QuasithinUnique.A5.Kc3L5

open Matrix CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5

theorem scalars_eq_bot_gen {n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    StatedScalars (Fin n) F = ⊥ := by
  classical
  have := Fintype.ofFinite F
  have hu : Subsingleton Fˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units]
    have : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
    omega
  rw [eq_bot_iff]
  rintro g ⟨u, rfl⟩
  rw [Subsingleton.elim u 1, map_one]
  exact Subgroup.one_mem _

@[expose] def psiN (n : ℕ) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    StatedProj (StatedSL n F) →* GL (Fin n) F :=
  QuotientGroup.lift _ (StatedSL n F).subtype (by
    intro x hx
    have hx' : (x : GL (Fin n) F) ∈ StatedScalars (Fin n) F := Subgroup.mem_subgroupOf.1 hx
    rw [scalars_eq_bot_gen hF] at hx'
    rw [MonoidHom.mem_ker]
    exact Subgroup.mem_bot.1 hx')

theorem psiN_mk (n : ℕ) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (s : ↥(StatedSL n F)) : psiN n hF (QuotientGroup.mk s) = (s : GL (Fin n) F) := rfl

theorem psiN_injective (n : ℕ) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Function.Injective (psiN n hF) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (s : GL (Fin n) F) = 1 := by
    rw [MonoidHom.mem_ker, psiN_mk] at hx
    exact hx
  have : s = 1 := Subtype.ext h1
  simp [this]

theorem psiN_surjective (n : ℕ) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Function.Surjective (psiN n hF) := by
  classical
  have := Fintype.ofFinite F
  have hu : Subsingleton Fˣ := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units]
    have : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
    omega
  intro g
  have hdet : ((g : Matrix (Fin n) (Fin n) F)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
    have h2 := congrArg Units.val h1
    simpa using h2
  have hmem : g ∈ StatedSL n F := Subgroup.subset_closure hdet
  exact ⟨QuotientGroup.mk ⟨g, hmem⟩, rfl⟩

theorem exists_equiv_Gl {X : Type} [Group X] (hX : Kc3L5 X) : Nonempty (X ≃* Gl) := by
  classical
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : Fintype F := Fintype.ofFinite F
  have hfc : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card, hF2]
  let e₁ : StatedProj (StatedSL 5 F) ≃* GL (Fin 5) F :=
    MulEquiv.ofBijective (psiN 5 hF2) ⟨psiN_injective 5 hF2, psiN_surjective 5 hF2⟩
  let σ : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime (R := F) Nat.prime_two hfc
  let e₂ : GL (Fin 5) F ≃* Gl :=
    Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 5) σ.symm).toMulEquiv
  exact ⟨(e.trans e₁).trans e₂⟩

end CFSG.QuasithinUnique.A5.Kc3L5
