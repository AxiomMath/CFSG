module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

@[expose] def d4ThreeReps : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [2, 1, 0, 0], [0, 0, 1, 0]]

@[expose] def d4ThreeOrbit : List ℕ :=
  [0, 1, 644337, 2, 3, 4, 1110906, 92, 434258587, 5, 171949, 9, 166125, 5361219, 11, 18, 19, 20,
   1081533557, 71593, 19109, 123434, 12, 48250955, 18461, 48250963, 91, 900, 644339, 1522, 1110907,
   7379, 229, 881, 237, 13357317, 164845, 1523, 71595, 883, 164909, 66203, 123435, 66275, 2037, 172,
   170, 171, 97, 29, 1484149, 99, 1484157, 595691, 1548, 1546, 1547, 897, 253, 13352269, 899,
   13352277, 66187, 100, 5368259, 13714, 5362435, 819, 2053, 7953, 2125, 120170397, 18317, 13715,
   596475, 7955, 1483589, 7355, 595827, 7363, 18325]

@[expose] def d4ThreeStab0 : StabCert3 where
  vec := [0, 0, 0, 0]
  simple := [0, 1, 2, 3]
  keys := [50462976]

@[expose] def d4ThreeStab1 : StabCert3 where
  vec := [1, 0, 0, 0]
  simple := [1, 2, 3]
  keys := [16909079, 17105687, 33558290, 50462976, 50659588, 117442837, 150996747, 251658769]

@[expose] def d4ThreeStab2 : StabCert3 where
  vec := [0, 1, 0, 0]
  simple := [0, 2, 3]
  keys := [136963, 464643, 33625101, 50462976, 50791936, 83957001, 151064069, 218173698]

@[expose] def d4ThreeStab3 : StabCert3 where
  vec := [1, 1, 0, 0]
  simple := [2, 3]
  keys :=
    [136963, 464643, 595722, 988938, 16909079, 17105687, 17369623, 17631767, 33558290, 33625101,
     33756178, 34804754, 50462976, 50659588, 50791936, 51119620, 83957001, 84088080, 84874512,
     117442837, 117641237, 118296597, 150996747, 151064069, 151784971, 201527828, 201921044,
     218173698, 218566920, 251658769, 251987985, 318901006]

@[expose] def d4ThreeStab4 : StabCert3 where
  vec := [2, 1, 0, 0]
  simple := [2, 3, 12]
  keys := [33558290, 33625101, 50462976, 50659588, 50791936, 51119620, 150996747, 151064069]

@[expose] def d4ThreeStab5 : StabCert3 where
  vec := [0, 0, 1, 0]
  simple := [0, 1, 3]
  keys :=
    [1185283, 1381891, 18088726, 18154262, 34606861, 35065613, 50462976, 51708160, 85070601,
     85398281, 118753555, 118950163, 151521029, 152504069, 202706191, 202837263, 218827778,
     219614210, 252576268, 253166092, 319882503, 320275719, 370212865, 370475009]

@[expose] def d4ThreeCheck (_ : Unit := ()) : Bool :=
  orbitCheck3 .D4 d4ThreeReps d4ThreeOrbit &&
    [d4ThreeStab0, d4ThreeStab1, d4ThreeStab2, d4ThreeStab3, d4ThreeStab4, d4ThreeStab5].all
      fun S => S.check d4Certificate && decide ((S.passing d4Certificate).length ≤ 1)

theorem d4ThreeCheck_eq_true : d4ThreeCheck () = true := by decide +kernel

theorem d4ThreeCheck_spec :
    orbitCheck3 .D4 d4ThreeReps d4ThreeOrbit = true ∧
      ∀ S ∈ [d4ThreeStab0, d4ThreeStab1, d4ThreeStab2, d4ThreeStab3, d4ThreeStab4, d4ThreeStab5],
        S.check d4Certificate = true ∧ (S.passing d4Certificate).length ≤ 1 := by
  have h := d4ThreeCheck_eq_true
  simpa only [d4ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem d4ThreeOrbit_check : orbitCheck3 .D4 d4ThreeReps d4ThreeOrbit = true :=
  d4ThreeCheck_spec.1

theorem card_kernelPosStabilizer_le_D4_three :
    ∀ ρ < d4ThreeReps.length,
    Nat.card (kernelPosStabilizer (triChar (τ := .D4) (vec3 (d4ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : d4ThreeReps.length = 6 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab4 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := d4ThreeCheck_spec.2 d4ThreeStab5 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le d4Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_D4_three
    (χ : Multiplicative (Fin Tag.D4.rank → ℤ) →* Z3) :
    charStabilizer χ = kernelWeylGroup χ :=
  charStabilizer_eq_of_card_le_one
    (card_charQuotient_le_of_orbitCheck3 d4ThreeOrbit_check card_kernelPosStabilizer_le_D4_three χ)

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_D4_three
    {K : Type} [Field K]
    (a : Fin Tag.D4.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (fun χ => (charStabilizer_eq_kernelWeylGroup_D4_three χ).le) a h3

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
