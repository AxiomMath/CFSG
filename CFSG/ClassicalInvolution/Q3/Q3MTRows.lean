module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabRows
public import CFSG.ClassicalInvolution.Uniform.U3Thm6

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform

section Orth

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}


theorem hasOrthTypeU_five (ε : Bool) : HasOrthTypeU p f Ω 5 ε ↔ HasLieTypeU p f Ω .PSp 2 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_five ε t n).mp hI
    exact hL
  · exact fun h => ⟨.PSp, 2, (isOrth_five ε _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthTypeU_six_true : HasOrthTypeU p f Ω 6 true ↔ HasLieTypeU p f Ω .PSL 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_six_true t n).mp hI
    exact hL
  · exact fun h => ⟨.PSL, 4, (isOrth_six_true _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthTypeU_six_false : HasOrthTypeU p f Ω 6 false ↔ HasLieTypeU p f Ω .PSU 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_six_false t n).mp hI
    exact hL
  · exact fun h => ⟨.PSU, 4, (isOrth_six_false _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthTypeU_seven (ε : Bool) :
    HasOrthTypeU p f Ω 7 ε ↔ HasLieTypeU p f Ω .POmegaOdd 3 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_seven ε t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaOdd, 3, (isOrth_seven ε _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthTypeU_eight_true :
    HasOrthTypeU p f Ω 8 true ↔ HasLieTypeU p f Ω .POmegaPlus 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_eight_true t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaPlus, 4, (isOrth_eight_true _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthTypeU_eight_false :
    HasOrthTypeU p f Ω 8 false ↔ HasLieTypeU p f Ω .POmegaMinus 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_eight_false t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaMinus, 4, (isOrth_eight_false _ _).mpr ⟨rfl, rfl⟩, h⟩

end Orth

section Clauses

open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}


@[expose] def HasTypeU (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Prop :=
  (∃ t k, HasLieTypeU p f Ω t k) ∨ HasM11TypeU p f Ω

@[expose] def MuValuesU (p f : ℕ) [Fact p.Prime] (π : Bool) (Ω : Set (Subgroup G))
    (W : Subgroup G) : Prop :=
  (∀ t k, HasLieTypeU p f Ω t k → MuVal Ω W (muKind π t k)) ∧
    (HasM11TypeU p f Ω → MuVal Ω W .z2)

theorem clause_generalU {π : Bool} (hex : HasTypeU p f Ω) (hv : MuValuesU p f π Ω W)
    {P : Prop} {κ : MuKind} (hκ : κ ≠ .z2) (hP : ∀ κ', MuVal Ω W κ' → (P ↔ κ' = κ))
    {S : StatedLieTag → ℕ → Prop} (hS : ∀ t k, muKind π t k = κ ↔ S t k) :
    P ↔ ∃ t k, S t k ∧ HasLieTypeU p f Ω t k := by
  constructor
  · intro hp
    rcases hex with ⟨t, k, hL⟩ | hM
    · exact ⟨t, k, (hS t k).mp ((hP _ (hv.1 t k hL)).mp hp), hL⟩
    · exact absurd ((hP _ (hv.2 hM)).mp hp).symm hκ
  · rintro ⟨t, k, hSt, hL⟩
    exact (hP _ (hv.1 t k hL)).mpr ((hS t k).mpr hSt)

theorem clause_z2U (π : Bool) (hex : HasTypeU p f Ω) (hv : MuValuesU p f π Ω W) :
    MuIsoZ2 Ω W ↔ ((if π then HasLieTypeU p f Ω .PSU 3 else HasLieTypeU p f Ω .PSL 3) ∨
      HasM11TypeU p f Ω) := by
  constructor
  · intro h
    rcases hex with ⟨t, k, hL⟩ | hM
    · have hk := ((muIso_iff_of_val (hv.1 t k hL)).1).mp h
      rcases (muKind_eq_z2_iff π t k).mp hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl hL
      · exact Or.inl hL
    · exact Or.inr hM
  · rintro (h | hM)
    · cases π
      · exact ((muIso_iff_of_val (hv.1 _ _ h)).1).mpr
          ((muKind_eq_z2_iff false _ _).mpr (Or.inl ⟨rfl, rfl, rfl⟩))
      · exact ((muIso_iff_of_val (hv.1 _ _ h)).1).mpr
          ((muKind_eq_z2_iff true _ _).mpr (Or.inr ⟨rfl, rfl, rfl⟩))
    · exact hv.2 hM

theorem clause_s3U (π : Bool) (hex : HasTypeU p f Ω) (hv : MuValuesU p f π Ω W) :
    MuIsoS3 Ω W ↔ ((if π then HasLieTypeU p f Ω .PSL 3 else HasLieTypeU p f Ω .PSU 3) ∨
      HasLieTypeU p f Ω .G2 0 ∨ HasLieTypeU p f Ω .trialityD4 0) := by
  rw [clause_generalU hex hv (by decide) (fun κ' h => (muIso_iff_of_val h).2.1)
    (muKind_eq_s3_iff π)]
  cases π <;> simp [or_and_right, exists_or]

theorem clause_e4U (π : Bool) (hex : HasTypeU p f Ω) (hv : MuValuesU p f π Ω W) :
    MuIsoE4 Ω W ↔ (HasOrthTypeU p f Ω 5 true ∨ HasOrthTypeU p f Ω 6 (!π) ∨
      (if π then HasLieTypeU p f Ω .PSU 5 else HasLieTypeU p f Ω .PSL 5)) := by
  rw [clause_generalU hex hv (by decide) (fun κ' h => (muIso_iff_of_val h).2.2.1)
    (muKind_eq_e4_iff π), hasOrthTypeU_five]
  cases π <;> simp [hasOrthTypeU_six_true, hasOrthTypeU_six_false, or_and_right, exists_or]

theorem clause_s4U (π : Bool) (hex : HasTypeU p f Ω) (hv : MuValuesU p f π Ω W) :
    MuIsoS4 Ω W ↔
      (HasOrthTypeU p f Ω 6 π ∨ HasOrthTypeU p f Ω 7 true ∨ HasOrthTypeU p f Ω 8 false) := by
  rw [clause_generalU hex hv (by decide) (fun κ' h => (muIso_iff_of_val h).2.2.2)
    (muKind_eq_s4_iff π), hasOrthTypeU_seven, hasOrthTypeU_eight_false]
  cases π <;> simp [hasOrthTypeU_six_true, hasOrthTypeU_six_false, or_and_right, exists_or]

theorem clause_wylU (π : Bool) (hv : MuValuesU p f π Ω W) (h : HasOrthTypeU p f Ω 8 true) :
    MuIsoWylD4 Ω W := by
  have hL := hasOrthTypeU_eight_true.mp h
  have := hv.1 _ _ hL
  have hk : muKind π .POmegaPlus 4 = .wyl := (muKind_eq_wyl_iff π _ _).mpr ⟨rfl, rfl⟩
  rw [hk] at this
  exact this

theorem kind_of_wylU {π : Bool} (hv : MuValuesU p f π Ω W) (hw : MuIsoWylD4 Ω W)
    {t : StatedLieTag} {k : ℕ} (hL : HasLieTypeU p f Ω t k) :
    muKind π t k = .wyl ∨ muKind π t k = .big10 ∨ muKind π t k = .large := by
  by_contra hcon
  push Not at hcon
  exact (muIsoWyl_of_val (hv.1 t k hL)).2 hcon.1 hcon.2.1 hcon.2.2 hw

theorem clause_wylU_converse (π : Bool) (hv : MuValuesU p f π Ω W)
    (h6 : Disconnected.DEdgeless Ω → HasLieTypeU p f Ω .PSL 3 ∨ HasLieTypeU p f Ω .PSU 3 ∨
      HasLieTypeU p f Ω .G2 0 ∨ HasLieTypeU p f Ω .trialityD4 0 ∨ HasM11TypeU p f Ω)
    (h8 : ¬ Disconnected.DEdgeless Ω → ¬ Disconnected.DConnected Ω →
      ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthTypeU p f Ω d ε)
    (hnc : ¬ Disconnected.DConnected Ω) (hw : MuIsoWylD4 Ω W) : HasOrthTypeU p f Ω 8 true := by
  by_cases hE : Disconnected.DEdgeless Ω
  · exfalso
    rcases h6 hE with hL | hL | hL | hL | hM
    · rcases kind_of_wylU hv hw hL with h | h | h <;> cases π <;> simp [muKind] at h
    · rcases kind_of_wylU hv hw hL with h | h | h <;> cases π <;> simp [muKind] at h
    · rcases kind_of_wylU hv hw hL with h | h | h <;> cases π <;> simp [muKind] at h
    · rcases kind_of_wylU hv hw hL with h | h | h <;> cases π <;> simp [muKind] at h
    · exact (muIsoWyl_of_val (κ := .z2) (hv.2 hM)).2 (by decide) (by decide) (by decide) hw
  · obtain ⟨d, ε, hd5, hd8, hO⟩ := h8 hE hnc
    interval_cases d
    · exfalso
      rcases kind_of_wylU hv hw ((hasOrthTypeU_five ε).mp hO) with h | h | h <;>
        cases π <;> simp [muKind] at h
    · exfalso
      cases ε
      · rcases kind_of_wylU hv hw (hasOrthTypeU_six_false.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
      · rcases kind_of_wylU hv hw (hasOrthTypeU_six_true.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
    · exfalso
      rcases kind_of_wylU hv hw ((hasOrthTypeU_seven ε).mp hO) with h | h | h <;>
        cases π <;> simp [muKind] at h
    · cases ε
      · exfalso
        rcases kind_of_wylU hv hw (hasOrthTypeU_eight_false.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
      · exact hO

theorem muRowsU_of_values (hex : HasTypeU p f Ω) (hv : MuValuesU p f (piSign p f) Ω W)
    (h6 : Disconnected.DEdgeless Ω → HasLieTypeU p f Ω .PSL 3 ∨ HasLieTypeU p f Ω .PSU 3 ∨
      HasLieTypeU p f Ω .G2 0 ∨ HasLieTypeU p f Ω .trialityD4 0 ∨ HasM11TypeU p f Ω)
    (h8 : ¬ Disconnected.DEdgeless Ω → ¬ Disconnected.DConnected Ω →
      ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthTypeU p f Ω d ε) :
    (MuIsoZ2 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSU 3
        else HasLieTypeU p f Ω .PSL 3) ∨ HasM11TypeU p f Ω)) ∧
    (MuIsoS3 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSL 3
        else HasLieTypeU p f Ω .PSU 3) ∨ HasLieTypeU p f Ω .G2 0 ∨
        HasLieTypeU p f Ω .trialityD4 0)) ∧
    (MuIsoE4 Ω W ↔ (HasOrthTypeU p f Ω 5 true ∨ HasOrthTypeU p f Ω 6 (!piSign p f) ∨
        (if piSign p f then HasLieTypeU p f Ω .PSU 5 else HasLieTypeU p f Ω .PSL 5))) ∧
    (MuIsoS4 Ω W ↔ (HasOrthTypeU p f Ω 6 (piSign p f) ∨ HasOrthTypeU p f Ω 7 true ∨
        HasOrthTypeU p f Ω 8 false)) ∧
    (HasOrthTypeU p f Ω 8 true → MuIsoWylD4 Ω W) ∧
    (¬ Disconnected.DConnected Ω → MuIsoWylD4 Ω W → HasOrthTypeU p f Ω 8 true) :=
  ⟨clause_z2U _ hex hv, clause_s3U _ hex hv, clause_e4U _ hex hv, clause_s4U _ hex hv,
    fun h => clause_wylU _ hv h, fun hnc hw => clause_wylU_converse _ hv h6 h8 hnc hw⟩

end Clauses

section TypeExists

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


theorem hasTypeU_three_of_citBelowT {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) (hlt : Nat.card G < n)
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty) :
    HasTypeU 3 1 Ω := by
  obtain ⟨D, hcard⟩ := exists_omegaLieU_of_simple hn hlt hΩ hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · exact Or.inl ⟨t, k, ⟨D, hcard, i, e, he, ht, hadm, hc⟩⟩
  · exfalso
    obtain ⟨K, hK⟩ := hne
    obtain ⟨z, hz⟩ := hΩ.classical K hK
    obtain ⟨j, R, hR, hKR⟩ := D.fundamental K hK
    obtain rfl : j = i := Fin.ext (by have := i.2; have := j.2; omega)
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom i) hR
    have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
    have hsurj := D.hom_surjective_of_simple hΩ ⟨K, hK⟩ i
    have hKtop : K = ⊤ := by
      rw [hKR, ← hRR, hR'top, Subgroup.map_top, range_castHom]
      exact MonoidHom.range_eq_top.mpr hsurj
    rw [hKtop] at hz
    exact hz.false_of_top
  · exact Or.inr ⟨h3, D, hcard, i, hc⟩

end TypeExists

end CFSG.ClassicalInvolution.Q3.Q3MT
