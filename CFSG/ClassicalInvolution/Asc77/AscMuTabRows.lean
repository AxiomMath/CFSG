module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind
public import CFSG.ClassicalInvolution.Asc77.AscMuTabWyl
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

namespace MuTab

section Val

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {W : Subgroup X}

theorem natCard_eq_of_muIso {Y Z : Type} [Group Y] [Group Z] (hY : MuIso Φ W Y)
    (hZ : MuIso Φ W Z) : Nat.card Y = Nat.card Z := by
  rw [← muIso_natCard hY, ← muIso_natCard hZ]

theorem muIso_iff_of_val {κ : MuKind} (h : MuVal Φ W κ) :
    (MuIsoZ2 Φ W ↔ κ = .z2) ∧ (MuIsoS3 Φ W ↔ κ = .s3) ∧ (MuIsoE4 Φ W ↔ κ = .e4) ∧
      (MuIsoS4 Φ W ↔ κ = .s4) := by
  have c2 := card_z2
  have c3 := card_perm3
  have c4 := card_klein
  have c24 := card_perm4
  cases κ with
  | z2 =>
    refine ⟨iff_of_true h rfl, ?_, ?_, ?_⟩
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
  | s3 =>
    refine ⟨?_, iff_of_true h rfl, ?_, ?_⟩
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
  | e4 =>
    refine ⟨?_, ?_, iff_of_true h rfl, ?_⟩
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
  | s4 =>
    refine ⟨?_, ?_, ?_, iff_of_true h rfl⟩
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
    · exact iff_of_false (fun h' => by have := natCard_eq_of_muIso h h'; omega) (by simp)
  | wyl =>
    obtain ⟨φ⟩ := h
    refine ⟨iff_of_false (fun ⟨ψ⟩ => not_wyl_equiv_z2 ⟨φ.symm.trans ψ⟩) (by simp),
      iff_of_false (fun ⟨ψ⟩ => not_wyl_equiv_perm3 ⟨φ.symm.trans ψ⟩) (by simp),
      iff_of_false (fun ⟨ψ⟩ => not_wyl_equiv_klein ⟨φ.symm.trans ψ⟩) (by simp),
      iff_of_false (fun ⟨ψ⟩ => not_wyl_equiv_perm4 ⟨φ.symm.trans ψ⟩) (by simp)⟩
  | big10 => exact ⟨iff_of_false h.1 (by simp), iff_of_false h.2.1 (by simp),
      iff_of_false h.2.2.1 (by simp), iff_of_false h.2.2.2 (by simp)⟩
  | large => exact ⟨iff_of_false h.1 (by simp), iff_of_false h.2.1 (by simp),
      iff_of_false h.2.2.1 (by simp), iff_of_false h.2.2.2 (by simp)⟩

theorem muIsoWyl_of_val {κ : MuKind} (h : MuVal Φ W κ) :
    (κ = .wyl → MuIsoWylD4 Φ W) ∧ (κ ≠ .wyl → κ ≠ .big10 → κ ≠ .large → ¬ MuIsoWylD4 Φ W) := by
  cases κ with
  | wyl => exact ⟨fun _ => h, fun h' => absurd rfl h'⟩
  | z2 => exact ⟨fun h' => absurd h' (by simp), fun _ _ _ ⟨ψ⟩ => by
      obtain ⟨φ⟩ := h
      exact not_wyl_equiv_z2 ⟨ψ.symm.trans φ⟩⟩
  | s3 => exact ⟨fun h' => absurd h' (by simp), fun _ _ _ ⟨ψ⟩ => by
      obtain ⟨φ⟩ := h
      exact not_wyl_equiv_perm3 ⟨ψ.symm.trans φ⟩⟩
  | e4 => exact ⟨fun h' => absurd h' (by simp), fun _ _ _ ⟨ψ⟩ => by
      obtain ⟨φ⟩ := h
      exact not_wyl_equiv_klein ⟨ψ.symm.trans φ⟩⟩
  | s4 => exact ⟨fun h' => absurd h' (by simp), fun _ _ _ ⟨ψ⟩ => by
      obtain ⟨φ⟩ := h
      exact not_wyl_equiv_perm4 ⟨ψ.symm.trans φ⟩⟩
  | big10 => exact ⟨fun h' => absurd h' (by simp), fun _ h' => absurd rfl h'⟩
  | large => exact ⟨fun h' => absurd h' (by simp), fun _ _ h' => absurd rfl h'⟩

end Val

section Kinds

theorem muKind_eq_z2_iff (π : Bool) (t : StatedLieTag) (k : ℕ) :
    muKind π t k = .z2 ↔ (t = .PSL ∧ k = 3 ∧ π = false) ∨ (t = .PSU ∧ k = 3 ∧ π = true) := by
  cases t <;> cases π <;> simp [muKind] <;> split_ifs <;> simp_all

theorem muKind_eq_s3_iff (π : Bool) (t : StatedLieTag) (k : ℕ) :
    muKind π t k = .s3 ↔ (t = .PSL ∧ k = 3 ∧ π = true) ∨ (t = .PSU ∧ k = 3 ∧ π = false) ∨
      (t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0) := by
  cases t <;> cases π <;> simp [muKind] <;> split_ifs <;> simp_all

theorem muKind_eq_e4_iff (π : Bool) (t : StatedLieTag) (k : ℕ) :
    muKind π t k = .e4 ↔ (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4 ∧ π = false) ∨
      (t = .PSU ∧ k = 4 ∧ π = true) ∨ (t = .PSL ∧ k = 5 ∧ π = false) ∨
      (t = .PSU ∧ k = 5 ∧ π = true) := by
  cases t <;> cases π <;> simp [muKind] <;> split_ifs <;> simp_all

theorem muKind_eq_s4_iff (π : Bool) (t : StatedLieTag) (k : ℕ) :
    muKind π t k = .s4 ↔ (t = .PSL ∧ k = 4 ∧ π = true) ∨ (t = .PSU ∧ k = 4 ∧ π = false) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaMinus ∧ k = 4) := by
  cases t <;> cases π <;> simp [muKind] <;> split_ifs <;> simp_all

theorem muKind_eq_wyl_iff (π : Bool) (t : StatedLieTag) (k : ℕ) :
    muKind π t k = .wyl ↔ t = .POmegaPlus ∧ k = 4 := by
  cases t <;> cases π <;> simp [muKind] <;> split_ifs <;> simp_all

end Kinds

section Orth

theorem isOrth_five (ε : Bool) (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 5 ε t n ↔ t = .PSp ∧ n = 2 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;>
      first | exact ⟨h1, h2⟩ | omega
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨rfl, h1, h2⟩

theorem isOrth_six_true (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 6 true t n ↔ t = .PSL ∧ n = 4 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h1, h2⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;>
      first | exact ⟨h1, h2⟩ | omega | simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)

theorem isOrth_six_false (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 6 false t n ↔ t = .PSU ∧ n = 4 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;>
      first | exact ⟨h1, h2⟩ | omega | simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩))

theorem isOrth_seven (ε : Bool) (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 7 ε t n ↔ t = .POmegaOdd ∧ n = 3 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h1, h2⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩) <;>
      first | exact ⟨h1, by omega⟩ | omega
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, h1, by omega⟩)))

theorem isOrth_eight_true (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 8 true t n ↔ t = .POmegaPlus ∧ n = 4 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, h1, h2⟩ | ⟨-, -, h, -⟩) <;>
      first | exact ⟨h1, by omega⟩ | omega | simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, h1, by omega⟩))))

theorem isOrth_eight_false (t : StatedLieTag) (n : ℕ) :
    IsOrthTag 8 false t n ↔ t = .POmegaMinus ∧ n = 4 := by
  unfold IsOrthTag
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h1, h2⟩) <;>
      first | exact ⟨h1, by omega⟩ | omega | simp at h
  · rintro ⟨h1, h2⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by norm_num, by norm_num, rfl, h1, by omega⟩))))

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem hasOrthType_five (ε : Bool) : HasOrthType p f Φ 5 ε ↔ HasLieType p f Φ .PSp 2 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_five ε t n).mp hI
    exact hL
  · exact fun h => ⟨.PSp, 2, (isOrth_five ε _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthType_six_true : HasOrthType p f Φ 6 true ↔ HasLieType p f Φ .PSL 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_six_true t n).mp hI
    exact hL
  · exact fun h => ⟨.PSL, 4, (isOrth_six_true _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthType_six_false : HasOrthType p f Φ 6 false ↔ HasLieType p f Φ .PSU 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_six_false t n).mp hI
    exact hL
  · exact fun h => ⟨.PSU, 4, (isOrth_six_false _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthType_seven (ε : Bool) :
    HasOrthType p f Φ 7 ε ↔ HasLieType p f Φ .POmegaOdd 3 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_seven ε t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaOdd, 3, (isOrth_seven ε _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthType_eight_true :
    HasOrthType p f Φ 8 true ↔ HasLieType p f Φ .POmegaPlus 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_eight_true t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaPlus, 4, (isOrth_eight_true _ _).mpr ⟨rfl, rfl⟩, h⟩

theorem hasOrthType_eight_false :
    HasOrthType p f Φ 8 false ↔ HasLieType p f Φ .POmegaMinus 4 := by
  constructor
  · rintro ⟨t, n, hI, hL⟩
    obtain ⟨rfl, rfl⟩ := (isOrth_eight_false t n).mp hI
    exact hL
  · exact fun h => ⟨.POmegaMinus, 4, (isOrth_eight_false _ _).mpr ⟨rfl, rfl⟩, h⟩

end Orth

section Datum

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_datum_of_hasLieType (hS : TransSection p f Φ) {t : StatedLieTag} {k : ℕ}
    (h : HasLieType p f Φ t k) : ∃ e, Nonempty (Ih8Model p f Φ t k e) := by
  obtain ⟨D, hcard, i, ht, hk⟩ := h
  have hsurj := D.hom_surjective_of_gen hcard hS.gen i
  subst ht hk
  exact ⟨D.exp i, ⟨{ isFundTag := D.isFundTag i
                     admissible := D.admissible i
                     exp_eq := D.exp_eq i
                     ψ := D.hom i
                     ker_le_center := D.ker_le_center i
                     surj := hsurj
                     cls := D.cls i
                     cls_sub := fun _ hR => hR.1
                     mem_iff := fun _ => D.mem_iff_exists_cls hcard i
                     cls_conj := fun _ hR g => D.cls_conj hS.hyp.conjInvariant i hR g }⟩⟩

end Datum

section Clauses

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)} {W : Subgroup X}

@[expose] def MuValues (p f : ℕ) [Fact p.Prime] (π : Bool) (Φ : Set (Subgroup X))
    (W : Subgroup X) : Prop :=
  ∀ t k, HasLieType p f Φ t k → MuVal Φ W (muKind π t k)

theorem clause_general {π : Bool} (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f π Φ W)
    {P : Prop} {κ : MuKind} (hP : ∀ κ', MuVal Φ W κ' → (P ↔ κ' = κ))
    {S : StatedLieTag → ℕ → Prop} (hS : ∀ t k, muKind π t k = κ ↔ S t k) :
    P ↔ ∃ t k, S t k ∧ HasLieType p f Φ t k := by
  constructor
  · intro hp
    obtain ⟨t, k, hL⟩ := hex
    exact ⟨t, k, (hS t k).mp ((hP _ (hv t k hL)).mp hp), hL⟩
  · rintro ⟨t, k, hSt, hL⟩
    exact (hP _ (hv t k hL)).mpr ((hS t k).mpr hSt)

theorem clause_z2 (π : Bool) (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f π Φ W) :
    MuIsoZ2 Φ W ↔ (if π then HasLieType p f Φ .PSU 3 else HasLieType p f Φ .PSL 3) := by
  rw [clause_general hex hv (fun κ' h => (muIso_iff_of_val h).1) (muKind_eq_z2_iff π)]
  cases π <;> simp

theorem clause_s3 (π : Bool) (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f π Φ W) :
    MuIsoS3 Φ W ↔ ((if π then HasLieType p f Φ .PSL 3 else HasLieType p f Φ .PSU 3) ∨
      HasLieType p f Φ .G2 0 ∨ HasLieType p f Φ .trialityD4 0) := by
  rw [clause_general hex hv (fun κ' h => (muIso_iff_of_val h).2.1) (muKind_eq_s3_iff π)]
  cases π <;> simp [or_and_right, exists_or]

theorem clause_e4 (π : Bool) (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f π Φ W) :
    MuIsoE4 Φ W ↔ (HasOrthType p f Φ 5 true ∨ HasOrthType p f Φ 6 (!π) ∨
      (if π then HasLieType p f Φ .PSU 5 else HasLieType p f Φ .PSL 5)) := by
  rw [clause_general hex hv (fun κ' h => (muIso_iff_of_val h).2.2.1) (muKind_eq_e4_iff π),
    hasOrthType_five]
  cases π <;> simp [hasOrthType_six_true, hasOrthType_six_false, or_and_right, exists_or]

theorem clause_s4 (π : Bool) (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f π Φ W) :
    MuIsoS4 Φ W ↔
      (HasOrthType p f Φ 6 π ∨ HasOrthType p f Φ 7 true ∨ HasOrthType p f Φ 8 false) := by
  rw [clause_general hex hv (fun κ' h => (muIso_iff_of_val h).2.2.2) (muKind_eq_s4_iff π),
    hasOrthType_seven, hasOrthType_eight_false]
  cases π <;> simp [hasOrthType_six_true, hasOrthType_six_false, or_and_right, exists_or]

theorem clause_wyl (π : Bool) (hv : MuValues p f π Φ W) (h : HasOrthType p f Φ 8 true) :
    MuIsoWylD4 Φ W := by
  have hL := hasOrthType_eight_true.mp h
  have := hv _ _ hL
  have hk : muKind π .POmegaPlus 4 = .wyl := (muKind_eq_wyl_iff π _ _).mpr ⟨rfl, rfl⟩
  rw [hk] at this
  exact this

theorem kind_of_wyl {π : Bool} (hv : MuValues p f π Φ W) (hw : MuIsoWylD4 Φ W) {t : StatedLieTag}
    {k : ℕ} (hL : HasLieType p f Φ t k) :
    muKind π t k = .wyl ∨ muKind π t k = .big10 ∨ muKind π t k = .large := by
  by_contra hcon
  push Not at hcon
  exact (muIsoWyl_of_val (hv t k hL)).2 hcon.1 hcon.2.1 hcon.2.2 hw

theorem clause_wyl_converse (π : Bool) (hv : MuValues p f π Φ W)
    (h6 : Disconnected.DEdgeless Φ → HasLieType p f Φ .PSL 3 ∨ HasLieType p f Φ .PSU 3 ∨
      HasLieType p f Φ .G2 0 ∨ HasLieType p f Φ .trialityD4 0)
    (h8 : ¬ Disconnected.DEdgeless Φ → ¬ Disconnected.DConnected Φ →
      ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType p f Φ d ε)
    (hnc : ¬ Disconnected.DConnected Φ) (hw : MuIsoWylD4 Φ W) : HasOrthType p f Φ 8 true := by
  by_cases hE : Disconnected.DEdgeless Φ
  · exfalso
    rcases h6 hE with hL | hL | hL | hL <;> rcases kind_of_wyl hv hw hL with h | h | h <;>
      cases π <;> simp [muKind] at h
  · obtain ⟨d, ε, hd5, hd8, hO⟩ := h8 hE hnc
    interval_cases d
    · exfalso
      rcases kind_of_wyl hv hw ((hasOrthType_five ε).mp hO) with h | h | h <;>
        cases π <;> simp [muKind] at h
    · exfalso
      cases ε
      · rcases kind_of_wyl hv hw (hasOrthType_six_false.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
      · rcases kind_of_wyl hv hw (hasOrthType_six_true.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
    · exfalso
      rcases kind_of_wyl hv hw ((hasOrthType_seven ε).mp hO) with h | h | h <;>
        cases π <;> simp [muKind] at h
    · cases ε
      · exfalso
        rcases kind_of_wyl hv hw (hasOrthType_eight_false.mp hO) with h | h | h <;>
          cases π <;> simp [muKind] at h
      · exact hO

theorem muRows_of_values (hex : ∃ t k, HasLieType p f Φ t k) (hv : MuValues p f (piSign p f) Φ W)
    (h6 : Disconnected.DEdgeless Φ → HasLieType p f Φ .PSL 3 ∨ HasLieType p f Φ .PSU 3 ∨
      HasLieType p f Φ .G2 0 ∨ HasLieType p f Φ .trialityD4 0)
    (h8 : ¬ Disconnected.DEdgeless Φ → ¬ Disconnected.DConnected Φ →
      ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType p f Φ d ε) : MuRows p f Φ W :=
  ⟨clause_z2 _ hex hv, clause_s3 _ hex hv, clause_e4 _ hex hv, clause_s4 _ hex hv,
    fun h => clause_wyl _ hv h, fun hnc hw => clause_wyl_converse _ hv h6 h8 hnc hw⟩

end Clauses

end MuTab

end CFSG.ClassicalInvolution.Asc77
