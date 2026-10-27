module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot

variable {n : ℕ} {F : Type} [Field F]

theorem elt_short_mem_pos {k : Fin n} (hk : k.val + 1 < n) (c : F) :
    elt (.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk)) c ∈ rootGroup n F (Pi.single k 1) :=
  elt_mem_rootGroup (stdVec_shortPos_eq hk) c

theorem elt_short_mem_neg {k : Fin n} (hk : k.val + 1 < n) (c : F) :
    elt (.difference ⟨k.val + 1, hk⟩ k (ne_succ' hk).symm) c ∈ rootGroup n F (-Pi.single k 1) :=
  elt_mem_rootGroup (stdVec_shortNeg_eq hk) c

theorem elt_long_mem_pos {k : Fin n} (hk : ¬ k.val + 1 < n) (c : F) :
    elt (.positiveLong k) c ∈ rootGroup n F (Pi.single k 1) :=
  elt_mem_rootGroup (stdVec_positiveLong_eq hk) c

theorem elt_long_mem_neg {k : Fin n} (hk : ¬ k.val + 1 < n) (c : F) :
    elt (.negativeLong k) c ∈ rootGroup n F (-Pi.single k 1) :=
  elt_mem_rootGroup (stdVec_negativeLong_eq hk) c

theorem rankOne_sup_eq_top_two :
    rankOne (rootDatum 2 F).rootGroup (0 : Fin 2) ⊔ rankOne (rootDatum 2 F).rootGroup (1 : Fin 2) =
      ⊤ := by
  have h0 : (0 : Fin 2).val + 1 < 2 := by decide
  have h1 : ¬ (1 : Fin 2).val + 1 < 2 := by decide
  have m0p : ∀ c : F, elt (.difference (0 : Fin 2) ⟨(0 : Fin 2).val + 1, h0⟩ (ne_succ' h0)) c ∈
      rankOne (rootDatum 2 F).rootGroup (0 : Fin 2) ⊔ rankOne (rootDatum 2 F).rootGroup (1 : Fin 2) :=
    fun c => Subgroup.mem_sup_left (Subgroup.mem_sup_left (elt_short_mem_pos h0 c))
  have m0n : ∀ c : F, elt (.difference ⟨(0 : Fin 2).val + 1, h0⟩ (0 : Fin 2) (ne_succ' h0).symm) c ∈
      rankOne (rootDatum 2 F).rootGroup (0 : Fin 2) ⊔ rankOne (rootDatum 2 F).rootGroup (1 : Fin 2) :=
    fun c => Subgroup.mem_sup_left (Subgroup.mem_sup_right (elt_short_mem_neg h0 c))
  refine eq_top_of_adjacent_of_long_statedSp _ (1 : Fin 2) ?_ ?_ ?_
  · intro i j hij c hadj
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact m0p c
    · exact m0n c
    · exact absurd rfl hij
  · intro c
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (elt_long_mem_pos h1 c))
  · intro c
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (elt_long_mem_neg h1 c))

theorem elt_difference_congr {a a' b b' : Fin n} (ha : a = a') (hb : b = b') (h : a ≠ b)
    (h' : a' ≠ b') (c : F) :
    elt (.difference a b h) c = elt (.difference a' b' h') c := by
  subst ha hb
  rfl

def lastTwo (m : ℕ) : Fin 2 → Fin (m + 2) := fun k => Fin.natAdd m k

theorem lastTwo_injective (m : ℕ) : Function.Injective (lastTwo m) := fun a b h => by
  simpa [lastTwo, Fin.natAdd, Fin.ext_iff] using h

theorem spEmbed_rankOne_zero_le (m : ℕ) :
    (rankOne (rootDatum 2 F).rootGroup (0 : Fin 2)).map (spEmbed (lastTwo m) (lastTwo_injective m)) ≤
      rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (0 : Fin 2)) := by
  have h0 : (0 : Fin 2).val + 1 < 2 := by decide
  have h0' : (Fin.natAdd m (0 : Fin 2)).val + 1 < m + 2 := by simp
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortPos_eq h0)).1 hx
    rw [Subgroup.mem_comap, spEmbed_elt_difference]
    refine Subgroup.mem_sup_left ?_
    have := elt_short_mem_pos h0' c
    simp only [lastTwo]
    rw [elt_difference_congr (a' := Fin.natAdd m (0 : Fin 2))
      (b' := ⟨(Fin.natAdd m (0 : Fin 2)).val + 1, h0'⟩) rfl
      (Fin.ext (by simp)) _ (ne_succ' h0') c]
    exact this
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_shortNeg_eq h0)).1 hx
    rw [Subgroup.mem_comap, spEmbed_elt_difference]
    refine Subgroup.mem_sup_right ?_
    have := elt_short_mem_neg h0' c
    simp only [lastTwo]
    rw [elt_difference_congr (b' := Fin.natAdd m (0 : Fin 2))
      (a' := ⟨(Fin.natAdd m (0 : Fin 2)).val + 1, h0'⟩) (Fin.ext (by simp)) rfl _
      (ne_succ' h0').symm c]
    exact this

theorem spEmbed_rankOne_one_le (m : ℕ) :
    (rankOne (rootDatum 2 F).rootGroup (1 : Fin 2)).map (spEmbed (lastTwo m) (lastTwo_injective m)) ≤
      rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (1 : Fin 2)) := by
  have h1 : ¬ (1 : Fin 2).val + 1 < 2 := by decide
  have h1' : ¬ (Fin.natAdd m (1 : Fin 2)).val + 1 < m + 2 := by simp
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_positiveLong_eq h1)).1 hx
    rw [Subgroup.mem_comap, spEmbed_elt_positiveLong]
    exact Subgroup.mem_sup_left (elt_long_mem_pos h1' c)
  · obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_negativeLong_eq h1)).1 hx
    rw [Subgroup.mem_comap, spEmbed_elt_negativeLong]
    exact Subgroup.mem_sup_right (elt_long_mem_neg h1' c)

theorem range_spEmbed_le (m : ℕ) :
    (spEmbed (lastTwo m) (lastTwo_injective m) : StatedSp 2 F →* StatedSp (m + 2) F).range ≤
      rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (0 : Fin 2)) ⊔
        rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (1 : Fin 2)) := by
  rw [MonoidHom.range_eq_map, ← rankOne_sup_eq_top_two (F := F), Subgroup.map_sup]
  exact sup_le_sup (spEmbed_rankOne_zero_le m) (spEmbed_rankOne_one_le m)

theorem not_isPSolvable_perm_six : ¬ CFSG.HallHigman.IsPSolvable 3 (Equiv.Perm (Fin 6)) := by
  intro hsolv
  have h5 : 5 ≤ Nat.card (Fin 6) := by simp
  have hS : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    intro hc
    have a1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have a2 : (Equiv.swap (0 : Fin 6) 3 * Equiv.swap 0 4) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have := hc.is_comm.comm ⟨_, a1⟩ ⟨_, a2⟩
    have h : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2) * (Equiv.swap 0 3 * Equiv.swap 0 4) =
        (Equiv.swap 0 3 * Equiv.swap 0 4) * (Equiv.swap 0 1 * Equiv.swap 0 2) :=
      congrArg Subtype.val this
    exact absurd h (by decide)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact false_of_isPSolvable_surj (N := Equiv.Perm (Fin 6)) (H := alternatingGroup (Fin 6)) hsolv
    (MonoidHom.id _) Function.surjective_id hS hnc h3

theorem not_isPSolvable_statedSp_two [Finite F] (hF : Nat.card F = 2) :
    ¬ CFSG.HallHigman.IsPSolvable 3 (StatedSp 2 F) := by
  have := Fintype.ofFinite F
  obtain ⟨e⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := F) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  intro h
  exact not_isPSolvable_perm_six (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv e h)

theorem not_isPSolvable_lastTwo [Finite F] (hF : Nat.card F = 2) (m : ℕ) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (0 : Fin 2)) ⊔
        rankOne (rootDatum (m + 2) F).rootGroup (Fin.natAdd m (1 : Fin 2))) := by
  intro h
  have hle := range_spEmbed_le (F := F) m
  have h1 := OrdinaryProofs.PSolvableClosure.isPSolvable_of_le (p := 3) (X := StatedSp (m + 2) F)
    h hle
  have e := MonoidHom.ofInjective (spEmbed_injective (K := F) (σ := lastTwo m)
    (lastTwo_injective m))
  exact not_isPSolvable_statedSp_two hF
    (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv e.symm h1)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
