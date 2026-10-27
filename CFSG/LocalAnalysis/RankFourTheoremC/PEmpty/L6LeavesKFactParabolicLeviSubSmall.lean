module

public import CFSG.RankThree.Chevalley.OddRankOneReeTitsModels
public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideBase
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Quasithin.Recognition.CertTitsTwoLocal
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem not_dvd_two_pow_mul_small {p a c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hc : c = 1 ∨ c = 3) : ¬ p ∣ 2 ^ a * c := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h2
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    omega
  · rcases hc with rfl | rfl
    · have := Nat.le_of_dvd Nat.one_pos h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h2
      omega

theorem leviSubAt_of_overgroup_orders {S : Type} [Group S] [Finite S] (L : Set ℕ)
    (hL : ∀ (T : Sylow 2 S) (P : Subgroup S), P ≠ ⊤ → (T : Subgroup S) ≤ P →
      Nat.card P ∈ L)
    (hLp : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 →
      ∀ n ∈ L, ¬ p ∣ n) : LeviSubAt S := by
  intro K₀ p hB hp h5 hrank hpar hne hsyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, U, hU, hUN⟩ := hpar
  obtain ⟨-, hU2, hUdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hU
  rw [Subgroup.relIndex_top_right] at hUdvd
  have hUK : U ≤ K₀ := fun u hu => hUN ⟨Subgroup.le_normalizer hu, mem_top u⟩
  have hcard := hL (hU2.toSylow hUdvd) K₀ hne (by rw [IsPGroup.toSylow_coe]; exact hUK)
  exact absurd (dvd_card_of_sylow_hyp hp hsyl) (hLp p hp h5 hrank _ hcard)

theorem leviSubAt_alt6 : LeviSubAt ↥(alternatingGroup (Fin 6)) := by
  refine leviSubAt_of_overgroup_orders {8, 24} ?_ ?_
  · intro T P hP hTP
    have hT : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup ↥(alternatingGroup (Fin 6))) ⊤ :=
      CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow T
    rcases CFSG.Quasithin.SmithC27.card_eq_of_sylow_le_alt6 hT hTP with h | h | h
    · simp [h]
    · simp [h]
    · exact absurd (Subgroup.eq_top_of_card_eq P
        (by rw [h, CFSG.QuasithinUnique.Setup.X3.card_alt6])) hP
  · intro p hp h5 _ n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · simpa using not_dvd_two_pow_mul_small (a := 3) (c := 1) hp h5 (Or.inl rfl)
    · simpa using not_dvd_two_pow_mul_small (a := 3) (c := 3) hp h5 (Or.inr rfl)

theorem leviSubAt_of_alt6 {S : Type} [Group S] [Finite S]
    (e : Nonempty (S ≃* alternatingGroup (Fin 6))) : LeviSubAt S := by
  obtain ⟨e⟩ := e
  exact LeviSubAt.of_mulEquiv e leviSubAt_alt6

section U33


theorem leviSubAt_u33 {S : Type} [Group S] [Finite S] (h : StatedClassicalModel S .PSU 3 3 1) :
    LeviSubAt S := by
  obtain ⟨eK⟩ := CFSG.Quasithin.SBc17.nonempty_mulEquiv_PSU3_of_isPSU h
  obtain ⟨eU⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  refine leviSubAt_of_overgroup_orders {32, 96} ?_ ?_
  · intro T P hP hTP
    exact KSeitz.card_mem_of_overgroups (eK.trans eU.symm) CFSG.Quasithin.u33SylowT {32, 96}
      (fun X hX => by
        rw [CFSG.Quasithin.coe_u33SylowT] at hX
        rcases CFSG.Quasithin.u33Data.lattice X hX with h | h | h | h
        · right
          rw [h, CFSG.Quasithin.u33_card_T]
          simp
        · right
          rw [h, CFSG.Quasithin.H13.U3.card_u33_A]
          simp
        · right
          rw [h, CFSG.Quasithin.H13.U3.card_u33_B]
          simp
        · left
          exact h) T hP hTP
  · intro p hp h5 _ n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · simpa using not_dvd_two_pow_mul_small (a := 5) (c := 1) hp h5 (Or.inl rfl)
    · simpa using not_dvd_two_pow_mul_small (a := 5) (c := 3) hp h5 (Or.inr rfl)

end U33

section Tits


theorem leviSubAt_tits {S : Type} [Group S] [Finite S] {f : ℕ} (h : ReeTitsModel S .Tits 2 f) :
    LeviSubAt S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 f h
  have hm5 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup S) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.Chevalley.two_le_pRank_five_of_titsModel h
  have hSp : IsPGroup 2 CFSG.Quasithin.titsSD :=
    IsPGroup.of_card (n := 11) (by rw [CFSG.Quasithin.card_titsSD]; norm_num)
  have hSi : ¬ 2 ∣ CFSG.Quasithin.titsSD.index := by
    have h := Subgroup.card_mul_index CFSG.Quasithin.titsSD
    rw [CFSG.Quasithin.card_titsSD, CFSG.Sporadic.Schreier.Tits.card_titsD] at h
    have : CFSG.Quasithin.titsSD.index = 8775 := by omega
    rw [this]
    decide
  refine leviSubAt_of_overgroup_orders {2048, 10240, 6144} ?_ ?_
  · intro T P hP hTP
    exact KSeitz.card_mem_of_overgroups φ (hSp.toSylow hSi) {2048, 10240, 6144}
      (fun X hX => by
        rw [IsPGroup.toSylow_coe] at hX
        rcases CFSG.Quasithin.titsD_overgroups X hX with h | h | h | h
        · right
          rw [h, CFSG.Quasithin.card_titsSD]
          simp
        · right
          rw [h, CFSG.Quasithin.card_titsHD]
          simp
        · right
          rw [h, CFSG.Quasithin.card_titsND]
          simp
        · left
          exact h) T hP hTP
  · intro p hp h5 hrank n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · simpa using not_dvd_two_pow_mul_small (a := 11) (c := 1) hp h5 (Or.inl rfl)
    · intro hpn
      have h' : p ∣ 2 ^ 11 * 5 := by simpa using hpn
      rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
        omega
      · have hp5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h2
        subst hp5
        omega
    · simpa using not_dvd_two_pow_mul_small (a := 11) (c := 3) hp h5 (Or.inr rfl)

end Tits

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
