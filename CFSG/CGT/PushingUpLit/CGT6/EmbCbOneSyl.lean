module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneQ
import CFSG.Quasithin.Recognition.M12AscTrans

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X G T : Subgroup (MulAut V)} {t : MulAut V}
  {m : ℕ}

namespace OneCfg

variable (c : OneCfg G T Y t m X)

include c in
theorem exists_index_two : ∃ X₀ : Subgroup ↥G, X₀.Normal ∧ X₀.index = 2 ∧ c.tG ∉ X₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥G := NG G X with hN
  let tN : ↥N := ⟨c.tG, c.tG_mem_NG⟩
  have htN2 : orderOf tN = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      apply Subtype.ext
      show t ^ 2 = 1
      exact c.ht2
    · intro h
      exact c.ht1 (congrArg (fun z : ↥N => ((z : ↥G) : MulAut V)) h)
  have hP₀ : IsPGroup 2 ↥(Subgroup.zpowers tN) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htN2, pow_one])
  obtain ⟨S, hS⟩ := hP₀.exists_le_sylow
  set S' : Subgroup ↥G := (S : Subgroup ↥N).map N.subtype with hS'
  have htS : c.tG ∈ S' := ⟨tN, hS (Subgroup.mem_zpowers tN), rfl⟩
  have hS'p : IsPGroup 2 ↥S' := S.isPGroup'.map N.subtype
  have hS'N : S' ≤ N := Subgroup.map_subtype_le _
  have hcardS' : Nat.card ↥S' = 2 ^ (Nat.card ↥G).factorization 2 := by
    have h1 : Nat.card ↥S' = Nat.card ↥(S : Subgroup ↥N) :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [h1, S.card_eq_multiplicity]
    have h2 := Subgroup.card_mul_index N
    have hidx : ¬ 2 ∣ N.index := by
      have hodd : Odd N.index := c.odd_index_NG
      rw [Nat.odd_iff] at hodd
      omega
    have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    have hi0 : N.index ≠ 0 := Nat.card_pos.ne'
    have h3 := congrArg (fun n => n.factorization 2) h2
    simp only [Nat.factorization_mul hN0 hi0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h3
    rw [h3]
  let SG : Sylow 2 ↥G := Sylow.ofCard S' hcardS'
  have hrel : (QG G X).relIndex S' = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨c.tG, htS⟩, fun b => ?_⟩
    have hbN : (b : ↥G) ∈ N := hS'N b.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show Xor ((b : ↥G) * c.tG ∈ QG G X) ((b : ↥G) ∈ QG G X)
    rcases c.mem_QG_or_mul_mem hbN with h | h
    · right
      refine ⟨h, fun h' => c.tG_not_mem_QG ?_⟩
      have := (QG G X).mul_mem ((QG G X).inv_mem h) h'
      simpa using this
    · left
      refine ⟨h, fun h' => c.tG_not_mem_QG ?_⟩
      have := (QG G X).mul_mem ((QG G X).inv_mem h') h
      simpa using this
  have hu : c.tG * c.tG = 1 := by
    apply Subtype.ext
    show t * t = 1
    rw [← pow_two]
    exact c.ht2
  obtain ⟨X₀, -, hX₀n, hX₀card, htX₀, -, -⟩ :=
    CFSG.Quasithin.thompson_transfer_index_two_sub (⊤ : Subgroup ↥G) S' (QG G X) le_top hS'p
      (fun R _ hR hSR => SG.is_maximal' hR hSR) hrel hu htS (fun a _ => c.conj_not_mem_QG a)
  refine ⟨X₀, ⟨fun w hw x => hX₀n x trivial w hw⟩, ?_, htX₀⟩
  have h1 := Subgroup.card_mul_index X₀
  rw [Subgroup.card_top] at hX₀card
  have hX0 : 0 < Nat.card ↥X₀ := Nat.card_pos
  rw [hX₀card] at h1
  have : Nat.card ↥X₀ * X₀.index = Nat.card ↥X₀ * 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hX0 this

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
