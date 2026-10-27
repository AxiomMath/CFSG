module

public import CFSG.CGT.PushingUpLit.LIT.A4.L35Strong
public import CFSG.CGT.PushingUpLit.LIT.A4.L35Bender
public import CFSG.CGT.PushingUpLit.LIT.A4.L34All

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.Open (fusionStronglyEmbedded)
open CFSG.RankThree.PartOne.SolD3 (Blk3)


theorem three_conj_false {G : Type} [Group G] [Finite G] {M X : Subgroup G} (c : A4Cfg G M X)
    (hr : 3 ≤ Nat.card ↥(blocksOf M X)) : False := by
  have := c.simple
  have hnn : ∃ m ∈ M, conjSub m X ≠ X := by
    by_contra hcon
    push Not at hcon
    have hsub : blocksOf M X ⊆ {X} := by
      rintro _ ⟨m, hm, rfl⟩
      exact hcon m hm
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at h1
    omega
  have F := L34.fam_of_a4cfg c hnn
  have hse : fusionStronglyEmbedded M := L34.Fam.stronglyEmbedded F hr c.ne_top
  obtain ⟨m, hm, hne⟩ := hnn
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.SolD3.exists_blk3 c.short c.nat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := by
    intro e
    obtain ⟨w, hw, hw1⟩ := ha.exists_ne_one
    exact hw1 (ha.fix w hw (by simp [e]))
  have ha3 : orderOf a = 3 := orderOf_eq_prime ha.cube ha1
  have hb3' : (m * a * m⁻¹) ^ 3 = 1 := by rw [conj_pow, ha.cube]; group
  have hb1 : m * a * m⁻¹ ≠ 1 := fun e => ha1 (conj_eq_one_iff.1 e)
  have hb3 : orderOf (m * a * m⁻¹) = 3 := orderOf_eq_prime hb3' hb1
  have hbX2 : m * a * m⁻¹ ∈ conjSub m X := conj_mem_conjSub ha.mem
  have hX𝒳 : X ∈ blocksOf M X := ⟨1, M.one_mem, (conjSub_one X).symm⟩
  have hX2𝒳 : conjSub m X ∈ blocksOf M X := ⟨m, hm, rfl⟩
  have hab : a * (m * a * m⁻¹) = (m * a * m⁻¹) * a :=
    F.comm X hX𝒳 (conjSub m X) hX2𝒳 hne.symm a ha.mem _ hbX2
  have hbnot : m * a * m⁻¹ ∉ Subgroup.zpowers a := by
    intro hbz
    have hle : Subgroup.zpowers (m * a * m⁻¹) ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hbz
    have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers (m * a * m⁻¹)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hb3]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have haz : a ∈ Subgroup.zpowers (m * a * m⁻¹) := heq ▸ Subgroup.mem_zpowers a
    have haX2 : a ∈ conjSub m X := (Subgroup.zpowers_le.2 hbX2) haz
    obtain ⟨w, hw, hw1⟩ := ha.exists_ne_one
    have hc := F.comm X hX𝒳 (conjSub m X) hX2𝒳 hne.symm w
      ((CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self X) hw) a haX2
    exact hw1 (ha.fix w hw (by rw [← hc]; group))
  have hRM : pCoreOf 2 M ≤ M := CFSG.CGT.PushingUpLit.SolK.pCoreOf_le_self M
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 M) := CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' M
  have hRn : ∀ k ∈ M, conjSub k (pCoreOf 2 M) = pCoreOf 2 M := fun k hk => by
    rw [← L34.pCoreOf_conjSub, conjSub_eq_self_of_mem hk]
  have hR1 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P, hP1, hP2, hPM⟩ := c.maxLocal.1
    intro hbot
    apply hP1
    have hPle : P ≤ pCoreOf 2 M := by
      refine CFSG.CGT.PushingUpLit.SolK.le_pCoreOf_of_normalized ?_ ?_ hP2
      · rw [hPM]
        exact Subgroup.le_normalizer
      · intro h hh x hx
        rw [hPM] at hh
        exact (Subgroup.mem_normalizer_iff.1 hh x).1 hx
    exact le_bot_iff.1 (hbot ▸ hPle)
  exact L35.no_stronglyEmbedded_Z3Z3 hse hRM hR2 hRn hR1 (c.le ha.mem) (c.conj_le hm hbX2) ha3 hb3
    hab hbnot

end CFSG.CGT.PushingUpLit.A4
