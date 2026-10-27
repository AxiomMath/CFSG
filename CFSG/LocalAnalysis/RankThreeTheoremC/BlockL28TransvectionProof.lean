module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Bar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

theorem false_of_simple_section {J Q : Type*} [Group J] [Group Q] (ρ : J →* Q)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker) (hQ : IsSimpleGroup Q)
    (hQ9 : 2 ^ 9 ∣ Nat.card Q) (B : Subgroup J) [B.Normal] {Y : Type*} [Group Y] (ψ : B →* Y)
    (hψ : Function.Surjective ψ) (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504) : False := by
  obtain ⟨ψ', hψ'⟩ := exists_surjective_range_of_isPGroup_ker (ρ.comp B.subtype)
    (isPGroup_ker_comp_subtype ρ hk B) ψ hψ hY hcard
  have hn : (ρ.comp B.subtype).range.Normal := by
    have : (ρ.comp B.subtype).range = B.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact Subgroup.Normal.map inferInstance ρ hρ
  have hY1 : Nontrivial Y := hY.toNontrivial
  rcases hQ.eq_bot_or_eq_top_of_normal (ρ.comp B.subtype).range with hb | ht
  · obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    obtain ⟨r, rfl⟩ := hψ' y
    have hr : (r : Q) ∈ (⊥ : Subgroup Q) := hb ▸ r.2
    have hr1 : r = 1 := Subtype.ext (Subgroup.mem_bot.mp hr)
    exact hy (by rw [hr1, map_one])
  · let e : ↥(ρ.comp B.subtype).range ≃* Q :=
      (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
    have hsimple : IsSimpleGroup ↥(ρ.comp B.subtype).range := e.isSimpleGroup
    rcases hsimple.eq_bot_or_eq_top_of_normal ψ'.ker with hk' | hk'
    · have hinj : Function.Injective ψ' := (MonoidHom.ker_eq_bot_iff ψ').mp hk'
      have h1 := Nat.card_congr (Equiv.ofBijective ψ' ⟨hinj, hψ'⟩)
      rw [Nat.card_congr e.toEquiv, hcard] at h1
      rw [h1] at hQ9
      have := Nat.le_of_dvd (by norm_num) hQ9
      omega
    · obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨r, rfl⟩ := hψ' y
      have : r ∈ ψ'.ker := by rw [hk']; trivial
      exact hy this

theorem kFactBlockL28Transvection_of_pl (hPL : CitedBlockTransvectionPL)
    (hSp : KFactSpTwoSimple) : KFactBlockL28Transvection := by
  intro G _ _ M S L hyps h3 hq
  obtain ⟨hK, hA, hL, -, hX, hS⟩ := hyps
  have hLM : L ≤ M := hL.le
  rcases hPL G M S L hK hA hL hX hS h3 with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨hQ, hQ9⟩ := hSp k d hk hd
    obtain ⟨B, d', ψ, hB, hd', hψ⟩ := exists_normal_section hLM hq
    obtain ⟨hY, hcard⟩ := catGroup_facts hd'
    exact false_of_simple_section
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 _)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (isPGroup_ker_comp_quotient e) hQ hQ9
      B ψ hψ hY hcard
  · exact not_hasL28Quot_of_perm hLM e hq

end CFSG.LocalAnalysis.RankThreeTheoremC
