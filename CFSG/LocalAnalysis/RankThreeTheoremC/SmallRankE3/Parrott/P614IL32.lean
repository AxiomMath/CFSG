module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IKFact
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Parab
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Core
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Camp
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Y
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z b : G}
  {H S K : Subgroup G}

theorem data619_of_hyp (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {f : ↥K →* GL32}
    (hfs : Function.Surjective f) (hfk : ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    Data619 M (zpowers x ⊔ zpowers z) H S K z f where
  charTwo := hyp.setting.charTwo
  twoLocal := isTwoLocal_H hyp
  eq_normalizer := hyp.optimal.eq_normalizer
  B_le := B_le_H hyp
  maxInv := hyp.optimal.maxInv
  core_le := hyp.optimal.core_le
  S_ne_bot := S_ne_bot hyp
  norm_le := hyp.optimal.norm_le
  char_le := hyp.optimal.char_le
  K_le := h618.comp.le
  K_normal := h618.comp.normal
  K_not_le := h618.comp.not_le
  K_simple := fun N hNK hN hle => by
    rw [← h618.core_eq] at hle ⊢
    exact h618.comp.maximal N hNK hN hle
  f_surj := hfs
  f_ker := hfk
  z_mem_K := z_mem_K h618
  z_mem_B := mem_sup_right (mem_zpowers z)
  z_order := orderOf_z hyp

theorem l32Data_of_hyp (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (h620 : Stage620 H S K x z b) {f : ↥K →* GL32} (hfs : Function.Surjective f)
    (hfk : ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    L32Data M (zpowers x ⊔ zpowers z) H S K z b f := by
  have hD := data619_of_hyp hyp h618 hfs hfk
  obtain ⟨hSK, hSi⟩ := hD.key
  have hpl := plane_of_hyp hyp
  exact
    { hD with
      S_le := hSK
      S_index := hSi
      K_perfect := h618.comp.perfect
      B_card := by rw [hpl.card_eq]; norm_num
      B_comm := fun a ha c hc => by
        have := hpl.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩
        simpa using congrArg Subtype.val this
      B_exp := hpl.isElemAbelian.2
      b_mem := h620.b_mem
      b_not_mem := h620.b_not_mem
      b_cent := h620.b_cent }

theorem stage620iii_of_kbarL32 (hBlock : KFactCampbellBlock) (h2813 : KFactLemma2813)
    (hOF : OmegaFalse G) (hCT : CoreTwo G) (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (h620 : Stage620 H S K x z b) (hL : KbarL32 H K) : Stage620iii H S z := by
  obtain ⟨f, hfs, hfk⟩ := hL
  have h := l32Data_of_hyp hyp h618 h620 hfs hfk
  obtain ⟨R, hSR, hRX, hR2, hRi, hC⟩ := h.campbell_hyp h2813 hOF hCT hyp h618
  obtain ⟨A₀, B₀, hAB, hBW, -, hXB, hKA, hKW, h8, hker⟩ := h.block hBlock hSR hRX hR2 hRi hC
  exact h.stage620iii_of_block hAB hBW hXB hKA hKW h8 hker

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
