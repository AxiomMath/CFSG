module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Cent
public import Certificates.Certificate40360
public import Certificates.Certificate40361
public import Certificates.Certificate40362

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4

theorem card_duad_comm_row31_row43 :
    Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
        (σ : Equiv.Perm (Fin 24)) * row31.piPerm = row31.piPerm * σ ∧
          (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = row31.gam ∧
      Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
        (σ : Equiv.Perm (Fin 24)) * row43.piPerm = row43.piPerm * σ ∧
          (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = row43.gam :=
  Certificates.certificate40362

theorem row_J4_31 :
    KFactSporLocalRow .J4 31 := by
  obtain ⟨⟨z, u, L, hR⟩, hcol_lt, hπ, hone, h4, h11, hce⟩ := Certificates.certificate40360
  exact row_of_rowFacts (ce := 8) (gam := 10) hR hcol_lt hπ hone h4 h11 hce
    card_duad_comm_row31_row43.1
    (show Nat.Prime 31 by norm_num) (show 31 ≠ 2 by norm_num) (show 0 < 10 by norm_num)
    (show ∀ k, 0 < k → k < 10 → ((27 : ℕ) : ZMod 31) ^ k ≠ 1 by
      intro k hk0 hk
      interval_cases k <;> decide)
    (show ¬ 31 ∣ 1816657920 by norm_num) (show ¬ 31 ∣ 21799895040 by norm_num)
    (show ¬ 31 ^ 2 ∣ 86775571046077562880 by norm_num)

theorem row_J4_43 :
    KFactSporLocalRow .J4 43 := by
  obtain ⟨⟨z, u, L, hR⟩, hcol_lt, hπ, hone, h4, h11, hce⟩ := Certificates.certificate40361
  exact row_of_rowFacts (ce := 4) (gam := 14) hR hcol_lt hπ hone h4 h11 hce
    card_duad_comm_row31_row43.2
    (show Nat.Prime 43 by norm_num) (show 43 ≠ 2 by norm_num) (show 0 < 14 by norm_num)
    (show ∀ k, 0 < k → k < 14 → ((22 : ℕ) : ZMod 43) ^ k ≠ 1 by
      intro k hk0 hk
      interval_cases k <;> decide)
    (show ¬ 43 ∣ 1816657920 by norm_num) (show ¬ 43 ∣ 21799895040 by norm_num)
    (show ¬ 43 ^ 2 ∣ 86775571046077562880 by norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
