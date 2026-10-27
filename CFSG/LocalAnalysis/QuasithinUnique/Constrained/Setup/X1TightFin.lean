module

public import Certificates.Certificate4038

public section

namespace CFSG.QuasithinUnique.Setup.X1.Tight

theorem good_false :
    ∀ x ∈ [0, 1, 30, 31], ∀ y < 32, good x y = false :=
  Certificates.certificate4038.1

theorem fix_dbC : ∀ n < 32, app5 dbC n = n → n = 0 ∨ n = 1 ∨ n = 30 ∨ n = 31 := by
  decide

theorem rebase_fin : ∀ w < 32,
    (∀ k < 5, app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (app5 (dwC w) (2 ^ k)))) = 2 ^ k) →
      ∃ x < 32, cycOK x = true ∧ app5 (dwC w) x = x :=
  Certificates.certificate4038.2

end CFSG.QuasithinUnique.Setup.X1.Tight
