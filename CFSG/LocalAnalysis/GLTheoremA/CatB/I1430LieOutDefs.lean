module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure LieSOutOrdW (N : ℕ) : Prop where
  three_dvd : 3 ∣ N
  not_dvd_216 : ¬ N ∣ 216
  not_dvd_12096 : ¬ N ∣ 12096
  ne_17971200 : N ≠ 17971200
  ne_triD4 : ∀ Q : ℕ, 2 ≤ Q → N ≠ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1)
  ne_g2 : ∀ Q : ℕ, 4 ≤ Q → N ≠ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1)
  ne_sl3 : ∀ q : ℕ, 2 ≤ q → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))
  ne_su3 : ∀ q : ℕ, 2 ≤ q → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))

structure LieSOutTypeW (T : TauCeti.CFSGIndex → Prop) (m f N : ℕ) : Prop where
  card_eq : TypeOrd T N
  det : ∀ {X : Type} [Group X], catalogIs X T → ∀ {t : StatedLieTag} {n g : ℕ},
    Blueprint.LieModel X t n 2 g → t = .PSp ∧ n = m ∧ g = f
  ord : LieSOutOrdW N
  at360 : N = 360 → m = 2 ∧ f = 1

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
