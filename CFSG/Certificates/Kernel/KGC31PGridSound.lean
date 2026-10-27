module

public import CFSG.Certificates.Kernel.KGC31PPow
public import Certificates.Data.Kernel.KGC31PGrid

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
open CFSG.KC.Child3 (tabP)

section Grp

variable {G : Type} [Group G] [DecidableEq G]

theorem gbad_grid {x y t : G} {p a b : Nat} (hp : p.Prime) (hxy : Commute x y) (hx : x ^ p = 1)
    (hy : y ^ p = 1) (ha : a < p) (hb : b < p) (h1 : gbad p x t = false)
    (h2 : ∀ c < p, gbad p (x ^ c * y) t = false) : gbad p (x ^ a * y ^ b) t = false := by
  have h1p := hp.one_lt
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · rw [pow_zero, mul_one]
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [pow_zero]
      exact gbad_one p t
    · rw [gbad_pow hx h1p (Nat.coprime_of_lt_prime ha0.ne' ha hp).symm]
      exact h1
  · have hco : Nat.Coprime b p := (Nat.coprime_of_lt_prime hb0.ne' hb hp).symm
    obtain ⟨b', -, hbb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco h1p
    have hc : a * b' % p < p := Nat.mod_lt _ (by omega)
    have hcb : a * b' % p * b % p = a := by
      rw [Nat.mod_mul_mod, mul_assoc, mul_comm b' b, Nat.mul_mod, hbb, mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt ha]
    have hg : (x ^ (a * b' % p) * y) ^ p = 1 := by
      rw [(hxy.pow_left _).mul_pow, ← pow_mul, mul_comm _ p, pow_mul, hx, one_pow, hy, one_mul]
    have e : (x ^ (a * b' % p) * y) ^ b = x ^ a * y ^ b := by
      rw [(hxy.pow_left _).mul_pow, ← pow_mul, pow_mod_eq hx, hcb]
    rw [← e, gbad_pow hg h1p hco]
    exact h2 _ hc

end Grp

variable {n w : Nat}

theorem pactOne_grid {p X Y a b t : Nat} (hX : PP n w X) (hY : PP n w Y) (ht : PP n w t)
    (hp : p.Prime) (hxy : Commute (sg n w X) (sg n w Y)) (hx : sg n w X ^ p = 1)
    (hy : sg n w Y ^ p = 1) (ha : a < p) (hb : b < p) (h1 : pactOne n w p X t = true)
    (h2 : ∀ c < p, pactOne n w p (pc n w (ppw n w X c) Y) t = true) :
    pactOne n w p (pc n w (ppw n w X a) (ppw n w Y b)) t = true := by
  have key : ∀ {Z : Nat}, PP n w Z →
      (pactOne n w p Z t = true ↔ gbad p (sg n w Z) (sg n w t) = false) := by
    intro Z hZ
    rw [pactOne_eq hZ ht]
    cases gbad p (sg n w Z) (sg n w t) <;> simp
  rw [key ((PP_ppw hX a).pc (PP_ppw hY b)), sg_pc (PP_ppw hX a) (PP_ppw hY b), sg_ppw hX,
    sg_ppw hY]
  refine gbad_grid hp hxy hx hy ha hb ((key hX).1 h1) fun c hc => ?_
  have h := (key ((PP_ppw hX c).pc hY)).1 (h2 c hc)
  rwa [sg_pc (PP_ppw hX c) hY, sg_ppw hX] at h

theorem actCheck_gridTabs {p X Y : Nat} (hX : PP n w X) (hY : PP n w Y) (hp : p.Prime)
    (hox : pord n w p X = true) (hoy : pord n w p Y = true)
    (hc : Nat.beq (pc n w X Y) (pc n w Y X) = true) {invs : List Table}
    (hI : ∀ t ∈ invs, ∃ u, PP n w u ∧ t = tabP n w u ∧ pactOne n w p X u = true ∧
      ∀ c < p, pactOne n w p (pc n w (ppw n w X c) Y) u = true) :
    actCheck n p invs (gridTabs n (tabP n w X) (tabP n w Y) p p) = true := by
  have hxy : Commute (sg n w X) (sg n w Y) := by
    have e := congrArg (sg n w) (Nat.eq_of_beq_eq_true hc)
    rwa [sg_pc hX hY, sg_pc hY hX] at e
  rw [actCheck, gridTabs, List.all_flatMap, List.all_eq_true]
  intro a ha
  rw [List.all_map, List.all_eq_true]
  intro b hb
  rw [List.mem_range] at ha hb
  have hZ := (PP_ppw hX a).pc (PP_ppw hY b)
  simp only [Function.comp_apply, powT_tabP hX, powT_tabP hY,
    compT_tabP' (PP_ppw hX a) (PP_ppw hY b)]
  rw [invOK_tabP hZ, Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨u, hu, rfl, h1, h2⟩ := hI t ht
  rw [actOne_tabP hZ hu]
  exact pactOne_grid hX hY hu hp hxy (sg_pow_of_pord hX hox) (sg_pow_of_pord hY hoy) ha hb h1 h2

theorem gridInj_tabP {X Y : Nat} (hX : PP n w X) (hY : PP n w Y) (p : Nat) :
    gridInj n (tabP n w X) (tabP n w Y) p = pgridInj n w X Y p := by
  rw [gridInj, pgridInj]
  refine all_congr' fun a _ => all_congr' fun b _ => all_congr' fun c _ =>
    all_congr' fun d _ => ?_
  simp only [powT_tabP hX, powT_tabP hY]
  rw [compT_tabP' (PP_ppw hX a) (PP_ppw hY b), compT_tabP' (PP_ppw hX c) (PP_ppw hY d),
    tblEq_tabP ((PP_ppw hX a).pc (PP_ppw hY b)) ((PP_ppw hX c).pc (PP_ppw hY d))]

end CFSG.KC.KGC31P

end
