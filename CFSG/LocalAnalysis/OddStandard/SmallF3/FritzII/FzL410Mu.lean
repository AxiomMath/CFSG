module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Emb
public import Certificates.Data.FzL410Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

structure Fz410Mod {G : Type} [Group G] [Finite G] (t tau lam rho s : G)
    (Z E W Q R T P : Subgroup G) (emb : FzL410.A → G) : Prop where
  str : FzStr t tau lam rho Z E W Q R T
  pf : FzPFacts t tau rho E W Q T P
  t_notin_P : t ∉ P
  s_cases : s = tau ∨ s = t * tau
  emb : Fz410Emb P t s lam rho emb

@[expose] noncomputable def fz410Mu {G : Type} [Group G] (emb : FzL410.A → G) (t s lam : G)
    (x : FzL410.TM) : G :=
  emb x.1 * t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val

private noncomputable def fz410MuV {G : Type} [Group G] (t s lam : G) (w : FzL410.V) : G :=
  t ^ w.1.val * s ^ w.2.1.val * lam ^ w.2.2.val

private lemma fz410_eq_zero_of_pow_mem {G : Type} [Group G] {a : ZMod 2} {K : Subgroup G} {g : G}
    (hg : g ∉ K) (h : g ^ a.val ∈ K) : a = 0 := by
  have hval : a.val = 0 := by
    by_contra hne
    have h1 : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr hne
    have h2 : a.val < 2 := ZMod.val_lt a
    have ha1 : a.val = 1 := by omega
    rw [ha1, pow_one] at h
    exact hg h
  exact (ZMod.val_eq_zero a).mp hval

private lemma fz410_pow_zmod2 {G : Type} [Group G] {g : G} (hg : g ^ 2 = 1) (a b : ZMod 2) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  have h01a : a = 0 ∨ a = 1 := by revert a; decide
  have h01b : b = 0 ∨ b = 1 := by revert b; decide
  rcases h01a with rfl | rfl <;> rcases h01b with rfl | rfl
  · simp only [add_zero, ZMod.val_zero, pow_zero, one_mul, mul_one]
  · simp only [zero_add, ZMod.val_zero, ZMod.val_one 2, pow_zero, pow_one, one_mul]
  · simp only [add_zero, ZMod.val_zero, ZMod.val_one 2, pow_zero, pow_one, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, ZMod.val_zero, pow_zero,
        ZMod.val_one 2, pow_one, ← pow_two, hg]

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

private lemma fz410_conj_val {g : G} {f : FzL410.A → FzL410.A}
    (hf : ∀ q, MulAut.conj g (emb q) = emb (f q)) (a : ZMod 2) (q : FzL410.A) :
    ((MulAut.conj g) ^ a.val) (emb q) = emb (FzL410.ap a f q) := by
  have h01 : a = 0 ∨ a = 1 := by revert a; decide
  rcases h01 with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, MulAut.one_apply, FzL410.ap, if_pos rfl]
  · rw [ZMod.val_one 2, pow_one, FzL410.ap, if_neg (by decide)]
    exact hf q

include M

private lemma fz410_tau_comm_t : tau * t = t * tau := by
  have h := M.str.tau_t
  calc tau * t = tau * t * tau⁻¹ * tau := by group
    _ = t * tau := by rw [h]

private lemma fz410_t_mem_R : t ∈ R := M.str.QR (M.str.WQ M.str.t_mem)

private lemma fz410_s_mem_R : s ∈ R := by
  rcases M.s_cases with hs | hs
  · rw [hs]; exact M.str.tau_R
  · rw [hs]; exact R.mul_mem M.fz410_t_mem_R M.str.tau_R

private lemma fz410_s_notin_Q : s ∉ Q := by
  rcases M.s_cases with hs | hs
  · rw [hs]; exact M.str.tau_notin_Q
  · intro hsQ
    have htQ : t ∈ Q := M.str.WQ M.str.t_mem
    have h1 : t⁻¹ * (t * tau) ∈ Q := Q.mul_mem (Q.inv_mem htQ) (hs ▸ hsQ)
    exact M.str.tau_notin_Q (by simpa [mul_assoc] using h1)

private lemma fz410_s_mem_T : s ∈ T := M.str.RT M.fz410_s_mem_R

private lemma fz410_lam_notin_R : lam ∉ R := by
  intro hlam
  obtain ⟨z, hz, hz'⟩ := M.str.lam_Z
  exact hz' (M.str.R_Z lam hlam z hz)

private lemma fz410_ts_mem_R (a b : ZMod 2) : t ^ a.val * s ^ b.val ∈ R :=
  R.mul_mem (R.pow_mem M.fz410_t_mem_R a.val) (R.pow_mem M.fz410_s_mem_R b.val)

theorem t_sq : t ^ 2 = 1 := M.str.t_sq

theorem s_sq : s ^ 2 = 1 := by
  rcases M.s_cases with hs | hs
  · rw [hs]; exact M.pf.tau_sq1
  · rw [hs, pow_two]
    have ht : t * t = 1 := by simpa [pow_two] using M.str.t_sq
    have htau : tau * tau = 1 := by simpa [pow_two] using M.pf.tau_sq1
    calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [M.fz410_tau_comm_t]
      _ = (t * t) * (tau * tau) := by group
      _ = 1 := by rw [ht, htau, mul_one]

theorem lam_sq : lam ^ 2 = 1 := M.str.lam_sq

theorem s_comm_t : s * t = t * s := by
  rcases M.s_cases with hs | hs
  · rw [hs]; exact M.fz410_tau_comm_t
  · rw [hs, show (t * tau) * t = t * (tau * t) by group, M.fz410_tau_comm_t]

theorem lam_comm_t : lam * t = t * lam := by
  have h := M.str.lam_t
  calc lam * t = lam * t * lam⁻¹ * lam := by group
    _ = t * lam := by rw [h]

theorem lam_comm_s : lam * s = s * lam := by
  rcases M.s_cases with hs | hs
  · rw [hs]; exact M.str.tau_lam.symm
  · rw [hs]
    calc lam * (t * tau) = (lam * t) * tau := by group
      _ = (t * lam) * tau := by rw [M.lam_comm_t]
      _ = t * (lam * tau) := by group
      _ = t * (tau * lam) := by rw [← M.str.tau_lam]
      _ = (t * tau) * lam := by group

theorem v_mem_R {a b c : ZMod 2} (h : t ^ a.val * s ^ b.val * lam ^ c.val ∈ R) : c = 0 := by
  have hA : t ^ a.val * s ^ b.val ∈ R := M.fz410_ts_mem_R a b
  have hlam : lam ^ c.val ∈ R := by
    have h1 := R.mul_mem (R.inv_mem hA) h
    simpa [mul_assoc] using h1
  exact fz410_eq_zero_of_pow_mem M.fz410_lam_notin_R hlam

theorem v_mem_Q {a b c : ZMod 2} (h : t ^ a.val * s ^ b.val * lam ^ c.val ∈ Q) :
    b = 0 ∧ c = 0 := by
  have hc : c = 0 := M.v_mem_R (M.str.QR h)
  subst hc
  simp only [ZMod.val_zero, pow_zero, mul_one] at h
  have hb : b = 0 := by
    apply fz410_eq_zero_of_pow_mem M.fz410_s_notin_Q
    have hA : t ^ a.val ∈ Q := Q.pow_mem (M.str.WQ M.str.t_mem) a.val
    have h1 := Q.mul_mem (Q.inv_mem hA) h
    simpa [mul_assoc] using h1
  exact ⟨hb, rfl⟩

theorem v_mem_P {a b c : ZMod 2} (h : t ^ a.val * s ^ b.val * lam ^ c.val ∈ P) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨hb, hc⟩ := M.v_mem_Q (M.pf.PQ h)
  subst hb; subst hc
  simp only [ZMod.val_zero, pow_zero, mul_one] at h
  have ha : a = 0 := fz410_eq_zero_of_pow_mem M.t_notin_P h
  exact ⟨ha, rfl, rfl⟩

private lemma fz410_conj_v (w : FzL410.V) (q : FzL410.A) :
    fz410MuV t s lam w * emb q * (fz410MuV t s lam w)⁻¹ = emb (FzL410.act w q) := by
  obtain ⟨a, b, c⟩ := w
  have ht : ∀ q, MulAut.conj t (emb q) = emb (FzL410.tt q) := by
    intro q; rw [MulAut.conj_apply]; exact M.emb.cj_t q
  have hs : ∀ q, MulAut.conj s (emb q) = emb (FzL410.ss q) := by
    intro q; rw [MulAut.conj_apply]; exact M.emb.cj_s q
  have hl : ∀ q, MulAut.conj lam (emb q) = emb (FzL410.ll q) := by
    intro q; rw [MulAut.conj_apply]; exact M.emb.cj_lam q
  have hlhs : fz410MuV t s lam (a, b, c) * emb q * (fz410MuV t s lam (a, b, c))⁻¹
      = MulAut.conj (t ^ a.val * s ^ b.val * lam ^ c.val) (emb q) := by
    rw [MulAut.conj_apply]
    rfl
  rw [hlhs, show MulAut.conj (t ^ a.val * s ^ b.val * lam ^ c.val)
      = MulAut.conj t ^ a.val * MulAut.conj s ^ b.val * MulAut.conj lam ^ c.val by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]]
  simp only [MulAut.mul_apply]
  rw [fz410_conj_val (emb := emb) hl c q,
      fz410_conj_val (emb := emb) hs b (FzL410.ap c FzL410.ll q),
      fz410_conj_val (emb := emb) ht a (FzL410.ap b FzL410.ss (FzL410.ap c FzL410.ll q))]
  rfl

private lemma fz410_mu_eq (x : FzL410.TM) :
    fz410Mu emb t s lam x = emb x.1 * fz410MuV t s lam x.2 := by
  rw [fz410Mu, fz410MuV]
  group

private lemma fz410_muV_add (u w : FzL410.V) :
    fz410MuV t s lam (u + w) = fz410MuV t s lam u * fz410MuV t s lam w := by
  obtain ⟨a1, b1, c1⟩ := u
  obtain ⟨a2, b2, c2⟩ := w
  show t ^ (a1 + a2).val * s ^ (b1 + b2).val * lam ^ (c1 + c2).val
      = t ^ a1.val * s ^ b1.val * lam ^ c1.val * (t ^ a2.val * s ^ b2.val * lam ^ c2.val)
  rw [fz410_pow_zmod2 M.t_sq a1 a2, fz410_pow_zmod2 M.s_sq b1 b2,
      fz410_pow_zmod2 M.lam_sq c1 c2]
  have hst := (((commute_iff_eq t s).mpr M.s_comm_t.symm).pow_pow a2.val b1.val).eq.symm
  have hlt := (((commute_iff_eq t lam).mpr M.lam_comm_t.symm).pow_pow a2.val c1.val).eq.symm
  have hls := (((commute_iff_eq s lam).mpr M.lam_comm_s.symm).pow_pow b2.val c1.val).eq.symm
  have key : (t ^ a1.val * s ^ b1.val * lam ^ c1.val) * (t ^ a2.val * s ^ b2.val * lam ^ c2.val)
      = (t ^ a1.val * t ^ a2.val) * (s ^ b1.val * s ^ b2.val) * (lam ^ c1.val * lam ^ c2.val) := by
    calc (t ^ a1.val * s ^ b1.val * lam ^ c1.val) * (t ^ a2.val * s ^ b2.val * lam ^ c2.val)
        = (t ^ a1.val * s ^ b1.val) * (lam ^ c1.val * t ^ a2.val)
            * (s ^ b2.val * lam ^ c2.val) := by group
      _ = (t ^ a1.val * s ^ b1.val) * (t ^ a2.val * lam ^ c1.val)
            * (s ^ b2.val * lam ^ c2.val) := by rw [hlt]
      _ = (t ^ a1.val * (s ^ b1.val * t ^ a2.val) * lam ^ c1.val)
            * (s ^ b2.val * lam ^ c2.val) := by group
      _ = (t ^ a1.val * (t ^ a2.val * s ^ b1.val) * lam ^ c1.val)
            * (s ^ b2.val * lam ^ c2.val) := by rw [hst]
      _ = (t ^ a1.val * t ^ a2.val) * (s ^ b1.val * (lam ^ c1.val * s ^ b2.val))
            * lam ^ c2.val := by group
      _ = (t ^ a1.val * t ^ a2.val) * (s ^ b1.val * (s ^ b2.val * lam ^ c1.val))
            * lam ^ c2.val := by rw [hls]
      _ = (t ^ a1.val * t ^ a2.val) * (s ^ b1.val * s ^ b2.val)
            * (lam ^ c1.val * lam ^ c2.val) := by group
  exact key.symm

private lemma fz410_muV_mul_self (w : FzL410.V) :
    fz410MuV t s lam w * fz410MuV t s lam w = 1 := by
  rw [← M.fz410_muV_add w w]
  have hww : w + w = 0 := by
    have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
    ext <;> exact hxx _
  rw [hww]
  simp [fz410MuV, ZMod.val_zero, pow_zero]

private lemma fz410_mu_mem_T (x : FzL410.TM) : fz410Mu emb t s lam x ∈ T := by
  rw [fz410_mu_eq M x, fz410MuV]
  exact T.mul_mem
    (M.str.RT (M.str.QR (M.pf.PQ ((M.emb.mem (emb x.1)).mpr ⟨x.1, rfl⟩))))
    (T.mul_mem (T.mul_mem
      (T.pow_mem (M.str.RT M.fz410_t_mem_R) x.2.1.val)
      (T.pow_mem M.fz410_s_mem_T x.2.2.1.val))
      (T.pow_mem M.str.lam_T x.2.2.2.val))

theorem mu_mul (x y : FzL410.TM) :
    fz410Mu emb t s lam (FzL410.mulT x y) = fz410Mu emb t s lam x * fz410Mu emb t s lam y := by
  rw [fz410_mu_eq M x, fz410_mu_eq M y, fz410_mu_eq M (FzL410.mulT x y)]
  simp only [FzL410.mulT]
  rw [M.emb.mul, M.fz410_muV_add]
  have key : emb (FzL410.act x.2 y.1) * fz410MuV t s lam x.2
      = fz410MuV t s lam x.2 * emb y.1 := by
    rw [← M.fz410_conj_v x.2 y.1]
    group
  calc (emb x.1 * emb (FzL410.act x.2 y.1)) * (fz410MuV t s lam x.2 * fz410MuV t s lam y.2)
      = emb x.1 * (emb (FzL410.act x.2 y.1) * fz410MuV t s lam x.2)
          * fz410MuV t s lam y.2 := by group
    _ = emb x.1 * (fz410MuV t s lam x.2 * emb y.1) * fz410MuV t s lam y.2 := by rw [key]
    _ = (emb x.1 * fz410MuV t s lam x.2) * (emb y.1 * fz410MuV t s lam y.2) := by group

theorem mu_inj : Function.Injective (fz410Mu emb t s lam) := by
  intro x y hxy
  rw [fz410_mu_eq M x, fz410_mu_eq M y] at hxy
  have hVin : (fz410MuV t s lam x.2)⁻¹ = fz410MuV t s lam x.2 :=
    inv_eq_of_mul_eq_one_right (M.fz410_muV_mul_self x.2)
  have hP : fz410MuV t s lam (y.2 + x.2) ∈ P := by
    rw [M.fz410_muV_add]
    have h1 : (emb y.1)⁻¹ * emb x.1 * fz410MuV t s lam x.2 = fz410MuV t s lam y.2 := by
      have := congrArg (fun z => (emb y.1)⁻¹ * z) hxy
      simpa [mul_assoc] using this
    have h2 : (emb y.1)⁻¹ * emb x.1
        = fz410MuV t s lam y.2 * fz410MuV t s lam x.2 := by
      calc (emb y.1)⁻¹ * emb x.1
          = ((emb y.1)⁻¹ * emb x.1 * fz410MuV t s lam x.2)
              * (fz410MuV t s lam x.2)⁻¹ := by group
        _ = fz410MuV t s lam y.2 * (fz410MuV t s lam x.2)⁻¹ := by rw [h1]
        _ = fz410MuV t s lam y.2 * fz410MuV t s lam x.2 := by rw [hVin]
    rw [← h2]
    exact P.mul_mem (P.inv_mem ((M.emb.mem (emb y.1)).mpr ⟨y.1, rfl⟩))
      ((M.emb.mem (emb x.1)).mpr ⟨x.1, rfl⟩)
  obtain ⟨ha, hb, hc⟩ := M.v_mem_P hP
  have hsum : y.2 + x.2 = 0 := by
    ext <;> assumption
  have hxx : x.2 + x.2 = 0 := by
    have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
    ext <;> simp [h2]
  have hyx : y.2 = x.2 := by
    calc y.2 = y.2 + (x.2 + x.2) := by rw [hxx, add_zero]
      _ = (y.2 + x.2) + x.2 := by rw [add_assoc]
      _ = 0 + x.2 := by rw [hsum]
      _ = x.2 := zero_add x.2
  rw [hyx] at hxy
  have hx1 : x.1 = y.1 := M.emb.inj x.1 y.1 (mul_right_cancel hxy)
  exact Prod.ext hx1 hyx.symm

theorem mem_T (g : G) : g ∈ T ↔ ∃ x, fz410Mu emb t s lam x = g := by
  constructor
  · intro hg
    classical
    haveI : Fintype T := Fintype.ofFinite T
    let f : FzL410.TM → T := fun x => ⟨fz410Mu emb t s lam x, M.fz410_mu_mem_T x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact M.mu_inj (congrArg Subtype.val hxy)
    have hcardTM : Fintype.card FzL410.TM = 512 := by
      simp only [FzL410.TM, FzL410.A, FzL410.V, Fintype.card_prod, ZMod.card]
    have hcardT : Fintype.card T = 512 := by
      rw [← Nat.card_eq_fintype_card, M.str.card_T]
    have hbij := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by rw [hcardTM, hcardT]⟩
    obtain ⟨x, hx⟩ := hbij.2 ⟨g, hg⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, rfl⟩
    exact M.fz410_mu_mem_T x

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
