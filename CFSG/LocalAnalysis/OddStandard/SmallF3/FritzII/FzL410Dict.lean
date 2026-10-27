module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Mu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Def

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

private lemma fz410_zmod4_two_mul_val (c : ZMod 2) :
    (2 : ZMod 4) * (c.val : ZMod 4) = 0 ↔ c = 0 := by
  revert c; decide

private lemma fz410_tt_fix_iff (a : FzL410.A) : FzL410.tt a = a ↔ FzL410.EA a := by
  have hx : ∀ c : ZMod 2, (2 : ZMod 4) * (c.val : ZMod 4) = 0 ↔ c = 0 :=
    fun c => fz410_zmod4_two_mul_val c
  constructor
  · intro h
    have h1 : a.2.2.1 = 0 := by
      have hf := congrArg (fun z : FzL410.A => z.1) h
      simp only [FzL410.tt] at hf
      have hz : (2 : ZMod 4) * (a.2.2.1.val : ZMod 4) = 0 :=
        add_left_cancel (hf.trans (add_zero a.1).symm)
      exact (hx a.2.2.1).mp hz
    have h2 : a.2.2.2 = 0 := by
      have hf := congrArg (fun z : FzL410.A => z.2.1) h
      simp only [FzL410.tt] at hf
      have hz : (2 : ZMod 4) * (a.2.2.2.val : ZMod 4) = 0 :=
        add_left_cancel (hf.trans (add_zero a.2.1).symm)
      exact (hx a.2.2.2).mp hz
    show a.2.2 = 0
    exact Prod.ext h1 h2
  · intro h
    have h1 : a.2.2.1 = 0 := congrArg Prod.fst h
    have h2 : a.2.2.2 = 0 := congrArg Prod.snd h
    ext <;> simp [FzL410.tt, h1, h2]

include M

private lemma fz410_mem_E_iff (a : FzL410.A) :
    emb a ∈ E ↔ emb a ∈ P ∧ t * emb a * t⁻¹ = emb a := by
  constructor
  · intro ha
    refine ⟨M.pf.EP ha, ?_⟩
    have hW : emb a ∈ W := M.str.EW ha
    have hcomm : t * emb a = emb a * t := M.str.W_comm t M.str.t_mem (emb a) hW
    rw [hcomm]; group
  · rintro ⟨haP, hcent⟩
    by_contra haE
    have haW : emb a ∉ W := fun hW => haE (M.pf.PW (emb a) haP hW)
    have htc : t * emb a = emb a * t := by
      have h' := congrArg (fun z => z * t) hcent
      simpa [mul_assoc] using h'
    have hconj : emb a * t * (emb a)⁻¹ = t := by
      calc emb a * t * (emb a)⁻¹ = (t * emb a) * (emb a)⁻¹ := by rw [← htc]
        _ = t := by group
    exact M.str.Q_t (emb a) (M.pf.PQ haP) haW hconj

private lemma fz410_conj_ts (a : FzL410.A) :
    (t * s) * emb a * (t * s)⁻¹ = emb (FzL410.tt (FzL410.ss a)) := by
  calc (t * s) * emb a * (t * s)⁻¹
      = t * (s * emb a * s⁻¹) * t⁻¹ := by group
    _ = t * emb (FzL410.ss a) * t⁻¹ := by rw [M.emb.cj_s a]
    _ = emb (FzL410.tt (FzL410.ss a)) := M.emb.cj_t (FzL410.ss a)

private lemma fz410_vpart_mem_P (x : FzL410.TM) (hx : fz410Mu emb t s lam x ∈ P) :
    t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val ∈ P := by
  have h1 : (emb x.1)⁻¹ * fz410Mu emb t s lam x ∈ P :=
    P.mul_mem (P.inv_mem (M.emb.emb_mem x.1)) hx
  have h2 : (emb x.1)⁻¹ * fz410Mu emb t s lam x
      = t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val := by
    unfold fz410Mu
    group
  rwa [h2] at h1

theorem mu_pe (a : FzL410.A) : fz410Mu emb t s lam (FzL410.pe a) = emb a := by
  simp [fz410Mu, FzL410.pe]

theorem mu_tM : fz410Mu emb t s lam FzL410.tM = t := by
  simp [fz410Mu, FzL410.tM, M.emb.emb_zero, ZMod.val_one 2]

theorem mu_tsM : fz410Mu emb t s lam FzL410.tsM = t * s := by
  simp [fz410Mu, FzL410.tsM, M.emb.emb_zero, ZMod.val_one 2]

theorem mu_eE (a b : ZMod 4) : fz410Mu emb t s lam (FzL410.eE a b) = emb (a, b, 0, 0) := by
  simp [fz410Mu, FzL410.eE]

theorem mem_P (x : FzL410.TM) : fz410Mu emb t s lam x ∈ P ↔ FzL410.inP x := by
  constructor
  · intro hx
    obtain ⟨ha, hb, hc⟩ := M.v_mem_P (M.fz410_vpart_mem_P x hx)
    show x.2 = 0
    exact Prod.ext ha (Prod.ext hb hc)
  · intro hx
    rw [FzL410.inP] at hx
    rw [show x = (x.1, (0 : FzL410.V)) from Prod.ext rfl hx]
    have hmu : fz410Mu emb t s lam (x.1, (0 : FzL410.V)) = emb x.1 := by
      unfold fz410Mu
      simp
    rw [hmu]
    exact M.emb.emb_mem x.1

theorem mem_Q (x : FzL410.TM) : fz410Mu emb t s lam x ∈ Q ↔ FzL410.inQ x := by
  constructor
  · intro hx
    have hV : t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val ∈ Q := by
      have h1 : (emb x.1)⁻¹ * fz410Mu emb t s lam x ∈ Q :=
        Q.mul_mem (Q.inv_mem (M.pf.PQ (M.emb.emb_mem x.1))) hx
      have h2 : (emb x.1)⁻¹ * fz410Mu emb t s lam x
          = t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val := by
        unfold fz410Mu
        group
      rwa [h2] at h1
    exact M.v_mem_Q hV
  · intro hx
    obtain ⟨hb, hc⟩ := hx
    have hmu : fz410Mu emb t s lam x = emb x.1 * t ^ x.2.1.val := by
      unfold fz410Mu
      simp [hb, hc]
    rw [hmu]
    exact Q.mul_mem (M.pf.PQ (M.emb.emb_mem x.1))
      (Q.pow_mem (M.str.WQ M.str.t_mem) x.2.1.val)

theorem mem_R (x : FzL410.TM) : fz410Mu emb t s lam x ∈ R ↔ FzL410.inR x := by
  have hsR : s ∈ R := by
    rcases M.s_cases with hs | hs
    · rw [hs]; exact M.str.tau_R
    · rw [hs]; exact R.mul_mem (M.str.QR (M.str.WQ M.str.t_mem)) M.str.tau_R
  constructor
  · intro hx
    have hV : t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val ∈ R := by
      have h1 : (emb x.1)⁻¹ * fz410Mu emb t s lam x ∈ R :=
        R.mul_mem (R.inv_mem (M.str.QR (M.pf.PQ (M.emb.emb_mem x.1)))) hx
      have h2 : (emb x.1)⁻¹ * fz410Mu emb t s lam x
          = t ^ x.2.1.val * s ^ x.2.2.1.val * lam ^ x.2.2.2.val := by
        unfold fz410Mu
        group
      rwa [h2] at h1
    exact M.v_mem_R hV
  · intro hx
    rw [FzL410.inR] at hx
    have hmu : fz410Mu emb t s lam x = emb x.1 * t ^ x.2.1.val * s ^ x.2.2.1.val := by
      unfold fz410Mu
      simp [hx]
    rw [hmu]
    exact R.mul_mem (R.mul_mem (M.str.QR (M.pf.PQ (M.emb.emb_mem x.1)))
      (R.pow_mem (M.str.QR (M.str.WQ M.str.t_mem)) x.2.1.val)) (R.pow_mem hsR x.2.2.1.val)

theorem mem_E (a : FzL410.A) : emb a ∈ E ↔ FzL410.EA a := by
  rw [fz410_mem_E_iff M a, ← fz410_tt_fix_iff a]
  constructor
  · rintro ⟨-, hcent⟩
    have h := M.emb.cj_t a
    rw [h] at hcent
    exact M.emb.inj _ _ hcent
  · intro htt
    exact ⟨M.emb.emb_mem a, by rw [M.emb.cj_t a, htt]⟩

theorem mem_Z (a : FzL410.A) : emb a ∈ Z ↔ FzL410.ZA a := by
  have hsq : (emb a) ^ 2 = 1 ↔ (2 : ℕ) • a = 0 := by
    have h := M.emb.emb_nsmul 2 a
    constructor
    · intro h2
      apply M.emb.inj
      rw [h, M.emb.emb_zero]
      exact h2
    · intro h2
      rw [← h, h2, M.emb.emb_zero]
  have hZE : emb a ∈ Z ↔ emb a ∈ E ∧ (emb a) ^ 2 = 1 :=
    ⟨fun hz => ⟨M.str.ZE hz, M.str.Z_sq _ hz⟩,
      fun ⟨he, h2⟩ => M.str.E_invol _ he h2⟩
  rw [hZE, mem_E M a, hsq]
  simp only [FzL410.EA, FzL410.ZA]

theorem mem_F (a : FzL410.A) : emb a ∈ fz410F P t s ↔ FzL410.FA a := by
  have hconj := fz410_conj_ts M a
  constructor
  · intro ha
    have hcomm : (t * s) * emb a = emb a * (t * s) := by
      have hcen := (Subgroup.mem_inf.mp ha).2
      rw [Subgroup.mem_centralizer_iff] at hcen
      exact hcen (t * s) (Set.mem_singleton _)
    have h2 : (t * s) * emb a * (t * s)⁻¹ = emb a := by
      rw [hcomm]; group
    rw [hconj] at h2
    exact M.emb.inj _ _ h2
  · intro hfa
    refine Subgroup.mem_inf.mpr ⟨M.emb.emb_mem a, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h2 : (t * s) * emb a * (t * s)⁻¹ = emb a := by rw [hconj, hfa]
    show (t * s) * emb a = emb a * (t * s)
    calc (t * s) * emb a = ((t * s) * emb a * (t * s)⁻¹) * (t * s) := by group
      _ = emb a * (t * s) := by rw [h2]

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
