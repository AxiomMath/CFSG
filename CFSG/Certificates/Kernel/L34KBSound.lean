module

public import CFSG.Certificates.Kernel.L34KSound
public import Certificates.Data.Kernel.L34KB
import CFSG.Certificates.Kernel.L34KSnd.RunB
import CFSG.Certificates.Kernel.L34KSnd.Run
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.PSL3Four.Native

structure PinEB (n w m : Nat) (gs : Array Tab) (cap ng N L K ew : Nat) (G T E C S SI : Nat → Nat)
    (B : List Nat) (H : Subgroup (Equiv.Perm (Fin n))) : Prop where
  size : gs.size = ng
  bind : ∀ k < ng, gs[k]! = unpack n w (G k)
  perm : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true
  head : headK n w ng G T C K N (pidn n w) = true
  hN : N = L * K
  hL : 0 < L
  cap : N ≤ cap
  hm : m = mask w
  gen : ∀ k < ng, ∃ γ ∈ H, ∀ x : Fin n, pg w (mask w) (G k) x = γ x
  sep : ∀ γ ∈ H, ∀ δ ∈ H, (∀ b ∈ B, ∀ hb : b < n, γ ⟨b, hb⟩ = δ ⟨b, hb⟩) → γ = δ
  bB : ∀ b ∈ B, b < n
  sl : ∀ s < K, pinSlB n w m ng G T E C S SI B N L ew s = true

theorem PinEB.canonG {n w m : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} {B : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
    (P : PinEB n w m gs cap ng N L K ew G T E C S SI B H) :
    ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := by
  have h := P.head
  unfold headK at h
  exact CFSG.KS.Raw.Orb.allN_iff.1 (andT (andT h).2).1

theorem enumB_sound {n w m : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} {B : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
    (P : PinEB n w m gs cap ng N L K ew G T E C S SI B H) :
    ((enumBFS n gs cap).tabs = pts n w N T ∧ enumOK n gs (enumBFS n gs cap) = true) ∧
      ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  have hh := P.head
  unfold headK at hh
  obtain ⟨hsz, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨-, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hT0, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hC0, hCK⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have hC0' : C 0 = 1 := Nat.eq_of_beq_eq_true hC0
  have hCK' : C K = N := Nat.eq_of_beq_eq_true hCK
  have hGc := P.canonG
  obtain ⟨hn, hw⟩ := CFSG.KC.BfsPin.szOK_facts' hsz
  have hn32 : n < 2 ^ 32 := by omega
  have hN0 : N ≠ 0 := by
    rw [P.hN]
    have hK : K ≠ 0 := by
      intro e
      subst e
      rw [P.hN, Nat.mul_zero] at hCK'
      rw [hCK'] at hC0'
      exact absurd hC0' (by decide)
    exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.1 P.hL) hK
  let Q : Nat → Prop := fun x =>
    canonK n w (mask w) (n * w) x = true ∧ ∃ γ ∈ H, CFSG.KS.Raw.Orb.PRep n w x γ
  have hst : ∀ k < ng, ∀ t, Q t → Q (lstep n w G k t) := by
    rintro k hk t ⟨hc, γ, hγ, hr⟩
    obtain ⟨δ, hδ, hd⟩ := P.gen k hk
    exact ⟨CFSG.KC.BfsPin.canonK_pcomp (hGc k hk) hc, δ * γ, Subgroup.mul_mem _ hδ hγ,
      CFSG.KS.Raw.Orb.prep_pcomp hn32 hd hr⟩
  have heq : ∀ k < ng, ∀ t y, Q t → Q y → baseEqL w m G B k t y = true → y = lstep n w G k t := by
    rintro k hk t y ⟨hc, γ, hγ, hr⟩ ⟨hcy, ε, hε, hry⟩ hb
    obtain ⟨δ, hδ, hd⟩ := P.gen k hk
    have hb' := CFSG.KC.L34KSnd.baseEqL_spec hb
    rw [P.hm] at hb'
    have hp := CFSG.KS.Raw.Orb.prep_pcomp hn32 hd hr
    have e : ε = δ * γ := P.sep ε hε (δ * γ) (Subgroup.mul_mem _ hδ hγ) fun b hbB hbn => by
      apply Fin.ext
      rw [← hry ⟨b, hbn⟩, ← hp ⟨b, hbn⟩]
      change pg w (mask w) y b = pg w (mask w) (pcomp n w (mask w) (G k) t) b
      rw [hb' b hbB, CFSG.KC.L34KSnd.pg_pcomp' (hGc k hk) hbn]
    subst e
    exact CFSG.KC.L34KSnd.eq_of_pg hcy (CFSG.KC.BfsPin.canonK_pcomp (hGc k hk) hc) fun i hi =>
      (hry ⟨i, hi⟩).trans (hp ⟨i, hi⟩).symm
  have h0 : Q (T 0) := by
    rw [hT0']
    exact ⟨CFSG.KC.L34KSnd.canon_pidn hsz, 1, Subgroup.one_mem _,
      CFSG.KS.Raw.Orb.prep_pidn hn hw⟩
  obtain ⟨hrun, hQ⟩ := CFSG.KC.L34KSnd.runW_of_runB (eqb := baseEqL w m G B) hst heq h0 hC0'
    hCK' P.hN hN0 fun s hs => (CFSG.KC.L34KSnd.andB_iff.1 (P.sl s hs)).1
  have hcan : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := fun i hi => (hQ i hi).1
  have hinj := CFSG.KC.L34KSnd.inj_of_distSl P.hN P.hL fun s hs =>
    (CFSG.KC.L34KSnd.andB_iff.1 (P.sl s hs)).2
  have PW : CFSG.KC.L34KSnd.PinW n w ng N (lstep n w G) (leftStep n gs) T :=
    { canT := hcan
      inj := hinj
      step := fun j hj h hh => by
        unfold leftStep lstep
        rw [P.bind j hj]
        exact CFSG.KC.L34KSnd.comp_unpack' (hGc j hj) (hcan h hh) }
  have hroot : idTab n = unpack n w (T 0) := by
    rw [hT0']
    exact CFSG.KC.L34KSnd.idTab_unpack' hsz
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.bfs_of_runW PW hrun hroot P.cap
  refine ⟨?_, hcan⟩
  unfold enumBFS enumOK pts
  rw [P.size]
  exact ⟨h1, h2⟩

theorem PinEB.canon {n w m : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} {B : List Nat} {H : Subgroup (Equiv.Perm (Fin n))}
    (P : PinEB n w m gs cap ng N L K ew G T E C S SI B H) :
    ∀ i < N, canonK n w (mask w) (n * w) (T i) = true :=
  (enumB_sound P).2

end CFSG.KC.L34K

end
