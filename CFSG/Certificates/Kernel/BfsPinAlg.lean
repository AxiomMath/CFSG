
module

public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PinvSSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PinvS CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow

@[expose, reducible] def PP (n w p : Nat) : Prop :=
  canonK n w (mask w) (n * w) p = true ∧ InjK n w p

variable {n w : Nat}

theorem szOK_facts' {n w : Nat} (h : szOK n w = true) : n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have h3 := Nat.blt_eq.mp h2
  rw [PF.shl_eq, Nat.one_mul] at h3
  exact ⟨Nat.blt_eq.mp h1, h3⟩

theorem PP.lt32 {p : Nat} (hp : PP n w p) : n < 2 ^ 32 := by
  have := (PF.canon_facts hp.1).1
  omega

theorem PP.sz {p : Nat} (hp : PP n w p) : szOK n w = true := by
  have h := hp.1
  unfold canonK at h
  exact ((bAnd_iff _ _).1 h).1

theorem PP.mul {p q : Nat} (hp : PP n w p) (hq : PP n w q) : PP n w (pcomp n w (mask w) p q) :=
  ⟨canonK_pcomp hp.1 hq.1, injK_pcomp hp.lt32 hp.2 hq.2⟩

theorem PP.inv {p : Nat} (hp : PP n w p) : PP n w (pinvS n w (mask w) p) := by
  obtain ⟨-, hw, -, -⟩ := PF.canon_facts hp.1
  exact ⟨canonK_pinvS hp.1 hp.2, injK_pinvS (by omega) hp.2⟩

theorem PP.id (hsz : szOK n w = true) : PP n w (pidn n w) := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  have hlt : ∀ i < n, pg w (mask w) (pidn n w) i < n := fun i hi => by
    rw [PF.pg_pidn hn hw hi]
    exact hi
  refine ⟨?_, ⟨hlt, fun a ha b hb e => ?_⟩⟩
  · unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr (PF.pidn_shr hn hw),
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hlt i hi)⟩
  · rwa [PF.pg_pidn hn hw ha, PF.pg_pidn hn hw hb] at e

theorem PP_of_permOK {p : Nat} (hsz : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p (pinvS n w (mask w) p) = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hc : canonK n w (mask w) (n * w) p = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem eqA_PP {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q :=
  eqA_unpack hp.1 hq.1

theorem compA_PP {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  compA_unpack hp.1 hq.1

theorem invCand_PP {p : Nat} (hp : PP n w p) :
    invCand n (unpack n w p) = unpack n w (pinvS n w (mask w) p) :=
  invCand_unpack (permOK_pinvS hp.1 hp.2)

theorem idA_eq (hsz : szOK n w = true) : idA n = unpack n w (pidn n w) :=
  (idK_sound (idK_of_szOK hsz)).symm

theorem unpack_getElem! (P x : Nat) :
    (unpack n w P)[x]! = if x < n then pg w (mask w) P x else 0 := by
  split
  · next h => exact CFSG.KS.Raw.Orb.unpack_get h
  · next h =>
    rw [getElem!_neg]
    · rfl
    · simpa [unpack] using h

theorem PP_gen {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true)
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true) :
    ∀ k < ng, PP n w (G k) := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  exact fun k hk1 => PP_of_permOK hk'.1 (hp k hk1)

theorem PP_pts {ng N : Nat} {G T E S : Nat → Nat} (hk : bfsK n w ng G N T E S = true)
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true) :
    ∀ i < N, PP n w (T i) := by
  have hsz : szOK n w = true := by
    have hk' := hk
    unfold bfsK at hk'
    simp only [bAnd_iff] at hk'
    exact hk'.1
  have hG := PP_gen hk hp
  exact (bfsK_points (PP n w) (PP.id hsz) (fun y hy k hk1 => (hG k hk1).mul hy) hk).2.2.1

theorem gens_eq {gs : List (Array Nat)} {ng : Nat} {G : Nat → Nat} (hs : gs.toArray.size = ng)
    (hg : ∀ k < ng, gs.toArray[k]! = unpack n w (G k)) :
    gs = (List.range ng).map fun k => unpack n w (G k) := by
  have hl : gs.length = ng := by simpa using hs
  apply List.ext_getElem (by simp [hl])
  intro k h1 h2
  have e := hg k (hl ▸ h1)
  rw [getElem!_pos gs.toArray k (by simpa using h1), List.getElem_toArray] at e
  rw [e, List.getElem_map, List.getElem_range]

theorem eltsN_eq {gs : List (Array Nat)} {ng N : Nat} {G T E S : Nat → Nat}
    (hs : gs.toArray.size = ng) (hg : ∀ k < ng, gs.toArray[k]! = unpack n w (G k))
    (hk : bfsK n w ng G N T E S = true) (hf : N ≤ 4000) :
    eltsN n gs = (List.range N).map fun i => unpack n w (T i) := by
  unfold eltsN certN
  rw [enumBfs_pts hs hg hk hf]
  exact pts_toList fun i => unpack n w (T i)

theorem enumCheckN_of {gs : List (Array Nat)} {ng N : Nat} {G T E S : Nat → Nat}
    (hs : gs.toArray.size = ng) (hg : ∀ k < ng, gs.toArray[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true)
    (hk : bfsK n w ng G N T E S = true) (hf : N ≤ 4000) : enumCheckN n gs N = true := by
  unfold enumCheckN certN
  rw [enumOK_of_bfsK hs hg hp hk hf, enumBfs_pts hs hg hk hf, Bool.true_and, Array.size_ofFn]
  exact beq_self_eq_true N

theorem anyN_eq (N : Nat) (f : Nat → Bool) : CFSG.KLie.CT.anyN N f = (List.range N).any f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change CFSG.KLie.CT.orB (f N) (CFSG.KLie.CT.anyN N f) = _
    rw [ih, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_comm]
    cases f N <;> rfl

theorem allN_eq' (N : Nat) (f : Nat → Bool) : allN N f = (List.range N).all f :=
  CFSG.KS.Raw.Orb.allN_eq N f

theorem sumN_count (N : Nat) (f : Nat → Bool) :
    CFSG.KLie.CT.sumN N (fun j => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f j)) =
      ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (f N)) (CFSG.KLie.CT.sumN N _) = _
    rw [ih, List.range_succ, List.filter_append, List.length_append]
    cases h : f N <;> simp [h, Nat.add_comm]

theorem inLN_PP {N p : Nat} {T : Nat → Nat} (hp : PP n w p) (hT : ∀ i < N, PP n w (T i)) :
    inLN n ((List.range N).map fun i => unpack n w (T i)) (unpack n w p) =
      (List.range N).any fun j => Nat.beq p (T j) := by
  unfold inLN
  rw [List.any_map]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor <;> rintro ⟨j, hj, h⟩
  · exact ⟨j, hj, by rwa [eqA_PP hp (hT j hj)] at h⟩
  · exact ⟨j, hj, by rwa [eqA_PP hp (hT j hj)]⟩

end CFSG.KC.BfsPin

end
