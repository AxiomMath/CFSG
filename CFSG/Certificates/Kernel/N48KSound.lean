module

public import Certificates.Data.Kernel.N48K
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48NTests
import CFSG.Certificates.Kernel.N48KGlue

public section

namespace CFSG.KC.N48K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.N48
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Q47
open CFSG.KLie.CT (orB notB)

@[expose] def nInvG (gs : List (Array ℕ)) : List (Array ℕ) :=
  (eltsN 64 gs).filter fun a => eqA 64 (mulN 64 a a) (idA 64)

@[expose] def rankCheckG (gs : List (Array ℕ)) : Bool :=
  (nInvG gs).all fun a => (nInvG gs).all fun b => (nInvG gs).all fun c =>
    !(commN 64 a b) || !(commN 64 a c) || !(commN 64 b c) || eqA 64 a (idA 64) ||
      eqA 64 b (idA 64) || eqA 64 b a || eqA 64 c (idA 64) || eqA 64 c a || eqA 64 c b ||
        eqA 64 c (mulN 64 a b)

@[expose] def n48CheckG (gs : List (Array ℕ)) : Bool :=
  enumCheckN 64 gs 336 && rankCheckG gs && (nInvG gs).all fun a => (nInvG gs).all fun b =>
    pairCheck a b

theorem n48Check_eq : n48Check = n48CheckG q47NGens := rfl

theorem n48K_sound {w : Nat} {gs : List (Array ℕ)} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin 64 w gs g G N T E S) (hN : N = 336)
    (hr : ∀ i < (invL w N T).length, rankRowK w (invL w N T) i = true)
    (hp : ∀ i < (invL w N T).length, pairRowK w (invL w N T) i = true) :
    n48CheckG gs = true := by
  have sT := PP_pts p.ok p.perm
  have hI : nInvG gs = (invL w N T).map (unpack 64 w) := by
    unfold nInvG
    rw [eltsN_eq p.size p.bind p.ok p.fuel, filter_sq_eq sT]
  have pI : ∀ a ∈ invL w N T, PP 64 w a := fun a ha => mem_invL sT ha
  have row : ∀ {f : Array ℕ → Bool} {g : Nat → Bool},
      (∀ a ∈ invL w N T, f (unpack 64 w a) = g a) →
      (∀ i < (invL w N T).length, g ((invL w N T).getD i 0) = true) →
      ((invL w N T).map (unpack 64 w)).all f = true := by
    intro f g hfg hg
    rw [all_map_congr hfg, List.all_eq_true]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have h := hg i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  unfold n48CheckG
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hN ▸ enumCheckN_of p.size p.bind p.perm p.ok p.fuel, ?_⟩, ?_⟩
  · unfold rankCheckG
    rw [hI]
    refine row (g := fun a => (invL w N T).all fun b => (invL w N T).all fun c =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (comm 64 w a b)) (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (comm 64 w a c)) (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (comm 64 w b c))
        (CFSG.KLie.CT.orB (Nat.beq a (pidn 64 w)) (CFSG.KLie.CT.orB (Nat.beq b (pidn 64 w)) (CFSG.KLie.CT.orB (Nat.beq b a)
          (CFSG.KLie.CT.orB (Nat.beq c (pidn 64 w)) (CFSG.KLie.CT.orB (Nat.beq c a) (CFSG.KLie.CT.orB (Nat.beq c b)
            (Nat.beq c (mul 64 w a b))))))))))) (fun a ha => ?_) fun i hi => by
      have h := hr i hi
      unfold rankRowK at h
      rwa [strictB_eq'] at h
    have pa := pI a ha
    refine all_map_congr fun b hb => all_map_congr fun c hc => ?_
    have pb := pI b hb
    have pc := pI c hc
    rw [commN_PP pa pb, commN_PP pa pc, commN_PP pb pc, eqA_id_PP pa, eqA_id_PP pb, eqA_PP pb pa,
      eqA_id_PP pc, eqA_PP pc pa, eqA_PP pc pb, mulN_PP pa pb, eqA_PP pc (pa.mul pb)]
    simp only [orB_eq, notB_eq, Bool.or_assoc]
    rfl
  · rw [hI]
    refine row (g := fun a => (invL w N T).all fun b => pairK w a b) (fun a ha => ?_)
      fun i hi => by
      have h := hp i hi
      unfold pairRowK at h
      rwa [strictB_eq'] at h
    exact all_map_congr fun b hb => pairCheck_eq (pI a ha) (pI b hb)

end CFSG.KC.N48K

end
