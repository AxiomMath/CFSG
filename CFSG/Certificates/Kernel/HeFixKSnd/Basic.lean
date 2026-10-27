
module

public import CFSG.Certificates.Kernel.LocalCompPinSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.HexaKGlue
import all CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.HeFixKFix

public section

namespace CFSG.KC.HeFixKSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native

variable {n w : Nat}

theorem beq_unpack_PP {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    (unpack n w p == unpack n w q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · apply beq_false_of_ne
    intro e
    exact Nat.ne_of_beq_eq_false h (CFSG.KS.PEnum.unpack_inj hp.1 hq.1 e)
  · have := Nat.eq_of_beq_eq_true h
    subst this
    exact beq_self_eq_true _

theorem comp_unpack_PP {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  CFSG.KS.PEnum.comp_unpack hp.1 hq.1

theorem invTab_unpack_PP {p : Nat} (hp : PP n w p) :
    invTab n (unpack n w p) = unpack n w (pinvS n w (mask w) p) :=
  invCand_PP hp

theorem idTab_unpack_PP (hsz : szOK n w = true) : idTab n = unpack n w (pidn n w) :=
  CFSG.KS.PEnum.idTab_unpack hsz

theorem getElem!_ofFn_lt {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {k : Nat}
    (hk : k < m) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem comp_assoc_tab {p q r : Tab} (hr : ∀ i < n, r[i]! < n) :
    comp n (comp n p q) r = comp n p (comp n q r) := by
  unfold comp
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    rw [getElem!_ofFn_lt _ (hr i hi)]
    rw [getElem!_ofFn_lt _ hi]

theorem size_unpack (p : Nat) : (unpack n w p).size = n := by simp [unpack]

theorem comp_inv_left_PP {p : Nat} (hp : PP n w p) :
    comp n (unpack n w (pinvS n w (mask w) p)) (unpack n w p) = idTab n := by
  have hw : n < 2 ^ w := by
    have := szOK_facts' hp.sz
    omega
  unfold comp idTab
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    have e1 : (unpack n w p)[i]! = pg w (mask w) p i := CFSG.KC.HeFixK.unpack_getElem! hi
    have e2 : pg w (mask w) p i < n := CFSG.KC.HeFixK.pg_lt_of_canonK hp.1 hi
    rw [e1, CFSG.KC.HeFixK.unpack_getElem! e2, CFSG.KS.PinvS.pg_pinvS hw hp.2 hi]

theorem unpack_lt_PP {p : Nat} (hp : PP n w p) {i : Nat} (hi : i < n) : (unpack n w p)[i]! < n := by
  rw [CFSG.KC.HeFixK.unpack_getElem! hi]
  exact CFSG.KC.HeFixK.pg_lt_of_canonK hp.1 hi

theorem conjTab_unpack_PP {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    conjTab n (unpack n w g) (unpack n w (pinvS n w (mask w) g)) (unpack n w y) =
      unpack n w (conj n w g y) := by
  rw [← conjA_PP hg hy, ← invCand_PP hg]
  unfold conjTab CFSG.RankThree.Native.conjA
  exact comp_assoc_tab (fun i hi => by rw [invCand_PP hg]; exact unpack_lt_PP hg.inv hi)

theorem conjInvTab_unpack_PP {g y : Nat} (hg : PP n w g) (hy : PP n w y) :
    conjTab n (unpack n w (pinvS n w (mask w) g)) (unpack n w g) (unpack n w y) =
      unpack n w (conjInv n w g y) := by
  rw [← conjInvA_PP hg hy, ← invCand_PP hg]
  unfold conjTab CFSG.RankThree.Native.conjInvA
  exact comp_assoc_tab (fun i hi => unpack_lt_PP hg hi)

theorem pin_enum {gs : Array Tab} {g N cap : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs.toList g G N T E S) (hf : N ≤ cap) :
    enumOK n gs (enumBFS n gs cap) = true ∧
      (enumBFS n gs cap).tabs = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
  have hs : gs.size = g := by simpa using p.size
  have hg : ∀ k < g, gs[k]! = unpack n w (G k) := by simpa using p.bind
  exact CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hg p.ok hf

theorem pin_size {gs : Array Tab} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs.toList g G N T E S) : gs.size = g := by simpa using p.size

theorem pin_bind {gs : Array Tab} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs.toList g G N T E S) : ∀ k < g, gs[k]! = unpack n w (G k) := by
  simpa using p.bind

theorem pin_gen_PP {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) : ∀ k < g, PP n w (G k) :=
  PP_gen p.ok p.perm

theorem pin_pts_PP {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (p : Pin n w gs g G N T E S) : ∀ i < N, PP n w (T i) :=
  PP_pts p.ok p.perm

end CFSG.KC.HeFixKSnd

end
