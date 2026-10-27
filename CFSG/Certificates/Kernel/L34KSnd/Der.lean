
module

public import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34KSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native

variable {n w : Nat}

structure DerF (n w m : Nat) (T TI : Nat → Nat) (m' : Nat) (D : Nat → Nat) : Prop where
  canT : ∀ a < m, canonK n w (mask w) (n * w) (T a) = true
  canTI : ∀ a < m, canonK n w (mask w) (n * w) (TI a) = true
  invT : ∀ a < m, pcomp n w (mask w) (TI a) (T a) = pidn n w
  pos : 0 < m'
  one : D 0 = pidn n w
  canD : ∀ a < m', canonK n w (mask w) (n * w) (D a) = true
  inv : ∀ a < m', ∃ q < m', pcomp n w (mask w) (D q) (D a) = pidn n w
  dist : ∀ a < m', ∀ b < m', D a = D b → a = b
  mul : ∀ a < m', ∀ b < m', ∃ q < m', D q = pcomp n w (mask w) (D a) (D b)
  comm : ∀ a < m, ∀ b < m, ∃ c < m', D c = commK n w T TI a b
  wit : ∀ a < m', ∃ a₁ < m, ∃ a₂ < m, ∃ a₃ < m, ∃ a₄ < m,
    D a = pcomp n w (mask w) (commK n w T TI a₁ a₂) (commK n w T TI a₃ a₄)

theorem derF_of_derK {m m' IW W : Nat} {T TI D PW CW : Nat → Nat}
    (h : derK n w m T TI m' D PW CW IW W = true) : DerF n w m T TI m' D := by
  unfold derK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  obtain ⟨hT, h⟩ := andB_iff.1 h
  obtain ⟨h0, h⟩ := andB_iff.1 h
  obtain ⟨hD, h⟩ := andB_iff.1 h
  obtain ⟨hC, hW⟩ := andB_iff.1 h
  obtain ⟨hpos, hone⟩ := andB_iff.1 h0
  have hDb : ∀ a < m', ∀ b < m',
      (Nat.beq a b = true ∨ CFSG.KLie.CT.notB (Nat.beq (D a) (D b)) = true) ∧
        ∃ q < m', D q = pcomp n w (mask w) (D a) (D b) := by
    intro a ha b hb
    have h3 := (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hD a ha)).2
    rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h3
    have h8 := CFSG.KS.Raw.Orb.allN_iff.1 (andB_iff.1 h3).2 b hb
    rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h8
    obtain ⟨h9, h10⟩ := andB_iff.1 h8
    obtain ⟨h11, h12⟩ := andB_iff.1 h10
    exact ⟨orB_iff.1 h9, _, Nat.blt_eq.mp h11, Nat.eq_of_beq_eq_true h12⟩
  refine ⟨fun a ha => (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hT a ha)).1,
    fun a ha => (andB_iff.1 (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hT a ha)).2).1,
    fun a ha => Nat.eq_of_beq_eq_true
      (andB_iff.1 (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hT a ha)).2).2,
    Nat.blt_eq.mp hpos, Nat.eq_of_beq_eq_true hone,
    fun a ha => (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hD a ha)).1, ?_, ?_,
    fun a ha b hb => (hDb a ha b hb).2, ?_, ?_⟩
  · intro a ha
    have h3 := (andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hD a ha)).2
    rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h3
    have h4 := (andB_iff.1 h3).1
    rw [CFSG.KC.BfsPin.strictB_app] at h4
    obtain ⟨h6, h7⟩ := andB_iff.1 h4
    exact ⟨_, Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩
  · intro a ha b hb e
    rcases (hDb a ha b hb).1 with h1 | h1
    · exact Nat.eq_of_beq_eq_true h1
    · exact absurd e (Nat.ne_of_beq_eq_false (notB_iff.1 h1))
  · intro a ha b hb
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hC a ha
    rw [CFSG.KC.BfsPin.strictB_app] at h1
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 b hb
    rw [CFSG.KC.BfsPin.strictB_app] at h2
    obtain ⟨h3, h4⟩ := andB_iff.1 h2
    exact ⟨_, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4⟩
  · intro a ha
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hW a ha
    rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app,
      CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h1
    obtain ⟨h2, h3⟩ := andB_iff.1 h1
    obtain ⟨h4, h5⟩ := andB_iff.1 h2
    obtain ⟨h6, h7⟩ := andB_iff.1 h5
    obtain ⟨h8, h9⟩ := andB_iff.1 h7
    exact ⟨_, Nat.blt_eq.mp h4, _, Nat.blt_eq.mp h6, _, Nat.blt_eq.mp h8, _, Nat.blt_eq.mp h9,
      Nat.eq_of_beq_eq_true h3⟩

private theorem mem_iff_get {X : Array Tab} {x : Tab} :
    x ∈ X.toList ↔ ∃ i < X.size, X[i]! = x := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [getElem!_pos X i hi, e]⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [← getElem!_pos X i hi, e]⟩

private theorem mem_pts {N : Nat} {T : Nat → Nat} {x : Tab} :
    x ∈ (Array.ofFn (n := N) fun i => unpack n w (T i.val)).toList ↔
      ∃ i < N, unpack n w (T i) = x := by
  rw [mem_iff_get, Array.size_ofFn]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [← pts_get hi, e]⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [pts_get hi, e]⟩

private theorem inj_of_nodup {X : Array Tab} (h : X.toList.Nodup) :
    ∀ a < X.size, ∀ b < X.size, X[a]! = X[b]! → a = b := by
  intro a ha b hb e
  rw [getElem!_pos X a ha, getElem!_pos X b hb] at e
  have ha' : a < X.toList.length := by simpa using ha
  have hb' : b < X.toList.length := by simpa using hb
  exact (List.Nodup.getElem_inj_iff h (hi := ha') (hj := hb')).1 (by simpa using e)

theorem derivedOK_of_derK {m m' IW W : Nat} {TT TI D PW CW : Nat → Nat} {A DD : Array Tab}
    {WW : Array (Nat × Nat × Nat × Nat)}
    (hA : ∀ x, x ∈ A.toList ↔ x ∈ (Array.ofFn (n := m) fun i => unpack n w (TT i.val)).toList)
    (h : derK n w m TT TI m' D PW CW IW W = true) (hnd : DD.toList.Nodup)
    (hsz : WW.size = DD.size)
    (hwit : ∀ i < DD.size, WW[i]!.1 < A.size ∧ WW[i]!.2.1 < A.size ∧ WW[i]!.2.2.1 < A.size ∧
      WW[i]!.2.2.2 < A.size ∧
      DD[i]! = comp n (commTab n A[WW[i]!.1]! A[WW[i]!.2.1]! (A.map (invTab n))[WW[i]!.1]!
          (A.map (invTab n))[WW[i]!.2.1]!)
        (commTab n A[WW[i]!.2.2.1]! A[WW[i]!.2.2.2]! (A.map (invTab n))[WW[i]!.2.2.1]!
          (A.map (invTab n))[WW[i]!.2.2.2]!))
    (hcomp : ∀ a₁ < A.size, ∀ a₂ < A.size, ∀ a₃ < A.size, ∀ a₄ < A.size,
      comp n (commTab n A[a₁]! A[a₂]! (A.map (invTab n))[a₁]! (A.map (invTab n))[a₂]!)
        (commTab n A[a₃]! A[a₄]! (A.map (invTab n))[a₃]! (A.map (invTab n))[a₄]!) ∈ DD.toList) :
    derivedOK n A (A.map (invTab n)) DD WW = true ∧ DD.size = m' ∧
      ∀ x, x ∈ DD.toList ↔ x ∈ (Array.ofFn (n := m') fun i => unpack n w (D i.val)).toList := by
  have F := derF_of_derK h
  have hTI : ∀ a < m, invTab n (unpack n w (TT a)) = unpack n w (TI a) := fun a ha =>
    invTab_eq_of_pcomp (F.canT a ha) (F.canTI a ha)
      (pcomp_inv_of_pcomp (F.canTI a ha) (F.canT a ha) (F.invT a ha))
  have hcK : ∀ a < m, ∀ b < m, canonK n w (mask w) (n * w) (commK n w TT TI a b) = true :=
    fun a ha b hb => CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp
      (CFSG.KC.BfsPin.canonK_pcomp (F.canT a ha) (F.canT b hb)) (F.canTI a ha)) (F.canTI b hb)
  have hcT : ∀ a < m, ∀ b < m, commTab n (unpack n w (TT a)) (unpack n w (TT b))
      (unpack n w (TI a)) (unpack n w (TI b)) = unpack n w (commK n w TT TI a b) := by
    intro a ha b hb
    unfold commTab CFSG.KC.L34K.commK
    rw [comp_unpack' (F.canT a ha) (F.canT b hb),
      comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp (F.canT a ha) (F.canT b hb)) (F.canTI a ha),
      comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp (F.canT a ha)
        (F.canT b hb)) (F.canTI a ha)) (F.canTI b hb)]
  have hAel : ∀ k < A.size, ∃ a < m, A[k]! = unpack n w (TT a) ∧
      (A.map (invTab n))[k]! = unpack n w (TI a) := by
    intro k hk
    obtain ⟨a, ha, e⟩ := mem_pts.1 ((hA _).1 (mem_iff_get.2 ⟨k, hk, rfl⟩))
    refine ⟨a, ha, e.symm, ?_⟩
    rw [map_get _ hk, ← e, hTI a ha]
  have hAmem : ∀ a < m, ∃ k < A.size, A[k]! = unpack n w (TT a) ∧
      (A.map (invTab n))[k]! = unpack n w (TI a) := by
    intro a ha
    obtain ⟨k, hk, e⟩ := mem_iff_get.1 ((hA _).2 (mem_pts.2 ⟨a, ha, rfl⟩))
    refine ⟨k, hk, e, ?_⟩
    rw [map_get _ hk, e, hTI a ha]
  have hcA : ∀ k < A.size, ∀ l < A.size, ∃ c < m',
      commTab n A[k]! A[l]! (A.map (invTab n))[k]! (A.map (invTab n))[l]! = unpack n w (D c) := by
    intro k hk l hl
    obtain ⟨a, ha, e1, e2⟩ := hAel k hk
    obtain ⟨b, hb, e3, e4⟩ := hAel l hl
    obtain ⟨c, hc, e5⟩ := F.comm a ha b hb
    exact ⟨c, hc, by rw [e1, e2, e3, e4, hcT a ha b hb, e5]⟩
  have hmul : ∀ p < m', ∀ q < m', ∃ r < m',
      comp n (unpack n w (D p)) (unpack n w (D q)) = unpack n w (D r) := by
    intro p hp q hq
    obtain ⟨r, hr, e⟩ := F.mul p hp q hq
    exact ⟨r, hr, by rw [comp_unpack' (F.canD p hp) (F.canD q hq), e]⟩
  have hset : ∀ x, x ∈ DD.toList ↔
      x ∈ (Array.ofFn (n := m') fun i => unpack n w (D i.val)).toList := by
    intro x
    rw [mem_pts]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_iff_get.1 hx
      obtain ⟨h1, h2, h3, h4, e⟩ := hwit i hi
      obtain ⟨c, hc, e1⟩ := hcA _ h1 _ h2
      obtain ⟨c', hc', e2⟩ := hcA _ h3 _ h4
      obtain ⟨r, hr, e3⟩ := hmul c hc c' hc'
      exact ⟨r, hr, by rw [e, e1, e2, e3]⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨a₁, h1, a₂, h2, a₃, h3, a₄, h4, e⟩ := F.wit p hp
      obtain ⟨k₁, hk₁, e₁, f₁⟩ := hAmem a₁ h1
      obtain ⟨k₂, hk₂, e₂, f₂⟩ := hAmem a₂ h2
      obtain ⟨k₃, hk₃, e₃, f₃⟩ := hAmem a₃ h3
      obtain ⟨k₄, hk₄, e₄, f₄⟩ := hAmem a₄ h4
      have hc := hcomp k₁ hk₁ k₂ hk₂ k₃ hk₃ k₄ hk₄
      rw [e₁, f₁, e₂, f₂, e₃, f₃, e₄, f₄, hcT a₁ h1 a₂ h2, hcT a₃ h3 a₄ h4,
        comp_unpack' (hcK a₁ h1 a₂ h2) (hcK a₃ h3 a₄ h4), ← e] at hc
      exact hc
  have hndP : (Array.ofFn (n := m') fun i => unpack n w (D i.val)).toList.Nodup := by
    rw [Array.toList_ofFn]
    exact List.nodup_ofFn.2 fun i j e =>
      Fin.ext (F.dist i i.2 j j.2 (unpack_inj' (F.canD i i.2) (F.canD j j.2) e))
  have hsize : DD.size = m' := by
    rw [← Array.length_toList, ((List.perm_ext_iff_of_nodup hnd hndP).2 hset).length_eq,
      Array.length_toList, Array.size_ofFn]
  refine ⟨?_, hsize, hset⟩
  have Dmem : ∀ p < m', unpack n w (D p) ∈ DD.toList := fun p hp =>
    (hset _).2 (mem_pts.2 ⟨p, hp, rfl⟩)
  have hfound : ∀ x, x ∈ DD.toList → found (indexOf DD) DD x = true := fun x hx =>
    (CFSG.KS.PEnum.found_indexOf_iff DD x).2 (mem_iff_get.1 hx)
  have hget : ∀ i < DD.size, ∃ p < m', DD[i]! = unpack n w (D p) := fun i hi => by
    obtain ⟨p, hp, e⟩ := mem_pts.1 ((hset _).1 (mem_iff_get.2 ⟨i, hi, rfl⟩))
    exact ⟨p, hp, e.symm⟩
  unfold derivedOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, beq_iff_eq.2 hsz⟩, ?_⟩
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, true_and]
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    obtain ⟨a, ha, e1, e2⟩ := hAel k hk
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [e2, e1]
    exact ⟨size_unpack _, comp_inv_of_pcomp (F.canT a ha) (F.canTI a ha)
      (pcomp_inv_of_pcomp (F.canTI a ha) (F.canT a ha) (F.invT a ha))⟩
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_
    unfold posOf
    rw [(CFSG.KS.BfsReplay.indexOf_spec (inj_of_nodup hnd)).1 i hi]
    exact beq_self_eq_true _
  · apply hfound
    rw [idTab_unpack' (canon_sz (F.canD 0 F.pos)), ← F.one]
    exact Dmem 0 F.pos
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi =>
      CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_
    obtain ⟨p, hp, e1⟩ := hget i hi
    obtain ⟨q, hq, e2⟩ := hget j hj
    obtain ⟨r, hr, e3⟩ := hmul p hp q hq
    rw [e1, e2, e3]
    exact hfound _ (Dmem r hr)
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_
    obtain ⟨p, hp, e1⟩ := hget i hi
    obtain ⟨q, hq, e2⟩ := F.inv p hp
    have e3 : pcomp n w (mask w) (D p) (D q) = pidn n w :=
      pcomp_inv_of_pcomp (F.canD q hq) (F.canD p hp) e2
    rw [e1, invTab_eq_of_pcomp (F.canD p hp) (F.canD q hq) e3, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hfound _ (Dmem q hq), comp_inv_of_pcomp (F.canD p hp) (F.canD q hq) e3⟩
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk =>
      CFSG.KS.BfsReplay.allBelow_iff.2 fun l hl => ?_
    obtain ⟨c, hc, e⟩ := hcA k hk l hl
    rw [e]
    exact hfound _ (Dmem c hc)
  · refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_
    obtain ⟨h1, h2, h3, h4, e⟩ := hwit i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, e⟩

end CFSG.KC.L34KSnd

end
