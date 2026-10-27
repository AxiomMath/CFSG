
module

public import Certificates.Data.Kernel.L34K
public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import CFSG.Certificates.Kernel.BfsPinAlg
import all CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.L34KSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

variable {n w : Nat}

theorem andB_iff {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [CFSG.KLie.CT.andB]

theorem orB_iff {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [CFSG.KLie.CT.orB]

theorem notB_iff {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

theorem unpack_inj' {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : unpack n w p = unpack n w q) : p = q :=
  CFSG.KS.PEnum.unpack_inj hp hq h

theorem comp_unpack' {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  CFSG.KS.PEnum.comp_unpack hp hq

theorem idTab_unpack' (hsz : szOK n w = true) : idTab n = unpack n w (pidn n w) :=
  CFSG.KS.PEnum.idTab_unpack hsz

theorem canon_sz {p : Nat} (hp : canonK n w (mask w) (n * w) p = true) : szOK n w = true := by
  unfold canonK at hp
  exact ((bAnd_iff _ _).1 hp).1

theorem canon_lt {p i : Nat} (hp : canonK n w (mask w) (n * w) p = true) (hi : i < n) :
    pg w (mask w) p i < n :=
  (CFSG.KS.PF.canon_facts hp).2.2.2 i hi

theorem canon_pidn (hsz : szOK n w = true) : canonK n w (mask w) (n * w) (pidn n w) = true :=
  (CFSG.KC.BfsPin.PP.id hsz).1

theorem pts_get {N i : Nat} {T : Nat → Nat} (hi : i < N) :
    (Array.ofFn (n := N) fun j => unpack n w (T j.val))[i]! = unpack n w (T i) := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {A : Array α} {i : Nat}
    (hi : i < A.size) : (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

theorem size_unpack (p : Nat) : (unpack n w p).size = n := by simp [unpack]

theorem eq_of_pg {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true)
    (h : ∀ i < n, pg w (mask w) p i = pg w (mask w) q i) : p = q := by
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hq
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0 h

theorem pg_pcomp' {p q i : Nat} (hp : canonK n w (mask w) (n * w) p = true) (hi : i < n) :
    pg w (mask w) (pcomp n w (mask w) p q) i = pg w (mask w) p (pg w (mask w) q i) := by
  have hn := (CFSG.KS.PF.canon_facts hp).1
  exact CFSG.KS.PF.pg_pcomp (by omega) hi

theorem pg_pidn' {i : Nat} (hsz : szOK n w = true) (hi : i < n) : pg w (mask w) (pidn n w) i = i := by
  obtain ⟨hn, hw⟩ := CFSG.KC.BfsPin.szOK_facts' hsz
  exact CFSG.KS.PF.pg_pidn hn hw hi

theorem pcomp_assoc' {p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  refine eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hp hq) hr)
    (CFSG.KC.BfsPin.canonK_pcomp hp (CFSG.KC.BfsPin.canonK_pcomp hq hr)) fun i hi => ?_
  rw [pg_pcomp' (CFSG.KC.BfsPin.canonK_pcomp hp hq) hi, pg_pcomp' hp hi, pg_pcomp' hq hi,
    pg_pcomp' hp (canon_lt hr hi)]

theorem beq_unpack {p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    (unpack n w p == unpack n w q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · apply beq_false_of_ne
    intro e
    exact Nat.ne_of_beq_eq_false h (CFSG.KS.PEnum.unpack_inj hp hq e)
  · have := Nat.eq_of_beq_eq_true h
    subst this
    exact beq_self_eq_true _

theorem unpack_eq_idTab_iff {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    unpack n w x = idTab n ↔ x = pidn n w := by
  rw [CFSG.KS.PEnum.idTab_unpack (canon_sz hx)]
  exact ⟨CFSG.KS.PEnum.unpack_inj hx (canon_pidn (canon_sz hx)), fun e => by rw [e]⟩

theorem commPt_iff {x g : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hg : canonK n w (mask w) (n * w) g = true) :
    commPt n w x g = true ↔
      comp n (unpack n w x) (unpack n w g) = comp n (unpack n w g) (unpack n w x) := by
  rw [CFSG.KS.PEnum.comp_unpack hx hg, CFSG.KS.PEnum.comp_unpack hg hx]
  unfold commPt
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    have e : pcomp n w (mask w) x g = pcomp n w (mask w) g x :=
      eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp hx hg) (CFSG.KC.BfsPin.canonK_pcomp hg hx)
        fun i hi => by
          rw [pg_pcomp' hx hi, pg_pcomp' hg hi]
          exact Nat.beq_eq.mp (h i hi)
    rw [e]
  · intro h i hi
    have h' : (unpack n w (pcomp n w (mask w) x g))[i]! =
        (unpack n w (pcomp n w (mask w) g x))[i]! := congrArg (fun a : Tab => a[i]!) h
    rw [CFSG.KC.BfsPin.unpack_get' hi, CFSG.KC.BfsPin.unpack_get' hi, pg_pcomp' hx hi,
      pg_pcomp' hg hi] at h'
    exact Nat.beq_eq.mpr h'

theorem invPt_iff {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    invPt n w x = true ↔ comp n (unpack n w x) (unpack n w x) = idTab n := by
  have hsz := canon_sz hx
  rw [CFSG.KS.PEnum.comp_unpack hx hx, CFSG.KS.PEnum.idTab_unpack hsz]
  unfold invPt
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    have e : pcomp n w (mask w) x x = pidn n w :=
      eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp hx hx) (canon_pidn hsz) fun i hi => by
        rw [pg_pcomp' hx hi, pg_pidn' hsz hi]
        exact Nat.beq_eq.mp (h i hi)
    rw [e]
  · intro h i hi
    have h' : (unpack n w (pcomp n w (mask w) x x))[i]! = (unpack n w (pidn n w))[i]! :=
      congrArg (fun a : Tab => a[i]!) h
    rw [CFSG.KC.BfsPin.unpack_get' hi, CFSG.KC.BfsPin.unpack_get' hi, pg_pcomp' hx hi,
      pg_pidn' hsz hi] at h'
    exact Nat.beq_eq.mpr h'

theorem injK_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    CFSG.KS.PinvS.InjK n w g ∧ CFSG.KS.PinvS.InjK n w gi ∧
      ∀ i < n, pg w (mask w) g (pg w (mask w) gi i) = i ∧
        pg w (mask w) gi (pg w (mask w) g i) = i := by
  have hsz := canon_sz hg
  have h1 : ∀ i < n, pg w (mask w) g (pg w (mask w) gi i) = i := fun i hi => by
    have h' : pg w (mask w) (pcomp n w (mask w) g gi) i = pg w (mask w) (pidn n w) i :=
      congrArg (fun p => pg w (mask w) p i) h
    rwa [pg_pcomp' hg hi, pg_pidn' hsz hi] at h'
  have hI : CFSG.KS.PinvS.InjK n w gi :=
    ⟨fun i hi => canon_lt hgi hi, fun a ha b hb e => by rw [← h1 a ha, ← h1 b hb, e]⟩
  have h2 : ∀ i < n, pg w (mask w) gi (pg w (mask w) g i) = i := fun i hi => by
    obtain ⟨x, hx, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hI i hi
    rw [h1 x hx]
  refine ⟨⟨fun i hi => canon_lt hg hi, fun a ha b hb e => ?_⟩, hI, fun i hi => ⟨h1 i hi, h2 i hi⟩⟩
  rw [← h2 a ha, ← h2 b hb, e]

theorem pinvS_eq_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    pinvS n w (mask w) g = gi := by
  obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts hg
  obtain ⟨hI, -, hinv⟩ := injK_of_pcomp hg hgi h
  refine eq_of_pg (CFSG.KS.PinvS.canonK_pinvS hg hI) hgi fun i hi => ?_
  have := CFSG.KS.PinvS.pg_pinvS (by omega) hI (canon_lt hgi hi)
  rwa [(hinv i hi).1] at this

theorem invTab_eq_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    invTab n (unpack n w g) = unpack n w gi := by
  rw [← pinvS_eq_of_pcomp hg hgi h]
  exact CFSG.KC.BfsPin.invCand_PP ⟨hg, (injK_of_pcomp hg hgi h).1⟩

theorem pcomp_inv_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    pcomp n w (mask w) gi g = pidn n w := by
  have hsz := canon_sz hg
  obtain ⟨-, -, hinv⟩ := injK_of_pcomp hg hgi h
  refine eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp hgi hg) (canon_pidn hsz) fun i hi => ?_
  rw [pg_pcomp' hgi hi, pg_pidn' hsz hi]
  exact (hinv i hi).2

theorem comp_inv_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    comp n (unpack n w gi) (unpack n w g) = idTab n := by
  rw [CFSG.KS.PEnum.comp_unpack hgi hg, pcomp_inv_of_pcomp hg hgi h,
    CFSG.KS.PEnum.idTab_unpack (canon_sz hg)]

theorem invsOK_of_pcomp {gs : Array Tab} {ng : Nat} {G GI : Nat → Nat} (hs : gs.size = ng)
    (hb : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hc : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true ∧
      canonK n w (mask w) (n * w) (GI k) = true ∧ pcomp n w (mask w) (G k) (GI k) = pidn n w) :
    (∀ k < ng, (gs.map (invTab n))[k]! = unpack n w (GI k)) ∧
      invsOK n gs (gs.map (invTab n)) = true := by
  have hi : ∀ k < ng, (gs.map (invTab n))[k]! = unpack n w (GI k) := fun k hk => by
    rw [map_get _ (by omega), hb k hk]
    exact invTab_eq_of_pcomp (hc k hk).1 (hc k hk).2.1 (hc k hk).2.2
  refine ⟨hi, ?_⟩
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  rw [hs] at hk
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hi k hk, hb k hk]
  exact ⟨size_unpack _, comp_inv_of_pcomp (hc k hk).1 (hc k hk).2.1 (hc k hk).2.2⟩

theorem inj_of_distSl {N L K : Nat} {T S SI : Nat → Nat} (hN : N = L * K) (hL : 0 < L)
    (h : ∀ s < K, distSl N T S SI L s = true) : ∀ a < N, ∀ b < N, T a = T b → a = b := by
  refine CFSG.KS.PEnum.inj_of_sort (S := S) (SI := SI) fun i hi => ?_
  have hs : i / L < K := by
    rw [hN] at hi
    exact Nat.div_lt_of_lt_mul hi
  have h1 := h (i / L) hs
  unfold distSl at h1
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (i % L) (Nat.mod_lt _ hL)
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [e, strictB_app, strictB_app] at h2
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  obtain ⟨h5, h6⟩ := andB_iff.1 h4
  refine ⟨Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h5, fun hi1 => ?_⟩
  rcases orB_iff.1 h6 with h7 | h7
  · exact absurd (Nat.eq_of_beq_eq_true h7) (by omega)
  · exact Nat.blt_eq.mp h7

theorem canon_of_canonSl {N L K : Nat} {T : Nat → Nat} (hN : N = L * K) (hL : 0 < L)
    (h : ∀ s < K, canonSl n w T L s = true) : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  intro i hi
  have hs : i / L < K := by
    rw [hN] at hi
    exact Nat.div_lt_of_lt_mul hi
  have h1 := h (i / L) hs
  unfold canonSl at h1
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (i % L) (Nat.mod_lt _ hL)
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rwa [e] at h2

theorem filter_range_eq_map {N m : Nat} {p : Nat → Bool} {I : Nat → Nat}
    (hI : ∀ k < m, I k < N ∧ (k + 1 < m → I k < I (k + 1)) ∧ p (I k) = true)
    (hm : ((List.range N).filter p).length = m) :
    (List.range N).filter p = (List.range m).map I := by
  have hmono : ∀ a b, a < b → b < m → I a < I b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact lt_trans (ih h (by omega)) ((hI b (by omega)).2.1 hb)
      · subst h
        exact (hI a (by omega)).2.1 hb
  have hsL : List.Pairwise (· < ·) ((List.range m).map I) :=
    List.pairwise_map.2 ((List.pairwise_lt_range (n := m)).imp_of_mem
      fun _ hb hab => hmono _ _ hab (List.mem_range.1 hb))
  have hsF : List.Pairwise (· < ·) ((List.range N).filter p) :=
    (List.pairwise_lt_range (n := N)).filter p
  have hsub : (List.range m).map I ⊆ (List.range N).filter p := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hk' := List.mem_range.1 hk
    exact List.mem_filter.2 ⟨List.mem_range.2 (hI k hk').1, (hI k hk').2.2⟩
  have hperm : List.Perm ((List.range m).map I) ((List.range N).filter p) :=
    (List.subperm_of_subset hsL.nodup hsub).perm_of_length_le (by simp [hm])
  exact (List.Perm.eq_of_pairwise (fun a _ _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl a))
    hsL hsF hperm).symm

theorem anyBelow_iff {m : Nat} {f : Nat → Bool} : anyBelow m f = true ↔ ∃ i < m, f i = true := by
  unfold anyBelow
  rw [List.any_eq_true]
  simp

theorem found_pts {N q X : Nat} {T : Nat → Nat} (hq : q < N) (e : T q = X) :
    found (indexOf (Array.ofFn (n := N) fun i => unpack n w (T i.val)))
      (Array.ofFn (n := N) fun i => unpack n w (T i.val)) (unpack n w X) = true := by
  rw [CFSG.KS.PEnum.found_indexOf_iff]
  exact ⟨q, by simpa using hq, by rw [pts_get hq, e]⟩

end CFSG.KC.L34KSnd

end
