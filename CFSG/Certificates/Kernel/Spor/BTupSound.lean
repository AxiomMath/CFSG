module

public import Certificates.Data.Kernel.Spor.BTup
public import Certificates.Data.Kernel.Spor.Chain
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btSl_spec {n w m d kw km k cnt base lo len : Nat} {G K R POS : Nat → Nat}
    (h : btSlK n w m d kw km k cnt base G K R POS lo len = true) {i : Nat} (h1 : lo ≤ i)
    (h2 : i < lo + len) (hi : i < cnt) : btPtK n w m d kw km k cnt base G K R POS i = true := by
  unfold btSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

theorem btMov_spec {w d g x y : Nat} (h : btMov w (mask w) d g x y = true) :
    ∀ t < d, pg w (mask w) y t = pg w (mask w) g (pg w (mask w) x t) := fun t ht =>
  Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 h t ht)

structure PtFacts (n w d kw km k cnt base : Nat) (G K R POS : Nat → Nat) (i : Nat) : Prop where
  canon : btKey kw km K i >>> (d * w) = 0
  lt : ∀ t < d, pg w (mask w) (btKey kw km K i) t < n
  sorted : i + 1 < cnt → btKey kw km K i < btKey kw km K (i + 1)
  root : btDep (btRec R i) = 0 → btKey kw km K i = base
  tree : btDep (btRec R i) ≠ 0 → btPar (btRec R i) < cnt ∧ btLab (btRec R i) < k ∧
    btDep (btRec R (btPar (btRec R i))) + 1 = btDep (btRec R i) ∧
    ∀ t < d, pg w (mask w) (btKey kw km K i) t =
      pg w (mask w) (G (btLab (btRec R i))) (pg w (mask w) (btKey kw km K (btPar (btRec R i))) t)
  clos : ∀ j < k, btPos POS k i j < cnt ∧ ∀ t < d,
    pg w (mask w) (btKey kw km K (btPos POS k i j)) t =
      pg w (mask w) (G j) (pg w (mask w) (btKey kw km K i) t)

theorem ptFacts {n w d kw km k cnt base i : Nat} {G K R POS : Nat → Nat}
    (h : btPtK n w (mask w) d kw km k cnt base G K R POS i = true) :
    PtFacts n w d kw km k cnt base G K R POS i := by
  unfold btPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hs, ht, hcl⟩ := h
  unfold btCanon at hc
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  refine ⟨?_, fun t ht' => Nat.blt_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 hc.2 t ht'), fun hi => ?_,
    fun h0 => ?_, fun h0 => ?_, fun j hj => ?_⟩
  · have e := Nat.beq_eq.mp hc.1
    change btKey kw km K i >>> (w * d) = 0 at e
    rwa [Nat.mul_comm] at e
  · rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hi)] at hs
    exact Nat.blt_eq.mp hs
  · rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (Nat.beq_eq.mpr h0)] at ht
    exact Nat.beq_eq.mp ht
  · have h0' : Nat.beq (btDep (btRec R i)) (nat_lit 0) = false := by
      cases e : Nat.beq (btDep (btRec R i)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.beq_eq.mp e) h0
    rw [CFSG.KS.Raw.Orb.bIf_eq, h0', if_neg Bool.false_ne_true, CFSG.KS.Raw.Orb.strictB_eq,
      CFSG.KS.Raw.Orb.strictB_eq] at ht
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.beq_eq.mp h3, btMov_spec h4⟩
  · have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hcl j hj
    rw [CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true] at h1
    exact ⟨Nat.blt_eq.mp h1.1, btMov_spec h1.2⟩

section Orbit

variable {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n}

@[expose] def genSub (n k : Nat) (gp : Nat → Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ j < k, gp j = g}

theorem gp_mem {n k j : Nat} {gp : Nat → Equiv.Perm (Fin n)} (hj : j < k) :
    gp j ∈ genSub n k gp :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

variable (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
include hg hb hp

theorem btKey_mem_dep : ∀ D i, i < cnt → btDep (btRec R i) = D →
    ∃ h ∈ genSub n k gp, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t) := by
  intro D
  induction D with
  | zero =>
    intro i hi hD
    refine ⟨1, Subgroup.one_mem _, fun t => ?_⟩
    rw [(ptFacts (hp i hi)).root hD, hb t, Equiv.Perm.one_apply]
  | succ D ih =>
    intro i hi hD
    obtain ⟨hpar, hlab, hdep, hmov⟩ := (ptFacts (hp i hi)).tree (by omega)
    obtain ⟨h, hh, he⟩ := ih _ hpar (by omega)
    refine ⟨gp (btLab (btRec R i)) * h, Subgroup.mul_mem _ (gp_mem hlab) hh, fun t => ?_⟩
    rw [hmov t t.2, he t, hg _ hlab, Equiv.Perm.mul_apply]

theorem btKey_mem {i : Nat} (hi : i < cnt) :
    ∃ h ∈ genSub n k gp, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t) :=
  btKey_mem_dep hg hb hp _ i hi rfl

omit hg in
theorem btBase_dep : ∀ D i, i < cnt → btDep (btRec R i) = D →
    ∃ i₀ < cnt, ∀ t : Fin d, pg w (mask w) (btKey kw km K i₀) t = b t := by
  intro D
  induction D with
  | zero =>
    intro i hi hD
    exact ⟨i, hi, fun t => by rw [(ptFacts (hp i hi)).root hD, hb t]⟩
  | succ D ih =>
    intro i hi hD
    obtain ⟨hpar, -, hdep, -⟩ := (ptFacts (hp i hi)).tree (by omega)
    exact ih _ hpar (by omega)

@[expose] def stSet (n w d kw km cnt : Nat) (K : Nat → Nat) : Set (Fin d → Fin n) :=
  {v | ∃ i < cnt, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = v t}

omit hb in
theorem stSet_gen {v : Fin d → Fin n} (hv : v ∈ stSet n w d kw km cnt K) {j : Nat} (hj : j < k) :
    (fun t => gp j (v t)) ∈ stSet n w d kw km cnt K := by
  obtain ⟨i, hi, he⟩ := hv
  obtain ⟨hq, hm⟩ := (ptFacts (hp i hi)).clos j hj
  exact ⟨_, hq, fun t => by rw [hm t t.2, he t, hg j hj]⟩

omit hb in
theorem stSet_sub {h : Equiv.Perm (Fin n)} (hh : h ∈ genSub n k gp) :
    ∀ v ∈ stSet n w d kw km cnt K, (fun t => h (v t)) ∈ stSet n w d kw km cnt K := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact fun v hv => stSet_gen hg hp hv hj
  | one => exact fun v hv => hv
  | mul x y _ _ hx hy => exact fun v hv => hx _ (hy v hv)
  | inv x _ hx =>
    intro v hv
    have hm : Set.MapsTo (fun u : Fin d → Fin n => fun t => x (u t)) (stSet n w d kw km cnt K)
        (stSet n w d kw km cnt K) := fun u hu => hx u hu
    have hinj : Set.InjOn (fun u : Fin d → Fin n => fun t => x (u t))
        (stSet n w d kw km cnt K) := fun u _ u' _ e =>
      funext fun t => x.injective (congrFun e t)
    obtain ⟨u, hu, e⟩ := ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo hm).1 hinj |>.surjOn hv
    have e' : (fun t => x⁻¹ (v t)) = u := funext fun t => by
      rw [← e]
      exact Equiv.symm_apply_apply x (u t)
    rw [e']
    exact hu

theorem btKey_cover (hc : btHdK cnt = true) {h : Equiv.Perm (Fin n)} (hh : h ∈ genSub n k gp) :
    ∃ i < cnt, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t) := by
  have h0 : 0 < cnt := Nat.blt_eq.mp hc
  exact stSet_sub hg hp hh b (btBase_dep hb hp _ 0 h0 rfl)

end Orbit

theorem btKey_inj {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat} (hw : 0 < w)
    (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true) {i j : Nat}
    (hi : i < cnt) (hj : j < cnt)
    (h : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = pg w (mask w) (btKey kw km K j) t) :
    i = j := by
  have hmono : ∀ a c, a < c → c < cnt → btKey kw km K a < btKey kw km K c := by
    intro a c hac hc
    induction c with
    | zero => omega
    | succ c ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hac with h' | h'
      · exact lt_trans (ih h' (by omega)) ((ptFacts (hp c (by omega))).sorted hc)
      · subst h'
        exact (ptFacts (hp a (by omega))).sorted hc
  have e : btKey kw km K i = btKey kw km K j :=
    CFSG.KS.PF.eq_of_fields hw (ptFacts (hp i hi)).canon (ptFacts (hp j hj)).canon
      fun t ht => h ⟨t, ht⟩
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd e (Nat.ne_of_lt (hmono i j h' hj))
  · exact h'
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h' hi))

theorem btOrbit_card {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat}
    {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n} (hw : 0 < w)
    (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
    (hb : ∀ t : Fin d, pg w (mask w) base t = b t) (hc : btHdK cnt = true)
    (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true) :
    Nat.card {v : Fin d → Fin n // ∃ h ∈ genSub n k gp, ∀ t, v t = h (b t)} = cnt := by
  let φ : Fin cnt → Fin d → Fin n := fun i t =>
    ⟨pg w (mask w) (btKey kw km K i) t, (ptFacts (hp i i.2)).lt t t.2⟩
  have hφ : ∀ i : Fin cnt, ∃ h ∈ genSub n k gp, ∀ t, φ i t = h (b t) := fun i => by
    obtain ⟨h, hh, he⟩ := btKey_mem hg hb hp i.2
    exact ⟨h, hh, fun t => Fin.ext (he t)⟩
  let ψ : Fin cnt → {v : Fin d → Fin n // ∃ h ∈ genSub n k gp, ∀ t, v t = h (b t)} :=
    fun i => ⟨φ i, hφ i⟩
  have hbij : Function.Bijective ψ := by
    refine ⟨fun i j e => Fin.ext (btKey_inj hw hp i.2 j.2 fun t => ?_), fun v => ?_⟩
    · have := congrArg (fun v => (v.1 t : Nat)) e
      exact this
    · obtain ⟨v, h, hh, hv⟩ := v
      obtain ⟨i, hi, he⟩ := btKey_cover hg hb hp hc hh
      exact ⟨⟨i, hi⟩, Subtype.ext (funext fun t => Fin.ext (by
        change pg w (mask w) (btKey kw km K i) t = (v t : Nat)
        rw [he t, hv t]))⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_eq_orbit_card {n d : Nat} (H : Subgroup (Equiv.Perm (Fin n))) (b : Fin d → Fin n)
    (hfix : ∀ h ∈ H, (∀ t, h (b t) = b t) → h = 1) :
    Nat.card H = Nat.card {v : Fin d → Fin n // ∃ h ∈ H, ∀ t, v t = h (b t)} := by
  let ψ : H → {v : Fin d → Fin n // ∃ h ∈ H, ∀ t, v t = h (b t)} :=
    fun h => ⟨fun t => h.1 (b t), h.1, h.2, fun _ => rfl⟩
  have hbij : Function.Bijective ψ := by
    refine ⟨fun h₁ h₂ e => ?_, fun v => ?_⟩
    · have he : ∀ t, h₁.1 (b t) = h₂.1 (b t) := fun t => congrFun (congrArg Subtype.val e) t
      have h1 := hfix (h₂.1⁻¹ * h₁.1) (Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂.2) h₁.2)
        fun t => by
          rw [Equiv.Perm.mul_apply, he t]
          exact Equiv.symm_apply_apply h₂.1 (b t)
      exact Subtype.ext (inv_mul_eq_one.1 h1).symm
    · obtain ⟨v, h, hh, hv⟩ := v
      exact ⟨⟨h, hh⟩, Subtype.ext (funext fun t => (hv t).symm)⟩
  exact Nat.card_congr (Equiv.ofBijective ψ hbij)

end CFSG.KS.BTup

end
