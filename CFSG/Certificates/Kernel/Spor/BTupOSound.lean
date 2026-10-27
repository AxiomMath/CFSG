module

public import Certificates.Data.Kernel.Spor.BTupO
public import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.Group

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btWalkF_succ (w m : Nat) (G R : Nat → Nat) (D i p : Nat) :
    btWalkF w m G R (D + 1) i p =
      pg w m (G (btLab (btRec R i))) (btWalkF w m G R D (btPar (btRec R i)) p) := by
  change strictN (btRec R i) (fun r => strictN (btWalkF w m G R D (btPar r) p)
    (fun q => pg w m (G (btLab r)) q)) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.strictN_eq]

theorem btPre_spec {n w d mc B : Nat} {C PRE : Nat → Nat} (h : btPreK n w (mask w) d mc B C PRE = true)
    {j t : Nat} (hj : j < mc) (ht : t < d) :
    btPre PRE d j t < n ∧ pg w (mask w) (C j) (btPre PRE d j t) = pg w (mask w) B t := by
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h j hj) t ht
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨Nat.blt_eq.mp h1.1, Nat.beq_eq.mp h1.2⟩

theorem btOcSl_spec {w m d kw km mc cnt B Wr lo len : Nat} {G K R C PRE TG : Nat → Nat}
    (h : btOcSlK w m d kw km mc cnt B Wr G K R C PRE TG lo len = true) {i : Nat} (h1 : lo ≤ i)
    (h2 : i < lo + len) (hi : i < cnt) : btOcK w m d kw km mc cnt B Wr G K R C PRE TG i = true := by
  unfold btOcSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

theorem btOcK_spec {w d kw km mc cnt B Wr : Nat} {G K R C PRE TG : Nat → Nat} {i : Nat}
    (h : btOcK w (mask w) d kw km mc cnt B Wr G K R C PRE TG i = true)
    (hin : btTgIn (btTg TG i) = true) :
    (btTgDep (btTg TG i) = 0 → btMov w (mask w) d Wr B (btKey kw km K i) = true) ∧
    (btTgDep (btTg TG i) ≠ 0 → btTgPar (btTg TG i) < cnt ∧ btTgLab (btTg TG i) < mc ∧
      btTgIn (btTg TG (btTgPar (btTg TG i))) = true ∧
      btTgDep (btTg TG (btTgPar (btTg TG i))) + 1 = btTgDep (btTg TG i) ∧
      ∀ t < d, pg w (mask w) (btKey kw km K i) t = pg w (mask w) (C (btTgLab (btTg TG i)))
        (btWalk w (mask w) G R (btTgPar (btTg TG i)) (btPre PRE d (btTgLab (btTg TG i)) t))) := by
  unfold btOcK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, if_pos hin,
    CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rwa [if_pos (Nat.beq_eq.mpr h0)] at h
  · have h0' : Nat.beq (btTgDep (btTg TG i)) (nat_lit 0) = false := by
      cases e : Nat.beq (btTgDep (btTg TG i)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.beq_eq.mp e) h0
    rw [h0', if_neg Bool.false_ne_true, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq,
      CFSG.KS.Raw.Orb.strictB_eq] at h
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, h3, Nat.beq_eq.mp h4,
      fun t ht => Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 h5 t ht)⟩

section Walk

variable {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n}
  (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
  (hfix : ∀ h ∈ genSub n k gp, (∀ t, h (b t) = b t) → h = 1)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
include hg hp hfix hb

theorem btWalk_dep : ∀ D i, i < cnt → btDep (btRec R i) = D → ∀ h ∈ genSub n k gp,
    (∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t)) → ∀ p : Fin n,
    btWalkF w (mask w) G R D i p = h p := by
  intro D
  induction D with
  | zero =>
    intro i hi hD h hh he p
    have h1 : h = 1 := hfix h hh fun t => Fin.ext (by
      rw [← he t, (ptFacts (hp i hi)).root hD, hb t])
    rw [h1]
    rfl
  | succ D ih =>
    intro i hi hD h hh he p
    obtain ⟨hpar, hlab, hdep, hmov⟩ := (ptFacts (hp i hi)).tree (by omega)
    set q := btPar (btRec R i)
    set l := btLab (btRec R i)
    have hh' : (gp l)⁻¹ * h ∈ genSub n k gp :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (gp_mem hlab)) hh
    have he' : ∀ t : Fin d, pg w (mask w) (btKey kw km K q) t = ((gp l)⁻¹ * h) (b t) := by
      intro t
      have hlt : pg w (mask w) (btKey kw km K q) t < n := (ptFacts (hp q hpar)).lt t t.2
      have e1 : gp l ⟨_, hlt⟩ = h (b t) := Fin.ext (by
        rw [← hg l hlab, ← he t, hmov t t.2])
      rw [Equiv.Perm.mul_apply, ← e1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [btWalkF_succ, ih q hpar (by omega) _ hh' he' p, hg l hlab, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem btWalk_spec {i : Nat} (hi : i < cnt) {h : Equiv.Perm (Fin n)} (hh : h ∈ genSub n k gp)
    (he : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t)) (p : Fin n) :
    btWalk w (mask w) G R i p = h p :=
  btWalk_dep hg hp hfix hb _ i hi rfl h hh he p

variable {mc Wr PRE0 : Nat} {C PRE TG : Nat → Nat} {c : Nat → Equiv.Perm (Fin n)}
  {W : Equiv.Perm (Fin n)}
  (hC : ∀ j < mc, ∀ x : Fin n, pg w (mask w) (C j) x = c j x)
  (hW : ∀ x : Fin n, pg w (mask w) Wr x = W x)
  (hpre : btPreK n w (mask w) d mc base C PRE = true)
  (hoc : ∀ i < cnt, btOcK w (mask w) d kw km mc cnt base Wr G K R C PRE TG i = true)
  (hX : ∀ y ∈ genSub n k gp, ∀ g ∈ genSub n mc c,
    (∀ t, y (b t) = (g * W * g⁻¹) (b t)) → y = g * W * g⁻¹)
include hC hW hpre hoc hX

theorem btOc_dep : ∀ D i, i < cnt → btTgIn (btTg TG i) = true → btTgDep (btTg TG i) = D →
    ∃ g ∈ genSub n mc c, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = (g * W * g⁻¹) (b t) := by
  intro D
  induction D with
  | zero =>
    intro i hi hin hD
    have hm := btMov_spec ((btOcK_spec (hoc i hi) hin).1 hD)
    refine ⟨1, Subgroup.one_mem _, fun t => ?_⟩
    rw [hm t t.2, hb t, hW, one_mul, inv_one, mul_one]
  | succ D ih =>
    intro i hi hin hD
    obtain ⟨hq, hl, hqin, hdep, hk⟩ := (btOcK_spec (hoc i hi) hin).2 (by omega)
    set q := btTgPar (btTg TG i)
    set l := btTgLab (btTg TG i)
    obtain ⟨g, hg', he⟩ := ih q hq hqin (by omega)
    obtain ⟨y, hy, hye⟩ := btKey_mem hg hb hp (kw := kw) (km := km) hq
    have hyg : y = g * W * g⁻¹ := hX y hy g hg' fun t => Fin.ext (by rw [← hye t, he t])
    refine ⟨c l * g, Subgroup.mul_mem _ (gp_mem hl) hg', fun t => ?_⟩
    obtain ⟨hplt, hpe⟩ := btPre_spec hpre hl t.2
    have e1 : c l ⟨_, hplt⟩ = b t := Fin.ext (by rw [← hC l hl, hpe, hb t])
    have e2 : (c l)⁻¹ (b t) = ⟨_, hplt⟩ := by
      rw [← e1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    have e3 : c l * g * W * (c l * g)⁻¹ = c l * (g * W * g⁻¹) * (c l)⁻¹ := by group
    rw [hk t t.2, btWalk_spec hg hp hfix hb hq hy hye ⟨_, hplt⟩, hC l hl, hyg, e3]
    simp only [Equiv.Perm.mul_apply]
    rw [e2]

theorem btOc_mem {i : Nat} (hi : i < cnt) (hin : btTgIn (btTg TG i) = true) :
    ∃ g ∈ genSub n mc c, ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = (g * W * g⁻¹) (b t) :=
  btOc_dep hg hp hfix hb hC hW hpre hoc hX _ i hi hin rfl

theorem btOc_card (hw : 0 < w) :
    btCntN cnt (fun i => btTgIn (btTg TG i)) ≤
      Nat.card {x : Equiv.Perm (Fin n) | ∃ g ∈ genSub n mc c, x = g * W * g⁻¹} := by
  rw [btCntN_eq]
  set T := (Finset.range cnt).filter (fun i => btTgIn (btTg TG i) = true)
  have hT : T.card = Nat.card {i : Nat // i ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hT]
  have hmemT : ∀ i ∈ T, i < cnt ∧ btTgIn (btTg TG i) = true := fun i hi => by
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  choose! gg hgg hge using fun i (hi : i ∈ T) =>
    btOc_mem hg hp hfix hb hC hW hpre hoc hX (hmemT i hi).1 (hmemT i hi).2
  let φ : {i : Nat // i ∈ T} →
      {x : Equiv.Perm (Fin n) | ∃ g ∈ genSub n mc c, x = g * W * g⁻¹} := fun i =>
    ⟨gg i.1 * W * (gg i.1)⁻¹, gg i.1, hgg i.1 i.2, rfl⟩
  refine Nat.card_le_card_of_injective φ fun i j e => Subtype.ext ?_
  have ev : gg i.1 * W * (gg i.1)⁻¹ = gg j.1 * W * (gg j.1)⁻¹ := congrArg Subtype.val e
  exact btKey_inj hw hp (hmemT i.1 i.2).1 (hmemT j.1 j.2).1 fun t => by
    rw [hge i.1 i.2 t, hge j.1 j.2 t, ev]

end Walk

end CFSG.KS.BTup

end
