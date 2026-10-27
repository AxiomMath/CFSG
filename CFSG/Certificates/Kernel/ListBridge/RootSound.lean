module

public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import Certificates.Data.Kernel.ListBridgeRoot
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge

section Group

variable {M : Type*} [Group M]

theorem wit_conj {r k c g : M} (hkr : k * r = r * k)
    (h1 : ((k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹)) *
      ((k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹)) = 1)
    (h2 : (k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹) ≠ 1)
    (h3 : (k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹) ≠ r) :
    (c * ((k⁻¹ * g * k) * c * (k⁻¹ * g * k)⁻¹)) * (c * ((k⁻¹ * g * k) * c * (k⁻¹ * g * k)⁻¹)) =
      1 ∧ c * ((k⁻¹ * g * k) * c * (k⁻¹ * g * k)⁻¹) ≠ 1 ∧
      c * ((k⁻¹ * g * k) * c * (k⁻¹ * g * k)⁻¹) ≠ r := by
  have e : c * ((k⁻¹ * g * k) * c * (k⁻¹ * g * k)⁻¹) =
      k⁻¹ * ((k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹)) * k := by group
  rw [e]
  generalize (k * c * k⁻¹) * (g * (k * c * k⁻¹) * g⁻¹) = x at h1 h2 h3
  have ex : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  refine ⟨?_, fun h => h2 ?_, fun h => h3 ?_⟩
  · calc k⁻¹ * x * k * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
      _ = 1 := by rw [h1]; group
  · rw [ex, h]
    group
  · rw [ex, h, hkr]
    group

theorem cqCheck_of_sylow [DecidableEq M] (K S : Subgroup M) [Finite K] {r : M}
    (hr : ∀ k ∈ K, k * r = r * k) (hr2 : r * r = 1) (L : List M) (hL : ∀ g, g ∈ L ↔ g ∈ K)
    (hSK : S ≤ K) (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf K).index)
    (hw : ∀ c ∈ S, c * c = r → ∃ g ∈ K, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
      c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ r) :
    Nobq.cqCheck r L = true := by
  simp only [Nobq.cqCheck, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true]
  intro c hcL
  by_cases hcr : c * c = r
  swap
  · exact Or.inl hcr
  right
  have hcK := (hL c).1 hcL
  have hSp : IsPGroup 2 (S.subgroupOf K) := hS.comap_of_injective K.subtype K.subtype_injective
  have hu : (⟨c, hcK⟩ : K) ^ (2 ^ 2) = 1 := by
    apply Subtype.ext
    have e : c ^ (2 ^ 2) = (c * c) * (c * c) := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq]
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [e, hcr, hr2]
  obtain ⟨k, hk⟩ := Nobq.exists_conj_mem_of_twoPow (S.subgroupOf K) hSp hidx hu
  have hs : (k : M) * c * (k : M)⁻¹ ∈ S := by
    simpa [Subgroup.mem_subgroupOf] using hk
  have hkr := hr k k.2
  have hss : ((k : M) * c * (k : M)⁻¹) * ((k : M) * c * (k : M)⁻¹) = r := by
    calc ((k : M) * c * (k : M)⁻¹) * ((k : M) * c * (k : M)⁻¹) =
        (k : M) * (c * c) * (k : M)⁻¹ := by group
      _ = r := by rw [hcr, hkr]; group
  obtain ⟨g, hgK, h1, h2, h3⟩ := hw _ hs hss
  refine ⟨(k : M)⁻¹ * g * k, (hL _).2 (K.mul_mem (K.mul_mem (K.inv_mem k.2) hgK) k.2), ?_⟩
  exact wit_conj hkr h1 h2 h3

end Group

variable {n w : Nat}

theorem eq_of_prep_shr {P Q : Nat} {g h : Equiv.Perm (Fin n)} (hw : 0 < w)
    (hP : P >>> (n * w) = 0) (hQ : Q >>> (n * w) = 0) (gP : PRep n w P g) (hQr : PRep n w Q h)
    (e : g = h) : P = Q :=
  CFSG.KS.PF.eq_of_fields hw hP hQ fun i hi => by rw [gP ⟨i, hi⟩, hQr ⟨i, hi⟩, e]

theorem rootsK_sound {ng N : Nat} {G T E S WI : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}
    {R : Nat} {r : Equiv.Perm (Fin n)} (hk : bfsK n w ng G N T E S = true)
    (hl : gens.length = ng) (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1))
    (hR : PRep n w R r) (h : rootsK n w R N T WI = true) :
    ∀ c ∈ Subgroup.closure {s | s ∈ gens}, c * c = r →
      ∃ g ∈ Subgroup.closure {s | s ∈ gens}, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
        c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ r := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  have hn32 : n < 2 ^ 32 := by omega
  have hnw : n < 2 ^ w := by omega
  have hw0 : 0 < w := CFSG.KS.PF.w_pos hw
  set H := Subgroup.closure {s | s ∈ gens} with hH
  obtain ⟨hmem, -⟩ := enum_closure hk hl hG
  have hQ := (bfsK_points (fun y => ∃ g ∈ H, PRep n w y g)
    ⟨1, H.one_mem, prep_pidn hn hw⟩ (fun y ⟨g, hg, hy⟩ k hk1 =>
      ⟨gens.getD k 1 * g, H.mul_mem (Subgroup.subset_closure (getD_mem (hl ▸ hk1))) hg,
        prep_pcomp hn32 (hG k hk1) hy⟩) hk).2.2.1
  unfold rootsK at h
  rw [Orb.strictB_eq] at h
  obtain ⟨hRc, hall⟩ := (bAnd_iff _ _).1 h
  have hRs := (CFSG.KS.PF.canon_facts hRc).2.2.1
  have hIs := CFSG.KS.PF.pidn_shr hn hw
  intro c hc hcc
  obtain ⟨i, hi, hci⟩ := (hmem c).1 hc
  have hi' := allN_spec hall i hi
  rw [Orb.strictB_eq] at hi'
  have hb : Nat.beq (pcomp n w (mask w) (T i) (T i)) R = true := by
    rw [eq_of_prep_shr hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) hRs (prep_pcomp hn32 hci hci) hR
      hcc]
    exact Nat.beq_refl _
  rw [hb] at hi'
  have hi2 : strictB (WI i) (fun j => bAnd(Nat.blt j N, rootWitK n w R (T i) (T j))) = true :=
    hi'
  rw [Orb.strictB_eq] at hi2
  obtain ⟨hj, hwit⟩ := (bAnd_iff _ _).1 hi2
  obtain ⟨g, hgH, hgT⟩ := hQ _ (Nat.blt_eq.mp hj)
  refine ⟨g, hgH, ?_⟩
  unfold rootWitK at hwit
  rw [Orb.strictB_eq] at hwit
  obtain ⟨hx2, hrest⟩ := (bAnd_iff _ _).1 hwit
  have hX := prep_pcomp hn32 hci (prep_pcomp hn32 (prep_pcomp hn32 hgT hci)
    (CFSG.KS.SporSch.MOC.prep_pinvS hnw hgT).1)
  have hXs := CFSG.KS.PF.pcomp_shr (T i) (pcomp n w (mask w) (pcomp n w (mask w) (T (WI i)) (T i))
    (pinvS n w (mask w) (T (WI i)))) hn32 hw0
  refine ⟨?_, fun e => ?_, fun e => ?_⟩
  · have h2 := prep_pcomp hn32 hX hX
    rw [Nat.eq_of_beq_eq_true hx2] at h2
    exact prep_unique h2 (prep_pidn hn hw)
  · rw [eq_of_prep_shr hw0 hXs hIs hX (prep_pidn hn hw) e, Nat.beq_refl] at hrest
    exact Bool.false_ne_true hrest
  · have e1 : Nat.beq (pcomp n w (mask w) (T i) (pcomp n w (mask w)
        (pcomp n w (mask w) (T (WI i)) (T i)) (pinvS n w (mask w) (T (WI i))))) (pidn n w) =
        false := by
      cases hb1 : Nat.beq (pcomp n w (mask w) (T i) (pcomp n w (mask w)
        (pcomp n w (mask w) (T (WI i)) (T i)) (pinvS n w (mask w) (T (WI i))))) (pidn n w)
      · rfl
      · rw [hb1] at hrest
        exact absurd hrest Bool.false_ne_true
    rw [e1, eq_of_prep_shr hw0 hXs hRs hX hR e, Nat.beq_refl] at hrest
    exact Bool.false_ne_true hrest

end CFSG.ClassicalInvolution.ListBridge

end
