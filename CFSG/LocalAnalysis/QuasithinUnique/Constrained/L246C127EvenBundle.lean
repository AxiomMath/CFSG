module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenAux
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLatAlt

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

namespace L246C127

open Equiv

theorem overgroups_charTwo {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (cts : List (CTCert (Perm (Fin n)))) (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A)
    (hc : c.check RN.enc = true) (hm : memberOK c cts = true) (Y : Subgroup ↥A)
    (hDY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y) : Y = ⊤ ∨ CharTwo Y := by
  have hcl := c.closedOK_of_check hc
  have hsz := c.sizesOK_of_check hc
  let Y' : Subgroup (Perm (Fin n)) := Y.map A.subtype
  have hTY' : Subgroup.closure {g | g ∈ c.tGens} ≤ Y' := fun t ht =>
    ⟨⟨t, hTA ht⟩, hDY (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hY'A : Y' ≤ A := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hY'M : Y' ≤ Subgroup.closure {g | g ∈ c.mGens} := hM ▸ hY'A
  obtain ⟨L, hL, hYL⟩ := c.overgroups (rawIsEnc n) hc Y' hTY' hY'M
  have hYY : Y'.subgroupOf A = Y :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective Y
  have hmL := (List.all_eq_true.1 hm) L hL
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hmL
  rcases hmL with hfull | ⟨ct, -, hhg, hck⟩
  · left
    have hLcl := c.members_closed hcl L hL
    have hcard : Nat.card (Subgroup.closure {g | g ∈ L}) = c.msize := by
      rw [card_closure_of_closedH (rawIsEnc n) L c.depth hLcl]
      exact hfull
    have hcM : Nat.card (Subgroup.closure {g | g ∈ c.mGens}) = c.msize :=
      c.card_m (rawIsEnc n) hcl hsz
    have hle : Subgroup.closure {g | g ∈ L} ≤ Subgroup.closure {g | g ∈ c.mGens} := hYL ▸ hY'M
    have hLM : Subgroup.closure {g | g ∈ L} = Subgroup.closure {g | g ∈ c.mGens} :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcM])
    have hY'eq : Y' = A := hYL.trans (hLM.trans hM)
    rw [← hYY, hY'eq, Subgroup.subgroupOf_self]
  · right
    have hch := CTCert.charTwo (rawIsEnc n) ct hck
    rw [hhg, ← hYL] at hch
    have := charTwo_subgroupOf_of_le hY'A hch
    rwa [hYY] at this

theorem isSylow_of_cert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A) (hc : c.check RN.enc = true) {k m : ℕ}
    (hk : c.sizes.headD 0 = 2 ^ k) (hm : c.msize = 2 ^ k * m) (hodd : ¬ 2 ∣ m) :
    IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) (⊤ : Subgroup ↥A) := by
  subst hM
  exact c.isSylowTwoOf_top (rawIsEnc n) hc hk hm hodd

theorem closure_eq_alt_of_cert {n : ℕ} (c : LatCert (Perm (Fin n))) (hc : c.check RN.enc = true)
    (hgen : ∀ g ∈ c.mGens, Equiv.Perm.sign g = 1)
    (hsize : c.msize = Nat.card (alternatingGroup (Fin n))) :
    Subgroup.closure {g | g ∈ c.mGens} = alternatingGroup (Fin n) := by
  have hcl := c.closedOK_of_check hc
  have hsz := c.sizesOK_of_check hc
  have hle : Subgroup.closure {g | g ∈ c.mGens} ≤ alternatingGroup (Fin n) := by
    rw [Subgroup.closure_le]
    intro g hg
    exact Equiv.Perm.mem_alternatingGroup.2 (hgen g hg)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [c.card_m (rawIsEnc n) hcl hsz, hsize]

end L246C127

end CFSG.QuasithinUnique
