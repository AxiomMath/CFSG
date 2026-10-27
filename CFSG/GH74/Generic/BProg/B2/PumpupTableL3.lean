module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv
public import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3
import CFSG.GH74.Generic.BProg.BpGeneral
public import CFSG.GH74.Generic.BProg.B2.PumpupTable

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableL3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv

theorem isCompIn_centralizer_subgroupOf {N : Type} [Group N] {H L : Subgroup N} {t : N} (htH : t ∈ H)
    (hc : IsCompIn (H ⊓ Subgroup.centralizer ({t} : Set N)) L) :
    IsCompIn (Subgroup.centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H)) (L.subgroupOf H) := by
  have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
  rw [IsCompIn, CFSG.GH74.Generic.BProg.centralizer_singleton_mk_eq_subgroupOf htH]
  exact ⟨Subgroup.comap_mono hc.1,
    (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
      (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hc.2⟩

theorem false_of_invData {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hLC : IsCompIn (H ⊓ Subgroup.centralizer ({t} : Set N)) L) (htH : t ∈ H)
    (h2 : HasTwoInvolutions L) {q : ℕ} {S : Subgroup ↥H}
    (hInv : CFSG.GH74.KGroups.L3Eps.InvData q ↥H (⟨t, htH⟩ : ↥H) S) : False := by
  have hB := isCompIn_centralizer_subgroupOf htH hLC
  have hLS : L.subgroupOf H = S :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hInv.quasisimple
      hInv.le_centralizer hInv.conj_mem hInv.commutator_mem hB
  have hLH : L ≤ H := hLC.1.trans inf_le_left
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ := h2
  have hmem : ∀ c ∈ L, c * c = 1 → c ≠ 1 → c = t := by
    intro c hc hc2 hc1
    have hcS : (⟨c, hLH hc⟩ : ↥H) ∈ S := by
      rw [← hLS]
      exact hc
    rcases hInv.involution _ hcS (Subtype.ext hc2) with h | h
    · exact absurd (congrArg Subtype.val h) hc1
    · exact congrArg Subtype.val h
  exact hab ((hmem a haL ha2 ha1).trans (hmem b hbL hb2 hb1).symm)

section Certified


theorem pumpupIn_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f) :
    PumpupEmptyIn (fun X _ => LieModel X .PSL 3 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have ht1 : t ≠ 1 := fun h => by
    have := hs.inv
    rw [h, orderOf_one] at this
    omega
  have hst := CFSG.GH74.Generic.BProg.B2.PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hH
  obtain ⟨S, hInv⟩ := CFSG.GH74.GLS.IVK.exists_invData_lin hp hp2 h5 hf hst (⟨t, htH⟩ : ↥H)
    (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h))
  exact false_of_invData hs.comp htH (hasTwoInvolutions_of_shapeInCent hs) hInv

theorem pumpupIn_u3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    PumpupEmptyIn (fun X _ => LieModel X .PSU 3 p f) := by
  intro N _ _ H t L hs htH hH
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have ht1 : t ≠ 1 := fun h => by
    have := hs.inv
    rw [h, orderOf_one] at this
    omega
  have hst := CFSG.GH74.Generic.BProg.B2.PumpupTableBasic.stated_of_lieModel (Or.inr rfl) hH
  obtain ⟨S, hInv⟩ := ((CFSG.GH74.Generic.S3.libData_uni hp hp2 h5) ↥H hst).1 (⟨t, htH⟩ : ↥H)
    (Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h))
  exact false_of_invData hs.comp htH (hasTwoInvolutions_of_shapeInCent hs) hInv

end Certified

end CFSG.GH74.Generic.BProg.B2.PumpupTableL3
