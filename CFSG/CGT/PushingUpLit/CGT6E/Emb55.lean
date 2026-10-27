module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Fin
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Cent
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Prime

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6

section PCoreFacts

variable {V : Type} [CommGroup V] (H : Subgroup (MulAut V))

@[expose] def oThree : Subgroup (MulAut V) := (pCore 3 ↥H).map H.subtype

theorem oThree_le : oThree H ≤ H := Subgroup.map_subtype_le _

theorem oThree_norm : ∀ h ∈ H, ∀ q ∈ oThree H, h * q * h⁻¹ ∈ oThree H := by
  rintro h hh _ ⟨q', hq', rfl⟩
  exact ⟨⟨h, hh⟩ * q' * ⟨h, hh⟩⁻¹,
    (pCore_normal (p := 3) (G := ↥H)).conj_mem q' hq' ⟨h, hh⟩, by simp⟩

theorem oThree_isPGroup : IsPGroup 3 ↥(oThree H) :=
  (pCore_isPGroup (p := 3) (G := ↥H)).map H.subtype

theorem oThree_max : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
    IsPGroup 3 ↥N → N ≤ oThree H := by
  intro N hNH hNnorm hN3
  have hnormal : (N.subgroupOf H).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNnorm g g.2 n hn⟩
  have hp : IsPGroup 3 ↥(N.subgroupOf H) :=
    hN3.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ pCore 3 ↥H := le_sSup ⟨hnormal, hp⟩
  intro n hn
  exact ⟨⟨n, hNH hn⟩, hle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem mem_oThree_iff {h : MulAut V} (hh : h ∈ H) : h ∈ oThree H ↔ (⟨h, hh⟩ : ↥H) ∈ pCore 3 ↥H :=
  ⟨fun ⟨q, hq, e⟩ => by
    have : q = ⟨h, hh⟩ := Subtype.ext e
    rwa [← this], fun hq => ⟨⟨h, hh⟩, hq, rfl⟩⟩

theorem gen_of_conjClosure {Y : Subgroup (MulAut V)} (hconj : CGT6.conjClosure Y H = H) :
    ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → Y ≤ N → H ≤ N := by
  intro N hNH hNnorm hYN
  rw [← hconj]
  exact (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, y, hy, rfl⟩
    exact hNnorm g hg y (hYN hy))

end PCoreFacts

theorem emb55_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (G T Y H : Subgroup (MulAut V)),
      Sec5Hyp V G T Y → H ≤ G → Y ≤ H → CGT6.conjClosure Y H = H →
      T ≤ Subgroup.normalizer (H : Set (MulAut V)) →
      generalizedFitting ↥H = pCore 3 ↥H → Y ≤ (pCore 3 ↥H).map H.subtype := by
  intro V _ _ G T Y H hsec hHG hYH hconj hT hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : IsCharacteristicP 3 ↥H :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 3).mpr hF
  have hQcent : ∀ h ∈ H, (∀ q ∈ oThree H, h * q = q * h) → h ∈ oThree H := by
    intro h hh hc
    have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.centralizer (pCore 3 ↥H : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (by simpa using (hc x ⟨x, hx, rfl⟩).symm)
    exact (mem_oThree_iff H hh).mpr (hchar hmem)
  have d : Emb55Data V G T Y H (oThree H) :=
    ⟨hsec, hHG, hYH, fun t ht h => Subgroup.mem_normalizer_iff.mp (hT ht) h,
      gen_of_conjClosure H hconj, oThree_le H, oThree_norm H, oThree_isPGroup H, oThree_max H,
      hQcent⟩
  exact d.Y_le

theorem emb55Z_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (G T Y H : Subgroup (MulAut V)) (Z : Subgroup ↥H),
      Sec5Hyp V G T Y → H ≤ G → Y ≤ H → CGT6.conjClosure Y H = H →
      T ≤ Subgroup.normalizer (H : Set (MulAut V)) → Z ≤ Subgroup.center ↥H → Odd (Nat.card ↥Z) →
      generalizedFitting ↥H = pCore 3 ↥H ⊔ Z → Y ≤ (pCore 3 ↥H).map H.subtype := by
  intro V _ _ G T Y H Z hsec hHG hYH hconj hT hZc hZodd hF
  have hZle : Z ≤ pCore 3 ↥H := by
    intro z hz
    have hzc : ∀ h ∈ H, (z : MulAut V) * h = h * z := fun h hh => by
      have := Subgroup.mem_center_iff.mp (hZc hz) ⟨h, hh⟩
      exact (congrArg Subtype.val this).symm
    have hodd : Odd (orderOf (z : MulAut V)) := by
      rw [Subgroup.orderOf_coe]
      have h2 : orderOf z = orderOf (⟨z, hz⟩ : ↥Z) := Subgroup.orderOf_coe (⟨z, hz⟩ : ↥Z)
      exact Odd.of_dvd_nat hZodd (h2 ▸ orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z))
    have hmem := central_odd_le_Q hsec hYH (gen_of_conjClosure H hconj) (oThree_max H) z.2 hzc hodd
    exact (mem_oThree_iff H z.2).mp hmem
  have hF' : generalizedFitting ↥H = pCore 3 ↥H := by
    rw [hF]; exact sup_eq_left.mpr hZle
  exact emb55_holds V G T Y H hsec hHG hYH hconj hT hF'

theorem emb55F_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (G T Y H N : Subgroup (MulAut V)),
      Sec5Hyp V G T Y → H ≤ G → Y ≤ H → CGT6.conjClosure Y H = H →
      T ≤ Subgroup.normalizer (H : Set (MulAut V)) → N ≤ H →
      (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → T ≤ Subgroup.normalizer (N : Set (MulAut V)) →
      Nat.Coprime (Nat.card ↥N) 6 → generalizedFitting ↥H = pCore 3 ↥H ⊔ N.subgroupOf H →
      Y ≤ (pCore 3 ↥H).map H.subtype := by
  intro V _ _ G T Y H N hsec hHG hYH hconj hT hNH hNnorm hTN hcop hF
  have hYN : Y ≤ Subgroup.normalizer (N : Set (MulAut V)) := fun y hy =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hNnorm y (hYH hy) x hx, fun hx => by
      have := hNnorm y⁻¹ (H.inv_mem (hYH hy)) _ hx
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [e] at this⟩
  have hYcent := hsec.centralizes_of_normalized (hNH.trans hHG) hYN hTN hcop
  have hcentral : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h :=
    centralizes_of_gen (gen_of_conjClosure H hconj) hYH hNnorm (fun y hy x hx => hYcent x hx y hy)
  have hZc : N.subgroupOf H ≤ Subgroup.center ↥H := fun z hz => by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by
      have := hcentral g g.2 z (Subgroup.mem_subgroupOf.mp hz)
      simpa using this)
  have hZodd : Odd (Nat.card ↥(N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
  exact emb55Z_holds V G T Y H (N.subgroupOf H) hsec hHG hYH hconj hT hZc hZodd hF

end CFSG.CGT.PushingUpLit.CGT6E
