module

public import CFSG.GH74.Uniqueness.SU.SU13TC5Base

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

section Q

variable {e : Elts G z} {e9 : Elts9 z e} (f : FPart9 z e) (E9 : EPart9 z e e9 f.toFPart) (hWc : WAbel e)

theorem NHE_eq (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) :
    normalizer ((Asub E9 hWc : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) = NHE E9.E z := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgz⟩ := mem_inf.mp hg
    have hgz' : g * z = z * g := mem_centralizer_singleton_iff.mp hgz
    refine mem_inf.mpr ⟨?_, hgz⟩
    have key : ∀ {g : G}, g ∈ normalizer ((Asub E9 hWc : Subgroup G) : Set G) → g * z = z * g →
        ∀ x ∈ E9.E, g * x * g⁻¹ ∈ E9.E := by
      intro g hgN hgz x hx
      have hxA : g * x * g⁻¹ ∈ Asub E9 hWc := (mem_normalizer_iff.mp hgN x).mp (mem_sup_left hx)
      have hxz : g * x * g⁻¹ ∈ centralizer ({z} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have hxz' : x * z = z * x := E9.Es_comm x (E9.Es_ge hx)
        have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
        calc g * x * g⁻¹ * z = g * x * (g⁻¹ * z) := by group
          _ = g * x * (z * g⁻¹) := by rw [hgi]
          _ = g * (x * z) * g⁻¹ := by group
          _ = g * (z * x) * g⁻¹ := by rw [hxz']
          _ = (g * z) * x * g⁻¹ := by group
          _ = (z * g) * x * g⁻¹ := by rw [hgz]
          _ = z * (g * x * g⁻¹) := by group
      have : g * x * g⁻¹ ∈ Asub E9 hWc ⊓ centralizer ({z} : Set G) := mem_inf.mpr ⟨hxA, hxz⟩
      rwa [A_inf_cent_z f E9 hWc hW5 hz] at this
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key hgN hgz' x, fun hx => ?_⟩
    have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz')).eq
    have := key (inv_mem hgN) hgi _ hx
    simpa [mul_assoc] using this
  · intro g hg
    exact mem_inf.mpr ⟨NHE_le_normalizer_A f E9 hWc hz hW5 l hg, (mem_inf.mp hg).2⟩

theorem S₂_sylow_X (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) :
    IsSylowIn (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) E9.S₂ := by
  have hT : IsSylowIn (normalizer ((Asub E9 hWc : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) E9.S₂ := by
    rw [NHE_eq f E9 hWc hz hW5 l]; exact E9.S₂_syl
  exact isSylowIn_of_central_involution hT E9.S₂_z
    (fun s hs => mem_centralizer_singleton_iff.mp (mem_inf.mp (E9.S₂_syl.1 hs)).2) E9.S₂_cen hz

theorem z_isolated (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) (hm : MPart9 z e E9.E) {g : G}
    (hg : g ∈ normalizer ((Asub E9 hWc : Subgroup G) : Set G)) (hS : g⁻¹ * z * g ∈ E9.S₂) :
    g⁻¹ * z * g = z := by
  by_contra hne
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  set u := g⁻¹ * z * g with hu
  have hu2 : orderOf u = 2 := by
    have := orderOf_conj_eq (a := z) g⁻¹
    rw [inv_inv] at this
    rw [hu, this]; exact hz
  have huN : u ∈ NHE E9.E z := E9.S₂_syl.1 hS
  obtain ⟨h, hhN, hh⟩ := E9.invClass u huN hu2 hne
  have hNA := NHE_le_normalizer_A f E9 hWc hz hW5 l
  have h1 := card_inf_centralizer_conj (Y := Asub E9 hWc) (hNA hhN) e.t
  rw [hh, card_A_cent_t f E9 hWc hz hW5 l hm] at h1
  have h2 := card_inf_centralizer_conj (Y := Asub E9 hWc) (inv_mem hg) z
  have h3 : g⁻¹ * z * g⁻¹⁻¹ = u := by rw [hu]; group
  rw [h3, A_inf_cent_z f E9 hWc hW5 hz, E9.E_card] at h2
  omega

theorem comm_z_mem_oc (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) (hm : MPart9 z e E9.E) {v : G}
    (hv : v ∈ normalizer ((Asub E9 hWc : Subgroup G) : Set G)) :
    z * v * z⁻¹ * v⁻¹ ∈ oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) := by
  set X : Subgroup G := normalizer ((Asub E9 hWc : Subgroup G) : Set G) with hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := S₂_sylow_X f E9 hWc hz hW5 l
  have hzX : z ∈ X := NHE_le_normalizer_A f E9 hWc hz hW5 l (z_mem_NHE f E9)
  have hP : IsPGroup 2 (E9.S₂.subgroupOf X) :=
    IsPGroup.of_equiv hSyl.isPGroup (Subgroup.subgroupOfEquivOfLe hSyl.le).symm
  have hidx : ¬ 2 ∣ (E9.S₂.subgroupOf X).index := by
    have h1 : Odd (E9.S₂.relIndex X) := hSyl.2.2
    have h2 : (E9.S₂.subgroupOf X).index = E9.S₂.relIndex X := rfl
    rw [h2]
    intro hd
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr hd)
  let S : Sylow 2 ↥X := hP.toSylow hidx
  have hSmem : ∀ y : ↥X, y ∈ (S : Subgroup ↥X) ↔ (y : G) ∈ E9.S₂ := fun y => by
    show y ∈ (hP.toSylow hidx : Subgroup ↥X) ↔ _
    rw [IsPGroup.toSylow_coe]; exact Subgroup.mem_subgroupOf
  let z' : ↥X := ⟨z, hzX⟩
  have hz'S : z' ∈ (S : Subgroup ↥X) := (hSmem z').mpr E9.S₂_z
  let zS : ↥(S : Subgroup ↥X) := ⟨z', hz'S⟩
  have hzcomm : ∀ s ∈ E9.S₂, s * z = z * s := fun s hs =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (E9.S₂_syl.1 hs)).2
  have hzZ : zS ∈ Subgroup.center (S : Subgroup ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    apply Subtype.ext
    exact hzcomm ((s : ↥X) : G) ((hSmem _).mp s.2)
  have hz2 : orderOf zS = 2 := by
    have h1 : orderOf (zS : ↥X) = orderOf zS := Subgroup.orderOf_coe zS
    have h2 : orderOf (z' : G) = orderOf z' := Subgroup.orderOf_coe z'
    rw [← h1]
    have : orderOf (z' : G) = 2 := hz
    rw [h2] at this
    exact this
  have hwc : ∀ g : ↥X, g⁻¹ * (zS : ↥X) * g ∈ (S : Subgroup ↥X) → g⁻¹ * (zS : ↥X) * g = (zS : ↥X) := by
    intro g hg
    have h1 : (g : G)⁻¹ * z * (g : G) ∈ E9.S₂ := (hSmem _).mp hg
    exact Subtype.ext (z_isolated f E9 hWc hz hW5 l hm g.2 h1)
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S zS hzZ hz2 hwc
  have hc := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk (⟨v, hv⟩ : ↥X))
  have h1 : (QuotientGroup.mk (z' * (⟨v, hv⟩ : ↥X) * z'⁻¹ * (⟨v, hv⟩ : ↥X)⁻¹) :
      ↥X ⧸ CFSG.oddCore ↥X) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (QuotientGroup.mk z' : ↥X ⧸ CFSG.oddCore ↥X) * QuotientGroup.mk (⟨v, hv⟩ : ↥X) *
          (QuotientGroup.mk z')⁻¹ * (QuotientGroup.mk (⟨v, hv⟩ : ↥X))⁻¹
        = (QuotientGroup.mk (⟨v, hv⟩ : ↥X) * QuotientGroup.mk z') * (QuotientGroup.mk z')⁻¹ *
          (QuotientGroup.mk (⟨v, hv⟩ : ↥X))⁻¹ := by
          rw [show (QuotientGroup.mk (⟨v, hv⟩ : ↥X) * QuotientGroup.mk z' : ↥X ⧸ CFSG.oddCore ↥X) =
            QuotientGroup.mk z' * QuotientGroup.mk (⟨v, hv⟩ : ↥X) from hc]
      _ = 1 := by group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [TB.oddCore_eq_pPrimeCore] at h2
  exact mem_oc.mpr ⟨X.mul_mem (X.mul_mem (X.mul_mem hzX hv) (X.inv_mem hzX)) (X.inv_mem hv), h2⟩

theorem V_le_oc_X (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) (hm : MPart9 z e E9.E) :
    Vsub z e.s₁ hWc ≤ oc (normalizer ((Asub E9 hWc : Subgroup G) : Set G)) := by
  intro v hv
  have hvX := V_le_normalizer_A f E9 hWc hz hW5 hv
  have h := comm_z_mem_oc f E9 hWc hz hW5 l hm hvX
  have h3 := V_exp hz f hWc hW5 v hv
  have : z * v * z⁻¹ * v⁻¹ = v := by
    rw [hv.2]
    calc v⁻¹ * v⁻¹ = v⁻¹ * v⁻¹ * v ^ 3 := by rw [h3, mul_one]
      _ = v := by group
  rwa [this] at h

end Q

end CFSG.GH74.Uniqueness.SU.SU13
