module

public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionEightSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem card_subgroupOf_eq (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_map_conj (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem normalizer_subgroupOf_eq {H K : Subgroup G} (hHK : H ≤ K) :
    Subgroup.normalizer ((H.subgroupOf K : Subgroup K) : Set K) =
      (Subgroup.normalizer (H : Set G)).subgroupOf K := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have h1 := (h ⟨g, hHK hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hg
      have hgK : g ∈ K := by
        have h1 : (x : G) * g * (x : G)⁻¹ ∈ K := hHK hg
        have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
        rw [h2]
        exact K.mul_mem (K.mul_mem (K.inv_mem x.2) h1) x.2
      exact Subgroup.mem_subgroupOf.mp ((h ⟨g, hgK⟩).mpr (Subgroup.mem_subgroupOf.mpr hg))
  · intro h y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h y

theorem centralizer_subgroupOf_eq {H K : Subgroup G} (hHK : H ≤ K) :
    Subgroup.centralizer ((H.subgroupOf K : Subgroup K) : Set K) =
      (Subgroup.centralizer (H : Set G)).subgroupOf K := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hHK hg⟩ (Subgroup.mem_subgroupOf.mpr hg))
  · intro h y hy
    exact Subtype.ext (h y (Subgroup.mem_subgroupOf.mp hy))

theorem isKleinFour_of_mulEquiv {H K : Type*} [Group H] [Group K] [IsKleinFour H] (e : H ≃* K) :
    IsKleinFour K :=
  ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

end General

section Local

variable {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
  (f : SemidihedralGroup n ≃* S)

theorem sylow_inf_normalizer_eq_map {W : Subgroup G} (hWS : W ≤ S) :
    (S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) =
      (Subgroup.normalizer ((W.subgroupOf S : Subgroup S) : Set S)).map
        (S : Subgroup G).subtype := by
  rw [normalizer_subgroupOf_eq hWS, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem sylow_inf_centralizer_eq_map {W : Subgroup G} (hWS : W ≤ S) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) =
      (Subgroup.centralizer ((W.subgroupOf S : Subgroup S) : Set S)).map
        (S : Subgroup G).subtype := by
  rw [centralizer_subgroupOf_eq hWS, Subgroup.subgroupOf_map_subtype, inf_comm]

include hn f in
theorem kleinFour_sylow_facts (W : Subgroup G) (hWS : W ≤ S) [IsKleinFour W] :
    Nonempty (((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) ≃*
        DihedralGroup 4) ∧
      Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) = 8 ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ≤ W := by
  have : IsKleinFour (W.subgroupOf S) :=
    isKleinFour_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hWS).symm
  obtain ⟨x, hxW, hxz⟩ := kleinFour_exists_not_mem hn f (W.subgroupOf S)
  obtain ⟨-, hC, -⟩ := kleinFour_eq_closure hn f (W.subgroupOf S) x hxW hxz
  obtain ⟨-, ⟨e⟩, hcard⟩ := normalizer_kleinFour hn f (W.subgroupOf S) x hxW hxz
  rw [sylow_inf_normalizer_eq_map S hWS, sylow_inf_centralizer_eq_map S hWS, hC,
    Subgroup.subgroupOf_map_subtype]
  refine ⟨⟨((Subgroup.normalizer _).equivMapOfInjective _
    (S : Subgroup G).subtype_injective).symm.trans e⟩, ?_, inf_le_left⟩
  rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, hcard]

include hn f in
theorem quaternionEight_sylow_facts (W : Subgroup G) (hWS : W ≤ S)
    (hW : Nonempty (W ≃* QuaternionGroup 2)) :
    Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) = 16 ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ≤ W ∧
      (n = 4 → Nonempty (((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) ≃*
        SemidihedralGroup 4)) ∧
      (5 ≤ n → Nonempty (((S : Subgroup G) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) ≃*
        QuaternionGroup 4)) := by
  obtain ⟨eW⟩ := hW
  obtain ⟨hchar, -, hloc⟩ := quaternion_eight_subgroups_aux n hn f rfl rfl rfl rfl
  obtain ⟨i, hi, hWi⟩ := (hchar (W.subgroupOf S)).mp ⟨(Subgroup.subgroupOfEquivOfLe hWS).trans eW⟩
  obtain ⟨hC, hZ, -, hcard, htop, hq16, -⟩ := hloc i hi
  rw [← hWi] at hC hZ hcard htop hq16
  have hCW : Subgroup.centralizer ((W.subgroupOf S : Subgroup S) : Set S) ≤ W.subgroupOf S := by
    rw [hC, ← hZ]
    exact Subgroup.map_subtype_le _
  have hmapW : (W.subgroupOf S).map (S : Subgroup G).subtype = W :=
    Subgroup.map_subgroupOf_eq_of_le hWS
  have eN := (Subgroup.normalizer ((W.subgroupOf S : Subgroup S) : Set S)).equivMapOfInjective _
    (S : Subgroup G).subtype_injective
  rw [sylow_inf_normalizer_eq_map S hWS, sylow_inf_centralizer_eq_map S hWS]
  refine ⟨?_, ?_, fun h4 => ?_, fun h5 => ?_⟩
  · rw [Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective, hcard]
  · calc _ ≤ (W.subgroupOf S).map (S : Subgroup G).subtype := Subgroup.map_mono hCW
      _ = W := hmapW
  · have h := htop h4
    subst h4
    exact ⟨eN.symm.trans ((MulEquiv.subgroupCongr h).trans (Subgroup.topEquiv.trans f.symm))⟩
  · obtain ⟨e⟩ := hq16 h5
    exact ⟨eN.symm.trans e⟩

end Local

section OddCore

theorem odd_card_oddCore (H : Type*) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) := by
  have h := CFSG.LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ Nat.card (CFSG.oddCore H) := Nat.dvd_of_mod_eq_zero (by omega)
  exact h ⟨2, Nat.prime_two⟩ h2' rfl

theorem le_oddCore {H : Type*} [Group H] {M : Subgroup H} (hM : M.Normal)
    (hodd : Odd (Nat.card M)) : M ≤ CFSG.oddCore H :=
  le_sSup ⟨hM, hodd⟩

end OddCore

section Core

variable {G : Type*} [Group G] [Finite G]

theorem sylow_inf_normalizer (S : Sylow 2 G) (T : Subgroup G) (hT2 : IsPGroup 2 T)
    (hc : ∀ g : G, T.map (MulAut.conj g).toMonoidHom ≤ S →
      Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer
        ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) : Subgroup G) ≤
      Nat.card ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G)) :
    ∃ P : Sylow 2 (Subgroup.normalizer (T : Set G)),
      (P : Subgroup (Subgroup.normalizer (T : Set G))) =
        ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
          (Subgroup.normalizer (T : Set G)) := by
  have hR2 : IsPGroup 2 (((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))) :=
    (S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨U, hRU⟩ := hR2.exists_le_sylow
  have hTN : (T.subgroupOf (Subgroup.normalizer (T : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  have hT2' : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (T : Set G))) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm
  have hTU : T.subgroupOf (Subgroup.normalizer (T : Set G)) ≤ U := hT2'.le_sylow_of_normal U
  have hUG2 : IsPGroup 2 ((U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype) :=
    U.isPGroup'.map _
  obtain ⟨P, hUP⟩ := hUG2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hconjS : ((U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype).map
      (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    have hyP : y ∈ (P : Subgroup G) := hUP hy
    rw [← hg] at hyP
    change y ∈ MulAut.conj g • (S : Subgroup G) at hyP
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hyP
    simpa using hyP
  have hTUG : T ≤ (U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype := fun t ht =>
    ⟨⟨t, Subgroup.le_normalizer ht⟩, hTU (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hWS : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ S :=
    (Subgroup.map_mono hTUG).trans hconjS
  have hUN : ((U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype).map
      (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer
        ((T.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hcard : Nat.card U ≤ Nat.card (((S : Subgroup G) ⊓
      Subgroup.normalizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G))) := by
    calc Nat.card U = Nat.card ((U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype) :=
          (Subgroup.card_map_of_injective (Subgroup.normalizer (T : Set G)).subtype_injective).symm
      _ = Nat.card (((U : Subgroup _).map (Subgroup.normalizer (T : Set G)).subtype).map
          (MulAut.conj g⁻¹).toMonoidHom) := (card_map_conj _ _).symm
      _ ≤ _ := Subgroup.card_le_of_le (le_inf hconjS hUN)
      _ ≤ _ := hc g⁻¹ hWS
      _ = _ := by rw [card_subgroupOf_eq, inf_assoc, inf_idem]
  exact ⟨U, (Subgroup.eq_of_le_of_card_ge hRU hcard).symm⟩

theorem odd_index_inf_centralizer (S : Sylow 2 G) (T : Subgroup G) (hTS : T ≤ S)
    (hSC : (S : Subgroup G) ⊓ Subgroup.centralizer (T : Set G) ≤ T)
    (h2 : 2 ∣ Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G))
    (hRsyl : ∃ P : Sylow 2 (Subgroup.normalizer (T : Set G)),
      (P : Subgroup (Subgroup.normalizer (T : Set G))) =
        ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
          (Subgroup.normalizer (T : Set G))) :
    Odd (((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))).index) := by
  obtain ⟨P, hP⟩ := hRsyl
  have hCN := Subgroup.centralizer_le_normalizer (T : Set G)
  have : ((Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer _
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal P (N := (Subgroup.centralizer
    (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)))
  have hcop := Sylow.card_coprime_index Q
  have htrace : (S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) ⊓
      Subgroup.centralizer (T : Set G) = T ⊓ Subgroup.centralizer (T : Set G) := by
    apply le_antisymm
    · rintro x ⟨⟨hxS, -⟩, hxC⟩
      exact ⟨hSC ⟨hxS, hxC⟩, hxC⟩
    · rintro x ⟨hxT, hxC⟩
      exact ⟨⟨hTS hxT, hCN hxC⟩, hxC⟩
  have hinter : ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G)) ⊓ (Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G)) = ((S : Subgroup G) ⊓ Subgroup.normalizer (T : Set G) ⊓
      Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hQcard : Nat.card Q.toSubgroup =
      Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
    rw [hQ, card_subgroupOf_eq, inf_assoc, inf_idem, hP, hinter, card_subgroupOf_eq, htrace,
      inf_eq_left.mpr (inf_le_right.trans hCN)]
  have hCcard : Nat.card ((Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.normalizer (T : Set G))) = Nat.card (Subgroup.centralizer (T : Set G)) := by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hCN]
  have hAcard : Nat.card ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))) =
      Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
    rw [card_subgroupOf_eq, inf_assoc, inf_idem]
  have h1 := Subgroup.card_mul_index Q.toSubgroup
  have h2' := Subgroup.card_mul_index ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
    (Subgroup.centralizer (T : Set G)))
  rw [hQcard, hCcard] at h1
  rw [hAcard] at h2'
  have hpos : 0 < Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := Nat.card_pos
  have heq : ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))).index = Q.toSubgroup.index :=
    Nat.eq_of_mul_eq_mul_left hpos (h2'.trans h1.symm)
  rw [hQcard] at hcop
  rw [heq, ← Nat.coprime_two_left]
  exact Nat.Coprime.coprime_dvd_left h2 hcop

theorem center_oddCore_complement (T : Subgroup G) (hT2 : IsPGroup 2 T)
    (hodd : Odd (((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))).index)) :
    (T ⊓ Subgroup.centralizer (T : Set G)) ⊔
        (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
          (Subgroup.normalizer (T : Set G)).subtype = Subgroup.centralizer (T : Set G) ∧
      (T ⊓ Subgroup.centralizer (T : Set G)) ⊓
        (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
          (Subgroup.normalizer (T : Set G)).subtype = ⊥ ∧
      Nat.card (Subgroup.centralizer (T : Set G)) =
        Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) *
          Nat.card ((CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
            (Subgroup.normalizer (T : Set G)).subtype) ∧
      (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
        (Subgroup.normalizer (T : Set G)).subtype ⊓ T = ⊥ := by
  have hCN := Subgroup.centralizer_le_normalizer (T : Set G)
  have hAc : (T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.centralizer (T : Set G))
      ≤ Subgroup.center (Subgroup.centralizer (T : Set G)) := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 a (Subgroup.mem_subgroupOf.mp ha).1).symm
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp
    (hT2.to_le (inf_le_left : T ⊓ Subgroup.centralizer (T : Set G) ≤ T))
  have hAcard : Nat.card ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))) = 2 ^ j := by
    rw [card_subgroupOf_eq, inf_assoc, inf_idem, hj]
  have hcop : (Nat.card ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G)))).Coprime ((T ⊓ Subgroup.centralizer
        (T : Set G)).subgroupOf (Subgroup.centralizer (T : Set G))).index := by
    rw [hAcard]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  obtain ⟨K₀, -, hK₀card, -, hsup, hinf, -, -, -, hmem, -⟩ :=
    central_hall_subgroup_direct_complement _ hAc hcop
  have hKmem : ∀ g : G, g ∈ K₀.map (Subgroup.centralizer (T : Set G)).subtype ↔
      g ∈ Subgroup.centralizer (T : Set G) ∧ g ^ ((T ⊓ Subgroup.centralizer
        (T : Set G)).subgroupOf (Subgroup.centralizer (T : Set G))).index = 1 := by
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, (hmem k).mp hk,
        Subgroup.coe_one]⟩
    · rintro ⟨hgC, hg⟩
      exact ⟨⟨g, hgC⟩, (hmem _).mpr (Subtype.ext (by simpa using hg)), rfl⟩
  have hDodd : Odd (Nat.card ((CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.normalizer (T : Set G)).subtype_injective]
    exact odd_card_oddCore _
  have hDN : (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.map_subtype_le _
  have hDnormal : ∀ x ∈ Subgroup.normalizer (T : Set G),
      ∀ d ∈ (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
        (Subgroup.normalizer (T : Set G)).subtype,
      x * d * x⁻¹ ∈ (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
        (Subgroup.normalizer (T : Set G)).subtype := by
    rintro x hx _ ⟨d', hd', rfl⟩
    exact ⟨⟨x, hx⟩ * d' * ⟨x, hx⟩⁻¹,
      (inferInstance : (CFSG.oddCore (Subgroup.normalizer (T : Set G))).Normal).conj_mem d' hd'
        ⟨x, hx⟩, rfl⟩
  have hDT : (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype ⊓ T = ⊥ := by
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp hT2
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [ht]
    exact Nat.Coprime.pow_right t (Nat.coprime_two_right.mpr hDodd)
  have hDC : (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype ≤ Subgroup.centralizer (T : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hcomm : d * t * d⁻¹ * t⁻¹ = 1 := by
      have h1 : d * t * d⁻¹ * t⁻¹ ∈ (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
          (Subgroup.normalizer (T : Set G)).subtype := by
        have h2 := Subgroup.mul_mem _ hd
          (hDnormal t (Subgroup.le_normalizer ht) d⁻¹ (Subgroup.inv_mem _ hd))
        simpa only [mul_assoc] using h2
      have h3 : d * t * d⁻¹ * t⁻¹ ∈ T :=
        T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDN hd) t).mp ht) (T.inv_mem ht)
      have h4 : d * t * d⁻¹ * t⁻¹ ∈ (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
          (Subgroup.normalizer (T : Set G)).subtype ⊓ T := ⟨h1, h3⟩
      rw [hDT] at h4
      exact h4
    calc t * d = (d * t * d⁻¹ * t⁻¹)⁻¹ * d * t := by group
      _ = d * t := by rw [hcomm, inv_one, one_mul]
  have hCcard : Nat.card (Subgroup.centralizer (T : Set G)) = 2 ^ j * ((T ⊓
      Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.centralizer (T : Set G))).index := by
    rw [← hAcard, Subgroup.card_mul_index]
  have hDK : (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
      (Subgroup.normalizer (T : Set G)).subtype ≤
        K₀.map (Subgroup.centralizer (T : Set G)).subtype := by
    intro d hd
    rw [hKmem]
    refine ⟨hDC hd, ?_⟩
    have hod : Odd (orderOf d) := Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard _ hd)
    have hdC := Subgroup.orderOf_dvd_natCard _ (hDC hd)
    rw [hCcard] at hdC
    have hcop' : (orderOf d).Coprime (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hod)
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop'.dvd_of_dvd_mul_left hdC)
  have hKN : K₀.map (Subgroup.centralizer (T : Set G)).subtype ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.map_subtype_le _).trans hCN
  have hKnormal : ((K₀.map (Subgroup.centralizer (T : Set G)).subtype).subgroupOf
      (Subgroup.normalizer (T : Set G))).Normal := by
    constructor
    intro k hk x
    rw [Subgroup.mem_subgroupOf, hKmem] at hk ⊢
    obtain ⟨hkC, hkm⟩ := hk
    refine ⟨?_, ?_⟩
    · have h := (Subgroup.normal_subgroupOf_centralizer_normalizer (T : Set G)).conj_mem k
        (Subgroup.mem_subgroupOf.mpr hkC) x
      exact Subgroup.mem_subgroupOf.mp h
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conj_pow, hkm, mul_one,
        mul_inv_cancel]
  have hKodd : Odd (Nat.card ((K₀.map (Subgroup.centralizer (T : Set G)).subtype).subgroupOf
      (Subgroup.normalizer (T : Set G)))) := by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hKN,
      Subgroup.card_map_of_injective (Subgroup.centralizer (T : Set G)).subtype_injective,
      hK₀card]
    exact hodd
  have hKD : K₀.map (Subgroup.centralizer (T : Set G)).subtype ≤
      (CFSG.oddCore (Subgroup.normalizer (T : Set G))).map
        (Subgroup.normalizer (T : Set G)).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKN]
    exact Subgroup.map_mono (le_oddCore hKnormal hKodd)
  have hDeq := le_antisymm hDK hKD
  have hAmap : ((T ⊓ Subgroup.centralizer (T : Set G)).subgroupOf
      (Subgroup.centralizer (T : Set G))).map (Subgroup.centralizer (T : Set G)).subtype =
      T ⊓ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  refine ⟨?_, ?_, ?_, hDT⟩
  · rw [hDeq, ← hAmap, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [hDeq, ← hAmap,
      ← Subgroup.map_inf_eq _ _ _ (Subgroup.centralizer (T : Set G)).subtype_injective, hinf,
      Subgroup.map_bot]
  · rw [hDeq, Subgroup.card_map_of_injective (Subgroup.centralizer (T : Set G)).subtype_injective,
      hK₀card, hj]
    exact hCcard

end Core

end CFSG.Semidihedral.Local
