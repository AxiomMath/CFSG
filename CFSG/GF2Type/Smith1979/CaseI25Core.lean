module

public import CFSG.GF2Type.Smith1979.CaseI25Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Generic

theorem eq_one_of_mem_commutator_NLbar (ν : NLbar S g →* Multiplicative (ZMod 2)) {x : S.O}
    (hx : x ∈ ⁅NLbar S g, NLbar S g⁆) (hxN : x ∈ NLbar S g) : ν ⟨x, hxN⟩ = 1 := by
  have hle : ⁅NLbar S g, NLbar S g⁆ ≤ (ν.ker).map (NLbar S g).subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : ⁅a, b⁆ ∈ NLbar S g :=
      Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha hb)
    refine ⟨⟨⁅a, b⁆, hab⟩, ?_, rfl⟩
    show ν ⟨⁅a, b⁆, hab⟩ = 1
    have e : (⟨⁅a, b⁆, hab⟩ : NLbar S g) = ⁅(⟨a, ha⟩ : NLbar S g), ⟨b, hb⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hxN⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem commutator_NLbar_eq_map : ⁅NLbar S g, NLbar S g⁆ =
    (commutator (NLbar S g)).map (NLbar S g).subtype :=
  (Subgroup.map_subtype_commutator _).symm

end Generic

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem Kbar_le_commutator_NLbar (hΔ : (Delta S g t).ncard = 6) :
    Kbar S g t ≤ ⁅NLbar S g, NLbar S g⁆ := by
  rw [Kbar_eq_commutator hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ]
  exact Subgroup.commutator_mono Lbar_le_NLbar le_rfl

theorem commutator_NLbar_inf_Lbar (hΔ : (Delta S g t).ncard = 6) :
    ⁅NLbar S g, NLbar S g⁆ ⊓ S.Lbar g = Kbar S g t := by
  obtain ⟨ν, -, hνK⟩ := exists_nu_ker hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine le_antisymm (fun x hx => ?_)
    (le_inf (Kbar_le_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ) (Kbar_le_Lbar ht))
  obtain ⟨hxN', hxL⟩ := Subgroup.mem_inf.mp hx
  exact (hνK x hxL).mp (eq_one_of_mem_commutator_NLbar ν hxN' (Lbar_le_NLbar hxL))

theorem not_mem_commutator_NLbar (hΔ : (Delta S g t).ncard = 6) :
    t ∉ ⁅NLbar S g, NLbar S g⁆ := by
  obtain ⟨ν, hν, -⟩ := exists_nu_ker hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  exact fun h => hν (eq_one_of_mem_commutator_NLbar ν h (Lbar_le_NLbar ht))

open scoped Classical in
theorem map_permDelta_commutator (hΔ : (Delta S g t).ncard = 6) :
    (commutator (NLbar S g)).map (permDelta S g t) = alternatingGroup (Delta S g t) := by
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  have h5 : 5 ≤ Nat.card (Delta S g t) := by rw [hΔcard]; norm_num
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  rcases range_permDelta_eq hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ with h | h
  · rw [h]
    exact commutator_alternatingGroup_eq_self h5
  · rw [h, ← commutator_def]
    exact alternatingGroup.commutator_perm_eq h5

open scoped Classical in
theorem exists_mem_commutator_perm (hΔ : (Delta S g t).ncard = 6)
    {σ : Equiv.Perm (Delta S g t)} (hσ : σ ∈ alternatingGroup (Delta S g t)) :
    ∃ n : S.O, ∃ hn : n ∈ NLbar S g, n ∈ ⁅NLbar S g, NLbar S g⁆ ∧
      permDelta S g t ⟨n, hn⟩ = σ := by
  rw [← map_permDelta_commutator hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ] at hσ
  obtain ⟨n₀, hn₀, hπ⟩ := hσ
  refine ⟨n₀, n₀.2, ?_, hπ⟩
  rw [commutator_NLbar_eq_map]
  exact ⟨n₀, hn₀, rfl⟩

open scoped Classical in
theorem Kbar_le_commutator_commutator (hΔ : (Delta S g t).ncard = 6) :
    Kbar S g t ≤ ⁅⁅NLbar S g, NLbar S g⁆, ⁅NLbar S g, NLbar S g⁆⁆ := by
  have hι : Fintype.card (Delta S g t) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hΔ
  have hK := Kbar_le_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine (closure_le _).mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hxL : x ∈ S.Lbar g := delta_subset_Lbar ht hx
  have hyL : y ∈ S.Lbar g := delta_subset_Lbar ht hy
  by_cases hxy : x = y
  · rw [hxy, mul_self_of_mem_Lbar S H.conj_mem hyL]
    exact one_mem _
  · set x' : Delta S g t := ⟨x, hx⟩
    set y' : Delta S g t := ⟨y, hy⟩
    have hx'y' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    obtain ⟨c, d, hc, hd, hcd⟩ := SixGen.exists_two_ne_notMem hι
      ({x', y'} : Finset (Delta S g t)) (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
    have hσ : Equiv.swap x' y' * Equiv.swap y' c ∈ alternatingGroup (Delta S g t) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hx'y',
        Equiv.Perm.sign_swap (Ne.symm hc.2)]
      rfl
    have hσx : (Equiv.swap x' y' * Equiv.swap y' c) x' = y' := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx'y' (Ne.symm hc.1)]
      exact Equiv.swap_apply_left _ _
    have hσd : (Equiv.swap x' y' * Equiv.swap y' c) d = d := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hd.2 hcd.symm,
        Equiv.swap_apply_of_ne_of_ne hd.1 hd.2]
    obtain ⟨n, hn, hnN', hπ⟩ :=
      exists_mem_commutator_perm hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hσ
    have hnx : n * x * n⁻¹ = y := by
      have h1 : ((permDelta S g t ⟨n, hn⟩ x' : Delta S g t) : S.O) = n * x * n⁻¹ := rfl
      rw [← h1, hπ, hσx]
    have hnd : n * (d : S.O) * n⁻¹ = (d : S.O) := by
      have h1 : ((permDelta S g t ⟨n, hn⟩ d : Delta S g t) : S.O) = n * (d : S.O) * n⁻¹ := rfl
      rw [← h1, hπ, hσd]
    have hxx : x * x = 1 := mul_self_of_mem_Lbar S H.conj_mem hxL
    have hkK : x * (d : S.O) ∈ Kbar S g t := subset_closure ⟨x, hx, d, d.2, rfl⟩
    have e : ⁅n, x * (d : S.O)⁆ = x * y := by
      rw [commutatorElement_def]
      calc n * (x * (d : S.O)) * n⁻¹ * (x * (d : S.O))⁻¹
          = (n * x * n⁻¹) * (n * (d : S.O) * n⁻¹) * (x * (d : S.O))⁻¹ := by group
        _ = y * (d : S.O) * ((d : S.O)⁻¹ * x⁻¹) := by rw [hnx, hnd, mul_inv_rev]
        _ = y * x⁻¹ := by group
        _ = y * x := by rw [inv_eq_of_mul_eq_one_right hxx]
        _ = x * y := Lbar_comm S H.conj_mem hyL hxL
    rw [← e]
    exact Subgroup.commutator_mem_commutator hnN' (hK hkK)

open scoped Classical in
theorem commutator_commutator_NLbar (hΔ : (Delta S g t).ncard = 6) :
    ⁅⁅NLbar S g, NLbar S g⁆, ⁅NLbar S g, NLbar S g⁆⁆ = ⁅NLbar S g, NLbar S g⁆ := by
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  have h5 : 5 ≤ Nat.card (Delta S g t) := by rw [hΔcard]; norm_num
  refine le_antisymm (Subgroup.commutator_le_self _) (fun z hz => ?_)
  set N₀ : Subgroup (NLbar S g) := commutator (NLbar S g)
  have hN'eq : ⁅NLbar S g, NLbar S g⁆ = N₀.map (NLbar S g).subtype := commutator_NLbar_eq_map
  have hN''eq : ⁅⁅NLbar S g, NLbar S g⁆, ⁅NLbar S g, NLbar S g⁆⁆ =
      (⁅N₀, N₀⁆).map (NLbar S g).subtype := by
    rw [hN'eq, Subgroup.map_commutator]
  have hπN₀ : N₀.map (permDelta S g t) = alternatingGroup (Delta S g t) :=
    map_permDelta_commutator hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hπN₁ : (⁅N₀, N₀⁆).map (permDelta S g t) = alternatingGroup (Delta S g t) := by
    rw [Subgroup.map_commutator, hπN₀]
    exact commutator_alternatingGroup_eq_self h5
  rw [hN'eq] at hz
  obtain ⟨n₀, hn₀, rfl⟩ := hz
  have hπ : permDelta S g t n₀ ∈ (⁅N₀, N₀⁆).map (permDelta S g t) := by
    rw [hπN₁, ← hπN₀]
    exact ⟨n₀, hn₀, rfl⟩
  obtain ⟨m, hm, hmπ⟩ := hπ
  have hmN₀ : m ∈ N₀ := Subgroup.commutator_le_self _ hm
  have hw : permDelta S g t (m⁻¹ * n₀) = 1 := by rw [map_mul, map_inv, hmπ, inv_mul_cancel]
  have hwL : ((m⁻¹ * n₀ : NLbar S g) : S.O) ∈ S.Lbar g :=
    (permDelta_eq_one_iff_mem_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ _).mp hw
  have hwN' : ((m⁻¹ * n₀ : NLbar S g) : S.O) ∈ ⁅NLbar S g, NLbar S g⁆ := by
    rw [hN'eq]
    exact ⟨m⁻¹ * n₀, mul_mem (inv_mem hmN₀) hn₀, rfl⟩
  have hwK : ((m⁻¹ * n₀ : NLbar S g) : S.O) ∈ Kbar S g t := by
    rw [← commutator_NLbar_inf_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ]
    exact Subgroup.mem_inf.mpr ⟨hwN', hwL⟩
  have hwN'' := Kbar_le_commutator_commutator hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hwK
  rw [hN''eq] at hwN'' ⊢
  obtain ⟨w₁, hw₁, hw₁e⟩ := hwN''
  have hw₁' : w₁ = m⁻¹ * n₀ := Subtype.ext hw₁e
  rw [hw₁'] at hw₁
  refine ⟨n₀, ?_, rfl⟩
  have e : n₀ = m * (m⁻¹ * n₀) := by group
  rw [e]
  exact mul_mem hm hw₁

open scoped Classical in
theorem card_commutator_NLbar (hΔ : (Delta S g t).ncard = 6) :
    Nat.card ↥(⁅NLbar S g, NLbar S g⁆) = 5760 := by
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  set N₀ : Subgroup (NLbar S g) := commutator (NLbar S g)
  have hN'eq : ⁅NLbar S g, NLbar S g⁆ = N₀.map (NLbar S g).subtype := commutator_NLbar_eq_map
  rw [hN'eq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hnt : Nontrivial (Delta S g t) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have h1 := Subgroup.relIndex_mul_card (H := (permDelta S g t).ker) (K := N₀)
  have hπN₀ : N₀.map (permDelta S g t) = alternatingGroup (Delta S g t) :=
    map_permDelta_commutator hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  rw [Subgroup.relIndex_ker, hπN₀, nat_card_alternatingGroup, hΔcard] at h1
  have hinf : Nat.card ↥((permDelta S g t).ker ⊓ N₀) = 16 := by
    have hmap : ((permDelta S g t).ker ⊓ N₀).map (NLbar S g).subtype = Kbar S g t := by
      rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), ← hN'eq,
        ker_permDelta_eq hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
        Subgroup.map_subgroupOf_eq_of_le Lbar_le_NLbar, inf_comm,
        commutator_NLbar_inf_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ]
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (NLbar S g)), hmap,
      card_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ]
    norm_num
  rw [hinf] at h1
  have hfact : Nat.factorial 6 = 720 := by decide
  rw [hfact] at h1
  omega

open scoped Classical in
theorem exists_conj_of_mem_Kbar (hΔ : (Delta S g t).ncard = 6) {a b : S.O}
    (ha : a ∈ Kbar S g t) (ha1 : a ≠ 1) (hb : b ∈ Kbar S g t) (hb1 : b ≠ 1) :
    ∃ n ∈ ⁅NLbar S g, NLbar S g⁆, n * a * n⁻¹ = b := by
  have hι : Fintype.card (Delta S g t) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hΔ
  obtain ⟨-, f, -, -, -, -, -, hpair, -⟩ :=
    invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hpair a ha ha1
  obtain ⟨x', hx', y', hy', hxy', rfl⟩ := hpair b hb hb1
  obtain ⟨σ, hσ, hσx, hσy⟩ := SixGen.exists_alt_two hι (i := (⟨x, hx⟩ : Delta S g t))
    (j := (⟨y, hy⟩ : Delta S g t)) (k := (⟨x', hx'⟩ : Delta S g t))
    (l := (⟨y', hy'⟩ : Delta S g t)) (fun h => hxy (congrArg Subtype.val h))
    (fun h => hxy' (congrArg Subtype.val h))
  obtain ⟨n, hn, hnN', hπ⟩ := exists_mem_commutator_perm hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hσ
  refine ⟨n, hnN', ?_⟩
  have e1 : n * x * n⁻¹ = x' := by
    have h1 : ((permDelta S g t ⟨n, hn⟩ ⟨x, hx⟩ : Delta S g t) : S.O) = n * x * n⁻¹ := rfl
    rw [← h1, hπ, hσx]
  have e2 : n * y * n⁻¹ = y' := by
    have h1 : ((permDelta S g t ⟨n, hn⟩ ⟨y, hy⟩ : Delta S g t) : S.O) = n * y * n⁻¹ := rfl
    rw [← h1, hπ, hσy]
  calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    _ = x' * y' := by rw [e1, e2]

theorem twoCentralBar_of_mem_Kbar (hΔ : (Delta S g t).ncard = 6) {ι : S.O}
    (hι : ι ∈ Kbar S g t) (hι1 : ι ≠ 1) : TwoCentralBar S ι := by
  obtain ⟨-, f, -, -, -, -, -, -, htrans, -⟩ :=
    invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  obtain ⟨T, hTsyl, hLT, hTN⟩ := exists_sylow_le_NLbar H C
  have hKT : Kbar S g t ≤ T := (Kbar_le_Lbar ht).trans hLT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent T := hTsyl.isPGroup.isNilpotent
  set H' : Subgroup T := (Kbar S g t).subgroupOf T with hH'
  haveI : H'.Normal := ⟨fun k hk x => by
    rw [hH', Subgroup.mem_subgroupOf] at hk ⊢
    exact conj_mem_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ (hTN x.2) hk⟩
  have hH'ne : H' ≠ ⊥ := by
    intro h
    have : (⟨ι, hKT hι⟩ : T) ∈ H' := Subgroup.mem_subgroupOf.mpr hι
    rw [h, Subgroup.mem_bot] at this
    exact hι1 (congrArg Subtype.val this)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH'ne)
  have hzH : (z : T) ∈ H' := (Subgroup.mem_inf.mp z.2).1
  have hzC : (z : T) ∈ center T := (Subgroup.mem_inf.mp z.2).2
  have hι₀K : ((z : T) : S.O) ∈ Kbar S g t := Subgroup.mem_subgroupOf.mp hzH
  have hι₀1 : ((z : T) : S.O) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hι₀c : ∀ y ∈ T, y * ((z : T) : S.O) = ((z : T) : S.O) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨y, hy⟩)
  obtain ⟨n, hn, hnι⟩ := htrans _ hι₀K hι₀1 ι hι hι1
  refine ⟨T.map (MulAut.conj n).toMonoidHom, ?_, ?_⟩
  · have hMbar : S.Mbar.map (MulAut.conj n).toMonoidHom = S.Mbar :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hn.1)
    have h1 := hTsyl.map (MulAut.conj n).toMonoidHom
    rwa [hMbar] at h1
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hnι]
    calc n * y * n⁻¹ * (n * ((z : T) : S.O) * n⁻¹) = n * (y * ((z : T) : S.O)) * n⁻¹ := by group
      _ = n * (((z : T) : S.O) * y) * n⁻¹ := by rw [hι₀c y hy]
      _ = n * ((z : T) : S.O) * n⁻¹ * (n * y * n⁻¹) := by group

open scoped Classical in
theorem perfect_core_N (hΔ : (Delta S g t).ncard = 6) :
    ⁅NLbar S g, NLbar S g⁆ ≤ S.Mbar ∧
      ⁅⁅NLbar S g, NLbar S g⁆, ⁅NLbar S g, NLbar S g⁆⁆ = ⁅NLbar S g, NLbar S g⁆ ∧
      ⁅NLbar S g, NLbar S g⁆ ⊓ S.Lbar g = Kbar S g t ∧
      Nat.card ↥(⁅NLbar S g, NLbar S g⁆) = 5760 ∧
      t ∉ ⁅NLbar S g, NLbar S g⁆ ∧
      (∀ a ∈ Kbar S g t, a ≠ 1 → ∀ b ∈ Kbar S g t, b ≠ 1 →
        ∃ n ∈ ⁅NLbar S g, NLbar S g⁆, n * a * n⁻¹ = b) ∧
      (∀ ι ∈ Kbar S g t, ι ≠ 1 → TwoCentralBar S ι) :=
  ⟨(Subgroup.commutator_le_self _).trans inf_le_left,
    commutator_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
    commutator_NLbar_inf_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
    card_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
    not_mem_commutator_NLbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
    fun _ ha ha1 _ hb hb1 =>
      exists_conj_of_mem_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ ha ha1 hb hb1,
    fun _ hι hι1 => twoCentralBar_of_mem_Kbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hι hι1⟩

end Context

end Case25

end CFSG.GF2Type.Smith1979
