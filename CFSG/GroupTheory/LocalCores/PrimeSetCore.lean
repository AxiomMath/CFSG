module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.LocalCores

open Subgroup

variable {G : Type*} [Group G]

theorem le_piCore_of_normal {π : Set Nat.Primes} {N : Subgroup G} (hN : N.Normal)
    (hNπ : IsPiSubgroup π N) : N ≤ piCore π G :=
  le_sSup ⟨hN, hNπ⟩

theorem isPiSubgroup_map {G' : Type*} [Group G'] {π : Set Nat.Primes} {K : Subgroup G}
    (hK : IsPiSubgroup π K) (f : G →* G') : IsPiSubgroup π (K.map f) := fun q hq =>
  hK q (hq.trans (K.card_map_dvd f))

theorem piCore_map_mulEquiv {G' : Type*} [Group G'] (π : Set Nat.Primes) (f : G ≃* G') :
    (piCore π G).map f.toMonoidHom = piCore π G' := by
  let S : Set (Subgroup G) := {K | K.Normal ∧ IsPiSubgroup π K}
  let S' : Set (Subgroup G') := {K | K.Normal ∧ IsPiSubgroup π K}
  have hImage : MulEquiv.mapSubgroup f '' S = S' := by
    ext K'
    constructor
    · rintro ⟨K, ⟨hKn, hKπ⟩, rfl⟩
      exact ⟨hKn.map f.toMonoidHom f.surjective, isPiSubgroup_map hKπ f.toMonoidHom⟩
    · rintro ⟨hKn, hKπ⟩
      refine ⟨K'.map f.symm.toMonoidHom, ⟨hKn.map _ f.symm.surjective,
        isPiSubgroup_map hKπ f.symm.toMonoidHom⟩, ?_⟩
      change (K'.map f.symm.toMonoidHom).map f.toMonoidHom = K'
      rw [Subgroup.map_map]
      convert Subgroup.map_id K'
      ext x
      simp
  have h1 : (piCore π G).map f.toMonoidHom = MulEquiv.mapSubgroup f (sSup S) := rfl
  rw [h1, OrderIso.map_sSup, ← sSup_image, hImage]
  rfl

instance piCore_characteristic (π : Set Nat.Primes) : (piCore π G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun φ => piCore_map_mulEquiv π φ

instance piCore_normal (π : Set Nat.Primes) : (piCore π G).Normal := inferInstance

theorem prime_set_core_normal (π : Set Nat.Primes) :
    (piCore π G).Characteristic ∧ (piCore π G).Normal :=
  ⟨inferInstance, inferInstance⟩

theorem isPiSubgroup_bot (π : Set Nat.Primes) : IsPiSubgroup π (⊥ : Subgroup G) := fun q hq =>
  absurd (Nat.dvd_one.mp (by simpa using hq)) q.2.ne_one

theorem isPiSubgroup_of_map_of_inf_ker [Finite G] {G' : Type*} [Group G'] {π : Set Nat.Primes}
    (f : G →* G') {H : Subgroup G} (hmap : IsPiSubgroup π (H.map f))
    (hker : IsPiSubgroup π (H ⊓ f.ker)) : IsPiSubgroup π H := by
  intro q hq
  have : Fact q.val.Prime := ⟨q.2⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) q.val hq
  have hdvd : orderOf (f x) ∣ q.val := by
    rw [← hx, ← Subgroup.orderOf_coe]
    exact orderOf_map_dvd f x
  rcases (Nat.dvd_prime q.2).mp hdvd with h1 | hq'
  · have hxker : (x : G) ∈ H ⊓ f.ker := ⟨x.2, by simpa [orderOf_eq_one_iff] using h1⟩
    apply hker q
    rw [← hx, ← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard _ hxker
  · apply hmap q
    rw [← hq']
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem f x.2)

theorem isPiSubgroup_sup_normal [Finite G] {π : Set Nat.Primes} {H K : Subgroup G} [K.Normal]
    (hH : IsPiSubgroup π H) (hK : IsPiSubgroup π K) : IsPiSubgroup π (H ⊔ K) := by
  refine isPiSubgroup_of_map_of_inf_ker (QuotientGroup.mk' K) ?_ ?_
  · rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    exact fun q hq => hH q (hq.trans (H.card_map_dvd _))
  · rw [QuotientGroup.ker_mk', inf_eq_right.mpr le_sup_right]
    exact hK

theorem piCore_isPiSubgroup [Finite G] (π : Set Nat.Primes) : IsPiSubgroup π (piCore π G) := by
  let S : Set (Subgroup G) := {K | K.Normal ∧ IsPiSubgroup π K}
  have hS : S.Finite := Set.toFinite S
  have hcore : piCore π G = hS.toFinset.sup id := by
    rw [Finset.sup_id_eq_sSup, Set.Finite.coe_toFinset]
    rfl
  rw [hcore]
  refine (Finset.sup_induction (p := fun K : Subgroup G => K.Normal ∧ IsPiSubgroup π K)
    ⟨normal_bot, isPiSubgroup_bot π⟩ ?_ ?_).2
  · rintro a ⟨ha, haπ⟩ b ⟨hb, hbπ⟩
    exact ⟨Subgroup.sup_normal a b, isPiSubgroup_sup_normal haπ hbπ⟩
  · intro b hb
    exact hS.mem_toFinset.mp hb

theorem prime_set_core_maximal [Finite G] (π : Set Nat.Primes) :
    IsPiSubgroup π (piCore π G) ∧
      (∀ N : Subgroup G, N.Normal → IsPiSubgroup π N → N ≤ piCore π G) ∧
      ∀ M : Subgroup G, M.Normal → IsPiSubgroup π M →
        (∀ N : Subgroup G, N.Normal → IsPiSubgroup π N → N ≤ M) → M = piCore π G :=
  ⟨piCore_isPiSubgroup π, fun _ hN hNπ => le_piCore_of_normal hN hNπ,
    fun _ hM hMπ hmax => le_antisymm (le_piCore_of_normal hM hMπ)
      (hmax _ inferInstance (piCore_isPiSubgroup π))⟩

theorem prime_set_core_normal_intersection [Finite G] (π : Set Nat.Primes) {N : Subgroup G}
    (hN : N.Normal) : (piCore π N).map N.subtype = N ⊓ piCore π G := by
  apply le_antisymm
  · refine le_inf (Subgroup.map_subtype_le _) (le_piCore_of_normal ?_ ?_)
    · exact ConjAct.normal_of_characteristic_of_normal
    · exact isPiSubgroup_map (piCore_isPiSubgroup (G := N) π) N.subtype
  · have hle : (N ⊓ piCore π G).subgroupOf N ≤ piCore π N := by
      have : N.Normal := hN
      refine le_piCore_of_normal ((inferInstance : (N ⊓ piCore π G).Normal).comap N.subtype) ?_
      refine fun q hq => piCore_isPiSubgroup (G := G) π q (hq.trans ?_)
      rw [show Nat.card ((N ⊓ piCore π G).subgroupOf N) = Nat.card (N ⊓ piCore π G : Subgroup G)
        from Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    have := Subgroup.map_mono (f := N.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at this

theorem prime_set_core_quotient [Finite G] (π : Set Nat.Primes) :
    piCore π (G ⧸ piCore π G) = ⊥ := by
  set f := QuotientGroup.mk' (piCore π G)
  set H := (piCore π (G ⧸ piCore π G)).comap f
  have hHπ : IsPiSubgroup π H := by
    refine isPiSubgroup_of_map_of_inf_ker f ?_ ?_
    · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
      exact piCore_isPiSubgroup π
    · rw [QuotientGroup.ker_mk']
      exact (piCore_isPiSubgroup π).of_le inf_le_right
  have hH : H ≤ piCore π G := le_piCore_of_normal (Subgroup.Normal.comap inferInstance f) hHπ
  have := Subgroup.map_mono (f := f) hH
  rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self, le_bot_iff] at this

theorem prime_set_core_subnormal_intersection [Finite G] (π : Set Nat.Primes) {N : Subgroup G}
    (hN : N.IsSubnormal) : (piCore π N).map N.subtype = N ⊓ piCore π G := by
  induction hN with
  | top =>
    rw [top_inf_eq, ← piCore_map_mulEquiv π (Subgroup.topEquiv (G := G))]
    rfl
  | step H K hHK _ hHn ih =>
    have key := prime_set_core_normal_intersection π hHn
    have hmap := congrArg (Subgroup.map K.subtype) key
    rw [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHK, ih, ← inf_assoc, inf_eq_left.mpr hHK, Subgroup.map_map] at hmap
    rw [← hmap, ← piCore_map_mulEquiv π (Subgroup.subgroupOfEquivOfLe hHK), Subgroup.map_map]
    rfl

theorem distinct_prime_cores_commute {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    pCore p G ⊓ pCore r G = ⊥ ∧ ⁅pCore p G, pCore r G⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hinf : pCore p G ⊓ pCore r G = ⊥ :=
    (IsPGroup.disjoint_of_ne p r hpr _ _ pCore_isPGroup pCore_isPGroup).eq_bot
  have : (pCore p G).Normal := pCore_normal
  have : (pCore r G).Normal := pCore_normal
  exact ⟨hinf, le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf _ _)⟩

end CFSG.LocalCores
