module

public import CFSG.CGT.Timmesfeld75.WCBasic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

section Conjugates

theorem mem_normalizer_of_conjSubgroup_eq {g : G} {T : Subgroup G} (h : conjSubgroup g T = T) :
    g ∈ Subgroup.normalizer (T : Set G) :=
  mem_normalizer_iff_conjSubgroup_eq.2 h

theorem mul_comm_of_conj_mul_comm {g a b : G}
    (h : g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g)) : a * b = b * a :=
  calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

theorem isPGroup_two_of_isElemAbelian {T : Subgroup G} (hT : IsElemAbelian 2 T) :
    IsPGroup 2 T := CFSG.Open.IsElemAbelian.isPGroup hT

theorem card_conjSubgroup (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSubgroup_eq_of_le [Finite G] {T : Subgroup G} {g : G} (h : conjSubgroup g T ≤ T) :
    conjSubgroup g T = T :=
  Subgroup.eq_of_le_of_card_ge h (card_conjSubgroup g T).ge

theorem conjSubgroup_eq_of_ge [Finite G] {T : Subgroup G} {g : G} (h : T ≤ conjSubgroup g T) :
    conjSubgroup g T = T :=
  (Subgroup.eq_of_le_of_card_ge h (card_conjSubgroup g T).le).symm

end Conjugates

section FixedModuloSubgroup

theorem exists_fixed_mod_of_pGroup [Finite G] {T A C : Subgroup G} (hT : IsPGroup 2 T)
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hA : IsPGroup 2 A)
    (hAT : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T) (hCT : C ≤ T) (hne : C ≠ T)
    (hCA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) :
    ∃ h ∈ T, h ∉ C ∧ ∀ a ∈ A, ⁅a, h⁆ ∈ C := by
  let _ : SMul A T := ⟨fun a t => ⟨(a : G) * t * (a : G)⁻¹, hAT a a.2 t t.2⟩⟩
  have hsmul : ∀ (a : A) (t : T), ((a • t : T) : G) = (a : G) * t * (a : G)⁻¹ := fun _ _ => rfl
  let _ : MulAction A T :=
    { one_smul := fun t => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun a b t => Subtype.ext (by simp only [hsmul]; simp [mul_assoc]) }
  have hQA : MulAction.QuotientAction A (C.subgroupOf T) :=
    ⟨fun a x y h => by
      rw [Subgroup.mem_subgroupOf] at h ⊢
      have hc : ((x⁻¹ * y : T) : G) ∈ C := h
      have := hCA a a.2 _ hc
      have e : (((a • x)⁻¹ * a • y : T) : G) = (a : G) * ((x⁻¹ * y : T) : G) * (a : G)⁻¹ := by
        simp only [hsmul, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e, this]
      simpa using hc⟩
  have hidx : 2 ∣ Nat.card (T ⧸ C.subgroupOf T) := by
    obtain ⟨n, hn⟩ := hT.index (C.subgroupOf T)
    have hn1 : n ≠ 0 := by
      rintro rfl
      have h1 : (C.subgroupOf T).index = 1 := by simpa using hn
      rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
      exact hne (le_antisymm hCT h1)
    change 2 ∣ (C.subgroupOf T).index
    rw [hn]
    exact dvd_pow_self 2 hn1
  have hfix1 : (QuotientGroup.mk 1 : T ⧸ C.subgroupOf T) ∈
      MulAction.fixedPoints A (T ⧸ C.subgroupOf T) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [MulAction.Quotient.smul_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by rw [hsmul]; simp))
  obtain ⟨b, hb, hb1⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (T ⧸ C.subgroupOf T) hidx hfix1
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨(h : G), h.2, ?_, ?_⟩
  · intro hhC
    refine hb1 ?_
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hhC
  · intro a ha
    have h1 := (MulAction.mem_fixedPoints.1 hb) ⟨a, ha⟩
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have hc : ((a * h * a⁻¹)⁻¹ * h)⁻¹ ∈ C := C.inv_mem h1
    have hcomm : ⁅a, (h : G)⁆ = (h : G) * ((a * h * a⁻¹)⁻¹ * h)⁻¹ * (h : G)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hcomm, hTab h h.2 _ (hCT hc), mul_inv_cancel_right]
    exact hc

end FixedModuloSubgroup

section WeaklyClosed

theorem IsWC.conj {T : Subgroup G} (hT : IsWC T) (g : G) : IsWC (conjSubgroup g T) := by
  refine ⟨isElemAbelian_conjSubgroup hT.1 g, fun t' ht' ht'1 => ?_⟩
  have ht : g⁻¹ * t' * g ∈ T := mem_conjSubgroup.1 ht'
  have ht1 : g⁻¹ * t' * g ≠ 1 := by
    intro h
    exact ht'1 (by simpa [mul_assoc] using congrArg (fun z => g * z * g⁻¹) h)
  obtain ⟨-, hwc⟩ := hT.2 _ ht ht1
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mul_comm_of_conj_mul_comm (elemAbelian_mul_comm hT.1 ht (mem_conjSubgroup.1 hx))
  · have hk' : conjSubgroup (g⁻¹ * k * g) T ≤
        Subgroup.centralizer ({g⁻¹ * t' * g} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hx' : g * x * g⁻¹ ∈ conjSubgroup k (conjSubgroup g T) := by
        rw [conjSubgroup_conjSubgroup, mem_conjSubgroup]
        have := mem_conjSubgroup.1 hx
        convert this using 1
        group
      have hc := Subgroup.mem_centralizer_iff.1 (hk hx') t' (Set.mem_singleton t')
      calc g⁻¹ * t' * g * x = g⁻¹ * (t' * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹ * t') * g := by rw [hc]
        _ = x * (g⁻¹ * t' * g) := by group
    have hm := hwc _ hk'
    rw [conjSubgroup_conjSubgroup, show k * g = g * (g⁻¹ * k * g) by group,
      ← conjSubgroup_conjSubgroup, hm]

theorem eq_of_le_normalizer_of_isWC [Finite G] {T U : Subgroup G} (hT : IsWC T)
    (hU : ∃ g : G, U = conjSubgroup g T) (hN : U ≤ Subgroup.normalizer (T : Set G)) : U = T := by
  obtain ⟨g, rfl⟩ := hU
  by_cases hbot : T = ⊥
  · subst hbot
    simp [conjSubgroup]
  obtain ⟨h, hhT, hhC, hcomm⟩ := exists_fixed_mod_of_pGroup (isPGroup_two_of_isElemAbelian hT.1)
    (fun x hx y hy => elemAbelian_mul_comm hT.1 hx hy)
    (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hT.1 g))
    (fun a ha t ht => conj_mem_of_mem_normalizer (hN ha) ht) (bot_le : (⊥ : Subgroup G) ≤ T)
    (fun hb => hbot hb.symm)
    (fun a _ c hc => by rw [Subgroup.mem_bot.1 hc]; simp)
  have hh1 : h ≠ 1 := fun h1 => hhC (h1 ▸ (⊥ : Subgroup G).one_mem)
  refine (hT.2 h hhT hh1).2 g fun a ha => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact ((commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 (hcomm a ha))).symm)

end WeaklyClosed

section PGroupConjugates

theorem exists_mem_normalizer_not_mem_of_pGroup [Finite G] {S H : Subgroup G} (hS : IsPGroup 2 S)
    (hHS : H ≤ S) (hne : H ≠ S) :
    ∃ x ∈ S, x ∈ Subgroup.normalizer (H : Set G) ∧ x ∉ H := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : H.subgroupOf S < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hHS (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨x, x.2, ?_, hxn⟩
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · intro hh
    have := (hx ⟨h, hHS hh⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have hhS : h ∈ S := by
      have : (x : G)⁻¹ * (x * h * x⁻¹) * x ∈ S :=
        S.mul_mem (S.mul_mem (S.inv_mem x.2) (hHS hh)) x.2
      simpa [mul_assoc] using this
    have := (hx ⟨h, hhS⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this

theorem eq_of_conj_le_pGroup [Finite G] {T S : Subgroup G} (hT : IsWC T) (hS : IsPGroup 2 S)
    (hTS : T ≤ S) {g : G} (hg : conjSubgroup g T ≤ S) : conjSubgroup g T = T := by
  have key : ∀ H : Subgroup G, T ≤ H → H ≤ S →
      (∀ k : G, conjSubgroup k T ≤ H → conjSubgroup k T = T) →
      ∀ k : G, conjSubgroup k T ≤ S → conjSubgroup k T = T := by
    intro H
    induction H using WellFoundedGT.induction with
    | ind H ih =>
      intro hTH hHS hgood
      by_cases hHeq : H = S
      · subst hHeq
        exact hgood
      obtain ⟨x, hxS, hxN, hxH⟩ := exists_mem_normalizer_not_mem_of_pGroup hS hHS hHeq
      have hlt : H < S ⊓ Subgroup.normalizer (H : Set G) :=
        lt_of_le_of_ne (le_inf hHS Subgroup.le_normalizer)
          fun h => hxH (by rw [h]; exact ⟨hxS, hxN⟩)
      have hNT : S ⊓ Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (T : Set G) := by
        rintro y ⟨-, hyN⟩
        refine mem_normalizer_of_conjSubgroup_eq (hgood y fun z hz => ?_)
        have hz' : y⁻¹ * z * y ∈ T := mem_conjSubgroup.1 hz
        have := (Subgroup.mem_normalizer_iff.1 hyN _).1 (hTH hz')
        simpa [mul_assoc] using this
      exact ih _ hlt (le_inf (hTH.trans hHS) (hTH.trans Subgroup.le_normalizer)) inf_le_left
        fun k hk => eq_of_le_normalizer_of_isWC hT ⟨k, rfl⟩ (hk.trans hNT)
  exact key T le_rfl hTS (fun k hk => conjSubgroup_eq_of_le hk) g hg

end PGroupConjugates

section CorollaryB

theorem commute_conjSubgroup_of_comm_mem {A C : Subgroup G} {h : G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hCA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hh : ∀ a ∈ A, ⁅a, h⁆ ∈ C) : ∀ x ∈ A, ∀ y ∈ conjSubgroup h A, Commute x y := by
  intro x hx y hy
  have ha : h⁻¹ * y * h ∈ A := mem_conjSubgroup.1 hy
  have hc : ⁅(h⁻¹ * y * h)⁻¹, h⁆ ∈ C := hh _ (A.inv_mem ha)
  have hy_eq : y = (h⁻¹ * y * h) * ⁅(h⁻¹ * y * h)⁻¹, h⁆ := by
    simp only [commutatorElement_def]; group
  rw [hy_eq]
  calc x * (h⁻¹ * y * h * ⁅(h⁻¹ * y * h)⁻¹, h⁆)
      = (x * (h⁻¹ * y * h)) * ⁅(h⁻¹ * y * h)⁻¹, h⁆ := (mul_assoc _ _ _).symm
    _ = ((h⁻¹ * y * h) * x) * ⁅(h⁻¹ * y * h)⁻¹, h⁆ := by rw [hAab x hx _ ha]
    _ = (h⁻¹ * y * h) * (x * ⁅(h⁻¹ * y * h)⁻¹, h⁆) := mul_assoc _ _ _
    _ = (h⁻¹ * y * h) * (⁅(h⁻¹ * y * h)⁻¹, h⁆ * x) := by rw [hCA x hx _ hc]
    _ = ((h⁻¹ * y * h) * ⁅(h⁻¹ * y * h)⁻¹, h⁆) * x := (mul_assoc _ _ _).symm

theorem commute_of_commute_conjSubgroup {g : G} {U V : Subgroup G}
    (h : ∀ x ∈ conjSubgroup g U, ∀ y ∈ conjSubgroup g V, Commute x y) :
    ∀ x ∈ U, ∀ y ∈ V, Commute x y := by
  intro x hx y hy
  have hx' : g * x * g⁻¹ ∈ conjSubgroup g U := by
    rw [mem_conjSubgroup]; simpa [mul_assoc] using hx
  have hy' : g * y * g⁻¹ ∈ conjSubgroup g V := by
    rw [mem_conjSubgroup]; simpa [mul_assoc] using hy
  have h2 : g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := h _ hx' _ hy'
  calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h2]
    _ = y * x := by group

theorem eq_of_conj_le_centralizer_of_corBHyp [Finite G] {T : Subgroup G}
    (hab : IsElemAbelian 2 T) (hTI : IsTI T)
    (hiff : ∀ g : G, (∀ x ∈ T, ∀ y ∈ conjSubgroup g T, Commute x y) ↔ conjSubgroup g T = T)
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) {g : G}
    (hg : conjSubgroup g T ≤ Subgroup.centralizer ({t} : Set G)) : conjSubgroup g T = T := by
  by_contra hne
  have hAab : ∀ a ∈ conjSubgroup g T, ∀ b ∈ conjSubgroup g T, a * b = b * a :=
    fun a ha b hb => elemAbelian_mul_comm (isElemAbelian_conjSubgroup hab g) ha hb
  have hAN : conjSubgroup g T ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.1 (hg hx) t (Set.mem_singleton t)
    have hconj : x⁻¹ * t * x = t := by rw [mul_assoc, hxt, inv_mul_cancel_left]
    rcases hTI x with h0 | h1
    · have : t ∈ T ⊓ conjSubgroup x T := ⟨ht, mem_conjSubgroup.2 (by rw [hconj]; exact ht)⟩
      rw [h0, Subgroup.mem_bot] at this
      exact absurd this ht1
    · exact mem_normalizer_of_conjSubgroup_eq
        (conjSubgroup_eq_of_ge (h1.symm.le.trans inf_le_right))
  have hTA : T ⊓ conjSubgroup g T = ⊥ := by
    rcases hTI g with h0 | h1
    · exact h0
    · exact absurd (conjSubgroup_eq_of_ge (h1.symm.le.trans inf_le_right)) hne
  have hAC : ∀ a ∈ conjSubgroup g T, ∀ h ∈ T ⊓ Subgroup.normalizer (conjSubgroup g T : Set G),
      a * h = h * a := by
    intro a ha h hh
    have h1 : ⁅a, h⁆ ∈ T := comm_mem_of_mem_normalizer (hAN ha) hh.1
    have h2 : ⁅a, h⁆ ∈ conjSubgroup g T := by
      rw [← commutatorElement_inv]
      exact (conjSubgroup g T).inv_mem (comm_mem_of_mem_normalizer hh.2 ha)
    have h3 : ⁅a, h⁆ ∈ T ⊓ conjSubgroup g T := ⟨h1, h2⟩
    rw [hTA, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hCne : T ⊓ Subgroup.normalizer (conjSubgroup g T : Set G) ≠ T := by
    intro hCT
    refine hne ((hiff g).1 fun x hx y hy => ?_)
    exact (hAC y hy x (by rw [hCT]; exact hx)).symm
  obtain ⟨h, hhT, hhC, hcomm⟩ := exists_fixed_mod_of_pGroup (isPGroup_two_of_isElemAbelian hab)
    (fun x hx y hy => elemAbelian_mul_comm hab hx hy)
    (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hab g))
    (fun a ha t ht => conj_mem_of_mem_normalizer (hAN ha) ht) inf_le_left hCne hAC
  have hid : conjSubgroup g (conjSubgroup (g⁻¹ * h * g) T) = conjSubgroup h (conjSubgroup g T) := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      show g * (g⁻¹ * h * g) = h * g by group]
  have hcommA := commute_conjSubgroup_of_comm_mem hAab hAC hcomm
  have hk : conjSubgroup (g⁻¹ * h * g) T = T :=
    (hiff _).1 (commute_of_commute_conjSubgroup fun x hx y hy => hcommA x hx y (hid ▸ hy))
  have hhA : conjSubgroup h (conjSubgroup g T) = conjSubgroup g T := by
    rw [← hid, hk]
  exact hhC ⟨hhT, mem_normalizer_of_conjSubgroup_eq hhA⟩

theorem isWC_of_corBHyp [Finite G] {T : Subgroup G} (hT : CorBHyp T) : IsWC T := by
  obtain ⟨hab, hTI, hiff⟩ := hT
  refine ⟨hab, fun t ht ht1 => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact elemAbelian_mul_comm hab ht hx
  · exact eq_of_conj_le_centralizer_of_corBHyp hab hTI hiff ht ht1 hg

end CorollaryB

end CFSG.CGT.Timmesfeld75
