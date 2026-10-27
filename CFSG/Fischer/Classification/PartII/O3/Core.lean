module

public import CFSG.Fischer.Classification.PartII.O3Local
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Fischer.Classification.Skeleton

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

@[expose] def coreSet (E : Set X) (e : X) : Set (Subgroup X) :=
  {S | IsPGroup 3 S ∧ S ≤ LocalGroup E e ∧ ∀ l ∈ LocalGroup E e, ∀ s ∈ S, l * s * l⁻¹ ∈ S}

@[expose] def core (E : Set X) (e : X) : Subgroup X :=
  (CFSG.pCore 3 (LocalGroup E e)).map (LocalGroup E e).subtype

theorem le_core {e : X} {S : Subgroup X} (hS : S ∈ coreSet E e) : S ≤ core E e := by
  intro s hs
  have hsL : s ∈ LocalGroup E e := hS.2.1 hs
  have hN : (S.subgroupOf (LocalGroup E e)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hS.2.2 g g.2 n hn⟩
  have hle : S.subgroupOf (LocalGroup E e) ≤ CFSG.pCore 3 (LocalGroup E e) :=
    le_sSup ⟨hN, hS.1.comap_subtype⟩
  exact ⟨⟨s, hsL⟩, hle (show (⟨s, hsL⟩ : LocalGroup E e) ∈ S.subgroupOf _ from hs), rfl⟩

theorem core_le_localGroup (E : Set X) (e : X) : core E e ≤ LocalGroup E e :=
  Subgroup.map_subtype_le _

theorem isPGroup_core (E : Set X) (e : X) : IsPGroup 3 (core E e) :=
  CFSG.pCore_isPGroup.map _

theorem conj_mem_core {e l s : X} (hl : l ∈ LocalGroup E e) (hs : s ∈ core E e) :
    l * s * l⁻¹ ∈ core E e := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨⟨l, hl⟩ * t * ⟨l, hl⟩⁻¹, CFSG.pCore_normal.conj_mem t ht ⟨l, hl⟩, rfl⟩

theorem core_mem_coreSet (E : Set X) (e : X) : core E e ∈ coreSet E e :=
  ⟨isPGroup_core E e, core_le_localGroup E e, fun _ hl _ hs => conj_mem_core hl hs⟩

theorem Pair.conj_mem_localGroup_conj (hP : Pair X E) (g : X) {e l : X}
    (hl : l ∈ LocalGroup E e) : g * l * g⁻¹ ∈ LocalGroup E (g * e * g⁻¹) := by
  have hl' : l ∈ Subgroup.closure (LocalClass E e) := hl
  clear hl
  induction hl' using Subgroup.closure_induction with
  | mem f hf => exact mem_localGroup ((Pair.conj_mem_localClass_iff hP g).2 hf)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem Pair.map_mem_coreSet (hP : Pair X E) (g : X) {e : X} {S : Subgroup X}
    (hS : S ∈ coreSet E e) :
    S.map (MulAut.conj g).toMonoidHom ∈ coreSet E (g * e * g⁻¹) := by
  refine ⟨hS.1.map _, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact Pair.conj_mem_localGroup_conj hP g (hS.2.1 hs)
  · rintro l hl _ ⟨s, hs, rfl⟩
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ LocalGroup E e := by
      have h := Pair.conj_mem_localGroup_conj hP g⁻¹ hl
      rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at h
    refine ⟨g⁻¹ * l * g⁻¹⁻¹ * s * (g⁻¹ * l * g⁻¹⁻¹)⁻¹, hS.2.2 _ hl' s hs, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem Pair.conj_mem_core_conj (hP : Pair X E) (g : X) {e s : X} (hs : s ∈ core E e) :
    g * s * g⁻¹ ∈ core E (g * e * g⁻¹) := by
  exact le_core (Pair.map_mem_coreSet hP g (core_mem_coreSet E e)) ⟨s, hs, rfl⟩

theorem Pair.conj_mem_core_of_commute (hP : Pair X E) {e c s : X} (hc : c * e = e * c)
    (hs : s ∈ core E e) : c * s * c⁻¹ ∈ core E e := by
  have h := Pair.conj_mem_core_conj hP c hs
  rwa [hc, mul_inv_cancel_right] at h

theorem core_le_centralizer (E : Set X) (e : X) :
    core E e ≤ Subgroup.centralizer ({e} : Set X) := fun _ hs =>
  Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_localGroup_self
    (core_le_localGroup E e hs))

theorem Pair.exists_core_move (hP : Pair X E) {d : X}
    (h3 : HasNormalPSubgroup 3 (LocalQuotient E d)) :
    ∃ g ∈ core E d, ∃ x ∈ LocalClass E d, g * x * g⁻¹ ≠ x := by
  classical
  have := Pair.finite hP
  obtain ⟨Q, hQn, hQ1, hQp⟩ := h3
  set L := LocalGroup E d
  set π := QuotientGroup.mk' (Subgroup.center L)
  set M : Subgroup L := Q.comap π
  have hMn : M.Normal := hQn.comap π
  let f : M →* Q := (π.comp M.subtype).codRestrict Q fun m => m.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    exact ⟨⟨m, hq⟩, rfl⟩
  have hcen : ∀ m : M, f m = 1 → (m : L) ∈ Subgroup.center L := by
    intro m hm
    have h1 : π m = 1 := congrArg Subtype.val hm
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hker : f.ker ≤ Subgroup.center M := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro n
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen m hm) n)
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have : Group.IsNilpotent M := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨T⟩ : Nonempty (Sylow 3 M) := inferInstance
  have hTc : (T : Subgroup M).Characteristic := Sylow.characteristic_of_normal T inferInstance
  have hTn : ((T : Subgroup M).map M.subtype).Normal := inferInstance
  set S : Subgroup X := ((T : Subgroup M).map M.subtype).map L.subtype
  have hS : S ∈ coreSet E d := by
    refine ⟨(T.isPGroup'.map M.subtype).map L.subtype, Subgroup.map_subtype_le _, ?_⟩
    rintro l hl _ ⟨t, ht, rfl⟩
    exact ⟨⟨l, hl⟩ * t * ⟨l, hl⟩⁻¹, hTn.conj_mem t ht ⟨l, hl⟩, rfl⟩
  by_contra! hall
  have hT : (T : Subgroup M).map f = ⊥ := by
    refine (Subgroup.map_eq_bot_iff _).2 fun t ht => ?_
    show f t = 1
    have htS : ((t : L) : X) ∈ S := ⟨t, ⟨t, ht, rfl⟩, rfl⟩
    have hc : ∀ x ∈ LocalClass E d, x * ((t : L) : X) = (t : L) * x := by
      intro x hx
      have h := hall _ (le_core hS htS) x hx
      calc x * ((t : L) : X) = (t : L) * x * ((t : L) : X)⁻¹ * (t : L) := by rw [h]
        _ = (t : L) * x := by group
    have hz : (t : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.2 fun l =>
      Subtype.ext (commute_of_mem_localGroup hc l.2)
    apply Subtype.ext
    show π t = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  have htop := (T.mapSurjective hf).is_maximal' (hQp.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective, hT] at htop
  apply hQ1
  rw [eq_bot_iff]
  intro q hq
  have : (⟨q, hq⟩ : Q) ∈ (⊥ : Subgroup Q) := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

end O3

end CFSG.Fischer.Classification
