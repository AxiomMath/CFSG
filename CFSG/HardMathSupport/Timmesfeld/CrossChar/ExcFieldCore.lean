module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open

section Canonical

variable {C : Type*} [Group C]

theorem isQuasisimple_of_simple_nonabelian {J : Type*} [Group J] [IsSimpleGroup J]
    (hnc : ¬ ∀ a b : J, a * b = b * a) : CFSG.IsQuasisimple J := by
  have hZ : Subgroup.center J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
    · exact h
    · exfalso
      refine hnc fun a b => ?_
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a
  have hperf : Group.IsPerfect J := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
    · exfalso
      refine hnc fun a b => ?_
      have h1 : a * b * a⁻¹ * b⁻¹ ∈ commutator J := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · exact h
  let e : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := Classical.not_forall.1 hnc |>.imp fun _ h => Classical.not_forall.1 h
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem fieldCoreAt_of_canonical_quasisimple [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ}
    {δ : MulAut C} (hδp : orderOf δ = p) {J : Subgroup C} (hJq : CFSG.IsQuasisimple J)
    (hNδ : J.map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer ({δ} : Set (MulAut C)))
    (hnormal : ((J.map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer ({δ} : Set (MulAut C)))).Normal)
    (hcent : Subgroup.centralizer ({δ} : Set (MulAut C)) ⊓
      Subgroup.centralizer (((J.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C))) = Subgroup.zpowers δ)
    (hJp : ¬ Nat.Coprime p (Nat.card J)) : FieldCoreAt p δ := by
  have hfix : ∀ j ∈ J, δ j = j := by
    intro j hj
    have hmem : (MulAut.conj j : MulAut C) ∈ J.map (MulAut.conj : C →* MulAut C) :=
      ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hNδ hmem)
    apply hinj
    rw [← mul_conj_mul_inv δ j]
    rw [← h1]
    group
  refine ⟨J, fun j hj => hfix j hj, fun f hf t ht => ?_, ?_, hJp, ?_⟩
  · have hc : MulAut.conj f ∈ Subgroup.centralizer ({δ} : Set (MulAut C)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (conj_commute_of_mem_fixSub hf).symm
    have hmt : (MulAut.conj t : MulAut C) ∈ J.map (MulAut.conj : C →* MulAut C) :=
      ⟨t, ht, rfl⟩
    have hn : (⟨MulAut.conj t, hNδ hmt⟩ : Subgroup.centralizer ({δ} : Set (MulAut C))) ∈
        (J.map (MulAut.conj : C →* MulAut C)).subgroupOf
          (Subgroup.centralizer ({δ} : Set (MulAut C))) := hmt
    have h2 := hnormal.conj_mem _ hn ⟨MulAut.conj f, hc⟩
    obtain ⟨s, hs, hsf⟩ := Subgroup.mem_subgroupOf.1 h2
    have : s = f * t * f⁻¹ := by
      apply hinj
      rw [map_mul, map_mul, map_inv]
      exact hsf
    rwa [← this]
  · exact hJq
  · intro g hgp hgδ hgJ
    have hg1 : g ∈ Subgroup.centralizer ({δ} : Set (MulAut C)) ⊓
        Subgroup.centralizer (((J.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
          Set (MulAut C))) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgδ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      have h1 := mul_conj_mul_inv g j
      rw [hgJ j hj] at h1
      change MulAut.conj j * g = g * MulAut.conj j
      calc MulAut.conj j * g = (g * MulAut.conj j * g⁻¹) * g := by rw [h1]
        _ = g * MulAut.conj j := by group
    rw [hcent] at hg1
    have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hg1
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

theorem fieldCoreAt_of_canonical_data [Finite C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {p : ℕ}
    {δ : MulAut C} (hδp : orderOf δ = p) {J : Subgroup C}
    (hsimple : IsSimpleGroup J) (hnc : ¬ ∀ a b : J, a * b = b * a)
    (hNδ : J.map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer ({δ} : Set (MulAut C)))
    (hnormal : ((J.map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer ({δ} : Set (MulAut C)))).Normal)
    (hcent : Subgroup.centralizer ({δ} : Set (MulAut C)) ⊓
      Subgroup.centralizer (((J.map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C))) = Subgroup.zpowers δ)
    (hJp : ¬ Nat.Coprime p (Nat.card J)) : FieldCoreAt p δ :=
  have : IsSimpleGroup J := hsimple
  fieldCoreAt_of_canonical_quasisimple hinj hδp (isQuasisimple_of_simple_nonabelian hnc) hNδ
    hnormal hcent hJp

theorem fieldCoreAt_of_fixSub_eq {p : ℕ} {δ : MulAut C} (hδp : orderOf δ = p) {J : Subgroup C}
    (hJq : CFSG.IsQuasisimple J) (hJ : ∀ g : C, g ∈ J ↔ δ g = g)
    (hfix : ∀ β : MulAut C, (∀ u ∈ J, β u = u) → β ∈ Subgroup.zpowers δ)
    (hJp : ¬ Nat.Coprime p (Nat.card J)) : FieldCoreAt p δ := by
  refine ⟨J, fun j hj => (hJ j).1 hj, fun f hf t ht => ?_, hJq, hJp, ?_⟩
  · refine (hJ _).2 ?_
    have hf' := mem_fixSub.1 hf
    have ht' := (hJ t).1 ht
    change δ (f * t * f⁻¹) = f * t * f⁻¹
    rw [map_mul, map_mul, map_inv]
    change δ f * δ t * (δ f)⁻¹ = f * t * f⁻¹
    rw [show δ f = f from hf', ht']
  · intro g hgp _ hgJ
    have hg := hfix g hgJ
    have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hg
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

end Canonical

section Transport

variable {K : Type*} [Group K]

theorem fixSub_conj (δ x : MulAut K) :
    fixSub (δ * x * δ⁻¹) = (fixSub x).map (δ : K →* K) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨δ⁻¹ y, ?_, by simp⟩
    have h := mem_fixSub.1 hy
    change δ (x (δ⁻¹ y)) = y at h
    rw [mem_fixSub]
    have h2 : δ⁻¹ (δ (x (δ⁻¹ y))) = δ⁻¹ y := congrArg (fun z => δ⁻¹ z) h
    rw [MulAut.inv_apply_self] at h2
    exact h2
  · rintro ⟨z, hz, rfl⟩
    rw [mem_fixSub]
    change δ (x (δ⁻¹ (δ z))) = δ z
    rw [MulAut.inv_apply_self, mem_fixSub.1 hz]

theorem FieldCoreAt.conj {p : ℕ} {x : MulAut K} (h : FieldCoreAt p x) (δ : MulAut K) :
    FieldCoreAt p (δ * x * δ⁻¹) := by
  obtain ⟨T, hTF, hTn, hTq, hTp, hfaith⟩ := h
  refine ⟨T.map (δ : K →* K), ?_, ?_, ?_, ?_, ?_⟩
  · rw [fixSub_conj]
    exact Subgroup.map_mono hTF
  · rintro f hf _ ⟨t, ht, rfl⟩
    rw [fixSub_conj] at hf
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
    exact ⟨f' * t * f'⁻¹, hTn f' hf' t ht, by simp⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (T.equivMapOfInjective (δ : K →* K) δ.injective) hTq
  · rwa [Subgroup.card_map_of_injective δ.injective]
  · intro g hgp hgx hgT
    have hg' : δ⁻¹ * g * δ = 1 := by
      refine hfaith (δ⁻¹ * g * δ) ?_ ?_ ?_
      · have h1 := MulEquiv.orderOf_eq (MulAut.conj δ⁻¹) g
        rw [MulAut.conj_apply, inv_inv] at h1
        rwa [h1]
      · calc δ⁻¹ * g * δ * x = δ⁻¹ * (g * (δ * x * δ⁻¹)) * δ := by group
          _ = δ⁻¹ * ((δ * x * δ⁻¹) * g) * δ := by rw [hgx]
          _ = x * (δ⁻¹ * g * δ) := by group
      · intro t ht
        have h1 := hgT (δ t) ⟨t, ht, rfl⟩
        change δ⁻¹ (g (δ t)) = t
        rw [h1, MulAut.inv_apply_self]
    calc g = δ * (δ⁻¹ * g * δ) * δ⁻¹ := by group
      _ = 1 := by rw [hg']; group

theorem fixSub_eq_of_zpowers_eq {x y : MulAut K} (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    fixSub x = fixSub y := by
  have key : ∀ {a b : MulAut K}, b ∈ Subgroup.zpowers a → fixSub a ≤ fixSub b := by
    intro a b hb t ht
    have hle : Subgroup.zpowers a ≤ fixingSubgroup (MulAut K) ((fixSub a : Subgroup K) : Set K) :=
      Subgroup.zpowers_le.2 ((mem_fixingSubgroup_iff _).2 fun y hy => mem_fixSub.1 hy)
    exact (mem_fixingSubgroup_iff _).1 (hle hb) t ht
  exact le_antisymm (key (h ▸ Subgroup.mem_zpowers y)) (key (h ▸ Subgroup.mem_zpowers x))

theorem FieldCoreAt.of_zpowers_eq {p : ℕ} {x y : MulAut K}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) (hx : FieldCoreAt p x) : FieldCoreAt p y := by
  obtain ⟨T, hTF, hTn, hTq, hTp, hfaith⟩ := hx
  have hF := fixSub_eq_of_zpowers_eq h
  have hcomm : ∀ g : MulAut K, g * y = y * g → g * x = x * g := by
    intro g hg
    have hxy : x ∈ Subgroup.zpowers y := h ▸ Subgroup.mem_zpowers x
    have : g ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup (MulAut K)) :
        Set (MulAut K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨n, rfl⟩
      exact (Commute.zpow_left (show Commute y g from hg.symm) n).eq
    exact (Subgroup.mem_centralizer_iff.1 this x hxy).symm
  exact ⟨T, hF ▸ hTF, fun f hf t ht => hTn f (hF ▸ hf) t ht, hTq, hTp,
    fun g hgp hgy hgT => hfaith g hgp (hcomm g hgy) hgT⟩

theorem fieldCoreAt_of_conj {p : ℕ} {δ x : MulAut K} (h : FieldCoreAt p δ) (δ' : MulAut K)
    (hδ : δ' * x * δ'⁻¹ = δ) : FieldCoreAt p x := by
  have h1 := h.conj δ'⁻¹
  rw [← hδ] at h1
  have h2 : δ'⁻¹ * (δ' * x * δ'⁻¹) * δ'⁻¹⁻¹ = x := by group
  rwa [h2] at h1

end Transport

section Cyclic

theorem mem_zpowers_of_pow_eq_one_of_isCyclic' {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : 0 < p) {η ε : G} (hη : orderOf η = p) (hε : ε ^ p = 1) :
    ε ∈ Subgroup.zpowers η := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := (Finset.univ : Finset G).filter fun x => x ^ p = 1 with hS
  have hSle : S.card ≤ p := IsCyclic.card_pow_eq_one_le hp
  have hsub : (Subgroup.zpowers η : Set G).toFinset ⊆ S := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hη, pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Subgroup.zpowers η : Set G).toFinset.card = p := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← hη,
      ← Nat.card_zpowers]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hSle)
  have hεS : ε ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hε⟩
  rw [← heq, Set.mem_toFinset] at hεS
  exact hεS

theorem mem_zpowers_of_mem_zpowers_of_pow_eq_one {G : Type*} [Group G] [Finite G] {φ x y : G}
    (hx : x ∈ Subgroup.zpowers φ) (hy : y ∈ Subgroup.zpowers φ) {p : ℕ} (hp : 0 < p)
    (hyp : orderOf y = p) (hxp : x ^ p = 1) : x ∈ Subgroup.zpowers y := by
  have hy' : orderOf (⟨y, hy⟩ : Subgroup.zpowers φ) = p := by
    rw [Subgroup.orderOf_mk]
    exact hyp
  have hx' : (⟨x, hx⟩ : Subgroup.zpowers φ) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have := mem_zpowers_of_pow_eq_one_of_isCyclic' hp hy' hx'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

end Cyclic

end CFSG.HardMathSupport.Timmesfeld.CrossChar
