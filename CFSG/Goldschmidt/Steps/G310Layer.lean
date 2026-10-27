module

public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.Goldschmidt.Steps.G310Odd
public import CFSG.Goldschmidt.Steps.G3b34

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

section Join

variable {X : Type*} [Group X]

theorem iSup_le_centralizer {ι : Type*} {s : Set ι} {f : ι → Subgroup X} {L₀ : Subgroup X}
    (h : ∀ i ∈ s, f i ≤ Subgroup.centralizer (L₀ : Set X)) :
    (⨆ i ∈ s, f i) ≤ Subgroup.centralizer (L₀ : Set X) :=
  iSup₂_le h

theorem exists_mul_inv_centralizes [DecidableEq (Subgroup X)] (s : Finset (Subgroup X))
    (hcomm : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → L ≤ Subgroup.centralizer (L' : Set X))
    (B : Subgroup X → Subgroup X) (hB : ∀ L ∈ s, B L ≤ L) (x : X)
    (hx : ∀ L ∈ s, ∃ ℓ ∈ B L, ∀ y ∈ L, x⁻¹ * y * x = ℓ⁻¹ * y * ℓ) :
    ∃ w ∈ ⨆ L ∈ s, B L, ∀ L ∈ s, ∀ y ∈ L, x * w⁻¹ * y = y * (x * w⁻¹) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, fun L hL => absurd hL (Finset.notMem_empty L)⟩
  | @insert L₀ s hL₀ ih =>
    obtain ⟨w', hw', hw'c⟩ := ih (fun L hL L' hL' => hcomm L (Finset.mem_insert_of_mem hL) L'
      (Finset.mem_insert_of_mem hL')) (fun L hL => hB L (Finset.mem_insert_of_mem hL))
      (fun L hL => hx L (Finset.mem_insert_of_mem hL))
    obtain ⟨ℓ₀, hℓ₀, hact⟩ := hx L₀ (Finset.mem_insert_self _ _)
    have hℓ₀L : ℓ₀ ∈ L₀ := hB L₀ (Finset.mem_insert_self _ _) hℓ₀
    have hw'L₀ : w' ∈ Subgroup.centralizer (L₀ : Set X) := by
      refine iSup_le_centralizer (s := (s : Set (Subgroup X))) (fun L hL => ?_) hw'
      refine (hB L (Finset.mem_insert_of_mem hL)).trans (hcomm L (Finset.mem_insert_of_mem hL)
        L₀ (Finset.mem_insert_self _ _) ?_)
      rintro rfl
      exact hL₀ hL
    have hcw : ∀ y ∈ L₀, y * w' = w' * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hw'L₀ y hy
    refine ⟨ℓ₀ * w', ?_, fun L hL y hy => ?_⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact (le_iSup₂ (f := fun L (_ : L ∈ insert L₀ s) => B L) L₀
          (Finset.mem_insert_self _ _)) hℓ₀
      · refine (iSup₂_le fun L hL => ?_ : (⨆ L ∈ s, B L) ≤ ⨆ L ∈ insert L₀ s, B L) hw'
        exact le_iSup₂ (f := fun L (_ : L ∈ insert L₀ s) => B L) L
          (Finset.mem_insert_of_mem hL)
    · rcases Finset.mem_insert.mp hL with rfl | hLs
      ·
        have h1 : x⁻¹ * y * x = ℓ₀⁻¹ * y * ℓ₀ := hact y hy
        have hyℓ : ℓ₀⁻¹ * y * ℓ₀ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hℓ₀L) hy) hℓ₀L
        have h2 : w' * (ℓ₀⁻¹ * y * ℓ₀) = (ℓ₀⁻¹ * y * ℓ₀) * w' := (hcw _ hyℓ).symm
        have key : (ℓ₀ * w') * (x⁻¹ * y * x) * (ℓ₀ * w')⁻¹ = y := by
          rw [h1]
          calc (ℓ₀ * w') * (ℓ₀⁻¹ * y * ℓ₀) * (ℓ₀ * w')⁻¹
              = ℓ₀ * (w' * (ℓ₀⁻¹ * y * ℓ₀)) * w'⁻¹ * ℓ₀⁻¹ := by group
            _ = ℓ₀ * ((ℓ₀⁻¹ * y * ℓ₀) * w') * w'⁻¹ * ℓ₀⁻¹ := by rw [h2]
            _ = y := by group
        calc x * (ℓ₀ * w')⁻¹ * y
            = x * (ℓ₀ * w')⁻¹ * ((ℓ₀ * w') * (x⁻¹ * y * x) * (ℓ₀ * w')⁻¹) := by rw [key]
          _ = y * (x * (ℓ₀ * w')⁻¹) := by group
      ·
        have hℓy : ℓ₀ * y = y * ℓ₀ := by
          have hne : L₀ ≠ L := by
            rintro rfl
            exact hL₀ hLs
          exact Subgroup.mem_centralizer_iff.mp (hcomm L₀ (Finset.mem_insert_self _ _) L
            (Finset.mem_insert_of_mem hLs) hne hℓ₀L) y hy |>.symm
        have hℓinv : ℓ₀⁻¹ * y = y * ℓ₀⁻¹ := by
          calc ℓ₀⁻¹ * y = ℓ₀⁻¹ * (y * ℓ₀) * ℓ₀⁻¹ := by group
            _ = ℓ₀⁻¹ * (ℓ₀ * y) * ℓ₀⁻¹ := by rw [hℓy]
            _ = y * ℓ₀⁻¹ := by group
        have h1 := hw'c L hLs y hy
        calc x * (ℓ₀ * w')⁻¹ * y = (x * w'⁻¹) * (ℓ₀⁻¹ * y) := by group
          _ = (x * w'⁻¹) * (y * ℓ₀⁻¹) := by rw [hℓinv]
          _ = (x * w'⁻¹ * y) * ℓ₀⁻¹ := by group
          _ = (y * (x * w'⁻¹)) * ℓ₀⁻¹ := by rw [h1]
          _ = y * (x * (ℓ₀ * w')⁻¹) := by group

theorem eq_one_of_centralizes [DecidableEq (Subgroup X)] (s : Finset (Subgroup X))
    (hcomm : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → L ≤ Subgroup.centralizer (L' : Set X))
    (hZ : ∀ L ∈ s, ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1) :
    ∀ x ∈ ⨆ L ∈ s, L, (∀ L ∈ s, ∀ y ∈ L, x * y = y * x) → x = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    simpa using hx
  | @insert L₀ s hL₀ ih =>
    intro x hx hxc
    set V := ⨆ L ∈ s, L with hV
    have hVc : V ≤ Subgroup.centralizer (L₀ : Set X) := by
      refine iSup₂_le fun L hL => hcomm L (Finset.mem_insert_of_mem hL) L₀
        (Finset.mem_insert_self _ _) ?_
      rintro rfl
      exact hL₀ hL
    have hsup : (⨆ L ∈ insert L₀ s, L) = L₀ ⊔ V := by
      rw [Finset.iSup_insert]
    rw [hsup] at hx
    have hL₀N : L₀ ≤ Subgroup.normalizer (V : Set X) :=
      (Subgroup.le_centralizer_iff.mp hVc).trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨l, hl, v, hv, rfl⟩ := exists_mul_of_mem_sup hL₀N hx
    have hl1 : l = 1 := by
      refine hZ L₀ (Finset.mem_insert_self _ _) l hl fun y hy => ?_
      have h1 := hxc L₀ (Finset.mem_insert_self _ _) y hy
      have h2 : v * y = y * v := (Subgroup.mem_centralizer_iff.mp (hVc hv) y hy).symm
      calc l * y = l * v * y * v⁻¹ := by rw [mul_assoc l v y, h2]; group
        _ = y * (l * v) * v⁻¹ := by rw [h1]
        _ = y * l := by group
    subst hl1
    rw [one_mul] at hxc ⊢
    exact ih (fun L hL L' hL' => hcomm L (Finset.mem_insert_of_mem hL) L'
      (Finset.mem_insert_of_mem hL')) (fun L hL => hZ L (Finset.mem_insert_of_mem hL)) v hv
      (fun L hL => hxc L (Finset.mem_insert_of_mem hL))

end Join

section SylowTransport

variable {X : Type*} [Group X]

theorem fusionIsSylowIn_of_subgroupOf {p : ℕ} {S L : Subgroup X} (hSL : S ≤ L)
    (h : fusionIsSylowIn p (S.subgroupOf L) ⊤) : fusionIsSylowIn p S L := by
  obtain ⟨-, hp, hmax⟩ := h
  refine ⟨hSL, ?_, fun Q hQL hQ hSQ => ?_⟩
  · exact hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSL)
  · have h1 := hmax (Q.subgroupOf L) le_top hQ.comap_subtype (fun x hx => hSQ hx)
    have h2 := congrArg (Subgroup.map L.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hQL, Subgroup.map_subgroupOf_eq_of_le hSL] at h2

end SylowTransport

section Comp

variable {M : Type} [Group M] [Finite M]

theorem le_centralizer_of_ne {A L L' : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A))
    (hL' : IsComponentOf L' (normalClosureIn ⊤ A)) (hne : L ≠ L') :
    L ≤ Subgroup.centralizer (L' : Set M) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (N8b M L L' (isComponentOf_top_of_normal (normalClosureIn_top_normal A) hL)
      (isComponentOf_top_of_normal (normalClosureIn_top_normal A) hL') hne)

theorem mem_normalizer_of_mem_centralizer
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) {c : M}
    (hc : c ∈ Subgroup.centralizer (A : Set M)) : c ∈ Subgroup.normalizer (L : Set M) := by
  apply mem_normalizer_of_map_eq'
  by_contra hne
  have hL' := isComponentOf_conj (normalClosureIn_top_normal A) hL c
  obtain ⟨x, hx, y, hy, hxy⟩ := (compFacts hO hS hL).noncentral
  have hxc : x ∈ L.map (MulAut.conj c).toMonoidHom := by
    refine ⟨x, hx.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Subgroup.mem_centralizer_iff.mp hc x hx.1]
    group
  exact hxy (Subgroup.mem_centralizer_iff.mp (le_centralizer_of_ne hL' hL hne hxc) y hy).symm

theorem exists_act_of_mem (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) {k : M}
    (hk : k ∈ normalClosureIn ⊤ A) : ∃ ℓ ∈ L, ∀ y ∈ L, k⁻¹ * y * k = ℓ⁻¹ * y * ℓ := by
  obtain ⟨Z₂, -, hZc, hgen⟩ := exists_gen hO hS
  refine G3a.mem_actsBy.mp (hgen (G3a.actsBy L L le_rfl)
    (fun z hz => G3a.mem_actsBy.mpr ⟨1, L.one_mem, fun y hy => ?_⟩) (fun L' hL' => ?_) hk)
  · have := hZc z hz y (hL.1 hy)
    calc z⁻¹ * y * z = z⁻¹ * (z * y) := by rw [mul_assoc, ← this]
      _ = 1⁻¹ * y * 1 := by group
  · by_cases hLL : L' = L
    · subst hLL
      exact fun ℓ hℓ => G3a.mem_actsBy.mpr ⟨ℓ, hℓ, fun _ _ => rfl⟩
    · intro ℓ hℓ
      refine G3a.mem_actsBy.mpr ⟨1, L.one_mem, fun y hy => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp (le_centralizer_of_ne hL' hL hLL hℓ) y hy
      calc ℓ⁻¹ * y * ℓ = ℓ⁻¹ * (ℓ * y) := by rw [mul_assoc, this]
        _ = 1⁻¹ * y * 1 := by group

theorem mem_normalizer_of_mem (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) {k : M}
    (hk : k ∈ normalClosureIn ⊤ A) : k ∈ Subgroup.normalizer (L : Set M) := by
  obtain ⟨ℓ, hℓ, hact⟩ := exists_act_of_mem hO hS hL hk
  obtain ⟨ℓ', hℓ', hact'⟩ := exists_act_of_mem hO hS hL ((normalClosureIn ⊤ A).inv_mem hk)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := hact' y hy
    rw [inv_inv] at h1
    rw [h1]
    exact L.mul_mem (L.mul_mem (L.inv_mem hℓ') hy) hℓ'
  · intro hy
    have h1 := hact _ hy
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e] at h1
    rw [h1]
    exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hy) hℓ

end Comp

section TypeII

variable {M : Type} [Group M] [Finite M]

@[expose] def typeIISet (A : Subgroup M) : Set (Subgroup M) :=
  {L | IsComponentOf L (normalClosureIn ⊤ A) ∧ IsGoldTypeII L}

@[expose] def layerII (A : Subgroup M) : Subgroup M := sSup (typeIISet A)

theorem center_eq_bot_of_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) : Subgroup.center L = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (compFacts hO hS hL.1).center
  have hodd := hL.2.1
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

theorem eq_one_of_central_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) {z : M} (hz : z ∈ L)
    (hc : ∀ y ∈ L, z * y = y * z) : z = 1 := by
  have h1 : (⟨z, hz⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [center_eq_bot_of_typeII hO hS hL, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

theorem isSylow_inf_of_typeII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : L ∈ typeIISet A) :
    fusionIsSylowIn 2 (A ⊓ L) L := by
  have hF := compFacts hO hS hL.1
  have hZ := center_eq_bot_of_typeII hO hS hL
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.2.2
  have : IsSimpleGroup L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup_congr.mp
      inferInstance
  have hA' : IsSStarIn ⊤ ((A ⊓ L).subgroupOf L) := by
    have := SStarTransport.isSStarIn_subgroupOf hF.sstar le_rfl
    rwa [Subgroup.subgroupOf_self] at this
  have hne : (A ⊓ L).subgroupOf L ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.noncentral
    intro hb
    have h1 : (⟨x, hx.2⟩ : L) ∈ (A ⊓ L).subgroupOf L := hx
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : x = 1 := congrArg Subtype.val h1
    rw [h2, one_mul, mul_one] at hxy
    exact hxy rfl
  exact fusionIsSylowIn_of_subgroupOf inf_le_right (G34 L hL.2 _ hA' hne).1

theorem typeIISet_finite (A : Subgroup M) : (typeIISet A).Finite := Set.toFinite _

theorem map_conj_mem_typeIISet {A L : Subgroup M} (hL : L ∈ typeIISet A) (g : M) :
    L.map (MulAut.conj g).toMonoidHom ∈ typeIISet A :=
  ⟨isComponentOf_conj (normalClosureIn_top_normal A) hL.1 g,
    SStarTransport.isGoldTypeII_of_mulEquiv
      (L.equivMapOfInjective _ (MulAut.conj g).injective) hL.2⟩

theorem layerII_normal (A : Subgroup M) : (layerII A).Normal := by
  constructor
  intro x hx g
  have hle : (layerII A).map (MulAut.conj g).toMonoidHom ≤ layerII A := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_conj_mem_typeIISet hL g)
  exact hle ⟨x, hx, rfl⟩

theorem layerII_eq_iSup (A : Subgroup M) [DecidableEq (Subgroup M)] :
    layerII A = ⨆ L ∈ (typeIISet_finite A).toFinset, L := by
  rw [layerII, sSup_eq_iSup]
  simp only [Set.Finite.mem_toFinset]

omit [Finite M] in
theorem le_layerII {A L : Subgroup M} (hL : L ∈ typeIISet A) : L ≤ layerII A := le_sSup hL

omit [Finite M] in
theorem layerII_le (A : Subgroup M) : layerII A ≤ normalClosureIn ⊤ A :=
  sSup_le fun _ hL => hL.1.1

theorem le_centralizer_of_typeII_ne {A L L' : Subgroup M} (hL : L ∈ typeIISet A)
    (hL' : L' ∈ typeIISet A) (hne : L ≠ L') : L ≤ Subgroup.centralizer (L' : Set M) :=
  le_centralizer_of_ne hL.1 hL'.1 hne

omit [Finite M] in
theorem mem_centralizer_layerII {A : Subgroup M} {c : M}
    (hc : ∀ L ∈ typeIISet A, ∀ y ∈ L, c * y = y * c) :
    c ∈ Subgroup.centralizer (layerII A : Set M) := by
  have hle : layerII A ≤ Subgroup.centralizer ({c} : Set M) := by
    refine sSup_le fun L hL y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc L hL y hy).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem eq_one_of_mem_layerII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {x : M} (hx : x ∈ layerII A)
    (hc : ∀ L ∈ typeIISet A, ∀ y ∈ L, x * y = y * x) : x = 1 := by
  classical
  rw [layerII_eq_iSup] at hx
  refine eq_one_of_centralizes (typeIISet_finite A).toFinset ?_ ?_ x hx ?_
  · intro L hL L' hL' hne
    rw [Set.Finite.mem_toFinset] at hL hL'
    exact le_centralizer_of_typeII_ne hL hL' hne
  · intro L hL z hz hzc
    rw [Set.Finite.mem_toFinset] at hL
    exact eq_one_of_central_typeII hO hS hL hz hzc
  · intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    exact hc L hL

theorem exists_mul_inv_mem_centralizer_layerII {A : Subgroup M} (B : Subgroup M → Subgroup M)
    (hB : ∀ L ∈ typeIISet A, B L ≤ L) (x : M)
    (hx : ∀ L ∈ typeIISet A, ∃ ℓ ∈ B L, ∀ y ∈ L, x⁻¹ * y * x = ℓ⁻¹ * y * ℓ) :
    ∃ w ∈ ⨆ L ∈ typeIISet A, B L, x * w⁻¹ ∈ Subgroup.centralizer (layerII A : Set M) := by
  classical
  obtain ⟨w, hw, hwc⟩ := exists_mul_inv_centralizes (typeIISet_finite A).toFinset
    (fun L hL L' hL' hne => by
      rw [Set.Finite.mem_toFinset] at hL hL'
      exact le_centralizer_of_typeII_ne hL hL' hne)
    B (fun L hL => hB L ((Set.Finite.mem_toFinset _).mp hL)) x
    (fun L hL => hx L ((Set.Finite.mem_toFinset _).mp hL))
  refine ⟨w, ?_, mem_centralizer_layerII fun L hL y hy =>
    hwc L ((Set.Finite.mem_toFinset _).mpr hL) y hy⟩
  simpa only [Set.Finite.mem_toFinset] using hw

omit [Finite M] in
theorem iSup_inf_le (A : Subgroup M) :
    (⨆ L ∈ typeIISet A, A ⊓ L) ≤ A ⊓ layerII A :=
  iSup₂_le fun _ hL => inf_le_inf_left _ (le_layerII hL)

theorem exists_act_of_mem_A
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) {a : M}
    (ha : a ∈ A) : ∃ x ∈ A ⊓ L, ∀ y ∈ L, a⁻¹ * y * a = x⁻¹ * y * x := by
  have hF := compFacts hO hS hL
  have hAc := hS.2.1
  have hN : A ⊓ L ≤ Subgroup.normalizer
      ((A ⊓ Subgroup.centralizer (L : Set M) : Subgroup M) : Set M) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have hcomm : ∀ b ∈ A, g * b * g⁻¹ = b := by
      intro b hb
      rw [mul_comm_of_isMulCommutative hAc hg.1 hb, mul_inv_cancel_right]
    constructor
    · intro hb
      rw [hcomm b hb.1]
      exact hb
    · intro hb
      have hbA : b ∈ A := by
        have h1 := hb.1
        have h2 : b = g⁻¹ * (g * b * g⁻¹) * g := by group
        rw [h2]
        exact A.mul_mem (A.mul_mem (A.inv_mem hg.1) h1) hg.1
      rw [hcomm b hbA] at hb
      exact hb
  have hmem : a ∈ A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set M) := by
    rw [← hF.split]
    exact ha
  obtain ⟨x, hx, c, hc, rfl⟩ := exists_mul_of_mem_sup hN hmem
  refine ⟨x, hx, fun y hy => ?_⟩
  have hxy : x⁻¹ * y * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hx.2) hy) hx.2
  have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hxy
  calc (x * c)⁻¹ * y * (x * c) = c⁻¹ * ((x⁻¹ * y * x) * c) := by group
    _ = c⁻¹ * (c * (x⁻¹ * y * x)) := by rw [h1]
    _ = x⁻¹ * y * x := by group

theorem split_layerII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    A = A ⊓ layerII A ⊔ A ⊓ Subgroup.centralizer (layerII A : Set M) := by
  refine le_antisymm (fun a ha => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨w, hw, hwc⟩ := exists_mul_inv_mem_centralizer_layerII (A := A) (fun L => A ⊓ L)
    (fun L _ => inf_le_right) a (fun L hL => exists_act_of_mem_A hO hS hL.1 ha)
  have hw' := iSup_inf_le A hw
  have e : a = (a * w⁻¹) * w := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨A.mul_mem ha (A.inv_mem hw'.1), hwc⟩)
    (Subgroup.mem_sup_left hw')

omit [Finite M] in
theorem isPGroup_two_of_isSStarIn {H A : Subgroup M} (hS : IsSStarIn H A) : IsPGroup 2 A := by
  obtain ⟨-, -, T, hT, hAT, -⟩ := hS
  exact hT.2.1.to_le hAT

theorem isSylow_layerII
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    fusionIsSylowIn 2 (A ⊓ layerII A) (layerII A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := layerII A with hLb
  have hA₀2 : IsPGroup 2 ↥(A ⊓ Lb) := (isPGroup_two_of_isSStarIn hS).to_le inf_le_left
  obtain ⟨S', hS'⟩ := (hA₀2.comap_subtype (K := Lb)).exists_le_sylow
  set S := (S' : Subgroup Lb).map Lb.subtype with hSdef
  have hSsyl : fusionIsSylowIn 2 S Lb := fusionIsSylowIn_map S'
  have hA₀S : A ⊓ Lb ≤ S := fun x hx => ⟨⟨x, hx.2⟩, hS' hx, rfl⟩
  have hSA : S ≤ A ⊓ Lb := by
    intro s hs
    have hsL : s ∈ Lb := hSsyl.1 hs
    have hsK : s ∈ normalClosureIn ⊤ A := layerII_le A hsL
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hSsyl.2.1) ⟨s, hs⟩
    have hsk : s ^ (2 ^ k) = 1 := by
      have h1 := pow_orderOf_eq_one (⟨s, hs⟩ : S)
      rw [hk] at h1
      simpa using congrArg Subtype.val h1
    have hact : ∀ L ∈ typeIISet A, ∃ ℓ ∈ A ⊓ L, ∀ y ∈ L, s⁻¹ * y * s = ℓ⁻¹ * y * ℓ := by
      intro L hL
      obtain ⟨ℓ, hℓ, hact⟩ := exists_act_of_mem hO hS hL.1 hsK
      refine ⟨ℓ, ?_, hact⟩
      have hsyl := isSylow_inf_of_typeII hO hS hL
      have hSL : S ⊓ L = A ⊓ L := hsyl.2.2 (S ⊓ L) inf_le_right (hSsyl.2.1.to_le inf_le_left)
        (le_inf ((inf_le_inf_left _ (le_layerII hL)).trans hA₀S) inf_le_right)
      have hℓ2 : ℓ ^ (2 ^ k) = 1 := by
        refine eq_one_of_central_typeII hO hS hL (L.pow_mem hℓ _) fun y hy => ?_
        have h1 := G3a.act_pow hℓ hact (2 ^ k) y hy
        rw [hsk, inv_one, one_mul, mul_one] at h1
        calc ℓ ^ 2 ^ k * y = ℓ ^ 2 ^ k * ((ℓ ^ 2 ^ k)⁻¹ * y * ℓ ^ 2 ^ k) := by rw [← h1]
          _ = y * ℓ ^ 2 ^ k := by group
      have hsN := mem_normalizer_of_mem hO hS hL.1 hsK
      have hconj : ∀ y ∈ L, ℓ * y * ℓ⁻¹ = s * y * s⁻¹ := by
        intro y hy
        have hz : s * y * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
        have h1 := hact _ hz
        have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
        rw [e] at h1
        have h2 : ℓ * y * ℓ⁻¹ = ℓ * (ℓ⁻¹ * (s * y * s⁻¹) * ℓ) * ℓ⁻¹ :=
          congrArg (fun t => ℓ * t * ℓ⁻¹) h1
        rw [h2]
        group
      have hℓN : ℓ ∈ Subgroup.normalizer ((A ⊓ L : Subgroup M) : Set M) := by
        rw [Subgroup.mem_normalizer_iff, ← hSL]
        intro y
        by_cases hy : y ∈ L
        · rw [hconj y hy]
          constructor
          · intro h
            exact ⟨S.mul_mem (S.mul_mem hs h.1) (S.inv_mem hs),
              (Subgroup.mem_normalizer_iff.mp hsN y).mp h.2⟩
          · intro h
            refine ⟨?_, hy⟩
            have e : y = s⁻¹ * (s * y * s⁻¹) * s := by group
            rw [e]
            exact S.mul_mem (S.mul_mem (S.inv_mem hs) h.1) hs
        · constructor
          · intro h
            exact absurd h.2 hy
          · intro h
            exfalso
            apply hy
            have e : y = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * ℓ := by group
            rw [e]
            exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) h.2) hℓ
      have hp : IsPGroup 2 (Subgroup.zpowers ℓ) := by
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hℓ2)
        exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
      have hsup := hp.to_sup_of_normal_right' hsyl.2.1 (Subgroup.zpowers_le.mpr hℓN)
      have heq := hsyl.2.2 _ (sup_le (Subgroup.zpowers_le.mpr hℓ) inf_le_right) hsup le_sup_right
      rw [← heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers ℓ)
    obtain ⟨w, hw, hwc⟩ := exists_mul_inv_mem_centralizer_layerII (A := A) (fun L => A ⊓ L)
      (fun L _ => inf_le_right) s hact
    have hw' := iSup_inf_le A hw
    have h1 : s * w⁻¹ = 1 := by
      refine eq_one_of_mem_layerII hO hS (Lb.mul_mem hsL (Lb.inv_mem hw'.2)) fun L hL y hy => ?_
      exact (Subgroup.mem_centralizer_iff.mp hwc y (le_layerII hL hy)).symm
    rw [mul_inv_eq_one] at h1
    rw [h1]
    exact hw'
  rw [le_antisymm hA₀S hSA]
  exact hSsyl

end TypeII

end CFSG.Goldschmidt.G310
