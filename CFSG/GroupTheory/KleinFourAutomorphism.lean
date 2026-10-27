module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm

public noncomputable section

namespace CFSG

open scoped Classical IsKleinFour

universe u

variable (E : Type u) [Group E]

@[expose] def nonidentityAutomorphismAction :
    MulAut E →* Equiv.Perm {x : E // x ≠ 1} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (by
    intro x
    constructor
    · intro h hx
      exact h (hx ▸ map_one a)
    · intro hx hax
      apply hx
      apply a.injective
      simpa using hax)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[simp] theorem nonidentityAutomorphismAction_coe (a : MulAut E) (x : E) (hx : x ≠ 1) :
    (nonidentityAutomorphismAction E a ⟨x, hx⟩ : E) = a x := rfl

theorem nonidentityAutomorphismAction_injective :
    Function.Injective (nonidentityAutomorphismAction E) := by
  intro a b hab
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val
      (congrArg (fun p : Equiv.Perm {x : E // x ≠ 1} => p ⟨x, hx⟩) hab)

variable [IsKleinFour E]

@[expose] def kleinFourAutomorphismOfPermutation
    (p : Equiv.Perm {x : E // x ≠ 1}) : MulAut E :=
  IsKleinFour.mulEquiv (Equiv.Perm.ofSubtype p)
    (Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp))

@[simp] theorem kleinFourAutomorphismOfPermutation_coe
    (p : Equiv.Perm {x : E // x ≠ 1}) (x : E) (hx : x ≠ 1) :
    kleinFourAutomorphismOfPermutation E p x = (p ⟨x, hx⟩ : E) :=
  Equiv.Perm.ofSubtype_apply_of_mem p hx

@[simp] theorem nonidentityAutomorphismAction_ofPermutation
    (p : Equiv.Perm {x : E // x ≠ 1}) :
    nonidentityAutomorphismAction E (kleinFourAutomorphismOfPermutation E p) = p := by
  ext x
  exact kleinFourAutomorphismOfPermutation_coe E p x.val x.property

theorem nonidentityAutomorphismAction_surjective :
    Function.Surjective (nonidentityAutomorphismAction E) := by
  intro p
  exact ⟨kleinFourAutomorphismOfPermutation E p,
    nonidentityAutomorphismAction_ofPermutation E p⟩

@[expose] def kleinFourAutomorphismEquiv :
    MulAut E ≃* Equiv.Perm {x : E // x ≠ 1} :=
  MulEquiv.ofBijective (nonidentityAutomorphismAction E)
    ⟨nonidentityAutomorphismAction_injective E, nonidentityAutomorphismAction_surjective E⟩

@[simp] theorem kleinFourAutomorphismEquiv_coe (a : MulAut E) (x : E) (hx : x ≠ 1) :
    (kleinFourAutomorphismEquiv E a ⟨x, hx⟩ : E) = a x := rfl

@[simp] theorem kleinFourAutomorphismEquiv_symm_coe
    (p : Equiv.Perm {x : E // x ≠ 1}) (x : E) (hx : x ≠ 1) :
    (kleinFourAutomorphismEquiv E).symm p x = (p ⟨x, hx⟩ : E) := by
  have h := congrArg (fun q : Equiv.Perm {x : E // x ≠ 1} => (q ⟨x, hx⟩ : E))
    ((kleinFourAutomorphismEquiv E).apply_symm_apply p)
  exact h

theorem kleinFour_nonidentity_card : Nat.card {x : E // x ≠ 1} = 3 := by
  let : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : E => x = 1)]
  simp

theorem kleinFour_automorphism_card : Nat.card (MulAut E) = 6 := by
  let : Fintype {x : E // x ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_congr (kleinFourAutomorphismEquiv E).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm,
    ← Nat.card_eq_fintype_card, kleinFour_nonidentity_card]
  decide

theorem kleinFour_automorphism_transitive (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let p : Equiv.Perm {x : E // x ≠ 1} := Equiv.swap ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨kleinFourAutomorphismOfPermutation E p, ?_⟩
  rw [kleinFourAutomorphismOfPermutation_coe E p x hx]
  exact congrArg (fun z : {x : E // x ≠ 1} => z.val)
    (Equiv.swap_apply_left ⟨x, hx⟩ ⟨y, hy⟩)

@[expose] def kleinFourAutomorphismEquivSymmetricThree :
    MulAut E ≃* Equiv.Perm (Fin 3) :=
  letI : Fintype {x : E // x ≠ 1} := Fintype.ofFinite _
  (kleinFourAutomorphismEquiv E).trans
    (Fintype.equivFinOfCardEq
      (by simpa only [Nat.card_eq_fintype_card] using kleinFour_nonidentity_card E)).permCongrHom

theorem kleinFour_automorphism_subgroup_card (H : Subgroup (MulAut E))
    (a : MulAut E) (ha : a ∈ H) (horder : orderOf a = 2) :
    Nat.card H = 2 ∨ Nat.card H = 6 := by
  have hdvd : Nat.card H ∣ 6 := by
    rw [← kleinFour_automorphism_card E]
    exact H.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card H := by
    have h := orderOf_dvd_natCard (⟨a, ha⟩ : H)
    rw [← Subgroup.orderOf_coe, horder] at h
    exact h
  have hbound : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  have hcases : ∀ d : ℕ, d ≤ 6 → d ∣ 6 → 2 ∣ d → d = 2 ∨ d = 6 := by decide
  exact hcases (Nat.card H) hbound hdvd htwo

theorem kleinFour_automorphism_subgroup_eq_top_of_card_six (H : Subgroup (MulAut E))
    (hcard : Nat.card H = 6) : H = ⊤ := by
  apply H.eq_top_of_card_eq
  rw [hcard, kleinFour_automorphism_card E]

theorem kleinFour_automorphism_subgroup_alternatives (H : Subgroup (MulAut E))
    (a : MulAut E) (ha : a ∈ H) (horder : orderOf a = 2) :
    Nat.card H = 2 ∨ Nonempty (H ≃* Equiv.Perm (Fin 3)) := by
  rcases kleinFour_automorphism_subgroup_card E H a ha horder with htwo | hsix
  · exact Or.inl htwo
  · apply Or.inr
    have htop := kleinFour_automorphism_subgroup_eq_top_of_card_six E H hsix
    exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans
      (kleinFourAutomorphismEquivSymmetricThree E)⟩

theorem kleinFour_automorphism_subgroup_transitive (H : Subgroup (MulAut E))
    (hcard : Nat.card H = 6) (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : H, a.val x = y := by
  obtain ⟨a, ha⟩ := kleinFour_automorphism_transitive E x y hx hy
  have htop := kleinFour_automorphism_subgroup_eq_top_of_card_six E H hcard
  exact ⟨⟨a, htop ▸ Subgroup.mem_top a⟩, ha⟩

theorem kleinFour_order_three_cycle (a : MulAut E) (horder : orderOf a = 3)
    (x : E) (hx : x ≠ 1) :
    a x ≠ x ∧ a (a x) ≠ x ∧ a (a x) ≠ a x ∧
      ∀ y : E, y ≠ 1 → y = x ∨ y = a x ∨ y = a (a x) := by
  let X := {x : E // x ≠ 1}
  let : Fintype X := Fintype.ofFinite _
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [X, Nat.card_eq_fintype_card] using kleinFour_nonidentity_card E)
  let f : MulAut E ≃* Equiv.Perm (Fin 3) := (kleinFourAutomorphismEquiv E).trans e.permCongrHom
  let p := f a
  have hporder : orderOf p = 3 := (f.orderOf_eq a).trans horder
  have hpow : p ^ 3 = 1 := by
    have h := pow_orderOf_eq_one p
    rw [hporder] at h
    exact h
  have hpne : p ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hporder
    exact (by decide : (1 : ℕ) ≠ 3) hporder
  have hfinite : ∀ p : Equiv.Perm (Fin 3), p ^ 3 = 1 → p ≠ 1 →
      ∀ z : Fin 3, p z ≠ z ∧ p (p z) ≠ z ∧ p (p z) ≠ p z ∧
        ∀ w : Fin 3, w = z ∨ w = p z ∨ w = p (p z) := by decide
  let ax : X := kleinFourAutomorphismEquiv E a ⟨x, hx⟩
  let aax : X := kleinFourAutomorphismEquiv E a ax
  have hpx : p (e ⟨x, hx⟩) = e ax := by
    change e (kleinFourAutomorphismEquiv E a (e.symm (e ⟨x, hx⟩))) = e ax
    rw [e.symm_apply_apply]
  have hppx : p (p (e ⟨x, hx⟩)) = e aax := by
    rw [hpx]
    change e (kleinFourAutomorphismEquiv E a (e.symm (e ax))) = e aax
    rw [e.symm_apply_apply]
  obtain ⟨hax, haax, haaxax, hcover⟩ := hfinite p hpow hpne (e ⟨x, hx⟩)
  rw [hpx] at hax
  rw [hppx] at haax
  rw [hppx, hpx] at haaxax
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact hax (congrArg e (Subtype.ext heq))
  · intro heq
    exact haax (congrArg e (Subtype.ext heq))
  · intro heq
    exact haaxax (congrArg e (Subtype.ext heq))
  · intro y hy
    rcases hcover (e ⟨y, hy⟩) with h | h | h
    · exact Or.inl (congrArg Subtype.val (e.injective h))
    · rw [hpx] at h
      exact Or.inr (Or.inl (congrArg Subtype.val (e.injective h)))
    · rw [hppx] at h
      exact Or.inr (Or.inr (congrArg Subtype.val (e.injective h)))


section NormalizerCapture

public theorem normalizer_le_of_kleinFour_capture
    {G : Type u} [Group G] {V : Subgroup G} [IsKleinFour V]
    {x y : V} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    {M : Subgroup G}
    (hCx : Subgroup.centralizer ({(x : G)} : Set G) ≤ M)
    {k : G} (hkM : k ∈ M)
    (hkN : k ∈ Subgroup.normalizer (V : Set G))
    (hkxy : k * (x : G) * k⁻¹ = (y : G))
    (hkyx : k * (y : G) * k⁻¹ = (x : G)) :
    Subgroup.normalizer (V : Set G) ≤ M := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let MN : Subgroup N := M.subgroupOf N
  let φ : N →* MulAut V := V.normalizerMonoidHom
  let kN : N := ⟨k, hkN⟩
  let a : MulAut V := φ kN

  have hkyx_inv : k⁻¹ * (y : G) * k = (x : G) := by
    calc
      k⁻¹ * (y : G) * k = k⁻¹ * (k * (x : G) * k⁻¹) * k := by rw [hkxy]
      _ = (x : G) := by group
  have hCy : Subgroup.centralizer ({(y : G)} : Set G) ≤ M := by
    intro c hc
    have hc_comm : c * (y : G) = (y : G) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hc' : k⁻¹ * c * k ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (k⁻¹ * c * k) * (x : G) =
            (k⁻¹ * c * k) * (k⁻¹ * (y : G) * k) := by rw [hkyx_inv]
        _ = k⁻¹ * (c * (y : G)) * k := by group
        _ = k⁻¹ * ((y : G) * c) * k := by rw [hc_comm]
        _ = (k⁻¹ * (y : G) * k) * (k⁻¹ * c * k) := by group
        _ = (x : G) * (k⁻¹ * c * k) := by rw [hkyx_inv]
    have hcM : k⁻¹ * c * k ∈ M := hCx hc'
    rw [show c = k * (k⁻¹ * c * k) * k⁻¹ by group]
    exact M.mul_mem (M.mul_mem hkM hcM) (M.inv_mem hkM)

  have hax : a x = y := by
    apply Subtype.ext
    change ((V.normalizerMonoidHom kN x : V) : G) = (y : G)
    rw [V.normalizerMonoidHom_apply_apply_coe]
    exact hkxy
  have hay : a y = x := by
    apply Subtype.ext
    change ((V.normalizerMonoidHom kN y : V) : G) = (x : G)
    rw [V.normalizerMonoidHom_apply_apply_coe]
    exact hkyx

  have ha2 : a ^ 2 = 1 := by
    ext z
    by_cases hz1 : z = 1
    · simp [hz1]
    · by_cases hzx : z = x
      · subst z
        simp [pow_two, MulAut.mul_apply, hax, hay]
      · by_cases hzy : z = y
        · subst z
          simp [pow_two, MulAut.mul_apply, hay, hax]
        · have hzxy : z = x * y :=
            IsKleinFour.eq_mul_of_ne_all hx hy hxy hz1 hzx hzy
          have haz : a z = z := by
            calc
              a z = a (x * y) := by rw [hzxy]
              _ = a x * a y := map_mul a x y
              _ = y * x := by rw [hax, hay]
              _ = x * y :=
                mul_comm_of_exponent_two (IsKleinFour.exponent_two (G := V)) y x
              _ = z := hzxy.symm
          simp [pow_two, MulAut.mul_apply, haz]

  have hane : a ≠ 1 := by
    intro ha1
    exact hxy (by simpa [ha1] using hax)
  have haord : orderOf a = 2 :=
    orderOf_eq_prime (p := 2) ha2 hane

  have hCEx : Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer ({(x : G)} : Set G) := by
    apply Subgroup.centralizer_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact x.2
  have hker : φ.ker ≤ MN := by
    intro n hn
    have hnC : (n : G) ∈ Subgroup.centralizer (V : Set G) := by
      have hnSub : n ∈ (Subgroup.centralizer (V : Set G)).subgroupOf N := by
        rw [← V.normalizerMonoidHom_ker]
        exact hn
      exact Subgroup.mem_subgroupOf.mp hnSub
    exact Subgroup.mem_subgroupOf.mpr (hCx (hCEx hnC))
  have hkMN : kN ∈ MN := Subgroup.mem_subgroupOf.mpr hkM

  let H : Subgroup (MulAut V) := φ.range
  have haH : a ∈ H := ⟨kN, rfl⟩
  have hcardH := kleinFour_automorphism_subgroup_card V H a haH haord

  have hMtop : MN = ⊤ := by
    let I : Subgroup (MulAut V) := MN.map φ
    have haI : a ∈ I := ⟨kN, hkMN, rfl⟩
    have hIleH : I ≤ H := Subgroup.map_le_range φ MN
    rcases hcardH with hH2 | hH6
    · have hIge2 : 2 ≤ Nat.card I := by
        have hpos : 0 < Nat.card I := Nat.card_pos
        have hne1 : Nat.card I ≠ 1 := by
          intro hI1
          have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hI1
          have hmem : a ∈ I := haI
          rw [hIbot] at hmem
          exact hane (Subgroup.mem_bot.mp hmem)
        omega
      have hIle2 : Nat.card I ≤ 2 := by
        simpa [hH2] using Subgroup.card_le_of_le hIleH
      have hI2 : Nat.card I = 2 := by omega
      have hIeqH : I = H :=
        Subgroup.eq_of_le_of_card_ge hIleH (by omega)
      have hmap : MN.map φ = φ.range := by
        simpa [I, H] using hIeqH
      have h := Subgroup.comap_map_eq_self (f := φ) hker
      rw [hmap] at h
      rw [MonoidHom.comap_range_self] at h
      exact h.symm
    ·
      have hHtop : H = ⊤ :=
        kleinFour_automorphism_subgroup_eq_top_of_card_six V H hH6
      let z : V := x * y
      have hznot : z ∉ ({x, y, (1 : V)} : Set V) := by
        simpa [z] using
          (mul_notMem_of_exponent_two (IsKleinFour.exponent_two (G := V)) hx hy hxy)
      have hz1 : z ≠ 1 := fun h => hznot (by simp [h])
      have hzx : z ≠ x := fun h => hznot (by simp [h])
      have hzy : z ≠ y := fun h => hznot (by simp [h])

      let pX : Equiv.Perm {u : V // u ≠ 1} :=
        Equiv.swap ⟨y, hy⟩ ⟨z, hz1⟩
      let τx : MulAut V := (kleinFourAutomorphismEquiv V).symm pX
      have hτx_x : τx x = x := by
        change ((kleinFourAutomorphismEquiv V).symm pX) x = x
        rw [kleinFourAutomorphismEquiv_symm_coe V pX x hx]
        have h1 : (⟨x, hx⟩ : {u : V // u ≠ 1}) ≠ ⟨y, hy⟩ := by
          intro h
          exact hxy (Subtype.ext_iff.mp h)
        have h2 : (⟨x, hx⟩ : {u : V // u ≠ 1}) ≠ ⟨z, hz1⟩ := by
          intro h
          exact hzx (Subtype.ext_iff.mp h).symm
        have hp : pX ⟨x, hx⟩ = ⟨x, hx⟩ := by
          rw [show pX = Equiv.swap ⟨y, hy⟩ ⟨z, hz1⟩ from rfl]
          exact Equiv.swap_apply_of_ne_of_ne h1 h2
        exact congrArg Subtype.val hp
      have hτx_y : τx y = z := by
        change ((kleinFourAutomorphismEquiv V).symm pX) y = z
        rw [kleinFourAutomorphismEquiv_symm_coe V pX y hy]
        have hp : pX ⟨y, hy⟩ = ⟨z, hz1⟩ := by
          rw [show pX = Equiv.swap ⟨y, hy⟩ ⟨z, hz1⟩ from rfl]
          exact Equiv.swap_apply_left _ _
        rw [hp]

      let pY : Equiv.Perm {u : V // u ≠ 1} :=
        Equiv.swap ⟨x, hx⟩ ⟨z, hz1⟩
      let τy : MulAut V := (kleinFourAutomorphismEquiv V).symm pY
      have hτy_y : τy y = y := by
        change ((kleinFourAutomorphismEquiv V).symm pY) y = y
        rw [kleinFourAutomorphismEquiv_symm_coe V pY y hy]
        have h1 : (⟨y, hy⟩ : {u : V // u ≠ 1}) ≠ ⟨x, hx⟩ := by
          intro h
          exact hxy (Subtype.ext_iff.mp h).symm
        have h2 : (⟨y, hy⟩ : {u : V // u ≠ 1}) ≠ ⟨z, hz1⟩ := by
          intro h
          exact hzy (Subtype.ext_iff.mp h).symm
        have hp : pY ⟨y, hy⟩ = ⟨y, hy⟩ := by
          rw [show pY = Equiv.swap ⟨x, hx⟩ ⟨z, hz1⟩ from rfl]
          exact Equiv.swap_apply_of_ne_of_ne h1 h2
        exact congrArg Subtype.val hp
      have hτy_x : τy x = z := by
        change ((kleinFourAutomorphismEquiv V).symm pY) x = z
        rw [kleinFourAutomorphismEquiv_symm_coe V pY x hx]
        have hp : pY ⟨x, hx⟩ = ⟨z, hz1⟩ := by
          rw [show pY = Equiv.swap ⟨x, hx⟩ ⟨z, hz1⟩ from rfl]
          exact Equiv.swap_apply_left _ _
        exact congrArg Subtype.val hp

      have hτxy_ne : τx ≠ τy := by
        intro h
        have hx_eq : τx x = τy x := congrArg (fun f => f x) h
        rw [hτx_x, hτy_x] at hx_eq
        exact hzx hx_eq.symm
      have hτx_ne : τx ≠ 1 := by
        intro h
        have hy_eq : τx y = y := by rw [h]; rfl
        rw [hτx_y] at hy_eq
        exact hzy hy_eq
      have hτy_ne : τy ≠ 1 := by
        intro h
        have hx_eq : τy x = x := by rw [h]; rfl
        rw [hτy_x] at hx_eq
        exact hzx hx_eq

      have hτxH : τx ∈ H := by
        rw [hHtop]
        exact Subgroup.mem_top τx
      obtain ⟨nX, hnX⟩ := MonoidHom.mem_range.mp hτxH
      have hnX_conj : (nX : G) * (x : G) * (nX : G)⁻¹ = (x : G) := by
        have h := V.normalizerMonoidHom_apply_apply_coe nX x
        rw [hnX, hτx_x] at h
        exact h.symm
      have hnXcent : (nX : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc
          (nX : G) * (x : G) = ((nX : G) * (x : G) * (nX : G)⁻¹) * (nX : G) := by group
          _ = (x : G) * (nX : G) := by rw [hnX_conj]
      have hnXMN : nX ∈ MN := Subgroup.mem_subgroupOf.mpr (hCx hnXcent)

      have hτyH : τy ∈ H := by
        rw [hHtop]
        exact Subgroup.mem_top τy
      obtain ⟨nY, hnY⟩ := MonoidHom.mem_range.mp hτyH
      have hnY_conj : (nY : G) * (y : G) * (nY : G)⁻¹ = (y : G) := by
        have h := V.normalizerMonoidHom_apply_apply_coe nY y
        rw [hnY, hτy_y] at h
        exact h.symm
      have hnYcent : (nY : G) ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc
          (nY : G) * (y : G) = ((nY : G) * (y : G) * (nY : G)⁻¹) * (nY : G) := by group
          _ = (y : G) * (nY : G) := by rw [hnY_conj]
      have hnYMN : nY ∈ MN := Subgroup.mem_subgroupOf.mpr (hCy hnYcent)

      have hτxI : τx ∈ I := ⟨nX, hnXMN, hnX⟩
      have hτyI : τy ∈ I := ⟨nY, hnYMN, hnY⟩
      have hIcard_ne_two : Nat.card I ≠ 2 := by
        intro hI2
        obtain ⟨b, hb, huniq⟩ := (Nat.card_eq_two_iff' (1 : I)).mp hI2
        let τxI : I := ⟨τx, hτxI⟩
        let τyI : I := ⟨τy, hτyI⟩
        have hτxI_ne : τxI ≠ 1 := by
          intro h
          exact hτx_ne (congrArg Subtype.val h)
        have hτyI_ne : τyI ≠ 1 := by
          intro h
          exact hτy_ne (congrArg Subtype.val h)
        have heq : τxI = τyI :=
          (huniq τxI hτxI_ne).trans (huniq τyI hτyI_ne).symm
        exact hτxy_ne (congrArg Subtype.val heq)
      have hI6 : Nat.card I = 6 := by
        rcases kleinFour_automorphism_subgroup_card V I a haI haord with h2 | h6
        · exact absurd h2 hIcard_ne_two
        · exact h6
      have hIeqH : I = H :=
        Subgroup.eq_of_le_of_card_ge hIleH (by omega)
      have hmap : MN.map φ = φ.range := by
        simpa [I, H] using hIeqH
      have h := Subgroup.comap_map_eq_self (f := φ) hker
      rw [hmap] at h
      rw [MonoidHom.comap_range_self] at h
      exact h.symm
  intro g hg
  have hmem : (⟨g, hg⟩ : N) ∈ MN := by
    rw [hMtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end NormalizerCapture

end CFSG
