module

public import CFSG.Sporadic.SuzOddCore.SmallAut
public import Certificates.Certificate129060
public import Certificates.Certificate129061
public import Certificates.Certificate129062

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.PSL3Four CFSG.Certificates.Native

theorem suzGen_facts
    {i : ℕ} (hi : i < 4) :
    ∃ g ∈ suzM, ∃ h ∈ suzM, suzM ≤ Subgroup.closure
      {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹} :=
  Certificates.certificate129061 i hi

theorem suzGen_involution
    {τ : Equiv.Perm (Fin 1782)} (hτ : τ ∈ suzT) (h2 : orderOf τ = 2) :
    ∃ g ∈ suzM, ∃ h ∈ suzM, suzM ≤ Subgroup.closure {τ, g * τ * g⁻¹, h * τ * h⁻¹} := by
  obtain ⟨i, ⟨hi, c, hc, hcτ⟩, -⟩ := suzT_involution_class hτ h2
  obtain ⟨g, hg, h, hh, hgen⟩ := suzGen_facts hi
  have hcM : ∀ m ∈ suzM, c * m * c⁻¹ ∈ suzM := fun m hm => suzT_conj_mem_suzM hc hm
  have hcM' : ∀ m ∈ suzM, c⁻¹ * m * c ∈ suzM := fun m hm => by
    simpa using suzT_conj_mem_suzM (suzT.inv_mem hc) hm
  refine ⟨c * g * c⁻¹, hcM g hg, c * h * c⁻¹, hcM h hh, fun x hx => ?_⟩
  have hx' : c⁻¹ * x * c ∈ Subgroup.closure
      {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹} := hgen (hcM' x hx)
  let f : Equiv.Perm (Fin 1782) →* Equiv.Perm (Fin 1782) := (MulAut.conj c).toMonoidHom
  have hmap : (Subgroup.closure {suzInv i, g * suzInv i * g⁻¹, h * suzInv i * h⁻¹}).map f ≤
      Subgroup.closure {τ, c * g * c⁻¹ * τ * (c * g * c⁻¹)⁻¹, c * h * c⁻¹ * τ * (c * h * c⁻¹)⁻¹} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    have hf : ∀ z, f z = c * z * c⁻¹ := fun z => by simp [f, MulAut.conj_apply]
    rw [hf]
    rcases hy with rfl | rfl | rfl
    · rw [hcτ]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have e : c * (g * suzInv i * g⁻¹) * c⁻¹ =
          (c * g * c⁻¹) * (c * suzInv i * c⁻¹) * (c * g * c⁻¹)⁻¹ := by group
      rw [e, hcτ]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · have e : c * (h * suzInv i * h⁻¹) * c⁻¹ =
          (c * h * c⁻¹) * (c * suzInv i * c⁻¹) * (c * h * c⁻¹)⁻¹ := by group
      rw [e, hcτ]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton _)))
  have := hmap ⟨_, hx', rfl⟩
  convert this using 1
  show x = c * (c⁻¹ * x * c) * c⁻¹
  group

theorem suzAut_gen :
    ∀ ψ : MulAut ↥suzM, ψ * ψ = 1 → ψ ≠ 1 → ∃ cs : List ↥suzM, cs.length = 3 ∧
      (MulAut.conj : ↥suzM →* MulAut ↥suzM).range ≤ Subgroup.closure
        {x : MulAut ↥suzM | ∃ c ∈ cs, x = MulAut.conj c * ψ * (MulAut.conj c)⁻¹} := by
  intro ψ hψ2 hψ1
  obtain ⟨τ', rfl⟩ := suzConjT_bijective.2 ψ
  have hτ2 : τ' * τ' = 1 :=
    suzConjT_injective (by rw [map_mul, hψ2, map_one])
  have hτ1 : τ' ≠ 1 := fun h => hψ1 (by rw [h, map_one])
  have hτorder : orderOf (τ' : Equiv.Perm (Fin 1782)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact congrArg Subtype.val hτ2) (fun h => hτ1 (Subtype.ext h))
  obtain ⟨g, hg, h, hh, hgen⟩ := suzGen_involution τ'.2 hτorder
  let σ : ↥suzM → ↥suzT := fun c => ⟨c, suzM_le_suzT c.2⟩
  let cs : List ↥suzM := [1, ⟨g, hg⟩, ⟨h, hh⟩]
  refine ⟨cs, rfl, ?_⟩
  have hΘ : ∀ c : ↥suzM, suzConjT (σ c) = MulAut.conj c := by
    intro c
    ext m
    simp [suzConjT_apply, σ, MulAut.conj_apply]
  let Y' : Subgroup ↥suzT := Subgroup.closure {x | ∃ c ∈ cs, x = σ c * τ' * (σ c)⁻¹}
  have hX : Subgroup.closure {(τ' : Equiv.Perm (Fin 1782)), g * τ' * g⁻¹, h * τ' * h⁻¹} ≤
      Y'.map suzT.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · refine ⟨τ', Subgroup.subset_closure ⟨1, by simp [cs], ?_⟩, rfl⟩
      have h1 : σ 1 = 1 := rfl
      rw [h1]
      simp
    · refine ⟨σ ⟨g, hg⟩ * τ' * (σ ⟨g, hg⟩)⁻¹, Subgroup.subset_closure ⟨⟨g, hg⟩, by simp [cs], rfl⟩,
        rfl⟩
    · refine ⟨σ ⟨h, hh⟩ * τ' * (σ ⟨h, hh⟩)⁻¹, Subgroup.subset_closure ⟨⟨h, hh⟩, by simp [cs], rfl⟩,
        rfl⟩
  have hY' : suzM.subgroupOf suzT ≤ Y' := by
    intro m hm
    have hmM : (m : Equiv.Perm (Fin 1782)) ∈ suzM := hm
    obtain ⟨y, hy, hym⟩ := hX (hgen hmM)
    have : y = m := Subtype.ext hym
    rwa [← this]
  calc (MulAut.conj : ↥suzM →* MulAut ↥suzM).range
      = (suzM.subgroupOf suzT).map suzConjT := suzConjT_map_suzM.symm
    _ ≤ Y'.map suzConjT := Subgroup.map_mono hY'
    _ ≤ _ := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨c, hc, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨c, hc, ?_⟩
      rw [map_mul, map_mul, map_inv, hΘ]

theorem suzAG_facts_perm :
    ∃ (A : Subgroup (Equiv.Perm (Fin 1782))) (g : Equiv.Perm (Fin 1782)), A ≤ suzM ∧ g ∈ suzM ∧
      Nat.card A = 243 ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      (∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧ g ^ 11 = 1 ∧ ∃ a ∈ A, g * a * g⁻¹ ≠ a :=
  Certificates.certificate129060

theorem suzAG_facts :
    ∃ (A : Subgroup ↥suzM) (g : ↥suzM), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ a ∈ A, a ^ 3 = 1) ∧ Nat.card A = 243 ∧ (∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧ g ^ 11 = 1 ∧
      ∃ a ∈ A, g * a * g⁻¹ ≠ a := by
  obtain ⟨A₀, g₀, hAM, hgM, hcard, hcomm, hpow, hnorm, hg11, a₀, ha₀, hne⟩ := suzAG_facts_perm
  refine ⟨A₀.subgroupOf suzM, ⟨g₀, hgM⟩, fun a ha b hb => ?_, fun a ha => ?_, ?_,
    fun a ha => ?_, Subtype.ext ?_, ⟨⟨a₀, hAM ha₀⟩, ha₀, fun h => hne (congrArg Subtype.val h)⟩⟩
  · exact Subtype.ext (hcomm _ ha _ hb)
  · exact Subtype.ext (by simpa using hpow _ ha)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact hcard
  · exact hnorm _ ha
  · simpa using hg11

theorem card_le_of_colouring {T : Array Tab} {col : ℕ → ℕ} (hcol : ∀ i < T.size, col i < 63)
    (hsep : ∀ i < T.size, ∀ j < T.size, i < j → col j = col i →
      ¬ (comp 1782 T[i]! T[j]! = comp 1782 T[j]! T[i]!))
    {S : Subgroup (Equiv.Perm (Fin 1782))}
    (hmem : ∀ x ∈ S, x * x = 1 → x ≠ 1 → ∃ i < T.size, TabRep T[i]! x)
    {B : Subgroup (Equiv.Perm (Fin 1782))} (hBS : B ≤ S)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 6 := by
  classical
  let pos : B → ℕ := fun x => if h : (x : Equiv.Perm (Fin 1782)) = 1 then 0
    else (hmem x (hBS x.2) (hsq x x.2) h).choose
  have hpos : ∀ x : B, (x : Equiv.Perm (Fin 1782)) ≠ 1 → pos x < T.size ∧
      TabRep T[pos x]! (x : Equiv.Perm (Fin 1782)) := by
    intro x hx
    have hspec := (hmem x (hBS x.2) (hsq x x.2) hx).choose_spec
    have hp : pos x = (hmem x (hBS x.2) (hsq x x.2) hx).choose := dite_eq_right hx
    rw [hp]
    exact hspec
  let f : B → Option (Fin 63) := fun x =>
    if h : (x : Equiv.Perm (Fin 1782)) = 1 then none
    else some ⟨col (pos x), hcol _ (hpos x h).1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : Equiv.Perm (Fin 1782)) = 1
    · by_cases hy : (y : Equiv.Perm (Fin 1782)) = 1
      · exact Subtype.ext (hx.trans hy.symm)
      · have h1 : f x = none := dite_eq_left hx
        have h2 : f y = some ⟨col (pos y), hcol _ (hpos y hy).1⟩ := dite_eq_right hy
        rw [h1, h2] at hxy
        exact absurd hxy (by simp)
    · by_cases hy : (y : Equiv.Perm (Fin 1782)) = 1
      · have h1 : f y = none := dite_eq_left hy
        have h2 : f x = some ⟨col (pos x), hcol _ (hpos x hx).1⟩ := dite_eq_right hx
        rw [h1, h2] at hxy
        exact absurd hxy (by simp)
      · have h1 : f x = some ⟨col (pos x), hcol _ (hpos x hx).1⟩ := dite_eq_right hx
        have h2 : f y = some ⟨col (pos y), hcol _ (hpos y hy).1⟩ := dite_eq_right hy
        rw [h1, h2] at hxy
        have hxy : col (pos x) = col (pos y) := by
          have := Option.some.inj hxy
          exact congrArg Fin.val this
        by_contra hne
        have hxne : (x : Equiv.Perm (Fin 1782)) ≠ y := fun h => hne (Subtype.ext h)
        obtain ⟨hxi, hxr⟩ := hpos x hx
        obtain ⟨hyi, hyr⟩ := hpos y hy
        have hij : pos x ≠ pos y := by
          intro h
          apply hxne
          have : TabRep T[pos x]! (y : Equiv.Perm (Fin 1782)) := by rw [h]; exact hyr
          exact hxr.perm_eq this
        have hcommxy : comp 1782 T[pos x]! T[pos y]! = comp 1782 T[pos y]! T[pos x]! := by
          have h1 := hxr.comp hyr
          have h2 := hyr.comp hxr
          have : (x : Equiv.Perm (Fin 1782)) * y = y * x := hcomm x x.2 y y.2
          rw [this] at h1
          exact h1.tab_eq h2
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hsep _ hxi _ hyi hlt hxy.symm hcommxy
        · exact hsep _ hyi _ hxi hgt hxy hcommxy.symm
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card (Option (Fin 63)) = 64 := by simp
  rw [h2] at h1
  exact h1

theorem suzRank_S
    {B : Subgroup (Equiv.Perm (Fin 1782))} (hBS : B ≤ invSylow)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 6 := by
  have h := Certificates.certificate129062
  unfold suzRankCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsz, h⟩ := h
  rw [allBelow_eq_true] at h
  have hmem : ∀ x ∈ invSylow, x * x = 1 → x ≠ 1 →
      ∃ i < (suzInvTabs ()).size, TabRep (suzInvTabs ())[i]! x := by
    intro x hx hx2 hx1
    obtain ⟨t, ht, hrep⟩ := sylow_enumerates.complete x hx
    have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
    have hinv : isInvTab t = true := (isInvTab_iff hrep).2 hord
    have htmem : t ∈ (suzInvTabs ()).toList := by
      rw [suzInvTabs, Array.mem_toList_iff, Array.mem_filter]
      exact ⟨Array.mem_toList_iff.1 ht, hinv⟩
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem htmem
    exact ⟨i, hi, hrep⟩
  refine card_le_of_colouring (T := suzInvTabs ()) (col := suzCol) (fun i hi => ?_)
    (fun i hi j hj hij hcol => ?_) hmem hBS hcomm hsq
  · have := h i (hsz ▸ hi)
    rw [Bool.and_eq_true] at this
    simpa using this.1
  · have := h i (hsz ▸ hi)
    rw [Bool.and_eq_true, allBelow_eq_true] at this
    have h2 := this.2 j (hsz ▸ hj)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h2
    rcases h2 with (h2 | h2) | h2
    · omega
    · exact absurd hcol h2
    · exact h2

theorem suzExists_conj_le_sylow
    {B : Subgroup (Equiv.Perm (Fin 1782))} (hBT : B ≤ suzT)
    (hsq : ∀ x ∈ B, x * x = 1) : ∃ c ∈ suzT, ∀ b ∈ B, c * b * c⁻¹ ∈ invSylow := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 (B.subgroupOf suzT) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa [sq] using hsq _ (Subgroup.mem_subgroupOf.1 x.2)
  obtain ⟨Q, hQle⟩ := hB2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq suzT suzSylowTwo Q
  refine ⟨(x : Equiv.Perm (Fin 1782))⁻¹, suzT.inv_mem x.2, fun b hb => ?_⟩
  have hbQ : (⟨b, hBT hb⟩ : suzT) ∈ (Q : Subgroup suzT) :=
    hQle (Subgroup.mem_subgroupOf.2 hb)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbQ
  obtain ⟨s, hs, hst⟩ := hbQ
  have hsS : (s : Equiv.Perm (Fin 1782)) ∈ invSylow := by
    have : s ∈ invSylow.subgroupOf suzT := by rwa [suzSylowTwo_coe] at hs
    exact Subgroup.mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨b, hBT hb⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  have : (x : Equiv.Perm (Fin 1782))⁻¹ * b * ((x : Equiv.Perm (Fin 1782))⁻¹)⁻¹ = s := by
    rw [← e']
    group
  rw [this]
  exact hsS

theorem suzAut_rank :
    ∀ B : Subgroup (MulAut ↥suzM), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ 6 := by
  intro B hcomm hsq
  let eΘ : ↥suzT ≃* MulAut ↥suzM := MulEquiv.ofBijective suzConjT suzConjT_bijective
  let σ : MulAut ↥suzM →* Equiv.Perm (Fin 1782) :=
    suzT.subtype.comp eΘ.symm.toMonoidHom
  have hσinj : Function.Injective σ := suzT.subtype_injective.comp eΘ.symm.injective
  let B2 : Subgroup (Equiv.Perm (Fin 1782)) := B.map σ
  have hB2card : Nat.card B2 = Nat.card B := Subgroup.card_map_of_injective hσinj
  have hB2T : B2 ≤ suzT := by
    rintro _ ⟨b, -, rfl⟩
    exact (eΘ.symm b).2
  have hB2comm : ∀ x ∈ B2, ∀ y ∈ B2, x * y = y * x := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    rw [← map_mul, ← map_mul, hcomm b hb b' hb']
  have hB2sq : ∀ x ∈ B2, x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, hsq b hb, map_one]
  obtain ⟨c, hc, hcS⟩ := suzExists_conj_le_sylow hB2T hB2sq
  let B3 : Subgroup (Equiv.Perm (Fin 1782)) := B2.map (MulAut.conj c).toMonoidHom
  have hB3card : Nat.card B3 = Nat.card B2 :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hB3S : B3 ≤ invSylow := by
    rintro _ ⟨x, hx, rfl⟩
    have := hcS x hx
    simpa [MulAut.conj_apply] using this
  have h := suzRank_S hB3S (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hB2comm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hB2sq x hx, map_one])
  rw [hB3card, hB2card] at h
  exact h

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
