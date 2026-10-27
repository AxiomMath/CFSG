module

public import CFSG.GH74.GLS.Stage1.Main.BrRankE16
public import CFSG.GH74.GLS.Stage1.Main.BrPairModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74.GLS CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped Pointwise

section KFour

theorem kfour_apply
    {K : Type} [Group K] [Finite K] {q : ℕ} (hq : Odd q)
    (hP : IVK.IsPGL2 K (fun r => r = q)) {x y c : K} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x * y = y * x) (hne : x ≠ y) (hcx : c * x = x * c) (hcy : c * y = y * c) :
    c ∈ Subgroup.closure ({x, y} : Set K) := by
  obtain ⟨F, iF, fF, hFq, ⟨θ⟩⟩ := hP
  obtain ⟨V, hVle, hVe, hVcard⟩ :=
    AlternatingFourGroup.exists_elementary_four_of_commute hx hy hxy hne
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    have hn' : Nat.card F = ringChar F ^ (n : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hn
    refine ⟨ringChar F, n, hp, ?_, n.pos, hn'⟩
    apply hp.odd_of_ne_two
    intro h2
    rw [h2] at hn'
    have hev : Even (Nat.card F) := by
      rw [hn']
      exact Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩
    rw [hFq] at hev
    exact (Nat.not_even_iff_odd.2 hq) hev
  have : IsElementaryAbelian 2 ↥V := hVe
  have hVm : IsElementaryAbelian 2 ↥(V.map θ.toMonoidHom) := IsElementaryAbelian.map θ.toMonoidHom
  have : Finite ↥(V.map θ.toMonoidHom) :=
    Finite.of_equiv ↥V (V.equivMapOfInjective θ.toMonoidHom θ.injective).toEquiv
  have hcardm : Nat.card ↥(V.map θ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective θ.injective, hVcard]
  have hKF : IsKleinFour ↥(V.map θ.toMonoidHom) := by
    refine ⟨hcardm, ?_⟩
    have hnt : Nontrivial ↥(V.map θ.toMonoidHom) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hcardm]; norm_num)
    exact IsElementaryAbelian.exponent_eq_prime
  have hcent := CFSG.GorensteinWalter.pgl2_kleinFour_centralizer_eq_self F hF
    (V.map θ.toMonoidHom) hKF
  have hcl : Subgroup.closure ({x, y} : Set K) ≤ Subgroup.centralizer ({c} : Set K) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcy.symm
  have hmem : θ c ∈ Subgroup.centralizer ((V.map θ.toMonoidHom : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : v * c = c * v := Subgroup.mem_centralizer_singleton_iff.1 (hcl (hVle hv))
    show θ v * θ c = θ c * θ v
    rw [← map_mul, ← map_mul, h1]
  rw [hcent] at hmem
  obtain ⟨v, hv, hvc⟩ := hmem
  have : v = c := θ.injective hvc
  rw [← this]
  exact hVle hv

end KFour

section ModelFour

variable {Gs : Type} [Group Gs] [Finite Gs]

theorem z_mem_four {S' V : Subgroup Gs} {z' : Gs} (hSp : IsPGroup 2 ↥S') (hVS : V ≤ S')
    (hV4 : IVK.IsFourSubgroup V) (hVn : ∀ s ∈ S', ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hctr : (center ↥S').map S'.subtype = zpowers z') (hz'sq : z' * z' = 1) : z' ∈ V := by
  have hnil : Group.IsNilpotent ↥S' := hSp.isNilpotent
  have hH : (V.subgroupOf S').Normal := by
    constructor
    intro n hn g
    have := hVn g g.2 n hn
    exact this
  have hne : V.subgroupOf S' ≠ ⊥ := by
    intro hbot
    have h4 : Nat.card ↥(V.subgroupOf S') = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
      exact hV4.2
    rw [hbot, Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  obtain ⟨x, hx⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hxV : ((x : ↥S') : Gs) ∈ V := x.2.1
  have hxc : ((x : ↥S') : Gs) ∈ (center ↥S').map S'.subtype := ⟨x, x.2.2, rfl⟩
  rw [hctr] at hxc
  rcases eq_one_or_eq_of_mem_zpowers_sq hz'sq hxc with h | h
  · exfalso
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rw [← h]
    exact hxV

theorem four_elements {V : Subgroup Gs} (hV : Nat.card ↥V = 4) {a b : Gs} (ha : a ∈ V) (hb : b ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1) {v : Gs} (hv : v ∈ V) :
    v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hv1, hva, hvb, hvab⟩ := hcon
  have hmab : a * b ∈ V := V.mul_mem ha hb
  have hne1 : a * b ≠ a := by
    intro h
    apply hb1
    exact mul_eq_left.1 h
  have hne2 : a * b ≠ b := by
    intro h
    apply ha1
    exact mul_eq_right.1 h
  have hcard : ({1, a, b, a * b, v} : Finset Gs).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair]
    · exact Ne.symm hvab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hne2, Ne.symm hvb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, Ne.symm hne1, Ne.symm hva⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1, Ne.symm hv1⟩
  have hsub : (({1, a, b, a * b, v} : Finset Gs) : Set Gs) ⊆ (V : Set Gs) := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact ha
    · exact hb
    · exact hmab
    · exact hv
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hle
  have : (V : Set Gs).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV
  omega

theorem four_conj {S' V : Subgroup Gs} {z' u : Gs} (hz'V : z' ∈ V) (huV : u ∈ V)
    (hV4 : IVK.IsFourSubgroup V) (hz'sq : z' * z' = 1) (hz'1 : z' ≠ 1) (hu1 : u ≠ 1)
    (huz : u ≠ z') (hVn : ∀ s ∈ S', ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hz'c : ∀ x ∈ S', x * z' = z' * x) :
    ∀ x ∈ S', x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u * z' := by
  intro x hx
  have hv := hVn x hx u huV
  have hv1 : x * u * x⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [this, h]
    group
  have hvz : x * u * x⁻¹ ≠ z' := by
    intro h
    apply huz
    have : u = x⁻¹ * (x * u * x⁻¹) * x := by group
    rw [this, h]
    calc x⁻¹ * z' * x = x⁻¹ * (z' * x) := by group
      _ = x⁻¹ * (x * z') := by rw [← hz'c x hx]
      _ = z' := by group
  have hzu1 : z' * u ≠ 1 := by
    intro h
    apply huz
    have : u = z'⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz'sq
  have hcomm : z' * u = u * z' := by
    have h1 := hV4.1.toIsMulCommutative.is_comm.comm (⟨z', hz'V⟩ : ↥V) ⟨u, huV⟩
    exact congrArg Subtype.val h1
  rcases four_elements hV4.2 hz'V huV hz'1 hu1 huz.symm hzu1 hv with h | h | h | h
  · exact absurd h hv1
  · exact absurd h hvz
  · exact Or.inl h
  · exact Or.inr (h.trans hcomm)

end ModelFour

section ModelComp

variable {Gs : Type} [Group Gs] [Finite Gs]

theorem conj_perm {z' : Gs} {E₁ E₂ : Subgroup Gs} (hq₁ : IsQuasisimple ↥E₁)
    (hq₂ : IsQuasisimple ↥E₂) (hEz : IVK.Ez z' = E₁ ⊔ E₂)
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) {s : Gs}
    (hs : s ∈ centralizer ({z'} : Set Gs)) :
    E₁.map (MulAut.conj s).toMonoidHom = E₁ ∨ E₁.map (MulAut.conj s).toMonoidHom = E₂ := by
  set Ez := IVK.Ez z' with hEzdef
  have hE₁Ez : E₁ ≤ Ez := by rw [hEz]; exact le_sup_left
  have hE₂Ez : E₂ ≤ Ez := by rw [hEz]; exact le_sup_right
  have hq₁' : IsQuasisimple ↥(E₁.subgroupOf Ez) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hE₁Ez)).2 hq₁
  have hq₂' : IsQuasisimple ↥(E₂.subgroupOf Ez) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hE₂Ez)).2 hq₂
  have hcomm' : ∀ a ∈ E₁.subgroupOf Ez, ∀ b ∈ E₂.subgroupOf Ez, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hcomm a ha b hb)
  have hsup : E₁.subgroupOf Ez ⊔ E₂.subgroupOf Ez = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hE₁Ez hE₂Ez, ← hEz]
    exact Subgroup.subgroupOf_self _
  have hN : (E₁.subgroupOf Ez ⊔ E₂.subgroupOf Ez).Normal := by
    rw [hsup]
    exact Subgroup.normal_top
  have hC : ∀ γ : ↥Ez, (∀ a ∈ E₁.subgroupOf Ez ⊔ E₂.subgroupOf Ez, a * γ = γ * a) →
      γ ∈ E₁.subgroupOf Ez ⊔ E₂.subgroupOf Ez := by
    intro γ _
    rw [hsup]
    trivial
  have hcomps := comps_of_pair hq₁' hq₂' hcomm' hN hC
  have hc₁ : IsComponent (E₁.subgroupOf Ez) := by
    have : E₁.subgroupOf Ez ∈ {K : Subgroup ↥Ez | IsComponent K} := by
      rw [hcomps]
      exact Or.inl rfl
    exact this
  have hconjEz : Ez.map (MulAut.conj s).toMonoidHom = Ez := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact Ez_conj_mem hs he
    · intro y hy
      refine ⟨s⁻¹ * y * s, ?_, by show s * (s⁻¹ * y * s) * s⁻¹ = y; group⟩
      have := Ez_conj_mem (inv_mem hs) hy
      simpa using this
  let α : ↥Ez ≃* ↥Ez :=
    (Ez.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).trans
      (MulEquiv.subgroupCongr hconjEz)
  have hα : ∀ x : ↥Ez, (α x : Gs) = s * x * s⁻¹ := fun x => rfl
  have hαc := isComponent_map_of_isComponent α hc₁
  have hmem : (E₁.subgroupOf Ez).map α.toMonoidHom ∈
      ({E₁.subgroupOf Ez, E₂.subgroupOf Ez} : Set (Subgroup ↥Ez)) := by
    rw [← hcomps]
    exact hαc
  have hmapeq : (E₁.subgroupOf Ez).map α.toMonoidHom =
      (E₁.map (MulAut.conj s).toMonoidHom).subgroupOf Ez := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply, hα]⟩
    · rintro ⟨e, he, hex⟩
      refine ⟨⟨e, hE₁Ez he⟩, he, ?_⟩
      apply Subtype.ext
      have hex' : s * e * s⁻¹ = (x : Gs) := by simpa [MulAut.conj_apply] using hex
      show ((α ⟨e, hE₁Ez he⟩ : ↥Ez) : Gs) = (x : Gs)
      rw [hα]
      exact hex'
  have hle : E₁.map (MulAut.conj s).toMonoidHom ≤ Ez := by
    rintro _ ⟨e, he, rfl⟩
    exact Ez_conj_mem hs (hE₁Ez he)
  rw [hmapeq] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · left
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hle, inf_eq_left.2 hE₁Ez] at this
  · right
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hle, inf_eq_left.2 hE₂Ez] at this

end ModelComp

section ModelNorm

variable {Gs : Type} [Group Gs]

theorem mem_normalizer_of_map_eq {H : Subgroup Gs} {g : Gs}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set Gs) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hx
    have : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by
      rw [h]
      exact hx
    obtain ⟨e, he, hex⟩ := this
    have h1 : g * e * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hex
    have h2 : e = x := by
      calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = x := by group
    rw [← h2]
    exact he

end ModelNorm

end CFSG.GH74.GLS.Stage1.Main
