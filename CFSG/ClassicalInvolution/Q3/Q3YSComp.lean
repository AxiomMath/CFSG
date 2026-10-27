module

public import CFSG.ClassicalInvolution.Q3.Q3WANoA1
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Group

theorem card_map_eq_of_forall {M X : Type*} [Group M] [Group X] (ψ : M →* X) (F : Subgroup M)
    (h : ∀ x ∈ F, ψ x = 1 → x = 1) : Nat.card (F.map ψ) = Nat.card F := by
  have hinj : Function.Injective (ψ.comp F.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (h x.1 x.2 (MonoidHom.mem_ker.mp hx))
  have hrange : F.map ψ = (ψ.comp F.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem eq_of_inv_mul_mem_center {Y H : Type*} [Group Y] [Group H] [Group.IsPerfect Y]
    (a b : Y →* H) (hab : ∀ y, (a y)⁻¹ * b y ∈ Subgroup.center H) : a = b := by
  let χ : Y →* Subgroup.center H :=
    { toFun := fun y => ⟨(a y)⁻¹ * b y, hab y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => by
        apply Subtype.ext
        have hc : (a y')⁻¹ * ((a y)⁻¹ * b y) = ((a y)⁻¹ * b y) * (a y')⁻¹ :=
          Subgroup.mem_center_iff.1 (hab y) ((a y')⁻¹)
        change (a (y * y'))⁻¹ * b (y * y') = (a y)⁻¹ * b y * ((a y')⁻¹ * b y')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a y')⁻¹ * (a y)⁻¹ * (b y * b y') = ((a y')⁻¹ * ((a y)⁻¹ * b y)) * b y' := by
              simp only [mul_assoc]
          _ = ((a y)⁻¹ * b y) * (a y')⁻¹ * b y' := by rw [hc]
          _ = (a y)⁻¹ * b y * ((a y')⁻¹ * b y') := by simp only [mul_assoc] }
  have hker : _root_.commutator Y ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun y => ?_
  have hy : y ∈ χ.ker := hker (htop ▸ Subgroup.mem_top y)
  exact inv_mul_eq_one.1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hy))

theorem mem_center_of_commutators_central {M : Type*} [Group M] [Group.IsPerfect M] {f : M}
    (hf : ∀ m : M, ⁅f, m⁆ ∈ Subgroup.center M) : f ∈ Subgroup.center M := by
  have h := eq_of_inv_mul_mem_center (MulAut.conj f).toMonoidHom (MonoidHom.id M) (fun y => by
    have := hf y⁻¹
    rw [commutatorElement_def] at this
    simpa [mul_assoc] using this)
  rw [Subgroup.mem_center_iff]
  intro g
  have := DFunLike.congr_fun h g
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
    MonoidHom.id_apply] at this
  calc g * f = f * g * f⁻¹ * f := by rw [this]
    _ = f * g := by simp

theorem eq_or_eq_or_eq_mul_of_forall_fourGroup {X : Type} [Group X] [Finite X] {z : X}
    {C : Subgroup X} (hz1 : z ≠ 1)
    (hF : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → F ≤ C → z ∈ F) {p q : X}
    (hpC : p ∈ C) (hqC : q ∈ C) (hp : p * p = 1) (hq : q * q = 1) (hp1 : p ≠ 1) (hq1 : q ≠ 1)
    (hpq : p ≠ q) (hc : p * q = q * p) : z = p ∨ z = q ∨ z = p * q := by
  have hle : Subgroup.closure ({p, q} : Set X) ≤ C := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have hz := hF _ (Q3Y.isElemAbelian_closure_pair hp hq hc)
    (Balance.Bootstrap.card_closure_pair_eq_four hp hq hp1 hq1 hpq hc) hle
  rcases mem_closure_pair_cases hp hq hc hz with h | h | h | h
  · exact absurd h hz1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem exists_fourGroup_of_noncentral {G : Type} [Group G] [Finite G] {p q : G}
    (hp2 : p * p = 1) (hq2 : q * q = 1) (hc : p * q = q * p) (hp : p ∉ Subgroup.center G)
    (hq : q ∉ Subgroup.center G) (hpq : p * q ∉ Subgroup.center G) :
    ∃ F : Subgroup G, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ⊓ Subgroup.center G = ⊥ := by
  have hp1 : p ≠ 1 := fun h => hp (h ▸ Subgroup.one_mem _)
  have hq1 : q ≠ 1 := fun h => hq (h ▸ Subgroup.one_mem _)
  have hne : p ≠ q := by
    intro h
    apply hpq
    rw [← h, hp2]
    exact Subgroup.one_mem _
  refine ⟨Subgroup.closure {p, q}, Q3Y.isElemAbelian_closure_pair hp2 hq2 hc,
    Balance.Bootstrap.card_closure_pair_eq_four hp2 hq2 hp1 hq1 hne hc, ?_⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgF, hgZ⟩ := hg
  rw [Subgroup.mem_bot]
  rcases mem_closure_pair_cases hp2 hq2 hc hgF with h | h | h | h
  · exact h
  · exact absurd (h ▸ hgZ) hp
  · exact absurd (h ▸ hgZ) hq
  · exact absurd (h ▸ hgZ) hpq

end Group

section Lie


variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

structure BDLoc (D : LieSystemData3 ι X Φ) (i₀ : ι) (zb : X) : Prop where
  ne_one : zb ≠ 1
  mul_self : zb * zb = 1
  central : ∀ x : X, x * zb = zb * x
  mem : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 →
    F ≤ Subgroup.centralizer ((D.hom i₀).range : Set X) → zb ∈ F

theorem range_le_centralizer_of_ne (D : LieSystemData3 ι X Φ) {i j : ι} (hij : i ≠ j) :
    (D.hom i).range ≤ Subgroup.centralizer ((D.hom j).range : Set X) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  exact (D.commute i j hij a b).symm

theorem central_of_central_in_range (D : LieSystemData3 ι X Φ) {i : ι} {x : X}
    (hxi : x ∈ (D.hom i).range) (hx : ∀ y ∈ (D.hom i).range, y * x = x * y) :
    ∀ g : X, g * x = x * g := by
  have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [← D.generate]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst hj
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hxi
      exact Subgroup.mem_centralizer_singleton_iff.mpr (D.commute j i hj b a)
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

theorem eq_or_eq_or_eq_mul_of_bdLoc [Finite X] {D : LieSystemData3 ι X Φ} {i₀ : ι} {zb : X}
    (h : BDLoc D i₀ zb) {p q : X} (hpC : p ∈ Subgroup.centralizer ((D.hom i₀).range : Set X))
    (hqC : q ∈ Subgroup.centralizer ((D.hom i₀).range : Set X)) (hp : p * p = 1) (hq : q * q = 1)
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q) (hc : p * q = q * p) :
    zb = p ∨ zb = q ∨ zb = p * q :=
  eq_or_eq_or_eq_mul_of_forall_fourGroup h.ne_one h.mem hpC hqC hp hq hp1 hq1 hpq hc

theorem exists_noncentral_involution [Finite X] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι X Φ) (i : ι) (hi : D.kind i ≠ CompData.sl23) :
    ∃ c ∈ (D.hom i).range, c * c = 1 ∧ c ≠ 1 ∧ ∃ y ∈ (D.hom i).range, c * y ≠ y * c := by
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  have hcard := D.card_eq _ hRΦ
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R.map (D.hom i))) 2
    (by rw [hcard]; norm_num)
  have hc₀X : orderOf (c₀ : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hc₀
  have hsq : (c₀ : X) * (c₀ : X) = 1 := by
    rw [← pow_two]
    exact hc₀X ▸ pow_orderOf_eq_one _
  have hne : (c₀ : X) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc₀X
    omega
  obtain ⟨r, hrR, hr⟩ := c₀.2
  refine ⟨c₀, ⟨r, hr⟩, hsq, hne, ?_⟩
  by_contra hcon
  push Not at hcon
  have hr1 : r = 1 := Q3W.eq_one_of_central_comp3 hMFZ (D.kind i) (D.valid i) hi (D.hom i)
    (D.ker_le_center i) hR hrR fun y => by
      rw [hr]
      exact hcon _ ⟨y, rfl⟩
  exact hne (by rw [← hr, hr1, map_one])

theorem false_of_two_nonA1 [Finite X] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι X Φ) {i₀ : ι} {zb : X} (h : BDLoc D i₀ zb) {i j : ι} (hi : i ≠ i₀)
    (hj : j ≠ i₀) (hij : i ≠ j) (hki : D.kind i ≠ CompData.sl23)
    (hkj : D.kind j ≠ CompData.sl23) : False := by
  obtain ⟨c, hcR, hc2, hc1, y, hyR, hcy⟩ := exists_noncentral_involution hMFZ D i hki
  obtain ⟨d, hdR, hd2, hd1, w, hwR, hdw⟩ := exists_noncentral_involution hMFZ D j hkj
  have hcomm : ∀ a ∈ (D.hom i).range, ∀ b ∈ (D.hom j).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i j hij a b
  have hcd : c * d = d * c := hcomm c hcR d hdR
  have hcne : c ≠ d := by
    intro hcd'
    exact hcy (by rw [hcd']; exact (hcomm y hyR d hdR).symm)
  have hcC : c ∈ Subgroup.centralizer ((D.hom i₀).range : Set X) :=
    range_le_centralizer_of_ne D hi hcR
  have hdC : d ∈ Subgroup.centralizer ((D.hom i₀).range : Set X) :=
    range_le_centralizer_of_ne D hj hdR
  rcases eq_or_eq_or_eq_mul_of_bdLoc h hcC hdC hc2 hd2 hc1 hd1 hcne hcd with h1 | h1 | h1
  · exact hcy (by rw [← h1]; exact (h.central y).symm)
  · exact hdw (by rw [← h1]; exact (h.central w).symm)
  ·
    have hcz : c = zb * d := by
      calc c = c * (d * d) := by rw [hd2, mul_one]
        _ = (c * d) * d := (mul_assoc _ _ _).symm
        _ = zb * d := by rw [← h1]
    refine hcy ?_
    calc c * y = (zb * d) * y := by rw [hcz]
      _ = zb * (d * y) := mul_assoc _ _ _
      _ = zb * (y * d) := by rw [← hcomm y hyR d hdR]
      _ = (zb * y) * d := (mul_assoc _ _ _).symm
      _ = (y * zb) * d := by rw [h.central y]
      _ = y * (zb * d) := mul_assoc _ _ _
      _ = y * c := by rw [hcz]

theorem false_of_comp_fourGroup (D : LieSystemData3 ι X Φ) {i₀ : ι} {zb : X}
    (h : BDLoc D i₀ zb) {i : ι} (hi : i ≠ i₀)
    (hZ₂ : ∀ f : (D.kind i).G, (∀ m : (D.kind i).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i).G) →
      f ∈ Subgroup.center (D.kind i).G)
    {F : Subgroup (D.kind i).G} (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 4)
    (hFZ : F ⊓ Subgroup.center (D.kind i).G = ⊥) : False := by
  have hker : ∀ x ∈ F, D.hom i x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center (D.kind i).G := D.ker_le_center i (MonoidHom.mem_ker.mpr hx1)
    have hmem : x ∈ F ⊓ Subgroup.center (D.kind i).G := ⟨hx, hxc⟩
    rw [hFZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hE : IsElemAbelian 2 (F.map (D.hom i)) := Q3Y.isElemAbelian_map (D.hom i) hF
  have hEcard : Nat.card (F.map (D.hom i)) = 4 := by
    rw [card_map_eq_of_forall (D.hom i) F hker, hcard]
  have hEC : F.map (D.hom i) ≤ Subgroup.centralizer ((D.hom i₀).range : Set X) :=
    (Subgroup.map_le_range (D.hom i) F).trans (range_le_centralizer_of_ne D hi)
  obtain ⟨f, hfF, hfz⟩ := h.mem _ hE hEcard hEC
  have hfc : f ∈ Subgroup.center (D.kind i).G := by
    refine hZ₂ f fun m => ?_
    refine D.ker_le_center i ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hfz, commutatorElement_eq_one_iff_commute]
    exact (h.central (D.hom i m)).symm
  have hmem : f ∈ F ⊓ Subgroup.center (D.kind i).G := ⟨hfF, hfc⟩
  rw [hFZ, Subgroup.mem_bot] at hmem
  rw [hmem, map_one] at hfz
  exact h.ne_one hfz.symm

end Lie

end CFSG.ClassicalInvolution.Q3.Q3YS
