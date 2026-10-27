module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Facts
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Embed
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open Equiv Equiv.Perm

theorem exists_hom_of_central_involution_of_odd_index {E : Type*} [Group E] [Finite E] {z : E}
    (hz : ∀ x : E, x * z = z * x) (hz2 : z * z = 1) (P : Subgroup E) (hP : Odd P.index)
    (hzP : z ∈ P) {A : Type*} [CommGroup A] (ϕ : P →* A) :
    ∃ ψ : E →* A, ψ z = ϕ ⟨z, hzP⟩ := by
  have : P.FiniteIndex := ⟨by
    have : 0 < P.index := hP.pos
    omega⟩
  refine ⟨MonoidHom.transfer ϕ, ?_⟩
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : Commute z g₀ := (hz g₀).symm
    have h1 : z ^ k * g₀ = g₀ * z ^ k := (hc.pow_left k).eq
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = z ^ k := by rw [h1]; simp
  rw [MonoidHom.transfer_eq_pow ϕ z key]
  congr 1
  apply Subtype.ext
  obtain ⟨m, hm⟩ := hP
  simp only [hm, pow_succ, pow_mul]
  have : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  rw [this, one_pow, one_mul]

theorem exists_hom_zmod_two_of_index_two {E : Type*} [Group E] {P C : Subgroup E}
    (h : (C.subgroupOf P).index = 2) :
    ∃ ϕ : P →* Multiplicative (ZMod 2), ∀ x : P, ϕ x = 1 ↔ (x : E) ∈ C := by
  classical
  refine ⟨
    { toFun := fun x => if (x : E) ∈ C then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := fun x y => ?_ }, fun x => ?_⟩
  · have hmul := Subgroup.mul_mem_iff_of_index_two h (a := x) (b := y)
    simp only [Subgroup.mem_subgroupOf] at hmul
    have hxy : ((x * y : P) : E) = (x : E) * y := rfl
    show (if ((x * y : P) : E) ∈ C then 1 else Multiplicative.ofAdd (1 : ZMod 2)) =
      (if (x : E) ∈ C then 1 else Multiplicative.ofAdd (1 : ZMod 2)) *
        (if (y : E) ∈ C then 1 else Multiplicative.ofAdd (1 : ZMod 2))
    rw [hxy]
    by_cases hx : (x : E) ∈ C <;> by_cases hy : (y : E) ∈ C
    · have hxyC : (x : E) * y ∈ C := C.mul_mem hx hy
      simp [hxyC, hx, hy]
    · have hxyC : (x : E) * y ∉ C := by
        intro h'
        exact hy (by simpa using (C.mul_mem_cancel_left hx).mp h')
      simp [hxyC, hx, hy]
    · have hxyC : (x : E) * y ∉ C := by
        intro h'
        exact hx (by simpa using (C.mul_mem_cancel_right hy).mp h')
      simp [hxyC, hx, hy]
    · have hxyC : (x : E) * y ∈ C := by rw [← hxy]; exact hmul.mpr (by simp [hx, hy])
      simp only [hxyC, hx, hy, ↓reduceIte]
      rw [← ofAdd_add]
      decide
  · show (if (x : E) ∈ C then (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = 1 ↔
      (x : E) ∈ C
    by_cases hx : (x : E) ∈ C
    · simp [hx]
    · simp only [hx, ↓reduceIte, iff_false]
      decide

theorem not_isPerfect_of_split_over_sylow {E : Type*} [Group E] [Finite E] {z : E}
    (hz : ∀ x : E, x * z = z * x) (hz2 : z * z = 1) {P C : Subgroup E} (hP : Odd P.index)
    (hzP : z ∈ P) (hCP : C ≤ P) (hidx : Nat.card P = 2 * Nat.card C) (hzC : z ∉ C) :
    ¬ Group.IsPerfect E := by
  intro hperf
  have hindex : (C.subgroupOf P).index = 2 := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf P)
    have h2 : Nat.card (C.subgroupOf P) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
    have h3 : Nat.card (↥P) = Nat.card P := rfl
    have hpos : 0 < Nat.card C := Nat.card_pos
    rw [h2] at h1
    have : Nat.card C * (C.subgroupOf P).index = Nat.card C * 2 := by
      rw [h1]; rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨ϕ, hϕ⟩ := exists_hom_zmod_two_of_index_two hindex
  obtain ⟨ψ, hψ⟩ := exists_hom_of_central_involution_of_odd_index hz hz2 P hP hzP ϕ
  have hker := hom_trivial_of_perfect_of_commute hperf ψ (fun x y => mul_comm _ _) z
  exact hzC ((hϕ ⟨z, hzP⟩).mp (hψ.symm.trans hker))

theorem card_A7 : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.card_eq_fintype_card, Nat.factorial]

@[expose] def fixedIn {E : Type*} [Group E] (α : MulAut E) (H : Subgroup E) : Subgroup E :=
  H ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id E)

theorem mem_fixedIn {E : Type*} [Group E] {α : MulAut E} {H : Subgroup E} {x : E} :
    x ∈ fixedIn α H ↔ x ∈ H ∧ α x = x := Iff.rfl

structure IsDoubleCoverA7 {E : Type*} [Group E] (π : E →* A7) (z : E) : Prop where
  surjective : Function.Surjective π
  perfect : Group.IsPerfect E
  ne_one : z ≠ 1
  sq_eq_one : z * z = 1
  central : ∀ x : E, x * z = z * x
  ker_iff : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z

namespace IsDoubleCoverA7

variable {E : Type*} [Group E] {π : E →* A7} {z : E}

theorem card_ker (h : IsDoubleCoverA7 π z) : Nat.card π.ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨z, (h.ker_iff z).mpr (Or.inr rfl)⟩, fun h1 => h.ne_one (congrArg Subtype.val h1).symm, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases (h.ker_iff w).mp hw with rfl | rfl
  · left; rfl
  · right; rfl

theorem eq_or_eq_mul_z_of_map_eq (h : IsDoubleCoverA7 π z) {u v : E} (huv : π u = π v) :
    u = v ∨ u = v * z := by
  have : π (v⁻¹ * u) = 1 := by rw [map_mul, map_inv, huv, inv_mul_cancel]
  rcases (h.ker_iff _).mp this with h1 | h1
  · left; exact (inv_mul_eq_one.mp h1).symm
  · right; rw [← h1]; group

theorem mul_self_eq_of_map_eq (h : IsDoubleCoverA7 π z) {u v : E} (huv : π u = π v) :
    u * u = v * v := by
  rcases h.eq_or_eq_mul_z_of_map_eq huv with rfl | rfl
  · rfl
  · calc v * z * (v * z) = v * (z * v) * z := by group
      _ = v * (v * z) * z := by rw [h.central v]
      _ = v * v * (z * z) := by group
      _ = v * v := by rw [h.sq_eq_one, mul_one]

theorem exists_lift_involution (h : IsDoubleCoverA7 π z) {w : E} (hw : w * w = 1) (hw1 : w ≠ 1)
    (hwz : w ≠ z) : ∀ y : A7, y ≠ 1 → y * y = 1 → ∃ u : E, u * u = 1 ∧ π u = y := by
  have hπw : π w ≠ 1 := fun h1 => by
    rcases (h.ker_iff w).mp h1 with h2 | h2
    exacts [hw1 h2, hwz h2]
  have hπw2 : π w * π w = 1 := by rw [← map_mul, hw, map_one]
  obtain ⟨g₀, hg₀⟩ := a7_involution_conj (π w) hπw hπw2
  obtain ⟨x₀, hx₀⟩ := h.surjective g₀
  have hu₀ : (x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀) = 1 := by
    calc (x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀) = x₀⁻¹ * (w * w) * x₀ := by group
      _ = 1 := by rw [hw]; group
  have hu₀π : π (x₀⁻¹ * w * x₀) = tD := by
    rw [map_mul, map_mul, map_inv, hx₀, ← hg₀]
    group
  intro y hy hy2
  obtain ⟨g, hg⟩ := a7_involution_conj y hy hy2
  obtain ⟨x, hx⟩ := h.surjective g
  refine ⟨x * (x₀⁻¹ * w * x₀) * x⁻¹, ?_, ?_⟩
  · calc x * (x₀⁻¹ * w * x₀) * x⁻¹ * (x * (x₀⁻¹ * w * x₀) * x⁻¹)
        = x * ((x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀)) * x⁻¹ := by group
      _ = 1 := by rw [hu₀]; group
  · rw [map_mul, map_mul, map_inv, hu₀π, hx, ← hg]

section Involutions

variable [Finite E]

theorem eq_one_or_eq_z_of_sq_eq_one (h : IsDoubleCoverA7 π z) {w : E} (hw : w * w = 1) :
    w = 1 ∨ w = z := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hw1, hwz⟩ := hcon
  have hlift := h.exists_lift_involution hw hw1 hwz
  obtain ⟨hs2, ht2, h4, hne⟩ := dihedral_rel
  have hsD : sD ≠ 1 := by decide
  have htD : tD ≠ 1 := by decide
  have hcc : (sD * tD) ^ 2 * (sD * tD) ^ 2 = 1 := by rw [← pow_add]; exact h4
  obtain ⟨s', hs'2, hs'⟩ := hlift sD hsD hs2
  obtain ⟨t', ht'2, ht'⟩ := hlift tD htD ht2
  obtain ⟨c', hc'2, hc'⟩ := hlift ((sD * tD) ^ 2) hne hcc
  have hst : π ((s' * t') ^ 2) = π c' := by rw [map_pow, map_mul, hs', ht', hc']
  have hsq : (s' * t') ^ 2 * (s' * t') ^ 2 = 1 := by
    rw [h.mul_self_eq_of_map_eq hst, hc'2]
  have h4' : (s' * t') ^ 4 = 1 := by rw [show 4 = 2 + 2 from rfl, pow_add]; exact hsq
  set C : Subgroup E := Subgroup.closure ({s', t'} : Set E) with hC
  have hC8 : Nat.card C ≤ 8 := card_closure_pair_le_eight hs'2 ht'2 h4'
  have hmap : C.map π = D8 := by
    rw [hC, MonoidHom.map_closure, Set.image_pair, hs', ht']
    rfl
  have hker := Subgroup.card_ker_mul_card_range (π.comp C.subtype)
  have hrange : (π.comp C.subtype).range = D8 := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  rw [hrange, card_D8] at hker
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hkerpos : 0 < Nat.card (π.comp C.subtype).ker := Nat.card_pos
  have hker1 : Nat.card (π.comp C.subtype).ker = 1 := by omega
  have hC8' : Nat.card C = 8 := by omega
  have hker' : (π.comp C.subtype).ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hker1
  have hzC : z ∉ C := by
    intro hzC
    have hmem : (⟨z, hzC⟩ : C) ∈ (π.comp C.subtype).ker := by
      rw [MonoidHom.mem_ker]
      exact (h.ker_iff z).mpr (Or.inr rfl)
    rw [hker', Subgroup.mem_bot] at hmem
    exact h.ne_one (congrArg Subtype.val hmem)
  set P : Subgroup E := D8.comap π with hP
  have hPcard : Nat.card P = 2 * 8 := by
    rw [hP, QuaternionStructure.natCard_comap_eq π h.surjective D8, h.card_ker, card_D8]
  have hCP : C ≤ P := Subgroup.map_le_iff_le_comap.mp hmap.le
  have hzP : z ∈ P := by
    show π z ∈ D8
    rw [(h.ker_iff z).mpr (Or.inr rfl)]
    exact D8.one_mem
  have hodd : Odd P.index := by
    rw [hP, Subgroup.index_comap_of_surjective D8 h.surjective]
    have h1 := Subgroup.card_mul_index D8
    rw [card_D8, card_A7] at h1
    have h2 : D8.index = 315 := by omega
    rw [h2]
    decide
  exact not_isPerfect_of_split_over_sylow h.central h.sq_eq_one hodd hzP hCP (by omega) hzC
    h.perfect

end Involutions

end IsDoubleCoverA7

theorem mulAut_eq_one_of_perfect_of_central {G : Type*} [Group G] (hperf : Group.IsPerfect G)
    (α : MulAut G) (hc : ∀ x : G, x⁻¹ * α x ∈ Subgroup.center G) : α = 1 := by
  let θ : G →* G := MonoidHom.mk' (fun x => x⁻¹ * α x) (by
    intro x y
    have h1 : y⁻¹ * (x⁻¹ * α x) = (x⁻¹ * α x) * y⁻¹ := Subgroup.mem_center_iff.mp (hc x) y⁻¹
    calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by rw [map_mul]; group
      _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [h1]
      _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group)
  have hθ := hom_trivial_of_perfect_of_commute hperf θ (fun x y =>
    Subgroup.mem_center_iff.mp (hc y) (x⁻¹ * α x))
  ext x
  have h1 : x⁻¹ * α x = 1 := hθ x
  exact inv_mul_eq_one.mp h1 |>.symm

namespace IsDoubleCoverA7

variable {E : Type*} [Group E] {π : E →* A7} {z : E}

theorem mulAut_apply_z (h : IsDoubleCoverA7 π z) (α : MulAut E) : α z = z := by
  have hcen : ∀ x : E, x * α z = α z * x := by
    intro x
    calc x * α z = α (α.symm x * z) := by simp
      _ = α (z * α.symm x) := by rw [h.central]
      _ = α z * x := by simp
  have hπ : π (α z) = 1 := by
    have hc : π (α z) ∈ Subgroup.center A7 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := h.surjective g
      rw [← map_mul, ← map_mul, hcen]
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    exact Subgroup.mem_bot.mp hc
  rcases (h.ker_iff _).mp hπ with h1 | h1
  · exfalso
    exact h.ne_one (α.injective (by rw [h1, map_one]))
  · exact h1

theorem exists_mulAut_of_mulAut (h : IsDoubleCoverA7 π z) (α : MulAut E) :
    ∃ β : MulAut A7, ∀ x : E, π (α x) = β (π x) := by
  have hαz := h.mulAut_apply_z α
  have hker : π.ker ≤ (π.comp α.toMonoidHom).ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rcases (h.ker_iff w).mp hw with h1 | h1
    · rw [h1]; simp
    · rw [h1]
      show π (α z) = 1
      rw [hαz]
      exact (h.ker_iff z).mpr (Or.inr rfl)
  let β₀ : A7 →* A7 := π.liftOfSurjective h.surjective ⟨π.comp α.toMonoidHom, hker⟩
  have hβ₀ : ∀ x, β₀ (π x) = π (α x) := fun x =>
    π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv h.surjective)
      ⟨π.comp α.toMonoidHom, hker⟩ x
  have hinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    obtain ⟨x, rfl⟩ := h.surjective g
    rw [hβ₀] at hg
    rw [Subgroup.mem_bot]
    rcases (h.ker_iff _).mp hg with h1 | h1
    · have : x = 1 := α.injective (by rw [h1, map_one])
      rw [this, map_one]
    · have : x = z := α.injective (by rw [h1, hαz])
      rw [this]
      exact (h.ker_iff z).mpr (Or.inr rfl)
  have hsurj : Function.Surjective β₀ := by
    intro g
    obtain ⟨y, rfl⟩ := h.surjective g
    refine ⟨π (α.symm y), ?_⟩
    rw [hβ₀]
    simp
  exact ⟨MulEquiv.ofBijective β₀ ⟨hinj, hsurj⟩, fun x => (hβ₀ x).symm⟩

end IsDoubleCoverA7

@[expose] noncomputable def conjEquiv : Perm (Fin 7) ≃* MulAut A7 :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

theorem conjEquiv_apply (σ : Perm (Fin 7)) (a : A7) :
    ((conjEquiv σ a : A7) : Perm (Fin 7)) = σ * a * σ⁻¹ :=
  MulAut.conjNormal_apply σ a

namespace IsDoubleCoverA7

variable {E : Type*} [Group E] {π : E →* A7} {z : E}

noncomputable def indAut (h : IsDoubleCoverA7 π z) (α : MulAut E) : MulAut A7 :=
  Classical.choose (h.exists_mulAut_of_mulAut α)

theorem indAut_spec (h : IsDoubleCoverA7 π z) (α : MulAut E) (x : E) :
    π (α x) = h.indAut α (π x) :=
  Classical.choose_spec (h.exists_mulAut_of_mulAut α) x

theorem indAut_eq (h : IsDoubleCoverA7 π z) {α : MulAut E} {β : MulAut A7}
    (hβ : ∀ x : E, π (α x) = β (π x)) : h.indAut α = β := by
  ext g
  obtain ⟨x, rfl⟩ := h.surjective g
  rw [← h.indAut_spec, hβ]

noncomputable def indHom (h : IsDoubleCoverA7 π z) : MulAut E →* MulAut A7 where
  toFun := h.indAut
  map_one' := h.indAut_eq (fun x => rfl)
  map_mul' α α' := h.indAut_eq (fun x => by
    rw [MulAut.mul_apply, h.indAut_spec α, h.indAut_spec α', MulAut.mul_apply])

noncomputable def autPerm (h : IsDoubleCoverA7 π z) : MulAut E →* Perm (Fin 7) :=
  (conjEquiv.symm : MulAut A7 ≃* Perm (Fin 7)).toMonoidHom.comp h.indHom

theorem autPerm_spec (h : IsDoubleCoverA7 π z) (α : MulAut E) (x : E) :
    ((π (α x) : A7) : Perm (Fin 7)) = h.autPerm α * (π x : Perm (Fin 7)) * (h.autPerm α)⁻¹ := by
  rw [h.indAut_spec α x, ← conjEquiv_apply]
  congr 2
  show h.indAut α = conjEquiv (conjEquiv.symm (h.indHom α))
  simp only [MulEquiv.apply_symm_apply]
  rfl

theorem autPerm_injective (h : IsDoubleCoverA7 π z) : Function.Injective h.autPerm := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  rw [Subgroup.mem_bot]
  apply mulAut_eq_one_of_perfect_of_central h.perfect
  intro x
  have h1 : h.indAut α = 1 := by
    have : conjEquiv.symm (h.indHom α) = 1 := hα
    have h2 : h.indHom α = 1 := by
      have := congrArg conjEquiv this
      simpa using this
    exact h2
  have h3 : π (x⁻¹ * α x) = 1 := by
    rw [map_mul, map_inv, h.indAut_spec α x, h1]
    simp
  rcases (h.ker_iff _).mp h3 with h4 | h4
  · rw [h4]; exact Subgroup.one_mem _
  · rw [h4]
    exact Subgroup.mem_center_iff.mpr fun g => h.central g |>.symm ▸ rfl

theorem ker_le_center (h : IsDoubleCoverA7 π z) {w : E} (hw : π w = 1) :
    ∀ g : E, g * w = w * g := by
  rcases (h.ker_iff w).mp hw with rfl | rfl
  · intro g; simp
  · exact h.central

theorem inv_mul_mem_ker_iff {α : MulAut E} {x : E} :
    x⁻¹ * α x ∈ π.ker ↔ π (α x) = π x := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]

section Fixed

variable [Finite E]

theorem card_le_two_mul_card_fixedIn (h : IsDoubleCoverA7 π z) (α : MulAut E) (H : Subgroup E)
    (hH : ∀ x ∈ H, π (α x) = π x) : Nat.card H ≤ 2 * Nat.card (fixedIn α H) := by
  have hcen : ∀ x ∈ H, ∀ g : E, g * (x⁻¹ * α x) = (x⁻¹ * α x) * g := fun x hx =>
    h.ker_le_center (inv_mul_mem_ker_iff.mpr (hH x hx))
  let θ : H →* E := MonoidHom.mk' (fun x => (x : E)⁻¹ * α x) (by
    intro x y
    have h1 := hcen x x.2 (y : E)⁻¹
    calc ((x * y : H) : E)⁻¹ * α ((x * y : H) : E)
        = (y : E)⁻¹ * ((x : E)⁻¹ * α x) * α y := by simp [mul_assoc]
      _ = ((x : E)⁻¹ * α x) * (y : E)⁻¹ * α y := by rw [h1]
      _ = ((x : E)⁻¹ * α x) * ((y : E)⁻¹ * α y) := by group)
  have hrange : θ.range ≤ π.ker := by
    rintro _ ⟨x, rfl⟩
    exact inv_mul_mem_ker_iff.mpr (hH x x.2)
  have hrange2 : Nat.card θ.range ≤ 2 := h.card_ker ▸ Subgroup.card_le_of_le hrange
  have hkerfix : θ.ker.map H.subtype = fixedIn α H := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.subtype_apply, mem_fixedIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have : (y : E)⁻¹ * α y = 1 := hy
      exact (inv_mul_eq_one.mp this).symm
    · rintro ⟨hxH, hxα⟩
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      show x⁻¹ * α x = 1
      rw [hxα]; simp
  have hcard := Subgroup.card_ker_mul_card_range θ
  rw [← hkerfix, Subgroup.card_map_of_injective H.subtype_injective]
  calc Nat.card H = Nat.card θ.ker * Nat.card θ.range := hcard.symm
    _ ≤ Nat.card θ.ker * 2 := Nat.mul_le_mul_left _ hrange2
    _ = 2 * Nat.card θ.ker := by ring

theorem exists_fixed_two_subgroup (h : IsDoubleCoverA7 π z) (α : MulAut E) (hα : α * α = 1) :
    ∃ R : Subgroup E, IsPGroup 2 R ∧ 8 ≤ Nat.card R ∧ ∀ x ∈ R, α x = x := by
  set σ : Perm (Fin 7) := h.autPerm α with hσdef
  have hσ : σ * σ = 1 := by rw [hσdef, ← map_mul, hα, map_one]
  have hmod := card_evenCentralizer_mod hσ
  have h8dvd : 2 ^ 3 ∣ Nat.card (evenCentralizer σ) := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨B₀, hB₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8dvd
  set B : Subgroup A7 := B₀.map (evenCentralizer σ).subtype with hB
  have hBcard : Nat.card B = 8 := by
    rw [hB, Subgroup.card_map_of_injective (evenCentralizer σ).subtype_injective, hB₀]
    norm_num
  have hBle : ∀ g ∈ B, g ∈ evenCentralizer σ := by
    rintro _ ⟨g, _, rfl⟩
    exact g.2
  set H : Subgroup E := B.comap π with hH
  have hHcard : Nat.card H = 16 := by
    rw [hH, QuaternionStructure.natCard_comap_eq π h.surjective B, h.card_ker, hBcard]
  have hfix : ∀ x ∈ H, π (α x) = π x := fun x hx => by
    apply Subtype.ext
    rw [h.autPerm_spec α x, ← hσdef]
    have : (π x : Perm (Fin 7)) * σ = σ * π x := hBle _ hx
    calc σ * (π x : Perm (Fin 7)) * σ⁻¹ = ((π x : Perm (Fin 7)) * σ) * σ⁻¹ := by rw [this]
      _ = π x := by group
  have hcard := card_le_two_mul_card_fixedIn h α H hfix
  have hRle : fixedIn α H ≤ H := inf_le_left
  have hdvd : Nat.card (fixedIn α H) ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hRle
    rw [hHcard] at this
    simpa using this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨fixedIn α H, IsPGroup.of_card hk, by omega, fun x hx => hx.2⟩

omit [Finite E] in
theorem map_apply_eq_of_mem_evenCentralizer (h : IsDoubleCoverA7 π z) (α : MulAut E) {x : E}
    (hx : π x ∈ evenCentralizer (h.autPerm α)) : π (α x) = π x := by
  apply Subtype.ext
  rw [h.autPerm_spec α x]
  have hc : (π x : Perm (Fin 7)) * h.autPerm α = h.autPerm α * π x := hx
  calc h.autPerm α * (π x : Perm (Fin 7)) * (h.autPerm α)⁻¹
      = ((π x : Perm (Fin 7)) * h.autPerm α) * (h.autPerm α)⁻¹ := by rw [hc]
    _ = π x := by group

theorem mulAut_eq_one_of_centralizes_D8 (h : IsDoubleCoverA7 π z) (α : MulAut E)
    (hα : ∀ x ∈ D8.comap π, α x = x) : α = 1 := by
  by_contra hne
  set σ : Perm (Fin 7) := h.autPerm α with hσdef
  have hcomm : ∀ d : A7, d ∈ D8 → (d : Perm (Fin 7)) * σ = σ * d := by
    intro d hd
    obtain ⟨x, rfl⟩ := h.surjective d
    have hx : x ∈ D8.comap π := hd
    have h1 := h.autPerm_spec α x
    rw [hα x hx, ← hσdef] at h1
    calc (π x : Perm (Fin 7)) * σ = (σ * π x * σ⁻¹) * σ := by rw [← h1]
      _ = σ * π x := by group
  have hσ2 : σ * σ = 1 := sq_eq_one_of_commute_D8 hcomm
  have hα2 : α * α = 1 := by
    apply h.autPerm_injective
    rw [map_mul, ← hσdef, hσ2, map_one]
  have hσne : σ ≠ 1 := by
    intro h1
    apply hne
    apply h.autPerm_injective
    rw [map_one]
    exact h1
  obtain ⟨a, ha1, ha2⟩ := exists_commuting_conj σ hσ2 hσne
  set C : Subgroup A7 := evenCentralizer σ with hCdef
  have hDC : D8 ≤ C := fun d hd => hcomm d hd
  have h8C : 8 ∣ Nat.card C := card_D8 ▸ Subgroup.card_dvd_of_le hDC
  have hCdvd : Nat.card C ∣ 2520 := card_A7 ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨m, hm⟩ := h8C
  have hmodd : Odd m := by
    have h1 : 8 * m ∣ 8 * 315 := by rw [← hm]; simpa using hCdvd
    have h2 : m ∣ 315 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    exact Odd.of_dvd_nat (by decide) h2
  set HC : Subgroup E := C.comap π with hHCdef
  have hHC : Nat.card HC = 16 * m := by
    rw [hHCdef, QuaternionStructure.natCard_comap_eq π h.surjective C, h.card_ker, hm]
    ring
  have hHD : Nat.card (D8.comap π) = 16 := by
    rw [QuaternionStructure.natCard_comap_eq π h.surjective D8, h.card_ker, card_D8]
  have hfixC : ∀ x ∈ HC, π (α x) = π x := fun x hx => h.map_apply_eq_of_mem_evenCentralizer α hx
  have hcardC := card_le_two_mul_card_fixedIn h α HC hfixC
  have hDHC : D8.comap π ≤ HC := Subgroup.comap_mono hDC
  have hDR : D8.comap π ≤ fixedIn α HC := fun x hx => ⟨hDHC hx, hα x hx⟩
  have h16R : 16 ∣ Nat.card (fixedIn α HC) := hHD ▸ Subgroup.card_dvd_of_le hDR
  have hRle : fixedIn α HC ≤ HC := inf_le_left
  have hRdvd : Nat.card (fixedIn α HC) ∣ Nat.card HC := Subgroup.card_dvd_of_le hRle
  have hRHC : fixedIn α HC = HC := by
    obtain ⟨k, hk⟩ := h16R
    rw [hHC, hk] at hRdvd
    rw [hHC, hk] at hcardC
    obtain ⟨j, hj⟩ := hRdvd
    have hmj : m = k * j := by nlinarith
    have hj12 : j = 1 ∨ j = 2 := by
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0] at hk
          have : 0 < Nat.card (fixedIn α HC) := Nat.card_pos
          omega
        · exact h0
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0] at hmj; exact absurd hmodd (by simp [hmj])
        · exact h0
      have : k * j ≤ 2 * k := by nlinarith
      have : j ≤ 2 := by nlinarith
      omega
    have hj1 : j = 1 := by
      rcases hj12 with h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hmj
        exact (Nat.not_even_iff_odd.mpr hmodd) ⟨k, by omega⟩
    rw [hj1] at hj
    apply Subgroup.eq_of_le_of_card_ge hRle
    rw [hHC, hk]
    omega
  have hfixall : ∀ x : E, π x ∈ C → α x = x := fun x hx => by
    have hxHC : x ∈ HC := hx
    rw [← hRHC] at hxHC
    exact hxHC.2
  obtain ⟨x, hx⟩ := h.surjective a
  set y : E := x⁻¹ * α x with hy
  have hπy : (π y : Perm (Fin 7)) = ((a : Perm (Fin 7))⁻¹ * σ * a) * σ⁻¹ := by
    have h1 := h.autPerm_spec α x
    rw [← hσdef, hx] at h1
    rw [hy, map_mul, map_inv, hx, Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group
  have hπyC : π y ∈ C := by
    show (π y : Perm (Fin 7)) * σ = σ * (π y : Perm (Fin 7))
    rw [hπy]
    calc ((a : Perm (Fin 7))⁻¹ * σ * a * σ⁻¹) * σ = (a : Perm (Fin 7))⁻¹ * σ * a := by group
      _ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a) * σ⁻¹ := by
        rw [← ha2]; group
      _ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a * σ⁻¹) := by group
  have hαy : α y = y := hfixall y hπyC
  have hαy' : α y = y⁻¹ := by
    have h1 : α (α x) = x := by
      have := congrArg (fun β : MulAut E => β x) hα2
      simpa using this
    rw [hy, map_mul, map_inv, h1]
    group
  have hy2 : y * y = 1 := by
    have : y = y⁻¹ := hαy.symm.trans hαy'
    calc y * y = y⁻¹ * y := by rw [← this]
      _ = 1 := inv_mul_cancel y
  have hπy1 : π y = 1 := by
    rcases h.eq_one_or_eq_z_of_sq_eq_one hy2 with h1 | h1
    · rw [h1, map_one]
    · rw [h1]; exact (h.ker_iff z).mpr (Or.inr rfl)
  have hone : (π y : Perm (Fin 7)) = 1 := by rw [hπy1]; rfl
  rw [hπy] at hone
  apply ha1
  have : (a : Perm (Fin 7))⁻¹ * σ * a = σ := by
    have h3 := congrArg (fun t => t * σ) hone
    simpa [mul_assoc] using h3
  exact this

theorem card_E (h : IsDoubleCoverA7 π z) : Nat.card E = 5040 := by
  have := QuaternionStructure.natCard_comap_eq π h.surjective ⊤
  rw [Subgroup.comap_top, Subgroup.card_top, Subgroup.card_top, h.card_ker, card_A7] at this
  omega

theorem mulAut_eq_one_of_centralizes_sylow (h : IsDoubleCoverA7 π z) (Q : Sylow 2 E)
    (α : MulAut E) (hα : ∀ x ∈ (Q : Subgroup E), α x = x) : α = 1 := by
  have hcard : Nat.card (D8.comap π) = 2 ^ (Nat.card E).factorization 2 := by
    rw [QuaternionStructure.natCard_comap_eq π h.surjective D8, h.card_ker, card_D8, h.card_E,
      Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ : Sylow 2 E := Sylow.ofCard (D8.comap π) hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P₀ Q
  have hQ : ∀ x ∈ D8.comap π, g * x * g⁻¹ ∈ (Q : Subgroup E) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have h1 : (MulAut.conj g)⁻¹ * α * MulAut.conj g = 1 := by
    apply h.mulAut_eq_one_of_centralizes_D8
    intro x hx
    have h2 : ((MulAut.conj g)⁻¹ * α * MulAut.conj g) x = g⁻¹ * α (g * x * g⁻¹) * g := by
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [h2, hα _ (hQ x hx)]
    group
  calc α = MulAut.conj g * ((MulAut.conj g)⁻¹ * α * MulAut.conj g) * (MulAut.conj g)⁻¹ := by
        group
    _ = 1 := by rw [h1]; group

end Fixed

end IsDoubleCoverA7

end CFSG.ClassicalInvolution.Hat2A7
