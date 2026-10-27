module

public import CFSG.GroupTheory.LocalCores.Layer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.FixedSubgroup
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XModule

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open CFSG.LocalCores
open scoped Pointwise IsMulCommutative

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

private def threeSubgroups (ρ : X →* MulAut V) (V₁ V₂ : Subgroup V) (z : X) :
    Set (Subgroup V) :=
  {V₁, V₂, TauCeti.fixedSubgroup (ρ z).toMonoidHom}

private lemma threeSubgroups_finite (ρ : X →* MulAut V) (V₁ V₂ : Subgroup V) (z : X) :
    (threeSubgroups ρ V₁ V₂ z).Finite := by
  rw [threeSubgroups]
  exact Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _))

private noncomputable instance threeSubgroupsFintype (ρ : X →* MulAut V)
    (V₁ V₂ : Subgroup V) (z : X) :
    Fintype {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z} :=
  (threeSubgroups_finite ρ V₁ V₂ z).fintype

private def permOn (ρ : X →* MulAut V) : X →* Equiv.Perm (Subgroup V) :=
  (MulAction.toPermHom (MulAut V) (Subgroup V)).comp ρ

private lemma smul_subgroup_eq_map (σ : MulAut V) (U : Subgroup V) :
    σ • U = U.map σ.toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

private lemma apply_apply_self (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    ρ z (ρ z v) = v := by
  have h2 : ρ z * ρ z = 1 := by rw [← map_mul, h.mul_self, map_one]
  simpa using congrArg (fun f : MulAut V => f v) h2

private lemma V₁_ne_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₁ ≠ ⊥ := by
  intro hbot
  have hcard := h.card₁
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

private lemma V₂_ne_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₂ ≠ ⊥ := by
  intro hbot
  have hcard := h.card₂
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

private lemma nontrivial_V₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nontrivial V₁ := by
  haveI : Finite V₁ := Nat.finite_of_card_ne_zero (by rw [h.card₁]; norm_num)
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card₁]; norm_num)

private lemma V₁_ne_top (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₁ ≠ ⊤ := by
  intro htop
  have hle : V₂ ≤ V₁ := by rw [htop]; exact le_top
  have hbot : V₂ = ⊥ := by
    rw [← h.inf_eq_bot, inf_eq_right.mpr hle]
  exact V₂_ne_bot h hbot

private lemma V₂_ne_top (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₂ ≠ ⊤ := by
  intro htop
  have hle : V₁ ≤ V₂ := by rw [htop]; exact le_top
  have hbot : V₁ = ⊥ := by
    rw [← h.inf_eq_bot, inf_eq_left.mpr hle]
  exact V₁_ne_bot h hbot

private lemma V₁_ne_V₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : V₁ ≠ V₂ := by
  intro heq
  have hbot : V₁ = ⊥ := by
    rw [← h.inf_eq_bot, inf_eq_left.mpr heq.le]
  exact V₁_ne_bot h hbot

private lemma fixedSubgroup_inf (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    TauCeti.fixedSubgroup (ρ z).toMonoidHom ⊓ V₁ = ⊥ ∧
      TauCeti.fixedSubgroup (ρ z).toMonoidHom ⊓ V₂ = ⊥ := by
  constructor
  · rw [eq_bot_iff]
    intro v hv
    have hzV₂ : ρ z v ∈ V₂ := (h.swap v).mp hv.2
    have hv₂ : v ∈ V₂ := by rwa [show ρ z v = v from hv.1] at hzV₂
    exact (show v ∈ (⊥ : Subgroup V) from by
      rw [← h.inf_eq_bot]; exact ⟨hv.2, hv₂⟩)
  · rw [eq_bot_iff]
    intro v hv
    have hzV₁ : ρ z v ∈ V₁ := h.swap₂ hv.2
    have hv₁ : v ∈ V₁ := by rwa [show ρ z v = v from hv.1] at hzV₁
    exact (show v ∈ (⊥ : Subgroup V) from by
      rw [← h.inf_eq_bot]; exact ⟨hv₁, hv.2⟩)

private lemma fixedSubgroup_ne_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    TauCeti.fixedSubgroup (ρ z).toMonoidHom ≠ ⊥ := by
  haveI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  haveI : Nontrivial V₁ := nontrivial_V₁ h
  intro hbot
  obtain ⟨w, hw⟩ := exists_ne (1 : V₁)
  have hzz := apply_apply_self h
  have hwA : ((w : V) * ρ z w) ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom := by
    show ρ z ((w : V) * ρ z w) = (w : V) * ρ z w
    rw [map_mul, hzz]
    exact mul_comm _ _
  have hne : (w : V) * ρ z w ≠ 1 := by
    intro hprod
    have hwinv : ρ z w = (w : V)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have hw₂ : (w : V) ∈ V₂ := by
      have hmem : (w : V)⁻¹ ∈ V₂ := hwinv ▸ (h.swap w).mp w.2
      simpa using V₂.inv_mem hmem
    have hwbot : (w : V) ∈ (⊥ : Subgroup V) := by
      rw [← h.inf_eq_bot]
      exact ⟨w.2, hw₂⟩
    have hw1 : (w : V) = 1 := by simpa using hwbot
    exact hw (Subtype.ext hw1)
  have : (w : V) * ρ z w ∈ (⊥ : Subgroup V) := by rw [← hbot]; exact hwA
  exact hne (by simpa using this)

private lemma fixedSubgroup_ne_top (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    TauCeti.fixedSubgroup (ρ z).toMonoidHom ≠ ⊤ := by
  haveI : Nontrivial V₁ := nontrivial_V₁ h
  intro htop
  obtain ⟨w, hw⟩ := exists_ne (1 : V₁)
  have hwA : (w : V) ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom := by rw [htop]; trivial
  have hzV₂ : ρ z (w : V) ∈ V₂ := (h.swap w).mp w.2
  have hw₂ : (w : V) ∈ V₂ := by rwa [show ρ z (w : V) = (w : V) from hwA] at hzV₂
  have hwbot : (w : V) ∈ (⊥ : Subgroup V) := by
    rw [← h.inf_eq_bot]
    exact ⟨w.2, hw₂⟩
  have hw1 : (w : V) = 1 := by simpa using hwbot
  exact hw (Subtype.ext hw1)

private lemma fixedSubgroup_ne_V₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    TauCeti.fixedSubgroup (ρ z).toMonoidHom ≠ V₁ := by
  intro heq
  have hinf := (fixedSubgroup_inf h).1
  rw [heq] at hinf
  exact V₁_ne_bot h (by simpa [inf_idem] using hinf)

private lemma fixedSubgroup_ne_V₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    TauCeti.fixedSubgroup (ρ z).toMonoidHom ≠ V₂ := by
  intro heq
  have hinf := (fixedSubgroup_inf h).2
  rw [heq] at hinf
  exact V₂_ne_bot h (by simpa [inf_idem] using hinf)

private lemma threeSubgroups_ne_bot (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    ∀ S ∈ threeSubgroups ρ V₁ V₂ z, S ≠ ⊥ := by
  intro S hS hbot
  simp only [threeSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
  rcases hS with rfl | rfl | rfl
  · exact V₁_ne_bot h hbot
  · exact V₂_ne_bot h hbot
  · exact fixedSubgroup_ne_bot h hbot

private lemma threeSubgroups_ne_top (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    ∀ S ∈ threeSubgroups ρ V₁ V₂ z, S ≠ ⊤ := by
  intro S hS htop
  simp only [threeSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
  rcases hS with rfl | rfl | rfl
  · exact V₁_ne_top h htop
  · exact V₂_ne_top h htop
  · exact fixedSubgroup_ne_top h htop

private lemma threeSubgroups_card (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    Nat.card {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z} = 3 := by
  rw [Nat.card_coe_set_eq]
  have hV₁not : V₁ ∉ (insert V₂
      ({TauCeti.fixedSubgroup (ρ z).toMonoidHom} : Set (Subgroup V))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (heq | heq)
    · exact V₁_ne_V₂ h heq
    · exact fixedSubgroup_ne_V₁ h heq.symm
  have hV₂not : V₂ ∉ ({TauCeti.fixedSubgroup (ρ z).toMonoidHom} : Set (Subgroup V)) := by
    simp only [Set.mem_singleton_iff]
    intro heq
    exact fixedSubgroup_ne_V₂ h heq.symm
  rw [threeSubgroups]
  rw [Set.ncard_insert_of_notMem hV₁not, Set.ncard_insert_of_notMem hV₂not]
  simp

private theorem mapsTo_three (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {H : Subgroup X}
    (hHnorm : ∀ x ∈ H, ∀ g ∈ ⁅Q, Q⁆, x * g * x⁻¹ ∈ ⁅Q, Q⁆)
    {x : X} (hx : x ∈ H) {S : Subgroup V} (hS : S ∈ threeSubgroups ρ V₁ V₂ z) :
    S.map (ρ x).toMonoidHom ∈ threeSubgroups ρ V₁ V₂ z := by
  classical
  have hQ'leQ : ⁅Q, Q⁆ ≤ Q := by
    simpa using Subgroup.commutator_le_sup (H₁ := Q) (H₂ := Q)
  have hSinv : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ S, ρ g u ∈ S := by
    simp only [threeSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    rcases hS with rfl | rfl | rfl
    · intro g hg u hu
      exact h.apply_mem₁ (hQ'leQ hg) hu
    · intro g hg u hu
      exact h.apply_mem₂ (hQ'leQ hg) hu
    · intro g hg u hu
      have hgz : ρ g * ρ z = ρ z * ρ g := by
        have hcomm : g * z = z * g := h.mul_comm_of_mem (hQ'leQ hg)
        calc ρ g * ρ z = ρ (g * z) := (map_mul ρ g z).symm
          _ = ρ (z * g) := by rw [hcomm]
          _ = ρ z * ρ g := map_mul ρ z g
      show ρ z (ρ g u) = ρ g u
      calc ρ z (ρ g u) = (ρ z * ρ g) u := rfl
        _ = (ρ g * ρ z) u := by rw [hgz]
        _ = ρ g (ρ z u) := rfl
        _ = ρ g u := by rw [show ρ z u = u from hu]
  have hUinv : ∀ g ∈ ⁅Q, Q⁆, ∀ u ∈ S.map (ρ x).toMonoidHom,
      ρ g u ∈ S.map (ρ x).toMonoidHom := by
    intro g hg u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hg' : x⁻¹ * g * x ∈ ⁅Q, Q⁆ := by
      simpa using hHnorm x⁻¹ (H.inv_mem hx) g hg
    refine Subgroup.mem_map.mpr ⟨ρ (x⁻¹ * g * x) v, hSinv _ hg' v hv, ?_⟩
    calc ρ x (ρ (x⁻¹ * g * x) v) = (ρ x * ρ (x⁻¹ * g * x)) v := rfl
      _ = ρ (x * (x⁻¹ * g * x)) v := by rw [← map_mul]
      _ = ρ (g * x) v := by rw [show x * (x⁻¹ * g * x) = g * x by group]
      _ = (ρ g * ρ x) v := by rw [map_mul]
      _ = ρ g (ρ x v) := rfl
  rcases h.invariant_cases hUinv with hbot | hV₁ | hV₂ | hCV | htop
  · exfalso
    have hSbot : S = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := S) (f := (ρ x).toMonoidHom)
        (by simpa using (ρ x).injective)).mp hbot
    exact threeSubgroups_ne_bot h S hS hSbot
  · rw [hV₁]
    simp [threeSubgroups]
  · rw [hV₂]
    simp [threeSubgroups]
  · have hSA : S.map (ρ x).toMonoidHom = TauCeti.fixedSubgroup (ρ z).toMonoidHom := by
      ext v
      exact hCV v
    rw [hSA]
    simp [threeSubgroups]
  · exfalso
    have hStop : S = ⊤ := by
      apply (Subgroup.map_injective (f := (ρ x).toMonoidHom) (by simpa using (ρ x).injective))
      rw [htop, Subgroup.map_top_of_surjective _ (ρ x).surjective]
    exact threeSubgroups_ne_top h S hS hStop

private noncomputable def permHom (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (H : Subgroup X)
    (hHnorm : ∀ x ∈ H, ∀ g ∈ ⁅Q, Q⁆, x * g * x⁻¹ ∈ ⁅Q, Q⁆) :
    H →* Equiv.Perm {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z} := by
  letI : Fintype {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z} :=
    (threeSubgroups_finite ρ V₁ V₂ z).fintype
  exact
  { toFun := fun y =>
      (permOn ρ (y : X)).subtypePermOfFintype
        (fun S hS => mapsTo_three h hHnorm y.2 hS)
    map_one' := by
      refine Equiv.ext fun S => ?_
      apply Subtype.ext
      change (permOn ρ (1 : X)) S.1 = S.1
      rw [map_one]
      rfl
    map_mul' := by
      intro x y
      refine Equiv.ext fun S => ?_
      apply Subtype.ext
      change (permOn ρ ((x : X) * (y : X))) S.1 =
        ((permOn ρ (x : X) * permOn ρ (y : X)) S.1)
      rw [map_mul] }

private lemma left_eq_of_mul_eq_mul (hinf : V₁ ⊓ V₂ = ⊥) {a a' b b' : V}
    (ha : a ∈ V₁) (ha' : a' ∈ V₁) (hb : b ∈ V₂) (hb' : b' ∈ V₂)
    (heq : a * b = a' * b') : a = a' := by
  have h : b * b'⁻¹ = a⁻¹ * a' := by
    have h1 : a⁻¹ * (a * b) * b'⁻¹ = a⁻¹ * (a' * b') * b'⁻¹ := by rw [heq]
    have h2 : a⁻¹ * (a * b) * b'⁻¹ = b * b'⁻¹ := by group
    have h3 : a⁻¹ * (a' * b') * b'⁻¹ = a⁻¹ * a' := by
      group
    rw [← h2, h1, h3]
  have hmem₁ : a⁻¹ * a' ∈ V₁ := V₁.mul_mem (V₁.inv_mem ha) ha'
  have hmem₂ : b * b'⁻¹ ∈ V₂ := V₂.mul_mem hb (V₂.inv_mem hb')
  have hbot : a⁻¹ * a' ∈ (⊥ : Subgroup V) := by
    rw [← hinf]
    exact ⟨hmem₁, h ▸ hmem₂⟩
  have hone : a⁻¹ * a' = 1 := by simpa using hbot
  exact eq_of_inv_mul_eq_one hone

private lemma map_eq_self_of_forall_mem {σ : MulAut V} {U : Subgroup V}
    (h : ∀ v ∈ U, σ v ∈ U) (h' : ∀ v ∈ U, σ⁻¹ v ∈ U) :
    U.map σ.toMonoidHom = U := by
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    exact h u hu
  · intro v hv
    exact Subgroup.mem_map.mpr ⟨σ⁻¹ v, h' v hv, by simp⟩

private theorem mem_Q_of_permHom_eq_one (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    {H : Subgroup X}
    (hHnorm : ∀ x ∈ H, ∀ g ∈ ⁅Q, Q⁆, x * g * x⁻¹ ∈ ⁅Q, Q⁆)
    {x : X} (hx : x ∈ H)
    (hπ : permHom h H hHnorm ⟨x, hx⟩ = 1) : x ∈ Q := by
  classical
  haveI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  have hQ'leQ : ⁅Q, Q⁆ ≤ Q := by
    simpa using Subgroup.commutator_le_sup (H₁ := Q) (H₂ := Q)
  have hfix : ∀ S (hS : S ∈ threeSubgroups ρ V₁ V₂ z),
      S.map (ρ x).toMonoidHom = S := by
    intro S hS
    have h1 : (permHom h H hHnorm ⟨x, hx⟩ ⟨S, hS⟩ :
        {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z}) = ⟨S, hS⟩ := by
      rw [hπ]
      rfl
    have h2 := congrArg Subtype.val h1
    simpa [permHom, permOn, smul_subgroup_eq_map] using h2
  have hfix₁ : ∀ v ∈ V₁, ρ x v ∈ V₁ := by
    intro v hv
    have hmap := hfix V₁ (by simp [threeSubgroups])
    have hmem : ρ x v ∈ V₁.map (ρ x).toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hmap] at hmem
  have hfix₂ : ∀ v ∈ V₂, ρ x v ∈ V₂ := by
    intro v hv
    have hmap := hfix V₂ (by simp [threeSubgroups])
    have hmem : ρ x v ∈ V₂.map (ρ x).toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hmap] at hmem
  have hfixA : ∀ v ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom,
      ρ x v ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom := by
    intro v hv
    have hmap := hfix (TauCeti.fixedSubgroup (ρ z).toMonoidHom) (by simp [threeSubgroups])
    have hmem : ρ x v ∈ (TauCeti.fixedSubgroup (ρ z).toMonoidHom).map (ρ x).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hmap] at hmem
  have hnorm₁ : ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v ∈ V₁, ρ x (ρ g v) = ρ g' (ρ x v) := by
    intro g hg
    refine ⟨x * g * x⁻¹, hHnorm x hx g hg, fun v _ => ?_⟩
    have hxg : x * g = (x * g * x⁻¹) * x := by group
    calc ρ x (ρ g v) = (ρ x * ρ g) v := rfl
      _ = ρ (x * g) v := by rw [map_mul ρ x g]
      _ = ρ ((x * g * x⁻¹) * x) v := by
          conv_lhs => rw [hxg]
      _ = (ρ (x * g * x⁻¹) * ρ x) v := by rw [map_mul ρ (x * g * x⁻¹) x]
      _ = ρ (x * g * x⁻¹) (ρ x v) := rfl
  have hnorm₂ : ∀ g ∈ ⁅Q, Q⁆, ∃ g' ∈ ⁅Q, Q⁆, ∀ v ∈ V₂, ρ x (ρ g v) = ρ g' (ρ x v) := by
    intro g hg
    refine ⟨x * g * x⁻¹, hHnorm x hx g hg, fun v _ => ?_⟩
    have hxg : x * g = (x * g * x⁻¹) * x := by group
    calc ρ x (ρ g v) = (ρ x * ρ g) v := rfl
      _ = ρ (x * g) v := by rw [map_mul ρ x g]
      _ = ρ ((x * g * x⁻¹) * x) v := by
          conv_lhs => rw [hxg]
      _ = (ρ (x * g * x⁻¹) * ρ x) v := by rw [map_mul ρ (x * g * x⁻¹) x]
      _ = ρ (x * g * x⁻¹) (ρ x v) := rfl
  obtain ⟨q₁, hq₁Q, hq₁⟩ := h.exists_mem_Q₁ (σ := ρ x) hfix₁ hnorm₁
  obtain ⟨q₂, hq₂Q, hq₂⟩ := h.exists_mem_Q₂ (σ := ρ x) hfix₂ hnorm₂
  have hzz := apply_apply_self h
  have hq₁₂ : ∀ v ∈ V₁, ρ q₁ v = ρ q₂ v := by
    intro v hv
    have hzv₂ : ρ z v ∈ V₂ := (h.swap v).mp hv
    have hcomm₁ : ρ q₁ (ρ z v) = ρ z (ρ q₁ v) := by
      have hcomm : q₁ * z = z * q₁ := h.mul_comm_of_mem hq₁Q
      calc ρ q₁ (ρ z v) = (ρ q₁ * ρ z) v := rfl
        _ = ρ (q₁ * z) v := by rw [map_mul]
        _ = ρ (z * q₁) v := by rw [hcomm]
        _ = (ρ z * ρ q₁) v := by rw [map_mul]
        _ = ρ z (ρ q₁ v) := rfl
    have hcomm₂ : ρ q₂ (ρ z v) = ρ z (ρ q₂ v) := by
      have hcomm : q₂ * z = z * q₂ := h.mul_comm_of_mem hq₂Q
      calc ρ q₂ (ρ z v) = (ρ q₂ * ρ z) v := rfl
        _ = ρ (q₂ * z) v := by rw [map_mul]
        _ = ρ (z * q₂) v := by rw [hcomm]
        _ = (ρ z * ρ q₂) v := by rw [map_mul]
        _ = ρ z (ρ q₂ v) := rfl
    have hwA : v * ρ z v ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom := by
      show ρ z (v * ρ z v) = v * ρ z v
      rw [map_mul, hzz]
      exact mul_comm _ _
    have hpres : ρ x (v * ρ z v) ∈ TauCeti.fixedSubgroup (ρ z).toMonoidHom := hfixA _ hwA
    have hxv : ρ x v = ρ q₁ v := hq₁ v hv
    have hxzv : ρ x (ρ z v) = ρ q₂ (ρ z v) := hq₂ _ hzv₂
    have hpres' : ρ z (ρ q₁ v * ρ q₂ (ρ z v)) = ρ q₁ v * ρ q₂ (ρ z v) := by
      have h1 : ρ x (v * ρ z v) = ρ q₁ v * ρ q₂ (ρ z v) := by
        rw [map_mul, hxv, hxzv]
      rwa [h1] at hpres
    rw [hcomm₂] at hpres'
    have hleft : ρ z (ρ q₁ v * ρ z (ρ q₂ v)) = ρ q₁ (ρ z v) * ρ q₂ v := by
      rw [map_mul, hzz, ← hcomm₁]
    rw [hleft] at hpres'
    have heq : ρ q₂ v * ρ q₁ (ρ z v) = ρ q₁ v * ρ z (ρ q₂ v) := by
      rw [mul_comm (ρ q₂ v)]
      exact hpres'
    have hsame : ρ q₂ v = ρ q₁ v :=
      left_eq_of_mul_eq_mul h.inf_eq_bot
        (h.apply_mem₁ hq₂Q hv)
        (h.apply_mem₁ hq₁Q hv)
        (h.apply_mem₂ hq₁Q hzv₂)
        ((h.swap (ρ q₂ v)).mp (h.apply_mem₁ hq₂Q hv))
        heq
    exact hsame.symm
  have hq_eq : q₁ = q₂ := by
    have hq12 : q₁⁻¹ * q₂ ∈ Q := Q.mul_mem (Q.inv_mem hq₁Q) hq₂Q
    have htriv : ∀ v ∈ V₁, ρ (q₁⁻¹ * q₂) v = v := by
      intro v hv
      calc ρ (q₁⁻¹ * q₂) v = ρ q₁⁻¹ (ρ q₂ v) := by rw [map_mul]; rfl
        _ = ρ q₁⁻¹ (ρ q₁ v) := by rw [← hq₁₂ v hv]
        _ = v := by simp
    exact eq_of_inv_mul_eq_one (h.eq_one_of_apply₁ hq12 htriv)
  have hxq : ρ x = ρ q₁ := by
    ext v
    have hv : v ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, map_mul]
    congr 1
    · exact hq₁ a ha
    · rw [hq₂ b hb, ← hq_eq]
  rw [h.injective hxq]
  exact hq₁Q

theorem XHyp.concl_of_le_centralizer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q ≠ ⊤) {K : Subgroup X} (hK : IsComponent K)
    (hKz : K ≤ centralizer ({z} : Set X)) : XConcl ρ Q V₁ V₂ z := by
  classical
  let α := {S : Subgroup V // S ∈ threeSubgroups ρ V₁ V₂ z}
  have hzz := apply_apply_self h
  have hQ'leQ : ⁅Q, Q⁆ ≤ Q := by
    simpa using Subgroup.commutator_le_sup (H₁ := Q) (H₂ := Q)
  let J : Subgroup X := layer X ⊓ centralizer ({z} : Set X)
  have hJle : J ≤ centralizer ({z} : Set X) := inf_le_right
  have hJn : ∀ c ∈ centralizer ({z} : Set X), ∀ y ∈ J, c * y * c⁻¹ ∈ J := by
    intro c hc y hy
    refine ⟨?_, ?_⟩
    · haveI : (layer X).Characteristic := layer_characteristic (G := X)
      exact (inferInstance : (layer X).Normal).conj_mem y hy.1 c
    · change c * y * c⁻¹ ∈ centralizer ({z} : Set X)
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hcz : Commute z c := hc z (Set.mem_singleton z)
      have hzy : Commute z y :=
        (Subgroup.mem_centralizer_iff.mp hy.2) z (Set.mem_singleton z)
      exact ((hcz.mul_right hzy).mul_right hcz.inv_right).eq
  have hK_eq_Q' : K = ⁅Q, Q⁆ := by
    rcases h.le_zpowers_or_le (Y := J) hJle hJn with hJz | hQ'J
    · exfalso
      have hKJ : K ≤ J := le_inf (component_le_layer hK) hKz
      have hKzpow : K ≤ zpowers z := hKJ.trans hJz
      haveI : IsMulCommutative K := by
        rw [isMulCommutative_iff]
        intro a b
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hKzpow a.2)
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hKzpow b.2)
        apply Subtype.ext
        change (a : X) * (b : X) = (b : X) * (a : X)
        rw [← hm, ← hn]
        exact zpow_mul_comm z m n
      haveI : Group.IsPerfect K := hK.1.1
      have hbot : K = ⊥ := Subgroup.eq_bot_of_subsingleton K
      exact (Subgroup.nontrivial_iff_ne_bot K).mp (isQuasisimple_nontrivial hK.1) hbot
    · have hKQ' : K ≤ ⁅Q, Q⁆ :=
        h.le_commutator_of_perfect (Y := K) hKz (Subgroup.isPerfect_iff.mp hK.1.1)
      have hQ'layer : ⁅Q, Q⁆ ≤ layer X := hQ'J.trans inf_le_left
      haveI : IsSimpleGroup ↥⁅Q, Q⁆ := h.isSimpleGroup_commutator
      haveI : (K.subgroupOf ⁅Q, Q⁆).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer
          (hQ'layer.trans (layer_le_normalizer hK))
      rcases Subgroup.Normal.eq_bot_or_eq_top (K.subgroupOf ⁅Q, Q⁆) with hbot | htop
      · have hdisj : Disjoint K ⁅Q, Q⁆ := Subgroup.subgroupOf_eq_bot.mp hbot
        exfalso
        have hKbot : K = ⊥ := by
          have hinf : K ⊓ ⁅Q, Q⁆ = ⊥ := hdisj.eq_bot
          rwa [inf_eq_left.mpr hKQ'] at hinf
        exact (Subgroup.nontrivial_iff_ne_bot K).mp (isQuasisimple_nontrivial hK.1) hKbot
      · have hQ'K : ⁅Q, Q⁆ ≤ K := Subgroup.subgroupOf_eq_top.mp htop
        exact le_antisymm hKQ' hQ'K
  have hperfect_bot : ∀ P : Subgroup X,
      P ≤ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) → ⁅P, P⁆ = P → P = ⊥ := by
    intro P hPle hPperf
    have hPnorm : ∀ p ∈ P, ∀ g ∈ ⁅Q, Q⁆, p * g * p⁻¹ ∈ ⁅Q, Q⁆ := by
      intro p hp g hg
      have hcomm : g * p = p * g := (Subgroup.mem_centralizer_iff.mp (hPle hp)) g hg
      rw [← hcomm]
      simpa using hg
    letI : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hPperf
    let πP := permHom h P hPnorm
    have hsign : Equiv.Perm.sign.comp πP = 1 := by
      apply MonoidHom.ext
      intro p
      have htop : (Equiv.Perm.sign.comp πP).ker = ⊤ := by
        rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := P)]
        exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp πP)
      have hpker : p ∈ (Equiv.Perm.sign.comp πP).ker := by
        rw [htop]
        exact Subgroup.mem_top p
      exact MonoidHom.mem_ker.mp hpker
    have hrange_alt : πP.range ≤ alternatingGroup α := by
      rintro _ ⟨p, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup]
      exact congrArg (fun f : P →* ℤˣ => f p) hsign
    haveI hcommAlt : IsMulCommutative (alternatingGroup α) := by
      apply alternatingGroup.isMulCommutative_of_card_le_three
      rw [threeSubgroups_card h]
    haveI : IsMulCommutative πP.range := by
      refine IsMulCommutative.of_comm ?_
      intro x y
      apply Subtype.ext
      change (x : Equiv.Perm α) * (y : Equiv.Perm α) =
        (y : Equiv.Perm α) * (x : Equiv.Perm α)
      exact congrArg Subtype.val
        (mul_comm' (⟨(x : Equiv.Perm α), hrange_alt x.2⟩ : alternatingGroup α)
          ⟨(y : Equiv.Perm α), hrange_alt y.2⟩)
    haveI : Group.IsPerfect πP.range := Group.IsPerfect.range (f := πP)
    have hrange : πP.range = ⊥ := by
      haveI : Subsingleton πP.range := inferInstance
      exact Subgroup.eq_bot_of_subsingleton πP.range
    apply le_bot_iff.mp
    intro p hp
    have hpval : πP ⟨p, hp⟩ = 1 := by
      have hmem : πP ⟨p, hp⟩ ∈ πP.range := ⟨⟨p, hp⟩, rfl⟩
      rw [hrange] at hmem
      simpa using hmem
    have hpQ : p ∈ Q := mem_Q_of_permHom_eq_one h hPnorm hp hpval
    have hpC : p ∈ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := hPle hp
    have hmem : p ∈ Q ⊓ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := ⟨hpQ, hpC⟩
    have hbot : p ∈ (⊥ : Subgroup X) := by
      rwa [h.centralizer_commutator] at hmem
    simpa using hbot
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    by_contra hmem
    have hKg : IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
      isComponent_map_mulEquiv (MulAut.conj g) hK
    have hne : K.map (MulAut.conj g).toMonoidHom ≠ K := by
      intro heq
      apply hmem
      have hmem' : (MulAut.conj g) n ∈ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
      rw [heq, MulAut.conj_apply] at hmem'
      exact hmem'
    have hcommute : ⁅K.map (MulAut.conj g).toMonoidHom, K⁆ = ⊥ := by
      rcases distinct_components_commute hKg hK with heq | h
      · exact absurd heq hne
      · exact h
    have hleC : K.map (MulAut.conj g).toMonoidHom ≤
        centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := by
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommute
      simpa only [hK_eq_Q'] using hle
    have hperf : ⁅K.map (MulAut.conj g).toMonoidHom,
        K.map (MulAut.conj g).toMonoidHom⁆ = K.map (MulAut.conj g).toMonoidHom :=
      Subgroup.isPerfect_iff.mp hKg.1.1
    have hbot := hperfect_bot (K.map (MulAut.conj g).toMonoidHom) hleC hperf
    exact (Subgroup.nontrivial_iff_ne_bot _).mp (isQuasisimple_nontrivial hKg.1) hbot
  have hQ'normal : (⁅Q, Q⁆ : Subgroup X).Normal := hK_eq_Q' ▸ hKnormal
  have hXnorm : ∀ x ∈ (⊤ : Subgroup X), ∀ g ∈ ⁅Q, Q⁆, x * g * x⁻¹ ∈ ⁅Q, Q⁆ := by
    intro x _ g hg
    exact hQ'normal.conj_mem g hg x
  let eTop : X →* ↥(⊤ : Subgroup X) :=
    { toFun := fun x => ⟨x, Subgroup.mem_top x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  let π : X →* Equiv.Perm α := (permHom h ⊤ hXnorm).comp eTop
  have hπker_le : π.ker ≤ Q := by
    intro x hx
    exact mem_Q_of_permHom_eq_one h hXnorm (Subgroup.mem_top x)
      (by simpa [π, eTop] using MonoidHom.mem_ker.mp hx)
  have hπker_ge : Q ≤ π.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    have hpres : ∀ r ∈ Q, ∀ S ∈ threeSubgroups ρ V₁ V₂ z, ∀ v ∈ S, ρ r v ∈ S := by
      intro r hr S hS v hv
      simp only [threeSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
      rcases hS with rfl | rfl | rfl
      · exact h.apply_mem₁ hr hv
      · exact h.apply_mem₂ hr hv
      · have hrz : ρ r * ρ z = ρ z * ρ r := by
          have hcomm : r * z = z * r := h.mul_comm_of_mem hr
          calc ρ r * ρ z = ρ (r * z) := (map_mul ρ r z).symm
            _ = ρ (z * r) := by rw [hcomm]
            _ = ρ z * ρ r := map_mul ρ z r
        show ρ z (ρ r v) = ρ r v
        calc ρ z (ρ r v) = (ρ z * ρ r) v := rfl
          _ = (ρ r * ρ z) v := by rw [hrz]
          _ = ρ r (ρ z v) := rfl
          _ = ρ r v := by rw [show ρ z v = v from hv]
    have hqfix : ∀ S ∈ threeSubgroups ρ V₁ V₂ z, S.map (ρ q).toMonoidHom = S := by
      intro S hS
      exact map_eq_self_of_forall_mem (hpres q hq S hS)
        (fun v hv => by simpa using hpres q⁻¹ (Q.inv_mem hq) S hS v hv)
    refine Equiv.ext fun S => ?_
    apply Subtype.ext
    change (permOn ρ q) S.1 = S.1
    simpa [permOn, MulAction.toPerm_apply, smul_subgroup_eq_map] using hqfix S.1 S.2
  have hker : π.ker = Q := le_antisymm hπker_le hπker_ge
  have hPermCard : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_perm, threeSubgroups_card h]
    decide
  have hQindex_range : Q.index = Nat.card π.range := by
    rw [← hker]
    exact Subgroup.index_ker π
  have hQindex_dvd : Q.index ∣ 6 := by
    rw [hQindex_range]
    exact ⟨π.range.index, by rw [Subgroup.card_mul_index, hPermCard]⟩
  have hCne_top : centralizer ({z} : Set X) ≠ ⊤ := by
    rw [h.centralizer_eq]
    exact hX
  have hQleC : Q ≤ centralizer ({z} : Set X) := by
    rw [h.centralizer_eq]
    exact le_sup_right
  have hQneC : Q ≠ centralizer ({z} : Set X) := by
    intro heq
    have hzC : z ∈ centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rw [← heq] at hzC
    exact h.z_not_mem hzC
  have hrel : 1 < Q.relIndex (centralizer ({z} : Set X)) := by
    rw [Subgroup.relIndex]
    apply Subgroup.one_lt_index_of_ne_top
    intro htop
    exact hQneC (le_antisymm hQleC (Subgroup.subgroupOf_eq_top.mp htop))
  have hCindex_gt : 1 < (centralizer ({z} : Set X)).index :=
    Subgroup.one_lt_index_of_ne_top hCne_top
  have h4 : 4 ≤ Q.index := by
    have hmul := Subgroup.relIndex_mul_index hQleC
    rw [← hmul]
    calc 4 = 2 * 2 := by norm_num
      _ ≤ Q.relIndex (centralizer ({z} : Set X)) *
            (centralizer ({z} : Set X)).index := Nat.mul_le_mul (by omega) (by omega)
  have hQindex : Q.index = 6 := by
    have hle : Q.index ≤ 6 := Nat.le_of_dvd (by norm_num) hQindex_dvd
    interval_cases hq : Q.index
    · norm_num at hQindex_dvd
    · norm_num at hQindex_dvd
    · rfl
  have hcardX : Nat.card X = 6 * 887040 := by
    have hcard := Subgroup.card_mul_index (H := Q) (G := X)
    rw [h.card_Q, hQindex] at hcard
    omega
  have hcardC : (centralizer ({z} : Set X)).index = 3 := by
    have hcard := Subgroup.card_mul_index (H := centralizer ({z} : Set X)) (G := X)
    rw [h.card_centralizer, hcardX] at hcard
    omega
  have hodd : ¬ 2 ∣ (centralizer ({z} : Set X)).index := by
    rw [hcardC]
    norm_num
  let a : α := ⟨V₁, by simp [threeSubgroups]⟩
  let b : α := ⟨V₂, by simp [threeSubgroups]⟩
  let c : α := ⟨TauCeti.fixedSubgroup (ρ z).toMonoidHom, by simp [threeSubgroups]⟩
  have hab : a ≠ b := by
    intro heq
    exact V₁_ne_V₂ h (congrArg Subtype.val heq)
  have hca : c ≠ a := by
    intro heq
    exact fixedSubgroup_ne_V₁ h (congrArg Subtype.val heq)
  have hcb : c ≠ b := by
    intro heq
    exact fixedSubgroup_ne_V₂ h (congrArg Subtype.val heq)
  have hmapz₁ : V₁.map (ρ z).toMonoidHom = V₂ := by
    apply le_antisymm
    · rintro v ⟨u, hu, rfl⟩
      exact (h.swap u).mp hu
    · intro v hv
      exact Subgroup.mem_map.mpr ⟨ρ z v, h.swap₂ hv, hzz v⟩
  have hmapz₂ : V₂.map (ρ z).toMonoidHom = V₁ := by
    apply le_antisymm
    · rintro v ⟨u, hu, rfl⟩
      exact h.swap₂ hu
    · intro v hv
      exact Subgroup.mem_map.mpr ⟨ρ z v, (h.swap v).mp hv, hzz v⟩
  have hmapzA : (TauCeti.fixedSubgroup (ρ z).toMonoidHom).map (ρ z).toMonoidHom =
      TauCeti.fixedSubgroup (ρ z).toMonoidHom := by
    apply le_antisymm
    · rintro v ⟨u, hu, rfl⟩
      show ρ z (ρ z u) = ρ z u
      rw [hzz u]
      exact (show ρ z u = u from hu).symm
    · intro v hv
      refine Subgroup.mem_map.mpr ⟨ρ z v, ?_, hzz v⟩
      show ρ z (ρ z v) = ρ z v
      rw [hzz v]
      exact (show ρ z v = v from hv).symm
  have hπa : (π z) a = b := by
    apply Subtype.ext
    change (permOn ρ z) V₁ = V₂
    simpa [permOn, MulAction.toPerm_apply, smul_subgroup_eq_map] using hmapz₁
  have hπb : (π z) b = a := by
    apply Subtype.ext
    change (permOn ρ z) V₂ = V₁
    simpa [permOn, MulAction.toPerm_apply, smul_subgroup_eq_map] using hmapz₂
  have hπc : (π z) c = c := by
    apply Subtype.ext
    change (permOn ρ z) (TauCeti.fixedSubgroup (ρ z).toMonoidHom) =
      TauCeti.fixedSubgroup (ρ z).toMonoidHom
    simpa [permOn, MulAction.toPerm_apply, smul_subgroup_eq_map] using hmapzA
  have hswap : π z = Equiv.swap a b := by
    ext S
    obtain ⟨U, hU⟩ := S
    simp only [threeSubgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hU
    rcases hU with hU | hU | hU
    · subst U
      have hSa : (⟨V₁, by simp [threeSubgroups]⟩ : α) = a := Subtype.ext rfl
      rw [hSa, hπa, Equiv.swap_apply_left]
    · subst U
      have hSb : (⟨V₂, by simp [threeSubgroups]⟩ : α) = b := Subtype.ext rfl
      rw [hSb, hπb, Equiv.swap_apply_right]
    · subst U
      have hSc : (⟨TauCeti.fixedSubgroup (ρ z).toMonoidHom,
        by simp [threeSubgroups]⟩ : α) = c := Subtype.ext rfl
      rw [hSc, hπc, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have hsignz : Equiv.Perm.sign (π z) = -1 := by
    rw [hswap]
    exact Equiv.Perm.sign_swap hab
  have hX₀index : ((Equiv.Perm.sign.comp π).ker).index = 2 := by
    have hcomp : (Equiv.Perm.sign.comp π).ker = (alternatingGroup α).comap π := by
      rw [← MonoidHom.comap_ker]
      rfl
    rw [hcomp]
    haveI : Nontrivial α := ⟨a, b, hab⟩
    rw [Subgroup.index_comap_of_surjective]
    · exact alternatingGroup.index_eq_two
    · rw [← MonoidHom.range_eq_top]
      apply Subgroup.eq_top_of_card_eq
      rw [← hQindex_range, hQindex, hPermCard]
  have hzX₀ : z ∉ (Equiv.Perm.sign.comp π).ker := by
    rw [MonoidHom.mem_ker]
    intro hz
    have h1 : Equiv.Perm.sign (π z) = 1 := hz
    rw [hsignz] at h1
    exact (by decide : (1 : ℤˣ) ≠ -1) h1.symm
  exact ⟨⟨(Equiv.Perm.sign.comp π).ker, inferInstance, hX₀index, hzX₀⟩,
    h.exists_sylow_of_odd hodd⟩

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
