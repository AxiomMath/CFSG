module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bQuot
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bAbs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup Module CFSG.LocalAnalysis.EvenBN.Tits.I21L

section Irr

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]

theorem submodule_eq_top_of_card (hQ : Nat.card Q = 2 ^ 8) {U : Submodule (ZMod 2) Q}
    (h : Nat.card U = 2 ^ 8) : U = ⊤ := by
  have h' : Nat.card U.toAddSubgroup = Nat.card Q := by
    rw [hQ]; exact h
  have := AddSubgroup.eq_top_of_card_eq U.toAddSubgroup h'
  ext v
  have hv : v ∈ U.toAddSubgroup := by rw [this]; trivial
  exact ⟨fun _ => trivial, fun _ => hv⟩

theorem submodule_eq_bot_of_card {U : Submodule (ZMod 2) Q} (h : Nat.card U = 1) : U = ⊥ := by
  have : Subsingleton U := (Nat.card_eq_one_iff_unique.1 h).1
  exact (Submodule.subsingleton_iff_eq_bot).1 this

variable {B : Type*} [Group B] (ρ : B →* (Q ≃ₗ[ZMod 2] Q))

theorem irreducible_of_modData (hQ : Nat.card Q = 2 ^ 8)
    {x t z h : B} (hx5 : x ^ 5 = 1) (hfix : ∀ v : Q, ρ x v = v → v = 0)
    (ht2 : t ^ 2 = 1) (htx : t * x = x * t) (hzx : z * x * z⁻¹ = x⁻¹)
    (hh : h * t * h⁻¹ = t * z)
    (U : Submodule (ZMod 2) Q) (hU : ∀ b : B, ∀ u ∈ U, ρ b u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbot, htop⟩ := hcon
  have hx5' : ρ x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hcases := card_invariant_cases hQ (ρ x) hx5' hfix U (fun u hu => hU x u hu)
  have h16 : Nat.card U = 2 ^ 4 := by
    rcases hcases with h1 | h1 | h1
    · exact absurd (submodule_eq_bot_of_card h1) hbot
    · exact h1
    · exact absurd (submodule_eq_top_of_card hQ h1) htop
  have ht2' : ρ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have htx' : ρ t * ρ x = ρ x * ρ t := by rw [← map_mul, ← map_mul, htx]
  have hT := trivial_of_commuting_involution hQ (ρ x) (ρ t) hx5' hfix ht2' htx' U
    (fun u hu => hU x u hu) (fun u hu => hU t u hu) h16
  have hTZ : ∀ u ∈ U, ρ t (ρ z u) = u := by
    intro u hu
    have h1 : ρ h⁻¹ u ∈ U := hU h⁻¹ u hu
    have h2 : ρ t (ρ h⁻¹ u) = ρ h⁻¹ u := hT _ h1
    have h3 : ρ (h * t * h⁻¹) u = u := by
      simp only [map_mul, LinearEquiv.mul_apply, h2]
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hh, map_mul] at h3
    exact h3
  have hZ : ∀ u ∈ U, ρ z u = u := by
    intro u hu
    have h1 : ρ z u ∈ U := hU z u hu
    have h2 := hT _ h1
    rw [hTZ u hu] at h2
    exact h2.symm
  have hX2 : ∀ u ∈ U, ρ x u = u := by
    intro u hu
    have h1 : ρ x u ∈ U := hU x u hu
    have h2 : ρ z (ρ x u) = ρ x u := hZ _ h1
    have h3 : ρ z (ρ x u) = (ρ x)⁻¹ (ρ z u) := by
      have : ρ z * ρ x = (ρ x)⁻¹ * ρ z := by
        have := congrArg ρ hzx
        simp only [map_mul, map_inv] at this
        calc ρ z * ρ x = ρ z * ρ x * (ρ z)⁻¹ * ρ z := by group
          _ = (ρ x)⁻¹ * ρ z := by rw [this]
      exact congrArg (fun f => f u) this
    rw [hZ u hu] at h3
    have h4 : ρ x u = (ρ x)⁻¹ u := h2.symm.trans h3
    have h5 : ρ x (ρ x u) = u := by
      conv_lhs => rw [h4]
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    have h6 : ∀ n : ℕ, (ρ x ^ (2 * n)) u = u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, LinearEquiv.mul_apply]
        have : (ρ x ^ 2) u = u := by rw [pow_two, LinearEquiv.mul_apply]; exact h5
        rw [this, ih]
    have h7 : (ρ x ^ (2 * 3)) u = u := h6 3
    have h8 : ρ x ^ (2 * 3) = ρ x := by
      rw [show 2 * 3 = 5 + 1 by norm_num, pow_add, hx5', one_mul, pow_one]
    rwa [h8] at h7
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra hall
    apply hbot
    ext v
    simp only [Submodule.mem_bot]
    exact ⟨fun hv => by_contra fun hne => hall ⟨v, hv, hne⟩, fun hv => hv ▸ U.zero_mem⟩
  exact hu0 (hfix u (hX2 u hu))

theorem normal_exponent_two_acts_trivially (hQ : Nat.card Q = 2 ^ 8)
    (hirr : ∀ U : Submodule (ZMod 2) Q, (∀ b : B, ∀ u ∈ U, ρ b u ∈ U) → U = ⊥ ∨ U = ⊤)
    (N : Subgroup B) [N.Normal] (hN2 : ∀ n ∈ N, n * n = 1) : ∀ n ∈ N, ρ n = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Submodule (ZMod 2) Q :=
    { carrier := {v | ∀ n ∈ N, ρ n v = v}
      add_mem' := fun {a b} ha hb n hn => by rw [map_add, ha n hn, hb n hn]
      zero_mem' := fun n _ => map_zero _
      smul_mem' := fun c v hv n hn => by rw [map_smul, hv n hn] }
  have hCinv : ∀ b : B, ∀ u ∈ C, ρ b u ∈ C := by
    intro b u hu n hn
    have hn' : b⁻¹ * n * b ∈ N := by
      have := Subgroup.Normal.conj_mem ‹N.Normal› n hn b⁻¹
      simpa using this
    have h1 : ρ (b⁻¹ * n * b) u = u := hu _ hn'
    have h2 : ρ n (ρ b u) = ρ b (ρ (b⁻¹ * n * b) u) := by
      simp only [map_mul, map_inv, LinearEquiv.mul_apply]
      rw [← LinearEquiv.mul_apply (ρ b) (ρ b)⁻¹, mul_inv_cancel]
      rfl
    rw [h2, h1]
  have hpg : IsPGroup 2 N := fun n => ⟨1, by
    have := hN2 n n.2
    simpa [pow_two] using (Subtype.ext this : n * n = 1)⟩
  letI : MulAction N Q := MulAction.compHom Q (ρ.comp N.subtype)
  have hmod := hpg.card_modEq_card_fixedPoints Q
  have hne : C ≠ ⊥ := by
    intro hC
    have hfp : MulAction.fixedPoints N Q = {0} := by
      ext v
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hv
        have : v ∈ C := fun n hn => hv ⟨n, hn⟩
        rw [hC] at this
        exact (Submodule.mem_bot _).1 this
      · rintro rfl ⟨n, hn⟩
        exact (map_zero (ρ n) : ρ n 0 = 0)
    have h1 : Nat.card (MulAction.fixedPoints N Q) = 1 := by
      rw [hfp]; simp
    rw [h1, hQ] at hmod
    have := hmod.symm
    simp [Nat.ModEq] at this
  have htop : C = ⊤ := by
    rcases hirr C hCinv with h | h
    · exact absurd h hne
    · exact h
  intro n hn
  ext v
  have : v ∈ C := by rw [htop]; trivial
  exact this n hn

end Irr


section Layer1

variable {V : Type*} [CommGroup V] [Finite V] [Fact (∀ a : V, a * a = 1)]
variable (Z : Subgroup V) (B : Subgroup (MulAut V)) (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z)

structure MData (x t z h : ↥B) : Prop where
  card : Nat.card (Additive (V ⧸ Z)) = 2 ^ 8
  x5 : x ^ 5 = 1
  xfix : ∀ v : V, (x : MulAut V) v * v⁻¹ ∈ Z → v ∈ Z
  tt : t * t = 1
  tx : t * x = x * t
  zx : z * x * z⁻¹ = x⁻¹
  ht : h * t * h⁻¹ = t * z

variable {Z B hB} {x t z h : ↥B}

theorem MData.finrank (M : MData Z B x t z h) : finrank (ZMod 2) (Additive (V ⧸ Z)) = 8 := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (V ⧸ Z))
  rw [Nat.card_zmod, M.card] at h1
  exact Nat.pow_right_injective (le_refl 2) h1.symm

theorem MData.fix (M : MData Z B x t z h) (q : Additive (V ⧸ Z))
    (hq : quotRep Z B hB x q = q) : q = 0 := by
  obtain ⟨v, rfl⟩ := cls_surjective Z q
  rw [quotRep_cls] at hq
  have h1 := (cls_eq_iff Z _ _).1 hq
  have h2 : (x : MulAut V) v * v⁻¹ = (((x : MulAut V) v)⁻¹ * v)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_comm]
  have h3 : v ∈ Z := M.xfix v (by rw [h2]; exact inv_mem h1)
  exact (cls_eq_zero_iff Z v).2 h3

theorem MData.orderOf_x (M : MData Z B x t z h) : orderOf (quotRep Z B hB x) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : quotRep Z B hB x ^ 5 = 1 := by rw [← map_pow, M.x5, map_one]
  refine orderOf_eq_prime h5 ?_
  intro h1
  have : ∀ q : Additive (V ⧸ Z), q = 0 := fun q => M.fix q (by rw [h1]; rfl)
  have hc : Nat.card (Additive (V ⧸ Z)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (this a).trans (this b).symm⟩, ⟨0⟩⟩
  rw [M.card] at hc
  norm_num at hc

theorem MData.hypM (M : MData Z B x t z h) : HypM (quotRep Z B hB) x t z h where
  dim := M.finrank
  ord_x := M.orderOf_x
  fix := fun q hq => M.fix q hq
  t_sq := by rw [← map_mul, M.tt, map_one]
  tx := M.tx
  zx := M.zx
  ht := M.ht


theorem MData.irreducible (M : MData Z B x t z h) (U : Submodule (ZMod 2) (Additive (V ⧸ Z)))
    (hU : ∀ b : ↥B, ∀ u ∈ U, quotRep Z B hB b u ∈ U) : U = ⊥ ∨ U = ⊤ :=
  irreducible_of_modData (quotRep Z B hB) M.card M.x5 (fun q hq => M.fix q hq)
    (by rw [pow_two]; exact M.tt) M.tx M.zx M.ht U hU

theorem MData.normal_trivial (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z) (M : MData Z B x t z h)
    (Wb : Subgroup ↥B) [Wb.Normal]
    (hW2 : ∀ w ∈ Wb, w * w = 1) : ∀ w ∈ Wb, ∀ v : V, v⁻¹ * (w : MulAut V) v ∈ Z := by
  intro w hw v
  have h1 := normal_exponent_two_acts_trivially (quotRep Z B hB) M.card
    (fun U hU => M.irreducible (hB := hB) U hU) Wb hW2 w hw
  have h2 : quotRep Z B hB w (cls Z v) = cls Z v := by rw [h1]; rfl
  rw [quotRep_cls] at h2
  exact (cls_eq_iff Z _ _).1 h2.symm

end Layer1


section Generic

theorem eq_or_top_of_simple_quotient {Γ : Type*} [Group Γ] (N K : Subgroup Γ) [N.Normal] [K.Normal]
    (hNK : N ≤ K) (hs : IsSimpleGroup (Γ ⧸ N)) : K = N ∨ K = ⊤ := by
  have hn : (K.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map ‹K.Normal› _ (QuotientGroup.mk'_surjective N)
  haveI := hn
  rcases hs.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' N)) with h | h
  · left
    refine le_antisymm (fun k hk => ?_) hNK
    have : (QuotientGroup.mk' N) k ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
    rw [h] at this
    exact (QuotientGroup.eq_one_iff k).1 (Subgroup.mem_bot.1 this)
  · right
    refine eq_top_iff.2 fun g _ => ?_
    have : (QuotientGroup.mk' N) g ∈ K.map (QuotientGroup.mk' N) := by rw [h]; trivial
    obtain ⟨k, hk, hkg⟩ := this
    have h1 : k⁻¹ * g ∈ N := QuotientGroup.eq.1 hkg
    have : g = k * (k⁻¹ * g) := by group
    rw [this]
    exact mul_mem hk (hNK h1)

theorem exists_equiv_range_of_ker_eq {Γ Γ' : Type*} [Group Γ] [Group Γ'] (φ : Γ →* Γ')
    (N : Subgroup Γ) [N.Normal] (hker : φ.ker = N) (A : Type*) [Group A] (e : Γ ⧸ N ≃* A) :
    Nonempty (φ.range ≃* A) :=
  ⟨(QuotientGroup.quotientKerEquivRange φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩

end Generic


section Branches

variable {V : Type*} [CommGroup V] [Finite V] [Fact (∀ a : V, a * a = 1)]
variable {Z : Subgroup V} {B : Subgroup (MulAut V)} {hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z}
variable {x t z h : ↥B}

@[expose] def A6Concl {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type*} [Group B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) (x t : B') : Prop :=
  ∃ V₁ V₂ : Submodule (ZMod 2) Q, finrank (ZMod 2) V₁ = 4 ∧ IsCompl V₁ V₂ ∧
    V₂ = V₁.map (ρ t : Q →ₗ[ZMod 2] Q) ∧
    (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, Stable g V₁ ∧ Stable g V₂) ∧
    (∀ U : Submodule (ZMod 2) Q, U ≤ V₁ →
      (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, Stable g U) → U = ⊥ ∨ U = V₁) ∧
    (∀ U : Submodule (ZMod 2) Q, U ≤ V₂ →
      (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, Stable g U) → U = ⊥ ∨ U = V₂) ∧
    (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, (∀ v ∈ V₁, g v = v) → g = 1) ∧
    (∀ g ∈ (normalClosure ({x} : Set B')).map ρ, (∀ v ∈ V₂, g v = v) → g = 1)

theorem MData.ker_inf_eq (M : MData Z B x t z h) (Wb : Subgroup ↥B) [Wb.Normal]
    (hWtriv : ∀ w ∈ Wb, quotRep Z B hB w = 1)
    (hWJ : Wb ≤ normalClosure ({x} : Set ↥B))
    (hs : IsSimpleGroup (↥(normalClosure ({x} : Set ↥B)) ⧸
      Wb.subgroupOf (normalClosure ({x} : Set ↥B)))) :
    (quotRep Z B hB).ker ⊓ normalClosure ({x} : Set ↥B) = Wb := by
  set Jb := normalClosure ({x} : Set ↥B) with hJb
  set K := (quotRep Z B hB).ker with hK
  have hWK : Wb ≤ K := fun w hw => (MonoidHom.mem_ker).2 (hWtriv w hw)
  have hxJ : x ∈ Jb := Subgroup.subset_normalClosure rfl
  have h1 : K.subgroupOf Jb = Wb.subgroupOf Jb ∨ K.subgroupOf Jb = ⊤ :=
    eq_or_top_of_simple_quotient (Wb.subgroupOf Jb) (K.subgroupOf Jb)
      (fun w hw => Subgroup.mem_subgroupOf.2 (hWK (Subgroup.mem_subgroupOf.1 hw))) hs
  rcases h1 with h1 | h1
  · refine le_antisymm (fun k hk => ?_) (fun w hw => ⟨hWK hw, hWJ hw⟩)
    have : (⟨k, hk.2⟩ : ↥Jb) ∈ K.subgroupOf Jb := Subgroup.mem_subgroupOf.2 hk.1
    rw [h1] at this
    exact Subgroup.mem_subgroupOf.1 this
  · exfalso
    have : (⟨x, hxJ⟩ : ↥Jb) ∈ K.subgroupOf Jb := by rw [h1]; trivial
    have hx1 : quotRep Z B hB x = 1 := (MonoidHom.mem_ker).1 (Subgroup.mem_subgroupOf.1 this)
    have := M.orderOf_x (hB := hB)
    rw [hx1, orderOf_one] at this
    omega


theorem MData.range_equiv (M : MData Z B x t z h) (Wb : Subgroup ↥B) [Wb.Normal]
    (hWtriv : ∀ w ∈ Wb, quotRep Z B hB w = 1)
    (hWJ : Wb ≤ normalClosure ({x} : Set ↥B))
    (A : Type*) [Group A]
    (hs : IsSimpleGroup (↥(normalClosure ({x} : Set ↥B)) ⧸
      Wb.subgroupOf (normalClosure ({x} : Set ↥B))))
    (e : ↥(normalClosure ({x} : Set ↥B)) ⧸ Wb.subgroupOf (normalClosure ({x} : Set ↥B)) ≃* A) :
    Nonempty ((normalClosure ({x} : Set ↥B)).map (quotRep Z B hB) ≃* A) := by
  set Jb := normalClosure ({x} : Set ↥B) with hJb
  have hker := M.ker_inf_eq Wb hWtriv hWJ hs
  let φ : ↥Jb →* (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)) := (quotRep Z B hB).comp Jb.subtype
  have hφ : φ.ker = Wb.subgroupOf Jb := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker]
    simp [φ, Subgroup.mem_inf]
  have hrange : φ.range = Jb.map (quotRep Z B hB) := by
    simp only [φ, MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e'⟩ := exists_equiv_range_of_ker_eq φ (Wb.subgroupOf Jb) hφ A e
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans e'⟩


theorem card_toAddSubgroup_eq {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (U : Submodule (ZMod 2) Q) {n : ℕ} (h : finrank (ZMod 2) U = n) :
    Nat.card U.toAddSubgroup = 2 ^ n := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
  rw [Nat.card_zmod, h] at h1
  exact (Nat.card_congr (Equiv.refl _)).trans h1

theorem A6_branch (M : MData Z B x t z h) (Wb : Subgroup ↥B) [Wb.Normal]
    (hW2 : ∀ w ∈ Wb, w * w = 1) (hWJ : Wb ≤ normalClosure ({x} : Set ↥B))
    (hA6 : Nonempty (↥(normalClosure ({x} : Set ↥B)) ⧸
      Wb.subgroupOf (normalClosure ({x} : Set ↥B)) ≃* alternatingGroup (Fin 6)))
    (core : HypM (quotRep Z B hB) x t z h →
      Nonempty ((normalClosure ({x} : Set ↥B)).map (quotRep Z B hB) ≃* alternatingGroup (Fin 6)) →
      A6Concl (quotRep Z B hB) x t) :
    ∃ V₁ V₂ : Subgroup V, Z ≤ V₁ ∧ Z ≤ V₂ ∧ V₁ ⊔ V₂ = ⊤ ∧ V₁ ⊓ V₂ = Z ∧
      (∀ σ ∈ normalClosure ({x} : Set ↥B), ∀ v ∈ V₁, (σ : MulAut V) v ∈ V₁) ∧
      (∀ σ ∈ normalClosure ({x} : Set ↥B), ∀ v ∈ V₂, (σ : MulAut V) v ∈ V₂) ∧
      V₂ = V₁.map ((t : MulAut V) : V →* V) ∧ Z.relIndex V₁ = 2 ^ 4 ∧ Z.relIndex V₂ = 2 ^ 4 ∧
      (∀ U : Subgroup V, Z ≤ U → U ≤ V₁ →
        (∀ σ ∈ normalClosure ({x} : Set ↥B), ∀ u ∈ U, (σ : MulAut V) u ∈ U) → U = Z ∨ U = V₁) ∧
      (∀ U : Subgroup V, Z ≤ U → U ≤ V₂ →
        (∀ σ ∈ normalClosure ({x} : Set ↥B), ∀ u ∈ U, (σ : MulAut V) u ∈ U) → U = Z ∨ U = V₂) ∧
      (∀ σ ∈ normalClosure ({x} : Set ↥B), (∀ v ∈ V₁, v⁻¹ * (σ : MulAut V) v ∈ Z) → σ ∈ Wb) ∧
      (∀ σ ∈ normalClosure ({x} : Set ↥B), (∀ v ∈ V₂, v⁻¹ * (σ : MulAut V) v ∈ Z) → σ ∈ Wb) := by
  classical
  set ρ := quotRep Z B hB with hρ
  set Jb := normalClosure ({x} : Set ↥B) with hJb
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨e⟩ := hA6
  have hs : IsSimpleGroup (↥Jb ⧸ Wb.subgroupOf Jb) := e.isSimpleGroup
  have hWtriv : ∀ w ∈ Wb, ρ w = 1 := normal_exponent_two_acts_trivially ρ M.card
    (fun U hU => M.irreducible (hB := hB) U hU) Wb hW2
  have hker := M.ker_inf_eq Wb hWtriv hWJ hs
  obtain ⟨e'⟩ := M.range_equiv Wb hWtriv hWJ _ hs e
  obtain ⟨V₁, V₂, hdim, hcompl, hV2, hstab, hirr1, hirr2, hfa1, hfa2⟩ := core M.hypM ⟨e'⟩
  have hBmem : ∀ σ ∈ B, ∀ z' ∈ Z, (σ : MulAut V) z' ∈ Z := fun σ hσ z' hz' =>
    (hB σ hσ) ▸ ⟨z', hz', rfl⟩
  have hlift : ∀ σ ∈ Jb, ∀ (U : Submodule (ZMod 2) (Additive (V ⧸ Z))),
      Stable (ρ σ) U → ∀ v ∈ liftAdd Z U.toAddSubgroup, (σ : MulAut V) v ∈ liftAdd Z U.toAddSubgroup := by
    intro σ hσ U hU v hv
    have h1 := hU _ hv
    rw [quotRep_cls] at h1
    exact h1
  refine ⟨liftAdd Z V₁.toAddSubgroup, liftAdd Z V₂.toAddSubgroup, le_liftAdd Z _, le_liftAdd Z _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← liftAdd_sup, ← toAddSubgroup_sup, hcompl.sup_eq_top, Submodule.top_toAddSubgroup,
      liftAdd_top]
  · rw [← liftAdd_inf, ← toAddSubgroup_inf, hcompl.inf_eq_bot, Submodule.bot_toAddSubgroup,
      liftAdd_bot]
  · intro σ hσ v hv
    exact hlift σ hσ V₁ ((hstab (ρ σ) (Subgroup.mem_map_of_mem _ hσ)).1) v hv
  · intro σ hσ v hv
    exact hlift σ hσ V₂ ((hstab (ρ σ) (Subgroup.mem_map_of_mem _ hσ)).2) v hv
  ·
    ext v
    simp only [Subgroup.mem_map, MonoidHom.coe_coe, mem_liftAdd, Submodule.mem_toAddSubgroup]
    constructor
    · intro hv
      rw [hV2] at hv
      obtain ⟨u, hu, hut⟩ := hv
      obtain ⟨v₀, rfl⟩ := cls_surjective Z u
      have h1 : quotRep Z B hB t (cls Z v₀) = cls Z v := hut
      rw [quotRep_cls] at h1
      have hz' : ((t : MulAut V) v₀)⁻¹ * v ∈ Z := (cls_eq_iff Z _ _).1 h1
      have hzz := hBmem ((t⁻¹ : ↥B) : MulAut V) (t⁻¹).2 _ hz'
      refine ⟨v₀ * ((t⁻¹ : ↥B) : MulAut V) (((t : MulAut V) v₀)⁻¹ * v), ?_, ?_⟩
      · rw [cls_mul, (cls_eq_zero_iff Z _).2 hzz, add_zero]; exact hu
      · have hinv : ∀ w : V, (t : MulAut V) (((t⁻¹ : ↥B) : MulAut V) w) = w := fun w => by
          have := congrArg (fun σ : ↥B => (σ : MulAut V) w) (mul_inv_cancel t)
          simpa using this
        rw [map_mul, hinv]; group
    · rintro ⟨v', hv', rfl⟩
      rw [hV2]
      refine ⟨cls Z v', hv', ?_⟩
      show quotRep Z B hB t (cls Z v') = cls Z _
      rw [quotRep_cls]
  · rw [relIndex_liftAdd, card_toAddSubgroup_eq V₁ hdim]
  · rw [relIndex_liftAdd]
    have hd2 : finrank (ZMod 2) V₂ = 4 := by
      rw [hV2, LinearEquiv.finrank_map_eq (ρ t) V₁, hdim]
    rw [card_toAddSubgroup_eq V₂ hd2]
  · intro U hZU hUV hUinv
    obtain ⟨U', hU'⟩ := exists_eq_liftAdd Z U hZU
    let Us : Submodule (ZMod 2) (Additive (V ⧸ Z)) := AddSubgroup.toZModSubmodule 2 U'
    have hUs : Us.toAddSubgroup = U' := rfl
    have hle : Us ≤ V₁ := by
      have : liftAdd Z U' ≤ liftAdd Z V₁.toAddSubgroup := by rw [hU']; exact hUV
      exact (liftAdd_le_iff Z).1 this
    have hstabU : ∀ g ∈ (normalClosure ({x} : Set ↥B)).map ρ, Stable g Us := by
      rintro g ⟨σ, hσ, rfl⟩ u hu
      obtain ⟨v, rfl⟩ := cls_surjective Z u
      have hv : v ∈ U := by rw [← hU']; exact hu
      have := hUinv σ hσ v hv
      rw [← hU'] at this
      show quotRep Z B hB σ (cls Z v) ∈ Us
      rw [quotRep_cls]
      exact this
    rcases hirr1 Us hle hstabU with h | h
    · left
      rw [← hU', ← hUs, h, Submodule.bot_toAddSubgroup, liftAdd_bot]
    · right
      rw [← hU', ← hUs, h]
  · intro U hZU hUV hUinv
    obtain ⟨U', hU'⟩ := exists_eq_liftAdd Z U hZU
    let Us : Submodule (ZMod 2) (Additive (V ⧸ Z)) := AddSubgroup.toZModSubmodule 2 U'
    have hUs : Us.toAddSubgroup = U' := rfl
    have hle : Us ≤ V₂ := by
      have : liftAdd Z U' ≤ liftAdd Z V₂.toAddSubgroup := by rw [hU']; exact hUV
      exact (liftAdd_le_iff Z).1 this
    have hstabU : ∀ g ∈ (normalClosure ({x} : Set ↥B)).map ρ, Stable g Us := by
      rintro g ⟨σ, hσ, rfl⟩ u hu
      obtain ⟨v, rfl⟩ := cls_surjective Z u
      have hv : v ∈ U := by rw [← hU']; exact hu
      have := hUinv σ hσ v hv
      rw [← hU'] at this
      show quotRep Z B hB σ (cls Z v) ∈ Us
      rw [quotRep_cls]
      exact this
    rcases hirr2 Us hle hstabU with h | h
    · left
      rw [← hU', ← hUs, h, Submodule.bot_toAddSubgroup, liftAdd_bot]
    · right
      rw [← hU', ← hUs, h]
  · intro σ hσ hv
    have hg : ρ σ ∈ (normalClosure ({x} : Set ↥B)).map ρ := Subgroup.mem_map_of_mem _ hσ
    have h1 : ρ σ = 1 := hfa1 _ hg (by
      intro u hu
      obtain ⟨v, rfl⟩ := cls_surjective Z u
      have hvV : v ∈ liftAdd Z V₁.toAddSubgroup := hu
      have := hv v hvV
      show quotRep Z B hB σ (cls Z v) = cls Z v
      rw [quotRep_cls]
      exact ((cls_eq_iff Z v _).2 this).symm)
    rw [← hker]
    exact ⟨(MonoidHom.mem_ker).2 h1, hσ⟩
  · intro σ hσ hv
    have hg : ρ σ ∈ (normalClosure ({x} : Set ↥B)).map ρ := Subgroup.mem_map_of_mem _ hσ
    have h1 : ρ σ = 1 := hfa2 _ hg (by
      intro u hu
      obtain ⟨v, rfl⟩ := cls_surjective Z u
      have hvV : v ∈ liftAdd Z V₂.toAddSubgroup := hu
      have := hv v hvV
      show quotRep Z B hB σ (cls Z v) = cls Z v
      rw [quotRep_cls]
      exact ((cls_eq_iff Z v _).2 this).symm)
    rw [← hker]
    exact ⟨(MonoidHom.mem_ker).2 h1, hσ⟩


@[expose] def E25Concl {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type*} [Group B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) (x t : B') : Prop :=
  Nat.card ((normalClosure ({x} : Set B')).map ρ) = 25 ∧
  ∃ V₁ V₂ : Submodule (ZMod 2) Q, finrank (ZMod 2) V₁ = 4 ∧ IsCompl V₁ V₂ ∧
    V₂ = V₁.map (ρ t : Q →ₗ[ZMod 2] Q) ∧
    ∃ K₁ K₂ : Subgroup (Q ≃ₗ[ZMod 2] Q),
      K₁ ≤ (normalClosure ({x} : Set B')).map ρ ∧ K₂ ≤ (normalClosure ({x} : Set B')).map ρ ∧
      K₁ ⊓ K₂ = ⊥ ∧ K₁ ⊔ K₂ = (normalClosure ({x} : Set B')).map ρ ∧
      Nat.card K₁ = 5 ∧ Nat.card K₂ = 5 ∧
      (∀ v : Q, v ∈ V₁ ↔ ∀ g ∈ K₁, g v = v) ∧ (∀ v : Q, v ∈ V₂ ↔ ∀ g ∈ K₂, g v = v)

@[expose] def centModSub (Z : Subgroup V) (J' : Subgroup ↥B) : Subgroup V where
  carrier := {v | ∀ σ ∈ J', v⁻¹ * (σ : MulAut V) v ∈ Z}
  mul_mem' := fun {a b} ha hb σ hσ => by
    have : (a * b)⁻¹ * (σ : MulAut V) (a * b) = (a⁻¹ * (σ : MulAut V) a) * (b⁻¹ * (σ : MulAut V) b) := by
      rw [map_mul, mul_inv, mul_mul_mul_comm]
    rw [this]; exact mul_mem (ha σ hσ) (hb σ hσ)
  one_mem' := fun σ _ => by simp
  inv_mem' := fun {a} ha σ hσ => by
    have : a⁻¹⁻¹ * (σ : MulAut V) a⁻¹ = (a⁻¹ * (σ : MulAut V) a)⁻¹ := by
      rw [map_inv, mul_inv, inv_inv]
    rw [this]; exact inv_mem (ha σ hσ)

theorem le_centModSub (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z) (J' : Subgroup ↥B) :
    Z ≤ centModSub Z J' := fun z' hz' σ _ => by
  have hz'' : (σ : MulAut V) z' ∈ Z := (hB σ σ.2) ▸ ⟨z', hz', rfl⟩
  exact mul_mem (inv_mem hz') hz''


theorem E25_branch (M : MData Z B x t z h) (Wb : Subgroup ↥B) [Wb.Normal]
    (hW2 : ∀ w ∈ Wb, w * w = 1) (hWJ : Wb ≤ normalClosure ({x} : Set ↥B))
    (hE : Nonempty (↥(normalClosure ({x} : Set ↥B)) ⧸
      Wb.subgroupOf (normalClosure ({x} : Set ↥B)) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (core : HypM (quotRep Z B hB) x t z h →
      (∀ a ∈ (normalClosure ({x} : Set ↥B)).map (quotRep Z B hB),
        ∀ b ∈ (normalClosure ({x} : Set ↥B)).map (quotRep Z B hB), a * b = b * a) →
      E25Concl (quotRep Z B hB) x t) :
    ∃ J₁ J₂ : Subgroup ↥B, Wb ≤ J₁ ∧ J₁ ≤ normalClosure ({x} : Set ↥B) ∧ Wb ≤ J₂ ∧
      J₂ ≤ normalClosure ({x} : Set ↥B) ∧
      (∀ σ ∈ normalClosure ({x} : Set ↥B), ∃ σ₁ ∈ J₁, ∃ σ₂ ∈ J₂, σ₁ * σ₂ = σ) ∧ J₁ ⊓ J₂ = Wb ∧
      Wb.relIndex J₁ = 5 ∧ Wb.relIndex J₂ = 5 ∧
      centModSub Z J₁ ⊔ centModSub Z J₂ = ⊤ ∧ centModSub Z J₁ ⊓ centModSub Z J₂ = Z ∧
      Z.relIndex (centModSub Z J₁) = 2 ^ 4 ∧ Z.relIndex (centModSub Z J₂) = 2 ^ 4 ∧
      centModSub Z J₂ = (centModSub Z J₁).map ((t : MulAut V) : V →* V) := by
  classical
  set ρ := quotRep Z B hB with hρ
  set Jb := normalClosure ({x} : Set ↥B) with hJb
  obtain ⟨e⟩ := hE
  have hWtriv : ∀ w ∈ Wb, ρ w = 1 := normal_exponent_two_acts_trivially ρ M.card
    (fun U hU => M.irreducible (hB := hB) U hU) Wb hW2
  have hWK : Wb ≤ ρ.ker := fun w hw => (MonoidHom.mem_ker).2 (hWtriv w hw)
  have hcomm : ∀ a b : ↥Jb, a * b * a⁻¹ * b⁻¹ ∈ Wb.subgroupOf Jb := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    apply e.injective
    rw [map_one]
    have h1 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : ↥Jb ⧸ Wb.subgroupOf Jb) =
        QuotientGroup.mk a * QuotientGroup.mk b * (QuotientGroup.mk a)⁻¹ *
          (QuotientGroup.mk b)⁻¹ := rfl
    rw [h1]
    simp only [map_mul, map_inv]
    rw [mul_comm (e (QuotientGroup.mk a)) (e (QuotientGroup.mk b))]
    group
  have hab : ∀ a ∈ Jb.map ρ, ∀ b ∈ Jb.map ρ, a * b = b * a := by
    rintro _ ⟨σ₁, hσ₁, rfl⟩ _ ⟨σ₂, hσ₂, rfl⟩
    have h2 : σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹ ∈ Wb := hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
    have h3 : ρ (σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹) = 1 := hWtriv _ h2
    simp only [map_mul, map_inv] at h3
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)
  obtain ⟨hcard, V₁, V₂, hdim, hcompl, hV2, K₁, K₂, hK₁, hK₂, hinf, hsup, hc1, hc2, hf1, hf2⟩ :=
    core M.hypM hab
  have hker : ρ.ker ⊓ Jb = Wb := by
    let φ : ↥Jb →* (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)) := ρ.comp Jb.subtype
    have hφrange : φ.range = Jb.map ρ := by
      simp only [φ, MonoidHom.range_comp, Subgroup.range_subtype]
    have hφker : φ.ker = ρ.ker.subgroupOf Jb := by
      ext k
      simp [φ, Subgroup.mem_subgroupOf]
    have hWle : Wb.subgroupOf Jb ≤ φ.ker := by
      rw [hφker]
      exact fun w hw => Subgroup.mem_subgroupOf.2 (hWK (Subgroup.mem_subgroupOf.1 hw))
    have h5 : Nat.card (Multiplicative (ZMod 5)) = 5 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hidx1 : (Wb.subgroupOf Jb).index = 25 := by
      rw [Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_prod, h5]
    have hidx2 : φ.ker.index = 25 := by
      rw [Subgroup.index_ker, hφrange, hcard]
    have hrel := Subgroup.relIndex_mul_index hWle
    rw [hidx1, hidx2] at hrel
    have hrel1 : (Wb.subgroupOf Jb).relIndex φ.ker = 1 := by omega
    have hle : φ.ker ≤ Wb.subgroupOf Jb := Subgroup.relIndex_eq_one.1 hrel1
    refine le_antisymm (fun g hg => ?_) (fun w hw => ⟨hWK hw, hWJ hw⟩)
    have : (⟨g, hg.2⟩ : ↥Jb) ∈ φ.ker := by
      rw [hφker]; exact Subgroup.mem_subgroupOf.2 hg.1
    exact Subgroup.mem_subgroupOf.1 (hle this)
  have hBmem : ∀ σ ∈ B, ∀ z' ∈ Z, (σ : MulAut V) z' ∈ Z := fun σ hσ z' hz' =>
    (hB σ hσ) ▸ ⟨z', hz', rfl⟩
  have hmap : ∀ K : Subgroup (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)),
      K ≤ Jb.map ρ → (K.comap ρ ⊓ Jb).map ρ = K := by
    intro K hK
    ext g
    constructor
    · rintro ⟨σ, ⟨hσK, _⟩, rfl⟩
      exact hσK
    · intro hg
      obtain ⟨σ, hσ, rfl⟩ := hK hg
      exact ⟨σ, ⟨hg, hσ⟩, rfl⟩
  have hrelIdx : ∀ K : Subgroup (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)),
      K ≤ Jb.map ρ → Nat.card K = 5 → Wb.relIndex (K.comap ρ ⊓ Jb) = 5 := by
    intro K hK hK5
    have h1 : (K.comap ρ ⊓ Jb) ≤ Jb := inf_le_right
    have h2 : Wb.relIndex (K.comap ρ ⊓ Jb) = ρ.ker.relIndex (K.comap ρ ⊓ Jb) := by
      rw [← hker, ← Subgroup.inf_relIndex_right (ρ.ker ⊓ Jb) (K.comap ρ ⊓ Jb),
        inf_assoc, inf_eq_right.2 h1, Subgroup.inf_relIndex_right]
    rw [h2, Subgroup.relIndex_ker, hmap K hK, hK5]
  have hmemJ : ∀ σ ∈ Jb, ∀ K : Subgroup (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z)),
      ρ σ ∈ K → σ ∈ K.comap ρ ⊓ Jb := fun σ hσ K hK => ⟨hK, hσ⟩
  have hVeq : ∀ (U : Submodule (ZMod 2) (Additive (V ⧸ Z)))
      (K : Subgroup (Additive (V ⧸ Z) ≃ₗ[ZMod 2] Additive (V ⧸ Z))), K ≤ Jb.map ρ →
      (∀ v, v ∈ U ↔ ∀ g ∈ K, g v = v) →
      liftAdd Z U.toAddSubgroup = centModSub Z (K.comap ρ ⊓ Jb) := by
    intro U K hK hU
    ext v
    rw [mem_liftAdd, Submodule.mem_toAddSubgroup, hU]
    constructor
    · intro h σ hσ
      have := h (ρ σ) hσ.1
      rw [quotRep_cls] at this
      exact (cls_eq_iff Z v _).1 this.symm
    · intro h g hg
      obtain ⟨σ, hσ, rfl⟩ := hK hg
      have := h σ ⟨hg, hσ⟩
      rw [← cls_eq_iff] at this
      show quotRep Z B hB σ (cls Z v) = cls Z v
      rw [quotRep_cls]
      exact this.symm
  have hWJ₁ : Wb ≤ K₁.comap ρ ⊓ Jb :=
    fun w hw => Subgroup.mem_inf.2 ⟨by rw [Subgroup.mem_comap, hWtriv w hw]; exact one_mem _, hWJ hw⟩
  have hWJ₂ : Wb ≤ K₂.comap ρ ⊓ Jb :=
    fun w hw => Subgroup.mem_inf.2 ⟨by rw [Subgroup.mem_comap, hWtriv w hw]; exact one_mem _, hWJ hw⟩
  have hdecomp : ∀ σ ∈ Jb, ∃ σ₁ ∈ K₁.comap ρ ⊓ Jb, ∃ σ₂ ∈ K₂.comap ρ ⊓ Jb, σ₁ * σ₂ = σ := by
    intro σ hσ
    have h1 : ρ σ ∈ K₁ ⊔ K₂ := by rw [hsup]; exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨a, ha, b, hb, hab'⟩ := exists_mul_of_mem_sup_of_commute K₁ K₂
      (fun a ha b hb => hab a (hK₁ ha) b (hK₂ hb)) h1
    obtain ⟨σ₁, hσ₁, rfl⟩ := hK₁ ha
    obtain ⟨σ₂, hσ₂, rfl⟩ := hK₂ hb
    have h2 : (σ₁ * σ₂)⁻¹ * σ ∈ ρ.ker ⊓ Jb := by
      rw [Subgroup.mem_inf]
      refine ⟨(MonoidHom.mem_ker).2 ?_, mul_mem (inv_mem (mul_mem hσ₁ hσ₂)) hσ⟩
      rw [map_mul, map_inv, map_mul, hab']
      exact inv_mul_cancel _
    rw [hker] at h2
    refine ⟨σ₁, hmemJ σ₁ hσ₁ K₁ ha, σ₂ * ((σ₁ * σ₂)⁻¹ * σ), ?_, ?_⟩
    · exact mul_mem (hmemJ σ₂ hσ₂ K₂ hb) (hWJ₂ h2)
    · group
  have hinfW : (K₁.comap ρ ⊓ Jb) ⊓ (K₂.comap ρ ⊓ Jb) = Wb := by
    refine le_antisymm (fun σ hσ => ?_) (le_inf hWJ₁ hWJ₂)
    have h1 : ρ σ ∈ K₁ ⊓ K₂ := ⟨hσ.1.1, hσ.2.1⟩
    rw [hinf] at h1
    have h2 : ρ σ = 1 := Subgroup.mem_bot.1 h1
    rw [← hker]
    exact ⟨(MonoidHom.mem_ker).2 h2, hσ.1.2⟩
  have hV₁ := hVeq V₁ K₁ hK₁ hf1
  have hV₂ := hVeq V₂ K₂ hK₂ hf2
  have hd2 : finrank (ZMod 2) V₂ = 4 := by
    rw [hV2, LinearEquiv.finrank_map_eq (ρ t) V₁, hdim]
  refine ⟨K₁.comap ρ ⊓ Jb, K₂.comap ρ ⊓ Jb, hWJ₁, inf_le_right, hWJ₂, inf_le_right, hdecomp,
    hinfW, hrelIdx K₁ hK₁ hc1, hrelIdx K₂ hK₂ hc2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hV₁, ← hV₂, ← liftAdd_sup, ← toAddSubgroup_sup, hcompl.sup_eq_top,
      Submodule.top_toAddSubgroup, liftAdd_top]
  · rw [← hV₁, ← hV₂, ← liftAdd_inf, ← toAddSubgroup_inf, hcompl.inf_eq_bot,
      Submodule.bot_toAddSubgroup, liftAdd_bot]
  · rw [← hV₁, relIndex_liftAdd, card_toAddSubgroup_eq V₁ hdim]
  · rw [← hV₂, relIndex_liftAdd, card_toAddSubgroup_eq V₂ hd2]
  · rw [← hV₁, ← hV₂]
    ext v
    simp only [Subgroup.mem_map, MonoidHom.coe_coe, mem_liftAdd, Submodule.mem_toAddSubgroup]
    constructor
    · intro hv
      rw [hV2] at hv
      obtain ⟨u, hu, hut⟩ := hv
      obtain ⟨v₀, rfl⟩ := cls_surjective Z u
      have h1 : quotRep Z B hB t (cls Z v₀) = cls Z v := hut
      rw [quotRep_cls] at h1
      have hz' : ((t : MulAut V) v₀)⁻¹ * v ∈ Z := (cls_eq_iff Z _ _).1 h1
      have hzz := hBmem ((t⁻¹ : ↥B) : MulAut V) (t⁻¹).2 _ hz'
      refine ⟨v₀ * ((t⁻¹ : ↥B) : MulAut V) (((t : MulAut V) v₀)⁻¹ * v), ?_, ?_⟩
      · rw [cls_mul, (cls_eq_zero_iff Z _).2 hzz, add_zero]; exact hu
      · have hinv : ∀ w : V, (t : MulAut V) (((t⁻¹ : ↥B) : MulAut V) w) = w := fun w => by
          have := congrArg (fun σ : ↥B => (σ : MulAut V) w) (mul_inv_cancel t)
          simpa using this
        rw [map_mul, hinv]; group
    · rintro ⟨v', hv', rfl⟩
      rw [hV2]
      refine ⟨cls Z v', hv', ?_⟩
      show quotRep Z B hB t (cls Z v') = cls Z _
      rw [quotRep_cls]

end Branches



@[expose] def A6CoreStmt : Prop :=
  ∀ {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type} [Group B'] [Finite B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) {x t z h : B'}, HypM ρ x t z h →
      Nonempty ((normalClosure ({x} : Set B')).map ρ ≃* alternatingGroup (Fin 6)) →
        A6Concl ρ x t

@[expose] def E25CoreStmt : Prop :=
  ∀ {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] {B' : Type} [Group B'] [Finite B']
    (ρ : B' →* (Q ≃ₗ[ZMod 2] Q)) {x t z h : B'}, HypM ρ x t z h →
      (∀ a ∈ (normalClosure ({x} : Set B')).map ρ, ∀ b ∈ (normalClosure ({x} : Set B')).map ρ,
        a * b = b * a) → E25Concl ρ x t

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
