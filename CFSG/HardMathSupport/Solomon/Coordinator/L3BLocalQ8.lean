module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns Matrix

set_option synthInstance.maxSize 2000 in
theorem l3b_q8_orbit : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3), A ^ 4 = 1 → A ^ 2 ≠ 1 →
    B * B = A ^ 2 → A * B = B * A ^ 3 → ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∀ w : Fin 2 → ZMod 3,
    w ≠ 0 → ∃ i : Fin 4, ∃ j : Fin 2, ((A ^ (i : ℕ)) * (B ^ (j : ℕ))) *ᵥ v = w := by
  decide +kernel

@[expose] noncomputable def l3bLam {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] :
    AddMonoid.End V →* Module.End (ZMod 3) V where
  toFun α := AddMonoidHom.toZModLinearMap 3 α
  map_one' := by ext; rfl
  map_mul' α β := by ext; rfl

theorem l3b_q8_transitive_add {V : Type*} [AddCommGroup V] [Finite V] (hc : Nat.card V = 9)
    (h3 : ∀ x : V, 3 • x = 0) (ρ : QuaternionGroup 2 →* AddMonoid.End V)
    (hρ : Function.Injective ρ) :
    ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ q : QuaternionGroup 2, ρ q u = v := by
  classical
  let _ : Module (ZMod 3) V := AddCommGroup.zmodModule h3
  have : Fintype V := Fintype.ofFinite V
  have hr : Module.finrank (ZMod 3) V = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [← Nat.card_eq_fintype_card, hc, ZMod.card] at h
    have h9 : (3 : ℕ) ^ 2 = 3 ^ Module.finrank (ZMod 3) V := by rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h9).symm
  let b := Module.finBasisOfFinrankEq (ZMod 3) V hr
  let M : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp ((l3bLam (V := V)).comp ρ)
  have hMinj : Function.Injective M := by
    intro q q' h
    apply hρ
    ext x
    have h1 : (l3bLam (V := V) (ρ q)) = l3bLam (ρ q') :=
      (LinearMap.toMatrixAlgEquiv b).injective h
    exact LinearMap.congr_fun h1 x
  have hMv : ∀ q x, M q *ᵥ b.repr x = b.repr (ρ q x) := by
    intro q x
    exact LinearMap.toMatrix_mulVec_repr b b (l3bLam (V := V) (ρ q)) x
  intro u v hu hv
  have hu' : (b.repr u : Fin 2 → ZMod 3) ≠ 0 := by
    intro h
    apply hu
    apply b.repr.injective
    rw [map_zero]
    ext i
    exact congrFun h i
  have hv' : (b.repr v : Fin 2 → ZMod 3) ≠ 0 := by
    intro h
    apply hv
    apply b.repr.injective
    rw [map_zero]
    ext i
    exact congrFun h i
  have hA4 : M (QuaternionGroup.a 1) ^ 4 = 1 := by
    rw [← map_pow]; exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1) ▸ map_one M
  have hA2 : M (QuaternionGroup.a 1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    have := hMinj (h.trans (map_one M).symm)
    exact absurd this (by decide)
  have hBB : M (QuaternionGroup.xa 0) * M (QuaternionGroup.xa 0) =
      M (QuaternionGroup.a 1) ^ 2 := by
    rw [← map_mul, ← map_pow]
    congr 1
  have hAB : M (QuaternionGroup.a 1) * M (QuaternionGroup.xa 0) =
      M (QuaternionGroup.xa 0) * M (QuaternionGroup.a 1) ^ 3 := by
    rw [← map_mul, ← map_pow, ← map_mul]
    congr 1
  obtain ⟨i, j, hij⟩ := l3b_q8_orbit _ _ hA4 hA2 hBB hAB _ hu' _ hv'
  refine ⟨(QuaternionGroup.a 1) ^ (i : ℕ) * (QuaternionGroup.xa 0) ^ (j : ℕ), ?_⟩
  apply b.repr.injective
  ext k
  have h1 := hMv ((QuaternionGroup.a 1) ^ (i : ℕ) * (QuaternionGroup.xa 0) ^ (j : ℕ)) u
  rw [map_mul, map_pow, map_pow] at h1
  rw [← h1, hij]

section Autizer

variable {G : Type*} [Group G]

theorem l3b_comm_iff (g h e : G) :
    e * (g⁻¹ * h) = (g⁻¹ * h) * e ↔ g * e * g⁻¹ = h * e * h⁻¹ := by
  constructor
  · intro H
    calc g * e * g⁻¹ = g * (e * (g⁻¹ * h)) * h⁻¹ := by group
      _ = g * ((g⁻¹ * h) * e) * h⁻¹ := by rw [H]
      _ = h * e * h⁻¹ := by group
  · intro H
    calc e * (g⁻¹ * h) = g⁻¹ * (g * e * g⁻¹) * h := by group
      _ = g⁻¹ * (h * e * h⁻¹) * h := by rw [H]
      _ = (g⁻¹ * h) * e := by group

theorem l3b_autizer_mk_eq_iff {J E : Subgroup G} (g h : ↥(J ⊓ Subgroup.normalizer (E : Set G))) :
    (QuotientGroup.mk g : autizer J E) = QuotientGroup.mk h ↔
      ∀ e ∈ E, (g : G) * e * (g : G)⁻¹ = (h : G) * e * (h : G)⁻¹ := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, H⟩ e he
    exact (l3b_comm_iff _ _ e).1 (H e he)
  · intro H
    refine ⟨(J.mul_mem (J.inv_mem g.2.1) h.2.1), fun e he => ?_⟩
    exact (l3b_comm_iff _ _ e).2 (H e he)

theorem l3b_mem_normalizer [Finite G] {E : Subgroup G} {g : G} (h : ∀ x ∈ E, g * x * g⁻¹ ∈ E) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : E.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := by
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    simpa using h1
  rw [← this]
  exact hy

@[expose] noncomputable def l3bToEnd (E : Type*) [CommGroup E] :
    MulAut E →* AddMonoid.End (Additive E) where
  toFun α := MonoidHom.toAdditive (α : E →* E)
  map_one' := by ext; rfl
  map_mul' α β := by ext; rfl

theorem l3bToEnd_injective (E : Type*) [CommGroup E] : Function.Injective (l3bToEnd E) := by
  intro α β h
  ext x
  exact congrArg (fun φ : AddMonoid.End (Additive E) => Additive.toMul (φ (Additive.ofMul x))) h

theorem l3b_q8_transitive [Finite G] {J E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 9)
    (hQ : ∃ f : QuaternionGroup 2 →* autizer J E, Function.Injective f) :
    ∀ u ∈ E, ∀ v ∈ E, u ≠ 1 → v ≠ 1 →
      ∃ g ∈ J ⊓ Subgroup.normalizer (E : Set G), g * u * g⁻¹ = v := by
  obtain ⟨f, hf⟩ := hQ
  have hcomm : IsMulCommutative E := hE.1
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => hcomm.is_comm.comm a b }
  let ρ1 : autizer J E →* MulAut ↥E :=
    QuotientGroup.lift _ (autAct J E) (by rw [← ker_autAct])
  have hρ1mk : ∀ g : ↥(J ⊓ Subgroup.normalizer (E : Set G)),
      ρ1 (QuotientGroup.mk g) = autAct J E g := fun g => rfl
  have hρ1 : Function.Injective ρ1 := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
        rw [hρ1mk, hρ1mk] at hab
        rw [QuotientGroup.eq]
        have : g⁻¹ * h ∈ (autAct J E).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
        rwa [ker_autAct] at this
  let ρ : QuaternionGroup 2 →* AddMonoid.End (Additive E) :=
    (l3bToEnd E).comp (ρ1.comp f)
  have hρ : Function.Injective ρ :=
    (l3bToEnd_injective E).comp (hρ1.comp hf)
  have hcardA : Nat.card (Additive E) = 9 := by
    rw [← hc]; exact Nat.card_congr Additive.toMul
  have h3 : ∀ x : Additive E, 3 • x = 0 := by
    intro x
    apply Additive.toMul.injective
    simp only [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hE.2 _ (Additive.toMul x).2)
  intro u hu v hv hu1 hv1
  obtain ⟨q, hq⟩ := l3b_q8_transitive_add hcardA h3 ρ hρ (Additive.ofMul ⟨u, hu⟩)
    (Additive.ofMul ⟨v, hv⟩)
    (fun h => hu1 (congrArg Subtype.val (Additive.ofMul.injective h)))
    (fun h => hv1 (congrArg Subtype.val (Additive.ofMul.injective h)))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (f q)
  refine ⟨g, g.2, ?_⟩
  have h1 : ρ q (Additive.ofMul ⟨u, hu⟩) = Additive.ofMul ⟨v, hv⟩ := hq
  have h2 : (autAct J E g ⟨u, hu⟩ : ↥E) = ⟨v, hv⟩ := by
    have : ρ q = l3bToEnd E (autAct J E g) := by
      show l3bToEnd E (ρ1 (f q)) = _
      rw [← hg, hρ1mk]
    rw [this] at h1
    exact Additive.ofMul.injective h1
  have := congrArg Subtype.val h2
  rw [autAct_coe] at this
  exact this

end Autizer

end CFSG.HardMathSupport.Solomon.Coordinator
