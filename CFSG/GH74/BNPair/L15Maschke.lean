module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.GH74.BNPair

private theorem maschke_zmod {p : ℕ} [Fact p.Prime] {D : Type*} [Group D] [Finite D]
    (hD : Nat.Coprime p (Nat.card D)) {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : Representation (ZMod p) D M) (N : Submodule (ZMod p) M)
    (hN : ∀ d, ∀ x ∈ N, ρ d x ∈ N) :
    ∃ N' : Submodule (ZMod p) M, (∀ d, ∀ x ∈ N', ρ d x ∈ N') ∧ IsCompl N N' := by
  have : NeZero (Nat.card D : ZMod p) :=
    ⟨fun h => ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hD) ((ZMod.natCast_eq_zero_iff _ _).1 h)⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl
    (⟨N, fun d _ hx => hN d _ hx⟩ : Subrepresentation ρ)
  refine ⟨σ'.toSubmodule, fun d x hx => σ'.apply_mem_toSubmodule d hx, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hσ' ⊢
  exact ⟨congrArg Subrepresentation.toSubmodule hσ'.1,
    congrArg Subrepresentation.toSubmodule hσ'.2⟩

private theorem maschke_commGroup {p : ℕ} [Fact p.Prime] {D Q : Type*} [Group D] [Finite D]
    [CommGroup Q] (hD : Nat.Coprime p (Nat.card D)) (hQ : ∀ x : Q, x ^ p = 1)
    (ρ : D →* MulAut Q) (B : Subgroup Q) (hB : ∀ d, ∀ x ∈ B, ρ d x ∈ B) :
    ∃ C : Subgroup Q, (∀ d, ∀ x ∈ C, ρ d x ∈ C) ∧ B ⊓ C = ⊥ ∧ B ⊔ C = ⊤ := by
  let : Module (ZMod p) (Additive Q) :=
    AddCommGroup.zmodModule (n := p) fun x => Additive.toMul.injective (hQ (Additive.toMul x))
  let ρ' : Representation (ZMod p) D (Additive Q) :=
    { toFun := fun d => (AddMonoidHom.mk'
        (fun x : Additive Q => Additive.ofMul (ρ d (Additive.toMul x)))
        (fun x y => by simp)).toZModLinearMap p
      map_one' := by
        ext x
        simp
      map_mul' := fun s t => by
        ext x
        simp }
  obtain ⟨N', hN', hcompl⟩ := maschke_zmod hD ρ'
    (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup B)) (fun d x hx => hB d _ hx)
  refine ⟨{ carrier := {x | Additive.ofMul x ∈ N'}
            mul_mem' := fun {a b} ha hb => N'.add_mem ha hb
            one_mem' := N'.zero_mem
            inv_mem' := fun {a} ha => N'.neg_mem ha }, fun d x hx => hN' d _ hx, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact Additive.ofMul.injective (Submodule.disjoint_def.1 hcompl.disjoint _ hx.1 hx.2)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top (x := Additive.ofMul x))
    have hx : x = Additive.toMul y * Additive.toMul z := Additive.ofMul.injective hyz.symm
    rw [hx]
    exact Subgroup.mul_mem_sup hy hz

private theorem maschke_section {p : ℕ} [Fact p.Prime] {D G : Type*} [Group D] [Finite D]
    [Group G] (hD : Nat.Coprime p (Nat.card D)) (ρ : D →* MulAut G) (N W : Subgroup G)
    (hNW : N ≤ W) (hpow : ∀ x : G, x ^ p ∈ N) (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hρN : ∀ d, ∀ x ∈ N, ρ d x ∈ N) (hρW : ∀ d, ∀ x ∈ W, ρ d x ∈ W) :
    ∃ W' : Subgroup G, N ≤ W' ∧ (∀ d, ∀ x ∈ W', ρ d x ∈ W') ∧ W ⊔ W' = ⊤ ∧ W ⊓ W' = N := by
  have hNn : N.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by simp [mul_assoc]
    rw [this]
    exact N.mul_mem (hcomm g n) hn⟩
  let : CommGroup (G ⧸ N) :=
    { (inferInstance : Group (G ⧸ N)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        rename_i x y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have := hcomm y⁻¹ x⁻¹
        simpa [mul_assoc] using this }
  have hQ : ∀ x : G ⧸ N, x ^ p = 1 := fun x => by
    induction x using QuotientGroup.induction_on
    rename_i g
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hpow g
  have he : ∀ d : D, N.map (ρ d : G →* G) = N := fun d => by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hρN d x hx
    · intro x hx
      refine ⟨ρ d⁻¹ x, hρN d⁻¹ x hx, ?_⟩
      show ρ d (ρ d⁻¹ x) = x
      rw [← MulAut.mul_apply, ← map_mul ρ, mul_inv_cancel, map_one, MulAut.one_apply]
  let ρbar : D →* MulAut (G ⧸ N) :=
    { toFun := fun d => QuotientGroup.congr N N (ρ d) (he d)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on
        simp
      map_mul' := fun s t => by
        ext x
        induction x using QuotientGroup.induction_on
        simp }
  obtain ⟨C, hCinv, hinf, hsup⟩ := maschke_commGroup hD hQ ρbar
    (W.map (QuotientGroup.mk' N)) (fun d x hx => by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨ρ d w, hρW d w hw, rfl⟩)
  have h1 : (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = W := by
    rw [QuotientGroup.comap_map_mk', sup_eq_right.2 hNW]
  refine ⟨C.comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_⟩
  · intro n hn
    simp [(QuotientGroup.eq_one_iff n).2 hn]
  · intro d x hx
    have := hCinv d _ hx
    simpa [ρbar] using this
  · calc W ⊔ C.comap (QuotientGroup.mk' N)
        = (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ⊔
            C.comap (QuotientGroup.mk' N) := by rw [h1]
      _ = ((W.map (QuotientGroup.mk' N)) ⊔ C).comap (QuotientGroup.mk' N) :=
          Subgroup.comap_sup_eq _ _ _ (QuotientGroup.mk'_surjective N)
      _ = ⊤ := by rw [hsup, Subgroup.comap_top]
  · calc W ⊓ C.comap (QuotientGroup.mk' N)
        = (W.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ⊓
            C.comap (QuotientGroup.mk' N) := by rw [h1]
      _ = ((W.map (QuotientGroup.mk' N)) ⊓ C).comap (QuotientGroup.mk' N) :=
          (Subgroup.comap_inf _ _ _).symm
      _ = N := by rw [hinf, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem exists_invariant_complement_interval
    {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {Q Φ D T : Subgroup X}
    (hΦQ : Φ ≤ Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Φ)
    (hpow : ∀ x ∈ Q, x ^ p ∈ Φ)
    (hD : Nat.Coprime p (Nat.card D))
    (hDQ : ∀ d ∈ D, ∀ x ∈ Q, d * x * d⁻¹ ∈ Q)
    (hDΦ : ∀ d ∈ D, ∀ x ∈ Φ, d * x * d⁻¹ ∈ Φ)
    (hΦT : Φ ≤ T) (hTQ : T ≤ Q) (hDT : ∀ d ∈ D, ∀ x ∈ T, d * x * d⁻¹ ∈ T) :
    ∃ N : Subgroup X, Φ ≤ N ∧ N ≤ Q ∧ (∀ d ∈ D, ∀ x ∈ N, d * x * d⁻¹ ∈ N) ∧
      T ⊔ N = Q ∧ T ⊓ N = Φ := by
  have hDnorm : D ≤ Subgroup.normalizer (Q : Set X) := fun d hd => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hDQ d hd n, fun hn => ?_⟩
    simpa [mul_assoc] using hDQ d⁻¹ (D.inv_mem hd) _ hn
  let ρ : D →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hDnorm)
  have hρ : ∀ (d : D) (k : Q), ((ρ d k : Q) : X) = (d : X) * k * (d : X)⁻¹ := fun d k => rfl
  obtain ⟨W, hΦW, hinv, hsup, hinf⟩ := maschke_section hD ρ (Φ.subgroupOf Q) (T.subgroupOf Q)
    (fun x hx => hΦT hx) (fun x => hpow x x.2) (fun x y => hcomm x x.2 y y.2)
    (fun d x hx => by rw [Subgroup.mem_subgroupOf, hρ]; exact hDΦ d d.2 x hx)
    (fun d x hx => by rw [Subgroup.mem_subgroupOf, hρ]; exact hDT d d.2 x hx)
  refine ⟨W.map Q.subtype, ?_, Subgroup.map_subtype_le W, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hΦQ hx⟩, hΦW hx, rfl⟩
  · rintro d hd _ ⟨k, hk, rfl⟩
    exact ⟨ρ ⟨d, hd⟩ k, hinv ⟨d, hd⟩ k hk, hρ ⟨d, hd⟩ k⟩
  · refine le_antisymm (sup_le hTQ (Subgroup.map_subtype_le W)) fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ T.subgroupOf Q ⊔ W := hsup ▸ Subgroup.mem_top _
    have hmap : x ∈ (T.subgroupOf Q ⊔ W).map Q.subtype := ⟨⟨x, hx⟩, hx', rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTQ] at hmap
  · have hmap := congrArg (Subgroup.map Q.subtype) hinf
    rwa [Subgroup.map_inf_eq _ _ _ Q.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTQ,
      Subgroup.map_subgroupOf_eq_of_le hΦQ] at hmap

end CFSG.GH74.BNPair
