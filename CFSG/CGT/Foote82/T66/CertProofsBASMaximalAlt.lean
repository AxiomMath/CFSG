module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle
import CFSG.Quasithin.H13.A6S138Ib
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltCent
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResTLat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open scoped Pointwise

namespace BASMaxAlt

theorem evenWeightOnes_eq_constWeight : evenWeightOnes 6 = CFSG.Quasithin.constWeight 6 := by
  ext x
  constructor
  · intro hx i j
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    rw [← hk]
    rfl
  · intro hx
    refine AddSubgroup.mem_addSubgroupOf.mpr (AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(((x : Fin 6 → ZMod 2) 0).val : ℤ), ?_⟩)
    funext i
    rw [Pi.smul_apply, allOnes, zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_zmod_val,
      hx 0 i]

@[expose] noncomputable def heartEquiv : altHeart 6 ≃+ CFSG.Quasithin.AltHeart 6 :=
  QuotientAddGroup.quotientAddEquivOfEq evenWeightOnes_eq_constWeight

@[expose] def wt2 (a b : Fin 6) (hab : a ≠ b) : evenWeight 6 :=
  ⟨fun i => if i = a ∨ i = b then 1 else 0, by
    show ∑ i : Fin 6, (if i = a ∨ i = b then (1 : ZMod 2) else 0) = 0
    revert a b
    decide⟩

open CFSG.Quasithin.H13 in
theorem heartAct_mul (σ τ : Perm (Fin 6)) (y : CFSG.Quasithin.AltHeart 6) :
    heartAct 6 (σ * τ) y = heartAct 6 σ (heartAct 6 τ y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rfl

open CFSG.Quasithin.H13 in
theorem heartAct_one (y : CFSG.Quasithin.AltHeart 6) : heartAct 6 1 y = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rfl

open CFSG.Quasithin.H13 in
theorem heartAct_injective (σ : Perm (Fin 6)) : Function.Injective (heartAct 6 σ) := by
  intro y z h
  have := congrArg (heartAct 6 σ⁻¹) h
  rwa [← heartAct_mul, ← heartAct_mul, inv_mul_cancel, heartAct_one, heartAct_one] at this

@[expose] def inv22 : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def inv222 : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

theorem cycleType_inv22 : inv22.cycleType = {2, 2} := by
  have hd : Perm.Disjoint (swap (0 : Fin 6) 1) (swap 2 3) := by
    intro x
    revert x
    decide
  rw [inv22, Perm.Disjoint.cycleType_mul hd, isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩,
    isSwap_iff_cycleType.mp ⟨2, 3, by decide, rfl⟩]
  rfl

theorem cycleType_inv222 : inv222.cycleType = {2, 2, 2} := by
  have hd : Perm.Disjoint (swap (0 : Fin 6) 1 * swap 2 3) (swap 4 5) := by
    intro x
    revert x
    decide
  rw [inv222, Perm.Disjoint.cycleType_mul hd, show swap (0 : Fin 6) 1 * swap 2 3 = inv22 from rfl,
    cycleType_inv22, isSwap_iff_cycleType.mp ⟨4, 5, by decide, rfl⟩]
  rfl

open CFSG.Quasithin.H13 in
theorem exists_two_comm_model (π₀ : Perm (Fin 6)) (hπ₀ : π₀ = inv22 ∨ π₀ = inv222) :
    ∃ y₁ y₂ : CFSG.Quasithin.AltHeart 6, heartAct 6 π₀ y₁ - y₁ ≠ 0 ∧ heartAct 6 π₀ y₂ - y₂ ≠ 0 ∧
      heartAct 6 π₀ y₁ - y₁ ≠ heartAct 6 π₀ y₂ - y₂ := by
  have key : ∀ v : evenWeight 6,
      (¬ ∀ i j : Fin 6, (v : Fin 6 → ZMod 2) i = (v : Fin 6 → ZMod 2) j) →
        (QuotientAddGroup.mk v : CFSG.Quasithin.AltHeart 6) ≠ 0 :=
    fun v hv h => hv ((QuotientAddGroup.eq_zero_iff v).mp h)
  refine ⟨QuotientAddGroup.mk (wt2 0 4 (by decide)), QuotientAddGroup.mk (wt2 2 4 (by decide)),
    ?_, ?_, ?_⟩
  · rw [heartAct_mk, ← QuotientAddGroup.mk_sub]
    apply key
    rcases hπ₀ with rfl | rfl <;> decide
  · rw [heartAct_mk, ← QuotientAddGroup.mk_sub]
    apply key
    rcases hπ₀ with rfl | rfl <;> decide
  · rw [heartAct_mk, heartAct_mk, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub, Ne,
      ← sub_eq_zero, ← QuotientAddGroup.mk_sub]
    apply key
    rcases hπ₀ with rfl | rfl <;> decide

open CFSG.Quasithin.H13 in
theorem exists_two_comm (π : Perm (Fin 6)) (hπ2 : π * π = 1) (hπ1 : π ≠ 1) (hsw : ¬ π.IsSwap) :
    ∃ y₁ y₂ : CFSG.Quasithin.AltHeart 6, heartAct 6 π y₁ - y₁ ≠ 0 ∧ heartAct 6 π y₂ - y₂ ≠ 0 ∧
      heartAct 6 π y₁ - y₁ ≠ heartAct 6 π y₂ - y₂ := by
  have hord : orderOf π = 2 := orderOf_eq_prime (by rw [pow_two, hπ2]) hπ1
  obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two : (orderOf π).Prime)
  rw [hord] at hn
  have hsum := sum_cycleType_le π
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  obtain ⟨π₀, hπ₀, hct⟩ : ∃ π₀ : Perm (Fin 6), (π₀ = inv22 ∨ π₀ = inv222) ∧
      π₀.cycleType = π.cycleType := by
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · exact absurd (isSwap_iff_cycleType.mpr hn) hsw
    · exact ⟨inv22, Or.inl rfl, by rw [cycleType_inv22, hn]; rfl⟩
    · exact ⟨inv222, Or.inr rfl, by rw [cycleType_inv222, hn]; rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hct)
  obtain ⟨y₁, y₂, h₁, h₂, h₁₂⟩ := exists_two_comm_model π₀ hπ₀
  have hconj : ∀ y, heartAct 6 π (heartAct 6 g y) - heartAct 6 g y =
      heartAct 6 g (heartAct 6 π₀ y - y) := by
    intro y
    rw [← hg, heartAct_mul, heartAct_mul, ← heartAct_mul g⁻¹ g, inv_mul_cancel, heartAct_one,
      map_sub]
  refine ⟨heartAct 6 g y₁, heartAct 6 g y₂, ?_, ?_, ?_⟩
  · rw [hconj]
    exact fun h => h₁ (heartAct_injective g (by rw [h, map_zero]))
  · rw [hconj]
    exact fun h => h₂ (heartAct_injective g (by rw [h, map_zero]))
  · rw [hconj, hconj]
    exact fun h => h₁₂ (heartAct_injective g h)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem smul_mem_commSpace {L : Subgroup (GLV V)} {ℓ : GLV V} (hℓ : ℓ ∈ L) {w : V}
    (hw : w ∈ commSpace L ⊤) : ℓ w ∈ commSpace L ⊤ := by
  have h : ℓ w = (ℓ w - w) + w := by abel
  rw [h]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨ℓ, hℓ, w, Submodule.mem_top, rfl⟩) hw

theorem conj_mem {L : Subgroup (GLV V)} {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) {k : GLV V} (hk : k ∈ L) :
    d * k * d⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp hd k).mp hk

theorem inv_apply_apply (d : GLV V) (u : V) : d⁻¹ (d u) = u := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem apply_inv_apply (d : GLV V) (u : V) : d (d⁻¹ u) = u := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem d_mem_commSpace {L : Subgroup (GLV V)} {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ commSpace L ⊤) :
    d w ∈ commSpace L ⊤ := by
  have hle : commSpace L ⊤ ≤ (commSpace L ⊤).comap (d : V →ₗ[ZMod 2] V) := by
    rw [commSpace, Submodule.span_le]
    rintro _ ⟨k, hk, u, -, rfl⟩
    refine Submodule.subset_span ⟨d * k * d⁻¹, conj_mem hd hk, d u, Submodule.mem_top, ?_⟩
    show d (k u - u) = (d * k * d⁻¹) (d u) - d u
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_apply_apply]
  exact hle hw

theorem d_mem_fixedSpace {L : Subgroup (GLV V)} {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) {v : V} (hv : v ∈ fixedSpace L) :
    d v ∈ fixedSpace L := by
  intro k hk
  have hk' : d⁻¹ * k * d ∈ L := by
    have := conj_mem (inv_mem hd) hk
    rwa [inv_inv] at this
  have h := hv _ hk'
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  calc k (d v) = d (d⁻¹ (k (d v))) := (apply_inv_apply d _).symm
    _ = d v := by rw [h]

theorem finrank_add_two_le [Finite V] {L : Subgroup (GLV V)} {M : Type} [AddCommGroup M]
    (β : ↥(commSpace L ⊤) →+ M) (hker : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L)
    (C : Submodule (ZMod 2) V) (u₁ u₂ : ↥(commSpace L ⊤)) (h₁ : (u₁ : V) ∈ C)
    (h₂ : (u₂ : V) ∈ C) (hb₁ : β u₁ ≠ 0) (hb₂ : β u₂ ≠ 0) (hb₁₂ : β u₁ ≠ β u₂) :
    Module.finrank (ZMod 2) ↥(tildeVBot L) + 2 ≤ Module.finrank (ZMod 2) ↥(C ⊔ tildeVBot L) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hz2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hcomb : ∀ a b : ZMod 2, a • (u₁ : V) + b • (u₂ : V) ∈ fixedSpace L → a = 0 ∧ b = 0 := by
    intro a b hab
    have hβ : β (a • u₁ + b • u₂) = 0 := (hker _).mpr hab
    rcases hz2 a with rfl | rfl <;> rcases hz2 b with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hβ
      exact absurd hβ hb₂
    · simp at hβ
      exact absurd hβ hb₁
    · simp only [one_smul, map_add] at hβ
      exfalso
      apply hb₁₂
      rw [eq_neg_of_add_eq_zero_left hβ, ← map_neg, ZModModule.neg_eq_self]
  have hli : LinearIndependent (ZMod 2) ![(u₁ : V), (u₂ : V)] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    exact hcomb a b (by rw [hab]; exact Submodule.zero_mem _)
  have hrange : Set.range ![(u₁ : V), (u₂ : V)] = {(u₁ : V), (u₂ : V)} :=
    Matrix.range_cons_cons_empty _ _ _
  have hP : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {(u₁ : V), (u₂ : V)}) = 2 := by
    rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]
  have hPT : Submodule.span (ZMod 2) {(u₁ : V), (u₂ : V)} ⊓ tildeVBot L = ⊥ := by
    rw [eq_bot_iff]
    intro v ⟨hvP, hvT⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hvP
    obtain ⟨ha, hb⟩ := hcomb a b hvT.1
    rw [ha, hb, zero_smul, zero_smul, add_zero]
    exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod 2) {(u₁ : V), (u₂ : V)}) (tildeVBot L)
  rw [hPT, finrank_bot, add_zero, hP] at hsum
  have hle : Submodule.span (ZMod 2) {(u₁ : V), (u₂ : V)} ⊔ tildeVBot L ≤ C ⊔ tildeVBot L := by
    refine sup_le_sup_right ?_ _
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact h₁
    · exact h₂
  have := Submodule.finrank_mono hle
  omega

open CFSG.Quasithin.H13 in
theorem exists_perm {L : Subgroup (GLV V)}
    {α : ↥L →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαi : Function.Injective α) {β : ↥(commSpace L ⊤) →+ altHeart 6}
    (hβs : Function.Surjective β)
    (hker : ∀ w : ↥(commSpace L ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace L)
    (hβℓ : ∀ (ℓ : ↥L) (w : ↥(commSpace L ⊤)) (x : evenWeight 6), β w = ↑x →
      β ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩ =
        ↑(evenWeightPerm (α ℓ : Perm (Fin 6)) x))
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1) :
    ∃ π : Perm (Fin 6), π * π = 1 ∧
      (∀ ℓ : ↥L, ((α ⟨d * ℓ * d⁻¹, conj_mem hd ℓ.2⟩ : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) = π * (α ℓ : Perm (Fin 6)) * π⁻¹) ∧
      ∀ w : ↥(commSpace L ⊤),
        heartEquiv (β ⟨d w, d_mem_commSpace hd w.2⟩) = heartAct 6 π (heartEquiv (β w)) := by
  let αe : ↥L ≃* alternatingGroup (Fin 6) := MulEquiv.ofBijective α ⟨hαi, hαs⟩
  let dU : ↥(commSpace L ⊤) →+ ↥(commSpace L ⊤) :=
    { toFun := fun w => ⟨d w, d_mem_commSpace hd w.2⟩
      map_zero' := Subtype.ext (map_zero d)
      map_add' := fun a b => Subtype.ext (map_add d (a : V) b) }
  have hdker : β.ker ≤ β.ker.comap dU := by
    intro w hw
    rw [AddSubgroup.mem_comap, AddMonoidHom.mem_ker, hker]
    rw [AddMonoidHom.mem_ker, hker] at hw
    exact d_mem_fixedSpace hd hw
  let e := QuotientAddGroup.quotientKerEquivOfSurjective β hβs
  let D : altHeart 6 →+ altHeart 6 :=
    e.toAddMonoidHom.comp ((QuotientAddGroup.map β.ker β.ker dU hdker).comp e.symm.toAddMonoidHom)
  have hD : ∀ w, D (β w) = β (dU w) := by
    intro w
    have h1 : e.symm (β w) = QuotientAddGroup.mk w := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    show e (QuotientAddGroup.map _ _ dU hdker (e.symm (β w))) = β (dU w)
    rw [h1, QuotientAddGroup.map_mk]
    rfl
  have hDinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := hβs y
    rw [hD, hker] at hy
    change d (w : V) ∈ fixedSpace L at hy
    rw [hker]
    have := d_mem_fixedSpace (inv_mem hd) hy
    rwa [show (d⁻¹ : GLV V) (d w) = w from inv_apply_apply d _] at this
  let cd : ↥L →* ↥L :=
    { toFun := fun ℓ => ⟨d * ℓ * d⁻¹, conj_mem hd ℓ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let ψ : A6Coc.Γ →* A6Coc.Γ := αe.toMonoidHom.comp (cd.comp αe.symm.toMonoidHom)
  have hψ : ∀ ℓ : ↥L, ψ (α ℓ) = α (cd ℓ) := fun ℓ => by
    show αe (cd (αe.symm (αe ℓ))) = α (cd ℓ)
    rw [MulEquiv.symm_apply_apply]
    rfl
  let φ : CFSG.Quasithin.AltHeart 6 →+ CFSG.Quasithin.AltHeart 6 :=
    heartEquiv.toAddMonoidHom.comp (D.comp heartEquiv.symm.toAddMonoidHom)
  have hφinj : Function.Injective φ := fun y z h =>
    heartEquiv.symm.injective (hDinj (heartEquiv.injective h))
  have hφψ : ∀ (x : A6Coc.Γ) (y : CFSG.Quasithin.AltHeart 6),
      φ (heartAct 6 (x : Perm (Fin 6)) y) = heartAct 6 (ψ x : Perm (Fin 6)) (φ y) := by
    intro x y
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨w, hw⟩ := hβs (QuotientAddGroup.mk z)
    obtain ⟨z', hz'⟩ := QuotientAddGroup.mk_surjective (β (dU w))
    obtain ⟨ℓ, rfl⟩ := αe.surjective x
    have h1 := hβℓ ℓ w z hw
    have h2 := hβℓ (cd ℓ) (dU w) z' hz'.symm
    have hdℓ : (⟨(cd ℓ : GLV V) (dU w : V), smul_mem_commSpace (cd ℓ).2 (dU w).2⟩ :
        ↥(commSpace L ⊤)) = dU ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩ := by
      apply Subtype.ext
      show (d * (ℓ : GLV V) * d⁻¹) (d (w : V)) = d ((ℓ : GLV V) (w : V))
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, inv_apply_apply]
    have hL1 : φ (heartAct 6 ((αe ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6))
        (QuotientAddGroup.mk z)) =
        heartEquiv (β ⟨(cd ℓ : GLV V) (dU w : V), smul_mem_commSpace (cd ℓ).2 (dU w).2⟩) := by
      show heartEquiv (D (QuotientAddGroup.mk (CFSG.Quasithin.permWeight 6
        ((αe ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) z))) = _
      have h3 : (QuotientAddGroup.mk (CFSG.Quasithin.permWeight 6
          ((αe ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) z) : altHeart 6) =
          β ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩ := h1.symm
      rw [h3, hD, ← hdℓ]
    have hR1 : φ (QuotientAddGroup.mk z) = heartEquiv (β (dU w)) := by
      show heartEquiv (D (QuotientAddGroup.mk z)) = _
      rw [← hw, hD]
    have hψ' : ψ (αe ℓ) = α (cd ℓ) := hψ ℓ
    rw [hL1, hR1, h2, ← hz', hψ']
    rfl
  obtain ⟨π, hπψ, hπφ⟩ := CFSG.Quasithin.H13.A6.A6Nrm.exists_perm_heart φ hφinj ψ hφψ
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hcdcd : ∀ ℓ : ↥L, cd (cd ℓ) = ℓ := fun ℓ => Subtype.ext (by
    show d * (d * (ℓ : GLV V) * d⁻¹) * d⁻¹ = ℓ
    rw [hdinv, ← mul_assoc, ← mul_assoc, hdd, one_mul, mul_assoc, hdd, mul_one])
  have hψψ : ∀ x, ψ (ψ x) = x := fun x => by
    show αe (cd (αe.symm (αe (cd (αe.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, hcdcd, MulEquiv.apply_symm_apply]
  have hπ2 : π * π = 1 := by
    apply CFSG.EvenSporadicStandard.M24Std.centralizer_alt_six
    intro a ha
    have h := congrArg (fun z : A6Coc.Γ => (z : Perm (Fin 6))) (hψψ ⟨a, ha⟩)
    simp only at h
    rw [hπψ, hπψ] at h
    calc π * π * a = π * (π * a * π⁻¹) * π⁻¹ * (π * π) := by group
      _ = a * (π * π) := by rw [h]
  refine ⟨π, hπ2, fun ℓ => ?_, fun w => ?_⟩
  · have h := hπψ (α ℓ)
    rw [hψ ℓ] at h
    exact h
  · rw [← hπφ]
    show heartEquiv (β (dU w)) = heartEquiv (D (heartEquiv.symm (heartEquiv (β w))))
    rw [AddEquiv.symm_apply_apply, hD]

end BASMaxAlt

open BASMaxAlt CFSG.Quasithin.H13

theorem basMaximal_altSix {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)) (hL : IsAltNaturalModule L 6)
    (hf : FaithfulTildeV L) (d : GLV V) (hd : d ∈ Subgroup.normalizer (L : Set (GLV V)))
    (hd2 : orderOf d = 2)
    (htv : Module.finrank (ZMod 2) ↥(BAS.tvComm L d) =
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1) :
    IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L) := by
  obtain ⟨α, hαs, β, hβs, hβk, hR⟩ := hL
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, pow_two] at h
    exact h
  have hker : ∀ w : ↥(commSpace L ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace L := by
    intro w
    rw [← AddMonoidHom.mem_ker, hβk]
    rfl
  have hβℓ : ∀ (ℓ : ↥L) (w : ↥(commSpace L ⊤)) (x : evenWeight 6), β w = ↑x →
      β ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩ =
        ↑(evenWeightPerm (α ℓ : Perm (Fin 6)) x) :=
    fun ℓ w x hx => hR ℓ w _ rfl x hx
  have hαi : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro ℓ hℓ
    rw [MonoidHom.mem_ker] at hℓ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hf ℓ ℓ.2 fun w hw => ?_
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β ⟨w, hw⟩)
    have h1 := hβℓ ℓ ⟨w, hw⟩ x hx.symm
    rw [hℓ] at h1
    have hx1 : evenWeightPerm ((1 : alternatingGroup (Fin 6)) : Perm (Fin 6)) x = x := rfl
    rw [hx1, hx] at h1
    have h2 := (hker (⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 hw⟩ - ⟨w, hw⟩)).mp
      (by rw [map_sub, h1, sub_self])
    exact h2
  let αe : ↥L ≃* alternatingGroup (Fin 6) := MulEquiv.ofBijective α ⟨hαi, hαs⟩
  obtain ⟨π, hπ2, hπψ, hπφ⟩ := exists_perm hαs hαi hβs hker hβℓ hd hdd
  let dU : ↥(commSpace L ⊤) →+ ↥(commSpace L ⊤) :=
    { toFun := fun w => ⟨d w, d_mem_commSpace hd w.2⟩
      map_zero' := Subtype.ext (map_zero d)
      map_add' := fun a b => Subtype.ext (map_add d (a : V) b) }
  set Cd := commSpace (Subgroup.zpowers d) (commSpace L ⊤) with hCd
  have hdU_mem : ∀ w : ↥(commSpace L ⊤), ((dU w - w : ↥(commSpace L ⊤)) : V) ∈ Cd := fun w =>
    Submodule.subset_span ⟨d, Subgroup.mem_zpowers d, w, w.2, rfl⟩
  have hβu : ∀ w : ↥(commSpace L ⊤), β (dU w - w) =
      heartEquiv.symm (heartAct 6 π (heartEquiv (β w)) - heartEquiv (β w)) := by
    intro w
    rw [map_sub, map_sub, ← hπφ w, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rfl
  have hπ1 : π ≠ 1 := by
    intro h1
    have hfix : ∀ w : ↥(commSpace L ⊤), ((dU w - w : ↥(commSpace L ⊤)) : V) ∈ tildeVBot L := by
      intro w
      refine ⟨(hker _).mp ?_, (dU w - w).2⟩
      rw [hβu, h1, BASMaxAlt.heartAct_one, sub_self, map_zero]
    have hle : Cd ≤ tildeVBot L := by
      rw [hCd, commSpace, Submodule.span_le]
      rintro _ ⟨k, ⟨n, rfl⟩, u, hu, rfl⟩
      have hdn : d ^ n = 1 ∨ d ^ n = d := by
        rw [← zpow_mod_orderOf, hd2]
        rcases Int.emod_two_eq_zero_or_one n with h | h
        · left
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
        · right
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rcases hdn with h | h
      · show (d ^ n) u - u ∈ tildeVBot L
        rw [h]
        simp
      · show (d ^ n) u - u ∈ tildeVBot L
        rw [h]
        exact hfix ⟨u, hu⟩
    have heq : BAS.tvComm L d = tildeVBot L := sup_eq_right.mpr hle
    rw [heq] at htv
    omega
  have hsw : π.IsSwap := by
    by_contra hsw
    obtain ⟨y₁, y₂, h₁, h₂, h₁₂⟩ := exists_two_comm π hπ2 hπ1 hsw
    obtain ⟨w₁, hw₁⟩ := hβs (heartEquiv.symm y₁)
    obtain ⟨w₂, hw₂⟩ := hβs (heartEquiv.symm y₂)
    have hb : ∀ (w : ↥(commSpace L ⊤)) (y : CFSG.Quasithin.AltHeart 6),
        β w = heartEquiv.symm y → β (dU w - w) = heartEquiv.symm (heartAct 6 π y - y) := by
      intro w y hwy
      rw [hβu, hwy, AddEquiv.apply_symm_apply]
    have hle := finrank_add_two_le β hker Cd (dU w₁ - w₁) (dU w₂ - w₂) (hdU_mem w₁) (hdU_mem w₂)
      (by rw [hb w₁ y₁ hw₁]; exact fun h => h₁ (heartEquiv.symm.injective (by rw [h, map_zero])))
      (by rw [hb w₂ y₂ hw₂]; exact fun h => h₂ (heartEquiv.symm.injective (by rw [h, map_zero])))
      (by rw [hb w₁ y₁ hw₁, hb w₂ y₂ hw₂]; exact fun h => h₁₂ (heartEquiv.symm.injective h))
    have : BAS.tvComm L d = Cd ⊔ tildeVBot L := rfl
    rw [← this] at hle
    omega
  obtain ⟨i, j, hij, hπij⟩ := hsw
  have hC : (L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L =
      (MulAction.stabilizer (alternatingGroup (Fin 6)) ({i, j} : Set (Fin 6))).map
        αe.symm.toMonoidHom := by
    rw [← Subgroup.comap_equiv_eq_map_symm']
    ext ℓ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCent.mem_stabilizer_swap_iff hij,
      Subgroup.mem_centralizer_singleton_iff]
    let cd : ↥L → ↥L := fun ℓ => ⟨d * ℓ * d⁻¹, conj_mem hd ℓ.2⟩
    have hl : ∀ ℓ : ↥L, (ℓ : GLV V) * d = d * ℓ ↔ cd ℓ = ℓ := fun ℓ => by
      constructor
      · intro h
        apply Subtype.ext
        show d * (ℓ : GLV V) * d⁻¹ = ℓ
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      · intro h
        have h' : d * (ℓ : GLV V) * d⁻¹ = ℓ := congrArg Subtype.val h
        calc (ℓ : GLV V) * d = d * (ℓ : GLV V) * d⁻¹ * d := by rw [h']
          _ = d * ℓ := by group
    rw [hl]
    have hαℓ : ((αe ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * swap i j =
        swap i j * ((αe ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ↔ α (cd ℓ) = αe ℓ := by
      show ((α ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * swap i j =
        swap i j * ((α ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ↔ α (cd ℓ) = α ℓ
      rw [← Subtype.coe_inj (a := α (cd ℓ)), hπψ ℓ, ← hπij]
      constructor
      · intro h
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      · intro h
        calc ((α ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * π =
            π * ((α ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * π⁻¹ * π := by rw [h]
          _ = π * ((α ℓ : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by group
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hαℓ]
    simp only [SetLike.coe_mem, true_and]
    exact ⟨fun h => by rw [h]; rfl, fun h => hαi h⟩
  rw [hC, show (MulAction.stabilizer (alternatingGroup (Fin 6)) ({i, j} : Set (Fin 6))).map
      αe.symm.toMonoidHom = αe.symm.mapSubgroup
        (MulAction.stabilizer (alternatingGroup (Fin 6)) ({i, j} : Set (Fin 6))) from rfl,
    OrderIso.isCoatom_iff]
  exact CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltCent.isCoatom_stabilizer_pair
    (by norm_num) hij
