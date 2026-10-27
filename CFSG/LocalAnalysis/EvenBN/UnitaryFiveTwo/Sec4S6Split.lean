module

public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

open Subgroup

section Fix

variable {V : Type*} [Group V] {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut V)

@[expose] def fixSub (S : Subgroup Γ) : Subgroup V where
  carrier := {v | ∀ g ∈ S, ρ g v = v}
  one_mem' := fun g _ => map_one _
  mul_mem' := fun {a b} ha hb g hg => by rw [map_mul, ha g hg, hb g hg]
  inv_mem' := fun {a} ha g hg => by rw [map_inv, ha g hg]

theorem mem_fixSub {S : Subgroup Γ} {v : V} : v ∈ fixSub ρ S ↔ ∀ g ∈ S, ρ g v = v := Iff.rfl

theorem fixSub_anti {S T : Subgroup Γ} (h : S ≤ T) : fixSub ρ T ≤ fixSub ρ S :=
  fun _ hv g hg => hv g (h hg)

theorem ρ_inv_apply_self (g : Γ) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem ρ_apply_inv_self (g : Γ) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem ρ_conj_apply (g s : Γ) (v : V) : ρ (g * s * g⁻¹) v = ρ g (ρ s (ρ g⁻¹ v)) := by
  simp only [map_mul, MulAut.mul_apply]

@[expose] def stabSub (v : V) : Subgroup Γ where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a * b) v = v
    rw [map_mul, MulAut.mul_apply]
    change ρ b v = v at hb
    change ρ a v = v at ha
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a v = v at ha
    change ρ a⁻¹ v = v
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := ρ_inv_apply_self ρ a v

theorem fixSub_sup (S T : Subgroup Γ) : fixSub ρ (S ⊔ T) = fixSub ρ S ⊓ fixSub ρ T := by
  apply le_antisymm
  · exact le_inf (fixSub_anti ρ le_sup_left) (fixSub_anti ρ le_sup_right)
  · intro v hv
    obtain ⟨hS, hT⟩ := Subgroup.mem_inf.1 hv
    have : S ⊔ T ≤ stabSub ρ v := sup_le (fun g hg => hS g hg) (fun g hg => hT g hg)
    exact fun g hg => this hg

theorem fixSub_map_conj (S : Subgroup Γ) (g : Γ) :
    fixSub ρ (S.map (MulAut.conj g).toMonoidHom) = (fixSub ρ S).map (ρ g).toMonoidHom := by
  ext v
  rw [Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨ρ g⁻¹ v, fun s hs => ?_, ρ_apply_inv_self ρ g v⟩
    have h1 := h (g * s * g⁻¹) ⟨s, hs, by simp [MulAut.conj_apply]⟩
    rw [ρ_conj_apply] at h1
    have h2 := congrArg (ρ g⁻¹) h1
    rwa [ρ_inv_apply_self] at h2
  · rintro ⟨w, hw, rfl⟩ x ⟨s, hs, rfl⟩
    show ρ (g * s * g⁻¹) (ρ g w) = ρ g w
    rw [ρ_conj_apply, ρ_inv_apply_self, hw s hs]

theorem ρ_mem_fixSub_of_comm {S : Subgroup Γ} {g : Γ} (hg : ∀ s ∈ S, s * g = g * s) {v : V}
    (hv : v ∈ fixSub ρ S) : ρ g v ∈ fixSub ρ S := by
  intro s hs
  rw [← MulAut.mul_apply, ← map_mul, hg s hs, map_mul, MulAut.mul_apply, hv s hs]

theorem map_fixSub_of_comm {S : Subgroup Γ} {g : Γ} (hg : ∀ s ∈ S, s * g = g * s) :
    (fixSub ρ S).map (ρ g).toMonoidHom = fixSub ρ S := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact ρ_mem_fixSub_of_comm ρ hg hv
  · intro v hv
    refine ⟨ρ g⁻¹ v, ?_, ρ_apply_inv_self ρ g v⟩
    refine ρ_mem_fixSub_of_comm ρ (g := g⁻¹) (fun s hs => ?_) hv
    have := hg s hs
    calc s * g⁻¹ = g⁻¹ * (g * s) * g⁻¹ := by group
      _ = g⁻¹ * (s * g) * g⁻¹ := by rw [this]
      _ = g⁻¹ * s := by group

@[expose] def restrictAct (X : Subgroup Γ) (Z : Subgroup V) (hZ : ∀ g ∈ X, ∀ z ∈ Z, ρ g z ∈ Z) :
    X →* MulAut ↥Z where
  toFun g :=
    { toFun := fun z => ⟨ρ (g : Γ) z, hZ g g.2 z z.2⟩
      invFun := fun z => ⟨ρ (g : Γ)⁻¹ z, hZ (g : Γ)⁻¹ (X.inv_mem g.2) z z.2⟩
      left_inv := fun z => Subtype.ext (ρ_inv_apply_self ρ (g : Γ) z)
      right_inv := fun z => Subtype.ext (ρ_apply_inv_self ρ (g : Γ) z)
      map_mul' := fun a b => Subtype.ext (map_mul (ρ (g : Γ)) (a : V) (b : V)) }
  map_one' := by
    ext z
    show ρ ((1 : X) : Γ) z = z
    simp
  map_mul' := fun a b => by
    ext z
    show ρ ((a * b : X) : Γ) z = ρ (a : Γ) (ρ (b : Γ) z)
    rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]

theorem restrictAct_apply (X : Subgroup Γ) (Z : Subgroup V) (hZ : ∀ g ∈ X, ∀ z ∈ Z, ρ g z ∈ Z)
    (g : X) (z : Z) : ((restrictAct ρ X Z hZ g z : ↥Z) : V) = ρ (g : Γ) (z : V) := rfl

theorem restrictAct_ne_one (X : Subgroup Γ) (Z : Subgroup V) (hZ : ∀ g ∈ X, ∀ z ∈ Z, ρ g z ∈ Z)
    {g : Γ} (hg : g ∈ X) {z : V} (hz : z ∈ Z) (h : ρ g z ≠ z) :
    restrictAct ρ X Z hZ ≠ 1 := by
  intro h1
  apply h
  have h3 := congrArg (fun f : X →* MulAut ↥Z => ((f ⟨g, hg⟩ ⟨z, hz⟩ : ↥Z) : V)) h1
  have h4 : ((restrictAct ρ X Z hZ ⟨g, hg⟩ ⟨z, hz⟩ : ↥Z) : V) = ρ g z := rfl
  have h5 : (((1 : X →* MulAut ↥Z) ⟨g, hg⟩ ⟨z, hz⟩ : ↥Z) : V) = z := rfl
  rw [h4, h5] at h3
  exact h3

end Fix

section TwoGroups

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isPGroup_sup_of_comm {S T : Subgroup Γ} (hS : IsPGroup 2 S) (hT : IsPGroup 2 T)
    (hc : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) : IsPGroup 2 ↥(S ⊔ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hST : IsPGroup 2 (↥S × ↥T) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hS
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
    exact (IsPGroup.iff_card).2 ⟨m + n, by rw [Nat.card_prod, hm, hn, pow_add]⟩
  have hc' : ∀ (a : ↥S) (b : ↥T), Commute (S.subtype a) (T.subtype b) := fun a b => hc a a.2 b b.2
  have hrange : (MonoidHom.noncommCoprod S.subtype T.subtype hc').range = S ⊔ T := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have h1 : IsPGroup 2 ↥(MonoidHom.noncommCoprod S.subtype T.subtype hc').range :=
    hST.of_surjective (MonoidHom.noncommCoprod S.subtype T.subtype hc').rangeRestrict
      (MonoidHom.noncommCoprod S.subtype T.subtype hc').rangeRestrict_surjective
  rw [← hrange]
  exact h1

theorem exists_ne_one_fixed {V : Type*} [Group V] [Finite V] (ρ : Γ →* MulAut V)
    (S : Subgroup Γ) (hS : IsPGroup 2 S) {n : ℕ} (hV : Nat.card V = 2 ^ n) (hn : 1 ≤ n) :
    ∃ v ∈ fixSub ρ S, v ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction S V := MulAction.compHom V (ρ.comp S.subtype)
  have h2 : 2 ∣ Nat.card V := by rw [hV]; exact dvd_pow_self 2 (by omega)
  have h1 : (1 : V) ∈ MulAction.fixedPoints S V := fun s => by
    change ρ (s : Γ) 1 = 1
    exact map_one _
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2 h1
  exact ⟨b, fun g hg => hb ⟨g, hg⟩, fun h => hne h.symm⟩

end TwoGroups

section Product

variable {V : Type*} [Group V] [Finite V]

theorem commute_subtype (hcomm : ∀ a b : V, a * b = b * a) (P Q : Subgroup V) :
    ∀ (m : ↥P) (n : ↥Q), Commute (P.subtype m) (Q.subtype n) := fun m n => hcomm m n

theorem prodMap_injective (hcomm : ∀ a b : V, a * b = b * a) (P Q : Subgroup V)
    (hPQ : P ⊓ Q = ⊥) :
    Function.Injective (MonoidHom.noncommCoprod P.subtype Q.subtype (commute_subtype hcomm P Q)) := by
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨P.subtype_injective, Q.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact hPQ

theorem card_mul_le (hcomm : ∀ a b : V, a * b = b * a) (P Q : Subgroup V) (hPQ : P ⊓ Q = ⊥) :
    Nat.card P * Nat.card Q ≤ Nat.card V := by
  have := Nat.card_le_card_of_injective _ (prodMap_injective hcomm P Q hPQ)
  rwa [Nat.card_prod] at this

theorem exists_mul_of_card_le (hcomm : ∀ a b : V, a * b = b * a) (P Q : Subgroup V)
    (hPQ : P ⊓ Q = ⊥) (hcard : Nat.card V ≤ Nat.card P * Nat.card Q) (a : V) :
    ∃ p ∈ P, ∃ q ∈ Q, a = p * q := by
  have hbij : Function.Bijective
      (MonoidHom.noncommCoprod P.subtype Q.subtype (commute_subtype hcomm P Q)) :=
    (prodMap_injective hcomm P Q hPQ).bijective_of_nat_card_le (by rw [Nat.card_prod]; exact hcard)
  obtain ⟨⟨p, q⟩, hpq⟩ := hbij.2 a
  exact ⟨p, p.2, q, q.2, by rw [← hpq]; rfl⟩

end Product

section Main

open Matrix

theorem splitting {V : Type*} [Group V] [Finite V] {Γ : Type*} [Group Γ] [Finite Γ]
    (ρ : Γ →* MulAut V) (hcomm : ∀ a b : V, a * b = b * a) (hV : Nat.card V = 2 ^ 8)
    {k : Type*} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 4)
    (t : Γ) (ht : t * t = 1)
    (Γ₁ Γ₂ U₁ U₂ : Subgroup Γ) (w₁ w₂ : Γ)
    (e₂ : Γ₂ ≃* SpecialLinearGroup (Fin 2) k) (e₁ : Γ₁ ≃* SpecialLinearGroup (Fin 2) k)
    (hU : U₁.map (MulAut.conj t).toMonoidHom = U₂)
    (hcommΓ : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a)
    (hU₁ : U₁ ≤ Γ₁) (hU₂ : U₂ ≤ Γ₂) (hw₁ : w₁ ∈ Γ₁) (hw₂ : w₂ ∈ Γ₂)
    (hp₁ : IsPGroup 2 U₁) (hp₂ : IsPGroup 2 U₂)
    (hgen₁ : Γ₁ ≤ U₁ ⊔ U₁.map (MulAut.conj w₁).toMonoidHom)
    (hgen₂ : Γ₂ ≤ U₂ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom)
    (hfix : ∀ v : V, (∀ g ∈ Γ₁, ρ g v = v) → (∀ g ∈ Γ₂, ρ g v = v) → v = 1)
    (hplus : Nat.card ↥(fixSub ρ (U₁ ⊔ U₂)) = 16)
    (hdisj : fixSub ρ (U₁ ⊔ U₂) ⊓
      (fixSub ρ (U₁ ⊔ U₂)).map (ρ (w₁ * w₂)).toMonoidHom = ⊥) :
    Nat.card ↥(fixSub ρ Γ₁) = 16 ∧ Nat.card ↥(fixSub ρ Γ₂) = 16 ∧
      fixSub ρ Γ₁ ⊔ fixSub ρ Γ₂ = ⊤ ∧ fixSub ρ Γ₁ ⊓ fixSub ρ Γ₂ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A₁ := fixSub ρ U₁ with hA₁
  set A₂ := fixSub ρ U₂ with hA₂
  set B₁ := fixSub ρ (U₁.map (MulAut.conj w₁).toMonoidHom) with hB₁
  set B₂ := fixSub ρ (U₂.map (MulAut.conj w₂).toMonoidHom) with hB₂
  have hB₁' : B₁ = A₁.map (ρ w₁).toMonoidHom := fixSub_map_conj ρ U₁ w₁
  have hB₂' : B₂ = A₂.map (ρ w₂).toMonoidHom := fixSub_map_conj ρ U₂ w₂
  have hU₁w : U₁.map (MulAut.conj w₁).toMonoidHom ≤ Γ₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hw₁ (hU₁ hu)) (inv_mem hw₁)
  have hU₂w : U₂.map (MulAut.conj w₂).toMonoidHom ≤ Γ₂ := by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hw₂ (hU₂ hu)) (inv_mem hw₂)
  have hZ₁ : fixSub ρ Γ₁ = A₁ ⊓ B₁ := by
    apply le_antisymm
    · exact le_inf (fixSub_anti ρ hU₁) (fixSub_anti ρ hU₁w)
    · rw [hA₁, hB₁, ← fixSub_sup]
      exact fixSub_anti ρ hgen₁
  have hZ₂ : fixSub ρ Γ₂ = A₂ ⊓ B₂ := by
    apply le_antisymm
    · exact le_inf (fixSub_anti ρ hU₂) (fixSub_anti ρ hU₂w)
    · rw [hA₂, hB₂, ← fixSub_sup]
      exact fixSub_anti ρ hgen₂
  have hVp0 : fixSub ρ (U₁ ⊔ U₂) = A₁ ⊓ A₂ := fixSub_sup ρ U₁ U₂
  have hw₂A₁ : A₁.map (ρ w₂).toMonoidHom = A₁ :=
    map_fixSub_of_comm ρ (fun s hs => hcommΓ s (hU₁ hs) w₂ hw₂)
  have hw₁B₂ : B₂.map (ρ w₁).toMonoidHom = B₂ := by
    refine map_fixSub_of_comm ρ (fun s hs => ?_)
    exact (hcommΓ w₁ hw₁ s (hU₂w hs)).symm
  have hVm0 : (fixSub ρ (U₁ ⊔ U₂)).map (ρ (w₁ * w₂)).toMonoidHom = B₁ ⊓ B₂ := by
    have hcomp : (ρ (w₁ * w₂)).toMonoidHom =
        (ρ w₁).toMonoidHom.comp (ρ w₂).toMonoidHom := by
      ext v
      simp [map_mul, MulAut.mul_apply]
    rw [hVp0, hcomp, ← Subgroup.map_map, Subgroup.map_inf _ _ _ (ρ w₂).injective, hw₂A₁,
      ← hB₂', Subgroup.map_inf _ _ _ (ρ w₁).injective, hw₁B₂, ← hB₁']
  have hplus' : Nat.card ↥(A₁ ⊓ A₂) = 16 := by rw [← hVp0]; exact hplus
  have hVmcard : Nat.card ↥(B₁ ⊓ B₂) = 16 := by
    rw [← hVm0, Subgroup.card_map_of_injective (ρ _).injective, hplus]
  have hdisj' : (A₁ ⊓ A₂) ⊓ (B₁ ⊓ B₂) = ⊥ := by rw [← hVp0, ← hVm0]; exact hdisj
  have hdec : ∀ a : V, ∃ p ∈ A₁ ⊓ A₂, ∃ m ∈ B₁ ⊓ B₂, a = p * m := fun a =>
    exists_mul_of_card_le hcomm _ _ hdisj' (by rw [hV, hplus', hVmcard]; norm_num) a
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hτ₁ : A₁.map (ρ t).toMonoidHom = A₂ := by
    rw [← fixSub_map_conj ρ U₁ t, hU]
  have hτ₂ : A₂.map (ρ t).toMonoidHom = A₁ := by
    rw [← fixSub_map_conj ρ U₂ t, ← hU, Subgroup.map_map]
    have : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id Γ := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, ht']
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht]; group
    rw [this, Subgroup.map_id]
  have hnot : A₁ = A₂ → False := by
    intro h12
    have hVpA : A₁ ⊓ A₂ = A₁ := by rw [← h12, inf_idem]
    have hA₁card : Nat.card ↥A₁ = 16 := by rw [← hVpA]; exact hplus'
    have hB₂card : Nat.card ↥B₂ = 16 := by
      rw [hB₂', Subgroup.card_map_of_injective (ρ w₂).injective, ← h12, hA₁card]
    have hVmB₂ : B₁ ⊓ B₂ = B₂ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hVmcard, hB₂card])
    have hpg : IsPGroup 2 ↥(U₂.map (MulAut.conj w₂).toMonoidHom) :=
      hp₂.of_equiv (Subgroup.equivMapOfInjective U₂ (MulAut.conj w₂).toMonoidHom
        (MulAut.conj w₂).injective)
    have hpg' : IsPGroup 2 ↥(U₁ ⊔ U₂.map (MulAut.conj w₂).toMonoidHom) :=
      isPGroup_sup_of_comm hp₁ hpg (fun a ha b hb => hcommΓ a (hU₁ ha) b (hU₂w hb))
    obtain ⟨v, hv, hv1⟩ := exists_ne_one_fixed ρ _ hpg' (n := 8) hV (by norm_num)
    rw [fixSub_sup] at hv
    have hv' : v ∈ (A₁ ⊓ A₂) ⊓ (B₁ ⊓ B₂) := by
      refine ⟨?_, ?_⟩
      · rw [hVpA]; exact hv.1
      · rw [hVmB₂]; exact hv.2
    rw [hdisj'] at hv'
    exact hv1 (Subgroup.mem_bot.1 hv')
  have hn12 : ¬ A₁ ≤ A₂ := by
    intro h
    have h' : A₂ ≤ A₁ := by
      have := Subgroup.map_mono (f := (ρ t).toMonoidHom) h
      rwa [hτ₁, hτ₂] at this
    exact hnot (le_antisymm h h')
  have hn21 : ¬ A₂ ≤ A₁ := by
    intro h
    have h' : A₁ ≤ A₂ := by
      have := Subgroup.map_mono (f := (ρ t).toMonoidHom) h
      rwa [hτ₂, hτ₁] at this
    exact hnot (le_antisymm h' h)
  have hZ₁ne : fixSub ρ Γ₁ ≠ ⊥ := by
    obtain ⟨a, ha1, ha2⟩ := Set.not_subset.1 hn12
    obtain ⟨p, hp, m, hm, rfl⟩ := hdec a
    have hm1 : m ∈ A₁ := by
      have := mul_mem (inv_mem ((inf_le_left : A₁ ⊓ A₂ ≤ A₁) hp)) ha1
      simpa using this
    have hmne : m ≠ 1 := by
      rintro rfl
      exact ha2 (by simpa using (inf_le_right : A₁ ⊓ A₂ ≤ A₂) hp)
    intro hbot
    have : m ∈ fixSub ρ Γ₁ := by rw [hZ₁]; exact ⟨hm1, hm.1⟩
    rw [hbot] at this
    exact hmne (Subgroup.mem_bot.1 this)
  have hZ₂ne : fixSub ρ Γ₂ ≠ ⊥ := by
    obtain ⟨a, ha1, ha2⟩ := Set.not_subset.1 hn21
    obtain ⟨p, hp, m, hm, rfl⟩ := hdec a
    have hm1 : m ∈ A₂ := by
      have := mul_mem (inv_mem ((inf_le_right : A₁ ⊓ A₂ ≤ A₂) hp)) ha1
      simpa using this
    have hmne : m ≠ 1 := by
      rintro rfl
      exact ha2 (by simpa using (inf_le_left : A₁ ⊓ A₂ ≤ A₁) hp)
    intro hbot
    have : m ∈ fixSub ρ Γ₂ := by rw [hZ₂]; exact ⟨hm1, hm.2⟩
    rw [hbot] at this
    exact hmne (Subgroup.mem_bot.1 this)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 8) hV
  have hk4 : Nat.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hinv₂ : ∀ g ∈ Γ₂, ∀ z ∈ fixSub ρ Γ₁, ρ g z ∈ fixSub ρ Γ₁ := fun g hg z hz =>
    ρ_mem_fixSub_of_comm ρ (fun s hs => hcommΓ s hs g hg) hz
  have hinv₁ : ∀ g ∈ Γ₁, ∀ z ∈ fixSub ρ Γ₂, ρ g z ∈ fixSub ρ Γ₂ := fun g hg z hz =>
    ρ_mem_fixSub_of_comm ρ (fun s hs => (hcommΓ g hg s hs).symm) hz
  have h16₁ : 16 ≤ Nat.card ↥(fixSub ρ Γ₁) := by
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hZ₁ne)
    have hz := z.2
    have hnt : ∃ g ∈ Γ₂, ρ g (z : V) ≠ z := by
      by_contra hcon
      have hcon' : ∀ g ∈ Γ₂, ρ g (z : V) = z := fun g hg => by_contra fun h => hcon ⟨g, hg, h⟩
      exact hz1 (Subtype.ext (hfix z (fun g hg => hz g hg) hcon'))
    obtain ⟨g, hg, hgz⟩ := hnt
    have hρ := restrictAct_ne_one ρ Γ₂ (fixSub ρ Γ₁) hinv₂ hg z.2 hgz
    have := Common.sl2_card_sq_le_of_ne_one e₂ hk4 le_rfl (restrictAct ρ Γ₂ (fixSub ρ Γ₁) hinv₂)
      (hVp.of_injective (fixSub ρ Γ₁).subtype (fixSub ρ Γ₁).subtype_injective) hρ
    rw [hk] at this
    omega
  have h16₂ : 16 ≤ Nat.card ↥(fixSub ρ Γ₂) := by
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hZ₂ne)
    have hz := z.2
    have hnt : ∃ g ∈ Γ₁, ρ g (z : V) ≠ z := by
      by_contra hcon
      have hcon' : ∀ g ∈ Γ₁, ρ g (z : V) = z := fun g hg => by_contra fun h => hcon ⟨g, hg, h⟩
      exact hz1 (Subtype.ext (hfix z hcon' (fun g hg => hz g hg)))
    obtain ⟨g, hg, hgz⟩ := hnt
    have hρ := restrictAct_ne_one ρ Γ₁ (fixSub ρ Γ₂) hinv₁ hg z.2 hgz
    have := Common.sl2_card_sq_le_of_ne_one e₁ hk4 le_rfl (restrictAct ρ Γ₁ (fixSub ρ Γ₂) hinv₁)
      (hVp.of_injective (fixSub ρ Γ₂).subtype (fixSub ρ Γ₂).subtype_injective) hρ
    rw [hk] at this
    omega
  have hZinf : fixSub ρ Γ₁ ⊓ fixSub ρ Γ₂ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.2 (hfix v (fun g hg => hv.1 g hg) (fun g hg => hv.2 g hg))
  have hle := card_mul_le hcomm _ _ hZinf
  rw [hV] at hle
  have e1 : Nat.card ↥(fixSub ρ Γ₁) = 16 := by nlinarith
  have e2 : Nat.card ↥(fixSub ρ Γ₂) = 16 := by nlinarith
  refine ⟨e1, e2, ?_, hZinf⟩
  rw [eq_top_iff]
  intro v _
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_card_le hcomm _ _ hZinf
    (by rw [hV, e1, e2]; norm_num) v
  exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

end Main

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit
