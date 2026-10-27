module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumComb
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.CoreAux
import CFSG.Quasithin.H13.A7BlkAct
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open scoped commutatorElement IsMulCommutative

section Perf

variable {X : Type*} [Group X] {V K : Subgroup X} {n : ℕ}

theorem altBaum_commutator_le_commutator_commutator
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (Φ : ↥K →* alternatingGroup (Fin n)) (hΦ : Function.Surjective Φ) (h5 : 5 ≤ n)
    (hΦker : ∀ k : ↥K, Φ k = 1 → ∀ v ∈ V, (k : X) * v * (k : X)⁻¹ = v) :
    ⁅V, K⁆ ≤ ⁅⁅V, K⁆, K⁆ := by
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hVK
  have hUK : ∀ k ∈ K, ∀ u ∈ ⁅V, K⁆, k * u * k⁻¹ ∈ ⁅V, K⁆ := fun k hk u hu =>
    conj_mem_commutator V K hVK k hk hu
  have hDK : ∀ k ∈ K, ∀ d ∈ ⁅⁅V, K⁆, K⁆, k * d * k⁻¹ ∈ ⁅⁅V, K⁆, K⁆ := fun k hk d hd =>
    conj_mem_commutator ⁅V, K⁆ K hUK k hk hd
  have hperf : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; exact h5)⟩
  have key : ∀ v ∈ V, ∀ k : ↥K, ⁅v, (k : X)⁆ ∈ ⁅⁅V, K⁆, K⁆ := by
    intro v hv
    have : IsMulCommutative ↥V := IsMulCommutative.of_comm fun a b =>
      Subtype.ext (hVc _ a.2 _ b.2)
    have hmem : ∀ k : ↥K, ⁅v, (k : X)⁆ ∈ V := fun k => by
      have : ⁅v, (k : X)⁆ = v * ((k : X) * v⁻¹ * (k : X)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact V.mul_mem hv (hVK _ k.2 _ (V.inv_mem hv))
    let δ : ↥K →* (↥V ⧸ (⁅⁅V, K⁆, K⁆).subgroupOf V) :=
      { toFun := fun k => QuotientGroup.mk ⟨⁅v, (k : X)⁆, hmem k⟩
        map_one' := by
          have : (⟨⁅v, ((1 : ↥K) : X)⁆, hmem 1⟩ : ↥V) = 1 := Subtype.ext (by simp)
          rw [this]; rfl
        map_mul' := fun k₁ k₂ => by
          show (QuotientGroup.mk ⟨⁅v, ((k₁ * k₂ : ↥K) : X)⁆, hmem _⟩ :
              ↥V ⧸ (⁅⁅V, K⁆, K⁆).subgroupOf V) = QuotientGroup.mk ⟨⁅v, (k₁ : X)⁆, hmem k₁⟩ *
              QuotientGroup.mk ⟨⁅v, (k₂ : X)⁆, hmem k₂⟩
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hw : ⁅v, (k₂ : X)⁆ ∈ ⁅V, K⁆ := Subgroup.commutator_mem_commutator hv k₂.2
          have hd : ⁅(⁅v, (k₂ : X)⁆)⁻¹, (k₁ : X)⁆ ∈ ⁅⁅V, K⁆, K⁆ :=
            Subgroup.commutator_mem_commutator ((⁅V, K⁆).inv_mem hw) k₁.2
          have hd' := (⁅⁅V, K⁆, K⁆).inv_mem hd
          convert hd' using 1
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group }
    have hδ : ∀ k : ↥K, δ k = 1 := fun k => by
      have h1 : δ = 1 := CFSG.Quasithin.A1c.hom_eq_one_of_perfect_quotient Φ hΦ hperf δ
        (fun k hk => by
          show (QuotientGroup.mk ⟨⁅v, (k : X)⁆, hmem k⟩ : ↥V ⧸ (⁅⁅V, K⁆, K⁆).subgroupOf V) = 1
          have hk1 : Φ k = 1 := hk
          have : (⟨⁅v, (k : X)⁆, hmem k⟩ : ↥V) = 1 := Subtype.ext (by
            have h2 := hΦker k hk1 v hv
            exact commutatorElement_eq_one_iff_mul_comm.2 (mul_inv_eq_iff_eq_mul.1 h2).symm)
          rw [this]; rfl)
      exact DFunLike.congr_fun h1 k
    intro k
    have h1 := hδ k
    rw [MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  exact Subgroup.commutator_le.2 fun v hv k hk => key v hv ⟨k, hk⟩

end Perf

section Natural

variable {X : Type*} [Group X] {V K : Subgroup X} {n : ℕ}

structure AltBaumSetup (V K : Subgroup X) {n : ℕ} (Φ : ↥K →* alternatingGroup (Fin n)) : Prop where
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  sq : ∀ v ∈ V, v * v = 1
  norm : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V
  surj : Function.Surjective Φ
  ker : ∀ k : ↥K, Φ k = 1 → ∀ v ∈ V, (k : X) * v * (k : X)⁻¹ = v

structure AltBaumSection (V K : Subgroup X) {n : ℕ} (Φ : ↥K →* alternatingGroup (Fin n))
    (π : ↥⁅V, K⁆ →* Multiplicative (evenWeight n)) : Prop where
  surj : Function.Surjective π
  ker_iff : ∀ u : ↥⁅V, K⁆, π u = 1 ↔ ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u
  equivar : ∀ (l : ↥K) (u u' : ↥⁅V, K⁆), (u' : X) = l * u * l⁻¹ →
    Multiplicative.toAdd (π u') =
      evenWeightPerm (Φ l : Perm (Fin n)) (Multiplicative.toAdd (π u))

@[expose] def altBaumConjU (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) (k : ↥K) :
    ↥⁅V, K⁆ →* ↥⁅V, K⁆ :=
  ((MulAut.conj (k : X)).toMonoidHom.comp (⁅V, K⁆).subtype).codRestrict (⁅V, K⁆)
    (fun u => conj_mem_commutator V K hVK k k.2 u.2)

@[simp] theorem coe_altBaumConjU (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) (k : ↥K) (u : ↥⁅V, K⁆) :
    ((altBaumConjU hVK k u : ↥⁅V, K⁆) : X) = (k : X) * u * (k : X)⁻¹ := rfl

variable {Φ : ↥K →* alternatingGroup (Fin n)} {π : ↥⁅V, K⁆ →* Multiplicative (evenWeight n)}

theorem isPerfect_stabilizer_alt (h6 : 6 ≤ n) (x₀ : Fin n) :
    Group.IsPerfect ↥(MulAction.stabilizer (alternatingGroup (Fin n)) x₀) :=
  Subgroup.isPerfect_iff.2 (CFSG.Quasithin.H13.A7Blk.perfect_stabilizer h6 x₀)

theorem AltBaumSection.fixed_lift (hS : AltBaumSetup V K Φ) (hπ : AltBaumSection V K Φ π)
    (hn : Odd n) (h6 : 6 ≤ n) {x₀ : Fin n} {u₀ : ↥⁅V, K⁆}
    (hu₀ : Multiplicative.toAdd (π u₀) = altBaumY hn x₀) (k : ↥K)
    (hk : (Φ k : Perm (Fin n)) x₀ = x₀) : (k : X) * u₀ * (k : X)⁻¹ = u₀ := by
  have : IsMulCommutative ↥V := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hS.comm _ a.2 _ b.2)
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hS.norm
  have hker : ∀ k : ↥K, (Φ k : Perm (Fin n)) x₀ = x₀ → ∀ k' ∈ K,
      (k' : X) * ((k : X) * u₀ * (k : X)⁻¹ * (u₀ : X)⁻¹) * (k' : X)⁻¹ =
        (k : X) * u₀ * (k : X)⁻¹ * (u₀ : X)⁻¹ := by
    intro k hk k' hk'
    have h1 : Multiplicative.toAdd (π (altBaumConjU hS.norm k u₀)) = Multiplicative.toAdd (π u₀) := by
      rw [hπ.equivar k u₀ (altBaumConjU hS.norm k u₀) rfl, hu₀, evenWeightPerm_altBaumY, hk]
    have h2 : π (altBaumConjU hS.norm k u₀ * u₀⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Multiplicative.toAdd.injective h1
    have := (hπ.ker_iff _).1 h2 k' hk'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_altBaumConjU] using this
  have hmem : ∀ k : ↥K, (k : X) * u₀ * (k : X)⁻¹ * (u₀ : X)⁻¹ ∈ V := fun k =>
    V.mul_mem (hUV (conj_mem_commutator V K hS.norm k k.2 u₀.2)) (V.inv_mem (hUV u₀.2))
  let K₀ : Subgroup ↥K := (MulAction.stabilizer (alternatingGroup (Fin n)) x₀).comap Φ
  let Φ₀ : ↥K₀ →* ↥(MulAction.stabilizer (alternatingGroup (Fin n)) x₀) :=
    (Φ.comp K₀.subtype).codRestrict (MulAction.stabilizer (alternatingGroup (Fin n)) x₀)
      (fun k => k.2)
  have hΦ₀ : Function.Surjective Φ₀ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨k, hk⟩ := hS.surj σ
    exact ⟨⟨k, by show Φ k ∈ MulAction.stabilizer (alternatingGroup (Fin n)) x₀; rw [hk]; exact hσ⟩, Subtype.ext hk⟩
  have hfix0 : ∀ k : ↥K₀, (Φ (k : ↥K) : Perm (Fin n)) x₀ = x₀ := fun k =>
    MulAction.mem_stabilizer_iff.1 k.2
  let c : ↥K₀ →* ↥V :=
    { toFun := fun k => ⟨((k : ↥K) : X) * u₀ * ((k : ↥K) : X)⁻¹ * (u₀ : X)⁻¹, hmem k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun k₁ k₂ => by
        apply Subtype.ext
        have hf := hker (k₂ : ↥K) (hfix0 k₂) (k₁ : ↥K) (k₁ : ↥K).2
        have hc := hS.comm _ (hmem (k₁ : ↥K)) _ (hmem (k₂ : ↥K))
        show ((((k₁ * k₂ : ↥K₀) : ↥K) : X)) * u₀ * ((((k₁ * k₂ : ↥K₀) : ↥K) : X))⁻¹ *
            (u₀ : X)⁻¹ = (((k₁ : ↥K) : X) * u₀ * ((k₁ : ↥K) : X)⁻¹ * (u₀ : X)⁻¹) *
            (((k₂ : ↥K) : X) * u₀ * ((k₂ : ↥K) : X)⁻¹ * (u₀ : X)⁻¹)
        rw [hc]
        have e : ((((k₁ * k₂ : ↥K₀) : ↥K) : X)) * u₀ * ((((k₁ * k₂ : ↥K₀) : ↥K) : X))⁻¹ *
            (u₀ : X)⁻¹ = (((k₁ : ↥K) : X) * (((k₂ : ↥K) : X) * u₀ * ((k₂ : ↥K) : X)⁻¹ *
              (u₀ : X)⁻¹) * ((k₁ : ↥K) : X)⁻¹) * (((k₁ : ↥K) : X) * u₀ *
              ((k₁ : ↥K) : X)⁻¹ * (u₀ : X)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]; group
        rw [e, hf] }
  have hc1 : ∀ k : ↥K₀, c k = 1 := fun k => by
    have h1 : c = 1 := CFSG.Quasithin.A1c.hom_eq_one_of_perfect_quotient Φ₀ hΦ₀
      (isPerfect_stabilizer_alt h6 x₀) c (fun k hk => by
        apply Subtype.ext
        have hk1 : Φ (k : ↥K) = 1 := congrArg Subtype.val hk
        have := hS.ker (k : ↥K) hk1 u₀ (hUV u₀.2)
        show ((k : ↥K) : X) * u₀ * ((k : ↥K) : X)⁻¹ * (u₀ : X)⁻¹ = 1
        rw [this, mul_inv_cancel])
    exact DFunLike.congr_fun h1 k
  have := hc1 ⟨k, MulAction.mem_stabilizer_iff.2 hk⟩
  have h2 : (k : X) * u₀ * (k : X)⁻¹ * (u₀ : X)⁻¹ = 1 := congrArg Subtype.val this
  exact mul_inv_eq_one.1 h2

section ProdVal

variable {A : Type*} [CommGroup A] {n : ℕ}

@[expose] def altBaumProd (a : Fin n → A) (v : Fin n → ZMod 2) : A := ∏ x, a x ^ (v x).val

private theorem pow_mod_two_of_mul_self {a : A} (h : a * a = 1) (m : ℕ) : a ^ (m % 2) = a ^ m := by
  have h2 : a ^ 2 = 1 := by rw [pow_two]; exact h
  conv_rhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, h2, one_pow, mul_one]

@[simp] theorem altBaumProd_zero (a : Fin n → A) : altBaumProd a 0 = 1 := by
  simp [altBaumProd]

theorem altBaumProd_add {a : Fin n → A} (ha : ∀ x, a x * a x = 1) (v w : Fin n → ZMod 2) :
    altBaumProd a (v + w) = altBaumProd a v * altBaumProd a w := by
  unfold altBaumProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Pi.add_apply, ZMod.val_add, pow_mod_two_of_mul_self (ha x), pow_add]

theorem map_altBaumProd {B : Type*} [CommGroup B] (f : A →* B) (a : Fin n → A) (v : Fin n → ZMod 2) :
    f (altBaumProd a v) = altBaumProd (fun x => f (a x)) v := by
  unfold altBaumProd
  rw [map_prod]
  simp [map_pow]

theorem map_altBaumProd_of_equivariant {a : Fin n → A} (σ : Perm (Fin n)) (c : A →* A)
    (hc : ∀ x, c (a x) = a (σ x)) (v : Fin n → ZMod 2) :
    c (altBaumProd a v) = altBaumProd a (fun i => v (σ⁻¹ i)) := by
  unfold altBaumProd
  rw [map_prod]
  simp only [map_pow, hc]
  have h := Equiv.prod_comp σ (fun y => a y ^ (v (σ⁻¹ y)).val)
  simp only [Perm.inv_def, Equiv.symm_apply_apply] at h
  exact h

end ProdVal

theorem AltBaumSection.exists_coherent (hS : AltBaumSetup V K Φ) (hπ : AltBaumSection V K Φ π)
    (hn : Odd n) (h9 : 9 ≤ n) :
    ∃ ũ : Fin n → ↥⁅V, K⁆, (∀ x, Multiplicative.toAdd (π (ũ x)) = altBaumY hn x) ∧
      ∀ (k : ↥K) (x : Fin n), altBaumConjU hS.norm k (ũ x) = ũ ((Φ k : Perm (Fin n)) x) := by
  have hn0 : 0 < n := by omega
  let x₀ : Fin n := ⟨0, hn0⟩
  obtain ⟨u₀, hu₀⟩ := hπ.surj (Multiplicative.ofAdd (altBaumY hn x₀))
  have hu₀' : Multiplicative.toAdd (π u₀) = altBaumY hn x₀ := by rw [hu₀]; rfl
  have hg : ∀ x : Fin n, ∃ k : ↥K, (Φ k : Perm (Fin n)) x₀ = x := fun x => by
    obtain ⟨σ, hσx⟩ :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.exists_alt_apply_eq
        (by omega : 3 ≤ n) x₀ x
    obtain ⟨k, hk⟩ := hS.surj σ
    exact ⟨k, by rw [hk]; exact hσx⟩
  choose g hg using hg
  refine ⟨fun x => altBaumConjU hS.norm (g x) u₀, fun x => ?_, fun k x => ?_⟩
  · rw [hπ.equivar (g x) u₀ _ rfl, hu₀', evenWeightPerm_altBaumY, hg]
  · apply Subtype.ext
    have hfixpt : (Φ ((g ((Φ k : Perm (Fin n)) x))⁻¹ * (k * g x)) : Perm (Fin n)) x₀ = x₀ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
      rw [hg x, Perm.inv_eq_iff_eq]
      exact (hg _).symm
    have hfix := hπ.fixed_lift hS hn (by omega) hu₀' _ hfixpt
    show (k : X) * ((g x : X) * u₀ * (g x : X)⁻¹) * (k : X)⁻¹ =
      (g ((Φ k : Perm (Fin n)) x) : X) * u₀ * (g ((Φ k : Perm (Fin n)) x) : X)⁻¹
    have e : (k : X) * ((g x : X) * u₀ * (g x : X)⁻¹) * (k : X)⁻¹ =
        (g ((Φ k : Perm (Fin n)) x) : X) *
          ((((g ((Φ k : Perm (Fin n)) x))⁻¹ * (k * g x) : ↥K) : X) * u₀ *
            ((((g ((Φ k : Perm (Fin n)) x))⁻¹ * (k * g x) : ↥K) : X))⁻¹) *
          (g ((Φ k : Perm (Fin n)) x) : X)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, hfix]

theorem pi_altBaumProd [IsMulCommutative ↥⁅V, K⁆] (π : ↥⁅V, K⁆ →* Multiplicative (evenWeight n))
    (hn : Odd n) {ũ : Fin n → ↥⁅V, K⁆}
    (hũπ : ∀ x, Multiplicative.toAdd (π (ũ x)) = altBaumY hn x) (v : evenWeight n) :
    π (altBaumProd ũ (v : Fin n → ZMod 2)) = Multiplicative.ofAdd v := by
  have h1 : ∀ x, π (ũ x) = Multiplicative.ofAdd (altBaumY hn x) := fun x =>
    Multiplicative.toAdd.injective (hũπ x)
  rw [map_altBaumProd π ũ]
  unfold altBaumProd
  simp_rw [h1, ← ofAdd_nsmul]
  rw [← ofAdd_sum, sum_val_smul_altBaumY]

theorem AltBaumSection.injective (hS : AltBaumSetup V K Φ) (hπ : AltBaumSection V K Φ π)
    (hn : Odd n) (h9 : 9 ≤ n) : Function.Injective π := by
  obtain ⟨ũ, hũπ, hũc⟩ := hπ.exists_coherent hS hn h9
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hS.norm
  have hUc : ∀ a ∈ ⁅V, K⁆, ∀ b ∈ ⁅V, K⁆, a * b = b * a := fun a ha b hb =>
    hS.comm a (hUV ha) b (hUV hb)
  have : IsMulCommutative ↥⁅V, K⁆ := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hUc _ a.2 _ b.2)
  have hsq : ∀ u : ↥⁅V, K⁆, u * u = 1 := fun u => Subtype.ext (hS.sq u (hUV u.2))
  let s : Multiplicative (evenWeight n) →* ↥⁅V, K⁆ :=
    { toFun := fun v => altBaumProd ũ ((Multiplicative.toAdd v : evenWeight n) : Fin n → ZMod 2)
      map_one' := altBaumProd_zero ũ
      map_mul' := fun v w => altBaumProd_add (fun x => hsq _) _ _ }
  have hs_apply : ∀ v, s v = altBaumProd ũ ((Multiplicative.toAdd v : evenWeight n) : Fin n → ZMod 2) :=
    fun v => rfl
  have hπs : ∀ v, π (s v) = v := fun v => pi_altBaumProd π hn hũπ _
  have hsK : ∀ (k : ↥K) (v : Multiplicative (evenWeight n)),
      altBaumConjU hS.norm k (s v) =
        s (Multiplicative.ofAdd (evenWeightPerm (Φ k : Perm (Fin n)) (Multiplicative.toAdd v))) := by
    intro k v
    rw [hs_apply, hs_apply, map_altBaumProd_of_equivariant (Φ k : Perm (Fin n)) (altBaumConjU hS.norm k)
      (fun x => hũc k x)]
    rfl
  let S₂ : Subgroup ↥⁅V, K⁆ := s.range
  have hS₂K : ∀ (k : ↥K), ∀ u ∈ S₂, altBaumConjU hS.norm k u ∈ S₂ := by
    rintro k _ ⟨v, rfl⟩
    rw [hsK]
    exact ⟨_, rfl⟩
  have hdec : ∀ u : ↥⁅V, K⁆, π (u * (s (π u))⁻¹) = 1 := fun u => by
    rw [map_mul, map_inv, hπs, mul_inv_cancel]
  have hcomm : ⁅⁅V, K⁆, K⁆ ≤ S₂.map (⁅V, K⁆).subtype := by
    refine Subgroup.commutator_le.2 fun u hu k hk => ?_
    set r : ↥⁅V, K⁆ := ⟨u, hu⟩ * (s (π ⟨u, hu⟩))⁻¹ with hr
    have hrfix : ∀ k' ∈ K, (k' : X) * (r : X) * (k' : X)⁻¹ = r :=
      (hπ.ker_iff r).1 (hdec ⟨u, hu⟩)
    refine ⟨s (π ⟨u, hu⟩) * (altBaumConjU hS.norm ⟨k, hk⟩ (s (π ⟨u, hu⟩)))⁻¹, ?_, ?_⟩
    · exact S₂.mul_mem ⟨_, rfl⟩ (S₂.inv_mem (hS₂K ⟨k, hk⟩ _ ⟨_, rfl⟩))
    · have hu' : (⟨u, hu⟩ : ↥⁅V, K⁆) = r * s (π ⟨u, hu⟩) := by rw [hr, inv_mul_cancel_right]
      have hrk : altBaumConjU hS.norm ⟨k, hk⟩ r = r := Subtype.ext (hrfix k hk)
      have hd : (⟨u, hu⟩ : ↥⁅V, K⁆) * (altBaumConjU hS.norm ⟨k, hk⟩ ⟨u, hu⟩)⁻¹ =
          s (π ⟨u, hu⟩) * (altBaumConjU hS.norm ⟨k, hk⟩ (s (π ⟨u, hu⟩)))⁻¹ := by
        conv_lhs => rw [hu', map_mul, hrk, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      have := congrArg (fun y : ↥⁅V, K⁆ => (y : X)) hd
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_altBaumConjU] at this
      show ((s (π ⟨u, hu⟩) * (altBaumConjU hS.norm ⟨k, hk⟩ (s (π ⟨u, hu⟩)))⁻¹ : ↥⁅V, K⁆) : X) = ⁅u, k⁆
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_altBaumConjU]
      rw [← this, commutatorElement_def]
      group
  have hU : ⁅V, K⁆ ≤ S₂.map (⁅V, K⁆).subtype :=
    (altBaum_commutator_le_commutator_commutator hS.comm hS.norm Φ hS.surj (by omega) hS.ker).trans hcomm
  rw [injective_iff_map_eq_one]
  intro r hr
  obtain ⟨y, hy, hyr⟩ := hU r.2
  have hyr' : y = r := Subtype.ext hyr
  rw [← hyr'] at hr ⊢
  obtain ⟨w, hw⟩ := hy
  rw [← hw] at hr ⊢
  have : w = 1 := by rw [← hπs w]; exact hr
  rw [this, map_one]

theorem AltBaumSection.centralizes_of_commute (hS : AltBaumSetup V K Φ)
    (hπ : AltBaumSection V K Φ π) (hn : Odd n) (h9 : 9 ≤ n) {x : X}
    (hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V)
    (hcomm : ∀ k ∈ K, ∀ v ∈ V, x * (k * v * k⁻¹) * x⁻¹ = k * (x * v * x⁻¹) * k⁻¹) :
    ∀ u ∈ ⁅V, K⁆, x * u * x⁻¹ = u := by
  have hinj := hπ.injective hS hn h9
  obtain ⟨ũ, hũπ, hũc⟩ := hπ.exists_coherent hS hn h9
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hS.norm
  have hUc : ∀ a ∈ ⁅V, K⁆, ∀ b ∈ ⁅V, K⁆, a * b = b * a := fun a ha b hb =>
    hS.comm a (hUV ha) b (hUV hb)
  have : IsMulCommutative ↥⁅V, K⁆ := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hUc _ a.2 _ b.2)
  have hsq : ∀ u : ↥⁅V, K⁆, u * u = 1 := fun u => Subtype.ext (hS.sq u (hUV u.2))
  have hxU : ∀ u ∈ ⁅V, K⁆, x * u * x⁻¹ ∈ ⁅V, K⁆ := by
    have : ⁅V, K⁆ ≤ (⁅V, K⁆).comap (MulAut.conj x).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun v hv k hk => ?_
      show x * ⁅v, k⁆ * x⁻¹ ∈ ⁅V, K⁆
      have e : x * ⁅v, k⁆ * x⁻¹ = ⁅x * v * x⁻¹, k⁆ := by
        have h1 := hcomm k hk v⁻¹ (V.inv_mem hv)
        have e1 : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by
          simp only [commutatorElement_def]; group
        have e2 : ⁅x * v * x⁻¹, k⁆ = (x * v * x⁻¹) * (k * (x * v⁻¹ * x⁻¹) * k⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1, e2, ← h1]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hxV v hv) hk
    intro u hu
    exact this hu
  let ξ : ↥⁅V, K⁆ →* ↥⁅V, K⁆ :=
    ((MulAut.conj x).toMonoidHom.comp (⁅V, K⁆).subtype).codRestrict (⁅V, K⁆)
      (fun u => hxU u u.2)
  have hξ_apply : ∀ u : ↥⁅V, K⁆, ((ξ u : ↥⁅V, K⁆) : X) = x * u * x⁻¹ := fun u => rfl
  have hξK : ∀ (k : ↥K) (u : ↥⁅V, K⁆), ξ (altBaumConjU hS.norm k u) = altBaumConjU hS.norm k (ξ u) := by
    intro k u
    apply Subtype.ext
    rw [hξ_apply, coe_altBaumConjU, coe_altBaumConjU, hξ_apply]
    exact hcomm k k.2 u (hUV u.2)
  have hξinj : Function.Injective ξ := by
    intro a b h
    apply Subtype.ext
    have h' := congrArg (fun y : ↥⁅V, K⁆ => (y : X)) h
    simp only [hξ_apply] at h'
    simpa using h'
  have hn0 : 0 < n := by omega
  let x₀ : Fin n := ⟨0, hn0⟩
  have hx₀ : ξ (ũ x₀) = ũ x₀ := by
    have hfixd : ∀ σ ∈ alternatingGroup (Fin n), σ x₀ = x₀ →
        evenWeightPerm σ (Multiplicative.toAdd (π (ξ (ũ x₀)))) =
          Multiplicative.toAdd (π (ξ (ũ x₀))) := by
      intro σ hσ hσx
      obtain ⟨k, hk⟩ := hS.surj ⟨σ, hσ⟩
      have hkx : (Φ k : Perm (Fin n)) x₀ = x₀ := by rw [hk]; exact hσx
      have h1 : altBaumConjU hS.norm k (ξ (ũ x₀)) = ξ (ũ x₀) := by
        rw [← hξK, hũc, hkx]
      have h2 := hπ.equivar k (ξ (ũ x₀)) (altBaumConjU hS.norm k (ξ (ũ x₀))) rfl
      rw [h1, hk] at h2
      exact h2.symm
    rcases eq_zero_or_eq_altBaumY_of_fixed hn (by omega) hfixd with h0 | h1
    · exfalso
      have h2 : π (ξ (ũ x₀)) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]; rfl
      have h3 : ξ (ũ x₀) = 1 := hinj (h2.trans (map_one π).symm)
      have h4 : ũ x₀ = 1 := hξinj (h3.trans (map_one ξ).symm)
      have h5 := hũπ x₀
      rw [h4, map_one] at h5
      exact altBaumY_ne_zero hn (by omega) x₀ (by rw [← h5]; rfl)
    · apply hinj
      apply Multiplicative.toAdd.injective
      rw [h1, hũπ]
  have hξy : ∀ y : Fin n, ξ (ũ y) = ũ y := by
    intro y
    obtain ⟨σ, hσy⟩ :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.exists_alt_apply_eq
        (by omega : 3 ≤ n) x₀ y
    obtain ⟨k, hk⟩ := hS.surj σ
    have hky : (Φ k : Perm (Fin n)) x₀ = y := by rw [hk]; exact hσy
    have h1 : altBaumConjU hS.norm k (ũ x₀) = ũ y := by rw [hũc, hky]
    rw [← h1, hξK, hx₀]
  intro u hu
  have hu' := hinj ((pi_altBaumProd π hn hũπ (Multiplicative.toAdd (π ⟨u, hu⟩))).trans (by rfl) :
    π (altBaumProd ũ ((Multiplicative.toAdd (π ⟨u, hu⟩) : evenWeight n) : Fin n → ZMod 2)) =
      π ⟨u, hu⟩)
  have hfix : ξ ⟨u, hu⟩ = ⟨u, hu⟩ := by
    rw [← hu', map_altBaumProd ξ ũ]
    simp only [hξy]
  have := congrArg (fun y : ↥⁅V, K⁆ => (y : X)) hfix
  simpa [hξ_apply] using this

end Natural

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
