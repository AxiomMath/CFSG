module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

variable {Γ : Type*} [Group Γ]

theorem exists_conj_eq_of_pow_eq_one_of_odd {m : ℕ} (hm : Odd m)
    {β : MulAut (alternatingGroup (Fin 6))} (hβ : β ^ m = 1) :
    ∃ a : alternatingGroup (Fin 6), MulAut.conj a = β := by
  obtain ⟨k, hk⟩ := CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
    (QuotientGroup.mk β : Outer (alternatingGroup (Fin 6)))
  have hm' : (QuotientGroup.mk β : Outer (alternatingGroup (Fin 6))) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have hgcd : Nat.gcd (2 ^ k) m = 1 := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have h := pow_gcd_eq_one.2 ⟨hk, hm'⟩
  rw [hgcd, pow_one] at h
  exact (QuotientGroup.eq_one_iff β).1 h

theorem not_forall_mul_self_eq_one_alternating_six :
    ¬ ∀ a : alternatingGroup (Fin 6), a * a = 1 := by
  intro h
  have hinv : ∀ a : alternatingGroup (Fin 6), a⁻¹ = a :=
    fun a => (mul_eq_one_iff_eq_inv.1 (h a)).symm
  have hcomm : IsMulCommutative (alternatingGroup (Fin 6)) :=
    ⟨⟨fun a b => by
      calc a * b = (a * b)⁻¹ := (hinv _).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [hinv, hinv]⟩⟩
  have h6 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hcomm
  simp at h6

theorem mem_iff_of_quotient_alternating_six (V : Subgroup Γ) [V.Normal]
    (hV : ∀ v ∈ V, v * v = 1) (e : Γ ⧸ V ≃* alternatingGroup (Fin 6)) (ψ : MulAut Γ) (x : Γ) :
    ψ x ∈ V ↔ x ∈ V := by
  have key : ∀ φ : MulAut Γ, ∀ x ∈ V, φ x ∈ V := by
    intro φ x hx
    set π : Γ →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' V)
    have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective V)
    have hker : ∀ y, π y = 1 → y ∈ V := by
      intro y hy
      have h1 : e (y : Γ ⧸ V) = 1 := hy
      rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact h1
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI hW : (V.map φ.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective
    haveI : ((V.map φ.toMonoidHom).map π).Normal := Subgroup.Normal.map hW π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V.map φ.toMonoidHom).map π) with h | h
    · apply hker
      have hmem : π (φ x) ∈ (V.map φ.toMonoidHom).map π :=
        ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      refine not_forall_mul_self_eq_one_alternating_six fun a => ?_
      have ha : a ∈ (V.map φ.toMonoidHom).map π := by rw [h]; exact Subgroup.mem_top a
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := ha
      change π (φ v) * π (φ v) = 1
      rw [← map_mul, ← map_mul, hV v hv, map_one, map_one]
  refine ⟨fun h => ?_, key ψ x⟩
  have h' := key ψ⁻¹ (ψ x) h
  simpa using h'

theorem exists_conj_mul_sq_eq_one (V : Subgroup Γ) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (Γ ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V,
      (∀ (x : Γ) (v : V), f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    {φ : MulAut Γ} {m : ℕ} (hm : Odd m) (hφ : φ ^ m = 1) :
    ∃ e : Γ, (MulAut.conj e * φ) ^ 2 = 1 := by
  obtain ⟨ε⟩ := hA6
  have hVinv := mem_iff_of_quotient_alternating_six V hV ε
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hinv : ∀ y ∈ V, y⁻¹ = y := fun y hy => (mul_eq_one_iff_eq_inv.1 (hV y hy)).symm
    calc a * b = (a * b)⁻¹ := (hinv _ (V.mul_mem ha hb)).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv b hb, hinv a ha]
  have hmap : V.map φ.toMonoidHom = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hVinv φ y).2 hy
    · intro hx
      refine ⟨φ.symm x, (hVinv φ _).1 ?_, φ.apply_symm_apply x⟩
      rw [φ.apply_symm_apply]
      exact hx
  let q : Γ ⧸ V ≃* Γ ⧸ V := QuotientGroup.congr V V φ hmap
  have hq : ∀ x : Γ, q (x : Γ ⧸ V) = ((φ x : Γ) : Γ ⧸ V) :=
    fun x => QuotientGroup.congr_mk V V φ hmap x
  let β : MulAut (alternatingGroup (Fin 6)) := (ε.symm.trans q).trans ε
  have hβ : ∀ x : Γ, β (ε (x : Γ ⧸ V)) = ε ((φ x : Γ) : Γ ⧸ V) := by
    intro x
    show ε (q (ε.symm (ε (x : Γ ⧸ V)))) = _
    rw [ε.symm_apply_apply, hq]
  have hβk : ∀ k : ℕ, ∀ x : Γ, (β ^ k) (ε (x : Γ ⧸ V)) = ε (((φ ^ k) x : Γ) : Γ ⧸ V) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hβ, pow_succ', MulAut.mul_apply]
  have hβm : β ^ m = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ε.symm y)
    have hy : y = ε (x : Γ ⧸ V) := by rw [hx, ε.apply_symm_apply]
    rw [hy, hβk, hφ, MulAut.one_apply, MulAut.one_apply]
  obtain ⟨a, ha⟩ := exists_conj_eq_of_pow_eq_one_of_odd hm hβm
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective (ε.symm a)
  have hax : a = ε (x₀ : Γ ⧸ V) := by rw [hx₀, ε.apply_symm_apply]
  have hφx : ∀ x : Γ, ((φ x : Γ) : Γ ⧸ V) = ((x₀ * x * x₀⁻¹ : Γ) : Γ ⧸ V) := by
    intro x
    apply ε.injective
    rw [← hβ, ← ha, MulAut.conj_apply, hax]
    simp
  refine ⟨x₀⁻¹, ?_⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : MulAut Γ, ψ = MulAut.conj x₀⁻¹ * φ := ⟨_, rfl⟩
  rw [← hψdef]
  have hψx : ∀ x : Γ, ψ x = x₀⁻¹ * φ x * x₀ := by
    intro x
    rw [hψdef, MulAut.mul_apply, MulAut.conj_apply]
    simp
  have hψV : ∀ x : Γ, ψ x * x⁻¹ ∈ V := by
    intro x
    have h1 : ((ψ x : Γ) : Γ ⧸ V) = (x : Γ ⧸ V) := by
      rw [hψx]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hφx]
      group
    have h2 := QuotientGroup.eq_iff_div_mem.1 h1
    simpa [div_eq_mul_inv] using h2
  have hψmem : ∀ v, ψ v ∈ V ↔ v ∈ V := hVinv ψ
  obtain ⟨f, hf⟩ : ∃ f : MulAut V, ∀ v : V, (f v : Γ) = ψ v :=
    ⟨{ toFun := fun v => ⟨ψ v, (hψmem v).2 v.2⟩
       invFun := fun v => ⟨ψ.symm v, (hψmem _).1 (by rw [ψ.apply_symm_apply]; exact v.2)⟩
       left_inv := fun v => Subtype.ext (ψ.symm_apply_apply v)
       right_inv := fun v => Subtype.ext (ψ.apply_symm_apply v)
       map_mul' := fun a b => Subtype.ext (map_mul ψ (a : Γ) (b : Γ)) }, fun v => rfl⟩
  have hf1 : f = 1 := by
    refine hcomm f fun x v => Subtype.ext ?_
    rw [hf, MulAut.conjNormal_apply, MulAut.conjNormal_apply, hf]
    obtain ⟨u, hudef⟩ : ∃ u : Γ, u = ψ x * x⁻¹ := ⟨_, rfl⟩
    have huV : u ∈ V := hudef ▸ hψV x
    have hux : ψ x = u * x := by rw [hudef]; group
    have hw : x * ψ v * x⁻¹ ∈ V := Subgroup.Normal.conj_mem inferInstance _ ((hψmem v).2 v.2) x
    calc ψ (x * v * x⁻¹) = ψ x * ψ v * (ψ x)⁻¹ := by simp
      _ = u * (x * ψ v * x⁻¹) * u⁻¹ := by rw [hux]; group
      _ = x * ψ v * x⁻¹ := by rw [hVc u huV _ hw]; group
  have hψfix : ∀ v ∈ V, ψ v = v := by
    intro v hv
    have h := congrArg (fun r : MulAut V => (r ⟨v, hv⟩ : Γ)) hf1
    simpa [hf] using h
  rw [pow_two]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.one_apply]
  obtain ⟨u, hudef⟩ : ∃ u : Γ, u = ψ x * x⁻¹ := ⟨_, rfl⟩
  have huV : u ∈ V := hudef ▸ hψV x
  have hux : ψ x = u * x := by rw [hudef]; group
  rw [hux, map_mul, hψfix u huV, hux, ← mul_assoc, hV u huV, one_mul]

end Abstract

section Wrapper

variable {H : Type*} [Group H]

theorem mem_of_odd_orderOf_of_mem_normalizer {Γ : Type*} [Group Γ] (E : Subgroup H) (θ : Γ ≃* E)
    (V : Subgroup Γ) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (Γ ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V,
      (∀ (x : Γ) (v : V), f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    (hC : IsPGroup 2 (Subgroup.centralizer (E : Set H)))
    {g : H} (hgE : g ∈ Subgroup.normalizer (E : Set H)) (hg : Odd (orderOf g)) : g ∈ E := by
  obtain ⟨γ, hγg⟩ : ∃ γ : ↥(Subgroup.normalizer (E : Set H)), (γ : H) = g := ⟨⟨g, hgE⟩, rfl⟩
  have hγ : γ ^ orderOf g = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hγg]; simpa using pow_orderOf_eq_one g)
  obtain ⟨φ, hφdef⟩ : ∃ φ : MulAut Γ, φ = (MulAut.congr θ).symm (E.normalizerMonoidHom γ) :=
    ⟨_, rfl⟩
  have hφ : φ ^ orderOf g = 1 := by
    apply (MulAut.congr θ).injective
    rw [map_pow, hφdef, MulEquiv.apply_symm_apply, ← map_pow, hγ, map_one, map_one]
  obtain ⟨eΓ, heΓ⟩ := exists_conj_mul_sq_eq_one V hV hA6 hcomm hg hφ
  obtain ⟨e, he⟩ : ∃ e : E, (MulAut.conj e * E.normalizerMonoidHom γ) ^ 2 = 1 := by
    refine ⟨θ eΓ, ?_⟩
    have h := congrArg (MulAut.congr θ) heΓ
    rw [map_pow, map_mul, hφdef, MulEquiv.apply_symm_apply, map_one] at h
    have hc : MulAut.congr θ (MulAut.conj eΓ) = MulAut.conj (θ eΓ) := by
      refine MulEquiv.ext fun h => ?_
      simp [MulAut.congr_apply]
    rwa [hc] at h
  obtain ⟨γe, hγe⟩ : ∃ γe : ↥(Subgroup.normalizer (E : Set H)), (γe : H) = e :=
    ⟨⟨e, Subgroup.le_normalizer e.2⟩, rfl⟩
  have hνe : E.normalizerMonoidHom γe = MulAut.conj e := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hγe]
    simp
  obtain ⟨γc, hγcdef⟩ : ∃ γc : ↥(Subgroup.normalizer (E : Set H)), γc = γe * γ := ⟨_, rfl⟩
  have hγc : (E.normalizerMonoidHom γc) ^ 2 = 1 := by
    rw [hγcdef, map_mul, hνe]
    exact he
  have hc2 : ((γc ^ 2 : ↥(Subgroup.normalizer (E : Set H))) : H) ∈
      Subgroup.centralizer (E : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : E.normalizerMonoidHom (γc ^ 2) = 1 := by rw [map_pow]; exact hγc
    have h2 := congrArg (fun ρ : MulAut E => ((ρ ⟨a, ha⟩ : E) : H)) h1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  obtain ⟨k, hk⟩ := hC ⟨_, hc2⟩
  have hγc1 : γc ^ (2 ^ (k + 1)) = 1 := by
    refine Subtype.ext ?_
    have h := congrArg Subtype.val hk
    simpa [pow_succ', pow_mul] using h
  haveI : (E.subgroupOf (Subgroup.normalizer (E : Set H))).Normal := Subgroup.normal_in_normalizer
  have hmk : (QuotientGroup.mk γc : _ ⧸ E.subgroupOf (Subgroup.normalizer (E : Set H))) =
      QuotientGroup.mk γ := by
    rw [hγcdef, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff γe).2 (Subgroup.mem_subgroupOf.2 (by rw [hγe]; exact e.2)),
      one_mul]
  have h1 : (QuotientGroup.mk γc : _ ⧸ E.subgroupOf (Subgroup.normalizer (E : Set H))) ^
      (2 ^ (k + 1)) = 1 := by
    rw [← QuotientGroup.mk_pow, hγc1, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk γc : _ ⧸ E.subgroupOf (Subgroup.normalizer (E : Set H))) ^
      orderOf g = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow, hγ, QuotientGroup.mk_one]
  have hcop : Nat.gcd (2 ^ (k + 1)) (orderOf g) = 1 :=
    Nat.Coprime.pow_left (k + 1) (Nat.coprime_two_left.2 hg)
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [hcop, pow_one] at h3
  have h4 : (e : H) * g ∈ E := by
    have := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff γc).1 h3)
    rwa [hγcdef, Subgroup.coe_mul, hγe, hγg] at this
  simpa using E.mul_mem (E.inv_mem e.2) h4

theorem exists_pow_two_pow_mem_of_mem_normalizer [Finite H] {Γ : Type*} [Group Γ]
    (E : Subgroup H) (θ : Γ ≃* E) (V : Subgroup Γ) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (Γ ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V,
      (∀ (x : Γ) (v : V), f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    (hC : IsPGroup 2 (Subgroup.centralizer (E : Set H)))
    {h : H} (hh : h ∈ Subgroup.normalizer (E : Set H)) : ∃ k : ℕ, h ^ 2 ^ k ∈ E := by
  obtain ⟨k, b, hb, hkb⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  refine ⟨k, mem_of_odd_orderOf_of_mem_normalizer E θ V hV hA6 hcomm hC (pow_mem hh _) ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) ⟨b, hkb⟩, hkb, Nat.mul_div_cancel_left _ (by positivity)]
  exact hb

theorem isPGroup_two_quotient [Finite H] {Γ : Type*} [Group Γ] (E : Subgroup H) [E.Normal]
    (θ : Γ ≃* E) (V : Subgroup Γ) [V.Normal] (hV : ∀ v ∈ V, v * v = 1)
    (hA6 : Nonempty (Γ ⧸ V ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ f : MulAut V,
      (∀ (x : Γ) (v : V), f (MulAut.conjNormal x v) = MulAut.conjNormal x (f v)) → f = 1)
    (hC : IsPGroup 2 (Subgroup.centralizer (E : Set H))) :
    IsPGroup 2 (H ⧸ E) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_normalizer E θ V hV hA6 hcomm hC
    (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top h)
  exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 hk⟩

end Wrapper

end CFSG.ClassicalInvolution.Sp62Rec
