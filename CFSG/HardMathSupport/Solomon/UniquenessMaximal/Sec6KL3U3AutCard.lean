module

public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.Assembly.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {Y : Type} [Group Y] [Finite Y]

theorem mapsTo_of_normal_sylow (V : Subgroup Y) [V.Normal] (hVcard : Nat.card V = 9)
    (hY : Nat.card Y = 72) (α : MulAut Y) {v : Y} (hv : v ∈ V) : α v ∈ V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card Y).factorization 3 = 2 := by
    rw [hY, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  let Rv : Sylow 3 Y := Sylow.ofCard V (by rw [hVcard, hfac]; norm_num)
  have hN : (Rv : Subgroup Y).Normal := inferInstanceAs V.Normal
  have hchar : (Rv : Subgroup Y).Characteristic := Sylow.characteristic_of_normal Rv hN
  have h := hchar.fixed α
  have hv' : v ∈ (Rv : Subgroup Y).comap α.toMonoidHom := by
    rw [h]; exact hv
  exact hv'

section Key

variable (V : Subgroup Y) [V.Normal]

theorem exists_conj_of_fixes (hVcard : Nat.card V = 9)
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hY : Nat.card Y = 72)
    (hcent : ∀ y : Y, (∀ v ∈ V, y * v = v * y) → y ∈ V)
    (α : MulAut Y) (hα : ∀ v ∈ V, α v = v) : ∃ v ∈ V, α = MulAut.conj v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac2 : (Nat.card Y).factorization 2 = 3 := by
    rw [hY, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  obtain ⟨Q⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hQcard : Nat.card (Q : Subgroup Y) = 8 := by
    rw [Sylow.card_eq_multiplicity Q, hfac2]; norm_num
  have hVQ : V ⊓ (Q : Subgroup Y) = ⊥ := by
    apply disjoint_iff.1
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hVcard, hQcard]; norm_num
  have hQV : ∀ x, x ∈ V → x ∈ (Q : Subgroup Y) → x = 1 := fun x hxV hxQ => by
    have : x ∈ V ⊓ (Q : Subgroup Y) := ⟨hxV, hxQ⟩
    rw [hVQ] at this
    exact this
  have hdecomp : ∀ y : Y, ∃ v ∈ V, ∃ q ∈ (Q : Subgroup Y), y = v * q := by
    let φ : V × (Q : Subgroup Y) → Y := fun p => (p.1 : Y) * (p.2 : Y)
    have hφ : Function.Injective φ := by
      rintro ⟨⟨v, hv⟩, ⟨q, hq⟩⟩ ⟨⟨v', hv'⟩, ⟨q', hq'⟩⟩ h
      simp only [φ] at h
      have h1 : v'⁻¹ * v = q' * q⁻¹ := by
        calc v'⁻¹ * v = v'⁻¹ * (v * q) * q⁻¹ := by group
          _ = v'⁻¹ * (v' * q') * q⁻¹ := by rw [h]
          _ = q' * q⁻¹ := by group
      have h2 : v'⁻¹ * v = 1 := hQV _ (V.mul_mem (V.inv_mem hv') hv)
        (h1 ▸ (Q : Subgroup Y).mul_mem hq' ((Q : Subgroup Y).inv_mem hq))
      have h3 : v = v' := by
        have := mul_eq_one_iff_eq_inv.1 h2
        simpa using this.symm
      subst h3
      have h4 : q = q' := mul_left_cancel h
      subst h4
      rfl
    have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by
      rw [Nat.card_prod, hVcard, hQcard, hY])
    intro y
    obtain ⟨⟨⟨v, hv⟩, ⟨q, hq⟩⟩, h⟩ := hbij.2 y
    exact ⟨v, hv, q, hq, h.symm⟩
  let Q' : Sylow 2 Y := Sylow.ofCard (Subgroup.map α.toMonoidHom (Q : Subgroup Y)) (by
    rw [Subgroup.card_map_of_injective α.injective, hQcard, hfac2]; norm_num)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y Q Q'
  obtain ⟨v, hv, q0, hq0, rfl⟩ := hdecomp y
  have hαQ : ∀ q ∈ (Q : Subgroup Y), v⁻¹ * α q * v ∈ (Q : Subgroup Y) := by
    intro q hq
    have hmem : α q ∈ ((Q' : Sylow 2 Y) : Subgroup Y) := ⟨q, hq, rfl⟩
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    have h1 : (v * q0)⁻¹ * α q * (v * q0) ∈ (Q : Subgroup Y) := hmem
    have h2 : q0 * ((v * q0)⁻¹ * α q * (v * q0)) * q0⁻¹ ∈ (Q : Subgroup Y) :=
      (Q : Subgroup Y).mul_mem ((Q : Subgroup Y).mul_mem hq0 h1) ((Q : Subgroup Y).inv_mem hq0)
    have e : q0 * ((v * q0)⁻¹ * α q * (v * q0)) * q0⁻¹ = v⁻¹ * α q * v := by group
    rwa [e] at h2
  have hcentV : ∀ u ∈ V, ∀ w ∈ V, u * w = w * u := hVcomm
  have hαq : ∀ q ∈ (Q : Subgroup Y), α q = v * q * v⁻¹ := by
    intro q hq
    set q' := v⁻¹ * α q * v with hq'
    have hq'Q : q' ∈ (Q : Subgroup Y) := hαQ q hq
    have hconjq : ∀ u ∈ V, q' * u * q'⁻¹ = q * u * q⁻¹ := by
      intro u hu
      have hquV : q * u * q⁻¹ ∈ V := Subgroup.Normal.conj_mem inferInstance u hu q
      have e1 : α q * u * (α q)⁻¹ = q * u * q⁻¹ := by
        calc α q * u * (α q)⁻¹ = α q * α u * (α q)⁻¹ := by rw [hα u hu]
          _ = α (q * u * q⁻¹) := by rw [map_mul, map_mul, map_inv]
          _ = q * u * q⁻¹ := hα _ hquV
      have e2 : v * u * v⁻¹ = u := by
        have := hcentV v hv u hu
        rw [this]; group
      have e3 : v⁻¹ * (q * u * q⁻¹) * v = q * u * q⁻¹ := by
        have := hcentV v⁻¹ (V.inv_mem hv) _ hquV
        rw [this]; group
      calc q' * u * q'⁻¹ = v⁻¹ * α q * (v * u * v⁻¹) * (α q)⁻¹ * v := by rw [hq']; group
        _ = v⁻¹ * (α q * u * (α q)⁻¹) * v := by rw [e2]; group
        _ = v⁻¹ * (q * u * q⁻¹) * v := by rw [e1]
        _ = q * u * q⁻¹ := e3
    have hcq : q⁻¹ * q' ∈ V := hcent _ (fun u hu => by
      have h := hconjq u hu
      have : q⁻¹ * q' * u = u * (q⁻¹ * q') := by
        calc q⁻¹ * q' * u = q⁻¹ * (q' * u * q'⁻¹) * q' := by group
          _ = q⁻¹ * (q * u * q⁻¹) * q' := by rw [h]
          _ = u * (q⁻¹ * q') := by group
      exact this)
    have hcqQ : q⁻¹ * q' ∈ (Q : Subgroup Y) :=
      (Q : Subgroup Y).mul_mem ((Q : Subgroup Y).inv_mem hq) hq'Q
    have h1 : q⁻¹ * q' = 1 := hQV _ hcq hcqQ
    have h2 : q' = q := by
      have := mul_eq_one_iff_eq_inv.1 h1
      simpa using this.symm
    calc α q = v * (v⁻¹ * α q * v) * v⁻¹ := by group
      _ = v * q * v⁻¹ := by rw [← hq', h2]
  refine ⟨v, hv, ?_⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨u, hu, q, hq, rfl⟩ := hdecomp z
  rw [map_mul, hα u hu, hαq q hq, MulAut.conj_apply]
  have e2 : v * u * v⁻¹ = u := by
    have := hcentV v hv u hu
    rw [this]; group
  calc u * (v * q * v⁻¹) = (v * u * v⁻¹) * (v * q * v⁻¹) := by rw [e2]
    _ = v * (u * q) * v⁻¹ := by group

theorem card_le_twentySeven_of_pGroup (hVcard : Nat.card V = 9)
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV3 : ∀ a ∈ V, a ^ 3 = 1)
    (hY : Nat.card Y = 72) (hcent : ∀ y : Y, (∀ v ∈ V, y * v = v * y) → y ∈ V)
    (P : Subgroup (MulAut Y)) (hP : IsPGroup 3 P) : Nat.card P ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmaps := mapsTo_of_normal_sylow V hVcard hY
  let rest : MulAut Y →* MulAut V :=
    { toFun := fun α =>
        { toFun := fun v => ⟨α (v : Y), hmaps α v.2⟩
          invFun := fun v => ⟨α⁻¹ (v : Y), hmaps α⁻¹ v.2⟩
          left_inv := fun v => Subtype.ext (by simp)
          right_inv := fun v => Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (map_mul α (a : Y) (b : Y)) }
      map_one' := MulEquiv.ext fun v => Subtype.ext rfl
      map_mul' := fun a b => MulEquiv.ext fun v => Subtype.ext rfl }
  let ρ : P →* MulAut V := rest.comp P.subtype
  have hcardAut : Nat.card (MulAut V) = 48 := by
    have hc : ∀ a b : V, a * b = b * a := fun a b => Subtype.ext (hVcomm a a.2 b b.2)
    have hp : ∀ a : V, a ^ 3 = 1 := fun a => Subtype.ext (hV3 a a.2)
    have := CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary (p := 3) (W := V) hc hp (n := 2) (by rw [hVcard]; norm_num)
    rw [this]
    simp [Fin.prod_univ_succ]
  have hrange : Nat.card ρ.range ≤ 3 := by
    have hpg : IsPGroup 3 ρ.range := hP.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
    have hdvd : Nat.card ρ.range ∣ 48 := hcardAut ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k ≤ 1 := by omega
      interval_cases k <;> simp at hlt
    have : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 hk2).trans hdvd
    norm_num at this
  have hker : Nat.card ρ.ker ≤ 9 := by
    let cV : V →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp V.subtype
    have hle : ρ.ker.map P.subtype ≤ cV.range := by
      rintro _ ⟨α, hα, rfl⟩
      have hfix : ∀ v ∈ V, (α : MulAut Y) v = v := by
        intro v hv
        have := congrArg (fun τ : MulAut V => (τ ⟨v, hv⟩ : Y)) (MonoidHom.mem_ker.1 hα)
        exact this
      obtain ⟨v, hv, hαv⟩ := exists_conj_of_fixes V hVcard hVcomm hY hcent (α : MulAut Y) hfix
      exact ⟨⟨v, hv⟩, hαv.symm⟩
    calc Nat.card ρ.ker = Nat.card (ρ.ker.map P.subtype) :=
          (Subgroup.card_map_of_injective P.subtype_injective).symm
      _ ≤ Nat.card cV.range := Subgroup.card_le_of_le hle
      _ ≤ Nat.card V := Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd cV)
      _ = 9 := hVcard
  have hmul := Subgroup.card_ker_mul_card_range ρ
  calc Nat.card P = Nat.card ρ.ker * Nat.card ρ.range := hmul.symm
    _ ≤ 9 * 3 := Nat.mul_le_mul hker hrange

end Key

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
