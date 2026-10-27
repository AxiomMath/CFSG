module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Grp
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Quot

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup Equiv

section AutC

variable {E : Type} [Group E]

theorem aut_sq_of_fix (hE2 : ∀ e : E, e * e = 1) (hEc : ∀ a b : E, a * b = b * a)
    {z : MulAut E} (hzz : z * z = 1) {c : MulAut E} (hcz : c * z = z * c)
    (hcV : ∀ e : E, z e = e → c e = e) : c * c = 1 := by
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hEc }
  have hinv : ∀ e : E, e⁻¹ = e := fun e => inv_eq_of_mul_eq_one_right (hE2 e)
  have hzz' : ∀ e : E, z (z e) = e := fun e => by
    have := congrArg (fun m : MulAut E => m e) hzz
    simpa using this
  have hcz' : ∀ e : E, c (z e) = z (c e) := fun e => by
    have := congrArg (fun m : MulAut E => m e) hcz
    simpa using this
  have hψ : ∀ p : E, z (z p * p) = z p * p := by
    intro p
    rw [map_mul, hzz']
    exact mul_comm _ _
  ext p
  have E1 : z (c p) * c p = z p * p := by
    have h := hcV (z p * p) (hψ p)
    rw [map_mul, hcz'] at h
    exact h
  have hq : z (c p * p) = c p * p := by
    have h1 : z (c p * p) * (c p * p) = 1 := by
      calc z (c p * p) * (c p * p) = (z (c p) * z p) * (c p * p) := by rw [map_mul]
        _ = (z (c p) * c p) * (z p * p) := mul_mul_mul_comm _ _ _ _
        _ = (z p * p) * (z p * p) := by rw [E1]
        _ = 1 := hE2 _
    have := eq_inv_of_mul_eq_one_left h1
    rw [this, hinv]
  have h2 := hcV _ hq
  rw [map_mul] at h2
  show c (c p) = p
  exact mul_right_cancel (h2.trans (mul_comm (c p) p))

end AutC


theorem iso_Z2_S3 {C : Type} [Group C] [Finite C] {z : C} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ a : C, a * z = z * a)
    (φ : C →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hker : ∀ a : C, φ a = 1 → a = 1 ∨ a = z) (hφz : φ z = 1)
    (ht : ∃ t : C, t * t = 1 ∧ φ t ≠ 1) :
    Nonempty (C ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨t, htt, hφt⟩ := ht
  have hz3 : z ^ 3 = z := by rw [pow_succ, pow_two, hzz, one_mul]
  have hord2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have hkerz : φ.ker = zpowers z := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      rcases hker a h with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact mem_zpowers z
    · intro h
      rcases mem_zpowers_invol hzz h with h1 | h1
      · rw [h1]; exact map_one φ
      · rw [h1]; exact hφz
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top_of_surjective φ hφs
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
  have hCcard : Nat.card C = 12 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkerz, hrange, Nat.card_zpowers, hord2, Subgroup.card_top, hperm] at h
    omega
  have hτ2 : φ t * φ t = 1 := by rw [← map_mul, htt, map_one]
  have hsignτ : Perm.sign (φ t) = -1 := by
    have key : ∀ σ : Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → Perm.sign σ = -1 := by decide
    exact key _ hτ2 hφt
  have hconjκ : φ t * finRotate 3 * (φ t)⁻¹ = (finRotate 3)⁻¹ := by
    have key : ∀ σ : Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → σ * finRotate 3 * σ⁻¹ = (finRotate 3)⁻¹ := by
      decide
    exact key _ hτ2 hφt
  have hκ3 : (finRotate 3) ^ 3 = (1 : Perm (Fin 3)) := by decide
  have hsignκ : Perm.sign (finRotate 3) = 1 := by decide
  obtain ⟨f₀, hf₀⟩ := hφs (finRotate 3)
  obtain ⟨f, hf3, hφf⟩ : ∃ f : C, f ^ 3 = 1 ∧ φ f = finRotate 3 := by
    have h1 : φ (f₀ ^ 3) = 1 := by rw [map_pow, hf₀, hκ3]
    rcases hker _ h1 with h | h
    · exact ⟨f₀, h, hf₀⟩
    · refine ⟨f₀ * z, ?_, by rw [map_mul, hf₀, hφz, mul_one]⟩
      have hc : Commute f₀ z := hzc f₀
      rw [hc.mul_pow, h, hz3, hzz]
  have hf1 : f ≠ 1 := by
    intro h
    have : finRotate 3 = 1 := by rw [← hφf, h, map_one]
    exact absurd this (by decide)
  have hordf : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  have htft : t * f * t⁻¹ = f⁻¹ := by
    have h1 : φ (t * f * t⁻¹ * f) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hφf]
      rw [hconjκ]; group
    rcases hker _ h1 with h | h
    · exact eq_inv_of_mul_eq_one_left h
    · exfalso
      have h2 : t * f * t⁻¹ = z * f⁻¹ := by
        have : t * f * t⁻¹ = (t * f * t⁻¹ * f) * f⁻¹ := by group
        rw [this, h]
      have h3 : (t * f * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hf3]; group
      rw [h2] at h3
      have hc : Commute z f⁻¹ := (hzc f⁻¹).symm
      rw [hc.mul_pow, hz3, inv_pow, hf3, inv_one, mul_one] at h3
      exact hz1 h3
  have hN : ∀ q ∈ zpowers f, t * q * t⁻¹ ∈ zpowers f := by
    intro q hq
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hq
    rw [← conj_zpow, htft]
    exact zpow_mem (inv_mem (mem_zpowers f)) k
  have htsq : t * t ∈ zpowers f := by rw [htt]; exact one_mem _
  have hsignpow : ∀ k : ℤ, Perm.sign (φ (f ^ k)) = 1 := by
    intro k
    rw [map_zpow, hφf, map_zpow, hsignκ]
    simp
  have htN : t ∉ zpowers f := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have := hsignpow k
    rw [hk, hsignτ] at this
    exact absurd this (by decide)
  have hMcard : Nat.card ↥(zpowers f ⊔ zpowers t) = 6 := by
    rw [card_sup_zpowers_sq htsq hN htN, Nat.card_zpowers, hordf]
  have hMidx : (zpowers f ⊔ zpowers t).index = 2 := by
    have := Subgroup.card_mul_index (zpowers f ⊔ zpowers t)
    rw [hMcard, hCcard] at this
    omega
  have hzM : z ∉ zpowers f ⊔ zpowers t := by
    intro h
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq htsq hN).1 h
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hq
      have h3 : z ^ 3 = 1 := by
        rw [h1, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf3, one_zpow]
      rw [hz3] at h3
      exact hz1 h3
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hq
      have h2 : φ z = φ (f ^ k * t) := by rw [h1]
      rw [hφz, map_mul] at h2
      have := congrArg Perm.sign h2
      rw [map_one, map_mul, hsignpow k, hsignτ] at this
      exact absurd this (by decide)
  have hrules := index_two_rules (S := ⊤) (K := zpowers f ⊔ zpowers t) le_top (by
    rw [relIndex_top_right]; exact hMidx)
  let ε : C →* Multiplicative (ZMod 2) :=
    { toFun := fun a => if a ∈ zpowers f ⊔ zpowers t then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := by
        intro a b
        by_cases ha : a ∈ zpowers f ⊔ zpowers t <;> by_cases hb : b ∈ zpowers f ⊔ zpowers t
        · simp [ha, hb, (zpowers f ⊔ zpowers t).mul_mem ha hb]
        · have : a * b ∉ zpowers f ⊔ zpowers t := fun h =>
            hb (by have := (zpowers f ⊔ zpowers t).mul_mem ((zpowers f ⊔ zpowers t).inv_mem ha) h
                   simpa using this)
          simp [ha, hb, this]
        · have : a * b ∉ zpowers f ⊔ zpowers t := fun h =>
            ha (by have := (zpowers f ⊔ zpowers t).mul_mem h ((zpowers f ⊔ zpowers t).inv_mem hb)
                   simpa using this)
          simp [ha, hb, this]
        · have := hrules.1 a (mem_top a) b (mem_top b) ha hb
          simp only [ha, hb, this, ite_true, ite_false]
          decide }
  have hεz : ε z ≠ 1 := by
    have : ε z = Multiplicative.ofAdd 1 := by simp [ε, hzM]
    rw [this]
    decide
  let Φ : C →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3) := ε.prod φ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ε a = 1 ∧ φ a = 1 := Prod.ext_iff.1 ha
    rcases hker a h1.2 with h | h
    · exact h
    · exfalso
      rw [h] at h1
      exact hεz h1.1
  have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; rfl
  exact ⟨MulEquiv.ofBijective Φ (hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hZ2, hperm, hCcard]))⟩



section AutC2

variable {E : Type} [Group E] [Finite E]

theorem autC_iso (hE2 : ∀ e : E, e * e = 1) (hEc : ∀ a b : E, a * b = b * a)
    (X Sb : Subgroup (MulAut E)) (hSyl : Sylow2In Sb X)
    {z t f : MulAut E} (hzS : z ∈ Sb) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (htS : t ∈ Sb) (htt : t * t = 1)
    (hSb : ∀ s ∈ Sb, s = 1 ∨ s = z ∨ s = t ∨ s = z * t) (hSbz : ∀ s ∈ Sb, s * z = z * s)
    (hfix : Nat.card {e : E // z e = e} = 4)
    (htV : ∃ v : E, z v = v ∧ t v ≠ v)
    (hfX : f ∈ X) (hfz : f * z = z * f) (hf3 : ∃ k : ℕ, f ^ 3 ^ k = 1)
    (hfV : ∃ v : E, z v = v ∧ f v ≠ v) :
    Nonempty (↥(X ⊓ centralizer ({z} : Set (MulAut E))) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (MulAut E) := X ⊓ centralizer ({z} : Set (MulAut E)) with hC
  have hmemC : ∀ c : MulAut E, c ∈ C ↔ c ∈ X ∧ c * z = z * c := by
    intro c
    rw [hC, mem_inf, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  have hzC : z ∈ C := (hmemC z).2 ⟨hSyl.1 hzS, rfl⟩
  have htC : t ∈ C := (hmemC t).2 ⟨hSyl.1 htS, hSbz t htS⟩
  have hfC : f ∈ C := (hmemC f).2 ⟨hfX, hfz⟩
  have hSbC : Sb ≤ C := fun s hs => (hmemC s).2 ⟨hSyl.1 hs, hSbz s hs⟩
  have hpres : ∀ c : MulAut E, c * z = z * c → ∀ e : E, z e = e → z (c e) = c e := by
    intro c hc e he
    have h := congrArg (fun m : MulAut E => m e) hc
    have h' : c (z e) = z (c e) := h
    rw [← h', he]
  let Ω : Type := {e : E // z e = e ∧ e ≠ 1}
  have hΩcard : Nat.card Ω = 3 := by
    have h1 : Nat.card {e : E // z e = e} = ({e : E | z e = e} : Set E).ncard :=
      (Nat.card_coe_set_eq _).symm
    have h2 : ({e : E | z e = e ∧ e ≠ 1} : Set E) = ({e : E | z e = e} : Set E) \ {1} := by
      ext e; simp
    have h3 : Nat.card Ω = ({e : E | z e = e ∧ e ≠ 1} : Set E).ncard := (Nat.card_coe_set_eq _).symm
    rw [h3, h2, Set.ncard_sdiff_singleton_of_mem (by simp), ← h1, hfix]
  let : MulAction ↥C Ω :=
    { smul := fun c ω => ⟨(c : MulAut E) ω.1, hpres c ((hmemC c).1 c.2).2 ω.1 ω.2.1,
        fun h => ω.2.2 ((c : MulAut E).injective (by rw [h, map_one]))⟩
      one_smul := fun ω => Subtype.ext rfl
      mul_smul := fun c d ω => Subtype.ext rfl }
  let r : ↥C →* Equiv.Perm Ω := MulAction.toPermHom ↥C Ω
  have hr : ∀ (c : ↥C) (ω : Ω), ((r c) ω).1 = (c : MulAut E) ω.1 := fun c ω => rfl
  have hkerfix : ∀ c : ↥C, r c = 1 → ∀ e : E, z e = e → (c : MulAut E) e = e := by
    intro c hc e he
    by_cases he1 : e = 1
    · rw [he1, map_one]
    · have := hr c ⟨e, he, he1⟩
      rw [hc] at this
      exact this.symm
  have hker2 : ∀ c : ↥C, r c = 1 → (c : MulAut E) * (c : MulAut E) = 1 := fun c hc =>
    aut_sq_of_fix hE2 hEc hzz ((hmemC c).1 c.2).2 (hkerfix c hc)
  have hzr : r ⟨z, hzC⟩ = 1 := by
    ext ω
    exact ω.2.1
  have hSylC : SylowIn 2 Sb C := by
    refine ⟨hSbC, hSyl.2.1, ?_⟩
    intro hdvd
    apply hSyl.2.2
    have h := relIndex_mul_relIndex Sb C X hSbC (inf_le_left : C ≤ X)
    rw [← h]
    exact Dvd.dvd.mul_right hdvd _
  have hKp : IsPGroup 2 ↥r.ker := by
    rw [IsPGroup.iff_orderOf]
    intro k
    have hk2 : k * k = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hker2 k.1 k.2
    have hd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hk2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
  have hKle : r.ker ≤ Sb.subgroupOf C := by
    have := hKp.le_sylow_of_normal hSylC.toSylow
    exact this
  have hker : ∀ c : ↥C, r c = 1 → c = 1 ∨ c = ⟨z, hzC⟩ := by
    intro c hc
    have hcS : (c : MulAut E) ∈ Sb := mem_subgroupOf.1 (hKle hc)
    obtain ⟨v, hv, htv⟩ := htV
    have htvz : z (t v) = t v := hpres t (hSbz t htS) v hv
    rcases hSb _ hcS with h | h | h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
    · exfalso
      have := hkerfix c hc v hv
      rw [h] at this
      exact htv this
    · exfalso
      have := hkerfix c hc v hv
      rw [h] at this
      apply htv
      have h2 : (z * t) v = z (t v) := rfl
      rw [h2, htvz] at this
      exact this
  have hperm : Nat.card (Equiv.Perm Ω) = 6 := by rw [Nat.card_perm, hΩcard]; rfl
  have hrt : r ⟨t, htC⟩ ≠ 1 := by
    obtain ⟨v, hv, htv⟩ := htV
    intro h
    exact htv (hkerfix ⟨t, htC⟩ h v hv)
  have hrf : r ⟨f, hfC⟩ ≠ 1 := by
    obtain ⟨v, hv, hfv⟩ := hfV
    intro h
    exact hfv (hkerfix ⟨f, hfC⟩ h v hv)
  have h2dvd : 2 ∣ Nat.card r.range := by
    have hord : orderOf (r ⟨t, htC⟩) = 2 := by
      apply orderOf_eq_prime ?_ hrt
      rw [pow_two, ← map_mul]
      have : (⟨t, htC⟩ : ↥C) * ⟨t, htC⟩ = 1 := Subtype.ext htt
      rw [this, map_one]
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard r.range ⟨⟨t, htC⟩, rfl⟩
  have h3dvd : 3 ∣ Nat.card r.range := by
    obtain ⟨k, hk⟩ := hf3
    have hfk : (r ⟨f, hfC⟩) ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨f, hfC⟩ : ↥C) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have hd : orderOf (r ⟨f, hfC⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hfk
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    have hi0 : i ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hi'
      exact hrf (orderOf_eq_one_iff.1 hi')
    have : 3 ∣ orderOf (r ⟨f, hfC⟩) := by rw [hi']; exact dvd_pow_self 3 hi0
    exact this.trans (Subgroup.orderOf_dvd_natCard r.range ⟨⟨f, hfC⟩, rfl⟩)
  have hrange : r.range = ⊤ := by
    have hdvd : Nat.card r.range ∣ 6 := hperm ▸ Subgroup.card_subgroup_dvd_card r.range
    have h6 : 6 ∣ Nat.card r.range :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
    have : Nat.card r.range = 6 := Nat.dvd_antisymm hdvd h6
    apply Subgroup.eq_top_of_card_eq
    rw [this, hperm]
  have hrs : Function.Surjective r := by
    intro σ
    have : σ ∈ r.range := by rw [hrange]; exact Subgroup.mem_top σ
    exact this
  let e₃ : Ω ≃ Fin 3 := Finite.equivFinOfCardEq hΩcard
  let φ : ↥C →* Equiv.Perm (Fin 3) :=
    (e₃.permCongrHom : Equiv.Perm Ω ≃* Equiv.Perm (Fin 3)).toMonoidHom.comp r
  have hφs : Function.Surjective φ := (e₃.permCongrHom.surjective).comp hrs
  have hφinj : ∀ a : ↥C, φ a = 1 → r a = 1 := by
    intro a h
    apply e₃.permCongrHom.injective
    rw [map_one]
    exact h
  have hφz : φ ⟨z, hzC⟩ = 1 := by
    show e₃.permCongrHom (r ⟨z, hzC⟩) = 1
    rw [hzr, map_one]
  exact iso_Z2_S3 (z := ⟨z, hzC⟩) (Subtype.ext hzz) (fun h => hz1 (congrArg Subtype.val h))
    (fun a => Subtype.ext ((hmemC a).1 a.2).2) φ hφs (fun a ha => hker a (hφinj a ha)) hφz
    ⟨⟨t, htC⟩, Subtype.ext htt, fun h => hrt (hφinj _ h)⟩

end AutC2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
