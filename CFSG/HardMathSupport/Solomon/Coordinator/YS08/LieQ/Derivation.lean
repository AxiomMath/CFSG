module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Skeleton

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

variable {q : ℕ} [Fact q.Prime]

theorem radSeq_eq_of_pCoreOf {S : Type*} [Group S] {R : Subgroup S}
    (hc : pCoreOf q (Subgroup.normalizer (R : Set S)) = R) : ∀ n, radSeq q R n = R
  | 0 => rfl
  | n + 1 => by
    show pCoreOf q (Subgroup.normalizer (radSeq q R n : Set S)) = R
    rw [radSeq_eq_of_pCoreOf hc n]
    exact hc

theorem radInf_eq_of_pCoreOf {S : Type*} [Group S] {R : Subgroup S}
    (hc : pCoreOf q (Subgroup.normalizer (R : Set S)) = R) : radInf q R = R :=
  le_antisymm (iSup_le fun n => (radSeq_eq_of_pCoreOf hc n).le) (le_radInf R)

theorem centralizer_le_of_radRigidInner {S : Type*} [Group S] [Finite S]
    (h : RadRigidInner q S) {R : Subgroup S} (hR : IsRadical q R) :
    ∀ x : S, (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  intro x hx
  set N := Subgroup.normalizer (R : Set S) with hN
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (R : Set S)
    (Subgroup.mem_centralizer_iff.2 fun r hr => (hx r hr).symm)
  have key : ∀ y ∈ N, (∀ t ∈ pCoreOf q N, y * t = t * y) → Nat.Coprime (orderOf y) q → y = 1 := by
    intro y _ hyc hyo
    refine h R hR y (fun r hr => hyc r ?_) hyo
    rw [hN, hR.2.2.1]
    exact hr
  have := centralizer_pCoreOf_le N key x hxN (fun t ht => hx t (by
    rw [hN, hR.2.2.1] at ht; exact ht))
  rwa [hN, hR.2.2.1] at this

theorem fixes_normalizer_of_fixes {S : Type*} [Group S] [Finite S] (R : Subgroup S)
    (hRq : IsPGroup q R) (hLI : ∀ x : S, (∀ r ∈ R, x * r = r * x) → x ∈ R)
    (α : MulAut S) {m : ℕ} (hm : Nat.Coprime m q) (hα : α ^ m = 1) (hfix : ∀ r ∈ R, α r = r) :
    ∀ x ∈ Subgroup.normalizer (R : Set S), α x = x := by
  intro x hx
  obtain ⟨z, hz⟩ : ∃ z : S, z = x⁻¹ * α x := ⟨_, rfl⟩
  have hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.1 hx r).1 hr
  have hcomm : ∀ r ∈ R, z * r = r * z := by
    intro r hr
    have h1 : α (x * r * x⁻¹) = x * r * x⁻¹ := hfix _ (hxR r hr)
    rw [map_mul, map_mul, map_inv, hfix r hr] at h1
    have h2 : α x * r = x * r * x⁻¹ * α x := by
      calc α x * r = (α x * r * (α x)⁻¹) * α x := by group
        _ = x * r * x⁻¹ * α x := by rw [h1]
    rw [hz]
    calc x⁻¹ * α x * r = x⁻¹ * (α x * r) := by group
      _ = x⁻¹ * (x * r * x⁻¹ * α x) := by rw [h2]
      _ = r * (x⁻¹ * α x) := by group
  have hzR : z ∈ R := hLI z hcomm
  have hαz : α z = z := hfix z hzR
  have hαx : α x = x * z := by rw [hz]; group
  have hpow : ∀ n : ℕ, (α ^ n) x = x * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαz, hαx, pow_succ']
      group
  have hzm : z ^ m = 1 := by
    have h1 := hpow m
    rw [hα, MulAut.one_apply] at h1
    have h2 : x * z ^ m = x * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  have hz1 : z = 1 := by
    have h8 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hRq) ⟨z, hzR⟩
    have hk' : orderOf z = q ^ k := by
      rw [← Subgroup.orderOf_coe (⟨z, hzR⟩ : R)] at hk
      exact hk
    have h9 : Nat.Coprime (orderOf z) m := by
      rw [hk']
      exact Nat.Coprime.pow_left k hm.symm
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h9 h8)
  rw [hαx, hz1, mul_one]

@[expose] def RadicalGen (q : ℕ) (S : Type*) [Group S] (U : Subgroup S) : Prop :=
  Subgroup.closure {x : S | ∃ R : Subgroup S, IsPGroup q R ∧ R ≤ U ∧
    (∀ y : S, (∀ r ∈ R, y * r = r * y) → y ∈ R) ∧ x ∈ Subgroup.normalizer (R : Set S)} = ⊤

theorem RadicalGen.map_conj {S : Type*} [Group S] {U : Subgroup S} (h : RadicalGen q S U) (g : S) :
    RadicalGen q S (U.map (MulAut.conj g).toMonoidHom) := by
  unfold RadicalGen at h ⊢
  rw [eq_top_iff]
  have h1 : (⊤ : Subgroup S) = (⊤ : Subgroup S).map (MulAut.conj g).toMonoidHom :=
    (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm
  rw [h1, ← h, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨R, hRq, hRU, hRC, hxN⟩, rfl⟩
  refine ⟨R.map (MulAut.conj g).toMonoidHom, hRq.map _, Subgroup.map_mono hRU, ?_, ?_⟩
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ R := by
      refine hRC _ fun r hr => ?_
      have := hy (g * r * g⁻¹) ⟨r, hr, rfl⟩
      calc (g⁻¹ * y * g) * r = g⁻¹ * (y * (g * r * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r * g⁻¹) * y) * g := by rw [this]
        _ = r * (g⁻¹ * y * g) := by group
    exact ⟨g⁻¹ * y * g, hy', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨x, hxN, rfl⟩

theorem RadicalGen.of_sylow {S : Type*} [Group S] [Finite S] (U₀ : Sylow q S)
    (h : RadicalGen q S (U₀ : Subgroup S)) (U : Sylow q S) : RadicalGen q S (U : Subgroup S) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S U₀ U
  have : (U : Subgroup S) = (U₀ : Subgroup S).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  rw [this]
  exact h.map_conj g

theorem radRigid_of_gen {S : Type*} [Group S] [Finite S] (hBT : HoldsTits S q)
    (hLI : ∀ R : Subgroup S, IsRadical q R → ∀ x : S, (∀ r ∈ R, x * r = r * x) → x ∈ R)
    (hGen : ∀ U : Sylow q S, RadicalGen q S (U : Subgroup S)) : RadRigid q S := by
  intro R hR α hfix hord
  have hα : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  have hD : ∀ R' : Subgroup S, IsPGroup q R' → (∀ y : S, (∀ r ∈ R', y * r = r * y) → y ∈ R') →
      (∀ r ∈ R', α r = r) → ∀ x ∈ Subgroup.normalizer (R' : Set S), α x = x :=
    fun R' hq hLI' hf => fixes_normalizer_of_fixes R' hq hLI' α hord hα hf
  obtain ⟨-, -, -, -, -, U, hU⟩ := canonical_parabolic_tits hBT h0 hp
  rw [radInf_eq_of_pCoreOf hc] at hU
  have hUfix : ∀ u ∈ (U : Subgroup S), α u = u := fun u hu =>
    hD R hp (hLI R ⟨h0, hp, hc, hnt⟩) hfix u (hU hu)
  have hgen := hGen U
  have hF : Subgroup.closure {x : S | ∃ R' : Subgroup S, IsPGroup q R' ∧ R' ≤ (U : Subgroup S) ∧
      (∀ y : S, (∀ r ∈ R', y * r = r * y) → y ∈ R') ∧ x ∈ Subgroup.normalizer (R' : Set S)} ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id S) := by
    rw [Subgroup.closure_le]
    rintro x ⟨R', hq, hRU, hLI', hx⟩
    exact hD R' hq hLI' (fun r hr => hUfix r (hRU hr)) x hx
  rw [hgen] at hF
  exact MulEquiv.ext fun x => hF (Subgroup.mem_top x)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
