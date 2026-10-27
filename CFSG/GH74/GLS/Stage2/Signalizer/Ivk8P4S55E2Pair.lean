module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Hyp89

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG
open scoped commutatorElement

section Generic

theorem le_center_of_normal_isPGroup {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    {p : ℕ} [Fact p.Prime] {Q : Subgroup K} (hQ : Q.Normal) (hp : IsPGroup p ↥Q) :
    Q ≤ center K := by
  have hs : IsSimpleGroup (K ⧸ center K) := hq.2.1
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    exact ⟨a, b, hab⟩
  let π : K →* K ⧸ center K := QuotientGroup.mk' (center K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN : (Q.map π).Normal := hQ.map π hπ
  rcases hs.eq_bot_or_eq_top_of_normal (Q.map π) with h | h
  · intro x hx
    have : π x ∈ Q.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    have hP : IsPGroup p (K ⧸ center K) := by
      have h1 := hp.map π
      rw [h] at h1
      exact h1.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial (K ⧸ center K) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hcn : Nontrivial ↥(center (K ⧸ center K)) := hP.center_nontrivial
    have hcen : (center (K ⧸ center K)) = ⊤ := by
      rcases hs.eq_bot_or_eq_top_of_normal (center (K ⧸ center K)) with h0 | h0
      · exfalso
        rw [h0] at hcn
        exact not_nontrivial_iff_subsingleton.mpr inferInstance hcn
      · exact h0
    have : a ∈ center (K ⧸ center K) := by rw [hcen]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem commute_of_comm_central {Γ : Type} [Group Γ] {K : Subgroup Γ} (hq : IsQuasisimple ↥K)
    {x : Γ} (hx : x ∈ normalizer (K : Set Γ))
    (h : ∀ k ∈ K, ∀ z ∈ K, (x * k * x⁻¹ * k⁻¹) * z = z * (x * k * x⁻¹ * k⁻¹)) :
    ∀ k ∈ K, x * k = k * x := by
  have hxK : ∀ k : ↥K, x * (k : Γ) * x⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp hx k).mp k.2
  let φ : ↥K → ↥K := fun k => ⟨x * k * x⁻¹, hxK k⟩
  have hφ1 : φ 1 = 1 := by
    apply Subtype.ext
    simp [φ]
  have hcen : ∀ y : ↥K, y⁻¹ * φ y ∈ center ↥K := by
    intro y
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have hc := h y y.2 z z.2
    have hyc : (y : Γ)⁻¹ * (x * y * x⁻¹ * (y : Γ)⁻¹) = (x * y * x⁻¹ * (y : Γ)⁻¹) * (y : Γ)⁻¹ := by
      have := h y y.2 (y : Γ)⁻¹ (K.inv_mem y.2)
      exact this.symm
    have e1 : ((y⁻¹ * φ y : ↥K) : Γ) = x * y * x⁻¹ * (y : Γ)⁻¹ := by
      show (y : Γ)⁻¹ * (x * y * x⁻¹) = _
      calc (y : Γ)⁻¹ * (x * y * x⁻¹) =
          (y : Γ)⁻¹ * (x * y * x⁻¹ * (y : Γ)⁻¹) * y := by group
        _ = (x * y * x⁻¹ * (y : Γ)⁻¹) * (y : Γ)⁻¹ * y := by rw [hyc]
        _ = x * y * x⁻¹ * (y : Γ)⁻¹ := by group
    show (z : Γ) * ((y⁻¹ * φ y : ↥K) : Γ) = ((y⁻¹ * φ y : ↥K) : Γ) * z
    rw [e1]
    exact hc.symm
  let δ : ↥K →* ↥(center ↥K) :=
    { toFun := fun y => ⟨y⁻¹ * φ y, hcen y⟩
      map_one' := by
        apply Subtype.ext
        simp [hφ1]
      map_mul' := by
        intro y z
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hcen y) z⁻¹
        have hφm : φ (y * z) = φ y * φ z := by
          apply Subtype.ext
          simp [φ, mul_assoc]
        calc (y * z)⁻¹ * φ (y * z) = z⁻¹ * (y⁻¹ * φ y) * φ z := by
              rw [hφm, mul_inv_rev]
              group
          _ = (y⁻¹ * φ y * z⁻¹) * φ z := by rw [hc]
          _ = (y⁻¹ * φ y) * (z⁻¹ * φ z) := by group }
  have hker : commutator ↥K ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hq.1.commutator_eq_top] at hker
  intro k hk
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top ⟨k, hk⟩)))
  simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h1
  have h1' : ((⟨k, hk⟩ : ↥K)⁻¹ * φ ⟨k, hk⟩ : ↥K) = 1 := h1
  have h2' := congrArg Subtype.val h1'
  have h3 : (k : Γ)⁻¹ * (x * k * x⁻¹) = 1 := by simpa [φ] using h2'
  have h2 : x * k * x⁻¹ = k := by
    calc x * k * x⁻¹ = k * ((k : Γ)⁻¹ * (x * k * x⁻¹)) := by group
      _ = k := by rw [h3, mul_one]
  calc x * k = (x * k * x⁻¹) * x := by group
    _ = k * x := by rw [h2]

theorem isPGroup_closure_pair_subtype {G : Type} [Group G] {H : Subgroup G} (x y : ↥H) {p : ℕ}
    (h : IsPGroup p ↥(closure ({(x : G), (y : G)} : Set G))) :
    IsPGroup p ↥(closure ({x, y} : Set ↥H)) := by
  have hmap : (closure ({x, y} : Set ↥H)).map H.subtype = closure ({(x : G), (y : G)} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  let e := (closure ({x, y} : Set ↥H)).equivMapOfInjective H.subtype H.subtype_injective
  have h' : IsPGroup p ↥((closure ({x, y} : Set ↥H)).map H.subtype) := by
    rw [hmap]
    exact h
  exact h'.of_equiv e.symm

end Generic

theorem mem_sup_zpowers_decomp {Γ : Type} [Group Γ] {K : Subgroup Γ} {a : Γ}
    (ha : a ∈ normalizer (K : Set Γ)) {g : Γ} (hg : g ∈ K ⊔ zpowers a) :
    ∃ (i : ℤ) (k : Γ), k ∈ K ∧ g = a ^ i * k := by
  have hnorm : ∀ (i : ℤ) (k : Γ), k ∈ K → a ^ i * k * a ^ (-i) ∈ K := by
    intro i k hk
    have h1 : a ^ i ∈ normalizer (K : Set Γ) := Subgroup.zpow_mem _ ha i
    have := (Subgroup.mem_normalizer_iff.mp h1 k).mp hk
    simpa [zpow_neg] using this
  let S : Subgroup Γ :=
    { carrier := {g | ∃ (i : ℤ) (k : Γ), k ∈ K ∧ g = a ^ i * k}
      one_mem' := ⟨0, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, k, hk, rfl⟩ ⟨j, k', hk', rfl⟩
        refine ⟨i + j, (a ^ (-j) * k * a ^ j) * k', K.mul_mem ?_ hk', ?_⟩
        · have := hnorm (-j) k hk
          simpa using this
        · simp only [zpow_add, zpow_neg]
          group
      inv_mem' := by
        rintro _ ⟨i, k, hk, rfl⟩
        refine ⟨-i, a ^ i * k⁻¹ * a ^ (-i), ?_, ?_⟩
        · exact hnorm i k⁻¹ (K.inv_mem hk)
        · simp only [zpow_neg]
          group }
  have hle : K ⊔ zpowers a ≤ S := by
    refine sup_le (fun k hk => ⟨0, k, hk, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, 1, K.one_mem, by simp⟩
  exact hle hg

section Pair

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ}

theorem exists_nonPGroup_pair (hf : Hyp89 p ρ K a) :
    ∃ k ∈ K, ¬ IsPGroup p ↥(closure ({a, k * a * k⁻¹} : Set Γ)) := by
  classical
  by_contra hcon0
  have hcon : ∀ k ∈ K, IsPGroup p ↥(closure ({a, k * a * k⁻¹} : Set Γ)) :=
    fun k hk => by_contra fun h => hcon0 ⟨k, hk, h⟩
  have : Fact p.Prime := ⟨hf.prime⟩
  let H : Subgroup Γ := K ⊔ zpowers a
  have haH : a ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hKH : K ≤ H := le_sup_left
  have hdec : ∀ g ∈ H, ∃ (i : ℤ) (k : Γ), k ∈ K ∧ g = a ^ i * k :=
    fun g hg => mem_sup_zpowers_decomp hf.norm hg
  have hBS := (CFSG.GroupTheory.baer_conjugate_pair_p_core p (G := ↥H)).2 ⟨a, haH⟩ (by
    intro g
    obtain ⟨i, k, hk, hg⟩ := hdec g g.2
    have h1 : ((g⁻¹ * ⟨a, haH⟩ * g : ↥H) : Γ) = k⁻¹ * a * (k⁻¹)⁻¹ := by
      have : (g : Γ) = a ^ i * k := hg
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
      simp only [mul_inv_rev, inv_inv]
      group
    apply isPGroup_closure_pair_subtype
    have : ({((⟨a, haH⟩ : ↥H) : Γ), ((g⁻¹ * ⟨a, haH⟩ * g : ↥H) : Γ)} : Set Γ) =
        {a, k⁻¹ * a * (k⁻¹)⁻¹} := by rw [h1]
    rw [this]
    exact hcon k⁻¹ (K.inv_mem hk))
  let R₀ : Subgroup ↥H := CFSG.pCore p ↥H
  let R : Subgroup Γ := R₀.map H.subtype
  have hR : IsPGroup p ↥R := CFSG.pCore_isPGroup.map H.subtype
  have haR : a ∈ R := ⟨⟨a, haH⟩, hBS, rfl⟩
  have hRconj : ∀ h ∈ H, ∀ x ∈ R, h * x * h⁻¹ ∈ R := by
    rintro h hh _ ⟨x₀, hx₀, rfl⟩
    exact ⟨⟨h, hh⟩ * x₀ * ⟨h, hh⟩⁻¹, (CFSG.pCore_normal (p := p) (G := ↥H)).conj_mem x₀ hx₀ ⟨h, hh⟩,
      rfl⟩
  let Q : Subgroup ↥K := R.comap K.subtype
  have hQn : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ((g * n * g⁻¹ : ↥K) : Γ) ∈ R
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hRconj g (hKH g.2) n hn
  have hQp : IsPGroup p ↥Q := hR.comap_of_injective K.subtype K.subtype_injective
  have hQc := le_center_of_normal_isPGroup hf.quasi hQn hQp
  have hcomm : ∀ k ∈ K, ∀ z ∈ K, (a * k * a⁻¹ * k⁻¹) * z = z * (a * k * a⁻¹ * k⁻¹) := by
    intro k hk z hz
    have hmemK : a * k * a⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp hf.norm k).mp hk) (K.inv_mem hk)
    have hmemR : a * k * a⁻¹ * k⁻¹ ∈ R := by
      have h1 : k * a⁻¹ * k⁻¹ ∈ R := by
        have := hRconj k (hKH hk) a⁻¹ (R.inv_mem haR)
        exact this
      have h2 : a * (k * a⁻¹ * k⁻¹) ∈ R := R.mul_mem haR h1
      have e : a * (k * a⁻¹ * k⁻¹) = a * k * a⁻¹ * k⁻¹ := by group
      rwa [e] at h2
    have hq : (⟨a * k * a⁻¹ * k⁻¹, hmemK⟩ : ↥K) ∈ center ↥K := hQc hmemR
    have := Subgroup.mem_center_iff.mp hq ⟨z, hz⟩
    exact congrArg Subtype.val this.symm
  have hcen := commute_of_comm_central hf.quasi hf.norm hcomm
  apply hf.acts
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : a * x = x * a := hcen x hx
  have : Commute (a ^ n) x := Commute.zpow_left (show Commute a x from hc) n
  rw [Subgroup.mem_bot, commutatorElement_def]
  have h3 : x * a ^ n = a ^ n * x := this.symm.eq
  calc x * a ^ n * x⁻¹ * (a ^ n)⁻¹ = (a ^ n * x) * x⁻¹ * (a ^ n)⁻¹ := by rw [h3]
    _ = 1 := by group

end Pair

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
