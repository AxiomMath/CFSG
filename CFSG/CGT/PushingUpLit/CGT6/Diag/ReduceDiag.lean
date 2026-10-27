module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.ReduceComp

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce

open CFSG CFSG.LocalCores
open scoped commutatorElement

variable {M : Type} [Group M]

theorem not_commutative_of_quasisimple {Y : Subgroup M} (hYq : IsQuasisimple Y)
    (h : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) : False := by
  obtain ⟨-, -, a, b, hab⟩ := hYq
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (h a' a'.2 b' b'.2)

@[expose] def diagHom (K : Subgroup M) (t : M) (hc : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a) :
    ↥K →* M where
  toFun k := (k : M) * (t * (k : M) * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h : (b : M) * (t * (a : M) * t⁻¹) = (t * (a : M) * t⁻¹) * (b : M) :=
      hc b b.2 _ (cj_mul_mem a.2)
    calc ((a * b : ↥K) : M) * (t * ((a * b : ↥K) : M) * t⁻¹)
        = (a : M) * ((b : M) * (t * (a : M) * t⁻¹)) * (t * (b : M) * t⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : M) * ((t * (a : M) * t⁻¹) * (b : M)) * (t * (b : M) * t⁻¹) := by rw [h]
      _ = ((a : M) * (t * (a : M) * t⁻¹)) * ((b : M) * (t * (b : M) * t⁻¹)) := by group

variable [Finite M]

theorem diag_eq {K Y H : Subgroup M} {t : M} (hKq : IsQuasisimple K) (ht2 : t * t = 1)
    (hc : ⁅K, cj t K⁆ = ⊥) (hYq : IsQuasisimple Y) (hYKK' : Y ≤ K ⊔ cj t K)
    (hYt : Y ≤ Subgroup.centralizer ({t} : Set M)) (hKH : K ⊔ cj t K ≤ H)
    (hsub : (Y.subgroupOf (H ⊓ Subgroup.centralizer ({t} : Set M))).IsSubnormal) :
    ∀ y : M, y ∈ Y ↔ ∃ k ∈ K, y = k * (t * k * t⁻¹) := by
  have hc' : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha) b
      hb).symm
  set δ := diagHom K t hc' with hδ
  set D := δ.range with hD
  have hDmem : ∀ d, d ∈ D ↔ ∃ k ∈ K, d = k * (t * k * t⁻¹) := by
    intro d
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hDKK' : D ≤ K ⊔ cj t K := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := (hDmem d).1 hd
    exact Subgroup.mul_mem_sup hk (cj_mul_mem hk)
  have hDt : D ≤ Subgroup.centralizer ({t} : Set M) := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := (hDmem d).1 hd
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    have h : k * (t * k * t⁻¹) = (t * k * t⁻¹) * k := hc' k hk _ (cj_mul_mem hk)
    have h2 : t * (k * (t * k * t⁻¹)) * t⁻¹ = k * (t * k * t⁻¹) := by
      calc t * (k * (t * k * t⁻¹)) * t⁻¹ = (t * k * t⁻¹) * ((t * t) * k * (t⁻¹ * t⁻¹)) := by group
        _ = (t * k * t⁻¹) * k := by
          have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
          rw [ht2, this, ht2]; group
        _ = k * (t * k * t⁻¹) := h.symm
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hhc : ∀ z ∈ K ⊓ cj t K, ∀ d ∈ K ⊔ cj t K, z * d = d * z := by
    intro z hz d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := (Nine7.mem_sup_iff_of_comm hc).1 hd
    have h1 : z * a = a * z := (hc' a ha z hz.2).symm
    have h2 : z * b = b * z := hc' z hz.1 b hb
    calc z * (a * b) = (z * a) * b := by group
      _ = a * (z * b) := by rw [h1]; group
      _ = a * (b * z) := by rw [h2]
      _ = a * b * z := by group
  have hYD : Y ≤ D := by
    refine Nine7.perfect_le_of_le_mul (D := K ⊔ cj t K) (Zc := K ⊓ cj t K) hYq.1 hYKK'
      (inf_le_left.trans le_sup_left) hhc ?_
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (Nine7.mem_sup_iff_of_comm hc).1 (hYKK' hy)
    have hfix : t * (a * b) * t⁻¹ = a * b := by
      have := Subgroup.mem_centralizer_iff.mp (hYt hy) t (Set.mem_singleton t)
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    obtain ⟨b₀, hb₀, rfl⟩ := mem_cj_iff_exists.1 hb
    have ha' : t * a * t⁻¹ ∈ cj t K := cj_mul_mem ha
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have e1 : t * (a * (t * b₀ * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * b₀ := by
      calc t * (a * (t * b₀ * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * ((t * t) * b₀ * (t⁻¹ * t⁻¹)) := by
            group
        _ = (t * a * t⁻¹) * b₀ := by
          rw [ht2, hinv, ht2]; group
    rw [e1] at hfix
    set a' := t * a * t⁻¹ with ha'def
    have hc1 : a⁻¹ * a' = a' * a⁻¹ := hc' a⁻¹ (K.inv_mem ha) a' ha'
    have hc2 : a⁻¹ * a'⁻¹ = a'⁻¹ * a⁻¹ := hc' a⁻¹ (K.inv_mem ha) a'⁻¹ ((cj t K).inv_mem ha')
    have ho1 : a⁻¹ * b₀ = a'⁻¹ * (t * b₀ * t⁻¹) := by
      have h3 : b₀ = a'⁻¹ * (a * (t * b₀ * t⁻¹)) := by
        rw [← hfix]; group
      calc a⁻¹ * b₀ = a⁻¹ * (a'⁻¹ * (a * (t * b₀ * t⁻¹))) := by rw [← h3]
        _ = (a⁻¹ * a'⁻¹) * (a * (t * b₀ * t⁻¹)) := by group
        _ = (a'⁻¹ * a⁻¹) * (a * (t * b₀ * t⁻¹)) := by rw [hc2]
        _ = a'⁻¹ * (t * b₀ * t⁻¹) := by group
    refine ⟨a * a', ⟨⟨a, ha⟩, rfl⟩, a⁻¹ * b₀,
      ⟨K.mul_mem (K.inv_mem ha) hb₀, ?_⟩, ?_⟩
    · rw [ho1]
      exact (cj t K).mul_mem ((cj t K).inv_mem ha') hb
    · calc a * (t * b₀ * t⁻¹) = a' * b₀ := hfix.symm
        _ = a * (a⁻¹ * a') * b₀ := by group
        _ = a * (a' * a⁻¹) * b₀ := by rw [hc1]
        _ = (a * a') * (a⁻¹ * b₀) := by group
  have hDY : D ≤ Y := by
    have hDle : D ≤ H ⊓ Subgroup.centralizer ({t} : Set M) := le_inf (hDKK'.trans hKH) hDt
    have hsubD : (Y.subgroupOf D).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hDle hsub
    have hδ's : Function.Surjective δ.rangeRestrict := δ.rangeRestrict_surjective
    have hY'sub : ((Y.subgroupOf D).comap δ.rangeRestrict).IsSubnormal :=
      hsubD.comap δ.rangeRestrict
    have hKtop : IsComponent (⊤ : Subgroup ↥K) :=
      ⟨isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hKq, Subgroup.IsSubnormal.top⟩
    rcases component_subnormal_subgroup hKtop hY'sub with htop | hcomm
    · intro d hd
      obtain ⟨k, hk⟩ := hδ's ⟨d, hd⟩
      have h1 : δ.rangeRestrict k ∈ Y.subgroupOf D := htop trivial
      rw [hk] at h1
      exact h1
    · exfalso
      have hcen : (Y.subgroupOf D).comap δ.rangeRestrict ≤ Subgroup.center ↥K :=
        Subgroup.commutator_top_left_eq_bot_iff_le_center.mp hcomm
      apply not_commutative_of_quasisimple hYq
      intro a ha b hb
      obtain ⟨k₁, hk₁⟩ := hδ's ⟨a, hYD ha⟩
      obtain ⟨k₂, hk₂⟩ := hδ's ⟨b, hYD hb⟩
      have hk₁Y : k₁ ∈ (Y.subgroupOf D).comap δ.rangeRestrict := by
        show δ.rangeRestrict k₁ ∈ Y.subgroupOf D
        rw [hk₁]
        exact ha
      have hcomm' : k₂ * k₁ = k₁ * k₂ := Subgroup.mem_center_iff.mp (hcen hk₁Y) k₂
      have h2 := congrArg (fun k : ↥K => ((δ.rangeRestrict k : ↥D) : M)) hcomm'
      simp only [map_mul, Subgroup.coe_mul, hk₁, hk₂] at h2
      exact h2.symm
  intro y
  rw [← hDmem]
  exact ⟨fun hy => hYD hy, fun hy => hDY hy⟩

end CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce
