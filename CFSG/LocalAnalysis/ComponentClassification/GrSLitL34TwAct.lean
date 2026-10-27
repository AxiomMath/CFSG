module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutBeta

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.HSFLit.AutBeta

variable {G : Type} [Group G]

private theorem realization_unique {E : Type*} [Group E]
    {q : E →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    {r r' : Equiv.Perm (Fin 42)} (hr : r ∈ R) (hr' : r' ∈ R)
    (h : ∀ e, r * q e * r⁻¹ = r' * q e * r'⁻¹) : r = r' := by
  have hc : r⁻¹ * r' ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun s hs => ?_, R.mul_mem (R.inv_mem hr) hr'⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have h1 := h e
    calc q e * (r⁻¹ * r') = r⁻¹ * (r * q e * r⁻¹) * r' := by group
      _ = r⁻¹ * (r' * q e * r'⁻¹) * r' := by rw [h1]
      _ = r⁻¹ * r' * q e := by group
  rw [centralizer_S_inf_R, mem_bot, inv_mul_eq_one] at hc
  exact hc

private theorem betaHat_congr (J : Subgroup G) {x y : G} (hx : x ∈ normalizer (J : Set G))
    (hy : y ∈ normalizer (J : Set G)) (h : x = y) (e : Jhat J) :
    betaHat J hx e = betaHat J hy e := by
  subst h
  rfl

private theorem betaHat_inv_jq (K : Subgroup G) (n : ↥(normalizer (K : Set G))) (k : ↥K) :
    betaHat K (inv_mem n.2) (jq K k) =
      jq K ⟨(n : G) * k * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 k).mp k.2⟩ := by
  rw [betaHat_jq]
  congr 1
  apply Subtype.ext
  simp only [coe_conjJ, inv_inv]

private theorem exists_real_inv {K : Subgroup G}
    {q : Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqker : q.ker = center (Jhat K)) (n : ↥(normalizer (K : Set G))) :
    ∃ r ∈ R, ∀ e, q (betaHat K (inv_mem n.2) e) = r * q e * r⁻¹ :=
  exists_realization q hqS hqsurj (betaHat K (inv_mem n.2)) fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e

variable [Finite G]

theorem exists_phi {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) :
    ∃ (q : L34Facts.Jhat K →* Equiv.Perm (Fin 42))
      (φ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42)),
      (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧ q.ker = center (L34Facts.Jhat K) ∧
      (∀ n, φ n ∈ R) ∧
      (∀ n : ↥(normalizer (K : Set G)), φ n ∈ S ↔ (n : G) ∈ withKernel K) ∧
      (∀ n : ↥(normalizer (K : Set G)), φ n = 1 ↔ (n : G) ∈ coreActionKernel K) ∧
      (∀ k : ↥K, φ ⟨k, le_normalizer k.2⟩ = q (L34Facts.jq K k)) ∧
      (∀ (n : ↥(normalizer (K : Set G))) (k : ↥K),
        q (L34Facts.jq K ⟨(n : G) * k * (n : G)⁻¹, by
          have := (mem_normalizer_iff.mp n.2 k).mp k.2
          simpa using this⟩) = φ n * q (L34Facts.jq K k) * (φ n)⁻¹) := by
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  choose r hrR hr using fun n : ↥(normalizer (K : Set G)) =>
    exists_real_inv hqS hqsurj hqker n
  have huniq : ∀ (n : ↥(normalizer (K : Set G))) (r' : Equiv.Perm (Fin 42)), r' ∈ R →
      (∀ e, q (betaHat K (inv_mem n.2) e) = r' * q e * r'⁻¹) → r n = r' :=
    fun n r' hr' h => realization_unique hqsurj (hrR n) hr' fun e => by rw [← hr n e, h e]
  have hmul : ∀ n n' : ↥(normalizer (K : Set G)), r (n * n') = r n * r n' := by
    intro n n'
    refine huniq (n * n') (r n * r n') (R.mul_mem (hrR n) (hrR n')) fun e => ?_
    have e1 : betaHat K (inv_mem (n * n').2) e =
        betaHat K (inv_mem n.2) (betaHat K (inv_mem n'.2) e) :=
      (betaHat_congr K _ _ (mul_inv_rev (n : G) (n' : G)) e).trans
        (betaHat_mul K (inv_mem n'.2) (inv_mem n.2) e)
    rw [e1, hr n, hr n']
    group
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42), ∀ n, φ n = r n :=
    ⟨MonoidHom.mk' r hmul, fun n => rfl⟩
  refine ⟨q, φ, hqS, hqsurj, hqker, fun n => (hφ n).symm ▸ hrR n, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hφ]
    constructor
    · intro hS
      obtain ⟨e₀, he₀⟩ := hqsurj _ hS
      have h := mem_withKernel_of_realization hK (inv_mem n.2) hqker (e₀ := e₀)
        (fun e => by rw [hr n e, he₀])
      exact inv_mem_iff.mp h
    · intro hn
      obtain ⟨e₀, he₀⟩ := exists_inner (inv_mem hn) (inv_mem n.2)
      have h1 : r n = (q e₀)⁻¹ := huniq n _ (R.inv_mem (S_le_R (hqS e₀))) fun e => by
        rw [he₀ e]
        simp only [map_mul, map_inv, inv_inv]
      rw [h1]
      exact S.inv_mem (hqS e₀)
  · intro n
    rw [hφ]
    constructor
    · intro h1
      have hq : q.comp (betaHat K (inv_mem n.2)).toMonoidHom = q.comp (MonoidHom.id _) := by
        refine MonoidHom.ext fun e => ?_
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [hr n e, h1]
        group
      have hid : ∀ e, betaHat K (inv_mem n.2) e = e := fun e =>
        DFunLike.congr_fun (hom_ext_of_central (commutator_jhat hK) q hqker.le hq) e
      exact inv_mem_iff.mp ((betaHat_eq_id_iff K (inv_mem n.2)).1 hid)
    · intro hn
      have hid := (betaHat_eq_id_iff K (inv_mem n.2)).2 (inv_mem hn)
      exact huniq n 1 R.one_mem fun e => by rw [hid e]; group
  · intro k
    rw [hφ]
    refine huniq _ _ (S_le_R (hqS _)) fun e => ?_
    have e1 : (⟨(k : G)⁻¹, K.inv_mem k.2⟩ : ↥K) = k⁻¹ := rfl
    rw [betaHat_mem_K K (K.inv_mem k.2) e, e1]
    simp only [map_mul, map_inv, inv_inv]
  · intro n k
    rw [hφ]
    exact (congrArg q (betaHat_inv_jq K n k)).symm.trans (hr n (jq K k))

end CFSG.ComponentClassification.GrSLit.L34Tw
