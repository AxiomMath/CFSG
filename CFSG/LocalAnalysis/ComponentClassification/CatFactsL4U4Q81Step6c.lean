module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6b
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81E8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}

theorem exists_conj_S (hs : Setting46e t L p f S w z V i j) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer {t} ⊓ centralizer {z})
    (hTP : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ P) :
    ∃ n : X, n ∈ centralizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) ∧
      P ≤ Q81.conjSub S n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNq, hS₀⟩ := hs.lemma44a_z
  set H₀ := centralizer ({t} : Set X) ⊓ centralizer {z} with hH₀
  have hSH : S ≤ H₀ := hS₀.le
  obtain ⟨P', hP', hPP'⟩ := Q81.exists_isSylowOf_ge hP hPC
  obtain ⟨g, hg, hgP'⟩ := L415.exists_map_conj hS₀ hP'
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H₀) with hπ
  have hSbar : (S.subgroupOf H₀).map π = ⊤ := by
    have h1 := isSylowOf_map π (Q81.isSylowOf_subgroupOf hS₀ le_rfl)
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h1
    exact (h1.eq_of_le le_top le_top (hNq.to_subgroup ⊤)).symm
  have hgS : π ⟨g, hg⟩ ∈ (S.subgroupOf H₀).map π := by rw [hSbar]; exact mem_top _
  obtain ⟨s', hs'S, hs'g⟩ := hgS
  have hO : s'⁻¹ * ⟨g, hg⟩ ∈ pPrimeCore 2 ↥H₀ := QuotientGroup.eq.mp hs'g
  set o : ↥H₀ := s'⁻¹ * ⟨g, hg⟩ with ho
  set n : X := ((s' * o * s'⁻¹ : ↥H₀) : X) with hn
  have hnO : s' * o * s'⁻¹ ∈ pPrimeCore 2 ↥H₀ :=
    (inferInstance : (pPrimeCore 2 ↥H₀).Normal).conj_mem o hO s'
  have hgns : g = n * (s' : X) := by
    rw [hn, ho]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hSs : Q81.conjSub S (s' : X) = S := by
    ext x
    rw [Q81.mem_conjSub]
    constructor
    · intro hx
      have h1 : x = (s' : X) * ((s' : X)⁻¹ * x * s') * (s' : X)⁻¹ := by group
      rw [h1]
      exact mul_mem (mul_mem hs'S hx) (inv_mem hs'S)
    · intro hx
      exact mul_mem (mul_mem (inv_mem hs'S) hx) hs'S
  have hSg : P' = Q81.conjSub S n := by
    rw [hgP', hgns]
    change Q81.conjSub S (n * (s' : X)) = _
    rw [← Q81.conjSub_conjSub, hSs]
  have hPS : P ≤ Q81.conjSub S n := hSg ▸ hPP'
  refine ⟨n, mem_centralizer_iff.mpr fun x hx => ?_, hPS⟩
  have hxS : x ∈ S := hs.setup.T_le hx
  have hy : n⁻¹ * x * n ∈ S := Q81.mem_conjSub.mp (hPS (hTP hx))
  have hxH := hSH hxS
  have hyH := hSH hy
  have hnH : n ∈ H₀ := (s' * o * s'⁻¹).2
  have himg : π ⟨n⁻¹ * x * n, hyH⟩ = π ⟨x, hxH⟩ := by
    have h1 : (⟨n⁻¹ * x * n, hyH⟩ : ↥H₀) = (⟨n, hnH⟩ : ↥H₀)⁻¹ * ⟨x, hxH⟩ * ⟨n, hnH⟩ :=
      Subtype.ext (by simp)
    have h2 : π ⟨n, hnH⟩ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hnO
    rw [h1, map_mul, map_mul, map_inv, h2, inv_one, one_mul, mul_one]
  have hinj := GSThmB.OddQuot.injOn_of_isPGroup (H := ↥H₀) (R := S.subgroupOf H₀)
    (hS₀.isPGroup.of_equiv (subgroupOfEquivOfLe hSH).symm)
  have h3 := hinj (show (⟨n⁻¹ * x * n, hyH⟩ : ↥H₀) ∈ S.subgroupOf H₀ from hy)
    (show (⟨x, hxH⟩ : ↥H₀) ∈ S.subgroupOf H₀ from hxS) himg
  have h4 : n⁻¹ * x * n = x := congrArg Subtype.val h3
  calc x * n = n * (n⁻¹ * x * n) := by group
    _ = n * x := by rw [h4]

theorem le_X_of_normal_R (hs : Setting46e t L p f S w z V i j) {R E : Subgroup X}
    (hRp : IsPGroup 2 R) (hRz : R ≤ centralizer ({z} : Set X))
    (hTR : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ R) (hER : E ≤ R) (hEt : E ≤ centralizer {t})
    (hEn : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ ∈ E) (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    E ≤ closure {t, w ^ (orderOf w / 2), z} := by
  have hTt : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({t} : Set X) :=
    hs.setup.T_le.trans hs.sylow.le
  obtain ⟨n, hnT, hPS⟩ := hs.exists_conj_S (hRp.to_le inf_le_left)
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hRz (mem_inf.mp hx).1⟩) (le_inf hTR hTt)
  have hFS : Q81.conjSub E n⁻¹ ≤ S := by
    intro x hx
    rw [Q81.mem_conjSub, inv_inv] at hx
    have h1 := Q81.mem_conjSub.mp (hPS (mem_inf.mpr ⟨hER hx, hEt hx⟩))
    rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h1
  have hFn : ∀ d ∈ S ⊓ L, ∀ x ∈ Q81.conjSub E n⁻¹, d * x * d⁻¹ ∈ Q81.conjSub E n⁻¹ := by
    intro d hd x hx
    rw [Q81.mem_conjSub, inv_inv] at hx ⊢
    have hdT : d ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_right hd)
    have hnd : n * d = d * n := (mem_centralizer_iff.mp hnT d hdT).symm
    have h1 := hEn d (hTR hdT) _ hx
    have h2 : n * (d * x * d⁻¹) * n⁻¹ = d * (n * x * n⁻¹) * d⁻¹ := by
      calc n * (d * x * d⁻¹) * n⁻¹ = (n * d) * x * (n * d)⁻¹ := by group
        _ = (d * n) * x * (d * n)⁻¹ := by rw [hnd]
        _ = d * (n * x * n⁻¹) * d⁻¹ := by group
    rw [h2]
    exact h1
  have hF2 : ∀ x ∈ Q81.conjSub E n⁻¹, x ^ 2 = 1 := by
    intro x hx
    rw [Q81.mem_conjSub, inv_inv] at hx
    have h1 := hE2 _ hx
    rw [sq] at h1 ⊢
    calc x * x = n⁻¹ * (n * x * n⁻¹ * (n * x * n⁻¹)) * n := by group
      _ = 1 := by rw [h1]; group
  have hFX := hs.setup.le_X_of_normal_S hFS hFn hF2
  intro e he
  have h1 : n⁻¹ * e * n ∈ Q81.conjSub E n⁻¹ := by
    rw [Q81.mem_conjSub, inv_inv]
    rwa [show n * (n⁻¹ * e * n) * n⁻¹ = e by group]
  have h2 := hFX h1
  have h3 : n⁻¹ * e * n * n = n * (n⁻¹ * e * n) :=
    mem_centralizer_iff.mp hnT _ ((hs.setup.X_le_T) h2)
  have h4 : n⁻¹ * e * n = e := by
    calc n⁻¹ * e * n = n⁻¹ * e * n * n * n⁻¹ := by group
      _ = n * (n⁻¹ * e * n) * n⁻¹ := by rw [h3]
      _ = e := by group
  rw [← h4]
  exact h2

end Setting46e

end CFSG.ComponentClassification.HarrisLit
