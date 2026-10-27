module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Data

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem z8_comm_aff8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, aff8 u b * z8 = z8 * aff8 u b := by decide

theorem sq_of_comm_x8_y8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, aff8 u b * x8 = x8 * aff8 u b →
    aff8 u b * y8 = y8 * aff8 u b → aff8 u b * aff8 u b = 1 := by decide

theorem not_inv_FD : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, fbit8 u = 1 → dbit8 b = 1 →
    aff8 u b * aff8 u b ≠ 1 := by decide

theorem rot_mul_y8_sq : ∀ u : (ZMod 8)ˣ, ∀ c : ZMod 8, (u = 1 ∨ u = -1) →
    aff8 u (2 * c) * aff8 u (2 * c) ≠ 1 → (aff8 u (2 * c) * y8) * (aff8 u (2 * c) * y8) = 1 := by
  decide

@[expose] def kleinCent (M : (ZMod 8)ˣ → ZMod 8 → Prop) (u₁ : (ZMod 8)ˣ) (b₁ : ZMod 8)
    (u₂ : (ZMod 8)ˣ) (b₂ : ZMod 8) (u : (ZMod 8)ˣ) (b : ZMod 8) : Prop :=
  (M u₁ b₁ ∧ M u₂ b₂ ∧ M u b ∧ aff8 u₁ b₁ * aff8 u₁ b₁ = 1 ∧ aff8 u₂ b₂ * aff8 u₂ b₂ = 1 ∧
    aff8 u₁ b₁ * aff8 u₂ b₂ = aff8 u₂ b₂ * aff8 u₁ b₁ ∧ aff8 u₁ b₁ ≠ 1 ∧ aff8 u₂ b₂ ≠ 1 ∧
    aff8 u₁ b₁ ≠ aff8 u₂ b₂ ∧ aff8 u b * aff8 u₁ b₁ = aff8 u₁ b₁ * aff8 u b ∧
    aff8 u b * aff8 u₂ b₂ = aff8 u₂ b₂ * aff8 u b) →
    (aff8 u b = 1 ∨ aff8 u b = aff8 u₁ b₁ ∨ aff8 u b = aff8 u₂ b₂ ∨
      aff8 u b = aff8 u₁ b₁ * aff8 u₂ b₂)

@[expose] def inD16 (u : (ZMod 8)ˣ) (_b : ZMod 8) : Prop := fbit8 u = 0

@[expose] def inSD16 (u : (ZMod 8)ˣ) (b : ZMod 8) : Prop := fbit8 u = dbit8 b

instance (u : (ZMod 8)ˣ) (b : ZMod 8) : Decidable (inD16 u b) := by unfold inD16; infer_instance

instance (u : (ZMod 8)ˣ) (b : ZMod 8) : Decidable (inSD16 u b) := by
  unfold inSD16; infer_instance

instance (u₁ b₁ u₂ b₂ u b) : Decidable (kleinCent inD16 u₁ b₁ u₂ b₂ u b) := by
  unfold kleinCent; infer_instance

instance (u₁ b₁ u₂ b₂ u b) : Decidable (kleinCent inSD16 u₁ b₁ u₂ b₂ u b) := by
  unfold kleinCent; infer_instance

theorem kleinCent_D16 : ∀ u₁ b₁ u₂ b₂ u b, kleinCent inD16 u₁ b₁ u₂ b₂ u b := by decide

theorem kleinCent_SD16 : ∀ u₁ b₁ u₂ b₂ u b, kleinCent inSD16 u₁ b₁ u₂ b₂ u b := by decide

theorem reflCent_D16 : ∀ u₁ : (ZMod 8)ˣ, ∀ b₁ : ZMod 8, ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8,
    fbit8 u₁ = 0 → dbit8 b₁ = 1 → fbit8 u = 0 → aff8 u₁ b₁ * aff8 u₁ b₁ = 1 →
    aff8 u b * aff8 u₁ b₁ = aff8 u₁ b₁ * aff8 u b →
    aff8 u b = 1 ∨ aff8 u b = z8 ∨ aff8 u b = aff8 u₁ b₁ ∨ aff8 u b = z8 * aff8 u₁ b₁ := by
  decide

namespace L2Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

omit [Finite X] in
theorem exists_aff8 (g : A.T) : ∃ u b, aff8 u b = A.ψ g := A.ψ_mem_H8 g

omit [Finite X] in
theorem type8_conj {h : X} (hh : h ∈ centralizer ({t} : Set X)) {g : X} (hg : g ∈ A.T)
    (hg' : h * g * h⁻¹ ∈ A.T) :
    type8 ⟨A.ψ ⟨h * g * h⁻¹, hg'⟩, A.ψ_mem_H8 _⟩ = type8 ⟨A.ψ ⟨g, hg⟩, A.ψ_mem_H8 _⟩ := by
  rw [← A.τ_eq, ← A.τ_eq]
  have : (⟨h * g * h⁻¹, Config.sylowIn_le A.syl hg'⟩ : centralizer ({t} : Set X)) =
      ⟨h, hh⟩ * ⟨g, Config.sylowIn_le A.syl hg⟩ * (⟨h, hh⟩ : centralizer ({t} : Set X))⁻¹ :=
    rfl
  rw [this, map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

omit [Finite X] in
theorem sq_mem_K_of_commute {g : X} (hg : g ∈ A.T) (hgR : ∀ r ∈ A.R, g * r = r * g) :
    g ^ 2 ∈ A.K := by
  obtain ⟨x, hx, hψx⟩ := A.exists_mem_R_ψ_eq (σ := x8) ⟨1, 1, Or.inl rfl, by norm_num⟩
  obtain ⟨y, hy, hψy⟩ := A.exists_mem_R_ψ_eq (σ := y8) ⟨-1, 0, Or.inr rfl, by norm_num⟩
  have hm : g ^ 2 ∈ A.T := pow_mem hg 2
  rw [A.mem_K_iff hm]
  have : (⟨g ^ 2, hm⟩ : A.T) = (⟨g, hg⟩ : A.T) ^ 2 := rfl
  rw [this, map_pow, pow_two]
  obtain ⟨u, b, hub⟩ := A.exists_aff8 ⟨g, hg⟩
  rw [← hub]
  refine sq_of_comm_x8_y8 u b ?_ ?_
  · rw [hub, ← hψx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgR x hx)
  · rw [hub, ← hψy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgR y hy)

theorem fix_of_sq {g : X} (hg : g ∈ A.T) (hgt : g ^ 2 = t)
    (hgc : ∀ i ∈ A.T, i ^ 2 = 1 → g * i = i * g) (w : X) (hw : w ∈ normalizer (A.T : Set X)) :
    w * t * w⁻¹ = t := by
  set g' := w * g * w⁻¹ with hg'
  have hg'T : g' ∈ A.T := A.conj_mem_T hw hg
  have hg'c : ∀ i ∈ A.T, i ^ 2 = 1 → g' * i = i * g' := by
    intro i hi hi2
    have hi' : w⁻¹ * i * w ∈ A.T := A.conj_inv_mem_T hw hi
    have hi'2 : (w⁻¹ * i * w) ^ 2 = 1 := by
      rw [show w⁻¹ * i * w = w⁻¹ * i * w⁻¹⁻¹ by rw [inv_inv], conj_pow, hi2]; group
    have h := hgc _ hi' hi'2
    calc g' * i = w * (g * (w⁻¹ * i * w)) * w⁻¹ := by rw [hg']; group
      _ = w * ((w⁻¹ * i * w) * g) * w⁻¹ := by rw [h]
      _ = i * g' := by rw [hg']; group
  have hR : ∀ r ∈ A.R, g' * r = r * g' := by
    intro r hr
    obtain ⟨u, b, hub⟩ := A.exists_aff8 ⟨r, hr.1⟩
    by_cases hr2 : r ^ 2 = 1
    · exact hg'c r hr.1 hr2
    · obtain ⟨y, hy, hψy⟩ := A.exists_mem_R_ψ_eq (σ := y8) ⟨-1, 0, Or.inr rfl, by norm_num⟩
      have hy2 : y ^ 2 = 1 := by
        have hm : y ^ 2 ∈ A.R := pow_mem hy 2
        refine A.eq_of_ψ_eq hm (one_mem _) ?_
        have : (⟨y ^ 2, hm.1⟩ : A.T) = (⟨y, hy.1⟩ : A.T) ^ 2 := rfl
        rw [this, map_pow, hψy]
        exact (show y8 ^ 2 = 1 by decide).trans (map_one A.ψ).symm
      have hry : (r * y) ^ 2 = 1 := by
        have hm : (r * y) ^ 2 ∈ A.R := pow_mem (mul_mem hr hy) 2
        refine A.eq_of_ψ_eq hm (one_mem _) ?_
        have e1 : (⟨(r * y) ^ 2, hm.1⟩ : A.T) = ((⟨r, hr.1⟩ : A.T) * ⟨y, hy.1⟩) ^ 2 := rfl
        rw [e1, map_pow, map_mul, hψy]
        refine Eq.trans ?_ (map_one A.ψ).symm
        obtain ⟨u', c, hu', hc⟩ := A.ψ_mem_R8' hr
        rw [← hc, pow_two]
        refine rot_mul_y8_sq u' c hu' fun h => hr2 ?_
        have hm2 : r ^ 2 ∈ A.R := pow_mem hr 2
        refine A.eq_of_ψ_eq hm2 (one_mem _) ?_
        have e2 : (⟨r ^ 2, hm2.1⟩ : A.T) = (⟨r, hr.1⟩ : A.T) ^ 2 := rfl
        rw [e2, map_pow, ← hc, pow_two, h]
        exact (map_one A.ψ).symm
      have h1 := hg'c (r * y) (mul_mem hr.1 hy.1) hry
      have h2 := hg'c y hy.1 hy2
      calc g' * r = g' * (r * y) * y⁻¹ := by group
        _ = (r * y) * g' * y⁻¹ := by rw [h1]
        _ = (r * y) * (g' * y) * y⁻¹ * y⁻¹ := by group
        _ = (r * y) * (y * g') * y⁻¹ * y⁻¹ := by rw [h2]
        _ = r * (y * y) * g' * y⁻¹ * y⁻¹ := by group
        _ = r * g' := by
            rw [← pow_two, hy2, mul_one]
            have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy2])
            calc r * g' * y⁻¹ * y⁻¹ = r * g' * (y⁻¹ * y⁻¹) := by group
              _ = r * g' := by rw [hyinv, ← pow_two, hy2, mul_one]
  have hK : w * t * w⁻¹ ∈ A.K := by
    have : w * t * w⁻¹ = g' ^ 2 := by rw [hg', conj_pow, hgt]
    rw [this]
    exact A.sq_mem_K_of_commute hg'T hR
  exact A.eq_t_of_mem_K hK (A.conj_t_sq w) (A.conj_t_ne_one w)

theorem exists_conj_le_T {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({t} : Set X)) :
    ∃ h ∈ centralizer ({t} : Set X), P.map (MulAut.conj h).toMonoidHom ≤ A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({t} : Set X))) :=
    hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) Q A.syl
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hpC : p ∈ centralizer ({t} : Set X) := hPt hp
  have hpQ : (⟨p, hpC⟩ : centralizer ({t} : Set X)) ∈ (Q : Subgroup _) := hQ hp
  have : h * (⟨p, hpC⟩ : centralizer ({t} : Set X)) * h⁻¹ ∈ (A.syl : Subgroup _) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact ⟨_, hpQ, rfl⟩
  exact ⟨_, this, rfl⟩

theorem gen4_of_harada (hH : HaradaInput) {B : Subgroup X} (hB : ElemAbelianTwo B)
    (hcard : Nat.card B = 8) (htB : t ∈ B)
    (hcent : ∀ h ∈ centralizer ({t} : Set X), B.map (MulAut.conj h).toMonoidHom ≤ A.T →
      ∀ g ∈ A.T, (∀ e ∈ B.map (MulAut.conj h).toMonoidHom, g * e = e * g) →
        g ∈ B.map (MulAut.conj h).toMonoidHom)
    (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  refine gen4_of_harada_of_maximal hH hB hcard (fun Q hQ hBQ hQC => ?_) P hP
  have hQt : Q ≤ centralizer ({t} : Set X) := by
    intro q hq
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp (hQC hq)) t htB).symm
  obtain ⟨h, hh, hQT⟩ := A.exists_conj_le_T hQ hQt
  have hBT : B.map (MulAut.conj h).toMonoidHom ≤ A.T := (map_mono hBQ).trans hQT
  have heq : Q.map (MulAut.conj h).toMonoidHom = B.map (MulAut.conj h).toMonoidHom := by
    refine le_antisymm ?_ (map_mono hBQ)
    rintro _ ⟨q, hq, rfl⟩
    refine hcent h hh hBT _ (hQT ⟨q, hq, rfl⟩) ?_
    rintro _ ⟨e, he, rfl⟩
    have := (mem_centralizer_iff.mp (hQC hq)) e he
    change h * q * h⁻¹ * (h * e * h⁻¹) = h * e * h⁻¹ * (h * q * h⁻¹)
    calc h * q * h⁻¹ * (h * e * h⁻¹) = h * (q * e) * h⁻¹ := by group
      _ = h * (e * q) * h⁻¹ := by rw [this]
      _ = h * e * h⁻¹ * (h * q * h⁻¹) := by group
  exact map_injective (MulAut.conj h).injective heq

end L2Data

end CFSG.ComponentClassification.HSFLit
