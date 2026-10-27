module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open Subgroup

section Conj

variable {G : Type*} [Group G]

theorem mem_centralizer_conj_iff (c x u : G) :
    c * u * c⁻¹ ∈ centralizer ({c * x * c⁻¹} : Set G) ↔ u ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have e1 : c * u * c⁻¹ * (c * x * c⁻¹) = c * (u * x) * c⁻¹ := by group
  have e2 : c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
  rw [e1, e2]
  simp

theorem natCard_centralizer_eq_of_isConj {s τ : G} (h : IsConj s τ) :
    Nat.card ↥(centralizer ({s} : Set G)) = Nat.card ↥(centralizer ({τ} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun u =>
    (mem_centralizer_conj_iff c s u).symm)

theorem natCard_centralizer_inf_conj {ζ g : G} (hg : g ∈ centralizer ({ζ} : Set G)) (x : G) :
    Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hgζ : g * ζ * g⁻¹ = ζ := by
    rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun u => ?_)).symm
  have h1 := mem_centralizer_conj_iff g ζ u
  rw [hgζ] at h1
  have h2 := mem_centralizer_conj_iff g x u
  simp only [mem_inf, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply]
  rw [h1, h2]

end Conj

section Cover

variable {H J : Type*} [Group H] [Group J] {ρ : H →* J}

theorem eq_one_of_mul_self_eq_one_of_mem_zpowers {ζ w : H} (hζ : orderOf ζ = 3)
    (hw : w ∈ zpowers ζ) (hw2 : w * w = 1) : w = 1 := by
  have h1 : orderOf w ∣ 3 := hζ ▸ orderOf_dvd_of_mem_zpowers hw
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [sq])
  have h3 : orderOf w ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (by simpa using h3)

theorem eq_of_map_eq_of_mul_self_eq_one (hodd : ∀ w : H, ρ w = 1 → w * w = 1 → w = 1)
    (hcomm : ∀ w : H, ρ w = 1 → ∀ h : H, w * h = h * w) {t u : H} (ht : t * t = 1)
    (hu : u * u = 1) (h : ρ t = ρ u) : t = u := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hρw : ρ (u * t⁻¹) = 1 := by rw [map_mul, map_inv, ← h, mul_inv_cancel]
  have hc := hcomm _ hρw t
  rw [ht', mul_assoc, ht, mul_one] at hc
  have hww : (u * t⁻¹) * (u * t⁻¹) = 1 := by
    rw [ht']
    calc u * t * (u * t) = u * (t * (u * t)) := mul_assoc _ _ _
      _ = u * u := by rw [← hc]
      _ = 1 := hu
  have h2 : u * t⁻¹ = 1 := hodd _ hρw hww
  rw [ht'] at h2
  rw [eq_inv_of_mul_eq_one_left h2, ht']

theorem exists_conj_of_isConj_map (hρ : Function.Surjective ρ)
    (hodd : ∀ w : H, ρ w = 1 → w * w = 1 → w = 1)
    (hcomm : ∀ w : H, ρ w = 1 → ∀ h : H, w * h = h * w) {t u : H} (ht : t * t = 1)
    (hu : u * u = 1) (h : IsConj (ρ u) (ρ t)) : ∃ g : H, g * u * g⁻¹ = t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hρ c
  refine ⟨g, eq_of_map_eq_of_mul_self_eq_one hodd hcomm ?_ ht ?_⟩
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu]; group
  · rw [map_mul, map_mul, map_inv]
    exact hc

theorem n_mul_card_centralizer_le [Finite H] [Finite J] (hρ : Function.Surjective ρ)
    (hodd : ∀ w : H, ρ w = 1 → w * w = 1 → w = 1)
    (hcomm : ∀ w : H, ρ w = 1 → ∀ h : H, w * h = h * w) {t : H} (ht : t * t = 1) {n : ℕ}
    (hn : n ≤ Nat.card ↥ρ.ker) :
    n * Nat.card ↥(centralizer ({ρ t} : Set J)) ≤ Nat.card ↥(centralizer ({t} : Set H)) := by
  let f : ↥(centralizer ({t} : Set H)) →* J := ρ.comp (centralizer ({t} : Set H)).subtype
  have hker : n ≤ Nat.card ↥f.ker := by
    refine hn.trans (Nat.card_le_card_of_injective
      (fun w : ↥ρ.ker => (⟨⟨w.1, mem_centralizer_singleton_iff.2 (hcomm w.1 w.2 t)⟩, w.2⟩ :
        ↥f.ker)) ?_)
    intro a b hab
    exact Subtype.ext (congrArg (fun x : ↥f.ker => ((x : ↥(centralizer ({t} : Set H))) : H)) hab)
  have hrange : centralizer ({ρ t} : Set J) ≤ f.range := by
    intro v hv
    obtain ⟨g, rfl⟩ := hρ v
    have hcg : ρ g * ρ t = ρ t * ρ g := mem_centralizer_singleton_iff.1 hv
    have hgt : g * t * g⁻¹ = t := by
      refine eq_of_map_eq_of_mul_self_eq_one hodd hcomm ?_ ht ?_
      · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
          _ = 1 := by rw [ht]; group
      · rw [map_mul, map_mul, map_inv, hcg]
        simp
    exact ⟨⟨g, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hgt)⟩, rfl⟩
  calc n * Nat.card ↥(centralizer ({ρ t} : Set J)) ≤ Nat.card ↥f.ker * Nat.card ↥f.range :=
        Nat.mul_le_mul hker (card_le_of_le hrange)
    _ = Nat.card ↥f.ker * f.ker.index := by rw [index_ker]
    _ = Nat.card ↥(centralizer ({t} : Set H)) := card_mul_index _

end Cover

section Recog

variable {G J : Type*} [Group G] [Finite G] [Group J] [Finite J]

theorem centralizer_eq_of_cover {D : Subgroup G} {ζ : G}
    (hDζ : D ≤ centralizer ({ζ} : Set G)) (hζD : ζ ∈ D) (hζ3 : orderOf ζ = 3)
    (ρ : ↥D →* J) (hρ : Function.Surjective ρ)
    (hker : ∀ d : ↥D, ρ d = 1 ↔ (d : G) ∈ zpowers ζ)
    {τ₀ τ₁ : J} (hJ : ∀ s : J, s * s = 1 → s ≠ 1 → IsConj s τ₀ ∨ IsConj s τ₁)
    {c₀ c₁ : ℕ} (hc₀ : Nat.card ↥(centralizer ({τ₀} : Set J)) = c₀)
    (hc₁ : Nat.card ↥(centralizer ({τ₁} : Set J)) = c₁) (hlt : c₁ < c₀)
    {tA tB : G} (htA : tA ∈ D) (htB : tB ∈ D) (hoA : orderOf tA = 2) (hoB : orderOf tB = 2)
    (hAB : ¬ IsConj tA tB)
    (hbA : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({tA} : Set G)) ≤ 3 * c₀)
    (hbB : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({tB} : Set G)) ≤ 3 * c₁) :
    centralizer ({ζ} : Set G) = D := by
  have hodd : ∀ w : ↥D, ρ w = 1 → w * w = 1 → w = 1 := by
    intro w hw hw2
    have h2 : (w : G) * (w : G) = 1 := by simpa using congrArg Subtype.val hw2
    exact Subtype.ext (eq_one_of_mul_self_eq_one_of_mem_zpowers hζ3 ((hker w).1 hw) h2)
  have hcomm : ∀ w : ↥D, ρ w = 1 → ∀ h : ↥D, w * h = h * w := by
    intro w hw h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((hker w).1 hw)
    have hh : (h : G) * ζ = ζ * (h : G) := mem_centralizer_singleton_iff.1 (hDζ h.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (Commute.zpow_left (show Commute ζ (h : G) from hh.symm) k).eq
  have hn : 3 ≤ Nat.card ↥ρ.ker := by
    have hz1 : ρ ⟨ζ, hζD⟩ = 1 := (hker ⟨ζ, hζD⟩).2 (mem_zpowers ζ)
    have hz3 : orderOf (⟨ζ, hζD⟩ : ↥D) = 3 := by rw [Subgroup.orderOf_mk]; exact hζ3
    have hle : zpowers (⟨ζ, hζD⟩ : ↥D) ≤ ρ.ker := zpowers_le.2 hz1
    have := card_le_of_le hle
    rwa [Nat.card_zpowers, hz3] at this
  have hinv : ∀ {t : G} (ht : t ∈ D), orderOf t = 2 →
      (⟨t, ht⟩ : ↥D) * ⟨t, ht⟩ = 1 ∧ ρ ⟨t, ht⟩ * ρ ⟨t, ht⟩ = 1 ∧ ρ ⟨t, ht⟩ ≠ 1 := by
    intro t ht ho
    have hsq : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ho, sq] at this
    have h1 : (⟨t, ht⟩ : ↥D) * ⟨t, ht⟩ = 1 := Subtype.ext hsq
    refine ⟨h1, by rw [← map_mul, h1, map_one], fun h => ?_⟩
    have h2 : orderOf t ∣ 3 := hζ3 ▸ orderOf_dvd_of_mem_zpowers ((hker ⟨t, ht⟩).1 h)
    rw [ho] at h2
    exact absurd h2 (by norm_num)
  have hlowD : ∀ {t : G} (ht : t ∈ D), orderOf t = 2 →
      3 * Nat.card ↥(centralizer ({ρ ⟨t, ht⟩} : Set J)) ≤
        Nat.card ↥(D ⊓ centralizer ({t} : Set G)) := by
    intro t ht ho
    have h1 := n_mul_card_centralizer_le hρ hodd hcomm (hinv ht ho).1 hn
    rw [TabMFive.card_centralizer_subtype (⟨t, ht⟩ : ↥D)] at h1
    exact h1
  have hlow : ∀ {t : G} (ht : t ∈ D), orderOf t = 2 →
      3 * Nat.card ↥(centralizer ({ρ ⟨t, ht⟩} : Set J)) ≤
        Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) :=
    fun ht ho => (hlowD ht ho).trans (card_le_of_le (inf_le_inf_right _ hDζ))
  have hB : IsConj (ρ ⟨tB, htB⟩) τ₁ := by
    obtain ⟨-, h2, h3⟩ := hinv htB hoB
    rcases hJ _ h2 h3 with h | h
    · exfalso
      have := hlow htB hoB
      rw [natCard_centralizer_eq_of_isConj h, hc₀] at this
      omega
    · exact h
  have hA : IsConj (ρ ⟨tA, htA⟩) τ₀ := by
    obtain ⟨-, h2, h3⟩ := hinv htA hoA
    rcases hJ _ h2 h3 with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := exists_conj_of_isConj_map hρ hodd hcomm (hinv htB hoB).1
        (hinv htA hoA).1 (h.trans hB.symm)
      refine hAB (isConj_iff.2 ⟨(g : G), ?_⟩)
      simpa using congrArg Subtype.val hg
  have hclass : ∀ (u : G) (hu : u ∈ D), orderOf u = 2 → ∀ (τ : J) (c : ℕ),
      Nat.card ↥(centralizer ({τ} : Set J)) = c → IsConj (ρ ⟨u, hu⟩) τ →
      Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({u} : Set G)) ≤ 3 * c →
      ∀ (t : G) (ht : t ∈ D), orderOf t = 2 → IsConj (ρ ⟨t, ht⟩) τ →
        (∃ g ∈ D, g * u * g⁻¹ = t) ∧
        Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) = 3 * c ∧
        centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G) ≤ D := by
    intro u hu hou τ c hc hτu hbu t ht hot hτt
    obtain ⟨g, hg⟩ := exists_conj_of_isConj_map hρ hodd hcomm (hinv ht hot).1 (hinv hu hou).1
      (hτu.trans hτt.symm)
    have hgG : (g : G) * u * (g : G)⁻¹ = t := by simpa using congrArg Subtype.val hg
    have hup : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) ≤ 3 * c := by
      have h1 := natCard_centralizer_inf_conj (hDζ g.2) u
      rw [hgG] at h1
      rw [h1]
      exact hbu
    have hlo : 3 * c ≤ Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) := by
      have := hlow ht hot
      rwa [natCard_centralizer_eq_of_isConj hτt, hc] at this
    have heq : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) = 3 * c :=
      le_antisymm hup hlo
    refine ⟨⟨g, g.2, hgG⟩, heq, ?_⟩
    have hDle : D ⊓ centralizer ({t} : Set G) ≤
        centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G) := inf_le_inf_right _ hDζ
    have hDc : 3 * c ≤ Nat.card ↥(D ⊓ centralizer ({t} : Set G)) := by
      have := hlowD ht hot
      rwa [natCard_centralizer_eq_of_isConj hτt, hc] at this
    have hDeq := eq_of_le_of_card_ge hDle (by rw [heq]; exact hDc)
    rw [← hDeq]
    exact inf_le_left
  have hmain : ∀ (t : G) (ht : t ∈ D), orderOf t = 2 →
      ((∃ g ∈ D, g * tA * g⁻¹ = t) ∧
        Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) = 3 * c₀ ∧
        centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G) ≤ D) ∨
      ((∃ g ∈ D, g * tB * g⁻¹ = t) ∧
        Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G)) = 3 * c₁ ∧
        centralizer ({ζ} : Set G) ⊓ centralizer ({t} : Set G) ≤ D) := by
    intro t ht ho
    obtain ⟨-, h2, h3⟩ := hinv ht ho
    rcases hJ _ h2 h3 with h | h
    · exact Or.inl (hclass tA htA hoA τ₀ c₀ hc₀ hA hbA t ht ho h)
    · exact Or.inr (hclass tB htB hoB τ₁ c₁ hc₁ hB hbB t ht ho h)
  refine (TabMFive.eq_of_involutions (C := centralizer ({ζ} : Set G)) (D := D) hDζ ?_ ?_
    htA htB hoA hoB ?_).symm
  · intro t ht ho
    rcases hmain t ht ho with h | h
    · exact h.2.2
    · exact h.2.2
  · intro t ht u hu hot hou hcard
    rcases hmain t ht hot with ⟨⟨g, hg, hgt⟩, hct, -⟩ | ⟨⟨g, hg, hgt⟩, hct, -⟩ <;>
      rcases hmain u hu hou with ⟨⟨g', hg', hgu⟩, hcu, -⟩ | ⟨⟨g', hg', hgu⟩, hcu, -⟩
    · exact ⟨g * g'⁻¹, D.mul_mem hg (D.inv_mem hg'), by rw [← hgt, ← hgu]; group⟩
    · exfalso
      omega
    · exfalso
      omega
    · exact ⟨g * g'⁻¹, D.mul_mem hg (D.inv_mem hg'), by rw [← hgt, ← hgu]; group⟩
  · have hA' : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({tA} : Set G)) = 3 * c₀ := by
      rcases hmain tA htA hoA with h | h
      · exact h.2.1
      · exfalso
        obtain ⟨g, -, hgt⟩ := h.1
        exact hAB (isConj_iff.2 ⟨g, hgt⟩).symm
    have hB' : Nat.card ↥(centralizer ({ζ} : Set G) ⊓ centralizer ({tB} : Set G)) = 3 * c₁ := by
      rcases hmain tB htB hoB with h | h
      · exfalso
        obtain ⟨g, -, hgt⟩ := h.1
        exact hAB (isConj_iff.2 ⟨g, hgt⟩)
      · exact h.2.1
    rw [hA', hB']
    omega

end Recog

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
