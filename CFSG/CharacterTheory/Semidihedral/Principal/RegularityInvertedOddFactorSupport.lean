module

public import CFSG.GroupTheory.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

section Confinement

variable {G : Type*} [Group G]

theorem normalizer_le_centralizer_of_confined {t : G} (ht : orderOf t = 2) {U P Q : Subgroup G}
    (hUodd : Odd (Nat.card U))
    (hinv : ∀ w ∈ Subgroup.centralizer ({t} : Set G), orderOf w = 2 → w ≠ t →
      ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hconf : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.centralizer ({t} : Set G))
    (hPU : P ≤ U) (hP : P ≠ ⊥) (hPQ : P ≤ Q) (hQC : Q ≤ Subgroup.centralizer ({t} : Set G)) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨⟨u, huP⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
  have hu1 : u ≠ 1 := fun h => hu1' (Subtype.ext h)
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w := g * t * g⁻¹ with hw
  have hwQ : ∀ x ∈ Q, x * w = w * x := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    have hc : g⁻¹ * x * g * t = t * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hx')
    calc x * w = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by rw [hw]; group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = w * x := by rw [hw]; group
  have hwu : u * w = w * u := hwQ u (hPQ huP)
  have hwC : w ∈ Subgroup.centralizer ({t} : Set G) :=
    hconf u (hPU huP) hu1 (Subgroup.mem_centralizer_singleton_iff.mpr hwu.symm)
  have hw2 : orderOf w = 2 := by
    have hsc : SemiconjBy g t w := by
      change g * t = g * t * g⁻¹ * g
      group
    rw [← SemiconjBy.orderOf_eq g hsc, ht]
  by_contra hne
  have hwt : w ≠ t := by
    intro h
    apply hne
    calc g * t = w * g := by rw [hw]; group
      _ = t * g := by rw [h]
  have hinvu := hinv w hwC hw2 hwt u (hPU huP)
  have huu : u = u⁻¹ := by
    rw [← hinvu, ← hwu, mul_inv_cancel_right]
  have hu2 : u ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [huu]
    exact mul_inv_cancel u
  have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have : Finite U := CFSG.OddInversion.finite_of_odd_card hUodd
  have hdvdU : orderOf u ∣ Nat.card U := by
    have h := orderOf_dvd_natCard (⟨u, hPU huP⟩ : U)
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime 2 (Nat.card U) := Nat.coprime_two_left.mpr hUodd
  have h1 : orderOf u = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd2 hdvdU)
  exact hu1 (orderOf_eq_one_iff.mp h1)

theorem exists_sylow_eq_map_of_normalizer_le [Finite G] {ℓ : ℕ} [Fact ℓ.Prime] {H : Subgroup G}
    (Q : Sylow ℓ H)
    (hN : Subgroup.normalizer (((Q : Subgroup H).map H.subtype : Subgroup G) : Set G) ≤ H) :
    ∃ T : Sylow ℓ G, (T : Subgroup G) = (Q : Subgroup H).map H.subtype := by
  set Q₀ : Subgroup G := (Q : Subgroup H).map H.subtype with hQ₀
  have hQ₀p : IsPGroup ℓ Q₀ := Q.isPGroup'.map H.subtype
  obtain ⟨T, hT⟩ := hQ₀p.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have hlt : Q₀.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm _ hT
    intro x hx
    have : (⟨x, hx⟩ : T) ∈ Q₀.subgroupOf T := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition T.isPGroup' hlt
  obtain ⟨g, hgN, hgQ⟩ := IsConcreteLE.exists_of_lt hnorm
  rw [← Subgroup.subgroupOf_normalizer_eq hT, Subgroup.mem_subgroupOf] at hgN
  have hgH : (g : G) ∈ H := hN hgN
  set R : Subgroup H := ((T : Subgroup G) ⊓ Subgroup.normalizer (Q₀ : Set G)).comap H.subtype
  have hRp : IsPGroup ℓ R :=
    (T.isPGroup'.comap_of_injective H.subtype Subtype.val_injective).to_le
      (Subgroup.comap_mono inf_le_left)
  have hQR : (Q : Subgroup H) ≤ R := by
    intro x hx
    refine ⟨hT ⟨x, hx, rfl⟩, ?_⟩
    exact Subgroup.le_normalizer ⟨x, hx, rfl⟩
  have hReq := Q.is_maximal' hRp hQR
  have hgR : (⟨g, hgH⟩ : H) ∈ R := ⟨g.2, hgN⟩
  rw [hReq] at hgR
  exact hgQ ⟨⟨g, hgH⟩, hgR, rfl⟩

end Confinement

theorem regular_index_arithmetic {g c d a b h q e I : ℚ} (he : e = 1 ∨ e = -1) (hq : 1 < q)
    (ha : a ≠ 0) (hh : h ≠ 0) (hb : b ≠ 0)
    (hc : c = 2 * a * b * h * q * (q ^ 2 - 1)) (hd : d = 2 * a * h * (q + e))
    (hg : g = c ^ 3 / d ^ 2 * ((q ^ 2 - e * q + 1) / (q - e) ^ 2)) (hI : g = c * I) :
    I = b ^ 2 * q ^ 2 * (q ^ 2 - e * q + 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hqe : q - e ≠ 0 := by rcases he with rfl | rfl <;> intro h <;> linarith
  have hqe' : q + e ≠ 0 := by rcases he with rfl | rfl <;> intro h <;> linarith
  have hd0 : d ≠ 0 := by rw [hd]; exact mul_ne_zero (by positivity) hqe'
  have hcd : c = d * (b * q * (q - e)) := by
    rw [hc, hd]
    have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
    linear_combination (2 * a * b * h * q) * he2
  have hc0 : c ≠ 0 := by rw [hcd]; exact mul_ne_zero hd0 (by positivity)
  have hI' : I = c ^ 2 / d ^ 2 * ((q ^ 2 - e * q + 1) / (q - e) ^ 2) := by
    apply mul_left_cancel₀ hc0
    rw [← hI, hg]
    ring
  rw [hI', hcd]
  field_simp

end CFSG.Semidihedral.Principal
