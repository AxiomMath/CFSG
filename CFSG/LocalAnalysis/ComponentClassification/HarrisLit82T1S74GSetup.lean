module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74FDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

structure Setup (G : Type) [Group G] [Finite G] where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  p : ℕ
  f : ℕ
  hp : p.Prime
  hp2 : p ≠ 2
  hK : Nat.card K = p ^ f
  h5 : 5 ≤ p ^ f
  z : G
  L : Subgroup G
  φ : spinGroup (quadOdd 3 K) →* G
  hφ : Function.Injective φ
  hrange : φ.range = L
  hφz : φ (spinZ K) = z
  hLH : L ≤ centralizer ({z} : Set G)
  hLn : ∀ h ∈ centralizer ({z} : Set G), ∀ l ∈ L, h * l * h⁻¹ ∈ L
  hodd : Odd (L.relIndex (centralizer ({z} : Set G)))
  hinv : ∀ x ∈ centralizer ({z} : Set G), orderOf x = 2 → x ∈ L
  oneClass : ∀ x : G, orderOf x = 2 → ∃ g : G, g * z * g⁻¹ = x

attribute [instance] Setup.instField Setup.instFinite

namespace Setup

variable {G : Type} [Group G] [Finite G] (S : Setup G)

abbrev X : Type := spinGroup (quadOdd 3 S.K)

instance : Finite S.X := Finite.of_injective S.φ S.hφ

abbrev H : Subgroup G := centralizer ({S.z} : Set G)

abbrev t : G := S.φ (tSeven S.K)

abbrev q₃ : G := S.φ (qThree S.K)

abbrev T : Subgroup G := (fourT S.K).map S.φ

abbrev D : Subgroup G := S.H ⊓ centralizer ({S.t} : Set G)

theorem odd_card : Odd (Nat.card S.K) := S.hK ▸ (S.hp.odd_of_ne_two S.hp2).pow

theorem four_le_card : 4 ≤ Nat.card S.K := four_le_card_spin S.hK S.h5

theorem two_ne_zero : (2 : S.K) ≠ 0 := two_ne_zero_spin S.hp S.hp2 S.hK

theorem mem_L (x : S.X) : S.φ x ∈ S.L := S.hrange ▸ ⟨x, rfl⟩

theorem exists_eq_of_mem_L {g : G} (hg : g ∈ S.L) : ∃ x : S.X, S.φ x = g := by
  rw [← S.hrange] at hg
  exact hg

theorem map_le_L (A : Subgroup S.X) : A.map S.φ ≤ S.L := by
  rintro _ ⟨x, -, rfl⟩
  exact S.mem_L x

theorem card_map (A : Subgroup S.X) : Nat.card ↥(A.map S.φ) = Nat.card A :=
  card_map_of_injective S.hφ

theorem orderOf_φ (x : S.X) : orderOf (S.φ x) = orderOf x := orderOf_injective S.φ S.hφ x

theorem map_centralizer (x : S.X) :
    (centralizer ({x} : Set S.X)).map S.φ = S.L ⊓ centralizer ({S.φ x} : Set G) := by
  ext g
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨S.mem_L y, by rw [← map_mul, ← map_mul, hy]⟩
  · rintro ⟨hgL, hg⟩
    obtain ⟨y, rfl⟩ := S.exists_eq_of_mem_L hgL
    refine ⟨y, S.hφ ?_, rfl⟩
    rw [map_mul, map_mul, hg]

theorem card_inf_centralizer (x : S.X) :
    Nat.card ↥(S.L ⊓ centralizer ({S.φ x} : Set G)) = Nat.card ↥(centralizer ({x} : Set S.X)) := by
  rw [← S.map_centralizer, S.card_map]

theorem map_inf (A B : Subgroup S.X) : (A ⊓ B).map S.φ = A.map S.φ ⊓ B.map S.φ :=
  map_inf_eq A B S.φ S.hφ

theorem commute_z {g : G} (hg : g ∈ S.L) : g * S.z = S.z * g :=
  mem_centralizer_singleton_iff.mp (S.hLH hg)

theorem facts :
    S.z * S.z = 1 ∧ S.z ≠ 1 ∧ S.t * S.t = 1 ∧ S.t ≠ 1 ∧ S.z * S.t = S.t * S.z ∧
      S.z ≠ S.t ∧ S.z * S.t ≠ 1 ∧ S.t ∈ S.L ∧ S.t ∈ S.H := by
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -⟩ := spinZ_facts S.hp S.hp2 S.hK
  have hφz := S.hφz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, S.mem_L _, S.hLH (S.mem_L _)⟩
  · rw [← hφz, ← map_mul, hzz, map_one]
  · rw [← hφz]
    exact fun h => hz1 (S.hφ (h.trans (map_one S.φ).symm))
  · change S.φ _ * S.φ _ = 1
    rw [← map_mul, htt, map_one]
  · exact fun h => ht1 (S.hφ (h.trans (map_one S.φ).symm))
  · rw [← hφz, ← map_mul, ← map_mul, (mem_center_iff.mp hzc (tSeven S.K)).symm]
  · rw [← hφz]
    intro h
    exact htc (S.hφ h ▸ hzc)
  · rw [← hφz, ← map_mul]
    intro h
    have h' := S.hφ (h.trans (map_one S.φ).symm)
    have : tSeven S.K = spinZ S.K := by
      calc tSeven S.K = (spinZ S.K)⁻¹ := (eq_inv_of_mul_eq_one_right h')
        _ = spinZ S.K := inv_eq_of_mul_eq_one_right hzz
    exact htc (this ▸ hzc)

theorem exists_conj_t {h : G} (hh : h ∈ S.H) : ∃ l ∈ S.L, h * S.t * h⁻¹ = l * S.t * l⁻¹ := by
  have hu : h * S.t * h⁻¹ ∈ S.L := S.hLn h hh _ S.facts.2.2.2.2.2.2.2.1
  obtain ⟨y, hy⟩ := S.exists_eq_of_mem_L hu
  have hy2 : orderOf y = 2 := by
    rw [← S.orderOf_φ, hy]
    have : h * S.t * h⁻¹ = MulAut.conj h S.t := rfl
    rw [this, MulEquiv.orderOf_eq, S.orderOf_φ]
    exact orderOf_longSL2_neg_one _ fin3_zero_ne_one S.odd_card true true
  have hyZ : y ∉ center S.X := by
    intro hyc
    obtain ⟨-, -, hzc, -, -, htc, -⟩ := spinZ_facts S.hp S.hp2 S.hK
    have h2 := S.two_ne_zero
    have : Invertible (2 : S.K) := invertibleOfNonzero h2
    rw [center_spinGroup_quadOdd h2 (le_refl 3)] at hyc
    rcases (eq_one_or_eq_of_mem_zpowers_of_mul_self (spinZ_facts S.hp S.hp2 S.hK).1 hyc) with
      rfl | rfl
    · rw [orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    ·
      rw [S.hφz] at hy
      have : S.t = S.z := by
        have hc := S.commute_z (S.mem_L (tSeven S.K))
        have hh' := mem_centralizer_singleton_iff.mp hh
        calc S.t = h⁻¹ * (h * S.t * h⁻¹) * h := by group
          _ = h⁻¹ * S.z * h := by rw [← hy]
          _ = S.z := by rw [mul_assoc, ← hh']; group
      exact S.facts.2.2.2.2.2.1 this.symm
  obtain ⟨g, hg⟩ := spinSeven_lemma410b S.odd_card S.four_le_card hy2 hyZ
  refine ⟨S.φ g, S.mem_L g, ?_⟩
  rw [← hy, ← hg]
  simp only [map_mul, map_inv]

theorem le_sup_D : S.H ≤ S.L ⊔ S.H ⊓ centralizer ({S.t} : Set G) :=
  le_sup_inf_centralizer (fun _ hg => S.exists_conj_t hg) S.hLH

theorem exists_swap : ∃ n : G, n * S.t * n⁻¹ = S.z ∧ n * S.z * n⁻¹ = S.t := by
  obtain ⟨hzz, hz1, htt, ht1, hzt, hzt', -, htL, htH⟩ := S.facts
  have ht2 : orderOf S.t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  obtain ⟨g, hg⟩ := S.oneClass S.t ht2
  set u := g⁻¹ * S.z * g with hu
  have huH : u ∈ S.H := by
    rw [mem_centralizer_singleton_iff]
    have h1 : S.z = g⁻¹ * S.t * g := by rw [← hg]; group
    calc u * S.z = g⁻¹ * (S.z * S.t) * g := by rw [hu, h1]; group
      _ = g⁻¹ * (S.t * S.z) * g := by rw [hzt]
      _ = S.z * u := by rw [hu, h1]; group
  have hu2 : orderOf u = 2 := by
    have : u = MulAut.conj g⁻¹ S.z := by rw [hu, MulAut.conj_apply, inv_inv]
    rw [this, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  have huL : u ∈ S.L := S.hinv u huH hu2
  have huz : u ≠ S.z := by
    intro h
    apply hzt'
    calc S.z = g * u * g⁻¹ := by rw [hu]; group
      _ = g * S.z * g⁻¹ := by rw [h]
      _ = S.t := hg
  obtain ⟨y, hy⟩ := S.exists_eq_of_mem_L huL
  have hy2 : orderOf y = 2 := by rw [← S.orderOf_φ, hy, hu2]
  have hyZ : y ∉ center S.X := by
    intro hyc
    have h2 := S.two_ne_zero
    have : Invertible (2 : S.K) := invertibleOfNonzero h2
    rw [center_spinGroup_quadOdd h2 (le_refl 3)] at hyc
    rcases (eq_one_or_eq_of_mem_zpowers_of_mul_self (spinZ_facts S.hp S.hp2 S.hK).1 hyc) with
      rfl | rfl
    · rw [orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    · rw [S.hφz] at hy
      exact huz hy.symm
  obtain ⟨l, hl⟩ := spinSeven_lemma410b S.odd_card S.four_le_card hy2 hyZ
  have hlt : S.φ l * S.t * (S.φ l)⁻¹ = u := by
    rw [← hy, ← hl]
    simp only [map_mul, map_inv]
  have hlz : S.φ l * S.z * (S.φ l)⁻¹ = S.z := by
    rw [S.commute_z (S.mem_L l)]
    group
  refine ⟨(S.φ l)⁻¹ * g⁻¹, ?_, ?_⟩
  · calc (S.φ l)⁻¹ * g⁻¹ * S.t * ((S.φ l)⁻¹ * g⁻¹)⁻¹ = (S.φ l)⁻¹ * (g⁻¹ * S.t * g) * S.φ l := by
          group
      _ = (S.φ l)⁻¹ * S.z * S.φ l := by rw [← hg]; group
      _ = (S.φ l)⁻¹ * (S.φ l * S.z * (S.φ l)⁻¹) * S.φ l := by rw [hlz]
      _ = S.z := by group
  · calc (S.φ l)⁻¹ * g⁻¹ * S.z * ((S.φ l)⁻¹ * g⁻¹)⁻¹ = (S.φ l)⁻¹ * u * S.φ l := by
          rw [hu]; group
      _ = (S.φ l)⁻¹ * (S.φ l * S.t * (S.φ l)⁻¹) * S.φ l := by rw [hlt]
      _ = S.t := by group

end Setup

end CFSG.ComponentClassification.HarrisLit.T1.S74
