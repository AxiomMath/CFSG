module

public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc3
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive
public import CFSG.ClassicalInvolution.AschTight.S1916Tr
public import CFSG.ClassicalInvolution.Asc77.AscS24BKC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

theorem zpow_cases {Q : Type*} [Group Q] {γ : Q} (h4 : γ ^ 4 = 1) {k : ℤ}
    (h2 : γ ^ k * γ ^ k = 1) (h1 : γ ^ k ≠ 1) :
    (γ ^ 2 = 1 ∧ γ ^ k = γ) ∨ (γ ^ 2 ≠ 1 ∧ γ ^ k = γ ^ 2) := by
  have h4' : γ ^ (4 : ℤ) = 1 := by rw [zpow_ofNat]; exact h4
  have hk := zpow_eq_zpow_emod k h4'
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  have e3 : γ ^ 3 * γ ^ 3 = γ ^ 2 := by
    have e : γ ^ 3 * γ ^ 3 = γ ^ 4 * γ ^ 2 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, h4, one_mul]
  rcases hcases with h | h | h | h <;> rw [h] at hk <;> rw [hk] at h2 h1 ⊢
  · exact absurd (zpow_zero γ) h1
  · rw [zpow_one] at h2 ⊢
    exact Or.inl ⟨by rw [sq]; exact h2, rfl⟩
  · rw [zpow_ofNat] at h1 ⊢
    exact Or.inr ⟨h1, rfl⟩
  · rw [zpow_ofNat] at h2 ⊢
    have h22 : γ ^ 2 = 1 := e3.symm.trans h2
    refine Or.inl ⟨h22, ?_⟩
    calc γ ^ 3 = γ ^ 2 * γ := pow_succ γ 2
      _ = γ := by rw [h22, one_mul]

theorem zpow_eq_zpow_of_sq {Q : Type*} [Group Q] {γ : Q} (h4 : γ ^ 4 = 1) {i j : ℤ}
    (hi2 : γ ^ i * γ ^ i = 1) (hi1 : γ ^ i ≠ 1) (hj2 : γ ^ j * γ ^ j = 1) (hj1 : γ ^ j ≠ 1) :
    γ ^ i = γ ^ j := by
  rcases zpow_cases h4 hi2 hi1 with ⟨h2, hi⟩ | ⟨h2, hi⟩ <;>
    rcases zpow_cases h4 hj2 hj1 with ⟨h2', hj⟩ | ⟨h2', hj⟩
  · rw [hi, hj]
  · exact absurd h2 h2'
  · exact absurd h2' h2
  · rw [hi, hj]

variable {G : Type} [Group G]

theorem cyc_quot {S P : Subgroup G} (hPn : ∀ g ∈ S, ∀ x ∈ P, g * x * g⁻¹ ∈ P) {g₀ : G}
    (hg₀ : g₀ ∈ S) (h4 : g₀ ^ 4 ∈ P)
    (hgen : ∀ y ∈ S, ∃ k : ℤ, (g₀ ^ k)⁻¹ * y ∈ P) :
    (∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ P) ∧
      ∀ b ∈ S, ∀ c ∈ S, b * b ∈ P → c * c ∈ P → b ∉ P → c ∉ P → b⁻¹ * c ∈ P := by
  set N : Subgroup ↥S := P.subgroupOf S with hN
  have hNn : N.Normal := ⟨fun n hn s => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact hPn s s.2 n hn⟩
  let π : ↥S →* ↥S ⧸ N := QuotientGroup.mk' N
  have hπ : ∀ x : ↥S, π x = 1 ↔ (x : G) ∈ P := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
  have hγ4 : π ⟨g₀, hg₀⟩ ^ 4 = 1 := by
    rw [← map_pow]
    exact (hπ _).mpr h4
  have hpow : ∀ y : ↥S, ∃ k : ℤ, π y = π ⟨g₀, hg₀⟩ ^ k := by
    intro y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    have h := (hπ ((⟨g₀, hg₀⟩ ^ k)⁻¹ * y)).mpr hk
    rw [map_mul, map_inv, map_zpow, inv_mul_eq_one] at h
    exact h.symm
  constructor
  · intro x hx y hy
    obtain ⟨i, hi⟩ := hpow ⟨x, hx⟩
    obtain ⟨j, hj⟩ := hpow ⟨y, hy⟩
    have h : π (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hi, hj,
        (Commute.zpow_zpow_self (π ⟨g₀, hg₀⟩) i j).eq]
      group
    exact (hπ _).mp h
  · intro b hb c hc hb2 hc2 hbP hcP
    obtain ⟨i, hi⟩ := hpow ⟨b, hb⟩
    obtain ⟨j, hj⟩ := hpow ⟨c, hc⟩
    have key : ∀ (y : ↥S) (k : ℤ), π y = π ⟨g₀, hg₀⟩ ^ k → (y : G) * y ∈ P → (y : G) ∉ P →
        π ⟨g₀, hg₀⟩ ^ k * π ⟨g₀, hg₀⟩ ^ k = 1 ∧ π ⟨g₀, hg₀⟩ ^ k ≠ 1 := by
      intro y k hk hy2 hyP
      refine ⟨?_, ?_⟩
      · rw [← hk, ← map_mul]
        exact (hπ _).mpr hy2
      · rw [← hk]
        exact fun h => hyP ((hπ y).mp h)
    obtain ⟨hi2, hi1⟩ := key _ i hi hb2 hbP
    obtain ⟨hj2, hj1⟩ := key _ j hj hc2 hcP
    have e := zpow_eq_zpow_of_sq hγ4 hi2 hi1 hj2 hj1
    have h : π (⟨b, hb⟩⁻¹ * ⟨c, hc⟩) = 1 := by
      rw [map_mul, map_inv, hi, hj, e, inv_mul_cancel]
    exact (hπ _).mp h

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}


namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem false_of [IsSimpleGroup G] (h3 : H3 p f) (hng : NoGraph p f)
    (hSP : ¬ (S : Subgroup G) ≤ MGrp Ω W) : False := by
  obtain ⟨g₀, hg₀S, hg₀4, hgen, d, hd, hdd⟩ := C.exists_gen h3 hng hSP
  obtain ⟨hab, huniq⟩ := cyc_quot (fun g hg x hx => C.P_normal hg hx) hg₀S hg₀4 hgen
  have hdA := C.Dg_le_A hd
  have hdS : d ∈ (S : Subgroup G) := C.A_le_S hdA
  have hx₂P : C.D.x₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W := C.W_le_P C.D.x₂_mem
  have hdP : d ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro h
    rcases C.Dg_mem_P hd h with h' | h'
    · rw [h', one_mul] at hdd
      exact C.hzK.ne_one hdd.symm
    · rw [h', C.hzK.sq] at hdd
      exact C.hzK.ne_one hdd.symm
  obtain ⟨e, he⟩ : ∃ e, e = d * C.D.x₂ := ⟨_, rfl⟩
  have heS : e ∈ (S : Subgroup G) := he ▸ (S : Subgroup G).mul_mem hdS hx₂P.1
  have heP : e ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
    intro h
    apply hdP
    have e1 : d = e * C.D.x₂⁻¹ := by rw [he]; group
    rw [e1]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hx₂P)
  have hcx : d * C.D.x₂ = C.D.x₂ * d :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.A_le_centralizer_x₂ hdA)
  have he2 : e * e = 1 := by
    calc e * e = d * (C.D.x₂ * d) * C.D.x₂ := by rw [he]; group
      _ = d * (d * C.D.x₂) * C.D.x₂ := by rw [hcx]
      _ = (d * d) * (C.D.x₂ * C.D.x₂) := by group
      _ = 1 := by rw [hdd, ← sq, C.x₂_sq, C.hzK.sq]
  have heR : R ≤ Subgroup.centralizer ({e} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : v * d = d * v := Subgroup.mem_centralizer_iff.mp ((C.mem_A).mp hdA).2.2.1 v hv
    have h2 : v * C.D.x₂ = C.D.x₂ * v := C.commutes_R_R' v hv _ C.x₂_mem_R'
    calc v * e = v * d * C.D.x₂ := by rw [he, mul_assoc]
      _ = d * (v * C.D.x₂) := by rw [h1, mul_assoc]
      _ = e * v := by rw [h2, he, mul_assoc]
  have hez : e ≠ z := fun h => heP (h ▸ C.z_mem_P)
  have hne : ∀ g : G, g * z * g⁻¹ ≠ e :=
    C.ne_conj_z C.hs.stand.mem C.hRsyl C.hzK heR hez
  refine AschTight.S1916.false_of_transfer (T7C.exists_not_commute_of_stand C.hs.stand) S
    (P := (S : Subgroup G) ⊓ MGrp Ω W) ?_ hab heS heP he2 ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => C.P_normal hg hx
    · intro hx
      have e1 : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
      rw [e1]
      exact C.P_normal ((S : Subgroup G).inv_mem hg) hx
  · intro g hg
    have hb2 : (g⁻¹ * e * g) * (g⁻¹ * e * g) = 1 := by
      calc (g⁻¹ * e * g) * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
        _ = 1 := by rw [he2]; group
    have hbP : g⁻¹ * e * g ∉ (S : Subgroup G) ⊓ MGrp Ω W := by
      intro hbP
      have hb1 : g⁻¹ * e * g ≠ 1 := by
        intro h1
        apply heP
        have e1 : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
        rw [e1, h1, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      obtain ⟨g', hg'⟩ := C.kc hg hbP.2 hb2 hb1
      apply hne (g * g')
      calc g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ := by group
        _ = e := by rw [hg']; group
    exact huniq _ hg _ heS (by rw [hb2]; exact Subgroup.one_mem _)
      (by rw [he2]; exact Subgroup.one_mem _) hbP heP

end Ctx8

theorem c24_9_core_of (h3 : H3 p f) (hng : NoGraph p f) : C24_9_core p f := by
  intro G _ _ _ Ω K K' W S R R' z u h h8 hSP
  obtain ⟨C⟩ := Ctx8.nonempty h.std.setting h.data h8
  exact C.false_of h3 hng hSP

end S24B

end CFSG.ClassicalInvolution.Asc77
