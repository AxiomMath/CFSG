module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Cos

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_RL {V X : Subgroup G} {t : G} (hbot : X ⊓ centralizer (V : Set G) = ⊥)
    (hXN : X ≤ normalizer (V : Set G)) (hXt : X ≤ centralizer ({t} : Set G))
    (htN : t ∈ normalizer (V : Set G)) (ht2 : t * t = 1)
    (hfus : ∀ u ∈ X, u * u = 1 → u ≠ 1 → ∃ n ∈ normalizer (V : Set G), n⁻¹ * t * n = t * u)
    {y : MulAut ↥V}
    (hy : (∃ x ∈ autIn X V, y = betaOf V t * x) ∧ y * y = 1 ∧ y ≠ 1) :
    (∃ b ∈ secNb V, y = b * betaOf V t * b⁻¹) ∧ y ∈ Subgroup.centralizer {betaOf V t} := by
  obtain ⟨⟨x, hx, hyx⟩, hy2, -⟩ := hy
  obtain ⟨u, huX, huN, rfl⟩ := sec127_mem_autIn_iff.mp hx
  have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp (hXt huX)
  have hcomm : betaOf V u * betaOf V t = betaOf V t * betaOf V u := by
    rw [← sec127_betaOf_mul huN htN, ← sec127_betaOf_mul htN huN, hut]
  have hbt2 : betaOf V t * betaOf V t = 1 := by
    rw [← sec127_betaOf_mul htN htN, ht2, sec127_betaOf_one]
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · by_cases hu1 : u = 1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [hyx, hu1, sec127_betaOf_one]
      group
    · have hu2 : u * u = 1 := by
        have h1 : y * y = betaOf V (u * u) := by
          rw [hyx, sec127_betaOf_mul huN huN]
          calc (betaOf V t * betaOf V u) * (betaOf V t * betaOf V u)
              = betaOf V t * (betaOf V u * betaOf V t) * betaOf V u := by group
            _ = betaOf V t * (betaOf V t * betaOf V u) * betaOf V u := by rw [hcomm]
            _ = (betaOf V t * betaOf V t) * (betaOf V u * betaOf V u) := by group
            _ = betaOf V u * betaOf V u := by rw [hbt2, one_mul]
        rw [h1] at hy2
        have h2 := (sec127_betaOf_eq_one_iff ((normalizer (V : Set G)).mul_mem huN huN)).mp hy2
        have h3 : u * u ∈ X ⊓ centralizer (V : Set G) :=
          Subgroup.mem_inf.mpr ⟨X.mul_mem huX huX, h2⟩
        rwa [hbot, Subgroup.mem_bot] at h3
      obtain ⟨n, hn, hnt⟩ := hfus u huX hu2 hu1
      refine ⟨betaOf V n⁻¹,
        sec127_mem_secNb_iff.mpr ⟨n⁻¹, (normalizer (V : Set G)).inv_mem hn, rfl⟩, ?_⟩
      have h1 := sec127_betaOf_conj (V := V) ((normalizer (V : Set G)).inv_mem hn) htN
      rw [inv_inv, hnt] at h1
      rw [hyx, ← sec127_betaOf_mul htN huN, h1]
  · rw [hyx]
    calc betaOf V t * betaOf V u * betaOf V t = betaOf V t * (betaOf V u * betaOf V t) := by group
      _ = betaOf V t * (betaOf V t * betaOf V u) := by rw [hcomm]

theorem sec127_LR [Finite G] {V X L : Subgroup G} {t : G} {K : Subgroup (MulAut ↥V)}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hXN : X ≤ normalizer (V : Set G)) (hbot : X ⊓ centralizer (V : Set G) = ⊥)
    (hXt : X ≤ centralizer ({t} : Set G)) (hXL : X ≤ L) (htN : t ∈ normalizer (V : Set G))
    (ht2 : t * t = 1) (ht1 : betaOf V t ≠ 1) (hKX : autIn X V ≤ K) (hKcard : Nat.card ↥K = 120)
    (hKt : betaOf V t ∈ K) (hKeq : K = secNb V ⊓ Subgroup.centralizer {betaOf V t})
    (hVel : CFSG.Open.IsElemAbelian 2 V)
    (hrange : ∀ u ∈ X, u * u = 1 → u ≠ 1 → ∀ d ∈ V, u * d = d * u →
      ∃ v ∈ V, u * v * u⁻¹ * v⁻¹ = d)
    (hcent : centralizer (V : Set G) = V ⊔ oddCoreIn (secN V)) (hL : ∀ g : G, g⁻¹ * t * g ∉ L)
    {y : MulAut ↥V}
    (hy : (∃ b ∈ secNb V, y = b * betaOf V t * b⁻¹) ∧ y ∈ Subgroup.centralizer {betaOf V t}) :
    (∃ x ∈ autIn X V, y = betaOf V t * x) ∧ y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨⟨b, hb, hyb⟩, hycomm⟩ := hy
  obtain ⟨n, hn, rfl⟩ := sec127_mem_secNb_iff.mp hb
  have hβt : betaOf V t ∈ secNb V := sec127_mem_secNb_iff.mpr ⟨t, htN, rfl⟩
  have hyN : y ∈ secNb V := by
    rw [hyb]
    exact (secNb V).mul_mem ((secNb V).mul_mem hb hβt) ((secNb V).inv_mem hb)
  have hbt2 : betaOf V t * betaOf V t = 1 := by
    rw [← sec127_betaOf_mul htN htN, ht2, sec127_betaOf_one]
  have hy2 : y * y = 1 := by
    rw [hyb]
    calc (betaOf V n * betaOf V t * (betaOf V n)⁻¹) * (betaOf V n * betaOf V t * (betaOf V n)⁻¹)
        = betaOf V n * (betaOf V t * betaOf V t) * (betaOf V n)⁻¹ := by group
      _ = 1 := by rw [hbt2]; group
  have hy1 : y ≠ 1 := by
    intro h
    apply ht1
    have h1 : betaOf V n * betaOf V t * (betaOf V n)⁻¹ = 1 := by rw [← hyb]; exact h
    calc betaOf V t
        = (betaOf V n)⁻¹ * (betaOf V n * betaOf V t * (betaOf V n)⁻¹) * betaOf V n := by group
      _ = 1 := by rw [h1]; group
  have hyK : y ∈ K := by
    rw [hKeq]
    exact Subgroup.mem_inf.mpr ⟨hyN, hycomm⟩
  have hKcomm : ∀ y' ∈ K, betaOf V t * y' = y' * betaOf V t := by
    intro y' hy'
    rw [hKeq] at hy'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy').2).symm
  rcases sec127_cases_K hA5 hXN hbot hXt htN ht1 hKX hKcard hKt hKcomm hyK with hyX | ⟨x, hx, hxy⟩
  · exfalso
    obtain ⟨u, huX, huN, hyu⟩ := sec127_mem_autIn_iff.mp hyX
    have hsN : n * t * n⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hn htN)
        ((normalizer (V : Set G)).inv_mem hn)
    have hys : y = betaOf V (n * t * n⁻¹) := by rw [hyb, sec127_betaOf_conj hn htN]
    have hs2 : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
      calc (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hu2 : u * u = 1 := by
      have h1 : betaOf V (u * u) = 1 := by
        rw [sec127_betaOf_mul huN huN, ← hyu]
        exact hy2
      have h2 := (sec127_betaOf_eq_one_iff ((normalizer (V : Set G)).mul_mem huN huN)).mp h1
      have h3 : u * u ∈ X ⊓ centralizer (V : Set G) :=
        Subgroup.mem_inf.mpr ⟨X.mul_mem huX huX, h2⟩
      rwa [hbot, Subgroup.mem_bot] at h3
    have hu1 : u ≠ 1 := by
      rintro rfl
      apply hy1
      rw [hyu, sec127_betaOf_one]
    have hc : u⁻¹ * (n * t * n⁻¹) ∈ V ⊔ oddCoreIn (secN V) := by
      rw [← hcent]
      exact (sec127_betaOf_eq_iff huN hsN).mp (hyu.symm.trans hys)
    obtain ⟨g, hg⟩ := sec127_conj_coset_oddCore hVel huN hu2 (hrange u huX hu2 hu1) hc hs2
    apply hL (n⁻¹ * g⁻¹)
    have hu : u = (n⁻¹ * g⁻¹)⁻¹ * t * (n⁻¹ * g⁻¹) := by
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = g * (n * t * n⁻¹) * g⁻¹ := by rw [hg]
        _ = (n⁻¹ * g⁻¹)⁻¹ * t * (n⁻¹ * g⁻¹) := by group
    rw [← hu]
    exact hXL huX
  · exact ⟨⟨x, hx, hxy⟩, hy2, hy1⟩

end CFSG.OddStandard.SmallF3.Omega
