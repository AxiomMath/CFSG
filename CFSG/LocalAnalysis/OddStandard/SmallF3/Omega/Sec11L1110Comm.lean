module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Star

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isPGroup_zpowers_of_mul_self' {a : G} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem sec11L1110_comm [Finite G] (hp : Asc82Pre11) (hT : Asc82Step1110Type) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {h h' : G} (hh : h ∈ centralizer ({z} : Set G)) (hh' : h' ∈ centralizer ({z} : Set G))
    (hcomm : (h'⁻¹ * t * h') * (h⁻¹ * t * h) = (h⁻¹ * t * h) * (h'⁻¹ * t * h')) :
    h'⁻¹ * t * h' = h⁻¹ * t * h ∨ h'⁻¹ * t * h' = h⁻¹ * t * h * z := by
  obtain ⟨ht2, hz2, htz, ht1, hz1⟩ := sec11_invols hctx.toSec10Ctx
  obtain ⟨A, hA⟩ : ∃ A, A = h'⁻¹ * t * h' := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = h⁻¹ * t * h := ⟨_, rfl⟩
  rw [← hA, ← hB] at hcomm ⊢
  have hCz : ∀ x ∈ centralizer ({z} : Set G), x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx
  obtain ⟨g, hg⟩ : ∃ g, g = h' * h⁻¹ := ⟨_, rfl⟩
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [hg]
    exact (centralizer ({z} : Set G)).mul_mem hh' ((centralizer ({z} : Set G)).inv_mem hh)
  obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * t * g := ⟨_, rfl⟩
  have e1 : u = h * A * h⁻¹ := by rw [hu, hg, hA]; group
  have e2 : t = h * B * h⁻¹ := by rw [hB]; group
  have hut : u * t = t * u := by
    calc u * t = h * A * h⁻¹ * (h * B * h⁻¹) := by rw [← e1, ← e2]
      _ = h * (A * B) * h⁻¹ := by group
      _ = h * (B * A) * h⁻¹ := by rw [hcomm]
      _ = h * B * h⁻¹ * (h * A * h⁻¹) := by group
      _ = t * u := by rw [← e1, ← e2]
  have hgz' : g * z = z * g := hCz g hgz
  have hgz'' : g⁻¹ * z = z * g⁻¹ :=
    hCz g⁻¹ ((centralizer ({z} : Set G)).inv_mem hgz)
  have huz : u * z = z * u := by
    calc u * z = g⁻¹ * t * (g * z) := by rw [hu]; group
      _ = g⁻¹ * t * (z * g) := by rw [hgz']
      _ = g⁻¹ * (t * z) * g := by group
      _ = g⁻¹ * (z * t) * g := by rw [htz]
      _ = (g⁻¹ * z) * t * g := by group
      _ = (z * g⁻¹) * t * g := by rw [hgz'']
      _ = z * u := by rw [hu]; group
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hSle : S ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf hctx.sylow.1 (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (hctx.central x hx))
  have hSC : IsSylow2Of S (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) :=
    sec10C_isSylow2Of_mono hctx.sylow hSle inf_le_left
  have huC : u ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hut,
      Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  obtain ⟨P, hP, huP⟩ := exists_isSylow2Of_ge (isPGroup_zpowers_of_mul_self' hu2)
    (Subgroup.zpowers_le.mpr huC)
  obtain ⟨a, haC, ha⟩ := IsSylow2Of.exists_conj_mem hSC hP
  have huP' : u ∈ P := huP (Subgroup.mem_zpowers u)
  have hv : a⁻¹ * u * a ∈ S := (ha u).mp huP'
  obtain ⟨hat, haz⟩ := Subgroup.mem_inf.mp haC
  have hat' : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp hat
  have haz' : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haz
  have hga : g * a ∈ centralizer ({z} : Set G) :=
    (centralizer ({z} : Set G)).mul_mem hgz (Subgroup.mem_centralizer_singleton_iff.mpr haz')
  have hvS : (g * a)⁻¹ * t * (g * a) ∈ S := by
    have e : (g * a)⁻¹ * t * (g * a) = a⁻¹ * u * a := by rw [hu]; group
    rw [e]
    exact hv
  have hstar := sec11L1110_star hp hT hctx hga hvS
  have e : (g * a)⁻¹ * t * (g * a) = a⁻¹ * u * a := by rw [hu]; group
  rw [e] at hstar
  have hu_eq : u = a * (a⁻¹ * u * a) * a⁻¹ := by group
  have hat'' : a * t * a⁻¹ = t := by rw [hat']; group
  have haz'' : a * z * a⁻¹ = z := by rw [haz']; group
  have hu' : u = t ∨ u = t * z := by
    rcases hstar with h1 | h1
    · left
      rw [hu_eq, h1, hat'']
    · right
      rw [hu_eq, h1]
      calc a * (t * z) * a⁻¹ = (a * t * a⁻¹) * (a * z * a⁻¹) := by group
        _ = t * z := by rw [hat'', haz'']
  have hAu : A = h⁻¹ * u * h := by rw [e1]; group
  have hBt : B = h⁻¹ * t * h := hB
  have hzh : h⁻¹ * z * h = z := by
    have := hCz h hh
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [this]
      _ = z := by group
  rcases hu' with h1 | h1
  · left
    rw [hAu, h1, hBt]
  · right
    rw [hAu, h1, hBt]
    calc h⁻¹ * (t * z) * h = (h⁻¹ * t * h) * (h⁻¹ * z * h) := by group
      _ = h⁻¹ * t * h * z := by rw [hzh]

end CFSG.OddStandard.SmallF3.Omega
