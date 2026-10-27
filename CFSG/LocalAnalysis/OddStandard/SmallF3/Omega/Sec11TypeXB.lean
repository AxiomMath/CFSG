module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXStar

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
  {K1 K2 T R : Subgroup G} {h : G}

private theorem t11b_isPGroup_zpowers {a : G} (ha : a * a = 1) : IsPGroup 2 (zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

theorem t11_type_t (H : T11Hyp t L S z K1 K2 T R h) :
    InducesTypeSome (CFSG.conjugate L h) t 5 1 2 1 := by
  have hctx := H.ctx
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic H.pre.basic hctx.toSec10Ctx
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp H.cent
  have hst := t11_s_comm_t H
  obtain ⟨hne1, hne2⟩ := t11_s_ne_t H
  obtain ⟨u, hu⟩ : ∃ u, u = h * t * h⁻¹ := ⟨_, rfl⟩
  have hut : u * t = t * u := by
    calc u * t = h * (t * (h⁻¹ * t * h)) * h⁻¹ := by rw [hu]; group
      _ = h * (h⁻¹ * t * h * t) * h⁻¹ := by rw [hst]
      _ = t * u := by rw [hu]; group
  have hhz' : h⁻¹ * z = z * h⁻¹ := by
    calc h⁻¹ * z = h⁻¹ * (z * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * z) * h⁻¹ := by rw [hhz]
      _ = z * h⁻¹ := by group
  have huz : u * z = z * u := by
    calc u * z = h * t * (h⁻¹ * z) := by rw [hu]; group
      _ = h * t * (z * h⁻¹) := by rw [hhz']
      _ = h * (t * z) * h⁻¹ := by group
      _ = h * (z * t) * h⁻¹ := by rw [htz]
      _ = (h * z) * t * h⁻¹ := by group
      _ = (z * h) * t * h⁻¹ := by rw [hhz]
      _ = z * u := by rw [hu]; group
  have hu2 : u * u = 1 := by
    rw [hu]
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hSle : S ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf hctx.sylow.1 (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (hctx.central x hx))
  have hSC : IsSylow2Of S (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) :=
    sec10C_isSylow2Of_mono hctx.sylow hSle inf_le_left
  have huC : u ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hut,
      Subgroup.mem_centralizer_singleton_iff.mpr huz⟩
  obtain ⟨P, hP, huP⟩ := exists_isSylow2Of_ge (t11b_isPGroup_zpowers hu2)
    (Subgroup.zpowers_le.mpr huC)
  obtain ⟨a, haC, ha⟩ := IsSylow2Of.exists_conj_mem hSC hP
  have hv : a⁻¹ * u * a ∈ S := (ha u).mp (huP (Subgroup.mem_zpowers u))
  obtain ⟨hat, haz⟩ := Subgroup.mem_inf.mp haC
  have hat' : a * t = t * a := Subgroup.mem_centralizer_singleton_iff.mp hat
  have haz' : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haz
  have hg : h⁻¹ * a ∈ centralizer ({z} : Set G) :=
    (centralizer ({z} : Set G)).mul_mem ((centralizer ({z} : Set G)).inv_mem H.cent)
      (Subgroup.mem_centralizer_singleton_iff.mpr haz')
  have e : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) = a⁻¹ * u * a := by rw [hu]; group
  have hvS : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) ∈ S := by rw [e]; exact hv
  have hstar := t11_star_or_i2p H.pre hctx hg hvS
  rw [e] at hstar
  have hat'' : a * t * a⁻¹ = t := by rw [hat']; group
  have haz'' : a * z * a⁻¹ = z := by rw [haz']; group
  have hu_eq : u = a * (a⁻¹ * u * a) * a⁻¹ := by group
  have hzh : h⁻¹ * z * h = z := t11_conj_z H
  rcases hstar with h1 | h1 | h1
  ·
    exfalso
    apply hne1
    have hut' : u = t := by rw [hu_eq, h1, hat'']
    calc h⁻¹ * t * h = h⁻¹ * u * h := by rw [hut']
      _ = t := by rw [hu]; group
  ·
    exfalso
    apply hne2
    have hut' : u = t * z := by
      rw [hu_eq, h1]
      calc a * (t * z) * a⁻¹ = (a * t * a⁻¹) * (a * z * a⁻¹) := by group
        _ = t * z := by rw [hat'', haz'']
    have e2 : t = h⁻¹ * t * h * z := by
      calc t = h⁻¹ * u * h := by rw [hu]; group
        _ = h⁻¹ * (t * z) * h := by rw [hut']
        _ = h⁻¹ * t * h * (h⁻¹ * z * h) := by group
        _ = h⁻¹ * t * h * z := by rw [hzh]
    calc h⁻¹ * t * h = h⁻¹ * t * h * z * z := by rw [mul_assoc (h⁻¹ * t * h) z z, hz2, mul_one]
      _ = t * z := by rw [← e2]
  ·
    have haN : a ∈ normalizer (L : Set G) := t11_cent_le_norm H.pre hctx.toSec10Ctx hat
    have h2 := kl_inducesTypeSome_conj haN h1
    rw [← hu_eq] at h2
    have h3 := inducesTypeSome_conjugate h2 h
    have e3 : h⁻¹ * u * h = t := by rw [hu]; group
    rwa [e3] at h3

end CFSG.OddStandard.SmallF3.Omega
