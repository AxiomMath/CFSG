module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Ker2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Pi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Dich

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem mem_W_of_comm_z {n : G} (hn : n ∈ c.N1) (hnz : n * z = z * n) :
    n ∈ L ⊓ centralizer ({t} : Set G) := by
  have hcz : n ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z :=
    (c.h.normalizer_Q_cent_z_iff c.hα c.hF c.hWr c.hBD).1 ⟨c.mem_Nc.1 (c.N1_le_Nc hn), hnz⟩
  have hAB : zpowers z ≤ centralizer ((L ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => c.h.conf.cfg.z_comm_of_mem_A ha.1
  obtain ⟨ℓ, hℓ, w, hw, hnℓ⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hcz
  rcases mem_zpowers_sq_eq_one c.h.z_sq hw with hw1 | hw1
  · rw [hw1, mul_one] at hnℓ
    rw [hnℓ]; exact hℓ
  · exfalso
    rw [hw1] at hnℓ
    obtain ⟨e, he, b, hb, hℓeb⟩ := c.exists_eq_mul_of_mem_W hℓ
    have hℓα : ℓ * α = α * ℓ := by
      rw [hℓeb]
      have h1 : e * α = α * e := (c.mem_Qs.1 (c.E_le_Qs he)).2
      have h2 : b * α = α * b := c.h.BS b hb α c.hα.mem
      calc e * b * α = e * (α * b) := by rw [mul_assoc, h2]
        _ = α * (e * b) := by rw [← mul_assoc, h1, mul_assoc]
    have hℓt : ℓ * t = t * ℓ := mem_centralizer_singleton_iff.1 hℓ.2
    have hn2 := (c.mem_N1.1 hn).2
    have : n * α * n⁻¹ = α * t := by
      rw [hnℓ]
      calc ℓ * z * α * (ℓ * z)⁻¹ = ℓ * (z * α * z⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (α * t) * ℓ⁻¹ := by rw [c.h.z_conj_alpha c.hα]
        _ = (ℓ * α * ℓ⁻¹) * (ℓ * t * ℓ⁻¹) := by group
        _ = α * t := by
          rw [hℓα, hℓt]; group
    rw [hn2] at this
    exact c.h.t_ne (by simpa using this.symm)

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ

theorem pi_convN_mul {e b : G} (he : e ∈ E) (hb : b ∈ B) (hℓ : e * b ∈ normalizer (E : Set G)) :
    π (convN (⟨e * b, hℓ⟩ : normalizer (E : Set G))) = π (c.kappa ⟨b, hb⟩) := by
  have hmul : convN (⟨e * b, hℓ⟩ : normalizer (E : Set G)) =
      MulAut.conj (⟨e, he⟩ : ↥E) * c.kappa ⟨b, hb⟩ := by
    refine MulEquiv.ext fun f => ?_
    apply Subtype.ext
    show e * b * (f : G) * (e * b)⁻¹ = e * (b * f * b⁻¹) * e⁻¹
    group
  rw [hmul, map_mul]
  have : π (MulAut.conj (⟨e, he⟩ : ↥E)) = 1 := (hπ.ker _).2 ⟨_, rfl⟩
  rw [this, one_mul]

theorem rho_range_odd {a b : MulAut ↥E} (hab : (a, b) ∈ c.rho.range) (hπab : π a = π b) :
    π a ∈ alternatingGroup (Fin 5) := by
  obtain ⟨n, hn⟩ := hab
  have hj : π (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hπab, inv_mul_cancel]
  obtain ⟨e, he⟩ := (hπ.ker _).1 hj
  obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs 1 e
  have hρq' : c.rho ⟨q, c.Qs_le_N1 hq⟩ = (1, b⁻¹ * a) := by
    rw [hρq, map_one, he]
  let n' : ↥c.N1 := n * ⟨q, c.Qs_le_N1 hq⟩
  have hρn' : c.rho n' = (a, a) := by
    show c.rho (n * ⟨q, c.Qs_le_N1 hq⟩) = (a, a)
    rw [map_mul, hn, hρq']
    ext <;> simp
  obtain ⟨k, hk, hkz⟩ := c.exists_comm_adjust n'.2 (by rw [hρn'])
  obtain ⟨hkN, hkρ⟩ := c.mem_KR.1 hk
  let n'' : ↥c.N1 := n' * ⟨k, hkN⟩
  have hρn'' : c.rho n'' = (a, a) := by
    show c.rho (n' * ⟨k, hkN⟩) = (a, a)
    rw [map_mul, hρn', hkρ, mul_one]
  have hW : ((n'' : ↥c.N1) : G) ∈ L ⊓ centralizer ({t} : Set G) :=
    c.mem_W_of_comm_z n''.2 hkz
  have hconv := c.rho_conv n'' hkz (c.W_le_normE hW)
  rw [hρn''] at hconv
  have ha : a = convN (⟨(n'' : G), c.W_le_normE hW⟩ : normalizer (E : Set G)) :=
    (Prod.ext_iff.1 hconv).1
  obtain ⟨e', he', b', hb', heb⟩ := c.exists_eq_mul_of_mem_W hW
  have hnorm : e' * b' ∈ normalizer (E : Set G) := heb ▸ c.W_le_normE hW
  have h1 : (⟨(n'' : G), c.W_le_normE hW⟩ : normalizer (E : Set G)) = ⟨e' * b', hnorm⟩ :=
    Subtype.ext heb
  rw [ha, h1, c.pi_convN_mul hπ he' hb' hnorm]
  exact c.pi_kappa_mem ⟨b', hb'⟩

theorem rho_range_dichotomy :
    (∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
      π a ∈ alternatingGroup (Fin 5) ∧ π b = π a) ∨
    (∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
      π a ∈ alternatingGroup (Fin 5) ∧ π b ∈ alternatingGroup (Fin 5)) := by
  refine dichotomy π c.rho.range ?_ ?_ ?_ ?_
  · intro a b ha hb
    obtain ⟨e₁, he₁⟩ := (hπ.ker _).1 ha
    obtain ⟨e₂, he₂⟩ := (hπ.ker _).1 hb
    obtain ⟨q, hq, hρ⟩ := c.exists_rho_Qs e₁ e₂
    exact ⟨⟨q, c.Qs_le_N1 hq⟩, by rw [hρ, he₁, he₂]⟩
  · rintro a b ⟨n, hn⟩
    refine ⟨c.zconjN1 n, ?_⟩
    rw [c.rho_zconj, hn]
  · intro s hs
    obtain ⟨b, hb⟩ := c.exists_pi_kappa hπ hs
    refine ⟨c.kappa b, hb, ⟨b, c.B_le_N1 b.2⟩, ?_⟩
    exact c.rho_B b
  · intro a b hab hπab
    exact c.rho_range_odd hπ hab hπab

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
