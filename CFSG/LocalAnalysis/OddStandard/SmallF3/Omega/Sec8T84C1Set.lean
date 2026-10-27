module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B4Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem kappa_eq_one_iff (E : Subgroup G) (x : ↥(normalizer (E : Set G))) :
    E.normalizerMonoidHom x = 1 ↔ (x : G) ∈ centralizer (E : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem range_kappa (E : Subgroup G) : E.normalizerMonoidHom.range = secNb E := by
  rw [secNb, secN, autIn, Subgroup.subgroupOf_self, Subgroup.map_top,
    MonoidHom.range_eq_map]

theorem kappa_eq_rhoG (hE : Sec8E G t L S z g B E) {x : G} (hxX : x ∈ normalizer (E : Set G))
    (hxN : x ∈ Nsub8 t B) : E.normalizerMonoidHom ⟨x, hxX⟩ = B89.rhoG hE x := by
  ext e
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, B89.rhoG_apply_X hE hxN hxX]

theorem kappa_t (hE : Sec8E G t L S z g B E) :
    E.normalizerMonoidHom ⟨t, B89.t_mem_X hE⟩ = B89.rhoG hE t :=
  kappa_eq_rhoG hE (B89.t_mem_X hE) B89.t_mem_N

theorem two_elt_cent_le (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) :
    ∀ x ∈ centralizer (E : Set G), (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ E := by
  intro x hx ⟨k, hk⟩
  obtain ⟨hCE, hOle⟩ := F.hCE G t L S z g B E hE
  have hxO : x ∈ E ⊔ oddCoreIn (normalizer (E : Set G)) := by rw [← hCE]; exact hx
  have hcomm : ∀ a ∈ E, ∀ b ∈ oddCoreIn (normalizer (E : Set G)), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hOle hb) a ha
  obtain ⟨a, haE, b, hbO, rfl⟩ := A3.exists_mul_of_comm hcomm hxO
  rcases k with _ | j
  · simp only [pow_zero, pow_one] at hk
    rw [hk]
    exact E.one_mem
  · have ha1 : a ^ (2 ^ (j + 1)) = 1 := by
      rw [pow_succ' (2 : ℕ) j, pow_mul, hE.elem.1.2 a haE, one_pow]
    have hbpow : b ^ (2 ^ (j + 1)) = 1 := by
      have h := Commute.mul_pow (hcomm a haE b hbO) (2 ^ (j + 1))
      rw [h, ha1, one_mul] at hk
      exact hk
    have hdvd : orderOf b ∣ 2 ^ (j + 1) := orderOf_dvd_of_pow_eq_one hbpow
    have hbodd : Odd (orderOf b) :=
      Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hbO)
    have hcop : Nat.Coprime (orderOf b) (2 ^ (j + 1)) :=
      (hbodd.coprime_two_right).pow_right (j + 1)
    have hborder : orderOf b = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    have hb1 : b = 1 := orderOf_eq_one_iff.mp hborder
    rw [hb1, mul_one]
    exact haE

theorem rhoG_eq_or (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {x m : G}
    (hx : x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) (hmL : m ∈ L)
    (hmB : m ∈ normalizer (B : Set G)) (hind : ∀ b ∈ B, x * b * x⁻¹ = m * b * m⁻¹) :
    B89.rhoG hE x = B89.rhoG hE m ∨ B89.rhoG hE x = B89.rhoG hE t * B89.rhoG hE m := by
  have hLt : L ≤ centralizer ({t} : Set G) := hE.ctx.toSec3SettingLB.component.le
  have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp (hLt hmL)
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hmN : m ∈ Nsub8 t B := B89.mem_N_of_comm hmt hmB
  have hxN : x ∈ Nsub8 t B := B89.XCt_le_N hE hx
  let c : G := m⁻¹ * x
  have hcN : c ∈ Nsub8 t B := (Nsub8 t B).mul_mem ((Nsub8 t B).inv_mem hmN) hxN
  have hxmc : x = m * c := by
    dsimp [c]
    group
  have hc_t : c * t = t * c := by
    have hmit : m⁻¹ * t = t * m⁻¹ := (Commute.inv_left hmt).eq
    dsimp [c]
    calc (m⁻¹ * x) * t = m⁻¹ * (x * t) := by group
      _ = m⁻¹ * (t * x) := by rw [hxt]
      _ = (m⁻¹ * t) * x := by group
      _ = (t * m⁻¹) * x := by rw [hmit]
      _ = t * (m⁻¹ * x) := by group
  have hcB : ∀ b ∈ B, c * b = b * c := by
    intro b hb
    have h1 : c * b * c⁻¹ = b := by
      have h2 : m⁻¹ * (x * b * x⁻¹) * m = b := by
        rw [hind b hb]
        group
      calc c * b * c⁻¹ = m⁻¹ * (x * b * x⁻¹) * m := by
            dsimp [c]; group
        _ = b := h2
    calc c * b = (c * b * c⁻¹) * c := by group
      _ = b * c := by rw [h1]
  have hcA : c ∈ centralizer (Asub8 t B : Set G) := B89.mem_cent_A_of hc_t hcB
  have hρc := B89.rhoG_of_cent_A F.h8A hE hcA
  have hρx : B89.rhoG hE x = B89.rhoG hE m * B89.rhoG hE c := by
    rw [hxmc, B89.rhoG_mul hE hmN hcN]
  rcases hρc with h1 | h1
  · left
    rw [hρx, h1, mul_one]
  · right
    have hmA : B89.rhoG hE m ∈ B89.Abar hE := B89.rhoG_mem_Abar hE hmL hmB
    rw [hρx, h1, B89.Abar_comm_u hE hmA]

end C10

end CFSG.OddStandard.SmallF3.Omega
