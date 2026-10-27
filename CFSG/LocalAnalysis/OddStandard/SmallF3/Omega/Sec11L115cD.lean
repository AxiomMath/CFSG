module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec11cAdm (t z : G) (D E : Subgroup G) : Prop :=
  zpowers t ⊔ zpowers z ≤ E ∧ E ≤ D ∧ secK0 t z = secKD E ⊔ oddCoreIn (secK0 t z)

theorem sec11c_mem_cent_sup {E F : Subgroup G} {c : G} (hE : c ∈ centralizer (E : Set G))
    (hF : c ∈ centralizer (F : Set G)) : c ∈ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
  have hle : E ⊔ F ≤ centralizer ({c} : Set G) := by
    refine sup_le (fun h hh => ?_) (fun h hh => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hE h hh)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hF h hh)
  exact Subgroup.mem_centralizer_iff.2 (fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh))

theorem sec11c_normalizer_D {Q R : Subgroup G} (hQR : R ≤ normalizer (Q : Set G)) {r : G}
    (hr : r ∈ R) : r ∈ normalizer ((centralizer (Q : Set G) ⊓ R : Subgroup G) : Set G) := by
  have key : ∀ s ∈ R, ∀ h ∈ centralizer (Q : Set G) ⊓ R,
      s * h * s⁻¹ ∈ centralizer (Q : Set G) ⊓ R := fun s hs h hh =>
    ⟨sec11c_conj_cent (hQR hs) hh.1, R.mul_mem (R.mul_mem hs hh.2) (R.inv_mem hs)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key r hr h, fun hh => ?_⟩
  have h1 := key r⁻¹ (R.inv_mem hr) _ hh
  have h2 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
  rw [h2] at h1
  exact h1

theorem sec11c_adm_step [Finite G] {t z : G} {K1 K2 : Subgroup G} (hS : Sec11cSplit t z K1 K2)
    {D E : Subgroup G} (hD : D ≤ centralizer (secQ K1 K2 : Set G)) (hD2 : IsPGroup 2 D)
    (hE : Sec11cAdm t z D E) {d : G} (hdD : d ∈ D) (hdN : d ∈ normalizer (E : Set G)) :
    Sec11cAdm t z D (E ⊔ zpowers d) := by
  obtain ⟨hWE, hED, hK0⟩ := hE
  have hKE : secKD E ≤ secK0 t z := sec11c_KD_le_K0 hWE
  have hdQ : ∀ q ∈ secQ K1 K2, d * q = q * d := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp (hD hdD) q hq).symm
  have hEQ : ∀ e ∈ E, ∀ q ∈ secQ K1 K2, e * q = q * e := fun e he q hq =>
    (Subgroup.mem_centralizer_iff.mp (hD (hED he)) q hq).symm
  have hdKD : d ∈ normalizer (secKD E : Set G) := sec11c_normalizer_KD hdN
  have hdK : ∀ x ∈ secKD E, d * x * d⁻¹ ∈ secKD E := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hdKD x).mp hx
  have hcomm := hS.comm_mod hKE hdQ hdK
  have hd2 : IsPGroup 2 (zpowers d) := hD2.to_le (Subgroup.zpowers_le.2 hdD)
  have hN0 : oddCoreIn (secK0 t z) ≤ secK0 t z := (oddCoreIn_normal _).1
  refine ⟨hWE.trans le_sup_left, sup_le hED (Subgroup.zpowers_le.2 hdD), le_antisymm ?_ ?_⟩
  · have hKE' : secKD E ≤ secKD (E ⊔ zpowers d) ⊔ oddCoreIn (secK0 t z) := by
      refine (Subgroup.closure_le _).2 ?_
      intro g hg
      have hgK : g ∈ secKD E := sec11c_mem_oTwoRes hg.1 hg.2
      have hgK0 : g ∈ secK0 t z := hKE hgK
      have hv : g⁻¹ * (d * g * d⁻¹) ∈ oddCoreIn (secKD E) :=
        hS.inf_le_oddCore hKE
          ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hgK) (hdK g hgK), hcomm g hgK⟩
      obtain ⟨c, hc, hdc⟩ := sec11c_fixed_coset hd2 (odd_card_oddCoreIn (secKD E))
        (fun m hm => sec11_conj_mem_oddCoreIn hdKD hm) hv
      have hcN : g⁻¹ * c ∈ oddCoreIn (secK0 t z) := hS.oddCore_le hKE hEQ hc
      have hcK : c ∈ secKD E := by
        have h1 : g * (g⁻¹ * c) ∈ secKD E :=
          Subgroup.mul_mem _ hgK ((oddCoreIn_normal _).1 hc)
        rwa [mul_inv_cancel_left] at h1
      have hcodd : Odd (orderOf c) := by
        have h1 := hS.odd_mul hgK0 hcN hg.2
        rwa [mul_inv_cancel_left] at h1
      have hcd : Commute d c := hdc
      have hcz : c ∈ centralizer ((zpowers d : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.2 (fun h hh => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
          exact (hcd.zpow_left k))
      have hcKd : c ∈ secKD (E ⊔ zpowers d) :=
        sec11c_mem_oTwoRes (sec11c_mem_cent_sup (sec11c_oTwoRes_le _ hcK) hcz) hcodd
      have hg' : g = c * (c⁻¹ * g) := by group
      rw [hg']
      refine Subgroup.mul_mem_sup hcKd ?_
      have h1 : (g⁻¹ * c)⁻¹ ∈ oddCoreIn (secK0 t z) := Subgroup.inv_mem _ hcN
      simpa [mul_assoc] using h1
    calc secK0 t z = secKD E ⊔ oddCoreIn (secK0 t z) := hK0
      _ ≤ secKD (E ⊔ zpowers d) ⊔ oddCoreIn (secK0 t z) := sup_le hKE' le_sup_right
  · exact sup_le (sec11c_KD_le_K0 (hWE.trans le_sup_left)) hN0

theorem sec11c_adm_max [Finite G] {t z : G} {K1 K2 : Subgroup G} (hS : Sec11cSplit t z K1 K2)
    {D : Subgroup G} (hD : D ≤ centralizer (secQ K1 K2 : Set G)) (hD2 : IsPGroup 2 D) :
    ∀ n : ℕ, ∀ E : Subgroup G, Nat.card D - Nat.card E = n → Sec11cAdm t z D E →
      Sec11cAdm t z D D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hn hE
    by_cases hED : E = D
    · subst hED
      exact hE
    · obtain ⟨d, hdD, hdN, hdE⟩ := HarrisU33.S4A.exists_mem_normalizer_not_mem hD2
        (lt_of_le_of_ne hE.2.1 hED)
      have hE' := sec11c_adm_step hS hD hD2 hE hdD hdN
      have hlt : E < E ⊔ zpowers d := by
        refine lt_of_le_of_ne le_sup_left (fun h => hdE ?_)
        have h1 : d ∈ E ⊔ zpowers d := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
        rwa [← h] at h1
      have hc1 : Nat.card E < Nat.card ↥(E ⊔ zpowers d) := Subgroup.card_lt_of_lt hlt
      have hc2 : Nat.card ↥(E ⊔ zpowers d) ≤ Nat.card D := Subgroup.card_le_of_le hE'.2.1
      exact ih (Nat.card D - Nat.card ↥(E ⊔ zpowers d)) (by omega) _ rfl hE'

end CFSG.OddStandard.SmallF3.Omega
