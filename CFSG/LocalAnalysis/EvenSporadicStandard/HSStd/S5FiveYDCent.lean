module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYDBar

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv

section Cent

variable {D : Type} [Group D] [Finite D] (c : DConfig D)

omit [Finite D] in
theorem DConfig.fhom_comm_tb (σ : Perm (Fin 5)) : c.fhom σ * c.tb = c.tb * c.fhom σ := by
  rw [DConfig.fhom_apply, DConfig.tb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    c.J_t _ (c.ψ σ).2]

theorem DConfig.card_cent_bar : Nat.card ↥(centralizer ({c.tb} : Set (DBar D))) ≤ 480 := by
  have hs := quotHom_surjective (K := D) (x := c.t) c.t_sq c.t_ne_one
  set f := quotHom c.t with hf
  have h1 : Nat.card ↥(centralizer ({c.t} : Set D)) =
      Nat.card ↥(centralizer ({QuotientGroup.mk' (CFSG.oddCore D) c.t} : Set (DBar D))) *
        Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hs).toEquiv]
  have hyt : c.y ∈ centralizer ({c.t} : Set D) :=
    mem_centralizer_singleton_iff.2 (c.y_central c.t).symm
  set yt : ↥(centralizer ({c.t} : Set D)) := ⟨c.y, hyt⟩ with hyt'
  have hyker : yt ∈ f.ker := MonoidHom.mem_ker.2
    (Subtype.ext ((QuotientGroup.eq_one_iff _).2 c.y_mem_oddCore))
  have hord : orderOf yt = 3 := (Subgroup.orderOf_mk c.y hyt).trans c.y_ord
  have hdvd : 3 ∣ Nat.card f.ker := hord ▸ Subgroup.orderOf_dvd_natCard f.ker hyker
  have h3 : 3 ≤ Nat.card f.ker := Nat.le_of_dvd Nat.card_pos hdvd
  have hc := c.card_cent
  have hcc : Nat.card ↥(centralizer ({c.tb} : Set (DBar D))) =
      Nat.card ↥(centralizer ({QuotientGroup.mk' (CFSG.oddCore D) c.t} : Set (DBar D))) := rfl
  rw [hcc]
  rw [h1] at hc
  nlinarith

theorem DConfig.cent_tb :
    centralizer ({c.tb} : Set (DBar D)) = (zpowers c.tb ⊔ zpowers c.vb) ⊔ c.fhom.range := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · refine sup_le (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 c.tvb_comm.symm))) ?_
    rintro _ ⟨σ, rfl⟩
    exact mem_centralizer_singleton_iff.2 (c.fhom_comm_tb σ)
  · rw [c.card_VJ]
    exact c.card_cent_bar

theorem DConfig.card_cent_tb : Nat.card ↥(centralizer ({c.tb} : Set (DBar D))) = 480 := by
  rw [c.cent_tb, c.card_VJ]

omit [Finite D] in
theorem DConfig.VJ_le_cent {a : DBar D} (ha : a ∈ zpowers c.tb ⊔ zpowers c.vb) :
    (zpowers c.tb ⊔ zpowers c.vb) ⊔ c.fhom.range ≤ centralizer ({a} : Set (DBar D)) := by
  have hcV : ∀ x ∈ zpowers c.tb ⊔ zpowers c.vb, x * a = a * x := by
    intro x hx
    have hc : ∀ h ∈ zpowers c.tb, ∀ k ∈ zpowers c.vb, h * k = k * h := by
      intro h hh k hk
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
      exact (Commute.zpow_zpow (show Commute c.tb c.vb from c.tvb_comm) m n).eq
    obtain ⟨h, hh, k, hk, rfl⟩ := mem_sup_of_commute hc hx
    obtain ⟨h', hh', k', hk', rfl⟩ := mem_sup_of_commute hc ha
    have e1 : h * h' = h' * h := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hh'
      exact (Commute.zpow_zpow_self c.tb m n).eq
    have e2 : k * k' = k' * k := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk'
      exact (Commute.zpow_zpow_self c.vb m n).eq
    have e3 : h * k' = k' * h := hc h hh k' hk'
    have e4 : k * h' = h' * k := (hc h' hh' k hk).symm
    calc h * k * (h' * k') = h * (k * h') * k' := by group
      _ = h * (h' * k) * k' := by rw [e4]
      _ = (h * h') * (k * k') := by group
      _ = (h' * h) * (k' * k) := by rw [e1, e2]
      _ = h' * (h * k') * k := by group
      _ = h' * (k' * h) * k := by rw [e3]
      _ = h' * k' * (h * k) := by group
  refine sup_le (fun x hx => mem_centralizer_singleton_iff.2 (hcV x hx)) ?_
  rintro _ ⟨σ, rfl⟩
  refine mem_centralizer_singleton_iff.2 ?_
  exact (c.V_comm_J a ha (c.fhom σ) ⟨σ, rfl⟩).symm

end Cent

end CFSG.EvenSporadicStandard.HSStd.FiveY
