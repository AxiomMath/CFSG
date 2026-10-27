module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Coprime
public import CFSG.Milestones.OO_odd_order_solvable

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPerfect {P N D : Subgroup G} (hPD : P ≤ D)
    (hNn : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hodd : Odd (N.relIndex D))
    (hP : Group.IsPerfect ↥P) : P ≤ N := by
  let N' := N.subgroupOf D
  have hN' : N'.Normal := ⟨fun n hn d => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact hNn d d.2 n hn⟩
  have hsol : Group.IsSolvable (↥D ⧸ N') :=
    CFSG.Milestones.odd_order_solvable (by rw [← index_eq_card]; exact hodd)
  let ψ : ↥P →* ↥D ⧸ N' := (QuotientGroup.mk' N').comp (inclusion hPD)
  have hR : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    have : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
    rwa [hR, mem_bot] at this
  have h2 : (⟨x, hPD hx⟩ : ↥D) ∈ N' := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

omit [Finite G] in
theorem card_inf_mul_card_le {H L C : Subgroup G} [Finite H] (hLH : L ≤ H)
    (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) :
    Nat.card ↥(H ⊓ C) * Nat.card L ≤ Nat.card H * Nat.card ↥(L ⊓ C) := by
  have hB : H ⊓ C ≤ normalizer (L : Set G) := le_normalizer_of_conj_mem hLn inf_le_left
  have h := card_sup_mul_card_inf_of_le_normalizer' hB
  have hinf : L ⊓ (H ⊓ C) = L ⊓ C := by
    rw [← inf_assoc, inf_of_le_left hLH]
  rw [hinf] at h
  have hle : Nat.card ↥(L ⊔ H ⊓ C) ≤ Nat.card H := card_le_of_le (sup_le hLH inf_le_left)
  calc Nat.card ↥(H ⊓ C) * Nat.card L = Nat.card L * Nat.card ↥(H ⊓ C) := mul_comm _ _
    _ = Nat.card ↥(L ⊔ H ⊓ C) * Nat.card ↥(L ⊓ C) := h.symm
    _ ≤ Nat.card H * Nat.card ↥(L ⊓ C) := Nat.mul_le_mul_right _ hle

omit [Finite G] in
theorem card_inf_mul_card_eq {H L C : Subgroup G} (hLH : L ≤ H)
    (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hcov : H ≤ L ⊔ H ⊓ C) :
    Nat.card ↥(H ⊓ C) * Nat.card L = Nat.card H * Nat.card ↥(L ⊓ C) := by
  have hB : H ⊓ C ≤ normalizer (L : Set G) := le_normalizer_of_conj_mem hLn inf_le_left
  have h := card_sup_mul_card_inf_of_le_normalizer' hB
  have hinf : L ⊓ (H ⊓ C) = L ⊓ C := by
    rw [← inf_assoc, inf_of_le_left hLH]
  rw [hinf, le_antisymm (sup_le hLH inf_le_left) hcov] at h
  rw [mul_comm, ← h]

omit [Finite G] in
theorem le_sup_inf_centralizer {H L : Subgroup G} {a : G}
    (h : ∀ g ∈ H, ∃ l ∈ L, g * a * g⁻¹ = l * a * l⁻¹) (hLH : L ≤ H) :
    H ≤ L ⊔ H ⊓ centralizer ({a} : Set G) := by
  intro g hg
  obtain ⟨l, hl, hgl⟩ := h g hg
  have hc : l⁻¹ * g ∈ H ⊓ centralizer ({a} : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hLH hl)) hg, mem_centralizer_singleton_iff.mpr ?_⟩
    calc l⁻¹ * g * a = l⁻¹ * (g * a * g⁻¹) * g := by group
      _ = l⁻¹ * (l * a * l⁻¹) * g := by rw [hgl]
      _ = a * (l⁻¹ * g) := by group
  have : g = l * (l⁻¹ * g) := by group
  rw [this]
  exact mul_mem_sup hl hc

abbrev toSylowIn {S C : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex C) : Sylow 2 ↥C :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow (hS.of_equiv (subgroupOfEquivOfLe hSC).symm) hSi

omit [Finite G] in
theorem mem_toSylowIn {S C : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex C) (x : ↥C) :
    x ∈ ((toSylowIn hSC hS hSi : Sylow 2 ↥C) : Subgroup ↥C) ↔ (x : G) ∈ S :=
  mem_subgroupOf

omit [Finite G] in
theorem mem_smul_sylow_iff {C : Subgroup G} (P : Sylow 2 ↥C) (c x : ↥C) :
    x ∈ ((c • P : Sylow 2 ↥C) : Subgroup ↥C) ↔ c⁻¹ * x * c ∈ (P : Subgroup ↥C) := by
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

theorem exists_conj_eq_of_sylow {S S' C : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex C) (hS'C : S' ≤ C) (hS' : IsPGroup 2 S')
    (hS'i : ¬ 2 ∣ S'.relIndex C) :
    ∃ c ∈ C, S.map (MulAut.conj c).toMonoidHom = S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C (toSylowIn hSC hS hSi) (toSylowIn hS'C hS' hS'i)
  refine ⟨c, c.2, ?_⟩
  ext y
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : c * ⟨x, hSC hx⟩ * c⁻¹ ∈ ((c • toSylowIn hSC hS hSi : Sylow 2 ↥C) : Subgroup ↥C) := by
      rw [mem_smul_sylow_iff, mem_toSylowIn]
      simpa [mul_assoc] using hx
    rw [hc, mem_toSylowIn] at h1
    simpa using h1
  · intro hy
    have h1 : (⟨y, hS'C hy⟩ : ↥C) ∈ ((c • toSylowIn hSC hS hSi : Sylow 2 ↥C) : Subgroup ↥C) := by
      rw [hc, mem_toSylowIn]
      exact hy
    rw [mem_smul_sylow_iff, mem_toSylowIn] at h1
    refine ⟨_, h1, ?_⟩
    simp [mul_assoc]

theorem exists_conj_le_of_sylow {S Q C : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex C) (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) :
    ∃ c ∈ C, Q.map (MulAut.conj c).toMonoidHom ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.of_equiv (subgroupOfEquivOfLe hQC).symm
  obtain ⟨R, hR⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C R (toSylowIn hSC hS hSi)
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxR : (⟨x, hQC hx⟩ : ↥C) ∈ (R : Subgroup ↥C) := hR hx
  have hmem : c * ⟨x, hQC hx⟩ * c⁻¹ ∈ ((c • R : Sylow 2 ↥C) : Subgroup ↥C) := by
    rw [mem_smul_sylow_iff]
    simpa [mul_assoc] using hxR
  rw [hc, mem_toSylowIn] at hmem
  simpa using hmem

omit [Finite G] in
theorem eq_of_sylow_le {S Q C : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex C) (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) (hSQ : S ≤ Q) : Q = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.of_equiv (subgroupOfEquivOfLe hQC).symm
  have h := (toSylowIn hSC hS hSi).is_maximal' hQ' (fun x hx => by
    rw [mem_toSylowIn] at hx
    exact mem_subgroupOf.mpr (hSQ hx))
  apply le_antisymm _ hSQ
  intro x hx
  have hx' : (⟨x, hQC hx⟩ : ↥C) ∈ Q.subgroupOf C := mem_subgroupOf.mpr hx
  rw [h, mem_toSylowIn] at hx'
  exact hx'

theorem not_dvd_relIndex_of_center {S C : Subgroup G} {z : G}
    (hSC : S ≤ C ⊓ centralizer ({z} : Set G)) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex (C ⊓ centralizer ({z} : Set G))) (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hZ : ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x = 1 ∨ x = z) : ¬ 2 ∣ S.relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC' : S ≤ C := hSC.trans inf_le_left
  have hS' : IsPGroup 2 (S.subgroupOf C) := hS.of_equiv (subgroupOfEquivOfLe hSC').symm
  obtain ⟨R, hR⟩ := hS'.exists_le_sylow
  set RG := (R : Subgroup ↥C).map C.subtype with hRG
  have hRGC : RG ≤ C := map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map C.subtype
  have hSR : S ≤ RG := by
    intro x hx
    exact ⟨⟨x, hSC' hx⟩, hR (mem_subgroupOf.mpr hx), rfl⟩
  have hRnt : Nontrivial (R : Subgroup ↥C) := by
    refine ⟨⟨1, ⟨⟨z, hSC' hzS⟩, hR (mem_subgroupOf.mpr hzS)⟩, fun h => hz1 ?_⟩⟩
    have := congrArg (fun r : (R : Subgroup ↥C) => ((r : ↥C) : G)) h
    simpa using this.symm
  have hcnt : Nontrivial (center (R : Subgroup ↥C)) := R.isPGroup'.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : center (R : Subgroup ↥C))
  have hcen : ∀ r ∈ RG, (((c : (R : Subgroup ↥C)) : ↥C) : G) * r = r * (((c : _) : ↥C) : G) := by
    rintro _ ⟨r, hr, rfl⟩
    have := (mem_center_iff.mp c.2) ⟨r, hr⟩
    exact congrArg (fun r : (R : Subgroup ↥C) => ((r : ↥C) : G)) this.symm
  set g : G := (((c : (R : Subgroup ↥C)) : ↥C) : G) with hg
  have hgR : g ∈ RG := ⟨_, (c : (R : Subgroup ↥C)).2, rfl⟩
  have hg1 : g ≠ 1 := by
    intro h
    apply hc
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hgz : g ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hcen z (hSR hzS))
  have hQ : S ⊔ zpowers g = S := by
    refine eq_of_sylow_le hSC hS hSi (sup_le hSC (zpowers_le.mpr ⟨hRGC hgR, hgz⟩))
      (hRG2.to_le (sup_le hSR (zpowers_le.mpr hgR))) le_sup_left
  have hgS : g ∈ S := hQ ▸ mem_sup_right (mem_zpowers g)
  have hgz' : g = z := (hZ g hgS fun y hy => hcen y (hSR hy)).resolve_left hg1
  have hRz : RG ≤ C ⊓ centralizer ({z} : Set G) := by
    intro r hr
    refine ⟨hRGC hr, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hgz']
    exact (hcen r hr).symm
  have hRS : RG = S := eq_of_sylow_le hSC hS hSi hRz hRG2 hSR
  have hidx : S.relIndex C = (R : Subgroup ↥C).index := by
    rw [← hRS, hRG]
    change (((R : Subgroup ↥C).map C.subtype).comap C.subtype).index = _
    rw [comap_map_eq_self_of_injective C.subtype_injective]
  rw [hidx]
  exact R.not_dvd_index

end CFSG.ComponentClassification.HarrisLit.T1.S74
