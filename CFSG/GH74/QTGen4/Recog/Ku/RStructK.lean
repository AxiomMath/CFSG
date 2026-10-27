module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructJ

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem eq_of_card_four {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) {p q : Q}
    (hp : p ≠ 1) (hq : q ≠ 1) (hpq : p ≠ q) (hpq1 : p * q ≠ 1) (x : Q) :
    x = 1 ∨ x = p ∨ x = q ∨ x = p * q := by
  classical
  have := Fintype.ofFinite Q
  have h1 : (1 : Q) ∉ ({p, q, p * q} : Finset Q) := by
    simp [hp.symm, hq.symm, hpq1.symm]
  have h2 : p ∉ ({q, p * q} : Finset Q) := by
    simp [hpq, hq]
  have h3 : q ≠ p * q := by
    intro h
    apply hp
    simpa using h
  have hcard : ({1, p, q, p * q} : Finset Q).card = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card, hQ, Finset.card_insert_of_notMem h1,
      Finset.card_insert_of_notMem h2, Finset.card_pair h3]
  have := Finset.eq_univ_of_card _ hcard
  have hx : x ∈ ({1, p, q, p * q} : Finset Q) := by rw [this]; exact Finset.mem_univ x
  simpa using hx

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_cover (h : KuHyp G T M H P z) {p q : G} (hp : p ∈ kuR T M) (hq : q ∈ kuR T M)
    (hpV : p ∉ pCoreOf 2 M) (hqV : q ∉ pCoreOf 2 M) (hpqV : p⁻¹ * q ∉ pCoreOf 2 M)
    (hpq'V : p * q ∉ pCoreOf 2 M) {a : G} (ha : a ∈ kuR T M) :
    a ∈ pCoreOf 2 M ∨ p⁻¹ * a ∈ pCoreOf 2 M ∨ q⁻¹ * a ∈ pCoreOf 2 M ∨
      (p * q)⁻¹ * a ∈ pCoreOf 2 M := by
  have hVR : pCoreOf 2 M ≤ kuR T M := h.pCore_le_kuR
  have hVn : ((pCoreOf 2 M).subgroupOf (kuR T M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVR]
    intro r hr
    exact h.mem_normalizer_V_of_mem_M (oTwoUpper_le M (show r ∈ kuR T M from hr).2)
  have hQ : Nat.card (↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact h.relIndex_pCore_kuR
  have key : ∀ g : ↥(kuR T M),
      (QuotientGroup.mk g : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) = 1 ↔
        (g : G) ∈ pCoreOf 2 M := fun g => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have key2 : ∀ g g' : ↥(kuR T M),
      (QuotientGroup.mk g : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) = QuotientGroup.mk g' ↔
        ((g : G)⁻¹ * (g' : G)) ∈ pCoreOf 2 M := fun g g' => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hmain := eq_of_card_four hQ
    (p := (QuotientGroup.mk ⟨p, hp⟩ : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)))
    (q := QuotientGroup.mk ⟨q, hq⟩)
    (fun hh => hpV ((key ⟨p, hp⟩).mp hh))
    (fun hh => hqV ((key ⟨q, hq⟩).mp hh))
    (fun hh => hpqV ((key2 ⟨p, hp⟩ ⟨q, hq⟩).mp hh))
    (fun hh => by
      apply hpq'V
      have := (key (⟨p, hp⟩ * ⟨q, hq⟩)).mp (by rw [QuotientGroup.mk_mul]; exact hh)
      exact this)
    (QuotientGroup.mk ⟨a, ha⟩)
  rcases hmain with h0 | h1 | h2 | h3
  · exact Or.inl ((key ⟨a, ha⟩).mp h0)
  · exact Or.inr (Or.inl ((key2 ⟨p, hp⟩ ⟨a, ha⟩).mp h1.symm))
  · exact Or.inr (Or.inr (Or.inl ((key2 ⟨q, hq⟩ ⟨a, ha⟩).mp h2.symm)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have := (key2 (⟨p, hp⟩ * ⟨q, hq⟩) ⟨a, ha⟩).mp (by rw [QuotientGroup.mk_mul]; exact h3.symm)
    simpa using this

theorem sq_eq_one_of_cover_case (h : KuHyp G T M H P z) {u ε a : G} (hu : u ∈ kuR T M)
    (huV : u ∉ pCoreOf 2 M) (hε : ε ∈ kuR T M) (hεε : ε * ε = 1) (hεu : u * ε = ε * u)
    (hav : ε⁻¹ * a ∈ pCoreOf 2 M) (hau : u * a = a * u) : a * a = 1 := by
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hεε
  rw [hεi] at hav
  have hvu : u * (ε * a) = (ε * a) * u := by
    calc u * (ε * a) = (u * ε) * a := by group
      _ = (ε * u) * a := by rw [hεu]
      _ = ε * (u * a) := by group
      _ = ε * (a * u) := by rw [hau]
      _ = (ε * a) * u := by group
  have hv2 : ε * a ∈ kuV2 T M := by
    rw [← h.centralizer_pCore_eq_kuV2 hu huV]
    exact ⟨hav, Subgroup.mem_centralizer_singleton_iff.mpr hvu.symm⟩
  have hvε : (ε * a) * ε = ε * (ε * a) := h.kuV2_comm hv2 hε
  have hvv : (ε * a) * (ε * a) = 1 := h.kuV2_sq hv2
  have ha : a = ε * (ε * a) := by rw [← mul_assoc, hεε, one_mul]
  calc a * a = (ε * (ε * a)) * (ε * (ε * a)) := by rw [← ha]
    _ = (ε * ε) * ((ε * a) * (ε * a)) := by
      calc (ε * (ε * a)) * (ε * (ε * a)) = ε * ((ε * a) * ε) * (ε * a) := by group
        _ = ε * (ε * (ε * a)) * (ε * a) := by rw [hvε]
        _ = (ε * ε) * ((ε * a) * (ε * a)) := by group
    _ = 1 := by rw [hεε, hvv, one_mul]

theorem exists_cover_of_invol (h : KuHyp G T M H P z) {u : G} (hu : u ∈ kuR T M)
    (huV : u ∉ pCoreOf 2 M) (huu : u * u = 1) :
    ∃ c : G, c ∈ kuR T M ∧ c * c = 1 ∧ u * c = c * u ∧
      ∀ a ∈ kuR T M, a ∈ pCoreOf 2 M ∨ u⁻¹ * a ∈ pCoreOf 2 M ∨ c⁻¹ * a ∈ pCoreOf 2 M ∨
        (u * c)⁻¹ * a ∈ pCoreOf 2 M := by
  obtain ⟨y, hyL, -, hy3, hyR, -, hf, hg⟩ := h.exists_y
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.oTwoUpper_le_normalizer_V hyL
  have hcomm : u * (y * u * y⁻¹) = (y * u * y⁻¹) * u :=
    h.commute_conj_involution hyR hy3' hf hg hu huu
  set c : G := y * u * y⁻¹ with hc
  have hcR : c ∈ kuR T M := (Subgroup.mem_normalizer_iff.mp hyR u).mp hu
  have hcc : c * c = 1 := by
    have : c * c = y * (u * u) * y⁻¹ := by rw [hc]; group
    rw [this, huu]; group
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hcV : c ∉ pCoreOf 2 M := fun hh =>
    huV ((Subgroup.mem_normalizer_iff.mp hyV u).mpr hh)
  have hucV : u * c ∉ pCoreOf 2 M := by
    intro hh
    apply huV
    apply hg u hu
    have : y * u * y⁻¹ * u⁻¹ = u * c := by rw [hui, ← hcomm]
    rw [this]; exact hh
  refine ⟨c, hcR, hcc, hcomm, fun a ha => ?_⟩
  exact h.exists_cover hu hcR huV hcV (by rw [hui]; exact hucV) hucV ha

theorem sq_eq_one_of_commute (h : KuHyp G T M H P z) {u a : G} (hu : u ∈ kuR T M)
    (huV : u ∉ pCoreOf 2 M) (huu : u * u = 1) (ha : a ∈ kuR T M) (hau : u * a = a * u) :
    a * a = 1 := by
  obtain ⟨c, hcR, hcc, hcu, hcov⟩ := h.exists_cover_of_invol hu huV huu
  rcases hcov a ha with h0 | h1 | h2 | h3
  · exact h.pCore_sq h0
  · exact h.sq_eq_one_of_cover_case hu huV hu huu rfl h1 hau
  · exact h.sq_eq_one_of_cover_case hu huV hcR hcc hcu h2 hau
  · refine h.sq_eq_one_of_cover_case hu huV (mul_mem hu hcR) ?_ ?_ h3 hau
    · calc u * c * (u * c) = (u * u) * (c * c) := by
            calc u * c * (u * c) = u * (c * u) * c := by group
              _ = u * (u * c) * c := by rw [hcu]
              _ = (u * u) * (c * c) := by group
        _ = 1 := by rw [huu, hcc, one_mul]
    · calc u * (u * c) = u * (c * u) := by rw [hcu]
        _ = u * c * u := by group

theorem abelian_complement_elem (h : KuHyp G T M H P z) {A' : Subgroup G}
    (hle : A' ≤ kuR T M) (hab : IsMulCommutative A') (hcard : Nat.card A' = 16)
    (hAV : A' ⊓ pCoreOf 2 M = kuV2 T M) (hinv : ∃ u ∈ A', u ∉ kuV2 T M ∧ u * u = 1) :
    IsElemAbelian 2 A' := by
  obtain ⟨u, huA, huV2, huu⟩ := hinv
  have huV : u ∉ pCoreOf 2 M := fun hh => huV2 (by rw [← hAV]; exact ⟨huA, hh⟩)
  refine ⟨hab, fun x hx => ?_⟩
  rw [pow_two]
  refine h.sq_eq_one_of_commute (hle huA) huV huu (hle hx) ?_
  exact congrArg Subtype.val (hab.is_comm.comm ⟨u, huA⟩ ⟨x, hx⟩)

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
