module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.TL4SepFamB
public import CFSG.ClassicalInvolution.Q3.TL4SepQuotB
public import CFSG.ClassicalInvolution.Q3.TL4SepThmAD
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem T4Hyp.toTightFam (h : T4Hyp r G Δ) : TightFam r G Δ where
  conjInvariant := h.hyp.conjInvariant
  inv := fun J hJ => (h.hyp.omega1 J hJ).1
  gen := fun _ hJ => h.gen hJ
  twoGroup := h.twoGroup
  quat := h.quat
  tight := h.tight
  noTwins := h.noTwins

omit [Finite G] in
theorem TightFam.sub (h : TightFam r G Δ) {Δ' : Set (Subgroup G)} (hsub : Δ' ⊆ Δ)
    (hinv : ConjInvariant Δ') : TightFam r G Δ' where
  conjInvariant := hinv
  inv := fun J hJ => h.inv J (hsub hJ)
  gen := fun J hJ => h.gen J (hsub hJ)
  twoGroup := fun J hJ => h.twoGroup J (hsub hJ)
  quat := fun J hJ => h.quat J (hsub hJ)
  tight := fun J hJ => h.tight J (hsub hJ)
  noTwins := fun J hJ J' hJ' => h.noTwins J (hsub hJ) J' (hsub hJ')

theorem commute_of_mem_oddCoreImg {H P : Subgroup G} (hPn : P.Normal) (hP2 : IsPGroup 2 P)
    {n x : G} (hn : n ∈ oddCoreImg H) (hxH : x ∈ H) (hxP : x ∈ P) : n * x = x * n := by
  have hc1 : n * x * n⁻¹ * x⁻¹ ∈ oddCoreImg H := by
    have h1 : x * n⁻¹ * x⁻¹ ∈ oddCoreImg H :=
      conj_mem_oddCoreImg (Subgroup.le_normalizer hxH) (Subgroup.inv_mem _ hn)
    have := Subgroup.mul_mem _ hn h1
    rwa [show n * (x * n⁻¹ * x⁻¹) = n * x * n⁻¹ * x⁻¹ by group] at this
  have hc2 : n * x * n⁻¹ * x⁻¹ ∈ P := P.mul_mem (hPn.conj_mem x hxP n) (P.inv_mem hxP)
  have hc := eq_one_of_isPGroup_of_mem_odd (odd_natCard_oddCoreImg H) hc1
    (hP2.to_le (Subgroup.zpowers_le.mpr hc2))
  calc n * x = n * x * n⁻¹ * x⁻¹ * (x * n) := by group
    _ = x * n := by rw [hc, one_mul]

theorem T4Hyp.commutes_of_le_proper (hD : ThmD1RBelow r (Nat.card G)) (h : T4Hyp r G Δ)
    {J L : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ) (hnc : ¬ ∃ g : G, conjSub g J = L) {u v : G}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v) {P : Subgroup G}
    (hPn : P.Normal) (hP2 : IsPGroup 2 P) (huP : u ∈ P) (hvP : v ∈ P) {H : Subgroup G}
    (hH : H ≠ ⊤) (hJH : J ≤ H) (hLH : L ≤ H) : Commutes J L := by
  have hr := h.three_le hJ
  have hJ2 := h.isPGroup_of_inO2 hJ hu ⟨P, hPn, hP2, huP⟩
  have hL2 := h.isPGroup_of_inO2 hL hv ⟨P, hPn, hP2, hvP⟩
  have hJL : J ≠ L := fun e => hnc ⟨1, by rw [conjSub_one, e]⟩
  have hsub : CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L ⊆ Δ := by
    rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact h.hyp.conjInvariant g J hJ
    · exact h.hyp.conjInvariant g L hL
  have hF : TightFam r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) :=
    h.toTightFam.sub hsub (conjInvariant_union (conjInvariant_conjClass J)
      (conjInvariant_conjClass L))
  have hFH := hF.restrict H
  have hJm : J.subgroupOf H ∈
      restrictFamily (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) H :=
    ⟨J, Or.inl (CoreAssembly.mem_conjClass_self J), hJH, rfl⟩
  have hLm : L.subgroupOf H ∈
      restrictFamily (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) H :=
    ⟨L, Or.inr (CoreAssembly.mem_conjClass_self L), hLH, rfl⟩
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
  have hN : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hlt : Nat.card (↥H ⧸ classicalInvolutionOddCore ↥H) < Nat.card G :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans_lt
      (lt_of_le_of_ne (Subgroup.card_le_card_group _)
        (fun e => hH ((Subgroup.card_eq_iff_eq_top _).mp e)))
  have hPHn : ((P.subgroupOf H).map f).Normal := by
    have : P.Normal := hPn
    exact Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  have hPH2 : IsPGroup 2 ↥((P.subgroupOf H).map f) :=
    (hP2.comap_of_injective _ (Subgroup.subtype_injective _)).map f
  have hall : ∀ K ∈ Set.image (fun K : Subgroup ↥H => K.map f)
      (restrictFamily (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) H),
      ∀ z, IsUniqueInvolution K z → TightInO2 z := by
    rintro _ ⟨_, ⟨K, hK, hKH, rfl⟩, rfl⟩ z hz
    obtain ⟨w, hw⟩ := hF.inv K hK
    have hwP : w ∈ P := by
      rcases hK with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · rw [hw.eq (hu.conj g)]
        exact hPn.conj_mem u huP g
      · rw [hw.eq (hv.conj g)]
        exact hPn.conj_mem v hvP g
    have hwH : w ∈ H := hKH hw.mem
    have hz' : z = f ⟨w, hwH⟩ :=
      hz.eq (isUniqueInvolution_map_mk hN (isUniqueInvolution_subgroupOf hw hKH))
    exact ⟨_, hPHn, hPH2, hz' ▸ ⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwP, rfl⟩⟩
  have hnc' : ¬ ∃ g : ↥H ⧸ classicalInvolutionOddCore ↥H,
      conjSub g ((J.subgroupOf H).map f) = (L.subgroupOf H).map f := by
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← AscQuot.map_conjSub] at hx
    obtain ⟨m, -, hm⟩ := hFH.exists_conj_of_map_eq hN (hFH.conjInvariant x _ hJm) hLm hx
    rw [← conjSub_mul] at hm
    obtain ⟨y, -, hy⟩ := exists_conjSub_of_restrict hJH hLH ⟨_, hm⟩
    exact hnc ⟨y, hy⟩
  have hc := hD _ hlt _ (hFH.t4Hyp_quot hr) hall _ ⟨_, hJm, rfl⟩ _ ⟨_, hLm, rfl⟩ hnc'
  have hLN : L ≤ Subgroup.normalizer (J : Set G) := by
    intro s hs
    have h1 := hc _ ⟨⟨u, hJH hu.mem⟩, Subgroup.mem_subgroupOf.mpr hu.mem, rfl⟩ _
      ⟨⟨s, hLH hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have h2 : f ⟨u, hJH hu.mem⟩ = f (⟨s, hLH hs⟩ * ⟨u, hJH hu.mem⟩ * ⟨s, hLH hs⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have hn : u⁻¹ * (s * u * s⁻¹) ∈ oddCoreImg H := ⟨_, QuotientGroup.eq.mp h2, rfl⟩
    have hnu := commute_of_mem_oddCoreImg hPn hP2 hn (hJH hu.mem) huP
    exact hF.mem_normalizer_of_conj_eq_mul (Or.inl (CoreAssembly.mem_conjClass_self J)) hu
      (mul_inv_cancel_left u (s * u * s⁻¹)).symm
      ((odd_natCard_oddCoreImg H).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hn))
      (h.tight J hJ u hu (Subgroup.mem_centralizer_singleton_iff.mpr hnu))
  exact commutes_of_le_normalizer h.hyp (mem_RSet_self hJ hJ2) (mem_RSet_self hL hL2) hJ2 hL2
    hJL hLN

end CFSG.ClassicalInvolution.Q3.TL4
