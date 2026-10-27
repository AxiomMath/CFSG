module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup UnbalancedLayer UnbalancedGS

variable {X : Type} [Group X] [Finite X]

theorem fusionZStar_ne_of_central_involution {M : Subgroup X} {y : X} (hy : orderOf y = 2)
    (hyM : y ∈ M) (hMy : M ≤ centralizer ({y} : Set X)) :
    Open.fusionZStar M ≠ pPrimeCore 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ne, fusionZStar_eq_iff]
  intro hbot
  have hc : (QuotientGroup.mk' (pPrimeCore 2 M) ⟨y, hyM⟩) ∈ center (M ⧸ pPrimeCore 2 M) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hMy g.2))
  rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have h := (pPrimeCore 2 M).orderOf_dvd_natCard hc
  rw [Subgroup.orderOf_mk, hy] at h
  exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := M)) h)
    (by norm_num)

theorem fusionZStar_le_of_central_involution {H : Type*} [Group H] [Finite H] {T M : Subgroup H}
    (hTM : T ≤ M) {y : H} (hy : orderOf y = 2) (hyT : y ∈ T)
    (hyc : ∀ g ∈ M, g * y = y * g) (hZ : Nat.card (center (T ⧸ pPrimeCore 2 T)) ≤ 2) :
    (Open.fusionZStar T).map T.subtype ≤
      (pPrimeCore 2 T).map T.subtype ⊔ (Open.fusionZStar M).map M.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 T with hO
  set π := QuotientGroup.mk' O with hπ
  set yT : T := ⟨y, hyT⟩ with hyTdef
  have hZ' : Nat.card (center (T ⧸ O)) ≤ 2 := hZ
  have hyc' : π yT ∈ center (T ⧸ O) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc g (hTM g.2))
  have hy1 : π yT ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h2 := O.orderOf_dvd_natCard h
    rw [hyTdef, Subgroup.orderOf_mk, hy] at h2
    exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := T)) h2)
      (by norm_num)
  have hyM : (⟨y, hTM hyT⟩ : M) ∈ Open.fusionZStar M := by
    rw [fusionZStar_eq_comap, mem_comap, mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc g g.2)
  rintro _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, fusionZStar_eq_comap, mem_comap] at hz
  have hcases : π z = 1 ∨ π z = π yT := by
    by_contra hc
    push Not at hc
    obtain ⟨hz1, hzy⟩ := hc
    have hsub : ({1, π yT, π z} : Set (T ⧸ O)) ⊆ (center (T ⧸ O) : Set (T ⧸ O)) := by
      intro a ha
      rcases ha with rfl | rfl | rfl
      · exact one_mem _
      · exact hyc'
      · exact hz
    have hc3 : ({1, π yT, π z} : Set (T ⧸ O)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hzy)]
      rintro (h | h)
      · exact hy1 h.symm
      · exact hz1 h.symm
    have h3 : 3 ≤ Nat.card (center (T ⧸ O)) := by
      calc 3 = ({1, π yT, π z} : Set (T ⧸ O)).ncard := hc3.symm
        _ ≤ (center (T ⧸ O) : Set (T ⧸ O)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card (center (T ⧸ O)) := (Nat.card_coe_set_eq _).symm
    omega
  rcases hcases with h | h
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact mem_sup_left (mem_map_of_mem T.subtype h)
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq] at h
    have hz' : (z : H) = y * ((yT⁻¹ * z : T) : H) := by simp [hyTdef]
    rw [Subgroup.coe_subtype, hz']
    exact mul_mem (mem_sup_right (mem_map_of_mem M.subtype hyM))
      (mem_sup_left (mem_map_of_mem T.subtype h))

theorem stable_pump_up_of_component (hPump : AlternatingPumpUpInput)
    (hHe : TBLit.HeldTrivialMultiplier) (hK : Assembly.KProper Blueprint.Catalog X) {x y : X}
    {T M : Subgroup X} {m : ℕ} (hx : orderOf x = 2) (hy : orderOf y = 2) (hyZ : y ∉ center X)
    (hTxy : T ≤ centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))))
    (hyT : y ∈ T) (hmo : Odd m) (hm7 : 7 ≤ m)
    (eT : T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin m))
    (hZT : Nat.card (center (T ⧸ pPrimeCore 2 T)) ≤ 2) (hMy : M ≤ centralizer ({y} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({y} : Set X))))
    (hTM : T ≤ M ⊔ conjugate M x) (hMx : conjugate M x = M) :
    ∃ m' : ℕ, IsDoublePair y M m' ∧ y ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hb := centralizer ({y} : Set X) with hHb
  set Cx := centralizer ({x} : Set X) with hCx
  have hTHb : T ≤ Hb := hTxy.trans inf_le_right
  have hTM' : T ≤ M := by rw [hMx, sup_idem] at hTM; exact hTM
  have hyM : y ∈ M := hTM' hyT
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp (hTxy hyT).1).symm
  have hxHb : x ∈ Hb := mem_centralizer_singleton_iff.mpr hxy
  set x' : Hb := ⟨x, hxHb⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hHbne : Hb ≠ ⊤ := by
    intro htop
    apply hyZ
    rw [mem_center_iff]
    intro g
    have hg : g ∈ Hb := htop ▸ mem_top g
    exact (mem_centralizer_singleton_iff.mp hg)
  have hKH : SectionRank.IsKGroupCat Hb :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK Hb hHbne
  have hxN : x' ∈ normalizer ((M.subgroupOf Hb : Subgroup Hb) : Set Hb) := by
    apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
    rw [conjugate_subgroupOf_eq M Hb x', hMx]
  have hcenx : centralizer ({x'} : Set Hb) = (Cx ⊓ Hb).subgroupOf Hb := by
    ext w
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, w.2⟩, fun h => Subtype.ext h.1⟩
  have hT'M : T.subgroupOf Hb ≤ M.subgroupOf Hb := fun w hw => hTM' hw
  have hT'C : T.subgroupOf Hb ≤ centralizer ({x'} : Set Hb) := by
    rw [hcenx]
    intro w hw
    exact mem_subgroupOf.mpr (hTxy (mem_subgroupOf.mp hw))
  have hT'pc : IsPComponent 2 ((T.subgroupOf Hb).subgroupOf (centralizer ({x'} : Set Hb))) := by
    rw [hcenx, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have eT' : T.subgroupOf Hb ⧸ Open.fusionZStar (T.subgroupOf Hb) ≃* alternatingGroup (Fin m) :=
    (fusionZStarQuotCongr (subgroupOfEquivOfLe hTHb)).trans eT
  have eM : M ⧸ Open.fusionZStar M ≃* M.subgroupOf Hb ⧸ Open.fusionZStar (M.subgroupOf Hb) :=
    fusionZStarQuotCongr (subgroupOfEquivOfLe hMy).symm
  have hne : Open.fusionZStar M ≠ pPrimeCore 2 M := fusionZStar_ne_of_central_involution hy hyM hMy
  have hyHb : y ∈ Hb := mem_centralizer_singleton_iff.mpr rfl
  have hZT' : Nat.card (center (T.subgroupOf Hb ⧸ pPrimeCore 2 (T.subgroupOf Hb))) ≤ 2 := by
    let e := coreQuotCongr (subgroupOfEquivOfLe hTHb)
    have h1 : Nat.card ((center _).map e.toMonoidHom) = Nat.card (center _) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    rw [map_center_eq_of_mulEquiv e] at h1
    omega
  have hcore := fusionZStar_le_of_central_involution (T := T.subgroupOf Hb)
    (M := M.subgroupOf Hb) hT'M (y := ⟨y, hyHb⟩) (by rw [Subgroup.orderOf_mk]; exact hy)
    (mem_subgroupOf.mpr hyT)
    (fun g _ => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)) hZT'
  rcases hPump Hb hKH (M.subgroupOf Hb) hM x' hx' hxN (T.subgroupOf Hb) hT'M hT'C hT'pc hcore m
      hmo hm7 ⟨eT'⟩ with ⟨m', hm'o, hmm', ⟨eA⟩⟩ | ⟨-, ⟨eHe⟩⟩
  · exact ⟨m', ⟨hy, hMy, hM, hm'o, hm7.trans hmm', hne, ⟨eM.trans eA⟩⟩, hyM⟩
  · exfalso
    have hq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hMy)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hM)
    have hZ := hHe (M ⧸ pPrimeCore 2 M) hq ⟨(coreQuotientCenterEquiv M).trans (eM.trans eHe)⟩
    exact hne ((fusionZStar_eq_iff M).mpr hZ)

theorem stable_pump_up (hPump : AlternatingPumpUpInput) (hHe : TBLit.HeldTrivialMultiplier)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput)
    (hK : Assembly.KProper Blueprint.Catalog X) {x y : X} {L M : Subgroup X} {m : ℕ}
    (hP : IsDoublePair x L m) (hy : orderOf y = 2) (hyZ : y ∉ center X)
    (hTxy : gsFixedLayer L y ≤ centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))
    (hTpc : IsPComponent 2 ((gsFixedLayer L y).subgroupOf
      (centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))))
    (φ : gsFixedLayer L y ⧸ pPrimeCore 2 (gsFixedLayer L y) ≃* L ⧸ pPrimeCore 2 L)
    (hyT : y ∈ gsFixedLayer L y) (hMy : M ≤ centralizer ({y} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({y} : Set X))))
    (hTM : gsFixedLayer L y ≤ M ⊔ conjugate M x) (hMx : conjugate M x = M) :
    ∃ m' : ℕ, IsDoublePair y M m' ∧ y ∈ M := by
  obtain ⟨-, -, hZL, -⟩ := hP.coreQuotient hSchur
  obtain ⟨hx, -, -, hmo, hm7, -, ⟨eL⟩⟩ := hP
  have hZT : Nat.card (center (gsFixedLayer L y ⧸ pPrimeCore 2 (gsFixedLayer L y))) ≤ 2 := by
    have h1 : Nat.card ((center _).map φ.toMonoidHom) = Nat.card (center _) :=
      Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
    rw [map_center_eq_of_mulEquiv φ] at h1
    omega
  exact stable_pump_up_of_component hPump hHe hK hx hy hyZ hTxy hTpc hyT hmo hm7
    ((fusionZStarQuotOfCore φ).trans eL) hZT hMy hM hTM hMx

end CFSG.ComponentClassification.Sol78
