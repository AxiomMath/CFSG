module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGDescent
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndConc
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndInd
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndInputs

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Sol78.F514

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem catalog_quotient_center_of_kProper (hKp : Assembly.KProper Blueprint.Catalog G)
    {N B : Subgroup G} (hNtop : N ≠ ⊤) (hBN : B ≤ N)
    (hBq : IsQuasisimple (↥B ⧸ pPrimeCore 2 ↥B)) :
    Blueprint.Catalog ((↥B ⧸ pPrimeCore 2 ↥B) ⧸ center (↥B ⧸ pPrimeCore 2 ↥B)) := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hπ
  set Zh : Subgroup ↥B := (center (↥B ⧸ pPrimeCore 2 ↥B)).comap π with hZh
  have : Zh.Normal := Subgroup.Normal.comap inferInstance π
  have hle : pPrimeCore 2 ↥B ≤ Zh := fun x hx => by
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hZh, mem_comap, h1]
    exact one_mem _
  have hmap : Zh.map π = center (↥B ⧸ pPrimeCore 2 ↥B) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  set L := Zh.map B.subtype with hL
  have hLB : L ≤ B := map_subtype_le _
  have hLsub : L.subgroupOf B = Zh := comap_map_eq_self_of_injective B.subtype_injective Zh
  have : (L.subgroupOf B).Normal := hLsub ▸ (inferInstance : Zh.Normal)
  let e : (↥B ⧸ pPrimeCore 2 ↥B) ⧸ center (↥B ⧸ pPrimeCore 2 ↥B) ≃* ↥B ⧸ L.subgroupOf B :=
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hle)).trans
      (QuotientGroup.quotientMulEquivOfEq hLsub.symm)
  have : IsSimpleGroup ((↥B ⧸ pPrimeCore 2 ↥B) ⧸ center (↥B ⧸ pPrimeCore 2 ↥B)) := hBq.2.1
  have hs : IsSimpleGroup (↥B ⧸ L.subgroupOf B) := e.symm.isSimpleGroup
  have hna : ∃ a b : ↥B ⧸ L.subgroupOf B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hBq.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hBtop : B ≠ ⊤ := fun h => hNtop (eq_top_iff.mpr (h ▸ hBN))
  exact SectionRank.catalog_of_mulEquiv e (hKp B L hBtop hLB hs hna)

theorem eq_mk_z_of_central_involution {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type}
    [Group 𝕊] [Finite 𝕊] {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)}
    (H : Hyp L₀ L Q S T z t s ε Lin) {B : Subgroup G} (hRsB : conjugate (S ⊓ L) s ≤ B)
    {x : ↥B ⧸ pPrimeCore 2 ↥B} (hx : x ∈ oddQuotImage B (conjugate (S ⊓ L) s))
    (hx2 : orderOf x = 2) (hxc : ∀ d ∈ oddQuotImage B (conjugate (S ⊓ L) s), x * d = d * x) :
    x = QuotientGroup.mk' (pPrimeCore 2 ↥B) ⟨z, hRsB H.z_mem_Rs⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hπ
  have hRs2 : IsPGroup 2 ↥((conjugate (S ⊓ L) s).subgroupOf B) :=
    (H.sec5.R_sylow.isPGroup.map _).comap_subtype
  have hinj := GSThmB.OddQuot.injOn_of_isPGroup hRs2
  obtain ⟨r, hr, rfl⟩ := hx
  have hrr : r * r = 1 := by
    refine hinj (mul_mem hr hr) (one_mem _) ?_
    have h1 := pow_orderOf_eq_one (π r)
    rw [hx2, sq] at h1
    rw [map_mul, map_one]
    exact h1
  have hr1 : r ≠ 1 := fun h => by
    rw [h, map_one, orderOf_one] at hx2
    omega
  have hrc : ∀ d ∈ conjugate (S ⊓ L) s, (r : G) * d = d * r := by
    intro d hd
    have hdB : (⟨d, hRsB hd⟩ : ↥B) ∈ (conjugate (S ⊓ L) s).subgroupOf B := hd
    have h1 := hxc (π ⟨d, hRsB hd⟩) (mem_map_of_mem π hdB)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hinj (mul_mem hr hdB) (mul_mem hdB hr) h1)
  obtain ⟨ρ', b', j, hdih, hc⟩ := H.exists_dihData_Rs
  have hrz : (r : G) = z := by
    rw [← hc]
    exact hdih.central_inv_eq hr (congrArg Subtype.val hrr) (fun h => hr1 (Subtype.ext h)) hrc
  congr 1
  exact Subtype.ext hrz

theorem false_of_hyp_endKnownGroupsInput {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type}
    [Group 𝕊] [Finite 𝕊] {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)}
    (H : Hyp L₀ L Q S T z t s ε Lin) (h3 : Asc76.Asc76Theorem3Large)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hKG : EndKnownGroupsInput) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWodd, hW1, hW2⟩ := H.exists_W h3
  by_cases hWbot : W = ⊥
  ·
    refine H.false_of_commutator_eq_bot h3 hK hcalc fun r hr hr2 => ?_
    have h1 := (hW2 t H.sec5.tR H.sec5.t2 r hr hr2).2
    rw [hWbot] at h1
    exact le_bot_iff.mp h1
  have hWN : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ normalizer (W : Set G) :=
    fun B₁ B₂ h₁ h₂ h₁1 h₂1 => (hW1 B₁ B₂ h₁ h₂ h₁1 h₂1).2.2
  obtain ⟨-, hs, -, hCz, hCt⟩ := H.normalizer_W_facts hK hcalc hWN
  have hNtop := H.normalizer_W_ne_top hWbot hWodd
  obtain ⟨B, hBN, hB, hLB, -, -⟩ := H.exists_component hCz hCt
  have hBs := H.conjugate_s_eq h3 hCt hNtop hs hBN hB hLB
  have hRsB : conjugate (S ⊓ L) s ≤ B := fun x hx => by
    have h1 : s * x * s⁻¹ ∈ S ⊓ L := UnbalancedLayer.mem_conjugate_iff.mp hx
    rw [← hBs, UnbalancedLayer.mem_conjugate_iff]
    exact hLB (mem_inf.mp h1).2
  obtain ⟨z', t', K, P, D, rfl, rfl, rfl, hKc, ⟨eK⟩, hPsyl, ht'P, ht'2, hzt', hz'D, hD, hPD,
    hD2, hDcard, hDdih, hsolv⟩ := H.exists_quotient_data h3 hLB hRsB
  have hBq : IsQuasisimple (↥B ⧸ pPrimeCore 2 ↥B) :=
    isQuasisimple_quotient_of_isPComponent hBN hB
  have hO : pPrimeCore 2 (↥B ⧸ pPrimeCore 2 ↥B) = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_two
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := H.sec5.quotient_simple.1
  have : IsSimpleGroup (oddQuotImage B L ⧸ pPrimeCore 2 (oddQuotImage B L)) :=
    eK.symm.isSimpleGroup
  have hKna : ∃ a b : oddQuotImage B L ⧸ pPrimeCore 2 (oddQuotImage B L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := H.sec5.quotient_nonabelian
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul, h]))⟩
  by_cases hzc : z' ∈ center (↥B ⧸ pPrimeCore 2 ↥B)
  ·
    have hCtop : centralizer ({z'} : Set (↥B ⧸ pPrimeCore 2 ↥B)) = ⊤ :=
      eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc g)
    have hsub := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hKc.2.1).mp hKc.2.2).1
    have hsurj : Function.Surjective
        (centralizer ({z'} : Set (↥B ⧸ pPrimeCore 2 ↥B))).subtype :=
      fun y => ⟨⟨y, hCtop ▸ mem_top y⟩, rfl⟩
    have h1 := IsSubnormal.map hsurj hsub
    rw [map_subgroupOf_eq_of_le hKc.2.1] at h1
    have hKtop : oddQuotImage B L = ⊤ := by
      rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hBq h1 with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hKna
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (mem_center_iff.mp (h b.2) a)
    let e₀ : ↥(oddQuotImage B L) ≃* (↥B ⧸ pPrimeCore 2 ↥B) :=
      (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
    exact H.false_of_equiv h3 hCt hNtop hBN hB hLB
      (eK.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans
        ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)))
  ·
    have hz'eq := eq_mk_z_of_central_involution H hRsB hz'D hKc.1
      fun d hd => (mem_centralizer_singleton_iff.mp (hD hd).1).symm
    have hDZ : oddQuotImage B (conjugate (S ⊓ L) s) ⊓ center (↥B ⧸ pPrimeCore 2 ↥B) = ⊥ := by
      by_contra hne
      have h2 : IsPGroup 2 ↥(oddQuotImage B (conjugate (S ⊓ L) s) ⊓
          center (↥B ⧸ pPrimeCore 2 ↥B)) := hD2.to_le inf_le_left
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero]))
      obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2
        (by rw [hn]; exact dvd_pow_self 2 hn0)
      rw [Subgroup.orderOf_mk] at hx2
      obtain ⟨hxD, hxZ⟩ := mem_inf.mp hx
      have hxeq := eq_mk_z_of_central_involution H hRsB hxD hx2
        fun d _ => (mem_center_iff.mp hxZ d).symm
      exact hzc (by rw [hz'eq, ← hxeq]; exact hxZ)
    obtain ⟨t₀, hce⟩ := H.sec5.sec4.ce
    obtain ⟨⟨hKp, -, -⟩, -⟩ := hce
    exact not_isSolvable_centralizer_of_endKnownGroupsInput hKG hBq hO
      (catalog_quotient_center_of_kProper hKp hNtop hBN hBq) hzc hDZ hKc hKna
      (footeFamilyType_of_quotient_equiv H.sec5.quotient_nonabelian eK H.footeFamilyType_L)
      hPsyl ht'P ht'2 hzt' hz'D hD hPD hDdih (hDcard ▸ H.eight_le_card_R)
      (H.noPumpUp hK hcalc hWN hBN hB hLB hRsB) hsolv

end CFSG.ComponentClassification.Foote5
