module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKCInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPump

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS CFSG.Sporadic.HeldB
  CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeKC

open HeFM in
theorem exists_center_pair
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (e : ↥L ≃* Blueprint.NativeSporadic.He) {u : X} (hu : HeldTwoA L u) :
    u ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype ∧
      ∃ z ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype,
        z * z = 1 ∧ z ≠ 1 ∧ z ≠ u ∧ u * z = z * u := by
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hKle : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 →
      (y : X) ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro y hy
    rw [← mem_center_trS_iff φ hKle y, hK]
    exact hy
  have hp₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ∈ heP := (mem_centralizerIn.mp HeGS.heGSU.2).1
  set q₂ : ↥heP := ⟨HeGS.heGSU, hp₂⟩ with hq₂
  have ho₂ : orderOf (HeGS.heGSU : Equiv.Perm (Fin 8330)) = 2 :=
    orderOf_of_mem_conjClass HeGS.heGSU_mem_conjClass
  have ho₁₂ : orderOf (heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330))) = 2 :=
    orderOf_of_mem_conjClass HeGS.heGST0U_mem_conjClass
  have hs₁ : heGenPerm 0 * heGenPerm 0 = 1 := HeGS.heGenPerm0_sq
  have hs₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) * HeGS.heGSU = 1 := by
    rw [← sq, ← ho₂, pow_orderOf_eq_one]
  have hn₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ≠ 1 := fun h => by
    rw [h, orderOf_one] at ho₂
    norm_num at ho₂
  have hne : heGenPerm 0 ≠ (HeGS.heGSU : Equiv.Perm (Fin 8330)) := fun h => by
    rw [← h, hs₁, orderOf_one] at ho₁₂
    norm_num at ho₁₂
  have hcomm : heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330)) = HeGS.heGSU * heGenPerm 0 :=
    ((mem_centralizerIn.mp HeGS.heGSU.2).2).symm
  have hZ₁ : heGenPerm 0 ∈ heZ0 := HeGS.mem_heZ0_of_mem_ker HeGS.heGST0_mem_ker
  have hZ₂ : (HeGS.heGSU : Equiv.Perm (Fin 8330)) ∈ heZ0 :=
    HeGS.mem_heZ0_of_mem_ker HeGS.heGSU_mem_ker
  refine ⟨hZ ⟨u, hu.1⟩ (by rw [hφ]; exact hZ₁), (φ.symm q₂ : X),
    hZ _ (by rw [MulEquiv.apply_symm_apply]; exact hZ₂), ?_, ?_, ?_, ?_⟩
  · have h : φ.symm q₂ * φ.symm q₂ = 1 := by
      rw [← map_mul, show q₂ * q₂ = 1 from Subtype.ext hs₂, map_one]
    exact congrArg Subtype.val h
  · intro h
    have h' : φ.symm q₂ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact hn₂ (congrArg Subtype.val h')
  · intro h
    have h' : φ.symm q₂ = ⟨u, hu.1⟩ := Subtype.ext h
    have h'' := congrArg (fun y => (φ y : Equiv.Perm (Fin 8330))) h'
    simp only [MulEquiv.apply_symm_apply] at h''
    exact hne (h''.trans hφ).symm
  · have h1 : φ ⟨u, hu.1⟩ * q₂ = q₂ * φ ⟨u, hu.1⟩ := by
      apply Subtype.ext
      simp only [coe_mul]
      rw [hφ]
      exact hcomm
    have h2 : (⟨u, hu.1⟩ : ↥L) * φ.symm q₂ = φ.symm q₂ * ⟨u, hu.1⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h1
    exact congrArg Subtype.val h2

theorem centralizer_ne_top {X : Type} [Group X] (hsimp : IsSimpleGroup X)
    (hnab : ∃ x y : X, x * y ≠ y * x) {x : X} (hx : x ≠ 1) : centralizer ({x} : Set X) ≠ ⊤ := by
  intro htop
  have hcen : center X = ⊥ := center_eq_bot_of_simple hnab
  have hxc : x ∈ center X := mem_center_iff.mpr fun g =>
    (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({x} : Set X)))
  rw [hcen, mem_bot] at hxc
  exact hx hxc

theorem isComponent_of_end
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hD : L34RankTwoCentralFixedInput) (hKD : HeldKDiagonalStep) {X : Type} [Group X] [Finite X]
    {L : Subgroup X}
    (hset : HeldEndSetting X L) {a : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) {u : X}
    (hu : HeldTwoA L u) :
    IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHS, hW, hstd, ⟨e⟩, hrank⟩ := id hset
  obtain ⟨hsimp, hnab, hK, -, hLB, -, ⟨e₀⟩⟩ := id hHS
  set K := gsFixedLayer L u with hKdef
  set Cu := centralizer ({u} : Set X) with hCu
  set Ca := centralizer ({a} : Set X) with hCa
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hu2 : orderOf u = 2 := hu.2.1
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    norm_num at hu2
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hLa hu.1)).symm
  have hutop : Cu ≠ ⊤ := centralizer_ne_top hsimp hnab hu1
  have haL : a ∉ L := by
    intro haL
    have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
    have hc : center Blueprint.NativeSporadic.He = ⊥ := center_eq_bot_of_simple exists_mul_ne_held
    have hz : e ⟨a, haL⟩ ∈ center Blueprint.NativeSporadic.He := by
      rw [mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLa l.2))
    rw [hc, mem_bot, MulEquiv.map_eq_one_iff] at hz
    have h1 : a = 1 := congrArg Subtype.val hz
    rw [h1, orderOf_one] at ha
    norm_num at ha
  have hKL : K ≤ L ⊓ Cu := gsFixedLayer_le_inf L u
  have hKp1 : IsPComponent 2 (K.subgroupOf (L ⊓ Cu)) := isPComponent_gsFixedLayer_of_held e hu
  have hLs : (L.subgroupOf Ca).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Ca hLa).1 hLc).1
  have hLs' : ((L ⊓ Cu).subgroupOf (Ca ⊓ Cu)).IsSubnormal := by
    have h1 : ((L.subgroupOf Ca).subgroupOf ((Ca ⊓ Cu).subgroupOf Ca)).IsSubnormal :=
      hLs.subgroupOf
    have h2 := h1.map (f := (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)).toMonoidHom)
      (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)).surjective
    convert h2 using 1
    ext k
    simp only [mem_subgroupOf, mem_inf, mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨hkL, -⟩
      exact ⟨⟨⟨k, (mem_inf.mp k.2).1⟩, k.2⟩, hkL, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, (mem_inf.mp ((subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cu ≤ Ca)) y).2).2⟩
  have hKau : K ≤ Ca ⊓ Cu := hKL.trans (inf_le_inf_right _ hLa)
  have hKp : IsPComponent 2 (K.subgroupOf (Ca ⊓ Cu)) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hKL (inf_le_inf_right _ hLa)
      hLs').mpr hKp1
  obtain ⟨hKperf, hKt⟩ := heldTwoALayerFact X L ⟨e⟩ u hu
  have hKs : IsSimpleGroup (↥K ⧸ center ↥K) := HeInner.isSimpleGroup_of_l34 hKt
  have hKperf' : commutator ↥K = ⊤ := (isPerfect_iff.mpr hKperf).commutator_eq_top
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hKau).1 hKp).2.2
  have hOK : pPrimeCore 2 ↥K ≤ center ↥K := by
    have hne : pPrimeCore 2 ↥K ≠ ⊤ := by
      intro htop
      obtain ⟨-, hs, -⟩ := hKq
      have : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.subsingleton_iff.mpr htop
      have : Nontrivial ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) :=
        hs.toNontrivial
      have : Subsingleton ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
        constructor
        intro x y
        obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
        obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
        rw [Subsingleton.elim x' y']
      exact false_of_nontrivial_of_subsingleton
        ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
    exact Quasisimple.normal_le_center_of_ne_top ⟨hKperf', hKs⟩ _ hne
  have hZK : Open.fusionZStar ↥K = center ↥K := GrS5.fusionZStar_eq_center_of_le hKperf' hOK
  have hKt' : IsL34Type (↥K ⧸ Open.fusionZStar ↥K) :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZK).symm hKt
  obtain ⟨huZ, z, hzZ, hzz, hz1, hzu, huz⟩ := exists_center_pair e hu
  have hZsub : ∀ y ∈ (center ↥K).map K.subtype, y ∈ (Open.fusionZStar ↥K).map K.subtype := by
    rw [hZK]
    exact fun y hy => hy
  set V := zpowers u ⊔ zpowers z with hV
  have hVe : IsElemTwo V := (isElemTwo_zpowers huu).sup (isElemTwo_zpowers hzz) (by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute u z from huz) i j).eq)
  have hV4 : 4 ≤ Nat.card V := four_le_card_sup_zpowers huu hzz hu1 hz1 hzu.symm huz
  have hVZ : V ≤ (Open.fusionZStar ↥K).map K.subtype :=
    sup_le (zpowers_le.mpr (hZsub u huZ)) (zpowers_le.mpr (hZsub z hzZ))
  have hVK : V ≤ K := fun y hy => by
    obtain ⟨t, -, rfl⟩ := hVZ hy
    exact t.2
  have hVL : V ≤ L := hVK.trans (hKL.trans inf_le_left)
  have huV : u ∈ V := mem_sup_left (mem_zpowers u)
  obtain ⟨M, hMu, hMp, hKM, hKMp, hle, hswap, heq⟩ :=
    HeK.exists_pump hS hK ha hau hutop hKau hKp
  have hZX : ∀ x : X, x ≠ 1 → centralizer ({x} : Set X) ≠ ⊤ := fun x hx =>
    centralizer_ne_top hsimp hnab hx
  by_cases hMa : M = conjugate M a
  ·
    have hMa' : conjugate M a = M := hMa.symm
    rw [hMa', sup_idem] at hKM hKMp
    have hidx := HeK.index_eq_of_mem hD hK ha hu2 hutop hMu hMp hMa' hKM hKMp hle
      (hVK huV) hKt' (hZsub u huZ) (hZsub z hzZ) huu hzz hu1 hz1 hzu.symm huz
    have hTO := heq hidx hMa
    obtain ⟨hcO, -⟩ := HeUV.central_of_invariant hS hUO hheld hK hZX ha hLa haL hW hVL hVe hV4
      huV hu2 (hKau.trans inf_le_left) hVZ hMu hMp hMa' (hKM.trans inf_le_left) hTO
    have hKMle : K ≤ M := hKM.trans inf_le_left
    have hMperf : Group.IsPerfect ↥M := by
      have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hMp
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMu).toMonoidHom)
        (subgroupOfEquivOfLe hMu).surjective
    have hKn : (K.subgroupOf M).Normal := by
      have hN : M ≤ normalizer (K : Set X) := by
        rw [← hTO]
        refine sup_le le_normalizer (fun o ho => ?_)
        rw [mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [hcO o ho y (hKMle hy), mul_inv_cancel_right]
          exact hy
        · intro hy
          have h1 := hcO o ho _ (hKMle hy)
          have h2 : y = o * y * o⁻¹ := by
            calc y = o⁻¹ * (o * y * o⁻¹) * o := by group
              _ = o⁻¹ * (o * (o * y * o⁻¹)) := by rw [mul_assoc, ← h1]
              _ = o * y * o⁻¹ := by group
          rw [h2]
          exact hy
      exact ⟨fun k hk g => by
        rw [mem_subgroupOf] at hk ⊢
        exact (mem_normalizer_iff.mp (hN g.2) k).mp hk⟩
    have hKeq : K = M := GrS5.eq_of_pPrimeCore_sup_eq hKMle hKn hMperf (by rw [sup_comm]; exact hTO)
    rw [hKeq]
    exact HeUC.isComponent_of_central hMu hMp hcO
  ·
    exfalso
    have hfix := hswap hMa
    have hne : conjugate M a ≠ M := fun h => hMa h.symm
    by_cases hI : M ⊓ (conjugate M a ⊔ (pPrimeCore 2 ↥Cu).map Cu.subtype) ≤
        (pPrimeCore 2 ↥Cu).map Cu.subtype
    · have hV4' : Nat.card V = 4 := by
        have hle4 : Nat.card V ≤ 4 := by
          have huN : u ∈ normalizer (zpowers z : Set X) := by
            rw [mem_normalizer_iff]
            intro y
            constructor
            · intro hy
              obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
              rw [(Commute.zpow_right (show Commute u z from huz) k).eq, mul_inv_cancel_right]
              exact zpow_mem (mem_zpowers z) k
            · intro hy
              obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
              have h : y = z ^ k := by
                calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
                  _ = u⁻¹ * z ^ k * u := by rw [hk]
                  _ = z ^ k := by
                    rw [(Commute.zpow_right (show Commute u⁻¹ z from
                      (Commute.inv_left (show Commute u z from huz))) k).eq,
                      inv_mul_cancel_right]
              rw [h]
              exact zpow_mem (mem_zpowers z) k
          have h := card_zpowers_sup_le huu huN
          have h2 : Nat.card (zpowers z) = 2 := by
            rw [Nat.card_zpowers]
            exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
          rw [hV]
          omega
        omega
      have hcO := HeDM.central_of_trivial_meet hS hUO hheld hHS hW ha hLa hVL
        (HeUV.isFourGroup_of_card hVe hV4') huV hu1 (hKL.trans inf_le_left) hKau hKp hVZ hMu hMp
        hne hfix hI
      exact hKD X L hset a u M ha hLa hLc hu hMu hMp hne hfix (Or.inr hcO)
    · exact hKD X L hset a u M ha hLa hLc hu hMu hMp hne hfix (Or.inl hI)

end HeKC

theorem heldKNormalStep_of_diagonalStep
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hD : L34RankTwoCentralFixedInput) (hKD : HeldKDiagonalStep)
    (hKNC : HeldKNormalFromComponent) : HeldKNormalStep := by
  intro X _ _ L hset u hu
  obtain ⟨⟨-, -, -, -, -, ⟨a, ha, hLa, hLc⟩, -⟩, -⟩ := id hset
  exact hKNC X L hset u hu
    (HeKC.isComponent_of_end hS hUO hheld hD hKD hset ha hLa hLc hu)

end CFSG.ComponentClassification.GrSLit
