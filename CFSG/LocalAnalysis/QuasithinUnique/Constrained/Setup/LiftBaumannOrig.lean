module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNormalLS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigKernel

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open scoped Pointwise

section Defs

variable {G : Type} [Group G]

structure NaturalBaumannOutput (R V : Subgroup G) : Prop where
  baum_eq : autOn (baum R) V = autOn (thompsonJ R) V
  image_sylow : IsSylowTwoOf (autOn (baum R) V) (autOn (oddOrderSubgroup (⊤ : Subgroup G)) V)
  image_LS : autOn (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) V =
    autOn (oddOrderSubgroup (⊤ : Subgroup G)) V
  pCore_le : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G)) ≤ baum R
  sylow : IsSylowTwoOf (baum R) (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)
  normal : (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R).Normal
  E_split : omegaOneCenterOf (thompsonJ R) =
    (omegaOneCenterOf (thompsonJ R) ⊓
        Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)) ⊔
      (V ⊓ Subgroup.centralizer (thompsonJ R : Set G))
  A_le_E : V ⊓ Subgroup.centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R)
  V_span : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) l) = V
  closure : (⨆ l ∈ oddOrderSubgroup (⊤ : Subgroup G),
      Campbell.cj (omegaOneCenterOf (thompsonJ R)) l) =
    ⁅V, oddOrderSubgroup (⊤ : Subgroup G)⁆ ⊔
      (omegaOneCenterOf (thompsonJ R) ⊓
        Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G))
  J_C : ⁅thompsonJ R, V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)⁆ = ⊥

end Defs

section Tools

variable {G : Type} [Group G]

theorem map_inf_centralizer_map' {H : Type} [Group H] (f : H →* G) (hf : Function.Injective f)
    {U L : Subgroup H} :
    U.map f ⊓ Subgroup.centralizer ((L.map f : Subgroup G) : Set G) =
      (U ⊓ Subgroup.centralizer (L : Set H)).map f := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    refine ⟨u, ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (f l) ⟨l, hl, rfl⟩
    apply hf
    simpa using this
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    refine ⟨⟨u, hu, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_iff.mp hc l hl)

theorem mem_omegaOneCenter_of_centralizes {R V : Subgroup G} [Finite G] (hVR : V ≤ R)
    (hVe : IsElemAbelian 2 V) {v : G} (hv : v ∈ V)
    (hvJ : ∀ j ∈ thompsonJ R, j * v = v * j) : v ∈ omegaOneCenterOf (thompsonJ R) := by
  have hvA : ∀ A : Subgroup G, IsMaxElemAbelian R A → v ∈ A := by
    intro A hA
    rw [eq_omegaOneOf_centralizer hA]
    refine Subgroup.subset_closure ⟨⟨hVR hv, ?_⟩, hVe.2 v hv⟩
    exact Subgroup.mem_centralizer_iff.2 fun a ha => hvJ a (B6.le_thompsonJ hA ha)
  rw [(omegaOne_centralizer_thompsonJ R).2]
  simp only [Subgroup.mem_iInf]
  exact fun A hA => hvA A hA

end Tools

section Main

variable {G : Type} [Group G] [Finite G]

theorem baumann_apply
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc) {l : G}
    (hlL : l ∈ oddOrderSubgroup (⊤ : Subgroup G))
    (hlgen : autOn (oddOrderSubgroup (⊤ : Subgroup G)) V ≤
      autOn (thompsonJ R ⊔ CFSG.conjugate (thompsonJ R) l) V)
    (hlcodim : (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)).relIndex V *
        (V ⊓ Subgroup.centralizer ((CFSG.conjugate (thompsonJ R) l : Subgroup G) :
          Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)).relIndex V) :
    pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G)) ≤ baum R ∧
      omegaOneCenterOf (thompsonJ R) =
        (omegaOneCenterOf (thompsonJ R) ⊓
            Subgroup.centralizer (oddOrderSubgroup (⊤ : Subgroup G) : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ∧
      (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.centralizer (V : Set G)) →
        IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
            ((oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) ∧
          (IsSylowTwoOf (autOn (baum R) V)
              (autOn (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) V) →
            IsSylowTwoOf (baum R) (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbridge := even_SL2_original_bridge hS hLc
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have := hVn
  obtain ⟨-, -, -, -, hVR⟩ := even_SL2_setting_basic hS
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set J := thompsonJ R with hJ
  have hJR : J ≤ R := B6.thompsonJ_le R
  have hRn : ¬ R.Normal := fun h => hS.not_normal (h.subgroupOf _)
  have hVH : ¬ (⊤ : Subgroup G) ≤ Subgroup.centralizer (V : Set G) := fun hc =>
    hS.thompson_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hJR.trans (le_top.trans hc)))
  obtain ⟨hHfr1, hHfr2, hHfr3, hHfr4, hHfr5, hHfr6, hHfr7⟩ :=
    minimal_parabolic_reduced_module_Frattini_kernel_production hS.sylow hRn hS.max.1 hS.max.2.1
      hS.max.2.2 hred hVH
  have hV' : CFSG.IsElementaryAbelian 2 V :=
    BlueprintB2.isElementaryAbelian_iff.mpr (isElemAbelian_iff.mp hVe)
  have hPQ : CFSG.inSubgroup (CFSG.pCore 2) L ≤ R ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hHfr2]
    exact (le_of_eq hHfr5).trans inf_le_right
  have hLQ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
    intro x _
    rw [hHfr2]
    have hn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
    exact (Subgroup.normalizer_eq_top_iff.mpr hn) ▸ Subgroup.mem_top x
  have hLclos : L = Subgroup.closure {g : G | Nat.Coprime (orderOf g) 2} := by
    rw [hL]
    unfold oddOrderSubgroup
    congr 1
    ext g
    simp [Nat.coprime_two_right]
  have hineq : ∀ A ∈ elemThompsonFamily R 2,
      (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A ≤
        ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R) := by
    intro A hA
    have hA' : IsMaxElemAbelian R (A.map R.subtype) :=
      BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.mpr
        ⟨BlueprintB2.map_subtype_le_self A, by rwa [BlueprintB2.subgroupOf_map_subtype_self]⟩
    have hweight := hbridge.weight _ hA'
    have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer ((A.map R.subtype : Subgroup G) : Set G)) :=
      Nat.card_pos
    have hmul := Subgroup.relIndex_mul_card
      (V ⊓ Subgroup.centralizer ((A.map R.subtype : Subgroup G) : Set G)) V
    rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer
      ((A.map R.subtype : Subgroup G) : Set G) ≤ V)] at hmul
    have hmain : (A.map R.subtype ⊓ Subgroup.centralizer (V : Set G)).relIndex (A.map R.subtype) =
        (V ⊓ Subgroup.centralizer ((A.map R.subtype : Subgroup G) : Set G)).relIndex V :=
      Nat.eq_of_mul_eq_mul_right hpos (hweight.symm.trans hmul.symm)
    have hVmap : (V.subgroupOf R).map R.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVR
    have e1 : (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A =
        (A.map R.subtype ⊓ Subgroup.centralizer (V : Set G)).relIndex (A.map R.subtype) := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := R.subtype) _ _ R.subtype_injective,
        ← map_inf_centralizer_map' R.subtype R.subtype_injective, hVmap]
    have e2 : ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R) =
        (V ⊓ Subgroup.centralizer ((A.map R.subtype : Subgroup G) : Set G)).relIndex V := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := R.subtype) _ _ R.subtype_injective,
        ← map_inf_centralizer_map' R.subtype R.subtype_injective, hVmap]
    rw [e1, e2]
    exact le_of_eq hmain
  have hXL : ∀ i : Fin 2, ∃ l' ∈ L,
      conjugate (![J, conjugate J l] i) l' ≤ R := by
    intro i
    fin_cases i
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      show cj J 1 ≤ R
      rw [cj_one]
      exact hJR
    · refine ⟨l⁻¹, Subgroup.inv_mem _ hlL, ?_⟩
      show cj (cj J l) l⁻¹ ≤ R
      rw [cj_inv_cj]
      exact hJR
  have hJe : elemThompsonIn 2 R = J := Wreath.elemThompsonIn_two_eq R
  have hXJ : ∀ i : Fin 2, (elemThompson (![J, conjugate J l] i) 2).map
      (![J, conjugate J l] i).subtype = ![J, conjugate J l] i := by
    intro i
    fin_cases i
    · show elemThompsonIn 2 J = J
      rw [← hJe]
      exact elemThompsonIn_eq_of_le 2 le_rfl (hJe ▸ hJR)
    · show elemThompsonIn 2 (cj J l) = cj J l
      rw [elemThompsonIn_cj, ← hJe]
      congr 1
      exact elemThompsonIn_eq_of_le 2 le_rfl (hJe ▸ hJR)
  have hJJ : CFSG.pRank 2 ↥J = CFSG.pRank 2 ↥R := by
    apply le_antisymm (pRank_mono hJR)
    obtain ⟨A, hA⟩ := BlueprintB2.elemThompsonFamily_nonempty R 2
    have hA' : A.map R.subtype ∈ elemFamilyIn 2 R := ⟨A, hA, rfl⟩
    obtain ⟨-, hel, hcard⟩ := mem_elemFamilyIn.mp hA'
    have hAJ : A.map R.subtype ≤ J := hJe ▸ le_elemThompsonIn hA'
    have h1 := card_le_pow_pRank_of_le (p := 2) hAJ hel
    rw [hcard] at h1
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h1
  have hXe : ∀ i : Fin 2, CFSG.pRank 2 ↥(![J, conjugate J l] i) = CFSG.pRank 2 ↥R := by
    intro i
    fin_cases i
    · exact hJJ
    · show CFSG.pRank 2 ↥(cj J l) = CFSG.pRank 2 ↥R
      rw [pRank_cj, hJJ]
  have hI : J ⊔ conjugate J l = ⨆ i : Fin 2, ![J, conjugate J l] i := by
    apply le_antisymm
    · exact sup_le (le_iSup (fun i : Fin 2 => ![J, conjugate J l] i) 0)
        (le_iSup (fun i : Fin 2 => ![J, conjugate J l] i) 1)
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
  have hρ : L.map (MulAut.conjNormal (H := V)) ≤
      (J ⊔ conjugate J l).map (MulAut.conjNormal (H := V)) := by
    rw [← autOn_eq_map_conjNormal, ← autOn_eq_map_conjNormal]
    exact hlgen
  have hcodim : ∏ i : Fin 2,
      (V ⊓ Subgroup.centralizer ((![J, conjugate J l] i : Subgroup G) : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := by
    rw [Fin.prod_univ_two]
    exact hlcodim
  have hJdef : J = (elemThompson R 2).map R.subtype :=
    (CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ R).symm
  have key := Baumann_central_splitting_and_Sylow_transfer 2 V hV' R hS.sylow.2.1 hVR L hLclos
    hHfr1 (R ⊓ Subgroup.centralizer (V : Set G)) (CFSG.inSubgroup (CFSG.pCore 2) L) rfl rfl hPQ hLQ
    (hHfr7 _ hHfr4) hineq 2 (by norm_num) ![J, conjugate J l] hXL hXJ hXe
    (J ⊔ conjugate J l) hI hρ J hJdef le_sup_left hcodim (elemBaumannIn 2 R) (elemCenterIn 2 R)
    rfl rfl
  obtain ⟨hPS, hEsplit, hSyl⟩ := key
  have hSb : elemBaumannIn 2 R = baum R := elemBaumann_map_subtype_eq_baum R
  have hEb : elemCenterIn 2 R = omegaOneCenterOf J :=
    elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf R
  have hPb : CFSG.inSubgroup (CFSG.pCore 2) L = pCoreOf 2 L := map_pCore_eq_pCoreOf L
  rw [hPb, hSb] at hPS
  rw [hEb] at hEsplit
  rw [hSb] at hSyl
  refine ⟨hPS, hEsplit, fun hQ => ⟨(hSyl hQ).1, fun h => (hSyl hQ).2 ?_⟩⟩
  rw [← autOn_eq_map_conjNormal, ← autOn_eq_map_conjNormal]
  exact h

theorem even_SL2_natural_baumann
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hle : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    NaturalBaumannOutput R V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata := natural_original_data hS hLc hle
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have := hVn
  have hnorm : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    hX (Subgroup.mem_top x)
  obtain ⟨-, -, -, -, hVR⟩ := even_SL2_setting_basic hS
  obtain ⟨l, hlL, hlgen, hlcodim⟩ := hdata.l_gen
  obtain ⟨hPS, hEsplit, hSyl⟩ := baumann_apply hS hLc hlL hlgen hlcodim
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set J := thompsonJ R with hJ
  have himgLS : autOn (L ⊔ baum R) V = autOn L V := by
    rw [autOn_eq_map_conjNormal, Subgroup.map_sup, ← autOn_eq_map_conjNormal,
      ← autOn_eq_map_conjNormal, hdata.baum_eq]
    exact sup_eq_left.2 hle
  have hJC : ∀ j ∈ J, ∀ c ∈ V ⊓ Subgroup.centralizer (L : Set G), j * c = c * j := by
    intro j hj c hc
    have hjn : j ∈ Subgroup.normalizer (V : Set G) := hnorm J hj
    have hφ : conjAct V ⟨j, hjn⟩ ∈ autOn L V := hle (mem_autOn_iff.2 ⟨⟨j, hjn⟩, hj, rfl⟩)
    obtain ⟨l', hl', hl'eq⟩ := mem_autOn_iff.1 hφ
    have h1 : ((conjAct V l' ⟨c, hc.1⟩ : ↥V) : G) = ((conjAct V ⟨j, hjn⟩ ⟨c, hc.1⟩ : ↥V) : G) := by
      rw [hl'eq]
    rw [coe_conjAct_apply, coe_conjAct_apply] at h1
    have h2 : (l' : G) * c * (l' : G)⁻¹ = c := by
      have h3 := Subgroup.mem_centralizer_iff.1 hc.2 l' hl'
      rw [h3, mul_inv_cancel_right]
    have h4 : j * c * j⁻¹ = c := by
      have : (j : G) * c * (j : G)⁻¹ = (l' : G) * c * (l' : G)⁻¹ := h1.symm
      rw [this, h2]
    exact (mul_inv_eq_iff_eq_mul.1 h4)
  have hCA : V ⊓ Subgroup.centralizer (L : Set G) ≤ V ⊓ Subgroup.centralizer (J : Set G) :=
    fun c hc => ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun j hj => hJC j hj c hc⟩
  have hAE : V ⊓ Subgroup.centralizer (J : Set G) ≤ omegaOneCenterOf J := fun v hv =>
    mem_omegaOneCenter_of_centralizes hVR hVe hv.1 fun j hj =>
      Subgroup.mem_centralizer_iff.1 hv.2 j hj
  have hQ : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      (Subgroup.centralizer (V : Set G)) := by
    refine isSylowTwoOf_of_isSylowOf ?_
    exact (isSylowOf_two_of hS.sylow).inf_of_le_normalizer le_top
      (by rw [Subgroup.normalizer_eq_top])
  have hmapS : IsSylowTwoOf (autOn (baum R) V) (autOn (L ⊔ baum R) V) := by
    rw [himgLS, hdata.baum_eq]
    exact hdata.image_sylow
  have hsylow : IsSylowTwoOf (baum R) (L ⊔ baum R) := (hSyl hQ).2 hmapS
  have hnormLS : (L ⊔ baum R).Normal := normal_L_sup_baum hS
  have hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤
      omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) :=
    fun c hc => ⟨hAE (hCA hc), hc.2⟩
  have hVle : V ≤ ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) := by
    calc V = ⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) := hdata.V_split
      _ ≤ ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) :=
        sup_le_sup_left hCU _
  have hcommV : ⁅V, L⁆ ≤ V := Subgroup.commutator_le.2 fun v hv l' _ => by
    have h1 : (l' : G) * v⁻¹ * l'⁻¹ ∈ V := hVn.conj_mem _ (V.inv_mem hv) l'
    have h2 := V.mul_mem hv h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hClosure : (⨆ l' ∈ L, cj (omegaOneCenterOf J) l') =
      ⁅V, L⁆ ⊔ (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) := by
    apply le_antisymm
    · refine iSup₂_le fun l' hl' => ?_
      have hcjE : cj (omegaOneCenterOf J) l' =
          cj (omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G)) l' ⊔
            cj (V ⊓ Subgroup.centralizer (J : Set G)) l' := by
        rw [← cj_sup, ← hEsplit]
      rw [hcjE]
      refine sup_le ?_ ?_
      · intro y hy
        have hy' : (l' : G) * y * (l' : G)⁻¹ ∈
            omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) := mem_cj.1 hy
        have h3 := Subgroup.mem_centralizer_iff.1 hy'.2 l' hl'
        have h4 : (l' : G) * y * (l' : G)⁻¹ = y := by
          have h5 : (l' : G) * ((l' : G) * y * (l' : G)⁻¹) =
              (l' : G) * y * (l' : G)⁻¹ * l' := h3
          calc (l' : G) * y * (l' : G)⁻¹
              = (l' : G)⁻¹ * ((l' : G) * ((l' : G) * y * (l' : G)⁻¹)) := by group
            _ = (l' : G)⁻¹ * ((l' : G) * y * (l' : G)⁻¹ * l') := by rw [h5]
            _ = y := by group
        have h6 : y ∈ omegaOneCenterOf J ⊓ Subgroup.centralizer (L : Set G) := by
          have := hy'
          rwa [h4] at this
        exact Subgroup.mem_sup_right h6
      · intro y hy
        have hy' : (l' : G) * y * (l' : G)⁻¹ ∈ V ⊓ Subgroup.centralizer (J : Set G) :=
          mem_cj.1 hy
        have hyV : (l' : G) * y * (l' : G)⁻¹ ∈ V := hy'.1
        have h2 := hVn.conj_mem _ hyV (l' : G)⁻¹
        have h6 : y ∈ V := by simpa [mul_assoc] using h2
        exact hVle h6
    · refine sup_le ?_ ?_
      · calc ⁅V, L⁆ ≤ V := hcommV
          _ = ⨆ l' ∈ L, cj (V ⊓ Subgroup.centralizer (J : Set G)) l' := hdata.V_span.symm
          _ ≤ ⨆ l' ∈ L, cj (omegaOneCenterOf J) l' :=
            iSup₂_mono fun l' _ => Subgroup.map_mono hAE
      · refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
        rw [cj_one]
        exact inf_le_left
  refine ⟨hdata.baum_eq, ?_, himgLS, hPS, hsylow, hnormLS, hEsplit, hAE, hdata.V_span, hClosure, ?_⟩
  · rw [hdata.baum_eq]
    exact hdata.image_sylow
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun j hj =>
      Subgroup.mem_centralizer_iff.2 fun c hc => (hJC j hj c hc).symm

end Main

end CFSG.QuasithinUnique.Setup.Lift
