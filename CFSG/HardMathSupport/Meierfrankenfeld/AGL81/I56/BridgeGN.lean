module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.NaturalOn
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeSylow

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open scoped commutatorElement

section GN

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_maxElemAbelian_comm (hGN : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    ∃ A : Subgroup X, IsMaxElemAbelian T A ∧ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L ∧
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hC : CFSG.IsComponent L := (isComponent_iff_open L).2 hL
  have hQ : CFSG.IsQuasisimple L := hC.1
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  have hnorm : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := fun A hA =>
    (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hGN hA)).trans
      (bestOffenderSub_le_normalizer_component (gnRep hV) hinj hC)
  have key : ∃ A : Subgroup X, IsMaxElemAbelian T A ∧ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = L := by
    by_contra hno
    push Not at hno
    have hcen : ∀ A : Subgroup X, IsMaxElemAbelian T A →
        A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      intro A hA
      by_cases hb : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = ⊥
      · intro a ha l hl
        have : ⁅l, a⁆ ∈ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ := Subgroup.commutator_mem_commutator hl ha
        rw [hb, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      · exact absurd (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commutator_eq_of_ne_bot hQ
          (hnorm A hA) hb) (hno A hA)
    have hJle : gnImg T (thompsonJ T) ≤ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
      unfold gnImg thompsonJ
      rw [Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hA => hcen A hA
    apply hLbot
    rw [← hJ, eq_bot_iff, Subgroup.commutator_le]
    intro l hl j hj
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 (hJle hj) l hl)
  obtain ⟨A, hAmax, hLA⟩ := key
  exact ⟨A, hAmax, hLA, hnorm A hAmax⟩


@[expose] def AltOddCentreTrivial : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ¬ 2 ∣ Nat.card (Subgroup.center Q) → ∀ n : ℕ, 9 ≤ n →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* alternatingGroup (Fin n)) → Subgroup.center Q = ⊥

theorem not_two_dvd_card_center (hGN : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) : ¬ 2 ∣ Nat.card (Subgroup.center ↥L) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite ↥(Subgroup.center ↥L)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center ↥L)) 2
    (by rw [← Nat.card_eq_fintype_card]; exact h2)
  set z' : X ⧸ gnC T := (((z : ↥L)) : X ⧸ gnC T) with hz'
  have hord : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  set K : Subgroup (X ⧸ gnC T) := Subgroup.zpowers z' with hK
  have hK2 : IsPGroup 2 ↥K := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hK, Nat.card_zpowers, hord]; norm_num
  have hKL : K ≤ L := by
    rw [hK, Subgroup.zpowers_le]; exact (z : ↥L).2
  have hcen : ∀ k ∈ K, ∀ l ∈ L, l * k * l⁻¹ = k := by
    intro k hk l hl
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hzc : (⟨l, hl⟩ : ↥L) * (z : ↥L) = (z : ↥L) * ⟨l, hl⟩ :=
      (Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩)
    have : l * z' = z' * l := congrArg Subtype.val hzc
    have h3 : l * z' * l⁻¹ = z' := by rw [this]; group
    calc l * z' ^ m * l⁻¹ = (l * z' * l⁻¹) ^ m := conj_zpow.symm
      _ = z' ^ m := by rw [h3]
  have hnormal : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff hKL).2 fun k l hk hl => by rw [hcen k hk l hl]; exact hk
  have hsub : IsSubnormal K ⊤ := IsSubnormal.step hKL hnormal hL.2.1
  have h1 : K ≤ CFSG.Open.pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hK2
  have h2' := CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsub
  have h3 : CFSG.Open.pCoreOf 2 (⊤ : Subgroup (X ⧸ gnC T)) = ⊥ := by
    rw [CFSG.Quasithin.pCoreOf_top, CFSG.pCore_eq_iSup]
    refine eq_bot_iff.2 (iSup_le fun N => iSup_le fun hN => iSup_le fun hN2 => ?_)
    have : N ≤ CFSG.pCore 2 (X ⧸ gnC T) := le_sSup ⟨hN, hN2⟩
    rw [FF531.pCore_two_gnQuot hGN] at this
    exact this
  have hz1 : z' ∈ K := Subgroup.mem_zpowers z'
  have := (h1.trans (h2'.trans h3.le)) hz1
  rw [Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hord
  omega


omit [Finite X] in
@[expose] def valHom' (hV : IsElemAbelian 2 (gnV T)) : IntMod (gnV T) hV →* X where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

omit [Finite X] in
theorem valHom'_injective (hV : IsElemAbelian 2 (gnV T)) : Function.Injective (valHom' hV) :=
  IntMod.val_injective

theorem isSylowTwoOf_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {S M : Subgroup A} (h : IsSylowTwoOf S M) :
    IsSylowTwoOf (S.map f) (M.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  have := Subgroup.relIndex_map_map_of_injective S M hf
  intro hd
  apply h.2.2
  have h' : (S.map f).relIndex (M.map f) = S.relIndex M := this
  have hd' : 2 ∣ (S.map f).relIndex (M.map f) := hd
  rw [h'] at hd'
  exact hd'

theorem agl81I56_of_gf2EightFive (hGF : GF2EightFive) (hZ : AltOddCentreTrivial) : AGL81I56 := by
  classical
  intro X _ _ T hGN L hL hJ n hn hne
  have hn9 : 9 ≤ n := hn
  have hQ : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hZ1 : Subgroup.center ↥L = ⊥ := hZ ↥L hQ (not_two_dvd_card_center hGN hL) n hn9 hne
  let e : ↥L ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans hne.some
  obtain ⟨A, hAmax, hLA, hAN⟩ := exists_maxElemAbelian_comm hGN hL hJ
  let mk : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)
  have hV : IsElemAbelian 2 (gnV T) := I542.isElemAbelian_gnV T hGN
  let ι : X ⧸ gnC T →* MulAut (IntMod (gnV T) hV) := gnIota hV
  have hι : Function.Injective ι := gnIota_injective hV
  have hV2 : ∀ v : IntMod (gnV T) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  let L1 : Subgroup (MulAut (IntMod (gnV T) hV)) := L.map ι
  let A1 : Subgroup (MulAut (IntMod (gnV T) hV)) := (A.map mk).map ι
  let H : Subgroup (MulAut (IntMod (gnV T) hV)) := L1 ⊔ A1
  have hLH : L1 ≤ H := le_sup_left
  have hAH : A1 ≤ H := le_sup_right
  have hA1n : ∀ a ∈ A1, ∀ l ∈ L1, a * l * a⁻¹ ∈ L1 := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨l, hl, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hAN hq) l).mp hl
    exact ⟨_, this, by simp⟩
  have hA1N : A1 ≤ Subgroup.normalizer (L1 : Set _) := le_normalizer_of_conj hA1n
  have hHN : H ≤ Subgroup.normalizer (L1 : Set _) := sup_le Subgroup.le_normalizer hA1N
  have hLn : ∀ h ∈ H, ∀ l ∈ L1, h * l * h⁻¹ ∈ L1 :=
    fun h hh l hl => (Subgroup.mem_normalizer_iff.mp (hHN hh) l).mp hl
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup e
  have hLbot : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := hsimple.toNontrivial
    rw [h] at this
    obtain ⟨x, y, hxy⟩ := exists_pair_ne ↥(⊥ : Subgroup (X ⧸ gnC T))
    exact hxy (Subsingleton.elim x y)
  have hA1eq : A1 = autI hV A := map_mk_map_gnIota hV A
  have hTN : T ≤ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    fun g _ => mem_normalizer_gnV T g
  have hA1ne : A1 ≠ ⊥ := by
    intro h
    have h1 : A.map mk = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hι).1 h
    rw [h1, Subgroup.commutator_bot_right] at hLA
    exact hLbot hLA.symm
  have hoff : IsFFStarOffender H A1 := by
    refine ⟨hAH, hA1ne, ⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hxy : x * y = y * x :=
        congrArg Subtype.val (hAmax.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      show ι (mk x) * ι (mk y) = ι (mk y) * ι (mk x)
      simp only [← map_mul, hxy]
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [← map_pow, ← map_pow]
      show ι (mk (x ^ 2)) = 1
      rw [hAmax.2.1.2 x hx, map_one, map_one]
    · intro B hB
      rw [hA1eq] at hB ⊢
      exact (offender_core hV (gnV_le T hGN) hTN hAmax hB).1
  have hAL : ¬ ∀ a ∈ A1, ∀ l ∈ L1, a * l = l * a := by
    intro hc
    apply hLbot
    rw [← hLA, eq_bot_iff, Subgroup.commutator_le]
    intro l hl q hq
    rw [Subgroup.mem_bot]
    apply hι
    rw [map_commutatorElement, map_one]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (hc (ι q) ⟨q, hq, rfl⟩ (ι l) ⟨l, hl, rfl⟩).symm
  let e1 : ↥L1 ≃* alternatingGroup (Fin n) := (Subgroup.equivMapOfInjective L ι hι).symm.trans e
  obtain ⟨α, hα, π, hπk, hπi⟩ :=
    natural_on_fixV hGF hV2 hn9 e1 hLH hLn le_rfl hoff hAL
  let T1 : Subgroup (MulAut (IntMod (gnV T) hV)) := (gnImg T T).map ι
  have hAT1 : A1 ≤ T1 := Subgroup.map_mono (Subgroup.map_mono hAmax.1)
  have hT1 : IsPGroup 2 T1 := (hGN.sylow.2.1.map mk).map ι
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hL.2.1 (isSylowTwoOf_gnImg_top hGN)
  have hTL1 : IsSylowTwoOf (T1 ⊓ L1) L1 := by
    have := isSylowTwoOf_map ι hι hSyl
    rwa [Subgroup.map_inf _ _ _ hι] at this
  have hPT : pCoreOf 2 H ≤ T1 := pCoreOf_le_of_sylow_shape hLH hAH hA1N le_rfl hAT1 hT1 hTL1
  have hZV : omegaOneCenterOf T ≤ gnV T := fun z hz => Subgroup.subset_normalClosure hz
  have hZfix : ∀ z (hz : z ∈ omegaOneCenterOf T), ∀ q ∈ pCoreOf 2 H,
      q (IntMod.mk hV ⟨z, hZV hz⟩) = IntMod.mk hV ⟨z, hZV hz⟩ := by
    intro z hz q hq
    obtain ⟨q0, ⟨t, ht, rfl⟩, rfl⟩ := hPT hq
    apply IntMod.val_injective
    show (gnConj hV t (IntMod.mk hV ⟨z, hZV hz⟩)).val = z
    rw [gnConj_apply_val]
    exact comm_of_mem_gnImg ⟨t, ht, rfl⟩ hz
  have hHst : H ≤ stabSub (fixV (pCoreOf 2 H)) := B1Red.le_stabSub_fixV_pCoreOf H
  have hinv : ∀ h ∈ H, ∀ w ∈ fixV (pCoreOf 2 H), h w ∈ fixV (pCoreOf 2 H) := B1Red.fixV_pCoreOf_inv
  have hval : ∀ (k : X) (w : IntMod (gnV T) hV), (ι (mk k) w).val = k * w.val * k⁻¹ :=
    fun k w => gnConj_apply_val hV k w
  have hKH : ∀ k ∈ L.comap mk, ι (mk k) ∈ H := fun k hk => hLH ⟨mk k, hk, rfl⟩
  let W : Subgroup X := (fixV (pCoreOf 2 H)).map (valHom' hV)
  have hWV : W ≤ gnV T := by
    rintro _ ⟨w, -, rfl⟩
    exact w.val_mem
  have hZW : omegaOneCenterOf T ≤ W := fun z hz =>
    ⟨IntMod.mk hV ⟨z, hZV hz⟩, fun q hq => hZfix z hz q hq, rfl⟩
  have hWK : ∀ k ∈ L.comap mk, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    rintro k hk _ ⟨w0, hw0, rfl⟩
    exact ⟨ι (mk k) w0, hinv _ (hKH k hk) w0 hw0, hval k w0⟩
  have hle : ⁅W, L.comap mk⁆ ≤ (natU H).map (valHom' hV) := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨w0, hw0, rfl⟩ k hk
    have hg : ι (mk k) ∈ H := hKH k hk
    have hgs : ι (mk k) ∈ stabSub (fixV (pCoreOf 2 H)) := hHst hg
    have hx : resHom (fixV (pCoreOf 2 H)) ⟨ι (mk k), hgs⟩ ∈ autSub H (fixV (pCoreOf 2 H)) :=
      mem_autSub.2 ⟨⟨ι (mk k), hgs⟩, hg, rfl⟩
    let v : ↥(fixV (pCoreOf 2 H)) := ⟨w0⁻¹, (fixV (pCoreOf 2 H)).inv_mem hw0⟩
    have hc : resHom (fixV (pCoreOf 2 H)) ⟨ι (mk k), hgs⟩ v * v⁻¹ ∈
        commV (autSub H (fixV (pCoreOf 2 H))) :=
      Subgroup.subset_closure ⟨_, hx, v, rfl⟩
    refine ⟨_, ⟨_, hc, rfl⟩, ?_⟩
    show (((resHom (fixV (pCoreOf 2 H)) ⟨ι (mk k), hgs⟩ v * v⁻¹ : ↥(fixV (pCoreOf 2 H))) :
      IntMod (gnV T) hV)).val = ⁅(w0 : IntMod (gnV T) hV).val, k⁆
    have h1 : (((resHom (fixV (pCoreOf 2 H)) ⟨ι (mk k), hgs⟩ v * v⁻¹ : ↥(fixV (pCoreOf 2 H))) :
        IntMod (gnV T) hV)) = ι (mk k) (w0⁻¹) * w0⁻¹⁻¹ := rfl
    rw [h1, inv_inv, IntMod.val_mul, IntMod.val_comm (ι (mk k) (w0⁻¹)) w0, hval, IntMod.val_inv,
      commutatorElement_def]
    group
  let ψ : ↥⁅W, L.comap mk⁆ →* ↥(natU H) :=
    ((Subgroup.equivMapOfInjective (natU H) (valHom' hV) (valHom'_injective hV)).symm).toMonoidHom.comp
      (Subgroup.inclusion hle)
  have hψ : ∀ u : ↥⁅W, L.comap mk⁆, (((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val = (u : X) := by
    intro u
    have := congrArg Subtype.val
      ((Subgroup.equivMapOfInjective (natU H) (valHom' hV) (valHom'_injective hV)).apply_symm_apply
        (Subgroup.inclusion hle u))
    exact this
  let g : ↥L →* alternatingGroup (Fin n) :=
    α.comp (Subgroup.equivMapOfInjective L ι hι).toMonoidHom
  have hg : Function.Surjective g := hα.comp (Subgroup.equivMapOfInjective L ι hι).surjective
  refine not_isPSolvable_of_natural_on hGN hL hn9 g hg W hWV hZW hWK (π.comp ψ) ?_ ?_
  · intro u hu k hk
    have h1 := hπk (ψ u) hu (ι (mk k)) ⟨mk k, hk, rfl⟩
    have h2 := congrArg IntMod.val h1
    rwa [hval, hψ] at h2
  · intro l hl u u' hu' x hx
    refine hπi ⟨ι (mk l), ⟨mk l, hl, rfl⟩⟩ (ψ u) (ψ u') ?_ x hx
    apply IntMod.val_injective
    show ((ψ u' : ↥(natU H)) : IntMod (gnV T) hV).val = (ι (mk l) ((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val
    rw [hval, hψ, hψ, hu']

end GN

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
