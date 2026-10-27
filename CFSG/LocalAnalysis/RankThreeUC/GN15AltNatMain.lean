module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockW
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatKey
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModPow
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartOne.MB3.FixedPoint

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (altHeart_fixed_eq_zero)
open Equiv
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem exists_altBaumSection_of_setup_ker {V₀ K : Subgroup X} {n : ℕ} (hn : 9 ≤ n) (hodd : Odd n)
    {Φ : ↥K →* alternatingGroup (Fin n)} (hS : AltBaumSetup V₀ K Φ)
    {π : ↥⁅V₀, K⁆ →* Multiplicative (altHeart n)} (hπs : Function.Surjective π)
    (hπk : ∀ u, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : ↥K) (u u' : ↥⁅V₀, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Perm (Fin n)) x) : altHeart n)) :
    ∃ π' : ↥⁅V₀, K⁆ →* Multiplicative (evenWeight n),
      AltBaumSection V₀ K Φ π' ∧ ∀ u, π' u = 1 ↔ π u = 1 := by
  classical
  let ε : evenWeight n ≃+ altHeart n :=
    AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes n))
      ⟨altHeart_mk_injective hodd, QuotientAddGroup.mk_surjective⟩
  let ε' : Multiplicative (altHeart n) ≃* Multiplicative (evenWeight n) :=
    AddEquiv.toMultiplicative ε.symm
  let π'' : ↥⁅V₀, K⁆ →* Multiplicative (evenWeight n) := ε'.toMonoidHom.comp π
  refine ⟨π'', ⟨ε'.surjective.comp hπs, fun u => ?_, fun l u u' h => ?_⟩, fun u => ?_⟩
  · rw [show π'' u = ε' (π u) from rfl, MulEquiv.map_eq_one_iff]
    refine ⟨fun h1 => hπk u h1, fun hfix => ?_⟩
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    have hfixv : ∀ σ ∈ alternatingGroup (Fin n),
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x := by
      intro σ hσ
      obtain ⟨k, hk⟩ := hS.surj ⟨σ, hσ⟩
      have h2 : (Φ k : Perm (Fin n)) = σ := congrArg Subtype.val hk
      have h3 := hπi k u u (hfix k k.2).symm x hx.symm
      rw [h2] at h3
      rw [← h3, hx]
    have h0 := altHeart_fixed_eq_zero (by omega) x hfixv
    rw [hx] at h0
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  · have hx : Multiplicative.toAdd (π u) =
        (QuotientAddGroup.mk (Multiplicative.toAdd (π'' u)) : altHeart n) := by
      show _ = ε (ε.symm (Multiplicative.toAdd (π u)))
      rw [ε.apply_symm_apply]
    have h1 := hπi l u u' h _ hx
    show ε.symm (Multiplicative.toAdd (π u')) = _
    rw [h1]
    exact ε.symm_apply_apply _
  · show ε' (π u) = 1 ↔ π u = 1
    exact MulEquiv.map_eq_one_iff _

theorem exists_naturalOnLayer_of_gf2EightFive (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n)
    (e : ↥L ≃* alternatingGroup (Fin n)) :
    GNNaturalOnLayer T L n := by
  classical
  obtain ⟨A, hAmax, hLA, hAN⟩ := exists_maxElemAbelian_comm hX hL hJ
  let mk : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
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
      exact (offender_core hV (gnV_le T hX) hTN hAmax hB).1
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
  have hT1 : IsPGroup 2 T1 := (hX.sylow.2.1.map mk).map ι
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hL.2.1 (isSylowTwoOf_gnImg_top hX)
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
  have hinv : ∀ h ∈ H, ∀ w ∈ fixV (pCoreOf 2 H), h w ∈ fixV (pCoreOf 2 H) :=
    B1Red.fixV_pCoreOf_inv
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
    have h1 : (((resHom (fixV (pCoreOf 2 H)) ⟨ι (mk k), hgs⟩ v * v⁻¹ :
        ↥(fixV (pCoreOf 2 H))) : IntMod (gnV T) hV)) = ι (mk k) (w0⁻¹) * w0⁻¹⁻¹ := rfl
    rw [h1, inv_inv, IntMod.val_mul, IntMod.val_comm (ι (mk k) (w0⁻¹)) w0, hval, IntMod.val_inv,
      commutatorElement_def]
    group
  let ψ : ↥⁅W, L.comap mk⁆ →* ↥(natU H) :=
    ((Subgroup.equivMapOfInjective (natU H) (valHom' hV)
      (valHom'_injective hV)).symm).toMonoidHom.comp (Subgroup.inclusion hle)
  have hψ : ∀ u : ↥⁅W, L.comap mk⁆, (((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val = (u : X) := by
    intro u
    have := congrArg Subtype.val
      ((Subgroup.equivMapOfInjective (natU H) (valHom' hV) (valHom'_injective hV)).apply_symm_apply
        (Subgroup.inclusion hle u))
    exact this
  let g : ↥L →* alternatingGroup (Fin n) :=
    α.comp (Subgroup.equivMapOfInjective L ι hι).toMonoidHom
  have hg : Function.Surjective g := hα.comp (Subgroup.equivMapOfInjective L ι hι).surjective

  have hA1sq : ∀ a ∈ A1, a * a = 1 := fun a ha => by
    simpa [pow_two] using hoff.2.2.1.2 a ha
  have hSet : AltNatSetup H L1 A1 :=
    altNatSetup hV2 (by omega : 5 ≤ n) e1 hLH hLn le_rfl hAH hA1sq
  have hLA1 : ⁅L1, A1⁆ = L1 := by
    have := Subgroup.map_commutator L (A.map mk) ι
    rw [hLA] at this
    exact this.symm
  have hk1 : ∀ u, (π.comp ψ) u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
      (k : X) * u * (k : X)⁻¹ = u := by
    intro u hu k hk
    have h1 := hπk (ψ u) hu (ι (mk k)) ⟨mk k, hk, rfl⟩
    have h2 := congrArg IntMod.val h1
    rwa [hval, hψ] at h2
  have hi1 : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd ((π.comp ψ) u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd ((π.comp ψ) u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n) := by
    intro l hl u u' hu' x hx
    refine hπi ⟨ι (mk l), ⟨mk l, hl, rfl⟩⟩ (ψ u) (ψ u') ?_ x hx
    apply IntMod.val_injective
    show ((ψ u' : ↥(natU H)) : IntMod (gnV T) hV).val =
      (ι (mk l) ((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val
    rw [hval, hψ, hψ, hu']
  have hne : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≠ ⊥ := by
    intro hbot
    have hLW : ∀ l ∈ L1, ∀ w ∈ fixV (pCoreOf 2 H), l w = w := by
      rintro _ ⟨l, hl, rfl⟩ w hw
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective l
      have hwW : (w : IntMod (gnV T) hV).val ∈ W := ⟨w, hw, rfl⟩
      have h1 : ⁅(w : IntMod (gnV T) hV).val, k⁆ ∈ ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ :=
        Subgroup.commutator_mem_commutator hwW hl
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      apply IntMod.val_injective
      rw [show ι (QuotientGroup.mk k) = ι (mk k) from rfl, hval]
      calc k * (w : IntMod (gnV T) hV).val * k⁻¹ = (w : IntMod (gnV T) hV).val * k * k⁻¹ := by
            rw [h1]
        _ = (w : IntMod (gnV T) hV).val := by group
    have hLP : L1 ≤ pCoreOf 2 H := fun l hl => by
      have : l ∈ H ⊓ centSub (fixV (pCoreOf 2 H)) := ⟨hLH hl, fun w hw => hLW l hl w hw⟩
      rwa [hSet.ker] at this
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    exact alt_not_two_group (by omega)
      ((hP2.to_le hLP).of_surjective e1.toMonoidHom e1.surjective)
  have hgi : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  have hΦs : Function.Surjective (liftToAlt L g) := liftToAlt_surjective L hg
  have hΦk := liftToAlt_eq_one_iff L hgi
  have hVC : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  have hVab := isElemAbelian_gnV T hX
  have hSW : AltBaumSetup W (L.comap (QuotientGroup.mk' (gnC T))) (liftToAlt L g) :=
    { comm := fun v hv w hw =>
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hWV hv⟩ ⟨w, hWV hw⟩)
      sq := fun v hv => by have := hVab.2 v (hWV hv); simpa [pow_two] using this
      norm := hWK
      surj := hΦs
      ker := fun k hk v hv => hVC _ ((hΦk k).1 hk) v (hWV hv) }
  have hi2 : ∀ (l : ↥(L.comap (QuotientGroup.mk' (gnC T))))
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd ((π.comp ψ) u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd ((π.comp ψ) u') = (QuotientAddGroup.mk
          (evenWeightPerm (liftToAlt L g l : Perm (Fin n)) x) : altHeart n) :=
    fun l u u' h x hx => hi1 (l : X) l.2 u u' h x hx
  have hπs : Function.Surjective (π.comp ψ) :=
    surjective_of_ne_bot (by omega) hSW hk1 hi2 hne
  obtain ⟨π', hπ', hπ'k⟩ := exists_altBaumSection_of_setup_ker hn9 hodd hSW hπs hk1 hi2
  have hinjX : ∀ u, (π.comp ψ) u = 1 → u = 1 := fun u hu =>
    (hπ'.injective hSW hodd hn9) (((hπ'k u).2 hu).trans (map_one π').symm)
  have hcommX : ∀ c : IntMod (gnV T) hV, c ∈ CFSG.Quasithin.commSub (fixV (pCoreOf 2 H)) L1 →
      c.val ∈ ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ := by
    intro c hc
    unfold CFSG.Quasithin.commSub at hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, ⟨l, hl, rfl⟩, w, hw, rfl⟩ := hc
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective l
      have hwW : (w : IntMod (gnV T) hV).val ∈ W := ⟨w, hw, rfl⟩
      have h1 : ⁅k, (w : IntMod (gnV T) hV).val⁆ ∈
          ⁅L.comap (QuotientGroup.mk' (gnC T)), W⁆ :=
        Subgroup.commutator_mem_commutator hl hwW
      rw [Subgroup.commutator_comm] at h1
      have e : (ι (QuotientGroup.mk k) w * w⁻¹).val = ⁅k, (w : IntMod (gnV T) hV).val⁆ := by
        rw [IntMod.val_mul, show ι (QuotientGroup.mk k) = ι (mk k) from rfl, hval, IntMod.val_inv,
          commutatorElement_def]
      rw [e]; exact h1
    | one => rw [IntMod.val_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [IntMod.val_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [IntMod.val_inv]; exact Subgroup.inv_mem _ ha
  have hinjV : ∀ u : ↥(natU H), (u : IntMod (gnV T) hV) ∈
      CFSG.Quasithin.commSub (fixV (pCoreOf 2 H)) L1 → π u = 1 → u = 1 := by
    intro u hu hπu
    have hx := hcommX u hu
    let x' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ := ⟨(u : IntMod (gnV T) hV).val, hx⟩
    have hψx : ψ x' = u := by
      apply Subtype.ext
      apply IntMod.val_injective
      exact hψ x'
    have h1 : (π.comp ψ) x' = 1 := by
      rw [MonoidHom.comp_apply, hψx]; exact hπu
    have h2 : x' = 1 := hinjX x' h1
    have h3 : (u : IntMod (gnV T) hV).val = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    apply IntMod.val_injective
    rw [h3]
    rfl
  have hcomm := altNat_key hV2 hodd hn9 e1 hLH hLn le_rfl hoff hLA1 α hα π hπk hπi hinjV
  have hVK : ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    let v0 : IntMod (gnV T) hV := IntMod.mk hV ⟨v, hv⟩
    have hmemc : (ι (mk k)) v0⁻¹ * v0 ∈ commV L1 :=
      Subgroup.subset_closure ⟨ι (mk k), ⟨mk k, hk, rfl⟩, v0⁻¹, by rw [inv_inv]⟩
    refine ⟨_, hcomm hmemc, ?_⟩
    show ((ι (mk k)) v0⁻¹ * v0).val = ⁅v, k⁆
    rw [IntMod.val_mul, IntMod.val_comm (ι (mk k) v0⁻¹) v0, hval, IntMod.val_inv,
      commutatorElement_def]
    show (v0.val) * (k * (v0.val)⁻¹ * k⁻¹) = _
    show v * (k * v⁻¹ * k⁻¹) = _
    group
  have hV0 := altBaumSetup_gnV hX hΦs hΦk
  have hperf := altBaum_commutator_le_commutator_commutator hV0.comm hV0.norm (liftToAlt L g) hΦs
    (by omega : 5 ≤ n) hV0.ker
  have hle2 : ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤
      ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ :=
    hperf.trans (Subgroup.commutator_mono hVK le_rfl)
  have hge : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤
      ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ := Subgroup.commutator_mono hWV le_rfl
  exact ⟨g, W, π.comp ψ, hg, hWV, hZW, hWK, hk1, hi1, le_antisymm hle2 hge⟩

theorem gnLayerHolds_of_gf2EightFive (hGF : GF2EightFive) : GNLayerHolds := by
  intro X _ _ T hX L hL hJ n hn9 hodd he
  obtain ⟨e⟩ := he
  exact exists_naturalOnLayer_of_gf2EightFive hGF hX hL hJ hn9 hodd e

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
