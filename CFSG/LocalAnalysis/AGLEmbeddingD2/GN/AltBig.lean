module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltDefs
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.AltOddCentre
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.ChevThree

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open scoped commutatorElement

section Reduction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_naturalOn_of_gf2EightFive (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn9 : 9 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ (g : ↥L →* alternatingGroup (Fin n)) (W : Subgroup X)
      (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n)),
      Function.Surjective g ∧ W ≤ gnV T ∧ omegaOneCenterOf T ≤ W ∧
      (∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
      (∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
        (k : X) * u * (k : X)⁻¹ = u) ∧
      ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
        (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
        (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
          Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
          Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
            (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n) := by
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
  refine ⟨g, W, π.comp ψ, hg, hWV, hZW, hWK, ?_, ?_⟩
  · intro u hu k hk
    have h1 := hπk (ψ u) hu (ι (mk k)) ⟨mk k, hk, rfl⟩
    have h2 := congrArg IntMod.val h1
    rwa [hval, hψ] at h2
  · intro l hl u u' hu' x hx
    refine hπi ⟨ι (mk l), ⟨mk l, hl, rfl⟩⟩ (ψ u) (ψ u') ?_ x hx
    apply IntMod.val_injective
    show ((ψ u' : ↥(natU H)) : IntMod (gnV T) hV).val =
      (ι (mk l) ((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val
    rw [hval, hψ, hψ, hu']

theorem exists_alt_eight_of_naturalOn (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn9 : 9 ≤ n)
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (W : Subgroup X) (hWV : W ≤ gnV T) (hZW : omegaOneCenterOf T ≤ W)
    (hWK : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n))
    (hπk : ∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
      (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n)) :
    ∃ φ : alternatingGroup (Fin 8) →* alternatingGroup (Fin n), Function.Injective φ ∧
      φ.range ≤ ((gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L).subgroupOf
        L).map g := by
  classical
  let mk : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)
  let K : Subgroup X := L.comap mk
  let f : ↥K →* ↥L := (mk.comp K.subtype).codRestrict L (fun k => k.2)
  have hf : Function.Surjective f := by
    intro l
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show mk x ∈ L
    rw [show mk x = (l : X ⧸ gnC T) from hx]
    exact l.2
  let Φ : ↥K →* alternatingGroup (Fin n) := g.comp f
  have hΦs : Function.Surjective Φ := hg.comp hf
  have hVab := isElemAbelian_gnV T hX
  have hVc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hWV hv⟩ ⟨w, hWV hw⟩)
  have hV2 : ∀ v ∈ W, v * v = 1 := fun v hv => by
    have := hVab.2 v (hWV hv)
    simpa [pow_two] using this
  have hLsub : IsSubnormal L ⊤ := hL.2.1
  have hSyl : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hLsub (isSylowTwoOf_gnImg_top hX)
  let S' : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ L
  let S : Subgroup X := S'.comap mk
  have hSK : S ≤ K := fun s hs => hs.2
  have hSsub : S.subgroupOf K = (S'.subgroupOf L).comap f := by
    ext k; exact Iff.rfl
  have hSodd : ¬ 2 ∣ (S.subgroupOf K).index := by
    rw [hSsub, Subgroup.index_comap_of_surjective _ hf]
    exact hSyl.2.2
  have himg : (S.subgroupOf K).map Φ = (S'.subgroupOf L).map g := by
    show Subgroup.map (g.comp f) _ = _
    rw [← Subgroup.map_map, hSsub, Subgroup.map_comap_eq_self_of_surjective hf]
  have hΦS : IsPGroup 2 ((S.subgroupOf K).map Φ) := by
    rw [himg]
    refine IsPGroup.map ?_ g
    exact hSyl.2.1.of_surjective (Subgroup.subgroupOfEquivOfLe hSyl.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSyl.1).symm.surjective
  have hΦodd : ¬ 2 ∣ ((S.subgroupOf K).map Φ).index := by
    rw [himg]
    intro hd
    exact hSyl.2.2 (hd.trans (Subgroup.index_map_dvd (S'.subgroupOf L) hg))
  have hSZ : ∀ s ∈ S, ∀ z ∈ omegaOneCenterOf T, s * z * s⁻¹ = z :=
    fun s hs z hz => comm_of_mem_gnImg hs.1 hz
  have hker : ∀ u : ↥⁅W, K⁆, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u :=
    fun u hu => hπk u hu
  have hπ' : ∀ (l : ↥K) (u u' : ↥⁅W, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') = (QuotientAddGroup.mk
        (evenWeightPerm (Φ l : Equiv.Perm (Fin n)) x) : altHeart n) :=
    fun l u u' hu x hx => hπi (l : X) l.2 u u' hu x hx
  obtain ⟨φ, hφinj, D, hDc, hDΦ⟩ := exists_alt_eight_centralizing W K (omegaOneCenterOf T) S
    hWK hVc hV2 hZW hSK hSodd hSZ hn9 Φ hΦs hΦS hΦodd π hker hπ'
  refine ⟨φ, hφinj, ?_⟩
  have hNle : D.map f ≤
      (gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L).subgroupOf L := by
    rintro _ ⟨d, hd, rfl⟩
    show ((f d : ↥L) : X ⧸ gnC T) ∈
      gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L
    refine ⟨Subgroup.mem_map.2 ⟨(d : X), ?_, rfl⟩, (f d).2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (mul_inv_eq_iff_eq_mul.1 (hDc d hd z hz)).symm
  rintro _ ⟨a, rfl⟩
  obtain ⟨d, hd, hda⟩ := hDΦ a
  exact ⟨f d, hNle ⟨d, hd, rfl⟩, by rw [← hda]; rfl⟩

theorem exists_alt_eight_le_centralizer (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn : 8 < n)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n))) :
    Subgroup.center ↥L = ⊥ ∧ ∃ φ : alternatingGroup (Fin 8) →* X ⧸ gnC T,
      Function.Injective φ ∧
        φ.range ≤ gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L := by
  classical
  have hn9 : 9 ≤ n := hn
  have hZ1 : Subgroup.center ↥L = ⊥ :=
    altOddCentreTrivial ↥L hL.2.2 (not_two_dvd_card_center hX hL) n hn9 he
  refine ⟨hZ1, ?_⟩
  let e : ↥L ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans he.some
  obtain ⟨g, W, π, hg, hWV, hZW, hWK, hπk, hπi⟩ :=
    exists_naturalOn_of_gf2EightFive hGF hX hL hJ hn9 e
  obtain ⟨φ, hφinj, hφ⟩ :=
    exists_alt_eight_of_naturalOn hX hL hn9 g hg W hWV hZW hWK π hπk hπi
  have hginj : Function.Injective g := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hg
  let ge : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective g ⟨hginj, hg⟩
  refine ⟨L.subtype.comp (ge.symm.toMonoidHom.comp φ), ?_, ?_⟩
  · exact L.subtype_injective.comp (ge.symm.injective.comp hφinj)
  · rintro _ ⟨a, rfl⟩
    obtain ⟨l, hl, hla⟩ := hφ ⟨a, rfl⟩
    have hl' : ge.symm (φ a) = l := ge.symm_apply_eq.2 hla.symm
    show ((ge.symm (φ a) : ↥L) : X ⧸ gnC T) ∈ _
    rw [hl']
    exact hl

end Reduction

section Consequences

theorem exists_orderOf_eq_three_alt_eight : ∃ a : alternatingGroup (Fin 8), orderOf a = 3 := by
  have hab : (0 : Fin 8) ≠ 1 := by decide
  have hac : (0 : Fin 8) ≠ 2 := by decide
  have hbc : (1 : Fin 8) ≠ 2 := by decide
  have h3 : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 0 2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hm : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact h3.sign
  refine ⟨⟨_, hm⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact h3.orderOf

theorem not_pElementSubgroup_le_of_alt_eight {Y : Type*} [Group Y] {A Z : Subgroup Y}
    {φ : alternatingGroup (Fin 8) →* Y} (hφ : Function.Injective φ) (hA : φ.range ≤ A)
    (hZ : Z = ⊥) : ¬ pElementSubgroup 3 A ≤ Z := by
  intro h
  obtain ⟨a, ha⟩ := exists_orderOf_eq_three_alt_eight
  have h1 : orderOf (φ a) = 3 := by rw [orderOf_injective φ hφ a, ha]
  have h2 : φ a ∈ Z := h (mem_pElementSubgroup_of_orderOf (hA ⟨a, rfl⟩) h1)
  rw [hZ, Subgroup.mem_bot] at h2
  rw [h2, orderOf_one] at h1
  omega

theorem one_lt_pRank_of_alt_eight {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y}
    {φ : alternatingGroup (Fin 8) →* Y} (hφ : Function.Injective φ) (hA : φ.range ≤ A) :
    1 < Open.pRank 3 A :=
  lt_of_lt_of_le one_lt_two ((two_le_pRank_of_mulEquiv_alternatingGroup (by norm_num)
    (MonoidHom.ofInjective hφ).symm).trans (SectionRank.pRank_mono (by norm_num) hA))

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem gnImg_centralizer_inf_le_gnA {C₁ : Subgroup X} (h1 : C₁ ≤ omegaOneCenterOf T)
    (L : Subgroup (X ⧸ gnC T)) :
    gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L ≤ gnA T C₁ L :=
  inf_le_inf_right L (Subgroup.map_mono
    ((Subgroup.centralizer_le h1).trans (Subgroup.centralizer_le_normalizer _)))

theorem not_pElementSubgroup_three_gnA_le_center (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn : 8 < n)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)))
    {C₁ : Subgroup X} (h1 : C₁ ≤ omegaOneCenterOf T) :
    ¬ pElementSubgroup 3 (gnA T C₁ L) ≤ (Subgroup.center ↥L).map L.subtype := by
  obtain ⟨hZ, φ, hφinj, hφ⟩ := exists_alt_eight_le_centralizer hGF hX hL hJ hn he
  exact not_pElementSubgroup_le_of_alt_eight hφinj (hφ.trans (gnImg_centralizer_inf_le_gnA h1 L))
    (by rw [hZ, Subgroup.map_bot])

theorem one_lt_pRank_three_gnA (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) {n : ℕ} (hn : 8 < n)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)))
    {C₁ : Subgroup X} (h1 : C₁ ≤ omegaOneCenterOf T) :
    1 < Open.pRank 3 (gnA T C₁ L) := by
  obtain ⟨-, φ, hφinj, hφ⟩ := exists_alt_eight_le_centralizer hGF hX hL hJ hn he
  exact one_lt_pRank_of_alt_eight hφinj (hφ.trans (gnImg_centralizer_inf_le_gnA h1 L))

end Consequences

@[expose] def GNAltRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
      ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T C₁ C₂ L →
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
          Subgroup.center ↥L = ⊥ ∧
            ¬ pElementSubgroup 3 (gnA T C₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
            (gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
              1 < Open.pRank 3 (gnA T C₁ L) ∨ 1 < Open.pRank 3 (gnA T C₂ L))

theorem gnAltFacts_of_gf2EightFive (hGF : GF2EightFive) (hR : GNAltRest) : GNAltFacts := by
  intro X _ _ T hX hT C₁ C₂ hP L hY n hn he
  rcases hn with rfl | hn
  · obtain ⟨hZ, h1, hc⟩ := hR X T hX hT C₁ C₂ hP L hY he
    exact ⟨hZ, h1, fun h => hc (h.resolve_left (by omega))⟩
  · obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := hP
    have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
    obtain ⟨hZ, -⟩ := exists_alt_eight_le_centralizer hGF hX hY.1 hJ hn he
    exact ⟨hZ, not_pElementSubgroup_three_gnA_le_center hGF hX hY.1 hJ hn he h1Z,
      fun _ => Or.inl (one_lt_pRank_three_gnA hGF hX hY.1 hJ hn he h1Z)⟩

end CFSG.AGLEmbeddingD2.GN
