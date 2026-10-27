module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSAutCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveHS
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.Sporadic.SmallOddCore.HSLocal

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.QuasithinUnique.Id2519 (fixSubgroup fixSubgroup_eq_map)
open CFSG.QuasithinUnique.Id2519.SporHS (fix_data hsRows_cases)
open CFSG.QuasithinUnique.Id2519.HSAut (outerC outerE commutator_outerC_eq card_outerE
  outerE_le_outerC outerE_simple)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_hs {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) : Nat.card S = 44352000 :=
  (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS

private theorem card_sylow_two_hs {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) (T : Sylow 2 S) : Nat.card T = 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, card_hs e, show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
    factorization_two_pow_mul (by norm_num)]

private theorem exists_fixedSubgroup_embedding
    {S : Type} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) {σ : MulAut S} (hσ : orderOf σ = 2) :
    ∃ r ∈ hsRows, ∃ ψ : S →* Equiv.Perm (Fin 3850), Function.Injective ψ ∧ (∀ s, ψ s ∈ hsP) ∧
      (fixedSubgroup σ).map ψ =
        hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range → r.outer = true) := by
  set θ : S ≃* hsP := e.trans hsPermEquiv
  set α : MulAut hsP := MulAut.congr θ σ
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hα2 : α * α = 1 := by
    rw [show α * α = MulAut.congr θ (σ * σ) from (map_mul (MulAut.congr θ) σ σ).symm, hσ2,
      map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have : σ = 1 := (MulAut.congr θ).injective (by rw [map_one]; exact h)
    rw [this, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨r, hr, g, hg, x, hxform, hxg, h3⟩ := fix_data α hα2 hα1
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hmapF : fixSubgroup α = (fixSubgroup σ).map θ.toMonoidHom :=
    fixSubgroup_eq_map θ σ α fun y => by simp [α, MulAut.congr_apply]
  have hfix : fixedSubgroup σ = fixSubgroup σ := by
    ext y
    exact Iff.rfl
  refine ⟨r, hr, (MulAut.conj g⁻¹).toMonoidHom.comp (hsP.subtype.comp θ.toMonoidHom),
    (MulAut.conj g⁻¹).injective.comp (hsP.subtype_injective.comp θ.injective), fun s => ?_, ?_,
    fun hout => ?_⟩
  · show g⁻¹ * ((θ s : hsP) : Equiv.Perm (Fin 3850)) * g⁻¹⁻¹ ∈ hsP
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) (θ s).2) (hsP.inv_mem (hsP.inv_mem hg))
  · rw [← Subgroup.map_map, ← Subgroup.map_map, hfix, ← hmapF, h3, Subgroup.map_map]
    rw [show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ by
      ext x
      simp [MulAut.conj_apply], Subgroup.map_id]
  ·
    by_contra hro
    have hrep : tp 3850 r.rep ∈ hsP := by
      by_contra hn
      exact hro (((hrows r hr).2.2.1).2 hn)
    have hxP : (x : Equiv.Perm (Fin 3850)) ∈ hsP := by
      rw [hxg]
      exact hsP.mul_mem (hsP.mul_mem hg hrep) (hsP.inv_mem hg)
    exact CatFC.not_forall_congr_eq_conj θ hout ⟨x, hxP⟩ fun p => Subtype.ext (hxform p)

theorem outerNotSylowCentral_hs
    {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) : OuterNotSylowCentral S := by
  intro σ hσ2 T hT
  by_contra hout
  have hσ1 : σ ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨r, hr, ψ, hψ, -, hψF, hrout⟩ := exists_fixedSubgroup_embedding e hσo
  obtain ⟨-, -, -, hrows, -, -, hmap, -⟩ := hs_involution_centralizers
  have hTF : (T : Subgroup S) ≤ fixedSubgroup σ := fun t ht => hT t ht
  have hdvd : 2 ^ 9 ∣ r.centOrder := by
    rw [← card_sylow_two_hs e T, ← (hrows r hr).2.2.2.2.1, ← hψF,
      Subgroup.card_map_of_injective hψ]
    exact Subgroup.card_dvd_of_le hTF
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      [(false, 5775, 7680), (false, 15400, 2880), (true, 1100, 40320), (true, 23100, 1920)] := by
    rw [← hmap]
    exact List.mem_map_of_mem (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder)) hr
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · exact absurd (h1.symm.trans (hrout hout)) (by decide)
  · exact absurd (h1.symm.trans (hrout hout)) (by decide)
  · rw [h3] at hdvd
    norm_num at hdvd
  · rw [h3] at hdvd
    norm_num at hdvd

private def centralizerSubtypeEquiv' {M : Type*} [Group M] (R : Subgroup M) (x : ↥R) :
    ↥(centralizer ({x} : Set ↥R)) ≃* ↥(centralizer ({(x : M)} : Set M) ⊓ R) where
  toFun c := ⟨(c.1 : M), mem_inf.2 ⟨by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2), c.1.2⟩⟩
  invFun c := ⟨⟨c.1, (mem_inf.1 c.2).2⟩, by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).1)⟩
  left_inv c := rfl
  right_inv c := rfl
  map_mul' a b := rfl

open CFSG.QuasithinUnique.Id2519.HSAut in
private theorem exists_commuting_five_three :
    ∃ x5 ∈ outerE, ∃ x3 ∈ outerE, orderOf x5 = 5 ∧ orderOf x3 = 3 ∧ x5 * x3 = x3 * x5 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨eC, hsz, -⟩ := outerE_classes
  have h2 : 2 < classSizes.size := by decide
  have hc : Nat.card (eC ⟨2, h2⟩).carrier = 1344 := (hsz _).trans rfl
  have hE : Nat.card outerE = 20160 := card_outerE
  obtain ⟨y, hy⟩ := ConjClasses.mk_surjective (eC ⟨2, h2⟩)
  set C := centralizer ({y} : Set outerE)
  have hC : Nat.card C = 15 := by
    have h : Nat.card C * Nat.card (ConjClasses.mk y).carrier = Nat.card outerE :=
      SeitzReduction.SporadicRefine.card_centralizer_mul_card_conjClass y
    rw [hy, hc, hE] at h
    omega
  have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hdvd : orderOf y ∣ 15 := hC ▸ Subgroup.orderOf_dvd_natCard C hyC
  have hy1 : y ≠ 1 := by
    rintro rfl
    have htop : C = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [mem_centralizer_singleton_iff, one_mul, mul_one]
    rw [htop, Subgroup.card_top, hE] at hC
    norm_num at hC
  have hmem : ∀ z : ↥outerE, (z : Equiv.Perm (Fin 3850)) ∈ outerE := fun z => z.2
  have hcomm : ∀ z ∈ C, (y : Equiv.Perm (Fin 3850)) * z = z * y := fun z hz =>
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp hz).symm
  obtain ⟨n, hn⟩ : ∃ n, orderOf y = n := ⟨_, rfl⟩
  have hn15 : n ≤ 15 := Nat.le_of_dvd (by norm_num) (hn ▸ hdvd)
  rw [hn] at hdvd
  interval_cases n <;> try norm_num at hdvd
  · exact absurd (orderOf_eq_one_iff.mp hn) hy1
  ·
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 (by rw [hC]; norm_num)
    refine ⟨((z : _) : Equiv.Perm (Fin 3850)), hmem _, y, hmem _, ?_, ?_, (hcomm _ z.2).symm⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    · rw [Subgroup.orderOf_coe, hn]
  ·
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC]; norm_num)
    refine ⟨y, hmem _, ((z : _) : Equiv.Perm (Fin 3850)), hmem _, ?_, ?_, hcomm _ z.2⟩
    · rw [Subgroup.orderOf_coe, hn]
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  ·
    refine ⟨((y ^ 3 : _) : Equiv.Perm (Fin 3850)), hmem _, ((y ^ 5 : _) : Equiv.Perm (Fin 3850)),
      hmem _, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, orderOf_pow' y (by norm_num), hn]
      norm_num
    · rw [Subgroup.orderOf_coe, orderOf_pow' y (by norm_num), hn]
      norm_num
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← pow_add, ← pow_add, add_comm]

private noncomputable def hsPToR :
    hsP →* RankThree.Native.hs100R :=
  (Subgroup.inclusion RankThree.Native.hs100P_le_R).comp RankThree.Native.hsPStarEquiv.toMonoidHom

private theorem hsPToR_injective :
    Function.Injective hsPToR :=
  (Subgroup.inclusion_injective RankThree.Native.hs100P_le_R).comp
    RankThree.Native.hsPStarEquiv.injective

private theorem card_hsP_inf_centralizer_outerE_le :
    Nat.card ↥(hsP ⊓ centralizer (outerE : Set (Equiv.Perm (Fin 3850)))) ≤ 2 := by
  classical
  have hEP : outerE ≤ hsP := outerE_le_outerC.trans inf_le_left
  have hZE : center outerE = ⊥ := by
    have := outerE_simple
    exact BMCase.center_eq_bot_of_isSimpleGroup
      (CatFC.nonabelian_of_simple_of_card_ne_prime (by rw [card_outerE]; norm_num))
  obtain ⟨x5, h5E, x3, h3E, ho5, ho3, hc53⟩ := exists_commuting_five_three
  obtain ⟨ι, hι⟩ : ∃ ι : hsP →* RankThree.Native.hs100R, Function.Injective ι :=
    ⟨hsPToR, hsPToR_injective⟩
  obtain ⟨F, hF, hFdef⟩ : ∃ F : outerE →* RankThree.Native.hs100R, Function.Injective F ∧
      ∀ x : outerE, F x = ι ⟨x, hEP x.2⟩ :=
    ⟨ι.comp (Subgroup.inclusion hEP), fun a b h => Subgroup.inclusion_injective hEP (hι h),
      fun _ => rfl⟩
  have hn : ∀ x : outerE, x ≠ 1 → F x ∉ centralizer (Set.range F) := by
    intro x hx1 hmem
    apply hx1
    have hxZ : x ∈ center outerE := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := mem_centralizer_iff.mp hmem (F z) ⟨z, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact hF h1
    rwa [hZE, Subgroup.mem_bot] at hxZ
  obtain ⟨y5, hy5def⟩ : ∃ y, F ⟨x5, h5E⟩ = y := ⟨_, rfl⟩
  obtain ⟨y3, hy3def⟩ : ∃ y, F ⟨x3, h3E⟩ = y := ⟨_, rfl⟩
  have hy5 : orderOf y5 = 5 := by
    rw [← hy5def, orderOf_injective F hF, Subgroup.orderOf_mk, ho5]
  have hy3 : orderOf y3 = 3 := by
    rw [← hy3def, orderOf_injective F hF, Subgroup.orderOf_mk, ho3]
  have hc : y5 * y3 = y3 * y5 := by
    rw [← hy5def, ← hy3def, ← map_mul, ← map_mul]
    exact congrArg F (Subtype.ext hc53)
  have hx5 : (⟨x5, h5E⟩ : outerE) ≠ 1 := fun h => by
    have h1 := Subgroup.orderOf_mk (H := outerE) x5 h5E
    rw [h, orderOf_one, ho5] at h1
    norm_num at h1
  have hx3 : (⟨x3, h3E⟩ : outerE) ≠ 1 := fun h => by
    have h1 := Subgroup.orderOf_mk (H := outerE) x3 h3E
    rw [h, orderOf_one, ho3] at h1
    norm_num at h1
  have h3 : 3 ∣ Nat.card ↥(centralizer ({(y5 : Equiv.Perm (Fin 100))} : Set _) ⊓
      RankThree.Native.hs100R) := by
    have hmem : (y3 : Equiv.Perm (Fin 100)) ∈
        centralizer ({(y5 : Equiv.Perm (Fin 100))} : Set _) ⊓ RankThree.Native.hs100R := by
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, y3.2⟩
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [Subgroup.orderOf_coe, hy3] at h
  obtain ⟨θ⟩ := EvenSporadicStandard.HSStd.hs100_five_centralizer y5.2
    (by rw [Subgroup.orderOf_coe, hy5]) h3
  have hle := EvenSporadicStandard.HSStd.PumpHS.card_centralizer_le_two_of_five_three
    (S := Set.range F) hy5 hy3 hc ⟨_, hy5def⟩ ⟨_, hy3def⟩ (hy5def ▸ hn _ hx5)
    (hy3def ▸ hn _ hx3) ((centralizerSubtypeEquiv' _ y5).trans θ)
  have hmemC : ∀ c : ↥(hsP ⊓ centralizer (outerE : Set (Equiv.Perm (Fin 3850)))),
      ι ⟨c, (mem_inf.mp c.2).1⟩ ∈ centralizer (Set.range F) := by
    intro c
    rw [mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    rw [hFdef, ← map_mul, ← map_mul]
    refine congrArg ι (Subtype.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_centralizer_iff.mp (mem_inf.mp c.2).2 z z.2
  refine le_trans (Nat.card_le_card_of_injective
    (fun c => (⟨_, hmemC c⟩ : ↥(centralizer (Set.range F)))) ?_) hle
  intro c d h
  have h1 : (⟨c, (mem_inf.mp c.2).1⟩ : hsP) = ⟨d, (mem_inf.mp d.2).1⟩ :=
    hι (congrArg Subtype.val h)
  exact Subtype.ext (congrArg (fun p : hsP => (p : Equiv.Perm (Fin 3850))) h1)

private theorem hsP_inf_centralizer_outerE :
    hsP ⊓ centralizer (outerE : Set (Equiv.Perm (Fin 3850))) = ⊥ := by
  have hEP : outerE ≤ hsP := outerE_le_outerC.trans inf_le_left
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  obtain ⟨hcP, hcE⟩ := mem_inf.mp hc
  have hco : orderOf c = 2 := by
    have hdvd := Subgroup.orderOf_dvd_natCard _ hc
    have hle := (Nat.le_of_dvd Nat.card_pos hdvd).trans card_hsP_inf_centralizer_outerE_le
    have hpos : 0 < orderOf c := orderOf_pos c
    have h1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨-, -, hC1, hC2, hcov⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨t, ht, k, hk, rfl⟩ := hcov c hcP hco
  have hEle : outerE ≤ hsP ⊓ centralizer ({k * t * k⁻¹} : Set (Equiv.Perm (Fin 3850))) :=
    fun z hz => mem_inf.mpr ⟨hEP hz, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hcE z hz)⟩
  have hdvd := Subgroup.card_dvd_of_le hEle
  rw [card_outerE, CFSG.Sporadic.SmallOddCore.inf_centralizer_conj hsP hk,
    Subgroup.card_map_of_injective (MulAut.conj k).injective] at hdvd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · rw [hC1] at hdvd
    norm_num at hdvd
  · rw [hC2] at hdvd
    norm_num at hdvd

private theorem pPrimeCore_eq_bot_of_simple {T : Type*} [Group T] [Finite T] (hT : IsSimpleGroup T)
    (h2 : 2 ∣ Nat.card T) : pPrimeCore 2 T = ⊥ := by
  rcases hT.eq_bot_or_eq_top_of_normal (pPrimeCore 2 T) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card (pPrimeCore 2 T)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private theorem coreActionKernel_eq_bot_of_le_fixedSubgroup
    {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) {σ : MulAut S} (hσ : orderOf σ = 2)
    {T : Subgroup S} (hTσ : T ≤ fixedSubgroup σ) (hTp : Group.IsPerfect T)
    (hTc : 20160 ≤ Nat.card T) : coreActionKernel T = ⊥ := by
  obtain ⟨r, hr, ψ, hψinj, hψP, hψF, -⟩ := exists_fixedSubgroup_embedding e hσ
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hcardF : Nat.card (fixedSubgroup σ) = r.centOrder := by
    rw [← (hrows r hr).2.2.2.2.1, ← hψF, Subgroup.card_map_of_injective hψinj]
  have hle : 20160 ≤ r.centOrder := hcardF ▸ hTc.trans (Subgroup.card_le_of_le hTσ)
  have hC : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
    rcases hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨hrep, -⟩ | h
    · omega
    · omega
    · rw [hrep]
      rfl
    · omega
  have hTE : T.map ψ = outerE := by
    have hle1 : T.map ψ ≤ outerC := hC ▸ hψF ▸ Subgroup.map_mono hTσ
    have hperf : ⁅T.map ψ, T.map ψ⁆ = T.map ψ := by
      rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hTp]
    have hle2 : T.map ψ ≤ outerE := by
      rw [← hperf, ← commutator_outerC_eq]
      exact Subgroup.commutator_mono hle1 hle1
    exact Subgroup.eq_of_le_of_card_ge hle2 (by
      rw [card_outerE, Subgroup.card_map_of_injective hψinj]
      exact hTc)
  have hTs : IsSimpleGroup T := by
    have ε : T ≃* outerE :=
      (T.equivMapOfInjective ψ hψinj).trans (MulEquiv.subgroupCongr hTE)
    exact (MulEquiv.isSimpleGroup_congr ε).2 outerE_simple
  have hO : pPrimeCore 2 T = ⊥ := pPrimeCore_eq_bot_of_simple hTs (by
    rw [← Subgroup.card_map_of_injective hψinj, hTE, card_outerE]
    norm_num)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hxT⟩ := mem_coreActionKernel.mp hx
  have hcomm : ∀ j ∈ T, x * j = j * x := by
    intro j hj
    have h1 := hxT j hj
    rw [hO, Subgroup.map_bot, Subgroup.mem_bot] at h1
    calc x * j = x * j * (j⁻¹ * x⁻¹ * j * x) := by rw [h1, mul_one]
      _ = j * x := by group
  have hψx : ψ x ∈ hsP ⊓ centralizer (outerE : Set (Equiv.Perm (Fin 3850))) := by
    refine Subgroup.mem_inf.mpr ⟨hψP x, ?_⟩
    rw [← hTE]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, hcomm j hj]
  rw [hsP_inf_centralizer_outerE, Subgroup.mem_bot] at hψx
  exact hψinj (hψx.trans (map_one ψ).symm)

theorem fixedA8KernelTrivial_hs
    {S : Type} [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HS) : FixedA8KernelTrivial S := by
  intro Q hQ2 hQc T hTF hT hT8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : Group.IsPerfect T := isPerfect_of_isPComponent hTF hT
  have hTc : 20160 ≤ Nat.card T := by
    rw [← hT8]
    exact Nat.le_of_dvd Nat.card_pos ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  by_cases hQ : ∃ σ ∈ Q, σ ≠ 1
  · obtain ⟨σ, hσQ, hσ1⟩ := hQ
    have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hQ2 σ hσQ) hσ1
    exact coreActionKernel_eq_bot_of_le_fixedSubgroup e hσo (fun t ht => hTF ht σ hσQ) hTp hTc
  ·
    exfalso
    simp only [not_exists, not_and, not_not] at hQ
    have hS : IsSimpleGroup S := by
      have : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .HS) :=
        CFSG.Sporadic.HS.isSimpleGroup_HS
      exact e.isSimpleGroup
    have htop : EvenPump.autFixed Q = ⊤ := by
      rw [eq_top_iff]
      intro l _ q hq
      rw [hQ q hq]
      rfl
    obtain ⟨-, -, hsub, -⟩ := hT
    have hTsub : T.IsSubnormal := Subgroup.IsSubnormal.trans hTF hsub
      (htop ▸ (inferInstance : (⊤ : Subgroup S).Normal).isSubnormal)
    rcases hTsub.eq_bot_or_top_of_isSimpleGroup hS with h | h
    · rw [h, Subgroup.card_bot] at hTc
      norm_num at hTc
    · have hc : Nat.card (↥T ⧸ Open.fusionZStar ↥T) = Nat.card (S ⧸ Open.fusionZStar S) := by
        rw [h]
        exact card_quot_fusionZStar_eq_of_equiv (Sol78.coreQuotCongr Subgroup.topEquiv)
      rw [hT8] at hc
      rcases hS.eq_bot_or_eq_top_of_normal (Open.fusionZStar S) with h0 | h1
      · rw [h0, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, card_hs e] at hc
        norm_num at hc
      · rw [h1, Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top,
          inferInstance⟩] at hc
        norm_num at hc

end CFSG.ComponentClassification.GSThmB.A10T
