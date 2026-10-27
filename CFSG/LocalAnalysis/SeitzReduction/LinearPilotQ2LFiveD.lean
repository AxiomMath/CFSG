module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCMatch
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial oddCoreLift)

@[expose] def LinearTwoFieldTypeAtNOne {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (c : Fin n) (W₁ : Subgroup G)
    (htN : t ∈ normalizer (W₁ : Set G)) : Prop :=
  ∃ Kc : Subgroup (seitzHat W₁), IsComponent Kc ∧ seitzLeviHat e c W₁ < Kc ∧
    Kc.map (MulAut.conj (seitzHatMap W₁ ⟨t, htN⟩)).toMonoidHom = Kc ∧
    seitzHatMap W₁ ⟨t, htN⟩ ∉ Kc ∧ center Kc = ⊥ ∧ LieModel Kc .PSL (n - 1) 2 2 ∧
    ∃ hsN : seitzHatMap W₁ ⟨t, htN⟩ ∈ normalizer (Kc : Set (seitzHat W₁)),
      Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range

@[expose] def LFiveFieldNOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      LinearTwoFieldTypeAtNOne e t c W₁ htN → False

section Helpers

theorem inf_eq_bot_of_card_map_mk_eq {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    {S : Subgroup H} (h : Nat.card (S.map (QuotientGroup.mk' N)) = Nat.card S) : S ⊓ N = ⊥ := by
  have hsurj := (QuotientGroup.mk' N).subgroupMap_surjective S
  have hinj := (hsurj.bijective_of_nat_card_le h.symm.le).1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxN⟩ := mem_inf.1 hx
  have h1 : (QuotientGroup.mk' N).subgroupMap S ⟨x, hxS⟩ =
      (QuotientGroup.mk' N).subgroupMap S 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' N x = QuotientGroup.mk' N 1
    rw [map_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hxN
  exact mem_bot.2 (congrArg Subtype.val (hinj h1))

theorem card_specialLinearGroup_three_of_card_four {F : Type} [Field F] (hF : Nat.card F = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 60480 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  classical
  rw [Matrix.card_SL_field, hq]
  decide

theorem card_dvd_of_lieModel_PSL_three_four {X : Type} [Group X] (hX : LieModel X .PSL 3 2 2) :
    Nat.card X ∣ 60480 := by
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  rw [Nat.card_congr ψ.toEquiv, ← card_specialLinearGroup_three_of_card_four (by rw [hF]; norm_num)]
  exact Subgroup.card_quotient_dvd_card _

end Helpers

section KMTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldKind_of_gOne_five
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin 5} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))} (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL 3 2 2)
    {G₁ : Subgroup G} (hperf : ⁅G₁, G₁⁆ = G₁)
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hδ : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L)
    (hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hL : IsSimpleGroup L := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  have hq : CFSG.Open.IsQuasisimple G₁ := isQuasisimple_of_linearSwapDiag h₁₂ hperf hL hδ hsurj
  set D := modelToG e (blockSL (K := K) (({a, b} : Finset (Fin 5)))ᶜ) with hDdef
  have hXL : modelToG e X₀ ≤ L := modelToG_le e X₀
  have hDL : D ≤ L := modelToG_le e _
  have hDX : D ≤ centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e (blockSL_compl_le_centralizer hX₀)
  have hDperf : ⁅D, D⁆ = D :=
    (commutator_modelToG_blockSL_pair_compl_and_ne_bot (by norm_num) e hab).1
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_torusQ1_of_seitzSetting hset hK1 e (by norm_num)
    htC ht hab hX₀ hX₀c rfl htX rfl
  obtain ⟨F', _, _, -, ⟨ψ'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hmodel
  have hOut := isSolvable_outer_of_mulEquiv (by norm_num) ψ'
  have hs : orderOf (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))
      ⟨t, htX⟩) = 2 := orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hDs := hcomp.1
  have hsD : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      centralizer ((D.subgroupOf (centralizer (modelToG e X₀ : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) :
        Set (centralizer (modelToG e X₀ : Set G) ⧸
          oddCore (centralizer (modelToG e X₀ : Set G)))) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hDs hd)
  have hsC : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))) := by
    intro h
    apply hτ
    have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G))))) ∈ Kc.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact h
    exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
  have hcore := perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKcomp hDK hs hsD hsN hsC hsyl hOut
  set δ := linearSwapDiag h₁₂ with hδdef
  have hmemL : ∀ x : G₁, δ x ∈ L := fun x => hδ x x.2
  set π : G₁ →* L := δ.codRestrict L hmemL with hπ
  have hπapp : ∀ x : G₁, (π x : G) = (x : G) * (t * x * t⁻¹) := fun x => rfl
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hπker : π.ker ≤ center G₁ := by
    intro x hx
    refine ker_linearSwapDiag_le_center h₁₂ ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hZodd : Odd (Nat.card (center G₁)) :=
    UnitaryPilot.odd_card_center_of_swapFactors hset.center_eq_bot ht hKt hq h₁₂ hδ hsurj
  have hkerodd : Odd (Nat.card π.ker) := Odd.of_dvd_nat hZodd (Subgroup.card_dvd_of_le hπker)
  have hπinj : Function.Injective π :=
    oddSchurTrivial_of_mulEquiv_projectiveSL_two hK e G₁ (Subgroup.isPerfect_iff.2 hperf) π hπs
      hπker hkerodd
  set TD : Subgroup G₁ := (D.subgroupOf L).comap π with hTD
  set C : Subgroup G := TD.map G₁.subtype with hC
  have hCG₁ : C ≤ G₁ := map_subtype_le _
  have hTDmap : TD.map π = D.subgroupOf L := Subgroup.map_comap_eq_self_of_surjective hπs _
  have hDsub : ⁅D.subgroupOf L, D.subgroupOf L⁆ = D.subgroupOf L :=
    CFSG.SeitzReduction.commutator_subgroupOf_eq_self hDL hDperf
  have hTDperf : ⁅TD, TD⁆ = TD := by
    apply Subgroup.map_injective hπinj
    rw [Subgroup.map_commutator, hTDmap, hDsub]
  have hCperf : ⁅C, C⁆ = C := by
    rw [hC, ← Subgroup.map_commutator, hTDperf]
  obtain ⟨-, -, -, -, -, -, -, ⟨φD⟩, -, -⟩ :=
    neighbour_data_torusQ1 e (by norm_num) hab htC hX₀ hX₀c rfl (D := D) rfl
  let φC : C ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    ((TD.equivMapOfInjective G₁.subtype G₁.subtype_injective).symm.trans
      ((TD.equivMapOfInjective π hπinj).trans (MulEquiv.subgroupCongr hTDmap))).trans
      ((subgroupOfEquivOfLe hDL).trans φD)
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 :=
    card_specialLinearGroup_three_of_card_two hK
  have hcardC : Nat.card C = 168 := by rw [Nat.card_congr φC.toEquiv, hcardSL]
  have hcardD : Nat.card D = 168 := by rw [Nat.card_congr φD.toEquiv]; exact hcardSL
  have hZSL : center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  have hZC : center C = ⊥ := F4Pilot.center_eq_bot_congr φC.symm hZSL
  have hCX : C ≤ centralizer (modelToG e X₀ : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx⟩ := hπs ⟨y, hXL hy⟩
    have hcD : ((π c : L) : G) ∈ D := mem_subgroupOf.1 (mem_comap.1 hc)
    have hxX : ((π x : L) : G) ∈ modelToG e X₀ := by
      rw [hx]
      exact hy
    have hcx : c * x = x * c := by
      apply hπinj
      rw [map_mul, map_mul]
      exact Subtype.ext (mem_centralizer_iff.1 (hDX hcD) _ hxX).symm
    have hct : (c : G) * (t * x * t⁻¹) = (t * x * t⁻¹) * c :=
      mem_centralizer_iff.1 (h₁₂ ⟨x, x.2, rfl⟩) c c.2
    have hyx : y = (x : G) * (t * x * t⁻¹) := by
      rw [← hπapp, hx]
    have hcx' : (c : G) * x = x * c := congrArg Subtype.val hcx
    rw [hyx]
    change (x : G) * (t * x * t⁻¹) * c = c * (x * (t * x * t⁻¹))
    calc (x : G) * (t * x * t⁻¹) * c = x * ((t * x * t⁻¹) * c) := by group
      _ = x * (c * (t * x * t⁻¹)) := by rw [hct]
      _ = (x * c) * (t * x * t⁻¹) := by group
      _ = (c * x) * (t * x * t⁻¹) := by rw [hcx']
      _ = c * (x * (t * x * t⁻¹)) := by group
  have hCtX : C.map (MulAut.conj t).toMonoidHom ≤ centralizer (modelToG e X₀ : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htX (hCX hx)) (inv_mem htX)
  have hCt_cent : C.map (MulAut.conj t).toMonoidHom ≤ centralizer (C : Set G) :=
    (map_mono hCG₁).trans (h₁₂.trans (centralizer_le hCG₁))
  have hCtperf : ⁅C.map (MulAut.conj t).toMonoidHom, C.map (MulAut.conj t).toMonoidHom⁆ =
      C.map (MulAut.conj t).toMonoidHom := by
    rw [← map_commutator, hCperf]
  obtain ⟨-, -, ⟨eDb⟩⟩ := nonempty_map_oddCore_mulEquiv_specialLinear_two hK e (by norm_num) htC
    hab hX₀ hX₀c rfl (D := D) rfl
  have hDO : D.subgroupOf (centralizer (modelToG e X₀ : Set G)) ⊓
      oddCore (centralizer (modelToG e X₀ : Set G)) = ⊥ := by
    refine inf_eq_bot_of_card_map_mk_eq _ ((Nat.card_congr eDb.toEquiv).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv, hcardD]
    exact hcardSL
  have hCO : C.subgroupOf (centralizer (modelToG e X₀ : Set G)) ⊓
      oddCore (centralizer (modelToG e X₀ : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hxH⟩ hx
    obtain ⟨hxC, hxO⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at hxC
    obtain ⟨c, hc, hcx⟩ := hxC
    have hcx' : (c : G) = x := hcx
    have htH : (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G)) * ⟨x, hxH⟩ *
        (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹ ∈
          oddCore (centralizer (modelToG e X₀ : Set G)) :=
      (inferInstance : (oddCore (centralizer (modelToG e X₀ : Set G))).Normal).conj_mem _ hxO _
    have hπc : ((π c : L) : G) ∈ D := mem_subgroupOf.1 (mem_comap.1 hc)
    have hmemH : ((π c : L) : G) ∈ centralizer (modelToG e X₀ : Set G) := hDX hπc
    have hδO : (⟨((π c : L) : G), hmemH⟩ : centralizer (modelToG e X₀ : Set G)) ∈
        oddCore (centralizer (modelToG e X₀ : Set G)) := by
      have heq : (⟨((π c : L) : G), hmemH⟩ : centralizer (modelToG e X₀ : Set G)) =
          ⟨x, hxH⟩ * ((⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G)) * ⟨x, hxH⟩ *
            (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹) := by
        apply Subtype.ext
        change ((π c : L) : G) = x * (t * x * t⁻¹)
        rw [hπapp, hcx']
      rw [heq]
      exact mul_mem hxO htH
    have h1 := (eq_bot_iff.1 hDO) (mem_inf.2 ⟨mem_subgroupOf.2 hπc, hδO⟩)
    have h2 : ((π c : L) : G) = 1 := congrArg Subtype.val (mem_bot.1 h1)
    have hπ1 : π c = 1 := Subtype.ext h2
    have hc1 : c = 1 := hπinj (hπ1.trans (map_one π).symm)
    rw [mem_bot]
    apply Subtype.ext
    change x = 1
    rw [← hcx', hc1]
    rfl
  have hCtO : (C.map (MulAut.conj t).toMonoidHom).subgroupOf
      (centralizer (modelToG e X₀ : Set G)) ⊓ oddCore (centralizer (modelToG e X₀ : Set G)) =
      ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨y, hyH⟩ hy
    obtain ⟨hyC, hyO⟩ := mem_inf.1 hy
    rw [mem_subgroupOf] at hyC
    obtain ⟨x, hxC, hxy⟩ := hyC
    have hxy' : t * x * t⁻¹ = y := hxy
    have hxH : x ∈ centralizer (modelToG e X₀ : Set G) := hCX hxC
    have hxO : (⟨x, hxH⟩ : centralizer (modelToG e X₀ : Set G)) ∈
        oddCore (centralizer (modelToG e X₀ : Set G)) := by
      have h2 := (inferInstance : (oddCore (centralizer (modelToG e X₀ : Set G))).Normal).conj_mem
        _ hyO (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹
      have heq : (⟨x, hxH⟩ : centralizer (modelToG e X₀ : Set G)) =
          (⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹ * ⟨y, hyH⟩ *
            ((⟨t, htX⟩ : centralizer (modelToG e X₀ : Set G))⁻¹)⁻¹ := by
        apply Subtype.ext
        change x = t⁻¹ * y * t⁻¹⁻¹
        rw [← hxy']
        group
      rw [heq]
      exact h2
    have h1 := (eq_bot_iff.1 hCO) (mem_inf.2 ⟨mem_subgroupOf.2 hxC, hxO⟩)
    have hx1 : x = 1 := congrArg Subtype.val (mem_bot.1 h1)
    rw [mem_bot]
    apply Subtype.ext
    change y = 1
    rw [← hxy', hx1]
    group
  set Cb := (C.subgroupOf (centralizer (modelToG e X₀ : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) with hCbdef
  set Cb' := ((C.map (MulAut.conj t).toMonoidHom).subgroupOf
    (centralizer (modelToG e X₀ : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) with hCb'def
  have hcardCb : Nat.card Cb = 168 := by
    rw [hCbdef, ← Nat.card_congr (F4Pilot.mapMkEquivOfInfEqBot _ _ hCO).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hCX).toEquiv, hcardC]
  have hcardCb' : Nat.card Cb' = 168 := by
    rw [hCb'def, ← Nat.card_congr (F4Pilot.mapMkEquivOfInfEqBot _ _ hCtO).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hCtX).toEquiv,
      Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective,
      hcardC]
  have hZCb : center Cb = ⊥ := F4Pilot.center_eq_bot_congr
    ((subgroupOfEquivOfLe hCX).symm.trans (F4Pilot.mapMkEquivOfInfEqBot _ _ hCO)) hZC
  have hcomm' : Cb' ≤ centralizer (Cb : Set (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.1 (hCt_cent (mem_subgroupOf.1 hy)) x (mem_subgroupOf.1 hx)
  have hinf : Cb ⊓ Cb' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := mem_inf.1 hz
    have hzc : (⟨z, hz1⟩ : Cb) ∈ center Cb := by
      rw [mem_center_iff]
      intro w
      apply Subtype.ext
      exact mem_centralizer_iff.1 (hcomm' hz2) w w.2
    rw [hZCb] at hzc
    exact mem_bot.2 (congrArg Subtype.val (mem_bot.1 hzc))
  have hCbK : Cb ≤ Kc := by
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect le_top ?_
    rw [hCbdef, ← map_commutator, CFSG.SeitzReduction.commutator_subgroupOf_eq_self hCX hCperf]
  have hCb'K : Cb' ≤ Kc := by
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect le_top ?_
    rw [hCb'def, ← map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self hCtX hCtperf]
  have hsup := card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hcomm' hinf
  rw [hcardCb, hcardCb'] at hsup
  have hdvd : 168 * 168 ∣ Nat.card Kc := hsup ▸ Subgroup.card_dvd_of_le (sup_le hCbK hCb'K)
  have h60 := hdvd.trans (card_dvd_of_lieModel_PSL_three_four hmodel)
  omega

end KMTwo

end CFSG.SeitzReduction.LinearPilot
