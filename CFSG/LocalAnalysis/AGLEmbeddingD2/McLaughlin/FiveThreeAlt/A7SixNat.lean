module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B1Red CFSG.QuasithinUnique
open CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open scoped commutatorElement

section Abstract

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_move_fixV_pCoreOf (hV : ∀ v : V, v ^ 2 = 1)
    {H L A : Subgroup (MulAut V)} (e : ↥L ≃* alternatingGroup (Fin 7))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hHA : H ≤ L ⊔ A)
    (hoff : IsFFStarOffender H A) :
    ∃ l ∈ L, ∃ w ∈ fixV (pCoreOf 2 H), l w ≠ w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 H with hPdef
  set W := fixV P with hWdef
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hAH : A ≤ H := hoff.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hoff.2.2.1.2
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    exact MulEquiv.isSimpleGroup e
  have hLP1 : L ⊓ P = ⊥ := by
    have hnorm : ((L ⊓ P).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y l hy hl =>
        ⟨L.mul_mem (L.mul_mem hl hy.1) (L.inv_mem hl), conj_mem_pCoreOf (hLH hl) hy.2⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ _ _ hnorm with h | h
    · refine eq_bot_iff.2 fun x hx => ?_
      have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
    · exfalso
      have hLP : L ≤ P := fun x hx => by
        have hx' : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := by rw [h]; trivial
        exact hx'.2
      have h2 : IsPGroup 2 ↥L := hP2.to_le hLP
      exact alt_not_two_group (by norm_num : 3 ≤ 7) (h2.of_surjective e.toMonoidHom e.surjective)
  have hLP : ∀ x ∈ L, ∀ q ∈ P, x * q = q * x := by
    intro x hx q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ L := by
      have := L.mul_mem hx (hLn q (hPH hq) x⁻¹ (L.inv_mem hx))
      simpa [mul_assoc] using this
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ P :=
      P.mul_mem (conj_mem_pCoreOf (hLH hx) hq) (P.inv_mem hq)
    have h3 : x * q * x⁻¹ * q⁻¹ ∈ L ⊓ P := ⟨h1, h2⟩
    rw [hLP1, Subgroup.mem_bot] at h3
    calc x * q = (x * q * x⁻¹ * q⁻¹) * q * x := by group
      _ = q * x := by rw [h3]; group
  have hAn : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha l hl => hLn a (hAH ha) l hl
  have hsq : ∀ x ∈ H, x ^ 2 ∈ L := by
    intro x hx
    obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_sup hAn (hHA hx)
    have ha1 : a * a = 1 := by simpa [pow_two] using hA2 a ha
    have : (l * a) ^ 2 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_two]; simp [mul_assoc]
    rw [this, ha1, mul_one]
    exact L.mul_mem hl (hLn a (hAH ha) l hl)
  have hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ L := by
    intro x hx ho
    obtain ⟨m, hm⟩ := ho
    have hx1 : x ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one x
    have : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hx1, one_mul]
    exact this ▸ L.pow_mem (hsq x hx) (m + 1)
  have hker : H ⊓ centSub W = P := kernel_eq_pCoreOf hV hD hLP
  by_contra hcon
  push Not at hcon
  have hLle : L ≤ P := fun l hl => by
    have h1 : l ∈ H ⊓ centSub W := ⟨hLH hl, fun w hw => hcon l hl w hw⟩
    rw [hker] at h1
    exact h1
  have h2 : IsPGroup 2 ↥L := hP2.to_le hLle
  exact alt_not_two_group (by norm_num : 3 ≤ 7) (h2.of_surjective e.toMonoidHom e.surjective)

end Abstract

section Reduction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_naturalOn_or_four_ne (hGF : GF2EightFive) (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) (e : ↥L ≃* alternatingGroup (Fin 7)) :
    (∃ (g : ↥L →* alternatingGroup (Fin 7)) (W : Subgroup X)
      (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart 7)),
      Function.Surjective g ∧ W ≤ gnV T ∧ omegaOneCenterOf T ≤ W ∧
      (∃ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∃ w ∈ W, k * w * k⁻¹ ≠ w) ∧
      
      (∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
      (∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
        (k : X) * u * (k : X)⁻¹ = u) ∧
      ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
        (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
        (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight 7,
          Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart 7) →
          Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
            (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7)) x) : altHeart 7)) ∨
    (∃ W U : Subgroup X, W ≤ gnV T ∧ omegaOneCenterOf T ≤ W ∧
      (∃ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∃ w ∈ W, k * w * k⁻¹ ≠ w) ∧
      
      (∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
      ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ U ∧ U ≤ gnV T ∧
      (∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ u ∈ U, k * u * k⁻¹ ∈ U) ∧
      Nat.card U = 2 ^ 4) := by
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
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
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
  let e1 : ↥L1 ≃* alternatingGroup (Fin 7) :=
    (Subgroup.equivMapOfInjective L ι hι).symm.trans e
  have hdich := natural_or_four_on_fixV hGF hV2 e1 hLH hLn le_rfl hoff hAL
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
  have hmoveW : ∃ k ∈ L.comap mk, ∃ w ∈ W, k * w * k⁻¹ ≠ w := by
    obtain ⟨l1, hl1, w0, hw0, hne⟩ := exists_move_fixV_pCoreOf hV2 e1 hLH hLn le_rfl hoff
    obtain ⟨l, hl, rfl⟩ := hl1
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective l
    refine ⟨k, hl, (w0 : IntMod (gnV T) hV).val, ⟨w0, hw0, rfl⟩, fun h => hne ?_⟩
    apply IntMod.val_injective
    exact (hval k w0).trans h
  rcases hdich with ⟨α, hα, π, hπk, hπi⟩ | hcard
  · left
    let ψ : ↥⁅W, L.comap mk⁆ →* ↥(natU H) :=
      ((Subgroup.equivMapOfInjective (natU H) (valHom' hV)
        (valHom'_injective hV)).symm).toMonoidHom.comp (Subgroup.inclusion hle)
    have hψ : ∀ u : ↥⁅W, L.comap mk⁆,
        (((ψ u : ↥(natU H)) : IntMod (gnV T) hV)).val = (u : X) := by
      intro u
      have := congrArg Subtype.val
        ((Subgroup.equivMapOfInjective (natU H) (valHom' hV)
          (valHom'_injective hV)).apply_symm_apply (Subgroup.inclusion hle u))
      exact this
    let g : ↥L →* alternatingGroup (Fin 7) :=
      α.comp (Subgroup.equivMapOfInjective L ι hι).toMonoidHom
    have hg : Function.Surjective g := hα.comp (Subgroup.equivMapOfInjective L ι hι).surjective
    refine ⟨g, W, π.comp ψ, hg, hWV, hZW, hmoveW, hWK, ?_, ?_⟩
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
  · right
    refine ⟨W, (natU H).map (valHom' hV), hWV, hZW, hmoveW, hWK, hle, ?_, ?_, ?_⟩
    · rintro _ ⟨u, -, rfl⟩
      exact u.val_mem
    · rintro k hk _ ⟨u, hu, rfl⟩
      exact ⟨ι (mk k) u, natU_invariant H (hKH k hk) hu, (hval k u).symm⟩
    · rw [Subgroup.card_map_of_injective (valHom'_injective hV)]
      exact hcard


end Reduction

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
