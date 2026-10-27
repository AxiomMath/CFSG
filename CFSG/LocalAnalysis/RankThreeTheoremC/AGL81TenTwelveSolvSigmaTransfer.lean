module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreTransport
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.RankThree.PartTwo.Sec8.HeringBMemLift
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LargeExtraspecial.S14C10Sym3
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_map_of_surjective_of_isPGroup_ker {A B : Type*} [Group A] [Group B] {p : ℕ}
    (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup p f.ker) (X : Subgroup A) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let g : X →* X.map f := (f.comp X.subtype).codRestrict (X.map f) fun x => ⟨x, x.2, rfl⟩
  have hgsurj : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨⟨a, ha⟩, rfl⟩
  have hgker : IsPGroup p g.ker := by
    rintro ⟨x, hx⟩
    have hgx : ((g x : X.map f) : B) = f (x : A) := rfl
    have hx' : f (x : A) = 1 := by
      have h := congrArg (fun y : X.map f => (y : B)) hx
      rw [hgx] at h
      simpa using h
    obtain ⟨n, hn⟩ := hker ⟨(x : A), hx'⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hmain := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker g hgsurj hgker
  unfold pCoreOf
  rw [← hmain, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem pCoreOf_barM_eq (M X : Subgroup G) (hXM : X ≤ M) :
    pCoreOf 2 (barM M X) =
      ((pCoreOf 2 X).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup (G := ↥M) 2
  have h := pCoreOf_map_of_surjective_of_isPGroup_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    (QuotientGroup.mk'_surjective _) hker (X.subgroupOf M)
  rw [barM, h, show pCoreOf 2 (X.subgroupOf M) = (pCoreOf 2 X).subgroupOf M from
    (CFSG.HardMathSupport.Cooperstein.Proving.subgroupOf_pCoreOf (p := 2) hXM).symm]

theorem barM_mem_cZero {M X I : Subgroup G} (hXM : X ≤ M) (hI : I ∈ cZero X)
    (hI3 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))) :
    barM M I ∈ cZero (barM M X) ∧
      Nonempty (↥(barM M I) ⧸ CFSG.pCore 2 ↥(barM M I) ≃* Equiv.Perm (Fin 3)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπM
  have hIM : I ≤ M := hI.le.trans hXM
  have hnot : ¬ IsTwoPrimeComponent I I := by
    rintro ⟨-, -, hperfect, -⟩
    obtain ⟨e⟩ := hI3
    have hperfI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hperfect
    have hperfq : Group.IsPerfect (↥I ⧸ CFSG.pCore 2 ↥I) := by
      have := hperfI
      exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥I))
        (QuotientGroup.mk'_surjective _)
    have hperfp : Group.IsPerfect (Equiv.Perm (Fin 3)) := by
      have := hperfq
      exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hbot : (⊤ : Subgroup (Equiv.Perm (Fin 3))) = ⊥ :=
      CFSG.LargeExtraspecial.S14.eq_bot_of_perfect_perm_three (P := ⊤) hperfp.commutator_eq_top
    have hcard1 : Nat.card (Equiv.Perm (Fin 3)) = 1 := by
      rw [← Subgroup.card_top (G := Equiv.Perm (Fin 3)), hbot, Subgroup.card_bot]
    have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    omega
  have hb : pCoreOf 2 I = pCoreOf 2 X := (hI.shape.resolve_left hnot).1
  have hsym : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I) := (hI.shape.resolve_left hnot).2
  have hsub : IsSubnormal (barM M I) (barM M X) :=
    IsSubnormal.map πM (IsSubnormal.comap M.subtype hI.subnormal)
  have hcore : pCoreOf 2 (barM M I) = pCoreOf 2 (barM M X) := by
    rw [pCoreOf_barM_eq M I hIM, pCoreOf_barM_eq M X hXM, hb]
  let eI : ↥I →* ↥(barM M I) :=
    (πM.comp (Subgroup.inclusion hIM)).codRestrict (barM M I) fun i =>
      Subgroup.mem_map_of_mem πM (Subgroup.mem_subgroupOf.mpr i.2)
  have heI : Function.Surjective eI := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext hmy⟩
  have hkerI : IsPGroup 2 eI.ker := by
    rintro ⟨i, hi⟩
    have heIx : ((eI i : ↥(barM M I)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
        πM (Subgroup.inclusion hIM i) := rfl
    have hi1 : πM (Subgroup.inclusion hIM i) = 1 := by
      have h := congrArg (fun y : ↥(barM M I) => (y : ↥M ⧸ CFSG.pCore 2 ↥M)) hi
      rw [heIx] at h
      simpa using h
    have hmem : Subgroup.inclusion hIM i ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff _).mp hi1
    have hmem' : ((i : ↥I) : G) ∈ pCoreOf 2 M :=
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hIM i, hmem, rfl⟩
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 M) ⟨((i : ↥I) : G), hmem'⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker eI heI hkerI
  refine ⟨⟨barM_mono hI.le, hsub, Or.inr ⟨hcore, ?_⟩⟩, ?_⟩
  · exact IsSymThreeOrSUThreeTwo.of_mulEquiv e hsym
  · obtain ⟨e₀⟩ := hI3
    exact ⟨e.symm.trans e₀⟩

theorem mk_mem_normalizer_of_barM {M H I₀ : Subgroup G} (hI₀H : I₀ ≤ H) (hI₀M : I₀ ≤ M)
    (hMH : pCoreOf 2 M ≤ pCoreOf 2 H) {x : G} (hxH : x ∈ H) (hxM : x ∈ M)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩ : M) ∈
      normalizer (barM M I₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    QuotientGroup.mk' (primeComplementCore (G := H) 3) (⟨x, hxH⟩ : H) ∈
      normalizer ((((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3)) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := primeComplementCore (G := H) 3 with hO
  set πH := QuotientGroup.mk' O with hπH
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπM
  have hO2H : pCoreOf 2 H ≤ O.map H.subtype := by
    have hcop : Nat.Coprime 3 (Nat.card ((pCoreOf 2 H).subgroupOf H)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).toEquiv]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 H)
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    have h := Subgroup.map_mono (f := H.subtype)
      (normal_coprime_le_primeComplementCore 3 _ (pCoreOf_normal 2 H) hcop)
    rwa [Subgroup.map_subgroupOf_eq_of_le (pCoreOf_le 2 H)] at h
  have hkill : ∀ o ∈ pCoreOf 2 M, ∀ hoH : o ∈ H, πH (⟨o, hoH⟩ : H) = 1 := by
    intro o ho hoH
    have hmem : o ∈ O.map H.subtype := hO2H (hMH ho)
    obtain ⟨y, hy, hyo⟩ := Subgroup.mem_map.mp hmem
    have hsub : (⟨o, hoH⟩ : H) = y := Subtype.ext (by simpa using hyo.symm)
    exact (QuotientGroup.eq_one_iff _).mpr (hsub ▸ hy)
  have hN : πH ⟨x, hxH⟩ ∈ Subgroup.normalizer ((I₀.subgroupOf H).map πH : Set _) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hs
    have hiI : (i : G) ∈ I₀ := Subgroup.mem_subgroupOf.mp hi
    have hiM : (i : G) ∈ M := hI₀M hiI
    have hmem : πM ⟨x * (i : G) * x⁻¹, M.mul_mem (M.mul_mem hxM hiM) (M.inv_mem hxM)⟩ ∈
        barM M I₀ := by
      have h1 : πM ⟨x, hxM⟩ * πM ⟨(i : G), hiM⟩ * (πM ⟨x, hxM⟩)⁻¹ ∈ barM M I₀ :=
        (Subgroup.mem_normalizer_iff.mp hx _).mp
          (Subgroup.mem_map_of_mem πM (Subgroup.mem_subgroupOf.mpr hiI))
      have heq : πM ⟨x, hxM⟩ * πM ⟨(i : G), hiM⟩ * (πM ⟨x, hxM⟩)⁻¹ =
          πM ⟨x * (i : G) * x⁻¹, M.mul_mem (M.mul_mem hxM hiM) (M.inv_mem hxM)⟩ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      rwa [heq] at h1
    obtain ⟨i', hi', hi'eq⟩ := Subgroup.mem_map.mp hmem
    have hi'I : (i' : G) ∈ I₀ := Subgroup.mem_subgroupOf.mp hi'
    have hdiffG : ((i' : ↥M) : G)⁻¹ * (x * (i : G) * x⁻¹) ∈ pCoreOf 2 M :=
      Subgroup.mem_map.mpr ⟨(i' : ↥M)⁻¹ * (⟨x * (i : G) * x⁻¹,
        M.mul_mem (M.mul_mem hxM hiM) (M.inv_mem hxM)⟩ : ↥M),
        QuotientGroup.eq.mp hi'eq, rfl⟩
    have hmemA : (x * (i : G) * x⁻¹)⁻¹ * (i' : G) ∈ pCoreOf 2 M := by
      have hinv := (pCoreOf 2 M).inv_mem hdiffG
      rwa [show (((i' : ↥M) : G)⁻¹ * (x * (i : G) * x⁻¹))⁻¹ =
        (x * (i : G) * x⁻¹)⁻¹ * (i' : G) by group] at hinv
    have heqH : πH ⟨x * (i : G) * x⁻¹,
          H.mul_mem (H.mul_mem hxH (hI₀H hiI)) (H.inv_mem hxH)⟩ =
        πH ⟨(i' : G), hI₀H hi'I⟩ := by
      have h1 : πH ((⟨x * (i : G) * x⁻¹,
          H.mul_mem (H.mul_mem hxH (hI₀H hiI)) (H.inv_mem hxH)⟩ : ↥H)⁻¹ *
          ⟨(i' : G), hI₀H hi'I⟩) = 1 := by
        have hlt : (⟨x * (i : G) * x⁻¹,
            H.mul_mem (H.mul_mem hxH (hI₀H hiI)) (H.inv_mem hxH)⟩ : ↥H)⁻¹ *
            ⟨(i' : G), hI₀H hi'I⟩ =
            ⟨(x * (i : G) * x⁻¹)⁻¹ * (i' : G),
              H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem hxH (hI₀H hiI)) (H.inv_mem hxH)))
                (hI₀H hi'I)⟩ := rfl
        rw [hlt]
        exact hkill _ hmemA _
      rw [map_mul, map_inv] at h1
      exact inv_mul_eq_one.mp h1
    have heq1 : πH ⟨x, hxH⟩ * πH i * (πH ⟨x, hxH⟩)⁻¹ =
        πH ⟨x * (i : G) * x⁻¹,
          H.mul_mem (H.mul_mem hxH (hI₀H hiI)) (H.inv_mem hxH)⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [heq1, heqH]
    exact Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr hi'I)
  have hO2sub : ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H) =
      CFSG.ComponentClassification.AS76b.oUpperTwo (I₀.subgroupOf H) := by
    have h1 : (CFSG.ComponentClassification.AS76b.oUpperTwo (I₀.subgroupOf H)).map H.subtype =
        CFSG.ComponentClassification.AS76b.oUpperTwo I₀ := by
      rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hI₀H]
    rw [← h1, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hO2 : ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map πH =
      CFSG.ComponentClassification.AS76b.oUpperTwo ((I₀.subgroupOf H).map πH) := by
    rw [hO2sub, CFSG.AGLEmbedding.SUPair.map_oUpperTwo]
  have hchar : Subgroup.normalizer ((I₀.subgroupOf H).map πH : Set (H ⧸ O)) ≤
      Subgroup.normalizer ((CFSG.ComponentClassification.AS76b.oUpperTwo
        ((I₀.subgroupOf H).map πH) : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    intro g hg
    have hZT : (CFSG.ComponentClassification.AS76b.oUpperTwo
        ((I₀.subgroupOf H).map πH) : Subgroup (H ⧸ O)) =
        Subgroup.closure {y : H ⧸ O | y ∈ (I₀.subgroupOf H).map πH ∧ Odd (orderOf y)} :=
      rfl
    rw [hZT]
    have hforward : ∀ h ∈ Subgroup.normalizer ((I₀.subgroupOf H).map πH : Set (H ⧸ O)),
        ∀ z ∈ (I₀.subgroupOf H).map πH, Odd (orderOf z) → h * z * h⁻¹ ∈
          {y : H ⧸ O | y ∈ (I₀.subgroupOf H).map πH ∧ Odd (orderOf y)} := by
      intro h hh z hz hodd
      refine ⟨(Subgroup.mem_normalizer_iff.mp hh z).mp hz, ?_⟩
      rw [show h * z * h⁻¹ = MulAut.conj h z from rfl, MulEquiv.orderOf_eq]
      exact hodd
    have hmap : ∀ h ∈ Subgroup.normalizer ((I₀.subgroupOf H).map πH : Set (H ⧸ O)),
        (Subgroup.closure {y : H ⧸ O | y ∈ (I₀.subgroupOf H).map πH ∧
            Odd (orderOf y)}).map (MulAut.conj h).toMonoidHom ≤
          Subgroup.closure {y : H ⧸ O | y ∈ (I₀.subgroupOf H).map πH ∧
            Odd (orderOf y)} := by
      intro h hh
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.subset_closure (by
        simpa [MulAut.conj_apply] using hforward h hh a ha.1 ha.2)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      simpa [MulAut.conj_apply] using
        hmap g hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz)
    · intro hz
      have hmem := hmap g⁻¹ (Subgroup.inv_mem _ hg)
        (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz)
      simpa [MulAut.conj_apply, mul_assoc] using hmem
  rw [hO2]
  exact hchar hN

theorem exists_three_elt_lift {M H : Subgroup G} {y : H ⧸ primeComplementCore (G := H) 3}
    (hy : y ∈ d1X0 3 M H) (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) :
    ∃ x : G, ∃ hxH : x ∈ H, x ∈ M ∧ (∃ k : ℕ, x ^ 3 ^ k = 1) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) 3) (⟨x, hxH⟩ : H) = y := by
  obtain ⟨k, hk⟩ := hy3
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
  have hgM : (g : G) ∈ M := (Subgroup.mem_subgroupOf.mp hg).2
  obtain ⟨x, hx3, hxy, u, hxu⟩ :=
    CFSG.RankThree.PartTwo.Sec8.HeringBMem.exists_three_pow_lift
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) (x := g) (k := k)
      (hgy.symm ▸ hk)
  refine ⟨(x : G), x.2, ?_, ?_, ?_⟩
  · have hxgu : (x : G) = (g : G) ^ u := by
      have h := congrArg (fun z : ↥H => (z : G)) hxu
      simpa using h
    rw [hxgu]
    exact M.pow_mem hgM u
  · obtain ⟨e, he⟩ := hx3
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  · simpa using hxy.trans hgy

theorem twentySeven_dvd_card_barM {M H X : Subgroup G} (hXH : X ≤ H) (hXM : X ≤ M)
    (h27 : 27 ∣ Nat.card ((X.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)))) :
    27 ∣ Nat.card (barM M X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπH
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπM
  let fH : ↥X →* ↥H ⧸ primeComplementCore (G := H) 3 := πH.comp (Subgroup.inclusion hXH)
  have hfH : fH.range = (X.subgroupOf H).map πH := by
    show (πH.comp (Subgroup.inclusion hXH)).range = (X.subgroupOf H).map πH
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let fM : ↥X →* ↥M ⧸ CFSG.pCore 2 ↥M := πM.comp (Subgroup.inclusion hXM)
  have hfM : fM.range = barM M X := by
    show (πM.comp (Subgroup.inclusion hXM)).range = barM M X
    rw [barM, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hcopH : Nat.Coprime 3 (Nat.card fH.ker) := by
    have hdvd : Nat.card fH.ker ∣ Nat.card ↥(primeComplementCore (G := H) 3) := by
      let ψ : ↥fH.ker →* ↥(primeComplementCore (G := H) 3) :=
        { toFun := fun k =>
            ⟨Subgroup.inclusion hXH (k : ↥X), by
              have hk : fH (k : ↥X) = 1 := MonoidHom.mem_ker.mp k.2
              exact (QuotientGroup.eq_one_iff _).mp
                (show (QuotientGroup.mk' (primeComplementCore (G := H) 3))
                  (Subgroup.inclusion hXH (k : ↥X)) = 1 from hk)⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl }
      have hψ : Function.Injective ψ := by
        intro a b hab
        have h1 : ((Subgroup.inclusion hXH (a : ↥X) : ↥H) : G) =
            ((Subgroup.inclusion hXH (b : ↥X) : ↥H) : G) :=
          congrArg (fun z : ↥(primeComplementCore (G := H) 3) => ((z : ↥H) : G)) hab
        exact Subtype.ext (Subtype.ext (by simpa using h1))
      exact Subgroup.card_dvd_of_injective ψ hψ
    exact Nat.Coprime.of_dvd_right hdvd (primeComplementCore_coprime (G := H) 3)
  have hP : IsPGroup 2 fM.ker := by
    rintro ⟨x, hx⟩
    have hfMx : fM x = πM (Subgroup.inclusion hXM x) := rfl
    have hx' : πM (Subgroup.inclusion hXM x) = 1 := by
      rw [← hfMx]
      exact MonoidHom.mem_ker.mp hx
    have hmem : Subgroup.inclusion hXM x ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff _).mp hx'
    have hmem' : ((x : ↥X) : G) ∈ pCoreOf 2 M :=
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXM x, hmem, rfl⟩
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 M) ⟨((x : ↥X) : G), hmem'⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hcopM : Nat.Coprime 3 (Nat.card fM.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hcardH : Nat.card X = Nat.card ((X.subgroupOf H).map πH) * Nat.card fH.ker := by
    have h := Subgroup.card_ker_mul_card_range fH
    rw [hfH] at h
    rw [← h, Nat.mul_comm]
  have hcardM : Nat.card X = Nat.card (barM M X) * Nat.card fM.ker := by
    have h := Subgroup.card_ker_mul_card_range fM
    rw [hfM] at h
    rw [← h, Nat.mul_comm]
  have h27X : 27 ∣ Nat.card X := by
    rw [hcardH]
    exact dvd_mul_of_dvd_left h27 _
  have hcop27 : Nat.Coprime 27 (Nat.card fM.ker) := by
    have h := Nat.Coprime.pow_left 3 hcopM
    simpa using h
  refine hcop27.dvd_of_dvd_mul_right ?_
  rw [← hcardM]
  exact h27X

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
