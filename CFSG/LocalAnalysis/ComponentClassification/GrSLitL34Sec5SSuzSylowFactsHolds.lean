module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSylowFacts
public import CFSG.Sporadic.SuzOddCore.SylowFactsModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem isElemTwo_comap_of_injective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {A : Subgroup Y} (hA : IsElemTwo A) :
    IsElemTwo (A.comap f) := by
  refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
  · rw [map_mul, map_mul]
    exact hA.1 (f a) ha (f b) hb
  · rw [map_mul, map_one]
    exact hA.2 (f a) ha

theorem centralizer_map_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (Q : Subgroup X) :
    (Subgroup.centralizer (Q : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ((Q.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subgroup.mem_centralizer_iff.mp hx q hq)
  · intro hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro q hq
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hy (e q)
      (Subgroup.mem_map_of_mem e.toMonoidHom hq)

theorem map_subtype_centralizer_of_subgroupOf {G : Type} [Group G] {X U : Subgroup G}
    (hUX : U ≤ X) :
    (Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      X ⊓ Subgroup.centralizer (U : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X) := hy
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy' ⊢
    intro u hu
    exact congrArg Subtype.val (hy' ⟨u, hUX hu⟩ (Subgroup.mem_subgroupOf.mpr hu))
  · rintro ⟨hxX, hxC⟩
    have hxC' : x ∈ Subgroup.centralizer (U : Set G) := hxC
    refine ⟨⟨x, hxX⟩, ?_, rfl⟩
    show (⟨x, hxX⟩ : X) ∈ Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X)
    rw [Subgroup.mem_centralizer_iff] at hxC' ⊢
    intro u hu
    exact Subtype.ext (hxC' u (Subgroup.mem_subgroupOf.mp hu))

theorem sylowFacts_of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (n : ℕ) (R₀ : Sylow 2 Y)
    (hR₀ : IsElemTwo (zGammaThree (R₀ : Subgroup Y)) ∧
      Nat.card (zGammaThree (R₀ : Subgroup Y)) = n ∧
      ∃ Q : Subgroup Y, Q ≤ R₀ ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        (R₀ : Subgroup Y) ⊔ Subgroup.centralizer (Q : Set Y) = ⊤) :
    ∀ R : Sylow 2 X, IsElemTwo (zGammaThree (R : Subgroup X)) ∧
      Nat.card (zGammaThree (R : Subgroup X)) = n ∧
      ∃ Q : Subgroup X, Q ≤ R ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        (R : Subgroup X) ⊔ Subgroup.centralizer (Q : Set X) = ⊤ := by
  intro R
  obtain ⟨hzEl, hzCard, Q₀, hQ₀le, hQ₀el, hQ₀card, hQ₀sup⟩ := hR₀
  let RY : Sylow 2 Y := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R
  have hRYcoe : (RY : Subgroup Y) = (R : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y RY R₀
  let f : X ≃* Y := e.trans (MulAut.conj g)
  have hfcomp : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
    ext x
    rfl
  have hfR : (R : Subgroup X).map f.toMonoidHom = R₀ := by
    rw [hfcomp, ← Subgroup.map_map, ← hRYcoe, ← hg]
    rfl
  let Q : Subgroup X := Q₀.comap f.toMonoidHom
  have hQmap : Q.map f.toMonoidHom = Q₀ := by
    change (Q₀.comap f.toMonoidHom).map f.toMonoidHom = Q₀
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr f.surjective, top_inf_eq]
  have hQle : Q ≤ R := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective]
    rw [hQmap, hfR]
    exact hQ₀le
  have hQel : IsElemTwo Q := isElemTwo_comap_of_injective f.toMonoidHom f.injective hQ₀el
  have hQcard : Nat.card Q = 8 := by
    calc Nat.card Q = Nat.card (Q.map f.toMonoidHom) :=
          (Subgroup.card_map_of_injective (K := Q) f.injective).symm
      _ = Nat.card Q₀ := by rw [hQmap]
      _ = 8 := hQ₀card
  have hzmap : (zGammaThree (R : Subgroup X)).map f.toMonoidHom =
      zGammaThree (R₀ : Subgroup Y) := by
    rw [map_zGammaThree_of_injOn f.toMonoidHom f.injective.injOn, hfR]
  have hzEl' : IsElemTwo (zGammaThree (R : Subgroup X)) := by
    have h : IsElemTwo ((zGammaThree (R : Subgroup X)).map f.toMonoidHom) := by
      rw [hzmap]; exact hzEl
    have h2 := isElemTwo_comap_of_injective f.toMonoidHom f.injective h
    rwa [Subgroup.comap_map_eq, (MonoidHom.ker_eq_bot_iff f.toMonoidHom).mpr f.injective,
      sup_bot_eq] at h2
  have hzCard' : Nat.card (zGammaThree (R : Subgroup X)) = n := by
    calc Nat.card (zGammaThree (R : Subgroup X)) =
          Nat.card ((zGammaThree (R : Subgroup X)).map f.toMonoidHom) :=
            (Subgroup.card_map_of_injective (K := zGammaThree (R : Subgroup X))
              f.injective).symm
      _ = Nat.card (zGammaThree (R₀ : Subgroup Y)) := by rw [hzmap]
      _ = n := hzCard
  have hcent : (Subgroup.centralizer (Q : Set X)).map f.toMonoidHom =
      Subgroup.centralizer (Q₀ : Set Y) := by
    rw [centralizer_map_mulEquiv f Q, hQmap]
  have hsup : (R : Subgroup X) ⊔ Subgroup.centralizer (Q : Set X) = ⊤ := by
    apply top_le_iff.mp
    rw [← Subgroup.map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective
      (H := ⊤) (K := (R : Subgroup X) ⊔ Subgroup.centralizer (Q : Set X))]
    rw [Subgroup.map_sup, hfR, hcent, hQ₀sup, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr f.surjective]
  exact ⟨hzEl', hzCard', Q, hQle, hQel, hQcard, hsup⟩

theorem suzSylowFacts_of_model
    (hmodel : ∃ R₀ : Subgroup (Equiv.Perm (Fin 1782)),
      R₀ ≤ CFSG.Sporadic.SuzOddCore.suzM ∧ Nat.card R₀ = 8192 ∧
      IsElemTwo (zGammaThree R₀) ∧ Nat.card (zGammaThree R₀) = 16 ∧
      ∃ Q : Subgroup (Equiv.Perm (Fin 1782)), Q ≤ R₀ ∧ IsElemTwo Q ∧ Nat.card Q = 8 ∧
        CFSG.Sporadic.SuzOddCore.suzM ≤
          R₀ ⊔ (CFSG.Sporadic.SuzOddCore.suzM ⊓
            Subgroup.centralizer (Q : Set (Equiv.Perm (Fin 1782))))) :
    SuzSylowFacts := by
  intro X _ _ hX R
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.suz_equiv_of_isSporadic hX
  obtain ⟨R₀, hR₀le, hRcard, hzel, hzcard, Q₀, hQ₀le, hQ₀el, hQ₀card, hQ₀sup⟩ := hmodel
  let R₀' : Subgroup ↥CFSG.Sporadic.SuzOddCore.suzM :=
    R₀.subgroupOf CFSG.Sporadic.SuzOddCore.suzM
  have hR₀'card : Nat.card R₀' = 8192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀le).toEquiv, hRcard]
  have hfac : (Nat.card ↥CFSG.Sporadic.SuzOddCore.suzM).factorization 2 = 13 := by
    rw [CFSG.Sporadic.SuzOddCore.suzM_card]
    show (448345497600 : ℕ).factorization 2 = 13
    rw [show (448345497600 : ℕ) = 2 ^ 13 * 54729675 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hR₀'syl : Nat.card R₀' = 2 ^ (Nat.card ↥CFSG.Sporadic.SuzOddCore.suzM).factorization 2 := by
    rw [hR₀'card, hfac]
    norm_num
  let R₀s : Sylow 2 ↥CFSG.Sporadic.SuzOddCore.suzM := Sylow.ofCard R₀' hR₀'syl
  have hR₀scoe : (R₀s : Subgroup ↥CFSG.Sporadic.SuzOddCore.suzM) = R₀' :=
    Sylow.coe_ofCard R₀' hR₀'syl
  have hR₀'map : R₀'.map (CFSG.Sporadic.SuzOddCore.suzM).subtype = R₀ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR₀le]
  have hzmap : (zGammaThree R₀').map (CFSG.Sporadic.SuzOddCore.suzM).subtype =
      zGammaThree R₀ := by
    rw [map_zGammaThree_of_injOn (CFSG.Sporadic.SuzOddCore.suzM).subtype
      (Set.injOn_of_injective (f := (CFSG.Sporadic.SuzOddCore.suzM).subtype)
        (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective), hR₀'map]
  have hzel' : IsElemTwo (zGammaThree R₀') := by
    have h : IsElemTwo ((zGammaThree R₀').map (CFSG.Sporadic.SuzOddCore.suzM).subtype) := by
      rw [hzmap]; exact hzel
    have h2 := isElemTwo_comap_of_injective (CFSG.Sporadic.SuzOddCore.suzM).subtype
      (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective h
    rwa [Subgroup.comap_map_eq,
      (MonoidHom.ker_eq_bot_iff (CFSG.Sporadic.SuzOddCore.suzM).subtype).mpr
        (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective, sup_bot_eq] at h2
  have hzcard' : Nat.card (zGammaThree R₀') = 16 := by
    calc Nat.card (zGammaThree R₀') = Nat.card ((zGammaThree R₀').map
          (CFSG.Sporadic.SuzOddCore.suzM).subtype) :=
          (Subgroup.card_map_of_injective (K := zGammaThree R₀')
            (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective).symm
      _ = Nat.card (zGammaThree R₀) := by rw [hzmap]
      _ = 16 := hzcard
  let Q' : Subgroup ↥CFSG.Sporadic.SuzOddCore.suzM :=
    Q₀.subgroupOf CFSG.Sporadic.SuzOddCore.suzM
  have hQ'map : Q'.map (CFSG.Sporadic.SuzOddCore.suzM).subtype = Q₀ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hQ₀le.trans hR₀le)]
  have hQ'le : Q' ≤ (R₀s : Subgroup ↥CFSG.Sporadic.SuzOddCore.suzM) := by
    rw [hR₀scoe]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hQ₀le (Subgroup.mem_subgroupOf.mp hx))
  have hQ'el : IsElemTwo Q' := by
    have h : IsElemTwo (Q'.map (CFSG.Sporadic.SuzOddCore.suzM).subtype) := by
      rw [hQ'map]; exact hQ₀el
    have h2 := isElemTwo_comap_of_injective (CFSG.Sporadic.SuzOddCore.suzM).subtype
      (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective h
    rwa [Subgroup.comap_map_eq,
      (MonoidHom.ker_eq_bot_iff (CFSG.Sporadic.SuzOddCore.suzM).subtype).mpr
        (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective, sup_bot_eq] at h2
  have hQ'card : Nat.card Q' = 8 := by
    calc Nat.card Q' = Nat.card (Q'.map (CFSG.Sporadic.SuzOddCore.suzM).subtype) :=
          (Subgroup.card_map_of_injective (K := Q')
            (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective).symm
      _ = Nat.card Q₀ := by rw [hQ'map]
      _ = 8 := hQ₀card
  have hcentmap : (Subgroup.centralizer (Q' : Set ↥CFSG.Sporadic.SuzOddCore.suzM)).map
      (CFSG.Sporadic.SuzOddCore.suzM).subtype =
      CFSG.Sporadic.SuzOddCore.suzM ⊓
        Subgroup.centralizer (Q₀ : Set (Equiv.Perm (Fin 1782))) :=
    map_subtype_centralizer_of_subgroupOf (hQ₀le.trans hR₀le)
  have hsup' : (R₀s : Subgroup ↥CFSG.Sporadic.SuzOddCore.suzM) ⊔
      Subgroup.centralizer (Q' : Set ↥CFSG.Sporadic.SuzOddCore.suzM) = ⊤ := by
    apply Subgroup.map_injective (f := (CFSG.Sporadic.SuzOddCore.suzM).subtype)
      (CFSG.Sporadic.SuzOddCore.suzM).subtype_injective
    rw [Subgroup.map_sup, hR₀scoe, hR₀'map, hcentmap, Subgroup.map_top,
      Subgroup.range_subtype]
    exact le_antisymm (sup_le hR₀le inf_le_left) hQ₀sup
  exact sylowFacts_of_mulEquiv e 16 R₀s
    ⟨hzel', hzcard', Q', hQ'le, hQ'el, hQ'card, hsup'⟩ R

theorem suzSylowFacts_holds :
    SuzSylowFacts :=
  suzSylowFacts_of_model CFSG.Sporadic.SuzOddCore.suz_sylow_model

end CFSG.ComponentClassification.GrSLit.L34Sec5S
