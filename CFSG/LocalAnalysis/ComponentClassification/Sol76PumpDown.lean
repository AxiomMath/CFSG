module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

section General

variable {Q : Type*} [Group Q] [Finite Q]

theorem primeResidual_two_eq_top (hQ : Group.IsPerfect Q) :
    CatalogueBPrimeJoin.primeResidual 2 Q = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CatalogueBPrimeJoin.primeResidual 2 Q with hR
  have : R.Characteristic := CatalogueBPrimeJoin.primeResidual_characteristic 2 Q
  have : R.Normal := inferInstance
  have hodd : Odd (Nat.card (Q ⧸ R)) :=
    Nat.coprime_two_left.mp (CatalogueBPrimeJoin.primeResidual_coprime_index 2 Q)
  have hsolv : Group.IsSolvable (Q ⧸ R) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  have h1 : Nat.card (Q ⧸ R) ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have : Nontrivial (Q ⧸ R) :=
    Finite.one_lt_card_iff_nontrivial.mp (lt_of_le_of_ne Nat.card_pos (Ne.symm h1))
  exact Group.IsPerfect.not_isSolvable (G := Q ⧸ R) hsolv

theorem le_fusionZStar_of_normal (hQ : Group.IsPerfect Q)
    (hq : IsQuasisimple (Q ⧸ pPrimeCore 2 Q)) {N : Subgroup Q} (hN : N.Normal) (hNt : N ≠ ⊤) :
    N ≤ Open.fusionZStar Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 Q) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hNm with h | h
  · exfalso
    apply hNt
    have hsup : N ⊔ pPrimeCore 2 Q = ⊤ := by
      have := congrArg (Subgroup.comap π) h
      rwa [comap_map_eq, hπ, QuotientGroup.ker_mk', comap_top] at this
    have himg : (pPrimeCore 2 Q).map (QuotientGroup.mk' N) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' N).ge,
        bot_sup_eq,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
      exact h1
    have hodd : Odd (Nat.card (Q ⧸ N)) := by
      have h1 := card_map_dvd (pPrimeCore 2 Q) (QuotientGroup.mk' N)
      rw [himg, card_top] at h1
      exact (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := Q))).of_dvd_nat h1
    have hsolv : Group.IsSolvable (Q ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    by_contra hne
    have h1 : Nat.card (Q ⧸ N) ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    have : Nontrivial (Q ⧸ N) :=
      Finite.one_lt_card_iff_nontrivial.mp (lt_of_le_of_ne Nat.card_pos (Ne.symm h1))
    exact Group.IsPerfect.not_isSolvable (G := Q ⧸ N) hsolv
  · rw [Sol78.fusionZStar_eq_comap]
    exact map_le_iff_le_comap.mp h

end General

section Quotient

variable {Y : Type*} [Group Y] [Finite Y]

theorem index_fusionZStar_eq_index_center {K : Subgroup (Y ⧸ pPrimeCore 2 Y)} (hK : K.IsSubnormal)
    {L : Subgroup Y} (hLK : L.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = K) :
    (Open.fusionZStar ↥L).index = (center ↥K).index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  have hmem : ∀ l : ↥L, π (L.subtype l) ∈ K := fun l => hLK ▸ mem_map_of_mem π l.2
  let f : ↥L →* ↥K := (π.comp L.subtype).codRestrict K hmem
  have hf_apply : ∀ l : ↥L, (f l : Y ⧸ pPrimeCore 2 Y) = π l := fun _ => rfl
  have hf : Function.Surjective f := by
    rintro ⟨k, hk⟩
    rw [← hLK] at hk
    obtain ⟨l, hl, rfl⟩ := hk
    exact ⟨⟨l, hl⟩, rfl⟩
  have hker : f.ker = pPrimeCore 2 ↥L := by
    apply le_antisymm
    · refine le_sSup ⟨f.normal_ker, ?_⟩
      let ι : f.ker →* pPrimeCore 2 Y :=
        { toFun := fun x => ⟨((x : ↥L) : Y), by
            have h1 : f x = 1 := x.2
            have h2 := congrArg Subtype.val h1
            rw [hf_apply] at h2
            exact (QuotientGroup.eq_one_iff _).mp h2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hι : Function.Injective ι := fun a b h => by
        have h2 : ((ι a : pPrimeCore 2 Y) : Y) = ι b := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h2)
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι)
        (pPrimeCore_coprime_card (p := 2) (G := Y))
    ·
      have hO : (pPrimeCore 2 ↥L).map f ≤ pPrimeCore 2 ↥K := by
        refine le_sSup ⟨(pPrimeCore_normal (p := 2) (G := ↥L)).map f hf, ?_⟩
        exact Nat.Coprime.coprime_dvd_right (card_map_dvd _ f)
          (pPrimeCore_coprime_card (p := 2) (G := ↥L))
      have hKO : (pPrimeCore 2 ↥K).map K.subtype ≤ pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) :=
        CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hK
      rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hKO
      intro x hx
      have h1 : f x ∈ pPrimeCore 2 ↥K := hO (mem_map_of_mem f hx)
      have h2 : (f x : Y ⧸ pPrimeCore 2 Y) ∈ (⊥ : Subgroup (Y ⧸ pPrimeCore 2 Y)) :=
        hKO (mem_map_of_mem K.subtype h1)
      rw [mem_bot] at h2
      exact MonoidHom.mem_ker.mpr (Subtype.ext h2)
  have hZ : Open.fusionZStar ↥L = (center ↥K).comap f := by
    ext x
    rw [Sol78.fusionZStar_eq_comap, mem_comap, mem_comap, mem_center_iff, mem_center_iff]
    constructor
    · intro h k
      obtain ⟨y, rfl⟩ := hf k
      have h1 := h (QuotientGroup.mk' (pPrimeCore 2 ↥L) y)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, ← hker] at h1
      rw [← map_mul, ← map_mul]
      have h2 := MonoidHom.mem_ker.mp h1
      rw [map_mul, map_inv] at h2
      exact (eq_of_inv_mul_eq_one h2)
    · intro h q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
      have h1 := h (f y)
      rw [← map_mul, ← map_mul] at h1
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, ← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [hZ, index_comap_of_surjective _ hf]

end Quotient

section PumpDown

variable {G : Type} [Group G] [Finite G]

theorem le_twoLayerIn_inf_centralizer {X J : Subgroup G} {s : G} (hsX : s ∈ X)
    (hs2 : ∀ x ∈ X, s ^ 2 * x = x * s ^ 2) (hs : IsPGroup 2 (zpowers s))
    (hJX : J ≤ twoLayerIn X) (hJs : J ≤ centralizer ({s} : Set G)) (hJ : ⁅J, J⁆ = J)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    (htype : ∀ K : Subgroup G, IsTwoComponentIn K X → ¬ J ≤ coreActionKernel K →
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J)) :
    J ≤ twoLayerIn (X ⊓ centralizer ({s} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX' : J ≤ X := hJX.trans (map_subtype_le _)
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  set O := pPrimeCore 2 ↥X with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := ↥X)
  set π := QuotientGroup.mk' O with hπ
  set xs : ↥X := ⟨s, hsX⟩ with hxs
  set g : ↥X ⧸ O := π xs with hg
  let ρ : ↥J →* ↥X ⧸ O := π.comp (Subgroup.inclusion hJX')
  have hρ : ∀ j : ↥J, ρ j = π ⟨j, hJX' j.2⟩ := fun _ => rfl
  set Jb := ρ.range with hJb
  have hJE : Jb ≤ layer (↥X ⧸ O) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le
    rintro _ ⟨j, rfl⟩
    refine mem_map_of_mem π ?_
    obtain ⟨y, hy, hyj⟩ := hJX j.2
    have : Subgroup.inclusion hJX' j = y := Subtype.ext hyj.symm
    rw [this]
    exact hy
  have hJp : ⁅Jb, Jb⁆ = Jb := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  have hJg : ∀ x ∈ Jb, Commute g x := by
    rintro _ ⟨j, rfl⟩
    rw [hρ, hg]
    refine Commute.map ?_ π
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJs j.2)).symm
  have hg2 : ∀ x ∈ layer (↥X ⧸ O), g ^ 2 * x = x * g ^ 2 := by
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
    rw [hg, ← map_pow]
    change π (xs ^ 2 * y) = π (y * xs ^ 2)
    congr 1
    exact Subtype.ext (hs2 y y.2)
  have hfixc : ∀ K : Subgroup (↥X ⧸ O), IsComponent K → ¬ Jb ≤ centralizer (K : Set _) →
      K.map (MulAut.conj g).toMonoidHom = K → ∀ k ∈ K, Commute g k := by
    intro K hK hJK hgK
    refine commute_of_forall_mul (Subgroup.isPerfect_iff.mp hK.1.1) hgK hJg ?_
    set E := layer (↥X ⧸ O) with hE
    set Z := E ⊓ centralizer (K : Set (↥X ⧸ O)) with hZ
    have hKE : K ≤ E := component_le_layer hK
    have hEK : E ≤ normalizer (K : Set (↥X ⧸ O)) := layer_le_normalizer hK
    have hZE : Z ≤ E := inf_le_left
    have hZn : (Z.subgroupOf E).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer hZE]
      refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
      obtain ⟨hxE, hxC⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨mul_mem (mul_mem hc hxE) (inv_mem hc), ?_⟩
      rw [mem_centralizer_iff]
      intro k hk
      have hk' : c⁻¹ * k * c ∈ K := by
        have := (mem_normalizer_iff.mp (hEK (inv_mem hc)) k).mp hk
        simpa using this
      have h1 : c⁻¹ * k * c * x = x * (c⁻¹ * k * c) := (mem_centralizer_iff.mp hxC) _ hk'
      calc k * (c * x * c⁻¹) = c * (c⁻¹ * k * c * x) * c⁻¹ := by group
        _ = c * (x * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
        _ = c * x * c⁻¹ * k := by group
    set φ := QuotientGroup.mk' (Z.subgroupOf E) with hφ
    have hQcard : Nat.card (↥E ⧸ Z.subgroupOf E) = (center ↥K).index := by
      let φK : ↥K →* ↥E ⧸ Z.subgroupOf E := φ.comp (Subgroup.inclusion hKE)
      have hsurj : Function.Surjective φK := by
        intro q
        obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf E) q
        obtain ⟨u, hu, huc⟩ := exists_mem_mul_centralizer hK e.2
        refine ⟨⟨u, hu⟩, ?_⟩
        change φ ⟨u, hKE hu⟩ = φ e
        rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          mem_subgroupOf]
        refine mem_inf.mpr ⟨mul_mem (inv_mem (hKE hu)) e.2, ?_⟩
        rw [mem_centralizer_iff]
        intro k hk
        exact (huc k hk).eq
      have hker : φK.ker = center ↥K := by
        ext k
        rw [MonoidHom.mem_ker, mem_center_iff]
        change φ ⟨k, hKE k.2⟩ = 1 ↔ _
        rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
        constructor
        · intro h l
          exact Subtype.ext ((mem_centralizer_iff.mp (mem_inf.mp h).2) l l.2)
        · intro h
          refine mem_inf.mpr ⟨hKE k.2, ?_⟩
          rw [mem_centralizer_iff]
          intro l hl
          exact congrArg Subtype.val (h ⟨l, hl⟩)
      rw [← hker, index_ker, (MonoidHom.range_eq_top_of_surjective _ hsurj), card_top]
    let ρE : ↥J →* ↥E := ρ.codRestrict E fun j => hJE ⟨j, rfl⟩
    let ψ : ↥J →* ↥E ⧸ Z.subgroupOf E := φ.comp ρE
    have hψ : ∀ j : ↥J, ψ j = φ ⟨ρ j, hJE ⟨j, rfl⟩⟩ := fun _ => rfl
    have hkerψ : ψ.ker ≠ ⊤ := by
      intro h
      apply hJK
      rintro _ ⟨j, rfl⟩
      have h1 : ψ j = 1 := MonoidHom.mem_ker.mp (by rw [h]; exact mem_top j)
      rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact (mem_inf.mp h1).2
    have hleZ : ψ.ker ≤ Open.fusionZStar ↥J :=
      le_fusionZStar_of_normal hJperf hJq ψ.normal_ker hkerψ
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥X) 2).1 K hK
    set K0 := CatalogueBPrimeJoin.canonicalPrimeLift 2 K with hK0def
    set Kt := K0.map X.subtype with hKt
    have hKtX : IsTwoComponentIn Kt X := by
      refine ⟨map_subtype_le _, ?_⟩
      rw [hKt, ← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
      exact hK0
    have hmove : ¬ J ≤ coreActionKernel Kt := by
      intro hc
      apply hJK
      rintro _ ⟨j, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, ← hK0map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 := (hc j.2).2 (k : G) (mem_map_of_mem X.subtype hk)
      have h2 := oddCoreIn_le_of_isTwoComponentIn hKtX h1
      obtain ⟨o, ho, hoe⟩ := h2
      have h3 : o = k⁻¹ * ⟨j, hJX' j.2⟩⁻¹ * k * ⟨j, hJX' j.2⟩ := Subtype.ext (by simpa using hoe)
      rw [h3] at ho
      rw [hρ, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq (s := O)).mpr ?_
      have e : (k * ⟨(j : G), hJX' j.2⟩)⁻¹ * (⟨(j : G), hJX' j.2⟩ * k) =
          (k⁻¹ * ⟨(j : G), hJX' j.2⟩⁻¹ * k * ⟨(j : G), hJX' j.2⟩)⁻¹ := by group
      rw [e]
      exact inv_mem ho
    have ht : (Open.fusionZStar ↥J).index = (center ↥K).index := by
      have h1 := htype Kt hKtX hmove
      have h2 : Nat.card (↥Kt ⧸ Open.fusionZStar ↥Kt) = Nat.card (↥K0 ⧸ Open.fusionZStar ↥K0) :=
        Nat.card_congr (Sol78.fusionZStarQuotCongr
          (K0.equivMapOfInjective X.subtype X.subtype_injective)).symm.toEquiv
      have h3 := index_fusionZStar_eq_index_center hK.2 hK0map
      change Nat.card (↥J ⧸ Open.fusionZStar ↥J) = _
      rw [← h1, h2]
      exact h3
    have hrange : ψ.range = ⊤ := by
      have h1 : (Open.fusionZStar ↥J).index ≤ Nat.card ψ.range := by
        rw [← index_ker]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          (index_dvd_of_le hleZ)
      apply eq_top_of_card_eq
      apply le_antisymm (card_le_of_le le_top |>.trans (by rw [card_top]))
      rw [hQcard, ← ht]
      exact h1
    intro k hk
    obtain ⟨j, hj⟩ : φ ⟨k, hKE hk⟩ ∈ ψ.range := hrange ▸ mem_top _
    refine ⟨ρ j, ⟨j, rfl⟩, fun x hx => ?_⟩
    rw [hψ, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf] at hj
    exact (mem_centralizer_iff.mp (mem_inf.mp hj).2 x hx)
  have hT := le_pLayer_centralizer hJp hJE hJg hg2 hfixc
  set Cg := centralizer ({g} : Set (↥X ⧸ O)) with hCg
  set Xs := X ⊓ centralizer ({s} : Set G) with hXs
  have hJXs : J ≤ Xs := le_inf hJX' hJs
  have hFmem : ∀ x : ↥Xs, π (Subgroup.inclusion (inf_le_left : Xs ≤ X) x) ∈ Cg := by
    intro x
    rw [hCg, mem_centralizer_singleton_iff, hg, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2)
  let F : ↥Xs →* ↥Cg := (π.comp (Subgroup.inclusion (inf_le_left : Xs ≤ X))).codRestrict Cg hFmem
  have hF : ∀ x : ↥Xs, (F x : ↥X ⧸ O) = π ⟨x, (mem_inf.mp x.2).1⟩ := fun _ => rfl
  have hzs : zpowers xs = (zpowers s).subgroupOf X := by
    rw [← comap_subtype, show zpowers s = (zpowers xs).map X.subtype by
      rw [MonoidHom.map_zpowers]; rfl, comap_map_eq_self_of_injective X.subtype_injective]
  have : Fact (IsPGroup 2 ↥(zpowers xs)) := ⟨by rw [hzs]; exact hs.comap_subtype⟩
  have hFsurj : Function.Surjective F := by
    rintro ⟨c, hc⟩
    have hcz : c ∈ centralizer (((zpowers xs).map π : Subgroup _) : Set (↥X ⧸ O)) := by
      rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure]
      exact hc
    rw [CFSG.centralizer_map_quotient_eq_map_centralizer 2 (zpowers xs) O hOn hOcop] at hcz
    obtain ⟨y, hy, rfl⟩ := hcz
    have hys : (y : G) ∈ centralizer ({s} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := (mem_centralizer_iff.mp hy) xs (mem_zpowers xs)
      exact (congrArg Subtype.val h1).symm
    refine ⟨⟨y, mem_inf.mpr ⟨y.2, hys⟩⟩, Subtype.ext ?_⟩
    rw [hF]
  have hFker : ¬ 2 ∣ Nat.card F.ker := by
    let ι : F.ker →* O :=
      { toFun := fun x => ⟨⟨x, (mem_inf.mp (x : ↥Xs).2).1⟩, by
          have h1 : F x = 1 := x.2
          have h2 := congrArg Subtype.val h1
          rw [hF] at h2
          exact (QuotientGroup.eq_one_iff _).mp h2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun a b h => by
      have h2 : (((ι a : O) : ↥X) : G) = ((ι b : O) : ↥X) :=
        congrArg (fun z : O => ((z : ↥X) : G)) h
      exact Subtype.ext (Subtype.ext h2)
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hOcop
      (h2.trans (Subgroup.card_dvd_of_injective ι hι))
  have hmapL := UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel F hFsurj hFker
  set J2 := J.subgroupOf Xs with hJ2
  have hJ2sup : J2 ≤ pLayer ↥Xs 2 ⊔ F.ker := by
    intro x hx
    rw [← comap_map_eq F (pLayer ↥Xs 2), hmapL, mem_comap]
    have h1 : (F x : ↥X ⧸ O) ∈ Jb := by
      rw [hF]
      exact ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩
    obtain ⟨c, hc, hce⟩ := hT h1
    have : c = F x := Subtype.ext hce
    rw [← this]
    exact hc
  have hJ2res : CatalogueBPrimeJoin.primeResidual 2 ↥J2 = ⊤ := by
    have : Group.IsPerfect ↥J2 :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJXs).symm.toMonoidHom)
        (subgroupOfEquivOfLe hJXs).symm.surjective
    exact primeResidual_two_eq_top this
  have : (pLayer ↥Xs 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hFker' : Nat.Coprime 2 (Nat.card F.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hFker
  have hJ2L : J2 ≤ pLayer ↥Xs 2 := by
    have h1 := LBalance.Quot.range_le_of_range_le_sup hJ2res hFker' J2.subtype
      (by rw [range_subtype]; exact hJ2sup)
    rwa [range_subtype] at h1
  calc J = J2.map Xs.subtype := (map_subgroupOf_eq_of_le hJXs).symm
    _ ≤ twoLayerIn Xs := map_mono hJ2L

end PumpDown

end CFSG.ComponentClassification.Sol76
