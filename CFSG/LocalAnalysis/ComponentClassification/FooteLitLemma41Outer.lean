module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41Inner
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isSolvable_of_le_sup {J P R O : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hPR : P ≤ normalizer (R : Set G)) (hJR : ⁅J, R⁆ ≤ O) (hJO : ¬ J ≤ O)
    (hJPR : J ≤ P ⊔ R) : ¬ Group.IsSolvable P := by
  intro hP
  set M := P ⊔ R with hM
  have hMR : M ≤ normalizer (R : Set G) := sup_le hPR le_normalizer
  have hRM : R ≤ M := le_sup_right
  have : (R.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hRM).mpr hMR
  set π := QuotientGroup.mk' (R.subgroupOf M) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : P ≤ M))) := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) q
    have hm' := hm
    rw [hM, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P R hPR] at hm'
    obtain ⟨p, hp, r, hr, rfl⟩ := hm'
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_left ⟨p, hp⟩ : M)⁻¹ * ⟨p * r, hm⟩ : M) ∈ R.subgroupOf M
    rw [mem_subgroupOf]
    simpa using hr
  have hsol : Group.IsSolvable (↥M ⧸ R.subgroupOf M) :=
    Group.isSolvable_of_surjective hsurj
  have hJM : J ≤ M := hJPR
  set ψ := π.comp (Subgroup.inclusion hJM) with hψ
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hsolr : Group.IsSolvable ψ.range := inferInstance
  have hsub : Subsingleton ψ.range := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) hsolr
  have hJR' : J ≤ R := by
    intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have := Subsingleton.elim (⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : ψ.range) 1
      exact congrArg Subtype.val this
    rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at h1
    exact h1
  apply hJO
  calc J = ⁅J, J⁆ := hJ.symm
    _ ≤ ⁅J, R⁆ := commutator_mono le_rfl hJR'
    _ ≤ O := hJR

omit [Finite G] in
theorem isSolvable_of_le_sup {K P R : Subgroup G} (hPR : P ≤ normalizer (R : Set G))
    (hKPR : K ≤ P ⊔ R) (hP : Group.IsSolvable P) (hKR : Group.IsSolvable ↥(K ⊓ R)) :
    Group.IsSolvable K := by
  set M := P ⊔ R with hM
  have hMR : M ≤ normalizer (R : Set G) := sup_le hPR le_normalizer
  have hRM : R ≤ M := le_sup_right
  have : (R.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hRM).mpr hMR
  set π := QuotientGroup.mk' (R.subgroupOf M) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : P ≤ M))) := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) q
    have hm' := hm
    rw [hM, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right P R hPR] at hm'
    obtain ⟨p, hp, r, hr, rfl⟩ := hm'
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_left ⟨p, hp⟩ : M)⁻¹ * ⟨p * r, hm⟩ : M) ∈ R.subgroupOf M
    rw [mem_subgroupOf]
    simpa using hr
  have hsol : Group.IsSolvable (↥M ⧸ R.subgroupOf M) :=
    Group.isSolvable_of_surjective hsurj
  set ψ := π.comp (Subgroup.inclusion hKPR) with hψ
  have hKRK : K ⊓ R ≤ K := inf_le_left
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hKRK) ψ fun x hx => ?_
  have h1 : ψ x = 1 := hx
  rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at h1
  exact ⟨⟨x, mem_inf.mpr ⟨x.2, h1⟩⟩, rfl⟩

omit [Finite G] in
theorem le_normalizer_of_commutator_le {A R : Subgroup G} (h : ⁅A, R⁆ ≤ R) :
    A ≤ normalizer (R : Set G) := by
  have key : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun a ha r hr => by
    have h1 := h (commutator_mem_commutator ha hr)
    rw [commutatorElement_def] at h1
    have h2 := mul_mem h1 hr
    rwa [inv_mul_cancel_right] at h2
  intro a ha
  rw [mem_normalizer_iff]
  intro r
  refine ⟨key a ha r, fun hr => ?_⟩
  have h1 := key a⁻¹ (inv_mem ha) _ hr
  rwa [show a⁻¹ * (a * r * a⁻¹) * a⁻¹⁻¹ = r by group] at h1

omit [Finite G] in
theorem commutator_sup_le {J A B O : Subgroup G} (hA : ⁅J, A⁆ ≤ O) (hB : ⁅J, B⁆ ≤ O)
    (hAO : A ≤ normalizer (O : Set G)) (hBO : B ≤ normalizer (O : Set G)) :
    ⁅J, A ⊔ B⁆ ≤ O := by
  let S : Subgroup G :=
    { carrier := {g | g ∈ normalizer (O : Set G) ∧ ∀ x ∈ J, ⁅x, g⁆ ∈ O}
      one_mem' := ⟨one_mem _, fun x _ => by rw [commutatorElement_one_right]; exact one_mem O⟩
      mul_mem' := by
        rintro g h ⟨hg, hgJ⟩ ⟨hh, hhJ⟩
        refine ⟨mul_mem hg hh, fun x hx => ?_⟩
        have e1 : ⁅x, g * h⁆ = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact mul_mem (hgJ x hx) ((mem_normalizer_iff.mp hg _).mp (hhJ x hx))
      inv_mem' := by
        rintro g ⟨hg, hgJ⟩
        refine ⟨inv_mem hg, fun x hx => ?_⟩
        have e1 : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact (mem_normalizer_iff.mp (inv_mem hg) _).mp (inv_mem (hgJ x hx)) }
  have hAS : A ≤ S := fun g hg => ⟨hAO hg, fun x hx => hA (commutator_mem_commutator hx hg)⟩
  have hBS : B ≤ S := fun g hg => ⟨hBO hg, fun x hx => hB (commutator_mem_commutator hx hg)⟩
  rw [commutator_le]
  intro x hx g hg
  exact ((sup_le hAS hBS) hg).2 x hx

theorem exists_mul_mem_centralizer_of_involution {O : Subgroup G} (hO : Odd (Nat.card O))
    {b : G} (hb : b * b = 1) (hbO : b ∈ normalizer (O : Set G)) {x : G}
    (hx : (b * x * b)⁻¹ * x⁻¹ * (b * x * b) * x ∈ O) :
    ∃ n ∈ O, x * (b * x * b) * n ∈ centralizer ({b} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hP : IsPGroup 2 (zpowers b) := by
    have h1 : orderOf b ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hb])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hOd : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)
  obtain ⟨n, hn, hyn⟩ := exists_mul_mem_centralizer hP hOd (zpowers_le.mpr hbO)
    (y := x * (b * x * b)) fun u hu => by
      rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers hb hu with h1 | h1
      · rw [h1, one_mul, inv_one, mul_one, inv_mul_cancel]
        exact one_mem O
      · rw [h1, hbinv]
        have e1 : (x * (b * x * b))⁻¹ * (b * (x * (b * x * b)) * b) =
            (b * x * b)⁻¹ * x⁻¹ * (b * x * b) * x := by
          have e2 : b * (x * (b * x * b)) * b = b * x * b * x * (b * b) := by group
          rw [e2, hb, mul_one]
          group
        rw [e1]
        exact hx
  refine ⟨n, hn, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers b)) hyn⟩

omit [Finite G] in
theorem oddBarConj_eq_one_of_mem_coreActionKernel' {L : Subgroup G}
    {g : ↥(normalizer (L : Set G))} (hg : (g : G) ∈ coreActionKernel L) :
    GSThmB.oddBarConj L g = 1 := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [GSThmB.oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have h1 := (inv_mem hg : (g : G)⁻¹ ∈ coreActionKernel L).2 _ y.2
  rw [inv_inv] at h1
  obtain ⟨z, hz, hze⟩ := mem_map.mp (inv_mem h1)
  convert hz using 1
  apply Subtype.ext
  rw [subtype_apply] at hze
  rw [hze]
  simp only [coe_mul, coe_inv]
  group

omit [Finite G] in
theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  have hsZ : s ∈ center S := by
    rw [mem_center_iff]
    intro g
    have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hs) g
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * s = s * g * s⁻¹ * s := by rw [h1]
      _ = s * g := by group
  rw [hZ] at hsZ
  exact hsZ

omit [Finite G] in
theorem isSolvable_comap_conj {J Q : Subgroup G} (hZ : center (J ⧸ pPrimeCore 2 J) = ⊥)
    (hQ : Group.IsSolvable Q) :
    Group.IsSolvable ↥((((Q.subgroupOf (normalizer (J : Set G))).map
      (GSThmB.oddBarConj J)).comap (MulAut.conj : J ⧸ pPrimeCore 2 J →* MulAut _))) := by
  set S := J ⧸ pPrimeCore 2 J
  set N := normalizer (J : Set G)
  set Q' := (Q.subgroupOf N).map (GSThmB.oddBarConj J)
  have hinj := conj_injective_of_center_eq_bot hZ
  have : Group.IsSolvable Q := hQ
  let f : ↥(Q.subgroupOf N) →* ↥Q :=
    { toFun := fun x => ⟨((x : N) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have h1 : ((f x : Q) : G) = ((f y : Q) : G) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  have hQN : Group.IsSolvable ↥(Q.subgroupOf N) := Group.isSolvable_of_isSolvable_injective hf
  have hQ'eq : ((GSThmB.oddBarConj J).comp (Q.subgroupOf N).subtype).range = Q' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hQ' : Group.IsSolvable Q' := by
    rw [← hQ'eq]
    exact Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
  let g : ↥(Q'.comap (MulAut.conj : S →* MulAut S)) →* ↥Q' :=
    { toFun := fun x => ⟨MulAut.conj (x : S), x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hg : Function.Injective g := fun x y h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  exact Group.isSolvable_of_isSolvable_injective hg

theorem isSolvable_eqLocus_of_conjugate_ne {v w b : G} {J K : Subgroup G}
    (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    (hZ : center (J ⧸ pPrimeCore 2 J) = ⊥) (hwC : w ∈ centralizer ({v} : Set G))
    (hww : w * w = 1) (hwJ : conjugate J w ≠ J) (hbN : b ∈ normalizer (J : Set G))
    (hbb : b * b = 1)
    (hKN : centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K : Set G))
    (hwK : w ∈ K) (hKs : Group.IsSolvable ↥(K ⊓ centralizer ({v} : Set G))) :
    Group.IsSolvable ↥(MonoidHom.eqLocus (GSThmB.oddBarConj J ⟨b, hbN⟩).toMonoidHom
      (MonoidHom.id (J ⧸ pPrimeCore 2 J))) := by
  set C := centralizer ({v} : Set G) with hC
  set N := normalizer (J : Set G) with hN
  set ρ := GSThmB.oddBarConj J with hρ
  set Q := K ⊓ C with hQ
  set T := ((Q.subgroupOf N).map ρ).comap (MulAut.conj : J ⧸ pPrimeCore 2 J →* MulAut _) with hT
  have hTs : Group.IsSolvable T := isSolvable_comap_conj hZ hKs
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hJwC : conjugate J w ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJC (conjugate_le_of_mem hJC hwC) hJ
      (isPComponent_conjugate_subgroupOf hwC hJ) hwJ.symm
  have hle : MonoidHom.eqLocus (ρ ⟨b, hbN⟩).toMonoidHom (MonoidHom.id (J ⧸ pPrimeCore 2 J)) ≤
      T := by
    intro r hr
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective r
    have hfix : ρ ⟨b, hbN⟩ (y0 : J ⧸ pPrimeCore 2 J) = y0 := hr
    obtain ⟨x, hxy, hxb⟩ := GSThmB.exists_fixed_lift (L := J) (t := ⟨b, hbN⟩) hbb hfix
    have hxC : (x : G) ∈ C := hJC x.2
    have hxK : (x : G) ∈ normalizer (K : Set G) :=
      hKN (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hxb.symm, hxC⟩)
    set q := ⁅(x : G), w⁆ with hq
    have hqQ : q ∈ Q := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [hq, commutatorElement_def]
        exact mul_mem ((mem_normalizer_iff.mp hxK w).mp hwK) (inv_mem hwK)
      · rw [hq, commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hxC hwC) (inv_mem hxC)) (inv_mem hwC)
    have hwx : w * (x : G)⁻¹ * w⁻¹ ∈ coreActionKernel J := by
      apply hJwC
      have h1 := conj_mem_conjugate (inv_mem x.2) w
      rw [hwinv] at h1 ⊢
      exact h1
    have hxN : (x : G) ∈ N := le_normalizer x.2
    have hwxN : w * (x : G)⁻¹ * w⁻¹ ∈ N := hwx.1
    have hqx : q = (x : G) * (w * (x : G)⁻¹ * w⁻¹) := by
      rw [hq, commutatorElement_def]; group
    have hqN : q ∈ N := by rw [hqx]; exact mul_mem hxN hwxN
    have hρq : ρ ⟨q, hqN⟩ = MulAut.conj ((x : J) : J ⧸ pPrimeCore 2 J) := by
      have e1 : (⟨q, hqN⟩ : N) = ⟨(x : G), hxN⟩ * ⟨w * (x : G)⁻¹ * w⁻¹, hwxN⟩ :=
        Subtype.ext hqx
      rw [e1, map_mul, oddBarConj_eq_conj' x hxN,
        oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨_, hwxN⟩) hwx, mul_one]
    show MulAut.conj ((y0 : J) : J ⧸ pPrimeCore 2 J) ∈ (Q.subgroupOf N).map ρ
    rw [← hxy, ← hρq]
    exact mem_map_of_mem _ (show ((⟨q, hqN⟩ : N) : G) ∈ Q from hqQ)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem oddCoreOfCentralizer_le_coreActionKernel (hLB : FooteLBalanceInput) {v : G}
    (hv : orderOf v = 2) {J : Subgroup G} (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G)))) :
    oddCoreOfCentralizer v ≤ coreActionKernel J := by
  have hON : oddCoreOfCentralizer v ≤ normalizer (J : Set G) := fun x hx =>
    oddCoreOfCentralizer_inf_le_normalizer hLB hv rfl hJC hJ
      (mem_inf.mpr ⟨hx, oddCoreOfCentralizer_le_centralizer v hx⟩)
  refine le_coreActionKernel_of_commutator_le hON hJC ?_
  exact commutator_le_self_of_le_normalizer fun x hx => mem_normalizer_oddCoreOfCentralizer (hJC hx)

theorem exists_lift_commutator {v w b : G} {J K : Subgroup G}
    (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    (hwC : w ∈ centralizer ({v} : Set G)) (hbC : b ∈ centralizer ({v} : Set G))
    (hbb : b * b = 1) (hbJ : conjugate J b ≠ J)
    (hKN : centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K : Set G))
    (hwK : w ∈ K) {x : G} (hx : x ∈ J) :
    ∃ n ∈ oddCoreOfCentralizer v,
      ⁅x * (b⁻¹ * x * b) * n, w⁆ ∈ K ⊓ centralizer ({v} : Set G) := by
  set C := centralizer ({v} : Set G) with hC
  set O := oddCoreOfCentralizer v with hO
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbO : b ∈ normalizer (O : Set G) := mem_normalizer_oddCoreOfCentralizer hbC
  have hyb : b * x * b ∈ conjugate J b := by
    have h1 := conj_mem_conjugate hx b
    rwa [hbinv] at h1
  have hcomm : ⁅J, conjugate J b⁆ ≤ O :=
    commutator_le_oddCoreIn_of_ne ⟨hJC, hJ⟩
      ⟨conjugate_le_of_mem hJC hbC, isPComponent_conjugate_subgroupOf hbC hJ⟩ hbJ.symm
  have hxO : (b * x * b)⁻¹ * x⁻¹ * (b * x * b) * x ∈ O := by
    have h1 := hcomm (commutator_mem_commutator (inv_mem hx) (inv_mem hyb))
    have e1 : ⁅x⁻¹, (b * x * b)⁻¹⁆ = ((b * x * b)⁻¹ * x⁻¹ * (b * x * b) * x)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e1] at h1
    simpa using inv_mem h1
  obtain ⟨n, hn, hhb⟩ := exists_mul_mem_centralizer_of_involution
    (odd_card_oddCoreOfCentralizer v) hbb hbO hxO
  have e1 : x * (b * x * b) * n = x * (b⁻¹ * x * b) * n := by rw [hbinv]
  rw [e1] at hhb
  have hhC : x * (b⁻¹ * x * b) * n ∈ C :=
    mul_mem (mul_mem (hJC hx) (mul_mem (mul_mem (inv_mem hbC) (hJC hx)) hbC))
      (oddCoreOfCentralizer_le_centralizer v hn)
  refine ⟨n, hn, mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hKN (mem_inf.mpr ⟨hhb, hhC⟩)) w).mp hwK)
      (inv_mem hwK)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hhC hwC) (inv_mem hhC)) (inv_mem hwC)

omit [Finite G] in
theorem commutator_lift_eq (x b n w : G) :
    ⁅x * (b⁻¹ * x * b) * n, w⁆ = x * ((b⁻¹ * x * b) * n * (w * n⁻¹ * w⁻¹)) *
      ((b * w⁻¹)⁻¹ * x⁻¹ * (b * w⁻¹)) * (w * x⁻¹ * w⁻¹) := by
  rw [commutatorElement_def]
  group

theorem lift_factors_mem_coreActionKernel (hLB : FooteLBalanceInput) {v w b : G}
    {J : Subgroup G} (hv : orderOf v = 2) (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    (hwC : w ∈ centralizer ({v} : Set G)) (hww : w * w = 1) (hwJ : conjugate J w ≠ J)
    (hbC : b ∈ centralizer ({v} : Set G)) (hbb : b * b = 1) (hbJ : conjugate J b ≠ J)
    {x n : G} (hx : x ∈ J) (hn : n ∈ oddCoreOfCentralizer v) :
    (b⁻¹ * x * b) * n * (w * n⁻¹ * w⁻¹) ∈ coreActionKernel J ∧
      w * x⁻¹ * w⁻¹ ∈ coreActionKernel J := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hOJ := oddCoreOfCentralizer_le_coreActionKernel hLB hv hJC hJ
  have hJbC : conjugate J b ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJC (conjugate_le_of_mem hJC hbC) hJ
      (isPComponent_conjugate_subgroupOf hbC hJ) hbJ.symm
  have hJwC : conjugate J w ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJC (conjugate_le_of_mem hJC hwC) hJ
      (isPComponent_conjugate_subgroupOf hwC hJ) hwJ.symm
  have h1 : b⁻¹ * x * b ∈ conjugate J b := conj_mem_conjugate hx b
  have h2 : w * n⁻¹ * w⁻¹ ∈ oddCoreOfCentralizer v :=
    (mem_normalizer_iff.mp (mem_normalizer_oddCoreOfCentralizer hwC) _).mp (inv_mem hn)
  have h3 : w * x⁻¹ * w⁻¹ ∈ conjugate J w := by
    have h := conj_mem_conjugate (inv_mem hx) w
    rw [hwinv] at h ⊢
    exact h
  exact ⟨mul_mem (mul_mem (hJbC h1) (hOJ hn)) (hOJ h2), hJwC h3⟩

theorem false_of_conjugate_ne_conjugate (hLB : FooteLBalanceInput) {v w b : G}
    {J K : Subgroup G} (hv : orderOf v = 2) (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    [IsSimpleGroup (J ⧸ pPrimeCore 2 J)]
    (hna : ∃ g h : J ⧸ pPrimeCore 2 J, g * h ≠ h * g)
    (hwC : w ∈ centralizer ({v} : Set G)) (hww : w * w = 1) (hwJ : conjugate J w ≠ J)
    (hbC : b ∈ centralizer ({v} : Set G)) (hbb : b * b = 1) (hbJ : conjugate J b ≠ J)
    (hbw : conjugate J b ≠ conjugate J w)
    (hKN : centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K : Set G))
    (hwK : w ∈ K) (hKs : Group.IsSolvable ↥(K ⊓ centralizer ({v} : Set G))) : False := by
  set C := centralizer ({v} : Set G) with hC
  set N := normalizer (J : Set G) with hN
  set ρ := GSThmB.oddBarConj J with hρ
  have hZ : center (J ⧸ pPrimeCore 2 J) = ⊥ := center_eq_bot_of_isSimpleGroup hna
  set T := (((K ⊓ C).subgroupOf N).map ρ).comap
    (MulAut.conj : J ⧸ pPrimeCore 2 J →* MulAut _) with hT
  have hTs : Group.IsSolvable T := isSolvable_comap_conj hZ hKs
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hbwC : b * w⁻¹ ∈ C := mul_mem hbC (inv_mem hwC)
  have hJbw : conjugate J (b * w⁻¹) ≠ J := by
    intro h
    apply hbw
    have h1 : conjugate (conjugate J (b * w⁻¹)) w = conjugate J w := by rw [h]
    rwa [conjugate_conjugate, mul_assoc, inv_mul_cancel, mul_one] at h1
  have hJbwC : conjugate J (b * w⁻¹) ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJC (conjugate_le_of_mem hJC hbwC) hJ
      (isPComponent_conjugate_subgroupOf hbwC hJ) hJbw.symm
  have htop : T = ⊤ := by
    rw [eq_top_iff]
    intro r _
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨n, hn, hq⟩ := exists_lift_commutator hJC hJ hwC hbC hbb hbJ hKN hwK hx
    obtain ⟨hc₁, hc₂⟩ := lift_factors_mem_coreActionKernel hLB hv hJC hJ hwC hww hwJ hbC hbb hbJ
      hx hn
    have hd : (b * w⁻¹)⁻¹ * x⁻¹ * (b * w⁻¹) ∈ coreActionKernel J :=
      hJbwC (conj_mem_conjugate (inv_mem hx) (b * w⁻¹))
    set c := (b⁻¹ * x * b) * n * (w * n⁻¹ * w⁻¹) * ((b * w⁻¹)⁻¹ * x⁻¹ * (b * w⁻¹)) *
      (w * x⁻¹ * w⁻¹) with hc
    have hcK : c ∈ coreActionKernel J := mul_mem (mul_mem hc₁ hd) hc₂
    have hxN : x ∈ N := le_normalizer hx
    have hqe : ⁅x * (b⁻¹ * x * b) * n, w⁆ = x * c := by
      rw [commutator_lift_eq, hc]
      group
    have hqN : x * c ∈ N := mul_mem hxN hcK.1
    have hρq : ρ ⟨x * c, hqN⟩ = MulAut.conj ((⟨x, hx⟩ : J) : J ⧸ pPrimeCore 2 J) := by
      have e1 : (⟨x * c, hqN⟩ : N) = ⟨x, hxN⟩ * ⟨c, hcK.1⟩ := rfl
      rw [e1, map_mul, oddBarConj_eq_conj' ⟨x, hx⟩ hxN,
        oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨c, hcK.1⟩) hcK, mul_one]
    show MulAut.conj ((⟨x, hx⟩ : J) : J ⧸ pPrimeCore 2 J) ∈ ((K ⊓ C).subgroupOf N).map ρ
    rw [← hρq]
    refine mem_map_of_mem _ ?_
    show x * c ∈ K ⊓ C
    rw [← hqe]
    exact hq
  have hJs : Group.IsSolvable (J ⧸ pPrimeCore 2 J) := by
    have e : T ≃* J ⧸ pPrimeCore 2 J := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, h, hgh⟩ := hna
  exact hgh ((IsSimpleGroup.comm_iff_isSolvable.mpr hJs) g h)

theorem false_of_conjugate_eq_conjugate (hLB : FooteLBalanceInput) {v w b : G}
    {J K : Subgroup G} (hv : orderOf v = 2) (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    [IsSimpleGroup (J ⧸ pPrimeCore 2 J)]
    (hna : ∃ g h : J ⧸ pPrimeCore 2 J, g * h ≠ h * g)
    (hwC : w ∈ centralizer ({v} : Set G)) (hww : w * w = 1) (hwJ : conjugate J w ≠ J)
    (hbC : b ∈ centralizer ({v} : Set G)) (hbb : b * b = 1) (hbJ : conjugate J b ≠ J)
    (hbw : conjugate J b = conjugate J w) (hbwK : b * w ∉ coreActionKernel J)
    (hKN : centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K : Set G))
    (hwK : w ∈ K) (hKs : Group.IsSolvable ↥(K ⊓ centralizer ({v} : Set G))) : False := by
  set C := centralizer ({v} : Set G) with hC
  set N := normalizer (J : Set G) with hN
  set ρ := GSThmB.oddBarConj J with hρ
  set S := J ⧸ pPrimeCore 2 J with hS
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  set T := (((K ⊓ C).subgroupOf N).map ρ).comap (MulAut.conj : S →* MulAut S) with hT
  have hTs : Group.IsSolvable T := isSolvable_comap_conj hZ hKs
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  set g := (b * w⁻¹)⁻¹ with hg
  have hJg : conjugate J (b * w⁻¹) = J := by
    rw [← conjugate_conjugate, hbw, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have hbwN : b * w⁻¹ ∈ N := mem_normalizer_of_conjugate_eq hJg
  have hgN : g ∈ N := inv_mem hbwN
  set τ := ρ ⟨g, hgN⟩ with hτ
  have hmem : ∀ s : S, s * (τ s)⁻¹ ∈ T := by
    intro r
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨n, hn, hq⟩ := exists_lift_commutator hJC hJ hwC hbC hbb hbJ hKN hwK hx
    obtain ⟨hc₁, hc₂⟩ := lift_factors_mem_coreActionKernel hLB hv hJC hJ hwC hww hwJ hbC hbb hbJ
      hx hn
    set d := g * x⁻¹ * g⁻¹ with hd
    have hdJ : d ∈ J := (mem_normalizer_iff.mp hgN _).mp (inv_mem hx)
    set c₁ := (b⁻¹ * x * b) * n * (w * n⁻¹ * w⁻¹) with hc₁def
    set c₂ := w * x⁻¹ * w⁻¹ with hc₂def
    have hxN : x ∈ N := le_normalizer hx
    have hdN : d ∈ N := le_normalizer hdJ
    have hqe : ⁅x * (b⁻¹ * x * b) * n, w⁆ = x * c₁ * d * c₂ := by
      rw [commutator_lift_eq, hc₁def, hc₂def, hd, hg]
      group
    have hqN : x * c₁ * d * c₂ ∈ N := mul_mem (mul_mem (mul_mem hxN hc₁.1) hdN) hc₂.1
    have hdρ : ρ ⟨d, hdN⟩ = MulAut.conj ((τ ((⟨x, hx⟩ : J) : S))⁻¹) := by
      rw [oddBarConj_eq_conj' ⟨d, hdJ⟩ hdN, hτ, ← map_inv,
        show ((⟨x, hx⟩ : J) : S)⁻¹ = ((⟨x, hx⟩⁻¹ : J) : S) from rfl, hρ,
        GSThmB.oddBarConj_apply_mk]
      rfl
    have hρq : ρ ⟨x * c₁ * d * c₂, hqN⟩ =
        MulAut.conj (((⟨x, hx⟩ : J) : S) * (τ ((⟨x, hx⟩ : J) : S))⁻¹) := by
      have e1 : (⟨x * c₁ * d * c₂, hqN⟩ : N) =
          ⟨x, hxN⟩ * ⟨c₁, hc₁.1⟩ * ⟨d, hdN⟩ * ⟨c₂, hc₂.1⟩ := rfl
      rw [e1, map_mul, map_mul, map_mul, oddBarConj_eq_conj' ⟨x, hx⟩ hxN,
        oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨c₁, hc₁.1⟩) hc₁,
        oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨c₂, hc₂.1⟩) hc₂, hdρ, mul_one,
        mul_one, map_mul]
    show MulAut.conj (((⟨x, hx⟩ : J) : S) * (τ ((⟨x, hx⟩ : J) : S))⁻¹) ∈
      ((K ⊓ C).subgroupOf N).map ρ
    rw [← hρq]
    refine mem_map_of_mem _ ?_
    show x * c₁ * d * c₂ ∈ K ⊓ C
    rw [← hqe]
    exact hq
  set D := closure (Set.range fun s : S => s * (τ s)⁻¹) with hD
  have hDT : D ≤ T := (closure_le _).mpr (by rintro _ ⟨s, rfl⟩; exact hmem s)
  have hDn : D.Normal := by
    refine ⟨fun r hr y => ?_⟩
    have hle : D ≤ D.comap (MulAut.conj y).toMonoidHom := by
      rw [hD, closure_le]
      rintro _ ⟨s, rfl⟩
      show y * (s * (τ s)⁻¹) * y⁻¹ ∈ D
      have e1 : y * (s * (τ s)⁻¹) * y⁻¹ = (y * s) * (τ (y * s))⁻¹ * (y * (τ y)⁻¹)⁻¹ := by
        rw [map_mul]
        group
      rw [e1]
      exact mul_mem (subset_closure ⟨y * s, rfl⟩) (inv_mem (subset_closure ⟨y, rfl⟩))
    exact hle hr
  rcases hDn.eq_bot_or_eq_top with hbot | htop
  ·
    apply hbwK
    have hτ1 : τ = 1 := by
      ext s
      have h1 : s * (τ s)⁻¹ ∈ D := subset_closure ⟨s, rfl⟩
      rw [hbot, mem_bot, mul_inv_eq_one] at h1
      rw [MulAut.one_apply, ← h1]
    have hgK : g ∈ coreActionKernel J := GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one hτ1
    have h1 := inv_mem hgK
    rwa [hg, inv_inv, hwinv] at h1
  · have hJs : Group.IsSolvable S := by
      have hTt : T = ⊤ := eq_top_iff.mpr (htop ▸ hDT)
      have e : T ≃* S := (MulEquiv.subgroupCongr hTt).trans Subgroup.topEquiv
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    obtain ⟨g', h', hgh⟩ := hna
    exact hgh ((IsSimpleGroup.comm_iff_isSolvable.mpr hJs) g' h')

theorem false_of_conjugate_ne (hLB : FooteLBalanceInput) (hRk : FooteL2RankThree)
    {E : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) {a v w : G} (ha : a ∈ E) (hv : orderOf v = 2)
    (hEv : E ≤ centralizer ({v} : Set G)) (hwC : w ∈ centralizer ({v} : Set G))
    (hww : w * w = 1) {J : Subgroup G} (hJC : J ≤ centralizer ({v} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))))
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hS : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 9 ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hJa : conjugate J a = J) (haJ : a ∉ coreActionKernel J) (hwJ : conjugate J w ≠ J)
    (K : G → Subgroup G)
    (hKN : ∀ b ∈ E, b ≠ 1 → centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (K b : Set G))
    (hwK : ∀ b ∈ E, b ≠ 1 → w ∈ K b)
    (hKs : ∀ b ∈ E, b ≠ 1 → Group.IsSolvable ↥(K b ⊓ centralizer ({v} : Set G))) : False := by
  obtain ⟨p, f, hp, hp2, hf, h9, hL⟩ := hS
  set S := J ⧸ pPrimeCore 2 J with hSdef
  set N := normalizer (J : Set G) with hN
  set ρ := GSThmB.oddBarConj J with hρ
  have : IsSimpleGroup S := isSimpleGroup_of_lieModel_psl_two hL
  have hna : ∃ g h : S, g * h ≠ h * g := exists_mul_ne_mul_of_isQuasisimple hJq
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hSns : ¬ Group.IsSolvable S := fun h => by
    obtain ⟨g, h', hgh⟩ := hna
    exact hgh ((IsSimpleGroup.comm_iff_isSolvable.mpr h) g h')
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← sq]; exact hexp e he
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨x, hx⟩ ⟨y, hy⟩)
  have hEN : E ≤ N := by
    intro b hb
    by_contra hbN
    have hbJ : conjugate J b ≠ J := fun h => hbN (mem_normalizer_of_conjugate_eq h)
    have hb1 : b ≠ 1 := fun h => hbJ (by rw [h, conjugate_one])
    by_cases hbw : conjugate J b = conjugate J w
    · by_cases hbwK : b * w ∈ coreActionKernel J
      · have hab : a * b ∈ E := mul_mem ha hb
        have hJab : conjugate J (a * b) = conjugate J b := by rw [← conjugate_conjugate, hJa]
        have hab1 : a * b ≠ 1 := fun h => hbJ (by rw [← hJab, h, conjugate_one])
        have habb : a * b * (a * b) = 1 := hsq _ hab
        refine false_of_conjugate_eq_conjugate hLB hv hJC hJ hna hwC hww hwJ (hEv hab) habb
          (by rw [hJab]; exact hbJ) (by rw [hJab]; exact hbw) ?_ (hKN _ hab hab1)
          (hwK _ hab hab1) (hKs _ hab hab1)
        intro h
        apply haJ
        have e1 : a = (a * b * w) * (b * w)⁻¹ := by group
        rw [e1]
        exact mul_mem h (inv_mem hbwK)
      · exact false_of_conjugate_eq_conjugate hLB hv hJC hJ hna hwC hww hwJ (hEv hb) (hsq b hb)
          hbJ hbw hbwK (hKN b hb hb1) (hwK b hb hb1) (hKs b hb hb1)
    · exact false_of_conjugate_ne_conjugate hLB hv hJC hJ hna hwC hww hwJ (hEv hb) (hsq b hb)
        hbJ hbw (hKN b hb hb1) (hwK b hb hb1) (hKs b hb hb1)
  have hfix : ∀ b (hb : b ∈ E), b ≠ 1 → Group.IsSolvable ↥(MonoidHom.eqLocus
      (ρ ⟨b, hEN hb⟩).toMonoidHom (MonoidHom.id S)) := fun b hb hb1 =>
    isSolvable_eqLocus_of_conjugate_ne hJC hJ hZ hwC hww hwJ (hEN hb) (hsq b hb) (hKN b hb hb1)
      (hwK b hb hb1) (hKs b hb hb1)
  set φ : ↥E →* MulAut S := ρ.comp (Subgroup.inclusion hEN) with hφ
  by_cases hinj : Function.Injective φ
  ·
    have hcard : Nat.card φ.range = 8 := by
      rw [← h8]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have hsqE : ∀ ψ ∈ φ.range, ψ * ψ = 1 := by
      rintro _ ⟨e, rfl⟩
      rw [← map_mul, show e * e = 1 from Subtype.ext (hsq e e.2), map_one]
    obtain ⟨ψ, ⟨e, rfl⟩, hψ1, hψs⟩ :=
      hRk S p f hp hp2 hf h9 hL φ.range hsqE (by rw [hcard])
    have he1 : (e : G) ≠ 1 := fun h => hψ1 (by
      rw [show e = 1 from Subtype.ext h, map_one])
    exact hψs (hfix e e.2 he1)
  ·
    obtain ⟨e, he⟩ : ∃ e : ↥E, φ e = 1 ∧ e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hinj
      rw [injective_iff_map_eq_one]
      intro e h
      exact hcon e h
    have he1 : (e : G) ≠ 1 := fun h => he.2 (Subtype.ext h)
    have htop : MonoidHom.eqLocus (ρ ⟨e, hEN e.2⟩).toMonoidHom (MonoidHom.id S) = ⊤ := by
      rw [eq_top_iff]
      intro s _
      show (ρ ⟨e, hEN e.2⟩) s = s
      have h1 : ρ ⟨e, hEN e.2⟩ = 1 := he.1
      rw [h1, MulAut.one_apply]
    have h1 := hfix e e.2 he1
    rw [htop] at h1
    apply hSns
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom) Subgroup.topEquiv.surjective

end CFSG.ComponentClassification.FooteLit
