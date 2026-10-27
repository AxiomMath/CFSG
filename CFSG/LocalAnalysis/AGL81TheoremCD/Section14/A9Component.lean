module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.PerfectComponent
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.Vol2.Ch12Sec2Lem25F
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Quasithin.EmptyFaithful.S146D1
import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIGroup
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCard

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

private theorem fitting_eq_bot_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hO3 : CFSG.pCore 3 X = ⊥) :
    CFSG.fittingSubgroup X = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.Fitting_eq_pcore X 3 hO, hO3]

private theorem component_center_eq_bot {X : Type} [Group X] [Finite X]
    (hF : CFSG.fittingSubgroup X = ⊥) {C : Subgroup X} (hC : CFSG.IsComponent C) :
    Subgroup.center C = ⊥ := by
  have hle : Subgroup.map C.subtype (Subgroup.center C) ≤
      Subgroup.map (CFSG.layer X).subtype (Subgroup.center (CFSG.layer X)) :=
    CFSG.LocalCores.center_component_le_center_layer hC
  have hbot : Subgroup.map C.subtype (Subgroup.center C) = ⊥ := by
    refine le_bot_iff.mp (hle.trans ?_)
    calc Subgroup.map (CFSG.layer X).subtype (Subgroup.center (CFSG.layer X))
        ≤ CFSG.fittingSubgroup X := CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := X)
      _ = ⊥ := hF
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center C)
    (f := C.subtype) C.subtype_injective).mp hbot

private theorem exists_orderOf_three_not_mem_centralizer {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) {C : Subgroup X} (hC : CFSG.IsComponent C)
    (hZ : Subgroup.center C = ⊥) :
    ∃ y : X, y ∈ C ∧ orderOf y = 3 ∧ ∃ l ∈ C, y * l ≠ l * y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card C :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.prime_dvd_card_of_isComponent
      Nat.prime_three hO hC
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
  have hyne : y ≠ 1 := by
    intro h
    rw [h] at hyord
    simpa using hyord
  have hnot : y ∉ Subgroup.center C := by
    intro hyc
    rw [hZ, Subgroup.mem_bot] at hyc
    exact hyne hyc
  refine ⟨(y : X), y.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hyord]
  · by_contra h
    push Not at h
    apply hnot
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (h (z : X) z.2).symm

private theorem card_isComponent_le_three {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) :
    Nat.card {C : Subgroup X // CFSG.IsComponent C} ≤ 3 := by
  have hrank' : CFSG.pRank 3 ↥(⊤ : Subgroup X) ≤ 3 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.ncard_isComponent_le_three
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactOmegaNotCentral_holds hX hO hrank'
  change Nat.card ↥({C : Subgroup X | CFSG.IsComponent C} : Set (Subgroup X)) ≤ 3
  rwa [Nat.card_coe_set_eq]

private theorem normal_subgroup_le_ker_of_ne_top {X : Type} [Group X] [Finite X]
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I) {f : ↥I →* alternatingGroup (Fin 9)}
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) {K : Subgroup ↥I}
    (hK : K.Normal) (hKne : K ≠ ⊤) :
    K ≤ f.ker := by
  haveI hperfI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hperf
  have hMnorm : (Subgroup.map f K).Normal := hK.map f hf
  letI : (Subgroup.map f K).Normal := hMnorm
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 9) (by norm_num)
      (N := Subgroup.map f K) with hbot | htop
  · exact (Subgroup.map_eq_bot_iff K).mp hbot
  · exfalso
    have hsup : K ⊔ f.ker = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_sup_of_normal_right]
      have hx : f x ∈ Subgroup.map f K := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
      refine ⟨k, hk, k⁻¹ * x, ?_, ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      · group
    have hqsurj : Function.Surjective
        ((QuotientGroup.mk' K).comp (Subgroup.subtype f.ker)) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
      have hx : x ∈ K ⊔ f.ker := by rw [hsup]; exact Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_right] at hx
      obtain ⟨k, hk, c, hc, hck⟩ := hx
      refine ⟨⟨c, hc⟩, ?_⟩
      change (QuotientGroup.mk' K) c = (QuotientGroup.mk' K) x
      rw [← hck, map_mul]
      have hk1 : (QuotientGroup.mk' K) k = 1 :=
        (QuotientGroup.eq_one_iff k).mpr hk
      rw [hk1, one_mul]
    have hQp : IsPGroup 2 (↥I ⧸ K) :=
      IsPGroup.of_surjective hker _ hqsurj
    haveI hQperf : Group.IsPerfect (↥I ⧸ K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    have hsub : Subsingleton (↥I ⧸ K) :=
      CFSG.Quasithin.H13.C1294.subsingleton_of_perfect_isPGroup hQp
        hQperf.commutator_eq_top
    exact hKne ((QuotientGroup.subsingleton_iff).mp hsub)

theorem inf_eq_bot_of_isPGroup_three_of_a9 {V : Type} [Group V] [Finite V]
    {P I : Subgroup V} (hP : IsPGroup 3 P)
    (hIP : I ≤ Subgroup.normalizer (P : Set V))
    (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f)
    (hK : IsPGroup 2 f.ker) : P ⊓ I = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup ↥I := P.subgroupOf I
  have hQ3 : IsPGroup 3 Q := hP.comap_subtype
  have hQnorm : Q.Normal := by
    refine ⟨fun q hq i => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact ((Subgroup.mem_normalizer_iff.mp (hIP i.2)) (q : V)).mp hq
  have hQmap3 : IsPGroup 3 (Subgroup.map f Q) := hQ3.map f
  haveI hQmapN : (Subgroup.map f Q).Normal := Subgroup.Normal.map hQnorm f hf
  have hQmap_bot : Subgroup.map f Q = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 9)
      (N := Subgroup.map f Q) (by simp) with h | h
    · exact h
    · exfalso
      have h3top : IsPGroup 3 (⊤ : Subgroup (alternatingGroup (Fin 9))) := h ▸ hQmap3
      have h3A : IsPGroup 3 (alternatingGroup (Fin 9)) :=
        IsPGroup.of_equiv h3top (Subgroup.topEquiv)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h3A
      rw [CFSG.LocalAnalysis.RankThreeUC.AGL81C.natCard_alternatingGroup_fin 9 (by norm_num)] at hn
      norm_num at hn
      have h2dvd : 2 ∣ 3 ^ n := by rw [← hn]; norm_num
      have h23 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
      norm_num at h23
  have hQle : Q ≤ f.ker := (Subgroup.map_eq_bot_iff Q).mp hQmap_bot
  have hQ2 : IsPGroup 2 Q := hK.to_le hQle
  have hdisj : Disjoint Q Q := IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q Q hQ3 hQ2
  have hQbot : Q = ⊥ := disjoint_self.mp hdisj
  have hmap := congrArg (Subgroup.map I.subtype) hQbot
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at hmap

theorem exists_elemAbelian_27_disjoint_ker_of_a9 {X : Type} [Group X] [Finite X]
    {I : Subgroup X} {f : ↥I →* alternatingGroup (Fin 9)}
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    ∃ A : Subgroup X, A ≤ I ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧
      A ⊓ Subgroup.map I.subtype f.ker = ⊥ := by
  classical
  let idA9 : alternatingGroup (Fin 9) →* alternatingGroup (Fin 9) := MonoidHom.id _
  obtain ⟨F, hFab, hFcard⟩ :=
    CFSG.SectionRank.alternating_cover_rank_three (n := 9) (by norm_num) idA9
      (fun x => ⟨x, rfl⟩) (by rw [MonoidHom.ker_id]; exact bot_le)
  have hFle : F ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hf]
    exact le_top
  obtain ⟨S, hSI, hScard, hSab, -, hinj⟩ :=
    CFSG.Quasithin.H13.Lem25.exists_elemAbelian_lift f hker hFle hFab hFcard
  refine ⟨S, hSI, hSab, hScard, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxker⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨y, hyker, hyx⟩ := Subgroup.mem_map.mp hxker
  have hyS : (y : X) ∈ S := by
    rw [show (y : X) = x from hyx]
    exact hxS
  have hy1 : y = 1 := hinj y hyS (MonoidHom.mem_ker.mp hyker)
  rw [Subgroup.mem_bot]
  calc x = (y : X) := hyx.symm
    _ = 1 := by rw [hy1]; rfl

private theorem perm_action_ker_eq_top_of_card_le_three {X : Type} [Group X] [Finite X]
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {f : ↥I →* alternatingGroup (Fin 9)} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) {S : Type} [Finite S] (act : ↥I →* Equiv.Perm S)
    (hcard : Nat.card S ≤ 3) : act.ker = ⊤ := by
  by_contra hKne
  have hKle : act.ker ≤ f.ker :=
    normal_subgroup_le_ker_of_ne_top hperf hf hker (inferInstance : act.ker.Normal) hKne
  let fbar : (↥I ⧸ act.ker) →* alternatingGroup (Fin 9) :=
    QuotientGroup.lift act.ker f hKle
  have hfbar : Function.Surjective fbar := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨QuotientGroup.mk' act.ker x, ?_⟩
    exact (QuotientGroup.lift_mk' act.ker (φ := f) hKle x).trans hx
  have hle : Nat.card (alternatingGroup (Fin 9)) ≤ Nat.card (↥I ⧸ act.ker) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_surjective hfbar)
  have hquot : Nat.card (↥I ⧸ act.ker) = Nat.card act.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange act).toEquiv
  have hrange : Nat.card act.range ≤ Nat.card (Equiv.Perm S) :=
    Subgroup.card_le_card_group act.range
  have hperm : Nat.card (Equiv.Perm S) ≤ 6 := by
    rw [Nat.card_perm]
    calc (Nat.card S).factorial ≤ (3).factorial := Nat.factorial_le hcard
      _ = 6 := by norm_num
  have hA9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  omega

private theorem le_normalizer_of_component {X : Type} [Group X] [Finite X]
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {f : ↥I →* alternatingGroup (Fin 9)} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker)
    (hcard : Nat.card {C : Subgroup X // CFSG.IsComponent C} ≤ 3)
    {C : Subgroup X} (hC : CFSG.IsComponent C) :
    I ≤ Subgroup.normalizer (C : Set X) := by
  classical
  let S := {C : Subgroup X // CFSG.IsComponent C}
  letI : MulAction (MulAut X) (Subgroup X) := Subgroup.pointwiseMulAction
  letI : MulAction ↥I (Subgroup X) :=
    MulAction.compHom (Subgroup X) (MulAut.conj.comp I.subtype)
  let act : ↥I →* Equiv.Perm S :=
    { toFun := fun i => Equiv.Perm.subtypePerm (MulAction.toPermHom ↥I (Subgroup X) i)
        (fun A => by
          rw [show (MulAction.toPermHom ↥I (Subgroup X) i) A =
            A.map (MulAut.conj (i : X)).toMonoidHom from rfl]
          refine ⟨fun h => ?_, fun h =>
            CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (i : X)) h⟩
          have hmap : (A.map (MulAut.conj (i : X)).toMonoidHom).map
              ((MulAut.conj (i : X))⁻¹).toMonoidHom = A := by
            rw [Subgroup.map_map]
            have hcomp : ((MulAut.conj (i : X))⁻¹).toMonoidHom.comp
                (MulAut.conj (i : X)).toMonoidHom = MonoidHom.id X := by
              ext x
              exact MulAut.inv_apply_self X (MulAut.conj (i : X)) x
            rw [hcomp, Subgroup.map_id]
          have := CFSG.LocalCores.isComponent_map_mulEquiv
            (K := A.map (MulAut.conj (i : X)).toMonoidHom) (MulAut.conj (i : X))⁻¹ h
          rwa [hmap] at this)
      map_one' := by
        apply Equiv.Perm.ext
        intro A
        apply Subtype.ext
        change ((MulAction.toPermHom ↥I (Subgroup X)) (1 : ↥I)) A.1 = A.1
        rw [map_one]
        rfl
      map_mul' := by
        intro i j
        apply Equiv.Perm.ext
        intro A
        apply Subtype.ext
        change ((MulAction.toPermHom ↥I (Subgroup X)) (i * j)) A.1 =
          ((MulAction.toPermHom ↥I (Subgroup X)) i)
            (((MulAction.toPermHom ↥I (Subgroup X)) j) A.1)
        rw [map_mul]
        rfl }
  have hKtop : act.ker = ⊤ := perm_action_ker_eq_top_of_card_le_three hperf hf hker act hcard
  intro i hi
  have hmem : (⟨i, hi⟩ : ↥I) ∈ act.ker := by rw [hKtop]; exact Subgroup.mem_top _
  have hact : act ⟨i, hi⟩ = 1 := MonoidHom.mem_ker.mp hmem
  have hfix : (act ⟨i, hi⟩) ⟨C, hC⟩ = (1 : Equiv.Perm S) ⟨C, hC⟩ :=
    congrArg (fun e : Equiv.Perm S => e ⟨C, hC⟩) hact
  have hmap : C.map (MulAut.conj (i : X)).toMonoidHom = C := by
    have h := congrArg Subtype.val hfix
    rwa [show ((act ⟨i, hi⟩) ⟨C, hC⟩ : Subgroup X) =
      C.map (MulAut.conj (i : X)).toMonoidHom from rfl] at h
  rwa [Subgroup.mem_normalizer_iff_map_conj_eq]

private theorem exists_projection_hom_of_commute {X : Type} [Group X]
    {C D : Subgroup X} (hc : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x)
    (hCD : C ⊓ D = ⊥) :
    ∃ proj : ↥(C ⊔ D) →* ↥C,
      (∀ c : ↥C, proj (Subgroup.inclusion le_sup_left c) = c) ∧
        ∀ x : ↥(C ⊔ D), proj x = 1 → x ∈ D.subgroupOf (C ⊔ D) := by
  let J : Subgroup X := C ⊔ D
  have hCcent : C ≤ Subgroup.centralizer (D : Set X) := by
    intro c hcC
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hc c hcC d hd).symm
  have hCnorm : C ≤ Subgroup.normalizer (D : Set X) :=
    hCcent.trans (Subgroup.centralizer_le_normalizer _)
  have hDnormal : (D.subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hCnorm
  letI : (D.subgroupOf J).Normal := hDnormal
  let q : J →* J ⧸ D.subgroupOf J := QuotientGroup.mk' _
  let φ : C →* J ⧸ D.subgroupOf J := q.comp (Subgroup.inclusion (show C ≤ J from le_sup_left))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hmem := QuotientGroup.eq.mp hxy
    have hD : ((x : X)⁻¹ * (y : X)) ∈ D := Subgroup.mem_subgroupOf.mp hmem
    have hC : ((x : X)⁻¹ * (y : X)) ∈ C := C.mul_mem (C.inv_mem x.2) y.2
    have hbot : ((x : X)⁻¹ * (y : X)) ∈ (⊥ : Subgroup X) := by
      rw [← hCD]
      exact ⟨hC, hD⟩
    have hxy1 : (x : X)⁻¹ * (y : X) = 1 := Subgroup.mem_bot.mp hbot
    apply Subtype.ext
    calc (x : X) = (x : X) * ((x : X)⁻¹ * (y : X)) := by rw [hxy1, mul_one]
      _ = (y : X) := by group
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf J) y
    have hsplit : j ∈ C.subgroupOf J ⊔ D.subgroupOf J := by
      rw [← Subgroup.subgroupOf_sup (show C ≤ J from le_sup_left)
        (show D ≤ J from le_sup_right), Subgroup.subgroupOf_self]
      exact Subgroup.mem_top j
    rw [Subgroup.mem_sup_of_normal_right] at hsplit
    obtain ⟨c, hcC, d, hdD, hcd⟩ := hsplit
    refine ⟨⟨c, hcC⟩, ?_⟩
    change q (Subgroup.inclusion (show C ≤ J from le_sup_left) ⟨c, hcC⟩) = q j
    rw [← hcd, map_mul]
    have hd1 : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hdD
    rw [hd1, mul_one]
    exact congrArg q (Subtype.ext rfl)
  let e : C ≃* J ⧸ D.subgroupOf J := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let proj : J →* C := e.symm.toMonoidHom.comp q
  have hproj : ∀ c : C,
      proj (Subgroup.inclusion (show C ≤ J from le_sup_left) c) = c := by
    intro c
    change e.symm (q (Subgroup.inclusion (show C ≤ J from le_sup_left) c)) = c
    rw [← show e c = q (Subgroup.inclusion (show C ≤ J from le_sup_left) c) from rfl,
      e.symm_apply_apply]
  have hkerD : ∀ x : J, proj x = 1 → x ∈ D.subgroupOf J := by
    intro x hx
    change e.symm (q x) = 1 at hx
    have hq : q x = 1 := by
      have := congrArg e hx
      simpa using this
    exact (QuotientGroup.eq_one_iff x).mp hq
  exact ⟨proj, hproj, hkerD⟩

private theorem exists_injective_hom_of_le_sup_centralizer {X : Type} [Group X]
    {C D A : Subgroup X} (hc : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x)
    (hCD : C ⊓ D = ⊥) (hA : A ≤ C ⊔ D) (hAD : A ⊓ D = ⊥) :
    ∃ f : A →* C, Function.Injective f := by
  obtain ⟨proj, -, hkerD⟩ := exists_projection_hom_of_commute hc hCD
  let f : A →* C := proj.comp (Subgroup.inclusion hA)
  refine ⟨f, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  ext a
  constructor
  · intro ha
    have h1 : proj (Subgroup.inclusion hA a) = 1 := MonoidHom.mem_ker.mp ha
    have hmemD : (a : X) ∈ D :=
      Subgroup.mem_subgroupOf.mp (hkerD (Subgroup.inclusion hA a) h1)
    have hbot : (a : X) ∈ (⊥ : Subgroup X) := by
      rw [← hAD]
      exact ⟨a.2, hmemD⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  · intro ha
    rw [Subgroup.mem_bot] at ha
    rw [MonoidHom.mem_ker, ha]
    exact map_one f

private theorem exists_component_not_centralized {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hO3 : CFSG.pCore 3 X = ⊥)
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {f : ↥I →* alternatingGroup (Fin 9)} (hf : Function.Surjective f) :
    ∃ C : Subgroup X, CFSG.IsComponent C ∧
      ¬ I ≤ Subgroup.centralizer (C : Set X) := by
  classical
  by_contra h
  push Not at h
  have hF : CFSG.fittingSubgroup X = ⊥ := fitting_eq_bot_of_pCore_eq_bot hO hO3
  have hFstar : CFSG.generalizedFitting X = CFSG.layer X := by
    rw [CFSG.generalizedFitting.eq_sup, hF, bot_sup_eq]
  have hIlayer : I ≤ Subgroup.centralizer (CFSG.layer X : Set X) := by
    rw [CFSG.layer.eq_sSup, sSup_eq_iSup']
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun C : {C : Subgroup X // CFSG.IsComponent C} => C.1)
      (fun C => h C.1 C.2)
  have hIgen : I ≤ CFSG.generalizedFitting X := by
    have hcent : I ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
      rwa [hFstar]
    exact hcent.trans (CFSG.centralizer_generalizedFitting_le X)
  have hIcenter : I ≤ Subgroup.map (CFSG.layer X).subtype
      (Subgroup.center (CFSG.layer X)) := by
    intro i hi
    rw [CFSG.LocalCores.mem_map_center_iff]
    refine ⟨?_, hIlayer hi⟩
    rw [← hFstar]
    exact hIgen hi
  have hIbot : I = ⊥ := by
    rw [← le_bot_iff]
    calc I ≤ Subgroup.map (CFSG.layer X).subtype (Subgroup.center (CFSG.layer X)) := hIcenter
      _ ≤ CFSG.fittingSubgroup X := CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := X)
      _ = ⊥ := hF
  haveI hIsub : Subsingleton ↥I := by
    rw [hIbot]
    infer_instance
  have hsubA9 : Subsingleton (alternatingGroup (Fin 9)) :=
    Function.Surjective.subsingleton hf
  have hcard1 : Nat.card (alternatingGroup (Fin 9)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsubA9, inferInstance⟩
  have hA9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  omega

private theorem inf_centralizer_le_ker_of_not_le {X : Type} [Group X] [Finite X]
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {f : ↥I →* alternatingGroup (Fin 9)} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker)
    {C : Subgroup X} (hIY : I ≤ Subgroup.normalizer (C : Set X))
    (hnot : ¬ I ≤ Subgroup.centralizer (C : Set X)) :
    I ⊓ Subgroup.centralizer (C : Set X) ≤ Subgroup.map I.subtype f.ker := by
  let D : Subgroup X := Subgroup.centralizer (C : Set X)
  have hInormD : I ≤ Subgroup.normalizer (D : Set X) :=
    hIY.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer C)
  have hKnormal : ((I ⊓ D).subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer hInormD).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hKne : (I ⊓ D).subgroupOf I ≠ ⊤ := by
    intro htop
    apply hnot
    have hmap := congrArg (Subgroup.map I.subtype) htop
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [← hmap]
    exact inf_le_right
  have hKle := normal_subgroup_le_ker_of_ne_top hperf hf hker hKnormal hKne
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hKle ⟨hx.1, hx.2⟩, rfl⟩

private theorem three_le_pRank_of_component {X : Type} [Group X] [Finite X]
    {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {f : ↥I →* alternatingGroup (Fin 9)} (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker)
    {C : Subgroup X} (hC : CFSG.IsComponent C)
    (hIY : I ≤ Subgroup.normalizer (C : Set X))
    (hnot : ¬ I ≤ Subgroup.centralizer (C : Set X))
    (hZ : Subgroup.center C = ⊥)
    (hIle : I ≤ C ⊔ Subgroup.centralizer (C : Set X)) :
    3 ≤ CFSG.Open.pRank 3 C := by
  let D : Subgroup X := Subgroup.centralizer (C : Set X)
  obtain ⟨A, hAI, hAab, hAcard, hAdisj⟩ := exists_elemAbelian_27_disjoint_ker_of_a9 hf hker
  have hAle : A ≤ C ⊔ D := hAI.trans hIle
  have hID : I ⊓ D ≤ Subgroup.map I.subtype f.ker :=
    inf_centralizer_le_ker_of_not_le hperf hf hker hIY hnot
  have hAdisjD : A ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxI : x ∈ I := hAI hx.1
    have hxker : x ∈ Subgroup.map I.subtype f.ker := hID ⟨hxI, hx.2⟩
    have hxbot : x ∈ A ⊓ Subgroup.map I.subtype f.ker := ⟨hx.1, hxker⟩
    rw [hAdisj] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  have hCD : C ⊓ D = ⊥ := by
    rw [show C ⊓ D = (Subgroup.center C).map C.subtype from
      CFSG.GroupTheory.inf_centralizer_eq_map_center C, hZ, Subgroup.map_bot]
  have hc : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp hy x hx
  obtain ⟨g, hginj⟩ := exists_injective_hom_of_le_sup_centralizer hc hCD hAle hAdisjD
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => hAab.1.1.comm a b
  have hpow : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (hAab.2 (a : X) a.2)
  have hle3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup C) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm hpow hAcard
      g hginj le_top
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) C] at hle3

private theorem eq_of_isComponent_of_three_le_pRank {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hF : CFSG.fittingSubgroup X = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {C : Subgroup X} (hC : CFSG.IsComponent C) (hZ : Subgroup.center C = ⊥)
    (h3 : 3 ≤ CFSG.Open.pRank 3 C) :
    ∀ C' : Subgroup X, CFSG.IsComponent C' → C' = C := by
  intro C' hC'
  by_contra hne
  have hcomm : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    rcases CFSG.LocalCores.distinct_components_commute hC hC' with heq | hbot
    · exact absurd heq.symm hne
    · intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hx) y hy).symm
  have hinf : C ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hcent : x ∈ Subgroup.centralizer (C : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcomm y hy x hx.2
    have hmem : x ∈ C ⊓ Subgroup.centralizer (C : Set X) := ⟨hx.1, hcent⟩
    rw [show C ⊓ Subgroup.centralizer (C : Set X) =
        (Subgroup.center C).map C.subtype from
        CFSG.GroupTheory.inf_centralizer_eq_map_center C, hZ, Subgroup.map_bot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hZ' : Subgroup.center C' = ⊥ := component_center_eq_bot hF hC'
  have hpC' : 1 ≤ CFSG.Open.pRank 3 C' := by
    obtain ⟨y, hyC', hyord, -⟩ :=
      exists_orderOf_three_not_mem_centralizer hO hC' hZ'
    have hEa : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y) :=
      CFSG.Open.isElemAbelian_zpowers (by rw [← hyord, pow_orderOf_eq_one])
    have hcardZp : Nat.card (Subgroup.zpowers y) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hyord, pow_one]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
      (Subgroup.zpowers_le.mpr hyC') hEa hcardZp
  have hsum := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three hcomm hinf
  have hmono : CFSG.Open.pRank 3 (C ⊔ C') ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : C ⊔ C' ≤ ⊤)
  omega

theorem exists_isComponent_of_a9
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    {X : Type} [Group X] [Finite X] (hKX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore 3 X = ⊥) (hO3 : CFSG.pCore 3 X = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) :
    ∃ L : Subgroup X, CFSG.IsComponent L ∧ CFSG.generalizedFitting X = L ∧
      Subgroup.centralizer (L : Set X) = ⊥ ∧ I ≤ L ∧ CFSG.Open.pRank 3 L = 3 := by
  classical
  have hF : CFSG.fittingSubgroup X = ⊥ := fitting_eq_bot_of_pCore_eq_bot hO hO3
  have hcard : Nat.card {C : Subgroup X // CFSG.IsComponent C} ≤ 3 :=
    card_isComponent_le_three hKX hO hrank
  obtain ⟨C, hC, hnot⟩ := exists_component_not_centralized hO hO3 hperf hf
  have hIY : I ≤ Subgroup.normalizer (C : Set X) :=
    le_normalizer_of_component hperf hf hker hcard hC
  have hIle : I ≤ C ⊔ Subgroup.centralizer (C : Set X) :=
    perfect_le_sup_centralizer_of_isComponent h711 hKX hperf hC hIY
  have hZ : Subgroup.center C = ⊥ := component_center_eq_bot hF hC
  have h3 : 3 ≤ CFSG.Open.pRank 3 C :=
    three_le_pRank_of_component hperf hf hker hC hIY hnot hZ hIle
  have huniq : ∀ C' : Subgroup X, CFSG.IsComponent C' → C' = C :=
    eq_of_isComponent_of_three_le_pRank hO hF hrank hC hZ h3
  have hlayer : CFSG.layer X = C := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm
      (sSup_le fun K hK => (huniq K hK).le)
      (le_sSup (show C ∈ {K : Subgroup X | CFSG.IsComponent K} from hC))
  have hFstar : CFSG.generalizedFitting X = C := by
    rw [CFSG.generalizedFitting.eq_sup, hF, hlayer, bot_sup_eq]
  have hcent : Subgroup.centralizer (C : Set X) = ⊥ := by
    rw [← le_bot_iff]
    have hleC : Subgroup.centralizer (C : Set X) ≤ C := by
      rw [← hFstar]
      exact CFSG.centralizer_generalizedFitting_le X
    calc Subgroup.centralizer (C : Set X) ≤ C ⊓ Subgroup.centralizer (C : Set X) :=
          le_inf hleC le_rfl
      _ = (Subgroup.center C).map C.subtype :=
          CFSG.GroupTheory.inf_centralizer_eq_map_center C
      _ = ⊥ := by rw [hZ, Subgroup.map_bot]
  have hIleC : I ≤ C := by
    calc I ≤ C ⊔ Subgroup.centralizer (C : Set X) := hIle
      _ = C ⊔ ⊥ := by rw [hcent]
      _ = C := sup_bot_eq C
  have hpRankC : CFSG.Open.pRank 3 C = 3 := by
    have hle3 : CFSG.Open.pRank 3 C ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : C ≤ ⊤)).trans hrank
    omega
  exact ⟨C, hC, hFstar, hcent, hIleC, hpRankC⟩
