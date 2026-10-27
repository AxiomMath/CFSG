module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

public noncomputable section

namespace CFSG.Wreathed.OriginalSylowNormalizerWitness

open scoped Classical Pointwise IsKleinFour
open CFSG.SignalizerFunctor.Helpers

universe u v

variable {G : Type u} [Group G]

@[expose] def ambientOddCore (H : Subgroup G) : Subgroup G :=
  (CFSG.oddCore H).map H.subtype

@[expose] def ambientSylow {ell : ℕ} (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) : Subgroup G :=
  ((P : Subgroup (CFSG.oddCore H)).map (CFSG.oddCore H).subtype).map H.subtype

theorem ambientOddCore_le (H : Subgroup G) : ambientOddCore H ≤ H :=
  Subgroup.map_subtype_le _

theorem ambientOddCore_odd [Finite G] (H : Subgroup G) :
    Odd (Nat.card (ambientOddCore H)) := by
  rw [ambientOddCore, Subgroup.card_subtype]
  exact CFSG.ComponentClassification.OddCore.odd_card H

theorem ambientOddCore_normalized (H : Subgroup G) :
    H ≤ Subgroup.normalizer (ambientOddCore H : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (ambientOddCore_le H)).mp
  change (((CFSG.oddCore H).map H.subtype).comap H.subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

theorem original_sylow_normalizer_factorization [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) :
    (Subgroup.normalizer (ambientSylow H P : Set G) ⊓ H) ⊔ ambientOddCore H = H := by
  let : Fact ell.Prime := ⟨hell⟩
  let P0 : Subgroup H := (P : Subgroup (CFSG.oddCore H)).map (CFSG.oddCore H).subtype
  have hnormalizer : (Subgroup.normalizer (P0.map H.subtype : Set G)).comap H.subtype =
      Subgroup.normalizer (P0 : Set H) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range
      ((Subgroup.map_subtype_le P0).trans_eq H.range_subtype.symm)]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hfrat := congrArg (Subgroup.map H.subtype) (Sylow.normalizer_sup_eq_top P)
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hfrat
  change (Subgroup.normalizer (P0 : Set H)).map H.subtype ⊔ ambientOddCore H = H at hfrat
  rw [← hnormalizer, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm] at hfrat
  exact hfrat

theorem normal_odd_normalizer_subgroup_le_oddCore
    {N : Type v} [Group N] [Finite N] {ell : ℕ} (hell : ell.Prime)
    (P : Sylow ell (CFSG.oddCore N)) (D : Subgroup N)
    (hDB : D ≤ Subgroup.normalizer
      (((P : Subgroup (CFSG.oddCore N)).map (CFSG.oddCore N).subtype) : Set N))
    (hDnormal : (D.subgroupOf (Subgroup.normalizer
      (((P : Subgroup (CFSG.oddCore N)).map (CFSG.oddCore N).subtype) : Set N))).Normal)
    (hDodd : Odd (Nat.card D)) : D ≤ CFSG.oddCore N := by
  let : Fact ell.Prime := ⟨hell⟩
  let R := CFSG.oddCore N
  let B := Subgroup.normalizer
    (((P : Subgroup (CFSG.oddCore N)).map (CFSG.oddCore N).subtype) : Set N)
  let U := R ⊔ D
  have hBD : B ≤ Subgroup.normalizer (D : Set N) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDB).mp hDnormal
  have hBU : B ≤ Subgroup.normalizer (U : Set N) := by
    exact (le_inf Subgroup.le_normalizer_of_normal hBD).trans
      (Subgroup.inf_normalizer_le_normalizer_sup R D)
  have hRU : R ≤ Subgroup.normalizer (U : Set N) :=
    le_sup_left.trans U.le_normalizer
  have hnormal : U.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← Sylow.normalizer_sup_eq_top P]
    exact sup_le hBU hRU
  have hUodd : Odd (Nat.card U) :=
    CFSG.ComponentClassification.OddCore.odd_card_sup R D
      (CFSG.ComponentClassification.OddCore.odd_card N) hDodd
  have hUR : U ≤ R := le_sSup ⟨hnormal, hUodd⟩
  exact le_sup_right.trans hUR

theorem normal_odd_le_ambientOddCore (D H : Subgroup G) (hDH : D ≤ H)
    (hDnormal : (D.subgroupOf H).Normal) (hDodd : Odd (Nat.card D)) :
    D ≤ ambientOddCore H := by
  have hodd : Odd (Nat.card (D.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
    exact hDodd
  have hcore : D.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hDnormal, hodd⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hcore
  rwa [Subgroup.map_subgroupOf_eq_of_le hDH] at hmap

theorem original_sylow_le_normalizer_oddCore [Finite G]
    {ell : ℕ} (H : Subgroup G) (P : Sylow ell (CFSG.oddCore H)) :
    ambientSylow H P ≤ ambientOddCore
      (Subgroup.normalizer (ambientSylow H P : Set G)) := by
  let A := ambientSylow H P
  have hAR : A ≤ ambientOddCore H := Subgroup.map_mono (Subgroup.map_subtype_le _)
  apply normal_odd_le_ambientOddCore A (Subgroup.normalizer (A : Set G))
    A.le_normalizer (by infer_instance)
  exact (ambientOddCore_odd H).of_dvd_nat (Subgroup.card_dvd_of_le hAR)

theorem original_normalizer_oddCore_intersection [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) :
    ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G)) ⊓ H ≤
      ambientOddCore H := by
  let P0 : Subgroup H := (P : Subgroup (CFSG.oddCore H)).map (CFSG.oddCore H).subtype
  let K := Subgroup.normalizer (ambientSylow H P : Set G)
  let B := Subgroup.normalizer (P0 : Set H)
  let E := ambientOddCore K
  let D := E.comap H.subtype
  have hKB : K.comap H.subtype = B := by
    change (Subgroup.normalizer (P0.map H.subtype : Set G)).comap H.subtype = B
    rw [Subgroup.comap_normalizer_eq_of_le_range
      ((Subgroup.map_subtype_le P0).trans_eq H.range_subtype.symm),
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hDB : D ≤ B := by
    rw [← hKB]
    exact Subgroup.comap_mono (ambientOddCore_le K)
  have hBK : B.map H.subtype ≤ K := Subgroup.le_normalizer_map H.subtype
  have hBD : B ≤ Subgroup.normalizer (D : Set H) :=
    (Subgroup.map_le_iff_le_comap.mp
      (hBK.trans (ambientOddCore_normalized K))).trans
        (Subgroup.le_normalizer_comap H.subtype)
  have hDnormal : (D.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDB).mpr hBD
  have hDodd : Odd (Nat.card D) := by
    apply (ambientOddCore_odd K).of_dvd_nat
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le H.subtype E)
  have hDR : D ≤ CFSG.oddCore H :=
    normal_odd_normalizer_subgroup_le_oddCore hell P D hDB hDnormal hDodd
  have hmap := Subgroup.map_mono (f := H.subtype) hDR
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm] at hmap
  exact hmap


theorem sylow_map_maximal {H : Type v} [Group H] {ell : ℕ}
    (P : Sylow ell H) (f : H →* G) (hf : Function.Injective f)
    (D : Subgroup G) (hD : D ≤ f.range) (hDp : IsPGroup ell D)
    (hPD : (P : Subgroup H).map f ≤ D) : D = (P : Subgroup H).map f := by
  have hDp' : IsPGroup ell (D.comap f) := hDp.comap_of_injective f hf
  have hPD' : (P : Subgroup H) ≤ D.comap f := Subgroup.map_le_iff_le_comap.mp hPD
  have hmax := congrArg (Subgroup.map f) (P.is_maximal' hDp' hPD')
  rwa [Subgroup.map_comap_eq, inf_eq_right.mpr hD] at hmax

theorem original_sylow_maximal {ell : ℕ} (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) (D : Subgroup G)
    (hD : D ≤ ambientOddCore H) (hDp : IsPGroup ell D)
    (hPD : ambientSylow H P ≤ D) : D = ambientSylow H P := by
  let f : CFSG.oddCore H →* G := H.subtype.comp (CFSG.oddCore H).subtype
  have hf : Function.Injective f := H.subtype_injective.comp (CFSG.oddCore H).subtype_injective
  have hr : f.range = ambientOddCore H := by
    change (H.subtype.comp (CFSG.oddCore H).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hPD' : (P : Subgroup (CFSG.oddCore H)).map f ≤ D := by
    simpa only [f, ← Subgroup.map_map, ambientSylow] using hPD
  simpa only [f, ← Subgroup.map_map, ambientSylow] using
    sylow_map_maximal P f hf D (hD.trans_eq hr.symm) hDp hPD'

theorem original_sylow_in_intermediate {ell : ℕ} (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) (D : Subgroup G)
    (hPD : ambientSylow H P ≤ D) (hDR : D ≤ ambientOddCore H) :
    ∃ Q : Sylow ell D, (Q : Subgroup D).map D.subtype = ambientSylow H P := by
  have hAp : IsPGroup ell (ambientSylow H P) :=
    (P.isPGroup'.map (CFSG.oddCore H).subtype).map H.subtype
  have hApD : IsPGroup ell ((ambientSylow H P).subgroupOf D) :=
    hAp.comap_subtype
  obtain ⟨Q, hQ⟩ := hApD.exists_le_sylow
  have hAQ : ambientSylow H P ≤ (Q : Subgroup D).map D.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPD]
    exact Subgroup.map_mono hQ
  exact ⟨Q, original_sylow_maximal H P _
    ((Subgroup.map_subtype_le _).trans hDR) (Q.isPGroup'.map D.subtype) hAQ⟩

theorem original_sylow_in_normalizer_core_intersection [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) :
    ∃ Q : Sylow ell
      ↥(ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G)) ⊓ H),
      (Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G)) ⊓ H).subtype =
          ambientSylow H P := by
  apply original_sylow_in_intermediate H P _
  · exact le_inf (original_sylow_le_normalizer_oddCore H P)
      (Subgroup.map_subtype_le _)
  · exact original_normalizer_oddCore_intersection hell H P

theorem original_sylow_le_every_normalizer_core_sylow [Finite G]
    {ell : ℕ} (H : Subgroup G) (P : Sylow ell (CFSG.oddCore H))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G)))) :
    ambientSylow H P ≤ (Q : Subgroup _).map
      (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G))).subtype := by
  let A := ambientSylow H P
  let K := Subgroup.normalizer (A : Set G)
  let O := ambientOddCore K
  have hAO : A ≤ O := original_sylow_le_normalizer_oddCore H P
  have hOn : O ≤ Subgroup.normalizer (A : Set G) := ambientOddCore_le K
  let _ : (A.subgroupOf O).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hOn
  have hAp : IsPGroup ell A :=
    (P.isPGroup'.map (CFSG.oddCore H).subtype).map H.subtype
  have hAop : IsPGroup ell (A.subgroupOf O) := hAp.comap_subtype
  have hle := hAop.le_sylow_of_normal Q
  change A ≤ (Q : Subgroup O).map O.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hAO]
  exact Subgroup.map_mono hle

theorem original_invariant_normalizer_core_sylow [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H T : Subgroup G) [IsKleinFour T]
    (P : Sylow ell (CFSG.oddCore H))
    (hTP : T ≤ Subgroup.normalizer (ambientSylow H P : Set G)) :
    ∃ Q : Sylow ell (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G))),
      ambientSylow H P ≤ (Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G))).subtype ∧
      T ≤ Subgroup.normalizer (((Q : Subgroup _).map
        (ambientOddCore (Subgroup.normalizer (ambientSylow H P : Set G))).subtype) : Set G) := by
  let K := Subgroup.normalizer (ambientSylow H P : Set G)
  let O := ambientOddCore K
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by
    rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨Q, hQ⟩ := normalized_subgroup_invariant_sylow 2 ell Nat.prime_two hell T O hT2
    (hTP.trans (ambientOddCore_normalized K)) (ambientOddCore_odd K).coprime_two_left
  exact ⟨Q, original_sylow_le_every_normalizer_core_sylow H P Q, hQ⟩

theorem original_core_sylow_centralizer [Finite G]
    {ell : ℕ} (hell : ell.Prime) (x : G)
    (P : Sylow ell (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G)))) :
    ((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype) ⊓
        Subgroup.centralizer ({x} : Set G) =
      ambientSylow (Subgroup.centralizer ({x} : Set G)) P := by
  let H := Subgroup.centralizer ({x} : Set G)
  let A := ambientSylow H P
  let K := Subgroup.normalizer (A : Set G)
  let O := ambientOddCore K
  let B := (Q : Subgroup O).map O.subtype
  apply original_sylow_maximal H P (B ⊓ H)
  · exact (inf_le_inf (Subgroup.map_subtype_le _) le_rfl).trans
      (original_normalizer_oddCore_intersection hell H P)
  · exact (Q.isPGroup'.map O.subtype).to_le inf_le_left
  · exact le_inf (original_sylow_le_every_normalizer_core_sylow H P Q)
      (Subgroup.map_subtype_le _)


theorem odd_automorphism_fixed_times_inverted
    {X : Type u} [Group X] [Finite X] (phi : MulAut X)
    (hphi : Function.Involutive phi) (hcop : Nat.Coprime 2 (Nat.card X)) (g : X) :
    ∃ c i : X, phi c = c ∧ phi i = i⁻¹ ∧ g = c * i := by
  let d : X := (phi g)⁻¹ * g
  obtain ⟨i, hi⟩ :=
    (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).2 d
  change i ^ 2 = d at hi
  have hpd : phi d = d⁻¹ := by
    dsimp [d]
    rw [map_mul, map_inv, hphi]
    group
  have hpi : phi i = i⁻¹ := by
    apply (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).1
    calc
      (phi i) ^ 2 = phi (i ^ 2) := (map_pow phi i 2).symm
      _ = phi d := congrArg phi hi
      _ = d⁻¹ := hpd
      _ = (i⁻¹) ^ 2 := by rw [← hi, inv_pow]
  have hprod : phi g * i ^ 2 = g := by
    rw [hi]
    dsimp [d]
    group
  have hpg : phi g = g * (i⁻¹) ^ 2 := by
    calc
      phi g = (phi g * i ^ 2) * (i⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = g * (i⁻¹) ^ 2 := by rw [hprod]
  refine ⟨g * i⁻¹, i, ?_, hpi, by group⟩
  rw [map_mul, map_inv, hpi, inv_inv, hpg]
  group

theorem inverted_normalizing_fixed_element_commutes
    {X : Type u} [Group X] [Finite X] (phi : MulAut X)
    (hcop : Nat.Coprime 2 (Nat.card X)) (g y : X)
    (hg : phi g = g) (hy : phi y = y⁻¹)
    (hconj : phi (y⁻¹ * g * y) = y⁻¹ * g * y) : Commute g y := by
  have heq : y * g * y⁻¹ = y⁻¹ * g * y := by
    calc
      y * g * y⁻¹ = phi (y⁻¹ * g * y) := by rw [map_mul, map_mul, map_inv, hy, hg]; group
      _ = y⁻¹ * g * y := hconj
  have hconjsq : g * y ^ 2 * g⁻¹ = y ^ 2 := by
    have hsqcomm : y ^ 2 * g = g * y ^ 2 := by
      calc
        y ^ 2 * g = y * (y * g * y⁻¹) * y := by simp only [pow_two]; group
        _ = y * (y⁻¹ * g * y) * y := by rw [heq]
        _ = g * y ^ 2 := by simp only [pow_two]; group
    calc
      g * y ^ 2 * g⁻¹ = y ^ 2 * g * g⁻¹ := by rw [hsqcomm]
      _ = y ^ 2 := by group
  have hconjy : g * y * g⁻¹ = y := by
    apply (CFSG.GorensteinWalter.sq_bijective_of_coprime_two (G := X) hcop).1
    calc
      (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by simp only [pow_two]; group
      _ = y ^ 2 := hconjsq
  show g * y = y * g
  calc
    g * y = (g * y * g⁻¹) * g := by group
    _ = y * g := by rw [hconjy]


@[expose] def actionCentralizer {A : Type v} {X : Type u} [Group A] [Group X]
    [MulDistribMulAction A X] (a : A) : Subgroup X :=
  CFSG.fixedPointSubgroup (↥(Subgroup.zpowers a)) X

theorem mem_actionCentralizer {A : Type v} {X : Type u} [Group A] [Group X]
    [MulDistribMulAction A X] {a : A} {g : X} :
    g ∈ actionCentralizer a ↔ a • g = g := by
  constructor
  · intro hg
    exact hg (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a)
  · intro hg z
    exact smul_eq_self_of_mem_zpowers z.property hg

theorem actionCentralizer_invariant {A : Type v} {X : Type u} [CommGroup A] [Group X]
    [MulDistribMulAction A X] (a : A) :
    ∀ s : A, ∀ g ∈ actionCentralizer (X := X) a, s • g ∈ actionCentralizer (X := X) a := by
  intro s g hg
  apply (mem_actionCentralizer (a := a) (g := _)).mpr
  calc
    a • (s • g) = (a * s) • g := (mul_smul a s g).symm
    _ = (s * a) • g := by rw [mul_comm a s]
    _ = s • (a • g) := mul_smul s a g
    _ = s • g := congrArg (s • ·) ((mem_actionCentralizer (a := a) (g := g)).mp hg)

theorem four_group_normalizer_has_second_fixed_element
    {A : Type v} {X : Type u} [CommGroup A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    (hcop : Nat.Coprime 2 (Nat.card X)) (hNC : NormalizerCondition X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ g : X, g ∈ Subgroup.normalizer (actionCentralizer (X := X) a : Set X) ∧
        t • g = g ∧ g ∉ actionCentralizer (X := X) a := by
  let F : Subgroup X := actionCentralizer a
  let N := Subgroup.normalizer (F : Set X)
  have hFN : F < N := hNC F (lt_top_iff_ne_top.mpr hF)
  have hFInv := actionCentralizer_invariant (X := X) a
  have hNInv := normalizer_invariant_of_invariant F hFInv
  let _action := invariantSubgroupAction N hNInv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 A) := ⟨IsPGroup.of_card (n := 2) (by
    rw [IsKleinFour.card_four]; norm_num)⟩
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := A) 2
    (hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card N)) IsKleinFour.not_isCyclic
  have hex : ∃ t : A, t ≠ 1 ∧ t ≠ a ∧
      ¬ (actionCentralizer (X := N) t ≤ F.subgroupOf N) := by
    by_contra hn
    push Not at hn
    have hle : (⨆ (s : A) (_ : s ≠ 1),
        CFSG.fixedPointSubgroup (↥(Subgroup.zpowers s)) N) ≤ F.subgroupOf N := by
      refine iSup₂_le ?_
      intro s hs
      by_cases hsa : s = a
      · subst s
        intro g hg
        change (g : X) ∈ F
        apply (mem_actionCentralizer (a := a) (g := _)).mpr
        exact congrArg (fun z : N => (z : X)) ((mem_actionCentralizer (a := a) (g := g)).mp hg)
      · exact hn s hs hsa
    rw [hgen] at hle
    have hNF : N ≤ F := by
      intro g hg
      exact hle (show (⟨g, hg⟩ : N) ∈ (⊤ : Subgroup N) from Subgroup.mem_top _)
    exact (not_le_of_gt hFN) hNF
  obtain ⟨t, ht1, hta, htle⟩ := hex
  obtain ⟨g, hg, hgf⟩ := IsConcreteLE.not_le_iff_exists.mp htle
  have htb : t = b ∨ t = a * b := by
    by_cases ht : t = b
    · exact Or.inl ht
    · exact Or.inr (IsKleinFour.eq_mul_of_ne_all ha hb hab ht1 hta ht)
  refine ⟨t, htb, (g : X), g.property, ?_, hgf⟩
  exact congrArg (fun z : N => (z : X)) ((mem_actionCentralizer (a := t) (g := g)).mp hg)


theorem four_group_odd_normalizer_centralizing_inverted_witness
    {A : Type v} {X : Type u} [CommGroup A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    (hcop : Nat.Coprime 2 (Nat.card X)) (hNC : NormalizerCondition X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, y ≠ 1 ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) ∧
        y ∉ actionCentralizer (X := X) a := by
  let F : Subgroup X := actionCentralizer a
  let N := Subgroup.normalizer (F : Set X)
  obtain ⟨t, ht, g, hgN, htg, hgf⟩ :=
    four_group_normalizer_has_second_fixed_element hcop hNC a b ha hb hab hF
  let R := N ⊓ actionCentralizer (X := X) t
  have hNInv := normalizer_invariant_of_invariant F
    (actionCentralizer_invariant (X := X) a)
  have hRInv : ∀ s : A, ∀ z ∈ R, s • z ∈ R := by
    intro s z hz
    exact ⟨hNInv s z hz.1, actionCentralizer_invariant t s z hz.2⟩
  let _action := invariantSubgroupAction R hRInv
  let phi : MulAut R := MulDistribMulAction.toMulEquiv R a
  have hphi : Function.Involutive phi := by
    intro z
    change a • (a • z) = z
    rw [← mul_smul, IsKleinFour.mul_self, one_smul]
  let gR : R := ⟨g, hgN, (mem_actionCentralizer (a := t) (g := g)).mpr htg⟩
  obtain ⟨c, i, hc, hi, hgci⟩ := odd_automorphism_fixed_times_inverted phi hphi
    (hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card R)) gR
  have hcF : (c : X) ∈ F := by
    apply (mem_actionCentralizer (a := a) (g := _)).mpr
    exact congrArg (fun z : R => (z : X)) hc
  have hiInv : a • (i : X) = (i : X)⁻¹ :=
    congrArg (fun z : R => (z : X)) hi
  have hiNot : (i : X) ∉ F := by
    intro hiF
    apply hgf
    have eqg : g = (c : X) * (i : X) :=
      congrArg (fun z : R => (z : X)) hgci
    rw [eqg]
    exact F.mul_mem hcF hiF
  refine ⟨t, ht, (i : X), ?_, hiInv,
    (mem_actionCentralizer (a := t) (g := _)).mp i.property.2, ?_, hiNot⟩
  · intro hi1
    exact hiNot (hi1 ▸ F.one_mem)
  · intro z hz
    have hconj : (i : X)⁻¹ * z * (i : X) ∈ F :=
      ((Subgroup.mem_normalizer_iff''.mp i.property.1) z).mp hz
    exact (inverted_normalizing_fixed_element_commutes
      (MulDistribMulAction.toMulEquiv X a) hcop z (i : X)
      ((mem_actionCentralizer (a := a) (g := z)).mp hz) hiInv
      ((mem_actionCentralizer (a := a) (g := _)).mp hconj)).symm

theorem four_group_odd_p_group_centralizing_inverted_witness
    {A : Type v} {X : Type u} [Group A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hXp : IsPGroup p X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, y ≠ 1 ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) ∧
        y ∉ actionCentralizer (X := X) a := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Group.IsNilpotent X := hXp.isNilpotent
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card X) := by
    rw [hn]
    exact hpodd.pow.coprime_two_left
  exact four_group_odd_normalizer_centralizing_inverted_witness hcop
    Group.normalizerCondition_of_isNilpotent a b ha hb hab hF


theorem four_group_odd_p_group_prime_order_witness
    {A : Type v} {X : Type u} [Group A] [IsKleinFour A]
    [Group X] [Finite X] [MulDistribMulAction A X]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hXp : IsPGroup p X)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hF : actionCentralizer (X := X) a ≠ ⊤) :
    ∃ t : A, (t = b ∨ t = a * b) ∧
      ∃ y : X, orderOf y = p ∧ a • y = y⁻¹ ∧ t • y = y ∧
        (∀ g ∈ actionCentralizer (X := X) a, Commute y g) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, y, hy1, hya, hyt, hycomm, _⟩ :=
    four_group_odd_p_group_centralizing_inverted_witness hp hpodd hXp a b ha hb hab hF
  let k := orderOf y / p
  refine ⟨t, ht, y ^ k, ?_, ?_, ?_, ?_⟩
  · exact orderOf_pow_orderOf_div (orderOf_pos y).ne' (hXp.dvd_orderOf hy1)
  · rw [smul_pow', hya, inv_pow]
  · rw [smul_pow', hyt]
  · intro g hg
    exact (hycomm g hg).pow_left k

theorem prime_order_inverted_not_in_centralizer
    {G : Type u} [Group G] (x w : G) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hw : orderOf w = p) (hinv : x * w * x⁻¹ = w⁻¹) :
    w ∉ Subgroup.centralizer ({x} : Set G) := by
  intro hcentral
  have hcomm : Commute x w := Subgroup.mem_centralizer_iff.mp hcentral x (by simp)
  have heq : w = w⁻¹ := hcomm.mul_inv_cancel.symm.trans hinv
  have hsq : w ^ 2 = 1 := by
    rw [pow_two]
    calc
      w * w = w * w⁻¹ := congrArg (w * ·) heq
      _ = 1 := mul_inv_cancel w
  have hdiv : p ∣ 2 := hw ▸ (orderOf_dvd_iff_pow_eq_one.mpr hsq)
  have hpeq : p = 2 := Nat.prime_two.eq_one_or_self_of_dvd p hdiv |>.resolve_left hp.ne_one
  have heven : Even p := by rw [hpeq]; exact ⟨1, rfl⟩
  exact (Nat.not_even_iff_odd.mpr hpodd) heven


theorem original_actionCentralizer_eq (T B : Subgroup G)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) (a : T) :
    let _action := conjugationAction T B hTB
    actionCentralizer (X := B) a =
      (B ⊓ Subgroup.centralizer ({(a : G)} : Set G)).subgroupOf B := by
  let _action := conjugationAction T B hTB
  ext g
  rw [mem_actionCentralizer]
  change a • g = g ↔ (g : G) ∈ B ⊓ Subgroup.centralizer ({(a : G)} : Set G)
  constructor
  · intro hfix
    refine ⟨g.property, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hz' : z = (a : G) := Set.mem_singleton_iff.mp hz
    subst z
    have hconj : (a : G) * (g : G) * (a : G)⁻¹ = (g : G) :=
      congrArg (fun z : B => (z : G)) hfix
    calc
      (a : G) * (g : G) = ((a : G) * (g : G) * (a : G)⁻¹) * a := by group
      _ = (g : G) * a := by rw [hconj]
  · intro hg
    apply Subtype.ext
    change (a : G) * (g : G) * (a : G)⁻¹ = (g : G)
    have hcomm : Commute (a : G) (g : G) :=
      Subgroup.mem_centralizer_iff.mp hg.2 a (by simp)
    exact hcomm.mul_inv_cancel

theorem original_nonstationary_sylow_ne
    {ell : ℕ} (x : G)
    (P : Sylow ell (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hnot : ¬ ∃ U : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))),
      (U : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype =
          ambientSylow (Subgroup.centralizer ({x} : Set G)) P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G)))) :
    ((Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype) ≠
        ambientSylow (Subgroup.centralizer ({x} : Set G)) P := by
  intro heq
  exact hnot ⟨Q, heq⟩

theorem original_nonstationary_prime_order_witness [Finite G]
    {ell : ℕ} (hell : ell.Prime) (T : Subgroup G) [IsKleinFour T] (x y : G)
    (helld : ell ∣ Nat.card (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (P : Sylow ell (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hnot : ¬ ∃ U : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))),
      (U : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype =
          ambientSylow (Subgroup.centralizer ({x} : Set G)) P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))))
    (hTQ : T ≤ Subgroup.normalizer (((Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype)
        : Set G)) :
    ∃ t w : G, (t = y ∨ t = x * y) ∧
      w ∈ (Q : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype ∧
      orderOf w = ell ∧ x * w * x⁻¹ = w⁻¹ ∧ t * w * t⁻¹ = w ∧
      w ∈ Subgroup.centralizer
        (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G) := by
  let H := Subgroup.centralizer ({x} : Set G)
  let A := ambientSylow H P
  let O := ambientOddCore (Subgroup.normalizer (A : Set G))
  let B := (Q : Subgroup O).map O.subtype
  let a : T := ⟨x, hxT⟩
  let b : T := ⟨y, hyT⟩
  let _action := conjugationAction T B hTQ
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
  have hF : actionCentralizer (X := B) a ≠ ⊤ := by
    intro htop
    have hFA : actionCentralizer (X := B) a = A.subgroupOf B := by
      rw [original_actionCentralizer_eq T B hTQ a, original_core_sylow_centralizer hell x P Q]
    have hB : B = A := by
      apply le_antisymm
      · intro z hz
        have hm : (⟨z, hz⟩ : B) ∈ A.subgroupOf B := by
          rw [← hFA, htop]
          exact Subgroup.mem_top _
        exact hm
      · exact original_sylow_le_every_normalizer_core_sylow H P Q
    exact original_nonstationary_sylow_ne x P hnot Q hB
  have hellodd : Odd ell :=
    (CFSG.ComponentClassification.OddCore.odd_card H).of_dvd_nat helld
  obtain ⟨t, ht, w, hw, hwa, hwt, hwcomm⟩ :=
    four_group_odd_p_group_prime_order_witness hell hellodd (Q.isPGroup'.map O.subtype)
      a b ha hb hab hF
  refine ⟨(t : G), (w : G), ?_, w.property, ?_, ?_, ?_, ?_⟩
  · rcases ht with ht | ht
    · exact Or.inl (congrArg (fun z : T => (z : G)) ht)
    · exact Or.inr (congrArg (fun z : T => (z : G)) ht)
  · exact (orderOf_injective B.subtype B.subtype_injective w).trans hw
  · exact congrArg (fun z : B => (z : G)) hwa
  · exact congrArg (fun z : B => (z : G)) hwt
  · apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hzB : z ∈ B := original_sylow_le_every_normalizer_core_sylow H P Q hz
    have hzF : (⟨z, hzB⟩ : B) ∈ actionCentralizer (X := B) a := by
      rw [original_actionCentralizer_eq T B hTQ a]
      exact ⟨hzB, Subgroup.map_subtype_le _ hz⟩
    exact (congrArg (fun z : B => (z : G)) (hwcomm ⟨z, hzB⟩ hzF).eq).symm


noncomputable section

@[expose] def internalProductMap {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) :
    P × U →* ↥(P ⊔ U) :=
  ((P.subtype.noncommCoprod U.subtype hcomm).codRestrict (P ⊔ U) fun g =>
    Subgroup.mul_mem_sup g.1.property g.2.property)

theorem internalProductMap_injective {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) (hdis : Disjoint P U) :
    Function.Injective (internalProductMap P U hcomm) := by
  intro a b hab
  apply Subgroup.mul_injective_of_disjoint hdis
  exact congrArg (fun z : ↥(P ⊔ U) => (z : G)) hab

theorem internalProductMap_surjective {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) :
    Function.Surjective (internalProductMap P U hcomm) := by
  intro g
  have hrange : (P.subtype.noncommCoprod U.subtype hcomm).range = P ⊔ U := by
    have h := MonoidHom.noncommCoprod_range P.subtype U.subtype hcomm
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at h
  have hg : (g : G) ∈ (P.subtype.noncommCoprod U.subtype hcomm).range := by
    rw [hrange]
    exact g.property
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, Subtype.ext ha⟩

@[expose] def internalProductEquiv {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) (hdis : Disjoint P U) :
    P × U ≃* ↥(P ⊔ U) :=
  MulEquiv.ofBijective (internalProductMap P U hcomm)
    ⟨internalProductMap_injective P U hcomm hdis, internalProductMap_surjective P U hcomm⟩

theorem internalProduct_card {G : Type u} [Group G] (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ u : U, Commute (P.subtype p) (U.subtype u)) (hdis : Disjoint P U) :
    Nat.card ↥(P ⊔ U) = Nat.card P * Nat.card U := by
  rw [← Nat.card_congr (internalProductEquiv P U hcomm hdis).toEquiv, Nat.card_prod]


end

theorem inverted_zpowers_conj (x w : G) (hinv : x * w * x⁻¹ = w⁻¹)
    (z : G) (hz : z ∈ Subgroup.zpowers w) : x * z * x⁻¹ = z⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  change (MulAut.conj x) (w ^ n) = (w ^ n)⁻¹
  rw [map_zpow]
  change (x * w * x⁻¹) ^ n = (w ^ n)⁻¹
  rw [hinv, inv_zpow]

theorem inverted_zpowers_disjoint_centralizer [Finite G] (x w : G)
    (hodd : Odd (orderOf w)) (hinv : x * w * x⁻¹ = w⁻¹) :
    Disjoint (Subgroup.centralizer ({x} : Set G)) (Subgroup.zpowers w) := by
  apply Subgroup.disjoint_def.mpr
  intro z hzC hzU
  have hzInv := inverted_zpowers_conj x w hinv z hzU
  have hzCom : Commute x z := Subgroup.mem_centralizer_iff.mp hzC x (by simp)
  have heq : z = z⁻¹ := hzCom.mul_inv_cancel.symm.trans hzInv
  have hsq : z ^ 2 = 1 := by
    rw [pow_two]
    calc
      z * z = z⁻¹ * z := congrArg (· * z) heq
      _ = 1 := inv_mul_cancel z
  let zU : Subgroup.zpowers w := ⟨z, hzU⟩
  have hzUsq : zU ^ 2 = 1 := Subtype.ext hsq
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers]
    exact hodd.coprime_two_left
  have hz1 : zU = 1 :=
    CFSG.GorensteinWalter.eq_one_of_sq_eq_one_of_coprime_two hcop hzUsq
  exact congrArg (fun v : Subgroup.zpowers w => (v : G)) hz1

theorem four_group_witness_zpowers_invariant (T : Subgroup G) [IsKleinFour T]
    (x y w t : G) (hxT : x ∈ T) (hyT : y ∈ T)
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (ht : t = y ∨ t = x * y) (hinv : x * w * x⁻¹ = w⁻¹)
    (hfix : t * w * t⁻¹ = w) :
    T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
  let a : T := ⟨x, hxT⟩
  let b : T := ⟨y, hyT⟩
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
  have hxa : x ∈ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * w * x⁻¹) = _
    rw [hinv, Subgroup.zpowers_inv]
  have hta : t ∈ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * w * t⁻¹) = _
    rw [hfix]
  have hya : y ∈ Subgroup.normalizer (Subgroup.zpowers w : Set G) := by
    rcases ht with rfl | rfl
    · exact hta
    · have hm := (Subgroup.normalizer (Subgroup.zpowers w : Set G)).mul_mem
        ((Subgroup.normalizer (Subgroup.zpowers w : Set G)).inv_mem hxa) hta
      simpa only [inv_mul_cancel_left] using hm
  intro g hg
  let c : T := ⟨g, hg⟩
  by_cases hc1 : c = 1
  · have hg1 : g = 1 := congrArg (fun z : T => (z : G)) hc1
    simpa only [hg1] using (Subgroup.normalizer (Subgroup.zpowers w : Set G)).one_mem
  by_cases hca : c = a
  · have hga : g = x := congrArg (fun z : T => (z : G)) hca
    rw [hga]
    exact hxa
  by_cases hcb : c = b
  · have hgb : g = y := congrArg (fun z : T => (z : G)) hcb
    rw [hgb]
    exact hya
  have hc := IsKleinFour.eq_mul_of_ne_all ha hb hab hc1 hca hcb
  have hgc : g = x * y := congrArg (fun z : T => (z : G)) hc
  rw [hgc]
  exact (Subgroup.normalizer (Subgroup.zpowers w : Set G)).mul_mem hxa hya

theorem centralizer_zpowers_commute (P : Subgroup G) (w : G)
    (hcentral : w ∈ Subgroup.centralizer (P : Set G)) :
    ∀ p : P, ∀ z : Subgroup.zpowers w, Commute (P.subtype p) ((Subgroup.zpowers w).subtype z) := by
  intro p z
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.property
  change Commute (p : G) (z : G)
  rw [← hn]
  exact (show Commute (p : G) w from
    Subgroup.mem_centralizer_iff.mp hcentral p p.property).zpow_right n


theorem original_sylow_normalizer_set_product [Finite G]
    {ell : ℕ} (hell : ell.Prime) (H : Subgroup G) (P : Sylow ell (CFSG.oddCore H)) :
    (H : Set G) = (ambientOddCore H : Set G) *
      ((Subgroup.normalizer (ambientSylow H P : Set G) ⊓ H : Subgroup G) : Set G) := by
  let : Fact ell.Prime := ⟨hell⟩
  let B : Subgroup H := Subgroup.normalizer
    (((P : Subgroup (CFSG.oddCore H)).map (CFSG.oddCore H).subtype) : Set H)
  have hfrat : CFSG.oddCore H ⊔ B = ⊤ := by
    rw [sup_comm]
    exact Sylow.normalizer_sup_eq_top P
  apply Set.ext
  intro g
  constructor
  · intro hg
    have hgin : (⟨g, hg⟩ : H) ∈ CFSG.oddCore H ⊔ B := by
      rw [hfrat]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, b, hb, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hgin
    apply Set.mem_mul.mpr
    refine ⟨(r : G), Subgroup.mem_map_of_mem H.subtype hr,
      (b : G), ⟨?_, b.property⟩, ?_⟩
    · exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem H.subtype hb)
    · exact congrArg (fun z : H => (z : G)) heq
  · rintro ⟨r, hr, b, hb, rfl⟩
    exact H.mul_mem (ambientOddCore_le H hr) hb.2

theorem internalProduct_set_eq (P U : Subgroup G)
    (hcomm : ∀ p : P, ∀ z : U, Commute (P.subtype p) (U.subtype z)) :
    ((P ⊔ U : Subgroup G) : Set G) = (P : Set G) * (U : Set G) := by
  apply Set.ext
  intro g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := internalProductMap_surjective P U hcomm (⟨g, hg⟩ : ↥(P ⊔ U))
    exact Set.mem_mul.mpr ⟨a.1, a.1.property, a.2, a.2.property,
      congrArg (fun z : ↥(P ⊔ U) => (z : G)) ha⟩
  · rintro ⟨p, hp, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hp hz

theorem original_nonstationary_internal_direct_product [Finite G]
    {ell : ℕ} (hell : ell.Prime) (T : Subgroup G) [IsKleinFour T] (x y : G)
    (helld : ell ∣ Nat.card (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (P : Sylow ell (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hnot : ¬ ∃ U : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))),
      (U : Subgroup _).map (ambientOddCore (Subgroup.normalizer
        (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype =
          ambientSylow (Subgroup.centralizer ({x} : Set G)) P)
    (Q : Sylow ell (ambientOddCore (Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))))
    (hTQ : T ≤ Subgroup.normalizer (((Q : Subgroup _).map (ambientOddCore
      (Subgroup.normalizer (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G))).subtype)
        : Set G)) :
    let H := Subgroup.centralizer ({x} : Set G)
    let A := ambientSylow H P
    let O := ambientOddCore (Subgroup.normalizer (A : Set G))
    let B := (Q : Subgroup O).map O.subtype
    ∃ t w : G, (t = y ∨ t = x * y) ∧ w ∈ B ∧ orderOf w = ell ∧
      x * w * x⁻¹ = w⁻¹ ∧ t * w * t⁻¹ = w ∧ w ∈ Subgroup.centralizer (A : Set G) ∧
      w ∉ H ∧ T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) ∧
      Disjoint A (Subgroup.zpowers w) ∧ (A ⊔ Subgroup.zpowers w ≤ O) ∧
      (((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
        (A : Set G) * (Subgroup.zpowers w : Set G)) ∧
      Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card A ∧
      ∃ e : A × Subgroup.zpowers w ≃* ↥(A ⊔ Subgroup.zpowers w),
        ∀ p : A, ∀ z : Subgroup.zpowers w, (e (p, z) : G) = (p : G) * (z : G) := by
  let H := Subgroup.centralizer ({x} : Set G)
  let A := ambientSylow H P
  let O := ambientOddCore (Subgroup.normalizer (A : Set G))
  let B := (Q : Subgroup O).map O.subtype
  obtain ⟨t, w, ht, hwB, horder, hinv, hfix, hcentral⟩ :=
    original_nonstationary_prime_order_witness hell T x y helld hxT hyT hx hy hxy P hnot Q hTQ
  have hellodd : Odd ell :=
    (CFSG.ComponentClassification.OddCore.odd_card H).of_dvd_nat helld
  have hAn : A ≤ H := Subgroup.map_subtype_le _
  have hdis : Disjoint A (Subgroup.zpowers w) :=
    (inverted_zpowers_disjoint_centralizer x w (horder ▸ hellodd) hinv).mono_left hAn
  have hcomm := centralizer_zpowers_commute A w hcentral
  have hsup : A ⊔ Subgroup.zpowers w ≤ O := sup_le
    (original_sylow_le_normalizer_oddCore H P)
    ((Subgroup.zpowers_le.mpr hwB).trans (Subgroup.map_subtype_le _))
  refine ⟨t, w, ht, hwB, horder, hinv, hfix, hcentral,
    prime_order_inverted_not_in_centralizer x w hell hellodd horder hinv,
    four_group_witness_zpowers_invariant T x y w t hxT hyT hx hy hxy ht hinv hfix,
    hdis, hsup, internalProduct_set_eq A (Subgroup.zpowers w) hcomm, ?_, ?_⟩
  · rw [internalProduct_card A (Subgroup.zpowers w) hcomm hdis, Nat.card_zpowers, horder,
      Nat.mul_comm]
  · refine ⟨internalProductEquiv A (Subgroup.zpowers w) hcomm hdis, ?_⟩
    intro p z
    rfl


theorem original_four_group_generated_pair (T : Subgroup G) [IsKleinFour T]
    (x y : G) (hxT : x ∈ T) (hyT : y ∈ T) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) :
    T = Subgroup.closure ({x, y} : Set G) := by
  let a : T := ⟨x, hxT⟩
  let b : T := ⟨y, hyT⟩
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : T => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : T => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : T => (z : G)) h)
  apply le_antisymm
  · intro g hg
    let c : T := ⟨g, hg⟩
    by_cases hc1 : c = 1
    · have hg1 : g = 1 := congrArg (fun z : T => (z : G)) hc1
      rw [hg1]
      exact Subgroup.one_mem _
    by_cases hca : c = a
    · have hga : g = x := congrArg (fun z : T => (z : G)) hca
      rw [hga]
      exact Subgroup.subset_closure (by simp)
    by_cases hcb : c = b
    · have hgb : g = y := congrArg (fun z : T => (z : G)) hcb
      rw [hgb]
      exact Subgroup.subset_closure (by simp)
    have hc := IsKleinFour.eq_mul_of_ne_all ha hb hab hc1 hca hcb
    have hgc : g = x * y := congrArg (fun z : T => (z : G)) hc
    rw [hgc]
    exact (Subgroup.closure ({x, y} : Set G)).mul_mem
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le T).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact hxT
    · exact Set.mem_singleton_iff.mp hg ▸ hyT

theorem original_ambientSylow_card {ell : ℕ} (H : Subgroup G)
    (P : Sylow ell (CFSG.oddCore H)) : Nat.card (ambientSylow H P) = Nat.card P := by
  rw [ambientSylow, Subgroup.card_subtype, Subgroup.card_subtype]

theorem original_Sylow_normalizer_core_intersection_and_nonstationary_witness [Finite G]
    {ell : ℕ} (hell : ell.Prime) (T : Subgroup G) [IsKleinFour T] (x y : G)
    (hxT : x ∈ T) (hyT : y ∈ T) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y)
    (helld : ell ∣ Nat.card (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (P : Sylow ell (CFSG.oddCore (Subgroup.centralizer ({x} : Set G))))
    (hTP : T ≤ Subgroup.normalizer
      (ambientSylow (Subgroup.centralizer ({x} : Set G)) P : Set G)) :
    let N := Subgroup.centralizer ({x} : Set G)
    let R := ambientOddCore N
    let A := ambientSylow N P
    let K := Subgroup.normalizer (A : Set G)
    let O := ambientOddCore K
    T = Subgroup.closure ({x, y} : Set G) ∧ A ≤ O ∧
      (N : Set G) = (R : Set G) * ((K ⊓ N : Subgroup G) : Set G) ∧
      O ⊓ N ≤ R ∧ (∃ J : Sylow ell ↥(O ⊓ N), (J : Subgroup _).map (O ⊓ N).subtype = A) ∧
      (∃ Q : Sylow ell O, A ≤ (Q : Subgroup O).map O.subtype ∧
        T ≤ Subgroup.normalizer (((Q : Subgroup O).map O.subtype) : Set G)) ∧
      (∀ Q : Sylow ell O, ((Q : Subgroup O).map O.subtype) ⊓ N = A) ∧
      ((¬ ∃ J : Sylow ell O, (J : Subgroup O).map O.subtype = A) →
        ∀ Q : Sylow ell O,
          T ≤ Subgroup.normalizer (((Q : Subgroup O).map O.subtype) : Set G) →
          ∃ t w : G, (t = y ∨ t = x * y) ∧ w ∈ (Q : Subgroup O).map O.subtype ∧
            orderOf w = ell ∧ x * w * x⁻¹ = w⁻¹ ∧ t * w * t⁻¹ = w ∧
            w ∈ Subgroup.centralizer (A : Set G) ∧ w ∉ N ∧
            T ≤ Subgroup.normalizer (Subgroup.zpowers w : Set G) ∧
            Disjoint A (Subgroup.zpowers w) ∧ A ⊔ Subgroup.zpowers w ≤ O ∧
            (((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
              (A : Set G) * (Subgroup.zpowers w : Set G)) ∧
            Nat.card ↥(A ⊔ Subgroup.zpowers w) = ell * Nat.card P ∧
            ∃ e : A × Subgroup.zpowers w ≃* ↥(A ⊔ Subgroup.zpowers w),
              ∀ p : A, ∀ z : Subgroup.zpowers w, (e (p, z) : G) = (p : G) * (z : G)) := by
  let N := Subgroup.centralizer ({x} : Set G)
  have hx : x ≠ 1 := by
    intro h
    have hi : orderOf x = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hy : y ≠ 1 := by
    intro h
    have hi : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    omega
  refine ⟨original_four_group_generated_pair T x y hxT hyT hx hy hxy,
    original_sylow_le_normalizer_oddCore N P,
    original_sylow_normalizer_set_product hell N P,
    original_normalizer_oddCore_intersection hell N P,
    original_sylow_in_normalizer_core_intersection hell N P,
    original_invariant_normalizer_core_sylow hell N T P hTP,
    (fun Q => original_core_sylow_centralizer hell x P Q), ?_⟩
  intro hnot Q hTQ
  obtain ⟨t, w, ht, hmem, hord, hinv, hfix, hcent, hnotN, hUinv, hdis, hle,
    hprod, hcard, e, he⟩ :=
      original_nonstationary_internal_direct_product hell T x y helld
        hxT hyT hx hy hxy P hnot Q hTQ
  refine ⟨t, w, ht, hmem, hord, hinv, hfix, hcent, hnotN, hUinv, hdis, hle, hprod, ?_, e, he⟩
  rw [original_ambientSylow_card N P] at hcard
  exact hcard

end CFSG.Wreathed.OriginalSylowNormalizerWitness
