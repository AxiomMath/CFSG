module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsAlt
import CFSG.Quasithin.Background.PRankCommuteMod
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup
import CFSG.GroupTheory.SteinbergCBFTFactorization

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseTwo (M H : Subgroup G) : Prop :=
  IsKComp M H (kSub 3 M H) ∧ IsA11Star (kSub 3 M H)

theorem IsA11Star.exists_elemAbelian_le {A : Subgroup G} (hA : IsA11Star A) :
    ∃ F : Subgroup G, F ≤ A ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hA
  obtain ⟨Fbar, hFbar, hFbarCard⟩ :=
    CFSG.SectionRank.alternating_cover_rank_three (n := 11) (by norm_num)
      e.toMonoidHom e.surjective (by
        rw [MonoidHom.ker_eq_bot e.toMonoidHom e.injective]
        exact bot_le)
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥A) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  obtain ⟨S, -, hSelem, hScard⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift
      (N := CFSG.pPrimeCore 3 ↥A) hN hFbar
  refine ⟨S.map A.subtype, Subgroup.map_subtype_le S, hSelem.map A.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hScard, hFbarCard]

@[expose] def a11TwoSetStab (i j : Fin 11) : Subgroup (alternatingGroup (Fin 11)) where
  carrier := {σ | ((σ : Equiv.Perm (Fin 11)) i = i ∧ (σ : Equiv.Perm (Fin 11)) j = j) ∨
                  ((σ : Equiv.Perm (Fin 11)) i = j ∧ (σ : Equiv.Perm (Fin 11)) j = i)}
  one_mem' := by left; simp
  mul_mem' := by
    rintro a b (⟨hai, haj⟩ | ⟨hai, haj⟩) (⟨hbi, hbj⟩ | ⟨hbi, hbj⟩)
    · left
      refine ⟨?_, ?_⟩
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) i = i
        rw [Equiv.Perm.mul_apply, hbi, hai]
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) j = j
        rw [Equiv.Perm.mul_apply, hbj, haj]
    · right
      refine ⟨?_, ?_⟩
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) i = j
        rw [Equiv.Perm.mul_apply, hbi, haj]
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) j = i
        rw [Equiv.Perm.mul_apply, hbj, hai]
    · right
      refine ⟨?_, ?_⟩
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) i = j
        rw [Equiv.Perm.mul_apply, hbi, hai]
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) j = i
        rw [Equiv.Perm.mul_apply, hbj, haj]
    · left
      refine ⟨?_, ?_⟩
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) i = i
        rw [Equiv.Perm.mul_apply, hbi, haj]
      · change ((a : Equiv.Perm (Fin 11)) * (b : Equiv.Perm (Fin 11))) j = j
        rw [Equiv.Perm.mul_apply, hbj, hai]
  inv_mem' := by
    rintro a (⟨hai, haj⟩ | ⟨hai, haj⟩)
    · left
      refine ⟨?_, ?_⟩
      · show ((a : Equiv.Perm (Fin 11))⁻¹) i = i
        rw [show ((a : Equiv.Perm (Fin 11))⁻¹) = (a : Equiv.Perm (Fin 11)).symm from rfl,
          Equiv.symm_apply_eq]
        exact hai.symm
      · show ((a : Equiv.Perm (Fin 11))⁻¹) j = j
        rw [show ((a : Equiv.Perm (Fin 11))⁻¹) = (a : Equiv.Perm (Fin 11)).symm from rfl,
          Equiv.symm_apply_eq]
        exact haj.symm
    · right
      refine ⟨?_, ?_⟩
      · show ((a : Equiv.Perm (Fin 11))⁻¹) i = j
        rw [show ((a : Equiv.Perm (Fin 11))⁻¹) = (a : Equiv.Perm (Fin 11)).symm from rfl,
          Equiv.symm_apply_eq]
        exact haj.symm
      · show ((a : Equiv.Perm (Fin 11))⁻¹) j = i
        rw [show ((a : Equiv.Perm (Fin 11))⁻¹) = (a : Equiv.Perm (Fin 11)).symm from rfl,
          Equiv.symm_apply_eq]
        exact hai.symm

theorem a11TwoSetStab_index {i j : Fin 11} (hij : i ≠ j) :
    (a11TwoSetStab i j).index = 55 := by
  classical
  haveI : MulAction.IsPretransitive (alternatingGroup (Fin 11))
      (Set.powersetCard (Fin 11) 2) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by norm_num)
  let s : Set.powersetCard (Fin 11) 2 :=
    ⟨{i, j}, by simp [Set.powersetCard, Finset.card_pair hij]⟩
  have hstab : MulAction.stabilizer (alternatingGroup (Fin 11)) s = a11TwoSetStab i j := by
    ext σ
    change σ • s = s ↔ _
    constructor
    · intro h
      have h' : (σ : Equiv.Perm (Fin 11)) • ({i, j} : Finset (Fin 11)) = {i, j} :=
        congrArg Subtype.val h
      have hmem : (σ : Equiv.Perm (Fin 11)) i ∈ ({i, j} : Finset (Fin 11)) := by
        rw [← h']
        exact Finset.mem_smul_finset.mpr ⟨i, by simp, rfl⟩
      have hmemj : (σ : Equiv.Perm (Fin 11)) j ∈ ({i, j} : Finset (Fin 11)) := by
        rw [← h']
        exact Finset.mem_smul_finset.mpr ⟨j, by simp, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmemj
      rcases hmem with h1 | h1 <;> rcases hmemj with h2 | h2
      · exact absurd ((σ : Equiv.Perm (Fin 11)).injective (h1.trans h2.symm)) hij
      · left; exact ⟨h1, h2⟩
      · right; exact ⟨h1, h2⟩
      · exact absurd ((σ : Equiv.Perm (Fin 11)).injective (h1.trans h2.symm)) hij
    · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
      · have h' : (σ : Equiv.Perm (Fin 11)) • ({i, j} : Finset (Fin 11)) = {i, j} := by
          rw [Finset.smul_finset_insert, Finset.smul_finset_singleton,
            Equiv.Perm.smul_def, Equiv.Perm.smul_def, hi, hj]
        exact Subtype.ext h'
      · have h' : (σ : Equiv.Perm (Fin 11)) • ({i, j} : Finset (Fin 11)) = {i, j} := by
          rw [Finset.smul_finset_insert, Finset.smul_finset_singleton,
            Equiv.Perm.smul_def, Equiv.Perm.smul_def, hi, hj, Finset.pair_comm]
        exact Subtype.ext h'
  calc (a11TwoSetStab i j).index =
        (MulAction.stabilizer (alternatingGroup (Fin 11)) s).index := by rw [hstab]
    _ = Nat.card (Set.powersetCard (Fin 11) 2) :=
        MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin 11)) s
    _ = 55 := by
        rw [Set.powersetCard.card, Nat.card_fin]
        decide

@[expose] def KFactA11GammaTwoSet : Prop :=
  ∀ F Y : Subgroup (alternatingGroup (Fin 11)), IsElemAbelian 3 F → Nat.card F = 9 →
    (∀ F₀ : Subgroup (alternatingGroup (Fin 11)), F₀ ≤ F → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set _) ≤ Y) →
    Y = ⊤ ∨ ∃ i j : Fin 11, i ≠ j ∧ Y = a11TwoSetStab i j

theorem KFactA11GammaTwoSet.of_mulEquiv {X : Type} [Group X] [Finite X]
    (hKF : KFactA11GammaTwoSet) (e : X ≃* alternatingGroup (Fin 11)) :
    ∀ F Y : Subgroup X, IsElemAbelian 3 F → Nat.card F = 9 →
      (∀ F₀ : Subgroup X, F₀ ≤ F → F₀ ≠ ⊥ →
        Subgroup.normalizer (F₀ : Set X) ≤ Y) →
      Y = ⊤ ∨ ∃ i j : Fin 11, i ≠ j ∧ Y.map e.toMonoidHom = a11TwoSetStab i j := by
  intro F Y hF hFcard hcond
  have hFe : IsElemAbelian 3 (F.map e.toMonoidHom) := hF.map e.toMonoidHom
  have hFce : Nat.card ↥(F.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hFcard]
  have hconde : ∀ F₀' : Subgroup (alternatingGroup (Fin 11)), F₀' ≤ F.map e.toMonoidHom →
      F₀' ≠ ⊥ → Subgroup.normalizer (F₀' : Set (alternatingGroup (Fin 11))) ≤
        Y.map e.toMonoidHom := by
    intro F₀' hF₀' hne'
    let F₀ : Subgroup X := F₀'.map e.symm.toMonoidHom
    have hF₀le : F₀ ≤ F := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy' : (y : alternatingGroup (Fin 11)) ∈ F.map e.toMonoidHom := hF₀' hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
      have hzy' : z = e.symm.toMonoidHom y := by
        rw [← hzy]
        simp
      rwa [show e.symm.toMonoidHom y = z from hzy'.symm]
    have hF₀ne : F₀ ≠ ⊥ := by
      intro hbot
      apply hne'
      rw [← Subgroup.map_bot (f := e.toMonoidHom), ← hbot, Subgroup.map_map]
      congr 1
      ext x
      simp
    have hN := hcond F₀ hF₀le hF₀ne
    have hmap := Subgroup.map_mono (f := e.toMonoidHom) hN
    have hnorm : (Subgroup.normalizer (F₀ : Set X)).map e.toMonoidHom =
        Subgroup.normalizer (F₀.map e.toMonoidHom : Set (alternatingGroup (Fin 11))) :=
      Subgroup.map_normalizer_eq_of_bijective F₀ e.bijective
    have hF₀eq : F₀.map e.toMonoidHom = F₀' := by
      dsimp [F₀]
      rw [Subgroup.map_map]
      convert Subgroup.map_id F₀' using 1
      ext x
      simp
    rwa [hnorm, hF₀eq] at hmap
  rcases hKF (F.map e.toMonoidHom) (Y.map e.toMonoidHom) hFe hFce hconde with
    htop | ⟨i, j, hij, heq⟩
  · left
    by_contra hY
    have hYtop : Y = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [htop, Subgroup.map_top]
      exact (MonoidHom.range_eq_top.mpr e.surjective).symm
    exact hY hYtop
  · exact Or.inr ⟨i, j, hij, heq⟩


theorem S14Choice.caseTwo {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hpre : PreambleTypes M) (hA : ¬ TypeA M H) (hB : TypeB M H) :
    CaseTwo M H ∧ J = kSub 3 M H := by
  have hcase : CaseTwo M H := by
    obtain ⟨p, Q₀, hQ₀, hH⟩ := h.mem
    obtain ⟨-, hfive⟩ := hpre p Q₀ hQ₀ H hH
    rcases hfive with ⟨hcomp, hL | hSL | hA11⟩ | htwo
    · obtain ⟨J, hJcomp, hA11J⟩ := hB
      have hJK : J = kSub 3 M H := hcomp.eq_kSub_of_isKComp_self hJcomp
      have hA11K : IsA11Star (kSub 3 M H) := hJK ▸ hA11J
      have h1 := hL.card_threeStar
      have h2 := hA11K.card_threeStar
      omega
    · exact absurd ⟨kSub 3 M H, hcomp, hSL⟩ hA
    · exact ⟨hcomp, hA11⟩
    · obtain ⟨J₁, J₂, -, hJ₁, -, -, -, hSL₁, -⟩ := htwo
      exact absurd ⟨J₁, hJ₁, hSL₁⟩ hA
  refine ⟨hcase, ?_⟩
  have hK : IsKComp M H (kSub 3 M H) := hcase.1
  have hZ : Subgroup.center (threeStar (kSub 3 M H)) = ⊥ := hcase.2.center_eq_bot
  obtain ⟨H', -, hJ', -⟩ := h.J_star.1
  exact eq_kSub_of_le_of_subnormal hK hZ h.J_comp.1 h.J_comp.2.1 hJ'.three_dvd_card

theorem S14Choice.E_le_kSub {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) :
    E ≤ kSub 3 M H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let KE : Subgroup G := K ⊔ E
  have hKleH : K ≤ H := kSub_le 3 M H
  have hEM : E ≤ M := h.hypCGen.E_le_M
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => conj_mem_kSub (p := 3) (M := M) (H := H) (h.E_le_H he) (hEM he) hx
    · intro hx
      have h1 := conj_mem_kSub (p := 3) (M := M) (H := H)
        (y := e⁻¹) (H.inv_mem (h.E_le_H he)) (M.inv_mem (hEM he)) hx
      have h2 : e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ = x := by group
      rwa [h2] at h1
  have hKEN : KE ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hEN
  have hKEH : KE ≤ H := sup_le hKleH h.E_le_H
  have hOKleK : O ≤ K := Subgroup.map_subtype_le _
  have hOcard : Nat.card O = Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hOKcop : ¬ 3 ∣ Nat.card O := by
    rw [hOcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hKnormO : K ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := G) K
        (CFSG.pPrimeCore 3 ↥K))
  have hKEnormO : KE ≤ Subgroup.normalizer (O : Set G) :=
    hKEN.trans (CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := G) K
      (CFSG.pPrimeCore 3 ↥K))
  let ρ : ↥KE →* MulAut (threeStar K) := (actStar K).comp (Subgroup.inclusion hKEN)
  let D : Subgroup ↥KE := ρ.ker
  let DA : Subgroup G := D.map KE.subtype
  have hDAle : DA ≤ KE := Subgroup.map_subtype_le _
  have hDAK : DA ⊓ K = O := by
    apply le_antisymm
    · rintro x ⟨hxDA, hxK⟩
      obtain ⟨y, hyD, rfl⟩ := Subgroup.mem_map.mp hxDA
      have hρy : ρ y = 1 := hyD
      have hact : actStar K ⟨(y : G), hKEN y.2⟩ = 1 := by
        change actStar K (Subgroup.inclusion hKEN y) = 1 at hρy
        simpa [Subgroup.inclusion] using hρy
      exact (actStar_eq_one_iff_mem_pPrimeCore (J := K) h2.2.center_eq_bot
        ⟨(y : G), hKEN y.2⟩ hxK).mp hact
    · intro x hxO
      have hxK : x ∈ K := hOKleK hxO
      have hxKE : x ∈ KE := Subgroup.mem_sup_left hxK
      have hact : actStar K ⟨x, hKEN hxKE⟩ = 1 :=
        (actStar_eq_one_iff_mem_pPrimeCore (J := K) h2.2.center_eq_bot
          ⟨x, hKEN hxKE⟩ hxK).mpr hxO
      refine ⟨?_, hxK⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxKE⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      simpa [ρ, Subgroup.inclusion] using hact
  let Ksub : Subgroup ↥KE := K.subgroupOf KE
  let Esub : Subgroup ↥KE := E.subgroupOf KE
  have hKDmap : (Ksub ⊓ D).map KE.subtype = DA ⊓ K := by
    apply le_antisymm
    · rintro x ⟨y, ⟨hyK, hyD⟩, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨y, hyD, rfl⟩, Subgroup.mem_subgroupOf.mp hyK⟩
    · rintro x ⟨hxDA, hxK⟩
      have hxKE : x ∈ KE := Subgroup.mem_sup_left hxK
      obtain ⟨y, hyD, hyx⟩ := Subgroup.mem_map.mp hxDA
      have hxy : (⟨x, hxKE⟩ : ↥KE) = y := Subtype.ext hyx.symm
      refine ⟨⟨x, hxKE⟩, ⟨Subgroup.mem_subgroupOf.mpr hxK, ?_⟩, rfl⟩
      rwa [← hxy] at hyD
  have hcardKD : Nat.card ↥(Ksub ⊓ D) = Nat.card ↥O := by
    have h1 : Nat.card ↥((Ksub ⊓ D).map KE.subtype) = Nat.card ↥(Ksub ⊓ D) :=
      Subgroup.card_map_of_injective KE.subtype_injective
    rw [hKDmap, hDAK] at h1
    exact h1.symm
  have hKsubcard : Nat.card ↥Ksub = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ KE)).toEquiv
  have hkerEq : (ρ.domRestrict Ksub).ker = (Ksub ⊓ D).subgroupOf Ksub := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.inf_subgroupOf_right (H := D) (K := Ksub),
      inf_comm]
  have hkerCard : Nat.card ↥((ρ.domRestrict Ksub).ker) = Nat.card ↥(Ksub ⊓ D) := by
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hprodK : Nat.card ↥O * Nat.card ↥(Ksub.map ρ) = Nat.card ↥K := by
    have h := Subgroup.card_ker_mul_card_range (ρ.domRestrict Ksub)
    rw [MonoidHom.domRestrict_range, hkerCard, hcardKD, hKsubcard] at h
    exact h
  have hsubO : O.subgroupOf K = CFSG.pPrimeCore 3 ↥K := by
    change ((CFSG.pPrimeCore 3 ↥K).map K.subtype).comap K.subtype = _
    exact Subgroup.comap_map_eq_self_of_injective
      (H := CFSG.pPrimeCore 3 ↥K) (f := K.subtype) K.subtype_injective
  have hKcard : Nat.card ↥K = Nat.card ↥O * Nat.card (threeStar K) := by
    have h := Subgroup.card_mul_index (O.subgroupOf K)
    rw [Subgroup.index_eq_card] at h
    have hc : Nat.card ↥(O.subgroupOf K) = Nat.card ↥O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKleK).toEquiv
    rw [hc, hsubO] at h
    exact h.symm
  have hKmap : Nat.card ↥(Ksub.map ρ) = Nat.card (threeStar K) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥O))
    calc Nat.card ↥O * Nat.card ↥(Ksub.map ρ) = Nat.card ↥K := hprodK
      _ = Nat.card ↥O * Nat.card (threeStar K) := hKcard
  have hKmapCard : Nat.card ↥(Ksub.map ρ) = 19958400 := by
    rw [hKmap, h2.2.card_threeStar]
  have hrangeDvd : Nat.card ↥ρ.range ∣ Nat.factorial 11 := by
    have hAut : Nat.card (MulAut (threeStar K)) ∣ Nat.factorial 11 := by
      rw [show Nat.card (MulAut (threeStar K)) =
          Nat.card (MulAut (alternatingGroup (Fin 11))) from
        Nat.card_congr (MulAut.congr (Classical.choice h2.2)).toEquiv]
      exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactAutA11_holds
    exact (Subgroup.card_dvd_of_le (H := ρ.range) (K := ⊤) le_top).trans
      (by simpa using hAut)
  have htopSub : Ksub ⊔ Esub = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ KE) (le_sup_right : E ≤ KE)]
    exact Subgroup.subgroupOf_self KE
  have hRangeSup : ρ.range = Ksub.map ρ ⊔ Esub.map ρ := by
    rw [MonoidHom.range_eq_map, ← htopSub, Subgroup.map_sup]
  have hAutCard : Nat.card (MulAut (threeStar K)) = Nat.factorial 11 := by
    rw [show Nat.card (MulAut (threeStar K)) =
        Nat.card (MulAut (alternatingGroup (Fin 11))) from
      Nat.card_congr (MulAut.congr (Classical.choice h2.2)).toEquiv]
    have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
      (by norm_num) (by norm_num)
    have hcard : Nat.card (MulAut (alternatingGroup (Fin 11))) =
        Nat.card (Equiv.Perm (Fin 11)) :=
      (Nat.card_congr (Equiv.ofBijective _ hb)).symm
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hconjKer : (MulAut.conj : threeStar K →* MulAut (threeStar K)).ker =
      Subgroup.center (threeStar K) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hx : g * x * g⁻¹ = x := by
        simpa [MulAut.conj_apply] using congrArg (fun f : MulAut (threeStar K) => f x) h
      have hgx : g * x = x * g := by
        calc g * x = (g * x * g⁻¹) * g := by group
          _ = x * g := by rw [hx]
      exact hgx.symm
    · intro h
      ext x
      rw [MulAut.one_apply, MulAut.conj_apply]
      rw [← h x, mul_assoc, mul_inv_cancel, mul_one]
  let Inn : Subgroup (MulAut (threeStar K)) :=
    (MulAut.conj : threeStar K →* MulAut (threeStar K)).range
  have hInnCard : Nat.card ↥Inn = Nat.card (threeStar K) := by
    have h := Subgroup.card_ker_mul_card_range
      (MulAut.conj : threeStar K →* MulAut (threeStar K))
    rw [hconjKer, h2.2.center_eq_bot, Subgroup.card_bot, one_mul] at h
    exact h
  have hInnCard' : Nat.card ↥Inn = 19958400 := by
    rw [hInnCard, h2.2.card_threeStar]
  have hInnIndex : Inn.index = 2 := by
    have hm := Subgroup.card_mul_index Inn
    rw [hInnCard', hAutCard] at hm
    have hfact : Nat.factorial 11 = 2 * 19958400 := by norm_num [Nat.factorial]
    rw [hfact] at hm
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 19958400) hm
  have hquotCard : Nat.card (MulAut (threeStar K) ⧸ Inn) = 2 := by
    rw [← Subgroup.index_eq_card, hInnIndex]
  have hEmapInn : Esub.map ρ ≤ Inn := by
    rintro α ⟨y, hy, rfl⟩
    have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
    have hy3 : (y : G) ^ 3 = 1 := h.elem.2 (y : G) hyE
    have hy3' : y ^ 3 = 1 := Subtype.ext hy3
    have hρ3 : (ρ y) ^ 3 = 1 := by rw [← map_pow, hy3', map_one]
    have hq3 : (QuotientGroup.mk' Inn (ρ y)) ^ 3 = 1 := by
      rw [← map_pow, hρ3, map_one]
    have hq2 : (QuotientGroup.mk' Inn (ρ y)) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := QuotientGroup.mk' Inn (ρ y))
      rwa [hquotCard] at this
    have hq1 : QuotientGroup.mk' Inn (ρ y) = 1 := by
      calc QuotientGroup.mk' Inn (ρ y) =
          (QuotientGroup.mk' Inn (ρ y)) ^ 3 * ((QuotientGroup.mk' Inn (ρ y)) ^ 2)⁻¹ := by
            group
        _ = 1 := by rw [hq3, hq2, inv_one, mul_one]
    exact (QuotientGroup.eq_one_iff (ρ y)).mp hq1
  have hKmapInn : Ksub.map ρ ≤ Inn := by
    rintro α ⟨k, hk, rfl⟩
    refine ⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
      ⟨(k : G), Subgroup.mem_subgroupOf.mp hk⟩, ?_⟩
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) z
    change (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨(k : G),
        Subgroup.mem_subgroupOf.mp hk⟩) *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) x) *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨(k : G),
          Subgroup.mem_subgroupOf.mp hk⟩)⁻¹ =
      actStar K ⟨(k : G), hKEN k.2⟩ (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) x)
    rw [actStar_mk K ⟨(k : G), hKEN k.2⟩ x]
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext rfl)
  have hRangeInn : ρ.range ≤ Inn := by
    rw [hRangeSup]
    exact sup_le hKmapInn hEmapInn
  have hRangeEq : Ksub.map ρ = ρ.range := by
    have hcard : Nat.card ↥ρ.range ≤ Nat.card ↥(Ksub.map ρ) := by
      calc Nat.card ↥ρ.range ≤ Nat.card ↥Inn :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hRangeInn)
            (Subgroup.inclusion_injective hRangeInn)
        _ = 19958400 := hInnCard'
        _ = Nat.card ↥(Ksub.map ρ) := hKmapCard.symm
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_range ρ Ksub) hcard
  have hKE_eq : KE = K ⊔ DA := by
    apply le_antisymm
    · intro x hx
      have hxρ : ρ ⟨x, hx⟩ ∈ ρ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [← hRangeEq] at hxρ
      obtain ⟨k, hk, hρk⟩ := hxρ
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hkKE : (k : G) ∈ KE := Subgroup.mem_sup_left hkK
      have hmemD : x * (k : G)⁻¹ ∈ DA := by
        refine Subgroup.mem_map.mpr ⟨⟨x * (k : G)⁻¹, KE.mul_mem hx (KE.inv_mem hkKE)⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        have h1 : ρ ⟨x * (k : G)⁻¹, KE.mul_mem hx (KE.inv_mem hkKE)⟩ =
            ρ ⟨x, hx⟩ * (ρ k)⁻¹ := by
          rw [show (⟨x * (k : G)⁻¹, KE.mul_mem hx (KE.inv_mem hkKE)⟩ : ↥KE) =
              ⟨x, hx⟩ * k⁻¹ from Subtype.ext rfl, map_mul, map_inv]
        rw [h1, hρk, mul_inv_cancel]
      have hx_eq : x = (x * (k : G)⁻¹) * (k : G) := by group
      rw [hx_eq]
      exact (K ⊔ DA).mul_mem (Subgroup.mem_sup_right hmemD) (Subgroup.mem_sup_left hkK)
    · exact sup_le le_sup_left hDAle
  have hsupDK : DA ⊔ K = KE := by rw [sup_comm, hKE_eq]
  have hhmul := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := DA) (K := K) (hDAle.trans hKEN)
  have hrel := Subgroup.relIndex_mul_card K KE
  rw [inf_eq_left.mpr (show K ≤ KE from le_sup_left)] at hrel
  have hDcard : Nat.card DA = K.relIndex KE * Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥K))
    calc Nat.card DA * Nat.card K = Nat.card ↥(DA ⊔ K) * Nat.card ↥(DA ⊓ K) := hhmul.symm
      _ = Nat.card KE * Nat.card O := by rw [hsupDK, hDAK]
      _ = (K.relIndex KE * Nat.card K) * Nat.card O := by rw [← hrel]
      _ = (K.relIndex KE * Nat.card O) * Nat.card K := by ring
  by_contra hEnotK
  have hKsubNormal : Ksub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show K ≤ KE from le_sup_left)).mpr hKEN
  have hrel3 : 3 ∣ K.relIndex KE := by
    have hrelTop : Ksub.relIndex ⊤ = K.relIndex KE := by
      simpa using Subgroup.relIndex_subgroupOf (H := K) (K := KE) (L := KE)
        (hKL := le_rfl)
    have hrelEsub : Ksub.relIndex Esub = K.relIndex E := by
      simpa using Subgroup.relIndex_subgroupOf (H := K) (K := E) (L := KE)
        (hKL := le_sup_right)
    have hrelSup : Ksub.relIndex (Ksub ⊔ Esub) = Ksub.relIndex Esub :=
      Subgroup.relIndex_sup_left (H := Esub) (K := Ksub)
    have hrelE : K.relIndex KE = K.relIndex E := by
      rw [← hrelTop, ← htopSub, hrelSup, hrelEsub]
    have hdvd : K.relIndex KE ∣ Nat.card E := by
      rw [hrelE]
      exact Subgroup.relIndex_dvd_card K E
    have hne1 : K.relIndex KE ≠ 1 := by
      intro h1
      exact hEnotK (Subgroup.relIndex_eq_one.mp (by rwa [hrelE] at h1))
    have hdvd9 : K.relIndex KE ∣ 3 ^ 2 := by
      rw [h.card] at hdvd
      simpa [show (9 : ℕ) = 3 ^ 2 from by norm_num] using hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exact absurd (by rw [hj, h0]; simp) hne1
      · exact hpos
    rw [hj]
    exact dvd_pow_self 3 hjpos.ne'
  have hDA3 : 3 ∣ Nat.card DA := by
    rw [hDcard]
    exact dvd_mul_of_dvd_left hrel3 _
  obtain ⟨c, hcorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥DA) 3 hDA3
  have hcGorder : orderOf (c : G) = 3 := by
    simpa using (Subgroup.orderOf_coe c).trans hcorder
  have hcKE : (c : G) ∈ KE := hDAle c.2
  have hc_notK : (c : G) ∉ K := by
    intro hcK
    have hact : actStar K ⟨(c : G), hKEN hcKE⟩ = 1 := by
      obtain ⟨y, hyD, hyc⟩ := Subgroup.mem_map.mp c.2
      have hρy : ρ y = 1 := hyD
      have hρy' : actStar K (Subgroup.inclusion hKEN y) = 1 := by
        simpa [ρ] using hρy
      have heq : (⟨(c : G), hKEN hcKE⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = Subgroup.inclusion hKEN y :=
        (Subtype.ext hyc).symm
      rw [heq]
      exact hρy'
    have hcO : (c : G) ∈ O :=
      (actStar_eq_one_iff_mem_pPrimeCore (J := K) h2.2.center_eq_bot
        ⟨(c : G), hKEN hcKE⟩ hcK).mp hact
    have hcP : (⟨(c : G), hcK⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K := by
      have hsub : (⟨(c : G), hcK⟩ : ↥K) ∈ O.subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hcO
      rwa [hsubO] at hsub
    have hordP : orderOf (⟨(c : G), hcK⟩ : ↥K) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨(c : G), hcK⟩ : ↥K), hcGorder]
    have hordP' : orderOf (⟨⟨(c : G), hcK⟩, hcP⟩ :
        ↥(CFSG.pPrimeCore 3 ↥K)) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨⟨(c : G), hcK⟩, hcP⟩ :
        ↥(CFSG.pPrimeCore 3 ↥K)), hordP]
    have h3P : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) := by
      have h := _root_.orderOf_dvd_natCard
        (x := (⟨⟨(c : G), hcK⟩, hcP⟩ : ↥(CFSG.pPrimeCore 3 ↥K)))
      rwa [hordP'] at h
    exact hOKcop (by rwa [← hOcard] at h3P)
  obtain ⟨F0, hF0leK, hF0elem, hF0card⟩ := h2.2.exists_elemAbelian_le
  have hF0leH : F0 ≤ H := hF0leK.trans hKleH
  have hcH : (c : G) ∈ H := hKEH hcKE
  have hOH : O ≤ H := hOKleK.trans hKleH
  have hF0N : F0 ≤ Subgroup.normalizer (O : Set G) := hF0leK.trans hKnormO
  have hcN : (c : G) ∈ Subgroup.normalizer (O : Set G) := hKEnormO hcKE
  have hc3pow : (c : G) ^ 3 = 1 := by
    rw [← hcGorder]
    exact pow_orderOf_eq_one _
  have hcomm : ⁅F0, Subgroup.zpowers (c : G)⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcjKE : ((c : G) ^ j) ∈ KE := KE.zpow_mem hcKE j
    have hact : actStar K ⟨(c : G) ^ j, hKEN hcjKE⟩ = 1 := by
      obtain ⟨y, hyD, hyc⟩ := Subgroup.mem_map.mp c.2
      have hyDj : y ^ j ∈ D := D.zpow_mem hyD j
      have hρj : ρ (y ^ j) = 1 := hyDj
      have hρj' : actStar K (Subgroup.inclusion hKEN (y ^ j)) = 1 := by
        simpa [ρ] using hρj
      have hyG : (((y ^ j : ↥KE) : G)) = (c : G) ^ j := by
        simpa [Subgroup.coe_zpow] using congrArg (fun z : G => z ^ j) hyc
      have heq : (Subgroup.inclusion hKEN (y ^ j) :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨(c : G) ^ j, hKEN hcjKE⟩ :=
        Subtype.ext hyG
      rw [heq] at hρj'
      exact hρj'
    exact commutator_mem_pPrimeCore_of_actStar_eq_one (J := K)
      ⟨(c : G) ^ j, hKEN hcjKE⟩ ⟨x, hF0leK hx⟩ hact
  have hc_notF : (c : G) ∉ F0 ⊔ O := by
    intro hmem
    exact hc_notK (sup_le hF0leK hOKleK hmem)
  have hrank : 4 ≤ CFSG.Open.pRank 3 H :=
    CFSG.Quasithin.succ_le_pRank_of_commute_mod
      (p := 3) (X := H) (Q := O) (E := F0) (a := 3) (f := (c : G))
      hOKcop hF0N hcN hF0elem hF0card hc3pow hcomm hc_notF hF0leH hcH hOH
  have hle3 := CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen.pRank_le_three_of_isTwoLocal
    h.cstar Nat.prime_three (by norm_num) h.hypCGen.not_mem_sigmaA h.hypCGen.isTwoLocal
  omega


theorem S14Choice.isSylowOf_kSub {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) :
    CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M H) := by
  have hsup : kSub 3 M H ⊔ E = kSub 3 M H := sup_eq_left.mpr (h.E_le_kSub h2)
  simpa [hsup] using h.sylow

theorem S14Choice.kSub_sup_inf_eq {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) :
    kSub 3 M H ⊔ (H ⊓ M) = H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPmap⟩ := h.isSylowOf_kSub h2
  have hKleH : kSub 3 M H ≤ H := kSub_le 3 M H
  have hCnormal : ((kSub 3 M H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleH).mpr (hK 3 E H h.hypCGen)
  have hfr := CFSG.BenderSuzuki.normal_sup_normalizerIn_eq_of_sylow
    (X := G) (M := H) (C := kSub 3 M H) (Y := Q) (p := 3)
    hKleH hCnormal P hPmap
  have hQleM : Q ≤ M := h.Q_le_M hU
  have hQnormM : Subgroup.normalizer (Q : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne.normalizer_le h.maxLocal
      (hU 3 E H h.hypCGen) h.hypCGen.E_le_M h.elem h.card h.gamma h.E_le_Q hQleM
  have hnin : CFSG.BenderSuzuki.normalizerIn H Q ≤ H ⊓ M := by
    change H ⊓ Subgroup.normalizer (Q : Set G) ≤ H ⊓ M
    exact inf_le_inf le_rfl hQnormM
  apply le_antisymm
  · exact sup_le hKleH inf_le_left
  · calc H = kSub 3 M H ⊔ CFSG.BenderSuzuki.normalizerIn H Q := hfr.symm
      _ ≤ kSub 3 M H ⊔ (H ⊓ M) := sup_le_sup le_rfl hnin

theorem S14Choice.exists_twoSet {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) :
    ∃ (e : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11)) (i j : Fin 11), i ≠ j ∧
      ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map e.toMonoidHom) =
        a11TwoSetStab i j := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  have hKleH : K ≤ H := kSub_le 3 M H
  have hOKleK : O ≤ K := Subgroup.map_subtype_le _
  have hEM : E ≤ M := h.hypCGen.E_le_M
  have hEK : E ≤ K := h.E_le_kSub h2
  have hOKM : O ≤ M := h.hypCGen.pPrimeCore_map_le hK
  have hEnotM : ¬ K ≤ M := not_kSub_le_of_not_pLayerIn_le (hL 3 E H h.hypCGen)
  have hOKcop : ¬ 3 ∣ Nat.card O := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hEdisjO : E ⊓ O = ⊥ := by
    have hcop : Nat.Coprime (Nat.card E) (Nat.card O) := by
      rw [h.card]
      exact Nat.Coprime.pow_left 2
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hOKcop)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  let f : ↥E →* threeStar K := π.comp (Subgroup.inclusion hEK)
  have hfker : f.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxP : (⟨(x : G), hEK x.2⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
        (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K)
          (x := (⟨(x : G), hEK x.2⟩ : ↥K))).mp hx
      have hxO : (x : G) ∈ O := Subgroup.mem_map_of_mem K.subtype hxP
      have hxbot : (x : G) ∈ E ⊓ O := ⟨x.2, hxO⟩
      rw [hEdisjO, Subgroup.mem_bot] at hxbot
      exact Subtype.ext hxbot
    · intro hx
      rw [hx]
      simp
  let Fbar : Subgroup (threeStar K) := f.range
  have hFbarElem : IsElemAbelian 3 Fbar := by
    have h1 : IsElemAbelian 3 (E.subgroupOf K) := h.elem.subgroupOf K
    have h2 := h1.map π
    convert h2 using 1
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), hEK x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(y : G), hy⟩, ?_⟩
      rfl
  have hFbarCard : Nat.card Fbar = 9 := by
    have hmul := Subgroup.card_ker_mul_card_range f
    rw [hfker, Subgroup.card_bot, one_mul, h.card] at hmul
    exact hmul

  let Y : Subgroup (threeStar K) := ((K ⊓ M).subgroupOf K).map π
  have hYne : Y ≠ ⊤ := by
    intro hY
    change ((K ⊓ M).subgroupOf K).map π = ⊤ at hY
    rw [inf_comm, Subgroup.inf_subgroupOf_right] at hY
    exact hEnotM (le_of_map_subgroupOf_eq_top (K := K) hOKM hY)
  have hYcond : ∀ F₀ : Subgroup (threeStar K), F₀ ≤ Fbar → F₀ ≠ ⊥ →
      Subgroup.normalizer (F₀ : Set (threeStar K)) ≤ Y := by
    intro F₀ hF₀ hne
    let F₁ : Subgroup G := (F₀.comap π).map K.subtype ⊓ E
    have hF₁leE : F₁ ≤ E := inf_le_right
    have hF₁leK : F₁ ≤ K := hF₁leE.trans hEK
    have hTmap : (F₁.subgroupOf K).map π = F₀ := by
      apply le_antisymm
      · rintro z ⟨y, hy, rfl⟩
        have hyF : (y : G) ∈ (F₀.comap π).map K.subtype :=
          (Subgroup.mem_subgroupOf.mp hy).1
        obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hyF
        rw [show y = w from Subtype.ext hwy.symm]
        exact hw
      · intro z hz
        have hzFbar : z ∈ Fbar := hF₀ hz
        obtain ⟨e, hez⟩ := MonoidHom.mem_range.mp hzFbar
        refine ⟨⟨(e : G), hEK e.2⟩, ?_, ?_⟩
        · refine Subgroup.mem_subgroupOf.mpr ⟨?_, e.2⟩
          refine Subgroup.mem_map.mpr ⟨⟨(e : G), hEK e.2⟩, ?_, rfl⟩
          show π ⟨(e : G), hEK e.2⟩ ∈ F₀
          rwa [show π ⟨(e : G), hEK e.2⟩ = z from by
            simpa [f, Subgroup.inclusion] using hez]
        · simpa [f, Subgroup.inclusion] using hez
    have hF₁ne : F₁ ≠ ⊥ := by
      intro hbot
      apply hne
      rw [← hTmap, hbot]
      simp
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF₁ne
    have hx : (x : G) ∈ F₁ := x.2
    have hxE : (x : G) ∈ E := hF₁leE hx
    have hx3 : (x : G) ^ 3 = 1 := h.elem.2 (x : G) hxE
    have hxord : orderOf (x : G) = 3 :=
      orderOf_eq_prime hx3 (fun h1 => hx1 (Subtype.ext h1))
    have hzelem : IsElemAbelian 3 (Subgroup.zpowers (x : G)) :=
      CFSG.Open.isElemAbelian_zpowers hx3
    have hzcard : Nat.card ↥(Subgroup.zpowers (x : G)) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hxord]
      norm_num
    have hzle : Subgroup.zpowers (x : G) ≤ F₁ := Subgroup.zpowers_le.mpr hx
    have hpRank : 1 ≤ CFSG.Open.pRank 3 F₁ :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hzle hzelem hzcard
    have hNF₁ : Subgroup.normalizer (F₁ : Set G) ≤ M :=
      (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E M).mp h.gamma
        F₁ hF₁leE hpRank
    have hF₁p : IsPGroup 3 F₁ := (h.elem.mono hF₁leE).isPGroup
    have hTp : IsPGroup 3 ↥(F₁.subgroupOf K) :=
      IsPGroup.of_equiv hF₁p (Subgroup.subgroupOfEquivOfLe hF₁leK).symm
    have hnormEq : Subgroup.normalizer (F₁.subgroupOf K) =
        (K ⊓ Subgroup.normalizer (F₁ : Set G)).subgroupOf K :=
      CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K F₁ hF₁leK
    haveI : Fact (IsPGroup 3 ↥(F₁.subgroupOf K)) := ⟨hTp⟩
    have hNT := CFSG.normalizer_map_quotient_eq_map_normalizer (G := ↥K) (p := 3)
      (F₁.subgroupOf K) (CFSG.pPrimeCore 3 ↥K) (CFSG.pPrimeCore_normal)
      (CFSG.pPrimeCore_coprime_card)
    have hNT' : Subgroup.normalizer (F₀ : Set (threeStar K)) =
        ((K ⊓ Subgroup.normalizer (F₁ : Set G)).subgroupOf K).map π := by
      rw [← hTmap, ← hnormEq]
      simpa [π] using hNT
    rw [hNT']
    exact Subgroup.map_mono (f := π)
      (Subgroup.subgroupOf_mono K (inf_le_inf le_rfl hNF₁))
  obtain ⟨e⟩ := h2.2
  rcases hKF.of_mulEquiv e Fbar Y hFbarElem hFbarCard hYcond
    with htop | ⟨i, j, hij, heq⟩
  · exact absurd htop hYne
  · exact ⟨e, i, j, hij, by simpa [K, π, Y] using heq⟩


theorem S14Choice.relIndex_inf_eq {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) : (H ⊓ M).relIndex H = 55 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  have hKleH : K ≤ H := kSub_le 3 M H
  have hsup : K ⊔ (H ⊓ M) = H := h.kSub_sup_inf_eq h2 hK hU
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleH).mpr (hK 3 E H h.hypCGen)
  have hsupH : K.subgroupOf H ⊔ (H ⊓ M).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := K) (A' := H ⊓ M) (B := H) hKleH inf_le_left,
      hsup, Subgroup.subgroupOf_self]
  have hinf : K.subgroupOf H ⊓ (H ⊓ M).subgroupOf H = (K ⊓ (H ⊓ M)).subgroupOf H := by
    change Subgroup.comap H.subtype K ⊓ Subgroup.comap H.subtype (H ⊓ M) =
      Subgroup.comap H.subtype (K ⊓ (H ⊓ M))
    rw [Subgroup.comap_inf, Subgroup.comap_inf, Subgroup.comap_inf]
  have hSindex : ((H ⊓ M).subgroupOf H).index = (K ⊓ (H ⊓ M)).relIndex K := by
    rw [CFSG.GorensteinWalter.index_eq_relIndex_inf_of_normal_sup (K.subgroupOf H)
      ((H ⊓ M).subgroupOf H) hKnormal hsupH, hinf,
      Subgroup.relIndex_subgroupOf (H := K ⊓ (H ⊓ M)) (K := K) (L := H)
        hKleH]
  have hKinf : K ⊓ (H ⊓ M) = K ⊓ M := by
    calc K ⊓ (H ⊓ M) = (K ⊓ H) ⊓ M := (inf_assoc K H M).symm
      _ = K ⊓ M := by rw [inf_eq_left.mpr hKleH]
  rw [hKinf] at hSindex
  obtain ⟨e, i, j, hij, heq⟩ := h.exists_twoSet h2 hK hU hL hKF
  have hOKM : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ K ⊓ M := by
    refine le_inf (Subgroup.map_subtype_le _) ?_
    exact h.hypCGen.pPrimeCore_map_le hK
  have hker : CFSG.pPrimeCore 3 ↥K ≤ (K ⊓ M).subgroupOf K := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ⟨x.2, (Subgroup.mem_inf.mp (hOKM (Subgroup.mem_map_of_mem K.subtype hx))).2⟩
  have hmapidx : (((K ⊓ M).subgroupOf K).map π).index = ((K ⊓ M).subgroupOf K).index :=
    Subgroup.index_map_eq ((K ⊓ M).subgroupOf K)
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K))
      (by rw [QuotientGroup.ker_mk']; exact hker)
  have hYidx : (((K ⊓ M).subgroupOf K).map π).index = 55 := by
    have h1 : ((((K ⊓ M).subgroupOf K).map π).map e.toMonoidHom).index =
        (((K ⊓ M).subgroupOf K).map π).index :=
      Subgroup.index_map_equiv (H := ((K ⊓ M).subgroupOf K).map π) e
    rw [heq] at h1
    rw [← h1]
    exact a11TwoSetStab_index hij
  have hSindex55 : ((H ⊓ M).subgroupOf H).index = 55 := by
    rw [hSindex]
    have hrel : (K ⊓ M).relIndex K = ((K ⊓ M).subgroupOf K).index := rfl
    rw [hrel, ← hmapidx]
    exact hYidx
  exact hSindex55

theorem S14Choice.isSylowOf_two_of_inf {M H E Q T : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf 2 T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : (H ⊓ M).relIndex H = 55 :=
    h.relIndex_inf_eq h2 hK hU hL hKF
  have hodd : Odd ((H ⊓ M).relIndex H) := by rw [hidx]; norm_num
  have hfac : (Nat.card ↥H).factorization 2 = (Nat.card ↥(H ⊓ M)).factorization 2 :=
    CFSG.GroupTheory.FT63ChII.factorization_eq_of_not_dvd_relIndex
      (q := 2) (H := H ⊓ M) (K := H) (show H ⊓ M ≤ H from inf_le_left)
      (fun h2dvd => by rw [hidx] at h2dvd; norm_num at h2dvd)
  exact CFSG.ABGLocalTools.isSylowOf_of_card (p := 2) (P := T) (K := H)
    (hT.le.trans inf_le_left)
      ((CFSG.ABGLocalTools.IsSylowOf.card_eq hT).trans (by rw [hfac]))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
