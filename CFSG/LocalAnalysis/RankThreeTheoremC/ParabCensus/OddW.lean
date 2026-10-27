module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullBasic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.RankThree.GroupTheory.SteinbergCDCyclicNormalHall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup TenThreeThree
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {R : Type} [Group R] [Finite R]

theorem eq_bot_of_normal_isPGroup_two_of_isWBlock {X : Type} [Group X] [Finite X]
    (hX : IsWBlock X) {N : Subgroup X} (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  rcases hX with ⟨hq, hodd⟩ | hsym
  · have hcen : N ≤ Subgroup.center X :=
      CFSG.AGLEmbedding.le_center_of_normal_of_isPGroup_two hq hN h2
    exact CFSG.RankThree.GroupTheory.eq_bot_of_isPGroup_two_of_odd h2
      (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hcen))
  · have h3 : ¬ 3 ∣ Nat.card N := by
      intro h3dvd
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      rw [hn] at h3dvd
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourL34.normal_eq_bot_of_not_three_dvd
      CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourL34.kFactSUThreeTwoNoNormalThreePrime_holds
      hsym N h3

theorem pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex {k : ℕ} {G : Fin k → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {Λ : Subgroup (∀ j, G j)} (hSΛ : Subgroup.pi Set.univ S ≤ Λ)
    (hΛS : Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex Λ))
    (hS : ∀ j, S j = ⊥ ∨ IsWBlock (S j)) :
    CFSG.pCore 2 ↥Λ = ⊥ := by
  classical
  let N : Subgroup ↥Λ := (Subgroup.pi Set.univ S).subgroupOf Λ
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSΛ).mpr hΛS
  have hNindex : N.index = (Subgroup.pi Set.univ S).relIndex Λ := rfl
  have hPle : CFSG.pCore 2 ↥Λ ≤ N :=
    CFSG.ComponentClassification.AS76b.Lemma22Full.le_of_isPGroup_of_odd_relIndex
      (N := N) (Y := ⊤) (P := CFSG.pCore 2 ↥Λ) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hNnormal])
      (by simpa [Subgroup.relIndex_top_right, hNindex] using hodd) le_top
      CFSG.pCore_isPGroup
  have hcoord_mem : ∀ (j : Fin k) (x : ↥N),
      (((x : ↥N) : ↥Λ) : ∀ i, G i) j ∈ S j := by
    intro j x
    have hxpi := Subgroup.mem_subgroupOf.mp x.2
    rw [Subgroup.mem_pi] at hxpi
    exact hxpi j (Set.mem_univ j)
  let coord : ∀ j, ↥N →* ↥(S j) := fun j =>
    { toFun := fun x => ⟨(((x : ↥N) : ↥Λ) : ∀ i, G i) j, hcoord_mem j x⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun _ _ => by apply Subtype.ext; rfl }
  have hcoord_apply : ∀ (j : Fin k) (x : ↥N),
      ((coord j x : ↥(S j)) : G j) = (((x : ↥N) : ↥Λ) : ∀ i, G i) j :=
    fun _ _ => rfl
  have hcoord_surj : ∀ j, Function.Surjective (coord j) := by
    intro j y
    refine ⟨⟨⟨MonoidHom.mulSingle G j (y : G j),
        hSΛ ((Subgroup.mulSingle_mem_pi j (y : G j)).mpr fun _ => y.2)⟩,
      Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mulSingle_mem_pi j (y : G j)).mpr fun _ => y.2)⟩, ?_⟩
    apply Subtype.ext
    exact Pi.mulSingle_eq_same ..
  have hcoord_bot : ∀ j, ((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j) = ⊥ := by
    intro j
    have hnormal : (((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j)).Normal :=
      ((CFSG.pCore_normal (p := 2) (G := ↥Λ)).subgroupOf N).map (coord j) (hcoord_surj j)
    have h2 : IsPGroup 2 (((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j)) :=
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥Λ)).comap_subtype).map (coord j)
    rcases hS j with hbot | hW
    · haveI : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
      exact Subgroup.eq_bot_of_subsingleton _
    · exact eq_bot_of_normal_isPGroup_two_of_isWBlock hW hnormal h2
  rw [eq_bot_iff]
  intro y hy
  have hyN : y ∈ N := hPle hy
  apply Subtype.ext
  funext j
  have hyP : (⟨y, hyN⟩ : ↥N) ∈ (CFSG.pCore 2 ↥Λ).subgroupOf N :=
    Subgroup.mem_subgroupOf.mpr hy
  have hy' : coord j ⟨y, hyN⟩ ∈ ((CFSG.pCore 2 ↥Λ).subgroupOf N).map (coord j) :=
    ⟨⟨y, hyN⟩, hyP, rfl⟩
  rw [hcoord_bot j, Subgroup.mem_bot] at hy'
  have h1 : (((⟨y, hyN⟩ : ↥N) : ↥Λ) : ∀ i, G i) j = 1 := by
    rw [← hcoord_apply j ⟨y, hyN⟩]
    exact congrArg Subtype.val hy'
  simpa using h1

theorem le_sup_pCore_two_of_central_odd_quotient_two {Q : Type*} [Group Q] [Finite Q]
    {H Z : Subgroup Q} (hHN : H.Normal) (hZH : Z ≤ H)
    (hZc : Z ≤ Subgroup.center Q) (hZodd : Odd (Nat.card Z))
    [hZn : (Z.subgroupOf H).Normal]
    (hquot : IsPGroup 2 (↥H ⧸ Z.subgroupOf H)) :
    H ≤ Z ⊔ CFSG.pCore 2 Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : H.Normal := hHN
  have hZnormal : Z.Normal := Subgroup.normal_of_le_center hZc
  let f : ↥H →* ↥H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H)
  have hfker : f.ker ≤ Subgroup.center ↥H := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZc hz) (w : Q)
  haveI hquotNil : Group.IsNilpotent (↥H ⧸ Z.subgroupOf H) := hquot.isNilpotent
  haveI hHnil : Group.IsNilpotent ↥H :=
    Subgroup.isNilpotent_of_ker_le_center f hfker
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥H) (p := 2) hHnil
  have hZ'card : Nat.card ↥(Z.subgroupOf H) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
  have hleZ : Z.subgroupOf H ≤ CFSG.pPrimeCore 2 ↥H := by
    refine le_sSup ⟨hZn, ?_⟩
    rw [hZ'card]
    exact Nat.coprime_two_left.mpr hZodd
  have hgeZ : CFSG.pPrimeCore 2 ↥H ≤ Z.subgroupOf H := by
    refine CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient
      (Z.subgroupOf H) (CFSG.pPrimeCore 2 ↥H) hquot ?_
    exact (Nat.prime_two.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
  have hPPrime : CFSG.pPrimeCore 2 ↥H = Z.subgroupOf H := le_antisymm hgeZ hleZ
  have hsup : (⊤ : Subgroup ↥H) ≤ CFSG.pCore 2 ↥H ⊔ Z.subgroupOf H := by
    simpa [hPPrime] using htop
  have hpc_le : (CFSG.pCore 2 ↥H).map H.subtype ≤ CFSG.pCore 2 Q := by
    have hnorm : ((CFSG.pCore 2 ↥H).map H.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal (H := H) (K := CFSG.pCore 2 ↥H)
    refine le_sSup ⟨hnorm, ?_⟩
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  intro x hx
  have hxsup := hsup (Subgroup.mem_top (⟨x, hx⟩ : ↥H))
  rw [Subgroup.mem_sup_of_normal_right] at hxsup
  obtain ⟨y, hy, z, hz, hyz⟩ := hxsup
  have hxeq : (y : Q) * (z : Q) = x := by
    have := congrArg (fun t : ↥H => (t : Q)) hyz
    simpa using this
  have hyQ : (y : Q) ∈ CFSG.pCore 2 Q :=
    hpc_le (Subgroup.mem_map_of_mem H.subtype hy)
  refine Subgroup.mem_sup_of_normal_right.mpr ⟨z, hz, y, hyQ, ?_⟩
  rw [← hxeq]
  exact (Subgroup.mem_center_iff.mp (hZc hz) (y : Q)).symm

theorem exists_levi_quotient_of_pCore_eq_bot {Q R : Type*} [Group Q] [Finite Q] [Group R]
    {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] {σ : Q →* R}
    (hσ : Function.Surjective σ) (hc : σ.ker ≤ Subgroup.center Q)
    (ho : Odd (Nat.card σ.ker)) (β : Q →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hpc : CFSG.pCore 2 ↥β.range = ⊥) :
    ∃ ψ : ↥β.range →* R ⧸ CFSG.pCore 2 R,
      Function.Surjective ψ ∧
      (∀ q : Q, ψ ⟨β q, ⟨q, rfl⟩⟩ = QuotientGroup.mk' (CFSG.pCore 2 R) (σ q)) ∧
      ψ.ker ≤ (σ.ker).map β.rangeRestrict := by
  classical
  let Λ : Subgroup (∀ j, G j) := β.range
  let Rhat := R ⧸ CFSG.pCore 2 R
  have hpcΛ : CFSG.pCore 2 ↥Λ = ⊥ := hpc
  let φ : Q →* Rhat := (QuotientGroup.mk' (CFSG.pCore 2 R)).comp σ
  have hφsurj : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hσ
  have hβker_le : β.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hσx : σ x ∈ (β.ker).map σ := Subgroup.mem_map_of_mem σ hx
    have hle_pc : (β.ker).map σ ≤ CFSG.pCore 2 R :=
      le_sSup ⟨(inferInstance : β.ker.Normal).map σ hσ, hβ.map σ⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 R)) (σ x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hle_pc hσx
  let ψbar : Q ⧸ β.ker →* Rhat := QuotientGroup.lift β.ker φ hβker_le
  let ψ : ↥Λ →* Rhat :=
    ψbar.comp (QuotientGroup.quotientKerEquivRange β).symm.toMonoidHom
  have hψβ : ∀ q : Q, ψ ⟨β q, ⟨q, rfl⟩⟩ = φ q := by
    intro q
    have h2 : (QuotientGroup.quotientKerEquivRange β).symm ⟨β q, ⟨q, rfl⟩⟩ =
        QuotientGroup.mk q := by
      apply (QuotientGroup.quotientKerEquivRange β).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2]
    exact QuotientGroup.lift_mk β.ker hβker_le q
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := hφsurj r
    exact ⟨⟨β q, ⟨q, rfl⟩⟩, by rw [hψβ q]; exact hq⟩
  have hpc_le : CFSG.pCore 2 Q ≤ β.ker := by
    have hnorm : ((CFSG.pCore 2 Q).map β.rangeRestrict).Normal :=
      (CFSG.pCore_normal (p := 2) (G := Q)).map β.rangeRestrict
        (MonoidHom.rangeRestrict_surjective β)
    have h2 : IsPGroup 2 ((CFSG.pCore 2 Q).map β.rangeRestrict) :=
      (CFSG.pCore_isPGroup (p := 2) (G := Q)).map β.rangeRestrict
    have hle_pc : (CFSG.pCore 2 Q).map β.rangeRestrict ≤ CFSG.pCore 2 ↥Λ :=
      le_sSup ⟨hnorm, h2⟩
    rw [hpcΛ] at hle_pc
    intro x hx
    have hxmap : β.rangeRestrict x ∈ (CFSG.pCore 2 Q).map β.rangeRestrict :=
      Subgroup.mem_map_of_mem β.rangeRestrict hx
    rw [le_bot_iff.mp hle_pc, Subgroup.mem_bot] at hxmap
    rw [MonoidHom.mem_ker]
    simpa using congrArg Subtype.val hxmap
  have hH_eq : (CFSG.pCore 2 R).comap σ ≤ σ.ker ⊔ β.ker := by
    let H : Subgroup Q := (CFSG.pCore 2 R).comap σ
    have hHN : H.Normal := (CFSG.pCore_normal (p := 2) (G := R)).comap σ
    have hZH : σ.ker ≤ H := by
      intro z hz
      rw [Subgroup.mem_comap]
      rw [MonoidHom.mem_ker] at hz
      rw [hz]
      exact (CFSG.pCore 2 R).one_mem
    haveI hZn : (σ.ker.subgroupOf H).Normal := (inferInstance : σ.ker.Normal).subgroupOf H
    have hquot : IsPGroup 2 (↥H ⧸ σ.ker.subgroupOf H) := by
      let g : ↥H →* R := σ.domRestrict H
      have hker : g.ker = σ.ker.subgroupOf H := MonoidHom.ker_domRestrict H σ
      have hrange : g.range = CFSG.pCore 2 R := by
        ext r
        constructor
        · rintro ⟨x, -, rfl⟩
          exact x.2
        · intro hr
          obtain ⟨q, hq⟩ := hσ r
          exact ⟨⟨q, by rw [Subgroup.mem_comap]; rw [hq]; exact hr⟩, hq⟩
      have e : (↥H ⧸ σ.ker.subgroupOf H) ≃* ↥(CFSG.pCore 2 R) :=
        ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
          (QuotientGroup.quotientKerEquivRange g)).trans (MulEquiv.subgroupCongr hrange)
      exact (CFSG.pCore_isPGroup (p := 2) (G := R)).of_equiv e.symm
    calc
      (CFSG.pCore 2 R).comap σ ≤ σ.ker ⊔ CFSG.pCore 2 Q :=
        le_sup_pCore_two_of_central_odd_quotient_two hHN hZH hc ho hquot
      _ ≤ σ.ker ⊔ β.ker := sup_le le_sup_left (hpc_le.trans le_sup_right)
  have hψker : ψ.ker ≤ (σ.ker).map β.rangeRestrict := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨q, hqx⟩ := x.2
    have hxq : x = ⟨β q, ⟨q, rfl⟩⟩ := Subtype.ext hqx.symm
    have hx' : ψ ⟨β q, ⟨q, rfl⟩⟩ = 1 := by rwa [← hxq]
    have hφq : φ q = 1 := by rwa [← hψβ q]
    have hqH : q ∈ (CFSG.pCore 2 R).comap σ := by
      rw [Subgroup.mem_comap]
      rw [← QuotientGroup.eq_one_iff]
      exact hφq
    have hq : q ∈ σ.ker ⊔ β.ker := hH_eq hqH
    rw [Subgroup.mem_sup_of_normal_left] at hq
    obtain ⟨z, hz, k, hk, hzk⟩ := hq
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    apply Subtype.ext
    rw [← hqx, ← hzk, map_mul, MonoidHom.mem_ker.mp hk, mul_one]
    rfl
  exact ⟨ψ, hψsurj, hψβ, hψker⟩

theorem HasLeviCensus.not_two_dvd_index_wSup (h : HasLeviCensus R IsWBlock) :
    ¬ 2 ∣ (wSup (R ⧸ CFSG.pCore 2 R)).index := by
  classical
  obtain ⟨Q, hQgroup, hQfin, σ, k, G, hGgroup, hGfin, S, β, hσ, hc, ho, hβ, hle, hn, hi, hS,
    hZ⟩ := h
  letI : Group Q := hQgroup
  letI : Finite Q := hQfin
  letI : ∀ j, Group (G j) := hGgroup
  letI : ∀ j, Finite (G j) := hGfin
  let Λ : Subgroup (∀ j, G j) := β.range
  let NΛ : Subgroup ↥Λ := (Subgroup.pi Set.univ S).subgroupOf Λ
  let Rhat := R ⧸ CFSG.pCore 2 R
  have hodd : Odd ((Subgroup.pi Set.univ S).relIndex Λ) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact hi (Nat.dvd_iff_mod_eq_zero.mpr (Nat.even_iff.mp he))
  have hpcΛ : CFSG.pCore 2 ↥Λ = ⊥ :=
    pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex hle hn hodd hS
  obtain ⟨ψ, hψsurj, -, hψker⟩ :=
    exists_levi_quotient_of_pCore_eq_bot hσ hc ho β hβ hpcΛ
  have hsingle_mem : ∀ (j : Fin k) (s : ↥(S j)),
      MonoidHom.mulSingle G j (s : G j) ∈ Subgroup.pi Set.univ S :=
    fun j s => (Subgroup.mulSingle_mem_pi j (s : G j)).mpr fun _ => s.2
  let single : ∀ j, ↥(S j) →* ↥NΛ := fun j =>
    MonoidHom.codRestrict
      (((MonoidHom.mulSingle G j).comp (S j).subtype).codRestrict Λ
        fun s => hle (hsingle_mem j s)) NΛ
      fun s => Subgroup.mem_subgroupOf.mpr (hsingle_mem j s)
  let B : ∀ j, Subgroup ↥NΛ := fun j => (⊤ : Subgroup ↥(S j)).map (single j)
  have hsingle_inj : ∀ j, Function.Injective (single j) := by
    intro j a b hab
    have h := congrArg (fun x : ↥NΛ => (((x : ↥Λ) : ∀ i, G i) j)) hab
    simpa [single, Pi.mulSingle_eq_same] using h
  have hNΛ_normal : NΛ.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hn
  have hB_normal : ∀ j, (B j).Normal := by
    intro j
    refine ⟨fun b hb n => ?_⟩
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hb
    have hxpi := Subgroup.mem_subgroupOf.mp n.2
    rw [Subgroup.mem_pi] at hxpi
    have hnj : (((n : ↥NΛ) : ↥Λ) : ∀ i, G i) j ∈ S j := hxpi j (Set.mem_univ j)
    refine Subgroup.mem_map.mpr ⟨⟨((((n : ↥NΛ) : ↥Λ) : ∀ i, G i) j) * s *
      ((((n : ↥NΛ) : ↥Λ) : ∀ i, G i) j)⁻¹, ?_⟩, Subgroup.mem_top _, ?_⟩
    · exact (S j).mul_mem ((S j).mul_mem hnj s.2) ((S j).inv_mem hnj)
    · apply Subtype.ext
      apply Subtype.ext
      funext i
      by_cases hij : i = j
      · subst hij
        simp [single, Pi.mul_apply, Pi.inv_apply]
      · simp [single, Pi.mul_apply, Pi.inv_apply, hij]
  have hB_sub : ∀ j, IsSubnormal ((B j).map NΛ.subtype) ⊤ := by
    intro j
    refine IsSubnormal.step (Subgroup.map_subtype_le _) ?_
      (CFSG.Open.IsSubnormal.of_mathlib hNΛ_normal.isSubnormal)
    change (Subgroup.comap NΛ.subtype (Subgroup.map NΛ.subtype (B j))).Normal
    rw [Subgroup.comap_map_eq_self_of_injective (f := NΛ.subtype) NΛ.subtype_injective]
    exact hB_normal j
  let ψN : ↥NΛ →* Rhat := ψ.comp NΛ.subtype
  have hBsub : ∀ j, IsSubnormal ((B j).map ψN) ⊤ := by
    intro j
    have h := (hB_sub j).map ψ
    rwa [Subgroup.map_map, Subgroup.map_top_of_surjective ψ hψsurj] at h
  have hB_ker : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z : ↥NΛ,
      z ∈ B j → ψN z = 1 → z = 1 := by
    intro j hj z hz hψz
    have hzΛ : (z : ↥Λ) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact hψz
    obtain ⟨t, ht, htβ⟩ := Subgroup.mem_map.mp (hψker hzΛ)
    obtain ⟨s, -, hsz⟩ := Subgroup.mem_map.mp hz
    have hmem : β t ∈ (S j).map (MonoidHom.mulSingle G j) := by
      have htβ' : β t = ((z : ↥Λ) : ∀ i, G i) :=
        congrArg (fun x : ↥Λ => (x : ∀ i, G i)) htβ
      rw [htβ']
      have hsz' : (z : ↥Λ) = (single j s : ↥Λ) := (congrArg Subtype.val hsz).symm
      rw [hsz']
      exact Subgroup.mem_map_of_mem (MonoidHom.mulSingle G j) s.2
    have hβ1 : β t = 1 := hZ j hj t ht hmem
    have hz1 : (z : ↥Λ) = 1 := by
      rw [← htβ]
      exact Subtype.ext hβ1
    exact Subtype.ext hz1
  have hblock_le : ∀ j, (B j).map ψN ≤ wSup Rhat := by
    intro j
    rcases hS j with hbot | hW
    · have hBbot : B j = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
        have hs1 : s = 1 := by
          haveI : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
          exact Subsingleton.elim s 1
        rw [hs1, map_one]
        exact Subgroup.one_mem _
      rw [hBbot, Subgroup.map_bot]
      exact bot_le
    · by_cases hq : CFSG.Open.IsQuasisimple ↥(S j)
      · have hmul : ↥(S j) ≃* ↥(B j) :=
          (Subgroup.topEquiv (G := ↥(S j))).symm.trans
            (Subgroup.equivMapOfInjective (⊤ : Subgroup ↥(S j)) (single j) (hsingle_inj j))
        have hqB : CFSG.Open.IsQuasisimple ↥(B j) :=
          CFSG.Open.IsQuasisimple.of_mulEquiv hmul.symm hq
        by_cases hbotB : (B j).map ψN = ⊥
        · rw [hbotB]
          exact bot_le
        · haveI : Nontrivial ↥((B j).map ψN) :=
            (Subgroup.nontrivial_iff_ne_bot _).mpr hbotB
          let f : ↥(B j) →* ↥((B j).map ψN) :=
            (ψN.comp (B j).subtype).codRestrict _ fun x =>
              Subgroup.mem_map_of_mem ψN x.2
          have hf : Function.Surjective f := by
            rintro ⟨y, hy⟩
            obtain ⟨x, hx, rfl⟩ := hy
            exact ⟨⟨x, hx⟩, rfl⟩
          have hqimg : CFSG.Open.IsQuasisimple ↥((B j).map ψN) :=
            Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial hqB f hf
          exact le_wSup_of_subnormal_of_isQuasisimple (hBsub j) hqimg
      · rcases hW with ⟨hq', -⟩ | hsym
        · exact absurd hq' hq
        · have hmul : ↥(S j) ≃* ↥(B j) :=
            (Subgroup.topEquiv (G := ↥(S j))).symm.trans
              (Subgroup.equivMapOfInjective (⊤ : Subgroup ↥(S j)) (single j) (hsingle_inj j))
          have hsymB : IsSymThreeOrSUThreeTwo ↥(B j) :=
            IsSymThreeOrSUThreeTwo.of_mulEquiv hmul hsym
          let f : ↥(B j) →* ↥((B j).map ψN) :=
            (ψN.comp (B j).subtype).codRestrict _ fun x =>
              Subgroup.mem_map_of_mem ψN x.2
          have hf : Function.Surjective f := by
            rintro ⟨y, hy⟩
            obtain ⟨x, hx, rfl⟩ := hy
            exact ⟨⟨x, hx⟩, rfl⟩
          have hfi : Function.Injective f := by
            intro x y hxy
            have h1 : ψN ((x : ↥NΛ) * (y : ↥NΛ)⁻¹) = 1 := by
              rw [map_mul, map_inv,
                show ψN (x : ↥NΛ) = ψN (y : ↥NΛ) from congrArg Subtype.val hxy,
                mul_inv_cancel]
            have hxyB : ((x : ↥NΛ) * (y : ↥NΛ)⁻¹) ∈ B j :=
              (B j).mul_mem x.2 ((B j).inv_mem y.2)
            have hxy1 : (x : ↥NΛ) * (y : ↥NΛ)⁻¹ = 1 := hB_ker j hq _ hxyB h1
            apply Subtype.ext
            calc (x : ↥NΛ) = ((x : ↥NΛ) * (y : ↥NΛ)⁻¹) * (y : ↥NΛ) := by group
              _ = (y : ↥NΛ) := by rw [hxy1, one_mul]
          let e : ↥(B j) ≃* ↥((B j).map ψN) := MulEquiv.ofBijective f ⟨hfi, hf⟩
          have hsymimg : IsSymThreeOrSUThreeTwo ↥((B j).map ψN) :=
            IsSymThreeOrSUThreeTwo.of_mulEquiv e hsymB
          exact le_wSup_of_subnormal_of_symThree (hBsub j) hsymimg
  let J : Subgroup (∀ j, G j) := ⨆ j, (S j).map (MonoidHom.mulSingle G j)
  have hJ_factor_le_pi : ∀ j, (S j).map (MonoidHom.mulSingle G j) ≤
      Subgroup.pi Set.univ S := by
    intro j
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs
  have hpi_le_J : Subgroup.pi Set.univ S ≤ J :=
    Subgroup.pi_le_iff.mpr fun j =>
      le_iSup (fun j => (S j).map (MonoidHom.mulSingle G j)) j
  let eN : ↥NΛ ≃* ↥(Subgroup.pi Set.univ S) := Subgroup.subgroupOfEquivOfLe hle
  let B' : ∀ j, Subgroup ↥(Subgroup.pi Set.univ S) := fun j =>
    ((S j).map (MonoidHom.mulSingle G j)).subgroupOf (Subgroup.pi Set.univ S)
  have hB_map : ∀ j, (B j).map eN.toMonoidHom = B' j := by
    intro j
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem (MonoidHom.mulSingle G j) s.2)
    · intro hx
      obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨single j ⟨s, hs⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨s, hs⟩, Subgroup.mem_top _, rfl⟩
      · apply Subtype.ext
        exact hxs
  have hJ_map : (⨆ j, B' j).map (Subgroup.pi Set.univ S).subtype = J := by
    rw [Subgroup.map_iSup]
    have hfac : ∀ j, (B' j).map (Subgroup.pi Set.univ S).subtype =
        (S j).map (MonoidHom.mulSingle G j) := by
      intro j
      simp only [B']
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr (hJ_factor_le_pi j)
    simp only [hfac]
    rfl
  have hB'_top : (⨆ j, B' j) = ⊤ := by
    have h2 : (⊤ : Subgroup ↥(Subgroup.pi Set.univ S)).map
        (Subgroup.pi Set.univ S).subtype ≤ (⨆ j, B' j).map
          (Subgroup.pi Set.univ S).subtype := by
      simpa [Subgroup.map_top, Subgroup.range_subtype, hJ_map] using hpi_le_J
    exact eq_top_iff.mpr ((Subgroup.map_le_map_iff_of_injective
      (Subgroup.subtype_injective (Subgroup.pi Set.univ S))).mp h2)
  have hB_top : (⨆ j, B j) = ⊤ := by
    apply Subgroup.map_injective (f := eN.toMonoidHom) eN.injective
    rw [Subgroup.map_iSup]
    simp only [hB_map]
    rw [hB'_top, Subgroup.map_top_of_surjective eN.toMonoidHom eN.surjective]
  have hN_le_iSup : (⊤ : Subgroup ↥NΛ) ≤ ⨆ j, B j := by rw [hB_top]
  have hmapN : NΛ.map ψ ≤ wSup Rhat := by
    have hNΛ_map : (⊤ : Subgroup ↥NΛ).map ψN = NΛ.map ψ := by
      change (⊤ : Subgroup ↥NΛ).map (ψ.comp NΛ.subtype) = NΛ.map ψ
      rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hNΛ_map]
    calc
      (⊤ : Subgroup ↥NΛ).map ψN ≤ (⨆ j, B j).map ψN := Subgroup.map_mono hN_le_iSup
      _ = ⨆ j, (B j).map ψN := Subgroup.map_iSup ψN _
      _ ≤ wSup Rhat := iSup_le hblock_le
  have hindex_odd : ¬ 2 ∣ (NΛ.map ψ).index := by
    have hdvd : (NΛ.map ψ).index ∣ NΛ.index := Subgroup.index_map_dvd NΛ hψsurj
    exact fun h2 => hi (h2.trans hdvd)
  have hdvd2 : (wSup Rhat).index ∣ (NΛ.map ψ).index := Subgroup.index_dvd_of_le hmapN
  exact fun h2 => hindex_odd (h2.trans hdvd2)

theorem exists_wGen_of_not_two_dvd_index {Q : Type} [Group Q] [Finite Q]
    (h : ¬ 2 ∣ (wSup Q).index) (h2 : 2 ∣ Nat.card Q) :
    ∃ T : Subgroup Q, IsSubnormal T ⊤ ∧ (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T) := by
  by_contra hne
  have hbot : wSup Q = ⊥ := by
    unfold wSup
    rw [iSup_eq_bot]
    intro T
    by_cases hT : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}
    · exact absurd ⟨T, hT⟩ hne
    · rw [iSup_eq_bot]
      intro hT'
      exact absurd hT' hT
  rw [hbot, Subgroup.index_bot] at h
  exact h h2

theorem not_two_dvd_index_wSup_of_isQuasisimple {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ 2 ∣ (wSup Q).index := by
  have htop : wSup Q = ⊤ := by
    refine top_unique ?_
    exact le_wSup_of_subnormal_of_isQuasisimple (T := ⊤) (IsSubnormal.refl ⊤)
      (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hQ)
  rw [htop, Subgroup.index_top]
  norm_num

theorem not_two_dvd_index_wSup_of_odd {Q : Type} [Group Q] [Finite Q]
    (hQ : ¬ 2 ∣ Nat.card Q) : ¬ 2 ∣ (wSup Q).index :=
  fun h => hQ (h.trans (Subgroup.index_dvd_card _))

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
