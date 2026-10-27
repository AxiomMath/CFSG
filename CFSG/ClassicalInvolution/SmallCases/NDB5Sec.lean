module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

namespace S

@[expose] def sFamily (s : G) (L₁ L₂ : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ h ∈ Subgroup.centralizer ({s} : Set G), M = conjSub h L₁ ∨ M = conjSub h L₂}

omit [Finite G] in
theorem mem_sFamily_left (s : G) (L₁ L₂ : Subgroup G) : L₁ ∈ sFamily s L₁ L₂ :=
  ⟨1, Subgroup.one_mem _, Or.inl (conjSub_one L₁).symm⟩

omit [Finite G] in
theorem mem_sFamily_right (s : G) (L₁ L₂ : Subgroup G) : L₂ ∈ sFamily s L₁ L₂ :=
  ⟨1, Subgroup.one_mem _, Or.inr (conjSub_one L₂).symm⟩

omit [Finite G] in
theorem secData_sFamily {s z₁ z₂ : G} {L₁ L₂ : Subgroup G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₂ z₂) :
    SecData p f s (sFamily s L₁ L₂) where
  nonempty := ⟨L₁, mem_sFamily_left s L₁ L₂⟩
  le := by
    rintro M ⟨h, hh, rfl | rfl⟩
    · exact (conjSub_mono h₁.le).trans (conjSub_eq_self_of_mem hh).le
    · exact (conjSub_mono h₂.le).trans (conjSub_eq_self_of_mem hh).le
  conj := by
    rintro n hn M ⟨h, hh, rfl | rfl⟩
    · exact ⟨n * h, Subgroup.mul_mem _ hn hh, Or.inl (conjSub_mul n h L₁).symm⟩
    · exact ⟨n * h, Subgroup.mul_mem _ hn hh, Or.inr (conjSub_mul n h L₂).symm⟩
  member := by
    rintro M ⟨h, hh, rfl | rfl⟩
    · exact ⟨_, h₁.conj hh⟩
    · exact ⟨_, h₂.conj hh⟩

theorem isUniqueInvolution_modOdd_of_sec (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {s z : G} {L : Subgroup G}
    (h : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L z)
    (hz : z ∈ Subgroup.centralizer ({s} : Set G)) :
    IsUniqueInvolution (modOdd s L) (oddQuotMk s ⟨z, hz⟩) := by
  obtain ⟨hzY, hcl⟩ := h.toIn
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hcl
  have hodd : Odd (Nat.card ↥(CFSG.Open.componentClassificationOddCore
      ↥(Subgroup.centralizer ({s} : Set G)) ⊓ L.subgroupOf (Subgroup.centralizer ({s} : Set G)))) :=
    (OddCore.odd_card _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact isUniqueInvolution_map_mk_of_odd hodd hU

omit [Finite G] in
theorem map_conjSub {M Q : Type*} [Group M] [Group Q] (ψ : M →* Q) (k : M) (R : Subgroup M) :
    (conjSub k R).map ψ = conjSub (ψ k) (R.map ψ) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨ψ r, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨k * r * k⁻¹, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩

omit [Finite G] in
theorem modOdd_conjSub {s c : G} (hc : c ∈ Subgroup.centralizer ({s} : Set G))
    (K : Subgroup G) :
    modOdd s (conjSub c K) = conjSub (oddQuotMk s ⟨c, hc⟩) (modOdd s K) := by
  ext x
  rw [mem_modOdd_iff, mem_conjSub_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : c⁻¹ * (k : G) * c ∈ K := mem_conjSub_iff.mp hk
    have hkC : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer ({s} : Set G) :=
      mul_mem (mul_mem (inv_mem hc) k.2) hc
    refine ⟨⟨c⁻¹ * (k : G) * c, hkC⟩, hk', ?_⟩
    rw [show (⟨c⁻¹ * (k : G) * c, hkC⟩ : ↥(Subgroup.centralizer ({s} : Set G))) =
      ⟨c, hc⟩⁻¹ * k * ⟨c, hc⟩ from rfl, map_mul, map_mul, map_inv]
  · rintro ⟨k, hk, hkx⟩
    refine ⟨⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      have e : c⁻¹ * ((⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹ : ↥(Subgroup.centralizer ({s} : Set G))) : G) * c =
          k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact hk
    · rw [map_mul, map_mul, map_inv, hkx]
      group

theorem exists_fund_of_mem {Φ : Set (Subgroup G)} {a : G} (hs : SecData p f a Φ)
    (D : LocalLieSystemAt p f Φ a) {M : Subgroup G} (hM : M ∈ Φ) :
    ∃ j : Fin D.card, ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R.map (secComponentHom hs.normalizes D j) = modOdd a M := by
  have hMc : M ∈ centMembers Φ a := ⟨hM, hs.le M hM⟩
  set Y := centralizingLayer Φ {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hMc
  have hMfam : modOddIn Y M ∈ localFamily Φ a := ⟨M.subgroupOf Y, ⟨M, hMc, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn hs.normalizes hMc

theorem secComponentHom_commute {Φ : Set (Subgroup G)} {a : G} (hN : NormalizesLayer Φ a)
    (D : LocalLieSystemAt p f Φ a) {i j : Fin D.card} (hij : i ≠ j) (x : (compModel D i).K)
    (y : (compModel D j).K) :
    secComponentHom hN D i x * secComponentHom hN D j y =
      secComponentHom hN D j y * secComponentHom hN D i x := by
  have h1 := map_mul (sectionQuotientHom hN) (D.hom i x) (D.hom j y)
  have h2 := map_mul (sectionQuotientHom hN) (D.hom j y) (D.hom i x)
  have h3 := congrArg (sectionQuotientHom hN) (D.commute i j hij x y)
  exact h1.symm.trans (h3.trans h2)

theorem secComponentHom_mem_memberJoin {Φ : Set (Subgroup G)} {a : G} (hN : NormalizesLayer Φ a)
    (D : LocalLieSystemAt p f Φ a) (j : Fin D.card) (k : (compModel D j).K) :
    secComponentHom hN D j k ∈ memberJoin Φ a := by
  rw [← range_sectionQuotientHom hN]
  exact ⟨D.hom j k, rfl⟩

theorem moved_eq_range (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Φ : Set (Subgroup G)} {s : G}
    (hs : SecData p f s Φ) (D : LocalLieSystemAt p f Φ s) {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hsB : s ∈ B) (hs1 : s ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbs : b ≠ s) {j : Fin D.card}
    (hbj : ∀ hb, oddQuotMk s ⟨b, hb⟩ ∈ (secComponentHom hs.normalizes D j).range)
    {L : Subgroup (OddQuot s)} (hL : CFSG.IsComponent L) (hmov : MovedByAll B s L) :
    L = (secComponentHom hs.normalizes D j).range := by
  have hbC : b ∈ Subgroup.centralizer ({s} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hsB hbB
  have hbBar : oddQuotMk s ⟨b, hbC⟩ ∈ modOdd s B := oddQuotMk_mem_modOdd hbB hbC
  have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hsB hs1 hbB hb1 hbs hbC
  obtain ⟨y, hyL, hy⟩ := hmov _ hbBar hnot
  have hJ : (memberJoin Φ s).Normal := memberJoin_normal_of_normalizes hs.normalizes
  obtain ⟨D', hD'Q, -⟩ := hs.lieDecomposition_comp hp
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq D
  obtain ⟨k, hk⟩ := hbj hbC
  rcases D'.eq_or_commutes_of_isComponentOf ((CFSG.isComponent_iff_open L).mp hL) with
    ⟨i, hi⟩ | hcomm
  · obtain ⟨j', hj'⟩ := hD'Q i
    have hLj : L = (secComponentHom hs.normalizes D j').range := hi.trans hj'.symm
    by_cases hjj : j' = j
    · rw [hLj, hjj]
    · exfalso
      rw [hLj] at hyL
      obtain ⟨m, rfl⟩ := hyL
      apply hy
      rw [← hk]
      exact (secComponentHom_commute hs.normalizes D hjj m k).symm
  · exfalso
    apply hy
    have hbJ : oddQuotMk s ⟨b, hbC⟩ ∈ memberJoin Φ s := by
      rw [← hk]
      exact secComponentHom_mem_memberJoin hs.normalizes D j k
    exact (hcomm y hyL _ hbJ).symm

theorem exists_conj_of_img {Φ : Set (Subgroup G)} {s : G} (hN : NormalizesLayer Φ s)
    (D : LocalLieSystemAt p f Φ s) (j : Fin D.card) {R : Subgroup (compModel D j).K}
    {L : Subgroup G} (hR : R.map (secComponentHom hN D j) = modOdd s L) (k : (compModel D j).K) :
    ∃ h ∈ Subgroup.centralizer ({s} : Set G),
      (conjSub k R).map (secComponentHom hN D j) = modOdd s (conjSub h L) := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective _ (secComponentHom hN D j k)
  refine ⟨c, c.2, ?_⟩
  rw [map_conjSub, hR, modOdd_conjSub c.2]
  exact congrArg (fun x => conjSub x (modOdd s L)) hc.symm

structure SComponent (A : Subgroup G) (s z₁ z₂ : G) (L₁ L₂ : Subgroup G)
    (hN : NormalizesLayer (sFamily s L₁ L₂) s) (D : LocalLieSystemAt p f (sFamily s L₁ L₂) s)
    (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K) : Prop where
  ker : (secComponentHom hN D j₀).ker ≤ Subgroup.center (compModel D j₀).K
  fund₁ : R₁ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D
  fund₂ : R₂ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D
  img₁ : R₁.map (secComponentHom hN D j₀) = modOdd s L₁
  img₂ : R₂.map (secComponentHom hN D j₀) = modOdd s L₂
  ne : modOdd s L₁ ≠ modOdd s L₂
  mem₁ : ∀ h, oddQuotMk s ⟨z₁, h⟩ ∈ modOdd s L₁
  mem₂ : ∀ h, oddQuotMk s ⟨z₂, h⟩ ∈ modOdd s L₂
  conj₁ : ∀ k : (compModel D j₀).K, ∃ h ∈ Subgroup.centralizer ({s} : Set G),
    (conjSub k R₁).map (secComponentHom hN D j₀) = modOdd s (conjSub h L₁)
  conj₂ : ∀ k : (compModel D j₀).K, ∃ h ∈ Subgroup.centralizer ({s} : Set G),
    (conjSub k R₂).map (secComponentHom hN D j₀) = modOdd s (conjSub h L₂)
  moved : ∀ L : Subgroup (OddQuot s), CFSG.IsComponent L → MovedByAll A s L →
    L = (secComponentHom hN D j₀).range

theorem exists_sComponent (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) {s z₁ z₂ : G} (hsA : s ∈ A) (hz₁A : z₁ ∈ A)
    (hz₂A : z₂ ∈ A) (hs1 : s ≠ 1) (hz₁1 : z₁ ≠ 1) (hz₂1 : z₂ ≠ 1) (hz₁s : z₁ ≠ s) (hz₂s : z₂ ≠ s)
    (hz₁₂ : z₁ ≠ z₂) {L₁ L₂ : Subgroup G}
    (h₁ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember p f (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (D : LocalLieSystemAt p f (sFamily s L₁ L₂) s) {L : Subgroup (OddQuot s)}
    (hL : CFSG.IsComponent L) (hmov : MovedByAll A s L) :
    ∃ (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
      SComponent A s z₁ z₂ L₁ L₂ (secData_sFamily h₁ h₂).normalizes D j₀ R₁ R₂ := by
  have hs := secData_sFamily h₁ h₂
  have hz₁C : z₁ ∈ Subgroup.centralizer ({s} : Set G) := h₁.le h₁.mem
  have hz₂C : z₂ ∈ Subgroup.centralizer ({s} : Set G) := h₂.le h₂.mem
  obtain ⟨j₁, R₁, hR₁, hR₁img⟩ := exists_fund_of_mem hs D (mem_sFamily_left s L₁ L₂)
  obtain ⟨j₂, R₂, hR₂, hR₂img⟩ := exists_fund_of_mem hs D (mem_sFamily_right s L₁ L₂)
  have hb₁ : ∀ hb, oddQuotMk s ⟨z₁, hb⟩ ∈ (secComponentHom hs.normalizes D j₁).range :=
    fun hb => Subgroup.map_le_range _ R₁ (hR₁img ▸ oddQuotMk_mem_modOdd h₁.mem hb)
  have hb₂ : ∀ hb, oddQuotMk s ⟨z₂, hb⟩ ∈ (secComponentHom hs.normalizes D j₂).range :=
    fun hb => Subgroup.map_le_range _ R₂ (hR₂img ▸ oddQuotMk_mem_modOdd h₂.mem hb)
  have hL₂ := moved_eq_range hp hq hs D hA hsA hs1 hz₂A hz₂1 hz₂s hb₂ hL hmov
  have hj : j₁ = j₂ := by
    by_contra hne
    have hbBar : oddQuotMk s ⟨z₁, hz₁C⟩ ∈ modOdd s A := oddQuotMk_mem_modOdd hz₁A hz₁C
    obtain ⟨y, hyL, hy⟩ := hmov _ hbBar
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hA hsA hs1 hz₁A hz₁1 hz₁s hz₁C)
    rw [hL₂] at hyL
    obtain ⟨m, rfl⟩ := hyL
    obtain ⟨k, hk⟩ := hb₁ hz₁C
    apply hy
    rw [← hk]
    exact secComponentHom_commute hs.normalizes D hne k m
  subst hj
  have hne : modOdd s L₁ ≠ modOdd s L₂ := by
    intro heq
    have hU := isUniqueInvolution_modOdd_of_sec hp hq h₁ hz₁C
    have hz₂mem : oddQuotMk s ⟨z₂, hz₂C⟩ ∈ modOdd s L₁ :=
      heq ▸ oddQuotMk_mem_modOdd h₂.mem hz₂C
    have hsq : ∀ {u : G} (hu : u ∈ Subgroup.centralizer ({s} : Set G)), u ∈ A →
        (⟨u, hu⟩ : ↥(Subgroup.centralizer ({s} : Set G))) * ⟨u, hu⟩ = 1 := fun hu huA =>
      Subtype.ext (by rw [← pow_two]; exact hA.2 _ huA)
    have hz₂sq : oddQuotMk s ⟨z₂, hz₂C⟩ * oddQuotMk s ⟨z₂, hz₂C⟩ = 1 := by
      rw [← map_mul, hsq hz₂C hz₂A, map_one]
    rcases hU.unique _ hz₂mem hz₂sq with h | h
    · exact hz₂1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (hsq hz₂C hz₂A) h))
    · have h12C : z₁ * z₂ ∈ Subgroup.centralizer ({s} : Set G) := Subgroup.mul_mem _ hz₁C hz₂C
      have h12 : oddQuotMk s ⟨z₁ * z₂, h12C⟩ = 1 := by
        rw [show (⟨z₁ * z₂, h12C⟩ : ↥(Subgroup.centralizer ({s} : Set G))) =
          ⟨z₁, hz₁C⟩ * ⟨z₂, hz₂C⟩ from rfl, map_mul, h]
        have := hsq hz₁C hz₁A
        rw [← map_mul, this, map_one]
      have h1 := congrArg Subtype.val
        (eq_one_of_oddQuotMk_eq_one (hsq h12C (A.mul_mem hz₁A hz₂A)) h12)
      apply hz₁₂
      have hz₂2 : z₂ * z₂ = 1 := by rw [← pow_two]; exact hA.2 _ hz₂A
      calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, hz₂2, mul_one]
        _ = z₂ := by rw [show z₁ * z₂ = 1 from h1, one_mul]
  exact ⟨j₁, R₁, R₂,
    { ker := secComponentHom_ker_le_center _ D j₁
      fund₁ := hR₁
      fund₂ := hR₂
      img₁ := hR₁img
      img₂ := hR₂img
      ne := hne
      mem₁ := fun h => oddQuotMk_mem_modOdd h₁.mem h
      mem₂ := fun h => oddQuotMk_mem_modOdd h₂.mem h
      conj₁ := exists_conj_of_img hs.normalizes D j₁ hR₁img
      conj₂ := exists_conj_of_img hs.normalizes D j₁ hR₂img
      moved := fun L' hL' hmov' =>
        moved_eq_range hp hq hs D hA hsA hs1 hz₁A hz₁1 hz₁s hb₁ hL' hmov' }⟩

end S

end CFSG.ClassicalInvolution.NDB
