module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Models
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Q
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Center
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicOvergroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndexResidue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviMain

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.McLaughlin

section Aux

variable {Q : Type} [Group Q]

theorem index_map_subgroupOf_dvd {Lb P E : Subgroup Q} (hPL : P ≤ Lb) (hEP : E ≤ P) :
    (((E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))).subgroupOf
      ((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))).index ∣
      E.relIndex P := by
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set Jim : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := P'.map ρ with hJim
  let φ : ↥P' →* ↥Jim := (ρ.comp P'.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hle : E'.subgroupOf P' ≤ ((E'.map ρ).subgroupOf Jim).comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have h1 := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ hφ] at h1
  have h2 : (E'.subgroupOf P').index = E.relIndex P := by
    rw [← Subgroup.relIndex_subgroupOf (H := E) (K := P) (L := Lb) hPL]
    rfl
  rwa [h2] at h1

end Aux

section Small

variable {X : Type} [Group X]

theorem false_of_nineFree (hNF : NineFreeOver X) (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    {T J : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set X) ≤ J)
    (hperf : ∀ U : Subgroup X, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (h9 : 9 ∣ Nat.card J) : False := by
  have htop := hNF _ _ hT (Subgroup.le_normalizer.trans hNJ) h9
  have hc := hperf ⊤ htop.ge hX
  rw [← htop] at hc
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc ((dvd_mul_right 3 3).trans h9)

end Small

section Main


theorem kFactParabolicE9NotTransitive_proved (hG : GriessAllModelsStatement) :
    KFactParabolicE9NotTransitive := by
  classical
  intro Q _ _ Lb P E N hqs hcl hpar hnot hno hEP hEel hE9 hsyl hNL hNE hNP htr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : P ≤ Lb := hpar.1
  have hEL : E ≤ Lb := hEP.trans hPL
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  have hE'card : Nat.card E' = 9 := by
    rw [hE', ← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hE3 : IsPGroup 3 E := isPGroup_of_isElemAbelian hEel
  have hE'3 : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEL).symm
  obtain ⟨T, hT, hNJ, hJ, hperf⟩ := exists_overgroup_quotient_map Lb P hpar hnot hno
  have hcen := kFactParabolicThreeCensus _ hcl T _ hT hNJ hJ hperf
  have hZ9 : ¬ 9 ∣ Nat.card (Subgroup.center ↥Lb) := fun h9 =>
    not_nine_dvd_card_griess_of_census hG hcen
      (h9.trans (card_center_dvd_card_griessHopfMultiplier
        (OutElemRank.isPerfect_of_quasisimple hqs) (MulEquiv.refl _)))
  by_cases hA : E' ≤ Subgroup.center ↥Lb
  · exact hZ9 (hE'card ▸ Subgroup.card_dvd_of_le hA)
  by_cases hB : ∃ x ∈ E', x ≠ 1 ∧ x ∈ Subgroup.center ↥Lb
  ·
    obtain ⟨x, hxE, hx1, hxZ⟩ := hB
    set W : Subgroup Q := E ⊓ (Subgroup.center ↥Lb).map Lb.subtype with hW
    have hWE : W ≤ E := inf_le_left
    have hNW : N ≤ Subgroup.normalizer (W : Set Q) := by
      intro n hn
      have key : ∀ m ∈ N, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
        intro m hm w hw
        obtain ⟨hwE, z, hz, rfl⟩ := Subgroup.mem_inf.mp hw
        have hmL := hNL hm
        have hmL' : m⁻¹ ∈ Subgroup.normalizer (Lb : Set Q) := hNL (N.inv_mem hm)
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hNE hm) _).mp hwE,
          ⟨⟨m * z * m⁻¹, (Subgroup.mem_normalizer_iff.mp hmL _).mp z.2⟩, ?_, rfl⟩⟩
        show _ ∈ Subgroup.center ↥Lb
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have hy : m⁻¹ * y * m ∈ Lb := by
          have := (Subgroup.mem_normalizer_iff.mp hmL' (y : Q)).mp y.2
          simpa using this
        have hc := Subgroup.mem_center_iff.mp hz ⟨m⁻¹ * y * m, hy⟩
        have hc' := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at hc' ⊢
        calc (y : Q) * (m * z * m⁻¹) = m * ((m⁻¹ * y * m) * z) * m⁻¹ := by group
          _ = m * (z * (m⁻¹ * y * m)) * m⁻¹ := by rw [hc']
          _ = m * z * m⁻¹ * y := by group
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact ⟨fun h' => key n hn _ h', fun h' => by
        have := key n⁻¹ (N.inv_mem hn) _ h'
        simpa [mul_assoc] using this⟩
    rcases irreducibleOn_of_transitiveOnNonidentity htr W hWE hNW with h | h
    · have hx' : (x : Q) ∈ W := Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxE,
        ⟨x, hxZ, rfl⟩⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact hx1 (Subtype.ext hx')
    · apply hA
      intro y hy
      have hyE : (y : Q) ∈ E := Subgroup.mem_subgroupOf.mp hy
      rw [← h] at hyE
      obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_inf.mp hyE).2
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
  push Not at hB
  have hinj : ∀ x ∈ E', ρ x = 1 → x = 1 := fun x hx hx1 =>
    by_contra fun hne => hB x hx hne ((QuotientGroup.eq_one_iff x).mp hx1)
  have hcardE : Nat.card (E'.map ρ) = 9 := by
    rw [card_map_eq_of_inj_on ρ hinj, hE'card]
  have hEJ : E'.map ρ ≤ P'.map ρ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hEP (Subgroup.mem_subgroupOf.mp hx))
  have hsyl' : ¬ 3 ∣ ((E'.map ρ).subgroupOf (P'.map ρ)).index := fun h =>
    hsyl (h.trans (index_map_subgroupOf_dvd hPL hEP))
  have hXp : ⁅(⊤ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)),
      (⊤ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb))⁆ = ⊤ := by
    have hLp : Group.IsPerfect ↥Lb := OutElemRank.isPerfect_of_quasisimple hqs
    have : Group.IsPerfect (↥Lb ⧸ Subgroup.center ↥Lb) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact this.commutator_eq_top
  have h9J : 9 ∣ Nat.card (P'.map ρ) := hcardE ▸ Subgroup.card_dvd_of_le hEJ
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hNJ' := hNJ
  have hJ' := hJ
  rw [← hS] at hNJ' hJ'
  have hsep : ∀ {t : CFSG.Open.StatedLieTag} {n : ℕ},
      CFSG.Open.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) t n 2 1 →
      (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU) →
      ¬ TransitiveOnNonidentity N E := fun {t n} hc ht =>
    not_transitive_of_separated hPL hEP hNL hNP
      (separated_pair_of_model hc ht S _ hNJ' hJ' hperf hEJ hcardE hsyl')
  have hmodel : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ},
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) t n 2 1 →
      (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU) →
      ¬ TransitiveOnNonidentity N E := by
    intro t n hc ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact hsep (t := .PSL) hc (Or.inl rfl)
    · exact hsep (t := .PSp) hc (Or.inr (Or.inl rfl))
    · exact hsep (t := .POmegaPlus) hc (Or.inr (Or.inr (Or.inl rfl)))
    · exact hsep (t := .POmegaMinus) hc (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hsep (t := .PSU) hc (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ?_
  rcases hcen with ⟨d, hd, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
    exact hmodel hc ht htr
  · rcases hm with rfl | rfl | rfl
    ·
      have h60 : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      have := h9J.trans (Subgroup.card_subgroup_dvd_card _)
      rw [h60] at this
      norm_num at this
    · exact false_of_nineFree (NineFreeOver.of_mulEquiv e.symm nineFreeOver_alt_six) hXp hT hNJ
        hperf h9J
    · exact hmodel (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight
        _ ⟨e⟩) (Or.inl rfl) htr
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    · exact false_of_nineFree (nineFreeOver_catalog_seven hq hd' e) hXp hT hNJ hperf h9J
    · exact false_of_nineFree (nineFreeOver_catalog_psu_three_three hq hd' e) hXp hT hNJ hperf h9J

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
