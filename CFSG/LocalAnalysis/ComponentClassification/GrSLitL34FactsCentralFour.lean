module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

@[expose] def zTwo (P : Subgroup G) : Subgroup G := (Subgroup.upperCentralSeries ↥P 2).map P.subtype

theorem mem_zTwo {P : Subgroup G} {y : G} :
    y ∈ zTwo P ↔ y ∈ P ∧ ∀ w ∈ P, ∀ w' ∈ P,
      y * w * y⁻¹ * w⁻¹ * w' = w' * (y * w * y⁻¹ * w⁻¹) := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, fun w hw w' hw' => ?_⟩
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hy' ⟨w, hw⟩
    rw [Subgroup.upperCentralSeries_one, mem_center_iff] at h1
    have h2 := congrArg Subtype.val (h1 ⟨w', hw'⟩)
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h2
    exact h2.symm
  · rintro ⟨hy, h⟩
    refine ⟨⟨y, hy⟩, (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun w => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one, mem_center_iff]
    intro w'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
    exact (h w w.2 w' w'.2).symm

theorem conj_mem_zTwo {P : Subgroup G} {g : G} (hg : g ∈ normalizer (P : Set G)) {y : G}
    (hy : y ∈ zTwo P) : g * y * g⁻¹ ∈ zTwo P := by
  obtain ⟨hyP, h⟩ := mem_zTwo.1 hy
  refine mem_zTwo.2 ⟨(mem_normalizer_iff.mp hg y).mp hyP, fun w hw w' hw' => ?_⟩
  have hc : ∀ v ∈ P, g⁻¹ * v * g ∈ P := fun v hv => by
    have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
    rwa [inv_inv] at this
  have h1 := h _ (hc w hw) _ (hc w' hw')
  calc g * y * g⁻¹ * w * (g * y * g⁻¹)⁻¹ * w⁻¹ * w' =
      g * (y * (g⁻¹ * w * g) * y⁻¹ * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * w' * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * w' * g) * (y * (g⁻¹ * w * g) * y⁻¹ * (g⁻¹ * w * g)⁻¹)) * g⁻¹ := by rw [h1]
    _ = w' * (g * y * g⁻¹ * w * (g * y * g⁻¹)⁻¹ * w⁻¹) := by group

theorem normalizer_le_omegaOne_zTwo (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (omegaOne (zTwo P) : Set G) := by
  have key : ∀ g ∈ normalizer (P : Set G), ∀ h ∈ omegaOne (zTwo P),
      g * h * g⁻¹ ∈ omegaOne (zTwo P) := by
    intro g hg h hh
    have hmap : (omegaOne (zTwo P)).map (MulAut.conj g).toMonoidHom ≤ omegaOne (zTwo P) := by
      rw [omegaOne, MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, ⟨hy, hy2⟩, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨conj_mem_zTwo hg hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    exact hmap ⟨h, hh, rfl⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem Z0_le_T0 : Z0 ≤ T0 := inf_le_right

theorem l34CentralFourFact :
    L34CentralFourFact := by
  intro G _ _ J P x hJ hL hP hx hxP hcyc hz4
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hβ, hT⟩ := exists_standard hJ hL hx hP hxP
  have hxN := hx.1
  have hU : IsUSetting q l (betaHat J hxN) := ⟨hqS, hqsurj, hqker, h3, hl, hls, hβ⟩
  have hQ := hU.toQ
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  have hcyc' : ¬ IsCyclic q.ker := fun h =>
    hcyc (isCyclic_of_surjective ζ.symm.toMonoidHom ζ.symm.surjective)
  have hk4 : ∃ e ∈ q.ker, e * e ≠ 1 := by
    obtain ⟨z, hz, hz1⟩ := hz4
    obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
    refine ⟨jq J ⟨z, hP.1 hzP⟩, by rw [hqker]; exact (mem_zStarIn_iff _).1 hzZ, fun h => hz1 ?_⟩
    rw [← map_mul] at h
    exact eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hzP hzP) h
  obtain ⟨hΩe, hΩ16, hΩZ, hrep, hinv⟩ := hU.omegaZ_props hcyc'
  have hΩT : omegaZ q l (betaHat J hxN) ≤ T0.comap q := hΩZ.trans (comap_mono Z0_le_T0)
  have hmulP : ∀ {a b : G} (ha : a ∈ P) (hb : b ∈ P),
      jq J ⟨a * b, hP.1 (P.mul_mem ha hb)⟩ = jq J ⟨a, hP.1 ha⟩ * jq J ⟨b, hP.1 hb⟩ :=
    fun ha hb => by rw [← map_mul]; rfl
  have hinvP : ∀ {a : G} (ha : a ∈ P), jq J ⟨a⁻¹, hP.1 (P.inv_mem ha)⟩ = (jq J ⟨a, hP.1 ha⟩)⁻¹ :=
    fun ha => by rw [← map_inv]; rfl
  have hTP : ∀ {a : G} (ha : a ∈ P), q (jq J ⟨a, hP.1 ha⟩) ∈ T0 := fun ha =>
    (hT _).2 ⟨_, ha, _, rfl⟩
  have hcen : ∀ {c : G} (hc : c ∈ P), (∀ w ∈ P, c * w = w * c) → q (jq J ⟨c, hP.1 hc⟩) = 1 := by
    intro c hc hcw
    refine hQ.q_eq_one_of_central hk4 (hTP hc) fun e' he' => ?_
    obtain ⟨w, hwP, hwJ, rfl⟩ := (hT e').1 he'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcw w hwP)
  have hcomm : ∀ {y w : G} (hy : y ∈ P) (hw : w ∈ P), y⁻¹ * w⁻¹ * y * w ∈ zStarIn J ↔
      q (jq J ⟨y, hP.1 hy⟩) * q (jq J ⟨w, hP.1 hw⟩) =
        q (jq J ⟨w, hP.1 hw⟩) * q (jq J ⟨y, hP.1 hy⟩) := by
    intro y w hy hw
    have hm : y⁻¹ * w⁻¹ * y * w ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hy) (P.inv_mem hw)) hy) hw
    rw [mem_zStarIn_iff (hP.1 hm), ← hqker, MonoidHom.mem_ker]
    have e : (⟨y⁻¹ * w⁻¹ * y * w, hP.1 hm⟩ : J) = (⟨y, hP.1 hy⟩ : J)⁻¹ *
        (⟨w, hP.1 hw⟩ : J)⁻¹ * ⟨y, hP.1 hy⟩ * ⟨w, hP.1 hw⟩ := rfl
    rw [e]
    simp only [map_mul, map_inv]
    generalize q (jq J ⟨y, hP.1 hy⟩) = a
    generalize q (jq J ⟨w, hP.1 hw⟩) = b
    constructor
    · intro h
      calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
        _ = b * a := by rw [h, mul_one]
    · intro h
      rw [mul_assoc a⁻¹ b⁻¹ a, ← mul_assoc, mul_assoc _ a b, h]
      group
  have hZ0 : ∀ {y : G} (hy : y ∈ P), q (jq J ⟨y, hP.1 hy⟩) ∈ Z0 ↔
      ∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J := by
    intro y hy
    constructor
    · intro hyZ w hw
      exact (hcomm hy hw).2 ((mem_centralizer_iff.mp hyZ.1) _ (hTP hw)).symm
    · intro h
      refine ⟨mem_centralizer_iff.mpr fun t ht => ?_, hTP hy⟩
      obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht)
      obtain ⟨w, hwP, hwJ, rfl⟩ := (hT e).1 (he ▸ ht)
      rw [← he]
      exact ((hcomm hy hwP).1 (h w hwP)).symm
  have hzTwo : ∀ {y : G}, y ∈ zTwo P ↔ ∃ hy : y ∈ P, q (jq J ⟨y, hP.1 hy⟩) ∈ Z0 := by
    intro y
    rw [mem_zTwo]
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, (hZ0 hy).2 fun w hw => (hcomm hy hw).2 ?_⟩
      have hc : y * w * y⁻¹ * w⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem (P.mul_mem hy hw) (P.inv_mem hy)) (P.inv_mem hw)
      have h1 := hcen hc fun w' hw' => h w hw w' hw'
      have e : (⟨y * w * y⁻¹ * w⁻¹, hP.1 hc⟩ : J) = ⟨y, hP.1 hy⟩ * ⟨w, hP.1 hw⟩ *
          (⟨y, hP.1 hy⟩ : J)⁻¹ * (⟨w, hP.1 hw⟩ : J)⁻¹ := rfl
      rw [e] at h1
      simp only [map_mul, map_inv] at h1
      generalize q (jq J ⟨y, hP.1 hy⟩) = a at h1 ⊢
      generalize q (jq J ⟨w, hP.1 hw⟩) = b at h1 ⊢
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · rintro ⟨hy, hyZ⟩
      refine ⟨hy, fun w hw w' hw' => ?_⟩
      have hc : y * w * y⁻¹ * w⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem (P.mul_mem hy hw) (P.inv_mem hy)) (P.inv_mem hw)
      have hk : jq J ⟨y * w * y⁻¹ * w⁻¹, hP.1 hc⟩ ∈ center (Jhat J) := by
        rw [← hqker, MonoidHom.mem_ker]
        have e : (⟨y * w * y⁻¹ * w⁻¹, hP.1 hc⟩ : J) = ⟨y, hP.1 hy⟩ * ⟨w, hP.1 hw⟩ *
            (⟨y, hP.1 hy⟩ : J)⁻¹ * (⟨w, hP.1 hw⟩ : J)⁻¹ := rfl
        rw [e]
        simp only [map_mul, map_inv]
        rw [← (mem_centralizer_iff.mp hyZ.1) _ (hTP hw)]
        group
      apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hc hw') (P.mul_mem hw' hc)
      rw [hmulP hc hw', hmulP hw' hc]
      exact ((mem_center_iff.mp hk) _).symm
  have hC : omegaOne (zTwo P) = pullP J P hP.1 (omegaZ q l (betaHat J hxN)) := by
    apply le_antisymm
    · rw [omegaOne, closure_le]
      rintro y ⟨hy, hy2⟩
      obtain ⟨hyP, hyZ⟩ := hzTwo.1 hy
      refine mem_pullP.2 ⟨hyP, hinv _ hyZ ?_⟩
      rw [← hmulP hyP hyP]
      have : (⟨y * y, hP.1 (P.mul_mem hyP hyP)⟩ : J) = 1 := Subtype.ext hy2
      rw [this, map_one]
    · intro y hy
      obtain ⟨hyP, hyΩ⟩ := mem_pullP.1 hy
      apply Subgroup.subset_closure
      refine ⟨hzTwo.2 ⟨hyP, hΩZ hyΩ⟩, ?_⟩
      apply eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hyP hyP)
      rw [hmulP hyP hyP]
      exact hΩe.2 _ hyΩ
  refine ⟨omegaOne (zTwo P), ?_, ?_, ?_, ?_, ?_, normalizer_le_omegaOne_zTwo P⟩
  · rw [hC]
    exact pullP_le _
  · rw [hC]
    exact isElemTwo_pullP hP2 hΩe
  · rw [hC, card_pullP hP2 hT hΩT, hΩ16]
  · rw [hC]
    intro p hp
    obtain ⟨θ, hθ⟩ := exists_theta hxN hP hxP hT
    have hm := (θ ⟨p, hp⟩).2
    rw [hθ] at hm
    obtain ⟨-, hsq, -⟩ := hU.noncyclic_case hcyc'
    have h2 := hsq _ hm
    have hq8 := hU.q_mem_Q8_of_fix hm
    have hqZ : q (jq J ⟨p, hP.1 hp.1⟩) ∈ Z0 := by
      rcases eq_of_mem_Q8_of_mul_self hq8 (by rw [← map_mul, h2, map_one]) with h1 | h1
      · rw [h1]
        exact one_mem _
      · rw [h1]
        exact mem_Z0.2 ⟨4, by decide, rfl⟩
    exact mem_pullP.2 ⟨hp.1, hinv _ hqZ h2⟩
  · intro y hy
    constructor
    · intro h
      have hyZ := (hZ0 hy).2 h
      obtain ⟨ω, hω, hωy⟩ := hrep _ hyZ
      obtain ⟨c, hc, hcJ, hcω⟩ := exists_mem_pullP (hPJ := hP.1) hT hΩT hω
      have hcP := pullP_le _ hc
      have hz : c⁻¹ * y ∈ P ⊓ zStarIn J := by
        refine mem_inf.mpr ⟨P.mul_mem (P.inv_mem hcP) hy, ?_⟩
        rw [mem_zStarIn_iff (hP.1 (P.mul_mem (P.inv_mem hcP) hy)), ← hqker]
        have e : (⟨c⁻¹ * y, hP.1 (P.mul_mem (P.inv_mem hcP) hy)⟩ : J) =
            (⟨c, hcJ⟩ : J)⁻¹ * ⟨y, hP.1 hy⟩ := rfl
        rw [e, map_mul, map_inv, hcω]
        exact hωy
      have hy' : y = c * (c⁻¹ * y) := by group
      have hcC : c ∈ omegaOne (zTwo P) := by rw [hC]; exact hc
      rw [hy']
      exact mul_mem (mem_sup_left hcC) (mem_sup_right hz)
    · intro h
      have hle : omegaOne (zTwo P) ⊔ (P ⊓ zStarIn J) ≤ pullP J P hP.1 (Z0.comap q) := by
        refine sup_le ?_ fun z hz => ?_
        · rw [hC]
          exact pullP_mono hΩZ
        · obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
          refine mem_pullP.2 ⟨hzP, ?_⟩
          have hk : jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
            rw [hqker]
            exact (mem_zStarIn_iff _).1 hzZ
          rw [mem_comap, MonoidHom.mem_ker.mp hk]
          exact one_mem _
      exact (hZ0 hy).1 (mem_pullP.1 (hle h)).2

end CFSG.ComponentClassification.GrSLit.L34Facts
