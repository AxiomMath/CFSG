module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicEightModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem cyclicCentralEight :
    ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (a : G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
      IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 → a ∈ P ⊓ zStarIn J →
      a * a = 1 → a ≠ 1 →
      ∃ B : Subgroup G, B ≤ P ∧ IsEightGroup B ∧ B ⊓ zStarIn J = zpowers a ∧
        (∀ y ∈ P, y ∈ B ↔ y * y = 1 ∧ ∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ∧
        (∀ y ∈ P, (∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ B ⊔ (P ⊓ zStarIn J)) ∧
        B ≤ closure {t | ∃ s ∈ P ⊓ centralizer (B : Set G), t = s * s} := by
  intro G _ _ J P a hJ hL hP hcyc h4 ha ha2 ha1
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨ζe, -⟩ := exists_zeta hP hqker
  have hkcyc : IsCyclic q.ker := isCyclic_of_surjective ζe.toMonoidHom ζe.surjective
  have hk4 : Nat.card q.ker = 4 := by rw [← Nat.card_congr ζe.toEquiv, h4]
  obtain ⟨haP, haZ⟩ := mem_inf.mp ha
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  have hâk : jq J ⟨a, hP.1 haP⟩ ∈ q.ker := by
    rw [hqker]
    exact (mem_zStarIn_iff _).1 haZ
  have hâ2 : jq J ⟨a, hP.1 haP⟩ * jq J ⟨a, hP.1 haP⟩ = 1 := by
    rw [← hmulP haP haP]
    have : (⟨a * a, hP.1 (P.mul_mem haP haP)⟩ : J) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hâ1 : jq J ⟨a, hP.1 haP⟩ ≠ 1 := fun h => ha1 (eq_one_of_jq_eq_one hP.1 hP2 haP h)
  set â := jq J ⟨a, hP.1 haP⟩ with hâ
  obtain ⟨hA8, hAZ⟩ := hQ.exists_A0 hâk hâ1 hâ2
  have hA8' : IsEightGroup (A0 l â) := hA8
  have hAZ' : A0 l â ≤ Z0.comap q := hAZ
  have hAT : A0 l â ≤ T0.comap q := hAZ'.trans (comap_mono (inf_le_right : Z0 ≤ T0))
  set B := pullP J P hP.1 (A0 l â) with hB
  have hBe : IsElemTwo B := isElemTwo_pullP hP2 hA8'.1
  have hB8 : Nat.card B = 8 := by rw [hB, card_pullP hP2 hT hAT, hA8'.2]
  have hBP : B ≤ P := pullP_le _
  have hzZ : ∀ {z : G} (hzP : z ∈ P), z ∈ zStarIn J ↔ jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
    intro z hzP
    rw [mem_zStarIn_iff, hqker]
  have hcommZ : ∀ {y : G} (hy : y ∈ P),
      q (jq J ⟨y, hP.1 hy⟩) ∈ Z0 ↔ ∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J :=
    fun hy => mem_Z0_iff_comm hP hqsurj hqker hT hy
  refine ⟨B, hBP, ⟨hBe, hB8⟩, ?_, fun y hy => ?_, fun y hy => ?_, ?_⟩
  ·
    apply le_antisymm
    · intro y hy
      obtain ⟨hyB, hyZ⟩ := mem_inf.mp hy
      obtain ⟨hyP, hyA⟩ := mem_pullP.1 hyB
      have hyk := (hzZ hyP).1 hyZ
      have hmem : jq J ⟨y, hP.1 hyP⟩ ∈ zpowers â := by
        rw [← hQ.A0_inf_ker hkcyc hk4 hâk hâ1 hâ2]
        exact mem_inf.mpr ⟨hyA, hyk⟩
      rcases eq_one_or_eq_of_mem_zpowers hâ2 hmem with h | h
      · rw [eq_one_of_jq_eq_one hP.1 hP2 hyP h]
        exact one_mem _
      · rw [eq_of_jq_eq hP.1 hP2 hyP haP h]
        exact mem_zpowers a
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨mem_pullP.2 ⟨haP, mem_sup_right (mem_sup_right (mem_zpowers _))⟩, haZ⟩
  ·
    constructor
    · intro hyB
      obtain ⟨hyP, hyA⟩ := mem_pullP.1 hyB
      exact ⟨hBe.2 y hyB, (hcommZ hyP).1 (hAZ' hyA)⟩
    · rintro ⟨hy2, hc⟩
      have hyZ0 := (hcommZ hy).2 hc
      refine mem_pullP.2 ⟨hy, hQ.inv_mem_A0 hkcyc hk4 hâk hâ1 hâ2 hyZ0 ?_⟩
      rw [← hmulP hy hy]
      have : (⟨y * y, hP.1 (P.mul_mem hy hy)⟩ : J) = 1 := Subtype.ext hy2
      rw [this, map_one]
  ·
    constructor
    · intro hc
      obtain ⟨ω, hω, hωk⟩ := hQ.exists_rep_A0 â ((hcommZ hy).2 hc)
      obtain ⟨b, hb, hbJ, hbω⟩ := exists_mem_pullP (hPJ := hP.1) hT hAT hω
      have hbP := hBP hb
      have hz : b⁻¹ * y ∈ P ⊓ zStarIn J := by
        refine mem_inf.mpr ⟨P.mul_mem (P.inv_mem hbP) hy, ?_⟩
        rw [hzZ (P.mul_mem (P.inv_mem hbP) hy)]
        have e1 : (⟨b⁻¹ * y, hP.1 (P.mul_mem (P.inv_mem hbP) hy)⟩ : J) =
            (⟨b, hbJ⟩ : J)⁻¹ * ⟨y, hP.1 hy⟩ := rfl
        rw [e1, map_mul, map_inv, hbω]
        exact hωk
      rw [show y = b * (b⁻¹ * y) by group]
      exact mul_mem (mem_sup_left hb) (mem_sup_right hz)
    · intro hy'
      have hle : B ⊔ (P ⊓ zStarIn J) ≤ pullP J P hP.1 (Z0.comap q) := by
        refine sup_le (pullP_mono hAZ') fun z hz => ?_
        obtain ⟨hzP, hzZ'⟩ := mem_inf.mp hz
        refine mem_pullP.2 ⟨hzP, ?_⟩
        rw [mem_comap, MonoidHom.mem_ker.mp ((hzZ hzP).1 hzZ')]
        exact one_mem _
      obtain ⟨hyP, hyZ0⟩ := mem_pullP.1 (hle hy')
      exact (hcommZ hyP).1 hyZ0
  ·
    set H := closure {t | ∃ s ∈ P ⊓ centralizer (B : Set G), t = s * s} with hH
    have hsq : ∀ {s : G}, s ∈ P → (∀ b ∈ B, s * b = b * s) → s * s ∈ H := by
      intro s hsP hsB
      refine subset_closure ⟨s, mem_inf.mpr ⟨hsP, mem_centralizer_iff.mpr fun b hb => ?_⟩, rfl⟩
      exact (hsB b hb).symm
    obtain ⟨g, hg1, hg⟩ := cyclic_four hk4
    have hâg : (⟨â, hâk⟩ : q.ker) = g * g := by
      rcases (hg ⟨_, hâk⟩).1.1 (Subtype.ext hâ2) with h | h
      · exact absurd (congrArg Subtype.val h) hâ1
      · exact h
    have hgc : (g : Jhat J) ∈ center (Jhat J) := hqker ▸ g.2
    obtain ⟨z, hzP, hzJ, hzg⟩ := exists_mem_of_mem_center hP hgc
    have hzZ' : z ∈ zStarIn J := (mem_zStarIn_iff hzJ).2 (hzg ▸ hgc)
    have hza : z * z = a := by
      apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hzP hzP) haP
      rw [hmulP hzP hzP]
      have e1 : (⟨z, hP.1 hzP⟩ : J) = ⟨z, hzJ⟩ := rfl
      rw [e1, hzg]
      exact (congrArg Subtype.val hâg).symm
    have haH : a ∈ H := by
      rw [← hza]
      exact hsq hzP fun b hb => comm_of_mem_Z hP (mem_inf.mpr ⟨hzP, hzZ'⟩) (hBP hb)
    obtain ⟨s₁, s₂, hs₁T, hs₂T, hs₁c, hs₂c, hs₁4, hs₂4, hq₁, hq₂⟩ :=
      hQ.exists_cce hkcyc hk4 hâk hâ1 hâ2
    obtain ⟨p₁, hp₁P, hp₁J, hp₁e⟩ := (hT s₁).1 hs₁T
    obtain ⟨p₂, hp₂P, hp₂J, hp₂e⟩ := (hT s₂).1 hs₂T
    have hcB : ∀ {p : G} (hpP : p ∈ P) {s : Jhat J}, jq J ⟨p, hP.1 hpP⟩ = s →
        (∀ x ∈ A0 l â, s * x = x * s) → ∀ b ∈ B, p * b = b * p := by
      intro p hpP s hps hsc b hb
      obtain ⟨hbP, hbA⟩ := mem_pullP.1 hb
      apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hpP hbP) (P.mul_mem hbP hpP)
      rw [hmulP hpP hbP, hmulP hbP hpP, hps]
      exact hsc _ hbA
    have hsqB : ∀ {p : G} (hpP : p ∈ P) {s : Jhat J}, jq J ⟨p, hP.1 hpP⟩ = s → s ^ 4 = 1 →
        q (s * s) ∈ Z0 → p * p ∈ B := by
      intro p hpP s hps hs4 hsZ
      refine mem_pullP.2 ⟨P.mul_mem hpP hpP, ?_⟩
      rw [hmulP hpP hpP, hps]
      refine hQ.inv_mem_A0 hkcyc hk4 hâk hâ1 hâ2 hsZ ?_
      rw [← pow_four_eq]
      exact hs4
    have hp₁' : jq J ⟨p₁, hP.1 hp₁P⟩ = s₁ := hp₁e
    have hp₂' : jq J ⟨p₂, hP.1 hp₂P⟩ = s₂ := hp₂e
    have hZ4 : wordPerm (tg 4) ∈ Z0 := mem_Z0.2 ⟨4, by decide, rfl⟩
    have hZ8 : wordPerm (tg 8) ∈ Z0 := mem_Z0.2 ⟨8, by decide, rfl⟩
    have hb₁B := hsqB hp₁P hp₁' hs₁4 (hq₁ ▸ hZ4)
    have hb₂B := hsqB hp₂P hp₂' hs₂4 (hq₂ ▸ hZ8)
    have hb₁H := hsq hp₁P (hcB hp₁P hp₁' hs₁c)
    have hb₂H := hsq hp₂P (hcB hp₂P hp₂' hs₂c)
    have haB : a ∈ B := mem_pullP.2 ⟨haP, mem_sup_right (mem_sup_right (mem_zpowers _))⟩
    have hqb : ∀ {p : G} (hpP : p ∈ P), q (jq J ⟨p * p, hP.1 (P.mul_mem hpP hpP)⟩) =
        q (jq J ⟨p, hP.1 hpP⟩ * jq J ⟨p, hP.1 hpP⟩) := fun hpP => by rw [hmulP hpP hpP]
    have h4ne : wordPerm (tg 4) ≠ 1 := fun h => by
      rw [← wordPerm_tg_zero] at h
      exact absurd (tg_injective (by norm_num) (by norm_num) h) (by norm_num)
    have hb₁a : p₁ * p₁ ∉ zpowers a := fun hm => by
      rcases eq_one_or_eq_of_mem_zpowers ha2 hm with h | h
      · have := hqb hp₁P
        rw [hp₁', hq₁] at this
        apply h4ne
        rw [← this]
        have e1 : (⟨p₁ * p₁, hP.1 (P.mul_mem hp₁P hp₁P)⟩ : J) = 1 := Subtype.ext h
        rw [e1, map_one, map_one]
      · have := hqb hp₁P
        rw [hp₁', hq₁] at this
        apply h4ne
        rw [← this]
        have e1 : (⟨p₁ * p₁, hP.1 (P.mul_mem hp₁P hp₁P)⟩ : J) = ⟨a, hP.1 haP⟩ := Subtype.ext h
        rw [e1]
        exact hâk
    have hb₂n : p₂ * p₂ ∉ zpowers (p₁ * p₁) ⊔ zpowers a := fun hm => by
      have hle : zpowers (p₁ * p₁) ⊔ zpowers a ≤
          pullP J P hP.1 ((zpowers (wordPerm (tg 4))).comap q) := by
        refine sup_le (zpowers_le.2 (mem_pullP.2 ⟨P.mul_mem hp₁P hp₁P, ?_⟩))
          (zpowers_le.2 (mem_pullP.2 ⟨haP, ?_⟩))
        · rw [mem_comap, hqb hp₁P, hp₁', hq₁]
          exact mem_zpowers _
        · rw [mem_comap, MonoidHom.mem_ker.mp hâk]
          exact one_mem _
      obtain ⟨hm₂, hm'⟩ := mem_pullP.1 (hle hm)
      rw [mem_comap, hqb hp₂P, hp₂', hq₂] at hm'
      exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hQ.tg_mul_self_of_ilift (d := (4, 1, 1, 1)) (by decide) (by norm_num)) hm'
    have h8 := isEightGroup_of_three ha2 (hBe.2 _ hb₁B) (hBe.2 _ hb₂B)
      (hBe.1 _ haB _ hb₁B) (hBe.1 _ haB _ hb₂B) (hBe.1 _ hb₁B _ hb₂B) ha1 hb₁a hb₂n
    have hleB : zpowers (p₂ * p₂) ⊔ (zpowers (p₁ * p₁) ⊔ zpowers a) ≤ B :=
      sup_le (zpowers_le.2 hb₂B) (sup_le (zpowers_le.2 hb₁B) (zpowers_le.2 haB))
    have heq := eq_of_le_of_card_ge hleB (by rw [hB8, h8.2])
    rw [← heq]
    exact sup_le (zpowers_le.2 hb₂H) (sup_le (zpowers_le.2 hb₁H) (zpowers_le.2 haH))

end CFSG.ComponentClassification.GrSLit.L34Facts
