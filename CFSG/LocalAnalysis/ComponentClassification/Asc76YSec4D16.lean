module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D15
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D14

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem normalClosure_eq_top_of_single (hΩ : Assumption41 Ω) {K₀ : Subgroup G}
    (hall : ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g) :
    normalClosure (K₀ : Set G) = ⊤ := by
  rw [eq_top_iff, ← hΩ.generates]
  refine sSup_le fun L hL => ?_
  obtain ⟨g, rfl⟩ := hall L hL
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h1 := (normalClosure_normal (s := (K₀ : Set G))).conj_mem _ (subset_normalClosure hx) g⁻¹
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem MinCounter.sylowNormalizes (h22 : Asc76Lemma22) {S : Subgroup G} (hM : MinCounter Ω S)
    (hZ2 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ →
      ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S' : Set G) → x ∈ sec4W Ω S')
    (hno4 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ → ∀ a b : G, a ∈ sec4W Ω S' → IsZInv Ω a →
      b ∈ sec4W Ω S' → IsZInv Ω b → a ≠ b → IsZInv Ω (a * b) → False)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (heven : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))) :
    SylowNormalizes J K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  obtain ⟨⟨v₀, hv₀⟩, hv₀2⟩ := exists_prime_orderOf_dvd_card'
    (G := (J ⊓ normalizer (K : Set G) : Subgroup G)) 2 (even_iff_two_dvd.mp heven)
  rw [Subgroup.orderOf_mk] at hv₀2
  have hv₀P : IsPGroup 2 (zpowers v₀) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, ← hv₀2, pow_orderOf_eq_one])
  obtain ⟨V, hV, hv₀V⟩ := exists_isSylowOf_le hv₀P ((zpowers_le).mpr hv₀)
  have hV1 : V ≠ ⊥ := by
    intro h
    have := hv₀V (mem_zpowers v₀)
    rw [h, mem_bot] at this
    rw [this, orderOf_one] at hv₀2
    omega
  obtain ⟨R, hR, hVR⟩ := exists_isSylowOf_normalized hV.isPGroup (hV.le.trans inf_le_right)
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have hcardU := hU.card_eq
  have h4 := hU.four_le
  rcases lemma415 h22 hΩ hK hJ hR hU hV hV1 hVR with ⟨hVJ, -, -⟩ | ⟨⟨e⟩, hcomm, -, -⟩ |
    ⟨hV2, hD, hinv⟩
  · exact ⟨V, hVJ, hV.le.trans inf_le_right⟩
  ·
    exfalso
    have hcardV : Nat.card V = Nat.card U := Nat.card_congr e.toEquiv
    have hKJ : K ≠ J := by
      rintro rfl
      have hVK : IsSylowOf 2 V K := by
        have h1 := hV
        rwa [inf_eq_left.mpr le_normalizer] at h1
      have := Assumption41.card_sylow_eq hΩ hK hK hVK hR
      omega
    have hVc : IsCyclic V := by
      have := hU.isCyclic
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨T, hT, hVT⟩ := exists_isDihedralRot_of_isCyclic hΩ hJ hK hR hU
      (hV.le.trans inf_le_left) hV.isPGroup hVc hcardV
    have hP : IsPGroup 2 (V ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hV.isPGroup hR.isPGroup hVR
    obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP (le_top : V ⊔ R ≤ ⊤)
    have hRW' : R ≤ normalizer (sec4W Ω S' : Set G) :=
      (le_sup_right.trans hPS').trans (le_normalizer_sec4W hΩ.conj_mem S')
    have hUW' : U ≤ sec4W Ω S' := rot_le_sec4W hΩ hS' hK hR hU hRW'
    have hVW' : V ≤ sec4W Ω S' := le_sec4W (le_sup_left.trans hPS') (isRot_of hJ hT hVT)
    obtain ⟨T₁, hT₁, hVT₁, hT₁W'⟩ :=
      exists_isSylowOf_le_normalizer_of_isRot hΩ hS' hJ hT hVT hVW'
    have hnot : ¬ T₁ ≤ normalizer (K : Set G) := by
      intro h
      obtain ⟨hJK, -⟩ := le_normalizer_of_sylow h22 hΩ hK hJ hKJ hT₁ h
      have hVJ : IsSylowOf 2 V J := by
        have h1 := hV
        rwa [inf_eq_left.mpr hJK] at h1
      have := Assumption41.card_sylow_eq hΩ hJ hK hVJ hR
      omega
    obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
    obtain ⟨y, hyV, hy1, hyy, -, -⟩ := hVT₁.exists_involution
    obtain ⟨x, hxR, hxU⟩ := hU.exists_not_mem
    have hconj := conj_z_of_not_sylow ⟨h22, hΩ, hM.twoNil⟩ hS' hK hJ hKJ hR hT₁ hRW' hT₁W' hU
      hnot ⟨U, hU, hzU, hz1, hzz⟩ ⟨V, hVT₁, hyV, hy1, hyy⟩ hxR hxU
    have hyZ : IsZInv Ω y := ⟨J, hJ, T₁, V, hT₁, hVT₁, hyV, hy1, hyy⟩
    have hzZ : IsZInv Ω z := ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩
    have hyz : y ≠ z := fun h => hKJ (eq_of_mem_of_mem hΩ hK hJ (hR.le (hU.le hzU))
      (h ▸ hT₁.le (hVT₁.le hyV)) hz1 hzz)
    have hyzZ : IsZInv Ω (y * z) := by
      rw [← hconj]
      exact hyZ.conj hΩ x
    exact hno4 S' hS' y z (hVW' hyV) hyZ (hUW' hzU) hzZ hyz hyzZ
  ·
    exfalso
    have hKJ : K ≠ J := by
      rintro rfl
      have hVK : IsSylowOf 2 V K := by
        have h1 := hV
        rwa [inf_eq_left.mpr le_normalizer] at h1
      have := Assumption41.card_sylow_eq hΩ hK hK hVK hR
      omega
    have hv₀1 : v₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hv₀2; omega
    have hv₀v₀ : v₀ * v₀ = 1 := by rw [← pow_two, ← hv₀2, pow_orderOf_eq_one]
    have hv₀J : v₀ ∈ J := (mem_inf.mp hv₀).1
    have hnadj : ¬ DStarAdj Ω K J := by
      rintro ⟨-, -, ⟨T', V', hT', hV', hV'K⟩, -⟩
      have hV'2 : IsPGroup 2 V' := hV'.isPGroup.to_le hV'.le
      obtain ⟨V'', hV'', hV'V''⟩ := exists_isSylowOf_le hV'2
        (le_inf (hV'.le.trans hT'.le) hV'K)
      have hle : Nat.card V' ≤ Nat.card V'' := card_le_of_le hV'V''
      have heq : Nat.card V'' = Nat.card V := by rw [hV''.card_eq, hV.card_eq]
      have := hV'.four_le
      omega
    obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
    have hzK : z ∈ K := hR.le (hU.le hzU)
    have hzv : z ∈ centralizer ({v₀} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := hinv v₀ (hv₀V (mem_zpowers v₀)) hv₀1 z hzU
      rw [inv_eq_of_mul_eq_one_right hzz] at h1
      calc z * v₀ = (v₀ * z * v₀⁻¹) * v₀ := by rw [h1]
        _ = v₀ * z := by group
    have hzJ : z ∈ normalizer (J : Set G) :=
      Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) hv₀J hv₀1 hv₀v₀ hzv
    have hzP : IsPGroup 2 (zpowers z) :=
      isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hzz)
    obtain ⟨T', hT', hzT'⟩ := exists_isSylowOf_normalized hzP ((zpowers_le).mpr hzJ)
    obtain ⟨V', hV'⟩ := Assumption41.exists_rot hΩ hJ hT'
    have hzinv := conj_eq_inv_of_not_dStarAdj h22 hΩ hK hJ (fun h => hnadj h.symm) hzK hz1
      hzz hzJ hT' hV' (hzT' (mem_zpowers z))
    have hP : IsPGroup 2 (zpowers z ⊔ T' : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hzP hT'.isPGroup hzT'
    obtain ⟨S'', hS'', hPS''⟩ := exists_isSylowOf_le hP (le_top : zpowers z ⊔ T' ≤ ⊤)
    have hV'W : V' ≤ sec4W Ω S'' :=
      le_sec4W ((hV'.le.trans le_sup_right).trans hPS'') (isRot_of hJ hT' hV')
    have hzW := hZ2 S'' hS'' z ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩
      ((le_normalizer_sec4W hΩ.conj_mem S'') (hPS'' (mem_sup_left (mem_zpowers z))))
    obtain ⟨ρ, hρ, hρo⟩ := hV'.exists_gen
    have hρV' : ρ ∈ V' := hρ ▸ mem_zpowers ρ
    apply hV'.gen_mul_self_ne_one hρo
    have h1 := hzinv ρ hρV'
    have h2 := sec4W_mul_comm hΩ hS'' hzW (hV'W hρV')
    rw [h2, mul_inv_cancel_right] at h1
    calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel ρ

theorem MinCounter.false_of_not_conn (h22 : Asc76Lemma22) (h27 : L26.Asc76Lemma27)
    (h1 : Asc76Theorem1) (hBF : Asc76X.BenderFacts) (hHall : HallDihedralFusion)
    {S : Subgroup G} (hM : MinCounter Ω S) (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hZ2 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ →
      ∀ x, IsZInv Ω x → x ∈ normalizer (sec4W Ω S' : Set G) → x ∈ sec4W Ω S' :=
    fun S' hS' x hx hxN => (hM.of_sylow hS').mem_sec4W_of_isZInv h22 hHall hdis hx hxN
  have hno4 : ∀ S' : Subgroup G, IsSylowOf 2 S' ⊤ → ∀ a b : G, a ∈ sec4W Ω S' → IsZInv Ω a →
      b ∈ sec4W Ω S' → IsZInv Ω b → a ≠ b → IsZInv Ω (a * b) → False :=
    fun S' hS' a b haW haZ hbW hbZ hab habZ =>
      (hM.of_sylow hS').false_of_fourGroup h27 hdis (hZ2 S' hS') haW haZ hbW hbZ hab habZ
  obtain ⟨K₀, hK₀, hall⟩ := hM.single
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K₀
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK₀ hR
  obtain ⟨z, hzU, hz1, hzz, -, hzR⟩ := hU.exists_involution
  obtain ⟨r, hrR, hrU⟩ := hU.exists_not_mem
  have hrr : r * r = 1 := hU.mul_self r hrR hrU
  have hrz : r ≠ z := fun h => hrU (h ▸ hzU)
  have hr1 : r ≠ 1 := fun h => hrU (h ▸ U.one_mem)
  have hrank : 1 < CFSG.Open.pRank 2 R := by
    refine Asc76X.one_lt_pRank_of_fourGroup (E := Sec4.fourGroup r z hrr hzz (hzR r hrR)) ?_
      (isElemAbelian_fourGroup hrr hzz (hzR r hrR)) (card_fourGroup hrr hzz (hzR r hrR) hr1 hz1 hrz)
    intro y hy
    rcases (mem_fourGroup).mp hy with h | h | h | h
    · rw [h]; exact R.one_mem
    · rw [h]; exact hrR
    · rw [h]; exact hU.le hzU
    · rw [h]; exact R.mul_mem hrR (hU.le hzU)
  have hstar : ∀ g : G, Even (Nat.card
      (AschbacherTightEmbedding.rightConjugate K₀ g ⊓ normalizer (K₀ : Set G) : Subgroup G)) →
      SylowNormalizes (AschbacherTightEmbedding.rightConjugate K₀ g) K₀ := fun g hg =>
    hM.sylowNormalizes h22 hZ2 hno4 hK₀ (hΩ.conj_mem K₀ hK₀ g) hg
  rcases h1 G K₀ (Assumption41.tightlyEmbedded hΩ hK₀) (normalClosure_eq_top_of_single hΩ hall)
    (hΩ.perfect K₀ hK₀) hΩ.oddCore hstar R hR hrank with h | h | ⟨hSz, -⟩
  · apply hM.not_normal_member hK₀
    rw [h]
    exact Subgroup.normal_top
  · exact (hΩ.dihedral K₀ hK₀ R hR).2 h.1
  · obtain ⟨P, hRP⟩ := hR.isPGroup.exists_le_sylow
    have hrc := hBF.involution_center G hSz P r (hRP hrR) (by rw [pow_two]; exact hrr)
    obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
    have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
    apply hU.gen_mul_self_ne_one hρo
    have h1 := hU.conj_eq r hrR hrU ρ hρU
    have h2 : ρ * r = r * ρ := (mem_centralizer_iff.mp hrc) ρ (hRP (hU.le hρU))
    rw [← h2, mul_inv_cancel_right] at h1
    calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel ρ

end CFSG.ComponentClassification.Asc76.Sec4
