module

public import CFSG.CGT.T75K.ExoticHat
public import CFSG.CGT.Timmesfeld75.JLemma
public import CFSG.CGT.Timmesfeld75.Sec63Main

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.SectionRank

theorem center_eq_bot_of_quot_alt6 {K : Type} [Group K] (hK : IsSimpleGroup K)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) : Subgroup.center K = ⊥ := by
  rcases hK.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have h1 : Nat.card (K ⧸ Subgroup.center K) = 1 := by
      show (Subgroup.center K).index = 1
      rw [h]
      exact Subgroup.index_top
    have h2 : Nat.card (K ⧸ Subgroup.center K) = Nat.card (alternatingGroup (Fin 6)) :=
      Nat.card_congr e.toEquiv
    have h3 : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega

variable {G : Type} [Group G] {T T₁ T₃ : Subgroup G} {n m : ℕ} {x : G}

theorem a6_numerics (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hc : Sec6Ctx T T₁ n m)
    (cfg : Sec63Cfg T T₁ n m x T₃)
    (hF : ∀ j : Fin 3, (⨅ i, normIn (sec63Fam T T₁ T₃ j) (sec63Fam T T₁ T₃ i)) ≠ ⊥)
    (hA6 : Nonempty (jQuot ↥(T ⊔ T₁ ⊔ T₃) ⧸ Subgroup.center (jQuot ↥(T ⊔ T₁ ⊔ T₃)) ≃*
      alternatingGroup (Fin 6))) :
    m = 1 ∧ Nat.card T = 4 * Nat.card ↥(normIn T T₃) := by
  have hfin := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hlt := cfg.small
  have hbig := cfg.big
  obtain ⟨g, hg⟩ := cfg.conj
  have hT := hc.hy.pair.wc
  obtain ⟨y₁, hy₁, hy₁eq⟩ := hc.sec3.conj
  obtain ⟨y₃, hy₃, hy₃eq⟩ := cfg.sec3.conj
  have hRfam : (⨆ i, sec63Fam T T₁ T₃ i) = T ⊔ T₁ ⊔ T₃ := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup (sec63Fam T T₁ T₃) 0) (le_iSup (sec63Fam T T₁ T₃) 1))
        (le_iSup (sec63Fam T T₁ T₃) 2)
  set R := T ⊔ T₁ ⊔ T₃ with hR
  have hTR : T ≤ R := le_sup_left.trans le_sup_left
  have hX₁ : T ⊔ T₁ ≤ R := le_sup_left
  have hX₃ : T ⊔ T₃ ≤ R := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hy₁R : y₁ ∈ R := hX₁ hy₁
  have hy₃R : y₃ ∈ R := hX₃ hy₃
  have hinj : Function.Injective (sec63Fam T T₁ T₃) := by
    have h01 : T ≠ T₁ := fun h => hc.hy.pair.ne h.symm
    have h02 : T ≠ T₃ := fun h => cfg.ne_left h.symm
    have h12 : T₁ ≠ T₃ := fun h => cfg.ne_mid h.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sec63Fam, h01.symm]
  have hconj : ∀ i, ∃ g : G, sec63Fam T T₁ T₃ i = conjSubgroup g T := by
    intro i
    fin_cases i
    · exact ⟨1, (conjSubgroup_one T).symm⟩
    · exact hc.hy.pair.conj
    · exact ⟨g, hg⟩
  have hRconj : ∀ i, ∃ g' ∈ R, sec63Fam T T₁ T₃ i = conjSubgroup g' T := by
    intro i
    fin_cases i
    · exact ⟨1, R.one_mem, (conjSubgroup_one T).symm⟩
    · exact ⟨y₁, hy₁R, hy₁eq⟩
    · exact ⟨y₃, hy₃R, hy₃eq⟩
  have hLA : Nat.card ↥(normIn T T₃) < Nat.card ↥(normIn T T₁) := by
    rw [cfg.card_normIn]
    exact hlt
  have h2L := hc.two_mul_card_normIn_le
  have hq : ∃ j, 2 * Nat.card ↥(normIn T (sec63Fam T T₁ T₃ j)) < Nat.card T := by
    refine ⟨2, ?_⟩
    show 2 * Nat.card ↥(normIn T T₃) < Nat.card T
    omega
  obtain ⟨hsimple, -, hhyp, -, -, hker⟩ := jLemma h215 h26 hc.hy.nonab hc.hy.ind hT hc.hS hc.hI
    (by omega) (r := 3) (Ts := sec63Fam T T₁ T₃) (by norm_num) hinj hconj ⟨0, rfl⟩
    hF hRfam hRconj hq
  obtain ⟨e⟩ := hA6
  have hcenter : Subgroup.center (jQuot ↥R) = ⊥ := center_eq_bot_of_quot_alt6 hsimple e
  set That : Subgroup (jQuot ↥R) := (T.subgroupOf R).map (jMap ↥R) with hThat
  have hThatAb : IsElemAbelian 2 That := hhyp.1.1
  have hThat2 : 2 < Nat.card That := hhyp.2.1
  have hThat4 : Nat.card That = 4 := by
    have hp : IsPGroup 2 That := isPGroup_two_of_isElemAbelian hThatAb
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hp
    have hf : Function.Injective
        ((e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (jQuot ↥R))).comp That.subtype))) := by
      have h1 : Function.Injective (QuotientGroup.mk' (Subgroup.center (jQuot ↥R))) := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenter]
      exact e.injective.comp (h1.comp Subtype.val_injective)
    have hrank := le_pRank_of_injective Nat.one_lt_two
      (fun a b => Subtype.ext (elemAbelian_mul_comm hThatAb a.2 b.2))
      (fun a => by rw [pow_two]; exact Subtype.ext (elemAbelian_mul_self hThatAb a.2))
      hk _ hf (H := ⊤) le_top
    have hk2 : k ≤ 2 := by
      have := twoRank_alternatingGroup_six_le_two
      unfold twoRank at this
      omega
    rw [hk] at hThat2 ⊢
    interval_cases k <;> simp_all
  let ψ : ↥T →* jQuot ↥R := (jMap ↥R).comp (Subgroup.inclusion hTR)
  have hψrange : ψ.range = That := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hψker : ψ.ker ≤ (normIn T T₃).subgroupOf T := by
    intro t ht
    rw [Subgroup.mem_subgroupOf]
    have hmem : Subgroup.inclusion hTR t ∈ (jMap ↥R).ker := ht
    have h1 := hker _ hmem 2
    have h2 : conjSubgroup (t : G) T₃ = T₃ := h1
    exact mem_normIn.2 ⟨t.2, mem_normalizer_iff_conjSubgroup_eq.2 h2⟩
  have hAT : normIn T T₃ ≤ T := normIn_le _ _
  have hAcard : Nat.card ↥((normIn T T₃).subgroupOf T) = Nat.card ↥(normIn T T₃) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
  have hcardψ : Nat.card ψ.ker * 4 = Nat.card T := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, hThat4] at h
    exact h
  have hdvd : Nat.card ψ.ker ∣ Nat.card ↥(normIn T T₃) := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hψker
  have hApos : 0 < Nat.card ↥(normIn T T₃) := Nat.card_pos
  have hK₀pos : 0 < Nat.card ψ.ker := Nat.card_pos
  obtain ⟨d, hd⟩ := hdvd
  have hd2 : d < 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hd0 : d ≠ 0 := by
    rintro rfl
    omega
  have hd1 : d = 1 := by omega
  rw [hd1, mul_one] at hd
  have hTA : Nat.card T = 4 * Nat.card ↥(normIn T T₃) := by
    rw [← hcardψ, hd]
    ring
  refine ⟨?_, hTA⟩
  have hm0 : m ≠ 0 := m_ne_zero hc
  have hmul := hc.mul_card_normIn
  have h2m : 2 ^ m < 4 := by
    by_contra hcon
    push Not at hcon
    have : 4 * Nat.card ↥(normIn T T₁) ≤ 2 ^ m * Nat.card ↥(normIn T T₁) :=
      Nat.mul_le_mul_right _ hcon
    omega
  have hm2 : m < 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  omega

end CFSG.CGT.T75K
