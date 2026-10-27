module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open Subgroup
open scoped commutatorElement

section GLTwo

variable {p : ℕ} [Fact p.Prime]

theorem upper_scalar_pow_succ (a b : ZMod p) (n : ℕ) :
    !![a, b; 0, a] ^ (n + 1) =
      !![a ^ (n + 1), ((n + 1 : ℕ) : ZMod p) * a ^ n * b; 0, a ^ (n + 1)] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring

theorem mem_center_of_commute_of_pow_eq_one {u c : GL (Fin 2) (ZMod p)} (hu : u ^ p = 1)
    (hu1 : u ≠ 1) (hcu : c * u = u * c) (hc : (orderOf c).Coprime p) :
    c ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  obtain ⟨g, hg⟩ := CFSG.RankThree.SubgroupLists.exists_conj_transvection u hu hu1
  set c' : GL (Fin 2) (ZMod p) := g⁻¹ * c * g with hc'
  have hU : ((g⁻¹ * u * g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![1, 1; 0, 1] := by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hg, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  have hcom : c' * (g⁻¹ * u * g) = (g⁻¹ * u * g) * c' := by
    rw [hc']
    calc g⁻¹ * c * g * (g⁻¹ * u * g) = g⁻¹ * (c * u) * g := by group
      _ = g⁻¹ * (u * c) * g := by rw [hcu]
      _ = _ := by group
  have hm : (c' : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (c' : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [← hU, ← Units.val_mul, hcom, Units.val_mul]
  set C := (c' : Matrix (Fin 2) (Fin 2) (ZMod p)) with hC
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  have h11 : C 1 1 = C 0 0 := by linear_combination -h01
  have hC' : C = !![C 0 0, C 0 1; 0, C 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11]
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hup := upper_scalar_pow_succ (C 0 0) (C 0 1) (p - 1)
  rw [hp1, ZMod.natCast_self, zero_mul, zero_mul] at hup
  have hpow : ((c' ^ p : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (C 0 0 ^ p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [Units.val_pow_eq_pow_val, ← hC, hC', hup]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hc'p : c' ^ p = g⁻¹ * c ^ p * g := by
    have := conj_pow (a := g⁻¹) (b := c) (i := p)
    simpa [hc'] using this
  have hmat : ((c ^ p : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (C 0 0 ^ p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    have hcp : c ^ p = g * c' ^ p * g⁻¹ := by rw [hc'p]; group
    rw [hcp, Units.val_mul, Units.val_mul, hpow, Matrix.mul_smul, mul_one, Matrix.smul_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcen : c ^ p ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hmat, Matrix.mul_smul, mul_one, Matrix.smul_mul, one_mul]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc.symm
  rw [← hm]
  exact pow_mem hcen m

end GLTwo

theorem le_centralizer_of_commutator_eq_of_le_normalizer {X : Type*} [Group X] {S : Subgroup X}
    {t : X} (hS : ⁅S, S⁆ = S) (hN : S ≤ normalizer (zpowers t : Set X)) :
    S ≤ centralizer ({t} : Set X) := by
  have hmem : ∀ g ∈ S, ∃ a : ℤ, ∀ n : ℤ, g * t ^ n * g⁻¹ = t ^ (a * n) := fun g hg => by
    obtain ⟨a, ha⟩ := mem_zpowers_iff.mp
      ((mem_normalizer_iff.mp (hN hg) t).mp (mem_zpowers t))
    exact ⟨a, fun n => by rw [← conj_zpow, ← ha, ← zpow_mul]⟩
  have key : ∀ s ∈ S, ∀ s' ∈ S, s * s' * t * (s * s')⁻¹ = s' * s * t * (s' * s)⁻¹ := by
    intro s hs s' hs'
    obtain ⟨a, ha⟩ := hmem s hs
    obtain ⟨b, hb⟩ := hmem s' hs'
    have e1 : s * s' * t * (s * s')⁻¹ = t ^ (a * (b * 1)) := by
      rw [← ha, ← hb, zpow_one]; group
    have e2 : s' * s * t * (s' * s)⁻¹ = t ^ (b * (a * 1)) := by
      rw [← hb, ← ha, zpow_one]; group
    rw [e1, e2, show a * (b * 1) = b * (a * 1) by ring]
  rw [← hS, commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [mem_centralizer_singleton_iff]
  have h := key g₁⁻¹ (inv_mem h₁) g₂⁻¹ (inv_mem h₂)
  have h2 : ⁅g₁, g₂⁆ * t * ⁅g₁, g₂⁆⁻¹ = t := by
    rw [commutatorElement_def]
    calc g₁ * g₂ * g₁⁻¹ * g₂⁻¹ * t * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹ =
        (g₁ * g₂) * (g₁⁻¹ * g₂⁻¹ * t * (g₁⁻¹ * g₂⁻¹)⁻¹) * (g₁ * g₂)⁻¹ := by group
      _ = (g₁ * g₂) * (g₂⁻¹ * g₁⁻¹ * t * (g₂⁻¹ * g₁⁻¹)⁻¹) * (g₁ * g₂)⁻¹ := by rw [h]
      _ = t := by group
  calc ⁅g₁, g₂⁆ * t = ⁅g₁, g₂⁆ * t * ⁅g₁, g₂⁆⁻¹ * ⁅g₁, g₂⁆ := by group
    _ = t * ⁅g₁, g₂⁆ := by rw [h2]

section Reduced

open CFSG.AGLEmbedding CFSG.RankThree.SubgroupLists CFSG.SectionRank.Ccomm CFSG.Open

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Sylow p Y} {Y₀ : Subgroup Y}

theorem not_dvd_card_of_layer_eq_bot
    (h : ReducedNongeneration p Y R Y₀) (hlayer : CFSG.layer Y = ⊥) {J : Subgroup Y}
    (hJY : J ≤ Y₀) (hJ : ⁅J, J⁆ = J) : ¬ p ∣ Nat.card J := by
  intro hpJ
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore p Y with hQ
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  haveI : Q.Normal := CFSG.pCore_normal
  have hQc : centralizer (Q : Set Y) ≤ Q :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y p h.core_eq_bot hlayer
  obtain ⟨z, hz, hzp⟩ : ∃ z ∈ centralizer ((R : Subgroup Y) : Set Y), orderOf z = p := by
    obtain ⟨E, hER, -, hEc⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (R : Subgroup Y)
    have hRne : (R : Subgroup Y) ≠ ⊥ := by
      intro hb
      rw [hb, le_bot_iff] at hER
      rw [hER, Subgroup.card_bot] at hEc
      have h1 : p ^ 1 ≤ p ^ CFSG.Open.pRank p (R : Subgroup Y) :=
        Nat.pow_le_pow_right hp.pos (le_trans (by norm_num) h.three_le_pRank)
      have h2 : 1 < p ^ 1 := by simpa using hp.one_lt
      omega
    haveI : Nontrivial (R : Subgroup Y) := (Subgroup.nontrivial_iff_ne_bot _).mpr hRne
    haveI := R.isPGroup'.center_nontrivial
    have hdvd : p ∣ Nat.card (Subgroup.center (R : Subgroup Y)) := by
      rcases (R.isPGroup'.to_subgroup (Subgroup.center _)).card_eq_or_dvd with h1 | h1
      · exact absurd h1 Finite.one_lt_card.ne'
      · exact h1
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨((w : (R : Subgroup Y)) : Y), Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨r, hr⟩)
    · exact ((Subgroup.orderOf_coe _).trans (Subgroup.orderOf_coe w)).trans hw
  obtain ⟨D, hDc, -, -, hDcard, hDnc, hker⟩ := h.exists_nonabelian_witness hQp hQc hz hzp
  obtain ⟨-, hZ, ⟨e⟩⟩ := center_structure_of_card_eq_pow_three hDcard hDnc
  set ρD := (autQuotient (Subgroup.center D)).comp
    ((MulAut.characteristic D).comp (MulAut.conjNormal (H := Q))) with hρD
  set ρ : Y →* GL (Fin 2) (ZMod p) := (elemAutEquivGL e).toMonoidHom.comp ρD with hρ
  have hkerρ : IsPGroup p ρ.ker := by
    refine (isPGroup_ker_centerQuotient_action hQp hQc D hZ hker).to_le fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (elemAutEquivGL e).injective (by rw [map_one]; exact hx)
  have hkerR : ρ.ker ≤ (R : Subgroup Y) := hkerρ.le_sylow_of_normal R
  have hRY₀ : (R : Subgroup Y) ≤ Y₀ := h.sylow_le
  have hY₀dvd : p ∣ Nat.card (Y₀.map ρ) := by
    have hRne : (R : Subgroup Y).map ρ ≠ ⊥ := fun hb =>
      h.not_sylow_le_of_normal hkerρ ((Subgroup.map_eq_bot_iff _).mp hb)
    rcases (R.isPGroup'.map ρ).card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hRne
    · exact h1.trans (Subgroup.card_dvd_of_le (Subgroup.map_mono hRY₀))
  set J' := J.map ρ with hJ'
  have hJ'perf : ⁅J', J'⁆ = J' := by rw [hJ', ← Subgroup.map_commutator, hJ]
  have hJ'ne : J' ≠ ⊥ := by
    intro hb
    have hJp : IsPGroup p J := hkerρ.to_le ((Subgroup.map_eq_bot_iff _).mp hb)
    obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries J).1 hJp.isNilpotent
    have hl : ∀ k, J.lowerCentralSeries k = J := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hJ]
    rw [hl n] at hn
    rw [hn, Subgroup.card_bot] at hpJ
    exact hp.not_dvd_one hpJ
  have hJ'Y : J' ≤ Y₀.map ρ := Subgroup.map_mono hJY
  have hSL : StatedSL 2 (ZMod p) ≤ Y₀.map ρ := by
    haveI : Group.IsPerfect J' :=
      (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J').mpr hJ'perf
    obtain ⟨-, -, -, -, hdiv, -⟩ := perfect_prime_linear_recognition h.ne_two J' hJ'ne
    by_cases hpJ' : p ∣ Nat.card J'
    · refine le_trans ?_ hJ'Y
      rw [(hdiv hpJ').1]
      intro A hA
      exact ⟨⟨(A : Matrix (Fin 2) (Fin 2) (ZMod p)), (mem_statedSL_iff A).mp hA⟩, Units.ext rfl⟩
    rcases dickson_gl_two (Y₀.map ρ) hY₀dvd with ⟨T₀, hT₀n, hT₀c⟩ | hSL
    · exfalso
      obtain ⟨t, -, htp, ht1, htz⟩ := exists_zpowers_eq_of_card_eq hT₀c
      have hN : J' ≤
          normalizer (zpowers (t : GL (Fin 2) (ZMod p)) : Set (GL (Fin 2) (ZMod p))) := by
        have h1 := Subgroup.le_normalizer_map (H := (T₀ : Subgroup (Y₀.map ρ))) (Y₀.map ρ).subtype
        rw [Subgroup.normalizer_eq_top_iff.mpr hT₀n, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype, ← htz, MonoidHom.map_zpowers] at h1
        exact hJ'Y.trans h1
      have hc := le_centralizer_of_commutator_eq_of_le_normalizer hJ'perf hN
      have hcop : Nat.Coprime p (Nat.card J') := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpJ'
      have hcen : J' ≤ Subgroup.center (GL (Fin 2) (ZMod p)) := by
        intro j hj
        refine mem_center_of_commute_of_pow_eq_one (u := (t : GL (Fin 2) (ZMod p)))
          (by rw [← Subgroup.coe_pow, htp]; rfl) (fun h1 => ht1 (Subtype.ext h1))
          (mem_centralizer_singleton_iff.mp (hc hj)) ?_
        have hdv : orderOf j ∣ Nat.card J' := by
          rw [← Subgroup.orderOf_mk j hj]
          exact orderOf_dvd_natCard _
        exact (Nat.Coprime.coprime_dvd_right hdv hcop).symm
      apply hJ'ne
      rw [← hJ'perf, eq_bot_iff, commutator_le]
      intro g₁ h₁ g₂ h₂
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp (hcen h₁) g₂ |>.symm
    · exact hSL
  set W := (StatedSL 2 (ZMod p)).comap ρ with hW
  have hWn : W.Normal := Subgroup.Normal.comap inferInstance ρ
  have hWY : W ≤ Y₀ := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hSL hw
    have hk : y⁻¹ * w ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyw, inv_mul_cancel]
    have := Y₀.mul_mem hy (hRY₀ (hkerR hk))
    simpa using this
  have hRW : (R : Subgroup Y) ≤ W := by
    intro r hr
    show ρ r ∈ StatedSL 2 (ZMod p)
    rw [mem_statedSL_iff]
    apply det_eq_one_of_pow_eq_one
    obtain ⟨k, hk⟩ := (R.isPGroup'.map ρ) ⟨ρ r, ⟨r, hr, rfl⟩⟩
    have hk' : (ρ r) ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    have hm1 : m ≤ 1 := by
      by_contra hm1
      exact not_sq_dvd_card_GL_two (p := p)
        ((pow_dvd_pow p (by omega)).trans (hmo ▸ orderOf_dvd_natCard (ρ r)))
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hmo]
    exact (pow_dvd_pow p hm1).trans (by rw [pow_one])
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Y₀ := by
    by_contra hall
    push Not at hall
    exact h.ne_top (eq_top_iff.mpr fun x _ => hall x)
  have hWc : W ≤ Y₀ ⊓ GLBConj x Y₀ := by
    refine le_inf hWY fun w hw => ⟨x * w * x⁻¹, hWY (hWn.conj_mem w hw x), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h3 := h.three_le_pRank.trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (hRW.trans hWc))
  have h2 := h.pRank_inf_conj_le x hx
  omega

end Reduced

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
