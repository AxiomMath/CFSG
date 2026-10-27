module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_normalized_sylow [Finite G] {H A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    ∃ S : Subgroup G, S ≤ H ∧ Nat.card S = 3 ^ (Nat.card H).factorization 3 ∧
      ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : A →* MulAut H := (Subgroup.normalizerMonoidHom H).comp (Subgroup.inclusion hAH)
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H φ
  obtain ⟨S, hS⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card (α := Sylow 3 H)
    (not_dvd_card_sylow 3 H)
  refine ⟨(S : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  · intro a ha s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h1 : (⟨a, ha⟩ : A) • S = S := hS ⟨a, ha⟩
    have h2 : (⟨a, ha⟩ : A) • (S : Subgroup H) = S := by
      have := congrArg (fun T : Sylow 3 H => (T : Subgroup H)) h1
      exact this
    have h3 : φ ⟨a, ha⟩ t ∈ (S : Subgroup H) := by
      rw [← h2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ ht
    refine ⟨_, h3, ?_⟩
    simp [φ]

theorem commute_of_conj_mem_zpowers {x a : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {m : ℕ} (ha : orderOf a = 3 ^ m) (h : a * x * a⁻¹ ∈ Subgroup.zpowers x) :
    a * x = x * a := by
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hx4 : x ^ 4 = x := by
    calc x ^ 4 = x ^ 3 * x := by rw [← pow_succ]
      _ = x := by rw [hx3, one_mul]
  obtain ⟨k, hk⟩ := h
  have hk' : x ^ k = a * x * a⁻¹ := hk
  have hy : a * x * a⁻¹ = x ^ (k % 3) := by
    rw [← hk']
    have := zpow_mod_orderOf x k
    rw [hox] at this
    exact_mod_cast this.symm
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hy
    exact absurd (by simpa using hy) hx1
  · rw [h1, zpow_one, mul_inv_eq_iff_eq_mul] at hy
    exact hy
  · rw [h2] at hy
    have hy2 : a * x * a⁻¹ = x ^ 2 := by simpa using hy
    have e1 : a * x = x ^ 2 * a := mul_inv_eq_iff_eq_mul.1 hy2
    have e2 : a * x ^ 2 = x ^ 4 * a := by
      calc a * x ^ 2 = (a * x) * x := by simp [pow_two, mul_assoc]
        _ = x ^ 2 * a * x := by rw [e1]
        _ = x ^ 2 * (a * x) := by simp [pow_two, mul_assoc]
        _ = x ^ 2 * (x ^ 2 * a) := by rw [e1]
        _ = x ^ 4 * a := by simp [pow_succ, mul_assoc]
    have hsq : a ^ 2 * x = x * a ^ 2 := by
      calc a ^ 2 * x = a * (a * x) := by simp [pow_two, mul_assoc]
        _ = a * (x ^ 2 * a) := by rw [e1]
        _ = (a * x ^ 2) * a := by simp [mul_assoc]
        _ = x ^ 4 * a * a := by rw [e2]
        _ = x ^ 4 * a ^ 2 := by simp [pow_two, mul_assoc]
        _ = x * a ^ 2 := by rw [hx4]
    have hodd : (3 ^ m) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    have hapow : a = (a ^ 2) ^ ((3 ^ m + 1) / 2) := by
      rw [← pow_mul]
      have : 2 * ((3 ^ m + 1) / 2) = 3 ^ m + 1 := by omega
      rw [this, pow_succ, ← ha, pow_orderOf_eq_one, one_mul]
    have hcomm : a * x = x * a := by
      have hc : Commute (a ^ 2) x := hsq
      rw [hapow]
      exact ((hc.pow_left _).eq)
    have h5 : a * x * a⁻¹ = x := by rw [hcomm]; group
    rw [h5] at hy2
    have h6 : x * x = x * 1 := by rw [mul_one, ← pow_two]; exact hy2.symm
    exact absurd (mul_left_cancel h6) hx1

theorem isQuasisimple_quotient_of_glaPComponent [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
  have h1 := glaPComponent_of_le Nat.prime_three hJ le_rfl hJ.1
  have h2 := h1.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥(barX 3 J J) at h2
  rw [barX_self] at h2
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv h2

theorem exists_centralizing_order_three [Finite G] {X J A : Subgroup G}
    (hJ : GLAPComponent 3 X J) (hA3 : IsPGroup 3 A)
    (hAc : A ≤ centralizerQuot J (GLAPPrimeCoreOf 3 J)) :
    ∃ x : G, x ∈ J ∧ x ^ 3 = 1 ∧ x ∉ oPrimePOf 3 J ∧ ∀ a ∈ A, a * x = x * a := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hQ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  set P : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hPdef
  have hPcop : Nat.Coprime 3 (Nat.card P) := coprime_card_gLAPPrimeCore_aux 3 ↥J
  have hPnd : ¬ 3 ∣ Nat.card P := (Nat.Prime.coprime_iff_not_dvd h3).1 hPcop
  let π : ↥J →* ↥J ⧸ P := QuotientGroup.mk' P
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hπker : ∀ j : ↥J, π j = 1 ↔ j ∈ P := fun j => QuotientGroup.eq_one_iff j
  have hQnt : Nontrivial (↥J ⧸ P) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have := hQ.2.toNontrivial
    have : Subsingleton ((↥J ⧸ P) ⧸ Subgroup.center (↥J ⧸ P)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (↥J ⧸ P))).subsingleton
    exact not_subsingleton _ this
  have hdvd : 3 ∣ Nat.card (↥J ⧸ P) := by
    by_contra hnd
    have hc : Nat.Coprime 3 (Nat.card (↥J ⧸ P)) := (Nat.Prime.coprime_iff_not_dvd h3).2 hnd
    have hbot : GLAPPrimeCore 3 (↥J ⧸ P) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    have htop : (⊤ : Subgroup (↥J ⧸ P)) ≤ GLAPPrimeCore 3 (↥J ⧸ P) :=
      le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    rw [hbot] at htop
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥J ⧸ P)
    exact huv ((Subgroup.mem_bot.1 (htop (Subgroup.mem_top u))).trans
      (Subgroup.mem_bot.1 (htop (Subgroup.mem_top v))).symm)
  obtain ⟨xb, hxbord, hxbc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hQ h3 (by norm_num) hdvd
  have hxb3 : xb ^ 3 = 1 := by
    have := pow_orderOf_eq_one xb
    rwa [hxbord] at this
  set H₀ : Subgroup ↥J := (Subgroup.zpowers xb).comap π with hH₀
  have hmemH₀ : ∀ j : ↥J, j ∈ H₀ ↔ π j ∈ Subgroup.zpowers xb := fun j => Iff.rfl
  have hPH₀ : P ≤ H₀ := fun j hj => by
    rw [hmemH₀, (hπker j).2 hj]; exact one_mem _
  have hcardH₀ : Nat.card H₀ = 3 * Nat.card P := by
    let π' : H₀ →* ↥J ⧸ P := π.comp H₀.subtype
    have hker : π'.ker = P.subgroupOf H₀ := by
      ext h
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hπker h
    have hrange : π'.range = Subgroup.zpowers xb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective hπs _
    have h1 := Subgroup.card_ker_mul_card_range π'
    rw [hker, hrange, Nat.card_zpowers, hxbord,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH₀).toEquiv] at h1
    rw [← h1, mul_comm]
  let H : Subgroup G := H₀.map J.subtype
  have hHJ : H ≤ J := Subgroup.map_subtype_le _
  have hcardH : Nat.card H = 3 * Nat.card P := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hcardH₀]
  have hmemH : ∀ h ∈ H, ∃ j : ↥J, (j : G) = h ∧ π j ∈ Subgroup.zpowers xb := by
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, rfl, hj⟩
  have hkey : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H := by
    intro a ha h hh
    obtain ⟨j, rfl, hj⟩ := hmemH h hh
    obtain ⟨hnJ, -, hcomm⟩ := hAc ha
    have haj : a * (j : G) * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hnJ (j : G)).1 j.2
    refine ⟨⟨a * (j : G) * a⁻¹, haj⟩, (hmemH₀ _).2 ?_, rfl⟩
    have hP' : (j⁻¹ * ⟨a * (j : G) * a⁻¹, haj⟩ : ↥J) ∈ P := by
      have hc := hcomm (j : G)⁻¹ (J.inv_mem j.2)
      refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
        (?_ : J.subtype (j⁻¹ * ⟨a * (j : G) * a⁻¹, haj⟩) ∈ GLAPPrimeCoreOf 3 J)
      simpa [mul_assoc] using hc
    have heq : π ⟨a * (j : G) * a⁻¹, haj⟩ = π j := by
      show QuotientGroup.mk' P _ = QuotientGroup.mk' P _
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := P.inv_mem hP'
      simpa using this
    rw [heq]; exact hj
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hkey a ha h, fun h' => ?_⟩
    have h2 := hkey a⁻¹ (A.inv_mem ha) _ h'
    have e : a⁻¹ * (a * h * a⁻¹) * a = h := by group
    rw [inv_inv, e] at h2
    exact h2
  obtain ⟨S, hSH, hScard, hSnorm⟩ := exists_normalized_sylow hA3 hAH
  have hS3 : Nat.card S = 3 := by
    rw [hScard, hcardH, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
      Finsupp.add_apply, h3.factorization_self, Nat.factorization_eq_zero_of_not_dvd hPnd]
    norm_num
  have : IsCyclic S := isCyclic_of_prime_card (p := 3) hS3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  set x : G := (g : G) with hxdef
  have hordg : orderOf g = 3 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hS3
  have hordx : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe, hordg]
  have hx3 : x ^ 3 = 1 := by rw [← hordx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hordx; norm_num at hordx
  have hSx : ∀ s ∈ S, s ∈ Subgroup.zpowers x := by
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨s, hs⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxS : x ∈ S := g.2
  have hxJ : x ∈ J := hHJ (hSH hxS)
  refine ⟨x, hxJ, hx3, ?_, ?_⟩
  · intro hxo
    obtain ⟨jx, hjx, hπjx⟩ := hmemH x (hSH hxS)
    obtain ⟨j', hj', hj'x⟩ := hxo
    have hj'jx : j' = jx := Subtype.ext (hj'x.trans hjx.symm)
    subst hj'jx
    have hordj : orderOf j' = 3 := by rw [← Subgroup.orderOf_coe, hjx, hordx]
    have hπ1 : π j' ≠ 1 := by
      intro h1
      have hjP : j' ∈ P := (hπker j').1 h1
      have := Subgroup.orderOf_dvd_natCard P hjP
      rw [hordj] at this
      exact hPnd this
    have hπ3 : orderOf (π j') = 3 := by
      have hd : orderOf (π j') ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (by
          have hj3 : j' ^ 3 = 1 := by
            have := pow_orderOf_eq_one j'
            rwa [hordj] at this
          rw [← map_pow, hj3, map_one])
      rcases (Nat.dvd_prime h3).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hπ1
      · exact h
    have hle : Subgroup.zpowers (π j') ≤ Subgroup.zpowers xb := Subgroup.zpowers_le.2 hπjx
    have heq : Subgroup.zpowers (π j') = Subgroup.zpowers xb :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hπ3, hxbord])
    have hxbmem : xb ∈ CFSG.pCore 3 (↥J ⧸ P) := by
      have hpc : π j' ∈ CFSG.pCore 3 (↥J ⧸ P) := hj'
      have : Subgroup.zpowers xb ≤ CFSG.pCore 3 (↥J ⧸ P) := by
        rw [← heq]; exact Subgroup.zpowers_le.2 hpc
      exact this (Subgroup.mem_zpowers xb)
    have hN : (CFSG.pCore 3 (↥J ⧸ P)).Normal := CFSG.pCore_normal
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ
      (CFSG.pCore 3 (↥J ⧸ P)) with h | h
    · exact hxbc (h hxbmem)
    · have hpg : IsPGroup 3 (↥J ⧸ P) := by
        have h0 : IsPGroup 3 (CFSG.pCore 3 (↥J ⧸ P)) := CFSG.pCore_isPGroup
        rw [h] at h0
        exact h0.of_surjective Subgroup.topEquiv.toMonoidHom
          (fun y => ⟨Subgroup.topEquiv.symm y, by simp⟩)
      have := hpg.isNilpotent
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥J ⧸ P)
      exact hlt.ne hQ.1
  · intro a ha
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hA3 ⟨a, ha⟩
    have ho : orderOf a = 3 ^ m := by
      rw [← Subgroup.orderOf_coe ⟨a, ha⟩] at hm
      exact hm
    exact commute_of_conj_mem_zpowers hx3 hx1 ho (hSx _ (hSnorm a ha x hxS))

end CFSG.HardMathSupport.Solomon.LocalBalance
