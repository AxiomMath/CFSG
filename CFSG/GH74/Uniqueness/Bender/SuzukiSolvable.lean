module

public import CFSG.GH74.Uniqueness.Bender.Sylow2Basic
public import CFSG.GH74.Uniqueness.Bender.SuzukiOdd
public import CFSG.GH74.Uniqueness.SE

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Strong

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.exists_sylow_centralizer_eq
    {n e : ℕ} (h : BenderType K n 2 e) {y : K}
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ Q : Sylow 2 K, y ∈ (Q : Subgroup K) ∧ centralizer ({y} : Set K) = (Q : Subgroup K) := by
  have he := h.e_eq_one_of_two
  subst he
  obtain ⟨Q, hQ⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hy).exists_le_sylow
  have hyQ : y ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers y)
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  exact ⟨Q, hyQ, hc.centralizer_eq_of_e_one (hc.mem_rootCenter_of_mul_self hyQ hy) hy1⟩

theorem BenderType.isStronglyEmbedded_normalizer_sylow
    {n e : ℕ} (h : BenderType K n 2 e)
    (J : Subgroup K) (S : Sylow 2 J) (hexp : ∀ x : J, ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1)
    (hS1 : (S : Subgroup J) ≠ ⊥) (hnorm : ¬ (S : Subgroup J).Normal) :
    IsStronglyEmbedded (normalizer ((S : Subgroup J) : Set J)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexpT : ∀ T : Subgroup J, IsPGroup 2 T → ∀ x ∈ T, x * x = 1 := by
    intro T hT x hx
    obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
    exact hexp x k (by simpa using congrArg Subtype.val hk)
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    exact hnorm (Subgroup.normalizer_eq_top_iff.mp htop)
  · obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hS1
      rw [pow_zero] at hm
      exact Subgroup.card_eq_one.mp hm
    have h2 : 2 ∣ Nat.card S := by
      rw [hm]
      exact dvd_pow_self 2 hm0
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer))
  · intro g hg
    by_contra hnodd
    have hev : 2 ∣ Nat.card ↥(normalizer ((S : Subgroup J) : Set J) ⊓
        conjugate (normalizer ((S : Subgroup J) : Set J)) g) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnodd)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hyo : orderOf (x : J) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have hysq : (x : J) * (x : J) = 1 := by
      have := pow_orderOf_eq_one (x : J)
      rwa [hyo, sq] at this
    have hy1 : (x : J) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hyo
      omega
    have hyM : (x : J) ∈ normalizer ((S : Subgroup J) : Set J) := (Subgroup.mem_inf.mp x.2).1
    have hyc : g * (x : J) * g⁻¹ ∈ normalizer ((S : Subgroup J) : Set J) :=
      mem_conjugate_iff_mul_inv.mp (Subgroup.mem_inf.mp x.2).2
    have hyS : (x : J) ∈ (S : Subgroup J) := mem_sylow_of_mem_normalizer S hysq hyM
    have hgS : g * (x : J) * g⁻¹ ∈ (S : Subgroup J) := by
      refine mem_sylow_of_mem_normalizer S ?_ hyc
      calc g * (x : J) * g⁻¹ * (g * (x : J) * g⁻¹) = g * ((x : J) * (x : J)) * g⁻¹ := by group
        _ = 1 := by rw [hysq]; group
    have hyKsq : ((x : J) : K) * ((x : J) : K) = 1 := congrArg Subtype.val hysq
    have hyK1 : ((x : J) : K) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
    obtain ⟨Q₀, -, hcen⟩ := h.exists_sylow_centralizer_eq hyKsq hyK1
    have hT : ∀ T : Subgroup J, IsPGroup 2 T → (x : J) ∈ T →
        T ≤ (Q₀ : Subgroup K).subgroupOf J := by
      intro T hT2 hyT t ht
      have hts : t * t = 1 := hexpT T hT2 t ht
      have hty : t * (x : J) * (t * (x : J)) = 1 := hexpT T hT2 _ (T.mul_mem ht hyT)
      have hcomm : t * (x : J) = (x : J) * t := comm_of_mul_self_eq_one hts hysq hty
      have hmem : (t : K) ∈ centralizer ({((x : J) : K)} : Set K) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hcomm
      rw [hcen] at hmem
      exact hmem
    have hQ₀2 : IsPGroup 2 ((Q₀ : Subgroup K).subgroupOf J) := Q₀.isPGroup'.comap_subtype
    have hS_le : (S : Subgroup J) ≤ (Q₀ : Subgroup K).subgroupOf J := hT S S.isPGroup' hyS
    let S₁ : Sylow 2 J := g⁻¹ • S
    have hyS₁ : (x : J) ∈ (S₁ : Subgroup J) := by
      show (x : J) ∈ ((g⁻¹ • S : Sylow 2 J) : Subgroup J)
      rw [mem_sylow_smul_iff, inv_inv]
      exact hgS
    have hS₁_le : (S₁ : Subgroup J) ≤ (Q₀ : Subgroup K).subgroupOf J :=
      hT S₁ S₁.isPGroup' hyS₁
    have h1 : (S : Subgroup J) = (Q₀ : Subgroup K).subgroupOf J := sylow_eq_of_le S hQ₀2 hS_le
    have h2 : (S₁ : Subgroup J) = (Q₀ : Subgroup K).subgroupOf J :=
      sylow_eq_of_le S₁ hQ₀2 hS₁_le
    have h3 : g⁻¹ • S = S := Sylow.ext (h2.trans h1.symm)
    have h4 : g⁻¹ ∈ normalizer ((S : Subgroup J) : Set J) := Sylow.smul_eq_iff_mem_normalizer.mp h3
    apply hg
    have := (normalizer ((S : Subgroup J) : Set J)).inv_mem h4
    simpa using this

end Strong

section SE

theorem BenderType.false_of_isStronglyEmbedded
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (J : Subgroup K)
    (hexp : ∀ x : J, ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1) {M : Subgroup ↥J}
    (hM : IsStronglyEmbedded M) {E : Subgroup ↥J} {k : ℕ} (hk : 2 ≤ k)
    (hEsq : ∀ x ∈ E, x * x = 1) (hEcard : Nat.card E = 2 ^ k) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he : e = 1 := h.e_eq_one_of_two
  subst he
  have hexpT : ∀ T : Subgroup J, IsPGroup 2 T → ∀ x ∈ T, x * x = 1 := by
    intro T hT x hx
    obtain ⟨k, hk⟩ := hT ⟨x, hx⟩
    exact hexp x k (by simpa using congrArg Subtype.val hk)
  obtain ⟨a, ha, hn⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨hi, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  rcases S_SE_proof ↥J _ hM with hrank | ⟨hBender, -, -⟩
  ·
    have hE : CFSG.Open.IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        exact comm_of_mul_self_eq_one (hEsq _ x.2) (hEsq _ y.2) (hEsq _ (E.mul_mem x.2 y.2))
      · rw [sq]
        exact hEsq x hx
    have hEle : E ≤ involutionClosure ↥J := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · apply Subgroup.subset_closure
        show orderOf x = 2
        apply orderOf_eq_prime _ hx1
        rw [sq]
        exact hEsq x hx
    have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hEle hE hEcard
    omega
  ·
    obtain ⟨n', i', e', hS⟩ := isBenderGroup_iff_exists_benderType.mp hBender
    set Xc : Subgroup ↥J := involutionClosure ↥J with hXc
    let Tc : Sylow 2 ↥Xc := default
    let Q' := Sylow.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥Xc)) Tc
    have hT₀2 : IsPGroup 2 ((Tc : Subgroup ↥Xc).map Xc.subtype) := Tc.isPGroup'.map Xc.subtype
    have hQ'sq : ∀ x ∈ (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)), x * x = 1 := by
      intro x hx
      rw [Sylow.coe_mapSurjective] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyJ : (y : ↥J) ∈ (Tc : Subgroup ↥Xc).map Xc.subtype := ⟨y, hy, rfl⟩
      have h1 := hexpT _ hT₀2 _ hyJ
      have h2 : y * y = 1 := Subtype.ext h1
      change QuotientGroup.mk' _ y * QuotientGroup.mk' _ y = 1
      rw [← map_mul, h2, map_one]
    obtain ⟨t', hc'⟩ := hS.exists_benderCore Q'
    have hi' : i' = 1 := by
      by_contra hne
      have hle : (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)) ≤
          rootCenter (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)) :=
        hc'.elemAbelian_le_rootCenter le_rfl hQ'sq
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [hc'.card_eq, hc'.card_center] at hdvd
      have hi2 : 2 ≤ i' := by
        have := hS.two_le.1
        omega
      have hn2 : 2 ≤ n' := hS.two_le.2
      have hq2 : 4 ≤ 2 ^ n' := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn2
      have hle2 := Nat.le_of_dvd (by positivity) hdvd
      have h3 : (2 ^ n') ^ 2 ≤ (2 ^ n') ^ i' := Nat.pow_le_pow_right (by omega) hi2
      have h4 : 2 ^ n' < (2 ^ n') ^ 2 := by
        rw [sq]
        nlinarith
      omega
    subst hi'
    have he' : e' = 1 := by
      rcases hS.cases' with ⟨-, he, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
      · exact he
      · omega
      · omega
    subst he'
    have h3S : 3 ∣ Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) := by
      rw [hS.card_eq]
      exact three_dvd_linear_card n'
    have h3K : 3 ∣ Nat.card K :=
      h3S.trans ((Subgroup.card_quotient_dvd_card _).trans
        ((Subgroup.card_subgroup_dvd_card Xc).trans (Subgroup.card_subgroup_dvd_card J)))
    rw [h.card_eq, hn] at h3K
    exact not_three_dvd_sz_card a h3K

theorem BenderType.isSolvable_of_sq_eq_one
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (J : Subgroup K)
    (hJ : ∀ x : J, ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1) : Group.IsSolvable J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, -⟩ : ∃ S : Sylow 2 J, True := ⟨default, trivial⟩
  have hS : ∀ x ∈ (S : Subgroup J), x * x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    exact hJ x k (by simpa using congrArg Subtype.val hk)
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hindex : ¬ 2 ∣ (S : Subgroup J).index := S.not_dvd_index
  have hcardJ : Nat.card J = 2 ^ k * (S : Subgroup J).index := by
    rw [← hk]
    exact (Subgroup.card_mul_index _).symm
  by_cases hk0 : k = 0
  ·
    subst hk0
    have hodd : Odd (Nat.card J) := by
      rw [hcardJ, pow_zero, one_mul]
      exact Nat.odd_iff.mpr (by omega)
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_cases hk1 : k = 1
  ·
    subst hk1
    have hScard : Nat.card S = 2 := by
      rw [hk]
      norm_num
    have hScyc : IsCyclic S := isCyclic_of_prime_card (p := 2) hScard
    have h2J : 2 ∣ Nat.card J := by
      rw [hcardJ]
      exact Dvd.dvd.mul_right (by norm_num) _
    have hmin : (Nat.card J).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr h2J
    have hcompl := IsCyclic.isComplement' hmin hScyc
    set N := (MonoidHom.transferSylow S (hScyc.normalizer_le_centralizer hmin)).ker with hN
    have hNc : Nat.card N * Nat.card S = Nat.card J := hcompl.card_mul_card
    have hNodd : Odd (Nat.card N) := by
      have h1 : Nat.card N = (S : Subgroup J).index := by
        rw [hScard, hcardJ] at hNc
        omega
      rw [h1]
      exact Nat.odd_iff.mpr (by omega)
    have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
    have hq : Nat.card (J ⧸ N) = 2 := by
      rw [← Subgroup.index, hcompl.symm.index_eq_card, hScard]
    have hQcyc : IsCyclic (J ⧸ N) := isCyclic_of_prime_card (p := 2) hq
    have hQsolv : Group.IsSolvable (J ⧸ N) := inferInstance
    exact Group.isSolvable_of_subgroup_quotient N
  by_cases hnorm : (S : Subgroup J).Normal
  ·
    have hSab : ∀ a b : S, a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact comm_of_mul_self_eq_one (hS _ a.2) (hS _ b.2) (hS _ (S.mul_mem a.2 b.2))
    have hSsolv : Group.IsSolvable S := Group.isSolvable_of_comm hSab
    have hQodd : Odd (Nat.card (J ⧸ (S : Subgroup J))) := by
      rw [← Subgroup.index]
      exact Nat.odd_iff.mpr (by omega)
    have hQsolv : Group.IsSolvable (J ⧸ (S : Subgroup J)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
    exact Group.isSolvable_of_subgroup_quotient (S : Subgroup J)
  ·
    exfalso
    have hS1 : (S : Subgroup J) ≠ ⊥ := by
      intro hbot
      apply hk0
      have : Nat.card S = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hk] at this
      exact Nat.pow_eq_one.mp this |>.resolve_left (by norm_num)
    have hM := h.isStronglyEmbedded_normalizer_sylow J S hJ hS1 hnorm
    exact h.false_of_isStronglyEmbedded J hJ hM (E := (S : Subgroup J)) (k := k)
      (by omega) hS hk

theorem BenderType.isSolvable_of_injective
    {K J : Type} [Group K] [Finite K] [Group J] {n e : ℕ}
    (h : BenderType K n 2 e) (f : J →* K) (hf : Function.Injective f)
    (hJ : ∀ x : J, ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1) : Group.IsSolvable J := by
  have hr : ∀ x : f.range, ∀ k : ℕ, x ^ 2 ^ k = 1 → x * x = 1 := by
    rintro ⟨_, y, rfl⟩ k hk
    have h1 : f (y ^ 2 ^ k) = f 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val hk
    have h2 := hJ y k (hf h1)
    apply Subtype.ext
    show f y * f y = 1
    rw [← map_mul, h2, map_one]
  have hsolv : Group.IsSolvable f.range := h.isSolvable_of_sq_eq_one f.range hr
  exact Group.isSolvable_of_isSolvable_injective (f := f.rangeRestrict)
    (fun a b hab => hf (congrArg Subtype.val hab))

end SE

end CFSG.GH74.Uniqueness.Bender
