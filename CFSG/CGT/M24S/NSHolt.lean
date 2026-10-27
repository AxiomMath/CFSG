module

public import CFSG.CGT.M24S.NSDefs
public import CFSG.Holt.H78.Defs
import CFSG.Holt.H78.Bridge

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General CFSG.Holt.H78

section Elementary

variable {G : Type} [Group G]

theorem normalizer_le_centralizer_of_sqDerivedEq {P : Subgroup G} {t : G}
    (hP : SqDerivedEq P t) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  intro g hg
  obtain ⟨y, hy, hyt⟩ := hP.2
  have hmap : (⁅P, P⁆ : Subgroup G).map (MulAut.conj g) = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]
  have hgy : g * y * g⁻¹ ∈ ⁅P, P⁆ := by
    rw [← hmap]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hsq : (g * y * g⁻¹) ^ 2 = g * t * g⁻¹ := by rw [← hyt, sq, sq]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hP.1 _ hgy with h1 | h1
  · rw [hsq] at h1
    have ht1 : t = 1 := by
      have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [this, h1]
      group
    rw [ht1, mul_one, one_mul]
  · rw [hsq] at h1
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]

private theorem not_two_pow_succ_dvd_card [Finite G] {C D P : Subgroup G} {n : ℕ}
    (hPC : P ≤ C) (hcard : Nat.card P = 2 ^ n)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ D → Nat.card Q ≤ Nat.card P)
    (hN : C ⊓ Subgroup.normalizer (P : Set G) ≤ D) :
    ¬ 2 ^ (n + 1) ∣ Nat.card C := by
  intro hdvd
  obtain ⟨K, hK, hPK, hKC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (hcard ▸ pow_dvd_pow 2 n.le_succ) hdvd hPC
  have hrel : P.relIndex K = 2 := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := K)
    rw [inf_of_le_left hPK, hcard, hK, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have : (P.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hrel
  have hKN : K ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mp this
  have hle := hmax K (IsPGroup.of_card hK) ((le_inf hKC hKN).trans hN)
  rw [hK, hcard, pow_succ] at hle
  have hpos : 0 < 2 ^ n := by positivity
  omega

private theorem card_mod_four_of_sign_eq_one {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]
    {σ : Equiv.Perm Ψ} (hσ2 : σ ^ 2 = 1) {ψ₀ : Ψ} (hfix : ∀ ψ, σ ψ = ψ ↔ ψ = ψ₀)
    (hsign : Equiv.Perm.sign σ = 1) : Fintype.card Ψ % 4 = 1 := by
  have hsupp : σ.support = Finset.univ.erase ψ₀ := by
    ext ψ
    simp [Equiv.Perm.mem_support, hfix]
  have hcard : σ.support.card = Fintype.card Ψ - 1 := by
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hσ2
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hct, Multiset.sum_replicate, smul_eq_mul, hcard] at hsum
  have hs := Equiv.Perm.sign_of_cycleType σ
  rw [hsign, hct, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hs
  have hev := (neg_one_pow_eq_one_iff_even (by decide)).mp hs.symm
  have hpos : 1 ≤ Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨ψ₀⟩
  obtain ⟨k, hk⟩ := hev
  omega

private theorem false_of_factorial {n N : ℕ} (hn4 : n % 4 = 1) (hn7 : 7 ≤ n)
    (hN : N = n.factorial / 2) (h10 : 2 ^ 10 ∣ N) (h11 : ¬ 2 ^ 11 ∣ N) : False := by
  by_cases h16 : 16 ≤ n
  · apply h11
    obtain ⟨k, hk⟩ := (show 2 ^ 12 ∣ Nat.factorial 16 by decide).trans
      (Nat.factorial_dvd_factorial h16)
    rw [hN, hk, show 2 ^ 12 * k = 2 * (2 ^ 11 * k) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro k rfl
  · have hlt : n < 16 := by omega
    subst hN
    interval_cases n <;> first | omega | (revert h10; decide)

private theorem card_center_le_two {S : Subgroup G} {z : G}
    (hZ : ∀ x ∈ S, ((∀ y ∈ S, x * y = y * x) ↔ (x = 1 ∨ x = z))) :
    Nat.card (Subgroup.center S) ≤ 2 := by
  classical
  have hmem : ∀ c : Subgroup.center S, ((c : S) : G) = 1 ∨ ((c : S) : G) = z := fun c =>
    (hZ _ (c : S).2).mp fun y hy => by
      have := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
  let f : Subgroup.center S → Bool := fun c => decide (((c : S) : G) = 1)
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : ((a : S) : G) = 1 ↔ ((b : S) : G) = 1 := by simpa [f] using hab
    apply Subtype.ext
    apply Subtype.ext
    by_cases ha1 : ((a : S) : G) = 1
    · rw [ha1, hab'.mp ha1]
    · rw [(hmem a).resolve_left ha1, (hmem b).resolve_left fun h => ha1 (hab'.mpr h)]
  calc Nat.card (Subgroup.center S) ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

end Elementary

theorem false_of_isHoltTriple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hHolt : CFSG.Holt.H78.HoltTheorem1) {M : Subgroup G} (hM : M ≠ ⊤) {S : Sylow 2 G} {z : G}
    (hS : Nat.card S = 2 ^ 10)
    (hZ : ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z)))
    (hTrip : CFSG.Holt.General.IsHoltTriple G (G ⧸ M) z ((1 : G) : G ⧸ M)) : False := by
  have : FaithfulSMul G (G ⧸ M) :=
    CFSG.RankThree.PartTwo.Sec21.faithfulSMul_quotient_of_simple hM
  have : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM
  obtain ⟨D⟩ := hHolt G (G ⧸ M)
    (IsHoltTriple.isStarGroup hTrip (IsHoltTriple.three_le_card hTrip))
  have hJ := jHull_eq_top_of_isSimpleGroup D.t_mem
  have hO := jOddCore_eq_bot_of_isSimpleGroup D.t_mem
  have hLi : ∀ i, D.L i = ⊤ := fun i => by
    have hn : (D.L i).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hJ ▸ D.le_normalizer i))
    have := HoltData.isSimpleGroup_L (D := D) hO i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.L i) with h' | h'
    · exact absurd h' ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)
    · exact h'
  obtain ⟨i₀, hι⟩ := D.exists_forall_eq_of_le_L hO (B := ⊤) top_ne_bot fun i => (hLi i).ge
  let e : G ≃* D.M i₀ := Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (hLi i₀).symm).trans (D.lEquiv hO i₀))
  rcases D.factor i₀ with ⟨hA, h7⟩ | ⟨q, k, hB⟩
  ·
    have hzL : z ∈ D.L i₀ := by rw [hLi i₀]; exact Subgroup.mem_top z
    set c := D.coordEquiv hO hι with hc
    set σ : Equiv.Perm (D.Ψc i₀) := (D.lEquiv hO i₀ ⟨z, hzL⟩ : Equiv.Perm (D.Ψc i₀)) with hσ
    have hσc : ∀ ω, σ (c ω) = c (z • ω) := fun ω =>
      (D.coordEquiv_smul hO hι ⟨z, hzL⟩ ω).symm
    have hfixσ : ∀ ψ, σ ψ = ψ ↔ ψ = c ((1 : G) : G ⧸ M) := fun ψ => by
      obtain ⟨ω, rfl⟩ := c.surjective ψ
      rw [hσc, c.injective.eq_iff, c.injective.eq_iff]
      exact hTrip.smul_eq_iff ω
    have hσ2 : σ ^ 2 = 1 := by
      have hl : (⟨z, hzL⟩ : D.L i₀) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hTrip.orderOf_eq_two ▸ pow_orderOf_eq_one z)
      rw [hσ, ← Subgroup.coe_pow, ← map_pow, hl, map_one, Subgroup.coe_one]
    have hsign : Equiv.Perm.sign σ = 1 := by
      have hσM : σ ∈ D.M i₀ := (D.lEquiv hO i₀ ⟨z, hzL⟩).2
      have hMA : D.M i₀ = alternatingGroup (D.Ψc i₀) := hA
      rw [hMA] at hσM
      exact Equiv.Perm.mem_alternatingGroup.mp hσM
    have hmod := card_mod_four_of_sign_eq_one hσ2 hfixσ hsign
    have : Nontrivial (D.Ψc i₀) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardG : Nat.card G = (Fintype.card (D.Ψc i₀)).factorial / 2 := by
      have hMA : D.M i₀ = alternatingGroup (D.Ψc i₀) := hA
      rw [Nat.card_congr e.toEquiv, hMA, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    have hS10 : Nat.card (S : Subgroup G) = 2 ^ 10 := hS
    have h10 : 2 ^ 10 ∣ Nat.card G := hS10 ▸ Subgroup.card_subgroup_dvd_card (S : Subgroup G)
    have h11 : ¬ 2 ^ 11 ∣ Nat.card G := fun hd => by
      have hd' := Sylow.pow_dvd_card_of_pow_dvd_card S hd
      rw [hS10] at hd'
      exact absurd (Nat.le_of_dvd (by positivity) hd') (by norm_num)
    exact false_of_factorial hmod h7 hcardG h10 h11
  ·
    let S' : Sylow 2 (D.M i₀) := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have h4 := hB.four_le_card_center_sylow S'
    let eS : (S : Subgroup G) ≃* (S' : Subgroup (D.M i₀)) :=
      (Subgroup.equivMapOfInjective (S : Subgroup G) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective e.surjective S).symm)
    have hcen : Nat.card (Subgroup.center (S : Subgroup G)) =
        Nat.card (Subgroup.center (S' : Subgroup (D.M i₀))) :=
      Nat.card_congr (Subgroup.centerCongr eS).toEquiv
    have h4' : 4 ≤ Nat.card (Subgroup.center (S : Subgroup G)) := by
      rw [hcen]
      exact h4
    have h2 := card_center_le_two hZ
    omega

theorem hasComplement_of_hyp_of_ns5 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hHolt : CFSG.Holt.H78.HoltTheorem1) {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T)
    (hNS5 : ¬ HasComplement T H → ∀ x ∈ H, x ∉ T → x ^ 2 = 1 →
      ∃ P : Subgroup G, P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) ∧
        (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
          Nat.card Q ≤ Nat.card P) ∧ Nat.card P = 2 ^ 7 ∧ ∃ t ∈ T, t ≠ 1 ∧ SqDerivedEq P t) :
    HasComplement T H := by
  by_contra hns
  have hT := h.wc.1
  have hNT : Subgroup.normalizer (T : Set G) = H := by
    rw [hL.normalizer_eq, hC, sup_eq_left.mpr h.le]
  obtain ⟨S, hTS, -, z, hzT, hz1, hZ⟩ := hL.sylow
  have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
  have hz2 : z ^ 2 = 1 := hT.2 z hzT
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hconj : ∀ g : G, g⁻¹ * z * g ∈ H → g⁻¹ * z * g ∈ T := by
    intro g hg
    by_contra hgT
    have hu2 : (g⁻¹ * z * g) ^ 2 = 1 := by
      rw [sq, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hzz, mul_one,
        inv_mul_cancel]
    obtain ⟨P, hP, hmax, hcard, t, htT, ht1, hPt⟩ := hNS5 hns _ hg hgT hu2
    have hNP : Subgroup.normalizer (P : Set G) ≤ H :=
      ((normalizer_le_centralizer_of_sqDerivedEq hPt).trans
        (hL.centralizer_le t htT ht1)).trans hNT.le
    refine not_two_pow_succ_dvd_card (n := 7) (hP.trans inf_le_right) hcard hmax
      (fun y hy => Subgroup.mem_inf.mpr ⟨hNP (Subgroup.mem_inf.mp hy).2,
        (Subgroup.mem_inf.mp hy).1⟩) ?_
    have hle : (S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({g⁻¹ * z * g} : Set G) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * s * g * (g⁻¹ * z * g) = g⁻¹ * (s * z) * g := by group
        _ = g⁻¹ * (z * s) * g := by rw [hSz s hs]
        _ = g⁻¹ * z * g * (g⁻¹ * s * g) := by group
    have hcS : Nat.card ((S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom) = 2 ^ 10 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hL.card_sylow S
    exact (pow_dvd_pow 2 (by norm_num : 7 + 1 ≤ 10)).trans (hcS ▸ Subgroup.card_dvd_of_le hle)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hTrip : IsHoltTriple G (G ⧸ H) z ((1 : G) : G ⧸ H) := by
    refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, fun ω => ?_,
      ⟨S, hTS hzT, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
      show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
    refine ⟨fun hg => ?_, fun hg => H.mul_mem (H.mul_mem (H.inv_mem hg) (h.le hzT)) hg⟩
    have hzc : z ∈ conjSubgroup g T := mem_conjSubgroup.mpr (hconj g hg)
    have hne : T ⊓ conjSubgroup g T ≠ ⊥ := by
      intro hb
      have hz' : z ∈ T ⊓ conjSubgroup g T := Subgroup.mem_inf.mpr ⟨hzT, hzc⟩
      rw [hb, Subgroup.mem_bot] at hz'
      exact hz1 hz'
    rw [← hNT]
    exact mem_normalizer_of_conjSubgroup_eq (h.wc.conj_eq_of_inf_ne_bot hne)
  have hHtop : H ≠ ⊤ := by
    intro hH
    have : T.Normal := Subgroup.normalizer_eq_top_iff.mp (hNT.trans hH)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hb | ht
    · rw [hb, Subgroup.mem_bot] at hzT
      exact hz1 hzT
    · have h1 := hL.card_T
      have h2 := hL.card_H
      rw [ht, Subgroup.card_top] at h1
      rw [hH, Subgroup.card_top] at h2
      omega
  exact false_of_isHoltTriple hHolt hHtop (hL.card_sylow S) hZ hTrip

end CFSG.CGT.M24S
