module

public import CFSG.LocalAnalysis.RankTwoShapes.AbelianRadical.TwoReduced
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SwapExtension
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.RankTwoShapes

variable {G : Type*} [Group G]

theorem wreathed_of_lt_of_le_normalizer [Finite G] (P : Subgroup G) (hP : IsPGroup 2 P)
    (Q : Subgroup G) (hQab : IsMulCommutative Q) (hQcard : 4 < Nat.card Q)
    (hQrank : TwoRankLeTwo Q) (hcent : Subgroup.centralizer (Q : Set G) ⊓ P = Q)
    (hO2 : CFSG.pCore 2 (↥(Subgroup.normalizer (Q : Set G)) ⧸
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = ⊥)
    (R : Subgroup G) (hQR : Q < R) (hRP : R ≤ P)
    (hRN : R ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ n : ℕ, 2 ≤ n ∧ (Q.subgroupOf R).Normal ∧ (Q.subgroupOf R).index = 2 ∧
      Nonempty (Q ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) ∧
      (∃ e : R ≃* CFSG.Open.WreathedTwoGroup n, (Q.subgroupOf R).map e.toMonoidHom =
        (RegularWreathProduct.rightHom :
          CFSG.Open.WreathedTwoGroup n →* Multiplicative (ZMod 2)).ker) ∧
      (Q.subgroupOf R).Characteristic ∧
      Nonempty ((↥(Subgroup.normalizer (Q : Set G)) ⧸
        (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) ≃*
          Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (Q : Set G)
  set C := Subgroup.centralizer (Q : Set G)
  set φ := Q.normalizerMonoidHom with hφ
  set A := φ.range
  let eΓ : (N ⧸ C.subgroupOf N) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq (Q.normalizerMonoidHom_ker).symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  have hO2A : CFSG.pCore 2 A = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 eΓ, hO2, Subgroup.map_bot]
  let ψ : R →* MulAut Q := φ.comp (Subgroup.inclusion hRN)
  have hφker : ∀ x : N, x ∈ φ.ker ↔ (x : G) ∈ C := fun x => by
    rw [hφ, Q.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hQC : Q ≤ C := hcent.symm.trans_le inf_le_left
  have hψker : ψ.ker = Q.subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf]
    change Subgroup.inclusion hRN r ∈ φ.ker ↔ _
    rw [hφker]
    change (r : G) ∈ C ↔ (r : G) ∈ Q
    exact ⟨fun h => hcent ▸ ⟨h, hRP r.2⟩, fun h => hQC h⟩
  have hψrange : ψ.range ≤ A := by
    rintro _ ⟨r, rfl⟩
    exact ⟨_, rfl⟩
  have hindex_card : (Q.subgroupOf R).index = Nat.card ψ.range := by
    rw [← hψker, Subgroup.index_ker]
  have hRp : IsPGroup 2 R := hP.to_le hRP
  obtain ⟨m, hm⟩ := hRp.exists_card_eq
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hm ▸ (Q.subgroupOf R).index_dvd_card)
  have hj1 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hj
    exact hQR.not_ge hj
  have hdvdA : (Q.subgroupOf R).index ∣ Nat.card A := by
    rw [hindex_card]
    exact Subgroup.card_dvd_of_le hψrange
  have heven : 2 ∣ Nat.card A := (dvd_pow_self 2 hj1).trans (hj ▸ hdvdA)
  have hQp : IsPGroup 2 Q := hP.to_le (hQR.le.trans hRP)
  let : CommGroup Q := IsMulCommutative.instCommGroup
  obtain ⟨n, hn1, ⟨eQ⟩, -, hbij, -, hA6, ⟨eS3⟩⟩ :=
    abelian_two_reduced_automorphisms hQp hQrank A heven hO2A
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n = 1 := by omega
    have hcard : Nat.card Q = 2 ^ n * 2 ^ n := by
      rw [Nat.card_congr eQ.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
        Nat.card_zmod]
    rw [hcard, hn] at hQcard
    norm_num at hQcard
  have hindex : (Q.subgroupOf R).index = 2 := by
    rw [hA6] at hdvdA
    rw [hj] at hdvdA ⊢
    have hj2 : j < 2 := by
      by_contra h
      have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans hdvdA
      norm_num at h4
    have hj1' : j = 1 := by omega
    rw [hj1', pow_one]
  obtain ⟨t, htR, htQ⟩ := IsConcreteLE.exists_of_lt hQR
  let tN : N := ⟨t, hRN htR⟩
  let a : A := ⟨φ tN, ⟨tN, rfl⟩⟩
  have ha1 : a ≠ 1 := by
    intro h
    have h' : tN ∈ φ.ker := congrArg Subtype.val h
    rw [hφker] at h'
    exact htQ (hcent ▸ ⟨h', hRP htR⟩)
  have hπa : squareQuotientAction A a ≠ 1 := fun h => ha1 (hbij.1 (h.trans (map_one _).symm))
  obtain ⟨v, hv⟩ : ∃ v, squareQuotientAction A a v ≠ v := by
    by_contra h
    push Not at h
    exact hπa (MulEquiv.ext h)
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
  rw [squareQuotientAction_apply] at hv
  have hnontriv : ∃ q' ∈ Q.subgroupOf R, ∀ r ∈ Q.subgroupOf R,
      (⟨t, htR⟩ : R) * q' * (⟨t, htR⟩ : R)⁻¹ ≠ q' * r ^ 2 := by
    refine ⟨⟨q, hQR.le q.2⟩, q.2, ?_⟩
    intro r hr heq
    apply hv
    let r' : Q := ⟨r, hr⟩
    have h1 : ((a : MulAut Q) q : Q) = q * r' ^ 2 := by
      have h2 := congrArg Subtype.val heq
      exact Subtype.ext h2
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (r' ^ 2)).mpr
      (Subgroup.mem_square.mpr ⟨r', pow_two r'⟩), mul_one]
  have hQRnormal : (Q.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRN
  have hiso : Nonempty ((Q.subgroupOf R) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hQR.le).trans eQ⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hwr, hchar⟩ :=
    homocyclic_swap_extension hn1 (Q.subgroupOf R) hQRnormal hindex hiso ⟨t, htR⟩ htQ hnontriv
  exact ⟨n, hn2, hQRnormal, hindex, ⟨eQ⟩, hwr, (hchar hn2).2.2, ⟨eΓ.trans eS3⟩⟩

theorem abelian_radical_normalizer_wreathed [Finite G] (P : Subgroup G) (hP : IsPGroup 2 P)
    (Q : Subgroup G) (hQP : Q < P) (hQab : IsMulCommutative Q) (hQcard : 4 < Nat.card Q)
    (hQrank : TwoRankLeTwo Q) (hcent : Subgroup.centralizer (Q : Set G) ⊓ P = Q)
    (hO2 : CFSG.pCore 2 (↥(Subgroup.normalizer (Q : Set G)) ⧸
      (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = ⊥) :
    ∃ n : ℕ, 2 ≤ n ∧ (Q.subgroupOf P).Normal ∧ (Q.subgroupOf P).index = 2 ∧
      Nonempty (Q ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) ∧
      (∃ e : P ≃* CFSG.Open.WreathedTwoGroup n, (Q.subgroupOf P).map e.toMonoidHom =
        (RegularWreathProduct.rightHom :
          CFSG.Open.WreathedTwoGroup n →* Multiplicative (ZMod 2)).ker) ∧
      (Q.subgroupOf P).Characteristic ∧
      Nonempty ((↥(Subgroup.normalizer (Q : Set G)) ⧸
        (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) ≃*
          Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : NormalizerCondition P := @Group.normalizerCondition_of_isNilpotent P _ hP.isNilpotent
  set N := Subgroup.normalizer (Q : Set G) with hN
  have hQR0 : Q < P ⊓ N := by
    have hlt : Q.subgroupOf P < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact hQP.not_ge
    have h := hnc _ hlt
    rw [← Subgroup.subgroupOf_normalizer_eq hQP.le] at h
    obtain ⟨g, hgN, hgQ⟩ := IsConcreteLE.exists_of_lt h
    refine lt_of_le_of_ne (le_inf hQP.le Subgroup.le_normalizer) fun heq => hgQ ?_
    rw [Subgroup.mem_subgroupOf] at hgN ⊢
    rw [heq]
    exact ⟨g.2, hgN⟩
  obtain ⟨-, -, -, -, -, -, hchar0, -⟩ := wreathed_of_lt_of_le_normalizer P hP Q hQab hQcard
    hQrank hcent hO2 (P ⊓ N) hQR0 inf_le_left inf_le_right
  have hPN : P ≤ N := by
    by_contra hPN
    have hlt : (P ⊓ N).subgroupOf P < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hPN (h.trans inf_le_right)
    have h := hnc _ hlt
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_left] at h
    obtain ⟨g, hgN, hgR⟩ := IsConcreteLE.exists_of_lt h
    rw [Subgroup.mem_subgroupOf] at hgN hgR
    apply hgR
    refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    by_cases hh : h ∈ P ⊓ N
    · have hfix := SetLike.ext_iff.mp (hchar0.fixed ((P ⊓ N).normalizerMonoidHom ⟨g, hgN⟩))
        ⟨h, hh⟩
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hfix
      exact hfix.symm
    · refine iff_of_false (fun hq => hh (hQR0.le hq)) (fun hq => hh ?_)
      exact (Subgroup.mem_normalizer_iff.mp hgN h).mpr (hQR0.le hq)
  exact wreathed_of_lt_of_le_normalizer P hP Q hQab hQcard hQrank hcent hO2 P hQP le_rfl hPN

theorem abelian_alperin_wreathed {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (Q : Subgroup G) (hQ : IsAlperinSubgroup 2 (S : Subgroup G) Q) (hQab : IsMulCommutative Q)
    (hQS : Q < (S : Subgroup G)) (hQcard : 4 < Nat.card Q)
    (hrank : ∀ E ≤ (S : Subgroup G), IsMulCommutative E → (∀ e ∈ E, e ^ 2 = 1) →
      Nat.card E ≤ 4) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hcentS, hrad⟩ := hQ
  set N := Subgroup.normalizer (Q : Set G)
  set C := Subgroup.centralizer (Q : Set G)
  have hQC : Q ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr hQab
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hcent : C ⊓ (S : Subgroup G) = Q := le_antisymm hcentS (le_inf hQC hQS.le)
  have hQrank : TwoRankLeTwo Q := by
    intro E hEab hEexp
    have h := hrank (E.map Q.subtype) ((Subgroup.map_subtype_le E).trans hQS.le) inferInstance
      (by
        rintro _ ⟨e, he, rfl⟩
        rw [← map_pow, hEexp e he, map_one])
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h
  have hO2 : CFSG.pCore 2 (N ⧸ C.subgroupOf N) = ⊥ := by
    set O := CFSG.pCore 2 (N ⧸ C.subgroupOf N)
    set π := QuotientGroup.mk' (C.subgroupOf N) with hπ
    set R : Subgroup G := (O.comap π).map N.subtype
    have hRN : R ≤ N := Subgroup.map_subtype_le _
    have hπC : ∀ x : N, π x = 1 ↔ (x : G) ∈ C := fun x => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hCR : C ≤ R := by
      intro c hc
      refine ⟨⟨c, hCN hc⟩, ?_, rfl⟩
      change π ⟨c, hCN hc⟩ ∈ O
      rw [(hπC ⟨c, hCN hc⟩).mpr hc]
      exact O.one_mem
    have hNR : N ≤ Subgroup.normalizer (R : Set G) := by
      have : (O.comap π).Normal := Subgroup.Normal.comap inferInstance π
      intro n hn
      apply Subgroup.le_normalizer_map N.subtype
      refine ⟨⟨n, hn⟩, ?_, rfl⟩
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hsup : Q ⊔ C = C := sup_eq_right.mpr hQC
    have hidx : ∃ k : ℕ, ((Q ⊔ C).subgroupOf R).index = 2 ^ k := by
      rw [hsup]
      let ξ : R →* (N ⧸ C.subgroupOf N) := π.comp (Subgroup.inclusion hRN)
      have hξker : ξ.ker = C.subgroupOf R := by
        ext r
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hπC (Subgroup.inclusion hRN r)
      have hξrange : ξ.range ≤ O := by
        rintro _ ⟨⟨r, hr⟩, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hr
        exact hx
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2)
        (G := N ⧸ C.subgroupOf N)).exists_card_eq
      have hdvd : (C.subgroupOf R).index ∣ 2 ^ k := by
        rw [← hξker, Subgroup.index_ker, ← hk]
        exact Subgroup.card_dvd_of_le hξrange
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨i, hi⟩
    have hRC : R = C := (hrad R (by rw [hsup]; exact hCR) hRN hNR hidx).trans hsup
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf N) x
    have hyR : (y : G) ∈ R := ⟨y, hx, rfl⟩
    rw [hRC] at hyR
    exact (hπC y).mpr hyR
  obtain ⟨n, hn, -, -, -, ⟨e, -⟩, -, -⟩ := abelian_radical_normalizer_wreathed
    (S : Subgroup G) S.isPGroup' Q hQS hQab hQcard hQrank hcent hO2
  exact ⟨n, hn, ⟨e⟩⟩

end CFSG.RankTwoShapes
