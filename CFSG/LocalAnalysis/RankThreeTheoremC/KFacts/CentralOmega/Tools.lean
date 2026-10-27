module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

open CFSG.Open

theorem not_forall_commute_of_isPGroup {L : Type*} [Group L] [Finite L] {x y : L}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y ≠ y * x) {H : Subgroup L}
    (hH : IsPGroup 3 H) (hxH : x ∈ H) (hyH : y ∈ H) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L P S
  intro hall
  have hmem : ∀ z ∈ (P : Subgroup L), g * z * g⁻¹ ∈ ((g • P : Sylow 3 L) : Subgroup L) := by
    intro z hz
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) _ hz
  have h := hall _ (hmem x (hHP hxH)) _ (hmem y (hHP hyH))
    (by rw [conj_pow, hx, mul_one, mul_inv_cancel]) (by rw [conj_pow, hy, mul_one, mul_inv_cancel])
  apply hxy
  have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h
      _ = g * (y * x) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h')

theorem exists_sylow_eq_of_nine_le {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : IsPGroup 3 H) (h9 : 9 ≤ Nat.card H) (h27 : ¬ 27 ∣ Nat.card X) :
    ∃ Q : Sylow 3 X, (Q : Subgroup X) = H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk2 : k ≤ 2 := by
    by_contra hk2
    push Not at hk2
    exact h27 ((pow_dvd_pow 3 hk2).trans hdvd)
  have hQ9 : Nat.card (Q : Subgroup X) ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  exact hQ9.trans h9

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers g) := by
  rintro ⟨h, hh⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem isPGroup_closure_of_conj_eq_mul {G : Type*} [Group G] {x y c : G}
    (hc : c ∈ Subgroup.center G) (hc3 : c ^ 3 = 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hconj : y * x * y⁻¹ = c * x) : IsPGroup 3 (Subgroup.closure {x, y}) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc)
  have hAp : IsPGroup 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left (isPGroup_zpowers_of_pow_three hc3)
      (isPGroup_zpowers_of_pow_three hx3)
  have hcy : y * c * y⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]
  have hcx : c * x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (c * x) := by
    have hmem : c⁻¹ * (c * x) ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (c * x) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rwa [inv_mul_cancel_left] at hmem
  have hmap : (Subgroup.zpowers c ⊔ Subgroup.zpowers x).map (MulAut.conj y).toMonoidHom =
      Subgroup.zpowers c ⊔ Subgroup.zpowers x := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have h1 : (MulAut.conj y).toMonoidHom c = c := hcy
    have h2 : (MulAut.conj y).toMonoidHom x = c * x := hconj
    rw [h1, h2]
    apply le_antisymm
    · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hcx)
    · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hx)
  have hyN : y ∈ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hBp : IsPGroup 3
      (Subgroup.zpowers c ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hAp (isPGroup_zpowers_of_pow_three hy3)
      (Subgroup.zpowers_le.mpr hyN)
  refine hBp.to_le (Subgroup.closure_le _ |>.mpr ?_)
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem exists_pair_of_cover {L X : Type*} [Group L] [Finite L] [Group X]
    (hperf : commutator L = ⊤) {φ : L →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center L) (hZp : IsPGroup 3 (Subgroup.center L))
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) {u v : X} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hnu : ∃ n : X, n * u * n⁻¹ = u⁻¹)
    (hnv : ∃ n : X, n * v * n⁻¹ = v⁻¹) (Q : Sylow 3 X)
    (hQ : (Q : Subgroup X) = Subgroup.closure {u, v}) :
    ∃ a b : L, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b ≠ b * a ∧
      ∃ P : Subgroup L, IsPGroup 3 P ∧ a ∈ P ∧ b ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd 3 := by decide
  obtain ⟨n, hn⟩ := hnu
  obtain ⟨m, hm⟩ := hnv
  obtain ⟨a, rfl, ha⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ
      hker.le hodd hu hn
  obtain ⟨b, rfl, hb⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ
      hker.le hodd hv hm
  have hkp : IsPGroup 3 φ.ker := hker ▸ hZp
  have hle : (Q : Subgroup X) ≤ φ.range := by
    rw [MonoidHom.range_eq_top.mpr hφ]
    exact le_top
  let P : Sylow 3 L := Q.comapOfKerIsPGroup φ hkp hle
  have hPeq : (P : Subgroup L) = (Q : Subgroup X).comap φ := Sylow.coe_comapOfKerIsPGroup _ _ _ _
  have haP : a ∈ (P : Subgroup L) := by
    rw [hPeq, Subgroup.mem_comap, hQ]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hbP : b ∈ (P : Subgroup L) := by
    rw [hPeq, Subgroup.mem_comap, hQ]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨a, b, ha, hb, fun hab => ?_, P, P.isPGroup', haP, hbP⟩
  apply GL83.not_isMulCommutative_sylow_of_perfect hperf h3 P
  have hpair : ({a, b} : Set L).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set L)) :=
    Subgroup.isMulCommutative_closure hpair
  have hdec : ∀ x ∈ (P : Subgroup L), ∃ c ∈ Subgroup.closure ({a, b} : Set L),
      c⁻¹ * x ∈ Subgroup.center L := by
    intro x hx
    rw [hPeq, Subgroup.mem_comap, hQ] at hx
    have hx' : φ x ∈ (Subgroup.closure ({a, b} : Set L)).map φ := by
      rw [MonoidHom.map_closure, Set.image_pair]
      exact hx
    obtain ⟨c, hc, hcx⟩ := hx'
    refine ⟨c, hc, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨c, hc, hcz⟩ := hdec x x.2
  obtain ⟨d, hd, hdw⟩ := hdec y y.2
  have hcd : c * d = d * c :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨c, hc⟩ : Subgroup.closure ({a, b} : Set L))
      ⟨d, hd⟩)
  have hzc : ∀ g : L, Commute (c⁻¹ * (x : L)) g := fun g =>
    (Subgroup.mem_center_iff.mp hcz g).symm
  have hwc : ∀ g : L, Commute (d⁻¹ * (y : L)) g := fun g =>
    (Subgroup.mem_center_iff.mp hdw g).symm
  have hx : (x : L) = c * (c⁻¹ * (x : L)) := by group
  have hy : (y : L) = d * (d⁻¹ * (y : L)) := by group
  change (x : L) * y = y * x
  rw [hx, hy]
  calc c * (c⁻¹ * (x : L)) * (d * (d⁻¹ * (y : L)))
        = c * d * ((c⁻¹ * (x : L)) * (d⁻¹ * (y : L))) := (hzc d).mul_mul_mul_comm c _
    _ = d * c * ((d⁻¹ * (y : L)) * (c⁻¹ * (x : L))) := by rw [hcd, (hzc _).eq]
    _ = d * (d⁻¹ * (y : L)) * (c * (c⁻¹ * (x : L))) := ((hwc c).mul_mul_mul_comm d _).symm

theorem not_forall_commute_of_cover {L X : Type*} [Group L] [Finite L] [Group X]
    (hq : CFSG.Open.IsQuasisimple L) (hc : Nat.card (Subgroup.center L) = 3)
    (e : L ⧸ Subgroup.center L ≃* X) {u v : X} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (hnu : ∃ n : X, n * u * n⁻¹ = u⁻¹)
    (hnv : ∃ n : X, n * v * n⁻¹ = v⁻¹) (Q : Sylow 3 X)
    (hQ : (Q : Subgroup X) = Subgroup.closure {u, v}) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  let φ : L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
  obtain ⟨a, b, ha, hb, hab, P, hP, haP, hbP⟩ := exists_pair_of_cover hq.1 hφ hker hZp
    (by rw [hc]) hu hv hnu hnv Q hQ
  exact not_forall_commute_of_isPGroup ha hb hab hP haP hbP S

@[expose] def CentralOmegaReduced : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    IsCatalogGroup (L ⧸ Subgroup.center L) → Subgroup.center L ≠ ⊥ →
    IsPGroup 3 (Subgroup.center L) → CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 →
      ∀ S : Sylow 3 L, ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L),
        a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a

theorem kFactCentralOmega_of_reduced (h : CentralOmegaReduced) : KFactCentralOmega := by
  intro K _ _ hq hcat h3 hrk S
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : (3 : ℕ).Prime := Nat.prime_three
  let N : Subgroup K := GL83.I243.Cover.primeCentre 3 K
  have hqN : CFSG.Open.IsQuasisimple (K ⧸ N) := GL83.I243.Cover.isQuasisimple_quotient hq
  have hcatN : IsCatalogGroup ((K ⧸ N) ⧸ Subgroup.center (K ⧸ N)) := by
    obtain ⟨e⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
    obtain ⟨i, ⟨f⟩⟩ := hcat
    exact ⟨i, ⟨e.trans f⟩⟩
  have hcore : CFSG.pCore 3 K ≠ ⊥ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 3 h3
    have hzo : orderOf (z : K) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have hz3 : (z : K) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
    have hle : Subgroup.zpowers (z : K) ≤ CFSG.pCore 3 K :=
      le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2),
        isPGroup_zpowers_of_pow_three hz3⟩
    intro hbot
    rw [hbot] at hle
    have h1 : (z : K) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    rw [h1, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  have hneN : Subgroup.center (K ⧸ N) ≠ ⊥ := GL83.I243.Cover.center_quotient_ne_bot hq hcore
  have hZpN : IsPGroup 3 (Subgroup.center (K ⧸ N)) := GL83.I243.Cover.isPGroup_center_quotient hq
  have hNc : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp GL83.I243.Cover.coprime_card_primeCentre
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hNc
  have hrkN : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ N)) ≤ 3 := by
    have h1 := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp (QuotientGroup.mk' N) hker
      (⊤ : Subgroup K)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    omega
  have hmk : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hS' := h (K ⧸ N) hqN hcatN hneN hZpN hrkN (S.mapSurjective hmk)
  intro hall
  apply hS'
  have hSN : (S : Subgroup K) ⊓ N = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.inf_eq_bot_of_isPGroup_of_not_dvd hp S.isPGroup' hNc
  have hcube : ∀ a ∈ (S : Subgroup K), QuotientGroup.mk' N a ^ 3 = 1 → a ^ 3 = 1 := by
    intro a ha ha3
    have hmem : a ^ 3 ∈ (S : Subgroup K) ⊓ N := by
      refine ⟨Subgroup.pow_mem _ ha 3, ?_⟩
      rw [← map_pow] at ha3
      exact (QuotientGroup.eq_one_iff _).mp ha3
    rw [hSN] at hmem
    exact Subgroup.mem_bot.mp hmem
  intro a' ha' b' hb' ha'3 hb'3
  rw [Sylow.coe_mapSurjective] at ha' hb'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  rw [← map_mul, ← map_mul, hall a ha b hb (hcube a ha ha'3) (hcube b hb hb'3)]

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
