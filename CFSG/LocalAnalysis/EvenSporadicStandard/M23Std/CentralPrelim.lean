module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarWreath
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelCentralizerSurjective

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

theorem isSylowOf_map_top {A Y : Type} [Group A] [Finite A] [Group Y] [Finite Y] (f : A →* Y)
    (hf : Function.Surjective f) {Q : Subgroup A} (hQ : IsPGroup 2 Q) (hidx : ¬ 2 ∣ Q.index) :
    IsSylowOf 2 (Q.map f) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_iff.2 ⟨le_top, hQ.map f, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact fun h => hidx (h.trans (Subgroup.index_map_dvd Q hf))

theorem eq_one_of_mem_oddCore_centralizer {X : Type} [Group X] [Finite X] {z : X}
    (e : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 7))
    {c : X} (hc : c ∈ centralizer ({z} : Set X)) (hcO : c ∈ fusionOddCore X) : c = 1 := by
  classical
  have hOodd : Odd (Nat.card (fusionOddCore X)) := natCard_fusionOddCore_odd X
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hCbot : fusionOddCore (centralizer ({z} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_equiv e
      (fusionOddCore_prod_eq_bot_of_simple even_natCard_alternatingGroup_seven)
  have hnormal : ((fusionOddCore X).comap (centralizer ({z} : Set X)).subtype).Normal :=
    (inferInstance : (fusionOddCore X).Normal).comap _
  have hodd : Odd (Nat.card ((fusionOddCore X).comap (centralizer ({z} : Set X)).subtype)) := by
    have hle : ((fusionOddCore X).comap (centralizer ({z} : Set X)).subtype).map
        (centralizer ({z} : Set X)).subtype ≤ fusionOddCore X := by
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (centralizer ({z} : Set X)).subtype_injective] at h1
    exact Odd.of_dvd_nat hOodd h1
  have hle := le_fusionOddCore_of_odd hodd
  rw [hCbot, le_bot_iff] at hle
  have hc' : (⟨c, hc⟩ : centralizer ({z} : Set X)) ∈
      (fusionOddCore X).comap (centralizer ({z} : Set X)).subtype := hcO
  rw [hle, mem_bot] at hc'
  exact congrArg Subtype.val hc'

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

@[expose] def Nbar (L F L1 : Subgroup G) : Subgroup (Ybar L1) :=
  ((normalizer (F : Set G) ⊓ L).subgroupOf (normalizer (L1 : Set G))).map (piY L1)

omit [Finite G] in
theorem mem_Nbar_iff {y : Ybar L1} :
    y ∈ Nbar L F L1 ↔ ∃ x : ↥(normalizer (L1 : Set G)),
      (x : G) ∈ normalizer (F : Set G) ⊓ L ∧ piY L1 x = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem exists_centralizer_piY (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    (y : Ybar L1) :
    ∃ c : ↥(normalizer (L1 : Set G)), (c : G) ∈ centralizer ({z} : Set G) ∧ piY L1 c = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : (QuotientGroup.mk S.zX : Xbar L1) * QuotientGroup.mk S.zX = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
    rw [this, QuotientGroup.mk_one]
  have hz1 : (QuotientGroup.mk S.zX : Xbar L1) ≠ 1 := by
    intro h
    have := S.orderOf_zbar
    rw [h, orderOf_one] at this
    omega
  obtain ⟨x, hx, hxy⟩ := CFSG.GorensteinWalter.exists_centralizer_lift_of_odd_kernel
    (fusionOddCore (Xbar L1)) (natCard_fusionOddCore_odd (Xbar L1))
    ⟨hz1, by rw [pow_two]; exact hz2⟩ y (mem_centralizer_singleton_iff.2 (hcen y))
  rw [S.centralizer_zbar_eq] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨c, Subgroup.mem_subgroupOf.1 hc, hxy⟩

theorem mem_F_of_piY_eq_one (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F)
    {c : ↥(normalizer (L1 : Set G))} (hc : (c : G) ∈ centralizer ({z} : Set G))
    (h1 : piY L1 c = 1) : (c : G) ∈ F := by
  obtain ⟨e⟩ := S.centralizer_zbar_equiv hA7
  have hcO : (QuotientGroup.mk c : Xbar L1) ∈ fusionOddCore (Xbar L1) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have hcb : (QuotientGroup.mk c : Xbar L1) ∈ centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} :
      Set (Xbar L1)) := by
    rw [S.centralizer_zbar_eq]
    exact ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩
  have h2 : (QuotientGroup.mk c : Xbar L1) = 1 := eq_one_of_mem_oddCore_centralizer e hcb hcO
  have hcC : (c : G) ∈ centralizer (L1 : Set G) :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
  have := centralizer_X_z_inf_C S.one S.nd S.L1_normE S.L1_cz S.F_le S.L1_comm S.L1_card S.K_eq
    S.z_norm
  rw [← this]
  exact mem_inf.2 ⟨mem_inf.2 ⟨c.2, hc⟩, hcC⟩

theorem zbar_not_mem_Nbar (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F) :
    piY L1 S.zX ∉ Nbar L F L1 := by
  intro h
  obtain ⟨x, hx, hxz⟩ := mem_Nbar_iff.1 h
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxL : (x : G) ∈ L := (mem_inf.1 hx).2
  have hzx : z * (x : G) = (x : G) * z := S.one.z_comm _ hxL
  have hc : ((S.zX⁻¹ * x : ↥(normalizer (L1 : Set G))) : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : ((S.zX⁻¹ * x : ↥(normalizer (L1 : Set G))) : G) = z⁻¹ * (x : G) := rfl
    rw [this, hzi]
    calc z * (x : G) * z = z * ((x : G) * z) := by group
      _ = z * (z * (x : G)) := by rw [← hzx]
  have h1 : piY L1 (S.zX⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hxz]
    exact inv_mul_cancel _
  have hF := S.mem_F_of_piY_eq_one hA7 hc h1
  have : ((S.zX⁻¹ * x : ↥(normalizer (L1 : Set G))) : G) = z⁻¹ * (x : G) := rfl
  rw [this, hzi] at hF
  apply S.one.z_not_mem
  have : z = (z * (x : G)) * (x : G)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (S.nd.F_le hF) (Subgroup.inv_mem _ hxL)

theorem D_le_X : normalizer (F : Set G) ⊓ L ≤ normalizer (L1 : Set G) :=
  le_sup_right.trans S.Q_le_X

omit [Finite G] in
theorem eq_or_eq_mul_of_mem_sup {c : G} (hc : c ∈ zpowers z ⊔ (normalizer (F : Set G) ⊓ L)) :
    (∃ d ∈ normalizer (F : Set G) ⊓ L, c = d) ∨ ∃ d ∈ normalizer (F : Set G) ⊓ L, c = z * d := by
  have hDc : normalizer (F : Set G) ⊓ L ≤ centralizer (zpowers z : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute z d from S.one.z_comm d (mem_inf.1 hd).2) k).eq
  obtain ⟨a, ha, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hDc hc
  rcases mem_zpowers_involution S.one.z_mul_self ha with rfl | rfl
  · exact Or.inl ⟨d, hd, by rw [one_mul]⟩
  · exact Or.inr ⟨d, hd, rfl⟩

theorem Nbar_index_eq_two (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F)
    (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y) : (Nbar L F L1).index = 2 := by
  refine Subgroup.index_eq_two_iff.2 ⟨piY L1 S.zX, fun y => ?_⟩
  have hzb2 : piY L1 S.zX * piY L1 S.zX = 1 := S.zbar_sq
  have hnot := S.zbar_not_mem_Nbar hA7
  obtain ⟨c, hc, rfl⟩ := S.exists_centralizer_piY hcen y
  have hcQ : (c : G) ∈ zpowers z ⊔ (normalizer (F : Set G) ⊓ L) :=
    S.inf_centralizer_eq ▸ mem_inf.2 ⟨c.2, hc⟩
  rcases S.eq_or_eq_mul_of_mem_sup hcQ with ⟨d, hd, hcd⟩ | ⟨d, hd, hcd⟩
  · have hyN : piY L1 c ∈ Nbar L F L1 := mem_Nbar_iff.2 ⟨c, hcd ▸ hd, rfl⟩
    refine Or.inr ⟨hyN, fun h => hnot ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) h
    simpa using this
  · have hdX : d ∈ normalizer (L1 : Set G) := S.D_le_X hd
    have hy : piY L1 c = piY L1 S.zX * piY L1 ⟨d, hdX⟩ := by
      rw [← map_mul]
      exact congrArg _ (Subtype.ext hcd)
    have hπd : piY L1 ⟨d, hdX⟩ ∈ Nbar L F L1 := mem_Nbar_iff.2 ⟨⟨d, hdX⟩, hd, rfl⟩
    have hyz : piY L1 c * piY L1 S.zX = piY L1 ⟨d, hdX⟩ := by
      calc piY L1 c * piY L1 S.zX = (piY L1 S.zX * piY L1 ⟨d, hdX⟩) * piY L1 S.zX := by rw [hy]
        _ = (piY L1 ⟨d, hdX⟩ * piY L1 S.zX) * piY L1 S.zX := by rw [hcen (piY L1 ⟨d, hdX⟩)]
        _ = piY L1 ⟨d, hdX⟩ * (piY L1 S.zX * piY L1 S.zX) := mul_assoc _ _ _
        _ = piY L1 ⟨d, hdX⟩ := by rw [hzb2, mul_one]
    refine Or.inl ⟨hyz ▸ hπd, fun h => hnot ?_⟩
    have h2 := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hπd)
    rw [hy] at h2
    simpa using h2

end Setup

end CFSG.EvenSporadicStandard.M23Std
