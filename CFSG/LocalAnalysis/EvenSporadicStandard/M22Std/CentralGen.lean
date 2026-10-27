module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.CentralFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.XbarGen

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.EvenSporadicStandard.M23Std

theorem eq_one_of_mem_oddCore_centralizer_gen {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hAe : Even (Nat.card A)) {X : Type} [Group X] [Finite X] {z : X}
    (e : centralizer ({z} : Set X) ≃* Multiplicative (ZMod 2) × A)
    {c : X} (hc : c ∈ centralizer ({z} : Set X)) (hcO : c ∈ fusionOddCore X) : c = 1 := by
  classical
  have hOodd : Odd (Nat.card (fusionOddCore X)) := natCard_fusionOddCore_odd X
  have hCbot : fusionOddCore (centralizer ({z} : Set X)) = ⊥ :=
    fusionOddCore_eq_bot_of_equiv e (fusionOddCore_prod_eq_bot_of_simple hAe)
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
  {A : Type} [Group A] [Finite A] [IsSimpleGroup A]

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem mem_F_of_piY_eq_one_gen (hAe : Even (Nat.card A))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F)
    {c : ↥(normalizer (L1 : Set G))} (hc : (c : G) ∈ centralizer ({z} : Set G))
    (h1 : piY L1 c = 1) : (c : G) ∈ F := by
  obtain ⟨e⟩ := centralizer_zbar_equiv_gen S hA
  have hcO : (QuotientGroup.mk c : Xbar L1) ∈ fusionOddCore (Xbar L1) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have hcb : (QuotientGroup.mk c : Xbar L1) ∈ centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} :
      Set (Xbar L1)) := by
    rw [S.centralizer_zbar_eq]
    exact ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩
  have h2 : (QuotientGroup.mk c : Xbar L1) = 1 :=
    eq_one_of_mem_oddCore_centralizer_gen hAe e hcb hcO
  have hcC : (c : G) ∈ centralizer (L1 : Set G) :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
  have := centralizer_X_z_inf_C S.one S.nd S.L1_normE S.L1_cz S.F_le S.L1_comm S.L1_card S.K_eq
    S.z_norm
  rw [← this]
  exact mem_inf.2 ⟨mem_inf.2 ⟨c.2, hc⟩, hcC⟩

theorem zbar_not_mem_Nbar_gen (hAe : Even (Nat.card A))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) : piY L1 S.zX ∉ Nbar L F L1 := by
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
  have hF := Setup.mem_F_of_piY_eq_one_gen S hAe hA hc h1
  have : ((S.zX⁻¹ * x : ↥(normalizer (L1 : Set G))) : G) = z⁻¹ * (x : G) := rfl
  rw [this, hzi] at hF
  apply S.one.z_not_mem
  have : z = (z * (x : G)) * (x : G)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (S.nd.F_le hF) (Subgroup.inv_mem _ hxL)

theorem Nbar_index_eq_two_gen (hAe : Even (Nat.card A))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F)
    (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y) : (Nbar L F L1).index = 2 := by
  refine Subgroup.index_eq_two_iff.2 ⟨piY L1 S.zX, fun y => ?_⟩
  have hzb2 : piY L1 S.zX * piY L1 S.zX = 1 := S.zbar_sq
  have hnot := Setup.zbar_not_mem_Nbar_gen S hAe hA
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

theorem exists_order_four_gen (hAe : Even (Nat.card A))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) {a4 : A} (ha4 : orderOf a4 = 4) :
    ∃ g₀ : Ybar L1, orderOf g₀ = 4 := by
  obtain ⟨ψ, hψ, hker⟩ := id hA
  obtain ⟨d₀, hd₀⟩ := hψ a4
  have hdX : (d₀ : G) ∈ normalizer (L1 : Set G) := S.D_le_X d₀.2
  refine ⟨piY L1 ⟨d₀, hdX⟩, ?_⟩
  have key : orderOf (piY L1 ⟨d₀, hdX⟩) = orderOf a4 := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    have hpowX : (⟨(d₀ : G), hdX⟩ : ↥(normalizer (L1 : Set G))) ^ n =
        ⟨(d₀ : G) ^ n, (normalizer (L1 : Set G)).pow_mem hdX n⟩ := rfl
    have hDpow : ψ (d₀ ^ n) = a4 ^ n := by
      rw [map_pow, hd₀]
    have hkerD : ψ (d₀ ^ n) = 1 ↔ (d₀ : G) ^ n ∈ F := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    rw [← hDpow, hkerD, ← map_pow, hpowX]
    constructor
    · intro h
      have hcomm : (d₀ : G) * z = z * (d₀ : G) := (S.one.z_comm _ (mem_inf.1 d₀.2).2).symm
      refine Setup.mem_F_of_piY_eq_one_gen S hAe hA (c := ⟨(d₀ : G) ^ n, _⟩) ?_ h
      exact mem_centralizer_singleton_iff.2
        (Commute.pow_left (show Commute (d₀ : G) z from hcomm) n).eq
    · intro h
      exact S.piY_eq_one_of_mem_L1 (S.F_le h) _
  rw [key, ha4]

theorem exists_order_four_mem_sylow_gen (hAe : Even (Nat.card A))
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) {a4 : A} (ha4 : orderOf a4 = 4)
    (R : Sylow 2 (Ybar L1)) : ∃ g₁ ∈ R, orderOf g₁ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := Setup.exists_order_four_gen S hAe hA ha4
  have hpg : IsPGroup 2 (zpowers g₀) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg₀]; norm_num)
  obtain ⟨h, hh⟩ := exists_conj_mem_sylow R hpg
  refine ⟨h * g₀ * h⁻¹, hh, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj h) g₀
  rw [MulAut.conj_apply] at this
  rw [this, hg₀]

theorem weakly_closed_gen (hAe : Even (Nat.card A)) (hFix : FixFour L F)
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) {a4 : A} (ha4 : orderOf a4 = 4)
    (hL2 : ¬ 256 ∣ Nat.card L) (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G)))
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    ∀ g : G, (∀ x ∈ L1, g * x * g⁻¹ ∈ P) → ∀ x ∈ L1, g * x * g⁻¹ ∈ L1 := by
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxn⟩ := hcon
  have hPX : P ≤ normalizer (L1 : Set G) := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  obtain ⟨R, hRP, hRQ⟩ := S.exists_sylow_piY hcen hP hT
  have hR16 := S.card_sylow_piY_le hL2 hP hT R hRQ
  obtain ⟨g₁, hg₁R, hg₁o⟩ := Setup.exists_order_four_mem_sylow_gen S hAe hA ha4 R
  have hℓP : g * x * g⁻¹ ∈ P := hg x hx
  have hℓ2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [S.L1_sq x hx]; group
  have hcard16 := S.card_centralizer_L1_involution hFix hcen hP hT hℓP hℓ2 hxn
  set L' : Subgroup G := L1.map (MulAut.conj g).toMonoidHom with hL'
  have hL'mem : ∀ y, y ∈ L' ↔ ∃ w ∈ L1, y = g * w * g⁻¹ := by
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hL'P : L' ≤ P := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (hL'mem y).1 hy
    exact hg w hw
  have hL'X : L' ≤ normalizer (L1 : Set G) := hL'P.trans hPX
  have hL'card : Nat.card L' = 256 := by
    rw [hL', Subgroup.card_map_of_injective (MulAut.conj g).injective, S.L1_card]
  have hL'sq : ∀ y ∈ L', y * y = 1 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := (hL'mem y).1 hy
    calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [S.L1_sq w hw]; group
  let ρ : ↥L' →* Ybar L1 := (piY L1).comp (Subgroup.inclusion hL'X)
  have hρR : ∀ a : ↥L', ρ a ∈ (R : Subgroup (Ybar L1)) := fun a => hRP a (hL'P a.2)
  have hkey : ∀ a : ↥ρ.ker, ((a.1 : ↥L') : G) ∈ L1 ⊓ centralizer ({g * x * g⁻¹} : Set G) := by
    intro a
    have hy1 : ((a.1 : ↥L') : G) ∈ L1 :=
      S.mem_L1_of_piY_eq_one hP.isPGroup hL1P (hL'P a.1.2) (hL'X a.1.2) a.2
    refine mem_inf.2 ⟨hy1, mem_centralizer_singleton_iff.2 ?_⟩
    obtain ⟨w, hw, hwy⟩ := (hL'mem _).1 a.1.2
    rw [hwy]
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [S.L1_comm w hw x hx]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  have hkerle : Nat.card ρ.ker ≤ 16 := by
    rw [← hcard16]
    refine Nat.card_le_card_of_injective (fun a : ↥ρ.ker => ⟨_, hkey a⟩) (fun a b h => ?_)
    have h' := congrArg (fun u : ↥(L1 ⊓ centralizer ({g * x * g⁻¹} : Set G)) => (u : G)) h
    exact Subtype.ext (Subtype.ext h')
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hL'card] at h1
  have hrange16 : 16 ≤ Nat.card ρ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ρ.ker * Nat.card ρ.range < 16 * 16 := by
      calc Nat.card ρ.ker * Nat.card ρ.range ≤ 16 * Nat.card ρ.range :=
            Nat.mul_le_mul_right _ hkerle
        _ < 16 * 16 := by omega
    omega
  have hρle : ρ.range ≤ (R : Subgroup (Ybar L1)) := by
    rintro _ ⟨a, rfl⟩
    exact hρR a
  have hρeq : ρ.range = (R : Subgroup (Ybar L1)) :=
    Subgroup.eq_of_le_of_card_ge hρle (by omega)
  have hg₁range : g₁ ∈ ρ.range := hρeq ▸ hg₁R
  obtain ⟨a, rfl⟩ := hg₁range
  have ha : a * a = 1 := Subtype.ext (hL'sq a a.2)
  have : ρ a ^ 2 = 1 := by rw [pow_two, ← map_mul, ha, map_one]
  have := orderOf_dvd_of_pow_eq_one this
  rw [hg₁o] at this
  omega

theorem false_of_central_gen [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hAe : Even (Nat.card A)) (hFix : FixFour L F)
    (hA : NormQuot A (normalizer (F : Set G) ⊓ L) F) {a4 : A} (ha4 : orderOf a4 = 4)
    (hL2 : ¬ 256 ∣ Nat.card L) (hnc : ∀ x ∈ L1, ¬ IsConj z x)
    (hcen : ∀ y : Ybar L1, y * piY L1 S.zX = piY L1 S.zX * y) : False := by
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hz1 : z ≠ 1 := S.one.z_ne_one
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨P, hP, hzP, hT⟩ := S.exists_sylow_X hL2
  have hPX : P ≤ normalizer (L1 : Set G) := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  have hwc := Setup.weakly_closed_gen S hAe hFix hA ha4 hL2 hcen hP hT
  have hSyl : ¬ 2 ∣ P.index := not_dvd_index_of_weakly_closed hP.isPGroup hL1P hwc hPX hP
  have hnot := Setup.zbar_not_mem_Nbar_gen S hAe hA
  have hidx := S.relIndex_inf_preimageY (Setup.Nbar_index_eq_two_gen S hAe hA hcen) hnot hPX hzP
  have hz0 : z ∉ P ⊓ preimageY L1 (Nbar L F L1) := fun h =>
    hnot ((mem_preimageY_iff S.zX.2).1 (mem_inf.1 h).2)
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hP.isPGroup hSyl inf_le_left hidx hzP hz0
    hz2'
  obtain ⟨hyP, hyM⟩ := mem_inf.1 hg
  obtain ⟨hyX, hyN⟩ := mem_preimageY.1 hyM
  have hconj : IsConj z (g⁻¹ * z * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  have hy2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨d, hd, l, hl, hyd⟩ := S.exists_eq_mul_of_mem_sylowX hcen hP hT hyP
  have hdX : d ∈ normalizer (L1 : Set G) := S.D_le_X hd
  rcases hyd with hyd | hyd
  · by_cases hdF : d ∈ F
    · exact hnc _ (hyd ▸ L1.mul_mem (S.F_le hdF) hl) hconj
    · exact S.not_isConj_z_mul hFix hd hdF hl (hyd ▸ hy2) (hyd ▸ hconj)
  · have hlX : l ∈ normalizer (L1 : Set G) := Subgroup.le_normalizer hl
    have hπ : piY L1 ⟨g⁻¹ * z * g, hyX⟩ = piY L1 S.zX * piY L1 ⟨d, hdX⟩ := by
      have : (⟨g⁻¹ * z * g, hyX⟩ : ↥(normalizer (L1 : Set G))) =
          S.zX * ⟨d, hdX⟩ * ⟨l, hlX⟩ := Subtype.ext hyd
      rw [this, map_mul, map_mul, S.piY_eq_one_of_mem_L1 hl hlX, mul_one]
    have hπd : piY L1 ⟨d, hdX⟩ ∈ Nbar L F L1 := mem_Nbar_iff.2 ⟨⟨d, hdX⟩, hd, rfl⟩
    apply hnot
    have := Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hπd)
    rw [hπ] at this
    simpa using this

end Setup

end CFSG.EvenSporadicStandard.M22Std
