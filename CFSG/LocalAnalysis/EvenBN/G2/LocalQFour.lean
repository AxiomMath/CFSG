module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFour
public import CFSG.LocalAnalysis.EvenBN.G2.AutomorphismsTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalDescent
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open scoped commutatorElement Pointwise

namespace G2Data

section QFour

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [Finite K] [CharP K 2]

theorem leviA2_le_centralizer_J₁ (hK4 : Nat.card K = 4) :
    d.leviA2 ≤ centralizer (d.J₁ : Set G) := by
  rw [← (d.yamada_3_10_J₁_four_G hK4).1]
  exact inf_le_right

theorem leviA2_inf_centralizer (hK4 : Nat.card K = 4) :
    d.leviA2 ⊓ centralizer (d.leviA2 : Set G) = d.J₁ := by
  rw [← map_subtype_center_eq, (d.yamada_3_10_J₁_four_G hK4).2.2.1]

theorem isQuasisimple_leviA2 (hK4 : Nat.card K = 4) : CFSG.IsQuasisimple d.leviA2 := by
  obtain ⟨e⟩ := (d.yamada_3_10_J₁_four_G hK4).2.2.2.2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 K
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))

theorem lieModel_leviA2 (hK4 : Nat.card K = 4) :
    LieModel (d.leviA2 ⧸ center d.leviA2) .PSL 3 2 2 := by
  obtain ⟨e⟩ := (d.yamada_3_10_J₁_four_G hK4).2.2.2.2
  let e₁ : d.leviA2 ≃* Matrix.SpecialLinearGroup (Fin 3) K := e.symm
  let e₂ := QuotientGroup.congr (center d.leviA2)
    (center (Matrix.SpecialLinearGroup (Fin 3) K)) e₁ (map_center_eq e₁)
  let e₃ := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).symm
  exact SeitzReduction.LinearPilot.lieModel_of_mulEquiv_projectiveSL le_rfl (by norm_num)
    (by rw [hK4]; norm_num) (e₂.trans e₃)

theorem leviA2_eq_layer (hK4 : Nat.card K = 4) :
    d.leviA2 = CFSG.inSubgroup CFSG.layer (L ⊓ centralizer (d.J₁ : Set G)) := by
  rw [(d.yamada_3_10_J₁_four_G hK4).1]
  exact (SeitzReduction.LinearPilot.inSubgroup_layer_eq_of_commutator_mem le_rfl
    (fun g hg k hk => mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk))
    (d.isQuasisimple_leviA2 hK4)).symm

end QFour

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

variable {K : Type} [Field K]

theorem t_mem_centralizer_J₁ (h : Setup G L f t) (d : G2Data L K) :
    t ∈ centralizer (d.J₁ : Set G) :=
  mem_centralizer_iff.2 fun j hj => mem_centralizer_iff.1 h.htL j (d.image_le _ hj)

theorem t_mem_centralizer_leviA2 (h : Setup G L f t) (d : G2Data L K) :
    t ∈ centralizer (d.leviA2 : Set G) :=
  mem_centralizer_iff.2 fun k hk => mem_centralizer_iff.1 h.htL k (d.image_le _ hk)

theorem centralizer_J₁_ne_top [Finite K] (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    centralizer (d.J₁ : Set G) ≠ ⊤ := by
  intro htop
  have := h.simple
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := h.nonab
      exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
  have hJ : d.J₁ = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    have hjZ : j ∈ center G := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ centralizer (d.J₁ : Set G) := htop ▸ mem_top g
      exact (mem_centralizer_iff.1 hg j hj).symm
    rw [hZ] at hjZ
    exact hjZ
  have h1 := d.card_J₁
  rw [hJ, card_bot, hK] at h1
  have := h.four_le
  omega

end Light

section QFour

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem card_le_two_of_le_centralizer_leviA2 (h : Setup G L f t) (d : G2Data L K)
    (hK4 : Nat.card K = 4) {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (d.J₁ : Set G) ⊓ centralizer ({t} : Set G) ⊓
      centralizer (d.leviA2 : Set G)) : Nat.card U ≤ 2 := by
  obtain ⟨hKeq, -, -, -, -⟩ := d.yamada_3_10_J₁_four_G hK4
  have hc := (d.yamada_3_22_centralizer_G (n := 2) (by rw [hK4]; norm_num) le_rfl).1
  rw [hKeq] at hc
  have hCLN : centralizer (L : Set G) ≤ normalizer (d.leviA2 : Set G) := fun c hc' =>
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun k hk => (mem_centralizer_iff.1 hc' k (d.image_le _ hk)))
  have hUt : U ≤ zpowers t := by
    intro u hu
    obtain ⟨⟨-, hut⟩, huK⟩ := hUC hu
    have huN : u ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hut
    obtain ⟨l, hl, c, hcL, rfl⟩ := Common.exists_mul_of_le_normalizer hCLN _ (hc ⟨huN, huK⟩)
    have hlL : l ∈ L := d.image_le _ hl
    have hcl : l * c = c * l := mem_centralizer_iff.1 hcL l hlL
    have hlZ : l ∈ d.J₁ := by
      rw [← d.leviA2_inf_centralizer hK4]
      refine ⟨hl, mem_centralizer_iff.2 fun k hk => ?_⟩
      have h1 := mem_centralizer_iff.1 huK k hk
      have h2 := mem_centralizer_iff.1 hcL k (d.image_le _ hk)
      calc k * l = k * (l * c) * c⁻¹ := by group
        _ = l * c * k * c⁻¹ := by rw [h1]
        _ = l * (c * k) * c⁻¹ := by group
        _ = l * (k * c) * c⁻¹ := by rw [h2]
        _ = l * k := by group
    obtain ⟨n, hn⟩ := hU ⟨_, hu⟩
    have hn' : (l * c) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [(show Commute l c from hcl).mul_pow] at hn'
    have hl1 : l ^ 2 ^ n = 1 := by
      have hmem : l ^ 2 ^ n ∈ L ⊓ centralizer (L : Set G) := by
        refine Subgroup.mem_inf.2 ⟨pow_mem hlL _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hn']
        exact inv_mem (pow_mem hcL _)
      rw [h.inf_centralizer_eq_bot] at hmem
      exact hmem
    have hl3 : orderOf l ∣ 3 := by
      have := orderOf_dvd_natCard (⟨l, hlZ⟩ : d.J₁)
      rwa [orderOf_mk, d.card_J₁, hK4] at this
    have hl2 : orderOf l ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hl1
    have hco : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    have hl : l = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hco hl3 hl2)
    rw [hl, one_mul, ← h.centralizer_L_inf]
    exact ⟨hcL, by rw [hl, one_mul] at hut; exact hut⟩
  calc Nat.card U ≤ Nat.card (zpowers t) := card_le_of_le hUt
    _ = 2 := by rw [Nat.card_zpowers, h.ht]

theorem exists_mem_yamadaD₁_inf_centralizer_J₁_mul (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {m : G} (hm : m ∈ yamadaD₁ d t) :
    ∃ c ∈ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G), ∃ n ∈ d.D, m = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNU, hND, -, -⟩ := d.yamada_3_13_2_G
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hJ₁D : d.J₁ ≤ normalizer (d.D : Set G) := fun j hj => by
    have : j ∈ L ⊓ normalizer (d.D : Set G) := by
      rw [hND, ← hNU]
      exact d.J₁_le_inf_normalizer_U hj
    exact this.2
  have h2 := h.isPGroup_yamadaD₁ d hK
  have hsolv : Group.IsSolvable (yamadaD₁ d t) := by
    have := h2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₁).Coprime (Nat.card (yamadaD₁ d t)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [hk, d.card_J₁, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  exact Common.exists_mem_inf_centralizer_mul_of_coprime hDD₁
    ((h.yamadaD₁_le_yamadaC₁ d hK).trans (h.yamadaC₁_le_normalizer_D d hK))
    (fun j hj => h.inf_normalizer_U_le_normalizer_yamadaD₁ d hK (d.J₁_le_inf_normalizer_U hj))
    hJ₁D hsolv hcop hm fun j hj => h.mul_conj_mem_D_of_mem_J₁ d hK hm hj

theorem exists_mem_yamadaD₁_inf_centralizer_J₁_ne (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    ∃ c ∈ yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G), c * t ≠ t * c := by
  obtain ⟨-, -, hC₁tr, -⟩ := h.two_core_C₁ d hK
  have hU1 : d.U ≠ ⊥ := by
    intro hb
    have h1 := d.cards.1
    rw [hb, card_bot] at h1
    have := h.four_le
    omega
  obtain ⟨y, hyU, hy1⟩ := (d.U.bot_or_exists_ne_one).resolve_left hU1
  obtain ⟨x, hx, hxy⟩ := hC₁tr y hyU
  rw [(h.yamada_5_8_1 d hK).2.1] at hx
  have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
    (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK (h.t_mem_yamadaC₁ d hK))
  obtain ⟨m, hm, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hx
  obtain ⟨c, hc, n, hn, rfl⟩ := h.exists_mem_yamadaD₁_inf_centralizer_J₁_mul d hK hm
  refine ⟨c, hc, fun hct => ?_⟩
  have hτt : τ * t = t * τ := (commute_of_mem_zpowers hτ h.t_mem_centralizer).symm
  have hnt : n * t = t * n := mem_centralizer_singleton_iff.1
    (h.L_le_centralizer (d.image_le _ hn))
  have e : (c * n * τ)⁻¹ * t * (c * n * τ) = t := by
    calc (c * n * τ)⁻¹ * t * (c * n * τ) = τ⁻¹ * n⁻¹ * (c⁻¹ * (t * c)) * n * τ := by group
      _ = τ⁻¹ * n⁻¹ * (c⁻¹ * (c * t)) * n * τ := by rw [hct]
      _ = τ⁻¹ * (n⁻¹ * (t * n)) * τ := by group
      _ = τ⁻¹ * (n⁻¹ * (n * t)) * τ := by rw [hnt]
      _ = τ⁻¹ * (t * τ) := by group
      _ = τ⁻¹ * (τ * t) := by rw [hτt]
      _ = t := by group
  rw [e] at hxy
  exact hy1 (by simpa using hxy.symm)

theorem yamada_5_10_hr7 (h : Setup G L f t) (d : G2Data L K) (hK4 : Nat.card K = 4) :
    CFSG.Open.IsComponentOf
        ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))))
        (centralizer {(QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
            ⟨t, h.t_mem_centralizer_J₁ d⟩)}) ∧
      (∀ U : Subgroup (centralizer (d.J₁ : Set G) ⧸ CFSG.oddCore (centralizer (d.J₁ : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer (((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G))))) :
          Set (centralizer (d.J₁ : Set G) ⧸ CFSG.oddCore (centralizer (d.J₁ : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G))))) :=
  SeitzReduction.standard_inheritance h.std h.htL h.ht (h.t_mem_centralizer_J₁ d)
    (d.leviA2_eq_layer hK4)
    (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
      (d.isQuasisimple_leviA2 hK4))
    fun _ hU hUC => h.card_le_two_of_le_centralizer_leviA2 d hK4 hU hUC

theorem not_normal_leviA2_bar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) :
    ¬ ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G))))).Normal := by
  intro hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (d.J₁ : Set G) with hH
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  set Kb := (d.leviA2.subgroupOf H).map π with hKb
  have htH : t ∈ H := h.t_mem_centralizer_J₁ d
  set tb : H ⧸ CFSG.oddCore H := π ⟨t, htH⟩ with htb
  obtain ⟨-, hsyl, -⟩ := h.yamada_5_10_hr7 d hK4
  set T : Subgroup H := (yamadaC₁ d t).subgroupOf H with hT
  have hTp : IsPGroup 2 T := (LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype
  have htT : (⟨t, htH⟩ : H) ∈ T := h.t_mem_yamadaC₁ d hK
  have hO : Odd (Nat.card (CFSG.oddCore H)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have hTO : ∀ y ∈ T, y ∈ CFSG.oddCore H → y = 1 := by
    intro y hyT hyO
    obtain ⟨k, hk⟩ := hTp ⟨y, hyT⟩
    have hyk : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
    have h2 : orderOf y ∣ Nat.card (CFSG.oddCore H) := by
      have := orderOf_dvd_natCard (⟨y, hyO⟩ : CFSG.oddCore H)
      rwa [orderOf_mk] at this
    have h3 : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore H)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hO)
    exact orderOf_eq_one_iff.1 ((h3.coprime_dvd_left h1).eq_one_of_dvd h2)
  have htb1 : tb ≠ 1 := by
    intro h1
    have h2 : (⟨t, htH⟩ : H) ∈ CFSG.oddCore H := (QuotientGroup.eq_one_iff _).1 h1
    have := hTO _ htT h2
    exact h.t_ne_one (congrArg Subtype.val this)
  have htbK : tb ∈ centralizer (Kb : Set (H ⧸ CFSG.oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [htb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.1 (h.t_mem_centralizer_leviA2 d) _ (mem_subgroupOf.1 hk)
  set U := T.map π ⊓ centralizer (Kb : Set (H ⧸ CFSG.oddCore H)) with hU
  have hUp : IsPGroup 2 U := (hTp.map π).to_le inf_le_left
  have hU2 := hsyl U hUp inf_le_right
  have htbU : tb ∈ U := ⟨⟨_, htT, rfl⟩, htbK⟩
  have hcomm : ∀ x ∈ T, x * ⟨t, htH⟩ = ⟨t, htH⟩ * x := by
    intro x hxT
    have hxT' : π x ∈ T.map π := ⟨x, hxT, rfl⟩
    have hxb : π x * tb * (π x)⁻¹ ∈ U := by
      refine Subgroup.mem_inf.2 ⟨(T.map π).mul_mem
        ((T.map π).mul_mem hxT' (Subgroup.mem_inf.1 htbU).1) ((T.map π).inv_mem hxT'), ?_⟩
      rw [mem_centralizer_iff]
      intro k hk
      have hk' : (π x)⁻¹ * k * π x ∈ Kb := by
        have := hN.conj_mem k hk (π x)⁻¹
        rwa [inv_inv] at this
      have hc := mem_centralizer_iff.1 htbK _ hk'
      calc k * (π x * tb * (π x)⁻¹) = π x * ((π x)⁻¹ * k * π x * tb) * (π x)⁻¹ := by group
        _ = π x * (tb * ((π x)⁻¹ * k * π x)) * (π x)⁻¹ := by rw [hc]
        _ = π x * tb * (π x)⁻¹ * k := by group
    have heq : π x * tb * (π x)⁻¹ = tb := by
      by_contra hne
      have hne1 : π x * tb * (π x)⁻¹ ≠ 1 := fun h1 => htb1 (by
        have := congrArg (fun z => (π x)⁻¹ * z * π x) h1
        simpa [mul_assoc] using this)
      let e : Fin 3 → U := ![1, ⟨tb, htbU⟩, ⟨π x * tb * (π x)⁻¹, hxb⟩]
      have he : Function.Injective e := by
        intro a b hab
        fin_cases a <;> fin_cases b <;>
          simp only [e, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue] at hab ⊢
        all_goals first
          | rfl
          | exact absurd (congrArg Subtype.val hab) (by
              simp only [OneMemClass.coe_one]
              first
                | exact fun e => htb1 e.symm
                | exact fun e => hne1 e.symm
                | exact fun e => htb1 e
                | exact fun e => hne1 e
                | exact fun e => hne e.symm
                | exact fun e => hne e)
      have h3 := Nat.card_le_card_of_injective e he
      rw [Nat.card_fin] at h3
      have h4 := h3.trans hU2
      norm_num at h4
    have hcomm : x * ⟨t, htH⟩ * x⁻¹ * (⟨t, htH⟩ : H)⁻¹ ∈ CFSG.oddCore H := by
      have hπ1 : π (x * ⟨t, htH⟩ * x⁻¹ * (⟨t, htH⟩ : H)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← htb, heq, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).1 hπ1
    have h1 := hTO _ (mul_mem (mul_mem (mul_mem hxT htT) (inv_mem hxT)) (inv_mem htT)) hcomm
    have := congrArg (fun z => z * ⟨t, htH⟩ * x) h1
    simpa [mul_assoc] using this
  obtain ⟨c, ⟨hcD₁, hcJ⟩, hct⟩ := h.exists_mem_yamadaD₁_inf_centralizer_J₁_ne d hK
  have hcT : (⟨c, hcJ⟩ : H) ∈ T := h.yamadaD₁_le_yamadaC₁ d hK hcD₁
  exact hct (congrArg Subtype.val (hcomm _ hcT))

theorem yamada_5_10_layer_of_cat (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    ∃ Kc : Subgroup (centralizer (d.J₁ : Set G) ⧸ CFSG.oddCore (centralizer (d.J₁ : Set G))),
      CFSG.IsComponent Kc ∧
      (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom = Kc ∧
          (d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) < Kc ∧
          QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
              ⟨t, h.t_mem_centralizer_J₁ d⟩ ∉ Kc ∧
          (∃ hsN : QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))
                ⟨t, h.t_mem_centralizer_J₁ d⟩ ∈ normalizer (Kc : Set _),
            Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL 3 2 4) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer (d.J₁ : Set G))) ⟨t, h.t_mem_centralizer_J₁ d⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* ((d.leviA2.subgroupOf (centralizer (d.J₁ : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore (centralizer (d.J₁ : Set G)))) : Subgroup _)))) := by
  obtain ⟨hcomp, hsyl, hstd⟩ := h.yamada_5_10_hr7 d hK4
  have hov := SeitzReduction.LinearPilot.neighbour_overgroup_slm_center (f := 2) le_rfl
    (Or.inr le_rfl) hcat h.kproper (h.centralizer_J₁_ne_top d hK) (h.t_mem_centralizer_J₁ d) h.ht
    (d.leviA2_le_centralizer_J₁ hK4) (d.isQuasisimple_leviA2 hK4) (d.lieModel_leviA2 hK4)
    hcomp hsyl hstd (h.not_normal_leviA2_bar d hK hK4)
  exact SeitzReduction.LinearPilot.NeighbourOvergroupSLm.exact
    (SeitzReduction.F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (Or.inr le_rfl) hov

end QFour

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
