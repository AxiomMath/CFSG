module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransferCyclic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

section Action

variable {G : Type*} [Group G] {G₀ : Subgroup G} {n : ℕ} {F : Type*} [Field F]

@[expose] noncomputable def centerQuotientAutHom (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ center X) where
  toFun := centerQuotientAut
  map_one' := centerQuotientAut_one
  map_mul' := centerQuotientAut_mul

@[expose] noncomputable def normalizerQuotientAut (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F) :
    normalizer (G₀ : Set G) →* MulAut (projectiveSL n F) :=
  (MulAut.congr ψ).toMonoidHom.comp ((centerQuotientAutHom G₀).comp G₀.normalizerMonoidHom)

theorem normalizerQuotientAut_apply (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F)
    (m : normalizer (G₀ : Set G)) (x : G₀) :
    normalizerQuotientAut ψ m (ψ (x : G₀ ⧸ center G₀)) =
      ψ ((G₀.normalizerMonoidHom m x : G₀) : G₀ ⧸ center G₀) := by
  change ψ (centerQuotientAut (G₀.normalizerMonoidHom m) (ψ.symm (ψ (x : G₀ ⧸ center G₀)))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg ψ (centerQuotientAut_coe _ x)

theorem normalizerQuotientAut_of_mem (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F) {g : G}
    (hg : g ∈ G₀) :
    normalizerQuotientAut ψ ⟨g, le_normalizer hg⟩ =
      MulAut.conj (ψ ((⟨g, hg⟩ : G₀) : G₀ ⧸ center G₀)) := by
  ext y
  obtain ⟨q, rfl⟩ := ψ.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [normalizerQuotientAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem range_conj_le_range_normalizerQuotientAut (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F) :
    (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range ≤
      (normalizerQuotientAut ψ).range := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨q, rfl⟩ := ψ.surjective u
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨⟨g, le_normalizer g.2⟩, normalizerQuotientAut_of_mem ψ g.2⟩

theorem normalizerQuotientAut_eq_fieldAut (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F)
    {σ : F ≃+* F} {t : G} (htG₀ : t ∈ normalizer (G₀ : Set G))
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      fieldAut n F σ (ψ (x : G₀ ⧸ center G₀))) :
    normalizerQuotientAut ψ ⟨t, htG₀⟩ = fieldAut n F σ := by
  ext y
  obtain ⟨q, rfl⟩ := ψ.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [normalizerQuotientAut_apply, hψt]

end Action

section Kernel

variable {G : Type} [Group G] [Finite G] {L G₀ : Subgroup G} {n : ℕ} {F : Type*} [Field F]

theorem ker_normalizerQuotientAut_inf_centralizer_eq_bot
    (hL : CFSG.Open.standardComponentIsStandard L) (hZL : center L = ⊥) (hLG₀ : L ≤ G₀) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (htρ : normalizerQuotientAut ψ ⟨t, htG₀⟩ ≠ 1) :
    (normalizerQuotientAut ψ).ker.map (normalizer (G₀ : Set G)).subtype ⊓
      centralizer ({t} : Set G) = ⊥ := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  rw [eq_bot_iff]
  rintro _ ⟨⟨y, hy, rfl⟩, hyt⟩
  have hyN : (y : G) ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht hyt
  have hyL : (y : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    set l' : G₀ := ⟨l, hLG₀ hl⟩ with hl'
    have h1 := congrArg (fun α : MulAut (projectiveSL n F) => α (ψ (l' : G₀ ⧸ center G₀)))
      (MonoidHom.mem_ker.mp hy)
    simp only [MulAut.one_apply] at h1
    rw [normalizerQuotientAut_apply, ψ.injective.eq_iff, QuotientGroup.eq] at h1
    have hconj : ((G₀.normalizerMonoidHom y l' : G₀) : G) = y * l * (y : G)⁻¹ :=
      F4Pilot.coe_normalizerMonoidHom_mk_apply G₀ y.2 l'
    have hzL : (y * l * (y : G)⁻¹)⁻¹ * l ∈ L :=
      L.mul_mem (L.inv_mem ((mem_normalizer_iff.1 hyN l).1 hl)) hl
    have hzZ : ((⟨(y * l * (y : G)⁻¹)⁻¹ * l, hzL⟩ : L)) ∈ center L := by
      rw [mem_center_iff]
      intro m
      have h2 := mem_center_iff.mp h1 ⟨m, hLG₀ m.2⟩
      apply Subtype.ext
      have h3 := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      simp only [Subgroup.coe_mul]
      rw [hconj] at h3
      exact h3
    rw [hZL, mem_bot] at hzZ
    have h4 : (y * l * (y : G)⁻¹)⁻¹ * l = 1 := congrArg Subtype.val hzZ
    have h5 : y * l * (y : G)⁻¹ = l := inv_mul_eq_one.mp h4
    calc l * y = y * l * (y : G)⁻¹ * y := by rw [h5]
      _ = y * l := by group
  have hyz : (y : G) ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hyL, hyt⟩
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hyz with h | h
  · exact h
  · exfalso
    apply htρ
    have hy' : y = ⟨t, htG₀⟩ := Subtype.ext h
    rw [← hy']
    exact hy

theorem odd_card_ker_normalizerQuotientAut (hL : CFSG.Open.standardComponentIsStandard L)
    (hZL : center L = ⊥) (hLG₀ : L ≤ G₀) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (htρ : normalizerQuotientAut ψ ⟨t, htG₀⟩ ≠ 1) :
    Odd (Nat.card (normalizerQuotientAut ψ).ker) := by
  set N := normalizer (G₀ : Set G)
  set H := (normalizerQuotientAut ψ).ker.map N.subtype with hH
  have htH : t ∈ normalizer (H : Set G) := by
    have hle := Subgroup.le_normalizer_map (H := (normalizerQuotientAut ψ).ker) N.subtype
    rw [normalizer_eq_top_iff.2 (MonoidHom.normal_ker _), ← MonoidHom.range_eq_map,
      range_subtype] at hle
    exact hle htG₀
  have h := odd_card_of_inf_centralizer_eq_bot (H := H)
    (by rw [← sq, ← ht, pow_orderOf_eq_one]) htH
    (ker_normalizerQuotientAut_inf_centralizer_eq_bot hL hZL hLG₀ ht hKt ψ htG₀ htρ)
  rwa [hH, card_map_of_injective N.subtype_injective] at h

end Kernel

section Quotient

variable {N B : Type*} [Group N] [Group B]

theorem orderOf_mk_and_card_of_eq_ker (Φ : N →* B) (H : Subgroup N) [H.Normal]
    (hH : H = Φ.ker) :
    (∀ x : N, orderOf (QuotientGroup.mk' H x) = orderOf (Φ x)) ∧
      Nat.card (N ⧸ H) = Nat.card Φ.range := by
  subst hH
  refine ⟨fun x => ?_, Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv⟩
  rw [← orderOf_injective (QuotientGroup.kerLift Φ) (QuotientGroup.kerLift_injective Φ),
    QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk]

end Quotient

section Endgame

variable {G : Type} [Group G] [Finite G] {L G₀ : Subgroup G} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem exists_normal_index_two_of_globalField (hL : CFSG.Open.standardComponentIsStandard L)
    (hZL : center L = ⊥) (hn : 3 ≤ n) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      fieldAut n F σ (ψ (x : G₀ ⧸ center G₀)))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (G₀ : Set G) with hN
  set ρ := normalizerQuotientAut ψ with hρ
  set t₀ : N := ⟨t, htG₀⟩ with ht₀
  have hρt : ρ t₀ = fieldAut n F σ := normalizerQuotientAut_eq_fieldAut ψ htG₀ hψt
  have hfσ1 : fieldAut n F σ ≠ 1 := by
    intro h
    have h' := congrArg (linearFieldPart F hn) h
    rw [linearFieldPart_fieldAut, map_one] at h'
    exact hσ1 h'
  have hker : Odd (Nat.card ρ.ker) :=
    odd_card_ker_normalizerQuotientAut hL hZL hLG₀ ht hKt ψ htG₀ (hρt ▸ hfσ1)
  set Φ := (linearFieldPart F hn).comp ρ with hΦ
  have hΦt : Φ t₀ = σ := by rw [hΦ, MonoidHom.comp_apply, hρt, linearFieldPart_fieldAut]
  set R := Φ.ker.map N.subtype with hR
  have hRN : R.subgroupOf N = Φ.ker := by
    rw [hR, subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hRn : (R.subgroupOf N).Normal := hRN ▸ MonoidHom.normal_ker Φ
  obtain ⟨horder, hcardQ⟩ := orderOf_mk_and_card_of_eq_ker Φ (R.subgroupOf N) hRN
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hσP : σ ∈ Φ.range := ⟨t₀, hΦt⟩
  set c := (Nat.card Φ.range).factorization 2 with hc
  have h2P : 2 ∣ Nat.card Φ.range := by
    have h := orderOf_dvd_natCard (⟨σ, hσP⟩ : Φ.range)
    rwa [Subgroup.orderOf_mk, hσo] at h
  have hc1 : 1 ≤ c := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2P
  have hQ : ¬ 2 ^ (c + 1) ∣ Nat.card (N ⧸ R.subgroupOf N) := by
    rw [hcardQ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two
  suffices hx : ∃ x : N, orderOf x = 2 ^ c ∧ orderOf (Φ x) = 2 ^ c ∧
      IsConj t ((x : G) ^ 2 ^ (c - 1)) by
    obtain ⟨x, hxo, hxΦ, hpow⟩ := hx
    exact F4Pilot.exists_normal_index_two_of_unique_of_quotient huniq x.2 hc1
      (by rw [Subgroup.orderOf_coe]; exact hxo) (by rw [Subtype.coe_eta, horder]; exact hxΦ) hQ
      hpow
  rcases (show c = 1 ∨ 2 ≤ c by omega) with hc1' | hc2
  ·
    refine ⟨t₀, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk, ht, hc1', pow_one]
    · rw [hΦt, hσo, hc1', pow_one]
    · rw [hc1', Nat.sub_self, pow_zero, pow_one]
  ·
    have ht₀2 : IsPGroup 2 (zpowers t₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
    obtain ⟨T, hT⟩ := ht₀2.exists_le_sylow
    have ht₀T : t₀ ∈ T := hT (mem_zpowers t₀)
    have hfs : Function.Surjective Φ.rangeRestrict := Φ.rangeRestrict_surjective
    set TP := T.mapSurjective hfs with hTP
    have hTPcard : Nat.card TP = 2 ^ c := Sylow.card_eq_multiplicity TP
    have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv
    obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (TP : Subgroup Φ.range))
    have hzT : (z : Φ.range) ∈ (T : Subgroup N).map Φ.rangeRestrict := z.2
    obtain ⟨y, hyT, hyz⟩ := hzT
    have hyo : orderOf (Φ y) = 2 ^ c := by
      have h1 : orderOf (Φ.rangeRestrict y) = orderOf (Φ y) := by
        rw [← Subgroup.orderOf_coe, MonoidHom.coe_rangeRestrict]
      rw [← h1, hyz, Subgroup.orderOf_coe, hz, hTPcard]
    set W := (T : Subgroup N).map ρ with hW
    have hWp : IsPGroup 2 W := T.isPGroup'.map ρ
    have hW𝒜 : W ≤ ρ.range := map_le_range ρ _
    have hσW : fieldAut n F σ ∈ W := ⟨t₀, ht₀T, hρt⟩
    have hwW : ρ y ∈ W := ⟨y, hyT, rfl⟩
    have hwo : orderOf (linearFieldPart F hn (ρ y)) = 2 ^ c := hyo
    obtain ⟨ξ, hξA, hξo, hξfc, u, hξu⟩ := exists_exact_lift hn hσ1 hσσ
      (range_conj_le_range_normalizerQuotientAut ψ) hW𝒜 hWp hσW hwW hc2 hwo
    obtain ⟨x, hxρ, hxo⟩ := exists_orderOf_eq_of_odd_ker ρ hker hξA hξo
    refine ⟨x, hxo, ?_, ?_⟩
    · rw [hΦ, MonoidHom.comp_apply, hxρ, hξfc]
      exact hwo
    ·
      obtain ⟨q, hq⟩ := ψ.surjective u
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
      set gN : N := ⟨g₀, le_normalizer g₀.2⟩ with hgN
      have hρg : ρ gN = MulAut.conj u := by
        rw [hρ, hgN, normalizerQuotientAut_of_mem ψ g₀.2, ← hq]
      set y₁ : N := gN⁻¹ * x ^ 2 ^ (c - 1) * gN with hy₁
      have hρy₁ : ρ y₁ = ρ t₀ := by
        rw [hy₁, map_mul, map_mul, map_inv, map_pow, hxρ, hξu, hρg, hρt]
        group
      set k : N := t₀⁻¹ * y₁ with hk
      have hkker : k ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hρy₁, inv_mul_cancel]
      have hkodd : Odd (orderOf k) := by
        have h1 : orderOf (⟨k, hkker⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hker h1
      have ht₀2' : t₀ * t₀ = 1 := Subtype.ext (by
        change t * t = 1
        rw [← sq, ← ht, pow_orderOf_eq_one])
      have hy₁2 : y₁ * y₁ = 1 := by
        have hpow2 : (x ^ 2 ^ (c - 1)) * (x ^ 2 ^ (c - 1)) = 1 := by
          rw [← pow_add, ← two_mul, ← pow_succ', show c - 1 + 1 = c by omega, ← hxo,
            pow_orderOf_eq_one]
        calc y₁ * y₁ = gN⁻¹ * ((x ^ 2 ^ (c - 1)) * (x ^ 2 ^ (c - 1))) * gN := by
              rw [hy₁]; group
          _ = 1 := by rw [hpow2, mul_one, inv_mul_cancel]
      have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2'
      have hky : t₀ * k = y₁ := by rw [hk, ← mul_assoc, mul_inv_cancel, one_mul]
      have hkinv : t₀ * k * t₀⁻¹ = k⁻¹ := by
        have h1 : t₀ * k * (t₀ * k) = 1 := by rw [hky, hy₁2]
        rw [ht₀inv]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [mul_assoc (t₀ * k) t₀ k]
        exact h1
      obtain ⟨d, hd⟩ := exists_conj_eq_mul_of_odd ht₀2' hkinv hkodd
      refine isConj_iff.2 ⟨((gN * d⁻¹ : N) : G), ?_⟩
      have h2 : (gN * d⁻¹) * t₀ * (gN * d⁻¹)⁻¹ = x ^ 2 ^ (c - 1) := by
        calc (gN * d⁻¹) * t₀ * (gN * d⁻¹)⁻¹ = gN * (d⁻¹ * t₀ * d) * gN⁻¹ := by group
          _ = gN * y₁ * gN⁻¹ := by rw [hd, hky]
          _ = x ^ 2 ^ (c - 1) := by rw [hy₁]; group
      have h3 := congrArg Subtype.val h2
      simpa using h3

theorem false_of_simple_globalField [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hL : CFSG.Open.standardComponentIsStandard L) (hZL : center L = ⊥) (hn : 3 ≤ n)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      fieldAut n F σ (ψ (x : G₀ ⧸ center G₀)))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False :=
  CFSG.SeitzReduction.RankOne.Endings.not_exists_normal_index_two hnonab
    (exists_normal_index_two_of_globalField hL hZL hn hσ1 hσσ ht hKt hLG₀ htG₀ ψ hψt huniq)

end Endgame

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_globalField (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L))
    {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K] [Field F] [Finite F] [CharP F 2]
    (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (e : L ≃* projectiveSL (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : FieldCoreTypeDet (m + 1) K F) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)) (hq : CFSG.IsQuasisimple G₀)
    (ψ : G₀ ⧸ center G₀ ≃* projectiveSL (m + 1) F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀))) :
    False := by
  have := hset.simple
  have hZL : center L = ⊥ := by
    rw [← map_center_eq e.symm, CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (by omega), Subgroup.map_bot]
  exact false_of_simple_globalField hset.nonab hset.standard hZL (by omega) hσ1 hσσ ht hKt hLG₀
    htG₀ ψ hψt (unique_of_fieldCoreTypeDet hset hOut hm ι hσ1 hσσ hfix e ht hKt hTD hG₀ hq ψ)

end FieldRow

end CFSG.SeitzReduction.LinearPilot
