module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem two_le_unitary_e {n : ℕ} (hn : 2 ≤ n) : 2 ≤ (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  have hg : 0 < Nat.gcd 3 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hg]
  have hg3 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have : n = 2 := by omega
    subst this
    decide
  · have : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega

theorem commutator_fixCartan_eq_unitary {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t₀ : K}
    (hc : BenderCore (2 ^ n) 3 e (Q : Subgroup K) t₀) :
    ⁅(Q : Subgroup K), fixCartan (Q : Subgroup K) t₀⁆ = Q := by
  classical
  set P : Subgroup K := (Q : Subgroup K) with hPdef
  set K₀ := fixCartan P t₀ with hK₀
  set W := ⁅P, K₀⁆ with hW
  set Z := rootCenter P with hZ
  have hK₀B : K₀ ≤ borel P := (fixCartan_le_cartan P t₀).trans (cartan_le_borel P t₀)
  have hWP : W ≤ P := by
    rw [hW, commutator_le]
    intro x hx d hd
    rw [commutatorElement_def]
    have h1 : d * x⁻¹ * d⁻¹ ∈ P := (mem_normalizer_iff.mp (hK₀B hd) _).mp (inv_mem hx)
    have := mul_mem hx h1
    simpa [mul_assoc] using this
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ d ∈ K₀, d ≠ 1 := by
    rcases h.cases' with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨-, he, hn⟩
    · exact absurd hi (by norm_num)
    · exact absurd hi (by norm_num)
    · have hcard : Nat.card K₀ = e := hc.card_fixCartan
      have h2 : 2 ≤ e := he ▸ two_le_unitary_e hn
      by_contra hne
      push Not at hne
      have : K₀ = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hne x hx)
      rw [this, card_bot] at hcard
      omega
  have hD : ∀ c ∈ cartan P t₀, ∀ w ∈ W ⊔ Z, c * w * c⁻¹ ∈ W ⊔ Z := by
    intro c hc' w hw
    have hcN : c ∈ normalizer (P : Set K) := cartan_le_borel P t₀ hc'
    have hPc : P.map (MulAut.conj c).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp hcN
    have hKc : K₀.map (MulAut.conj c).toMonoidHom = K₀ := by
      apply le_antisymm
      · rintro _ ⟨k, hk, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hc.cartan_comm hc' (fixCartan_le_cartan P t₀ hk), mul_inv_cancel_right]
        exact hk
      · intro k hk
        refine ⟨k, hk, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hc.cartan_comm hc' (fixCartan_le_cartan P t₀ hk), mul_inv_cancel_right]
    have hZc : Z.map (MulAut.conj c).toMonoidHom ≤ Z := by
      rintro _ ⟨z, hz, rfl⟩
      exact conj_mem_rootCenter hcN hz
    have hWc : W.map (MulAut.conj c).toMonoidHom = W := by rw [hW, map_commutator, hPc, hKc]
    have hle : (W ⊔ Z).map (MulAut.conj c).toMonoidHom ≤ W ⊔ Z := by
      rw [Subgroup.map_sup, hWc]
      exact sup_le_sup_left hZc W
    exact hle ⟨w, hw, rfl⟩
  have hZP : Z ≤ P := rootCenter_le P
  rcases h.irreducible_unitary Q hc.sq_eq_one hc.not_mem (W ⊔ Z) le_sup_right
      (sup_le hWP hZP) hD with h1 | h1
  ·
    exfalso
    have h1' : W ⊔ Z = Z := h1
    have hWZ : W ≤ Z := by rw [← h1']; exact le_sup_left
    have hPZ : P ≤ Z := by
      intro x hx
      refine h.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem
        (fixCartan_le_cartan P t₀ hd₀) hd₀1 hx ?_
      have h2 : ⁅x, d₀⁆ ∈ W := commutator_mem_commutator hx hd₀
      have h3 := inv_mem (hWZ h2)
      rw [commutatorElement_def] at h3
      simpa [mul_assoc] using h3
    have hcard := card_le_of_le hPZ
    rw [hc.card_eq, hc.card_center] at hcard
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le.2
    have h5 : (2 ^ n) ^ 1 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    rw [pow_one] at h5
    omega
  ·
    have h1' : W ⊔ Z = P := h1
    have hZc : ∀ z ∈ Z, ∀ y ∈ P, z * y = y * z := fun z hz y hy =>
      ((mem_rootCenter_iff.mp hz).2 y hy).symm
    have hZN : Z ≤ normalizer (W : Set K) := fun z hz => mem_normalizer_iff.mpr fun y => by
      constructor
      · intro hy
        rw [hZc z hz y (hWP hy), mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyP : z * y * z⁻¹ ∈ P := hWP hy
        have hyP' : y ∈ P := by
          have := mul_mem (mul_mem (inv_mem (hZP hz)) hyP) (hZP hz)
          simpa [mul_assoc] using this
        rwa [hZc z hz y hyP', mul_inv_cancel_right] at hy
    have hcomm : ⁅P, P⁆ ≤ W := by
      rw [commutator_le]
      intro a ha b hb
      have ha' : a ∈ ((W ⊔ Z : Subgroup K) : Set K) := by rw [h1']; exact ha
      have hb' : b ∈ ((W ⊔ Z : Subgroup K) : Set K) := by rw [h1']; exact hb
      rw [coe_mul_of_right_le_normalizer_left W Z hZN] at ha' hb'
      obtain ⟨w, hw, z, hz, rfl⟩ := ha'
      obtain ⟨w', hw', z', hz', rfl⟩ := hb'
      have e1 : z * w' = w' * z := hZc z hz w' (hWP hw')
      have e2 : z' * w = w * z' := hZc z' hz' w (hWP hw)
      have e3 : z * z' = z' * z := hZc z hz z' (hZP hz')
      have e4 : ⁅w * z, w' * z'⁆ = ⁅w, w'⁆ := by
        simp only [commutatorElement_def, mul_inv_rev]
        calc w * z * (w' * z') * (z⁻¹ * w⁻¹) * (z'⁻¹ * w'⁻¹) =
            w * (z * w') * z' * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by group
          _ = w * w' * (z * z') * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by rw [e1]; group
          _ = w * w' * (z' * z) * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by rw [e3]
          _ = w * w' * (z' * w⁻¹) * z'⁻¹ * w'⁻¹ := by group
          _ = w * w' * (w⁻¹ * z') * z'⁻¹ * w'⁻¹ := by
              rw [show z' * w⁻¹ = w⁻¹ * z' by
                rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e2, mul_assoc, mul_inv_cancel, mul_one]]
          _ = w * w' * w⁻¹ * w'⁻¹ := by group
      rw [e4, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hw hw') (inv_mem hw)) (inv_mem hw')
    have hZW : Z ≤ W := by
      have := (h.lemma_3_5_a_unitary Q).1
      rw [← hPdef] at this
      rw [hZ, ← this]
      exact hcomm
    rw [← h1', sup_eq_left.mpr hZW]

end Bender

theorem exists_odd_le_commutator_outer_unitary {K : Type*} [Group K] {n e : ℕ}
    (h : BenderType K n 3 e) :
    ∃ Dd : Subgroup (Outer K), Odd (Nat.card Dd) ∧ commutator (Outer K) ≤ Dd := by
  obtain ⟨Dd, hDn, -, hd, hqcyc, -⟩ := h.outer_unitary
  refine ⟨Dd, ?_, ?_⟩
  · rw [hd]
    exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {A : Subgroup G} {n y : G}
    (hn : n ∈ normalizer (A : Set G)) (hy : y ∈ centralizer (A : Set G)) :
    n * y * n⁻¹ ∈ centralizer (A : Set G) := by
  refine mem_centralizer_iff.mpr fun a ha => ?_
  have ha' : n⁻¹ * a * n ∈ A := (mem_normalizer_iff''.mp hn a).mp ha
  have e := mem_centralizer_iff.mp hy _ ha'
  calc a * (n * y * n⁻¹) = n * ((n⁻¹ * a * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * a * n)) * n⁻¹ := by rw [e]
    _ = n * y * n⁻¹ * a := by group

theorem normalizer_szA_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (szA L T t : Set G) ≤ normalizer (szT₁ L T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := h.setting.standardSetting
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      h.mem h.inv).1
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv (hst.core t h.inv)
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨Dd, hDodd, hDcomm⟩ := exists_odd_le_commutator_outer_unitary hB
  have hT₁Q : (Q : Subgroup L).map L.subtype = szT₁ L T :=
    map_subtype_eq_of_mem_iff (szT₁_le_right L T) hmemQ
  set K₀ := (fixCartan (Q : Subgroup L) t₀).map L.subtype with hK₀
  have hK₀L : K₀ ≤ L := by
    rintro _ ⟨d, -, rfl⟩
    exact d.2
  have hT₁eq : ⁅szT₁ L T, K₀⁆ = szT₁ L T := by
    rw [← hT₁Q, hK₀, ← map_commutator, commutator_fixCartan_eq_unitary hB Q hc]
  have htC : t ∈ centralizer (L : Set G) := h.mem
  have hAT₁ : szA L T t ≤ centralizer (szT₁ L T : Set G) :=
    sup_le inf_le_right (zpowers_le.mpr h.mem_centralizer_szT₁)
  have hAK₀ : szA L T t ≤ centralizer (K₀ : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_iff.mpr ?_)
      (zpowers_le.mpr (centralizer_le hK₀L htC))
    rintro _ ⟨d, hd, rfl⟩
    have haL : a ∈ L := szT₁_le_right L T (szA₁_le _ ha)
    have hdC : d ∈ centralizer (rootCenter (Q : Subgroup L) : Set L) := by
      rw [hc.centralizer_rootCenter_eq]
      exact mem_sup_right hd
    exact (congrArg Subtype.val
      (mem_centralizer_iff.mp hdC ⟨a, haL⟩ ((hmemZ ⟨a, haL⟩).mpr ha))).symm
  have hT₁A : szT₁ L T ≤ centralizer (szA L T t : Set G) := le_centralizer_iff.mp hAT₁
  have hK₀A : K₀ ≤ centralizer (szA L T t : Set G) := le_centralizer_iff.mp hAK₀
  have hCAt : centralizer (szA L T t : Set G) ≤ centralizer ({t} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr (mem_szA_right L T t))
  set C := centralizer ({t} : Set G) with hC
  set ψ : C →* Outer L := (QuotientGroup.mk' (inner L)).comp
    (L.normalizerMonoidHom.comp (inclusion hHN)) with hψ
  have hinner : ∀ c : C, ψ c = 1 → (c : G) ∈ L ⊔ zpowers t := by
    intro c hψc
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hψc
    obtain ⟨g, hg⟩ := hψc
    have hgm : ∀ y ∈ L, (c : G) * y * (c : G)⁻¹ = (g : G) * y * (g : G)⁻¹ := by
      intro y hy
      have := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hg
      simp only [MulAut.conj_apply, coe_mul, coe_inv, MonoidHom.comp_apply,
        normalizerMonoidHom_apply_apply_coe, coe_inclusion] at this
      exact this.symm
    have hgt : (g : G) ∈ C := mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.mem g g.2)
    have hk : (g : G)⁻¹ * c ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, mul_mem (inv_mem hgt) c.2⟩
      calc y * ((g : G)⁻¹ * c) = (g : G)⁻¹ * (g * y * (g : G)⁻¹) * c := by group
        _ = (g : G)⁻¹ * (c * y * (c : G)⁻¹) * c := by rw [hgm y hy]
        _ = (g : G)⁻¹ * c * y := by group
    have e1 : (c : G) = g * ((g : G)⁻¹ * c) := by group
    rw [e1]
    exact mul_mem (mem_sup_left g.2) (mem_sup_right hk)
  have key : ∀ n ∈ normalizer (szA L T t : Set G), ∀ x ∈ szT₁ L T,
      n * x * n⁻¹ ∈ szT₁ L T := by
    intro n hn
    set P := (szT₁ L T).map (MulAut.conj n).toMonoidHom with hP
    set K' := K₀.map (MulAut.conj n).toMonoidHom with hK'
    have hPA : P ≤ centralizer (szA L T t : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_centralizer_of_mem_normalizer hn (hT₁A hy)
    have hK'A : K' ≤ centralizer (szA L T t : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_centralizer_of_mem_normalizer hn (hK₀A hy)
    have hPC : P ≤ C := hPA.trans hCAt
    have hK'C : K' ≤ C := hK'A.trans hCAt
    have hPeq : ⁅P, K'⁆ = P := by rw [hP, hK', ← map_commutator, hT₁eq]
    set P' := P.subgroupOf C with hP'
    set K'' := K'.subgroupOf C with hK''
    have hPP' : P'.map C.subtype = P := by rw [hP', subgroupOf_map_subtype, inf_of_le_left hPC]
    have hKK'' : K''.map C.subtype = K' := by
      rw [hK'', subgroupOf_map_subtype, inf_of_le_left hK'C]
    have hP'eq : ⁅P', K''⁆ = P' := by
      apply map_injective C.subtype_injective
      rw [map_commutator, hPP', hKK'', hPeq]
    have hψP : P'.map ψ ≤ Dd := by
      rw [← hP'eq, map_commutator]
      exact (commutator_mono le_top le_top).trans hDcomm
    have hPp : IsPGroup 2 P' := by
      have h1 : IsPGroup 2 P := by
        have := (h.isPGroup.to_le (szT₁_le_left L T)).map (MulAut.conj n).toMonoidHom
        exact this
      exact h1.comap_subtype
    have hψP2 : IsPGroup 2 (P'.map ψ) := hPp.map ψ
    have hψbot : P'.map ψ = ⊥ := by
      obtain ⟨k, hk⟩ := hψP2.exists_card_eq
      have hdvd : Nat.card (P'.map ψ) ∣ Nat.card Dd := card_dvd_of_le hψP
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ Nat.card Dd :=
          dvd_trans (dvd_pow_self 2 hk0) hdvd
        exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h2)
      rw [hk0, pow_zero] at hk
      exact card_eq_one.mp hk
    have hPLt : P ≤ L ⊔ zpowers t := by
      intro p hp
      have hpP' : (⟨p, hPC hp⟩ : C) ∈ P' := by rw [hP', mem_subgroupOf]; exact hp
      have h1 : ψ ⟨p, hPC hp⟩ ∈ P'.map ψ := ⟨_, hpP', rfl⟩
      rw [hψbot, mem_bot] at h1
      exact hinner _ h1
    have hPL : P ≤ L := by
      rw [← hPeq, commutator_le]
      intro p hp k hk
      obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers htC (hPLt hp)
      have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (hK'C hk)
      have hzk : k * z = z * k := commute_of_mem_zpowers hz hkt
      have hkN : k ∈ normalizer (L : Set G) := hHN (hK'C hk)
      have e1 : ⁅l * z, k⁆ = l * (k * l⁻¹ * k⁻¹) := by
        rw [commutatorElement_def]
        calc l * z * k * (l * z)⁻¹ * k⁻¹ = l * (z * k) * z⁻¹ * l⁻¹ * k⁻¹ := by group
          _ = l * (k * l⁻¹ * k⁻¹) := by rw [← hzk]; group
      rw [e1]
      exact mul_mem hl ((mem_normalizer_iff.mp hkN _).mp (inv_mem hl))
    intro x hx
    have hxP : n * x * n⁻¹ ∈ P := ⟨x, hx, rfl⟩
    have hxL : n * x * n⁻¹ ∈ L := hPL hxP
    set PL := P.subgroupOf L with hPL'
    have hPLp : IsPGroup 2 PL := by
      have h1 : IsPGroup 2 P :=
        (h.isPGroup.to_le (szT₁_le_left L T)).map (MulAut.conj n).toMonoidHom
      exact h1.comap_subtype
    have hPLN : PL ≤ normalizer (Q : Set L) := by
      intro y hy
      rw [hPL', mem_subgroupOf] at hy
      have hyC : y ∈ centralizer (rootCenter (Q : Subgroup L) : Set L) := by
        refine mem_centralizer_iff.mpr fun z hz => Subtype.ext ?_
        have hzA : (z : G) ∈ szA L T t := szA₁_le_szA L T t ((hmemZ z).mp hz)
        exact (mem_centralizer_iff.mp (hPA hy) _ hzA)
      rw [hc.centralizer_rootCenter_eq] at hyC
      exact sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _)) hyC
    have hx1 : (⟨n * x * n⁻¹, hxL⟩ : L) ∈ PL := by rw [hPL', mem_subgroupOf]; exact hxP
    have hmem : (⟨n * x * n⁻¹, hxL⟩ : L) ∈ PL ⊓ normalizer (Q : Set L) :=
      mem_inf.mpr ⟨hx1, hPLN hx1⟩
    rw [hPLp.inf_normalizer_sylow Q] at hmem
    exact (hmemQ _).mp (mem_inf.mp hmem).2
  intro n hn
  have h1 : n⁻¹ ∈ normalizer (szT₁ L T : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => by
      simpa using key n hn x hx
  simpa using inv_mem h1

theorem normalizer_szA_le_normalizer_szA₁_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (szA L T t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) :=
  (h.normalizer_szA_le_of_card_sylow hS2).trans
    (normalizer_le_normalizer_inf_centralizer (szT₁ L T))

end U3Start

end CFSG.SeitzReduction.RankOne
