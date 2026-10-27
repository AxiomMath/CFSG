module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WCfg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Fac
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartOne
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Aux

variable {T : Type} [Group T] [Finite T]

private theorem w_isSylowOf {V P : Subgroup T} (h : IsSylow2In V P) :
    CFSG.ABGLocalTools.IsSylowOf 2 V P :=
  ⟨AscQuot.sylowOfIsSylow2In' h, by
    show (V.subgroupOf P).map P.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.1]⟩

private theorem w_conj_eq_inv {G : Type*} [Group G]
    (hnc : ∀ k d : G, orderOf k = 4 → orderOf d = 3 → k * d ≠ d * k) {d w : G}
    (hd : orderOf d = 3) (hw : orderOf w = 4) (hwd : w * d * w⁻¹ ∈ Subgroup.zpowers d) :
    w * d * w⁻¹ = d⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwd
  rw [← zpow_mod_orderOf, hd] at hk
  have hd3 : d ^ 3 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h | h | h <;> rw [h] at hk
  · exfalso
    rw [zpow_zero] at hk
    have hd1 : d = 1 := by
      calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
        _ = 1 := by rw [← hk]; group
    rw [hd1, orderOf_one] at hd
    norm_num at hd
  · exfalso
    rw [zpow_one] at hk
    refine hnc w d hw hd ?_
    calc w * d = (w * d * w⁻¹) * w := by group
      _ = d * w := by rw [← hk]
  · rw [← hk, zpow_two, eq_inv_iff_mul_eq_one, ← pow_three', hd3]

private theorem w_eq_bot {G : Type*} [Group G]
    (hnc : ∀ k d : G, orderOf k = 4 → orderOf d = 3 → k * d ≠ d * k) {D : Subgroup G}
    (hD : Nat.card D ∣ 3) {α β : G} (hα : orderOf α = 4) (hβ : orderOf β = 4)
    (hαβ : orderOf (α * β) = 4) (hDα : ∀ d ∈ D, α * d * α⁻¹ ∈ D)
    (hDβ : ∀ d ∈ D, β * d * β⁻¹ ∈ D) : D = ⊥ := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hD with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have : Finite D := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := D)).mp (by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h3
      omega)
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hd3 : orderOf d = 3 := by
      have hdvd : orderOf d ∣ 3 := h3 ▸ Subgroup.orderOf_dvd_natCard D hdD
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hd1'
      · exact h
    have hDz : Subgroup.zpowers d = D :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD)
        (by rw [Nat.card_zpowers, hd3, h3])
    have hαd : α * d * α⁻¹ = d⁻¹ :=
      w_conj_eq_inv hnc hd3 hα (by rw [hDz]; exact hDα d hdD)
    have hβd : β * d * β⁻¹ = d⁻¹ :=
      w_conj_eq_inv hnc hd3 hβ (by rw [hDz]; exact hDβ d hdD)
    apply hnc (α * β) d hαβ hd3
    calc α * β * d = α * (β * d * β⁻¹) * α⁻¹ * (α * β) := by group
      _ = (α * d * α⁻¹)⁻¹ * (α * β) := by rw [hβd]; group
      _ = d * (α * β) := by rw [hαd, inv_inv]

private theorem w_exists_four {K : Subgroup T} {z : T} (hd : FrameTightDatum K z) {g : T}
    {L : Subgroup T} (hg : conjSub g K = L) :
    ∃ a b : T, a ∈ L ∧ b ∈ L ∧ orderOf a = 4 ∧ orderOf b = 4 ∧ orderOf (a * b) = 4 := by
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨e⟩ := hd.quat R₀ hR₀
  have hmem : ∀ c : ↥R₀, g * (c : T) * g⁻¹ ∈ L := fun c => hg ▸ conj_mem_conjSub (hR₀.1 c.2)
  have hord : ∀ c : ↥R₀, orderOf (g * (c : T) * g⁻¹) = orderOf c := by
    intro c
    have e1 : g * (c : T) * g⁻¹ = MulAut.conj g (c : T) := by rw [MulAut.conj_apply]
    rw [e1, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  refine ⟨g * (e.symm (QuaternionGroup.a 1) : T) * g⁻¹,
    g * (e.symm (QuaternionGroup.xa 0) : T) * g⁻¹, hmem _, hmem _, ?_, ?_, ?_⟩
  · rw [hord, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  · rw [hord, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
  · have e2 : g * (e.symm (QuaternionGroup.a 1) : T) * g⁻¹ *
        (g * (e.symm (QuaternionGroup.xa 0) : T) * g⁻¹) =
        g * ((e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) : ↥R₀) : T) * g⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rw [e2, hord, ← map_mul, MulEquiv.orderOf_eq, QuaternionGroup.a_mul_xa,
      QuaternionGroup.orderOf_xa]

end Aux

namespace WCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem oddCoreOf_le_of_mem_aStar (cfg : WCfg K z J zJ H S) {L : Subgroup T}
    (hL : L ∈ aStar (CoreAssembly.conjClass K) K) : oddCoreOf L ≤ oddCoreOf (sigmaGen K) := by
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hLHt : L ≤ firstFactor K := (le_omegaGen hL).trans le_sup_left
  obtain ⟨g, hg⟩ := (mem_aStar_symm hKΩ hL).1
  have hg' : conjSub g K = L := hg
  obtain ⟨a, b, haL, hbL, ha4, hb4, hab4⟩ := w_exists_four cfg.datum hg'
  have hOHt : oddCoreOf L ≤ firstFactor K := (oddCoreOf_le_self L).trans hLHt
  have haHt : a ∈ firstFactor K := hLHt haL
  have hbHt : b ∈ firstFactor K := hLHt hbL
  have habHt : a * b ∈ firstFactor K := (firstFactor K).mul_mem haHt hbHt
  obtain ⟨e⟩ := cfg.ht
  let ρ : ↥(firstFactor K) →* G192 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K)))
  let ψ : ↥(oddCoreOf L) →* G192 := ρ.comp (Subgroup.inclusion hOHt)
  have hρ4 : ∀ (c : T) (hc : c ∈ firstFactor K), orderOf c = 4 → orderOf (ρ ⟨c, hc⟩) = 4 := by
    intro c hc hc4
    show orderOf (e ((⟨c, hc⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))) = 4
    rw [MulEquiv.orderOf_eq]
    exact orderOf_mk_eq_four hc hc4
  have hα4 : orderOf (ρ ⟨a, haHt⟩) = 4 := hρ4 a haHt ha4
  have hβ4 : orderOf (ρ ⟨b, hbHt⟩) = 4 := hρ4 b hbHt hb4
  have hαβ4 : orderOf (ρ ⟨a, haHt⟩ * ρ ⟨b, hbHt⟩) = 4 := by
    rw [← map_mul]
    exact hρ4 (a * b) habHt hab4
  have hnorm : ∀ (c : T) (hc : c ∈ L), ∀ d ∈ ψ.range,
      ρ ⟨c, hLHt hc⟩ * d * (ρ ⟨c, hLHt hc⟩)⁻¹ ∈ ψ.range := by
    rintro c hc _ ⟨x, rfl⟩
    have hcx : c * (x : T) * c⁻¹ ∈ oddCoreOf L :=
      Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hc) x.2
    refine ⟨⟨_, hcx⟩, ?_⟩
    have e1 : (Subgroup.inclusion hOHt ⟨_, hcx⟩ : ↥(firstFactor K)) =
        ⟨c, hLHt hc⟩ * Subgroup.inclusion hOHt x * (⟨c, hLHt hc⟩ : ↥(firstFactor K))⁻¹ :=
      Subtype.ext rfl
    show ρ (Subgroup.inclusion hOHt ⟨_, hcx⟩) = _
    rw [e1, map_mul, map_mul, map_inv]
    rfl
  have hodd : Odd (Nat.card ψ.range) :=
    (oddCoreOf_odd_natCard L).of_dvd_nat (Subgroup.card_range_dvd ψ)
  have h192 : Nat.card ψ.range ∣ 2 ^ 6 * 3 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [W192.w192_card] at h
  have h3 : Nat.card ψ.range ∣ 3 :=
    ((Odd.coprime_two_right hodd).pow_right 6).dvd_of_dvd_mul_left h192
  have hbot : ψ.range = ⊥ :=
    w_eq_bot (fun k d hk hd => W192.w192_not_commute_four_three k d hk hd) h3 hα4 hβ4 hαβ4
      (hnorm a haL) (hnorm b hbL)
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    have h0 : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hbot] at h0
    exact (Subgroup.mem_bot).mp h0
  have h1' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))
      (Subgroup.inclusion hOHt ⟨x, hx⟩) = 1 := by
    apply e.injective
    rw [map_one]
    exact h1
  have h2 : Subgroup.inclusion hOHt ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥(firstFactor K) :=
    (QuotientGroup.eq_one_iff _).mp h1'
  rw [← cfg.toFrameCfg.oddCoreOf_firstFactor]
  exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩

theorem factor_comm (cfg : WCfg K z J zJ H S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K))
    {x y : T} (hx : x ∈ conjSub m₁ (firstFactor K)) (hy : y ∈ conjSub m₂ (firstFactor K)) :
    x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (sigmaGen K) :=
  cfg.toFrameCfg.factor_comm_of (fun _ hL => cfg.oddCoreOf_le_of_mem_aStar hL) hm₁ hm₂ hne hx hy

theorem factor_le_normalizer_Q (cfg : WCfg K z J zJ H S) {g : T} (hg : g ∈ sigmaNorm K)
    (hgN : g ∉ Subgroup.normalizer (firstFactor K : Set T)) :
    rightConjugate (firstFactor K) g ≤ Subgroup.normalizer (wQ K : Set T) := by
  intro e he
  have he' : e ∈ conjSub g⁻¹ (firstFactor K) := he
  have hg' : g⁻¹ ∈ sigmaNorm K := (sigmaNorm K).inv_mem hg
  have hne : conjSub g⁻¹ (firstFactor K) ≠ conjSub 1 (firstFactor K) := by
    rw [conjSub_one]
    intro h
    apply hgN
    simpa using (Subgroup.normalizer (firstFactor K : Set T)).inv_mem
      (mem_normalizer_iff_conjSub_eq.mpr h)
  have hOle : oddCoreOf (sigmaGen K) ≤ oUpperTwo (firstFactor K) := fun y hy =>
    Subgroup.subset_closure ⟨(le_sup_right : oddCoreOf (sigmaGen K) ≤ firstFactor K) hy,
      (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)⟩
  have hgen : ∀ q ∈ {x | x ∈ oUpperTwo (firstFactor K) ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1},
      e * q * e⁻¹ ∈ wQ K := by
    rintro q ⟨hq, k, hk⟩
    have hqHt : q ∈ conjSub 1 (firstFactor K) := by
      rw [conjSub_one]
      exact oUpperTwo_le _ hq
    have hc : e * q * e⁻¹ * q⁻¹ ∈ oddCoreOf (sigmaGen K) := cfg.factor_comm hg' (one_mem _) hne he' hqHt
    have hO2 : e * q * e⁻¹ ∈ oUpperTwo (firstFactor K) := by
      have := (oUpperTwo (firstFactor K)).mul_mem (hOle hc) hq
      rwa [inv_mul_cancel_right] at this
    exact Subgroup.subset_closure ⟨hO2, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hle : conjSub e (wQ K) ≤ wQ K := by
    show (Subgroup.closure _).map (MulAut.conj e).toMonoidHom ≤ wQ K
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hgen q hq
  have hcard : Nat.card (conjSub e (wQ K)) = Nat.card (wQ K) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (wQ K) (MulAut.conj e).toMonoidHom
      (MulAut.conj e).injective).toEquiv).symm
  exact mem_normalizer_iff_conjSub_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]))

theorem card_T_ge_four (cfg : WCfg K z J zJ H S) {x : T} (hx : x ∉ sigmaNorm K)
    {T₀ : Subgroup T}
    (hT : IsSylow2In T₀ (rightConjugate (wQ K) x ⊓ Subgroup.normalizer (wQ K : Set T)))
    (hT1 : T₀ ≠ ⊥) : 4 ≤ Nat.card T₀ := by
  have hxN : x ∉ Subgroup.normalizer (wQ K : Set T) := fun h =>
    hx (Subgroup.mem_inf.mp (cfg.normalizer_Q_le h)).1
  have htight := cfg.tight
  have hodd : Odd (Nat.card (wQ K ⊓ rightConjugate (wQ K) x : Subgroup T)) := htight.2 x hxN
  have hfac : (Nat.card (wQ K)).factorization 2 =
      (Nat.card (rightConjugate (wQ K) x)).factorization 2 := by
    rw [rightConjugate_card]
  have hT2 : IsPGroup 2 T₀ := hT.2.1
  have hTN : T₀ ≤ Subgroup.normalizer (wQ K : Set T) := hT.1.trans inf_le_right
  obtain ⟨syl, hsyl⟩ :=
    CFSG.ComponentClassification.TwoActionInvariantSylow.subgroup (wQ K) T₀ hT2 hTN
  set R : Subgroup T := (syl : Subgroup (wQ K)).map (wQ K).subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf 2 R (wQ K) := ⟨syl, rfl⟩
  have hcard : Nat.card (R ⊓ Subgroup.normalizer (T₀ : Set T) : Subgroup T) = Nat.card T₀ :=
    CFSG.ComponentClassification.Asc76.Lemma22.card_inf_normalizer htight
      (rightConjugate_tightlyEmbedded (wQ K) htight x) hodd hfac (w_isSylowOf hT) hT1 hR hsyl
  obtain ⟨eR⟩ := cfg.sylow_Q hR
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hT02 : Nat.card T₀ = 2 := by
    have h1 : Nat.card T₀ ≠ 1 := fun h => hT1 (Subgroup.card_eq_one.mp h)
    rcases n with _ | _ | n
    · exact absurd (by rw [hn, pow_zero]) h1
    · rw [hn, pow_one]
    · exfalso
      have : 4 ≤ Nat.card T₀ := by
        rw [hn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : u * u = 1 := by
    have h := Subgroup.orderOf_dvd_natCard T₀ hu
    rw [hT02] at h
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1'
  have hTu : T₀ = Subgroup.zpowers u := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu)
    rw [Nat.card_zpowers, hord, hT02]
  have hCN : R ⊓ Subgroup.centralizer ({u} : Set T) ≤ R ⊓ Subgroup.normalizer (T₀ : Set T) := by
    rintro r ⟨hr, hrc⟩
    refine ⟨hr, ?_⟩
    have hc : Commute u r := (Subgroup.mem_centralizer_singleton_iff.mp hrc).symm
    rw [hTu]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hc.zpow_left k).eq
  have h4 := z4sq_card_fix_ge_four eR hu2 (hsyl hu)
  have h5 := Subgroup.card_le_of_le hCN
  omega

theorem exists_inner_inv (cfg : WCfg K z J zJ H S) {T₀ : Subgroup T} (hT2 : IsPGroup 2 T₀)
    (h4 : 4 ≤ Nat.card T₀) (hTN : T₀ ≤ Subgroup.normalizer (firstFactor K : Set T)) :
    ∃ u ∈ T₀, u ≠ 1 ∧ u * u = 1 ∧ ∃ huN : u ∈ Subgroup.normalizer (firstFactor K : Set T),
      s26Act (firstFactor K) ⟨u, huN⟩ ∈ inner (SecQuot (firstFactor K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : T → Prop := fun u => ∃ huN : u ∈ Subgroup.normalizer (firstFactor K : Set T),
    s26Act (firstFactor K) ⟨u, huN⟩ ∈ inner (SecQuot (firstFactor K)) with hI
  have hρ : ∀ a b : T, ∀ (ha : a ∈ Subgroup.normalizer (firstFactor K : Set T))
      (hb : b ∈ Subgroup.normalizer (firstFactor K : Set T)),
      s26Act (firstFactor K) ⟨a * b, Subgroup.mul_mem _ ha hb⟩ =
        s26Act (firstFactor K) ⟨a, ha⟩ * s26Act (firstFactor K) ⟨b, hb⟩ := fun a b ha hb => by
    rw [← map_mul]
    rfl
  have hmul : ∀ a ∈ T₀, ∀ b ∈ T₀, ¬ I a → ¬ I b → I (a * b) := by
    intro a ha b hb hIa hIb
    refine ⟨Subgroup.mul_mem _ (hTN ha) (hTN hb), ?_⟩
    rw [hρ a b (hTN ha) (hTN hb)]
    exact cfg.mul_mem_inner (fun h => hIa ⟨hTN ha, h⟩) (fun h => hIb ⟨hTN hb, h⟩)
  have hsq : ∀ a ∈ T₀, I (a * a) := by
    intro a ha
    by_cases h : I a
    · obtain ⟨haN, hin⟩ := h
      refine ⟨Subgroup.mul_mem _ haN haN, ?_⟩
      rw [hρ a a haN haN]
      exact Subgroup.mul_mem _ hin hin
    · exact hmul a ha a ha h h
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card T₀ := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  obtain ⟨U₀, hU₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set T₁ : Subgroup T := U₀.map T₀.subtype with hT₁def
  have hT₁ : T₁ ≤ T₀ := Subgroup.map_subtype_le _
  have hT₁4 : Nat.card T₁ = 4 := by
    rw [hT₁def, Subgroup.card_map_of_injective T₀.subtype_injective, hU₀]
    norm_num
  have h4pow : ∀ a ∈ T₁, a ^ 4 = 1 := fun a ha => by
    rw [← hT₁4]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ ha)
  by_cases hcyc : ∃ a ∈ T₁, a * a ≠ 1
  ·
    obtain ⟨a, haT, ha1⟩ := hcyc
    refine ⟨a * a, Subgroup.mul_mem _ (hT₁ haT) (hT₁ haT), ha1, ?_, hsq a (hT₁ haT)⟩
    have h44 : a ^ 4 = a * a * (a * a) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [← h44]
    exact h4pow a haT
  ·
    push Not at hcyc
    obtain ⟨⟨a, haT⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T₁)).mp (by
      intro h
      rw [h, Subgroup.card_bot] at hT₁4
      omega)
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha2 : a * a = 1 := hcyc a haT
    have hzp : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1'
    obtain ⟨b, hbT, hba⟩ : ∃ b ∈ T₁, b ∉ Subgroup.zpowers a := by
      by_contra hall
      push Not at hall
      have := Subgroup.card_le_of_le (show T₁ ≤ Subgroup.zpowers a from hall)
      omega
    have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hba
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
    by_cases hIa : I a
    · exact ⟨a, hT₁ haT, ha1', ha2, hIa⟩
    · by_cases hIb : I b
      · exact ⟨b, hT₁ hbT, hb1, hcyc b hbT, hIb⟩
      · exact ⟨a * b, Subgroup.mul_mem _ (hT₁ haT) (hT₁ hbT), hab1,
          hcyc _ (Subgroup.mul_mem _ haT hbT), hmul a (hT₁ haT) b (hT₁ hbT) hIa hIb⟩

theorem cent_of_inner (cfg : WCfg K z J zJ H S) {u : T} (hu2 : u * u = 1)
    (huN : u ∈ Subgroup.normalizer (firstFactor K : Set T))
    (hin : s26Act (firstFactor K) ⟨u, huN⟩ ∈ inner (SecQuot (firstFactor K))) :
    ∃ M' ∈ sigmaOf K, ∃ X' ∈ USet (CoreAssembly.conjClass K), X' ≤ M' ∧
      X' ≤ Subgroup.centralizer ({u} : Set T) := by
  obtain ⟨y, hy⟩ := hin
  have hyy : y * y = 1 := by
    have h1 : MulAut.conj (y * y) = 1 := by
      have hu1 : (⟨u, huN⟩ : ↥(Subgroup.normalizer (firstFactor K : Set T))) * ⟨u, huN⟩ = 1 :=
        Subtype.ext hu2
      rw [map_mul, hy, ← map_mul, hu1, map_one]
    have h2 : y * y ∈ Subgroup.center (SecQuot (firstFactor K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut (SecQuot (firstFactor K)) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * (y * y) = (y * y) * g * (y * y)⁻¹ * (y * y) := by rw [h3]
        _ = (y * y) * g := by group
    rw [cfg.center_eq_bot] at h2
    exact Subgroup.mem_bot.mp h2
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  have hR₀Ht : R₀ ≤ firstFactor K := hR₀.1.trans cfg.K_le_ht
  set φ : ↥R₀ →* SecQuot (firstFactor K) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(firstFactor K))).comp
      (Subgroup.inclusion hR₀Ht) with hφdef
  have hφinj : Function.Injective φ := w_mk_inclusion_injective hR₀Ht hR₀.2.1
  obtain ⟨e8⟩ := cfg.datum.quat R₀ hR₀
  have hP : Nonempty (↥φ.range ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hφinj).symm.trans e8⟩
  obtain ⟨xb, kb, hkbP, hkb4, hcomm⟩ := cfg.involution_cent_order_four hP hyy
  obtain ⟨k, rfl⟩ := hkbP
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hk4 : orderOf (k : T) = 4 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφinj k]
    exact hkb4
  set w : ↥(firstFactor K) := x * Subgroup.inclusion hR₀Ht k * x⁻¹ with hw
  have huw : u * (w : T) * u⁻¹ ∈ firstFactor K :=
    (Subgroup.mem_normalizer_iff.mp huN (w : T)).mp w.2
  set w' : ↥(firstFactor K) := ⟨u * (w : T) * u⁻¹, huw⟩
  have hact : s26Act (firstFactor K) ⟨u, huN⟩ (w : SecQuot (firstFactor K)) =
      (w' : SecQuot (firstFactor K)) :=
    s26Act_mk (firstFactor K) ⟨u, huN⟩ w w' rfl
  have hwb : (w : SecQuot (firstFactor K)) =
      (x : SecQuot (firstFactor K)) * φ k * (x : SecQuot (firstFactor K))⁻¹ := by
    rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rfl
  have heq : (w' : SecQuot (firstFactor K)) = (w : SecQuot (firstFactor K)) := by
    rw [← hact, ← hy, MulAut.conj_apply, hwb, hcomm, mul_inv_cancel_right]
  have hc : (w' * w⁻¹ : ↥(firstFactor K)) ∈ classicalInvolutionOddCore ↥(firstFactor K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq,
      mul_inv_cancel]
  exact cfg.toFrameCfg.cent_of_mod_odd hu2 huN x.2 hR₀ k.2 hk4
    (mem_oddCoreOf_iff.mpr ⟨(w' * w⁻¹).2, hc⟩)

theorem lemmaA (cfg : WCfg K z J zJ H S) {x : T}
    (hx : x⁻¹ * z * x ∈ Subgroup.normalizer (wQ K : Set T)) : x ∈ sigmaNorm K := by
  by_contra hxM
  have hz := cfg.datum.unique
  have hzQ : z ∈ wQ K := cfg.z_mem_Q
  have huQx : x⁻¹ * z * x ∈ rightConjugate (wQ K) x := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hzQ
  have hu2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [hz.sq]; group
  have hu1 : x⁻¹ * z * x ≠ 1 := fun h => hz.ne_one (by
    have := congrArg (fun w => x * w * x⁻¹) h
    simpa [mul_assoc] using this)
  have hord : orderOf (x⁻¹ * z * x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hup : IsPGroup 2 (Subgroup.zpowers (x⁻¹ * z * x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨T₀, hT₀, huT₀⟩ := IsSylow2In.exists_ge hup
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨huQx, hx⟩))
  have hT1 : T₀ ≠ ⊥ := fun h => hu1 (by
    have := huT₀ (Subgroup.mem_zpowers (x⁻¹ * z * x))
    rwa [h, Subgroup.mem_bot] at this)
  have h4 : 4 ≤ Nat.card T₀ := cfg.card_T_ge_four hxM hT₀ hT1
  have hTN : T₀ ≤ Subgroup.normalizer (firstFactor K : Set T) := fun y hy =>
    (Subgroup.mem_inf.mp (cfg.normalizer_Q_le (Subgroup.mem_inf.mp (hT₀.1 hy)).2)).2
  obtain ⟨u₁, hu₁T, hu₁1, hu₁2, hu₁N, hin⟩ := cfg.exists_inner_inv hT₀.2.1 h4 hTN
  have hu₁Qx : u₁ ∈ rightConjugate (wQ K) x := (Subgroup.mem_inf.mp (hT₀.1 hu₁T)).1
  obtain ⟨M', hM', X', hX', hX'M', hX'c⟩ := cfg.cent_of_inner hu₁2 hu₁N hin
  obtain ⟨w, hwM, rfl⟩ := cfg.inv_Qconj hxM hu₁Qx hu₁2 hu₁1
  exact hwM (cfg.toFrameCfg.mem_sigmaNorm_of_cent hM' hX' hX'M' hX'c)

theorem star (cfg : WCfg K z J zJ H S) (g : T)
    (heven : Even (Nat.card (rightConjugate (wQ K) g ⊓
      Subgroup.normalizer (wQ K : Set T) : Subgroup T))) :
    CFSG.ComponentClassification.Asc76.SylowNormalizes (rightConjugate (wQ K) g) (wQ K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨syl⟩ : Nonempty (Sylow 2 ↥(rightConjugate (wQ K) g)) := inferInstance
  have hSle : (syl : Subgroup ↥(rightConjugate (wQ K) g)).map (rightConjugate (wQ K) g).subtype ≤
      rightConjugate (wQ K) g :=
    Subgroup.map_subtype_le _
  refine ⟨_, ⟨syl, rfl⟩, ?_⟩
  by_cases hgQ : g ∈ Subgroup.normalizer (wQ K : Set T)
  ·
    have hQg : rightConjugate (wQ K) g = wQ K :=
      mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (wQ K : Set T)).inv_mem hgQ)
    refine hSle.trans ?_
    rw [hQg]
    exact Subgroup.le_normalizer
  · by_cases hgM : g ∈ sigmaNorm K
    · have hgN : g ∉ Subgroup.normalizer (firstFactor K : Set T) := fun h =>
        hgQ (cfg.normalizer_ht_le h)
      exact hSle.trans ((Subgroup.map_mono (wQ_le K)).trans (cfg.factor_le_normalizer_Q hgM hgN))
    · exfalso
      obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
      have hf' : orderOf (f : T) = 2 := (Subgroup.orderOf_coe f).trans hf
      have hf2 : (f : T) * (f : T) = 1 := by rw [← pow_two]; exact hf' ▸ pow_orderOf_eq_one _
      have hf1 : (f : T) ≠ 1 := fun h => by rw [h, orderOf_one] at hf'; omega
      obtain ⟨hfQ, hfN⟩ := Subgroup.mem_inf.mp f.2
      obtain ⟨w, hwM, hfw⟩ := cfg.inv_Qconj hgM hfQ hf2 hf1
      exact hwM (cfg.lemmaA (hfw ▸ hfN))

end WCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
