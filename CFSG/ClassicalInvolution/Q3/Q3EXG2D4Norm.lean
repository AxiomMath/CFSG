module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped MatrixGroups


section Odd

variable {G : Type} [Group G]

theorem le_of_gen3_of_cover {P Y Z H : Subgroup G} (hPY : P ≤ Y) (hZY : Z ≤ Y)
    (hZ : ∀ z ∈ Z, ∀ g ∈ Y, z * g = g * z) (hZ3 : ¬ 3 ∣ Nat.card Z) (hP : ModelFacts.Gen3 P)
    (hcov : ∀ x ∈ P, ∃ h ∈ H, h⁻¹ * x ∈ Z) : P ≤ H := by
  obtain ⟨S, hSP, hS3, hPS⟩ := hP
  have hS : ∀ s ∈ S, s ∈ H := by
    intro s hs
    obtain ⟨h, hh, hc⟩ := hcov s (hSP hs)
    set c := h⁻¹ * s with hcdef
    have hsc : s = h * c := by rw [hcdef]; group
    have hhY : h ∈ Y := by
      have : h = s * c⁻¹ := by rw [hcdef]; group
      rw [this]
      exact Subgroup.mul_mem _ (hPY (hSP hs)) (Subgroup.inv_mem _ (hZY hc))
    have hcomm : Commute h c := (hZ c hc h hhY).symm
    have h3 : (h * c) ^ 3 = 1 := by rw [← hsc]; exact hS3 s hs
    rw [hcomm.mul_pow] at h3
    have hc3 : c ^ 3 ∈ H := by
      have : c ^ 3 = (h ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
      rw [this]
      exact H.inv_mem (H.pow_mem hh 3)
    have hord : ¬ 3 ∣ orderOf c := fun h3' => hZ3 (h3'.trans (Subgroup.orderOf_dvd_natCard Z hc))
    have hcop : Nat.Coprime 3 (orderOf c) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hord
    have hcH : c ∈ H := (Subgroup.zpowers_le.mpr hc3) (mem_zpowers_pow_iff.mpr hcop)
    rw [hsc]
    exact H.mul_mem hh hcH
  exact hPS.trans ((Subgroup.closure_le H).mpr hS)

theorem eq_one_of_mem_oddCore_of_sq3 [Finite G] {c : G} (hc : c ∈ classicalInvolutionOddCore G)
    (h : c * c = 1) : c = 1 := by
  have h2 : orderOf (⟨c, hc⟩ : classicalInvolutionOddCore G) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using h))
  have h3 := orderOf_dvd_natCard (⟨c, hc⟩ : classicalInvolutionOddCore G)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h4)
  · rw [h4] at h3
    exact absurd (even_iff_two_dvd.mpr h3)
      (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))

end Odd

section Commute

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem commute_of_mk_commute3 (hP1 : LocalOddCentral Ω {x}) {u v : G} (hu : u ∈ locLayer Ω x)
    (hv : v ∈ locLayer Ω x) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu⟩) :
    u * v = v * u := by
  set a : ↥(locLayer Ω x) := ⟨u, hu⟩ with ha
  set b : ↥(locLayer Ω x) := ⟨v, hv⟩ with hb
  have haa : a * a = 1 := Subtype.ext hu2
  have hbb : b * b = 1 := Subtype.ext hv2
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) (a * b) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) (b * a) := by
    rw [map_mul, map_mul]
    exact h
  have hcO : (b * a)⁻¹ * (a * b) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    QuotientGroup.eq.mp hmk.symm
  set c := (b * a)⁻¹ * (a * b) with hc
  have hcc : c = a * b * a * b := by
    rw [hc, mul_inv_rev, hai, hbi]
    group
  have hcent : a * c = c * a := Subgroup.mem_center_iff.mp (hP1 hcO) a
  have hcc1 : c * c = 1 := by
    have h1 : a * c * a⁻¹ = c⁻¹ := by
      rw [hcc, hai]
      calc a * (a * b * a * b) * a = (a * a) * b * a * b * a := by group
        _ = b * a * b * a := by rw [haa, one_mul]
        _ = (a * b * a * b)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hai, hbi]
          group
    rw [hcent, mul_inv_cancel_right] at h1
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel c
  have h1 : c = 1 := eq_one_of_mem_oddCore_of_sq3 hcO hcc1
  have h2 : (b * a)⁻¹ * (a * b) = 1 := h1
  exact congrArg Subtype.val (inv_mul_eq_one.mp h2).symm

end Commute

section Transitive

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem Pkg3.transitive_points (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (F : G2D4Facts3 (CompData.model t n)) {M M' : Subgroup G} (hM : Fb Ω w M) (hM' : Fb Ω w M')
    {x x' : G} (hx : IsClassicalMember3 M x) (hx' : IsClassicalMember3 M' x') :
    ∃ y : ↥(locLayer Ω w), (y : G) * x * (y : G)⁻¹ = x' := by
  have hF := P.facts F
  obtain ⟨R, r, hxY, hRf, -, hu, hr⟩ := P.partner_data hΩ hex F hM hx
  obtain ⟨R', r', hx'Y, hR'f, -, hu', hr'⟩ := P.partner_data hΩ hex F hM' hx'
  obtain ⟨g, hg⟩ := hF.inv_conj R hRf R' hR'f r hu.mem r' hu'.mem hu.sq hu'.sq hu.ne_one
    hu'.ne_one (fun y hy => hu.commute_of_mem hy) (fun y hy => hu'.commute_of_mem hy)
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(locLayer Ω w)) (P.D.hom P.i₁ g)
  refine ⟨y, ?_⟩
  have h₁ : (y : G) * x * (y : G)⁻¹ ∈ locLayer Ω w :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 hxY) (Subgroup.inv_mem _ y.2)
  have hxsq := mul_self_eq_one_of_isClassicalMember3 hx
  have hx'sq := mul_self_eq_one_of_isClassicalMember3 hx'
  refine G2D4.eq_of_mk_eq_of_involutions P.p1 h₁ hx'Y ?_ hx'sq ?_
  · calc (y : G) * x * (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) =
        (y : G) * (x * x) * (y : G)⁻¹ := by group
      _ = 1 := by rw [hxsq]; group
  · have e1 : (⟨(y : G) * x * (y : G)⁻¹, h₁⟩ : ↥(locLayer Ω w)) = y * ⟨x, hxY⟩ * y⁻¹ :=
      Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hy, ← hr, ← map_inv, ← map_mul, ← map_mul, hg, hr']

end Transitive

section Normalizer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {a : ℕ}
  {t : StatedLieTag} {n : ℕ}

theorem Pkg3.layer_le_normalizer_of_pair (P : Pkg3 a t n Ω w) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (F : G2D4Facts3 (CompData.model t n)) {M M' : Subgroup G}
    (hM : Fb Ω w M) (hM' : Fb Ω w M') {u s : G} (hu : IsClassicalMember3 M u)
    (hs : IsClassicalMember3 M' s) (hus : u ≠ s) (hcomm : u * s = s * u) {Q : Subgroup G}
    (hQu : ∀ c : G, c * u * c⁻¹ = u → c ∈ Subgroup.normalizer (Q : Set G))
    (hQs : ∀ c : G, c * s * c⁻¹ = s → c ∈ Subgroup.normalizer (Q : Set G)) :
    layerX Ω w ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  have hF := P.facts F
  have hψ := P.inj F
  obtain ⟨R, r, huY, hRf, -, hRu, hr⟩ := P.partner_data hΩ hex F hM hu
  obtain ⟨R', r', hsY, hR'f, -, hR'u, hr'⟩ := P.partner_data hΩ hex F hM' hs
  have husq := mul_self_eq_one_of_isClassicalMember3 hu
  have hssq := mul_self_eq_one_of_isClassicalMember3 hs
  set mk := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω w)) with hmk
  have hne' : r ≠ r' := by
    intro h
    have h1 : mk ⟨u, huY⟩ = mk ⟨s, hsY⟩ := by rw [← hr, ← hr', h]
    exact hus (G2D4.eq_of_mk_eq_of_involutions P.p1 huY hsY husq hssq h1)
  have hcomm' : r * r' = r' * r := by
    apply hψ
    rw [map_mul, map_mul, hr, hr', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hgen := hF.gen r r' hRu.sq hR'u.sq hRu.ne_one hR'u.ne_one hne' hcomm'
  set T : Subgroup G := Subgroup.normalizer (Q : Set G) with hT
  set Hq : Subgroup (locQuot Ω w) :=
    ((T ⊓ layerX Ω w).subgroupOf (locLayer Ω w)).map mk with hHq
  have key : ∀ {u' : G} {ρ : (P.D.kind P.i₁).G} (hu'Y : u' ∈ locLayer Ω w), u' * u' = 1 →
      P.D.hom P.i₁ ρ = mk ⟨u', hu'Y⟩ → (∀ c : G, c * u' * c⁻¹ = u' → c ∈ T) →
      ∀ {e : (P.D.kind P.i₁).G}, e * ρ = ρ * e → P.D.hom P.i₁ e ∈ Hq := by
    intro u' ρ hu'Y hu'2 hρ hQ e hcomm''
    obtain ⟨y, hyL, hy⟩ := P.range_le_map_layerX hΩ hex F ⟨e, rfl⟩
    have hyu'Y : (y : G) * u' * (y : G)⁻¹ ∈ locLayer Ω w :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 hu'Y) (Subgroup.inv_mem _ y.2)
    have hyu' : (y : G) * u' * (y : G)⁻¹ = u' := by
      refine G2D4.eq_of_mk_eq_of_involutions P.p1 hyu'Y hu'Y ?_ hu'2 ?_
      · calc (y : G) * u' * (y : G)⁻¹ * ((y : G) * u' * (y : G)⁻¹)
            = (y : G) * (u' * u') * (y : G)⁻¹ := by group
          _ = 1 := by rw [hu'2]; group
      · have e1 : (⟨(y : G) * u' * (y : G)⁻¹, hyu'Y⟩ : ↥(locLayer Ω w)) =
            y * ⟨u', hu'Y⟩ * y⁻¹ := Subtype.ext rfl
        rw [e1, map_mul, map_mul, map_inv, hy, ← hρ, ← map_inv, ← map_mul, ← map_mul, hcomm'']
        simp
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hQ _ hyu', hyL⟩, hy⟩
  have hrange : (P.D.hom P.i₁).range ≤ Hq := by
    have hsup : (P.D.hom P.i₁).range =
        (Subgroup.centralizer ({r} : Set _)).map (P.D.hom P.i₁) ⊔
          (Subgroup.centralizer ({r'} : Set _)).map (P.D.hom P.i₁) := by
      rw [← Subgroup.map_sup, hgen, Subgroup.map_top]
    rw [hsup]
    refine sup_le ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      exact key huY husq hr hQu (Subgroup.mem_centralizer_singleton_iff.mp he)
    · rintro _ ⟨e, he, rfl⟩
      exact key hsY hssq hr' hQs (Subgroup.mem_centralizer_singleton_iff.mp he)
  refine le_of_gen3_of_cover (Y := locLayer Ω w) (Z := Asc77.oddCoreOf (locLayer Ω w))
    (layerX_le_locLayer Ω w) (Asc77.oddCoreOf_le_self _) (oddCore_central3 P.p1)
    (not_three_dvd_oddCoreOf P.o3) (gen3_layerX hΩ hex) ?_
  intro x hx
  have hxY : x ∈ locLayer Ω w := layerX_le_locLayer Ω w hx
  have hmem : mk ⟨x, hxY⟩ ∈ (P.D.hom P.i₁).range := P.mk_mem_range_of_mem_layerX hΩ hex F hx hxY
  obtain ⟨y, hy, hyx⟩ := hrange hmem
  have hy' := Subgroup.mem_subgroupOf.mp hy
  refine ⟨(y : G), hy'.1, ?_⟩
  have hO : y⁻¹ * ⟨x, hxY⟩ ∈ classicalInvolutionOddCore ↥(locLayer Ω w) := QuotientGroup.eq.mp hyx
  exact Asc77.mem_oddCoreOf_iff.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) hxY, hO⟩

end Normalizer

section Generation

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ} {t : StatedLieTag}
  {n : ℕ}

theorem adj_step (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u)
    {M : Subgroup G} (hM : Fb (conjClass3 K) u M) {x : G} (hx : IsClassicalMember3 M x)
    {N' L : Subgroup G} (hN' : Cn (conjClass3 K) u N') (hL : L ∈ conjClass3 K)
    (hc : Commutes N' L) :
    Cn (conjClass3 K) u L ∨ ∃ y : ↥(locLayer (conjClass3 K) u), ∃ N'' : Subgroup G,
      Cn (conjClass3 K) x N'' ∧ L = conjSub (y : G) N'' := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨P⟩ := S.exists_pkg hN₀ hu
  have hN'cls : IsClassicalMember3 N' u := cn_isClassical S F hN₀ hu hN'
  have hLu : L ∈ centralizingMembers (conjClass3 K) {u} :=
    (P.cnbhd_iff hΩ hex F hN'.1.1 hN'cls hL).mp (Or.inr hc.symm)
  rcases fb_or_cn hLu with h | h
  · exact Or.inl h
  · right
    obtain ⟨x'', hx''⟩ := hΩ.classical L hL
    obtain ⟨y, hy⟩ := P.transitive_points hΩ hex F hM h hx hx''
    obtain ⟨Px''⟩ := S.exists_pkg hL hx''
    have hLcn : Cn (conjClass3 K) x'' L := Px''.cn_of_isClassicalMember hΩ hex F hL hx''
    refine ⟨y, conjSub (y : G)⁻¹ L, ?_, ?_⟩
    · have := (cn_conj_iff hΩ.conjInvariant (y : G)⁻¹).mpr hLcn
      rwa [← hy, show (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * (y : G)⁻¹⁻¹ = x by group] at this
    · exact (conjSub_conjSub_inv _ L).symm

theorem generated_pair3 (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n))
    {u : G} {N₀ : Subgroup G} (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u)
    {M : Subgroup G} (hM : Fb (conjClass3 K) u M) {x : G} (hx : IsClassicalMember3 M x) :
    (⊤ : Subgroup G) ≤ layerX (conjClass3 K) u ⊔ layerX (conjClass3 K) x := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨P⟩ := S.exists_pkg hN₀ hu
  have hN₀cn : Cn (conjClass3 K) u N₀ := P.cn_of_isClassicalMember hΩ hex F hN₀ hu
  have hN₀fb : Fb (conjClass3 K) x N₀ := fb_of_cn_of_fb S F hN₀ hu hM hx hN₀cn
  set G₀ : Subgroup G := layerX (conjClass3 K) u ⊔ layerX (conjClass3 K) x with hG₀
  have hYu : centralizingLayer (conjClass3 K) {u} ≤ G₀ := by
    refine iSup₂_le fun L hL => ?_
    rcases fb_or_cn hL with h | h
    · exact (le_layerX (fb_of_cn_of_fb S F hN₀ hu hM hx h)).trans le_sup_right
    · exact (le_layerX h).trans le_sup_left
  have hYx : centralizingLayer (conjClass3 K) {x} ≤ G₀ := by
    refine iSup₂_le fun L hL => ?_
    rcases fb_or_cn hL with h | h
    · exact (le_layerX (fb_of_cn_swap S F hN₀ hu hM hx h)).trans le_sup_left
    · exact (le_layerX h).trans le_sup_right
  set 𝔖 : Set (Subgroup G) := {N | N ∈ conjClass3 K ∧ ∃ g ∈ G₀, ∃ N' : Subgroup G,
    (Cn (conjClass3 K) u N' ∨ Cn (conjClass3 K) x N') ∧ N = conjSub g N'} with h𝔖
  have hsub : 𝔖 ⊆ conjClass3 K := fun N hN => hN.1
  have hne : 𝔖.Nonempty := ⟨N₀, hN₀, 1, G₀.one_mem, N₀, Or.inl hN₀cn, (conjSub_one N₀).symm⟩
  have hcl : ∀ J ∈ 𝔖, ∀ L ∈ conjClass3 K, L ≠ J → Commutes J L → L ∈ 𝔖 := by
    rintro J ⟨hJΩ, g, hg, N', hN'cn, rfl⟩ L hLΩ - hcomm
    have hL'Ω : conjSub g⁻¹ L ∈ conjClass3 K := hΩ.conjInvariant g⁻¹ L hLΩ
    have hL'c : Commutes N' (conjSub g⁻¹ L) := by
      have := hcomm.conjSub g⁻¹
      rwa [conjSub_inv_conjSub] at this
    rcases hN'cn with hN' | hN'
    · rcases adj_step S F hN₀ hu hM hx hN' hL'Ω hL'c with h | ⟨y, N'', hN'', hy⟩
      · exact ⟨hLΩ, g, hg, conjSub g⁻¹ L, Or.inl h, (conjSub_conjSub_inv g L).symm⟩
      · refine ⟨hLΩ, g * y, G₀.mul_mem hg (hYu y.2), N'', Or.inr hN'', ?_⟩
        rw [conjSub_mul, ← hy, conjSub_conjSub_inv]
    · rcases adj_step S F hM.1.1 hx hN₀fb hu hN' hL'Ω hL'c with h | ⟨y, N'', hN'', hy⟩
      · exact ⟨hLΩ, g, hg, conjSub g⁻¹ L, Or.inr h, (conjSub_conjSub_inv g L).symm⟩
      · refine ⟨hLΩ, g * y, G₀.mul_mem hg (hYx y.2), N'', Or.inl hN'', ?_⟩
        rw [conjSub_mul, ← hy, conjSub_conjSub_inv]
  have hall : conjClass3 K ⊆ 𝔖 :=
    subset_of_adj_closed ((CoreAssembly.deltaConnected_iff K).mp S.setup.conn) hsub hne hcl
  rw [← hΩ.generated]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨-, g, hg, N', hN', rfl⟩ := hall hL
  have hN'le : N' ≤ G₀ := by
    rcases hN' with h | h
    · exact (le_centralizingLayer h.1).trans hYu
    · exact (le_centralizingLayer h.1).trans hYx
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := hN'le hy
  have h2 := G₀.mul_mem (G₀.mul_mem hg h1) (G₀.inv_mem hg)
  simpa [mul_assoc] using h2

end Generation

section TypeA

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ} {t : StatedLieTag}
  {n : ℕ}

theorem typeA_false [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : ExCtx3 G K z a t n) (F : G2D4Facts3 (CompData.model t n)) {u : G} {N₀ : Subgroup G}
    (hN₀ : N₀ ∈ conjClass3 K) (hu : IsClassicalMember3 N₀ u) {M M₁ : Subgroup G}
    (hM : Fb (conjClass3 K) u M) (hM₁ : Fb (conjClass3 K) u M₁) {p q : G}
    (hp : IsClassicalMember3 M p) (hq : IsClassicalMember3 M₁ q) (hpq : p ≠ q)
    (hcomm : p * q = q * p) (hqc : ∀ x ∈ layerX (conjClass3 K) p, q * x = x * q) : False := by
  classical
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hMΩ : M ∈ conjClass3 K := hM.1.1
  have hM₁Ω : M₁ ∈ conjClass3 K := hM₁.1.1
  obtain ⟨Pu⟩ := S.exists_pkg hN₀ hu
  obtain ⟨Pp⟩ := S.exists_pkg hMΩ hp
  have hMcn : Cn (conjClass3 K) p M := Pp.cn_of_isClassicalMember hΩ hex F hMΩ hp
  have hN₀cn : Cn (conjClass3 K) u N₀ := Pu.cn_of_isClassicalMember hΩ hex F hN₀ hu
  have hFsub : {N | Fb (conjClass3 K) p N} ⊆ {N | Fb (conjClass3 K) q N} := by
    intro N hN
    have hNq : N ∈ centralizingMembers (conjClass3 K) {q} :=
      ⟨hN.1.1, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (hqc x (le_layerX hN hx)).symm⟩
    rcases fb_or_cn hNq with hc | hf
    · exfalso
      have hNcls : IsClassicalMember3 N q := cn_isClassical S F hM₁Ω hq hc
      have hNfb : Fb (conjClass3 K) u N := fb_of_cn_swap S F hN₀ hu hM₁ hq hc
      have hcM : Commutes M N := by
        rcases hMcn.2 N hN.1 with h | h
        · subst h
          exact absurd hMcn hN.2
        · exact h
      exact hpq (Pu.eq_involution_of_commuting_pair hΩ hex F hM hNfb hp hNcls hcM)
    · exact hf
  obtain ⟨g, hg⟩ := exists_conj_point hMΩ hM₁Ω hp hq
  have hcard : {N | Fb (conjClass3 K) q N}.ncard ≤ {N | Fb (conjClass3 K) p N}.ncard := by
    have := ncard_fb_conj hΩ.conjInvariant g q
    rw [hg] at this
    exact this.ge
  have hFeq : {N | Fb (conjClass3 K) p N} = {N | Fb (conjClass3 K) q N} :=
    Set.eq_of_subset_of_ncard_le hFsub hcard (Set.toFinite _)
  have hXeq : layerX (conjClass3 K) p = layerX (conjClass3 K) q := by
    unfold layerX
    rw [hFeq]
  obtain ⟨Q, hQp'⟩ : ∃ Q, Q = layerX (conjClass3 K) p := ⟨_, rfl⟩
  have hQq' : Q = layerX (conjClass3 K) q := hQp'.trans hXeq
  have hQp : ∀ c : G, c * p * c⁻¹ = p → c ∈ Subgroup.normalizer (Q : Set G) := by
    intro c hc
    have h1 : conjSub c Q = Q := by
      rw [hQp', conjSub_layerX hΩ.conjInvariant c p, hc]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hQq : ∀ c : G, c * q * c⁻¹ = q → c ∈ Subgroup.normalizer (Q : Set G) := by
    intro c hc
    have h1 : conjSub c Q = Q := by
      rw [hQq', conjSub_layerX hΩ.conjInvariant c q, hc]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hXu : layerX (conjClass3 K) u ≤ Subgroup.normalizer (Q : Set G) :=
    Pu.layer_le_normalizer_of_pair hΩ hex F hM hM₁ hp hq hpq hcomm hQp hQq
  have hYu : centralizingLayer (conjClass3 K) {u} ≤ Subgroup.normalizer (Q : Set G) := by
    refine iSup₂_le fun L hL => ?_
    rcases fb_or_cn hL with h | h
    · have hLp : Fb (conjClass3 K) p L := fb_of_cn_of_fb S F hN₀ hu hM hp h
      have : L ≤ Q := hQp' ▸ le_layerX hLp
      exact this.trans Subgroup.le_normalizer
    · exact (le_layerX h).trans hXu
  have hXpt : ∀ (L : Subgroup G) (x : G), Fb (conjClass3 K) u L → IsClassicalMember3 L x →
      layerX (conjClass3 K) x = Q := by
    intro L x hL hx
    obtain ⟨y, hy⟩ := Pu.transitive_points hΩ hex F hM hL hp hx
    have h1 : conjSub (y : G) Q = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYu y.2)
    rw [← hy, ← conjSub_layerX hΩ.conjInvariant (y : G) p, ← hQp']
    exact h1
  have hcent : ∀ N ∈ {N | Fb (conjClass3 K) u N}, Q ≤ Subgroup.centralizer (N : Set G) := by
    intro N hN
    obtain ⟨x, hx⟩ := hΩ.classical N hN.1.1
    have hQx := hXpt N x hN hx
    obtain ⟨Px⟩ := S.exists_pkg hN.1.1 hx
    have hNcn : Cn (conjClass3 K) x N := Px.cn_of_isClassicalMember hΩ hex F hN.1.1 hx
    rw [← hQx]
    refine iSup₂_le fun L hL l hl => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    rcases hNcn.2 L hL.1 with h | h
    · subst h
      exact absurd hNcn hL.2
    · exact h n hn l hl
  have hXz : layerX (conjClass3 K) u ≤ Subgroup.centralizer (Q : Set G) := by
    refine iSup₂_le fun N hN n hn => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hcent N hN hq') n hn).symm
  have hgen := generated_pair3 S F hN₀ hu hM hp
  rw [← hQp'] at hgen
  have hQcent : Q ≤ Subgroup.centralizer (layerX (conjClass3 K) u : Set G) := by
    intro q' hq'
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hXz hh) q' hq').symm
  have hnormalizer : Subgroup.normalizer (layerX (conjClass3 K) u : Set G) = ⊤ := by
    rw [eq_top_iff]
    exact hgen.trans (sup_le Subgroup.le_normalizer
      (hQcent.trans (Subgroup.centralizer_le_normalizer _)))
  have hnormal : (layerX (conjClass3 K) u).Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (layerX (conjClass3 K) u) with hbot | htop
  · have hpmem : p ∈ layerX (conjClass3 K) u := le_layerX hM hp.mem
    rw [hbot, Subgroup.mem_bot] at hpmem
    have h2 := hp.orderOf_eq_two
    rw [hpmem, orderOf_one] at h2
    omega
  · have hcen := center_eq_bot_of_simple hnab
    have hN₀fb : Fb (conjClass3 K) p N₀ := fb_of_cn_of_fb S F hN₀ hu hM hp hN₀cn
    have huQ : u ∈ Q := hQp' ▸ le_layerX hN₀fb hu.mem
    have hucen : u ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have hgmem : g ∈ layerX (conjClass3 K) u := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp (hXz hgmem) u huQ).symm
    rw [hcen, Subgroup.mem_bot] at hucen
    have h2 := hu.orderOf_eq_two
    rw [hucen, orderOf_one] at h2
    omega

end TypeA

end CFSG.ClassicalInvolution.Q3.Q3W.EX
