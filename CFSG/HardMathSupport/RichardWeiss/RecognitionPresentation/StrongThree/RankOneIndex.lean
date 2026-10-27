module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusLieOffCharAux

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isPGroup_zpowers_of_pow_three {z : X} (hz : z ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers z) := by
  rintro ⟨g, hg⟩
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem exists_conj_mem_sylow (P : Sylow 3 X) {N : Subgroup X} (hPN : (P : Subgroup X) ≤ N)
    {z : X} (hzN : z ∈ N) (hz : z ^ 3 = 1) : ∃ g ∈ N, g⁻¹ * z * g ∈ (P : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsPGroup 3 ((Subgroup.zpowers z).subgroupOf N) :=
    (isPGroup_zpowers_of_pow_three hz).comap_of_injective N.subtype N.subtype_injective
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) (P.subtype hPN) Q
  have hzQ : (⟨z, hzN⟩ : ↥N) ∈ (Q : Subgroup ↥N) :=
    hQ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z))
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_subtype] at hzQ
  refine ⟨(g : X), g.2, ?_⟩
  have h := Subgroup.mem_subgroupOf.1 hzQ
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h

omit [Finite X] in
theorem map_conj_map_conj (H : Subgroup X) (a b : X) :
    (H.map (MulAut.conj b : X →* X)).map (MulAut.conj a : X →* X) =
      H.map (MulAut.conj (a * b) : X →* X) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite X] in
theorem map_conj_one (H : Subgroup X) : H.map (MulAut.conj (1 : X) : X →* X) = H := by
  have h : ((MulAut.conj (1 : X) : MulAut X) : X →* X) = MonoidHom.id X := by
    ext x
    simp
  rw [h, Subgroup.map_id]

omit [Finite X] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {n : X}
    (hn : n ∈ Subgroup.normalizer (H : Set X)) : H.map (MulAut.conj n : X →* X) = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 hn

omit [Finite X] in
theorem inv_mul_mem_normalizer_of_map_conj_eq {H : Subgroup X} {a b : X}
    (h : H.map (MulAut.conj a : X →* X) = H.map (MulAut.conj b : X →* X)) :
    b⁻¹ * a ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← map_conj_map_conj, h, map_conj_map_conj,
    inv_mul_cancel, map_conj_one]

theorem not_three_dvd_index_of_rankOne {K : Subgroup X} [hKn : K.Normal]
    (P : Sylow 3 X) (hT : (P : Subgroup X) ⊓ K ≠ ⊥)
    (hTI : ∀ k ∈ K, ∀ t ∈ (P : Subgroup X) ⊓ K, t ≠ 1 → k * t * k⁻¹ ∈ (P : Subgroup X) ⊓ K →
      k ∈ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X))
    (hmax : ∀ H : Subgroup X,
      K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ H → H ≤ K →
      H = K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ∨ H = K)
    (hidx : (K ⊓ Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X)).relIndex K =
      Nat.card ↥((P : Subgroup X) ⊓ K) + 1)
    (hΓ : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤) : ¬ 3 ∣ K.index := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup X := (P : Subgroup X) ⊓ K with hTdef
  set NT : Subgroup X := Subgroup.normalizer (T : Set X) with hNTdef
  set B : Subgroup X := K ⊓ NT with hBdef
  set Γ : Subgroup X := gammaCore 3 1 ⊤ (P : Subgroup X) with hΓdef
  have hT3 : IsPGroup 3 T := P.isPGroup'.to_le inf_le_left
  have hrkT : 1 ≤ CFSG.Open.pRank 3 T := by
    have hcard : Nat.card T ≠ 1 := fun h => hT (Subgroup.eq_bot_of_card_eq T h)
    have h3 : 3 ∣ Nat.card T := hT3.card_eq_or_dvd.resolve_left hcard
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 h3
    have hx3 : (x : X) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx] at h
      exact congrArg Subtype.val h
    have hx1 : (x : X) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    exact one_le_pRank_of_mem x.2 hx3 hx1
  have hNTΓ : NT ≤ Γ := fun g hg =>
    Subgroup.subset_closure ⟨Subgroup.mem_top _, T, inf_le_left, hrkT, hg⟩
  have hPNT : (P : Subgroup X) ≤ NT := by
    intro p hp
    rw [hNTdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hp h1)
        ((P : Subgroup X).inv_mem hp), hKn.conj_mem h h2 p⟩
    · rintro ⟨h1, h2⟩
      have e : h = p⁻¹ * (p * h * p⁻¹) * p := by group
      refine ⟨?_, ?_⟩
      · rw [e]
        exact (P : Subgroup X).mul_mem
          ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hp) h1) hp
      · rw [e]
        have := hKn.conj_mem _ h2 p⁻¹
        simpa [mul_assoc] using this
  have hΓK : Γ ⊓ K = B := by
    rcases hmax (Γ ⊓ K) (le_inf (inf_le_right.trans hNTΓ) inf_le_left) inf_le_right with h | h
    · exact h
    · exfalso
      have hKΓ : K ≤ Γ := by
        rw [← h]
        exact inf_le_left
      exact hΓ.ne (gammaCore_eq_top_of_le P hKΓ hrkT)
  have hcent : ∀ z ∈ NT, z ^ 3 = 1 → z ≠ 1 → ∀ c ∈ K, z * c * z⁻¹ = c → c ∈ NT := by
    intro z hz hz3 hz1 c hcK hzc
    obtain ⟨g, hgN, hgP⟩ := exists_conj_mem_sylow P hPNT hz hz3
    have hy3 : (g⁻¹ * z * g) ^ 3 = 1 := by
      rw [show g⁻¹ * z * g = MulAut.conj g⁻¹ z by simp, ← map_pow, hz3,
        map_one]
    have hy1 : g⁻¹ * z * g ≠ 1 := by
      intro h
      apply hz1
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, h]
      group
    have hc'K : g⁻¹ * c * g ∈ K := by
      have := hKn.conj_mem c hcK g⁻¹
      simpa [mul_assoc] using this
    have hyc : (g⁻¹ * z * g) * (g⁻¹ * c * g) * (g⁻¹ * z * g)⁻¹ = g⁻¹ * c * g := by
      calc (g⁻¹ * z * g) * (g⁻¹ * c * g) * (g⁻¹ * z * g)⁻¹ = g⁻¹ * (z * c * z⁻¹) * g := by
            group
        _ = g⁻¹ * c * g := by rw [hzc]
    have hc'Γ : g⁻¹ * c * g ∈ Γ := mem_gammaCore_of_commute (P : Subgroup X) hgP hy3 hy1 hyc
    have hc'B : g⁻¹ * c * g ∈ B := by
      rw [← hΓK]
      exact ⟨hc'Γ, hc'K⟩
    have e : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [e]
    exact NT.mul_mem (NT.mul_mem hgN hc'B.2) (NT.inv_mem hgN)
  intro h3K
  have hPK : ¬ (P : Subgroup X) ≤ K := by
    intro hle
    exact P.not_dvd_index (h3K.trans (Subgroup.index_dvd_of_le hle))
  have hTlt : Nat.card T < Nat.card (P : Subgroup X) := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hPK ?_)
    rw [← h]
    exact inf_le_right
  have hBK : B ≠ K := by
    intro h
    have h1 : B.relIndex K = 1 := by
      rw [h]
      exact Subgroup.relIndex_self K
    rw [hidx] at h1
    have := Nat.card_pos (α := ↥T)
    omega
  obtain ⟨k, hkK, hkN⟩ : ∃ k ∈ K, k ∉ NT := by
    by_contra hcon
    push Not at hcon
    exact hBK (le_antisymm inf_le_left fun k hk => ⟨hk, hcon k hk⟩)
  set ω : Subgroup X := T.map (MulAut.conj k : X →* X) with hωdef
  have hωT : ω ≠ T := fun h => hkN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  let Ω : Set (Subgroup X) := Set.range fun c : ↥K => T.map (MulAut.conj (c : X) : X →* X)
  have hΩcard : Nat.card Ω ≤ Nat.card T + 1 := by
    rw [← hidx]
    let F : ↥K ⧸ B.subgroupOf K → Ω := Quotient.lift
      (fun c : ↥K => (⟨T.map (MulAut.conj (c : X) : X →* X), c, rfl⟩ : Ω)) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ B.subgroupOf K := QuotientGroup.leftRel_apply.1 hab
        have hn : (a : X)⁻¹ * (b : X) ∈ NT := (Subgroup.mem_subgroupOf.1 hab').2
        apply Subtype.ext
        show T.map (MulAut.conj (a : X) : X →* X) = T.map (MulAut.conj (b : X) : X →* X)
        have hb : (b : X) = (a : X) * ((a : X)⁻¹ * (b : X)) := by group
        rw [hb, ← map_conj_map_conj, map_conj_eq_of_mem_normalizer hn])
    have hF : Function.Surjective F := by
      rintro ⟨_, c, rfl⟩
      exact ⟨QuotientGroup.mk c, rfl⟩
    exact Nat.card_le_card_of_surjective F hF
  have hTΩ : T ∈ Ω := ⟨1, map_conj_one T⟩
  have hmemΩ : ∀ p ∈ (P : Subgroup X),
      ω.map (MulAut.conj p : X →* X) ∈ Ω ∧ ω.map (MulAut.conj p : X →* X) ≠ T := by
    intro p hp
    have hpNT : p ∈ NT := hPNT hp
    refine ⟨⟨⟨p * k * p⁻¹, hKn.conj_mem k hkK p⟩, ?_⟩, ?_⟩
    · show T.map (MulAut.conj (p * k * p⁻¹) : X →* X) = ω.map (MulAut.conj p : X →* X)
      rw [hωdef, map_conj_map_conj, ← map_conj_map_conj T (p * k),
        map_conj_eq_of_mem_normalizer (NT.inv_mem hpNT)]
    · intro h
      apply hωT
      have h2 := congrArg (fun H : Subgroup X => H.map (MulAut.conj p⁻¹ : X →* X)) h
      simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h2
      rw [h2]
      exact map_conj_eq_of_mem_normalizer (NT.inv_mem hpNT)
  obtain ⟨x, hxP, hx1, hxω⟩ : ∃ x ∈ (P : Subgroup X), x ≠ 1 ∧
      x ∈ Subgroup.normalizer (ω : Set X) := by
    by_contra hcon
    push Not at hcon
    let g : ↥(P : Subgroup X) → ↥(Ω \ {T}) := fun p =>
      ⟨ω.map (MulAut.conj (p : X) : X →* X), (hmemΩ p p.2).1,
        fun h => (hmemΩ p p.2).2 (Set.mem_singleton_iff.1 h)⟩
    have hg : Function.Injective g := by
      intro p q hpq
      have h := congrArg Subtype.val hpq
      have hn := inv_mul_mem_normalizer_of_map_conj_eq h
      by_contra hne
      have hne' : (q : X)⁻¹ * (p : X) ≠ 1 := by
        intro h1
        apply hne
        apply Subtype.ext
        exact (inv_mul_eq_one.1 h1).symm
      exact hcon _ ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem q.2) p.2) hne' hn
    have h1 := Nat.card_le_card_of_injective g hg
    have h2 : Nat.card ↥(Ω \ {T}) = Nat.card Ω - 1 := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
        Set.ncard_sdiff_singleton_of_mem hTΩ]
    omega
  obtain ⟨y, hyP, hy1, hy3, hyω⟩ : ∃ y ∈ (P : Subgroup X), y ≠ 1 ∧ y ^ 3 = 1 ∧
      y ∈ Subgroup.normalizer (ω : Set X) := by
    have hx3 : IsPGroup 3 (Subgroup.zpowers x) :=
      P.isPGroup'.to_le ((Subgroup.zpowers_le).2 hxP)
    have hcard : Nat.card (Subgroup.zpowers x) ≠ 1 := by
      intro h
      apply hx1
      have hb := Subgroup.eq_bot_of_card_eq _ h
      have hmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [hb, Subgroup.mem_bot] at hmem
      exact hmem
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) 3
      (hx3.card_eq_or_dvd.resolve_left hcard)
    refine ⟨y, (Subgroup.zpowers_le).2 hxP y.2, ?_, ?_, (Subgroup.zpowers_le).2 hxω y.2⟩
    · intro h
      have : y = 1 := Subtype.ext h
      rw [this, orderOf_one] at hy
      exact absurd hy (by norm_num)
    · have h := pow_orderOf_eq_one y
      rw [hy] at h
      exact congrArg Subtype.val h
  have hcentω : ∀ c ∈ K, y * c * y⁻¹ = c → c ∈ Subgroup.normalizer (ω : Set X) := by
    intro c hcK hyc
    have hz : k⁻¹ * y * k ∈ NT := by
      have h := Subgroup.mem_normalizer_iff_map_conj_eq.1 hyω
      rw [hωdef, map_conj_map_conj] at h
      rw [hNTdef, Subgroup.mem_normalizer_iff_map_conj_eq,
        show k⁻¹ * y * k = k⁻¹ * (y * k) by group, ← map_conj_map_conj, h, map_conj_map_conj,
        inv_mul_cancel, map_conj_one]
    have hz3 : (k⁻¹ * y * k) ^ 3 = 1 := by
      rw [show k⁻¹ * y * k = MulAut.conj k⁻¹ y by simp, ← map_pow, hy3,
        map_one]
    have hz1 : k⁻¹ * y * k ≠ 1 := by
      intro h
      apply hy1
      have : y = k * (k⁻¹ * y * k) * k⁻¹ := by group
      rw [this, h]
      group
    have hc'K : k⁻¹ * c * k ∈ K := by
      have := hKn.conj_mem c hcK k⁻¹
      simpa [mul_assoc] using this
    have hzc : (k⁻¹ * y * k) * (k⁻¹ * c * k) * (k⁻¹ * y * k)⁻¹ = k⁻¹ * c * k := by
      calc (k⁻¹ * y * k) * (k⁻¹ * c * k) * (k⁻¹ * y * k)⁻¹ = k⁻¹ * (y * c * y⁻¹) * k := by
            group
        _ = k⁻¹ * c * k := by rw [hyc]
    have hc' : k⁻¹ * c * k ∈ NT := hcent _ hz hz3 hz1 _ hc'K hzc
    have h := map_conj_eq_of_mem_normalizer hc'
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hωdef, map_conj_map_conj,
      show c * k = k * (k⁻¹ * c * k) by group, ← map_conj_map_conj, h]
  obtain ⟨T₀, hT₀⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hTI' : ∀ c ∈ T, c ∈ Subgroup.normalizer (ω : Set X) → c = 1 := by
    intro c hcT hcω
    have hcK : c ∈ K := hcT.2
    have hωK : ω ≤ K := by
      rintro _ ⟨t, ht, rfl⟩
      exact hKn.conj_mem t ht.2 k
    have hω3 : IsPGroup 3 ω := hT3.map _
    have hcard_ω : Nat.card ω = Nat.card T :=
      Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      hT3.to_le ((Subgroup.zpowers_le).2 hcT)
    have hH3 : IsPGroup 3 (ω ⊔ Subgroup.zpowers c : Subgroup X) :=
      hω3.to_sup_of_normal_left' hc3 ((Subgroup.zpowers_le).2 hcω)
    have hHK : ω ⊔ Subgroup.zpowers c ≤ K := sup_le hωK ((Subgroup.zpowers_le).2 hcK)
    have hle : Nat.card ↥(ω ⊔ Subgroup.zpowers c) ≤ Nat.card ↥T := by
      have hH3' : IsPGroup 3 ((ω ⊔ Subgroup.zpowers c).subgroupOf K) :=
        hH3.comap_of_injective K.subtype K.subtype_injective
      obtain ⟨Q, hQ⟩ := hH3'.exists_le_sylow
      have hQT : Nat.card (Q : Subgroup ↥K) = Nat.card ↥T := by
        rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity T₀, hT₀]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ≤ K)).toEquiv
      have hHQ : Nat.card ↥(ω ⊔ Subgroup.zpowers c) ≤ Nat.card (Q : Subgroup ↥K) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
        exact Subgroup.card_le_of_le hQ
      exact hHQ.trans hQT.le
    have hωeq : ω ⊔ Subgroup.zpowers c = ω :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard_ω]; exact hle)).symm
    have hcω' : c ∈ ω := by
      rw [← hωeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    obtain ⟨s, hsT, hsc⟩ := hcω'
    by_contra hc1
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply hc1
      rw [← hsc]
      simp
    have hks : k * s * k⁻¹ ∈ T := by
      have : (MulAut.conj k) s = k * s * k⁻¹ := MulAut.conj_apply k s
      rw [← this]
      exact hsc ▸ hcT
    exact hkN (hTI k hkK s hsT hs1 hks)
  have hPnil : Group.IsNilpotent ↥(P : Subgroup X) := P.isPGroup'.isNilpotent
  have hTn : (T.subgroupOf (P : Subgroup X)).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hPNT b.2) a).1 ha
  have hTne : T.subgroupOf (P : Subgroup X) ≠ ⊥ := by
    intro h
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have : (⟨t, ht.1⟩ : ↥(P : Subgroup X)) ∈ T.subgroupOf (P : Subgroup X) :=
      Subgroup.mem_subgroupOf.2 ht
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨⟨c, hcP⟩, hcT, hcZ⟩, hc1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hTne)
  have hcT' : c ∈ T := Subgroup.mem_subgroupOf.1 hcT
  have hyc : y * c * y⁻¹ = c := by
    have h := Subgroup.mem_center_iff.1 hcZ ⟨y, hyP⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    rw [h', mul_assoc, mul_inv_cancel, mul_one]
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  exact hc1' (hTI' c hcT' (hcentω c hcT'.2 hyc))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
