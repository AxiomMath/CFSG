module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs29
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2Seven
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.GorensteinWalter Subgroup
open scoped MatrixGroups

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem center_trivial_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ y : Y, (∀ y' : Y, y * y' = y' * y) → y = 1) :
    ∀ x : X, (∀ x' : X, x * x' = x' * x) → x = 1 := by
  intro x hx
  have h1 : e x = 1 := hY _ (fun y' => by
    obtain ⟨x', rfl⟩ := e.surjective y'
    rw [← map_mul, ← map_mul, hx x'])
  exact e.injective (by rw [h1, map_one])

theorem center_trivial_of_center_eq_bot {Y : Type} [Group Y] (h : Subgroup.center Y = ⊥) :
    ∀ y : Y, (∀ y' : Y, y * y' = y' * y) → y = 1 := by
  intro y hy
  have : y ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => (hy g).symm
  rw [h] at this
  exact Subgroup.mem_bot.mp this

theorem psl2_17_equiv {X : Type} [Group X] (h : StatedClassicalModel X .PSL 2 17 1) :
    Nonempty (X ≃* PSL(2, GaloisField 17 1)) := by
  obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := h
  have hFc : Nat.card F = 17 ^ 1 := hFcard
  exact ⟨e.trans
    (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 17 1 (by norm_num) hFc)⟩

theorem K9Type.center_trivial {X : Type} [Group X] (h : K9Type X) :
    ∀ x : X, (∀ x' : X, x * x' = x' * x) → x = 1 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h
  · have h4 : 4 ≤ Nat.card (Fin 6) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    exact center_trivial_of_equiv e
      (center_trivial_of_center_eq_bot (alternatingGroup.center_eq_bot h4))
  · have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact center_trivial_of_equiv e (center_trivial_of_center_eq_bot (psl2_center_eq_bot (ZMod 7)))
  · obtain ⟨e⟩ := psl2_17_equiv h
    exact center_trivial_of_equiv e
      (center_trivial_of_center_eq_bot (psl2_center_eq_bot (GaloisField 17 1)))

theorem psl2p_aut_conj_of_fixes_kleinFour
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hF : Nat.card F = p) (V : Subgroup PSL(2, F)) (hV : IsKleinFour V)
    (β : MulAut PSL(2, F)) (hβ : ∀ v ∈ V, β v = v) : ∃ g ∈ V, β = MulAut.conj g := by
  have hK' := Unc25K1.isOddPrimePower_of_card_prime (K := F) (p := p) hp7 hF
  have hKpow : Nat.card F = p ^ 1 := by rw [hF, pow_one]
  have hcard : 3 < Nat.card F := by omega
  have hex : ∃ (g : PGL2 F) (σ : F ≃+* F),
      β = pgl2InnerAutPSL2 F hK' hcard g * psl2FieldAut F σ := by
    obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective F hKpow hK' hcard β
    have h := congrArg (pGammaL2ToMulAutPSL2 F hK' hcard)
      (SemidirectProduct.inl_left_mul_inr_right xx)
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
    exact ⟨xx.left, xx.right, h.symm⟩
  obtain ⟨g, σ, hβgσ⟩ := hex
  have hσ : σ = 1 :=
    (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime F hF).elim _ _
  rw [hσ, map_one, mul_one] at hβgσ
  let toPGL : PSL(2, F) →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 F hK' hcard g v = v := by
      rw [← hβgσ]
      exact hβ v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply F hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self F hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  refine ⟨g0, hg0V, ?_⟩
  rw [hβgσ, ← hg0]
  exact pgl2InnerAutPSL2_toPGL F hK' hcard g0

theorem psl2p_aut_eq_one
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hF : Nat.card F = p) {G : Type} [Group G] [Finite G] {K L U : Subgroup G}
    (e₁ : ↥K ≃* PSL(2, F)) (hL : IsA4Block L U) (hUK : U ≤ K)
    (hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (hLN : L ≤ Subgroup.normalizer (K : Set G)) (α : MulAut ↥K)
    (hα : ∀ (l : G) (hl : l ∈ U), α ⟨l, hUK hl⟩ = ⟨l, hUK hl⟩)
    (hαc : ∀ (c : G) (_ : c ∈ L) (hcN : c ∈ Subgroup.normalizer (K : Set G)) (k : ↥K),
      α (conjAutK c hcN k) = conjAutK c hcN (α k)) : ∀ k : ↥K, α k = k := by
  obtain ⟨c, hcL, hc3, hcNU, hcfp, hLc⟩ := hL.exists_c
  let V₀ : Subgroup ↥K := U.subgroupOf K
  let V : Subgroup PSL(2, F) := V₀.map e₁.toMonoidHom
  have hV : IsKleinFour V := isKleinFour_map_of_injective V₀ (hL.isKleinFour_subgroupOf hUK)
    e₁.toMonoidHom e₁.injective
  let β : MulAut PSL(2, F) := (e₁.symm.trans α).trans e₁
  have hβapp : ∀ k : ↥K, β (e₁ k) = e₁ (α k) := by
    intro k
    show e₁ (α (e₁.symm (e₁ k))) = e₁ (α k)
    rw [MulEquiv.symm_apply_apply]
  have hβV : ∀ v ∈ V, β v = v := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ U := hu
    have hαu : α u = u := hα (u : G) hu'
    show β (e₁ u) = e₁ u
    rw [hβapp, hαu]
  obtain ⟨g, hgV, hg⟩ := psl2p_aut_conj_of_fixes_kleinFour hp7 hF V hV β hβV
  obtain ⟨g₀, hg₀, rfl⟩ := hgV
  have hg₀U : (g₀ : G) ∈ U := Subgroup.mem_subgroupOf.mp hg₀
  have hαk : ∀ k : ↥K, α k = g₀ * k * g₀⁻¹ := by
    intro k
    apply e₁.injective
    rw [← hβapp, hg]
    simp [MulAut.conj_apply]
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hLN hcL
  have hm : c⁻¹ * (g₀ : G) * c ∈ K := conj_mem_of_normalizer hcN g₀
  have hcent : (c⁻¹ * (g₀ : G) * c) = g₀ := by
    set m : ↥K := ⟨c⁻¹ * (g₀ : G) * c, hm⟩ with hmdef
    have hh : (g₀⁻¹ * m : ↥K) = 1 := by
      have hc1 : ∀ k : ↥K, (g₀⁻¹ * m) * k = k * (g₀⁻¹ * m) := by
        intro k
        let k₁ : ↥K := ⟨c * (k : G) * c⁻¹, by
          have := conj_mem_of_normalizer (inv_mem_normalizer' hcN) k
          simpa using this⟩
        have hk₁ : conjAutK c hcN k₁ = k := by
          apply Subtype.ext
          show c⁻¹ * (c * (k : G) * c⁻¹) * c = k
          group
        have h1 := hαc c hcL hcN k₁
        rw [hk₁, hαk, hαk] at h1
        have h2 := congrArg Subtype.val h1
        have h3 : (g₀ : G) * (k : G) * (g₀ : G)⁻¹ =
            c⁻¹ * ((g₀ : G) * (c * (k : G) * c⁻¹) * (g₀ : G)⁻¹) * c := h2
        apply Subtype.ext
        show (g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) * (k : G) =
          (k : G) * ((g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c))
        have h4 : (g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) * (k : G) * ((c⁻¹ * (g₀ : G) * c)⁻¹ * g₀) =
            (k : G) := by
          calc (g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) * (k : G) * ((c⁻¹ * (g₀ : G) * c)⁻¹ * g₀) =
              (g₀ : G)⁻¹ * ((c⁻¹ * (g₀ : G) * c) * (k : G) * (c⁻¹ * (g₀ : G) * c)⁻¹) * g₀ := by
                group
            _ = (g₀ : G)⁻¹ * ((g₀ : G) * (k : G) * (g₀ : G)⁻¹) * g₀ := by
                rw [h3]
                group
            _ = k := by group
        calc (g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) * (k : G) =
            ((g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) * (k : G) * ((c⁻¹ * (g₀ : G) * c)⁻¹ * g₀)) *
              ((g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c)) := by group
          _ = (k : G) * ((g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c)) := by rw [h4]
      have hz : (g₀⁻¹ * m : ↥K) = 1 := by
        apply Subtype.ext
        refine hZK ((g₀⁻¹ * m : ↥K) : G) (g₀⁻¹ * m).2 (fun k' hk' => ?_)
        exact congrArg Subtype.val (hc1 ⟨k', hk'⟩)
      exact hz
    have := congrArg Subtype.val hh
    have h5 : (g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c) = 1 := this
    calc c⁻¹ * (g₀ : G) * c = (g₀ : G) * ((g₀ : G)⁻¹ * (c⁻¹ * (g₀ : G) * c)) := by group
      _ = g₀ := by rw [h5, mul_one]
  have hcomm' : c * (g₀ : G) * c⁻¹ = (g₀ : G) := by
    calc c * (g₀ : G) * c⁻¹ = c * (c⁻¹ * (g₀ : G) * c) * c⁻¹ := by rw [hcent]
      _ = (g₀ : G) := by group
  have hg₀1 : (g₀ : G) = 1 := by
    by_contra hne
    exact hcfp _ hg₀U hne hcomm'
  intro k
  rw [hαk k]
  have : g₀ = 1 := Subtype.ext hg₀1
  rw [this]
  simp

theorem exists_noncomm_of_simple_card {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := fun a b => h a b }
  exact hQ IsSimpleGroup.prime_card

theorem two_pow_eight_dvd_cover
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hcov : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      Subgroup.center ↥K ≠ ⊥) : 2 ^ 8 ∣ Nat.card ↥K := by
  obtain ⟨⟨φ⟩, hc⟩ := hcov
  have hQcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 443520 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have hM22 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hfinM22 : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  have hZM : ∀ q : CFSG.Blueprint.NativeSporadic.Carrier .M22,
      (∀ q', q * q' = q' * q) → q = 1 := by
    intro q hq
    have hmem : q ∈ Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      Subgroup.mem_center_iff.mpr fun g => (hq g).symm
    rcases hM22.eq_bot_or_eq_top_of_normal
      (Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22)) with h | h
    · rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_noncomm_of_simple_card
        (Q := CFSG.Blueprint.NativeSporadic.Carrier .M22)
        (by rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 from
          CFSG.Sporadic.Mathieu.card_M22]; norm_num)
      have : a ∈ Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
        rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)
  have hZN : Subgroup.center ↥K ≤ CFSG.pCore 2 ↥K := by
    intro x hx
    have h1 : φ (QuotientGroup.mk x) = 1 := by
      refine hZM _ (fun q' => ?_)
      obtain ⟨y, rfl⟩ := φ.surjective q'
      rw [← map_mul, ← map_mul]
      congr 1
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hx y').symm]
    have h2 : (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
      φ.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hNbot : CFSG.pCore 2 ↥K ≠ ⊥ := by
    intro hN
    apply hc
    rw [eq_bot_iff]
    intro x hx
    have := hZN hx
    rw [hN] at this
    exact this
  have hN2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
  have hNcard : 2 ∣ Nat.card ↥(CFSG.pCore 2 ↥K) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hNbot
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact hn
    rw [hn]
    exact dvd_pow_self 2 hn0
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hQcard]
  have h7 : 2 ^ 7 ∣ 443520 := by norm_num
  have : 2 ^ 8 = 2 ^ 7 * 2 := by norm_num
  rw [this]
  exact mul_dvd_mul h7 hNcard

end CFSG.QuasithinUnique.A5
