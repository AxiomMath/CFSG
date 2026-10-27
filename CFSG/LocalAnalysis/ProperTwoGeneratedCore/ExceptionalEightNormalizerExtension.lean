module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCentralSplitting

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

theorem exceptional_eight_involution_coset_normalizer_produces_full_linear_extension
    {G : Type*} [Group G] [Finite G] {u : G} (hu : orderOf u = 2)
    {U : Subgroup G} [IsElementaryAbelian 2 U] (hU8 : Nat.card U = 8)
    (hUu : U ≤ Subgroup.centralizer {u}) (huU : u ∉ U)
    {E N : Subgroup G} (hE : E = Subgroup.zpowers u ⊔ U)
    (hN : N = Subgroup.normalizer (u • (U : Set G)))
    (hcent : Subgroup.centralizer (u • (U : Set G)) = E)
    [(E.subgroupOf N).Normal] [IsSimpleGroup (N ⧸ E.subgroupOf N)]
    (hnonab : ∃ a b : N ⧸ E.subgroupOf N, a * b ≠ b * a)
    (hcard : Nat.card (N ⧸ E.subgroupOf N) = 168)
    (hconj : ∀ x ∈ u • (U : Set G), IsConj u x)
    (hno4 : ∀ x ∈ Subgroup.centralizer {u}, orderOf x ≠ 4) :
    (U ≤ N ∧ (U.subgroupOf N).Normal) ∧
    (Subgroup.centralizer (U : Set G) ⊓ N = E ∧
      ∀ σ : MulAut U, ∃ n ∈ N, ∀ x : U, ((σ x : U) : G) = n * x * n⁻¹) ∧
    (u ∈ N ∧ (∀ n ∈ N, n * u * n⁻¹ * u⁻¹ ∈ U) ∧ u ^ 2 ∈ U ∧ u ∉ U ∧
      ∀ x ∈ N, x ^ 2 ∉ u • (U : Set G)) ∧
    ∃ Y : Subgroup G, Y ≤ N ∧ (Y.subgroupOf N).Normal ∧ U ≤ Y ∧ E ⊓ Y = U ∧ E ⊔ Y = N ∧
      Y.relIndex N = 2 ∧ Subgroup.centralizer (U : Set G) ⊓ Y = U ∧
      (∀ σ : MulAut U, ∃ y ∈ Y, ∀ x : U, ((σ x : U) : G) = y * x * y⁻¹) ∧
      Nat.card Y = 1344 := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ : Set G := u • (U : Set G) with hΔdef
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have huu : u * u = 1 := by rw [← pow_two]; exact hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hcu : ∀ v ∈ U, v * u = u * v := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hUu hv)
  have hUc : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (mul_comm_of_isElementaryAbelian (⟨v, hv⟩ : U) ⟨w, hw⟩)
  have hmemΔ : ∀ x, x ∈ Δ ↔ ∃ v ∈ U, u * v = x := fun x => by
    simp only [hΔdef, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
  have huΔ : u ∈ Δ := (hmemΔ u).mpr ⟨1, U.one_mem, mul_one u⟩
  have hΔΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x * y ∈ U := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := (hmemΔ x).mp hx
    obtain ⟨w, hw, rfl⟩ := (hmemΔ y).mp hy
    have heq : u * v * (u * w) = v * w := by
      calc u * v * (u * w) = u * (v * u) * w := by group
        _ = u * (u * v) * w := by rw [hcu v hv]
        _ = v * w := by rw [← mul_assoc u u v, huu, one_mul]
    rw [heq]
    exact U.mul_mem hv hw
  have hmemN : ∀ g, g ∈ N ↔ ∀ h, h ∈ Δ ↔ g * h * g⁻¹ ∈ Δ := by
    intro g
    rw [hN]
    exact Iff.rfl
  have hcentN : Subgroup.centralizer Δ ≤ N := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    rw [hmemN]
    intro h
    constructor
    · intro hh
      rw [← hg h hh, mul_inv_cancel_right]
      exact hh
    · intro hh
      have := hg _ hh
      have heq : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [this]
          _ = g * h * g⁻¹ := by group
      rw [heq]
      exact hh
  have hEN : E ≤ N := hcent ▸ hcentN
  have hUE : U ≤ E := by
    rw [← hcent]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨w, hw, rfl⟩ := (hmemΔ h).mp hh
    calc u * w * v = u * (v * w) := by rw [mul_assoc, hUc w hw v hv]
      _ = (u * v) * w := by rw [mul_assoc]
      _ = v * (u * w) := by rw [← hcu v hv, mul_assoc]
  have huE : u ∈ E := by
    rw [← hcent]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨w, hw, rfl⟩ := (hmemΔ h).mp hh
    rw [mul_assoc, hcu w hw]
  have hUN : U ≤ N := hUE.trans hEN
  have huN : u ∈ N := hEN huE
  have hNU : ∀ n ∈ N, ∀ v ∈ U, n * v * n⁻¹ ∈ U := by
    intro n hn v hv
    have h1 : n * u * n⁻¹ ∈ Δ := ((hmemN n).mp hn u).mp huΔ
    have h2 : n * (u * v) * n⁻¹ ∈ Δ :=
      ((hmemN n).mp hn _).mp ((hmemΔ _).mpr ⟨v, hv, rfl⟩)
    have h3 := hΔΔ _ h1 _ h2
    have heq : n * u * n⁻¹ * (n * (u * v) * n⁻¹) = n * v * n⁻¹ := by
      calc n * u * n⁻¹ * (n * (u * v) * n⁻¹) = n * (u * u) * v * n⁻¹ := by group
        _ = n * v * n⁻¹ := by rw [huu, mul_one]
    rwa [heq] at h3
  have hNnorm : N ≤ Subgroup.normalizer (U : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hNU n hn h hh, fun hh => ?_⟩
    have := hNU n⁻¹ (N.inv_mem hn) _ hh
    rwa [show n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h by group] at this
  have hEcU : E ≤ Subgroup.centralizer (U : Set G) := by
    rw [hE]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcu v hv
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hUc w hw v hv
  have hK : Subgroup.centralizer (U : Set G) ⊓ N = E := by
    refine le_antisymm ?_ (le_inf hEcU hEN)
    set K := Subgroup.centralizer (U : Set G) ⊓ N with hKdef
    have hwK : ∀ k ∈ K, u⁻¹ * (k * u * k⁻¹) ∈ U := by
      intro k hk
      obtain ⟨w, hw, hw'⟩ := (hmemΔ _).mp (((hmemN k).mp hk.2 u).mp huΔ)
      rw [← hw', ← mul_assoc, inv_mul_cancel, one_mul]
      exact hw
    have hcK : ∀ k ∈ K, ∀ v ∈ U, k * v * k⁻¹ = v := by
      intro k hk v hv
      rw [← (Subgroup.mem_centralizer_iff.mp hk.1) v hv, mul_inv_cancel_right]
    let vK : K →* U :=
      { toFun := fun k => ⟨u⁻¹ * ((k : G) * u * (k : G)⁻¹), hwK k k.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          change u⁻¹ * ((a : G) * b * u * ((a : G) * b)⁻¹) =
            u⁻¹ * ((a : G) * u * (a : G)⁻¹) * (u⁻¹ * ((b : G) * u * (b : G)⁻¹))
          have hca := hcK a a.2 _ (hwK b b.2)
          calc u⁻¹ * ((a : G) * b * u * ((a : G) * b)⁻¹)
              = u⁻¹ * ((a : G) * u * (a : G)⁻¹) *
                  ((a : G) * (u⁻¹ * ((b : G) * u * (b : G)⁻¹)) * (a : G)⁻¹) := by group
            _ = u⁻¹ * ((a : G) * u * (a : G)⁻¹) * (u⁻¹ * ((b : G) * u * (b : G)⁻¹)) := by
              rw [hca] }
    have hvK : ∀ k : K, ((vK k : U) : G) = u⁻¹ * ((k : G) * u * (k : G)⁻¹) := fun _ => rfl
    have hkerE : ∀ k : K, vK k = 1 → (k : G) ∈ E := by
      intro k hk
      have hku : (k : G) * u * (k : G)⁻¹ = u := by
        have := congrArg Subtype.val hk
        rw [hvK, OneMemClass.coe_one] at this
        exact (inv_mul_eq_one.mp this).symm
      rw [← hcent, Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨w, hw, rfl⟩ := (hmemΔ h).mp hh
      have hkw := hcK k k.2 w hw
      calc u * w * (k : G) = u * ((k : G) * w * (k : G)⁻¹) * (k : G) := by rw [hkw]
        _ = ((k : G) * u * (k : G)⁻¹) * ((k : G) * w) := by rw [hku]; group
        _ = (k : G) * (u * w) := by group
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ E := by
      intro a ha b hb
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      refine hkerE ⟨_, hmem⟩ ?_
      have heq : (⟨a * b * a⁻¹ * b⁻¹, hmem⟩ : K) =
          (⟨a, ha⟩ : K) * ⟨b, hb⟩ * (⟨a, ha⟩ : K)⁻¹ * (⟨b, hb⟩ : K)⁻¹ := rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm_of_isElementaryAbelian (vK ⟨a, ha⟩) (vK ⟨b, hb⟩)]
      group
    let K' : Subgroup N := K.subgroupOf N
    have hK'normal : K'.Normal := by
      refine ⟨fun k hk n => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, (n * k * n⁻¹).2⟩
      have hv' : (n : G)⁻¹ * v * n ∈ U := by
        have := hNU (n : G)⁻¹ (N.inv_mem n.2) v hv
        rwa [inv_inv] at this
      have hkv := hcK k hk _ hv'
      change v * ((n : G) * k * (n : G)⁻¹) = (n : G) * k * (n : G)⁻¹ * v
      calc v * ((n : G) * k * (n : G)⁻¹)
          = (n : G) * ((n : G)⁻¹ * v * n) * k * (n : G)⁻¹ := by group
        _ = (n : G) * ((k : G) * ((n : G)⁻¹ * v * n) * (k : G)⁻¹) * k * (n : G)⁻¹ := by
          rw [hkv]
        _ = (n : G) * k * (n : G)⁻¹ * v := by group
    have hMnormal : (K'.map (QuotientGroup.mk' (E.subgroupOf N))).Normal :=
      hK'normal.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (K'.map (QuotientGroup.mk' (E.subgroupOf N))) with hbot | htop
    · intro k hk
      have hkN : k ∈ N := hk.2
      have hmem : (⟨k, hkN⟩ : N) ∈ K' := by
        rw [Subgroup.mem_subgroupOf]
        exact hk
      have himg : QuotientGroup.mk' (E.subgroupOf N) ⟨k, hkN⟩ ∈
          K'.map (QuotientGroup.mk' (E.subgroupOf N)) := Subgroup.mem_map_of_mem _ hmem
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at himg
      exact himg
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ K'.map (QuotientGroup.mk' (E.subgroupOf N)) := by
        rw [htop]
        exact Subgroup.mem_top a
      have hb : b ∈ K'.map (QuotientGroup.mk' (E.subgroupOf N)) := by
        rw [htop]
        exact Subgroup.mem_top b
      obtain ⟨k₁, hk₁, rfl⟩ := ha
      obtain ⟨k₂, hk₂, rfl⟩ := hb
      apply hab
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hk₁' : (k₁ : G) ∈ K := hk₁
      have hk₂' : (k₂ : G) ∈ K := hk₂
      have h := hcomm _ (K.inv_mem hk₂') _ (K.inv_mem hk₁')
      rw [inv_inv, inv_inv] at h
      have heq : (((k₁ * k₂)⁻¹ * (k₂ * k₁) : N) : G) =
          (k₂ : G)⁻¹ * (k₁ : G)⁻¹ * k₂ * k₁ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
      rw [heq]
      exact h
  let ψ : N →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hNnorm)
  have hψ : ∀ (n : N) (x : U), ((ψ n x : U) : G) = n * x * (n : G)⁻¹ := fun n x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U _ x
  have hψker : ψ.ker = E.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hK]
    constructor
    · intro h1
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, n.2⟩
      have h2 := congrArg (fun σ : MulAut U => ((σ ⟨v, hv⟩ : U) : G)) h1
      simp only [hψ, MulAut.one_apply] at h2
      calc v * (n : G) = (n : G) * v * (n : G)⁻¹ * n := by rw [h2]
        _ = (n : G) * v := by group
    · rintro ⟨hc, -⟩
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [hψ, MulAut.one_apply, ← (Subgroup.mem_centralizer_iff.mp hc) x x.2,
        mul_inv_cancel_right]
  have : Finite (MulAut U) := Finite.of_injective (fun σ : MulAut U => (σ : U → U))
    (fun σ τ h => MulEquiv.ext (congrFun h))
  have hψsurj : Function.Surjective ψ := by
    have hcardRange : Nat.card ψ.range = 168 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, ← hcard]
      exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hψker).toEquiv
    have htop := Subgroup.eq_top_of_card_eq ψ.range
      (by rw [hcardRange, card_mulAut_eq_168 hU8])
    exact MonoidHom.range_eq_top.mp htop
  have hfullN : ∀ σ : MulAut U, ∃ n ∈ N, ∀ x : U, ((σ x : U) : G) = n * x * n⁻¹ := by
    intro σ
    obtain ⟨n, rfl⟩ := hψsurj σ
    exact ⟨n, n.2, fun x => hψ n x⟩
  have hcentral : ∀ n ∈ N, n * u * n⁻¹ * u⁻¹ ∈ U := by
    intro n hn
    obtain ⟨w, hw, hw'⟩ := (hmemΔ _).mp (((hmemN n).mp hn u).mp huΔ)
    rw [← hw', huinv, mul_assoc, hcu w hw, ← mul_assoc, huu, one_mul]
    exact hw
  have hnotsq : ∀ x ∈ N, x ^ 2 ∉ u • (U : Set G) := by
    intro x _ hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (hconj _ hx)
    have hy2 : (g⁻¹ * x * g) ^ 2 = u := by
      rw [pow_two, show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * x ^ 2 * g by rw [pow_two]; group,
        ← hg]
      group
    have hyc : g⁻¹ * x * g ∈ Subgroup.centralizer {u} := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hy2, pow_two]
      group
    have hy4 : orderOf (g⁻¹ * x * g) = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g⁻¹ * x * g)
        (by
          rw [pow_one, hy2]
          intro h1
          rw [h1, orderOf_one] at hu
          exact absurd hu (by decide))
        (by rw [show 2 ^ (1 + 1) = 2 * 2 by rfl, pow_mul, hy2, hu2])
      simpa using h
    exact hno4 _ hyc hy4
  refine ⟨⟨hUN, ⟨fun n hn g => ?_⟩⟩, ⟨hK, hfullN⟩, ⟨huN, hcentral, by rw [hu2]; exact U.one_mem,
    huU, hnotsq⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNU g g.2 n hn
  let U' : Subgroup N := U.subgroupOf N
  have hU'normal : U'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNU g g.2 n hn⟩
  let uN : N := ⟨u, huN⟩
  let c : N ⧸ U' := QuotientGroup.mk uN
  have hcJ : c ∈ Subgroup.center (N ⧸ U') := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 := hcentral _ (N.inv_mem n.2)
    have h2 := hNU u⁻¹ (N.inv_mem huN) _ h1
    have heq : (((n * uN)⁻¹ * (uN * n) : N) : G) =
        u⁻¹ * ((n : G)⁻¹ * u * (n : G)⁻¹⁻¹ * u⁻¹) * u⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, uN]
      group
    rw [heq]
    exact h2
  have hc1 : c ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact huU h
  have hcsq : c ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change u ^ 2 ∈ U
    rw [hu2]
    exact U.one_mem
  have hc2 : orderOf c = 2 := orderOf_eq_prime hcsq hc1
  have hsqJ : ∀ x : N ⧸ U', x ^ 2 ≠ c := by
    intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx
    apply hnotsq n n.2
    rw [hmemΔ]
    refine ⟨u⁻¹ * (n : G) ^ 2, ?_, by group⟩
    have := U.inv_mem hx
    simpa [Subgroup.coe_pow, uN] using this
  have hZnormal : (Subgroup.zpowers c).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxc : x ∈ Subgroup.center (N ⧸ U') := Subgroup.zpowers_le.mpr hcJ hx
    rw [(Subgroup.mem_center_iff.mp hxc) g, mul_inv_cancel_right]
    exact hx
  have hU'ker : U' ≤ ψ.ker := by
    rw [hψker]
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact hUE hv
  let ψbar : N ⧸ U' →* MulAut U := QuotientGroup.lift U' ψ hU'ker
  have hψbar_surj : Function.Surjective ψbar := by
    intro σ
    obtain ⟨n, rfl⟩ := hψsurj σ
    exact ⟨QuotientGroup.mk n, rfl⟩
  have huNorm : Subgroup.zpowers u ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hNnorm huN
  have hEimage : (E.subgroupOf N).map (QuotientGroup.mk' U') = Subgroup.zpowers c := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      have he' : (e : G) ∈ ((Subgroup.zpowers u ⊔ U : Subgroup G) : Set G) := hE ▸ he
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ huNorm] at he'
      obtain ⟨a, ha, v, hv, hav⟩ := Set.mem_mul.mp he'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hvN : v ∈ N := hUN hv
      have hesplit : e = uN ^ k * ⟨v, hvN⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow, uN]
        exact hav.symm
      have hv1 : (QuotientGroup.mk (⟨v, hvN⟩ : N) : N ⧸ U') = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hv)
      rw [hesplit, map_mul, map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hv1,
        mul_one]
      exact Subgroup.zpow_mem_zpowers c k
    · rw [Subgroup.zpowers_le]
      exact ⟨uN, huE, rfl⟩
  have hψbar_ker : ψbar.ker = Subgroup.zpowers c := by
    rw [QuotientGroup.ker_lift, hψker, hEimage]
  let Θ : (N ⧸ U') ⧸ Subgroup.zpowers c ≃* MulAut U :=
    (QuotientGroup.quotientMulEquivOfEq hψbar_ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψbar hψbar_surj)
  have hcardJZ : Nat.card ((N ⧸ U') ⧸ Subgroup.zpowers c) = 168 := by
    rw [Nat.card_congr Θ.toEquiv, card_mulAut_eq_168 hU8]
  obtain ⟨P₀, ⟨e₀⟩⟩ := exists_dihedral_subgroup_mulAut (U := U) hU8
  let P : Subgroup ((N ⧸ U') ⧸ Subgroup.zpowers c) := P₀.map (Θ.symm : MulAut U →* _)
  let eP : P ≃* DihedralGroup 4 := (Θ.symm.subgroupMap P₀).symm.trans e₀
  have hPcard : Nat.card P = 8 := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hPcard]; norm_num)
  have hPindex : P.index = 21 := by
    have h := P.index_mul_card
    rw [hPcard, hcardJZ] at h
    omega
  have hPodd : ¬ 2 ∣ P.index := by rw [hPindex]; decide
  let S : Sylow 2 ((N ⧸ U') ⧸ Subgroup.zpowers c) := hPp.toSylow hPodd
  have hS : Nonempty ((S : Subgroup ((N ⧸ U') ⧸ Subgroup.zpowers c)) ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hPp hPodd)).trans eP⟩
  obtain ⟨D, hDnormal, hDcompl, -⟩ :=
    central_nonsquare_involution_dihedral_eight_sylow_quotient_splits hcJ hc2 hsqJ ⟨S, hS⟩
  let DY : Subgroup N := D.comap (QuotientGroup.mk' U')
  let Y : Subgroup G := DY.map N.subtype
  have hmemY : ∀ g : G, g ∈ Y ↔ ∃ h : g ∈ N, (QuotientGroup.mk ⟨g, h⟩ : N ⧸ U') ∈ D := by
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hD⟩
      exact ⟨⟨g, h⟩, hD, rfl⟩
  have hYN : Y ≤ N := Subgroup.map_subtype_le DY
  have hU'DY : U' ≤ DY := by
    intro v hv
    change QuotientGroup.mk v ∈ D
    rw [(QuotientGroup.eq_one_iff v).mpr hv]
    exact D.one_mem
  have hUY : U ≤ Y := by
    intro v hv
    refine (hmemY v).mpr ⟨hUN hv, ?_⟩
    exact hU'DY (by rw [Subgroup.mem_subgroupOf]; exact hv)
  have hYsub : Y.subgroupOf N = DY :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective DY
  have hYnormal : (Y.subgroupOf N).Normal := by
    rw [hYsub]
    exact hDnormal.comap _
  have hEY : E ⊓ Y = U := by
    refine le_antisymm ?_ (le_inf hUE hUY)
    rintro g ⟨hgE, hgY⟩
    obtain ⟨hgN, hgD⟩ := (hmemY g).mp hgY
    have hgZ : (QuotientGroup.mk ⟨g, hgN⟩ : N ⧸ U') ∈ Subgroup.zpowers c := by
      rw [← hEimage]
      exact ⟨⟨g, hgN⟩, hgE, rfl⟩
    have hbot := Subgroup.disjoint_def.mp hDcompl.disjoint hgZ hgD
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hbot
    exact hbot
  have hdecomp : ∀ n : N, ∃ e ∈ E, ∃ y ∈ Y, (n : G) = e * y := by
    intro n
    have hsup : (QuotientGroup.mk n : N ⧸ U') ∈ Subgroup.zpowers c ⊔ D := by
      rw [hDcompl.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨z, hz, d, hd, hzd⟩ := Subgroup.mem_sup_of_normal_left.mp hsup
    rw [← hEimage] at hz
    obtain ⟨e, he, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hzd
    have hw : (e * y)⁻¹ * n ∈ DY := hU'DY hzd
    have hyw : y * ((e * y)⁻¹ * n) ∈ DY := DY.mul_mem hd hw
    refine ⟨e, he, _, ⟨_, hyw, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hEYsup : E ⊔ Y = N := by
    refine le_antisymm (sup_le hEN hYN) ?_
    intro n hn
    obtain ⟨e, he, y, hy, hey⟩ := hdecomp ⟨n, hn⟩
    rw [show n = e * y from hey]
    exact Subgroup.mul_mem_sup he hy
  have hYindex : Y.relIndex N = 2 := by
    rw [Subgroup.relIndex, hYsub,
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U'),
      hDcompl.index_eq_card, Nat.card_zpowers, hc2]
  have hCY : Subgroup.centralizer (U : Set G) ⊓ Y = U := by
    refine le_antisymm ?_ (le_inf (fun v hv => Subgroup.mem_centralizer_iff.mpr
      fun w hw => hUc w hw v hv) hUY)
    rintro g ⟨hgc, hgY⟩
    rw [← hEY]
    exact ⟨hK ▸ ⟨hgc, hYN hgY⟩, hgY⟩
  have hfullY : ∀ σ : MulAut U, ∃ y ∈ Y, ∀ x : U, ((σ x : U) : G) = y * x * y⁻¹ := by
    intro σ
    obtain ⟨n, hn, hnσ⟩ := hfullN σ
    obtain ⟨e, he, y, hy, hey⟩ := hdecomp ⟨n, hn⟩
    refine ⟨y, hy, fun x => ?_⟩
    rw [hnσ x, show n = e * y from hey]
    have hyx : y * x * y⁻¹ ∈ U := hNU y (hYN hy) x x.2
    have hce := (Subgroup.mem_centralizer_iff.mp (hEcU he)) _ hyx
    calc e * y * (x : G) * (e * y)⁻¹ = (e * (y * x * y⁻¹)) * e⁻¹ := by group
      _ = (y * x * y⁻¹ * e) * e⁻¹ := by rw [hce]
      _ = y * x * y⁻¹ := by group
  refine ⟨Y, hYN, hYnormal, hUY, hEY, hEYsup, hYindex, hCY, hfullY, ?_⟩
  let ψY : Y →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion (hYN.trans hNnorm))
  have hψY : ∀ (y : Y) (x : U), ((ψY y x : U) : G) = y * x * (y : G)⁻¹ := fun y x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U _ x
  have hψYsurj : Function.Surjective ψY := by
    intro σ
    obtain ⟨y, hy, hyσ⟩ := hfullY σ
    refine ⟨⟨y, hy⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hψY, hyσ]
  have hψYker : ψY.ker = U.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      rw [← hCY]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, y.2⟩
      have h2 := congrArg (fun σ : MulAut U => ((σ ⟨v, hv⟩ : U) : G)) h1
      simp only [hψY, MulAut.one_apply] at h2
      calc v * (y : G) = (y : G) * v * (y : G)⁻¹ * y := by rw [h2]
        _ = (y : G) * v := by group
    · intro hyU
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [hψY, MulAut.one_apply, hUc _ hyU _ x.2, mul_inv_cancel_right]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψY.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψY hψYsurj).toEquiv,
    card_mulAut_eq_168 hU8, hψYker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv, hU8]

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
