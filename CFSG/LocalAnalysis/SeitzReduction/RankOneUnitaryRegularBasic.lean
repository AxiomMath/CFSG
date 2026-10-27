module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryPartition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAffinePerm

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint SzPartition

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem forall_exists_conj_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {n : G}
    (hn : n ∈ normalizer (szA L T t : Set G))
    (hnA₁ : n ∈ centralizer (szA₁ (szT₁ L T) : Set G)) (hnt : n * t * n⁻¹ ≠ t) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ m ∈ normalizer (szA L T t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), m * t * m⁻¹ = b * t := by
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨c, hc, hnc⟩ := hD.exists_conj_t_eq hn
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [one_mul] at hnc
    exact hnt hnc
  intro b hb
  by_cases hb1 : b = 1
  · exact ⟨1, one_mem _, by rw [hb1]; group⟩
  obtain ⟨x, hxN, hxt, hxc⟩ := hD.torus c hc b hb hc1 hb1
  have hxA : x ∈ normalizer (szA L T t : Set G) :=
    mem_normalizer_sup_zpowers hD.mem_centralizer hxN hxt
  refine ⟨x * n * x⁻¹, mem_inf.mpr ⟨mul_mem (mul_mem hxA hn) (inv_mem hxA),
    mem_centralizer_iff.mpr fun a ha => ?_⟩, ?_⟩
  · have ha' : x⁻¹ * a * x ∈ szA₁ (szT₁ L T) := by
      have := (mem_normalizer_iff.mp (inv_mem hxN) a).mp ha
      rwa [inv_inv] at this
    have hna : n * (x⁻¹ * a * x) = (x⁻¹ * a * x) * n :=
      (mem_centralizer_iff.mp hnA₁ _ ha').symm
    calc a * (x * n * x⁻¹) = x * ((x⁻¹ * a * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * a * x)) * x⁻¹ := by rw [hna]
      _ = x * n * x⁻¹ * a := by group
  · have hxt' : x⁻¹ * t * x = t := by
      calc x⁻¹ * t * x = x⁻¹ * (t * x) := by group
        _ = x⁻¹ * (x * t) := by rw [hxt]
        _ = t := by group
    calc x * n * x⁻¹ * t * (x * n * x⁻¹)⁻¹ = x * (n * (x⁻¹ * t * x) * n⁻¹) * x⁻¹ := by group
      _ = x * (c * t) * x⁻¹ := by rw [hxt', hnc]
      _ = x * c * x⁻¹ * (x * t * x⁻¹) := by group
      _ = b * t := by rw [hxc, hxt, mul_inv_cancel_right]

theorem hasRegularNormalSubgroup_of_forall_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∃ m ∈ normalizer (szA L T t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), m * t * m⁻¹ = b * t) :
    HasRegularNormalSubgroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range := by
  have hD := h.partitionData_of_card_sylow hS2
  set N := normalizer (szA L T t : Set G) with hN
  set Ch := normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G) with hCh
  set π := gmsRootConjugateAction (szA L T t) (zpowers t) with hπ
  have hconj : ∀ g ∈ N, ∀ m ∈ Ch, g * m * g⁻¹ ∈ Ch := by
    intro g hg m hm
    obtain ⟨hmN, hmC⟩ := mem_inf.mp hm
    refine mem_inf.mpr ⟨mul_mem (mul_mem hg hmN) (inv_mem hg),
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have hgA₁ := hD.normalizer_le hg
    have ha' : g⁻¹ * a * g ∈ szA₁ (szT₁ L T) := by
      have := (mem_normalizer_iff.mp (inv_mem hgA₁) a).mp ha
      rwa [inv_inv] at this
    have hma : m * (g⁻¹ * a * g) = (g⁻¹ * a * g) * m := (mem_centralizer_iff.mp hmC _ ha').symm
    calc a * (g * m * g⁻¹) = g * ((g⁻¹ * a * g) * m) * g⁻¹ := by group
      _ = g * (m * (g⁻¹ * a * g)) * g⁻¹ := by rw [hma]
      _ = g * m * g⁻¹ * a := by group
  have hfix : ∀ m : N, (m : G) ∈ Ch → ∀ b ∈ szA₁ (szT₁ L T),
      (zpowers (b * t)).map (MulAut.conj (m : G)).toMonoidHom = zpowers (b * t) → π m = 1 := by
    intro m hm b hb hmb
    obtain ⟨c, hc, hmc⟩ := hD.exists_conj_t_eq m.2
    have hmb' : (m : G) * b * (m : G)⁻¹ = b := by
      rw [(mem_centralizer_iff.mp (mem_inf.mp hm).2 b hb).symm, mul_inv_cancel_right]
    rw [SzPartitionData.map_conj_zpowers_mul hmc b, hmb'] at hmb
    have hc1 : b * c = b :=
      hD.eq_of_zpowers_eq (mul_mem hb hc) hb hmb
    have hc1' : c = 1 := by
      have := congrArg (fun x => b⁻¹ * x) hc1
      simpa using this
    rw [hc1', one_mul] at hmc
    rw [h.action_eq_one_iff_of_card_sylow hS2]
    refine mem_centralizer_iff.mpr fun x hx => ?_
    rcases SzPartition.mem_sup_zpowers_cases hD.mem_centralizer hD.sq_eq_one hx with
      hxA₁ | ⟨a, ha, rfl⟩
    · exact (mem_centralizer_iff.mp (mem_inf.mp hm).2 x hxA₁)
    · have hma : a * (m : G) = (m : G) * a := mem_centralizer_iff.mp (mem_inf.mp hm).2 a ha
      have hmt : (m : G) * t = t * m := by
        calc (m : G) * t = (m : G) * t * (m : G)⁻¹ * m := by group
          _ = t * m := by rw [hmc]
      calc a * t * (m : G) = a * (t * m) := by group
        _ = a * ((m : G) * t) := by rw [hmt]
        _ = (m : G) * (a * t) := by rw [← mul_assoc, hma]; group
  refine ⟨(Ch.subgroupOf N).map π, map_le_range π _, ⟨fun x hx g => ?_⟩, fun Q Z => ?_⟩
  · rw [mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n', hn'⟩ := g.2
    refine ⟨n' * m * n'⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hm
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact hconj _ n'.2 _ hm
    · simp only [map_mul, map_inv, hmx, hn', coe_mul, coe_inv]
  · obtain ⟨b, hb, hQ⟩ := hD.mem_iff.mp Q.2
    obtain ⟨b', hb', hZ⟩ := hD.mem_iff.mp Z.2
    obtain ⟨m, hm, hmt⟩ := htr (b⁻¹ * b') (mul_mem (inv_mem hb) hb')
    have hmN : m ∈ N := (mem_inf.mp hm).1
    have hmQ : π ⟨m, hmN⟩ Q = Z := by
      apply Subtype.ext
      change (Q : Subgroup G).map (MulAut.conj m).toMonoidHom = Z
      have hmb : m * b * m⁻¹ = b := by
        rw [(mem_centralizer_iff.mp (mem_inf.mp hm).2 b hb).symm, mul_inv_cancel_right]
      rw [hQ, SzPartitionData.map_conj_zpowers_mul hmt b, hmb, hZ]
      congr 1
      group
    refine ⟨⟨π ⟨m, hmN⟩, ⟨m, hmN⟩, mem_subgroupOf.mpr hm, rfl⟩, hmQ, ?_⟩
    rintro ⟨e, ⟨m', hm', rfl⟩⟩ he
    apply Subtype.ext
    change π m' = π ⟨m, hmN⟩
    have hm'C : (m' : G) ∈ Ch := mem_subgroupOf.mp hm'
    have hk : π (⟨m, hmN⟩⁻¹ * m') = 1 := by
      refine hfix _ ?_ b hb ?_
      · show m⁻¹ * (m' : G) ∈ Ch
        exact mul_mem (inv_mem hm) hm'C
      · have h1 : π (⟨m, hmN⟩⁻¹ * m') Q = Q := by
          rw [map_mul, Equiv.Perm.mul_apply, map_inv]
          change (π ⟨m, hmN⟩)⁻¹ ((π m') Q) = Q
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact (he.trans hmQ.symm)
        have h2 : ((π (⟨m, hmN⟩⁻¹ * m') Q : gmsRootConjugates (szA L T t) (zpowers t)) :
            Subgroup G) = (Q : Subgroup G) := congrArg Subtype.val h1
        change (Q : Subgroup G).map
          (MulAut.conj ((⟨m, hmN⟩⁻¹ * m' : N) : G)).toMonoidHom = (Q : Subgroup G) at h2
        rw [hQ] at h2
        exact h2
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk.symm

theorem exists_translation_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hE : HasRegularNormalSubgroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range) :
    ∃ n ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
      n * t * n⁻¹ ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨hNA₁, hΔ, -⟩ := h.partition_of_card_sylow hS2
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨E, hEN, hEn, hreg⟩ := hE
  set N := normalizer (szA L T t : Set G) with hN
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set π := gmsRootConjugateAction (szA L T t) (zpowers t) with hπ
  set R₀ : gmsRootConjugates (szA L T t) (zpowers t) := ⟨zpowers t, SzPartitionData.zpowers_mem⟩
    with hR₀
  have hEcard : Nat.card E = 2 ^ f := by
    have hbij : Function.Bijective (fun e : E => (e : Equiv.Perm _) R₀) := by
      refine ⟨fun e e' hee => ?_, fun Z => ?_⟩
      · obtain ⟨x, -, hxu⟩ := hreg R₀ ((e : Equiv.Perm _) R₀)
        exact (hxu e rfl).trans (hxu e' hee.symm).symm
      · obtain ⟨x, hx, -⟩ := hreg R₀ Z
        exact ⟨x, hx⟩
    rw [Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq, hΔ]
  have hEp : IsPGroup 2 E := IsPGroup.of_card hEcard
  set ψ : N →* MulAut A₁ := A₁.normalizerMonoidHom.comp (inclusion hNA₁) with hψ
  have hψa : ∀ (x : N) (a : A₁), ((ψ x a : A₁) : G) = (x : G) * a * (x : G)⁻¹ := fun x a => rfl
  set Γ : Subgroup (MulAut A₁) := (E.comap π).map ψ with hΓ
  have hΓp : IsPGroup 2 Γ := by
    rintro ⟨γ, x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hEp ⟨π x, hx⟩
    have hk' : π (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [h.action_eq_one_iff_of_card_sylow hS2] at hk'
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hψa, MulAut.one_apply, ← mem_centralizer_iff.mp hk' a (szA₁_le_szA L T t a.2),
      mul_inv_cancel_right]
  have h1fix : (1 : A₁) ∈ MulAction.fixedPoints Γ A₁ := fun γ => map_one (γ : MulAut A₁)
  have h2dvd : 2 ∣ Nat.card A₁ := by
    rw [hA₁card]
    exact dvd_pow_self 2 (by have := h.two_le; omega)
  obtain ⟨a, hafix, ha1⟩ := hΓp.exists_fixed_point_of_prime_dvd_card_of_fixed_point A₁ h2dvd h1fix
  have hafix' : ∀ x : N, π x ∈ E → (x : G) * a * (x : G)⁻¹ = a := by
    intro x hx
    have := hafix ⟨ψ x, x, hx, rfl⟩
    rw [← hψa]
    exact congrArg Subtype.val this
  have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1.symm)
  have hcen : ∀ x : N, π x ∈ E → ∀ b ∈ A₁, (x : G) * b * (x : G)⁻¹ = b := by
    intro x hx b hb
    by_cases hb1 : b = 1
    · rw [hb1]; group
    obtain ⟨y, hyN, hyt, hyb⟩ := hD.torus a a.2 b hb ha1' hb1
    have hyA : y ∈ N := mem_normalizer_sup_zpowers hD.mem_centralizer hyN hyt
    set y' : N := ⟨y, hyA⟩
    have hx' : π (y'⁻¹ * x * y') ∈ E := by
      have hmem : (⟨π x, x, rfl⟩ : π.range) ∈ E.subgroupOf π.range := mem_subgroupOf.mpr hx
      have := hEn.conj_mem _ hmem ⟨π y'⁻¹, y'⁻¹, rfl⟩
      rw [mem_subgroupOf] at this
      simpa [map_mul, map_inv] using this
    have h1 := hafix' _ hx'
    simp only [coe_mul, coe_inv, y'] at h1
    rw [← hyb]
    calc (x : G) * (y * a * y⁻¹) * (x : G)⁻¹ =
        y * ((y⁻¹ * x * y) * a * (y⁻¹ * x * y)⁻¹) * y⁻¹ := by group
      _ = y * a * y⁻¹ := by rw [h1]
  have haZ : zpowers ((a : G) * t) ∈ gmsRootConjugates (szA L T t) (zpowers t) :=
    hD.mem_iff.mpr ⟨a, a.2, rfl⟩
  obtain ⟨e, he, -⟩ := hreg R₀ ⟨_, haZ⟩
  obtain ⟨x, hx⟩ := hEN e.2
  have hxE : π x ∈ E := by rw [hx]; exact e.2
  obtain ⟨c, hc, hxc⟩ := hD.exists_conj_t_eq x.2
  refine ⟨x, mem_inf.mpr ⟨x.2, mem_centralizer_iff.mpr fun b hb => ?_⟩, ?_⟩
  · have := hcen x hxE b hb
    calc b * (x : G) = (x : G) * b * (x : G)⁻¹ * x := by rw [this]
      _ = (x : G) * b := by group
  · intro hxt
    have h2 : ((π x R₀ : gmsRootConjugates (szA L T t) (zpowers t)) : Subgroup G) =
        zpowers ((a : G) * t) := by
      rw [hx]
      exact congrArg Subtype.val he
    change (zpowers t).map (MulAut.conj (x : G)).toMonoidHom = _ at h2
    rw [map_conj_zpowers, hxt] at h2
    have h3 : (1 : G) = a := hD.eq_of_zpowers_eq (one_mem _) a.2 (by rw [one_mul]; exact h2)
    exact ha1' h3.symm

theorem hasRegularNormalSubgroup_iff_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    HasRegularNormalSubgroup (gmsRootConjugateAction (szA L T t) (zpowers t)).range ↔
      ∃ n ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
        n * t * n⁻¹ ≠ t := by
  refine ⟨h.exists_translation_of_card_sylow hS2, fun ⟨n, hn, hnt⟩ => ?_⟩
  exact h.hasRegularNormalSubgroup_of_forall_of_card_sylow hS2
    (h.forall_exists_conj_of_card_sylow hS2 (mem_inf.mp hn).1 (mem_inf.mp hn).2 hnt)

end U3Start

end CFSG.SeitzReduction.RankOne
