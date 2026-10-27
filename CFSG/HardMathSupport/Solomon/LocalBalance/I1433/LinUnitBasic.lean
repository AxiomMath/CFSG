module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SimpleCfg
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

structure CoreCfg {P : Type} [Group P] (a b : MulAut P) (x : P) (J : Subgroup P) : Prop where
  comm : a * b * a⁻¹ * b⁻¹ = MulAut.conj x
  a_mem : a ∈ commutator (MulAut P)
  b_mem : b ∈ commutator (MulAut P)
  order : orderOf x = 3
  comp : GLAPComponent 3 (Subgroup.centralizer ({x} : Set P)) J
  mem : x ∈ J
  ord : (Nat.card J).factorization 3 = 3
  centralizes : ∀ L : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({x} : Set P)) L →
    ∀ l ∈ L, a l = l ∧ b l = l

theorem eq_of_perfect_of_central {G : Type*} [Group G] (F : Subgroup G) (hF : ⁅F, F⁆ = F)
    (φ : MulAut G) (h : ∀ f ∈ F, f⁻¹ * φ f ∈ Subgroup.center G) : ∀ f ∈ F, φ f = f := by
  let z : F →* Subgroup.center G :=
    { toFun := fun f => ⟨(f : G)⁻¹ * φ f, h f f.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun f g => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (h f f.2) ((g : G)⁻¹)
        change ((f * g : F) : G)⁻¹ * φ ((f * g : F) : G) =
          ((f : G)⁻¹ * φ f) * ((g : G)⁻¹ * φ g)
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc (g : G)⁻¹ * (f : G)⁻¹ * (φ f * φ g)
            = (g : G)⁻¹ * ((f : G)⁻¹ * φ f) * φ g := by group
          _ = (((f : G)⁻¹ * φ f) * (g : G)⁻¹) * φ g := by rw [hc]
          _ = ((f : G)⁻¹ * φ f) * ((g : G)⁻¹ * φ g) := by group }
  haveI : Group.IsPerfect ↥F := Subgroup.isPerfect_iff.mpr hF
  have hle : commutator ↥F ≤ z.ker := Abelianization.commutator_subset_ker z
  rw [(inferInstance : Group.IsPerfect ↥F).commutator_eq_top] at hle
  intro f hf
  have h1 : z ⟨f, hf⟩ = 1 := hle (Subgroup.mem_top _)
  have h2 := congrArg Subtype.val h1
  change f⁻¹ * φ f = 1 at h2
  exact (inv_mul_eq_one.1 h2).symm

theorem fixSubgroup_conj_eq {P : Type*} [Group P] (x : P) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set P) := by
  ext g
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  show x * g * x⁻¹ = g ↔ g * x = x * g
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [h]
      _ = g := by group

theorem conj_injective_of_center_bot {P : Type*} [Group P] (hZ : Subgroup.center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hgZ : g ∈ Subgroup.center P := Subgroup.mem_center_iff.2 fun s => by
    have h1 := congrArg (fun φ : MulAut P => φ s) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc s * g = g * s * g⁻¹ * g := by rw [h1]
      _ = g * s := by group
  rw [hZ] at hgZ
  exact hgZ

variable {S : Type} [Group S] [Finite S] {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S}
  {q : ℕ}

theorem I1433SCfg.exists_comm_pair (c : I1433SCfg Q x J q) :
    ∃ a ∈ Q, ∃ b ∈ Q, a * b * a⁻¹ * b⁻¹ = MulAut.conj x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, b, hb, hab⟩ := c.nonabelian
  have hcen : Nat.card (Subgroup.center ↥Q) = 3 := by
    refine card_center_eq_three c.card fun h => hab ?_
    have h1 := congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩)
    exact h1
  have hquot : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)
    rw [c.card, hcen] at h
    omega
  have hcomm := IsPGroup.commutative_of_card_eq_prime_sq hquot
  set a' : ↥Q := ⟨a, ha⟩ with ha'
  set b' : ↥Q := ⟨b, hb⟩ with hb'
  have hw : a' * b' * a'⁻¹ * b'⁻¹ ∈ Subgroup.center ↥Q := by
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥Q)]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have := hcomm (QuotientGroup.mk a') (QuotientGroup.mk b')
    rw [this]
    group
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers (MulAut.conj x) := by
    rw [← c.center]
    exact ⟨a' * b' * a'⁻¹ * b'⁻¹, hw, rfl⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hx3 : MulAut.conj x ^ 3 = 1 := by
    rw [← map_pow, ← c.order, pow_orderOf_eq_one, map_one]
  have hne : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
    intro h1
    apply hab
    have : a * b = b * a := by
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    exact this
  have hx3z : MulAut.conj x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hx3
  have hmod : MulAut.conj x ^ i = MulAut.conj x ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul, hx3z, one_zpow, mul_one]
  have hr : 0 ≤ i % 3 ∧ i % 3 < 3 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    apply hne
    rw [← hi, hmod, h0, zpow_zero]
  · refine ⟨a, ha, b, hb, ?_⟩
    rw [← hi, hmod, h1, zpow_one]
  · refine ⟨b, hb, a, ha, ?_⟩
    have h3 : a * b * a⁻¹ * b⁻¹ = (MulAut.conj x)⁻¹ := by
      rw [← hi, hmod, h2]
      have : MulAut.conj x ^ (2 : ℤ) * MulAut.conj x = 1 := by
        rw [← zpow_add_one, show (2 : ℤ) + 1 = (3 : ℕ) by norm_num, zpow_natCast, hx3]
      exact eq_inv_of_mul_eq_one_left this
    have h4 : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
    rw [h4, h3, inv_inv]

section Transport

variable {P : Type} [Group P]

theorem congr_mem_commutator (e : S ≃* P) {α : MulAut S} (hα : α ∈ commutator (MulAut S)) :
    MulAut.congr e α ∈ commutator (MulAut P) := by
  have h := Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hα
  rw [commutator, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective] at h
  exact h

theorem map_centralizer_singleton_equiv (e : S ≃* P) (k : S) :
    (Subgroup.centralizer ({k} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set P) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hu
    have := congrArg e hu
    simpa using this
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa using hy

theorem glaPComponent_map_equiv (e : S ≃* P) {X L : Subgroup S} (h : GLAPComponent 3 X L) :
    GLAPComponent 3 (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  refine glaPComponent_map Nat.prime_three e.toMonoidHom ?_ h
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  rw [this, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

theorem I1433SCfg.coreCfg_of_mulEquiv (e : S ≃* P) (c : I1433SCfg Q x J q) :
    ∃ (a b : MulAut P) (J' : Subgroup P), CoreCfg a b (e x) J' := by
  haveI : Finite P := Finite.of_equiv S e.toEquiv
  obtain ⟨a, ha, b, hb, hab⟩ := c.exists_comm_pair
  have hconj : MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hcent : ∀ (L : Subgroup S), GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) L →
      ∀ α ∈ Q, ∀ l ∈ L.map e.toMonoidHom, MulAut.congr e α l = l := by
    intro L hL α hα l hl
    obtain ⟨l', hl', rfl⟩ := hl
    have := c.centralizes L hL α hα l' hl'
    simp [MulAut.congr_apply, this]
  refine ⟨MulAut.congr e a, MulAut.congr e b, J.map e.toMonoidHom, ?_⟩
  refine ⟨?_, congr_mem_commutator e (c.derived ha), congr_mem_commutator e (c.derived hb),
    ?_, ?_, ⟨x, c.mem, rfl⟩, ?_, ?_⟩
  · rw [← hconj, ← hab]
    simp only [map_mul, map_inv]
  · rw [MulEquiv.orderOf_eq]
    exact c.order
  · rw [← map_centralizer_singleton_equiv e x]
    exact glaPComponent_map_equiv e c.comp
  · rw [Subgroup.card_map_of_injective e.injective]
    exact c.ord
  · intro L' hL' l hl
    have hL : GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) (L'.map e.symm.toMonoidHom) := by
      have h1 := glaPComponent_map_equiv e.symm hL'
      rw [← map_centralizer_singleton_equiv e x] at h1
      rw [Subgroup.map_map] at h1
      have h2 : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id S := by ext; simp
      rw [h2, Subgroup.map_id] at h1
      exact h1
    have hmap : (L'.map e.symm.toMonoidHom).map e.toMonoidHom = L' := by
      rw [Subgroup.map_map]
      have h2 : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id P := by ext; simp
      rw [h2, Subgroup.map_id]
    have hl' : l ∈ (L'.map e.symm.toMonoidHom).map e.toMonoidHom := by rw [hmap]; exact hl
    exact ⟨hcent _ hL a ha l hl', hcent _ hL b hb l hl'⟩

end Transport

section CentralQuotient

variable {X T : Type*} [Group X] [Group T]

theorem normal_map_subgroupOf_map_aux (π : X →* T) {A L : Subgroup X}
    (hL : ∀ c ∈ A, ∀ g ∈ L, c * g * c⁻¹ ∈ L) :
    ((L.map π).subgroupOf (A.map π)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨c, hc, hcg⟩ := g.2
  refine ⟨c * f * c⁻¹, hL c hc f hf, ?_⟩
  simp only [map_mul, map_inv, hcg, hfx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem not_le_ker_of_isQuasisimple_aux (π : X →* T) (hker : π.ker ≤ Subgroup.center X)
    {K : Subgroup X} (hK : CFSG.IsQuasisimple K) : ¬ K ≤ π.ker := by
  intro hKπ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hKπ x.2)) y).symm

theorem isComponentOf_map_fixSubgroup_aux (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {F : Subgroup X} (hFα : F ≤ fixSubgroup α)
    (hFn : ∀ c ∈ fixSubgroup α, ∀ g ∈ F, c * g * c⁻¹ ∈ F) (hFq : CFSG.IsQuasisimple F) :
    IsComponentOf (F.map π) (fixSubgroup β) := by
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β := map_fixSubgroup_le π hker α β hαβ
  haveI hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    normal_map_fixSubgroup π hker α β hαβ hπ
  haveI : ((F.map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    normal_map_subgroupOf_map_aux π hFn
  exact LieSemisimple.isComponentOf_of_normal_normal (Subgroup.map_mono hFα) hNC inferInstance hNn
    (CFSG.LocalCores.isQuasisimple_map hFq π (not_le_ker_of_isQuasisimple_aux π hker hFq))

end CentralQuotient

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
