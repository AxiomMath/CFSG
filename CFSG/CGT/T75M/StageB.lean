module

public import CFSG.CGT.T75M.StrongNormal
public import CFSG.CGT.T75M.StageA3
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

section Quotient

variable {K : Type} [Group K] [Finite K]

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {E : Subgroup G} (K : Subgroup G)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem exists_mul_of_conj_of_strongly_closed
    (hAsc : AschbacherNoPolarInput) {N B : Subgroup K} [N.Normal] (hB : IsElemAbelian 2 B)
    (hN : IsElemAbelian 2 N) (hBN : ∀ x ∈ B, x ∈ N → x = 1)
    (hfaith : ∀ b ∈ B, (∀ n ∈ N, b * n = n * b) → b = 1)
    (hsc : ∀ t ∈ B, t ≠ 1 → ∀ x ∈ B, ∀ g : K, ⁅g⁻¹ * x * g, t⁆ ∈ N →
      ∃ b ∈ B, ∃ n ∈ N, g⁻¹ * x * g = b * n)
    (h4 : 4 ≤ Nat.card B) (hlt : Nat.card N < Nat.card B ^ 2) :
    ∀ g : K, ∀ x ∈ B, ∃ b ∈ B, ∃ n ∈ N, g * x * g⁻¹ = b * n := by
  classical
  let π : K →* K ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (K ⧸ N) := B.map π
  have hAmem : ∀ z, z ∈ A ↔ ∃ b ∈ B, π b = z := fun z => Subgroup.mem_map
  have hπN : ∀ n ∈ N, π n = 1 := fun n hn => (QuotientGroup.eq_one_iff n).2 hn
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨b₁, hb₁, h₁⟩ := (hAmem x.1).1 x.2
      obtain ⟨b₂, hb₂, h₂⟩ := (hAmem y.1).1 y.2
      show (x : K ⧸ N) * y = y * x
      rw [← h₁, ← h₂, ← map_mul, ← map_mul, elemAbelian_mul_comm hB hb₁ hb₂]
    · obtain ⟨b, hb, rfl⟩ := (hAmem z).1 hz
      rw [← map_pow, hB.2 b hb, map_one]
  have hstrong : StrongWC A := by
    refine ⟨hAel, fun t ht ht1 a ha gb hgb => ?_⟩
    obtain ⟨b, hb, rfl⟩ := (hAmem t).1 ht
    obtain ⟨x, hx, rfl⟩ := (hAmem a).1 ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have hb1 : b ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hcomm : ⁅g⁻¹ * x * g, b⁆ ∈ N := by
      have h1 : π ⁅g⁻¹ * x * g, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2
          (Subgroup.mem_centralizer_singleton_iff.1 hgb)
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨b', hb', n, hn, hxe⟩ := hsc b hb hb1 x hx g hcomm
    refine (hAmem _).2 ⟨b', hb', ?_⟩
    have e : (π g)⁻¹ * π x * π g = π (g⁻¹ * x * g) := by simp only [map_mul, map_inv]
    show π b' = (π g)⁻¹ * π x * π g
    rw [e, hxe, map_mul, hπN n hn, mul_one]
  have hcardA : Nat.card A = Nat.card B := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun b : ↥B => (⟨π b, Subgroup.mem_map_of_mem π b.2⟩ : ↥A)) ⟨?_, ?_⟩)
    · intro b₁ b₂ h
      have h1 : π b₁ = π b₂ := congrArg Subtype.val h
      have h2 : (b₁ : K)⁻¹ * b₂ ∈ N := QuotientGroup.eq.1 h1
      have h3 : (b₁ : K)⁻¹ * b₂ ∈ B := B.mul_mem (B.inv_mem b₁.2) b₂.2
      exact Subtype.ext (inv_mul_eq_one.1 (hBN _ h3 h2))
    · rintro ⟨z, hz⟩
      obtain ⟨b, hb, rfl⟩ := (hAmem z).1 hz
      exact ⟨⟨b, hb⟩, rfl⟩
  have hconjN : ∀ n ∈ N, (MulAut.conjNormal n : MulAut ↥N) = 1 := fun n hn =>
    MulEquiv.ext fun m => Subtype.ext (by
      show n * (m : K) * n⁻¹ = m
      rw [elemAbelian_mul_comm hN hn m.2, mul_inv_cancel_right])
  let ρ : K ⧸ N →* MulAut ↥N := QuotientGroup.lift N MulAut.conjNormal hconjN
  have hρ : ∀ z ∈ A, ρ z = 1 → z = 1 := by
    intro z hz hρz
    obtain ⟨b, hb, rfl⟩ := (hAmem z).1 hz
    have h1 : ρ (π b) = MulAut.conjNormal b := QuotientGroup.lift_mk _ _ _
    rw [h1] at hρz
    have hb1 : b = 1 := hfaith b hb (fun n hn => by
      have h2 := congrArg (fun σ : MulAut ↥N => ((σ ⟨n, hn⟩ : ↥N) : K)) hρz
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc b * n = b * n * b⁻¹ * b := by group
        _ = n * b := by rw [h2])
    rw [hb1, map_one]
  obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥N = 2 ^ d := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (isPGroup_two_of_isElemAbelian hN).exists_card_eq
  have hnorm := normal_of_strongly_closed hAsc ρ hstrong (by rw [hcardA]; exact h4) hρ hd
    (by rw [hcardA]; exact hlt)
  intro g x hx
  have hgA : conjSubgroup (π g) A = A := hnorm (π g)
  have hmem : π (g * x * g⁻¹) ∈ A := by
    have h1 : π (g * x * g⁻¹) ∈ conjSubgroup (π g) A := by
      rw [mem_conjSubgroup]
      have e : (π g)⁻¹ * π (g * x * g⁻¹) * π g = π x := by
        simp only [map_mul, map_inv]; group
      rw [e]
      exact (hAmem _).2 ⟨x, hx, rfl⟩
    rwa [hgA] at h1
  obtain ⟨b, hb, hb'⟩ := (hAmem _).1 hmem
  have hn : b⁻¹ * (g * x * g⁻¹) ∈ N := QuotientGroup.eq.1 hb'
  exact ⟨b, hb, b⁻¹ * (g * x * g⁻¹), hn, by group⟩

end Quotient

section Concrete

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G} {a : ℕ}

theorem eq_one_of_mem_normIn_of_comm (hS : Sec3 T T₁) {x : G} (hx : x ∈ normIn T₁ T)
    (hc : ∀ τ ∈ T, x * τ = τ * x) : x = 1 := by
  obtain ⟨t, htT, htM⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
  have hxL : x ∈ normIn T T₁ := by
    rw [← hS.cfg.cfgM_inf_centralizer htT htM]
    exact Subgroup.mem_inf.2 ⟨Cfg.normIn_le_cfgM_right T T₁ hx,
      Subgroup.mem_centralizer_singleton_iff.2 (hc t htT)⟩
  have h : x ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨normIn_le _ _ hxL, normIn_le _ _ hx⟩
  rw [hS.cfg.inf, Subgroup.mem_bot] at h
  exact h

theorem conj_normIn_le_sup (hAsc : AschbacherNoPolarInput)
    (hKL : SzTriangleInput) [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hD : SzData T T₁ a) {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup h (normIn T₁ T) ≤ normIn T₁ T ⊔ T := by
  classical
  have hS := hD.sec3
  have hcfg := hS.cfg
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = Subgroup.normalizer (T : Set G) := ⟨_, rfl⟩
  have hTK : T ≤ K := hK ▸ Subgroup.le_normalizer
  have hL₁K : normIn T₁ T ≤ K := fun x hx => hK ▸ (mem_normIn.1 hx).2
  have hNn : (T.subgroupOf K).Normal := by rw [hK]; exact Subgroup.normal_in_normalizer
  have hLcard : 2 ^ (2 * (2 * a + 1)) ≤ Nat.card (normIn T T₁) := hD.two_pow_le_card_normIn
  have hqL : 2 ^ (2 * a + 1) < Nat.card (normIn T T₁) :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hLcard
  have hBcard : Nat.card ((normIn T₁ T).subgroupOf K) = Nat.card (normIn T T₁) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁K).toEquiv, card_normIn_right hS]
  have hNcard : Nat.card (T.subgroupOf K) = Nat.card (normIn T T₁) * 2 ^ (2 * a + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hD.card_eq_mul]
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have key := exists_mul_of_conj_of_strongly_closed hAsc
    (N := T.subgroupOf K) (B := (normIn T₁ T).subgroupOf K)
    (isElemAbelian_subgroupOf K (isElemAbelian_of_le' hcfg.wc₁.1 (normIn_le T₁ T)))
    (isElemAbelian_subgroupOf K hcfg.wc.1)
    (fun x hxB hxN => by
      have h1 : (x : G) ∈ T ⊓ T₁ := Subgroup.mem_inf.2
        ⟨Subgroup.mem_subgroupOf.1 hxN, normIn_le _ _ (Subgroup.mem_subgroupOf.1 hxB)⟩
      rw [hcfg.inf, Subgroup.mem_bot] at h1
      exact Subtype.ext h1)
    (fun b hb hc => Subtype.ext (eq_one_of_mem_normIn_of_comm hS (Subgroup.mem_subgroupOf.1 hb)
      (fun τ hτ => congrArg Subtype.val (hc ⟨τ, hTK hτ⟩ (Subgroup.mem_subgroupOf.2 hτ)))))
    (fun t ht ht1 x hx g hg => by
      have hg' : (g : G)⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
        hK ▸ (K.inv_mem g.2)
      have hc : ⁅(g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹, (t : G)⁆ ∈ T := by
        rw [inv_inv]
        exact Subgroup.mem_subgroupOf.1 hg
      have hmem := strongly_closed_L₁ hKL hnab hD hg' (Subgroup.mem_subgroupOf.1 hx)
        (Subgroup.mem_subgroupOf.1 ht) (fun h1 => ht1 (Subtype.ext h1)) hc
      rw [inv_inv] at hmem
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T
        (fun y hy => (mem_normIn.1 hy).2)
      rw [← SetLike.mem_coe, hset] at hmem
      obtain ⟨l, hl, τ, hτ, hlτ⟩ := Set.mem_mul.1 hmem
      exact ⟨⟨l, hL₁K hl⟩, Subgroup.mem_subgroupOf.2 hl, ⟨τ, hTK hτ⟩,
        Subgroup.mem_subgroupOf.2 hτ, Subtype.ext hlτ.symm⟩)
    (by
      rw [hBcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := hLcard)
    (by rw [hNcard, hBcard, sq]; exact Nat.mul_lt_mul_of_pos_left hqL hLpos)
  intro y hy
  have hhK : h ∈ K := hK ▸ hh
  have hx : h⁻¹ * y * h ∈ normIn T₁ T := mem_conjSubgroup.1 hy
  obtain ⟨b, hb, n, hn, hbn⟩ :=
    key ⟨h, hhK⟩ ⟨h⁻¹ * y * h, hL₁K hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  have h2 : h * (h⁻¹ * y * h) * h⁻¹ = (b : G) * n := congrArg Subtype.val hbn
  have h1 : y = (b : G) * n := by
    calc y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      _ = b * n := h2
  rw [h1]
  exact (normIn T₁ T ⊔ T).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hb))
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hn))

end Concrete

end CFSG.CGT.T75M
