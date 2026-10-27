module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnMain
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Pointwise

section RGD

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf_of_normal (A B : Subgroup X) [A.Normal] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h2 := Subgroup.relIndex_mul_card A B
  have h3 := Subgroup.relIndex_sup_right B A
  rw [inf_eq_left.2 le_sup_right, h3, sup_comm] at h1
  rw [← h1, ← h2]
  ring

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

theorem rgd2_card_sup_HU (R : RGD2 n H r₁ r₂ U root) :
    Nat.card ↥(H ⊔ U) = Nat.card H * Nat.card U := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : H × U => (⟨p.1 * p.2, ?_⟩ : ↥(H ⊔ U)))
    ⟨fun p p' hpp' => ?_, fun x => ?_⟩)
  · have : (p.1 : X) * p.2 ∈ ((H ⊔ U : Subgroup X) : Set X) := by
      rw [R.coe_sup_HU]
      exact Set.mul_mem_mul p.1.2 p.2.2
    exact this
  · have h := congrArg Subtype.val hpp'
    simp only at h
    have hmem : (p'.1 : X)⁻¹ * p.1 = p'.2 * (p.2 : X)⁻¹ := by
      calc (p'.1 : X)⁻¹ * p.1 = (p'.1 : X)⁻¹ * (p.1 * p.2) * (p.2 : X)⁻¹ := by group
        _ = (p'.1 : X)⁻¹ * (p'.1 * p'.2) * (p.2 : X)⁻¹ := by rw [h]
        _ = p'.2 * (p.2 : X)⁻¹ := by group
    have hUH : p'.2 * (p.2 : X)⁻¹ ∈ U ⊓ H := ⟨U.mul_mem p'.2.2 (U.inv_mem p.2.2),
      hmem ▸ H.mul_mem (H.inv_mem p'.1.2) p.1.2⟩
    rw [R.U_inf_H, Subgroup.mem_bot] at hUH
    have h2 : (p'.2 : X) = p.2 := mul_inv_eq_one.1 hUH
    have h1 : (p'.1 : X)⁻¹ * p.1 = 1 := by rw [hmem, hUH]
    have h1' : (p.1 : X) = p'.1 := by
      rw [← mul_right_inj (p'.1 : X)⁻¹, h1, inv_mul_cancel]
    exact Prod.ext (Subtype.ext h1') (Subtype.ext h2.symm)
  · have hx : (x : X) ∈ (H : Set X) * (U : Set X) := by
      rw [← R.coe_sup_HU]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem rgd2_eq_bot_of_normal_of_coprime [Finite X] (R : RGD2 n H r₁ r₂ U root)
    [(cartan (H ⊔ U) R.N).Normal] (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1) {r m : ℕ}
    (hX : r ^ m ∣ Nat.card X) (hB : ¬ r ^ m ∣ Nat.card ↥(H ⊔ U))
    (A : Subgroup X) [A.Normal] (hA : Nat.Coprime r (Nat.card A)) : A = ⊥ := by
  have hT := R.isTitsSystem hgen
  have hst : R.w₁ ≠ R.w₂ := R.weyl_ne
  have h3 := R.three_le
  have hcomm : R.w₁ * R.w₂ ≠ R.w₂ * R.w₁ := by
    intro hc
    have hw1 : R.w₁ * R.w₁ = 1 := by
      have := R.orderOf_w 0
      have h' := pow_orderOf_eq_one R.w₁
      rwa [show orderOf R.w₁ = 2 from this, sq] at h'
    have hw2 : R.w₂ * R.w₂ = 1 := by
      have := R.orderOf_w 1
      have h' := pow_orderOf_eq_one R.w₂
      rwa [show orderOf R.w₂ = 2 from this, sq] at h'
    have h2 : (R.w₁ * R.w₂) ^ 2 = 1 := by
      calc (R.w₁ * R.w₂) ^ 2 = R.w₁ * (R.w₂ * R.w₁) * R.w₂ := by rw [sq]; group
        _ = R.w₁ * (R.w₁ * R.w₂) * R.w₂ := by rw [← hc]
        _ = (R.w₁ * R.w₁) * (R.w₂ * R.w₂) := by group
        _ = 1 := by rw [hw1, hw2, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [R.orderOf_w₁_mul_w₂] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rcases rank_two_normal_sup_eq_top_or_le hT hst hcomm A with hAtop | hAB
  ·
    exfalso
    apply hB
    have hprod := card_sup_mul_card_inf_of_normal A (H ⊔ U)
    rw [hAtop, Subgroup.card_top] at hprod
    have h1 : r ^ m ∣ Nat.card A * Nat.card ↥(H ⊔ U) := by
      rw [← hprod]
      exact Dvd.dvd.mul_right hX _
    exact (Nat.Coprime.pow_left m hA).dvd_of_dvd_mul_left h1
  ·
    have hsat := R.isSaturated
    have hAH : A ≤ H := by
      intro a ha
      have : a ∈ (H ⊔ U) ⊓ R.N := by
        rw [IsSaturated] at hsat
        rw [hsat, Subgroup.mem_iInf]
        intro m
        refine ⟨(m : X) * a * (m : X)⁻¹, hAB ((inferInstance : A.Normal).conj_mem a ha m), ?_⟩
        simp [mul_assoc]
      rwa [R.B_inf_N] at this
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hC a (hAH ha) fun u hu => ?_
    have h1 : a * u * a⁻¹ ∈ U := R.conj_mem_U (hAH ha) hu
    have h2 : u * a⁻¹ * u⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) u
    have h3 : a * (u * a⁻¹ * u⁻¹) ∈ A := A.mul_mem ha h2
    have h4 : a * (u * a⁻¹ * u⁻¹) = (a * u * a⁻¹) * u⁻¹ := by group
    have h5 : (a * u * a⁻¹) * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have h6 : (a * u * a⁻¹) * u⁻¹ ∈ U ⊓ H := ⟨h5, hAH (h4 ▸ h3)⟩
    rw [R.U_inf_H, Subgroup.mem_bot] at h6
    have h7 : a * u * a⁻¹ = u := mul_inv_eq_one.1 h6
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h7]

end RGD

section Fold

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem foldData_eq_bot_of_normal_of_coprime [Finite X] (hf : FoldData R φ)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1) {r m : ℕ}
    (hXm : r ^ m ∣ Nat.card ↥(foldFix φ))
    (hBm : ¬ r ^ m ∣ Nat.card ↥(H ⊓ foldFix φ) * Nat.card ↥(U ⊓ foldFix φ))
    (A : Subgroup ↥(foldFix φ)) [A.Normal] (hA : Nat.Coprime r (Nat.card A)) : A = ⊥ := by
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hf.exists_rgd2
  have hr₁ : r₁' ∈ foldFix φ := h1
  have hr₂ : r₂' ∈ foldFix φ := h2
  have hroot : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have hgen'' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have R'' := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
  have := R''.cartan_normal
  refine rgd2_eq_bot_of_normal_of_coprime R'' hgen'' ?_ hXm ?_ A hA
  · intro t ht htc
    apply Subtype.ext
    exact hC t.1 ⟨(Subgroup.mem_subgroupOf.1 ht).1, t.2⟩ (fun u hu => by
      have := htc ⟨u, hu.2⟩ hu
      exact congrArg Subtype.val this)
  · rw [rgd2_card_sup_HU R'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : H ⊓ foldFix φ ≤ foldFix φ)).toEquiv, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ foldFix φ ≤ foldFix φ)).toEquiv]
    exact hBm

end Fold

section Cells

variable {G : Type*} [Group G]

theorem normalCore_eq_bot_of_cells (B U : Subgroup G)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) : B.normalCore = ⊥ := by
  have hKU : ∀ u ∈ U, u ∈ B.normalCore → u = 1 := fun u hu hK => hmeet u hu (hK c₀)
  refine eq_bot_iff.mpr fun k hk => ?_
  have hkB : k ∈ B := Subgroup.normalCore_le B hk
  have hcomm : ∀ u ∈ U, k * u = u * k := by
    intro u hu
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ B.normalCore := by
      have h2 : u * k⁻¹ * u⁻¹ ∈ B.normalCore :=
        (Subgroup.normalCore_normal B).conj_mem k⁻¹ (B.normalCore.inv_mem hk) u
      simpa [mul_assoc] using B.normalCore.mul_mem hk h2
    have h3 : k * u * k⁻¹ * u⁻¹ ∈ U := U.mul_mem (hUnorm k hkB u hu) (U.inv_mem hu)
    have h4 := hKU _ h3 h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  exact Subgroup.mem_bot.mpr (hKU k (hKC k hkB hcomm) hk)

theorem exists_mul_eq_of_cells_of_not_mem (B U : Subgroup G) (hUB : U ≤ B) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u) (A : Subgroup G) [A.Normal]
    {a : G} (haA : a ∈ A) (haB : a ∉ B) (g : G) : ∃ x ∈ A, ∃ y ∈ B, g = x * y := by
  by_cases hg : g ∈ B
  · exact ⟨1, A.one_mem, g, hg, (one_mul g).symm⟩
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := (hcell a).resolve_left haB
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := (hcell g).resolve_left hg
  refine ⟨(b₂ * b₁⁻¹) * (b₁ * c₀ * u₁) * (b₂ * b₁⁻¹)⁻¹, ‹A.Normal›.conj_mem _ haA _,
    (b₂ * b₁⁻¹) * (u₁⁻¹ * u₂), B.mul_mem (B.mul_mem hb₂ (B.inv_mem hb₁))
      (hUB (U.mul_mem (U.inv_mem hu₁) hu₂)), ?_⟩
  group

theorem eq_bot_of_cells_of_coprime [Finite G] (B U : Subgroup G) (hUB : U ≤ B)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) {r : ℕ} (hr : r ≠ 1)
    (hrB : r ∣ B.index) (A : Subgroup G) [A.Normal] (hA : Nat.Coprime r (Nat.card A)) :
    A = ⊥ := by
  by_cases hAB : A ≤ B
  · rw [eq_bot_iff, ← normalCore_eq_bot_of_cells B U hUnorm c₀ hmeet hKC]
    exact Subgroup.normal_le_normalCore.2 hAB
  exfalso
  obtain ⟨a, haA, haB⟩ := IsConcreteLE.not_le_iff_exists.1 hAB
  have htop : A ⊔ B = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      exists_mul_eq_of_cells_of_not_mem B U hUB c₀ hcell A haA haB g
    exact Subgroup.mul_mem_sup hx hy
  have hprod := card_sup_mul_card_inf_of_normal A B
  rw [htop, Subgroup.card_top, ← B.index_mul_card] at hprod
  have hidx : B.index * Nat.card ↥(A ⊓ B) = Nat.card A := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card B) ?_
    rw [← hprod]
    ring
  exact hr (Nat.Coprime.eq_one_of_dvd hA (hrB.trans (Dvd.intro _ hidx)))

theorem normal_coprime_eq_bot_of_equiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    {r : ℕ} (h : ∀ A : Subgroup F, A.Normal → Nat.Coprime r (Nat.card A) → A = ⊥) :
    ∀ A : Subgroup F', A.Normal → Nat.Coprime r (Nat.card A) → A = ⊥ := by
  intro A hA hcop
  have h0 := h (A.map e.symm.toMonoidHom) (hA.map _ e.symm.surjective)
    (by rwa [Subgroup.card_map_of_injective e.symm.injective])
  exact (Subgroup.map_eq_bot_iff_of_injective A e.symm.injective).1 h0

theorem eq_bot_of_fixSub_equiv {Y F : Type*} [Group Y] [Group F] {φ : MulAut Y} {r : ℕ}
    (e : F ≃* ↥(fixSub φ))
    (h : ∀ A : Subgroup F, A.Normal → Nat.Coprime r (Nat.card A) → A = ⊥) (N : Subgroup Y)
    (hNT : N ≤ fixSub φ) (hNn : ∀ g ∈ fixSub φ, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcop : Nat.Coprime r (Nat.card N)) : N = ⊥ := by
  have hN'n : (N.subgroupOf (fixSub φ)).Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.2
    (hNn g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  have hN'bot := normal_coprime_eq_bot_of_equiv e h _ hN'n
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv])
  rw [eq_bot_iff]
  intro n hn
  have hmem : (⟨n, hNT hn⟩ : ↥(fixSub φ)) ∈ N.subgroupOf (fixSub φ) :=
    Subgroup.mem_subgroupOf.2 hn
  rw [hN'bot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)

theorem not_even_of_pow_mod_three {p f : ℕ} (hq : (p ^ f) % 3 = 2) : ¬ Even f := by
  rintro ⟨m, rfl⟩
  rw [pow_add, Nat.mul_mod] at hq
  have h3 : p ^ m % 3 = 0 ∨ p ^ m % 3 = 1 ∨ p ^ m % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at hq <;> norm_num at hq

theorem card_fixSub_conj {Y : Type*} [Group Y] (β x : MulAut Y) :
    Nat.card ↥(fixSub (β * x * β⁻¹)) = Nat.card ↥(fixSub x) := by
  have h : fixSub (β * x * β⁻¹) = (fixSub x).map β.toMonoidHom := by
    ext t
    rw [mem_fixSub_conj_iff, Subgroup.mem_map]
    constructor
    · intro ht
      exact ⟨β⁻¹ t, ht, by simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
  rw [h, Subgroup.card_map_of_injective β.injective]

theorem sq_add_one_dvd_twelve {r : ℕ} (hr : 1 ≤ r)
    (h : r ^ 2 + 1 ∣ r ^ 12 * (r ^ 2 - 1) * (r ^ 6 - 1) * (r ^ 8 + r ^ 4 + 1)) :
    r ^ 2 + 1 ∣ 12 := by
  have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ hr
  rw [← CharP.cast_eq_zero_iff (ZMod (r ^ 2 + 1)) (r ^ 2 + 1)] at h
  rw [← CharP.cast_eq_zero_iff (ZMod (r ^ 2 + 1)) (r ^ 2 + 1)]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h6] at h ⊢
  have hx : ((r : ZMod (r ^ 2 + 1))) ^ 2 = -1 := by
    have h0 := CharP.cast_eq_zero (ZMod (r ^ 2 + 1)) (r ^ 2 + 1)
    push_cast at h0
    linear_combination h0
  set x : ZMod (r ^ 2 + 1) := (r : ZMod (r ^ 2 + 1)) with hxdef
  have e : x ^ 12 * (x ^ 2 - 1) * (x ^ 6 - 1) * (x ^ 8 + x ^ 4 + 1) =
      (x ^ 2) ^ 6 * (x ^ 2 - 1) * ((x ^ 2) ^ 3 - 1) * ((x ^ 2) ^ 4 + (x ^ 2) ^ 2 + 1) := by ring
  rw [e, hx] at h
  norm_num at h
  exact h

end Cells

section Polarity

open CFSG.LieType.Steinberg Multiplicative

theorem foldFix_polarity_eq_bot_of_coprime {X : Type*} [Group X] [Finite X]
    (D : RankTwoSystem X 3) {θ : X ≃* X} (hθ : D.IsPolarity θ) {c₀ : X}
    (hc₀ : c₀ ∈ dc D.B D.N D.w₀) (hc₀f : θ c₀ = c₀)
    (hKC : ∀ k ∈ D.B, θ k = k → (∀ u ∈ D.U, θ u = u → k * u = u * k) → k ∈ D.U) {r : ℕ}
    (hr : r ≠ 1) (hrU : r ∣ 1 + Nat.card ↥(D.U ⊓ foldFix θ)) (A : Subgroup ↥(foldFix θ))
    [A.Normal] (hA : Nat.Coprime r (Nat.card A)) : A = ⊥ := by
  have hmemB : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.B :=
    fun g => Subgroup.mem_subgroupOf
  have hmemU : ∀ g : ↥(foldFix θ), g ∈ D.U.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.U :=
    fun g => Subgroup.mem_subgroupOf
  have hw₀ : D.w₀ ≠ 1 := fun h => by
    have := D.rank2.dih.altWord_inj (i := 3) (j := 0) le_rfl (by norm_num)
      (h.trans (altWord_zero D.w₁ D.w₂).symm)
    omega
  have hc₀B : c₀ ∉ D.B := fun h => hw₀ ((D.bw_eq hc₀).symm.trans (D.bw_eq (mem_dc_one.2 h)))
  let c : ↥(foldFix θ) := ⟨c₀, hc₀f⟩
  have hcB : c ∉ D.B.subgroupOf (foldFix θ) := fun h => hc₀B ((hmemB c).1 h)
  have hUB : D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) := fun g hg =>
    (hmemB g).2 (D.U_le_B ((hmemU g).1 hg))
  have hcell : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
      ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u := by
    intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((hmemB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ :=
        hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (hmemB _).2 hb, ⟨u, huf⟩, (hmemU _).2 hu, Subtype.ext hgbu⟩
  have hinj : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ b' ∈ D.B.subgroupOf (foldFix θ),
      ∀ u ∈ D.U.subgroupOf (foldFix θ), ∀ u' ∈ D.U.subgroupOf (foldFix θ),
      b * c * u = b' * c * u' → b = b' ∧ u = u' := by
    intro b hb b' hb' u hu u' hu' h
    obtain ⟨h1, h2⟩ := RankTwoSystem.top_unique hc₀ ((hmemB b).1 hb) ((hmemB b').1 hb')
      ((hmemU u).1 hu) ((hmemU u').1 hu') (congrArg Subtype.val h)
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hindex := index_eq_one_add_card_of_cells (D.B.subgroupOf (foldFix θ))
    (D.U.subgroupOf (foldFix θ)) hUB c hcB hcell hinj
  have hUcard : Nat.card ↥(D.U.subgroupOf (foldFix θ)) = Nat.card ↥(D.U ⊓ foldFix θ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hUnorm : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ u ∈ D.U.subgroupOf (foldFix θ),
      b * u * b⁻¹ ∈ D.U.subgroupOf (foldFix θ) := fun b hb u hu =>
    (hmemU _).2 (D.conj_mem_U_of_mem_B ((hmemB b).1 hb) ((hmemU u).1 hu))
  have hmeet : ∀ u ∈ D.U.subgroupOf (foldFix θ), c * u * c⁻¹ ∈ D.B.subgroupOf (foldFix θ) →
      u = 1 := fun u hu h =>
    Subtype.ext (RankTwoSystem.U_meet_top hc₀ ((hmemU u).1 hu) ((hmemB _).1 h))
  have hKC' : ∀ k ∈ D.B.subgroupOf (foldFix θ),
      (∀ u ∈ D.U.subgroupOf (foldFix θ), k * u = u * k) → k ∈ D.U.subgroupOf (foldFix θ) := by
    intro k hk hcomm
    refine (hmemU k).2 (hKC k ((hmemB k).1 hk) (mem_foldFix.1 k.2) fun u hu huf => ?_)
    exact congrArg Subtype.val (hcomm ⟨u, huf⟩ ((hmemU _).2 hu))
  exact eq_bot_of_cells_of_coprime (D.B.subgroupOf (foldFix θ)) (D.U.subgroupOf (foldFix θ))
    hUB hUnorm c hcell hmeet hKC' hr (by rw [hindex, hUcard]; exact hrU) A hA

theorem foldFix_opposition_eq_bot_of_coprime {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hq : (p ^ f) % 3 = 2) (hf : 0 < f) {X : Type*} [Group X] [Finite X]
    (D : RankTwoSystem X 3) (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    (hĉ : ∃ c ∈ D.B ⊓ D.N, τ c = c ∧ c * c = 1 ∧ ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) :
    ∀ A : Subgroup ↥(foldFix τ), A.Normal → Nat.Coprime 3 (Nat.card A) → A = ⊥ := by
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  set x : X := ρ (sl2Lower (t : k))
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x))
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, hfix⟩ := un_heis_fixed D hp2 hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  have hKC := un_hKC D hab₁ hab₃ hTor θ hfix
  obtain ⟨c, hcH, hcτ, -, hcinv⟩ := hĉ
  have hc₀ := un_c0_mem_dc D ρ hρ2 hρm2 hρN hρH (un_two_ne_zero hp2) hcH hcinv t
  have hc₀f : θ (x⁻¹ * c * x) = x⁻¹ * c * x := by
    rw [hθapp]
    have e : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rw [e, hcτ]
  have h3 : 3 ∣ 1 + Nat.card ↥(D.U ⊓ foldFix θ) := by
    rw [hcard]
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hq]
  have hNA : ∀ A : Subgroup ↥(foldFix θ), A.Normal → Nat.Coprime 3 (Nat.card A) → A = ⊥ :=
    fun A hA hcop => by
      have := hA
      exact foldFix_polarity_eq_bot_of_coprime D hθpol hc₀ hc₀f hKC (by norm_num) h3 A hcop
  exact normal_coprime_eq_bot_of_equiv (unFixEquiv τ θ x hθapp) hNA

end Polarity

section Residuals

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def TrialityA2CoreFreeTwo : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      TrialityA2Rep 2 f Nat.prime_two K σ s →
        CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

end Residuals

section Faithful

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem eq_one_of_coprime_three_of_d4Out {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hφ : D4Out φ)
    (hout : ∀ ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ζ ^ 2 = 1 →
      ζ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      ζ * φ = φ * ζ → (∀ c ∈ fixSub φ, ζ c = c) → Even f → False)
    (ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hcop : Nat.Coprime 3 (orderOf ζ)) (hcomm : ζ * φ = φ * ζ)
    (hfix : ∀ c ∈ fixSub φ, ζ c = c) : ζ = 1 := by
  obtain ⟨hNoAbel, hPtKer⟩ := hφ
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, hΘinv⟩, -, -, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hpowcomm : ∀ n : ℕ, ζ ^ n * φ = φ * ζ ^ n := fun n =>
    (Commute.pow_left (show Commute ζ φ from hcomm) n).eq
  have hpowfix : ∀ n : ℕ, ∀ c ∈ fixSub φ, (ζ ^ n) c = c := by
    intro n
    induction n with
    | zero => intro c _; rfl
    | succ n ih => intro c hc; rw [pow_succ, MulAut.mul_apply, hfix c hc, ih c hc]
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ζ).ne'
  have hk2 : 2 ^ k ∣ orderOf ζ := ⟨o, hko⟩
  have hordo : orderOf (ζ ^ 2 ^ k) = o := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hk2, hko,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  have hζo : ζ ^ 2 ^ k = 1 := by
    refine hPtKer _ (by rw [hordo]; exact ho) ?_ (hpowcomm _) (fun c hc => hpowfix _ c hc)
    rw [hordo]
    exact (hcop.coprime_dvd_right ⟨2 ^ k, by rw [hko, mul_comm]⟩).symm
  have hord2 : orderOf ζ = 2 ^ k := by
    have h1 := orderOf_dvd_of_pow_eq_one hζo
    rw [hko] at h1 ⊢
    have ho1 : o = 1 := Nat.dvd_one.1 (Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos k)
      (by rw [mul_one]; exact h1))
    rw [ho1, mul_one]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hord2
    exact orderOf_eq_one_iff.1 hord2
  exfalso
  set ι := ζ ^ 2 ^ (k - 1) with hιdef
  have hιord : orderOf ι = 2 := by
    rw [hιdef, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (hord2 ▸ pow_dvd_pow 2 (Nat.sub_le k 1)), hord2, Nat.pow_div (Nat.sub_le k 1) two_pos,
      show k - (k - 1) = 1 by omega, pow_one]
  have hι2 : ι ^ 2 = 1 := by
    rw [← hιord]
    exact pow_orderOf_eq_one ι
  have hι1 : ι ≠ 1 := fun h => by
    rw [h, orderOf_one] at hιord
    exact absurd hιord (by norm_num)
  by_cases hΘι : Θ ι = 1
  · apply hι1
    exact d4_inner_fix_trivial hcen φ hNoAbel ι (by rw [← hΘker]; exact hΘι) (hpowcomm _)
      (fun c hc => hpowfix _ c hc)
  · rcases hΘinv ι hι2 with h | ⟨hfe, -⟩
    · exact hΘι h
    · refine hout ι hι2 (fun hmem => hΘι ?_) (hpowcomm _) (fun c hc => hpowfix _ c hc) hfe
      rw [← MonoidHom.mem_ker, hΘker]
      exact hmem

theorem card_fixSub_fieldActor_two {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ (3 * m * 2)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ p ^ (m * 2)) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ p ^ (3 * m)) :
    Nat.card ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) =
      (p ^ m) ^ 12 * ((p ^ m) ^ 2 - 1) * ((p ^ m) ^ 6 - 1) *
        ((p ^ m) ^ 8 + (p ^ m) ^ 4 + 1) := by
  obtain ⟨-, -, -, hcardFix, -⟩ := CFSG.RankThree.Chevalley.triality_canonical_field_facts hp hm
    le_rfl (by norm_num : Nat.Coprime 2 3) hK hσ hδ
  obtain ⟨-, -, -, -, -, -, h7, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hp hm
      le_rfl (by norm_num : Nat.Coprime 2 3) K hK σ hσ δ hδ
  have hLcard : Nat.card (fixSubfield δ) = (p ^ m) ^ 3 := by rw [hcardFix, mul_comm, pow_mul]
  have hσL : ∀ c : fixSubfield δ, fixSubfieldRestrict σ δ c = c ^ ((p ^ m) ^ 2) := by
    intro c
    apply Subtype.ext
    rw [coe_fixSubfieldRestrict, hσ _, SubmonoidClass.coe_pow, ← pow_mul]
  have hord := (triality_both_orientations_exact_finite_order p m hp hm (fixSubfield δ) hLcard 2
    (Or.inr rfl) (fixSubfieldRestrict σ δ).toRingHom (fun c => hσL c)).1
  have hfx : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub (fieldActor (t := TwistTag.D4) σ δ) =
      fixSub (fieldActor (t := TwistTag.D4) σ δ) := Subgroup.ext fun _ => Iff.rfl
  have h1 : Nat.card ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) =
      Nat.card ↥((CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
        (fieldActor (t := TwistTag.D4) σ δ)).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype) := by
    rw [hfx]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
  have h2 : (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
      (fieldActor (t := TwistTag.D4) σ δ)).map
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ δ := h7
  have h3 : Nat.card (trialityFieldImage σ δ) = Nat.card (graphFixedRootGroup TwistTag.D4
      (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).toEquiv.symm
  rw [h1, h2, h3, hord]

end Faithful

section Toral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_nonempty_fixSub_equiv (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nonempty (↥(foldFix (A2Core.a2Phi h φ)) ≃* ↥(fixSub φ)) := by
  have hfix : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ = fixSub φ :=
    Subgroup.ext fun _ => Iff.rfl
  exact ⟨((MulEquiv.subgroupMap (A2Core.a2Equiv h) (foldFix (A2Core.a2Phi h φ))).trans
    (MulEquiv.subgroupCongr (A2Core.a2_foldFix_map h φ hφ))).trans (MulEquiv.subgroupCongr hfix)⟩

theorem A2Core.a2_card_fixSub (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥(fixSub φ) = (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  have hFD := A2Core.a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  have : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv _ (A2Core.a2Equiv h).symm.toEquiv
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := hFD.exists_rgd2
  have hcard := hFD.card_fixed hgen (fun g _ hcomm => A2Core.a2_hZ h hcomm)
    (fun x hx => A2Core.a2_hz h φ hφ x hx) (A2Core.a2_hC h φ hφ)
    (fun k hk => A2Core.a2_card_foldRoot h φ hφ hk) (A2Core.a2_card_U_fix h φ hφ R')
  rw [A2Core.a2_card_H_fix h φ hφ] at hcard
  obtain ⟨e⟩ := a2_nonempty_fixSub_equiv h φ hφ
  rw [← hcard]
  exact (Nat.card_congr e.toEquiv).symm

theorem A2Core.a2_normal_coprime_three_eq_bot (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hNT : N ≤ fixSub φ)
    (hNn : ∀ g ∈ fixSub φ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hcop : Nat.Coprime 3 (Nat.card N)) :
    N = ⊥ := by
  have hFD := A2Core.a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  have : Finite (twistedGroup σ.toRingHom) := Finite.of_equiv _ (A2Core.a2Equiv h).symm.toEquiv
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := hFD.exists_rgd2
  have hU := A2Core.a2_card_U_fix h φ hφ R'
  have hH := A2Core.a2_card_H_fix h φ hφ
  have hcard := hFD.card_fixed hgen (fun g _ hcomm => A2Core.a2_hZ h hcomm)
    (fun x hx => A2Core.a2_hz h φ hφ x hx) (A2Core.a2_hC h φ hφ)
    (fun k hk => A2Core.a2_card_foldRoot h φ hφ hk) hU
  rw [hH] at hcard
  have hq1 := h.mod3
  have hq2 := h.two_le
  have hq3 : ¬ 3 ∣ q := fun h3 => by omega
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (n := (q - 1) ^ 2) (pow_ne_zero 2 (by omega)) 3 (by norm_num)
  have h3q : 3 ∣ q ^ 2 + q + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hq1]
  have hXm : 3 ^ (a + 1) ∣ Nat.card ↥(foldFix (A2Core.a2Phi h φ)) := by
    rw [hcard, hab, pow_succ]
    obtain ⟨c, hc⟩ := h3q
    exact ⟨b * q ^ 3 * (q + 1) * c, by rw [hc]; ring⟩
  have hBm : ¬ 3 ^ (a + 1) ∣
      Nat.card ↥((⨆ i, hHat σ.toRingHom i) ⊓ foldFix (A2Core.a2Phi h φ)) *
        Nat.card ↥((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
          foldFix (A2Core.a2Phi h φ)) := by
    rw [hH, hU, hab, pow_succ, mul_assoc]
    intro hdvd
    have h1 : 3 ∣ b * q ^ 3 := (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num) a)).1 hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h2 | h2
    · exact hb3 h2
    · exact hq3 (Nat.prime_three.dvd_of_dvd_pow h2)
  obtain ⟨e⟩ := a2_nonempty_fixSub_equiv h φ hφ
  refine eq_bot_of_fixSub_equiv e (fun A hA hcopA => ?_) N hNT hNn hcop
  have := hA
  exact foldData_eq_bot_of_normal_of_coprime hFD hgen (fun g _ hcomm => A2Core.a2_hZ h hcomm)
    (fun x hx => A2Core.a2_hz h φ hφ x hx) (A2Core.a2_hC h φ hφ) hXm hBm A hcopA

theorem a2_card_fixSub (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nat.card ↥(fixSub φ) = (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) :=
  A2Core.a2_card_fixSub h.toCore φ hφ

theorem a2_normal_coprime_three_eq_bot (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hNT : N ≤ fixSub φ)
    (hNn : ∀ g ∈ fixSub φ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hcop : Nat.Coprime 3 (Nat.card N)) :
    N = ⊥ :=
  A2Core.a2_normal_coprime_three_eq_bot h.toCore φ hφ N hNT hNn hcop

theorem trialityA2ToralOuterInvolution_holds :
    ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 → Even f →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      ∀ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 → d ≠ 1 →
      ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
      ∀ ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ζ ^ 2 = 1 →
        ζ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
        ζ * (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) =
          (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) * ζ →
        (∀ c ∈ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ), ζ c = c) → False := by
  intro p f hp hp2 hp3 hf hq hfe K _ _ hK σ hσ d hd hd3 hd1 s hs ζ hζ2 hζout _ hζfix
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hΘker, hΘinv⟩, -, -, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hΘζ : Θ ζ ≠ 1 := fun h1 => hζout (by rw [← hΘker]; exact h1)
  obtain ⟨-, hη⟩ := (hΘinv ζ hζ2).resolve_left hΘζ
  obtain ⟨m, hm⟩ : ∃ m, f = m * 2 :=
    ⟨f / 2, (Nat.div_mul_cancel (even_iff_two_dvd.1 hfe)).symm⟩
  have hm1 : 1 ≤ m := by omega
  have hδ : ∀ c, Θ ζ c = c ^ p ^ (3 * m) := fun c => by
    rw [hη c]
    congr 2
    omega
  obtain ⟨⟨g, δ'⟩, hgδ, -⟩ := hNF ζ
  have hδ' : δ' = Θ ζ := (hΘ ζ g δ' hgδ).symm
  subst hδ'
  have hgδ' : ζ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ (Θ ζ) := hgδ
  set φF : K ≃+* K := iterateFrobeniusEquiv K p 1 with hφFdef
  have hφF : ∀ c, φF c = c ^ p := fun c => by
    rw [hφFdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def, pow_one]
  have hε : σ ^ (3 - 2) * φF ^ (f / 2) = Θ ζ := RingEquiv.ext fun c => by
    change (σ ^ 1) ((φF ^ (f / 2)) c) = Θ ζ c
    rw [pow_one, ringAut_pow_apply_of_frobenius hφF, hσ, hδ, ← pow_mul, ← pow_add]
    congr 2
    omega
  have hgp : (MulAut.conj g * fieldActor (t := TwistTag.D4) σ (σ ^ (3 - 2) * φF ^ (f / 2))) ^ 2 =
      1 := by
    rw [hε, ← hgδ']
    exact hζ2
  obtain ⟨h₀, hh₀⟩ := CFSG.RankThree.Chevalley.exists_inner_conj_triality_field_actor (p := 2)
    (r := 2) hp hf K hK σ hσ hcen (by norm_num) ⟨m, by omega⟩ (Or.inr rfl) (by norm_num) hφF g
    hgp
  rw [hε, ← hgδ'] at hh₀
  have hcardζ : Nat.card ↥(fixSub ζ) = (p ^ m) ^ 12 * ((p ^ m) ^ 2 - 1) * ((p ^ m) ^ 6 - 1) *
      ((p ^ m) ^ 8 + (p ^ m) ^ 4 + 1) := by
    rw [← card_fixSub_conj (MulAut.conj h₀) ζ, hh₀]
    exact card_fixSub_fieldActor_two hp hm1 K (by rw [hK3, hm, ← mul_assoc]) σ
      (fun c => by rw [hσ c, hm]) (Θ ζ) hδ
  have hcardφ := a2_card_fixSub (a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1) _
    (a2_hφ_of_class (σ := σ) (d := d) hs)
  have hdvd := Subgroup.card_dvd_of_le
    (show fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) ≤ fixSub ζ from
      fun c hc => hζfix c hc)
  rw [hcardφ, hcardζ] at hdvd
  have hq1 : p ^ f + 1 ∣ (p ^ m) ^ 12 * ((p ^ m) ^ 2 - 1) * ((p ^ m) ^ 6 - 1) *
      ((p ^ m) ^ 8 + (p ^ m) ^ 4 + 1) :=
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _).trans hdvd
  rw [hm, pow_mul] at hq1
  have h12 := Nat.le_of_dvd (by norm_num) (sq_add_one_dvd_twelve (Nat.one_le_pow _ _ hp.pos) hq1)
  have hp4 : 4 ≤ p := by
    have := hp.two_le
    omega
  have hpm : 4 ≤ p ^ m := le_trans hp4 (Nat.le_self_pow (by omega) p)
  have h16 : 16 ≤ (p ^ m) ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (p ^ m) ^ 2 := Nat.pow_le_pow_left hpm 2
  omega

theorem coreFreeAt_three_A2Toral {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hd : Units.map σ.toRingHom.toMonoidHom d = d) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  refine ⟨fun N hNT hNn hcop => a2_normal_coprime_three_eq_bot
    (a2Std_of_class hp hp2 hf hq hK hσ hd hd3 hd1) _ (a2_hφ_of_class (σ := σ) (d := d) hs) N hNT
    hNn hcop, eq_one_of_coprime_three_of_d4Out hp hp2 hf hK hσ
    (d4OuterThreeA2Toral_thm p f hp hp2 hp3 hf hq K hK σ hσ d hd hd3 hd1 s hs) ?_⟩
  intro ζ hζ2 hζo hζc hζf hfe
  exact trialityA2ToralOuterInvolution_holds p f hp hp2 hp3 hf hq hfe K hK σ hσ d hd hd3 hd1 s hs
    ζ hζ2 hζo hζc hζf

end Toral

section Minus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem unTauX_normal_coprime_three_eq_bot (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hq3 : (p ^ f) % 3 = 2) (hf : 1 ≤ f)
    (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    ∀ A : Subgroup ↥(foldFix (unTauX h φ ε hcomm)), A.Normal →
      Nat.Coprime 3 (Nat.card A) → A = ⊥ := by
  have hσ' : ∀ c, σ c = c ^ ((p ^ f) ^ 4) := fun c => by rw [h.frob c, hq]
  have hK : Nat.card K = ((p ^ f) ^ 4) ^ 3 := by rw [h.card, hq]
  have hεσ : ∀ c, ε (σ c) = σ (ε c) := un_eps_sigma hσ' hε
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := un_eps_four hK hε
  have : CharP (UnK σ) p := un_charP_unK σ
  have hk : Nat.card (UnK σ) = (p ^ f) ^ 4 := un_card_unK hf hK hσ'
  have hεk : ∀ a : UnK σ, unEps ε hεσ a = a ^ (p ^ f) := un_eps_frob hσ' hε hεσ
  have hεε : ∀ c, (ε * ε) (σ c) = σ ((ε * ε) c) := fun c => by
    show ε (ε (σ c)) = σ (ε (ε c))
    rw [hεσ, hεσ]
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁', -⟩ := (unD_spec h φ hφ).lifts
  have hn₁X : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W :=
    Subtype.ext (hn₁'.trans (unSlFix_w h φ hφ).symm)
  obtain ⟨κ, hκ⟩ := unRho_tau h φ hφ hn₂ ε hεσ hcomm
  have hτ := un_isOpposition h φ hφ ε hεσ hcomm
  have hτe := un_tauX_tauX h φ ε hcomm hcommε
  refine foldFix_opposition_eq_bot_of_coprime hp2 hq3 (by omega) (unD h φ hφ)
    (unTauX h φ ε hcomm) (unFieldX h φ (ε * ε) hcommε) hτ hτe
    (fun b hb => by rw [← hτe b]; exact hτ.tau_sq_mem_B hb)
    (un_tauX_four h φ ε hε4 hcomm) hk (unEps ε hεσ) hεk (unRho h φ hφ n₂)
    (unRho_injective h φ hφ n₂) κ (fun a => (hκ a).1) (fun a => (hκ a).2)
    (unRho_upper_mem h φ hφ hn₂) (fun y hy => unRho_upper_surj h φ hφ hn₂ hy)
    (unRho_lower_mem h φ hφ hn₂) (unRho_N h φ hφ hn₂ hn₁ hn₁X) (unRho_H h φ hφ hn₂)
    (unX1 h φ hφ) (unX1_injective h φ hφ) (unX1_mem h φ hφ) (fun y hy => unX1_surj h φ hφ hy)
    (unX1_torus h φ hφ) ?_ (un_hab h φ hφ (Or.inl rfl)) (un_hab h φ hφ (Or.inr rfl))
    (un_hTor h φ hφ) (un_chat_X h φ hφ ε hεσ hcomm)
  intro a
  rw [unX1_field h φ hφ (ε * ε) hεε hcommε a, unEps_mul ε ε hεσ hεσ hεε a]

theorem unTau_normal_coprime_three_eq_bot {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ p]
    (hK₄ : Nat.card K₄ = ((p ^ f) ^ 4) ^ 3) (σ₄ ε : K₄ ≃+* K₄)
    (hσ₄ : ∀ c, σ₄ c = c ^ ((p ^ f) ^ 4)) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (b : K₄ˣ)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    ∀ F₀ : Subgroup ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)),
      F₀.Normal → Nat.Coprime 3 (Nat.card F₀) → F₀ = ⊥ := by
  have hA : A2Std σ₄ b ((p ^ f) ^ 4) := un_a2Std hp2 hf hq hK₄ hσ₄ hb3 hb1
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  obtain ⟨e, -⟩ := un_fixfix_equiv hA _ ε hcomm
  exact normal_coprime_eq_bot_of_equiv e
    (unTauX_normal_coprime_three_eq_bot hA _ hφ₄ hp2 hq hf rfl ε hε hcomm hcommε)

theorem minus_normal_coprime_three_eq_bot {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hs : D4MinusToral p f hp K σ s)
    (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hNT : N ≤ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))
    (hNn : ∀ g ∈ fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ), ∀ n ∈ N,
      g * n * g⁻¹ ∈ N) (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have hfx : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
      (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) =
      fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) :=
    Subgroup.ext fun _ => Iff.rfl
  exact eq_bot_of_fixSub_equiv (e.symm.trans (MulEquiv.subgroupCongr hfx))
    (unTau_normal_coprime_three_eq_bot hp2 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄) N hNT hNn
    hcop

theorem coreFreeAt_three_A2Minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (hK : Nat.card K = (p ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : D4MinusToral p f hp K σ s) :
    CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) :=
  ⟨minus_normal_coprime_three_eq_bot hp hp2 hf hq hK hσ hs,
    eq_one_of_coprime_three_of_d4Out hp hp2 hf hK hσ
      (d4OuterThreeA2Minus_thm p f hp hp2 hp3 hf hq K hK σ hσ s hs)
      fun _ _ _ _ _ hfe => not_even_of_pow_mod_three hq hfe⟩

end Minus

section Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem coreFreeAt_three_of_trialityA2Rep {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hs : TrialityA2Rep ℓ f hℓ K σ s) :
    CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  rcases hs with ⟨hq, d, hd, hd3, hd1, hsd⟩ | ⟨hq, hsm⟩
  · exact coreFreeAt_three_A2Toral hℓ hℓ2 hℓ3 hf hq hK hσ hd hd3 hd1 hsd
  · exact coreFreeAt_three_A2Minus hℓ hℓ2 hℓ3 hf hq hK hσ hsm

theorem trialityA2CoreFree_of_two (htwo : TrialityA2CoreFreeTwo) : TrialityA2CoreFree := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ s hs
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · exact htwo f hf K hK σ hσ s hs
  · exact coreFreeAt_three_of_trialityA2Rep hℓ hℓ2 hℓ3 hf hK hσ hs

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar
