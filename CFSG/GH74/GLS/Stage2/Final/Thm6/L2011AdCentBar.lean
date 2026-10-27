module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Abstract

variable {Q : Type} [Group Q]

theorem centralizes_of_comm_mem_odd [Finite Q] {L Y : Subgroup Q} {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hL : HasSL2Model ↥L (fun r => r = q)) (hYodd : ∀ y ∈ Y, Odd (orderOf y))
    (hYnorm : ∀ l ∈ L, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) {c : Q} (hcn : ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hcY : ∀ l ∈ L, ⁅c, l⁆ ∈ Y) : ∀ l ∈ L, c * l = l * c := by
  have hnorm : (Y.subgroupOf L).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hYnorm g g.2 n hn⟩
  have hodd : Odd (Nat.card ↥(Y.subgroupOf L)) :=
    IVK.Proofs2.Ivk93Adapt.odd_card_of_forall_odd _ (fun y hy => by
      rw [← Subgroup.orderOf_coe]
      exact hYodd _ (Subgroup.mem_subgroupOf.mp hy))
  have hle : Y.subgroupOf L ≤ pPrimeCore 2 ↥L :=
    GroupTheory.le_pPrimeCore_of_normal hnorm (Nat.coprime_two_left.2 hodd)
  have hbot : pPrimeCore 2 ↥L = ⊥ :=
    IVK.Proofs2.Ivk93Adapt.pPrimeCore_eq_bot_of_hasSL2Model hq h5 hL
  intro l hl
  have hmem : ⁅c, l⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (hcn l hl) (L.inv_mem hl)
  have h1 : (⟨⁅c, l⁆, hmem⟩ : ↥L) ∈ Y.subgroupOf L := hcY l hl
  have h2 : (⟨⁅c, l⁆, hmem⟩ : ↥L) = 1 := by
    have := hle h1
    rwa [hbot, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h2)

theorem false_of_swap_mem_odd {L₁ L₂ Y : Subgroup Q}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hI : Nat.card ↥(L₁ ⊓ L₂) = 2)
    {x : Q} (hx : x ∈ L₁) (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1)
    (hYodd : ∀ y ∈ Y, Odd (orderOf y)) {c : Q} (hcs : c * x * c⁻¹ ∈ L₂)
    (hcY : c * x * c⁻¹ * x⁻¹ ∈ Y) : False := by
  obtain ⟨j, hj⟩ := hYodd _ hcY
  have hwm : (c * x * c⁻¹ * x⁻¹) ^ (2 * j + 1) = 1 := by
    rw [← hj]
    exact pow_orderOf_eq_one _
  have hcm : Commute (c * x * c⁻¹) x⁻¹ := (hcomm x⁻¹ (L₁.inv_mem hx) _ hcs).symm
  rw [hcm.mul_pow, inv_pow] at hwm
  have hax : (c * x * c⁻¹) ^ (2 * j + 1) = x ^ (2 * j + 1) := mul_inv_eq_one.mp hwm
  have hmem : x ^ (2 * j + 1) ∈ L₁ ⊓ L₂ := ⟨L₁.pow_mem hx _, hax ▸ L₂.pow_mem hcs _⟩
  have hfin : Finite ↥(L₁ ⊓ L₂) := Nat.finite_of_card_ne_zero (by rw [hI]; norm_num)
  have hsq := mul_self_eq_one_of_card_le_two (Z := ↥(L₁ ⊓ L₂)) (by rw [hI]) ⟨x ^ (2 * j + 1), hmem⟩
  have hsq' : x ^ (2 * j + 1) * x ^ (2 * j + 1) = 1 := congrArg Subtype.val hsq
  apply hx2
  have : x ^ (2 * j + 1) * x ^ (2 * j + 1) = x ^ 2 := by
    rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 4 * j + 2 by ring, pow_add, pow_mul, hx4, one_pow, one_mul]
  rw [← this]
  exact hsq'

theorem mem_inf_of_centralizes_sup {L₁ L₂ : Subgroup Q}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hZ₁ : Nat.card ↥(center ↥L₁) = 2) (hZ₂ : Nat.card ↥(center ↥L₂) = 2)
    (hI : Nat.card ↥(L₁ ⊓ L₂) = 2) {x : Q} (hx : x ∈ L₁ ⊔ L₂)
    (h₁ : ∀ l ∈ L₁, x * l = l * x) (h₂ : ∀ l ∈ L₂, x * l = l * x) : x ∈ L₁ ⊓ L₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage2.Local.exists_mul_of_mem_sup_of_commute hcomm hx
  have hacen : ∀ l ∈ L₁, l * a = a * l := by
    intro l hl
    have e : l * a * b = a * l * b := by
      calc l * a * b = l * (a * b) := by group
        _ = (a * b) * l := (h₁ l hl).symm
        _ = a * (b * l) := by group
        _ = a * (l * b) := by rw [(hcomm l hl b hb).symm]
        _ = a * l * b := by group
    exact mul_right_cancel e
  have hbcen : ∀ l ∈ L₂, l * b = b * l := by
    intro l hl
    have e : a * (l * b) = a * (b * l) := by
      calc a * (l * b) = (a * l) * b := by group
        _ = (l * a) * b := by rw [hcomm a ha l hl]
        _ = l * (a * b) := by group
        _ = (a * b) * l := (h₂ l hl).symm
        _ = a * (b * l) := by group
    exact mul_left_cancel e
  have haL₂ : a ∈ L₂ :=
    CFSG.GH74.GLS.Stage2.Local.central_mem_of_card_inf hcomm hZ₁ hI ha hacen
  have hbL₁ : b ∈ L₁ :=
    CFSG.GH74.GLS.Stage2.Local.central_mem_of_card_inf (A := L₂) (B := L₁)
      (fun u hu v hv => (hcomm v hv u hu).symm) hZ₂ (by rw [inf_comm]; exact hI) hb hbcen
  exact ⟨L₁.mul_mem ha hbL₁, L₂.mul_mem haL₂ hb⟩

theorem eq_one_or_eq_of_card_eq_two_mem {I : Subgroup Q} (hI : Nat.card ↥I = 2) {u : Q} (hu : u ∈ I)
    (hu1 : u ≠ 1) {x : Q} (hx : x ∈ I) : x = 1 ∨ x = u := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥I)).mp hI
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have h1 := huniq ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    have h2 := huniq ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_pow_four_eq_one_sq_ne_one {K : Type} [Group K] {q : ℕ} (hq : Odd q)
    (hK : HasSL2Model K (fun r => r = q)) : ∃ x : K, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := IVK.Proofs2.exists_sl2_equiv_of_hasSL2Model hK
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  refine ⟨e (Semidihedral.OddLinearNormals.quarterTurn F), ?_, ?_⟩
  · rw [← map_pow, Semidihedral.OddFieldSL2.quarterTurn_period, map_one]
  · rw [← map_pow, Semidihedral.OddFieldSL2.quarterTurn_square]
    intro h
    exact Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2 (e.injective (h.trans (map_one e).symm))

end Abstract

section Bar

variable {G : Type} [Group G] {z : G}

theorem odd_orderOf_of_mem_barOf {N : Subgroup G} (hN : ∀ n ∈ N, Odd (orderOf n))
    {y : CentralizerBar z} (hy : y ∈ barOf z N) : Odd (orderOf y) := by
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 : Odd (orderOf (y' : G)) := hN _ (Subgroup.mem_subgroupOf.mp hy')
  rw [Subgroup.orderOf_coe] at h1
  exact Odd.of_dvd_nat h1 (orderOf_map_dvd (toBar z) y')

theorem conj_mem_barOf {N K : Subgroup G} (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    {l y : CentralizerBar z} (hl : l ∈ barOf z K) (hy : y ∈ barOf z N) : l * y * l⁻¹ ∈ barOf z N := by
  obtain ⟨k, hk, rfl⟩ := hl
  obtain ⟨n, hn, rfl⟩ := hy
  refine ⟨k * n * k⁻¹, ?_, by simp⟩
  exact hKN _ (Subgroup.mem_subgroupOf.mp hk) _ (Subgroup.mem_subgroupOf.mp hn)

theorem comm_mem_barOf {N : Subgroup G} {c k : G} (hc : c ∈ Cen z) (hk : k ∈ Cen z)
    (h : ⁅c, k⁆ ∈ N) : ⁅toBar z ⟨c, hc⟩, toBar z ⟨k, hk⟩⁆ ∈ barOf z N :=
  ⟨⁅(⟨c, hc⟩ : ↥(Cen z)), ⟨k, hk⟩⁆, Subgroup.mem_subgroupOf.mpr h, map_commutatorElement _ _ _⟩

theorem mem_oddCore_of_toBar_eq_one {x : G} (hx : x ∈ Cen z) (h : toBar z ⟨x, hx⟩ = 1) :
    x ∈ OddCore z :=
  ⟨⟨x, hx⟩, (ker_toBar z) ▸ h, rfl⟩

end Bar

theorem cent_bar_pair {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hz2 : orderOf z = 2) (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂)
    {H : Subgroup G} (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H)
    {c : G} (hcC : c ∈ centralizer ({z} : Set G)) (hcH : c ∈ H)
    (hcomm : ∀ k ∈ K₁ ⊔ K₂, ⁅c, k⁆ ∈ pPrimeCoreOf 2 H) :
    ∃ a ∈ OddCore z, c = a ∨ c = z * a := by
  have _ := hcH
  have hshape : PairShape L₁ L₂ := PairShape.of_stage1Pair hP
  have hq5 : 5 ≤ q := L2012.five_le_of_pair hP
  obtain ⟨c', hc'⟩ : ∃ c' : CentralizerBar z, c' = toBar z ⟨c, hcC⟩ := ⟨_, rfl⟩
  have hYodd : ∀ y ∈ barOf z (pPrimeCoreOf 2 H), Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_mem_barOf (fun n hn => LU.Local.odd_orderOf_pPrimeCoreOf hn) hy
  have hNnorm : ∀ k ∈ H, ∀ n ∈ pPrimeCoreOf 2 H, k * n * k⁻¹ ∈ pPrimeCoreOf 2 H :=
    fun k hk n hn => TwoThin.pPrimeCoreOf_normalized H hk hn
  have hY₁ : ∀ l ∈ L₁, ∀ y ∈ barOf z (pPrimeCoreOf 2 H), l * y * l⁻¹ ∈ barOf z (pPrimeCoreOf 2 H) :=
    fun l hl y hy =>
      conj_mem_barOf (fun k hk n hn => hNnorm k (hK₁H hk) n hn) (by rw [hK.bar₁]; exact hl) hy
  have hY₂ : ∀ l ∈ L₂, ∀ y ∈ barOf z (pPrimeCoreOf 2 H), l * y * l⁻¹ ∈ barOf z (pPrimeCoreOf 2 H) :=
    fun l hl y hy =>
      conj_mem_barOf (fun k hk n hn => hNnorm k (hK₂H hk) n hn) (by rw [hK.bar₂]; exact hl) hy
  have hc₁ : ∀ l ∈ L₁, ⁅c', l⁆ ∈ barOf z (pPrimeCoreOf 2 H) := by
    intro l hl
    rw [← hK.bar₁] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    rw [hc']
    exact comm_mem_barOf hcC k.2 (hcomm k (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk)))
  have hc₂ : ∀ l ∈ L₂, ⁅c', l⁆ ∈ barOf z (pPrimeCoreOf 2 H) := by
    intro l hl
    rw [← hK.bar₂] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    rw [hc']
    exact comm_mem_barOf hcC k.2 (hcomm k (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk)))
  have hno : ¬ cj c' L₁ = L₂ := by
    intro hswap
    obtain ⟨x, hx4, hx2⟩ := exists_pow_four_eq_one_sq_ne_one hP.odd hP.sl₁
    have hxL : (x : CentralizerBar z) ∈ L₁ := x.2
    refine false_of_swap_mem_odd (c := c') hshape.comm hP.prod.2.2 hxL
      (by simpa using congrArg Subtype.val hx4) (fun h => hx2 (Subtype.ext (by simpa using h))) hYodd ?_ ?_
    · rw [← hswap]
      exact ⟨x, hxL, rfl⟩
    · have := hc₁ _ hxL
      rwa [commutatorElement_def] at this
  have hn₁ : cj c' L₁ = L₁ := (hshape.cj_cases c').resolve_right hno
  have hn₂ : cj c' L₂ = L₂ := hshape.cj_fix hn₁
  have hcn₁ : ∀ l ∈ L₁, c' * l * c'⁻¹ ∈ L₁ := fun l hl => hn₁ ▸ (⟨l, hl, rfl⟩ : c' * l * c'⁻¹ ∈ cj c' L₁)
  have hcn₂ : ∀ l ∈ L₂, c' * l * c'⁻¹ ∈ L₂ := fun l hl => hn₂ ▸ (⟨l, hl, rfl⟩ : c' * l * c'⁻¹ ∈ cj c' L₂)
  have hcen₁ : ∀ l ∈ L₁, c' * l = l * c' :=
    centralizes_of_comm_mem_odd hP.odd hq5 hP.sl₁ hYodd hY₁ hcn₁ hc₁
  have hcen₂ : ∀ l ∈ L₂, c' * l = l * c' :=
    centralizes_of_comm_mem_odd hP.odd hq5 hP.sl₂ hYodd hY₂ hcn₂ hc₂
  have hcent : c' ∈ centralizer (generalizedFitting (CentralizerBar z) : Set (CentralizerBar z)) := by
    rw [hshape.fitting, Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : L₁ ⊔ L₂ ≤ centralizer ({c'} : Set (CentralizerBar z)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcen₁ a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcen₂ a ha).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hmem : c' ∈ L₁ ⊔ L₂ := hshape.fitting ▸ centralizer_generalizedFitting_le _ hcent
  have hinf : c' ∈ L₁ ⊓ L₂ :=
    mem_inf_of_centralizes_sup hshape.comm (sl2_model_center_inv hP.odd hP.sl₁).1
      (sl2_model_center_inv hP.odd hP.sl₂).1 hP.prod.2.2 hmem hcen₁ hcen₂
  have hz1 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h
    have hzsq : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    have h' := eq_one_of_toBar_eq_one z (u := ⟨z, mem_Cen_self z⟩)
      (Subtype.ext (by simpa using hzsq)) h
    have hz : z = 1 := congrArg Subtype.val h'
    rw [hz, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  rcases eq_one_or_eq_of_card_eq_two_mem hP.prod.2.2 (IVK.Proofs2.Ivk93Adapt.zbarC_mem_inf hP) hz1 hinf with
    h1 | h1
  · refine ⟨c, mem_oddCore_of_toBar_eq_one hcC (by rw [← hc']; exact h1), Or.inl rfl⟩
  · have hzc : z⁻¹ * c ∈ Cen z := (Cen z).mul_mem ((Cen z).inv_mem (mem_Cen_self z)) hcC
    refine ⟨z⁻¹ * c, mem_oddCore_of_toBar_eq_one hzc ?_, Or.inr (by simp)⟩
    have e : (⟨z⁻¹ * c, hzc⟩ : ↥(Cen z)) = (⟨z, mem_Cen_self z⟩ : ↥(Cen z))⁻¹ * ⟨c, hcC⟩ := rfl
    rw [e, map_mul, map_inv, ← hc', h1, inv_mul_cancel]

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
