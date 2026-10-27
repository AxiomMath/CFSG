module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Parts

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G]

theorem exists_data2011 {z : G} {k : Kind} {S : Subgroup G} (hC : Ctx2011 G z k S) :
    ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G),
      Stage1Pair G z S q L₁ L₂ ∧ (RC S z).relIndex S ≤ 4 ∧ CompData z K₁ K₂ L₁ L₂ := by
  obtain ⟨q, L₁, L₂, hpair, hidx⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1Pair G z S q L₁ L₂ ∧ (RC S z).relIndex S ≤ 4 := by
    rcases hC.2 with ⟨ε, q, hk, L₁, L₂, h⟩ | ⟨q, hk, L₁, L₂, h⟩
    · exact ⟨q, L₁, L₂, h.pair, h.index_le⟩
    · exact ⟨q, L₁, L₂, h.pair, h.index.le.trans (by norm_num)⟩
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := hC.1.ctx.thm4.1
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  exact ⟨q, L₁, L₂, K₁, K₂, hpair, hidx, hK⟩

omit [Finite G] in
theorem mem_oddCore_of_toBar_eq {z : G} {u v : G} (hu : u ∈ Cen z) (hv : v ∈ Cen z)
    (h : toBar z ⟨u, hu⟩ = toBar z ⟨v, hv⟩) : u⁻¹ * v ∈ OddCore z := by
  have h1 : toBar z ⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ = 1 := by
    have : (⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ : ↥(Cen z)) =
        (⟨u, hu⟩ : ↥(Cen z))⁻¹ * ⟨v, hv⟩ := rfl
    rw [this, map_mul, map_inv, h]
    group
  have h2 : (⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

theorem compData_fix {z : G} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hK : CompData z K₁ K₂ L₁ L₂) {y : G} (hy : y ∈ Cen z)
    (hyL : ∀ l ∈ L₁, toBar z ⟨y, hy⟩ * l * (toBar z ⟨y, hy⟩)⁻¹ ∈ L₁) :
    ∀ a ∈ K₁, y * a * y⁻¹ ∈ K₁ := by
  set P : Subgroup G := K₁.map (MulAut.conj y).toMonoidHom with hPdef
  have hPC : P ≤ Cen z := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Cen z).mul_mem ((Cen z).mul_mem hy (hK.le₁ ha)) ((Cen z).inv_mem hy)
  have hPperf : ⁅P, P⁆ = P := by
    rw [hPdef, ← Subgroup.map_commutator, hK.perf₁]
  have hPE : P ≤ Em (Cen z) := hK.perfect P hPC hPperf
  have hK₁E : K₁ ≤ Em (Cen z) := hK.layer ▸ le_sup_left
  have key : ∀ p ∈ P, ∃ k ∈ K₁, ∃ c ∈ OddCore z, c ∈ Em (Cen z) ∧ p = k * c := by
    intro p hp
    have hpC : p ∈ Cen z := hPC hp
    obtain ⟨a, ha, rfl⟩ := hp
    have haC : a ∈ Cen z := hK.le₁ ha
    have hpC' : y * a * y⁻¹ ∈ Cen z := hPC ⟨a, ha, rfl⟩
    have hbar : toBar z ⟨y * a * y⁻¹, hpC'⟩ ∈ L₁ := by
      have h1 : toBar z ⟨a, haC⟩ ∈ L₁ := by
        rw [← hK.bar₁]
        exact bar_mem_barOf_iff.2 ⟨a, haC, ha, rfl⟩
      have h2 := hyL _ h1
      have e : (⟨y * a * y⁻¹, hpC'⟩ : ↥(Cen z)) = ⟨y, hy⟩ * ⟨a, haC⟩ * ⟨y, hy⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact h2
    rw [← hK.bar₁] at hbar
    obtain ⟨k, hkC, hkK, hk⟩ := bar_mem_barOf_iff.1 hbar
    refine ⟨k, hkK, k⁻¹ * (y * a * y⁻¹), mem_oddCore_of_toBar_eq hkC hpC' hk, ?_, ?_⟩
    swap
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    exact (Em (Cen z)).mul_mem ((Em (Cen z)).inv_mem (hK₁E hkK)) (hPE ⟨a, ha, rfl⟩)
  have hle : P ≤ K₁ := by
    refine hPperf.symm.le.trans (Subgroup.commutator_le.2 ?_)
    intro p hp p' hp'
    obtain ⟨k, hk, c, hc, hcE, rfl⟩ := key p hp
    obtain ⟨k', hk', c', hc', hc'E, rfl⟩ := key p' hp'
    rw [commutator_mul_central (hK.oddcomm c hc k' (hK₁E hk')) (hK.oddcomm c hc c' hc'E)
      (hK.oddcomm c' hc' k (hK₁E hk))]
    have h := commutator_mem_commutator hk hk'
    rwa [hK.perf₁] at h
  intro a ha
  exact hle ⟨a, ha, rfl⟩

end Data

section JBar

variable {G : Type} [Group G] [Finite G]

theorem lift_sq_eq_one {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) {J : Subgroup G} {s' : ↥J}
    (hs : (s' : G) ∈ S) (h : mkH J s' * mkH J s' = 1) : (s' : G) * (s' : G) = 1 := by
  have h2 : s' * s' ∈ pPrimeCore 2 ↥J := (mkH_eq_one_iff J).1 (by rw [map_mul]; exact h)
  have hodd := odd_orderOf_of_mem_core J h2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨(s' : G) * (s' : G), S.mul_mem hs hs⟩
  have hord : orderOf (s' * s') = 2 ^ a := by
    rw [← Subgroup.orderOf_coe (s' * s'), Subgroup.coe_mul]
    rw [← Subgroup.orderOf_coe (⟨(s' : G) * (s' : G), S.mul_mem hs hs⟩ : ↥S)] at ha
    exact ha
  rw [hord] at hodd
  have ha0 : a = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [ha0, pow_zero, orderOf_eq_one_iff] at hord
  simpa using congrArg Subtype.val hord

theorem exists_sylow_bar {z : G} {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) {J : Subgroup G}
    (hzJ : z ∈ J) (hSJ : S ≤ J) :
    ∃ T : Sylow 2 (HBar J), (T : Subgroup (HBar J)) = barIn J S ∧
      mkH J ⟨z, hzJ⟩ ∈ (T : Subgroup (HBar J)) ∧
      ∀ x ∈ (T : Subgroup (HBar J)), x * mkH J ⟨z, hzJ⟩ = mkH J ⟨z, hzJ⟩ * x := by
  obtain ⟨T, hT⟩ := barIn_sylow J ctx.sylow_top hSJ
  refine ⟨T, hT, ?_, ?_⟩
  · rw [hT]
    exact Subgroup.mem_map.2 ⟨⟨z, hzJ⟩, Subgroup.mem_subgroupOf.2 ctx.z_mem, rfl⟩
  · intro x hx
    rw [hT] at hx
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (ctx.S_comm_z (Subgroup.mem_subgroupOf.1 hs'))

end JBar

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
