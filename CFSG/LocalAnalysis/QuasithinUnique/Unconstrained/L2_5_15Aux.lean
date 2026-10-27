module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Aux
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem normalizer_closure_of_forall [Finite G] {s : Set G} {x : G}
    (hx : ∀ g ∈ s, x * g * x⁻¹ ∈ Subgroup.closure s) :
    x ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem g hg => exact hx g hg
  | one => simp
  | mul a b _ _ ha hb =>
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
      have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha

theorem conjAct_apply' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : ↥V) :
    ((conjAct V g x : ↥V) : G) = (g : G) * x * (g : G)⁻¹ := rfl

theorem isPGroup_two_of_sq {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using h x.1 x.2

theorem odd_orbit_card [Finite G] (N : Subgroup G) (t : G) (U : Subgroup G)
    (hUt : ∀ u ∈ U, u * t = t * u) (hU : ¬ 2 ∣ (U.subgroupOf N).index) :
    ¬ 2 ∣ Nat.card {o : G // ∃ n ∈ N, o = n * t * n⁻¹} := by
  classical
  let _ : MulAction N G :=
    { smul := fun n g => (n : G) * g * (n : G)⁻¹
      one_smul := fun g => by simp [HSMul.hSMul, SMul.smul]
      mul_smul := fun a b g => by simp [HSMul.hSMul, SMul.smul, mul_assoc] }
  have hsmul : ∀ (n : N) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun n g => rfl
  have horb : Nat.card {o : G // ∃ n ∈ N, o = n * t * n⁻¹} =
      Nat.card (MulAction.orbit N t) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun o => ?_
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, rfl⟩
  have hidx : (MulAction.stabilizer N t).index = Nat.card (MulAction.orbit N t) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [horb, ← hidx]
  intro hdvd
  have hle : U.subgroupOf N ≤ MulAction.stabilizer N t := by
    intro u hu
    rw [MulAction.mem_stabilizer_iff, hsmul]
    have := hUt u (Subgroup.mem_subgroupOf.mp hu)
    calc (u : G) * t * (u : G)⁻¹ = t * (u : G) * (u : G)⁻¹ := by rw [this]
      _ = t := by group
  exact hU (hdvd.trans (Subgroup.index_dvd_of_le hle))

theorem card_le_mul_of_cover [Finite G] {R C : Subgroup G} (hCR : C ≤ R) {n : ℕ} (g : Fin n → G)
    (hg : ∀ i, g i ∈ R) (hcov : ∀ r ∈ R, ∃ i, ∃ c ∈ C, r = c * g i) :
    Nat.card R ≤ n * Nat.card C := by
  classical
  have h1 := (C.subgroupOf R).index_mul_card
  have hC : Nat.card (C.subgroupOf R) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv
  have hidx : (C.subgroupOf R).index ≤ n := by
    rw [Subgroup.index]
    have := Nat.card_le_card_of_surjective
      (fun i : Fin n => (QuotientGroup.mk ⟨(g i)⁻¹, R.inv_mem (hg i)⟩ : R ⧸ C.subgroupOf R)) (by
        intro q
        obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨i, c, hc, hrc⟩ := hcov r⁻¹ (R.inv_mem hr)
        refine ⟨i, ?_⟩
        show (QuotientGroup.mk ⟨(g i)⁻¹, R.inv_mem (hg i)⟩ : R ⧸ C.subgroupOf R) =
          QuotientGroup.mk ⟨r, hr⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        show ((g i)⁻¹)⁻¹ * r ∈ C
        have : r = (g i)⁻¹ * c⁻¹ := by
          calc r = (r⁻¹)⁻¹ := by group
            _ = (c * g i)⁻¹ := by rw [← hrc]
            _ = (g i)⁻¹ * c⁻¹ := by group
        rw [this]
        simpa using C.inv_mem hc)
    simpa using this
  rw [hC] at h1
  calc Nat.card R = (C.subgroupOf R).index * Nat.card C := h1.symm
    _ ≤ n * Nat.card C := Nat.mul_le_mul_right _ hidx

theorem twoPart_eq_sixteen {X : Subgroup G} {b : ℕ} (hb : ¬ 2 ∣ b)
    (hX : Nat.card X = 16 * b) : twoPart X = 16 := by
  unfold twoPart
  have h16 : 16 * b = 2 ^ 4 * b := by norm_num
  rw [hX, h16, factorization_two_pow_mul hb]
  norm_num

theorem exists_elemAbelian_sup_zpowers [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) {n : ℕ} (hEcard : Nat.card E = p ^ n) {c : G}
    (hcp : c ^ p = 1) (hc1 : c ≠ 1) (hcom : ∀ e ∈ E, e * c = c * e) (hcE : c ∉ E) :
    CFSG.Assembly.IsElemAbelian p (E ⊔ Subgroup.zpowers c) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers c) = p ^ (n + 1) := by
  have ho : orderOf c = p := by
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hzc : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, ho]
  have hc : ∀ x ∈ E, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x c from hcom x hx) k).eq
  have hpowB : ∀ v ∈ Subgroup.zpowers c, v ^ p = 1 := by
    intro v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  have hinf : E ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyc⟩
    rw [Subgroup.mem_bot]
    by_contra hy1
    have hyp : y ^ p = 1 := hpowB y hyc
    have hyo : orderOf y = p := by
      have h1 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hyc
    have hcard : Nat.card (Subgroup.zpowers c) ≤ Nat.card (Subgroup.zpowers y) := by
      rw [hzc, Nat.card_zpowers, hyo]
    have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    apply hcE
    have : c ∈ Subgroup.zpowers y := by rw [heq]; exact Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hyE) this
  have hmem : ∀ x : G, x ∈ E ⊔ Subgroup.zpowers c ↔
      ∃ u ∈ E, ∃ v ∈ Subgroup.zpowers c, u * v = x := fun x =>
    BenderBranch.mem_sup_iff_of_commute hc
  have hcomA : ∀ u u' : G, u ∈ E → u' ∈ E → u * u' = u' * u := by
    intro u u' hu hu'
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : E) ⟨u', hu'⟩)
  have hcomB : ∀ v v' : G, v ∈ Subgroup.zpowers c → v' ∈ Subgroup.zpowers c →
      v * v' = v' * v := by
    intro v v' hv hv'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    exact (Commute.zpow_zpow_self c m k).eq
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨u, hu, v, hv, hx⟩ := (hmem x.1).mp x.2
    obtain ⟨u', hu', v', hv', hy⟩ := (hmem y.1).mp y.2
    have c1 : Commute u u' := hcomA u u' hu hu'
    have c2 : Commute v v' := hcomB v v' hv hv'
    have c3 : Commute u v' := hc u hu v' hv'
    have c4 : Commute v u' := (hc u' hu' v hv).symm
    show (x : G) * y = y * x
    rw [← hx, ← hy]
    exact ((c1.mul_right c3).mul_left (c4.mul_right c2)).eq
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (hmem x).mp hx
    have hcuv : Commute u v := hc u hu v hv
    rw [hcuv.mul_pow, hE.2 u hu, hpowB v hv, one_mul]
  · rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hc hinf, hEcard, hzc, pow_succ]

end Generic

end CFSG.QuasithinUnique.Unc25K1
