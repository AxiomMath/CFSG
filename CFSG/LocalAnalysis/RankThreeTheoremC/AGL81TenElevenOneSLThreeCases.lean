module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeMatrix
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem mem_zpowers_of_mem_sup {N : Subgroup G} {x z w : G} [(zpowers z).Normal]
    (hzN : z ∈ N) (hx3 : x ^ 3 = 1) (hxN : x ∉ N) (hw : w ∈ zpowers x ⊔ zpowers z)
    (hwN : w ∈ N) : w ∈ zpowers z := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  have hbN : b ∈ N := zpowers_le.2 hzN hb
  have haN : a ∈ N := by
    have e : a = a * b * b⁻¹ := by group
    rw [e]
    exact mul_mem hwN (inv_mem hbN)
  have ha1 : a ∈ N ⊓ zpowers x := ⟨haN, ha⟩
  rw [inf_zpowers_eq_bot hx3 hxN, mem_bot] at ha1
  rw [ha1, one_mul]
  exact hb

end Group

section Model

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ}

theorem frobGL_diagTau_eq {ψ : K ≃+* K} {τ : K} (hτ : τ ^ 3 = 1) (hψτ : ψ τ = τ) :
    frobGL ψ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL, coe_diagTau_eq_diagonal, diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [hψτ]

theorem exists_isPGLAt_of_mem_sup {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (e : L ≃* slPi π 3 (p ^ f) K) {x : G} (hx : x ∈ L ⊔ centralizer (L : Set G)) :
    ∃ y ∈ slPi π 3 (p ^ f) K, IsPGLAt e x y := by
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hx
  obtain ⟨l, hl, c, hc, rfl⟩ := hx
  refine ⟨e ⟨l, hl⟩, (e ⟨l, hl⟩).2, ?_⟩
  simpa using isPGLAt_mul e (isPGLAt_of_mem e hπ hl) (isPGLAt_of_mem_centralizer e hc)

theorem not_mem_sup_of_frob (e : L ≃* slPi true 3 (p ^ f) K) {x : G} {ψ : K ≃+* K} {c : K}
    (hc : ψ c ≠ c)
    (hxψ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨x, mem_normalizer_of_normal x⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s) :
    x ∉ L ⊔ centralizer (L : Set G) := by
  intro hx
  obtain ⟨y, -, hy⟩ := exists_isPGLAt_of_mem_sup (fun h => absurd h (by decide)) e hx
  refine not_forall_frobGL_eq_conj (q := p ^ f) hc y fun s hs => ?_
  rw [← hxψ ⟨s, hs⟩, hy.2 ⟨s, hs⟩]

theorem isPGLAt_conj_of_frob (e : L ≃* slPi true 3 (p ^ f) K) {σ x : G} {ψ : K ≃+* K}
    (hσψ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {y : GL (Fin 3) K} (hy : IsPGLAt e x y) : IsPGLAt e (σ * x * σ⁻¹) (frobGL ψ y) := by
  refine ⟨mem_glPi_true _ _, fun s => ?_⟩
  have hs' : slAct e ⟨σ, mem_normalizer_of_normal σ⟩
      (slAct e ⟨σ⁻¹, mem_normalizer_of_normal σ⁻¹⟩ s) = s := by
    rw [← slAct_mul_apply]
    have : (⟨σ * σ⁻¹, mem_normalizer_of_normal _⟩ : normalizer (L : Set G)) = 1 :=
      Subtype.ext (mul_inv_cancel σ)
    rw [this, map_one, MulAut.one_apply]
  have hfs : frobGL ψ ((slAct e ⟨σ⁻¹, mem_normalizer_of_normal σ⁻¹⟩ s :
      slPi true 3 (p ^ f) K) : GL (Fin 3) K) = s := by
    rw [← hσψ, hs']
  rw [slAct_mul_apply e (σ * x) σ⁻¹ s, slAct_mul_apply, hσψ, hy.2, map_mul, map_mul, map_inv,
    hfs]

variable (hK : PiField true p f K) (hq : ModThree true (p ^ f))
  (e : L ≃* slPi true 3 (p ^ f) K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
  {t : slPi true 3 (p ^ f) K}
  (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • (1 : Matrix (Fin 3) (Fin 3) K))

include hK hq hτ hτ1 ht in
theorem exists_w_of_not_mem_of_commute {x : G} (hx3 : x ^ 3 = 1) (hxL : x ∉ L)
    {y : GL (Fin 3) K} (hy : IsPGLAt e x y) {u : GL (Fin 3) K}
    (huL : u ∈ slPi true 3 (p ^ f) K) (hus : u ∉ StatedScalars (Fin 3) K) (hu3 : u ^ 3 = 1)
    (huy : u * y = y * u) :
    ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers (e.symm t : G) := by
  obtain ⟨-, hLC⟩ := inf_centralizer_eq_zpowers hK hq e hτ hτ1 ht
  have hZn : (zpowers (e.symm t : G)).Normal := by
    rw [← hLC]
    infer_instance
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  refine ⟨(e.symm ⟨u, huL⟩ : G), ?_, ?_, fun hw => ?_⟩
  · have h1 : slAct e ⟨x, mem_normalizer_of_normal x⟩ ⟨u, huL⟩ = ⟨u, huL⟩ :=
      Subtype.ext (by rw [hy.2]; change y * u * y⁻¹ = u; rw [← huy]; group)
    exact (commute_of_slAct_eq h1).symm
  · have : (⟨u, huL⟩ : slPi true 3 (p ^ f) K) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hu3)
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  · have hwZ := mem_zpowers_of_mem_sup (e.symm t).2 hx3 hxL hw (e.symm ⟨u, huL⟩).2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hwZ
    have hut : (⟨u, huL⟩ : slPi true 3 (p ^ f) K) = t ^ k :=
      e.symm.injective (Subtype.ext (by rw [map_zpow, Subgroup.coe_zpow, hk]))
    apply hus
    have hu' : u = ((t ^ k : slPi true 3 (p ^ f) K) : GL (Fin 3) K) := congrArg Subtype.val hut
    rw [hu', Subgroup.coe_zpow]
    exact zpow_mem (mem_statedScalars_of_eq_smul ht hτ0) k

include hK hq hτ hτ1 ht in
theorem exists_w_of_mem {a : G} (ha3 : a ^ 3 = 1) (haL : a ∉ L) {ψ : K ≃+* K}
    (hψτ : ψ τ = τ)
    (haψ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨a, mem_normalizer_of_normal a⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {x : G} (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hxz : x ∉ zpowers (e.symm t : G)) :
    ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers (e.symm t : G) := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  obtain ⟨-, hLC⟩ := inf_centralizer_eq_zpowers hK hq e hτ hτ1 ht
  have hτL := diagTau_mem_slPi hπ hq' hτ
  have hXs : ((e ⟨x, hxL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K :=
    fun hs => hxz (by
      rw [← hLC]
      exact ⟨hxL, mem_centralizer_of_isPGLAt_scalar (isPGLAt_of_mem e hπ hxL) hs⟩)
  have hX3 : ((e ⟨x, hxL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 = 1 := by
    have : (⟨x, hxL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hXo : orderOf ((e ⟨x, hxL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hX3 fun h => hXs (h ▸ one_mem _)
  obtain ⟨u, huL, hu⟩ := exists_slThree_conj_diagTau hK hq hτ hτ1 (e ⟨x, hxL⟩).2 hXs hXo
  set U : G := (e.symm ⟨u, huL⟩ : G) with hU
  set D : G := (e.symm ⟨diagTau hτ, hτL⟩ : G) with hD
  have hxUD : x = U * D * U⁻¹ := by
    have h1 : e ⟨x, hxL⟩ = ⟨u, huL⟩ * ⟨diagTau hτ, hτL⟩ * (⟨u, huL⟩ : slPi true 3 (p ^ f) K)⁻¹ :=
      Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hu]
        group)
    have := congrArg (fun s => (e.symm s : G)) h1
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] at this
    exact this
  have haD : a * D = D * a :=
    commute_of_slAct_eq (Subtype.ext (by rw [haψ]; exact frobGL_diagTau_eq hτ hψτ))
  refine ⟨U * a * U⁻¹, ?_, ?_, fun hw => haL ?_⟩
  · rw [hxUD]
    calc U * a * U⁻¹ * (U * D * U⁻¹) = U * (a * D) * U⁻¹ := by group
      _ = U * (D * a) * U⁻¹ := by rw [haD]
      _ = U * D * U⁻¹ * (U * a * U⁻¹) := by group
  · rw [conj_pow, ha3, mul_one, mul_inv_cancel]
  · have hle : zpowers x ⊔ zpowers (e.symm t : G) ≤ L :=
      sup_le (zpowers_le.2 hxL) (zpowers_le.2 (e.symm t).2)
    have e1 : a = U⁻¹ * (U * a * U⁻¹) * U := by group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem (e.symm _).2) (hle hw)) (e.symm _).2

include hK hq hτ hτ1 in
theorem exists_w_of_frob {z : G} (hLC : L ⊓ centralizer (L : Set G) = zpowers z) {x : G}
    (hx3 : x ^ 3 = 1) {ψ : K ≃+* K} (hψτ : ψ τ = τ) {c : K} (hc : ψ c ≠ c)
    (hxψ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨x, mem_normalizer_of_normal x⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s) :
    ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers z := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  have hZn : (zpowers z).Normal := by
    rw [← hLC]
    infer_instance
  have hzL : z ∈ L := (hLC ▸ mem_zpowers z : z ∈ L ⊓ centralizer (L : Set G)).1
  have hτL := diagTau_mem_slPi hπ hq' hτ
  have hxL : x ∉ L := fun h => not_mem_sup_of_frob e hc hxψ (mem_sup_left h)
  refine ⟨(e.symm ⟨diagTau hτ, hτL⟩ : G), ?_, ?_, fun hw => ?_⟩
  · exact (commute_of_slAct_eq (Subtype.ext (by
      rw [hxψ]; exact frobGL_diagTau_eq hτ (hψτ)))).symm
  · have : (⟨diagTau hτ, hτL⟩ : slPi true 3 (p ^ f) K) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact diagTau_pow_three hτ)
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  · have hDz := mem_zpowers_of_mem_sup hzL hx3 hxL hw (e.symm _).2
    rw [← hLC] at hDz
    have h1 := isPGLAt_inv_mul_mem hK hq (isPGLAt_of_mem_centralizer e hDz.2)
      (isPGLAt_of_mem e hπ (e.symm ⟨diagTau hτ, hτL⟩).2)
    simp only [inv_one, one_mul, Subtype.coe_eta, MulEquiv.apply_symm_apply] at h1
    exact diagTau_not_mem_statedScalars' hτ hτ1 h1

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
