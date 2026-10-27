module

public import CFSG.Fischer.Classification.Recognition.SpUBasic
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.Fischer.Classification.Recognition.SpU.U

open CFSG.Open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

theorem add_self_vecK {m : ℕ} (z : Fin m → K) : z + z = 0 := by
  rw [← two_smul K z, two_eq_zero, zero_smul]

theorem pow_four_K {μ : K} (hμ : μ ≠ 0) : μ ^ 4 = μ := by
  have h := frob_mul_self hμ
  rw [frob_apply] at h
  calc μ ^ 4 = (μ ^ 2 * μ) * μ := by ring
    _ = μ := by rw [h, one_mul]

theorem herm_v₀_smul {g : SUid frob (n + 2)} {μ : K} (hμ : μ ≠ 0) (hg : g • v₀ n = μ • v₀ n)
    (x : Fin (n + 2) → K) : herm frob (v₀ n) (g • x) = μ * herm frob (v₀ n) x := by
  have h1 : v₀ n = μ⁻¹ • g • v₀ n := by rw [hg, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  conv_lhs => rw [h1]
  rw [herm_smul_left, herm_smul_smul, frob_eq_inv (inv_ne_zero hμ), inv_inv]

theorem inv_smul_v₀ {g : SUid frob (n + 2)} {μ : K} (hμ : μ ≠ 0) (hg : g • v₀ n = μ • v₀ n) :
    g⁻¹ • v₀ n = μ⁻¹ • v₀ n := by
  rw [inv_smul_eq_iff, smul_comm, hg, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem pow_four_smul {g : SUid frob (n + 2)} {μ : K} (hμ : μ ≠ 0) (hg : g • v₀ n = μ • v₀ n)
    (hperp : ∀ y, herm frob (v₀ n) y = 0 → ∃ c : K, g • y = μ • y + c • v₀ n)
    (x : Fin (n + 2) → K) : (g ^ 4) • x = μ ^ 4 • x := by
  have h2 : ∀ x, ∃ e : K, g • g • x = μ ^ 2 • x + e • v₀ n := by
    intro x
    set a := g • x - μ • x with ha
    have hax : g • x = μ • x + a := by rw [ha]; abel
    have hav : herm frob (v₀ n) a = 0 := by
      rw [ha, herm_sub_right, herm_v₀_smul hμ hg, herm_smul_right, sub_self]
    obtain ⟨e, he⟩ := hperp a hav
    refine ⟨e, ?_⟩
    calc g • g • x = μ • (μ • x + a) + (μ • a + e • v₀ n) := by
          rw [hax, smul_add, smul_comm g μ x, hax, he]
      _ = μ ^ 2 • x + e • v₀ n + (μ • a + μ • a) := by rw [sq, mul_smul, smul_add]; abel
      _ = μ ^ 2 • x + e • v₀ n := by rw [add_self_vecK, add_zero]
  obtain ⟨e, he⟩ := h2 x
  have hv2 : g • g • v₀ n = μ ^ 2 • v₀ n := by rw [hg, smul_comm, hg, smul_smul, sq]
  calc (g ^ 4) • x = g • g • (g • g • x) := by simp only [pow_succ, pow_zero, one_mul, mul_smul]
    _ = g • g • (μ ^ 2 • x + e • v₀ n) := by rw [he]
    _ = μ ^ 2 • (g • g • x) + e • (g • g • v₀ n) := by
        rw [smul_add, smul_add, smul_comm g (μ ^ 2), smul_comm g (μ ^ 2), smul_comm g e,
          smul_comm g e]
    _ = μ ^ 2 • (μ ^ 2 • x + e • v₀ n) + e • (μ ^ 2 • v₀ n) := by rw [he, hv2]
    _ = μ ^ 4 • x + (μ ^ 2 * e + e * μ ^ 2) • v₀ n := by
        rw [smul_add, smul_smul, smul_smul, smul_smul, ← pow_add, add_assoc, ← add_smul]
    _ = μ ^ 4 • x := by
        rw [mul_comm e, ← two_mul, two_eq_zero, zero_mul, zero_smul, add_zero]

noncomputable def QU (n : ℕ) : Subgroup (SUid frob (n + 2)) where
  carrier := {g | g • v₀ n = v₀ n ∧
    ∀ y, herm frob (v₀ n) y = 0 → ∃ c : K, g • y = y + c • v₀ n}
  one_mem' := ⟨one_smul _ _, fun y _ => ⟨0, by rw [one_smul, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro g h ⟨hgv, hg⟩ ⟨hhv, hh⟩
    refine ⟨by rw [mul_smul, hhv, hgv], fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hh y hy
    obtain ⟨c', hc'⟩ := hg y hy
    exact ⟨c' + c, by rw [mul_smul, hc, smul_add, smul_comm, hgv, hc', add_smul, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨hgv, hg⟩
    have hv' : g⁻¹ • v₀ n = v₀ n := by rw [inv_smul_eq_iff, hgv]
    refine ⟨hv', fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hg (g⁻¹ • y) (by rw [← hv', herm_smul_smul, hy])
    rw [smul_inv_smul] at hc
    exact ⟨-c, by rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← hc]⟩

theorem pow_four_eq_one_of_mem_QU {x : SUid frob (n + 2)} (hx : x ∈ QU n) : x ^ 4 = 1 :=
  ext_smul _ fun z => by
    rw [pow_four_smul one_ne_zero (by rw [hx.1, one_smul]) (fun y hy => by
      obtain ⟨c, hc⟩ := hx.2 y hy
      exact ⟨c, by rw [hc, one_smul]⟩) z, one_pow, one_smul, one_smul]

theorem tvU_mul_tvU_smul {w : Fin (n + 2) → K} (hw : herm frob w w = 0)
    (hvw : herm frob (v₀ n) w = 0) {y : Fin (n + 2) → K} (hy : herm frob (v₀ n) y = 0) :
    (tvU w * tvU (v₀ n + w)) • y = y + herm frob w y • v₀ n := by
  have hwv : herm frob w (v₀ n) = 0 := herm_eq_zero_comm frob frob_frob hvw
  have hvw' : herm frob (v₀ n + w) (v₀ n + w) = 0 := by
    rw [herm_add_left, herm_add_right, herm_add_right, herm_v₀_v₀, hvw, hwv, hw, add_zero,
      add_zero]
  rw [mul_smul, tvU_smul hvw', tvU_smul hw, herm_add_left, hy, zero_add, herm_add_right,
    herm_smul_right, herm_add_right, hwv, hw, add_zero, mul_zero, add_zero, smul_add]
  calc y + (herm frob w y • v₀ n + herm frob w y • w) + herm frob w y • w =
      y + herm frob w y • v₀ n + (herm frob w y • w + herm frob w y • w) := by abel
    _ = y + herm frob w y • v₀ n := by rw [add_self_vecK, add_zero]

theorem tvU_mul_tvU_mem_QU {w : Fin (n + 2) → K} (hw : herm frob w w = 0)
    (hvw : herm frob (v₀ n) w = 0) : tvU w * tvU (v₀ n + w) ∈ QU n := by
  refine ⟨?_, fun y hy => ⟨herm frob w y, tvU_mul_tvU_smul hw hvw hy⟩⟩
  have := tvU_mul_tvU_smul hw hvw (herm_v₀_v₀ (n := n))
  rwa [herm_eq_zero_comm frob frob_frob hvw, zero_smul, add_zero] at this

theorem conj_mem_QU {g x : SUid frob (n + 2)} {μ : K} (hμ : μ ≠ 0) (hg : g • v₀ n = μ • v₀ n)
    (hx : x ∈ QU n) : g * x * g⁻¹ ∈ QU n := by
  have hg' := inv_smul_v₀ hμ hg
  refine ⟨by rw [mul_smul, mul_smul, hg', smul_comm x μ⁻¹, hx.1, smul_comm g μ⁻¹, hg,
    smul_smul, inv_mul_cancel₀ hμ, one_smul], fun y hy => ?_⟩
  have hy' : herm frob (v₀ n) (g⁻¹ • y) = 0 := by
    rw [herm_v₀_smul (inv_ne_zero hμ) hg', hy, mul_zero]
  obtain ⟨c, hc⟩ := hx.2 _ hy'
  exact ⟨c * μ, by rw [mul_smul, mul_smul, hc, smul_add, smul_inv_smul, smul_comm g c, hg,
    smul_smul]⟩

theorem exists_eq_smul_v₀ {x : Fin (n + 2) → K}
    (h : ∀ y, herm frob (v₀ n) y = 0 → herm frob x y = 0) : ∃ c : K, x = c • v₀ n := by
  have hπ : π n x = 0 := eq_zero_of_herm frob fun z => by
    rw [← herm_ι_right]
    exact h _ (herm_v₀_ι z)
  have hv : herm frob (v₀ n) x = 0 := herm_eq_zero_comm frob frob_frob (h _ herm_v₀_v₀)
  refine ⟨herm frob (u₀ n) x, ?_⟩
  conv_lhs => rw [decomp x]
  rw [hv, hπ, zero_smul, add_zero, map_zero, add_zero]

theorem exists_smul_of_forall_isotropic (hn : 2 ≤ n) {g : SUid frob (n + 2)} {μ : K}
    (hμ : μ ≠ 0) (hg : g • v₀ n = μ • v₀ n)
    (h : ∀ w, herm frob w w = 0 → herm frob (v₀ n) w = 0 → ∃ c : K, g • w = μ • w + c • v₀ n)
    {y : Fin (n + 2) → K} (hy : herm frob (v₀ n) y = 0) : ∃ c : K, g • y = μ • y + c • v₀ n := by
  have hF : ∀ z : Fin n → K, π n (g • ι n z) = μ • z := by
    have := linearMap_ext_isotropic hn
      (f := (π n).comp ((Matrix.mulVecLin ((g : GL (Fin (n + 2)) K) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) K)).comp (ι n)))
      (g := μ • LinearMap.id) fun z hz => by
        obtain ⟨c, hc⟩ := h (ι n z) (by rw [herm_ι_ι, hz]) (herm_v₀_ι z)
        show π n (((g : GL (Fin (n + 2)) K) : Matrix _ _ K) *ᵥ ι n z) = μ • z
        rw [← smul_def, hc, map_add, map_smul, map_smul, π_ι, π_v₀, smul_zero, add_zero]
    exact fun z => LinearMap.congr_fun this z
  have hgy : herm frob (v₀ n) (g • ι n (π n y)) = 0 := by
    rw [herm_v₀_smul hμ hg, herm_v₀_ι, mul_zero]
  have e1 := decomp_of_perp hy
  have e2 := decomp_of_perp hgy
  rw [hF, map_smul] at e2
  refine ⟨herm frob (u₀ n) (g • ι n (π n y)), ?_⟩
  calc g • y = g • (herm frob (u₀ n) y • v₀ n + ι n (π n y)) := by rw [← e1]
    _ = herm frob (u₀ n) y • (μ • v₀ n) + (herm frob (u₀ n) (g • ι n (π n y)) • v₀ n +
          μ • ι n (π n y)) := by rw [smul_add, smul_comm, hg, ← e2]
    _ = μ • (herm frob (u₀ n) y • v₀ n + ι n (π n y)) +
          herm frob (u₀ n) (g • ι n (π n y)) • v₀ n := by module
    _ = μ • y + herm frob (u₀ n) (g • ι n (π n y)) • v₀ n := by rw [← e1]

noncomputable def NU (n : ℕ) : Subgroup (PG (n + 2)) :=
  (QU n).map (QuotientGroup.mk' (Subgroup.center (SUid frob (n + 2))))

theorem exists_of_mem_centralizer (hn : 1 ≤ n) {c : PG (n + 2)}
    (hc : c ∈ Subgroup.centralizer {tq (v₀ n)}) :
    ∃ g : SUid frob (n + 2), (QuotientGroup.mk g : PG (n + 2)) = c ∧
      ∃ μ : K, μ ≠ 0 ∧ g • v₀ n = μ • v₀ n := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨g, rfl, ?_⟩
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 hc
  have h2 : tq (v₀ n) = tq (g • v₀ n) := by
    rw [← conj_tq g herm_v₀_v₀, h1, mul_inv_cancel_right]
  have hgv0 : g • v₀ n ≠ 0 := (smul_ne_zero_iff_ne g).2 v₀_ne_zero
  obtain ⟨μ, hμ⟩ := (tq_eq_tq_iff (by omega) v₀_ne_zero herm_v₀_v₀ hgv0
    (by rw [herm_smul_smul, herm_v₀_v₀])).1 h2
  refine ⟨μ, ?_, hμ⟩
  rintro rfl
  rw [zero_smul] at hμ
  exact hgv0 hμ

theorem NU_le_centralizer : NU n ≤ Subgroup.centralizer {tq (v₀ n)} := by
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 ?_)
  rw [QuotientGroup.mk'_apply, conj_tq x herm_v₀_v₀, hx.1]

theorem conj_mem_NU (hn : 1 ≤ n) {c x : PG (n + 2)}
    (hc : c ∈ Subgroup.centralizer {tq (v₀ n)}) (hx : x ∈ NU n) : c * x * c⁻¹ ∈ NU n := by
  obtain ⟨g, rfl, μ, hμ, hg⟩ := exists_of_mem_centralizer hn hc
  obtain ⟨x, hx, rfl⟩ := hx
  exact ⟨g * x * g⁻¹, conj_mem_QU hμ hg hx, by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩

theorem pow_four_eq_one_of_mem_NU {x : PG (n + 2)} (hx : x ∈ NU n) : x ^ 4 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hx
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow, pow_four_eq_one_of_mem_QU hx,
    QuotientGroup.mk_one]

theorem exists_smul_of_commute (hn : 1 ≤ n) {g : SUid frob (n + 2)} {μ : K} (hμ : μ ≠ 0)
    (hg : g • v₀ n = μ • v₀ n)
    (hcomm : ∀ x ∈ NU n, (QuotientGroup.mk g : PG (n + 2)) * x = x * QuotientGroup.mk g)
    {w : Fin (n + 2) → K} (hw : herm frob w w = 0) (hvw : herm frob (v₀ n) w = 0) :
    ∃ c : K, g • w = μ • w + c • v₀ n := by
  set q := tvU w * tvU (v₀ n + w)
  have hqQ : q ∈ QU n := tvU_mul_tvU_mem_QU hw hvw
  have hgq := conj_mem_QU hμ hg hqQ
  have hc' : (QuotientGroup.mk g : PG (n + 2)) * QuotientGroup.mk q =
      QuotientGroup.mk q * QuotientGroup.mk g := hcomm _ ⟨q, hqQ, rfl⟩
  have hmk : (QuotientGroup.mk (g * q * g⁻¹) : PG (n + 2)) = QuotientGroup.mk q := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc',
      mul_inv_cancel_right]
  rw [QuotientGroup.eq, center_SUid (by omega)] at hmk
  obtain ⟨l, hl⟩ := exists_smul_eq_of_mem_scalars hmk
  have hl1 : l = 1 := by
    have h := hl (v₀ n)
    rw [mul_smul, hqQ.1, inv_smul_eq_iff, smul_comm (g * q * g⁻¹) l (v₀ n), hgq.1] at h
    have : (1 - l) • v₀ n = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right v₀_ne_zero)).symm
  have hqx : ∀ x, q • x = (g * q * g⁻¹) • x := fun x => by
    have h := hl x
    rw [hl1, one_smul, mul_smul, inv_smul_eq_iff] at h
    exact h
  have hy : ∀ y, herm frob (v₀ n) y = 0 → herm frob (frob μ • g • w - w) y = 0 := by
    intro y hy
    have hy' : herm frob (v₀ n) (g⁻¹ • y) = 0 := by
      rw [herm_v₀_smul (inv_ne_zero hμ) (inv_smul_v₀ hμ hg), hy, mul_zero]
    have e := hqx y
    rw [tvU_mul_tvU_smul hw hvw hy, mul_smul, mul_smul, tvU_mul_tvU_smul hw hvw hy', smul_add,
      smul_inv_smul, smul_comm g, hg, smul_smul, add_right_inj] at e
    have e' := smul_left_injective K v₀_ne_zero e
    have hgw : herm frob w (g⁻¹ • y) = herm frob (g • w) y := by
      rw [← herm_smul_smul frob g w (g⁻¹ • y), smul_inv_smul]
    rw [herm_sub_left, herm_smul_left, frob_frob, ← hgw, e']
    ring
  obtain ⟨c, hc⟩ := exists_eq_smul_v₀ hy
  refine ⟨μ * c, ?_⟩
  rw [frob_eq_inv hμ, sub_eq_iff_eq_add'] at hc
  calc g • w = μ • (μ⁻¹ • g • w) := by rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
    _ = μ • w + (μ * c) • v₀ n := by rw [hc, smul_add, smul_smul]

theorem not_isComponentOf_centralizer (hn : 2 ≤ n) (L : Subgroup (PG (n + 2))) :
    ¬ IsComponentOf L (Subgroup.centralizer {tq (v₀ n)}) := by
  intro hL
  refine SpU.not_isComponentOf hL NU_le_centralizer
    (fun c hc x hx => conj_mem_NU (by omega) hc hx) (fun x hx => pow_four_eq_one_of_mem_NU hx)
    fun c hc hcomm => ?_
  obtain ⟨g, rfl, μ, hμ, hg⟩ := exists_of_mem_centralizer (by omega) hc
  have hperp : ∀ y, herm frob (v₀ n) y = 0 → ∃ e : K, g • y = μ • y + e • v₀ n :=
    fun y hy => exists_smul_of_forall_isotropic hn hμ hg
      (fun w hw hvw => exists_smul_of_commute (by omega) hμ hg hcomm hw hvw) hy
  have h4 : ∀ x, (g ^ 4) • x = μ • x := fun x => by
    rw [pow_four_smul hμ hg hperp x, pow_four_K hμ]
  have hz : g ^ 4 ∈ Subgroup.center (SUid frob (n + 2)) :=
    Subgroup.mem_center_iff.2 fun h => ext_smul _ fun x => by
      rw [mul_smul, mul_smul, h4, h4, smul_comm h μ x]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hz

end CFSG.Fischer.Classification.Recognition.SpU.U

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open Matrix CFSG.Fischer.Classification.Unitary

theorem not_isComponentOf_case4 {G : Type} [Group G] {D : Set G}
    (hN : ∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0))
    {d : G} (hd : d ∈ D) (K : Subgroup G) :
    ¬ IsComponentOf K (Subgroup.centralizer ({d} : Set G)) := by
  intro hK
  obtain ⟨m, hm, hmodel⟩ := hN
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmodel
  set ψ := φ.trans (u2Equiv (n + 2))
  have hψd : ψ d ∈ DG (n + 2) := by
    rw [← image_DU, ← hφ]
    exact ⟨φ d, ⟨d, hd, rfl⟩, rfl⟩
  obtain ⟨v, hv0, hv, hvd⟩ := hψd
  obtain ⟨u, -, hu, hvu⟩ := exists_partner_frob hv0 hv
  obtain ⟨g, hgv, -⟩ := exists_smul_eq_hyp (by omega) hv0 hv hu hvu
  set χ := ψ.trans (MulAut.conj (QuotientGroup.mk g : PG (n + 2))) with hχ
  have hχd : χ d = tq (v₀ n) := by
    rw [hχ, MulEquiv.trans_apply, MulAut.conj_apply, ← hvd, conj_tq g hv, hgv]
  have h := IsComponentOf.map_mulEquiv χ hK
  rw [map_centralizer_singleton, hχd] at h
  exact SpU.U.not_isComponentOf_centralizer (by omega) _ h

theorem componentOrder_case4 {G : Type} [Group G] [Finite G] {D : Set G} (_hH : Hyp G D)
    (hN : ∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0))
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders :=
  (not_isComponentOf_case4 hN hd K hK).elim

end CFSG.Fischer.Classification.Recognition
