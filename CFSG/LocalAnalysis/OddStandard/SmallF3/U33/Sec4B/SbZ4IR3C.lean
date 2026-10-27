module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR3B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {N Q Y V V' B K : Subgroup X} {ρ t τ l : X} [N.Normal]

private lemma toZE_card_B (h : Z4IData N Q Y V V' B K ρ t τ l) :
    Nat.card (B.map (z4iπ N)) = 16 := by
  rw [z4i_card_map N h.odd_N (h.isPGroup_Q.to_le h.B_le_Q), h.card_B]

private lemma toZE_Y_sq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ y ∈ Y.map (z4iπ N), y * y = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, h.Y_sq y hy, map_one]

private lemma toZE_normal {A : Subgroup X}
    (hA : ∀ g x : X, x ∈ A → g * x * g⁻¹ ∈ A) :
    ∀ g x : X ⧸ N, x ∈ A.map (z4iπ N) → g * x * g⁻¹ ∈ A.map (z4iπ N) := by
  intro g x hx
  obtain ⟨g0, rfl⟩ := z4iπ_surjective N g
  obtain ⟨x0, hx0, rfl⟩ := hx
  rw [← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem (z4iπ N) (hA g0 x0 hx0)

private lemma toZE_t_sq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N t * z4iπ N t = 1 := by
  rw [← map_mul, h.t_sq, map_one]

private lemma toZE_tau_sq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N τ * z4iπ N τ = 1 := by
  rw [← map_mul, h.tau_sq, map_one]

private lemma toZE_l_sq (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N l * z4iπ N l = 1 := by
  rw [← map_mul, h.l_sq, map_one]

private lemma toZE_t_tau (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N t * z4iπ N τ = z4iπ N τ * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_tau]

private lemma toZE_t_l (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N t * z4iπ N l = z4iπ N l * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_l]

private lemma toZE_tau_l (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N τ * z4iπ N l = z4iπ N l * z4iπ N τ := by
  rw [← map_mul, ← map_mul, h.tau_l]

private lemma toZE_t_rho (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N t * z4iπ N ρ = z4iπ N ρ * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_rho]

private lemma toZE_tau_rho (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N τ * z4iπ N ρ = z4iπ N ρ * z4iπ N τ := by
  rw [← map_mul, ← map_mul, h.tau_rho]

private lemma toZE_l_rho (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N l * z4iπ N ρ * (z4iπ N l)⁻¹ = (z4iπ N ρ)⁻¹ := by
  rw [← map_mul, ← map_inv, ← map_mul, h.l_rho, map_inv]

private lemma toZE_norm {A : Subgroup X} {a : X} (ha : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    ∀ x ∈ A.map (z4iπ N), z4iπ N a * x * (z4iπ N a)⁻¹ ∈ A.map (z4iπ N) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem (z4iπ N) (ha x hx)

private lemma toZE_comm_t_K (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ k ∈ K.map (z4iπ N),
      z4iπ N t * k * (z4iπ N t)⁻¹ * k⁻¹ ∈ Q.map (z4iπ N) := by
  rintro _ ⟨k, hk, rfl⟩
  have h1 : z4iπ N t * z4iπ N k * (z4iπ N t)⁻¹ * (z4iπ N k)⁻¹
      = z4iπ N (t * k * t⁻¹ * k⁻¹) := by
    simp only [map_mul, map_inv]
  rw [h1]
  exact (z4iπ_mem_map_iff N (A := Q) (x := t * k * t⁻¹ * k⁻¹)).mpr (h.comm_t_K k hk)

private lemma toZE_tau_inv (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N τ * q * (z4iπ N τ)⁻¹ = q⁻¹ := by
  rintro _ ⟨q, hq, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul, h.tau_inv q hq, map_inv]

private lemma toZE_tau_not_mem_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    z4iπ N τ ∉ Q.map (z4iπ N) :=
  fun hmem => h.tau_not_mem_Q ((z4iπ_mem_map_iff N (A := Q) (x := τ)).mp hmem)

private lemma toZE_B_cent_t (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ b ∈ B.map (z4iπ N), z4iπ N t * b = b * z4iπ N t := by
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h.B_cent_t b hb]

private lemma toZE_V_cent_t (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ v ∈ V.map (z4iπ N), z4iπ N t * v = v * z4iπ N t := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, h.V_cent_t v hv]

private lemma toZE_cent_t_Q (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N t * q = q * z4iπ N t → q ∈ B.map (z4iπ N) := by
  rintro _ ⟨q, hq, rfl⟩ hcomm
  exact Subgroup.mem_map_of_mem (z4iπ N) (h.cent_t_Q q hq
    (z4i_commute_of_map N h.Q_inf_N (fun x hx => h.normal_Q t x hx) hq hcomm))

private lemma toZE_Y_cent_t (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ y ∈ Y.map (z4iπ N), z4iπ N t * y = y * z4iπ N t → y ∈ V.map (z4iπ N) := by
  rintro _ ⟨y, hy, rfl⟩ hcomm
  exact Subgroup.mem_map_of_mem (z4iπ N) (h.Y_cent_t y hy
    (z4i_commute_of_map N h.Q_inf_N (fun x hx => h.normal_Q t x hx) (h.Y_le_Q hy) hcomm))

private lemma toZE_bound (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ R : Subgroup (X ⧸ N), IsPGroup 2 R →
      R ≤ centralizer ({z4iπ N t} : Set (X ⧸ N)) → Nat.card R ≤ 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht_ord : orderOf t = 2 := orderOf_eq_prime (by rw [sq, h.t_sq]) h.t_ne_one
  have hA : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht_ord]
    norm_num
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker N]; exact h.odd_N
  intro R hR hRc
  have hRc' : R ≤ centralizer (((zpowers t).map (z4iπ N) : Subgroup (X ⧸ N)) :
      Set (X ⧸ N)) := by
    rw [MonoidHom.map_zpowers]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ :=
      Subgroup.mem_zpowers_iff.mp (show y ∈ Subgroup.zpowers (z4iπ N t) from hy)
    have hcomm : Commute (z4iπ N t) r :=
      (Subgroup.mem_centralizer_iff.mp (hRc hr)) (z4iπ N t) (Set.mem_singleton _)
    exact hcomm.zpow_left n
  obtain ⟨P', hP', hmap, hP'c, -⟩ :=
    z4i_lift_two_cent (z4iπ N) (z4iπ_surjective N) hker hA hR hRc'
  have hle : P' ≤ centralizer ({t} : Set X) :=
    le_trans hP'c (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers t)))
  have hcard : Nat.card R = Nat.card P' := by rw [← hmap, z4i_card_map N h.odd_N hP']
  rw [hcard]
  exact h.bound P' hP' hle

private lemma toZE_not_conj (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ∀ g : X ⧸ N, g * z4iπ N t * g⁻¹ ≠ z4iπ N t * z4iπ N τ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht_ord : orderOf t = 2 := orderOf_eq_prime (by rw [sq, h.t_sq]) h.t_ne_one
  have htau_inv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.tau_sq
  have htτ_sq : (t * τ) ^ 2 = 1 := by
    rw [sq]
    calc t * τ * (t * τ) = t * (τ * t) * τ := by group
      _ = t * (t * τ) * τ := by rw [← h.t_tau]
      _ = (t * t) * (τ * τ) := by group
      _ = 1 := by rw [h.t_sq, h.tau_sq, mul_one]
  have htτ_ne : t * τ ≠ 1 := by
    intro h1
    exact h.t_ne_tau ((mul_eq_one_iff_eq_inv.mp h1).trans htau_inv)
  have htτ_ord : orderOf (t * τ) = 2 := orderOf_eq_prime htτ_sq htτ_ne
  intro g hg
  obtain ⟨g0, rfl⟩ := z4iπ_surjective N g
  have hconj_ord : orderOf (g0 * t * g0⁻¹) = 2 := by
    rw [← MulAut.conj_apply g0 t, MulEquiv.orderOf_eq, ht_ord]
  have hmk : ((g0 * t * g0⁻¹ : X) : X ⧸ N) = (t * τ : X) := by
    change z4iπ N (g0 * t * g0⁻¹) = z4iπ N (t * τ)
    rw [map_mul, map_mul, map_inv]
    exact hg
  obtain ⟨m, -, hm⟩ := CFSG.RankThree.OddKernel.isConj_of_mk_eq N h.odd_N hconj_ord htτ_ord hmk
  exact h.not_conj (m * g0) (by
    have he : m * g0 * t * (m * g0)⁻¹ = m * (g0 * t * g0⁻¹) * m⁻¹ := by group
    rw [he, hm])

theorem Z4IData.toZEData (h : Z4IData N Q Y V V' B K ρ t τ l) :
    ZEData (Q.map (z4iπ N)) (Y.map (z4iπ N)) (V.map (z4iπ N)) (V'.map (z4iπ N))
      (B.map (z4iπ N)) (K.map (z4iπ N)) (z4iπ N ρ) (z4iπ N t) (z4iπ N τ) (z4iπ N l) :=
  { toZIKData := h.toZIKData
    card_B := toZE_card_B h
    Y_sq := toZE_Y_sq h
    normal_Q := toZE_normal h.normal_Q
    normal_Y := toZE_normal h.normal_Y
    normal_V := toZE_normal h.normal_V
    t_sq := toZE_t_sq h
    tau_sq := toZE_tau_sq h
    l_sq := toZE_l_sq h
    t_tau := toZE_t_tau h
    t_l := toZE_t_l h
    tau_l := toZE_tau_l h
    t_rho := toZE_t_rho h
    tau_rho := toZE_tau_rho h
    l_rho := toZE_l_rho h
    t_norm_K := toZE_norm h.t_norm_K
    tau_norm_K := toZE_norm h.tau_norm_K
    l_norm_K := toZE_norm h.l_norm_K
    comm_t_K := toZE_comm_t_K h
    tau_inv := toZE_tau_inv h
    tau_not_mem_Q := toZE_tau_not_mem_Q h
    B_cent_t := toZE_B_cent_t h
    cent_t_Q := toZE_cent_t_Q h
    V_cent_t := toZE_V_cent_t h
    Y_cent_t := toZE_Y_cent_t h
    bound := toZE_bound h
    not_conj := toZE_not_conj h }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
