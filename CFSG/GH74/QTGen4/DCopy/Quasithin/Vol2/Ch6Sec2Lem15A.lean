module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem15A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem11L
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem14

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem sq_mem_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) {u : G} (hu : u ∈ uCh611 T L V) :
    u ^ 2 ∈ zCh611 T :=
  (h.almostSpecialHyp_Gz_F4 h331 h432 h512 h614 h615).G22_sq_mem hu

theorem comm_mem_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) {a b : G} (ha : a ∈ uCh611 T L V)
    (hb : b ∈ uCh611 T L V) : a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
  (h.commMod_ch611_F4 h331 h432 h512 h614 h615).comm a ha b hb

theorem centerOf_le_centralizer_V_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    centerOf (uCh611 T L V) ≤ Subgroup.centralizer (V : Set G) := by
  intro z hz
  by_contra hzV
  have hzT : z ∈ T := h.uCh611_le_T_F4 h331 h432 h512 h614 h615 hz.1
  have hzN : z ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer hzT
  have hzL : z ∈ Subgroup.normalizer (L : Set G) := h.toHyp611Nat.T_le_normalizer_L hzT
  have h1 : Nat.card ↥(V ⊓ Subgroup.centralizer ({z} : Set G)) ≤ 2 ^ 2 :=
    h.data.card_fixed_le_two_pow ⟨z, hzN⟩ hzL hzV
  have h8 := (stmt6_2_14_of_F4 h6210 h6211 h6212 G T M L V h hlt).2
  have hle : V ⊓ uCh611 T L V ≤ V ⊓ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz.2 x hx.2)⟩
  have := Subgroup.card_le_of_le hle
  rw [h8] at this
  omega

theorem centerOf_le_centralizer_K_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    centerOf (uCh611 T L V) ≤ Subgroup.centralizer (conjClosure V (hCh611 T) : Set G) := by
  have hZV := h.centerOf_le_centralizer_V_ch615_F4 h331 h432 h512 h614 h615 h6210 h6211 h6212 hlt
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  refine (Subgroup.closure_induction (p := fun y _ => y * z = z * y) ?_ ?_ ?_ ?_ hy)
  · rintro x ⟨g, hg, v, hv, rfl⟩
    have hz' : g⁻¹ * z * g ∈ centerOf (uCh611 T L V) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hCh611_le_normalizer_centerOf_ch615 T L V hg)) z).mp hz
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (hZV hz') v hv
    calc g * v * g⁻¹ * z = g * (v * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * v) * g⁻¹ := by rw [h1]
      _ = z * (g * v * g⁻¹) := by group
  · simp
  · intro a b _ _ ha hb
    calc a * b * z = a * (b * z) := by group
      _ = a * (z * b) := by rw [hb]
      _ = (a * z) * b := by group
      _ = (z * a) * b := by rw [ha]
      _ = z * (a * b) := by group
  · intro a _ ha
    calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * z) * a⁻¹ := by rw [ha]
      _ = z * a⁻¹ := by group

theorem centralizerMod_K_le_ch615_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4)
    (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    centralizerMod (centerOf (uCh611 T L V)) (conjClosure V (hCh611 T)) (uCh611 T L V) ≤
      centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  set Z := zCh611 T with hZdef
  set H := hCh611 T with hHdef
  set U := uCh611 T L V with hUdef
  set ZU := centerOf U with hZUdef
  have hZK := h.centerOf_le_centralizer_K_ch615_F4 h331 h432 h512 h614 h615 h6210 h6211 h6212 hlt
  obtain ⟨-, -, hO2, -, -⟩ := h6210 G T M L V h
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun g hg v hv => H.mul_mem (H.mul_mem hg (h.V_le_hCh611 hv)) (H.inv_mem hg)
  set P := H ⊓ Subgroup.centralizer (ZU : Set G) ⊓ centralizerMod ZU H U with hP
  have hPH : P ≤ H := fun x hx => hx.1.1
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    intro g hg
    have hgZU := hCh611_le_normalizer_centerOf_ch615 T L V hg
    have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (ZU : Set G) : Set G) :=
      F7.normalizer_le_normalizer_centralizer ZU hgZU
    have hgM : g ∈ Subgroup.normalizer (centralizerMod ZU H U : Set G) :=
      mem_normalizer_centralizerMod_ch62 hgZU (Subgroup.le_normalizer hg)
        (hCh611_le_normalizer_u T L V hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hP, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x),
      (Subgroup.mem_normalizer_iff.mp hgC x), (Subgroup.mem_normalizer_iff.mp hgM x)]
  have hP2 : ∀ p ∈ P, ∃ k : ℕ, p ^ 2 ^ k ∈ centralizerMod Z H U := by
    intro p hp
    obtain ⟨⟨hpH, hpZ⟩, hpM⟩ := hp
    refine ⟨1, mem_centralizerMod.mpr ⟨H.pow_mem hpH _, hCh611_le_normalizer_z T
      (H.pow_mem hpH _), fun u hu => ?_⟩⟩
    have hcu := (mem_centralizerMod.mp hpM).2.2 u hu
    have hcomm : p * (p * u * p⁻¹ * u⁻¹) = (p * u * p⁻¹ * u⁻¹) * p :=
      (Subgroup.mem_centralizer_iff.mp hpZ _ hcu).symm
    have e : p ^ 2 ^ 1 * u * (p ^ 2 ^ 1)⁻¹ * u⁻¹ = (p * u * p⁻¹ * u⁻¹) ^ 2 := by
      have e1 : p ^ 2 ^ 1 * u * (p ^ 2 ^ 1)⁻¹ * u⁻¹ =
          p * (p * u * p⁻¹ * u⁻¹) * p⁻¹ * (p * u * p⁻¹ * u⁻¹) := by
        simp only [pow_one, pow_two]; group
      rw [e1, hcomm, mul_inv_cancel_right, pow_two]
    rw [e]
    exact h.sq_mem_ch615_F4 h331 h432 h512 h614 h615 hcu.1
  have hPC := hO2 P hPH hHP hP2
  intro x hx
  obtain ⟨hxK, hxN, hxc⟩ := mem_centralizerMod.mp hx
  refine hPC ⟨⟨hKH hxK, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hZK hz) x hxK).symm⟩, mem_centralizerMod.mpr
      ⟨hKH hxK, hxN, hxc⟩⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
