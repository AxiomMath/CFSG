module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322D

public section
namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

section Theta

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem mem_M_of_conj_eq_mul_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e)
    {c c' g : G} (hcL : c ∈ Subgroup.centralizer (L : Set G))
    (hc'Z : c' ∈ quasithinOmegaOneCenter T) (hc'L : c' ∈ Subgroup.centralizer (L : Set G))
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hgz : g * (c * e) * g⁻¹ = c' * e) : g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set f := (MulAut.conj g).toMonoidHom with hf
  have hLθz : lTheta L (e : G) ≤ Subgroup.centralizer ({c * (e : G)} : Set G) :=
    (lTheta_mul_eq hcL (e : G)) ▸ lTheta_le_centralizer L (c * e)
  have h1 : (lTheta L (e : G)).map f ≤ lTheta L e := by
    calc (lTheta L (e : G)).map f ≤ (thetaOf (lTheta L (e : G))).map f :=
          Subgroup.map_mono (lTheta_le_thetaOf h hTL hc he heZ)
      _ ≤ thetaOf ((lTheta L (e : G)).map f) := map_thetaOf_le _ f (MulAut.conj g).injective
      _ ≤ thetaOf (Subgroup.centralizer ({c' * (e : G)} : Set G)) := by
          apply A7.theta_mono
          rw [← hgz]
          exact (Subgroup.map_mono hLθz).trans (map_conj_centralizer_le g _)
      _ ≤ lTheta L e := hθ c' hc'Z hc'L
  have heq : (lTheta L (e : G)).map f = lTheta L e :=
    Subgroup.eq_of_le_of_card_ge h1 (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hgLθ : g ∈ Subgroup.normalizer ((lTheta L (e : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq
  have hgN : g ∈ Subgroup.normalizer ((lTheta L (e : G) ⊔ T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hgLθ, Subgroup.mem_normalizer_iff_map_conj_eq.1 hgT]
  have hgR : g ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := by
    rw [← pCoreOf_lTheta_sup h7 h hML hTL hc he heZ]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hgN
  exact normalizer_le_M h5 h hML (pCoreOf_ne_bot_of_vec_six h he)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hgR

theorem mem_M_of_conj_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e)
    {z g : G} (hz : z ∈ (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers (e : G)) (hz1 : z ≠ 1)
    (hgz : g * z * g⁻¹ ∈ (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers (e : G)) (hgT : g ∈ Subgroup.normalizer (T : Set G)) : g ∈ M := by
  have he1 := coe_ne_one_of_vec_six he
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨c, hcC, hz'⟩ := exists_of_mem_sup_zpowers heZ he1 hz
  obtain ⟨c', hc'C, hgz'⟩ := exists_of_mem_sup_zpowers heZ he1 hgz
  rcases hz' with rfl | rfl <;> rcases hgz' with hgz' | hgz'
  · exact mem_M_of_conj_mem_centralizer h5 h hML hcC.1 hcC.2 hz1 (hgz' ▸ hc'C.1)
      (hgz' ▸ hc'C.2)
  · exact (false_of_conj_eq_mul h hc he hθ hcC.2 hc'C.1 hc'C.2 hgz').elim
  · refine (false_of_conj_eq_mul h hc he hθ (g := g⁻¹) (z := g * (c * e) * g⁻¹)
      (hgz' ▸ hc'C.2) hcC.1 hcC.2 ?_).elim
    group
  · exact mem_M_of_conj_eq_mul_F4 h5 h7 h14 h hc he heZ hθ hcC.2 hc'C.1 hc'C.2 hgT hgz'

end Theta

section Center

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem omegaOneCenter_inf_centralizer_eq_bot_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7)
    (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D) (hc : Coord322 T L ψ)
    {a b : ↥⁅vPlus L T, L⁆} (ha : vec ψ a = vecZO) (hb : vec ψ b = A7.vecSix)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (b : G)} : Set G)) ≤ lTheta L b) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set Z := quasithinOmegaOneCenter T with hZ
  set C := Z ⊓ Subgroup.centralizer (L : Set G) with hC
  set Zθ := C ⊔ Subgroup.zpowers (b : G) with hZθ
  have haZ : (a : G) ∈ Z := (mem_Z_iff h hTL hc a).2 (Or.inr (Or.inl ha))
  have hbZ : (b : G) ∈ Z := (mem_Z_iff h hTL hc b).2 (Or.inr (Or.inr (Or.inr hb)))
  have ha2 : (a : G) * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_omegaOneCenter T haZ
  have hb1 := coe_ne_one_of_vec_six hb
  obtain ⟨d, hdD, hdM⟩ := exists_mem_D_not_mem_M h
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hdZ : ∀ x ∈ Z, d * x * d⁻¹ ∈ Z := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_quasithinOmegaOneCenter T hdT) x).1 hx
  have hcos : ∀ x ∈ Z, x ∈ Zθ ∨ (a : G)⁻¹ * x ∈ Zθ := by
    intro x hx
    obtain ⟨c, hcC, hx'⟩ := exists_eq_of_mem_omegaOneCenter h hML hTL hc ha hb hx
    have hc' : c ∈ Zθ := Subgroup.mem_sup_left hcC
    have hbc : (b : G) * c ∈ Zθ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hc'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact Or.inl hc'
    · exact Or.inl hbc
    · right
      rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact hc'
    · right
      rw [show (a : G)⁻¹ * (a * b * c) = b * c by group]
      exact hbc
  have hout : ∀ x ∈ Zθ, x ≠ 1 → (a : G)⁻¹ * (d * x * d⁻¹) ∈ Zθ := by
    intro x hx hx1
    have hxZ : x ∈ Z := sup_le inf_le_left (Subgroup.zpowers_le.2 hbZ) hx
    rcases hcos _ (hdZ x hxZ) with h1 | h1
    · exact absurd (mem_M_of_conj_F4 h5 h7 h14 h hc hb (hbZ) hθ hx hx1 h1 hdT) hdM
    · exact h1
  rw [eq_bot_iff]
  intro c hcC
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hcb1 : c * (b : G) ≠ 1 := by
    intro h1
    have hbc : (b : G) = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine hb1 (congrArg Subtype.val (eq_one_of_centralizer hc b fun l hl => ?_))
    rw [hbc]
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hcC.2) l hl
  have h1 := hout c (Subgroup.mem_sup_left hcC) hc1
  have h2 := hout b (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hb1
  set u := (a : G)⁻¹ * (d * c * d⁻¹) with hu
  set v := (a : G)⁻¹ * (d * b * d⁻¹) with hv
  have huZ : u ∈ Z := sup_le inf_le_left (Subgroup.zpowers_le.2 hbZ) h1
  have hprod : d * (c * b) * d⁻¹ = u * v := by
    have hau : (a : G) * u = u * a := omegaOneCenter_comm T haZ huZ
    calc d * (c * b) * d⁻¹ = (a * u) * (a * v) := by rw [hu, hv]; group
      _ = (u * a) * (a * v) := by rw [hau]
      _ = u * (a * a) * v := by group
      _ = u * v := by rw [ha2, mul_one]
  have h4 : d * (c * b) * d⁻¹ ∈ Zθ := hprod ▸ Subgroup.mul_mem _ h1 h2
  exact hdM (mem_M_of_conj_F4 h5 h7 h14 h hc hb hbZ hθ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) hcb1 h4 hdT)

theorem exists_conj_eq_F4 (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {a b : ↥⁅vPlus L T, L⁆}
    (ha : vec ψ a = vecZO) (hb : vec ψ b = A7.vecSix)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (b : G)} : Set G)) ≤ lTheta L b) :
    ∃ d ∈ D, d * (a : G) * d⁻¹ = b := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hC := omegaOneCenter_inf_centralizer_eq_bot_F4 h5 h7 h14 h hc ha hb hθ
  set Z := quasithinOmegaOneCenter T with hZ
  have haZ : (a : G) ∈ Z := (mem_Z_iff h hTL hc a).2 (Or.inr (Or.inl ha))
  have hbZ : (b : G) ∈ Z := (mem_Z_iff h hTL hc b).2 (Or.inr (Or.inr (Or.inr hb)))
  have ha2 : (a : G) * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_omegaOneCenter T haZ
  have hb1 := coe_ne_one_of_vec_six hb
  have ha1 : (a : G) ≠ 1 := by
    intro h1
    have h2 : a = 1 := Subtype.ext h1
    rw [h2, A7.vec_one] at ha
    exact absurd ha (by decide +kernel)
  have hZ4 : ∀ x ∈ Z, x = 1 ∨ x = b ∨ x = a ∨ x = a * b := by
    intro x hx
    obtain ⟨c, hcC, hx'⟩ := exists_eq_of_mem_omegaOneCenter h hML hTL hc ha hb hx
    rw [hC, Subgroup.mem_bot] at hcC
    subst hcC
    simpa using hx'
  obtain ⟨d, hdD, hdM⟩ := exists_mem_D_not_mem_M h
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hdZ : ∀ x ∈ Z, d * x * d⁻¹ ∈ Z := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_quasithinOmegaOneCenter T hdT) x).1 hx
  have hbθ : (b : G) ∈ (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers (b : G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hdb : d * b * d⁻¹ ≠ b := by
    intro h1
    apply hdM
    refine mem_M_of_conj_F4 h5 h7 h14 h hc hb hbZ hθ hbθ hb1 ?_ hdT
    rw [h1]
    exact hbθ
  have hne : ∀ x : G, x ≠ 1 → d * x * d⁻¹ ≠ 1 := fun x hx h1 => hx (by
    calc x = d⁻¹ * (d * x * d⁻¹) * d := by group
      _ = 1 := by rw [h1]; group)
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h.Dodd.of_dvd_nat h1
  rcases hZ4 _ (hdZ _ hbZ) with h1 | h1 | h1 | h1
  · exact absurd h1 (hne _ hb1)
  · exact absurd h1 hdb
  ·
    refine ⟨d⁻¹, inv_mem hdD, ?_⟩
    rw [← h1]
    group
  · rcases hZ4 _ (hdZ _ haZ) with h2 | h2 | h2 | h2
    · exact absurd h2 (hne _ ha1)
    · exact ⟨d, hdD, h2⟩
    ·
      exfalso
      have hsq : d ^ 2 * b * (d ^ 2)⁻¹ = b := by
        calc d ^ 2 * b * (d ^ 2)⁻¹ = d * (d * b * d⁻¹) * d⁻¹ := by rw [sq]; group
          _ = d * (a * b) * d⁻¹ := by rw [h1]
          _ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
          _ = a * (a * b) := by rw [h2, h1]
          _ = b := by rw [← mul_assoc, ha2, one_mul]
      have hcomm : Commute (d ^ 2) b := by
        show d ^ 2 * b = b * d ^ 2
        calc d ^ 2 * b = d ^ 2 * b * (d ^ 2)⁻¹ * d ^ 2 := by group
          _ = b * d ^ 2 := by rw [hsq]
      have h3 : d * b = b * d := (commute_of_sq hodd hcomm).eq
      apply hdb
      rw [h3, mul_inv_cancel_right]
    ·
      exfalso
      have h3 : d * a * d⁻¹ = d * b * d⁻¹ := by rw [h1, h2]
      have hab : a = b := Subtype.ext (mul_left_cancel (mul_right_cancel h3))
      rw [hab, hb] at ha
      exact absurd ha (by decide +kernel)

end Center

end CFSG.Quasithin.H13.L3322
