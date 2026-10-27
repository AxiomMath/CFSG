module

public import CFSG.GH74.GLS.Stage4.HexCG2
public import CFSG.GH74.GLS.Stage4.HexCSt3
public import CFSG.GH74.GLS.Stage4.HexCAsm3
public import CFSG.GH74.GLS.Stage4.HexCNondeg2

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem g2_coords_p3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {H : Subgroup G}
    {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G} (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) {q : ℕ} (hqodd : Odd q) (h5 : 5 ≤ q) (hq : RootOrdersG2 root q)
    (hP : PStruct 3 U root) (h1 : SL2At H R.N root 1) (h4 : SL2At H R.N root 4)
    (hO : OrthPair root) (hL : LongA2 root) (hnd : NondegG2 root) (hx : NondegX15 root) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      ∃ ψ : Fin 6 → F → G, G2Coords (R.toPre hgen).toSystemOfSimple ψ := by
  obtain ⟨E⟩ := sl2Pos_of_sl2At h4
  obtain ⟨E₁⟩ := sl2Pos_of_sl2At h1
  have hab : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, ∀ y ∈ root i, x * y = y * x :=
    fun i hi1 hi6 x hx y hy => by
      have := (hP.2 i hi1 hi6).1
      exact setLike_mul_comm hx hy
  have hC : Hex6Comm root := Hex6Comm.of_data R hO hL.1 hL.2.1 hL.2.2 hab
  obtain ⟨D, hDφ⟩ := hexData_exists_phi R E E₁ hC hO hq hqodd
  have hcard : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]; exact hq 4 (by norm_num) (by norm_num)
  have h3z : (3 : E.F) = 0 := by
    have := cast_prime_eq_zero D (hP.2 4 (by norm_num) (by norm_num)).2
    exact_mod_cast this
  have h2 : (2 : E.F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hcard]; exact hqodd)
  obtain ⟨u, hu, hu2⟩ := exists_u_ne (F := E.F) (by rw [hcard]; exact h5)
  obtain ⟨μ, hμ⟩ := exists_mu R hC D
  obtain ⟨a2, a4, L, hcd⟩ := exists_commData R D
  obtain ⟨A2, A4, g3, had⟩ := exists_actData R D
  have hnact : ActsPos 6 root (D.φ (sl2W E.F)) (fun q => 4 - q) := by
    rw [hDφ]; exact actsPos_weylSix R E hO
  obtain ⟨e, ha2, hmuL, ha4, hA2, hMg, hA4⟩ :=
    stage2_lin R hC D h2 hu hu2 hμ hcd had rfl hnact
  have he : e ≠ 0 := e_ne_zero D hnd had hA2
  have eqc : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have hz2 : ∀ s t, D.p2 (a2 s t) = 1 := fun s t => by
    have : 3 * e * s ^ 2 * t = 0 := by rw [h3z]; ring
    rw [ha2 s t, this]; exact map_zero_of_add' D.p2_add
  have hz4 : ∀ s t, D.p4 (a4 s t) = 1 := fun s t => by
    have : 3 * e * s * t ^ 2 = 0 := by rw [h3z]; ring
    rw [ha4 s t, this]; exact map_zero_of_add' D.p4_add
  have hLadd : ∀ u v, L 1 (u + v) = L 1 u * L 1 v := fun u v =>
    (comm15_add_t R hC D hμ hcd 1 u v).2.1
  have hLmul : ∀ s t, L s t = L 1 (s * t) := fun s t => L_eq_mul R D hcd s t
  have hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = L 1 (s * t) := fun s t => by
    rw [eqc s t]; unfold Nel
    rw [hz2, hz4, one_mul, mul_one, hLmul]
  have hLinj0 : ∀ v, L 1 v = 1 → v = 0 := by
    intro v hv
    by_contra hv0
    have hcomm : ⁅D.p1 1, D.p5 v⁆ = 1 := by rw [hc15, one_mul]; exact hv
    rcases hx _ (D.p1_mem 1) _ (D.p5_mem v) hcomm with h | h
    · have : D.p1 1 = D.p1 0 := by rw [h, map_zero_of_add' D.p1_add]
      exact one_ne_zero (D.p1_inj this)
    · have : D.p5 v = D.p5 0 := by rw [h, map_zero_of_add' D.p5_add]
      exact hv0 (D.p5_inj this)
  have hcard3 : Nat.card (root 3) = Nat.card E.F := by
    rw [hq 3 (by norm_num) (by norm_num), hcard]
  obtain ⟨hLinj, hLsurj⟩ := exists_Lam3 D hcd hLadd hLinj0 hcard3
  have h6 : (6 : E.F) = 0 := by linear_combination 2 * h3z
  have hμ0 : ∀ x ∈ root 3, μ x = 0 := fun x hx => by
    obtain ⟨v, rfl⟩ := hLsurj x hx
    rw [hmuL 1 v, h6]; ring
  have hΛmem : ∀ v, L 1 v ∈ root 3 := hcd.L_mem 1
  have hr1 : ∀ s v, ⁅D.p1 s, L 1 v⁆ = 1 := fun s v => by
    rw [hμ.r1 s _ (hΛmem v), hμ0 _ (hΛmem v), mul_zero]; exact map_zero_of_add' D.p2_add
  have hr5 : ∀ t v, ⁅D.p5 t, L 1 v⁆ = 1 := fun t v => by
    rw [hμ.r5 t _ (hΛmem v), hμ0 _ (hΛmem v), mul_zero]; exact map_zero_of_add' D.p4_add
  have hg3 := g3_eq_char3 R hC D h2 h3z hμ hcd had hLinj hLsurj
  have hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (e * c * s ^ 3) * L 1 (-(c * s ^ 2)) *
      D.p4 (2 * e * c ^ 2 * s ^ 3) * D.p5 (c * s) := fun c s => by
    rw [had.eq c s]; unfold Nel
    rw [hA2 c s, hA4 c s, hg3 c s]
  have hrel := g2Rel_of_data3 hC D hΛmem hLadd hr5 h3z hr1 hc15 hAct
  exact ⟨E.F, E.field, E.finite, hcard, g2ψ3 D e (L 1),
    g2Coords_of_data3 R hgen D he hΛmem hLinj hLsurj hrel⟩

end CFSG.GH74.GLS.Stage4.Hex
