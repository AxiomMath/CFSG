module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3331S
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331E4

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace Lem3331E4

section Main

variable {G : Type} [Group G]

theorem step3_3_31E4_aux_F4 [CFSG.GH74.QTGen4.Finite4 G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25_F4) (h27 : Stmt3_3_27_F4)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T)
    (hF : frattini ↥(qL L T) ≠ ⊥) (hk4 : Nat.card ↥(tC L T) = 4) :
    Nonempty (↥(qL L T ⊔ CFSG.conjugate (vPlus L T) d) ≃* D8D8E4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hidx, hdS, hVdC, hQdec, hTdec, hZ2⟩ :=
    Lem3331S.step3_3_31S_aux_F4 h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV
  obtain ⟨-, hFTC, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
  obtain ⟨u, huQ, huVd, hu2, hCu⟩ := exists_u h h38 h39 hA6 hTL hF hFTC hVdC hQdec hTdec
  set Q := qL L T with hQdef
  set V := vPlus L T with hVdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  set U := blockU L with hUdef
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hCT : C ≤ T := inf_le_left
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_frattini_eq_bot (hT2.to_le hCT) hFTC
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hVT : V ≤ T := hVQ.trans hQT
  have hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    (Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hv) q hq).symm
  have hVe := hred.2.1
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVe.1
    exact setLike_mul_comm ha hb
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := Hyp331.le_normalizer_tC hTL
  have huN : u ∈ Subgroup.normalizer (C : Set G) := hCN (hQT huQ)
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hUV : U ≤ V := h.blockU_le_vPlus h38 h39 hA6.1 hTL
  have hZT : Z ≤ T := L246C127.omegaOneCenter_le_self T
  have hZcT : Z ≤ Subgroup.centralizer (T : Set G) := L246C127.omegaOneCenter_le_centralizer T
  have hZV : Z ≤ V := le_conjClosure _ _
  have hCVd : C ≤ Subgroup.centralizer (Vd : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hVdC hw) c hc).symm
  have hZL1 : Z ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨⟨z, hzZL⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZL1
  have hz1 : z ≠ 1 := fun h1 => hz1' (Subtype.ext h1)
  have hzC : z ∈ C := ⟨hZT hzZL.1, hzZL.2⟩
  have hzV : z ∈ V := hZV hzZL.1
  have hzz : z * z = 1 := by rw [← sq]; exact hCe.2 z hzC
  have hzT : ∀ t ∈ T, z * t = t * z := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hZcT hzZL.1) t ht).symm
  have hZLz : ∀ y ∈ Z ⊓ Subgroup.centralizer (L : Set G), y = 1 ∨ y = z := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      exact congrArg Subtype.val (Lem3328.eq_of_card_two hZ2 (x := ⟨y, hy⟩) (y := ⟨z, hzZL⟩)
        (fun h' => hy1 (congrArg Subtype.val h')) hz1')
  have hCu' : ∀ y ∈ C, y * u = u * y → y = 1 ∨ y = z := fun y hy hyu => hZLz y (hCu y hy hyu)
  obtain ⟨c, hcC, -, ρ₁, hρ₁Q, hρ₁Vd, hρ₁z, hcρ₁⟩ := exists_rho₁ huQ huVd huN hu2 hCQ hCVd
    hCab hCe.2 hzC (hzT u (hQT huQ)) hCu' hk4
  obtain ⟨ρ, β, hβs, hβk, hβe, hρT, -, -, -, hK, -⟩ := CZA6.exists_rho_cZ h38 h39 h hA6 hTL
  have hVdV : ∀ w ∈ Vd, d * w * d⁻¹ ∈ V := fun w hw => Lem3331S.mem_conjugate_iff.mp hw
  have hVdT : Vd ≤ T := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdT) _).mp (hVT (hVdV x hx))
    simpa [mul_assoc] using this
  obtain ⟨w₀, hw₀, hw₀Q⟩ := Set.not_subset.mp hdV
  have hw₀T : w₀ ∈ T := hVdT hw₀
  have hw₀w₀ : w₀ * w₀ = 1 := by
    have h1 := hVe.2 _ (hVdV w₀ hw₀)
    have e : (d * w₀ * d⁻¹) ^ 2 = d * (w₀ * w₀) * d⁻¹ := by rw [sq]; group
    rw [e] at h1
    have h2 := congrArg (fun g => d⁻¹ * g * d) h1
    simpa [mul_assoc] using h2
  have hρw : ρ ⟨w₀, hTL hw₀T⟩ ≠ 1 := fun h1 =>
    hw₀Q (hK w₀ (Subgroup.mem_sup_right hw₀T) (hTL hw₀T) h1)
  obtain ⟨v, hvU, zU, hzUU, hzUe, hzUZ⟩ := exists_v hTL ρ β hβs hβk hβe hρT hw₀T hw₀w₀ hρw
  have hvV : v ∈ V := hUV hvU
  have hvv : v * v = 1 := by rw [← sq]; exact hVe.2 v hvV
  have hzUV : zU ∈ V := hUV hzUU
  have hz'z' : (v * w₀) ^ 2 * (v * w₀) ^ 2 = 1 := by rw [← hzUe, ← sq]; exact hVe.2 zU hzUV
  have hz'1 : (v * w₀) ^ 2 ≠ 1 := fun h1 => hzUZ (by rw [hzUe, h1]; exact Subgroup.one_mem _)
  have hz'z : (v * w₀) ^ 2 ∉ Subgroup.zpowers z := by
    intro hmem
    rcases eq_one_or_of_mem_zpowers hzz hmem with h1 | h1
    · exact hz'1 h1
    · apply hzUZ
      have hzU : zU = z := hzUe.trans h1
      rw [hzU]
      exact ⟨hzU ▸ hzUU, hzZL.2⟩
  have hU16 := card_blockU_eq β hβs hβk
  have hV32 : 32 ≤ Nat.card V := card_ge_32 hUV hU16 (fun hZb => ⟨z, hzV, fun hzU => hz1 (by
    have h1 : z ∈ blockZ L := ⟨hzU, hzZL.2⟩
    rw [hZb] at h1
    exact h1)⟩)
  have hVW : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (Vd : Set G)) :=
    Lem3331S.card_le_two_mul (inv_mul_mem_of_relIndex_two hVQ le_sup_left hVZ hVdV hdS hidx)
  have hW16 : 16 ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (Vd : Set G)) := by omega
  obtain ⟨e₁, he₁W, e₂, he₂W, hi₁, hi₂⟩ := exists_e hW16 hzz hz'z'
    (hzT _ (hVT (hzUe ▸ hzUV)))
    (fun w hw => (hzT w (hVT hw.1)).symm)
    (fun w hw => hVab w hw.1 _ (hzUe ▸ hzUV))
    (fun w hw => by rw [← sq]; exact hVe.2 w hw.1)
  have hS2 : Nat.card ↥(Q ⊔ Vd) = 2 * Nat.card Q := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ Vd)
    rw [inf_of_le_left le_sup_left, hidx] at h1
    omega
  have hQ2 : Nat.card Q ≤ 2 * Nat.card ↥(U ⊔ C) := by
    have h1 := h.relIndex_qL_le_two h38 h39 hA6 hTL
    have h2 := Subgroup.relIndex_mul_card (H := U ⊔ C) (K := Q)
    rw [inf_of_le_left (sup_le (hUV.trans hVQ) hCQ)] at h2
    rw [← h2]
    exact Nat.mul_le_mul_right _ h1
  have hCU : C ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
    C1.mem_normalizer_blockU (hTL (hCT hx))
  have hZl : ∀ y ∈ blockZ L, y = 1 ∨ y = z := by
    intro y hy
    have hyV : y ∈ V := hUV hy.1
    exact hCu' y ⟨hVT hyV, hy.2⟩ (hVZ y hyV u huQ)
  have hUC := card_sup_le_64 hCU hU16 hk4 (fun x hx => hx.1) hZl hzC hz1 hzz
  have hcard : Nat.card ↥(Q ⊔ Vd) ≤ 256 := by omega
  have hcV : ∀ q ∈ Q, ∀ g ∈ V, Commute q g := fun q hq g hg => (hVZ g hg q hq).symm
  have hcVd : ∀ q ∈ Subgroup.centralizer (Vd : Set G), ∀ w ∈ Vd, Commute q w :=
    fun q hq w hw => (Subgroup.mem_centralizer_iff.mp hq w hw).symm
  have hρ₁ρ₂ : Commute ρ₁ (v * w₀) := (hcV ρ₁ hρ₁Q v hvV).mul_right (hcVd ρ₁ hρ₁Vd w₀ hw₀)
  have hcρ₂ : Commute c (v * w₀) :=
    (hcV c (hCQ hcC) v hvV).mul_right (hcVd c (hCVd hcC) w₀ hw₀)
  have hρ₂e : ∀ e ∈ V ⊓ Subgroup.centralizer (Vd : Set G), Commute (v * w₀) e := fun e he =>
    (Commute.mul_left (hVab v hvV e he.1) (hcVd e he.2 w₀ hw₀).symm)
  have hcc : c * c = 1 := by rw [← sq]; exact hCe.2 c hcC
  have hwi : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀w₀
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hρ₁4 : ρ₁ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hρ₁z, sq, hzz]
  have hρ₂4 : (v * w₀) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq ((v * w₀) ^ 2), hz'z']
  have hc₂ : v * (v * w₀) * v = (v * w₀)⁻¹ := by
    calc v * (v * w₀) * v = (v * v) * w₀ * v := by group
      _ = w₀⁻¹ * v⁻¹ := by rw [hvv, one_mul, hwi, hvi]
      _ = (v * w₀)⁻¹ := by group
  rw [← hρ₁z] at hz'z hi₁ hi₂
  exact nonempty_mulEquiv (Subgroup.mem_sup_left hρ₁Q) (Subgroup.mem_sup_left (hCQ hcC))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hVQ hvV)) (Subgroup.mem_sup_right hw₀))
    (Subgroup.mem_sup_left (hVQ hvV)) (Subgroup.mem_sup_left (hVQ he₁W.1))
    (Subgroup.mem_sup_left (hVQ he₂W.1)) hρ₁4 hcc hcρ₁ hρ₂4 hvv hc₂
    (by rw [← sq]; exact hVe.2 e₁ he₁W.1) (by rw [← sq]; exact hVe.2 e₂ he₂W.1)
    (hVab e₁ he₁W.1 e₂ he₂W.1) hρ₁ρ₂ (hcV ρ₁ hρ₁Q v hvV) hcρ₂ (hcV c (hCQ hcC) v hvV)
    (hcV ρ₁ hρ₁Q e₁ he₁W.1) (hcV ρ₁ hρ₁Q e₂ he₂W.1) (hcV c (hCQ hcC) e₁ he₁W.1)
    (hcV c (hCQ hcC) e₂ he₂W.1) (hρ₂e e₁ he₁W) (hρ₂e e₂ he₂W) (hVab v hvV e₁ he₁W.1)
    (hVab v hvV e₂ he₂W.1) (by rw [hρ₁z]; exact hz1) hz'z hi₁ hi₂ hcard

theorem step3_3_31E4_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25_F4) (h27 : Stmt3_3_27_F4) : Step3_3_31E4_F4 := by
  intro G _ _ T M L D h hA6 hTL hTC d hdD hdM hdV hF hk4
  exact step3_3_31E4_aux_F4 h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV hF hk4

end Main

end Lem3331E4

end CFSG.Quasithin.H13
