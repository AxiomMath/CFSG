module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub9
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem false_of_pCore_eq [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hJ : JLayer hs π) (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hcent : Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβW : β ∈ W := (mem_inf.mp hβZ).1
  obtain ⟨y, hyN, hyW, hy2, hy2grp, -, hyb, hyz⟩ :=
    hJ.exists_y hnab hFC hKC hI hKF hπi hQ hcent hW hUW
  obtain ⟨c, hcR, hc, e', h', hsub, hφ⟩ := hJ.exists_phi hKC hπi hW hUW
  obtain ⟨hzZ, hze, l, hlW₁, hlW, hl2, hlc, hlb, hlz⟩ :=
    hJ.exists_lambda hKC hπi hQ hW hUW hyN hyW hy2 hy2grp hyb hyz hcR h' hsub hφ
  obtain ⟨v₀, hv₀, hv₀sq, hte⟩ := hJ.exists_v0 hπi hW htW hcR hc h' hsub hφ
  have hβc : ∀ g ∈ W, g * β = β * g := fun g hg =>
    mem_centralizer_iff.mp (mem_inf.mp hβZ).2 g hg
  have hzc : ∀ g ∈ W, g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp (mem_inf.mp hzZ).2 g hg
  have hβ2 : β * β = 1 := by rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβt : β * t = t * β :=
    (mem_centralizer_singleton_iff.mp (hs.setup.t_mem_centralizer_beta i j)).symm
  have hW₁N : W ⊔ zpowers y ≤ normalizer (W : Set X) :=
    sup_le le_normalizer_self (zpowers_le.mpr hyN)
  have hlN := hW₁N hlW₁
  have hlz' : l * z = z * l := by
    calc l * z = (l * z * l⁻¹) * l := by group
      _ = z * l := by rw [hlz]
  have hn : ∀ x ∈ h'.sub, l * x * l⁻¹ ∈ h'.sub := by
    rw [hsub]
    exact conj_mem_inf' conj_mem_W conj_mem_oP l hlN
  have hlc' : ∀ a ∈ cModZ h'.sub, l * a = a * l := by rw [hsub]; exact hlc
  have he1 : e' 1 * e' 1 = 1 := by rw [← hze]; exact hz2
  have hlV : ∀ v ∈ W ⊓ oP W, MZ z l v := by
    intro v hv
    have := h'.conj_eq_of_comm_iv hn hlc' he1 (by rw [hsub]; exact hv)
    rw [← hze] at this
    exact this
  have hdec : ∀ g ∈ W, ∃ v ∈ W ⊓ oP W, g = v ∨ g = v * t ∨ g = v * β ∨ g = v * (β * t) :=
    fun g hg => hJ.exists_V0_mul hKC hπi hQ hW hUW hg
  have hV₀W : W ⊓ oP W ≤ W := inf_le_left
  rcases hJ.conj_t_lambda hQ hW hβW htW hcR h' hsub hφ hze hz1 hzZ hlN hl2 hlc hlb hlz with
    htl | htl
  ·
    have hlt : l * t = t * l := by
      calc l * t = (t * l * t⁻¹) * t := by rw [htl]
        _ = t * l := by group
    exact false_of_x0 hs hTW le_sup_left hy2grp hV₀W hβW hβc hzc hβ2 hz2 hβt hdec hlW₁ hlW hlt
      hlz' hlb (Or.inl hl2) fun v hv _ => hlV v hv
  ·
    have hcnt := hJ.count_ge hKC hπi hQ hcent hW hUW h' hsub hv₀ hte
    obtain ⟨u, huV, hut, hu2, huc⟩ := exists_u h' hsub hv₀ hv₀sq hte hcnt hze
    have huW : u ∈ W := (mem_inf.mp huV).1
    have hx₀t : t * (l * u) * t⁻¹ = l * u := by
      calc t * (l * u) * t⁻¹ = (t * l * t⁻¹) * (t * u * t⁻¹) := by group
        _ = z * l * (u * z) := by rw [htl, hut]
        _ = l * (z * u) * z := by rw [← hlz']; group
        _ = l * (u * z) * z := by rw [hzc u huW]
        _ = l * u * (z * z) := by group
        _ = l * u := by rw [hz2, mul_one]
    have hx₀t' : l * u * t = t * (l * u) := by
      calc l * u * t = (t * (l * u) * t⁻¹) * t := by rw [hx₀t]
        _ = t * (l * u) := by group
    have hx₀z : l * u * z = z * (l * u) := by
      calc l * u * z = l * (z * u) := by rw [mul_assoc, hzc u huW]
        _ = z * (l * u) := by rw [← mul_assoc, hlz', mul_assoc]
    have hx₀b : l * u * β * (l * u)⁻¹ = β * z := by
      calc l * u * β * (l * u)⁻¹ = l * (u * β * u⁻¹) * l⁻¹ := by group
        _ = l * β * l⁻¹ := by rw [hβc u huW, mul_inv_cancel_right]
        _ = β * z := hlb
    have hx₀2 : l * u * (l * u) = 1 ∨ l * u * (l * u) = z := by
      have e1 : l * u * (l * u) = (l * u * l⁻¹) * (l * l) * u := by group
      rw [e1, hl2, mul_one]
      rcases hlV u huV with h | h <;> rw [h]
      · exact hu2
      · rw [mul_assoc, ← hzc u huW, ← mul_assoc]
        rcases hu2 with h2 | h2 <;> rw [h2]
        · exact Or.inr (one_mul z)
        · exact Or.inl hz2
    have huMZ : ∀ v ∈ W ⊓ oP W, v * t = t * v → MZ z u v := by
      intro v hv hvt
      have htv : t * v * t⁻¹ = v := by rw [← hvt, mul_inv_cancel_right]
      have hvW := (mem_inf.mp hv).1
      have e2 : u * v * u⁻¹ = ⁅u, v⁆ * v := by rw [commutatorElement_def]; group
      rcases huc v hv htv with h | h
      · left
        rw [e2, h, one_mul]
      · right
        rw [e2, h, hzc v hvW]
    exact false_of_x0 hs hTW le_sup_left hy2grp hV₀W hβW hβc hzc hβ2 hz2 hβt hdec
      (mul_mem hlW₁ (mem_sup_left huW)) (fun h => hlW (by simpa using mul_mem h (inv_mem huW)))
      hx₀t' hx₀z hx₀b hx₀2 fun v hv hvt => MZ.mul_left hz2 hlz' (hlV v hv) (huMZ v hv hvt)

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
