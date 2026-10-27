module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinThree
public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSL3

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped MatrixGroups commutatorElement

variable {Y : Type} [Group Y] {L : Subgroup Y} {F' : Type} [Field F'] {x t : Y}
  {J₂ J₄ : Subgroup Y} {R : Subgroup Y} {S : Sylow 2 R}

theorem Frame.mem_of_odd [Finite F'] (hfr : Frame L F' x t J₂ J₄) (hodd : Odd (Nat.card F'))
    (ht : orderOf t = 2) {k j : Y} (hj : j ∈ J₄) (hk : k = j ∨ k = t * j) (hko : Odd (orderOf k)) :
    k ∈ J₄ := by
  rcases hk with rfl | rfl
  · exact hj
  · exfalso
    have hjt : t * j = j * t := (mem_cent.mp (hfr.cent₄ hj)).symm
    have h1 := pow_orderOf_eq_one (t * j)
    rw [Commute.mul_pow hjt] at h1
    obtain ⟨m, hm⟩ := hko
    have htm : t ^ orderOf (t * j) = t := by
      rw [hm, pow_succ, pow_mul, ← ht, pow_orderOf_eq_one, one_pow, one_mul]
    rw [htm] at h1
    have htJ : t ∈ J₄ := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact J₄.inv_mem (J₄.pow_mem hj _)
    have := hfr.inter_eq_one hodd ht hfr.mem₂ htJ
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem Frame3.conj_mem_J₄ [Finite Y] [Finite F'] (hfr : Frame3 L F' x t J₂ J₄) (hLn : L.Normal)
    (ht : orderOf t = 2) {g : Y} (hgt : g * t = t * g)
    (hgb : ∀ b ∈ J₂, b * b = t → Commute g b) : ∀ w ∈ J₄, g * w * g⁻¹ ∈ J₄ := by
  have hodd : Odd (Nat.card F') := by rw [hfr.card]; decide
  obtain ⟨e₄⟩ := hfr.equiv₄
  have hgen := oddGenerated_of_equiv_sl2 hodd e₄
  have hle : J₄ ≤ J₄.comap (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [← hgen]
    rw [Subgroup.closure_le]
    rintro w ⟨hw, hwo⟩
    show g * w * g⁻¹ ∈ J₄
    have hwt : Commute w t := mem_cent.mp (hfr.cent₄ hw)
    have hc : ∀ c ∈ J₂, Commute g c → Commute (g * w * g⁻¹) c := fun c hc hgc =>
      (hgc.mul_left (hfr.comm c hc w hw).symm).mul_left hgc.inv_left
    obtain ⟨j, hj, hk⟩ := hfr.cent_mem _ (hLn.conj_mem _ (hfr.le₄ hw) g)
      (((Commute.mul_left hgt hwt).mul_left (Commute.inv_left hgt)).eq)
      fun b hb hbb => (hc b hb (hgb b hb hbb)).eq
    refine hfr.toFrame.mem_of_odd hodd ht hj hk ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hwo
  intro w hw
  exact hle hw

theorem Frame3.good [Finite Y] [Finite F'] (hfr : Frame3 L F' x t J₂ J₄) (hLn : L.Normal)
    (hD : TightDatum R S t) {n : Y} (hnR : n ∈ R) (hnL : n ∈ L) (hn : n * n = t) :
    GoodThreeElement R t := by
  have hodd : Odd (Nat.card F') := by rw [hfr.card]; decide
  have ht := hD.order
  have ht2 := t_mul_self hD
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  obtain ⟨e₄⟩ := hfr.equiv₄
  obtain ⟨e₂⟩ := hfr.equiv₂
  obtain ⟨x₃, hx₃J, hx₃3, hx₃⟩ := exists_three_of_equiv_sl2 hfr.card e₂
  have hx₃t : Commute x₃ t := mem_cent.mp (hfr.cent₂ hx₃J)
  obtain ⟨b, hbJ, hnb⟩ := hfr.sq_mem n hnL (mem_cent.mp (hD.cent hnR)) hn
  obtain ⟨u, hu, rfl⟩ : ∃ u : Y, (u = 1 ∨ u = x * t) ∧ n = u * b := by
    rcases hnb with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨x * t, Or.inr rfl, h⟩
  have huC : ∀ g : Y, Commute g t → Commute g u := fun g hg => by
    rcases hu with rfl | rfl
    · exact Commute.one_right g
    · exact (show Commute g x from hfr.central g).mul_right hg
  have huu : u * u = 1 := by
    rcases hu with rfl | rfl
    · exact mul_one 1
    · rw [← sq, ← hfr.orderOf_xt, pow_orderOf_eq_one]
  have hbt : Commute b t := mem_cent.mp (hfr.cent₂ hbJ)
  have hJ₂t : ∀ c ∈ J₂, Commute c t := fun c hc => mem_cent.mp (hfr.cent₂ hc)
  have hsq : ∀ c ∈ J₂, c * c = t → c ^ 4 = 1 ∧ c ^ 2 ≠ 1 := fun c _ hc => by
    refine ⟨?_, ?_⟩
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hc, ht2]
    · rw [sq, hc]; exact ht1
  have hbb : b * b = t := by
    calc b * b = u * u * (b * b) := by rw [huu, one_mul]
      _ = u * b * (u * b) := by
        rw [show u * b * (u * b) = u * (b * u) * b by group, (huC b hbt).eq]; group
      _ = t := hn
  have hconj : ∀ c ∈ J₂, c * c = t → x₃ * c * x₃⁻¹ ∈ J₂ ∧
      x₃ * c * x₃⁻¹ * (x₃ * c * x₃⁻¹) = t := fun c hc hcc => by
    refine ⟨J₂.mul_mem (J₂.mul_mem hx₃J hc) (J₂.inv_mem hx₃J), ?_⟩
    rw [show x₃ * c * x₃⁻¹ * (x₃ * c * x₃⁻¹) = x₃ * (c * c) * x₃⁻¹ by group, hcc,
      hx₃t.eq, mul_assoc, mul_inv_cancel, mul_one]
  set b' := x₃ * b * x₃⁻¹ with hb'def
  obtain ⟨hb'J, hb'b'⟩ := hconj b hbJ hbb
  set b'' := x₃ * b' * x₃⁻¹ with hb''def
  obtain ⟨hb''J, -⟩ := hconj b' hb'J hb'b'
  obtain ⟨hxb, hne⟩ := hx₃ b hbJ (hsq b hbJ hbb).1 (hsq b hbJ hbb).2
  obtain ⟨-, hne'⟩ := hx₃ b' hb'J (hsq b' hb'J hb'b').1 (hsq b' hb'J hb'b').2
  have hO : ∀ o ∈ oddCoreImg R, o ∈ L → o = 1 := fun o ho hoL =>
    hfr.oddCore_inf_eq_one hLn hD ⟨ho, hoL⟩
  have hRn : ∀ r ∈ R, x₃ * r * x₃⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer (hfr.cent₂ hx₃J)) r).mp hr
  have hconjn : ∀ c : Y, x₃ * (u * c) * x₃⁻¹ = u * (x₃ * c * x₃⁻¹) := fun c => by
    rw [← mul_assoc x₃ u, (huC x₃ hx₃t).eq]; group
  refine ⟨x₃, 1, hfr.cent₂ hx₃J, by rw [pow_one]; exact hx₃3, ⟨u * b, hnR, fun h => ?_⟩, ?_⟩
  · have h1 := hO _ h (by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem (hfr.le₂ hx₃J) hnL) (L.inv_mem (hfr.le₂ hx₃J)))
        (L.inv_mem hnL))
    have h2 : x₃ * (u * b) = u * b * x₃ := commutatorElement_eq_one_iff_mul_comm.mp h1
    apply hxb
    rw [← mul_assoc, (huC x₃ hx₃t).eq, mul_assoc, mul_assoc] at h2
    exact mul_left_cancel h2
  · intro y hyC hyR
    have hyt : Commute y t := mem_cent.mp hyC
    have hyc : ∀ r ∈ R, r ∈ L → Commute y r := fun r hr hrL => by
      have h1 := hO _ (hyR r hr) (by
        rw [commutatorElement_def]
        exact L.mul_mem (hLn.conj_mem _ hrL y) (L.inv_mem hrL))
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hn'R : u * b' ∈ R := by rw [hb'def, ← hconjn]; exact hRn _ hnR
    have hn'L : u * b' ∈ L := by
      rw [hb'def, ← hconjn]
      exact hLn.conj_mem _ hnL x₃
    have hn''R : u * b'' ∈ R := by rw [hb''def, ← hconjn]; exact hRn _ hn'R
    have hn''L : u * b'' ∈ L := by
      rw [hb''def, ← hconjn]
      exact hLn.conj_mem _ hn'L x₃
    have hyu : Commute y u := huC y hyt
    have hyb : ∀ c, u * c ∈ R → u * c ∈ L → Commute y c := fun c hR hL => by
      have := (hyu.inv_right).mul_right (hyc _ hR hL)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    have h1 := hyb b hnR hnL
    have h2 := hyb b' hn'R hn'L
    have h3 := hyb b'' hn''R hn''L
    have hall : ∀ g : Y, Commute g b → Commute g b' → ∀ c ∈ J₂, c * c = t → Commute g c :=
      fun g hgb hgb' c hc hcc => comm_of_comm_pair hfr.card e₂ hbJ hb'J hc (hsq b hbJ hbb).1
        (hsq b hbJ hbb).2 (hsq b' hb'J hb'b').1 (hsq b' hb'J hb'b').2 (fun h => hne h.symm)
        (hsq c hc hcc).1 (hsq c hc hcc).2 hgb hgb'
    have hJ4 := hfr.conj_mem_J₄ hLn ht hyt.inv_left (hall _ h1.inv_left h2.inv_left)
    set z := y * x₃ * y⁻¹ with hz
    have hx₃b : SemiconjBy x₃ b b' := by
      show x₃ * b = b' * x₃
      rw [hb'def]; group
    have hx₃b' : SemiconjBy x₃ b' b'' := by
      show x₃ * b' = b'' * x₃
      rw [hb''def]; group
    have hzb : SemiconjBy z b b' :=
      SemiconjBy.mul_left (SemiconjBy.mul_left (h2 : SemiconjBy y b' b') hx₃b)
        (h1.inv_left : SemiconjBy y⁻¹ b b)
    have hzb' : SemiconjBy z b' b'' :=
      SemiconjBy.mul_left (SemiconjBy.mul_left (h3 : SemiconjBy y b'' b'') hx₃b')
        (h2.inv_left : SemiconjBy y⁻¹ b' b')
    have hg₀b : Commute (x₃⁻¹ * z) b := SemiconjBy.mul_left hx₃b.inv_symm_left hzb
    have hg₀b' : Commute (x₃⁻¹ * z) b' := SemiconjBy.mul_left hx₃b'.inv_symm_left hzb'
    have hg₀L : x₃⁻¹ * z ∈ L :=
      L.mul_mem (L.inv_mem (hfr.le₂ hx₃J)) (hLn.conj_mem _ (hfr.le₂ hx₃J) y)
    have hg₀t : Commute (x₃⁻¹ * z) t :=
      hx₃t.inv_left.mul_left ((hyt.mul_left hx₃t).mul_left hyt.inv_left)
    obtain ⟨j, hj, hg₀⟩ := hfr.cent_mem _ hg₀L hg₀t.eq fun c hc hcc =>
      (hall _ hg₀b hg₀b' c hc hcc).eq
    have hx₃g₀ : Commute x₃ (x₃⁻¹ * z) := by
      rcases hg₀ with h | h <;> rw [h]
      · exact hfr.comm x₃ hx₃J j hj
      · exact hx₃t.mul_right (hfr.comm x₃ hx₃J j hj)
    have hz3 : z ^ 3 = 1 := by rw [hz, conj_pow, hx₃3, mul_one, mul_inv_cancel]
    have hg₀3 : (x₃⁻¹ * z) ^ 3 = 1 := by
      have h := hz3
      rw [show z = x₃ * (x₃⁻¹ * z) by group, hx₃g₀.mul_pow, hx₃3, one_mul] at h
      exact h
    have hg₀J : x₃⁻¹ * z ∈ J₄ := hfr.toFrame.mem_of_odd hodd ht hj hg₀
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hg₀3))
    have hzJ : ∀ w ∈ J₄, Commute w z := fun w hw => by
      have hw' := hJ4 w hw
      rw [inv_inv] at hw'
      have hc := hfr.comm x₃ hx₃J _ hw'
      show w * (y * x₃ * y⁻¹) = y * x₃ * y⁻¹ * w
      calc w * (y * x₃ * y⁻¹) = y * (y⁻¹ * w * y * x₃) * y⁻¹ := by group
        _ = y * (x₃ * (y⁻¹ * w * y)) * y⁻¹ := by rw [hc]
        _ = y * x₃ * y⁻¹ * w := by group
    have hcent : ∀ w ∈ J₄, w * (x₃⁻¹ * z) = x₃⁻¹ * z * w := fun w hw =>
      ((show Commute w x₃ from (hfr.comm x₃ hx₃J w hw).symm).inv_right.mul_right (hzJ w hw)).eq
    rcases eq_one_or_of_central hodd e₄ hfr.mem₄ hfr.orderOf_xt hg₀J hcent with h | h
    · have hzx : z = x₃ := by rw [← mul_one x₃, ← h]; group
      rw [commutatorElement_def]
      have : x₃ * y * x₃⁻¹ * y⁻¹ = 1 := by
        rw [hz] at hzx
        calc x₃ * y * x₃⁻¹ * y⁻¹ = x₃ * (y * x₃ * y⁻¹)⁻¹ := by group
          _ = 1 := by rw [hzx, mul_inv_cancel]
      rw [this]
      exact Subgroup.one_mem _
    · exfalso
      rw [h] at hg₀3
      have hxt := pow_orderOf_eq_one (x * t)
      rw [hfr.orderOf_xt] at hxt
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hxt, one_mul] at hg₀3
      have := hfr.orderOf_xt
      rw [hg₀3, orderOf_one] at this
      exact absurd this (by norm_num)

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
