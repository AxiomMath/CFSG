module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx23
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx16

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem cube_conj (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G} (hx : x ∈ Wsub S U) :
    h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = x := by
  have h3 := hs.h_cube x hx
  rw [pow_three] at h3
  have e : h⁻¹ * (h⁻¹ * (h⁻¹ * x * h) * h) * h = (h * (h * h))⁻¹ * (x * (h * (h * h))) := by
    group
  rw [e, ← h3]
  group

theorem relIndex_S1_S (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hSne : S ≠ S1 S K₁) :
    (S1 S K₁).relIndex S = 2 := by
  have hle : (S1 S K₁).relIndex S ≤ 2 := hs.fused.p66.2.1.1
  have hpos : (S1 S K₁).relIndex S ≠ 0 := Basic.relIndex_ne_zero' _ _
  have hne : (S1 S K₁).relIndex S ≠ 1 := fun h' =>
    hSne (le_antisymm (Subgroup.relIndex_eq_one.1 h') S1_le_S)
  omega

theorem exists_W_not_S1 (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hSne : S ≠ S1 S K₁) {y₁ : G} (hy₁P : y₁ ∈ Pof S K₁)
    (hy₁inv : ∀ c ∈ Vof S K₁ W₂, y₁ * c * y₁⁻¹ = c⁻¹) : ∃ w ∈ Wsub S U, w ∉ S1 S K₁ := by
  by_contra hcon
  push Not at hcon
  have hWle : Wsub S U ≤ S1 S K₁ := hcon
  have hy₁W := hs.y₁_not_mem_W hII hq hy₁P hy₁inv
  have hW_S : (Wsub S U).relIndex S = 2 := by
    have hle := hs.relIndex_W_le_two hII
    have hne : (Wsub S U).relIndex S ≠ 1 := by
      intro h1
      have : S ≤ Wsub S U := Subgroup.relIndex_eq_one.1 h1
      exact hy₁W (this hy₁P.1)
    have hpos := Basic.relIndex_ne_zero' (Wsub S U) S
    omega
  have hmulW : Nat.card ↥(Wsub S U) * (Wsub S U).relIndex S = Nat.card ↥S :=
    Basic.card_mul_relIndex_of_le (inf_le_left : Wsub S U ≤ S)
  rw [hW_S] at hmulW
  have hSc : Nat.card ↥S = 2 * Nat.card ↥(S1 S K₁) := by
    rcases hs.card_S_of with ⟨hSS, -⟩ | ⟨-, hc⟩
    · exact absurd hSS hSne
    · exact hc
  have hWeq : Wsub S U = S1 S K₁ :=
    Subgroup.eq_of_le_of_card_ge hWle (by omega)
  exact hy₁W (hWeq ▸ hs.P_le_S1 hII (Or.inl rfl) hy₁P)

theorem g_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2) {m : ℕ}
    (hm : 2 ≤ m) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) (hSne : S ≠ S1 S K₁) {y : G}
    (hyW : y ∈ Wsub S U) (hyS1 : y ∈ S1 S K₁) (hyA : y ∉ Aof S K₁ W₂ h)
    (hyV₁ : ∀ c ∈ Vof S K₁ W₂, y * c * y⁻¹ = c⁻¹)
    (hrelA : (Aof S K₁ W₂ h).relIndex (Wsub S U ⊓ S1 S K₁) = 2)
    (hmod : ∀ a ∈ Aof S K₁ W₂ h, (y * a * y⁻¹) * a ∈ U) :
    (h⁻¹ * y * h) * y ∈ Aof S K₁ W₂ h := by
  by_contra hgA
  have hk2 : 2 ≤ m + 1 := by omega
  obtain ⟨x, hxV, hVx, hxo, hxz⟩ := hs.gen_V₁ hII hq hk
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx4 : x * x * (x * x) ≠ 1 := by
    intro h4
    have h5 : x ^ 4 = 1 := by rw [Basic.pow_four_eq]; exact h4
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hxo] at h6
    have h7 := Nat.le_of_dvd (by norm_num) h6
    have h8 : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hgW : (h⁻¹ * y * h) * y ∈ Wsub S U := mul_mem (hs.W_conj_h hyW) hyW
  obtain ⟨c, hcU, hgx⟩ := hs.g_mod_U hII hq hrec hk hyW hmod x hxA
  have hcA : c ∈ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec hk2 hk hcU
  have hcc : c * c = 1 := hs.four_sq c hcU
  have hxc : x * c = c * x := hs.A_comm hII hq hrec x hxA c hcA
  by_cases hgS1 : (h⁻¹ * y * h) * y ∈ S1 S K₁
  · have hg0 : (h⁻¹ * y * h) * y ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨hgW, hgS1⟩
    have hyW0 : y ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨hyW, hyS1⟩
    have ha₀ : ((h⁻¹ * y * h) * y) * y⁻¹ ∈ Aof S K₁ W₂ h :=
      Basic.mul_inv_mem_of_relIndex_two hrelA hg0 hyW0 hgA hyA
    have hdx : y * x * y⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hyW.1 hxA
    have hcomm : (((h⁻¹ * y * h) * y) * y⁻¹) * (y * x * y⁻¹) =
        (y * x * y⁻¹) * (((h⁻¹ * y * h) * y) * y⁻¹) := hs.A_comm hII hq hrec _ ha₀ _ hdx
    have hgx' : ((h⁻¹ * y * h) * y) * x * ((h⁻¹ * y * h) * y)⁻¹ = x⁻¹ := by
      calc ((h⁻¹ * y * h) * y) * x * ((h⁻¹ * y * h) * y)⁻¹
          = (((h⁻¹ * y * h) * y) * y⁻¹) * (y * x * y⁻¹) * (((h⁻¹ * y * h) * y) * y⁻¹)⁻¹ := by
            group
        _ = (y * x * y⁻¹) * (((h⁻¹ * y * h) * y) * y⁻¹) * (((h⁻¹ * y * h) * y) * y⁻¹)⁻¹ := by
            rw [hcomm]
        _ = y * x * y⁻¹ := by group
        _ = x⁻¹ := hyV₁ x hxV
    rw [hgx'] at hgx
    apply hx4
    have h1 : x⁻¹ * x⁻¹ = c := by
      calc x⁻¹ * x⁻¹ = x⁻¹ * (x * c) := congrArg (fun t => x⁻¹ * t) hgx
        _ = c := by group
    have h2 : x * x = c⁻¹ := by
      calc x * x = (x⁻¹ * x⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
        _ = c⁻¹ := by rw [h1]
    calc (x * x) * (x * x) = c⁻¹ * c⁻¹ := by rw [h2]
      _ = (c * c)⁻¹ := by group
      _ = 1 := by rw [hcc]; group
  · have hgS : (h⁻¹ * y * h) * y ∈ S := hgW.1
    obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
    have hV := hs.card_V₁ hII hq
    have h8 : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have he1 : e = 1 := by omega
    subst he1
    have h16 : 16 ≤ Nat.card ↥(Qof S K₁) := by omega
    have hsw := (hs.swap_V hII hq hrec h16 hgS hgS1).1 x hxV
    rw [hgx] at hsw
    have h1 : (x * c) * (x * c) = x * x := by
      calc (x * c) * (x * c) = x * (c * x) * c := by group
        _ = x * (x * c) * c := by rw [← hxc]
        _ = (x * x) * (c * c) := by group
        _ = x * x := by rw [hcc, mul_one]
    have h2 : x * x ∈ Vof S K₂ W₁ := by rw [← h1]; exact mul_mem hsw hsw
    have h3 : x * x ∈ Vof S K₁ W₂ := mul_mem hxV hxV
    exact hx4 (hs.V₁_inf_V₂_sq hII _ (Subgroup.mem_inf.2 ⟨h3, h2⟩))

theorem W₀_conj (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {y : G}
    (hyW : y ∈ Wsub S U) (hyS1 : y ∈ S1 S K₁) (hyA : y ∉ Aof S K₁ W₂ h)
    (hrelA : (Aof S K₁ W₂ h).relIndex (Wsub S U ⊓ S1 S K₁) = 2)
    (hg : (h⁻¹ * y * h) * y ∈ Aof S K₁ W₂ h) :
    ∀ v ∈ Wsub S U ⊓ S1 S K₁, h⁻¹ * v * h ∈ Wsub S U ⊓ S1 S K₁ := by
  intro v hv
  refine Subgroup.mem_inf.2 ⟨hs.W_conj_h hv.1, ?_⟩
  by_cases hvA : v ∈ Aof S K₁ W₂ h
  · exact hs.A_le_S1 hII hq hrec ((hs.A_conj hII hq hrec hk hvA).2)
  · have ha₀ : v * y⁻¹ ∈ Aof S K₁ W₂ h :=
      Basic.mul_inv_mem_of_relIndex_two hrelA hv (Subgroup.mem_inf.2 ⟨hyW, hyS1⟩) hvA hyA
    have ha₁ : h⁻¹ * (v * y⁻¹) * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk ha₀).2
    have e : h⁻¹ * v * h = (h⁻¹ * (v * y⁻¹) * h) * ((h⁻¹ * y * h) * y) * y⁻¹ := by group
    rw [e]
    exact mul_mem (hs.A_le_S1 hII hq hrec (mul_mem ha₁ hg)) (inv_mem hyS1)

theorem sigma_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k)
    (hSne : S ≠ S1 S K₁) {y : G} (hyW : y ∈ Wsub S U) (hyS1 : y ∈ S1 S K₁)
    (hyA : y ∉ Aof S K₁ W₂ h) (hrelA : (Aof S K₁ W₂ h).relIndex (Wsub S U ⊓ S1 S K₁) = 2)
    (hg : (h⁻¹ * y * h) * y ∈ Aof S K₁ W₂ h) {w : G} (hwW : w ∈ Wsub S U) (hwn : w ∉ S1 S K₁) :
    (h⁻¹ * w * h) * w⁻¹ ∈ Aof S K₁ W₂ h := by
  have hS1S : (S1 S K₁).relIndex S = 2 := hs.relIndex_S1_S hSne
  have hdW : h⁻¹ * w * h ∈ Wsub S U := hs.W_conj_h hwW
  have hwS : w ∈ S := hwW.1
  have hconj := hs.W₀_conj hII hq hrec hk hyW hyS1 hyA hrelA hg
  have hcube := hs.cube_conj hwW
  have hdn : h⁻¹ * w * h ∉ S1 S K₁ := by
    intro hd
    have h1 : h⁻¹ * w * h ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨hdW, hd⟩
    have h2 := hconj _ h1
    have h3 := hconj _ h2
    rw [hcube] at h3
    exact hwn h3.2
  have hdw : (h⁻¹ * w * h) * w⁻¹ ∈ S1 S K₁ :=
    Basic.mul_inv_mem_of_relIndex_two hS1S hdW.1 hwS hdn hwn
  have hdwW : (h⁻¹ * w * h) * w⁻¹ ∈ Wsub S U := mul_mem hdW (inv_mem hwW)
  by_contra hnotA
  have h5 : ((h⁻¹ * w * h) * w⁻¹) * y⁻¹ ∈ Aof S K₁ W₂ h :=
    Basic.mul_inv_mem_of_relIndex_two hrelA (Subgroup.mem_inf.2 ⟨hdwW, hdw⟩)
      (Subgroup.mem_inf.2 ⟨hyW, hyS1⟩) hnotA hyA
  obtain ⟨a₁, ha₁def⟩ : ∃ a₁, a₁ = ((h⁻¹ * w * h) * w⁻¹) * y⁻¹ := ⟨_, rfl⟩
  have ha₁A : a₁ ∈ Aof S K₁ W₂ h := ha₁def ▸ h5
  obtain ⟨gg, hgg⟩ : ∃ gg, gg = (h⁻¹ * y * h) * y := ⟨_, rfl⟩
  have hggA : gg ∈ Aof S K₁ W₂ h := hgg ▸ hg
  have hd : h⁻¹ * w * h = a₁ * y * w := by rw [ha₁def]; group
  have hψy : h⁻¹ * y * h = gg * y⁻¹ := by rw [hgg]; group
  have hyinvA : y⁻¹ * a₁ * y ∈ Aof S K₁ W₂ h := by
    have := hs.A_normS hII hq hrec (inv_mem hyW.1) ha₁A
    rwa [inv_inv] at this
  obtain ⟨a₃, ha₃def⟩ : ∃ a₃, a₃ = (h⁻¹ * a₁ * h) * gg * (y⁻¹ * a₁ * y) := ⟨_, rfl⟩
  have ha₃A : a₃ ∈ Aof S K₁ W₂ h := by
    rw [ha₃def]
    exact mul_mem (mul_mem (hs.A_conj hII hq hrec hk ha₁A).2 hggA) hyinvA
  have hψ2 : h⁻¹ * (h⁻¹ * w * h) * h = a₃ * w := by
    calc h⁻¹ * (h⁻¹ * w * h) * h = h⁻¹ * (a₁ * y * w) * h := by rw [hd]
      _ = (h⁻¹ * a₁ * h) * (h⁻¹ * y * h) * (h⁻¹ * w * h) := by group
      _ = (h⁻¹ * a₁ * h) * (gg * y⁻¹) * (a₁ * y * w) := by rw [hψy, hd]
      _ = ((h⁻¹ * a₁ * h) * gg * (y⁻¹ * a₁ * y)) * w := by group
      _ = a₃ * w := by rw [ha₃def]
  have hψ3 : h⁻¹ * (h⁻¹ * (h⁻¹ * w * h) * h) * h = (h⁻¹ * a₃ * h) * (a₁ * y * w) := by
    rw [hψ2]
    calc h⁻¹ * (a₃ * w) * h = (h⁻¹ * a₃ * h) * (h⁻¹ * w * h) := by group
      _ = (h⁻¹ * a₃ * h) * (a₁ * y * w) := by rw [hd]
  rw [hcube] at hψ3
  have h6 : (h⁻¹ * a₃ * h) * a₁ * y = 1 := by
    calc (h⁻¹ * a₃ * h) * a₁ * y = ((h⁻¹ * a₃ * h) * (a₁ * y * w)) * w⁻¹ := by group
      _ = w * w⁻¹ := by rw [← hψ3]
      _ = 1 := by group
  apply hyA
  have h7 := eq_inv_of_mul_eq_one_right h6
  rw [h7]
  exact inv_mem (mul_mem ((hs.A_conj hII hq hrec hk ha₃A).2) ha₁A)

theorem S_eq_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2) {m : ℕ}
    (hm : 2 ≤ m) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) : S = S1 S K₁ := by
  by_contra hSne
  have hk2 : 2 ≤ m + 1 := by omega
  obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  obtain ⟨y₂, hy₂P, hy₂sq, hy₂inv, -⟩ := hs.exists_y₂ hII hq hrec hk
  have hyW := hs.y_mem_W hII hq hy₁P hy₂P hy₁inv hy₂inv
  have hyV₁ := hs.y_inv_V₁ hII hy₂P hy₁inv
  have hyV₂ := hs.y_inv_V₂ hII hy₁P hy₂inv
  have hyA := hs.not_mem_A_of_inv hII hq hrec hyV₁
  have hyS1 : y₁ * y₂ ∈ S1 S K₁ :=
    mul_mem (hs.P_le_S1 hII (Or.inl rfl) hy₁P) (hs.P_le_S1 hII (Or.inr rfl) hy₂P)
  have hrelA := hs.A_relIndex_W₀ hII hq hrec he hk2 hk hy₁P hy₁inv
  have hmod := hs.y_inv_mod_U hII hq hrec hk2 hk hyW.1 hyV₁ hyV₂
  have hg := hs.g_mem_A hII hq hrec he hm hk hSne hyW hyS1 hyA hyV₁ hrelA hmod
  obtain ⟨w, hwW, hwn⟩ := hs.exists_W_not_S1 hII hq hSne hy₁P hy₁inv
  have hsigma := hs.sigma_mem_A hII hq hrec hk hSne hyW hyS1 hyA hrelA hg hwW hwn
  have hS1S : (S1 S K₁).relIndex S = 2 := hs.relIndex_S1_S hSne
  have hwS : w ∈ S := hwW.1
  obtain ⟨x, hxV, hVx, hxo, hxz⟩ := hs.gen_V₁ hII hq hk
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx'V : h⁻¹ * x * h ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rw [e]; exact hxV
  have hx'A : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right hx'V
  have hx'o : orderOf (h⁻¹ * x * h) = 2 ^ (m + 1) := by
    have h1 := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective x
    have e : (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by simp
    rw [e, hxo] at h1
    exact h1
  have hbot : Subgroup.zpowers x ⊓ Subgroup.zpowers (h⁻¹ * x * h) = ⊥ := by
    have h1 : Subgroup.zpowers x ≤ Vof S K₁ W₂ := Subgroup.zpowers_le.2 hxV
    have h2 : Subgroup.zpowers (h⁻¹ * x * h) ≤ conjugate (Vof S K₁ W₂) h :=
      Subgroup.zpowers_le.2 hx'V
    exact le_bot_iff.1 ((inf_le_inf h1 h2).trans (hs.V₁_inf_V_bot hII hq).le)
  have hcomm : x * (h⁻¹ * x * h) = (h⁻¹ * x * h) * x := hs.A_comm hII hq hrec _ hxA _ hx'A
  have hVh : conjugate (Vof S K₁ W₂) h ≤ Subgroup.zpowers (h⁻¹ * x * h) := by
    intro a₂ ha₂
    have h1 : h * a₂ * h⁻¹ ∈ Vof S K₁ W₂ := mem_conjugate_iff.1 ha₂
    rw [hVx] at h1
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h1
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    have h2 := conj_zpow (a := h⁻¹) (b := x) (i := i)
    rw [inv_inv] at h2
    rw [h2, hi]
    group
  have hAle : Aof S K₁ W₂ h ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers (h⁻¹ * x * h) := by
    apply sup_le
    · rw [← hVx]; exact le_sup_left
    · exact hVh.trans le_sup_right
  have hwx : w * x * w⁻¹ ∈ Vof S K₂ W₁ := by
    obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
    have hV := hs.card_V₁ hII hq
    have h8 : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have he1 : e = 1 := by omega
    subst he1
    have h16 : 16 ≤ Nat.card ↥(Qof S K₁) := by omega
    exact (hs.swap_V hII hq hrec h16 hwS hwn).1 x hxV
  have hwinv : w⁻¹ ∉ S1 S K₁ := fun h' => hwn (by simpa using inv_mem h')
  have hwwS1 : w * w ∈ S1 S K₁ := by
    have := Basic.mul_inv_mem_of_relIndex_two hS1S hwS (inv_mem hwS) hwn hwinv
    simpa using this
  have hww : w * w ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨mul_mem hwW hwW, hwwS1⟩
  have hφφ : w * (w * x * w⁻¹) * w⁻¹ = x ∨ w * (w * x * w⁻¹) * w⁻¹ = x⁻¹ := by
    have e : w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
    rw [e]
    by_cases hwwA : w * w ∈ Aof S K₁ W₂ h
    · left
      have hc : (w * w) * x = x * (w * w) := hs.A_comm hII hq hrec _ hwwA _ hxA
      calc (w * w) * x * (w * w)⁻¹ = (x * (w * w)) * (w * w)⁻¹ := by rw [hc]
        _ = x := by group
    · right
      have ha₀ : (w * w) * (y₁ * y₂)⁻¹ ∈ Aof S K₁ W₂ h :=
        Basic.mul_inv_mem_of_relIndex_two hrelA hww (Subgroup.mem_inf.2 ⟨hyW, hyS1⟩) hwwA hyA
      have hdx : (y₁ * y₂) * x * (y₁ * y₂)⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hyW.1 hxA
      have hcomm2 : ((w * w) * (y₁ * y₂)⁻¹) * ((y₁ * y₂) * x * (y₁ * y₂)⁻¹) =
          ((y₁ * y₂) * x * (y₁ * y₂)⁻¹) * ((w * w) * (y₁ * y₂)⁻¹) :=
        hs.A_comm hII hq hrec _ ha₀ _ hdx
      calc (w * w) * x * (w * w)⁻¹
          = ((w * w) * (y₁ * y₂)⁻¹) * ((y₁ * y₂) * x * (y₁ * y₂)⁻¹) *
              ((w * w) * (y₁ * y₂)⁻¹)⁻¹ := by group
        _ = ((y₁ * y₂) * x * (y₁ * y₂)⁻¹) * ((w * w) * (y₁ * y₂)⁻¹) *
              ((w * w) * (y₁ * y₂)⁻¹)⁻¹ := by rw [hcomm2]
        _ = (y₁ * y₂) * x * (y₁ * y₂)⁻¹ := by group
        _ = x⁻¹ := hyV₁ x hxV
  have hφψ : w * (h⁻¹ * x * h) * w⁻¹ = h⁻¹ * (w * x * w⁻¹) * h := by
    have hx'wA : w * (h⁻¹ * x * h) * w⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec hwS hx'A
    have hcomm₀ : ((h⁻¹ * w * h) * w⁻¹) * (w * (h⁻¹ * x * h) * w⁻¹) =
        (w * (h⁻¹ * x * h) * w⁻¹) * ((h⁻¹ * w * h) * w⁻¹) :=
      hs.A_comm hII hq hrec _ hsigma _ hx'wA
    calc w * (h⁻¹ * x * h) * w⁻¹
        = ((w * (h⁻¹ * x * h) * w⁻¹) * ((h⁻¹ * w * h) * w⁻¹)) * ((h⁻¹ * w * h) * w⁻¹)⁻¹ := by
          group
      _ = (((h⁻¹ * w * h) * w⁻¹) * (w * (h⁻¹ * x * h) * w⁻¹)) * ((h⁻¹ * w * h) * w⁻¹)⁻¹ := by
          rw [hcomm₀]
      _ = h⁻¹ * (w * x * w⁻¹) * h := by group
  have hzU : z ∈ U := hs.z_mem
  have hφz : w * z * w⁻¹ = z := by
    have := (Subgroup.mem_centralizer_iff.1 hwW.2) z hzU
    rw [← this]; group
  refine Basic.exp_contradiction (k := m + 1) (by omega) (x := x) (x' := h⁻¹ * x * h) (z := z)
    hxo hx'o hbot hcomm ?_ (MulAut.conj w) (MulAut.conj h⁻¹) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.add_sub_cancel]; exact hxz.symm
  · show h⁻¹ * x * h⁻¹⁻¹ = h⁻¹ * x * h
    rw [inv_inv]
  · show x * (h⁻¹ * x * h) * (h⁻¹ * (h⁻¹ * x * h) * h⁻¹⁻¹) = 1
    rw [inv_inv]
    exact hs.psi_rel hII hq hrec hk hxV
  · show w * (h⁻¹ * x * h) * w⁻¹ = h⁻¹ * (w * x * w⁻¹) * h⁻¹⁻¹
    rw [inv_inv]
    exact hφψ
  · exact hφz
  · show w * x * w⁻¹ ∈ _
    exact hAle (hs.A_normS hII hq hrec hwS hxA)
  · intro g hg
    have h1 : Subgroup.zpowers x ≤ Vof S K₁ W₂ := Subgroup.zpowers_le.2 hxV
    have h2 : Subgroup.zpowers (w * x * w⁻¹) ≤ Vof S K₂ W₁ := Subgroup.zpowers_le.2 hwx
    exact hs.V₁_inf_V₂_sq hII g (Subgroup.mem_inf.2 ⟨h1 hg.1, h2 hg.2⟩)
  · exact hφφ

end Setup8


end CFSG.GH74.GLS.Stage1.Thm3.Sec8
