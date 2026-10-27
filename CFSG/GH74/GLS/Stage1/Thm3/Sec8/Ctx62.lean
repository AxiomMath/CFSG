module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx60

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

theorem q8_inverting {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z v : G} (hQ : GQ Q z)
    (h8 : Nat.card ↥Q = 8) (hvQ : v ∈ Q) (hv2 : v * v = z) :
    ∃ a ∈ Q, a ∉ zpowers v ∧ a * a = z ∧ a * v * a⁻¹ = v⁻¹ := by
  have hz2 := hQ.z_sq
  have hz1 := hQ.z_ne
  have hC4 : Nat.card ↥(zpowers v) = 4 := card_zpowers_y hv2 hz2 hz1
  have hCQ : zpowers v ≤ Q := Subgroup.zpowers_le.2 hvQ
  obtain ⟨a, haQ, haC⟩ : ∃ a ∈ Q, a ∉ zpowers v := by
    by_contra hcon
    push Not at hcon
    have : Q ≤ zpowers v := fun a ha => hcon a ha
    have := Subgroup.card_le_of_le this
    omega
  obtain ⟨h1, h2⟩ := hQ.outside_cyclic (j := 3) (by rw [h8]; norm_num) hCQ inferInstance
    (by rw [hC4, h8]) (by rw [hC4]) haQ haC
  exact ⟨a, haQ, haC, h1, h2 v (Subgroup.mem_zpowers v)⟩

end Basic

theorem EData.swap' {G : Type} [Group G] {Y U E₁ E₂ : Subgroup G} (hE : EData Y U E₁ E₂) :
    EData Y U E₂ E₁ where
  le₁ := hE.le₂
  le₂ := hE.le₁
  elem₁ := hE.elem₂
  elem₂ := hE.elem₁
  card₁ := hE.card₂
  card₂ := hE.card₁
  inter := by rw [inf_comm]; exact hE.inter
  prod := by rw [sup_comm]; exact hE.prod
  invol := fun y hy h2 => (hE.invol y hy h2).symm
  comm := fun e he f hf => by
    have h1 := hE.comm f hf e he
    have : e * f * e⁻¹ * f⁻¹ = (f * e * f⁻¹ * e⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem h1

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem mem_W_of_comm_u (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G}
    (hxS : x ∈ S) (hxu : x * u = u * x) : x ∈ Wsub S U := by
  refine ⟨hxS, Subgroup.mem_centralizer_iff.2 (fun c hc => ?_)⟩
  rcases hs.U_elems c hc with h1 | h1 | h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact hs.z_comm hII hxS
  · rw [h1]; exact hxu.symm
  · rw [h1]
    calc u * z * x = u * (z * x) := by group
      _ = u * (x * z) := by rw [hs.z_comm hII hxS]
      _ = (u * x) * z := by group
      _ = (x * u) * z := by rw [hxu]
      _ = x * (u * z) := by group

theorem diag_mem_W (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {v₁ v₂ b₁ b₂ : G}
    (hu : u = v₁ * v₂) (hv₁ : v₁ ∈ Pof S K₁) (hv₂ : v₂ ∈ Pof S K₂) (hb₁ : b₁ ∈ Pof S K₁)
    (hb₂ : b₂ ∈ Pof S K₂) (hb₁i : b₁ * v₁ * b₁⁻¹ = v₁⁻¹) (hb₂i : b₂ * v₂ * b₂⁻¹ = v₂⁻¹) :
    b₁ * b₂ ∈ Wsub S U := by
  have hcomm := hs.P_comm hII
  have hu2 : u * u = 1 := hs.four_sq u hs.u_mem
  have c1 : b₂ * v₁ * b₂⁻¹ = v₁ := by
    calc b₂ * v₁ * b₂⁻¹ = (v₁ * b₂) * b₂⁻¹ := by rw [hcomm v₁ hv₁ b₂ hb₂]
      _ = v₁ := by group
  have c2 : b₁ * v₂ * b₁⁻¹ = v₂ := by
    calc b₁ * v₂ * b₁⁻¹ = (v₂ * b₁) * b₁⁻¹ := by rw [hcomm b₁ hb₁ v₂ hv₂]
      _ = v₂ := by group
  have hv12 : v₁ * v₂ = v₂ * v₁ := hcomm v₁ hv₁ v₂ hv₂
  have key : (b₁ * b₂) * u * (b₁ * b₂)⁻¹ = u := by
    rw [hu]
    calc (b₁ * b₂) * (v₁ * v₂) * (b₁ * b₂)⁻¹
        = b₁ * (b₂ * v₁ * b₂⁻¹) * (b₂ * v₂ * b₂⁻¹) * b₁⁻¹ := by group
      _ = b₁ * v₁ * (b₂ * v₂ * b₂⁻¹) * b₁⁻¹ := by rw [c1]
      _ = b₁ * v₁ * v₂⁻¹ * b₁⁻¹ := by rw [hb₂i]
      _ = (b₁ * v₁ * b₁⁻¹) * (b₁ * v₂⁻¹ * b₁⁻¹) := by group
      _ = v₁⁻¹ * (b₁ * v₂ * b₁⁻¹)⁻¹ := by rw [hb₁i]; group
      _ = v₁⁻¹ * v₂⁻¹ := by rw [c2]
      _ = (v₂ * v₁)⁻¹ := by group
      _ = (v₁ * v₂)⁻¹ := by rw [hv12]
      _ = v₁ * v₂ := by
        have : (v₁ * v₂) * (v₁ * v₂) = 1 := by rw [← hu]; exact hu2
        exact inv_eq_of_mul_eq_one_right this
  have hxu : (b₁ * b₂) * u = u * (b₁ * b₂) := by
    calc (b₁ * b₂) * u = ((b₁ * b₂) * u * (b₁ * b₂)⁻¹) * (b₁ * b₂) := by group
      _ = u * (b₁ * b₂) := by rw [key]
  exact hs.mem_W_of_comm_u hII (mul_mem hb₁.1 hb₂.1) hxu

theorem Y_inf_P (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {Y : Subgroup G} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) (hS128 : Nat.card ↥S = 2 ^ 7)
    (hP32 : Nat.card ↥(Pz S z) = 32) (hYS : Y ≤ S) (hYW : Y ≤ Wsub S U) (hY64 : Nat.card ↥Y = 64) :
    ∀ x ∈ Pz S z, x ∈ Wsub S U → x ∈ Y := by
  have hYN : Y ≤ normalizer (Pz S z : Set G) := by
    intro y hy
    have hyS := hYS hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hs.S_normalizes_Pz hII hyS x hx
    · intro hx
      have := hs.S_normalizes_Pz hII (inv_mem hyS) _ hx
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [e] at this
  have h1 := Basic.card_sup_mul_card_inf' (A := Pz S z) (B := Y) hYN
  have h2 : Nat.card ↥(Pz S z ⊔ Y) ≤ 128 := by
    have := Subgroup.card_le_of_le (sup_le (inf_le_left : Pz S z ≤ S) hYS)
    rw [hS128] at this
    norm_num at this
    exact this
  have h3 : 16 ≤ Nat.card ↥(Pz S z ⊓ Y) := by
    rw [hP32, hY64] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(Pz S z ⊔ Y) * Nat.card ↥(Pz S z ⊓ Y) ≤ 128 * 15 :=
      Nat.mul_le_mul h2 (by omega)
    omega
  obtain ⟨t₀, ht₀P, -, ht₀u⟩ := hs.exists_t₀ hII hq hk
  have ht₀W : t₀ ∉ Wsub S U := hs.t₀_not_mem_W hII ht₀P.1 ht₀u
  have h4 : Nat.card ↥(Pz S z ⊓ Wsub S U) ≤ 16 := by
    have hle : Pz S z ⊓ Wsub S U ≤ Pz S z := inf_le_left
    have h5 := Basic.card_mul_relIndex_of_le hle
    have hne : (Pz S z ⊓ Wsub S U).relIndex (Pz S z) ≠ 1 := by
      intro h6
      have := Subgroup.relIndex_eq_one.1 h6
      exact ht₀W (this ht₀P).2
    have hpos : (Pz S z ⊓ Wsub S U).relIndex (Pz S z) ≠ 0 := Basic.relIndex_ne_zero' _ _
    rw [hP32] at h5
    have hge : 2 ≤ (Pz S z ⊓ Wsub S U).relIndex (Pz S z) := by omega
    by_contra hgt
    push Not at hgt
    have : 17 * 2 ≤ Nat.card ↥(Pz S z ⊓ Wsub S U) * (Pz S z ⊓ Wsub S U).relIndex (Pz S z) :=
      Nat.mul_le_mul hgt hge
    omega
  have h5 : Pz S z ⊓ Y = Pz S z ⊓ Wsub S U :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_left _ hYW) (by omega)
  intro x hxP hxW
  have : x ∈ Pz S z ⊓ Wsub S U := ⟨hxP, hxW⟩
  rw [← h5] at this
  exact this.2

theorem exists_E_inf_P (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    {Y E₁ E₂ : Subgroup G} (hE : EData Y U E₁ E₂)
    (hPY : ∀ x ∈ Pz S z, x ∈ Wsub S U → x ∈ Y) :
    (∃ e ∈ E₁, e ∈ Pz S z ∧ e ∉ U) ∧ (∃ e ∈ E₂, e ∈ Pz S z ∧ e ∉ U) := by
  have hzz := hs.z_sq
  have hz1 := hs.z_ne
  have hP₂8 := (hs.cases8_aux hII hq hrec hP8).1
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, hv₁2, hv₂2⟩ := hs.u_decomp hII hq
  have hv₁P : v₁ ∈ Pof S K₁ := hv₁.2
  have hv₂P : v₂ ∈ Pof S K₂ := hv₂.2
  obtain ⟨a₁, ha₁P, ha₁C, ha₁sq, ha₁inv⟩ :=
    Basic.q8_inverting (hs.gq_P hII hq (Or.inl rfl)) hP8 hv₁P hv₁2
  obtain ⟨a₂, ha₂P, ha₂C, ha₂sq, ha₂inv⟩ :=
    Basic.q8_inverting (hs.gq_P hII hq (Or.inr rfl)) hP₂8 hv₂P hv₂2
  have hcomm := hs.P_comm hII
  have hzc : ∀ x ∈ S, z * x = x * z := fun x hx => hs.z_comm hII hx
  have ha₁'P : a₁ * v₁ ∈ Pof S K₁ := mul_mem ha₁P hv₁P
  have hv₁a : v₁ * a₁ = a₁ * v₁⁻¹ := by
    have h1 : a₁ * v₁⁻¹ * a₁⁻¹ = v₁ := by
      have := congrArg (fun x => x⁻¹) ha₁inv
      simpa [mul_assoc] using this
    calc v₁ * a₁ = (a₁ * v₁⁻¹ * a₁⁻¹) * a₁ := by rw [h1]
      _ = a₁ * v₁⁻¹ := by group
  have ha₁'sq : (a₁ * v₁) * (a₁ * v₁) = z := by
    calc (a₁ * v₁) * (a₁ * v₁) = a₁ * (v₁ * a₁) * v₁ := by group
      _ = a₁ * (a₁ * v₁⁻¹) * v₁ := by rw [hv₁a]
      _ = a₁ * a₁ := by group
      _ = z := ha₁sq
  have ha₁'inv : (a₁ * v₁) * v₁ * (a₁ * v₁)⁻¹ = v₁⁻¹ := by
    calc (a₁ * v₁) * v₁ * (a₁ * v₁)⁻¹ = a₁ * v₁ * a₁⁻¹ := by group
      _ = v₁⁻¹ := ha₁inv
  have ha₁'C : a₁ * v₁ ∉ zpowers v₁ := by
    intro hmem
    apply ha₁C
    have : a₁ = (a₁ * v₁) * v₁⁻¹ := by group
    rw [this]
    exact mul_mem hmem (inv_mem (Subgroup.mem_zpowers v₁))
  have hxW : a₁ * a₂ ∈ Wsub S U := hs.diag_mem_W hII huv hv₁P hv₂P ha₁P ha₂P ha₁inv ha₂inv
  have hyW : (a₁ * v₁) * a₂ ∈ Wsub S U :=
    hs.diag_mem_W hII huv hv₁P hv₂P ha₁'P ha₂P ha₁'inv ha₂inv
  have hxP : a₁ * a₂ ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII]; exact Subgroup.mul_mem_sup ha₁P ha₂P
  have hyP : (a₁ * v₁) * a₂ ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII]; exact Subgroup.mul_mem_sup ha₁'P ha₂P
  have hxY : a₁ * a₂ ∈ Y := hPY _ hxP hxW
  have hyY : (a₁ * v₁) * a₂ ∈ Y := hPY _ hyP hyW
  have hz₂ : z * a₂ = a₂ * z := hzc a₂ ha₂P.1
  have hx2 : (a₁ * a₂) * (a₁ * a₂) = 1 := by
    calc (a₁ * a₂) * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hcomm a₁ ha₁P a₂ ha₂P]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁sq, ha₂sq, hzz]
  have hy2 : ((a₁ * v₁) * a₂) * ((a₁ * v₁) * a₂) = 1 := by
    calc ((a₁ * v₁) * a₂) * ((a₁ * v₁) * a₂)
        = (a₁ * v₁) * (a₂ * (a₁ * v₁)) * a₂ := by group
      _ = (a₁ * v₁) * ((a₁ * v₁) * a₂) * a₂ := by rw [← hcomm _ ha₁'P a₂ ha₂P]
      _ = ((a₁ * v₁) * (a₁ * v₁)) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁'sq, ha₂sq, hzz]
  have hnc : (a₁ * a₂) * ((a₁ * v₁) * a₂) ≠ ((a₁ * v₁) * a₂) * (a₁ * a₂) := by
    intro hxy
    have e1 : (a₁ * a₂) * ((a₁ * v₁) * a₂) = (a₁ * (a₁ * v₁)) * (a₂ * a₂) := by
      calc (a₁ * a₂) * ((a₁ * v₁) * a₂) = a₁ * (a₂ * (a₁ * v₁)) * a₂ := by group
        _ = a₁ * ((a₁ * v₁) * a₂) * a₂ := by rw [← hcomm _ ha₁'P a₂ ha₂P]
        _ = (a₁ * (a₁ * v₁)) * (a₂ * a₂) := by group
    have e2 : ((a₁ * v₁) * a₂) * (a₁ * a₂) = ((a₁ * v₁) * a₁) * (a₂ * a₂) := by
      calc ((a₁ * v₁) * a₂) * (a₁ * a₂) = (a₁ * v₁) * (a₂ * a₁) * a₂ := by group
        _ = (a₁ * v₁) * (a₁ * a₂) * a₂ := by rw [← hcomm a₁ ha₁P a₂ ha₂P]
        _ = ((a₁ * v₁) * a₁) * (a₂ * a₂) := by group
    rw [e1, e2, ha₂sq] at hxy
    have e3 : a₁ * (a₁ * v₁) = z * v₁ := by
      calc a₁ * (a₁ * v₁) = (a₁ * a₁) * v₁ := by group
        _ = z * v₁ := by rw [ha₁sq]
    have e4 : (a₁ * v₁) * a₁ = z * v₁⁻¹ := by
      calc (a₁ * v₁) * a₁ = a₁ * (v₁ * a₁) := by group
        _ = a₁ * (a₁ * v₁⁻¹) := by rw [hv₁a]
        _ = (a₁ * a₁) * v₁⁻¹ := by group
        _ = z * v₁⁻¹ := by rw [ha₁sq]
    rw [e3, e4] at hxy
    have h5 : v₁ = v₁⁻¹ := mul_left_cancel (mul_right_cancel hxy)
    apply hz1
    rw [← hv₁2]
    calc v₁ * v₁ = v₁ * v₁⁻¹ := by rw [← h5]
      _ = 1 := mul_inv_cancel v₁
  have hx1 : a₁ * a₂ ≠ 1 := fun e => hnc (by rw [e]; simp)
  have hy1 : (a₁ * v₁) * a₂ ≠ 1 := fun e => hnc (by rw [e]; simp)
  have hxo : orderOf (a₁ * a₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hyo : orderOf ((a₁ * v₁) * a₂) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hxU : a₁ * a₂ ∉ U := by
    intro hxU
    exact hnc (hyW.2 (a₁ * a₂) hxU)
  have hyU : (a₁ * v₁) * a₂ ∉ U := by
    intro hyU
    exact hnc (hxW.2 ((a₁ * v₁) * a₂) hyU).symm
  rcases hE.invol _ hxY hxo with hx | hx <;> rcases hE.invol _ hyY hyo with hy | hy
  · exact absurd (hE.elem₁.1 _ hx _ hy) hnc
  · exact ⟨⟨a₁ * a₂, hx, hxP, hxU⟩, ⟨(a₁ * v₁) * a₂, hy, hyP, hyU⟩⟩
  · exact ⟨⟨(a₁ * v₁) * a₂, hy, hyP, hyU⟩, ⟨a₁ * a₂, hx, hxP, hxU⟩⟩
  · exact absurd (hE.elem₂.1 _ hx _ hy) hnc

theorem invol_E_conj (hII : II4_4_4_center) (hq : II4_4_quat) (h31 : IVK_3_1a_lifted)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {Y E : Subgroup G} (hEY : E ≤ Y)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE16 : Nat.card ↥E = 16) (hUE : U ≤ E)
    (hEh : ∀ x ∈ E, h⁻¹ * x * h ∈ E) (hYcent : ∀ y ∈ Y, h * y = y * h → y = 1)
    (hY3 : ∀ y ∈ Y, h ^ 3 * y = y * h ^ 3)
    (hex : ∃ e ∈ E, e ∈ Pz S z ∧ e ∉ U) : ∀ e ∈ E, orderOf e = 2 → IsConj z e := by
  obtain ⟨e₀, he₀E, he₀P, he₀U⟩ := hex
  have hTE : E ⊓ Pz S z ≤ E := inf_le_left
  have hUT : U ≤ E ⊓ Pz S z := fun x hx => ⟨hUE hx, hs.U_le_Pz hII hq hx⟩
  have hU4 : Nat.card ↥U = 4 := hs.U_four.2
  have hcardT : 8 ≤ Nat.card ↥(E ⊓ Pz S z) := by
    have h1 : Nat.card ↥U ∣ Nat.card ↥(E ⊓ Pz S z) := Subgroup.card_dvd_of_le hUT
    have h4 : Nat.card ↥U ≤ Nat.card ↥(E ⊓ Pz S z) := Subgroup.card_le_of_le hUT
    by_contra hlt
    push Not at hlt
    rw [hU4] at h1 h4
    have h5 : Nat.card ↥(E ⊓ Pz S z) = 4 := by omega
    have h6 : U = E ⊓ Pz S z := Subgroup.eq_of_le_of_card_ge hUT (by omega)
    apply he₀U
    rw [h6]
    exact ⟨he₀E, he₀P⟩
  have hmul := Basic.card_mul_relIndex_of_le hTE
  rw [hE16] at hmul
  have hrel : (E ⊓ Pz S z).relIndex E = 1 ∨ (E ⊓ Pz S z).relIndex E = 2 := by
    have hpos : (E ⊓ Pz S z).relIndex E ≠ 0 := Basic.relIndex_ne_zero' _ _
    by_contra hcon
    push Not at hcon
    have h3 : 3 ≤ (E ⊓ Pz S z).relIndex E := by omega
    have : 8 * 3 ≤ Nat.card ↥(E ⊓ Pz S z) * (E ⊓ Pz S z).relIndex E := Nat.mul_le_mul hcardT h3
    omega
  have hone : ∀ x ∈ E, ∀ y ∈ E, x ∉ E ⊓ Pz S z → y ∉ E ⊓ Pz S z → x * y⁻¹ ∈ E ⊓ Pz S z := by
    intro x hx y hy hxT hyT
    rcases hrel with h1 | h1
    · exact absurd ((Subgroup.relIndex_eq_one.1 h1) hx) hxT
    · exact Basic.mul_inv_mem_of_relIndex_two h1 hx hy hxT hyT
  intro e he he2
  have hee : e * e = 1 := mul_self_eq_one_of_orderOf_eq_two he2
  have he₁ : h⁻¹ * e * h ∈ E := hEh e he
  have he₂ : h⁻¹ * (h⁻¹ * e * h) * h ∈ E := hEh _ he₁
  have hprod : e * (h⁻¹ * e * h) * (h⁻¹ * (h⁻¹ * e * h) * h) = 1 := by
    have hcube : h ^ 3 * e = e * h ^ 3 := hY3 e (hEY he)
    have h3 : h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h = e := by
      have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
      rw [e3] at hcube
      calc h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h
          = (h * h * h)⁻¹ * (e * (h * h * h)) := by group
        _ = (h * h * h)⁻¹ * ((h * h * h) * e) := by rw [hcube]
        _ = e := by group
    set a := e * (h⁻¹ * e * h) * (h⁻¹ * (h⁻¹ * e * h) * h) with ha
    have haE : a ∈ E := mul_mem (mul_mem he he₁) he₂
    have hha : h⁻¹ * a * h = a := by
      have : h⁻¹ * a * h = (h⁻¹ * e * h) * (h⁻¹ * (h⁻¹ * e * h) * h) *
          (h⁻¹ * (h⁻¹ * (h⁻¹ * e * h) * h) * h) := by rw [ha]; group
      rw [this, h3, ha]
      have hc1 := hEc e he _ he₁
      have hc2 := hEc e he _ he₂
      have hc3 := hEc _ he₁ _ he₂
      calc (h⁻¹ * e * h) * (h⁻¹ * (h⁻¹ * e * h) * h) * e
          = (h⁻¹ * e * h) * ((h⁻¹ * (h⁻¹ * e * h) * h) * e) := by group
        _ = (h⁻¹ * e * h) * (e * (h⁻¹ * (h⁻¹ * e * h) * h)) := by rw [hc2.symm]
        _ = ((h⁻¹ * e * h) * e) * (h⁻¹ * (h⁻¹ * e * h) * h) := by group
        _ = (e * (h⁻¹ * e * h)) * (h⁻¹ * (h⁻¹ * e * h) * h) := by rw [hc1.symm]
    have hha' : h * a = a * h := by
      calc h * a = h * (h⁻¹ * a * h) := by rw [hha]
        _ = a * h := by group
    exact hYcent a (hEY haE) hha'
  have hconj1 : IsConj e (h⁻¹ * e * h) := isConj_iff.2 ⟨h⁻¹, by group⟩
  have hconj2 : IsConj e (h⁻¹ * (h⁻¹ * e * h) * h) :=
    hconj1.trans (isConj_iff.2 ⟨h⁻¹, by group⟩)
  have ho1 : orderOf (h⁻¹ * e * h) = 2 := by
    have := orderOf_conj' h⁻¹ e
    rw [inv_inv] at this
    rw [this, he2]
  have ho2 : orderOf (h⁻¹ * (h⁻¹ * e * h) * h) = 2 := by
    have := orderOf_conj' h⁻¹ (h⁻¹ * e * h)
    rw [inv_inv] at this
    rw [this, ho1]
  by_cases hT0 : e ∈ E ⊓ Pz S z
  · exact (hs.invol_P_conj hII h31 e hT0.2 he2)
  by_cases hT1 : h⁻¹ * e * h ∈ E ⊓ Pz S z
  · exact (hs.invol_P_conj hII h31 _ hT1.2 ho1).trans hconj1.symm
  by_cases hT2 : h⁻¹ * (h⁻¹ * e * h) * h ∈ E ⊓ Pz S z
  · exact (hs.invol_P_conj hII h31 _ hT2.2 ho2).trans hconj2.symm
  exfalso
  have hT1' : (h⁻¹ * e * h)⁻¹ ∉ E ⊓ Pz S z := fun hh => hT1 (by simpa using inv_mem hh)
  have h12 := hone e he _ (inv_mem he₁) hT0 hT1'
  rw [inv_inv] at h12
  have : h⁻¹ * (h⁻¹ * e * h) * h = (e * (h⁻¹ * e * h))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  exact hT2 (by rw [this]; exact inv_mem h12)

theorem one_class_final (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hP8 : Nat.card ↥(Pof S K₁) = 8) (hS128 : Nat.card ↥S = 2 ^ 7)
    {Y D : Subgroup G} {t w : G} (hC : Concl86 z S K₁ W₂ U u h Y D t w) {E₁ E₂ : Subgroup G}
    (hE : EData Y U E₁ E₂) : ∀ v : G, orderOf v = 2 → IsConj z v := by
  obtain ⟨hD, hY⟩ := hs.YData_of_concl86 hC hE
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hP₂ := (hs.cases8_aux hII hq hrec hP8).1
  have hP32 : Nat.card ↥(Pz S z) = 32 := by
    have := hs.card_P hII
    rw [hP8, hP₂] at this
    omega
  have hYS : Y ≤ S := hY.Y_le_S
  have hY64 : Nat.card ↥Y = 64 := hY.card
  have hPY := hs.Y_inf_P hII hq hk hS128 hP32 hYS hY.le_W hY64
  obtain ⟨⟨e₁, he₁E, he₁P, he₁U⟩, ⟨e₂, he₂E, he₂P, he₂U⟩⟩ :=
    hs.exists_E_inf_P hII hq hrec hP8 hE hPY
  have hUE₁ : U ≤ E₁ := hE.inter ▸ inf_le_left
  have hUE₂ : U ≤ E₂ := hE.inter ▸ inf_le_right
  have hY3 : ∀ y ∈ Y, h ^ 3 * y = y * h ^ 3 := fun y hy => hs.h_cube y (hY.le_W hy)
  have hE₁h := hs.E₁_hnorm hE hC
  have hE₂h := hs.E₁_hnorm hE.swap' hC
  have hI₁ := hs.invol_E_conj hII hq h31 hE.le₁ hE.elem₁.1 hE.card₁ hUE₁ hE₁h hY.cent_h hY3
    ⟨e₁, he₁E, he₁P, he₁U⟩
  have hI₂ := hs.invol_E_conj hII hq h31 hE.le₂ hE.elem₂.1 hE.card₂ hUE₂ hE₂h hY.cent_h hY3
    ⟨e₂, he₂E, he₂P, he₂U⟩
  have hIY : ∀ y ∈ Y, orderOf y = 2 → IsConj z y := by
    intro y hy hy2
    rcases hE.invol y hy hy2 with h1 | h1
    · exact hI₁ y h1 hy2
    · exact hI₂ y h1 hy2
  have hrelYS : Y.relIndex S = 2 := by
    have h1 := Basic.card_mul_relIndex_of_le hYS
    rw [hY64, hS128] at h1
    norm_num at h1
    omega
  have hIS : ∀ s ∈ S, orderOf s = 2 → IsConj z s := by
    intro s hsS hs2
    by_cases hsY : s ∈ Y
    · exact hIY s hsY hs2
    · have hss : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs2
      obtain ⟨g, hg, -⟩ := hs.transfer8 hII Y s hYS hrelYS hsS hsY hss
      have hgo : orderOf (g⁻¹ * s * g) = 2 := by
        have := orderOf_conj' g⁻¹ s
        rw [inv_inv] at this
        rw [this, hs2]
      exact (hIY _ hg hgo).trans (isConj_iff.2 ⟨g, by group⟩)
  intro v hv
  have hM := hs.m4 hII
  have hpg : IsPGroup 2 ↥(zpowers v) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hv, pow_one]⟩
  obtain ⟨P, hP, hvP⟩ := M.exists_syl2In_ge hpg (le_top : zpowers v ≤ ⊤)
  obtain ⟨c, -, hc⟩ := hM.S_top.exists_conj hP
  have hvP' : v ∈ P := hvP (Subgroup.mem_zpowers v)
  rw [hc, M.mem_cj] at hvP'
  have hw := hIS _ hvP' (by rw [orderOf_conj', hv])
  exact hw.trans (isConj_iff.2 ⟨c⁻¹, by group⟩)

end Setup8

theorem final81a (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) : Final81a := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS128 hC E₁ E₂ hE _
  exact hs.one_class_final hII hq hrec h31 hP8 hS128 hC hE

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
