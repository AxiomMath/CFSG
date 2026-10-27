module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611E

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OClasses

variable {G : Type*} [Group G] {α t : G}

theorem sqA_mul (hα : α * α = 1) {q q' : G} (hq : q = 1 ∨ q = α) (hq' : q' = 1 ∨ q' = α) :
    q * q' = 1 ∨ q * q' = α := by
  rcases hq with h1 | h1 <;> rcases hq' with h2 | h2 <;> rw [h1, h2]
  · left; rw [mul_one]
  · right; rw [one_mul]
  · right; rw [mul_one]
  · left; exact hα

theorem sqA_inv (hα : α * α = 1) {q : G} (hq : q = 1 ∨ q = α) : q⁻¹ = 1 ∨ q⁻¹ = α := by
  rcases hq with h1 | h1 <;> rw [h1]
  · left; simp
  · right; exact inv_eq_of_mul_eq_one_right hα

theorem sqB_mul_sqB (hα : α * α = 1) (ht : t * t = 1) (hc : α * t = t * α) {q q' : G}
    (hq : q = t ∨ q = α * t) (hq' : q' = t ∨ q' = α * t) : q * q' = 1 ∨ q * q' = α := by
  rcases hq with h1 | h1 <;> rcases hq' with h2 | h2 <;> rw [h1, h2]
  · left; exact ht
  · right
    calc t * (α * t) = (t * α) * t := by group
      _ = (α * t) * t := by rw [← hc]
      _ = α * (t * t) := by group
      _ = α := by rw [ht, mul_one]
  · right
    calc α * t * t = α * (t * t) := by group
      _ = α := by rw [ht, mul_one]
  · left
    calc α * t * (α * t) = α * (t * α) * t := by group
      _ = α * (α * t) * t := by rw [← hc]
      _ = (α * α) * (t * t) := by group
      _ = 1 := by rw [hα, ht, mul_one]

theorem sqA_sqB_false (ht1 : t ≠ 1) (hαt : α ≠ t) (hαt1 : α * t ≠ 1) (hαta : α * t ≠ α) {q : G}
    (hA : q = 1 ∨ q = α) (hB : q = t ∨ q = α * t) : False := by
  rcases hA with h1 | h1 <;> rcases hB with h2 | h2
  · exact ht1 (h2.symm.trans h1)
  · exact hαt1 (h2.symm.trans h1)
  · exact hαt (h1.symm.trans h2)
  · exact hαta (h2.symm.trans h1)

theorem orbit_parity {E : Subgroup G} {E2 E4 : Set G} {P0 P1 : G → Prop} (hE2 : E2 ⊆ E)
    (hP01 : ∀ x ∈ E2, P0 x ∨ P1 x) (hP : ∀ x ∈ E2, P0 x → P1 x → False)
    (horb2 : ∀ x ∈ E2, ∀ y ∈ E2, P1 x → P1 y) (horb4 : ∀ x ∈ E4, ∀ y ∈ E4, P0 x → P0 y)
    (h11 : ∀ x ∈ E, ∀ y ∈ E, P1 x → P1 y → P0 (x * y))
    (h00 : ∀ x ∈ E, ∀ y ∈ E, P0 x → P0 y → P0 (x * y)) (hinv : ∀ x ∈ E, P0 x → P0 x⁻¹)
    {x y z : G} (hx : x ∈ E2) (hy : y ∈ E2) (hz : z ∈ E2) (hxy : x * y ∈ E4)
    (hxyz : x * y * z ∈ E4) : ∀ e ∈ E2, P0 e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he, hne⟩ := hcon
  have h1e : P1 e := (hP01 e he).resolve_left hne
  have h1x := horb2 e he x hx h1e
  have h1y := horb2 e he y hy h1e
  have h1z := horb2 e he z hz h1e
  have hxE := hE2 hx
  have hyE := hE2 hy
  have hzE := hE2 hz
  have h0xy : P0 (x * y) := h11 x hxE y hyE h1x h1y
  have h0xyz : P0 (x * y * z) := horb4 _ hxy _ hxyz h0xy
  have hxyE : x * y ∈ E := mul_mem hxE hyE
  have h0z : P0 z := by
    have := h00 _ (inv_mem hxyE) _ (mul_mem hxyE hzE) (hinv _ hxyE h0xy) h0xyz
    rw [inv_mul_cancel_left] at this
    exact this
  exact hP z hz h0z h1z

end OClasses

open OClasses

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem alpha_t_ne {α : G} (hα : AlphaSpec S z t α) : α * t ≠ 1 ∧ α * t ≠ α := by
  refine ⟨fun h1 => hα.ne_t ?_, fun h1 => h.t_ne (mul_eq_left.1 h1)⟩
  have := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact inv_eq_of_mul_eq_one_right h.t_sq

theorem sq_eq_of_isLift {α : G} (hα : AlphaSpec S z t α) {ζ₀ x w w' : G}
    (hw : IsLift h hα ζ₀ x w) (hw' : IsLift h hα ζ₀ x w') : w' * w' = w * w := by
  have hu := h.isLift_unique hα hw hw'
  have hcu : (w⁻¹ * w') * w = w * (w⁻¹ * w') := (h.Zg_cent_Q hα hu).2 w hw.1
  have hu2 : (w⁻¹ * w') * (w⁻¹ * w') = 1 := h.Zg_sq hα hu
  calc w' * w' = (w * (w⁻¹ * w')) * (w * (w⁻¹ * w')) := by group
    _ = w * ((w⁻¹ * w') * w) * (w⁻¹ * w') := by group
    _ = w * (w * (w⁻¹ * w')) * (w⁻¹ * w') := by rw [hcu]
    _ = w * w * ((w⁻¹ * w') * (w⁻¹ * w')) := by group
    _ = w * w := by rw [hu2, mul_one]

theorem sq_conj_W {α : G} (hα : AlphaSpec S z t α) {b w : G}
    (hb : b ∈ L ⊓ centralizer ({t} : Set G))
    (hw : w ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    (b * w * b⁻¹) * (b * w * b⁻¹) = w * w := by
  have hZ : w * w ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (h.QF_sq hα hw)
  have hc : b * (w * w) = (w * w) * b := h.W_cent_Z hα hb hZ
  calc (b * w * b⁻¹) * (b * w * b⁻¹) = b * (w * w) * b⁻¹ := by group
    _ = w * w := by rw [hc]; group

theorem sq_mul_Qs {α : G} (hα : AlphaSpec S z t α) {w w' : G}
    (hw : w ∈ Fsub h hα ⊓ centralizer ({α} : Set G))
    (hw' : w' ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    (w * w') * (w * w') = (w * w' * w⁻¹ * w'⁻¹) * ((w * w) * (w' * w')) := by
  have hZ : w * w ∈ (zpowers α ⊔ zpowers t : Subgroup G) := (h.mem_Zg hα).2 (h.QF_sq hα hw)
  have hww : (w * w) * w' = w' * (w * w) := (h.Zg_cent_Q hα hZ).2 w' hw'
  calc (w * w') * (w * w')
      = ((w * w' * w⁻¹ * w'⁻¹) * (w' * w)) * (w * w') := by group
    _ = (w * w' * w⁻¹ * w'⁻¹) * (w' * (w * w) * w') := by group
    _ = (w * w' * w⁻¹ * w'⁻¹) * ((w * w) * w' * w') := by rw [← hww]
    _ = (w * w' * w⁻¹ * w'⁻¹) * ((w * w) * (w' * w')) := by group

theorem sq_lift_rel {α : G} (hα : AlphaSpec S z t α) {x w : G} (hx : x ∈ E)
    (hw : IsLift h hα α x w) : x * x = (w * w) * (z * (w * w) * z⁻¹) := by
  obtain ⟨a, ha, hxa, hcom⟩ := h.rel_d_t hα hx hw
  have hwQ := hw.1
  have hvQ : z * w * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := h.z_norm_Qs hα hwQ
  have haZ : a ∈ (zpowers α ⊔ zpowers t : Subgroup G) := by
    rcases ha with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact h.t_mem_Zg hα
  have haw : a * w = w * a := (h.Zg_cent_Q hα haZ).2 w hwQ
  have hav : a * (z * w * z⁻¹) = (z * w * z⁻¹) * a := (h.Zg_cent_Q hα haZ).2 _ hvQ
  have ha2 : a * a = 1 := h.Zg_sq hα haZ
  have e1 : (w * (z * w * z⁻¹) * a) * (w * (z * w * z⁻¹) * a) =
      (w * (z * w * z⁻¹)) * (w * (z * w * z⁻¹)) * (a * a) := by
    calc (w * (z * w * z⁻¹) * a) * (w * (z * w * z⁻¹) * a)
        = w * (z * w * z⁻¹) * (a * w) * (z * w * z⁻¹) * a := by group
      _ = w * (z * w * z⁻¹) * (w * a) * (z * w * z⁻¹) * a := by rw [haw]
      _ = w * (z * w * z⁻¹) * w * (a * (z * w * z⁻¹)) * a := by group
      _ = w * (z * w * z⁻¹) * w * ((z * w * z⁻¹) * a) * a := by rw [hav]
      _ = (w * (z * w * z⁻¹)) * (w * (z * w * z⁻¹)) * (a * a) := by group
  have e2 : (w * (z * w * z⁻¹)) * (w * (z * w * z⁻¹)) =
      (w * w) * ((z * w * z⁻¹) * (z * w * z⁻¹)) := by
    calc (w * (z * w * z⁻¹)) * (w * (z * w * z⁻¹))
        = w * ((z * w * z⁻¹) * w) * (z * w * z⁻¹) := by group
      _ = w * (w * (z * w * z⁻¹)) * (z * w * z⁻¹) := by rw [← hcom]
      _ = (w * w) * ((z * w * z⁻¹) * (z * w * z⁻¹)) := by group
  have e3 : (z * w * z⁻¹) * (z * w * z⁻¹) = z * (w * w) * z⁻¹ := by group
  calc x * x = (w * (z * w * z⁻¹) * a) * (w * (z * w * z⁻¹) * a) := by rw [← hxa]
    _ = (w * w) * (z * (w * w) * z⁻¹) := by rw [e1, e2, e3, ha2, mul_one]

theorem sq_conj_val {α : G} (hα : AlphaSpec S z t α) {q : G} :
    ((q = 1 ∨ q = t) → q * (z * q * z⁻¹) = 1) ∧
      ((q = α ∨ q = α * t) → q * (z * q * z⁻¹) = t) := by
  have hαt : α * t = t * α := h.t_comm_S α hα.mem
  have hzαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
      _ = α := by rw [mul_assoc, h.t_sq, mul_one]
  constructor
  · rintro (h1 | h1) <;> rw [h1]
    · group
    · rw [h.z_conj_t, h.t_sq]
  · rintro (h1 | h1) <;> rw [h1]
    · rw [h.z_conj_alpha hα]
      calc α * (α * t) = (α * α) * t := by group
        _ = t := by rw [hα.sq, one_mul]
    · rw [hzαt]
      calc α * t * α = α * (t * α) := by group
        _ = α * (α * t) := by rw [← hαt]
        _ = (α * α) * t := by group
        _ = t := by rw [hα.sq, one_mul]

@[expose] def SqEven {α : G} (hα : AlphaSpec S z t α) (x : G) : Prop :=
  ∃ w, IsLift h hα α x w ∧ (w * w = 1 ∨ w * w = α)

@[expose] def SqOdd {α : G} (hα : AlphaSpec S z t α) (x : G) : Prop :=
  ∃ w, IsLift h hα α x w ∧ (w * w = t ∨ w * w = α * t)

theorem sqEven_conj {α : G} (hα : AlphaSpec S z t α) {x b : G} (hx : x ∈ E)
    (hb : b ∈ L ⊓ centralizer ({t} : Set G)) (hS : SqEven h hα x) :
    SqEven h hα (b * x * b⁻¹) := by
  obtain ⟨w, hw, hw2⟩ := hS
  refine ⟨b * w * b⁻¹, h.isLift_conj_W hα hb hx hw, ?_⟩
  rw [h.sq_conj_W hα hb hw.1]
  exact hw2

theorem sqOdd_conj {α : G} (hα : AlphaSpec S z t α) {x b : G} (hx : x ∈ E)
    (hb : b ∈ L ⊓ centralizer ({t} : Set G)) (hS : SqOdd h hα x) :
    SqOdd h hα (b * x * b⁻¹) := by
  obtain ⟨w, hw, hw2⟩ := hS
  refine ⟨b * w * b⁻¹, h.isLift_conj_W hα hb hx hw, ?_⟩
  rw [h.sq_conj_W hα hb hw.1]
  exact hw2

theorem sqEven_mul {α : G} (hα : AlphaSpec S z t α)
    (hc : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) (h1 : SqEven h hα x) (h2 : SqEven h hα y) :
    SqEven h hα (x * y) := by
  obtain ⟨w, hw, hw2⟩ := h1
  obtain ⟨w', hw', hw2'⟩ := h2
  have hmem := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw
  have hmem' := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw'
  refine ⟨w * w', h.isLift_mul hα hα.sq hx hy hw hw', ?_⟩
  rw [h.sq_mul_Qs hα hw.1 hw'.1]
  exact sqA_mul hα.sq (hc w hmem w' hmem') (sqA_mul hα.sq hw2 hw2')

theorem sqEven_of_odd_odd {α : G} (hα : AlphaSpec S z t α)
    (hc : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α)
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) (h1 : SqOdd h hα x) (h2 : SqOdd h hα y) :
    SqEven h hα (x * y) := by
  obtain ⟨w, hw, hw2⟩ := h1
  obtain ⟨w', hw', hw2'⟩ := h2
  have hmem := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw
  have hmem' := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw'
  refine ⟨w * w', h.isLift_mul hα hα.sq hx hy hw hw', ?_⟩
  rw [h.sq_mul_Qs hα hw.1 hw'.1]
  exact sqA_mul hα.sq (hc w hmem w' hmem')
    (sqB_mul_sqB hα.sq h.t_sq (h.t_comm_S α hα.mem) hw2 hw2')

theorem sqEven_inv {α : G} (hα : AlphaSpec S z t α) {x : G} (hx : x ∈ E)
    (h1 : SqEven h hα x) : SqEven h hα x⁻¹ := by
  obtain ⟨w, hw, hw2⟩ := h1
  refine ⟨w⁻¹, h.isLift_inv hα hα.sq hx hw, ?_⟩
  have : w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
  rw [this]
  exact sqA_inv hα.sq hw2

theorem exists_lift' (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α) {ζ₀ : G} (hζ₀ : ZInv hα ζ₀) {x : G} (hx : x ∈ E) :
    ∃ w, IsLift h hα ζ₀ x w := by
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  exact h.exists_isLift hM hα hζ₀ hE (hgen a (by simp)) (hgen b (by simp)) (hgen c (by simp))
    (hgen d (by simp)) hx

theorem exists_lift_of_mem_Wsub' (hF : EFacts611 E t) {α : G} (hα : AlphaSpec S z t α) {w : G}
    (hw : w ∈ Wsub h hα (zpowers α)) : ∃ x ∈ E, IsLift h hα α x w := by
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  exact h.exists_isLift_of_mem_Wsub hα (h.zinv_alpha hα) hE (hgen a (by simp))
    (hgen b (by simp)) (hgen c (by simp)) (hgen d (by simp)) hw

theorem sqEven_or_sqOdd (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α) {x : G} (hx : x ∈ E) : SqEven h hα x ∨ SqOdd h hα x := by
  obtain ⟨w, hw⟩ := h.exists_lift' hF hM hα (h.zinv_alpha hα) hx
  rcases h.QF_sq hα hw.1 with h1 | h1 | h1 | h1
  · exact Or.inl ⟨w, hw, Or.inl h1⟩
  · exact Or.inr ⟨w, hw, Or.inl h1⟩
  · exact Or.inl ⟨w, hw, Or.inr h1⟩
  · exact Or.inr ⟨w, hw, Or.inr h1⟩

theorem not_sqEven_sqOdd {α : G} (hα : AlphaSpec S z t α) {x : G} (h1 : SqEven h hα x)
    (h2 : SqOdd h hα x) : False := by
  obtain ⟨w, hw, hw2⟩ := h1
  obtain ⟨w', hw', hw2'⟩ := h2
  rw [h.sq_eq_of_isLift hα hw hw'] at hw2'
  exact sqA_sqB_false h.t_ne hα.ne_t (h.alpha_t_ne hα).1 (h.alpha_t_ne hα).2 hw2 hw2'

theorem E_anti {a b : G} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a) :
    a * b = t * (b * a) :=
  (h.E_comm a ha b hb).resolve_left hab

theorem exists_third_E2 {x y : G} (hx : x ∈ E2 E t) (hy : y ∈ E2 E t) :
    ∃ z' ∈ E2 E t, z' * x ≠ x * z' ∧ z' * y ≠ y * z' := by
  by_contra hcon
  push Not at hcon
  have hsub : E2 E t ⊆ ({x, x * t, y, y * t} : Set G) := by
    intro z' hz'
    by_cases hzx : z' * x = x * z'
    · rcases h.E2_comm_cases hx hz' hzx.symm with h1 | h1
      · simp [h1]
      · simp [h1]
    · have hzy := hcon z' hz' hzx
      rcases h.E2_comm_cases hy hz' hzy.symm with h1 | h1
      · simp [h1]
      · simp [h1]
  have h10 : (E2 E t).ncard = 10 := h.ef.card_two
  have hle : (E2 E t).ncard ≤ ({x, x * t, y, y * t} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have e1 := Set.ncard_insert_le x ({x * t, y, y * t} : Set G)
  have e2 := Set.ncard_insert_le (x * t) ({y, y * t} : Set G)
  have e3 := Set.ncard_insert_le y ({y * t} : Set G)
  have e4 : ({y * t} : Set G).ncard = 1 := Set.ncard_singleton _
  omega

theorem exists_triple : ∃ x ∈ E2 E t, ∃ y ∈ E2 E t, ∃ z' ∈ E2 E t,
    x * y ∈ E4 E t ∧ x * y * z' ∈ E4 E t := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_anticomm_E2
  obtain ⟨z', hz', hzx, hzy⟩ := h.exists_third_E2 hx hy
  refine ⟨x, hx, y, hy, z', hz', ?_, ?_⟩
  · have hxx : x * x = 1 := hx.2.1
    have hyy : y * y = 1 := hy.2.1
    have hxy' : x * y = t * (y * x) := h.E_anti hx.1 hy.1 hxy
    have htx : x * t = t * x := h.t_comm_E x hx.1
    have hyx : y * x = t * (x * y) := by
      calc y * x = (t * t) * (y * x) := by rw [h.t_sq, one_mul]
        _ = t * (t * (y * x)) := by rw [mul_assoc]
        _ = t * (x * y) := by rw [← hxy']
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (t * (x * y)) * y := by rw [hyx]
      _ = (x * t) * x * y * y := by group
      _ = (t * x) * x * y * y := by rw [htx]
      _ = t * (x * x) * (y * y) := by group
      _ = t := by rw [hxx, hyy, mul_one, mul_one]
  · have hxx : x * x = 1 := hx.2.1
    have hyy : y * y = 1 := hy.2.1
    have hzz : z' * z' = 1 := hz'.2.1
    have hxy' : x * y = t * (y * x) := h.E_anti hx.1 hy.1 hxy
    have htx : x * t = t * x := h.t_comm_E x hx.1
    have hty : y * t = t * y := h.t_comm_E y hy.1
    have hyx : y * x = t * (x * y) := by
      calc y * x = (t * t) * (y * x) := by rw [h.t_sq, one_mul]
        _ = t * (t * (y * x)) := by rw [mul_assoc]
        _ = t * (x * y) := by rw [← hxy']
    have hz'x : z' * x = t * (x * z') := h.E_anti hz'.1 hx.1 hzx
    have hz'y : z' * y = t * (y * z') := h.E_anti hz'.1 hy.1 hzy
    have hxyxy : (x * y) * (x * y) = t := by
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (t * (x * y)) * y := by rw [hyx]
        _ = (x * t) * x * y * y := by group
        _ = (t * x) * x * y * y := by rw [htx]
        _ = t * (x * x) * (y * y) := by group
        _ = t := by rw [hxx, hyy, mul_one, mul_one]
    have hcomm : z' * (x * y) = (x * y) * z' := by
      calc z' * (x * y) = (z' * x) * y := by group
        _ = (t * (x * z')) * y := by rw [hz'x]
        _ = t * x * (z' * y) := by group
        _ = t * x * (t * (y * z')) := by rw [hz'y]
        _ = t * (x * t) * (y * z') := by group
        _ = t * (t * x) * (y * z') := by rw [htx]
        _ = (t * t) * x * (y * z') := by group
        _ = (x * y) * z' := by rw [h.t_sq, one_mul]; group
    refine ⟨mul_mem (mul_mem hx.1 hy.1) hz'.1, ?_⟩
    calc (x * y * z') * (x * y * z') = (x * y) * (z' * (x * y)) * z' := by group
      _ = (x * y) * ((x * y) * z') * z' := by rw [hcomm]
      _ = ((x * y) * (x * y)) * (z' * z') := by group
      _ = t := by rw [hxyxy, hzz, mul_one]

theorem sqOdd_E2 {α : G} (hα : AlphaSpec S z t α) {x y : G} (hx : x ∈ E2 E t)
    (hy : y ∈ E2 E t) (h1 : SqOdd h hα x) : SqOdd h hα y := by
  obtain ⟨b, hb, hbxy⟩ := h.W_orbit_two hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hy.1 hy.2.1 hy.2.2.1
    hy.2.2.2
  have := h.sqOdd_conj hα hx.1 hb h1
  rwa [hbxy] at this

theorem sqEven_E4 {α : G} (hα : AlphaSpec S z t α) {x y : G} (hx : x ∈ E4 E t)
    (h1 : SqEven h hα x) (hy : y ∈ E4 E t) : SqEven h hα y := by
  obtain ⟨b, hb, hbxy⟩ := h.W_orbit_four hx.1 hx.2 hy.1 hy.2
  have := h.sqEven_conj hα hx.1 hb h1
  rwa [hbxy] at this

theorem sqEven_E2 (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α)
    (hc : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α) : ∀ e ∈ E2 E t, SqEven h hα e := by
  obtain ⟨x, hx, y, hy, z', hz', hxy, hxyz⟩ := h.exists_triple
  refine orbit_parity (E := E) (E4 := E4 E t) (P0 := SqEven h hα) (P1 := SqOdd h hα) h.E2_sub
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy hz' hxy hxyz
  · intro e he
    exact h.sqEven_or_sqOdd hF hM hα he.1
  · intro e _ h0 h1
    exact h.not_sqEven_sqOdd hα h0 h1
  · intro a ha b hb h1
    exact h.sqOdd_E2 hα ha hb h1
  · intro a ha b hb h1
    exact h.sqEven_E4 hα ha h1 hb
  · intro a ha b hb h1 h2
    exact h.sqEven_of_odd_odd hα hc ha hb h1 h2
  · intro a ha b hb h1 h2
    exact h.sqEven_mul hα hc ha hb h1 h2
  · intro a ha h1
    exact h.sqEven_inv hα ha h1

theorem sqEven_all (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α)
    (hc : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α) : ∀ x ∈ E, SqEven h hα x := by
  have hE2 := h.sqEven_E2 hF hM hα hc
  intro x hx
  rcases h.ef.sq x hx with h1 | h1
  · by_cases hx1 : x = 1
    · rw [hx1]
      exact ⟨1, h.isLift_of_mem_Zg hα α (one_mem _), Or.inl (mul_one 1)⟩
    by_cases hxt : x = t
    · obtain ⟨w, hw⟩ := h.exists_lift' hF hM hα (h.zinv_alpha hα) hx
      rw [hxt] at hw
      have hw1 : IsLift h hα α 1 w := h.isLift_of_mul_t hα (one_mem _) (by rw [one_mul]; exact hw)
      have hwZ := h.mem_Zg_of_isLift_one hα hw1
      rw [hxt]
      exact ⟨w, hw, Or.inl (h.Zg_sq hα hwZ)⟩
    · exact hE2 x ⟨hx, h1, hx1, hxt⟩
  · obtain ⟨a, ha, b, hb, c, hc', hab, habc⟩ := h.exists_triple
    have hab' : SqEven h hα (a * b) :=
      h.sqEven_mul hα hc ha.1 hb.1 (hE2 a ha) (hE2 b hb)
    exact h.sqEven_E4 hα hab hab' ⟨hx, h1⟩

theorem sq_W1 (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α)
    (hcl : Lemma611Cl E B z t α (Fsub h hα) (Wsub h hα (zpowers α))
      (Wsub h hα (zpowers (α * t)))) :
    ∀ w ∈ Wsub h hα (zpowers α), w * w = 1 ∨ w * w = α := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := hcl
  intro w hw
  obtain ⟨x, hx, hwx⟩ := h.exists_lift_of_mem_Wsub' hF hα hw
  obtain ⟨w₀, hw₀, hw₀2⟩ := h.sqEven_all hF hM hα hc x hx
  rw [h.sq_eq_of_isLift hα hw₀ hwx]
  exact hw₀2

theorem sq_W2 (hF : EFacts611 E t) (hM : OuterMFacts E S z t) {α : G}
    (hα : AlphaSpec S z t α)
    (hcl : Lemma611Cl E B z t α (Fsub h hα) (Wsub h hα (zpowers α))
      (Wsub h hα (zpowers (α * t)))) :
    ∀ w ∈ Wsub h hα (zpowers (α * t)), w * w = 1 ∨ w * w = α * t := by
  intro w hw
  have hsq := h.sq_W1 hF hM hα hcl _ (h.conj_z_W2 hα hw)
  have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
  have hz' : z⁻¹ * α * z = α * t := by
    have : z⁻¹ * α * z = z * α * z⁻¹ := by rw [hzz]
    rw [this, h.z_conj_alpha hα]
  have e : (z * w * z⁻¹) * (z * w * z⁻¹) = z * (w * w) * z⁻¹ := by group
  rw [e] at hsq
  have hw2 : w * w = z⁻¹ * (z * (w * w) * z⁻¹) * z := by group
  rcases hsq with h1 | h1
  · left
    rw [hw2, h1]
    group
  · right
    rw [hw2, h1]
    exact hz'

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
