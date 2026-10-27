module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbStruct

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {m : ℕ}

theorem cbtSwap_comm {α : Type*} [DecidableEq α] {a b c d : α} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  ext x
  simp only [Perm.mul_apply]
  by_cases h1 : x = a
  · rw [h1, swap_apply_of_ne_of_ne hac had, swap_apply_left, swap_apply_of_ne_of_ne hbc hbd]
  by_cases h2 : x = b
  · rw [h2, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right, swap_apply_of_ne_of_ne hac had]
  by_cases h3 : x = c
  · rw [h3, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc),
      swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd), swap_apply_left]
  by_cases h4 : x = d
  · rw [h4, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd),
      swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc), swap_apply_right]
  simp only [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h3 h4]

@[expose] def cbtN (g : MulAut V) (v : V) : V := g v * v⁻¹

theorem cbtN_mul (g : MulAut V) (u v : V) : cbtN g (u * v) = cbtN g u * cbtN g v := by
  unfold cbtN
  rw [map_mul, mul_inv]
  ac_rfl

theorem cbtN_one (g : MulAut V) : cbtN g 1 = 1 := by simp [cbtN]

theorem cbtN_inv (g : MulAut V) (v : V) : cbtN g v⁻¹ = (cbtN g v)⁻¹ := by
  unfold cbtN
  rw [map_inv, mul_inv, inv_inv, mul_comm]

theorem cbtFix_commV {g : MulAut V} (hV : ∀ v : V, v ^ 2 = 1) (hg : g * g = 1) {u : V}
    (hu : u ∈ commV (Subgroup.zpowers g)) : g u = u := by
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hgg : ∀ z : V, g (g z) = z := fun z => by
      have := congrArg (fun f : MulAut V => f z) hg
      simpa [MulAut.mul_apply] using this
    rcases Int.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
    · have h1 : g ^ k = 1 := by
        rw [hn, ← two_mul, zpow_mul, zpow_two, hg, one_zpow]
      rw [h1]
      simp
    · have h1 : g ^ k = g := by
        rw [hn, zpow_add_one, zpow_mul, zpow_two, hg, one_zpow, one_mul]
      rw [h1, map_mul, hgg, map_inv, hinv (g v), hinv v]
      exact mul_comm _ _
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, ha]

namespace CbtY

@[expose] noncomputable def conjY (C : CbtY Y m) (τ : Equiv.Perm (Fin m)) (y : ↥Y) : ↥Y :=
  C.θ.symm ⟨τ * (C.θ y : Equiv.Perm (Fin m)) * τ⁻¹, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv,
      Equiv.Perm.mem_alternatingGroup.mp (C.θ y).2, mul_one, mul_inv_cancel]⟩

theorem conjY_theta (C : CbtY Y m) (τ : Equiv.Perm (Fin m)) (y : ↥Y) :
    (C.θ (C.conjY τ y) : Equiv.Perm (Fin m)) = τ * (C.θ y : Equiv.Perm (Fin m)) * τ⁻¹ := by
  unfold conjY
  rw [C.θ.apply_symm_apply]

theorem conjY_conjY (C : CbtY Y m) {τ : Equiv.Perm (Fin m)} (hτ : τ * τ = 1) (y : ↥Y) :
    C.conjY τ (C.conjY τ y) = y := by
  apply C.θ.injective
  apply Subtype.ext
  have hi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  rw [C.conjY_theta, C.conjY_theta, hi]
  calc τ * (τ * (C.θ y : Equiv.Perm (Fin m)) * τ) * τ
      = (τ * τ) * (C.θ y : Equiv.Perm (Fin m)) * (τ * τ) := by group
    _ = (C.θ y : Equiv.Perm (Fin m)) := by rw [hτ]; group

end CbtY

namespace CbtLift

variable {C : CbtY Y m} {t : MulAut V} {X : Subgroup (MulAut V)} (L : CbtLift C t X)

@[expose] def pairPerm {x y : Fin m} (hxy : x ≠ y) : alternatingGroup (Fin (m + 2)) :=
  ⟨swap (L.j x) (L.j y) * swap L.D.a L.D.b, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (fun h => hxy (L.hjinj h)),
      Equiv.Perm.sign_swap L.D.hab]
    decide⟩

@[expose] noncomputable def pairElt {x y : Fin m} (hxy : x ≠ y) : ↥X := L.D.θ.symm (L.pairPerm hxy)

variable {x y : Fin m} (hxy : x ≠ y)

theorem pairElt_theta : L.D.θ (L.pairElt hxy) = L.pairPerm hxy := L.D.θ.apply_symm_apply _

theorem swap_comm_ab (x y : Fin m) :
    swap (L.j x) (L.j y) * swap L.D.a L.D.b = swap L.D.a L.D.b * swap (L.j x) (L.j y) :=
  cbtSwap_comm (L.hja x) (L.hjb x) (L.hja y) (L.hjb y)

theorem pairPerm_sq :
    (swap (L.j x) (L.j y) * swap L.D.a L.D.b) * (swap (L.j x) (L.j y) * swap L.D.a L.D.b) = 1 := by
  calc (swap (L.j x) (L.j y) * swap L.D.a L.D.b) * (swap (L.j x) (L.j y) * swap L.D.a L.D.b)
      = swap (L.j x) (L.j y) * (swap L.D.a L.D.b * swap (L.j x) (L.j y)) * swap L.D.a L.D.b := by
        group
    _ = swap (L.j x) (L.j y) * (swap (L.j x) (L.j y) * swap L.D.a L.D.b) * swap L.D.a L.D.b := by
        rw [L.swap_comm_ab x y]
    _ = 1 := by
        rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]

theorem pairElt_w (p : Fin (m + 2)) :
    (L.pairElt hxy : MulAut V) (L.D.w p) =
      L.D.w ((swap (L.j x) (L.j y) * swap L.D.a L.D.b) p) := by
  have h := L.D.hwact (L.pairElt hxy : MulAut V) (L.pairElt hxy).2 p
  rw [h]
  have h2 : L.D.θ ⟨(L.pairElt hxy : MulAut V), (L.pairElt hxy).2⟩ = L.pairPerm hxy :=
    L.pairElt_theta hxy
  rw [h2]
  rfl

theorem pairElt_comm_t : t * (L.pairElt hxy : MulAut V) = (L.pairElt hxy : MulAut V) * t := by
  have h1 := L.D.hconj (L.pairElt hxy : MulAut V) (L.pairElt hxy).2
  have h2 : L.D.θ ⟨(L.pairElt hxy : MulAut V), (L.pairElt hxy).2⟩ = L.pairPerm hxy :=
    L.pairElt_theta hxy
  rw [h2] at h1
  have h3 : (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) =
      swap L.D.a L.D.b * (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) * (swap L.D.a L.D.b)⁻¹ := by
    show swap (L.j x) (L.j y) * swap L.D.a L.D.b =
      swap L.D.a L.D.b * (swap (L.j x) (L.j y) * swap L.D.a L.D.b) * (swap L.D.a L.D.b)⁻¹
    rw [swap_inv]
    calc swap (L.j x) (L.j y) * swap L.D.a L.D.b
        = (swap L.D.a L.D.b * swap (L.j x) (L.j y)) * (swap L.D.a L.D.b * swap L.D.a L.D.b) := by
          rw [swap_mul_self, mul_one, ← L.swap_comm_ab x y]
      _ = swap L.D.a L.D.b * (swap (L.j x) (L.j y) * swap L.D.a L.D.b) * swap L.D.a L.D.b := by
          group
  have h4 : (⟨t * (L.pairElt hxy : MulAut V) * t⁻¹, L.D.hn _ (L.pairElt hxy).2⟩ : ↥X) =
      L.pairElt hxy := by
    apply L.D.θ.injective
    apply Subtype.ext
    rw [h1, L.pairElt_theta hxy]
    exact h3.symm
  have h5 := congrArg Subtype.val h4
  have h6 : t * (L.pairElt hxy : MulAut V) * t⁻¹ = (L.pairElt hxy : MulAut V) := h5
  calc t * (L.pairElt hxy : MulAut V) = t * (L.pairElt hxy : MulAut V) * t⁻¹ * t := by group
    _ = (L.pairElt hxy : MulAut V) * t := by rw [h6]

@[expose] noncomputable def sElt (t' : MulAut V) {x y : Fin m} (hxy : x ≠ y) : MulAut V :=
  (L.pairElt hxy : MulAut V) * t'

theorem sElt_w (p : Fin (m + 2)) : L.sElt t hxy (L.D.w p) = L.D.w (swap (L.j x) (L.j y) p) := by
  unfold sElt
  rw [MulAut.mul_apply, L.D.htw p, L.pairElt_w hxy, Equiv.Perm.mul_apply, swap_apply_self]

theorem sElt_fix [Finite V] {f : V} (hf : f ∈ fixV X) : L.sElt t hxy f = t f := by
  unfold sElt
  rw [MulAut.mul_apply]
  exact mem_fixV.mp (CbData.fixV_invariant L.D.hn hf) _ (L.pairElt hxy).2

theorem perm_ext {π π' : Equiv.Perm (Fin (m + 2))} (ha : π L.D.a = π' L.D.a)
    (hb : π L.D.b = π' L.D.b) (hj : ∀ p, π (L.j p) = π' (L.j p)) : π = π' := by
  refine Equiv.ext fun q => ?_
  by_cases hqa : q = L.D.a
  · rw [hqa]; exact ha
  by_cases hqb : q = L.D.b
  · rw [hqb]; exact hb
  obtain ⟨p, rfl⟩ := L.hjsurj q hqa hqb
  exact hj p

theorem pairPerm_j (p : Fin m) :
    (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) (L.j p) = L.j (swap x y p) := by
  show (swap (L.j x) (L.j y) * swap L.D.a L.D.b) (L.j p) = _
  rw [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne (L.hja p) (L.hjb p), L.hjinj.swap_apply]

theorem pairPerm_a : (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) L.D.a = L.D.b := by
  show (swap (L.j x) (L.j y) * swap L.D.a L.D.b) L.D.a = _
  rw [Equiv.Perm.mul_apply, swap_apply_left,
    swap_apply_of_ne_of_ne (Ne.symm (L.hjb x)) (Ne.symm (L.hjb y))]

theorem pairPerm_b : (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) L.D.b = L.D.a := by
  show (swap (L.j x) (L.j y) * swap L.D.a L.D.b) L.D.b = _
  rw [Equiv.Perm.mul_apply, swap_apply_right,
    swap_apply_of_ne_of_ne (Ne.symm (L.hja x)) (Ne.symm (L.hja y))]

theorem pairPerm_inv : (L.pairPerm hxy : Equiv.Perm (Fin (m + 2)))⁻¹ =
    (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) :=
  inv_eq_of_mul_eq_one_right (L.pairPerm_sq (x := x) (y := y))

theorem sElt_conj (htY : ∀ y ∈ Y, t * y = y * t) {y₀ : MulAut V} (hy₀ : y₀ ∈ Y) :
    L.sElt t hxy * y₀ * (L.sElt t hxy)⁻¹ = (C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V) := by
  have h1 : L.sElt t hxy * y₀ * (L.sElt t hxy)⁻¹ =
      (L.pairElt hxy : MulAut V) * y₀ * (L.pairElt hxy : MulAut V)⁻¹ := by
    unfold sElt
    have := htY y₀ hy₀
    calc (L.pairElt hxy : MulAut V) * t * y₀ * ((L.pairElt hxy : MulAut V) * t)⁻¹
        = (L.pairElt hxy : MulAut V) * (t * y₀ * t⁻¹) * (L.pairElt hxy : MulAut V)⁻¹ := by group
      _ = (L.pairElt hxy : MulAut V) * y₀ * (L.pairElt hxy : MulAut V)⁻¹ := by
          rw [this]; group
  rw [h1]
  let E : ↥X := L.pairElt hxy
  let Y₀ : ↥X := ⟨y₀, L.hYX hy₀⟩
  let Z : ↥X := ⟨(C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V), L.hYX (C.conjY _ _).2⟩
  have h2 : E * Y₀ * E⁻¹ = Z := by
    apply L.D.θ.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have hE : (L.D.θ E : Equiv.Perm (Fin (m + 2))) = (L.pairPerm hxy : Equiv.Perm (Fin (m + 2))) :=
      congrArg Subtype.val (L.pairElt_theta hxy)
    have hEi : (L.D.θ E : Equiv.Perm (Fin (m + 2)))⁻¹ = (L.D.θ E : Equiv.Perm (Fin (m + 2))) := by
      rw [hE]
      exact L.pairPerm_inv hxy
    rw [hEi]
    have hzY : (⟨(C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V), L.hYX (C.conjY _ _).2⟩ : ↥X) = Z := rfl
    have hfa : (L.D.θ Y₀ : Equiv.Perm (Fin (m + 2))) L.D.a = L.D.a := (L.fix_ab y₀ hy₀).1
    have hfb : (L.D.θ Y₀ : Equiv.Perm (Fin (m + 2))) L.D.b = L.D.b := (L.fix_ab y₀ hy₀).2
    have hza : (L.D.θ Z : Equiv.Perm (Fin (m + 2))) L.D.a = L.D.a :=
      (L.fix_ab (C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V) (C.conjY _ _).2).1
    have hzb : (L.D.θ Z : Equiv.Perm (Fin (m + 2))) L.D.b = L.D.b :=
      (L.fix_ab (C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V) (C.conjY _ _).2).2
    have hYj : ∀ q, (L.D.θ Y₀ : Equiv.Perm (Fin (m + 2))) (L.j q) =
        L.j ((C.θ ⟨y₀, hy₀⟩ : Equiv.Perm (Fin m)) q) := fun q => L.hjθ y₀ hy₀ q
    have hZj : ∀ q, (L.D.θ Z : Equiv.Perm (Fin (m + 2))) (L.j q) =
        L.j ((swap x y * (C.θ ⟨y₀, hy₀⟩ : Equiv.Perm (Fin m)) * (swap x y)⁻¹) q) := by
      intro q
      have h7 := L.hjθ (C.conjY (swap x y) ⟨y₀, hy₀⟩ : MulAut V) (C.conjY _ _).2 q
      rw [C.conjY_theta] at h7
      exact h7
    apply L.perm_ext
    · show (L.D.θ E : Equiv.Perm (Fin (m + 2))) ((L.D.θ Y₀ : Equiv.Perm (Fin (m + 2)))
        ((L.D.θ E : Equiv.Perm (Fin (m + 2))) L.D.a)) = (L.D.θ Z : Equiv.Perm (Fin (m + 2))) L.D.a
      rw [hE, L.pairPerm_a hxy, hfb, L.pairPerm_b hxy, hza]
    · show (L.D.θ E : Equiv.Perm (Fin (m + 2))) ((L.D.θ Y₀ : Equiv.Perm (Fin (m + 2)))
        ((L.D.θ E : Equiv.Perm (Fin (m + 2))) L.D.b)) = (L.D.θ Z : Equiv.Perm (Fin (m + 2))) L.D.b
      rw [hE, L.pairPerm_b hxy, hfa, L.pairPerm_a hxy, hzb]
    · intro p
      show (L.D.θ E : Equiv.Perm (Fin (m + 2))) ((L.D.θ Y₀ : Equiv.Perm (Fin (m + 2)))
        ((L.D.θ E : Equiv.Perm (Fin (m + 2))) (L.j p))) =
          (L.D.θ Z : Equiv.Perm (Fin (m + 2))) (L.j p)
      rw [hE, L.pairPerm_j hxy, hYj, L.pairPerm_j hxy, hZj, swap_inv]
      rfl
  have h3 := congrArg Subtype.val h2
  exact h3

theorem pair_vec [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (x y : Fin m) :
    L.D.w (L.j x) * L.D.w (L.j y) = C.w x * C.w y := by
  rw [← L.eps_eq hV hm hodd x, ← L.eps_eq hV hm hodd y]
  unfold eps
  have hv : (L.D.w L.D.a * L.D.w L.D.b) * (L.D.w L.D.a * L.D.w L.D.b) = 1 := by
    rw [mul_mul_mul_comm, L.D.w_sq hV, L.D.w_sq hV, mul_one]
  rw [mul_mul_mul_comm, hv, mul_one]

theorem sElt_eps [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) :
    L.sElt t hxy (C.w x * C.w y) = C.w x * C.w y := by
  rw [← L.pair_vec hV hm hodd x y, map_mul, L.sElt_w hxy, L.sElt_w hxy, swap_apply_left,
    swap_apply_right, mul_comm]

theorem sElt_commV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m)
    (ht2 : t * t = 1) {u : V} (hu : u ∈ commV (Subgroup.zpowers t)) : L.sElt t hxy u = u := by
  have h1 := (L.D.commV_zpowers hV hm hodd (by rw [sq]; exact ht2)).1
  rw [h1] at hu
  obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup.mp hu
  have hv : L.sElt t hxy (L.D.w L.D.a * L.D.w L.D.b) = L.D.w L.D.a * L.D.w L.D.b := by
    rw [map_mul, L.sElt_w hxy, L.sElt_w hxy,
      swap_apply_of_ne_of_ne (Ne.symm (L.hja x)) (Ne.symm (L.hja y)),
      swap_apply_of_ne_of_ne (Ne.symm (L.hjb x)) (Ne.symm (L.hjb y))]
  have ha' : L.sElt t hxy a = a := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [map_zpow, hv]
  have hf' : L.sElt t hxy f = f := by
    rw [L.sElt_fix hxy hf.2]
    exact cbtFix_commV hV ht2 hf.1
  rw [map_mul, ha', hf']

theorem sElt_fix_U [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m)
    (ht2 : t * t = 1) {u : V}
    (hu : u ∈ Subgroup.zpowers (C.w x * C.w y) ⊔ commV (Subgroup.zpowers t)) :
    L.sElt t hxy u = u := by
  obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup.mp hu
  have ha' : L.sElt t hxy a = a := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [map_zpow, L.sElt_eps hxy hV hm hodd]
  rw [map_mul, ha', L.sElt_commV hxy hV hm hodd ht2 hf]

theorem sElt_N_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) {w : V}
    (hw : w ∈ commV X) : cbtN (L.sElt t hxy) w ∈ Subgroup.zpowers (C.w x * C.w y) := by
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  rw [← L.D.hwspan] at hw
  induction hw using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨p, rfl⟩ := hu
    unfold cbtN
    rw [L.sElt_w hxy]
    by_cases hp1 : p = L.j x
    · rw [hp1, swap_apply_left, hinv, ← L.pair_vec hV hm hodd x y, mul_comm]
      exact Subgroup.mem_zpowers _
    by_cases hp2 : p = L.j y
    · rw [hp2, swap_apply_right, hinv, ← L.pair_vec hV hm hodd x y]
      exact Subgroup.mem_zpowers _
    rw [swap_apply_of_ne_of_ne hp1 hp2, mul_inv_cancel]
    exact one_mem _
  | one => rw [cbtN_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [cbtN_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [cbtN_inv]; exact inv_mem ha

include L in
theorem N_t_fix [Finite V] {f : V} (hf : f ∈ fixV X) :
    cbtN t f ∈ fixV X ⊓ commV (Subgroup.zpowers t) := by
  refine ⟨?_, ?_⟩
  · unfold cbtN
    exact Subgroup.mul_mem _ (CbData.fixV_invariant L.D.hn hf) (Subgroup.inv_mem _ hf)
  · unfold cbtN
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, f, rfl⟩

theorem sElt_N_mem [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (v : V) :
    cbtN (L.sElt t hxy) v ∈ Subgroup.zpowers (C.w x * C.w y) ⊔ commV (Subgroup.zpowers t) := by
  have hv : v ∈ commV X ⊔ fixV X := by
    rw [(L.D.split hm hodd).1]
    exact Subgroup.mem_top v
  obtain ⟨w, hw, f, hf, rfl⟩ := Subgroup.mem_sup.mp hv
  clear hv
  rw [cbtN_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.sElt_N_W hxy hV hm hodd hw))
    (Subgroup.mem_sup_right ?_)
  unfold cbtN
  rw [L.sElt_fix hxy hf]
  exact (L.N_t_fix hf).2

include L in
theorem exists_N_preimage [Finite V] (hm : 7 ≤ m) (hodd : Odd m) (ht2 : t * t = 1) {u : V}
    (hu : u ∈ fixV X ⊓ commV (Subgroup.zpowers t)) : ∃ f ∈ fixV X, cbtN t f = u := by
  have hsq : t ^ 2 = 1 := by rw [sq]; exact ht2
  have hrange : commV (Subgroup.zpowers t) ≤ (MonoidHom.mk' (cbtN t) (cbtN_mul t)).range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨z, hz, v, rfl⟩
    rcases cb_mem_zpowers_sq hsq hz with h | h
    · exact ⟨1, by simp [cbtN, h]⟩
    · exact ⟨v, by simp [cbtN, h]⟩
  obtain ⟨v, hv⟩ := hrange hu.2
  have hv' : cbtN t v = u := hv
  have hsplit : v ∈ commV X ⊔ fixV X := by
    rw [(L.D.split hm hodd).1]
    exact Subgroup.mem_top v
  obtain ⟨w, hw, f, hf, rfl⟩ := Subgroup.mem_sup.mp hsplit
  refine ⟨f, hf, ?_⟩
  rw [cbtN_mul] at hv'
  have h1 : cbtN t w ∈ commV X := by
    unfold cbtN
    exact Subgroup.mul_mem _ (cb_commV_invariant_of_normalizing L.D.hn hw) (Subgroup.inv_mem _ hw)
  have h2 : cbtN t w ∈ fixV X := by
    have : cbtN t w = u * (cbtN t f)⁻¹ := by rw [← hv']; group
    rw [this]
    exact Subgroup.mul_mem _ hu.1 (Subgroup.inv_mem _ (L.N_t_fix hf).1)
  have h3 : cbtN t w ∈ commV X ⊓ fixV X := ⟨h1, h2⟩
  rw [(L.D.split hm hodd).2, Subgroup.mem_bot] at h3
  rw [h3, one_mul] at hv'
  exact hv'

end CbtLift

namespace CbtCtx

variable [Finite V] {G T : Subgroup (MulAut V)} {t : MulAut V} {X₁ X₂ : Subgroup (MulAut V)}
  (K : CbtCtx G T Y t m X₁ X₂) {x y : Fin m} (hxy : x ≠ y)

include K

@[expose] noncomputable def d0 : MulAut V := K.L₁.sElt t hxy * K.L₂.sElt t hxy

theorem d0_apply (v : V) :
    K.d0 hxy v = v * cbtN (K.L₁.sElt t hxy) v * cbtN (K.L₂.sElt t hxy) v := by
  unfold d0
  rw [MulAut.mul_apply]
  have h2 : K.L₂.sElt t hxy v = cbtN (K.L₂.sElt t hxy) v * v := by unfold cbtN; group
  have hU2 := K.L₂.sElt_N_mem hxy K.hV K.hm K.hodd v
  have hfix1 := K.L₁.sElt_fix_U hxy K.hV K.hm K.hodd K.t_mul_self hU2
  rw [h2, map_mul, hfix1]
  have h1 : K.L₁.sElt t hxy v = cbtN (K.L₁.sElt t hxy) v * v := by unfold cbtN; group
  rw [h1]
  ac_rfl

theorem d0_fix_U {u : V}
    (hu : u ∈ Subgroup.zpowers (K.C.w x * K.C.w y) ⊔ commV (Subgroup.zpowers t)) :
    K.d0 hxy u = u := by
  unfold d0
  rw [MulAut.mul_apply, K.L₂.sElt_fix_U hxy K.hV K.hm K.hodd K.t_mul_self hu,
    K.L₁.sElt_fix_U hxy K.hV K.hm K.hodd K.t_mul_self hu]

theorem d0_sq : K.d0 hxy * K.d0 hxy = 1 := by
  ext v
  rw [MulAut.mul_apply, K.d0_apply hxy v, map_mul, map_mul,
    K.d0_fix_U hxy (K.L₁.sElt_N_mem hxy K.hV K.hm K.hodd v),
    K.d0_fix_U hxy (K.L₂.sElt_N_mem hxy K.hV K.hm K.hodd v), K.d0_apply hxy v]
  have h := K.hV (cbtN (K.L₁.sElt t hxy) v * cbtN (K.L₂.sElt t hxy) v)
  rw [sq] at h
  calc v * cbtN (K.L₁.sElt t hxy) v * cbtN (K.L₂.sElt t hxy) v * cbtN (K.L₁.sElt t hxy) v *
        cbtN (K.L₂.sElt t hxy) v
      = v * (cbtN (K.L₁.sElt t hxy) v * cbtN (K.L₂.sElt t hxy) v *
          (cbtN (K.L₁.sElt t hxy) v * cbtN (K.L₂.sElt t hxy) v)) := by ac_rfl
    _ = v := by rw [h, mul_one]
    _ = (1 : MulAut V) v := rfl

theorem d0_comm_t : t * K.d0 hxy = K.d0 hxy * t := by
  have h1 := K.L₁.pairElt_comm_t hxy
  have h2 := K.L₂.pairElt_comm_t hxy
  unfold d0 CbtLift.sElt
  calc t * ((K.L₁.pairElt hxy : MulAut V) * t * ((K.L₂.pairElt hxy : MulAut V) * t))
      = (t * (K.L₁.pairElt hxy : MulAut V)) * t * ((K.L₂.pairElt hxy : MulAut V) * t) := by
        group
    _ = (K.L₁.pairElt hxy : MulAut V) * t * (t * (K.L₂.pairElt hxy : MulAut V)) * t := by
        rw [h1]; group
    _ = (K.L₁.pairElt hxy : MulAut V) * t * ((K.L₂.pairElt hxy : MulAut V) * t) * t := by
        rw [h2]

theorem d0_comm_Y (z : MulAut V) (hz : z ∈ Y) : z * K.d0 hxy = K.d0 hxy * z := by
  have h1 := K.L₂.sElt_conj hxy (K.t_comm_Y) hz
  have h2 := K.L₁.sElt_conj hxy (K.t_comm_Y)
    (show (K.C.conjY (swap x y) ⟨z, hz⟩ : MulAut V) ∈ Y from (K.C.conjY _ _).2)
  have h3 : K.C.conjY (swap x y) (K.C.conjY (swap x y) ⟨z, hz⟩) = ⟨z, hz⟩ :=
    K.C.conjY_conjY (swap_mul_self x y) _
  rw [h3] at h2
  have h4 : K.d0 hxy * z * (K.d0 hxy)⁻¹ = z := by
    unfold d0
    calc K.L₁.sElt t hxy * K.L₂.sElt t hxy * z * (K.L₁.sElt t hxy * K.L₂.sElt t hxy)⁻¹
        = K.L₁.sElt t hxy * (K.L₂.sElt t hxy * z * (K.L₂.sElt t hxy)⁻¹) *
          (K.L₁.sElt t hxy)⁻¹ := by group
      _ = z := by rw [h1]; exact h2
  calc z * K.d0 hxy = K.d0 hxy * z * (K.d0 hxy)⁻¹ * K.d0 hxy := by rw [h4]
    _ = K.d0 hxy * z := by group

theorem d0_mem : K.d0 hxy ∈ G := by
  unfold d0 CbtLift.sElt
  exact G.mul_mem (G.mul_mem (K.h₁.le_G (K.L₁.pairElt hxy).2) K.htG)
    (G.mul_mem (K.h₂.le_G (K.L₂.pairElt hxy).2) K.htG)

theorem eps_pow_eq_one {k : ℤ}
    (hk : (K.C.w x * K.C.w y) ^ k ∈ commV (Subgroup.zpowers t)) :
    (K.C.w x * K.C.w y) ^ k = 1 := by
  have h1 : (K.C.w x * K.C.w y) ^ k ∈ commV Y :=
    Subgroup.zpow_mem _ (Subgroup.mul_mem _ (K.C.hmem x).1 (K.C.hmem y).1) k
  have h2 : (K.C.w x * K.C.w y) ^ k ∈ fixV Y :=
    cb_commV_zpowers_le_fixV K.hV K.hm K.hodd K.C.θ K.C.hnat K.ht2 K.t_comm_Y hk
  have h3 : (K.C.w x * K.C.w y) ^ k ∈ commV Y ⊓ fixV Y := ⟨h1, h2⟩
  rw [commV_inf_fixV_of_natural K.hodd (by have := K.hm; omega) K.C.θ K.C.hnat] at h3
  exact Subgroup.mem_bot.mp h3

theorem d0_ne_one : K.d0 hxy ≠ 1 := by
  intro h1
  obtain ⟨-, hP1, -, hdisj⟩ := EndCfg4.card_commV_of_two_lifts K.h2 K.h K.hV K.hm K.hodd K.hY
    K.htG K.htT K.ht2 K.ht1 K.h₁ K.h₂ K.hne
  have hP1ne : fixV X₁ ⊓ commV (Subgroup.zpowers t) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hP1
    omega
  obtain ⟨⟨u₁, hu₁⟩, hu₁ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hP1ne
  have hu₁1 : u₁ ≠ 1 := fun h => hu₁ne (Subtype.ext h)
  obtain ⟨f, hf, hNf⟩ := K.L₁.exists_N_preimage K.hm K.hodd K.t_mul_self hu₁
  have hN1 : cbtN (K.L₁.sElt t hxy) f = u₁ := by
    unfold cbtN
    rw [K.L₁.sElt_fix hxy hf]
    exact hNf
  have hsplit : f ∈ commV X₂ ⊔ fixV X₂ := by
    rw [(K.L₂.D.split K.hm K.hodd).1]
    exact Subgroup.mem_top f
  obtain ⟨w', hw', f', hf', hff⟩ := Subgroup.mem_sup.mp hsplit
  have hN2 : cbtN (K.L₂.sElt t hxy) f = cbtN (K.L₂.sElt t hxy) w' * cbtN t f' := by
    rw [← hff, cbtN_mul]
    congr 1
    unfold cbtN
    rw [K.L₂.sElt_fix hxy hf']
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (K.L₂.sElt_N_W hxy K.hV K.hm K.hodd hw')
  have hp := K.L₂.N_t_fix hf'
  have hd := K.d0_apply hxy f
  rw [h1, hN1, hN2, ← hk] at hd
  have hprod : u₁ * ((K.C.w x * K.C.w y) ^ k * cbtN t f') = 1 := by
    have h2 : (1 : MulAut V) f = f := rfl
    rw [h2] at hd
    have h3 : f * 1 = f * (u₁ * ((K.C.w x * K.C.w y) ^ k * cbtN t f')) := by
      rw [mul_one]
      calc f = f * u₁ * ((K.C.w x * K.C.w y) ^ k * cbtN t f') := hd
        _ = f * (u₁ * ((K.C.w x * K.C.w y) ^ k * cbtN t f')) := by rw [mul_assoc]
    exact (mul_left_cancel h3).symm
  have he : (K.C.w x * K.C.w y) ^ k = (u₁ * cbtN t f')⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hprod]
    ac_rfl
  have hec : (K.C.w x * K.C.w y) ^ k ∈ commV (Subgroup.zpowers t) := by
    rw [he]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hu₁.2 hp.2)
  have hk1 := K.eps_pow_eq_one (x := x) (y := y) hec
  rw [hk1] at he
  have hu₁p : cbtN t f' = u₁⁻¹ := by
    have h4 : u₁ * cbtN t f' = 1 := inv_eq_one.mp he.symm
    exact eq_inv_of_mul_eq_one_right h4
  have hu₁P₂ : u₁ ∈ fixV X₂ ⊓ commV (Subgroup.zpowers t) := by
    have : u₁ = (cbtN t f')⁻¹ := by rw [hu₁p, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ hp
  have h5 : u₁ ∈ (fixV X₁ ⊓ commV (Subgroup.zpowers t)) ⊓
      (fixV X₂ ⊓ commV (Subgroup.zpowers t)) := ⟨hu₁, hu₁P₂⟩
  rw [hdisj] at h5
  exact hu₁1 (Subgroup.mem_bot.mp h5)

end CbtCtx

end CFSG.CGT.PushingUpLit.CGT6
