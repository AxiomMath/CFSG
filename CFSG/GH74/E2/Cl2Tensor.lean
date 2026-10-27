module

public import CFSG.GH74.E2.Cl2CaseDefs
import CFSG.GH74.E2.Cl2E2

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

section Aux

variable {Q : Type*} [Group Q]

private theorem cT_cube {g : MulAut Q} (hg : g ^ 3 = 1) (x : Q) : g (g (g x)) = x := by
  have := congrArg (fun f : MulAut Q => f x) hg
  simpa [pow_succ, MulAut.mul_apply] using this

private theorem cT_eq_one_of_zpow_odd (hQ : IsPGroup 2 Q) {x : Q} {m : ℤ}
    (hm : Odd m) (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hQ x
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : (orderOf x : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  by_contra hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by rw [hj]; rfl))
  have h3 : (2 : ℤ) ∣ m := by
    refine dvd_trans ?_ h2
    rw [hj]
    rcases j with _ | j'
    · exact absurd rfl hj0
    · exact ⟨2 ^ j', by push_cast; ring⟩
  exact (Int.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)

private theorem cT_eq_one_of_eps (hQ : IsPGroup 2 Q) {g : MulAut Q} {u : Q} (hu : g u = u)
    (he : eps g u = 1) : u = 1 := by
  rw [eps, hu, hu] at he
  refine cT_eq_one_of_zpow_odd hQ (m := 3) ⟨1, by norm_num⟩ ?_
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_three']
  exact he

private theorem cT_KL [Finite Q] (hQ : IsPGroup 2 Q) {g : MulAut Q} (hg : g ^ 3 = 1)
    {H : Subgroup Q} (hH : ∀ x ∈ H, g x ∈ H) {f : Q → Q}
    (hmul : ∀ x ∈ H, ∀ y ∈ H, f (x * y) = f x * f y) (h1 : ∀ x ∈ H, f (g x) = f x)
    (h2 : ∀ x ∈ H, g x = x → f x = 1) : ∀ x ∈ H, f x = 1 := by
  have h3 : ∀ y, g (g (g y)) = y := cT_cube hg
  let ĝ : MulAut H :=
    { toFun := fun x => ⟨g x, hH x x.2⟩
      invFun := fun x => ⟨g (g x), hH _ (hH x x.2)⟩
      left_inv := fun x => Subtype.ext (h3 x)
      right_inv := fun x => Subtype.ext (h3 x)
      map_mul' := fun x y => Subtype.ext (map_mul g x.1 y.1) }
  have hĝ : ĝ ^ 3 = 1 := by
    ext x
    exact congrArg Subtype.val (show ĝ (ĝ (ĝ x)) = x from Subtype.ext (h3 x))
  let φ : H →* Q := MonoidHom.mk' (fun x => f x) (fun x y => hmul x x.2 y y.2)
  have hK : ∀ x : H, ĝ x ∈ φ.ker ↔ x ∈ φ.ker := fun x => by
    simp only [MonoidHom.mem_ker]
    show f (g x) = 1 ↔ f x = 1
    rw [h1 x x.2]
  intro x hx
  have hx' : (⟨x, hx⟩ : H)⁻¹ * ĝ ⟨x, hx⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show (f x)⁻¹ * f (g x) = 1
    rw [h1 x hx, inv_mul_cancel]
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem (hQ.to_subgroup H) hĝ hK hx'
  have hgxn : g (x * n) = x * n := congrArg Subtype.val hfix
  have hxn : f (x * n) = 1 := h2 _ (H.mul_mem hx n.2) hgxn
  have hfn : f n = 1 := MonoidHom.mem_ker.mp hn
  rw [hmul x hx n n.2, hfn, mul_one] at hxn
  exact hxn

end Aux

section Bilin

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

private theorem cT_mul_right {u k k' : Q} (h : ⁅u, k'⁆ ∈ center Q) :
    ⁅u, k * k'⁆ = ⁅u, k⁆ * ⁅u, k'⁆ := by
  have hc : k * ⁅u, k'⁆ = ⁅u, k'⁆ * k := Subgroup.mem_center_iff.1 h k
  calc ⁅u, k * k'⁆ = ⁅u, k⁆ * (k * ⁅u, k'⁆ * k⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅u, k⁆ * ⁅u, k'⁆ := by rw [hc]; group

private theorem cT_mul_left {u v k : Q} (h : ⁅v, k⁆ ∈ center Q) :
    ⁅u * v, k⁆ = ⁅v, k⁆ * ⁅u, k⁆ := by
  have hc : u * ⁅v, k⁆ = ⁅v, k⁆ * u := Subgroup.mem_center_iff.1 h u
  calc ⁅u * v, k⁆ = (u * ⁅v, k⁆ * u⁻¹) * ⁅u, k⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅v, k⁆ * ⁅u, k⁆ := by rw [hc]; group

private theorem cT_mulz (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (z z' : Q) : ⁅u, z * z'⁆ = ⁅u, z⁆ * ⁅u, z'⁆ :=
  cT_mul_right (h.N_central (h.comm_mem hQ hu z'))

private theorem cT_mulu (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u u' : Q} (hu' : u' ∈ dsub Q)
    (z : Q) : ⁅u * u', z⁆ = ⁅u, z⁆ * ⁅u', z⁆ := by
  have hc : ⁅u', z⁆ ∈ center Q := h.N_central (h.comm_mem hQ hu' z)
  rw [cT_mul_left hc]
  exact (Subgroup.mem_center_iff.1 hc ⁅u, z⁆).symm

private theorem cT_abInv (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) : AbInv2 a b (dsub Q) :=
  ⟨h.dsub_comm hQ, h.dsub_inva, h.dsub_invb⟩

private theorem cT_ab (h : Cl3 Q a b N) (z : Q) : a (b z) = b (a z) := by
  have := congrArg (fun f : MulAut Q => f z) h.bpair.comm
  simpa [MulAut.mul_apply] using this

section Fin

variable [Finite Q]

private theorem cT_false (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N)
    (H : ∀ u ∈ dsub Q, ∀ z : Q, (a z = z ∨ b z = z) → ⁅u, z⁆ = 1) : False := by
  have htop : fixSub a ⊔ fixSub b = ⊤ := h.bpair.sup_fix hQ h.four
  have hall : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ = 1 := by
    intro u hu z
    let φ : Q →* Q := MonoidHom.mk' (fun z => ⁅u, z⁆) (cT_mulz hQ h hu)
    have hle : fixSub a ⊔ fixSub b ≤ φ.ker :=
      sup_le (fun y hy => MonoidHom.mem_ker.mpr (H u hu y (Or.inl hy)))
        (fun y hy => MonoidHom.mem_ker.mpr (H u hu y (Or.inr hy)))
    rw [htop] at hle
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top z))
  have hN : N = ⊥ := by
    rw [h.N_eq, eq_bot_iff, Subgroup.commutator_le]
    intro u hu k _
    rw [Subgroup.mem_bot]
    exact hall u hu k
  exact h.N_ne hN

private theorem cT_fixB_comm (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    {x : Q} (hxa : a x = x) (hxb : b x = x) : ⁅u, x⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 (h.dsub_comm hQ u hu x (h.fixB_le_dsub hQ ⟨hxa, hxb⟩))

private theorem cT_klQ1 (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (h1 : ∀ y : Q, b y = y → ⁅u, a y⁆ = ⁅u, y⁆) {z : Q} (hz : b z = z) : ⁅u, z⁆ = 1 :=
  cT_KL hQ h.bpair.a_cube (H := fixSub b)
    (fun x hx => show b (a x) = a x by rw [← cT_ab h, show b x = x from hx])
    (f := fun x => ⁅u, x⁆) (fun x _ y _ => cT_mulz hQ h hu x y)
    (fun x hx => h1 x hx) (fun x hx hax => cT_fixB_comm hQ h hu hax hx) z hz

private theorem cT_klQ2 (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (h1 : ∀ y : Q, a y = y → ⁅u, b y⁆ = ⁅u, y⁆) {z : Q} (hz : a z = z) : ⁅u, z⁆ = 1 :=
  cT_KL hQ h.bpair.b_cube (H := fixSub a)
    (fun x hx => show a (b x) = b x by rw [cT_ab h, show a x = x from hx])
    (f := fun x => ⁅u, x⁆) (fun x _ y _ => cT_mulz hQ h hu x y)
    (fun x hx => h1 x hx) (fun x hx hbx => cT_fixB_comm hQ h hu hx hbx) z hz

private theorem cT_klW (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {g : MulAut Q} (hg : g ^ 3 = 1)
    {W : Subgroup Q} (hWD : W ≤ dsub Q) (hW : ∀ x ∈ W, g x ∈ W)
    (hfix : ∀ x ∈ W, g x = x → x = 1) {z : Q} (h1 : ∀ x ∈ W, ⁅g x, z⁆ = ⁅x, z⁆) :
    ∀ x ∈ W, ⁅x, z⁆ = 1 :=
  cT_KL hQ hg hW (f := fun x => ⁅x, z⁆) (fun x _ y hy => cT_mulu hQ h (hWD hy) z)
    h1 (fun x hx hgx => by rw [hfix x hx hgx, commutatorElement_one_left])

private theorem cT_reduce (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hA : AbInv2 a b (dsub Q))
    {z : Q} (h0 : ∀ u ∈ wsub a b (dsub Q) hA .w0, ⁅u, z⁆ = 1)
    (hp : ∀ u ∈ wsub a b (dsub Q) hA .wp, ⁅u, z⁆ = 1)
    (hm : ∀ u ∈ wsub a b (dsub Q) hA .wm, ⁅u, z⁆ = 1)
    (ha : ∀ u ∈ wsub a b (dsub Q) hA .wa, u = 1)
    (hb : ∀ u ∈ wsub a b (dsub Q) hA .wb, u = 1) : ∀ u ∈ dsub Q, ⁅u, z⁆ = 1 := by
  intro u hu
  obtain ⟨x0, hx0, xa, hxa, xb, hxb, xp, hxp, xm, hxm, rfl⟩ :=
    wsub_decomp hQ h.bpair.a_cube h.bpair.b_cube h.bpair.comm hA hu
  rw [ha xa hxa, hb xb hxb, mul_one, mul_one, cT_mulu hQ h (wsub_le hA .wm hxm) z,
    cT_mulu hQ h (wsub_le hA .wp hxp) z, h0 x0 hx0, hp xp hxp, hm xm hxm, mul_one, mul_one]

private theorem cT_nff_core (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hA : AbInv2 a b (dsub Q))
    (hNfix : ∀ m ∈ N, a m = m ∧ b m = m)
    (ha : ∀ u ∈ wsub a b (dsub Q) hA .wa, u = 1) (hb : ∀ u ∈ wsub a b (dsub Q) hA .wb, u = 1) :
    False := by
  have hinv : ∀ (w : Wt) {x : Q}, x ∈ wsub a b (dsub Q) hA w →
      a x ∈ wsub a b (dsub Q) hA w ∧ b x ∈ wsub a b (dsub Q) hA w := fun w {x} hx =>
    wsub_inv hQ h.bpair.a_cube h.bpair.b_cube h.bpair.comm hA w hx
  have hcN : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N := fun u hu z => h.comm_mem hQ hu z
  refine cT_false hQ h fun u hu z hz => ?_
  rcases hz with hz | hz
  ·
    refine cT_reduce hQ h hA ?_ ?_ ?_ ha hb u hu
    · intro v hv
      obtain ⟨hvD, hav, hbv⟩ := (mem_wsub_w0 hA).1 hv
      refine cT_klQ2 hQ h hvD ?_ hz
      intro y _
      have e := (hNfix _ (hcN v hvD y)).2
      rwa [map_commutatorElement, hbv] at e
    · intro v hv
      refine cT_klW hQ h h.bpair.a_cube (wsub_le hA .wp) (fun x hx => (hinv .wp hx).1) ?_ ?_ v hv
      · intro x hx hax
        exact cT_eq_one_of_eps hQ hax ((mem_wsub_wp hA).1 hx).2.2
      · intro x hx
        have e := (hNfix _ (hcN x (wsub_le hA .wp hx) z)).1
        rwa [map_commutatorElement, hz] at e
    · intro v hv
      refine cT_klW hQ h h.bpair.a_cube (wsub_le hA .wm) (fun x hx => (hinv .wm hx).1) ?_ ?_ v hv
      · intro x hx hax
        exact cT_eq_one_of_eps hQ hax ((mem_wsub_wm hA).1 hx).2.2
      · intro x hx
        have e := (hNfix _ (hcN x (wsub_le hA .wm hx) z)).1
        rwa [map_commutatorElement, hz] at e
  ·
    refine cT_reduce hQ h hA ?_ ?_ ?_ ha hb u hu
    · intro v hv
      obtain ⟨hvD, hav, hbv⟩ := (mem_wsub_w0 hA).1 hv
      refine cT_klQ1 hQ h hvD ?_ hz
      intro y _
      have e := (hNfix _ (hcN v hvD y)).1
      rwa [map_commutatorElement, hav] at e
    · intro v hv
      obtain ⟨hvD, hvab, -⟩ := (mem_wsub_wp hA).1 hv
      refine cT_klQ1 hQ h hvD ?_ hz
      intro y hy
      have ev : ∀ y' : Q, b y' = y' → ⁅b v, y'⁆ = ⁅v, y'⁆ := by
        intro y' hy'
        have e := (hNfix _ (hcN v hvD y')).2
        rwa [map_commutatorElement, hy'] at e
      have e2 : ⁅b v, a y⁆ = ⁅v, y⁆ := by
        have e := (hNfix _ (hcN v hvD y)).1
        rwa [map_commutatorElement, hvab] at e
      have hay : b (a y) = a y := by rw [← cT_ab h, hy]
      rw [← ev (a y) hay]
      exact e2
    · intro v hv
      refine cT_klW hQ h h.bpair.b_cube (wsub_le hA .wm) (fun x hx => (hinv .wm hx).2) ?_ ?_ v hv
      · intro x hx hbx
        obtain ⟨-, hab, he⟩ := (mem_wsub_wm hA).1 hx
        rw [hbx] at hab
        exact cT_eq_one_of_eps hQ hab he
      · intro x hx
        have e := (hNfix _ (hcN x (wsub_le hA .wm hx) z)).2
        rwa [map_commutatorElement, hz] at e

private theorem cT_tp_core (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hA : AbInv2 a b (dsub Q))
    (hP : NTypeP a b N) (ha : ∀ u ∈ wsub a b (dsub Q) hA .wa, u = 1)
    (hb : ∀ u ∈ wsub a b (dsub Q) hA .wb, u = 1) (hm : ∀ u ∈ wsub a b (dsub Q) hA .wm, u = 1) :
    False := by
  obtain ⟨hNab, hNa⟩ := hP
  have hcN : ∀ u ∈ dsub Q, ∀ z : Q, ⁅u, z⁆ ∈ N := fun u hu z => h.comm_mem hQ hu z
  have hinv : ∀ (w : Wt) {x : Q}, x ∈ wsub a b (dsub Q) hA w →
      a x ∈ wsub a b (dsub Q) hA w ∧ b x ∈ wsub a b (dsub Q) hA w := fun w {x} hx =>
    wsub_inv hQ h.bpair.a_cube h.bpair.b_cube h.bpair.comm hA w hx
  have hsurj : ∀ v ∈ wsub a b (dsub Q) hA .wp, ∃ w ∈ wsub a b (dsub Q) hA .wp, a w = v :=
    fun v hv => ⟨a (a v), (hinv .wp (hinv .wp hv).1).1, cT_cube h.bpair.a_cube v⟩
  have hm' : ∀ z : Q, ∀ v ∈ wsub a b (dsub Q) hA .wm, ⁅v, z⁆ = 1 := fun z v hv => by
    rw [hm v hv, commutatorElement_one_left]
  refine cT_false hQ h fun u hu z hz => ?_
  rcases hz with hz | hz
  ·
    refine cT_reduce hQ h hA ?_ ?_ (hm' z) ha hb u hu
    · intro v hv
      obtain ⟨hvD, hav, hbv⟩ := (mem_wsub_w0 hA).1 hv
      have hn : a ⁅v, z⁆ = ⁅v, z⁆ := by rw [map_commutatorElement, hav, hz]
      exact hNa _ (hcN v hvD z) hn
    · intro v hv
      obtain ⟨hvD, -, -⟩ := (mem_wsub_wp hA).1 hv
      refine cT_klQ2 hQ h hvD ?_ hz
      intro y hy
      obtain ⟨w, hw, hwv⟩ := hsurj v hv
      obtain ⟨hwD, hwab, -⟩ := (mem_wsub_wp hA).1 hw
      have e1 : a ⁅w, y⁆ = ⁅a w, y⁆ := by rw [map_commutatorElement, hy]
      have e2 : b ⁅w, y⁆ = ⁅a w, b y⁆ := by rw [map_commutatorElement, ← hwab]
      have e3 := hNab _ (hcN w hwD y)
      rw [e1, e2, hwv] at e3
      exact e3.symm
  ·
    refine cT_reduce hQ h hA ?_ ?_ (hm' z) ha hb u hu
    · intro v hv
      obtain ⟨hvD, hav, hbv⟩ := (mem_wsub_w0 hA).1 hv
      have hn : a ⁅v, z⁆ = ⁅v, z⁆ := by
        rw [hNab _ (hcN v hvD z), map_commutatorElement, hbv, hz]
      exact hNa _ (hcN v hvD z) hn
    · intro v hv
      obtain ⟨hvD, -, -⟩ := (mem_wsub_wp hA).1 hv
      refine cT_klQ1 hQ h hvD ?_ hz
      intro y hy
      obtain ⟨w, hw, hwv⟩ := hsurj v hv
      obtain ⟨hwD, hwab, -⟩ := (mem_wsub_wp hA).1 hw
      have e1 : a ⁅w, y⁆ = ⁅a w, a y⁆ := map_commutatorElement a w y
      have e2 : b ⁅w, y⁆ = ⁅a w, y⁆ := by rw [map_commutatorElement, hy, ← hwab]
      have e3 := hNab _ (hcN w hwD y)
      rw [e1, e2, hwv] at e3
      exact e3

end Fin

end Bilin

variable {Q : Type*} [Group Q] {a b : MulAut Q} {N : Subgroup Q}

section
variable [Finite Q]

theorem Cl3.N_fixed_free (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {n : Q} (hn : n ∈ N)
    (h1 : a n = n) (h2 : b n = n) : n = 1 := by
  by_contra hne
  have hinv : ∀ g : MulAut Q, g n = n → ∀ x ∈ Subgroup.zpowers n, g x ∈ Subgroup.zpowers n := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, hg]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hNfix : ∀ m ∈ N, a m = m ∧ b m = m := by
    rcases h.N_simple (Subgroup.zpowers n) (Subgroup.zpowers_le.2 hn) (hinv a h1) (hinv b h2)
      with h0 | h0
    · have : n ∈ (⊥ : Subgroup Q) := h0 ▸ Subgroup.mem_zpowers n
      exact absurd (Subgroup.mem_bot.1 this) hne
    · intro m hm
      rw [← h0] at hm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
      exact ⟨by rw [map_zpow, h1], by rw [map_zpow, h2]⟩
  have hA := cT_abInv hQ h
  refine cT_nff_core hQ h hA hNfix ?_ ?_
  · intro u hu
    obtain ⟨huD, hbu, he⟩ := (mem_wsub_wa hA).1 hu
    have huN : u ∈ N := h.E2_a hQ huD (by rw [hbu, mul_inv_cancel]; exact N.one_mem)
      (by rw [he]; exact N.one_mem)
    exact cT_eq_one_of_eps hQ (hNfix u huN).1 he
  · intro u hu
    obtain ⟨huD, hau, he⟩ := (mem_wsub_wb hA).1 hu
    have huN : u ∈ N := h.E2_b hQ huD (by rw [hau, mul_inv_cancel]; exact N.one_mem)
      (by rw [he]; exact N.one_mem)
    exact cT_eq_one_of_eps hQ (hNfix u huN).2 he

theorem Cl3.tensor_plus (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) (hP : NTypeP a b N) :
    ∃ u ∈ dsub Q, u ≠ 1 ∧ a (b u) = u ∧ eps a u = 1 := by
  by_contra hcon
  have hA := cT_abInv hQ h
  refine cT_tp_core hQ h hA hP ?_ ?_ ?_
  · intro u hu
    obtain ⟨huD, hbu, he⟩ := (mem_wsub_wa hA).1 hu
    have huN : u ∈ N := h.E2_a hQ huD (by rw [hbu, mul_inv_cancel]; exact N.one_mem)
      (by rw [he]; exact N.one_mem)
    exact hP.2 u huN (by rw [hP.1 u huN, hbu])
  · intro u hu
    obtain ⟨huD, hau, he⟩ := (mem_wsub_wb hA).1 hu
    have huN : u ∈ N := h.E2_b hQ huD (by rw [hau, mul_inv_cancel]; exact N.one_mem)
      (by rw [he]; exact N.one_mem)
    exact hP.2 u huN hau
  · intro u hu
    obtain ⟨huD, hab, he⟩ := (mem_wsub_wm hA).1 hu
    by_contra hne
    exact hcon ⟨u, huD, hne, hab, he⟩

end

end CFSG.GH74.E2
