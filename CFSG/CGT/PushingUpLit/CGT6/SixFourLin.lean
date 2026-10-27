module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourE9

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section Phi

variable {V : Type*} [Group V]

@[expose] def autPhi (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) : V →* V where
  toFun v := σ v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
    simp only [map_mul, mul_inv_rev]
    ac_rfl

theorem autPhi_apply (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) (v : V) :
    autPhi hc σ v = σ v * v⁻¹ := rfl

theorem autPhi_ker (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) :
    (autPhi hc σ).ker = autFixSub σ := by
  ext v
  rw [MonoidHom.mem_ker, autPhi_apply, mem_autFixSub]
  exact mul_inv_eq_one

@[expose] def autRange (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) : Subgroup V :=
  (autPhi hc σ).range

theorem autPhi_mem_autRange (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) (v : V) :
    σ v * v⁻¹ ∈ autRange hc σ := ⟨v, rfl⟩

theorem card_autRange [Finite V] (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) :
    Nat.card (autRange hc σ) = (autFixSub σ).index := by
  rw [← autPhi_ker hc σ, Subgroup.index_ker]
  rfl

end Phi

section FixQ

variable {Q V : Type*} [Group Q] [Group V]

@[expose] def fixQ (θ : Q →* MulAut V) (S : Subgroup Q) : Subgroup V := autFixGrp (S.map θ)

theorem mem_fixQ {θ : Q →* MulAut V} {S : Subgroup Q} {v : V} :
    v ∈ fixQ θ S ↔ ∀ s ∈ S, θ s v = v := by
  rw [fixQ, mem_autFixGrp]
  constructor
  · intro h s hs
    exact h _ ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    exact h s hs

theorem fixQ_zpowers (θ : Q →* MulAut V) (a : Q) :
    fixQ θ (Subgroup.zpowers a) = autFixSub (θ a) := by
  ext v
  rw [mem_fixQ, mem_autFixSub]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [map_zpow]
    clear hs
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, MulAut.mul_apply, h, ih]
    | pred k ih =>
      have : (θ a) ((θ a)⁻¹ v) = v := by simp
      rw [zpow_sub_one, MulAut.mul_apply]
      have h2 : (θ a)⁻¹ v = v := by
        have := congrArg (fun w => (θ a)⁻¹ w) h
        simpa using this.symm
      rw [h2, ih]

theorem fixQ_sup (θ : Q →* MulAut V) (S S' : Subgroup Q) :
    fixQ θ (S ⊔ S') = fixQ θ S ⊓ fixQ θ S' := by
  ext v
  simp only [Subgroup.mem_inf, mem_fixQ]
  constructor
  · intro H
    exact ⟨fun s hs => H s (Subgroup.mem_sup_left hs), fun s hs => H s (Subgroup.mem_sup_right hs)⟩
  · rintro ⟨H1, H2⟩ s hs
    let F : Subgroup Q := (MulAction.stabilizer (MulAut V) v).comap θ
    have hS : S ≤ F := fun s hs => by
      show θ s • v = v
      exact H1 s hs
    have hS' : S' ≤ F := fun s hs => by
      show θ s • v = v
      exact H2 s hs
    exact (sup_le hS hS') hs

theorem fixQ_conj (θ : Q →* MulAut V) (S : Subgroup Q) (k : Q) :
    fixQ θ (S.map (MulAut.conj k).toMonoidHom) = (fixQ θ S).comap (θ k⁻¹ : MulAut V).toMonoidHom := by
  ext v
  rw [Subgroup.mem_comap, mem_fixQ, mem_fixQ]
  constructor
  · intro H s hs
    have h1 := H (k * s * k⁻¹) ⟨s, hs, rfl⟩
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := congrArg (fun w => θ k⁻¹ w) h1
    simp only [← MulAut.mul_apply, ← map_mul] at h2
    simpa [MulAut.mul_apply] using h2
  · rintro H _ ⟨s, hs, rfl⟩
    have h1 : θ s (θ k⁻¹ v) = θ k⁻¹ v := H s hs
    show θ (k * s * k⁻¹) v = v
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply]

theorem index_fixQ_conj (θ : Q →* MulAut V) (S : Subgroup Q) (k : Q) :
    (fixQ θ (S.map (MulAut.conj k).toMonoidHom)).index = (fixQ θ S).index := by
  rw [fixQ_conj θ S k]
  exact Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)

end FixQ

section E9T

variable {V : Type*} [Group V]

@[expose] def e9norm (b₁ b₂ : MulAut V) (v : V) : V :=
  v * b₁ v * (b₁ ^ 2) v * b₂ v * (b₁ * b₂) v * (b₁ ^ 2 * b₂) v * (b₂ ^ 2) v * (b₁ * b₂ ^ 2) v *
    (b₁ ^ 2 * b₂ ^ 2) v

theorem e9norm_mul (hc : ∀ a b : V, a * b = b * a) (b₁ b₂ : MulAut V) (a b : V) :
    e9norm b₁ b₂ (a * b) = e9norm b₁ b₂ a * e9norm b₁ b₂ b := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  simp only [e9norm, map_mul]
  ac_rfl

theorem e9norm_one (b₁ b₂ : MulAut V) : e9norm b₁ b₂ 1 = 1 := by
  simp [e9norm]

@[expose] def e9normHom (hc : ∀ a b : V, a * b = b * a) (b₁ b₂ : MulAut V) : V →* V where
  toFun := e9norm b₁ b₂
  map_one' := e9norm_one b₁ b₂
  map_mul' := e9norm_mul hc b₁ b₂

@[expose] def e9W (hc : ∀ a b : V, a * b = b * a) (b₁ b₂ : MulAut V) : Subgroup V :=
  (e9normHom hc b₁ b₂).ker

theorem mem_e9W (hc : ∀ a b : V, a * b = b * a) {b₁ b₂ : MulAut V} {v : V} :
    v ∈ e9W hc b₁ b₂ ↔ e9norm b₁ b₂ v = 1 := MonoidHom.mem_ker

theorem e9norm_b₁ (hc : ∀ a b : V, a * b = b * a) {b₁ b₂ : MulAut V} (hb₁ : b₁ ^ 3 = 1)
    (hb : b₁ * b₂ = b₂ * b₁) (v : V) : e9norm b₁ b₂ (b₁ v) = e9norm b₁ b₂ v := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hbc : Commute b₁ b₂ := hb
  have r1 : b₁ * b₁ = b₁ ^ 2 := (pow_two b₁).symm
  have r2 : b₁ ^ 2 * b₁ = 1 := by rw [← pow_succ]; exact hb₁
  have r3 : b₂ * b₁ = b₁ * b₂ := hb.symm
  have r4 : b₁ * b₂ * b₁ = b₁ ^ 2 * b₂ := by rw [mul_assoc, r3, ← mul_assoc, r1]
  have r5 : b₁ ^ 2 * b₂ * b₁ = b₂ := by rw [mul_assoc, r3, ← mul_assoc, r2, one_mul]
  have r6 : b₂ ^ 2 * b₁ = b₁ * b₂ ^ 2 := (hbc.pow_right 2).eq.symm
  have r7 : b₁ * b₂ ^ 2 * b₁ = b₁ ^ 2 * b₂ ^ 2 := by rw [mul_assoc, r6, ← mul_assoc, r1]
  have r8 : b₁ ^ 2 * b₂ ^ 2 * b₁ = b₂ ^ 2 := by
    rw [mul_assoc, r6, ← mul_assoc, r2, one_mul]
  simp only [e9norm, ← MulAut.mul_apply, r1, r2, r3, r4, r5, r6, r7, r8, MulAut.one_apply]
  ac_rfl

theorem e9norm_b₂ (hc : ∀ a b : V, a * b = b * a) {b₁ b₂ : MulAut V} (hb₂ : b₂ ^ 3 = 1)
    (hb : b₁ * b₂ = b₂ * b₁) (v : V) : e9norm b₁ b₂ (b₂ v) = e9norm b₁ b₂ v := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hbc : Commute b₁ b₂ := hb
  have r1 : b₂ * b₂ = b₂ ^ 2 := (pow_two b₂).symm
  have r2 : b₂ ^ 2 * b₂ = 1 := by rw [← pow_succ]; exact hb₂
  have r3 : b₁ * b₂ * b₂ = b₁ * b₂ ^ 2 := by rw [mul_assoc, r1]
  have r4 : b₁ ^ 2 * b₂ * b₂ = b₁ ^ 2 * b₂ ^ 2 := by rw [mul_assoc, r1]
  have r5 : b₁ * b₂ ^ 2 * b₂ = b₁ := by rw [mul_assoc, r2, mul_one]
  have r6 : b₁ ^ 2 * b₂ ^ 2 * b₂ = b₁ ^ 2 := by rw [mul_assoc, r2, mul_one]
  simp only [e9norm, ← MulAut.mul_apply, r1, r2, r3, r4, r5, r6, MulAut.one_apply]
  ac_rfl

theorem e9norm_of_mem_closure (hc : ∀ a b : V, a * b = b * a) {b₁ b₂ : MulAut V} (hb₁ : b₁ ^ 3 = 1)
    (hb₂ : b₂ ^ 3 = 1) (hb : b₁ * b₂ = b₂ * b₁) {y : MulAut V}
    (hy : y ∈ Subgroup.closure ({b₁, b₂} : Set (MulAut V))) :
    ∀ v : V, e9norm b₁ b₂ (y v) = e9norm b₁ b₂ v := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact e9norm_b₁ hc hb₁ hb
    · exact e9norm_b₂ hc hb₂ hb
  | one => intro v; rfl
  | mul x y _ _ hx hy =>
    intro v
    rw [MulAut.mul_apply, hx, hy]
  | inv x _ hx =>
    intro v
    have h := hx (x⁻¹ v)
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h
    exact h.symm

theorem autRange_le_e9W (hc : ∀ a b : V, a * b = b * a) {b₁ b₂ : MulAut V} (hb₁ : b₁ ^ 3 = 1)
    (hb₂ : b₂ ^ 3 = 1) (hb : b₁ * b₂ = b₂ * b₁) {y : MulAut V}
    (hy : y ∈ Subgroup.closure ({b₁, b₂} : Set (MulAut V))) :
    autRange hc y ≤ e9W hc b₁ b₂ := by
  rintro _ ⟨v, rfl⟩
  rw [mem_e9W hc, autPhi_apply]
  have h1 := e9norm_mul hc b₁ b₂ (y v * v⁻¹) v
  rw [inv_mul_cancel_right, e9norm_of_mem_closure hc hb₁ hb₂ hb hy v] at h1
  exact mul_right_cancel (b := e9norm b₁ b₂ v) (by rw [one_mul]; exact h1.symm)

theorem e9t_dihedral (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) {t b₁ b₂ : MulAut V}
    (hb₂ : b₂ ^ 3 = 1)
    (htb₁ : t * b₁ = b₁ ^ 2 * t) (htb₂ : t * b₂ = b₂ ^ 2 * t) {w : V} (htw : t w = w)
    (hw : e9norm b₁ b₂ w = 1) : w ∈ autRange hc t := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have r1 : b₂ ^ 2 * b₂ = 1 := by rw [← pow_succ]; exact hb₂
  set P : V := b₁ w * b₂ w * (b₁ * b₂) w * (b₁ * b₂ ^ 2) w with hP
  refine ⟨P, ?_⟩
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right (hV P)
  have e1 : t (b₁ w) = (b₁ ^ 2) w := by
    rw [← MulAut.mul_apply, htb₁, MulAut.mul_apply, htw]
  have e2 : t (b₂ w) = (b₂ ^ 2) w := by
    rw [← MulAut.mul_apply, htb₂, MulAut.mul_apply, htw]
  have e3 : t ((b₁ * b₂) w) = (b₁ ^ 2 * b₂ ^ 2) w := by
    have : t * (b₁ * b₂) = b₁ ^ 2 * b₂ ^ 2 * t := by
      rw [← mul_assoc, htb₁, mul_assoc, htb₂, ← mul_assoc]
    rw [← MulAut.mul_apply, this, MulAut.mul_apply, htw]
  have hb4 : b₂ ^ 2 * b₂ ^ 2 = b₂ := by
    calc b₂ ^ 2 * b₂ ^ 2 = b₂ ^ 4 := by rw [← pow_add]
      _ = b₂ ^ 3 * b₂ := by rw [← pow_succ]
      _ = b₂ := by rw [hb₂, one_mul]
  have h4 : t * b₂ ^ 2 = b₂ * t := by
    calc t * b₂ ^ 2 = t * (b₂ * b₂) := by rw [pow_two]
      _ = (t * b₂) * b₂ := by rw [mul_assoc]
      _ = (b₂ ^ 2 * t) * b₂ := by rw [htb₂]
      _ = b₂ ^ 2 * (t * b₂) := by rw [mul_assoc]
      _ = b₂ ^ 2 * (b₂ ^ 2 * t) := by rw [htb₂]
      _ = (b₂ ^ 2 * b₂ ^ 2) * t := by rw [mul_assoc]
      _ = b₂ * t := by rw [hb4]
  have e4 : t ((b₁ * b₂ ^ 2) w) = (b₁ ^ 2 * b₂) w := by
    have : t * (b₁ * b₂ ^ 2) = b₁ ^ 2 * b₂ * t := by
      rw [← mul_assoc, htb₁, mul_assoc, h4, ← mul_assoc]
    rw [← MulAut.mul_apply, this, MulAut.mul_apply, htw]
  have hN8 : w * (b₁ w * (b₁ ^ 2) w * b₂ w * (b₂ ^ 2) w * (b₁ * b₂) w * (b₁ ^ 2 * b₂ ^ 2) w *
      (b₁ * b₂ ^ 2) w * (b₁ ^ 2 * b₂) w) = 1 := by
    rw [← hw]
    unfold e9norm
    ac_rfl
  have key : t P * P = b₁ w * (b₁ ^ 2) w * b₂ w * (b₂ ^ 2) w * (b₁ * b₂) w * (b₁ ^ 2 * b₂ ^ 2) w *
      (b₁ * b₂ ^ 2) w * (b₁ ^ 2 * b₂) w := by
    rw [hP]
    simp only [map_mul, e1, e2, e3, e4]
    ac_rfl
  rw [autPhi_apply, hPinv, key]
  rw [eq_inv_of_mul_eq_one_right hN8]
  exact inv_eq_of_mul_eq_one_right (hV w)

theorem e9t_card_le [Finite V] (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1)
    {t b₁ b₂ : MulAut V} (hb₂ : b₂ ^ 3 = 1)
    (htb₁ : t * b₁ = b₁ ^ 2 * t) (htb₂ : t * b₂ = b₂ ^ 2 * t) :
    Nat.card (e9W hc b₁ b₂) ≤ Nat.card (autRange hc t) ^ 2 := by
  set W := e9W hc b₁ b₂ with hWdef
  let f : W →* V := (autPhi hc t).comp W.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card W := by
    have := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker] at this
    exact this
  have h2 : Nat.card f.range ≤ Nat.card (autRange hc t) :=
    Subgroup.card_le_of_le (by rintro _ ⟨y, rfl⟩; exact ⟨(y : V), rfl⟩)
  have h3 : Nat.card f.ker ≤ Nat.card (autRange hc t) := by
    have hmem : ∀ x : f.ker, ((x : W) : V) ∈ autRange hc t := by
      intro x
      have hx1 : f (x : W) = 1 := x.2
      have hx2 : t ((x : W) : V) * ((x : W) : V)⁻¹ = 1 := hx1
      have hx3 : t ((x : W) : V) = ((x : W) : V) := mul_inv_eq_one.mp hx2
      exact e9t_dihedral hc hV hb₂ htb₁ htb₂ hx3 ((x : W).2)
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : W) : V), hmem x⟩) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card W = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card (autRange hc t) * Nat.card (autRange hc t) := Nat.mul_le_mul h3 h2
    _ = Nat.card (autRange hc t) ^ 2 := (sq _).symm

theorem e9t_main [Finite V] (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1)
    {t b₁ b₂ : MulAut V} (hb₁ : b₁ ^ 3 = 1) (hb₂ : b₂ ^ 3 = 1) (hb : b₁ * b₂ = b₂ * b₁)
    (htb₁ : t * b₁ = b₁ ^ 2 * t) (htb₂ : t * b₂ = b₂ ^ 2 * t)
    (hidx : (autFixSub t).index ≤ 4) {y : MulAut V}
    (hy : y ∈ Subgroup.closure ({b₁, b₂} : Set (MulAut V))) (hyidx : 16 ≤ (autFixSub y).index)
    {x : MulAut V} (hx : x ∈ Subgroup.closure ({b₁, b₂} : Set (MulAut V))) (v : V) :
    x v * v⁻¹ ∈ autRange hc y := by
  have hW : Nat.card (e9W hc b₁ b₂) ≤ 16 := by
    refine (e9t_card_le hc hV hb₂ htb₁ htb₂).trans ?_
    rw [card_autRange]
    calc (autFixSub t).index ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hidx 2
      _ = 16 := by norm_num
  have hyW := autRange_le_e9W hc hb₁ hb₂ hb hy
  have hxW := autRange_le_e9W hc hb₁ hb₂ hb hx
  have hcard : Nat.card (e9W hc b₁ b₂) ≤ Nat.card (autRange hc y) := by
    rw [card_autRange]
    exact hW.trans hyidx
  have heq : autRange hc y = e9W hc b₁ b₂ := Subgroup.eq_of_le_of_card_ge hyW hcard
  rw [heq]
  exact hxW (autPhi_mem_autRange hc x v)

end E9T

section Three

variable {V : Type*} [Group V]

@[expose] def zNormHom (hc : ∀ a b : V, a * b = b * a) (z : MulAut V) : V →* V where
  toFun v := v * z v * (z ^ 2) v
  map_one' := by simp
  map_mul' a b := by
    let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
    simp only [map_mul]
    ac_rfl

@[expose] def zV0 (hc : ∀ a b : V, a * b = b * a) (z : MulAut V) : Subgroup V := (zNormHom hc z).ker

theorem mem_zV0 (hc : ∀ a b : V, a * b = b * a) {z : MulAut V} {v : V} :
    v ∈ zV0 hc z ↔ v * z v * (z ^ 2) v = 1 := MonoidHom.mem_ker

theorem zV0_inf_fix (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) {z : MulAut V} :
    zV0 hc z ⊓ autFixSub z = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h0, h1⟩ := Subgroup.mem_inf.mp hv
  rw [mem_zV0] at h0
  rw [mem_autFixSub] at h1
  have h2 : (z ^ 2) v = v := by
    rw [pow_two, MulAut.mul_apply, h1, h1]
  rw [h1, h2] at h0
  have : v * v * v = v := by rw [hV v, one_mul]
  rw [this] at h0
  exact (Subgroup.mem_bot).mpr h0

theorem zV0_sup_fix (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) {z : MulAut V}
    (hz : z ^ 3 = 1) : zV0 hc z ⊔ autFixSub z = ⊤ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  rw [eq_top_iff]
  intro v _
  have hsq : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
  have hn : v * z v * (z ^ 2) v ∈ autFixSub z := norm_mem_autFixSub hc hz v
  have hm : z v * (z ^ 2) v ∈ zV0 hc z := by
    rw [mem_zV0]
    have h3 : (z ^ 3) v = v := by rw [hz]; rfl
    have e1 : z (z v) = (z ^ 2) v := by simp [pow_two]
    have e2 : z ((z ^ 2) v) = v := by
      have : (z ^ 3) v = z ((z ^ 2) v) := by rw [pow_succ', MulAut.mul_apply]
      rw [← this, h3]
    have e3 : (z ^ 2) (z v) = z ((z ^ 2) v) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
    have e4 : (z ^ 2) ((z ^ 2) v) = z v := by
      rw [← MulAut.mul_apply, ← pow_add]
      have : z ^ (2 + 2) = z := by
        calc z ^ (2 + 2) = z ^ 3 * z := by rw [← pow_succ]
          _ = z := by rw [hz, one_mul]
      rw [this]
    simp only [map_mul]
    rw [e1, e2, e3, e2, e4]
    calc z v * (z ^ 2) v * ((z ^ 2) v * v) * (v * z v)
        = (v * z v * (z ^ 2) v) * (v * z v * (z ^ 2) v) := by ac_rfl
      _ = 1 := hV _
  have hv : v = (v * z v * (z ^ 2) v) * (z v * (z ^ 2) v) := by
    have : (v * z v * (z ^ 2) v) * (z v * (z ^ 2) v) = v * ((z v * z v) * ((z ^ 2) v * (z ^ 2) v)) := by
      ac_rfl
    rw [this, hV (z v), hV ((z ^ 2) v), one_mul, mul_one]
  have hmem := Subgroup.mul_mem_sup hn hm
  rw [sup_comm] at hmem
  rwa [← hv] at hmem

theorem le_zV0_of_fpf (hc : ∀ a b : V, a * b = b * a) {z : MulAut V} (hz : z ^ 3 = 1)
    {S : Subgroup V} (hS : ∀ s ∈ S, z s ∈ S) (hfix : S ⊓ autFixSub z = ⊥) : S ≤ zV0 hc z := by
  intro s hs
  have h1 : s * z s * (z ^ 2) s ∈ S := by
    refine S.mul_mem (S.mul_mem hs (hS s hs)) ?_
    rw [pow_two, MulAut.mul_apply]
    exact hS _ (hS s hs)
  have h2 : s * z s * (z ^ 2) s ∈ autFixSub z := norm_mem_autFixSub hc hz s
  have h3 : s * z s * (z ^ 2) s ∈ S ⊓ autFixSub z := ⟨h1, h2⟩
  rw [hfix] at h3
  exact (mem_zV0 hc).mpr (Subgroup.mem_bot.mp h3)

theorem four_le_card_of_fpf [Finite V] {z : MulAut V} (hz : z ^ 3 = 1) {H : Subgroup V}
    (hH : ∀ s ∈ H, z s ∈ H) (hfix : H ⊓ autFixSub z = ⊥) {u : V} (hu : u ∈ H) (hu1 : u ≠ 1) :
    4 ≤ Nat.card H := by
  classical
  have hzu : z u ≠ u := by
    intro h
    apply hu1
    have : u ∈ H ⊓ autFixSub z := ⟨hu, h⟩
    rw [hfix] at this
    exact Subgroup.mem_bot.mp this
  have hz1 : z u ≠ 1 := fun h => hu1 (by simpa using congrArg (fun w => z⁻¹ w) (h.trans (map_one z).symm))
  have hz2 : (z ^ 2) u = z (z u) := by simp [pow_two]
  have hz3 : z ((z ^ 2) u) = u := by
    have : (z ^ 3) u = z ((z ^ 2) u) := by rw [pow_succ', MulAut.mul_apply]
    rw [← this, hz]; rfl
  have hz2u : (z ^ 2) u ≠ u := by
    intro h
    apply hzu
    have := congrArg z h
    rw [hz3] at this
    exact this.symm
  have hz21 : (z ^ 2) u ≠ 1 := by
    intro h
    apply hu1
    have := congrArg z h
    rw [hz3, map_one] at this
    exact this
  have hz2z : (z ^ 2) u ≠ z u := by
    intro h
    apply hzu
    have h1 := congrArg z h
    have h2 := congrArg z h1
    rw [hz3] at h1
    rw [h1] at h2
    have h3 : z u = z (z u) := by rw [← hz2]; exact h.symm
    exact (z.injective h3).symm
  have hmem : ∀ w ∈ ({1, u, z u, (z ^ 2) u} : Finset V), w ∈ (H : Set V) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hu
    · exact hH u hu
    · rw [hz2]; exact hH _ (hH u hu)
  have hcard : ({1, u, z u, (z ^ 2) u} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact hz2z.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzu.symm, hz2u.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hu1.symm, hz1.symm, hz21.symm⟩
  have hsub : (({1, u, z u, (z ^ 2) u} : Finset V) : Set V) ⊆ (H : Set V) := fun w hw => hmem w hw
  calc 4 = ({1, u, z u, (z ^ 2) u} : Finset V).card := hcard.symm
    _ = (({1, u, z u, (z ^ 2) u} : Finset V) : Set V).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (H : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card H := Nat.card_coe_set_eq _ |>.symm

theorem fix_of_commute_fpf [Finite V] (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1)
    {z b : MulAut V} (hz : z ^ 3 = 1) (hbz : b * z = z * b) (hb : b * b = 1)
    {S : Subgroup V} (hS4 : Nat.card S = 4) (hSz : ∀ s ∈ S, z s ∈ S) (hSb : ∀ s ∈ S, b s ∈ S)
    (hfix : S ⊓ autFixSub z = ⊥) : ∀ s ∈ S, b s = s := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hsq : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
  set H₀ : Subgroup V := S ⊓ autFixSub b with hH₀
  have hle : H₀ ≤ S := inf_le_left
  have hH₀z : ∀ s ∈ H₀, z s ∈ H₀ := by
    intro s hs
    refine ⟨hSz s hs.1, ?_⟩
    show b (z s) = z s
    have h1 : b (z s) = z (b s) := by
      rw [← MulAut.mul_apply, hbz, MulAut.mul_apply]
    have h2 : b s = s := hs.2
    rw [h1, h2]
  have hH₀fix : H₀ ⊓ autFixSub z = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ S ⊓ autFixSub z := ⟨hv.1.1, hv.2⟩
    rw [hfix] at this
    exact this
  have hex : ∃ u ∈ H₀, u ≠ 1 := by
    have hne : S ≠ ⊥ := by
      intro h
      rw [h] at hS4
      simp at hS4
    obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hbt : b (s * b s) = s * b s := by
      rw [map_mul, ← MulAut.mul_apply, hb, MulAut.one_apply, mul_comm]
    have htS : s * b s ∈ S := S.mul_mem hs (hSb s hs)
    by_cases ht : s * b s = 1
    · refine ⟨s, ⟨hs, ?_⟩, hs1'⟩
      show b s = s
      have : b s = s⁻¹ := eq_inv_of_mul_eq_one_right ht
      rw [this, hsq]
    · exact ⟨s * b s, ⟨htS, hbt⟩, ht⟩
  obtain ⟨u, hu, hu1⟩ := hex
  have h4 : 4 ≤ Nat.card H₀ := four_le_card_of_fpf hz hH₀z hH₀fix hu hu1
  have hEq : H₀ = S := Subgroup.eq_of_le_of_card_ge hle (by rw [hS4]; exact h4)
  intro s hs
  have : s ∈ H₀ := hEq ▸ hs
  exact this.2

end Three

section Comm

variable {Q V : Type*} [Group Q] [Group V]

@[expose] def commSub (θ : Q →* MulAut V) (S : Subgroup Q) : Subgroup V :=
  Subgroup.closure {w | ∃ s ∈ S, ∃ v : V, w = θ s v * v⁻¹}

theorem mem_commSub_of_mem (θ : Q →* MulAut V) {S : Subgroup Q} {s : Q} (hs : s ∈ S) (v : V) :
    θ s v * v⁻¹ ∈ commSub θ S :=
  Subgroup.subset_closure ⟨s, hs, v, rfl⟩

@[expose] def stabComm (θ : Q →* MulAut V) (S : Subgroup Q) : Subgroup Q where
  carrier := {k | ∀ v : V, θ k v * v⁻¹ ∈ commSub θ S}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro k₁ k₂ h₁ h₂ v
    have e : θ (k₁ * k₂) v * v⁻¹ = (θ k₁ (θ k₂ v) * (θ k₂ v)⁻¹) * (θ k₂ v * v⁻¹) := by
      rw [map_mul, MulAut.mul_apply]
      group
    rw [e]
    exact (commSub θ S).mul_mem (h₁ _) (h₂ v)
  inv_mem' := by
    intro k hk v
    have h := hk (θ k⁻¹ v)
    have e : θ k (θ k⁻¹ v) = v := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [e] at h
    have := (commSub θ S).inv_mem h
    simpa using this

theorem le_stabComm (θ : Q →* MulAut V) (S : Subgroup Q) : S ≤ stabComm θ S :=
  fun _ hs v => mem_commSub_of_mem θ hs v

end Comm

end CFSG.CGT.PushingUpLit.CGT6
