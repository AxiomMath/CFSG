module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Quot

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Fixed

theorem exists_fixed_conj {G : Type*} [Group G] [Finite G] {y : G} (hy : orderOf y = 3)
    (S : Set G) (hS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hcard : ¬ 3 ∣ Nat.card S) :
    ∃ s ∈ S, y * s * y⁻¹ = s := by
  have hpow : ∀ (n : ℕ) (s : G), s ∈ S → y ^ n * s * (y ^ n)⁻¹ ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      have := hS _ (ih s hs)
      have e : y ^ (n + 1) * s * (y ^ (n + 1))⁻¹ = y * (y ^ n * s * (y ^ n)⁻¹) * y⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      exact this
  have hSa : ∀ a ∈ zpowers y, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
    intro a ha s hs
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 ha)
    exact hpow n s hs
  let act : MulAction (zpowers y) S :=
    { smul := fun a s => ⟨a * s * a⁻¹, hSa a a.2 s s.2⟩
      one_smul := fun s => Subtype.ext (by
        show ((1 : zpowers y) : G) * (s : G) * ((1 : zpowers y) : G)⁻¹ = s
        simp)
      mul_smul := fun a b s => Subtype.ext (by
        show ((a * b : zpowers y) : G) * s * ((a * b : zpowers y) : G)⁻¹ =
          a * (b * s * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_fixed_of_card_prime (G := zpowers y) (X := S) 3
    (by rw [Nat.card_zpowers, hy]) hcard
  refine ⟨s, s.2, ?_⟩
  have := hs ⟨y, mem_zpowers y⟩
  exact congrArg Subtype.val this

end Fixed

section Comm

variable {G : Type*} [Group G]

@[expose] def commHom (t : G) (F T : Subgroup G) (hFW : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hFt : ∀ w ∈ F, t * w * t⁻¹ ∈ F) (hT : ∀ w ∈ F, w * t * w⁻¹ * t⁻¹ ∈ T) : ↥F →* ↥T where
  toFun w := ⟨w * t * w⁻¹ * t⁻¹, hT w w.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    have hA : t * (a : G)⁻¹ * t⁻¹ ∈ F := hFt _ (F.inv_mem a.2)
    have hB : t * (b : G)⁻¹ * t⁻¹ ∈ F := hFt _ (F.inv_mem b.2)
    show (a * b : G) * t * (a * b : G)⁻¹ * t⁻¹ =
      ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)
    set A' := t * (a : G)⁻¹ * t⁻¹ with hA'
    set B' := t * (b : G)⁻¹ * t⁻¹ with hB'
    have e1 : (a * b : G) * t * (a * b : G)⁻¹ * t⁻¹ = a * b * B' * A' := by
      simp only [hA', hB']
      group
    have e2 : ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) =
        a * A' * (b * B') := by
      simp only [hA', hB']
      group
    rw [e1, e2]
    have c1 : B' * A' = A' * B' := hFW _ hB _ hA
    have c2 : (b : G) * A' = A' * b := hFW _ b.2 _ hA
    calc (a : G) * b * B' * A' = a * b * (B' * A') := by simp only [mul_assoc]
      _ = a * b * (A' * B') := by rw [c1]
      _ = a * (b * A') * B' := by simp only [mul_assoc]
      _ = a * (A' * b) * B' := by rw [c2]
      _ = a * A' * (b * B') := by simp only [mul_assoc]

end Comm

section WData

variable {G : Type*} [Group G] [Finite G]

structure WData (E W : Subgroup G) (t y : G) : Prop where
  t_sq : t * t = 1
  y_ord : orderOf y = 3
  yt : y * t = t * y
  W_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  E_le : E ≤ W
  E_t : ∀ e ∈ E, e * t = t * e
  t_nmem : t ∉ W
  tW : ∀ w ∈ W, t * w * t⁻¹ ∈ W
  yW : ∀ w ∈ W, y * w * y⁻¹ ∈ W
  wt_mem : ∀ w ∈ W, w * t * w⁻¹ ∈ zpowers t ⊔ E
  cent : centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E
  W_card : Nat.card W = 256
  E_card : Nat.card E = 16

variable {E W : Subgroup G} {t y : G}

omit [Finite G] in
theorem WData.inf_sup (h : WData E W t y) {g : G} (hgW : g ∈ W) (hg : g ∈ zpowers t ⊔ E) :
    g ∈ E := by
  obtain ⟨n, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup h.E_t hg
  rcases zpow_involution t h.t_sq n with h1 | h1
  · rw [h1, one_mul]
    exact he
  · exfalso
    rw [h1] at hgW
    apply h.t_nmem
    have := W.mul_mem hgW (W.inv_mem (h.E_le he))
    simpa using this

omit [Finite G] in
theorem WData.mem_E_of_comm (h : WData E W t y) {w : G} (hw : w ∈ W) (hc : w * t = t * w) :
    w ∈ E := by
  apply h.inf_sup hw
  rw [← h.cent]
  rw [mem_centralizer_iff]
  intro s hs
  have hle : zpowers t ⊔ E ≤ centralizer ({w} : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 hc.symm
    · intro e he
      exact mem_centralizer_singleton_iff.2 (h.W_comm e (h.E_le he) w hw)
  exact mem_centralizer_singleton_iff.1 (hle hs)

omit [Finite G] in
theorem WData.comm_mem_E (h : WData E W t y) {w : G} (hw : w ∈ W) :
    w * t * w⁻¹ * t⁻¹ ∈ E := by
  have h1 : w * t * w⁻¹ * t⁻¹ ∈ W := by
    have := W.mul_mem hw (h.tW _ (W.inv_mem hw))
    simpa [mul_assoc] using this
  apply h.inf_sup h1
  exact mul_mem (h.wt_mem w hw) (inv_mem (Subgroup.mem_sup_left (mem_zpowers t)))

theorem WData.surj (h : WData E W t y) (e : G) (he : e ∈ E) :
    ∃ w ∈ W, w * t * w⁻¹ * t⁻¹ = e := by
  let ψ := commHom t W E h.W_comm h.tW (fun w hw => h.comm_mem_E hw)
  have hker : ψ.ker = E.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (w : G) * t = t * w := by
        have := mul_inv_eq_one.1 h2
        exact (mul_inv_eq_one.1 (by simpa [mul_assoc] using h2))
      exact h.mem_E_of_comm w.2 h3
    · intro h1
      apply Subtype.ext
      show (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1
      rw [h.E_t _ h1]
      group
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv, h.E_card,
    h.W_card] at hcard
  have hr : Nat.card ψ.range = Nat.card E := by rw [h.E_card]; omega
  have htop := Subgroup.eq_top_of_card_eq ψ.range hr
  have hmem : (⟨e, he⟩ : E) ∈ ψ.range := by rw [htop]; exact mem_top _
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem WData.lift (h : WData E W t y) {e : G} (he : e ∈ E) (hey : y * e = e * y) :
    ∃ w ∈ W, y * w = w * y ∧ w * t * w⁻¹ * t⁻¹ = e := by
  obtain ⟨w₀, hw₀, hψ₀⟩ := h.surj e he
  have hconj' : y⁻¹ * t * y = t := by
    rw [mul_assoc, ← h.yt, inv_mul_cancel_left]
  have hy' : y⁻¹ * t⁻¹ = t⁻¹ * y⁻¹ := by
    have := congrArg (fun a => a⁻¹) h.yt
    simpa [mul_inv_rev] using this.symm
  have hye : y * e * y⁻¹ = e := mul_inv_eq_iff_eq_mul.2 hey
  let S : Set G := {w | w ∈ W ∧ w * t * w⁻¹ * t⁻¹ = e}
  have hS : ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    rintro s ⟨hsW, hse⟩
    refine ⟨h.yW s hsW, ?_⟩
    calc y * s * y⁻¹ * t * (y * s * y⁻¹)⁻¹ * t⁻¹
        = y * s * (y⁻¹ * t * y) * s⁻¹ * y⁻¹ * t⁻¹ := by group
      _ = y * s * t * s⁻¹ * (y⁻¹ * t⁻¹) := by rw [hconj']; group
      _ = y * s * t * s⁻¹ * (t⁻¹ * y⁻¹) := by rw [hy']
      _ = y * (s * t * s⁻¹ * t⁻¹) * y⁻¹ := by group
      _ = e := by rw [hse, hye]
  have hcard : Nat.card S = 16 := by
    let f : E → S := fun x => ⟨w₀ * x, mul_mem hw₀ (h.E_le x.2), by
      have hx : (x : G) * t = t * x := h.E_t x x.2
      calc w₀ * x * t * (w₀ * x)⁻¹ * t⁻¹ = w₀ * (x * t * (x : G)⁻¹) * w₀⁻¹ * t⁻¹ := by group
        _ = w₀ * t * w₀⁻¹ * t⁻¹ := by rw [hx]; group
        _ = e := hψ₀⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (mul_left_cancel this)
      · rintro ⟨s, hsW, hse⟩
        have h1 : w₀ * t * w₀⁻¹ * t⁻¹ = s * t * s⁻¹ * t⁻¹ := hψ₀.trans hse.symm
        have h2 : w₀ * t * w₀⁻¹ = s * t * s⁻¹ := mul_right_cancel h1
        have hxW : w₀⁻¹ * s ∈ W := W.mul_mem (W.inv_mem hw₀) hsW
        have hxc : w₀⁻¹ * s * t = t * (w₀⁻¹ * s) := by
          calc w₀⁻¹ * s * t = w₀⁻¹ * (s * t * s⁻¹) * s := by group
            _ = w₀⁻¹ * (w₀ * t * w₀⁻¹) * s := by rw [← h2]
            _ = t * (w₀⁻¹ * s) := by group
        refine ⟨⟨w₀⁻¹ * s, h.mem_E_of_comm hxW hxc⟩, ?_⟩
        apply Subtype.ext
        show w₀ * (w₀⁻¹ * s) = s
        group
    rw [← Nat.card_congr (Equiv.ofBijective f hf), h.E_card]
  obtain ⟨s, hs, hfix⟩ := exists_fixed_conj h.y_ord S hS (by rw [hcard]; decide)
  exact ⟨s, hs.1, mul_inv_eq_iff_eq_mul.1 hfix, hs.2⟩

theorem WData.card_cent (h : WData E W t y)
    (hEy : Nat.card ↥(E ⊓ centralizer ({y} : Set G)) = 4) :
    Nat.card ↥(W ⊓ centralizer ({y} : Set G)) = 16 := by
  have hyt : Commute y t := h.yt
  have hcy : ∀ w ∈ centralizer ({y} : Set G), Commute y w := fun w hw =>
    (mem_centralizer_singleton_iff.1 hw).symm
  have hFW : ∀ a ∈ W ⊓ centralizer ({y} : Set G), ∀ b ∈ W ⊓ centralizer ({y} : Set G),
      a * b = b * a := fun a ha b hb => h.W_comm a ha.1 b hb.1
  have hFt : ∀ w ∈ W ⊓ centralizer ({y} : Set G), t * w * t⁻¹ ∈ W ⊓ centralizer ({y} : Set G) := by
    intro w hw
    refine ⟨h.tW w hw.1, mem_centralizer_singleton_iff.2 ?_⟩
    exact ((hyt.mul_right (hcy w hw.2)).mul_right hyt.inv_right).symm
  have hT : ∀ w ∈ W ⊓ centralizer ({y} : Set G),
      w * t * w⁻¹ * t⁻¹ ∈ E ⊓ centralizer ({y} : Set G) := by
    intro w hw
    refine ⟨h.comm_mem_E hw.1, mem_centralizer_singleton_iff.2 ?_⟩
    have hw' := hcy w hw.2
    exact ((((hw'.mul_right hyt).mul_right hw'.inv_right).mul_right hyt.inv_right)).symm
  let ψ := commHom t (W ⊓ centralizer ({y} : Set G)) (E ⊓ centralizer ({y} : Set G)) hFW hFt hT
  have hle : E ⊓ centralizer ({y} : Set G) ≤ W ⊓ centralizer ({y} : Set G) :=
    inf_le_inf_right _ h.E_le
  have hker : ψ.ker = (E ⊓ centralizer ({y} : Set G)).subgroupOf
      (W ⊓ centralizer ({y} : Set G)) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (w : G) * t = t * w := by
        have h4 : (w : G) * t * (w : G)⁻¹ = t := by
          rw [mul_inv_eq_one] at h2
          exact h2
        have h5 := mul_inv_eq_iff_eq_mul.1 h4
        exact h5
      exact ⟨h.mem_E_of_comm w.2.1 h3, w.2.2⟩
    · intro h1
      apply Subtype.ext
      show (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1
      rw [h.E_t _ h1.1]
      group
  have hsurj : Function.Surjective ψ := by
    rintro ⟨e, he1, he2⟩
    obtain ⟨w, hwW, hwy, hwe⟩ := h.lift he1 (mem_centralizer_singleton_iff.1 he2).symm
    exact ⟨⟨w, hwW, mem_centralizer_singleton_iff.2 hwy.symm⟩, Subtype.ext hwe⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hEy] at hcard
  omega

end WData

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
