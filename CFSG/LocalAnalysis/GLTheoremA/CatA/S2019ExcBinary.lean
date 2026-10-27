module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

section Binary

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_fixedPointFree (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    {z : MulAut W} (hz : z ^ p = 1) {H : Subgroup W} (hH : H ≠ ⊥) (hzH : ∀ a ∈ H, z a ∈ H)
    (hfix : ∀ a ∈ H, z a = a → a = 1) : 2 ^ orderOf (2 : ZMod p) ≤ Nat.card H := by
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW H
  have hne : m ≠ 0 := by
    intro hm0
    apply hH
    rw [← Subgroup.card_eq_one, hm, hm0, pow_zero]
  let f : H → H := fun a => ⟨z a, hzH a a.2⟩
  have hiter : ∀ (n : ℕ) (a : H), ((f^[n] a : H) : W) = (z ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
  have hf : ∀ a, f^[p] a = a := by
    intro a
    apply Subtype.ext
    rw [hiter, hz]
    rfl
  have hmod := card_modEq_fix_prime p f hf
  have hfix1 : Nat.card {a : H | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one z)⟩⟩⟩
    have hone : ∀ c : {a : H | f a = a}, (c.1 : W) = 1 := fun c =>
      hfix _ c.1.2 (congrArg Subtype.val c.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [hone a, hone b]
  rw [hfix1, hm] at hmod
  have h2 : ((2 ^ m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  have h3 : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h3)

private noncomputable def resAut (H : Subgroup W) (g : MulAut W)
    (hg : H.map g.toMonoidHom = H) : MulAut ↥H :=
  (g.subgroupMap H).trans (MulEquiv.subgroupCongr hg)

private theorem resAut_apply (H : Subgroup W) (g : MulAut W) (hg : H.map g.toMonoidHom = H)
    (v : H) : ((resAut H g hg v : H) : W) = g v := rfl

private theorem map_eq_of_mapsTo {H : Subgroup W} {g : MulAut W} (h1 : ∀ a ∈ H, g a ∈ H)
    (h2 : ∀ a ∈ H, g⁻¹ a ∈ H) : H.map g.toMonoidHom = H := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact h1 b hb
  · intro ha
    refine ⟨g⁻¹ a, h2 a ha, ?_⟩
    change g (g⁻¹ a) = a
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

private theorem apply_mem_eigE_zero {x z g : MulAut W} (hgz : g * z = z * g) (hgx : g * x = x * g)
    {t : W} (ht : t ∈ eigE x z 0) : g t ∈ eigE x z 0 := by
  obtain ⟨htT, htx⟩ := mem_eigE.1 ht
  refine mem_eigE.2 ⟨apply_mem_imgT hgz htT, ?_⟩
  rw [pow_zero, mul_one] at htx ⊢
  have h := congrArg (fun h : MulAut W => h t) hgx
  simp only [MulAut.mul_apply] at h
  rw [← h, htx]

theorem two_pow_le_card_imgT_of_pairs {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    ∀ (e : ℕ) {W : Type} [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ (z : MulAut W) (x y : Fin e → MulAut W), z ^ p = 1 → z ≠ 1 →
        (∀ i, ExtraCfg p (x i) (y i) z) →
        (∀ i j, i ≠ j → x i * x j = x j * x i ∧ x i * y j = y j * x i ∧ y i * y j = y j * y i) →
        2 ^ (p ^ e * orderOf (2 : ZMod p)) ≤ Nat.card (imgT z) := by
  intro e
  induction e with
  | zero =>
    intro W _ _ hW z x y hz hz1 _ _
    rw [pow_zero, one_mul]
    refine two_pow_le_card_of_fixedPointFree hW hz ?_ (fun a ha => apply_mem_imgT rfl ha)
      (fun a ha hza => eq_one_of_mem_imgT_fixed hW hodd hz ha hza)
    intro hbot
    apply hz1
    ext v
    have hv : z v * v⁻¹ ∈ imgT z := mem_imgT.2 ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hv
    exact hv
  | succ e ih =>
    intro W _ _ hW z x y hz hz1 hcfg hcomm
    have h0 := hcfg 0
    set E₀ : Subgroup W := eigE (x 0) z 0 with hE₀
    have hle : Nat.card E₀ ^ p ≤ Nat.card (imgT z) := by
      have hrange : ∀ f, prodE (x 0) z p f ∈ imgT z := by
        intro f
        rw [prodE_apply]
        exact Subgroup.prod_mem _ fun j _ => (mem_eigE.1 (f j).2).1
      have hinj : Function.Injective
          ((prodE (x 0) z p).codRestrict (imgT z) hrange) := by
        intro a b hab
        exact prodE_injective h0 hW hodd (congrArg Subtype.val hab)
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_pi] at h1
      have h2 : ∏ j : Fin p, Nat.card (eigE (x 0) z j) = Nat.card E₀ ^ p := by
        rw [Finset.prod_congr rfl (fun j _ => h0.card_eigE_eq (le_of_lt j.2))]
        simp [hE₀]
      rw [h2] at h1
      exact h1
    have hE₀1 : E₀ ≠ ⊥ := by
      intro hbot
      obtain ⟨j, hj, hjne⟩ := h0.exists_eigE_ne_bot hW hodd
      apply hjne
      rw [← Subgroup.card_eq_one, h0.card_eigE_eq hj.le, ← hE₀, hbot, Subgroup.card_bot]
    have hinv : ∀ {g : MulAut W}, g * z = z * g → g * x 0 = x 0 * g →
        g⁻¹ * z = z * g⁻¹ ∧ g⁻¹ * x 0 = x 0 * g⁻¹ := by
      intro g hgz hgx
      constructor
      · rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgz, mul_assoc, mul_inv_cancel, mul_one]
      · rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgx, mul_assoc, mul_inv_cancel, mul_one]
    have hmap : ∀ {g : MulAut W}, g * z = z * g → g * x 0 = x 0 * g →
        E₀.map g.toMonoidHom = E₀ := by
      intro g hgz hgx
      obtain ⟨hgz', hgx'⟩ := hinv hgz hgx
      exact map_eq_of_mapsTo (fun a ha => apply_mem_eigE_zero hgz hgx ha)
        (fun a ha => apply_mem_eigE_zero hgz' hgx' ha)
    have hzz : z * z = z * z := rfl
    have hzx : z * x 0 = x 0 * z := h0.zx.symm
    have hxz : ∀ i : Fin e, x i.succ * z = z * x i.succ := fun i => (hcfg i.succ).zx
    have hyz : ∀ i : Fin e, y i.succ * z = z * y i.succ := fun i => (hcfg i.succ).zy
    have hxx : ∀ i : Fin e, x i.succ * x 0 = x 0 * x i.succ := fun i =>
      (hcomm i.succ 0 (Fin.succ_ne_zero i)).1
    have hyx : ∀ i : Fin e, y i.succ * x 0 = x 0 * y i.succ := fun i =>
      ((hcomm 0 i.succ (Fin.succ_ne_zero i).symm).2.1).symm
    set z' := resAut E₀ z (hmap hzz hzx) with hz'
    set x' : Fin e → MulAut ↥E₀ := fun i => resAut E₀ (x i.succ) (hmap (hxz i) (hxx i)) with hx'
    set y' : Fin e → MulAut ↥E₀ := fun i => resAut E₀ (y i.succ) (hmap (hyz i) (hyx i)) with hy'
    have hext : ∀ {a b : MulAut ↥E₀}, (∀ v : E₀, (a v : W) = b v) → a = b := fun h =>
      MulEquiv.ext fun v => Subtype.ext (h v)
    have hW' : ∀ w : E₀, w * w = 1 := fun w => Subtype.ext (hW w)
    have hz'p : z' ^ p = 1 := by
      apply hext
      intro v
      have : ∀ n : ℕ, ((z' ^ n) v : W) = (z ^ n) v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ihn => rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, ← ihn]; rfl
      rw [this, hz]
      rfl
    have hz'1 : z' ≠ 1 := by
      intro h
      obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE₀1
      apply hv1
      apply Subtype.ext
      change v = 1
      have h1 : z v = v := by
        have := congrArg (fun g : MulAut ↥E₀ => ((g ⟨v, hv⟩ : E₀) : W)) h
        simpa [hz', resAut_apply] using this
      exact eq_one_of_mem_imgT_fixed hW hodd hz (mem_eigE.1 hv).1 h1
    have happ : ∀ (a b : MulAut W) (v : W), (a * b) v = a (b v) := fun _ _ _ => rfl
    have hcfg' : ∀ i, ExtraCfg p (x' i) (y' i) z' := by
      intro i
      have hi := hcfg i.succ
      refine ⟨?_, hz'p, ?_, ?_, ?_, hz'1⟩
      · apply hext
        intro v
        have : ∀ n : ℕ, (((x' i) ^ n) v : W) = (x i.succ ^ n) v := by
          intro n
          induction n with
          | zero => rfl
          | succ n ihn =>
            rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, ← ihn]; rfl
        rw [this, hi.xp]
        rfl
      · apply hext
        intro v
        change x i.succ (z v) = z (x i.succ v)
        rw [← happ, hi.zx, happ]
      · apply hext
        intro v
        change y i.succ (z v) = z (y i.succ v)
        rw [← happ, hi.zy, happ]
      · apply hext
        intro v
        have hy1 : ∀ w : E₀, (((y' i)⁻¹ w : E₀) : W) = (y i.succ)⁻¹ w := by
          intro w
          have h1 : (y' i) ((y' i)⁻¹ w) = w := by
            rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
          have h2 : y i.succ (((y' i)⁻¹ w : E₀) : W) = w := congrArg Subtype.val h1
          rw [← h2, ← happ, inv_mul_cancel, MulAut.one_apply]
        change (((y' i)⁻¹ (x' i (y' i v)) : E₀) : W) = x i.succ (z v)
        rw [hy1]
        change (y i.succ)⁻¹ (x i.succ (y i.succ v)) = x i.succ (z v)
        rw [← happ, ← happ, hi.yx, happ]
    have hcomm' : ∀ i j, i ≠ j → x' i * x' j = x' j * x' i ∧ x' i * y' j = y' j * x' i ∧
        y' i * y' j = y' j * y' i := by
      intro i j hij
      obtain ⟨h1, h2, h3⟩ := hcomm i.succ j.succ (fun h => hij (Fin.succ_injective _ h))
      refine ⟨hext fun v => ?_, hext fun v => ?_, hext fun v => ?_⟩
      · change x i.succ (x j.succ v) = x j.succ (x i.succ v)
        rw [← happ, h1, happ]
      · change x i.succ (y j.succ v) = y j.succ (x i.succ v)
        rw [← happ, h2, happ]
      · change y i.succ (y j.succ v) = y j.succ (y i.succ v)
        rw [← happ, h3, happ]
    have hIH := ih hW' z' x' y' hz'p hz'1 hcfg' hcomm'
    have hcardE : 2 ^ (p ^ e * orderOf (2 : ZMod p)) ≤ Nat.card E₀ :=
      hIH.trans (Subgroup.card_le_card_group _)
    calc 2 ^ (p ^ (e + 1) * orderOf (2 : ZMod p))
        = (2 ^ (p ^ e * orderOf (2 : ZMod p))) ^ p := by
          rw [← pow_mul, pow_succ]
          ring_nf
      _ ≤ Nat.card E₀ ^ p := Nat.pow_le_pow_left hcardE p
      _ ≤ Nat.card (imgT z) := hle

end Binary

section Pairs

variable {E : Type} [Group E]

private def ecomm (x y : E) : E := x⁻¹ * y⁻¹ * x * y

private theorem ecomm_eq_one_iff {x y : E} : ecomm x y = 1 ↔ x * y = y * x := by
  unfold ecomm
  constructor
  · intro h
    calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
      _ = y * x := by rw [h, mul_one]
  · intro h
    calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
      _ = 1 := by rw [h]; group

private theorem conj_eq_of_ecomm {x y z : E} (h : ecomm x y = z) : y⁻¹ * x * y = x * z := by
  rw [← h]
  unfold ecomm
  group

private theorem ecomm_swap (x y : E) : ecomm y x = (ecomm x y)⁻¹ := by
  unfold ecomm
  group

private theorem ecomm_self (x : E) : ecomm x x = 1 := by
  unfold ecomm
  group

private theorem ecomm_one_right (x : E) : ecomm x 1 = 1 := by
  unfold ecomm
  group

private theorem ecomm_one_left (y : E) : ecomm 1 y = 1 := by
  unfold ecomm
  group

private theorem ecomm_mul_right (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x y y' : E) :
    ecomm x (y * y') = ecomm x y * ecomm x y' := by
  have h1 : y⁻¹ * x * y = x * ecomm x y := by unfold ecomm; group
  have hcen := Subgroup.mem_center_iff.1 (hc x y)
  calc ecomm x (y * y') = x⁻¹ * y'⁻¹ * (y⁻¹ * x * y) * y' := by unfold ecomm; group
    _ = x⁻¹ * y'⁻¹ * x * (ecomm x y * y') := by rw [h1]; group
    _ = x⁻¹ * y'⁻¹ * x * (y' * ecomm x y) := by rw [hcen y']
    _ = ecomm x y' * ecomm x y := by unfold ecomm; group
    _ = ecomm x y * ecomm x y' := hcen _

private theorem ecomm_mul_left (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x x' y : E) :
    ecomm (x * x') y = ecomm x y * ecomm x' y := by
  have h1 : x⁻¹ * y⁻¹ * x = ecomm x y * y⁻¹ := by unfold ecomm; group
  have hcen := Subgroup.mem_center_iff.1 (hc x y)
  calc ecomm (x * x') y = x'⁻¹ * (x⁻¹ * y⁻¹ * x) * x' * y := by unfold ecomm; group
    _ = (x'⁻¹ * ecomm x y) * (y⁻¹ * x' * y) := by rw [h1]; group
    _ = (ecomm x y * x'⁻¹) * (y⁻¹ * x' * y) := by rw [hcen x'⁻¹]
    _ = ecomm x y * ecomm x' y := by unfold ecomm; group

private theorem ecomm_inv_right (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x y : E) :
    ecomm x y⁻¹ = (ecomm x y)⁻¹ := by
  have h := ecomm_mul_right hc x y y⁻¹
  rw [mul_inv_cancel, ecomm_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem ecomm_inv_left (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x y : E) :
    ecomm x⁻¹ y = (ecomm x y)⁻¹ := by
  have h := ecomm_mul_left hc x x⁻¹ y
  rw [mul_inv_cancel, ecomm_one_left] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem ecomm_zpow_right (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x y : E)
    (n : ℤ) : ecomm x (y ^ n) = (ecomm x y) ^ n := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, zpow_zero, ecomm_one_right]
  | succ n ih => rw [zpow_add_one, ecomm_mul_right hc, ih, zpow_add_one]
  | pred n ih =>
    rw [zpow_sub_one, ecomm_mul_right hc, ih, ecomm_inv_right hc, zpow_sub_one]

private theorem ecomm_zpow_left (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) (x y : E)
    (n : ℤ) : ecomm (x ^ n) y = (ecomm x y) ^ n := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, zpow_zero, ecomm_one_left]
  | succ n ih => rw [zpow_add_one, ecomm_mul_left hc, ih, zpow_add_one]
  | pred n ih =>
    rw [zpow_sub_one, ecomm_mul_left hc, ih, ecomm_inv_left hc, zpow_sub_one]

private theorem exists_pairs [Finite E] {p : ℕ} [Fact p.Prime]
    (hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E) {z : E} (hz : z ∈ Subgroup.center E)
    (hzp : z ^ p = 1) (hz1 : z ≠ 1) (hrange : ∀ x y : E, ecomm x y ∈ Subgroup.zpowers z) :
    ∀ (k : ℕ) (F : Subgroup E), z ∈ F → Nat.card F = p ^ (1 + 2 * k) →
      (∀ x ∈ F, x ∉ Subgroup.zpowers z → ∃ y ∈ F, ecomm x y = z) →
      ∃ x y : Fin k → E, (∀ i, x i ∈ F ∧ y i ∈ F) ∧ (∀ i, ecomm (x i) (y i) = z) ∧
        ∀ i j, i ≠ j → x i * x j = x j * x i ∧ x i * y j = y j * x i ∧ y i * y j = y j * y i := by
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzo]
  intro k
  induction k with
  | zero =>
    intro F _ _ _
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro F hzF hcard hnd
    obtain ⟨x, hxF, hxz⟩ : ∃ x ∈ F, x ∉ Subgroup.zpowers z := by
      by_contra hcon
      push Not at hcon
      have hle : Nat.card F ≤ Nat.card (Subgroup.zpowers z) :=
        Subgroup.card_le_of_le (fun g hg => hcon g hg)
      rw [hcard, hzcard] at hle
      have hp1 := (Fact.out : p.Prime).one_lt
      have : p ^ 1 < p ^ (1 + 2 * (k + 1)) := Nat.pow_lt_pow_right hp1 (by omega)
      rw [pow_one] at this
      omega
    obtain ⟨y, hyF, hxy⟩ := hnd x hxF hxz
    let F' : Subgroup E := F ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {y}
    have hF'F : F' ≤ F := fun g hg => hg.1.1
    have hmemF' : ∀ g, g ∈ F' ↔ g ∈ F ∧ ecomm g x = 1 ∧ ecomm g y = 1 := by
      intro g
      simp only [F', Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, ecomm_eq_one_iff]
      tauto
    let θ : F →* E × E :=
      { toFun := fun g => (ecomm (g : E) x, ecomm (g : E) y)
        map_one' := by rw [Subgroup.coe_one, ecomm_one_left, ecomm_one_left]; rfl
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul, ecomm_mul_left hc, Prod.mk_mul_mk] }
    have hθ : ∀ g : F, θ g = (ecomm (g : E) x, ecomm (g : E) y) := fun g => rfl
    have hker : ∀ g : F, g ∈ θ.ker ↔ (g : E) ∈ F' := by
      intro g
      rw [MonoidHom.mem_ker, hmemF', hθ, Prod.mk_eq_one]
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    have hrangeθ : θ.range = (Subgroup.zpowers z).prod (Subgroup.zpowers z) := by
      apply le_antisymm
      · rintro _ ⟨g, rfl⟩
        rw [hθ]
        exact ⟨hrange _ _, hrange _ _⟩
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        refine ⟨⟨y ^ (-m) * x ^ n, F.mul_mem (F.zpow_mem hyF _) (F.zpow_mem hxF _)⟩, ?_⟩
        rw [hθ]
        change (ecomm (y ^ (-m) * x ^ n) x, ecomm (y ^ (-m) * x ^ n) y) = (z ^ m, z ^ n)
        rw [ecomm_mul_left hc, ecomm_mul_left hc, ecomm_zpow_left hc, ecomm_zpow_left hc,
          ecomm_zpow_left hc, ecomm_zpow_left hc, ecomm_swap x y, hxy, ecomm_self, ecomm_self,
          one_zpow, one_zpow, mul_one, one_mul, inv_zpow', neg_neg]
    have hcardF : Nat.card F = Nat.card F' * p ^ 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hrangeθ,
        Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hzcard] at h1
      have h2 : Nat.card θ.ker = Nat.card F' :=
        Nat.card_congr
          { toFun := fun g => ⟨((g : F) : E), (hker g).1 g.2⟩
            invFun := fun g => ⟨⟨g, hF'F g.2⟩, (hker _).2 g.2⟩
            left_inv := fun g => rfl
            right_inv := fun g => rfl }
      rw [h1, h2, sq, mul_comm]
    have hcardF' : Nat.card F' = p ^ (1 + 2 * k) := by
      have hp0 : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
      have h1 : Nat.card F' * p ^ 2 = p ^ (1 + 2 * k) * p ^ 2 := by
        rw [← hcardF, hcard, ← pow_add]
        ring_nf
      exact Nat.eq_of_mul_eq_mul_right hp0 h1
    have hzF' : z ∈ F' := (hmemF' z).2 ⟨hzF,
      ecomm_eq_one_iff.2 (Subgroup.mem_center_iff.1 hz x).symm,
      ecomm_eq_one_iff.2 (Subgroup.mem_center_iff.1 hz y).symm⟩
    have hnd' : ∀ x' ∈ F', x' ∉ Subgroup.zpowers z → ∃ y' ∈ F', ecomm x' y' = z := by
      intro x' hx' hx'z
      obtain ⟨hx'F, hx'x, hx'y⟩ := (hmemF' x').1 hx'
      obtain ⟨y'', hy''F, hx'y''⟩ := hnd x' hx'F hx'z
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hrange x y'')
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hrange y y'')
      refine ⟨y'' * x ^ m * y ^ (-n), ?_, ?_⟩
      · refine (hmemF' _).2 ⟨F.mul_mem (F.mul_mem hy''F (F.zpow_mem hxF _)) (F.zpow_mem hyF _),
          ?_, ?_⟩
        · rw [ecomm_swap, ecomm_mul_right hc, ecomm_mul_right hc, ecomm_zpow_right hc,
            ecomm_zpow_right hc, hxy, ← hn, ecomm_self, one_zpow, mul_one, zpow_neg,
            mul_inv_cancel, inv_one]
        · rw [ecomm_swap, ecomm_mul_right hc, ecomm_mul_right hc, ecomm_zpow_right hc,
            ecomm_zpow_right hc, ecomm_swap x y, hxy, ← hm, ecomm_self, one_zpow, mul_one,
            inv_zpow', zpow_neg, mul_inv_cancel, inv_one]
      · rw [ecomm_mul_right hc, ecomm_mul_right hc, ecomm_zpow_right hc, ecomm_zpow_right hc,
          hx'y'', hx'x, hx'y, one_zpow, one_zpow, mul_one, mul_one]
    obtain ⟨xs, ys, hmem, hrel, hcross⟩ := ih F' hzF' hcardF' hnd'
    have hxs : ∀ i, (xs i ∈ F ∧ ecomm (xs i) x = 1 ∧ ecomm (xs i) y = 1) := fun i =>
      (hmemF' _).1 (hmem i).1
    have hys : ∀ i, (ys i ∈ F ∧ ecomm (ys i) x = 1 ∧ ecomm (ys i) y = 1) := fun i =>
      (hmemF' _).1 (hmem i).2
    have cx : ∀ i, x * xs i = xs i * x := fun i => (ecomm_eq_one_iff.1 (hxs i).2.1).symm
    have cy : ∀ i, y * xs i = xs i * y := fun i => (ecomm_eq_one_iff.1 (hxs i).2.2).symm
    have dx : ∀ i, x * ys i = ys i * x := fun i => (ecomm_eq_one_iff.1 (hys i).2.1).symm
    have dy : ∀ i, y * ys i = ys i * y := fun i => (ecomm_eq_one_iff.1 (hys i).2.2).symm
    refine ⟨Fin.cons x xs, Fin.cons y ys, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hxF, hyF⟩ (fun i => ⟨(hxs i).1, (hys i).1⟩) i
    · intro i
      refine Fin.cases hxy (fun i => hrel i) i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨cx j, dx j, dy j⟩
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨(cx i).symm, (cy i).symm, (dy i).symm⟩
        | succ j =>
          simp only [Fin.cons_succ]
          exact hcross i j (fun h => hij (by rw [h]))

end Pairs

theorem two_pow_le_card_of_extraspecial {E : Type} [Group E] [Finite E] {p e : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hE : CFSG.IsExtraspecialPGroup p E) (hexp : ∀ g : E, g ^ p = 1)
    (hcard : Nat.card E = p ^ (1 + 2 * e)) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (φ : E →* MulAut W) {z : E} (hz : z ∈ Subgroup.center E)
    (hφz : φ z ≠ 1) : 2 ^ (p ^ e * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  obtain ⟨-, hcomm, -, hZp⟩ := hE
  have hz1 : z ≠ 1 := fun h => hφz (by rw [h, map_one])
  have hzp : z ^ p = 1 := hexp z
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hZ : Subgroup.zpowers z = Subgroup.center E := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
    rw [hZp, Nat.card_zpowers, hzo]
  have hc : ∀ x y : E, ecomm x y ∈ Subgroup.center E := by
    intro x y
    rw [← hcomm]
    have : ecomm x y = ⁅x⁻¹, y⁻¹⁆ := by rw [commutatorElement_def]; unfold ecomm; group
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hrange : ∀ x y : E, ecomm x y ∈ Subgroup.zpowers z := fun x y => hZ ▸ hc x y
  have hnd : ∀ x ∈ (⊤ : Subgroup E), x ∉ Subgroup.zpowers z →
      ∃ y ∈ (⊤ : Subgroup E), ecomm x y = z := by
    intro x _ hx
    rw [hZ, Subgroup.mem_center_iff] at hx
    push Not at hx
    obtain ⟨y₀, hy₀⟩ := hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hrange x y₀)
    have hw1 : z ^ n ≠ 1 := by
      rw [hn]
      intro h
      exact hy₀ (ecomm_eq_one_iff.1 h).symm
    have hwo : orderOf (z ^ n) = p :=
      orderOf_eq_prime (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hzp, one_zpow]) hw1
    have hle : Subgroup.zpowers (z ^ n) ≤ Subgroup.zpowers z :=
      Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers z n)
    have heq : Subgroup.zpowers (z ^ n) = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hzo])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ Subgroup.mem_zpowers z)
    refine ⟨y₀ ^ m, Subgroup.mem_top _, ?_⟩
    rw [ecomm_zpow_right hc, ← hn, hm]
  obtain ⟨x, y, -, hrel, hcross⟩ := exists_pairs hc hz hzp hz1 hrange e ⊤
    (Subgroup.mem_top z) (by rw [Subgroup.card_top, hcard]) hnd
  have hcen : ∀ g : E, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hcfg : ∀ i, ExtraCfg p (φ (x i)) (φ (y i)) (φ z) := by
    intro i
    refine ⟨by rw [← map_pow, hexp, map_one], by rw [← map_pow, hzp, map_one], ?_, ?_, ?_, hφz⟩
    · rw [← map_mul, ← map_mul, hcen]
    · rw [← map_mul, ← map_mul, hcen]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, conj_eq_of_ecomm (hrel i)]
  have hcross' : ∀ i j, i ≠ j → φ (x i) * φ (x j) = φ (x j) * φ (x i) ∧
      φ (x i) * φ (y j) = φ (y j) * φ (x i) ∧ φ (y i) * φ (y j) = φ (y j) * φ (y i) := by
    intro i j hij
    obtain ⟨h1, h2, h3⟩ := hcross i j hij
    exact ⟨by rw [← map_mul, ← map_mul, h1], by rw [← map_mul, ← map_mul, h2],
      by rw [← map_mul, ← map_mul, h3]⟩
  exact (two_pow_le_card_imgT_of_pairs hodd e hW (φ z) (fun i => φ (x i)) (fun i => φ (y i))
    (by rw [← map_pow, hzp, map_one]) hφz hcfg hcross').trans (Subgroup.card_le_card_group _)

end CFSG.LocalAnalysis.GLTheoremA.S2019
