module

public import CFSG.Quasithin.Background.SmithB45ExcSylow

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

structure HeisCfg {G : Type*} [Group G] (p n : ℕ) (x y : Fin n → G) (z : G) : Prop where
  xp : ∀ i, x i ^ p = 1
  zp : z ^ p = 1
  zx : ∀ i, x i * z = z * x i
  zy : ∀ i, y i * z = z * y i
  yx : ∀ i, (y i)⁻¹ * x i * y i = x i * z
  xx : ∀ i j, x i * x j = x j * x i
  yy : ∀ i j, i ≠ j → y i * y j = y j * y i
  xy : ∀ i j, i ≠ j → x i * y j = y j * x i
  z1 : z ≠ 1

section Basic

variable {G : Type*} [Group G] {p n : ℕ}

theorem HeisCfg.tail {x y : Fin (n + 1) → G} {z : G} (h : HeisCfg p (n + 1) x y z) :
    HeisCfg p n (fun i => x i.succ) (fun i => y i.succ) z where
  xp _ := h.xp _
  zp := h.zp
  zx _ := h.zx _
  zy _ := h.zy _
  yx _ := h.yx _
  xx _ _ := h.xx _ _
  yy _ _ hij := h.yy _ _ fun e => hij (Fin.succ_injective _ e)
  xy _ _ hij := h.xy _ _ fun e => hij (Fin.succ_injective _ e)
  z1 := h.z1

theorem HeisCfg.ofSubgroup {H : Type*} [Group H] {x y : Fin n → G} {z : G} (S : Subgroup G)
    (f : ↥S →* H) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hz : z ∈ S)
    (h : HeisCfg p n x y z) (hfz : f ⟨z, hz⟩ ≠ 1) :
    HeisCfg p n (fun i => f ⟨x i, hx i⟩) (fun i => f ⟨y i, hy i⟩) (f ⟨z, hz⟩) where
  xp i := by
    rw [← map_pow, show (⟨x i, hx i⟩ : S) ^ p = 1 from Subtype.ext (by simpa using h.xp i),
      map_one]
  zp := by
    rw [← map_pow, show (⟨z, hz⟩ : S) ^ p = 1 from Subtype.ext (by simpa using h.zp), map_one]
  zx i := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (h.zx i))
  zy i := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (h.zy i))
  yx i := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (by simpa using h.yx i))
  xx i j := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (h.xx i j))
  yy i j hij := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (h.yy i j hij))
  xy i j hij := by
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (h.xy i j hij))
  z1 := hfz

end Basic

section Core

variable {W : Type} [CommGroup W] {p : ℕ}

theorem HeisCfg.extraCfg {n : ℕ} {x y : Fin (n + 1) → MulAut W} {z : MulAut W}
    (h : HeisCfg p (n + 1) x y z) : ExtraCfg p (x 0) (y 0) z :=
  ⟨h.xp 0, h.zp, h.zx 0, h.zy 0, h.yx 0, h.z1⟩

theorem two_pow_le_card_imgT_of_zp [Finite W] [Fact p.Prime] (hW : ∀ w : W, w * w = 1)
    (hodd : Odd p) {z : MulAut W} (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card (imgT z) := by
  have hT : ∃ t ∈ imgT z, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hz1
    ext v
    have := hcon (z v * v⁻¹) (mem_imgT.2 ⟨v, rfl⟩)
    rw [mul_inv_eq_one] at this
    simpa using this
  let f : imgT z → imgT z := fun a => ⟨z a, apply_mem_imgT rfl a.2⟩
  have hiter : ∀ (n : ℕ) (a : imgT z), ((f^[n] a : imgT z) : W) = (z ^ n) a := by
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
  have hfix : Nat.card {a : imgT z | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one z)⟩⟩⟩
    have hone : ∀ c : {a : imgT z | f a = a}, (c.1 : W) = 1 := by
      intro c
      have h1 : z (c.1 : W) = c.1 := congrArg Subtype.val c.2
      exact eq_one_of_mem_imgT_fixed hW hodd hz c.1.2 h1
    apply Subtype.ext
    apply Subtype.ext
    rw [hone a, hone b]
  rw [hfix] at hmod
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW (imgT z)
  have hne : m ≠ 0 := by
    intro hm0
    obtain ⟨t, ht, ht1⟩ := hT
    have h1 : Nat.card (imgT z) = 1 := by rw [hm, hm0, pow_zero]
    exact ht1 (by simpa using (Subgroup.card_eq_one.1 h1 ▸ ht : t ∈ (⊥ : Subgroup W)))
  rw [hm] at hmod
  have h2 : ((2 ^ m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  have h3 : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h3)

theorem eigE_zero_ne_bot_of_extraCfg [Finite W] [Fact p.Prime] {x y z : MulAut W}
    (h : ExtraCfg p x y z) (hW : ∀ w : W, w * w = 1) (hodd : Odd p) : eigE x z 0 ≠ ⊥ := by
  obtain ⟨j, hj, hne⟩ := h.exists_eigE_ne_bot hW hodd
  intro h0
  apply hne
  have hc := h.card_eigE_eq hj.le
  rw [h0, Subgroup.card_bot] at hc
  exact Subgroup.card_eq_one.1 hc

theorem mem_stabSub_eigE {x z g : MulAut W} (hgz : g * z = z * g) (hgx : g * x = x * g) :
    g ∈ stabSub (eigE x z 0) := by
  have key : ∀ g : MulAut W, g * z = z * g → g * x = x * g →
      ∀ t ∈ eigE x z 0, g t ∈ eigE x z 0 := by
    intro g hgz hgx t ht
    obtain ⟨hT, hx⟩ := mem_eigE.1 ht
    refine mem_eigE.2 ⟨apply_mem_imgT hgz hT, ?_⟩
    simp only [pow_zero, mul_one] at hx ⊢
    have h1 := congrArg (fun m : MulAut W => m t) hgx
    simp only [MulAut.mul_apply, hx] at h1
    exact h1.symm
  intro u
  constructor
  · intro hu
    have hgz' : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
    have hgx' : g⁻¹ * x = x * g⁻¹ := (Commute.inv_left (show Commute g x from hgx)).eq
    have := key g⁻¹ hgz' hgx' (g u) hu
    simpa using this
  · exact key g hgz hgx u

def HeisBound (p n : ℕ) : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ {x y : Fin n → MulAut W} {z : MulAut W}, HeisCfg p n x y z →
      2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card (imgT z)

theorem two_pow_le_card_eigE_of_bound [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hn : HeisBound p n)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {x y : Fin (n + 1) → MulAut W} {z : MulAut W} (h : HeisCfg p (n + 1) x y z) :
    2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card (eigE (x 0) z 0) := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hx0 : ∀ i : Fin n, x i.succ * x 0 = x 0 * x i.succ := fun i => h.xx _ _
  have hxs : ∀ i : Fin n, x i.succ ∈ stabSub (eigE (x 0) z 0) := fun i =>
    mem_stabSub_eigE (h.zx _) (h.xx _ _)
  have hys : ∀ i : Fin n, y i.succ ∈ stabSub (eigE (x 0) z 0) := fun i =>
    mem_stabSub_eigE (h.zy _) (h.xy 0 _ (Fin.succ_ne_zero i).symm).symm
  have hzs : z ∈ stabSub (eigE (x 0) z 0) := mem_stabSub_eigE rfl (h.zx 0).symm
  have hE0 : eigE (x 0) z 0 ≠ ⊥ := eigE_zero_ne_bot_of_extraCfg h.extraCfg hW hodd
  have hfz : resHom (eigE (x 0) z 0) ⟨z, hzs⟩ ≠ 1 := by
    intro hf1
    apply hE0
    rw [eq_bot_iff]
    intro e he
    have hze : z e = e := congrArg (fun φ : MulAut ↥(eigE (x 0) z 0) => ((φ ⟨e, he⟩ : W))) hf1
    exact Subgroup.mem_bot.2 (eq_one_of_mem_imgT_fixed hW hodd h.zp (mem_eigE.1 he).1 hze)
  have h' := HeisCfg.ofSubgroup (stabSub (eigE (x 0) z 0)) (resHom (eigE (x 0) z 0)) hxs hys hzs
    h.tail hfz
  have hW' : ∀ w : ↥(eigE (x 0) z 0), w * w = 1 := fun w => Subtype.ext (by simpa using hW w)
  exact (hn hW' h').trans (Subgroup.card_le_card_group _)

theorem heisBound [Fact p.Prime] (hp2 : p ≠ 2) : ∀ n : ℕ, HeisBound p n := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  intro n
  induction n with
  | zero =>
    unfold HeisBound
    intro W _ _ hW x y z h
    simpa using two_pow_le_card_imgT_of_zp hW hodd h.zp h.z1
  | succ n ih =>
    unfold HeisBound
    intro W _ _ hW x y z h
    have hA := two_pow_le_card_eigE_of_bound hp2 ih hW h
    have hcard := B45Exc.card_range_prodE_of_cfg h.extraCfg hW hodd
    have hle : Nat.card (prodE (x 0) z p).range ≤ Nat.card (imgT z) :=
      Subgroup.card_le_of_le B45Exc.range_prodE_le_imgT
    calc 2 ^ (p ^ (n + 1) * orderOf (2 : ZMod p)) = (2 ^ (p ^ n * orderOf (2 : ZMod p))) ^ p := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ Nat.card (eigE (x 0) z 0) ^ p := Nat.pow_le_pow_left hA p
      _ = Nat.card (prodE (x 0) z p).range := hcard.symm
      _ ≤ Nat.card (imgT z) := hle

theorem two_pow_le_card_imgT_of_heisCfg {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {x y : Fin n → MulAut W} {z : MulAut W} (h : HeisCfg p n x y z) :
    2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card (imgT z) :=
  heisBound hp2 n hW h

theorem index_fixV_le_sq_of_inverts [Finite W] {p : ℕ} (hodd : Odd p) {x t : MulAut W}
    (hx : x ^ p = 1) (ht : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) :
    (fixV (Subgroup.zpowers x)).index ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  obtain ⟨m, hm⟩ := hodd
  set y : MulAut W := x ^ (m + 1) with hy
  have hty : t * y * t⁻¹ = y⁻¹ := by
    rw [hy, ← conj_pow, htx, inv_pow]
  have h1 : t * y⁻¹ * t⁻¹ = y := by
    rw [show t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ by group, hty, inv_inv]
  have hyy : y * y = x := by
    rw [hy, ← pow_add, show m + 1 + (m + 1) = p + 1 by omega, pow_succ, hx, one_mul]
  have hyt : y * t * y⁻¹ = x * t := by
    calc y * t * y⁻¹ = y * (t * y⁻¹ * t⁻¹) * t := by group
      _ = y * y * t := by rw [h1]
      _ = x * t := by rw [hyy]
  have hst : (x * t) * t = x := by rw [mul_assoc, ht, mul_one]
  calc (fixV (Subgroup.zpowers x)).index = (fixV (Subgroup.zpowers ((x * t) * t))).index := by
        rw [hst]
    _ ≤ (fixV (Subgroup.zpowers (x * t))).index * (fixV (Subgroup.zpowers t)).index :=
        index_fixV_mul_le _ _
    _ = (fixV (Subgroup.zpowers t)).index * (fixV (Subgroup.zpowers t)).index := by
        rw [← hyt, index_fixV_conj]
    _ = (fixV (Subgroup.zpowers t)).index ^ 2 := (sq _).symm

theorem two_pow_le_index_sq_of_heisCfg {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {x y : Fin (n + 1) → MulAut W} {z : MulAut W} (h : HeisCfg p (n + 1) x y z) {t : MulAut W}
    (ht : t * t = 1) (htx : t * x 0 * t⁻¹ = (x 0)⁻¹) :
    2 ^ ((p - 1) * p ^ n * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hA := two_pow_le_card_eigE_of_bound hp2 (heisBound hp2 n) hW h
  have hB := B45Exc.card_pow_le_index_of_cfg h.extraCfg hW hodd
  have hC := index_fixV_le_sq_of_inverts hodd (h.xp 0) ht htx
  calc 2 ^ ((p - 1) * p ^ n * orderOf (2 : ZMod p))
      = (2 ^ (p ^ n * orderOf (2 : ZMod p))) ^ (p - 1) := by
        rw [← pow_mul]; congr 1; ring
    _ ≤ Nat.card (eigE (x 0) z 0) ^ (p - 1) := Nat.pow_le_pow_left hA _
    _ ≤ (fixV (Subgroup.zpowers (x 0))).index := hB
    _ ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := hC

end Core

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
