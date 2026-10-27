module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

variable {W : Type} [CommGroup W] {p : ℕ}

theorem apply_eq_of_mem_zpowers_of_mem_eigE {x₀ z g : MulAut W}
    (hg : g ∈ Subgroup.zpowers x₀) {t : W} (ht : t ∈ eigE x₀ z 0) : g t = t := by
  have h1 : t ∈ fixV (Subgroup.zpowers (x₀ * z ^ 0)) := (Subgroup.mem_inf.1 ht).2
  rw [pow_zero, mul_one] at h1
  exact mem_fixV.1 h1 g hg

theorem two_pow_le_card_imgT_of_relHeis [Finite W] (hW : ∀ w : W, w * w = 1) [Fact p.Prime]
    (hp2 : p ≠ 2) {n : ℕ} {x₀ y₀ z : MulAut W} (h₀ : ExtraCfg p x₀ y₀ z)
    {x y : Fin n → MulAut W} (hx₀ : ∀ i, x i * x₀ = x₀ * x i) (hy₀ : ∀ i, y i * x₀ = x₀ * y i)
    (hzx : ∀ i, x i * z = z * x i) (hzy : ∀ i, y i * z = z * y i) (hxp : ∀ i, x i ^ p = 1)
    (hyx : ∀ i, (y i)⁻¹ * x i * y i = x i * z)
    (hxx : ∀ i j, x i * x j * (x j * x i)⁻¹ ∈ Subgroup.zpowers x₀)
    (hyy : ∀ i j, i ≠ j → y i * y j * (y j * y i)⁻¹ ∈ Subgroup.zpowers x₀)
    (hxy : ∀ i j, i ≠ j → x i * y j * (y j * x i)⁻¹ ∈ Subgroup.zpowers x₀) :
    2 ^ (p ^ (n + 1) * orderOf (2 : ZMod p)) ≤ Nat.card (imgT z) := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  set E := eigE x₀ z 0 with hE
  have hxs : ∀ i, x i ∈ stabSub E := fun i => mem_stabSub_eigE (hzx i) (hx₀ i)
  have hys : ∀ i, y i ∈ stabSub E := fun i => mem_stabSub_eigE (hzy i) (hy₀ i)
  have hzs : z ∈ stabSub E := mem_stabSub_eigE rfl h₀.zx.symm
  have hE0 : E ≠ ⊥ := eigE_zero_ne_bot_of_extraCfg h₀ hW hodd
  set f := resHom E with hf
  have key : ∀ a b : stabSub E, (a : MulAut W) * (b : MulAut W)⁻¹ ∈ Subgroup.zpowers x₀ →
      f a = f b := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by
      ext u
      exact apply_eq_of_mem_zpowers_of_mem_eigE hab u.2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  have hexact : ∀ a b : stabSub E, (a : MulAut W) = (b : MulAut W) → f a = f b :=
    fun a b hab => congrArg f (Subtype.ext hab)
  have hcfg : HeisCfg p n (fun i => f ⟨x i, hxs i⟩) (fun i => f ⟨y i, hys i⟩) (f ⟨z, hzs⟩) :=
    { xp := fun i => by
        rw [← map_pow, show (⟨x i, hxs i⟩ : stabSub E) ^ p = 1 from
          Subtype.ext (by simpa using hxp i), map_one]
      zp := by
        rw [← map_pow, show (⟨z, hzs⟩ : stabSub E) ^ p = 1 from
          Subtype.ext (by simpa using h₀.zp), map_one]
      zx := fun i => by
        rw [← map_mul, ← map_mul]
        exact hexact _ _ (hzx i)
      zy := fun i => by
        rw [← map_mul, ← map_mul]
        exact hexact _ _ (hzy i)
      yx := fun i => by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
        exact hexact _ _ (by simpa using hyx i)
      xx := fun i j => by
        rw [← map_mul, ← map_mul]
        exact key _ _ (by simpa using hxx i j)
      yy := fun i j hij => by
        rw [← map_mul, ← map_mul]
        exact key _ _ (by simpa using hyy i j hij)
      xy := fun i j hij => by
        rw [← map_mul, ← map_mul]
        exact key _ _ (by simpa using hxy i j hij)
      z1 := by
        intro hf1
        apply hE0
        rw [eq_bot_iff]
        intro e he
        have hze : z e = e :=
          congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : W))) hf1
        exact Subgroup.mem_bot.2 (eq_one_of_mem_imgT_fixed hW hodd h₀.zp (mem_eigE.1 he).1 hze) }
  have hW' : ∀ w : ↥E, w * w = 1 := fun w => Subtype.ext (by simpa using hW w)
  have hA : 2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card E :=
    (two_pow_le_card_imgT_of_heisCfg hW' hp2 hcfg).trans (Subgroup.card_le_card_group _)
  have hcard := B45Exc.card_range_prodE_of_cfg h₀ hW hodd
  have hle : Nat.card (prodE x₀ z p).range ≤ Nat.card (imgT z) :=
    Subgroup.card_le_of_le B45Exc.range_prodE_le_imgT
  calc 2 ^ (p ^ (n + 1) * orderOf (2 : ZMod p)) = (2 ^ (p ^ n * orderOf (2 : ZMod p))) ^ p := by
        rw [← pow_mul]; congr 1; ring
    _ ≤ Nat.card E ^ p := Nat.pow_le_pow_left hA p
    _ = Nat.card (prodE x₀ z p).range := hcard.symm
    _ ≤ Nat.card (imgT z) := hle

theorem two_pow_le_card_of_relHeis [Finite W] (hW : ∀ w : W, w * w = 1) [Fact p.Prime]
    (hp2 : p ≠ 2) {n : ℕ} {x₀ y₀ z : MulAut W} (h₀ : ExtraCfg p x₀ y₀ z)
    {x y : Fin n → MulAut W} (hx₀ : ∀ i, x i * x₀ = x₀ * x i) (hy₀ : ∀ i, y i * x₀ = x₀ * y i)
    (hzx : ∀ i, x i * z = z * x i) (hzy : ∀ i, y i * z = z * y i) (hxp : ∀ i, x i ^ p = 1)
    (hyx : ∀ i, (y i)⁻¹ * x i * y i = x i * z)
    (hxx : ∀ i j, x i * x j * (x j * x i)⁻¹ ∈ Subgroup.zpowers x₀)
    (hyy : ∀ i j, i ≠ j → y i * y j * (y j * y i)⁻¹ ∈ Subgroup.zpowers x₀)
    (hxy : ∀ i j, i ≠ j → x i * y j * (y j * x i)⁻¹ ∈ Subgroup.zpowers x₀) :
    2 ^ (p ^ (n + 1) * orderOf (2 : ZMod p)) ≤ Nat.card W :=
  (two_pow_le_card_imgT_of_relHeis hW hp2 h₀ hx₀ hy₀ hzx hzy hxp hyx hxx hyy hxy).trans
    (Subgroup.card_le_card_group _)

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
