module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.LiftData

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

omit [Finite G] in
theorem LiftData.ne_one_aux {f : Fin 4 → G} (hind : ∀ c c', mon4 f c = mon4 f c' → c = c')
    (i : Fin 4) : f i ≠ 1 := by
  intro hi
  have h1 : mon4 f (Pi.single i 1) = mon4 f 0 := by
    fin_cases i <;> (simp at hi; simp [mon4, hi, zmod_two_val_one])
  have h2 := congrFun (hind _ _ h1) i
  simp at h2

@[expose, instance_reducible] def lbadCommGroup (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (hbad : BadK z F) : CommGroup (LbadSub h hZ D X hbad) :=
  { (inferInstance : Group (LbadSub h hZ D X hbad)) with
    mul_comm := fun a b => Subtype.ext (lbad_comm h hZ D X hbad a.2 b.2) }

@[expose] def lbadPhi (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (hbad : BadK z F) : LbadSub h hZ D X hbad →* F :=
  (phiHom h D).comp (Subgroup.inclusion (lbad_le_Ksub h hZ D X hbad))

theorem coe_lbadPhi (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (hbad : BadK z F) (a : LbadSub h hZ D X hbad) :
    ((lbadPhi h hZ D X hbad a : F) : G) = phiv z (a : G) := rfl

@[expose] def lbadConj (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (hbad : BadK z F) {b : G} (hbL : b ∈ L) (hbF : ∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) :
    LbadSub h hZ D X hbad →* LbadSub h hZ D X hbad where
  toFun a := ⟨b * a * b⁻¹, lbad_conj h D hbL hbF a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a a' := Subtype.ext (by simp [mul_assoc])

theorem pow_natCast_val_four {M : Type*} [Monoid M] {x : M} (hx : x ^ 4 = 1) (n : ℕ) :
    x ^ ((n : ZMod 4).val) = x ^ n := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hx, one_pow, mul_one]

theorem badK_false (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hbad : BadK z F) (hlift : LiftData L F) : False := by
  obtain ⟨f, b₁, b₂, hf, hspan, hindf, hb₁L, hb₂L, hn₁, hn₂, hb₁sq, hb₂sq, hb₁₂, ha₁, ha₂⟩ :=
    hlift.exists_data
  have hf1 : ∀ i, f i ≠ 1 := LiftData.ne_one_aux hindf
  choose y hyΛ hyφ using fun i => exists_lbad_over h hZ D X htrans (hf i) (hf1 i)
  have hy2 : ∀ i, y i * y i = f i := fun i => by rw [lbad_sq h D (hyΛ i), hyφ i]
  let _ : CommGroup (LbadSub h hZ D X hbad) := lbadCommGroup h hZ D X hbad
  let Y : Fin 4 → LbadSub h hZ D X hbad := fun i => ⟨y i, hyΛ i⟩
  have hY2 : ∀ i, (((Y i) ^ 2 : LbadSub h hZ D X hbad) : G) = f i := fun i => by
    rw [Subgroup.coe_pow, pow_two]
    exact hy2 i
  have hexp : ∀ a : LbadSub h hZ D X hbad, a ^ 4 = 1 := by
    intro a
    apply Subtype.ext
    have h2 := lbad_sq h D a.2
    have hF := phiv_mem h D a.2.1
    show (a : G) ^ 4 = 1
    calc (a : G) ^ 4 = ((a : G) * (a : G)) * ((a : G) * (a : G)) := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (a : G), pow_two]
      _ = 1 := by rw [h2]; exact D.F_sq _ hF
  have hYcoe : ∀ i, ((Y i : LbadSub h hZ D X hbad) : G) = y i := fun i => rfl
  have hyf : ∀ i, y i ^ 2 = f i := fun i => by rw [pow_two]; exact hy2 i
  have hcoeProd : ∀ n : Fin 4 → ℕ, ((∏ i, Y i ^ n i : LbadSub h hZ D X hbad) : G) =
      y 0 ^ n 0 * y 1 ^ n 1 * y 2 ^ n 2 * y 3 ^ n 3 := by
    intro n
    rw [Fin.prod_univ_four]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hYcoe]
  have hphiY : ∀ i, ((lbadPhi h hZ D X hbad (Y i) : F) : G) = f i := fun i => by
    rw [coe_lbadPhi]
    exact hyφ i
  have hphiProd : ∀ n : Fin 4 → ℕ, ((lbadPhi h hZ D X hbad (∏ i, Y i ^ n i) : F) : G) =
      f 0 ^ n 0 * f 1 ^ n 1 * f 2 ^ n 2 * f 3 ^ n 3 := by
    intro n
    rw [Fin.prod_univ_four, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hphiY]
  have hgen : ∀ a : LbadSub h hZ D X hbad, ∃ c : Fin 4 → ZMod 4, a = ∏ i, Y i ^ (c i).val := by
    intro a
    obtain ⟨d, hd⟩ := hspan _ (phiv_mem h D a.2.1)
    have hW : ((lbadPhi h hZ D X hbad (∏ i, Y i ^ (d i).val) : F) : G) = mon4 f d :=
      hphiProd (fun i => (d i).val)
    have hV1 : phiv z ((a * (∏ i, Y i ^ (d i).val)⁻¹ : LbadSub h hZ D X hbad) : G) = 1 := by
      rw [← coe_lbadPhi h hZ D X hbad, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        hW, coe_lbadPhi, hd]
      exact mul_inv_cancel _
    obtain ⟨e, he⟩ := hspan _ (mem_F_of_lbad_phiv (a * (∏ i, Y i ^ (d i).val)⁻¹).2 hV1)
    have hU : (∏ i, Y i ^ (2 * (e i).val) : LbadSub h hZ D X hbad) =
        a * (∏ i, Y i ^ (d i).val)⁻¹ := by
      apply Subtype.ext
      rw [hcoeProd, he]
      simp only [mon4, pow_mul, hyf]
    refine ⟨fun i => ((2 * (e i).val + (d i).val : ℕ) : ZMod 4), ?_⟩
    have h1 : (∏ i, Y i ^ ((fun i => ((2 * (e i).val + (d i).val : ℕ) : ZMod 4)) i).val) =
        (∏ i, Y i ^ (2 * (e i).val)) * ∏ i, Y i ^ (d i).val := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_natCast_val_four (hexp (Y i)), pow_add]
    rw [h1, hU, inv_mul_cancel_right]
  have hindΛ : ∀ c c' : Fin 4 → ZMod 4,
      ∏ i, Y i ^ (c i).val = ∏ i, Y i ^ (c' i).val → c = c' := by
    have hsurj : Function.Surjective (fun c : Fin 4 → ZMod 4 => ∏ i, Y i ^ (c i).val) :=
      fun a => (hgen a).imp fun c hc => hc.symm
    have hcard : Nat.card (Fin 4 → ZMod 4) ≤ Nat.card (LbadSub h hZ D X hbad) := by
      rw [card_lbad h hZ D X htrans hbad]
      simp [Nat.card_eq_fintype_card]
    exact (hsurj.bijective_of_nat_card_le hcard).1
  let ρ₁ := lbadConj h hZ D X hbad hb₁L hn₁
  let ρ₂ := lbadConj h hZ D X hbad hb₂L hn₂
  have hρ₁ : ∀ a, ρ₁ (ρ₁ a) = a := fun a => Subtype.ext (by
    show b₁ * (b₁ * (a : G) * b₁⁻¹) * b₁⁻¹ = a
    calc b₁ * (b₁ * (a : G) * b₁⁻¹) * b₁⁻¹ = (b₁ * b₁) * (a : G) * (b₁ * b₁)⁻¹ := by group
      _ = a := by rw [hb₁sq]; group)
  have hρ₂ : ∀ a, ρ₂ (ρ₂ a) = a := fun a => Subtype.ext (by
    show b₂ * (b₂ * (a : G) * b₂⁻¹) * b₂⁻¹ = a
    calc b₂ * (b₂ * (a : G) * b₂⁻¹) * b₂⁻¹ = (b₂ * b₂) * (a : G) * (b₂ * b₂)⁻¹ := by group
      _ = a := by rw [hb₂sq]; group)
  have hρ₁₂ : ∀ a, ρ₁ (ρ₂ a) = ρ₂ (ρ₁ a) := fun a => Subtype.ext (by
    show b₁ * (b₂ * (a : G) * b₂⁻¹) * b₁⁻¹ = b₂ * (b₁ * (a : G) * b₁⁻¹) * b₂⁻¹
    calc b₁ * (b₂ * (a : G) * b₂⁻¹) * b₁⁻¹ = (b₁ * b₂) * (a : G) * (b₁ * b₂)⁻¹ := by group
      _ = (b₂ * b₁) * (a : G) * (b₂ * b₁)⁻¹ := by rw [hb₁₂]
      _ = _ := by group)
  have hm : ∀ (b : G) (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (ρ : LbadSub h hZ D X hbad →* _)
      (hρ : ∀ a, ((ρ a : LbadSub h hZ D X hbad) : G) = b * a * b⁻¹)
      (ha : ∀ i, b * f i * b⁻¹ = mon4 f (A i)) (k : Fin 4),
      ρ (Y k) ^ 2 = ∏ i, (Y i ^ 2) ^ (A k i).val := by
    intro b A ρ hρ ha k
    apply Subtype.ext
    rw [Subgroup.coe_pow, hρ, Fin.prod_univ_four]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hYcoe, hyf]
    calc (b * y k * b⁻¹) ^ 2 = b * y k ^ 2 * b⁻¹ := conj_pow
      _ = b * f k * b⁻¹ := by rw [hyf]
      _ = mon4 f (A k) := ha k
  exact no_bad_pair_group Y hexp hgen hindΛ ρ₁ ρ₂ hρ₁ hρ₂ hρ₁₂
    (hm b₁ liftA1 ρ₁ (fun a => rfl) ha₁) (hm b₂ liftA2 ρ₂ (fun a => rfl) ha₂)

end CFSG.EvenSporadicStandard.M23Std
