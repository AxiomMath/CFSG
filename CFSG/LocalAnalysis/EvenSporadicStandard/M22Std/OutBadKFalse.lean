module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutBadK
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.BadKExclude

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

omit [Finite G] in
theorem phiv_one_eq (h : OutOne L z F) : phiv z (1 : G) = 1 := by
  unfold phiv
  simp [h.z_mul_self]

theorem lbad_le_Ksub (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z)
    (X : FixedData L F) (hbad : BadK z F) :
    LbadSub h hsq X hbad ≤ Ksub z F := fun _ hk => hk.1

theorem card_lbad (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hbad : BadK z F) : Nat.card (LbadSub h hsq X hbad) = 256 := by
  let ψ : LbadSub h hsq X hbad →* F :=
    (phiHomO h).comp (Subgroup.inclusion (lbad_le_Ksub h hsq X hbad))
  have hψ : ∀ x : LbadSub h hsq X hbad, ((ψ x : F) : G) = phiv z (x : G) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    by_cases hf1 : f = 1
    · refine ⟨1, Subtype.ext ?_⟩
      rw [hψ]
      exact (phiv_one_eq h).trans hf1.symm
    · obtain ⟨k, hk, hkf⟩ := exists_lbad_over h hsq X htrans hf hf1
      exact ⟨⟨k, hk⟩, Subtype.ext (by rw [hψ]; exact hkf)⟩
  have hker : Nat.card ψ.ker = 16 := by
    rw [← h.F_card]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ψ.ker => (⟨(x.1 : G), ?_⟩ : F)) ⟨?_, ?_⟩)
    · have h1 : phiv z (x.1 : G) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        rwa [hψ] at this
      exact mem_F_of_lbad_phiv x.1.2 h1
    · intro x y hxy
      have h1 : ((x.1 : LbadSub h hsq X hbad) : G) = ((y.1 : LbadSub h hsq X hbad) : G) :=
        congrArg (fun e : F => (e : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      refine ⟨⟨⟨u, F_le_LbadSub h hsq X hbad hu⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (by rw [hψ]; exact phiv_eq_one_of_mem_F h hu)
  have := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, h.F_card] at this
  omega

@[expose, instance_reducible] def lbadCommGroup (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (hbad : BadK z F) : CommGroup (LbadSub h hsq X hbad) :=
  { (inferInstance : Group (LbadSub h hsq X hbad)) with
    mul_comm := fun a b => Subtype.ext (lbad_comm h hsq X hbad a.2 b.2) }

@[expose] def lbadPhi (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (hbad : BadK z F) : LbadSub h hsq X hbad →* F :=
  (phiHomO h).comp (Subgroup.inclusion (lbad_le_Ksub h hsq X hbad))

theorem coe_lbadPhi (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (hbad : BadK z F) (a : LbadSub h hsq X hbad) :
    ((lbadPhi h hsq X hbad a : F) : G) = phiv z (a : G) := rfl

@[expose] def lbadConj (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (hbad : BadK z F) {b : G} (hbL : b ∈ L) (hbF : ∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) :
    LbadSub h hsq X hbad →* LbadSub h hsq X hbad where
  toFun a := ⟨b * a * b⁻¹, lbad_conj h hbL hbF a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a a' := Subtype.ext (by simp [mul_assoc])

theorem badK_false (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hbad : BadK z F) (hlift : LiftData L F) : False := by
  obtain ⟨f, b₁, b₂, hf, hspan, hindf, hb₁L, hb₂L, hn₁, hn₂, hb₁sq, hb₂sq, hb₁₂, ha₁, ha₂⟩ :=
    hlift.exists_data
  have hf1 : ∀ i, f i ≠ 1 := LiftData.ne_one_aux hindf
  choose y hyΛ hyφ using fun i => exists_lbad_over h hsq X htrans (hf i) (hf1 i)
  have hy2 : ∀ i, y i * y i = f i := fun i => by rw [lbad_sq h (hyΛ i), hyφ i]
  let _ : CommGroup (LbadSub h hsq X hbad) := lbadCommGroup h hsq X hbad
  let Y : Fin 4 → LbadSub h hsq X hbad := fun i => ⟨y i, hyΛ i⟩
  have hY2 : ∀ i, (((Y i) ^ 2 : LbadSub h hsq X hbad) : G) = f i := fun i => by
    rw [Subgroup.coe_pow, pow_two]
    exact hy2 i
  have hexp : ∀ a : LbadSub h hsq X hbad, a ^ 4 = 1 := by
    intro a
    apply Subtype.ext
    have h2 := lbad_sq h a.2
    have hF := phiv_mem h a.2.1
    show (a : G) ^ 4 = 1
    calc (a : G) ^ 4 = ((a : G) * (a : G)) * ((a : G) * (a : G)) := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (a : G), pow_two]
      _ = 1 := by rw [h2]; exact h.F_sq _ hF
  have hYcoe : ∀ i, ((Y i : LbadSub h hsq X hbad) : G) = y i := fun i => rfl
  have hyf : ∀ i, y i ^ 2 = f i := fun i => by rw [pow_two]; exact hy2 i
  have hcoeProd : ∀ n : Fin 4 → ℕ, ((∏ i, Y i ^ n i : LbadSub h hsq X hbad) : G) =
      y 0 ^ n 0 * y 1 ^ n 1 * y 2 ^ n 2 * y 3 ^ n 3 := by
    intro n
    rw [Fin.prod_univ_four]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hYcoe]
  have hphiY : ∀ i, ((lbadPhi h hsq X hbad (Y i) : F) : G) = f i := fun i => by
    rw [coe_lbadPhi]
    exact hyφ i
  have hphiProd : ∀ n : Fin 4 → ℕ, ((lbadPhi h hsq X hbad (∏ i, Y i ^ n i) : F) : G) =
      f 0 ^ n 0 * f 1 ^ n 1 * f 2 ^ n 2 * f 3 ^ n 3 := by
    intro n
    rw [Fin.prod_univ_four, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hphiY]
  have hgen : ∀ a : LbadSub h hsq X hbad, ∃ c : Fin 4 → ZMod 4, a = ∏ i, Y i ^ (c i).val := by
    intro a
    obtain ⟨d, hd⟩ := hspan _ (phiv_mem h a.2.1)
    have hW : ((lbadPhi h hsq X hbad (∏ i, Y i ^ (d i).val) : F) : G) = mon4 f d :=
      hphiProd (fun i => (d i).val)
    have hV1 : phiv z ((a * (∏ i, Y i ^ (d i).val)⁻¹ : LbadSub h hsq X hbad) : G) = 1 := by
      rw [← coe_lbadPhi h hsq X hbad, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        hW, coe_lbadPhi, hd]
      exact mul_inv_cancel _
    obtain ⟨e, he⟩ := hspan _ (mem_F_of_lbad_phiv (a * (∏ i, Y i ^ (d i).val)⁻¹).2 hV1)
    have hU : (∏ i, Y i ^ (2 * (e i).val) : LbadSub h hsq X hbad) =
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
    have hcard : Nat.card (Fin 4 → ZMod 4) ≤ Nat.card (LbadSub h hsq X hbad) := by
      rw [card_lbad h hsq X htrans hbad]
      simp [Nat.card_eq_fintype_card]
    exact (hsurj.bijective_of_nat_card_le hcard).1
  let ρ₁ := lbadConj h hsq X hbad hb₁L hn₁
  let ρ₂ := lbadConj h hsq X hbad hb₂L hn₂
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
  have hm : ∀ (b : G) (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (ρ : LbadSub h hsq X hbad →* _)
      (hρ : ∀ a, ((ρ a : LbadSub h hsq X hbad) : G) = b * a * b⁻¹)
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

end OutOne

end CFSG.EvenSporadicStandard.M22Std
