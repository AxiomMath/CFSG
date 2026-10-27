module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBTransferA
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBTrFacts

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB

theorem nfProd_replicate_false : ∀ (L : List MB) (n : ℕ), nfProd L (List.replicate n false) = 1
  | [], _ => by simp [nfProd]
  | _ :: _, 0 => by simp [nfProd]
  | _ :: gs, n + 1 => by simp [nfProd, List.replicate_succ, nfProd_replicate_false gs n]

theorem bitsQ1_one : bitsQ1 1 = List.replicate 7 false := by decide +kernel

theorem applyQ1_one (φ : List MB) : applyQ1 φ 1 = 1 := by
  rw [applyQ1, bitsQ1_one, nfProd_replicate_false]

theorem nfix_pos (φ : List MB) : 0 < nfix φ :=
  List.length_pos_of_mem (List.mem_filter.mpr ⟨by decide +kernel,
    beq_iff_eq.mpr (applyQ1_one φ)⟩)

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace R2Data

variable (R : B.R2Data)

theorem c_not_mem_S₁ : R.c ∉ B.G.D₁.S₁ := by
  intro hc
  obtain ⟨x, hx⟩ := B.exists_ι hc
  have h1 := c_conj_k R
  rw [← hx, ← B.ι_k, ← map_inv, ← map_mul, ← map_mul, ← (MB.center_mem x).2,
    mul_inv_cancel_right, B.ι_k] at h1
  exact z_ne_one S (by simpa using h1.symm)

theorem r2mul_spec (x y : MB × Bool) :
    (B.ι x.1 * R.cp x.2) * (B.ι y.1 * R.cp y.2) =
      B.ι (MB.r2mul R.j x y).1 * R.cp (MB.r2mul R.j x y).2 := by
  calc (B.ι x.1 * R.cp x.2) * (B.ι y.1 * R.cp y.2) =
      B.ι x.1 * (R.cp x.2 * B.ι y.1 * (R.cp x.2)⁻¹) * (R.cp x.2 * R.cp y.2) := by group
    _ = B.ι x.1 * B.ι (R.σp x.2 y.1) *
        (B.ι (if x.2 && y.2 then R.s₂ else 1) * R.cp (xor x.2 y.2)) := by
      rw [R.cp_conj, R.cp_mul_cp]
    _ = B.ι (x.1 * R.σp x.2 y.1 * (if x.2 && y.2 then R.s₂ else 1)) * R.cp (xor x.2 y.2) := by
      rw [map_mul, map_mul]
      simp only [mul_assoc]
    _ = _ := rfl

theorem nf_inj {x y : MB × Bool} (h : B.ι x.1 * R.cp x.2 = B.ι y.1 * R.cp y.2) : x = y := by
  obtain ⟨s, a⟩ := x
  obtain ⟨s', a'⟩ := y
  have key : ∀ s s' : MB, B.ι s ≠ B.ι s' * R.c := fun s s' h' => R.c_not_mem_S₁ (by
    have : R.c = B.ι (s'⁻¹ * s) := by rw [map_mul, h', map_inv]; group
    rw [this]; exact B.ι_mem_S₁ _)
  cases a <;> cases a' <;> simp only [cp, ite_false, ite_true, mul_one, Bool.false_eq_true]
    at h
  · rw [B.ι_injective h]
  · exact absurd h (key s s')
  · exact absurd h.symm (key s' s)
  · rw [B.ι_injective (mul_right_cancel h)]

theorem not_conjTo_of_R2 {s : MB} {a : Bool}
    (h64 : 64 ≤ (Finset.univ.filter fun s' : MB =>
      MB.r2mul R.j (s', false) (s, a) = MB.r2mul R.j (s, a) (s', false)).card)
    (hw : 0 < (Finset.univ.filter fun s' : MB =>
      MB.r2mul R.j (s', true) (s, a) = MB.r2mul R.j (s, a) (s', true)).card) :
    ¬ ConjTo t (B.ι s * R.cp a) := by
  classical
  set F := Finset.univ.filter fun s' : MB =>
    MB.r2mul R.j (s', false) (s, a) = MB.r2mul R.j (s, a) (s', false) with hF
  obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp hw
  have hs₁' := (Finset.mem_filter.mp hs₁).2
  set m := B.ι s * R.cp a with hm
  set g := B.ι s₁ * R.cp true with hg
  have hcp : R.cp false = 1 := rfl
  have hcomm : ∀ s' ∈ F, B.ι s' * m = m * B.ι s' := by
    intro s' hs'
    have h := (Finset.mem_filter.mp hs').2
    have e1 := R.r2mul_spec (s', false) (s, a)
    have e2 := R.r2mul_spec (s, a) (s', false)
    rw [h, ← e2, hcp, mul_one] at e1
    exact e1
  have hgc : g * m = m * g := by
    have e1 := R.r2mul_spec (s₁, true) (s, a)
    have e2 := R.r2mul_spec (s, a) (s₁, true)
    rw [hs₁', ← e2] at e1
    exact e1
  set K : Subgroup X := R.R2 ⊓ centralizer ({m} : Set X) with hK
  have hK2 : IsPGroup 2 K := R.isPGroup_R2.to_le inf_le_left
  have hmemK : ∀ x : X, x ∈ R.R2 → x * m = m * x → x ∈ K := fun x hx hxm =>
    ⟨hx, mem_centralizer_singleton_iff.mpr hxm⟩
  have hgR : ∀ β : Bool, (if β then g else 1) ∈ R.R2 := by
    intro β
    cases β
    · exact one_mem _
    · exact ⟨s₁, true, rfl⟩
  have hcomm' : ∀ s' ∈ F, ∀ β : Bool,
      B.ι s' * (if β then g else 1) * m = m * (B.ι s' * (if β then g else 1)) := by
    intro s' hs' β
    have h1 := hcomm s' hs'
    cases β
    · show B.ι s' * 1 * m = m * (B.ι s' * 1)
      rw [mul_one]
      exact h1
    · show B.ι s' * g * m = m * (B.ι s' * g)
      rw [mul_assoc, hgc, ← mul_assoc, h1, mul_assoc]
  let f : (F ×ˢ (Finset.univ : Finset Bool) : Finset (MB × Bool)) → K := fun x =>
    ⟨B.ι x.1.1 * (if x.1.2 then g else 1), hmemK _ (mul_mem (R.ι_mem_R2 _) (hgR x.1.2))
      (hcomm' x.1.1 (Finset.mem_product.mp x.2).1 x.1.2)⟩
  have hgS : ∀ u v : MB, B.ι u * g ≠ B.ι v := fun u v h => R.c_not_mem_S₁ (by
    have : R.c = B.ι (s₁⁻¹ * (u⁻¹ * v)) := by
      rw [map_mul, map_mul, map_inv, map_inv, ← h, hg]
      simp [cp]
    rw [this]; exact B.ι_mem_S₁ _)
  have hf : Function.Injective f := by
    rintro ⟨⟨s₂, β₂⟩, h₂⟩ ⟨⟨s₃, β₃⟩, h₃⟩ heq
    have heq' : B.ι s₂ * (if β₂ then g else 1) = B.ι s₃ * (if β₃ then g else 1) :=
      congrArg Subtype.val heq
    cases β₂ <;> cases β₃
    · have h' : B.ι s₂ = B.ι s₃ := by simpa using heq'
      obtain rfl := B.ι_injective h'
      rfl
    · have h' : B.ι s₂ = B.ι s₃ * g := by simpa using heq'
      exact absurd h'.symm (hgS s₃ s₂)
    · have h' : B.ι s₂ * g = B.ι s₃ := by simpa using heq'
      exact absurd h' (hgS s₂ s₃)
    · have h' : B.ι s₂ * g = B.ι s₃ * g := by simpa using heq'
      obtain rfl := B.ι_injective (mul_right_cancel h')
      rfl
  have hcard : 128 ≤ Nat.card K := by
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_finsetCard, Finset.card_product, Finset.card_univ, Fintype.card_bool] at h1
    omega
  exact KD8abC.not_conjTo_of_card S hK2 inf_le_right (by omega)

end R2Data

namespace T2Data

variable (D : B.T2Data)

@[expose] def M : Subgroup X := D.T2 ⊓ centralizer ({B.ι MB.aW} : Set X)

theorem t_mem_T2 : t ∈ D.T2 := by
  have := D.ι_mem_T2 MB.t
  rwa [B.ι_t] at this

theorem aW_conj {x : X} (hx : x ∈ D.T2) :
    x * B.ι MB.aW * x⁻¹ = B.ι MB.aW ∨ x * B.ι MB.aW * x⁻¹ = B.ι MB.aW * S.z := by
  have hzc : B.ι MB.aW * S.z = S.z * B.ι MB.aW := by
    rw [← B.ι_z, ← map_mul, ← map_mul, (MB.center_mem MB.aW).1]
  rcases D.comm_Z2 MB.aW_mem_Z2L hx with h | h
  · left
    calc x * B.ι MB.aW * x⁻¹ = (x * B.ι MB.aW * x⁻¹ * (B.ι MB.aW)⁻¹) * B.ι MB.aW := by group
      _ = B.ι MB.aW := by rw [h, one_mul]
  · right
    calc x * B.ι MB.aW * x⁻¹ = (x * B.ι MB.aW * x⁻¹ * (B.ι MB.aW)⁻¹) * B.ι MB.aW := by group
      _ = B.ι MB.aW * S.z := by rw [h, hzc]

theorem t_conj_aW : t * B.ι MB.aW * t⁻¹ = B.ι MB.aW * S.z := by
  have := congrArg B.ι MB.t_conj_aW
  rwa [map_mul, map_mul, map_inv, B.ι_t, map_mul, B.ι_z] at this

theorem relIndex_M : D.M.relIndex D.T2 = 2 := by
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨t, D.t_mem_T2⟩, fun b => ?_⟩
  have hb := b.2
  have hzb := D.conj_z_T2 hb
  have hne : B.ι MB.aW * S.z ≠ B.ι MB.aW := fun h => z_ne_one S (by simpa using h)
  have hmem : ∀ x : X, x ∈ D.T2 → (x ∈ D.M ↔ x * B.ι MB.aW * x⁻¹ = B.ι MB.aW) := by
    intro x hx
    rw [M, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩; rw [h, mul_inv_cancel_right]
    · intro h
      refine ⟨hx, ?_⟩
      calc x * B.ι MB.aW = (x * B.ι MB.aW * x⁻¹) * x := by group
        _ = B.ι MB.aW * x := by rw [h]
  have hbt : (b : X) * t * B.ι MB.aW * ((b : X) * t)⁻¹ =
      ((b : X) * B.ι MB.aW * (b : X)⁻¹) * S.z := by
    calc (b : X) * t * B.ι MB.aW * ((b : X) * t)⁻¹ =
        (b : X) * (t * B.ι MB.aW * t⁻¹) * (b : X)⁻¹ := by group
      _ = ((b : X) * B.ι MB.aW * (b : X)⁻¹) * ((b : X) * S.z * (b : X)⁻¹) := by
        rw [t_conj_aW (B := B)]; group
      _ = _ := by rw [hzb]
  simp only [mem_subgroupOf, coe_mul]
  rw [hmem _ hb, hmem _ (mul_mem hb D.t_mem_T2), hbt]
  rcases D.aW_conj hb with h | h <;> rw [h]
  · exact Or.inr ⟨rfl, hne⟩
  · refine Or.inl ⟨by rw [mul_assoc, zz S, mul_one], hne⟩

theorem not_conjTo_M : ∀ m ∈ D.M, ¬ ConjTo t m := by
  rintro m ⟨hmT, hmc⟩ hconj
  have hm2 := sq_of_conjTo (A := A) hconj
  replace hmc : m * B.ι MB.aW = B.ι MB.aW * m := mem_centralizer_singleton_iff.mp hmc
  obtain ⟨τ, hτ, hact, e, he, hme⟩ := D.exists_entry hmT
  have hφm := D.H4elt_mem τ.1 τ.2.1 τ.2.2
  have hφl := MB.H4elt_length D.hp τ.1 τ.2.1 τ.2.2
  have hfix : MB.applyQ1 (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) MB.aW = MB.aW := by
    apply B.ι_injective
    rw [← hact _ (MB.inQ1_of_inQC _ (MB.Z2L_inQC _ MB.aW_mem_Z2L)), hmc, mul_inv_cancel_right]
  have htr := List.all_eq_true.mp (MB.tr_facts D.p D.hp) _ (MB.mem_H4Zof D.hp hτ)
  simp only [MB.trCheck, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    Bool.and_eq_true, decide_eq_true_eq] at htr
  have hK2 : IsPGroup 2 (D.Nm m ⊓ centralizer ({m} : Set X) : Subgroup X) :=
    D.isPGroup_T2.to_le fun y hy => hy.1.1
  rcases htr with ((((h0 | hinner) | hb1) | hb2) | hb3) | ⟨hb, hok⟩
  · exact h0 hfix
  · obtain ⟨s, a, b⟩ := τ
    simp only [MB.innerT, Bool.and_eq_true, Bool.not_eq_true'] at hinner
    obtain ⟨⟨rfl, rfl⟩, hsQ⟩ := hinner
    have hm : m = B.ι (s * e) := by
      rw [hme, lift, map_mul]
      simp [R2Data.cp, qp]
    have hQ : MB.inQ1 (s * e) = true := mul_mem (show s ∈ MB.Q1h from hsQ)
      (show e ∈ MB.Q1h from MB.inQ1_of_inQC e (MB.inQC_of_inE0 e he))
    have hc : s * e * MB.aW = MB.aW * (s * e) := B.ι_injective (by
      rw [map_mul, map_mul (B.ι) MB.aW, ← hm, hmc])
    exact not_conjTo_A (MB.inQC_of_comm_aW _ hQ hc) (hm ▸ hconj)
  · apply hb1
    have h1 := hact.mul hact hφm
    rw [hm2] at h1
    exact h1.eq_list actsQ1_one (by simp [MB.compQ1, hφl]) MB.gensQ1_length
  · have hcard := D.card_Nm_centralizer hmT hm2 hτ hact
    have hn := MB.nfix_pos (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)
    have h1 : MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) * 64 <
        MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) *
          Nat.card (D.Nm m ⊓ centralizer ({m} : Set X) : Subgroup X) := by
      have : 64 * MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) <
          8 * (MB.commL D.p (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)).length := by omega
      rw [mul_comm]
      exact lt_of_lt_of_le this hcard
    exact KD8abC.not_conjTo_of_card S hK2 inf_le_right (Nat.lt_of_mul_lt_mul_left h1) hconj
  · obtain ⟨hle, hsq⟩ := hb3
    have hcard := D.card_Nm_centralizer hmT hm2 hτ hact
    have hn := MB.nfix_pos (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)
    have h1 : MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) * 64 ≤
        MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) *
          Nat.card (D.Nm m ⊓ centralizer ({m} : Set X) : Subgroup X) := by
      have : 64 * MB.nfix (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) ≤
          8 * (MB.commL D.p (MB.H4elt D.p τ.1 τ.2.1 τ.2.2)).length := by omega
      rw [mul_comm]
      exact this.trans hcard
    exact KD8abC.not_conjTo_of_exp4 S hK2 inf_le_right (Nat.le_of_mul_le_mul_left h1 hn)
      (fun g hg => D.pow_four hact hφl hφm hsq hg.1) hconj
  ·
    obtain ⟨s, a, b⟩ := τ
    simp only at hb
    subst hb
    have hj := D.hj
    have he₁ : MB.σpB D.R.j a e ∈ MB.E0L := by
      cases a
      · exact (MB.mem_E0L e).mp he
      · rw [hj]
        exact MB.E0L_σ D.p.1 (MB.goodIdx_fst D.p D.hp) e ((MB.mem_E0L e).mp he)
    have hm : m = B.ι (s * MB.σpB D.R.j a e) * D.R.cp a := by
      rw [hme]
      show B.ι s * D.R.cp a * 1 * B.ι e = _
      rw [mul_one]
      calc B.ι s * D.R.cp a * B.ι e = B.ι s * (D.R.cp a * B.ι e * (D.R.cp a)⁻¹) * D.R.cp a := by
            group
        _ = B.ι s * B.ι (D.R.σp a e) * D.R.cp a := by rw [D.R.cp_conj]
        _ = _ := by rw [map_mul]; rfl
    have hok' := List.all_eq_true.mp hok _ (hj ▸ he₁)
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_true, decide_eq_true_eq] at hok'
    rw [← hj] at hok'
    rcases hok' with hsq | ⟨h64, hw⟩
    · apply hsq
      apply D.R.nf_inj
      rw [← D.R.r2mul_spec, ← hm, hm2]
      simp [R2Data.cp]
    · rw [hm] at hconj
      exact D.R.not_conjTo_of_R2 h64 hw hconj

include D in
theorem false_of_transfer [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) : False :=
  KD8abC.false_of_transfer hX A.orderOf_t D.sylow (M := D.M) inf_le_left D.relIndex_M
    D.not_conjTo_M

end T2Data

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
