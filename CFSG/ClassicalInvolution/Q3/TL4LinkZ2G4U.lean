module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4Red
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UH
public import Certificates.Certificate416201
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UA
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Arr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C
open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M CFSG.Sporadic.SmallOddCore

@[expose] def SpCore (y : Equiv.Perm (Fin 820)) : Prop :=
  y * u0P = u0P * y ∧ y * v0P = v0P * y ∧ y * y = 1 ∧
    (∃ x ∈ L1P, y * u1P = x * y) ∧ (∃ x ∈ L1P, y * v1P = x * y) ∧
      ∀ x ∈ L1P, y * x = x * y → x = 1 ∨ x = r0P

theorem spW_iff {w : List (Array ℕ)} {g : Equiv.Perm (Fin 820)} (hw : RepW 820 w g) {t : Array ℕ}
    {T : Equiv.Perm (Fin 820)} (ht : Rep 820 t T) :
    spW t (u0A ()) (v0A ()) (u1A ()) (v1A ()) (r0A ()) (q8A 820 (r0A ()) (u1A ()) (v1A ())) w =
        true ↔ SpCore (g * T) := by
  have hy : RepW 820 (t :: w) (g * T) := RepW.cons ht hw
  have hL : List.Forall₂ (Rep 820) (q8A 820 (r0A ()) (u1A ()) (v1A ())) L1P :=
    forall₂_q8A rep_r0 rep_u1 rep_v1
  have hany : ∀ (a : Array ℕ) (A : Equiv.Perm (Fin 820)), Rep 820 a A →
      (((q8A 820 (r0A ()) (u1A ()) (v1A ())).any fun x => twW a x (t :: w)) = true ↔
        ∃ x ∈ L1P, g * T * A = x * (g * T)) := by
    intro a A ha
    rw [any_eq_of_forall₂ hL (g := fun x => decide (g * T * A = x * (g * T))) fun b B hbB => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact twW_iff hy ha hbB]
    simp
  have hall : (((q8A 820 (r0A ()) (u1A ()) (v1A ())).all fun x =>
      !twW x x (t :: w) || eqA 820 x (idA 820) || eqA 820 x (r0A ())) = true ↔
        ∀ x ∈ L1P, g * T * x = x * (g * T) → x = 1 ∨ x = r0P) := by
    rw [all_eq_of_forall₂ hL (g := fun x => decide (g * T * x = x * (g * T) → x = 1 ∨ x = r0P))
      fun b B hbB => by
        have e1 : twW b b (t :: w) = decide (g * T * B = B * (g * T)) := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff]
          exact twW_iff hy hbB hbB
        rw [e1, eqA_eq hbB rep_idA, eqA_eq hbB rep_r0]
        by_cases h1 : g * T * B = B * (g * T) <;> by_cases h2 : B = 1 <;>
          by_cases h3 : B = r0P <;> simp [h1, h2, h3]]
    simp only [List.all_eq_true, decide_eq_true_eq]
  rw [spW, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, twW_iff hy rep_u0 rep_u0, twW_iff hy rep_v0 rep_v0, allLt_sq_iff hy,
    hany _ _ rep_u1, hany _ _ rep_v1, hall, SpCore]
  simp only [and_assoc]

theorem forall_lt_eight_of_all_map {f : ℕ → ℕ}
    (h : ((List.range 8).map f).all (fun c => c == 0) = true) : ∀ k < 8, f k = 0 := by
  simpa only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply,
    beq_iff_eq] using h

theorem sp_none
    {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) {k : ℕ} (hk : k < 8) : ¬ SpCore (g * tP k) := by
  classical
  have h := forall_lt_eight_of_all_map (f := fun k => countW (spW (tArr k) (u0A ()) (v0A ())
    (u1A ()) (v1A ()) (r0A ()) (q8A 820 (r0A ()) (u1A ()) (v1A ()))) blocks [])
    Certificates.certificate416201
  have hc := card_eq_countW_P (Pr := fun g => SpCore (g * tP k))
    (fun w g hw _ => spW_iff hw (rep_tArr k))
  have hc0 := hc.trans (h k hk)
  intro hcfg
  have : Nonempty {x : P // SpCore ((x : Equiv.Perm (Fin 820)) * tP k)} := ⟨⟨⟨g, hg⟩, hcfg⟩⟩
  have := Nat.card_pos (α := {x : P // SpCore ((x : Equiv.Perm (Fin 820)) * tP k)})
  omega

theorem false_of_sPHyp_PSU
    {S : Type} [Group S]
    (hS : CFSG.Blueprint.LieModel S .PSU 4 3 1) {A B : Subgroup S} {r : S} {x : MulAut S}
    (h : SPHyp A B r x) : False := by
  obtain ⟨θ⟩ := nonempty_mulEquiv_P hS
  set φ : S →* Equiv.Perm (Fin 820) := P.subtype.comp θ.toMonoidHom with hφdef
  have hφinj : Function.Injective φ := Subtype.val_injective.comp θ.injective
  have hφP : ∀ s, φ s ∈ P := fun s => (θ s).2
  have hφsurj : ∀ p ∈ P, ∃ s, φ s = p := fun p hp =>
    ⟨θ.symm ⟨p, hp⟩, by simp [hφdef]⟩
  have hrange : φ.range = P := le_antisymm (by rintro _ ⟨s, rfl⟩; exact hφP s) fun p hp => by
    obtain ⟨s, hs⟩ := hφsurj p hp
    exact ⟨s, hs⟩
  obtain ⟨q, hq, hqB⟩ := h.twin
  obtain ⟨ρ, hρR, hρ⟩ := autModel.surj (MulAut.congr θ x)
  have hρφ : ∀ s, φ (x s) = ρ * φ s * ρ⁻¹ := fun s => by
    have h1 := hρ (θ s)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hdP : Vtx.AmbientQuatDatum P (A.map φ) (φ r) := by
    have h1 := Vtx.ambientQuatDatum_map φ hφinj h.quat
    rwa [hrange] at h1
  have hqr : φ q * φ r = φ r * φ q := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hq]
  have hB' : conjSub (φ q) (A.map φ) = B.map φ := by rw [conjSub_map, hqB]
  have hρ2 : ρ * ρ = 1 := autModel.inj _ (R.mul_mem hρR hρR) fun p hp => by
    obtain ⟨s, rfl⟩ := hφsurj p hp
    calc ρ * ρ * φ s = ρ * (ρ * φ s * ρ⁻¹) * ρ⁻¹ * (ρ * ρ) := by group
      _ = φ (x (x s)) * (ρ * ρ) := by rw [← hρφ, ← hρφ]
      _ = φ s * (ρ * ρ) := by rw [h.apply_apply]
  obtain ⟨c, hc, hcr, hcK⟩ := exists_conj_K0 hdP
  have hd0 : Vtx.AmbientQuatDatum P K0 r0P := by
    have h1 := hdP.conj hc
    rwa [hcr, hcK] at h1
  have hBK : conjSub (c * φ q * c⁻¹) K0 = conjSub c (B.map φ) := by
    rw [← hcK, conjSub_conj, hB']
  have hK1 : conjSub c (B.map φ) = K1 := by
    rw [← hBK]
    refine twin_eq_K1 hd0 (P.mul_mem (P.mul_mem hc (hφP q)) (P.inv_mem hc)) ?_ ?_
    · rw [← hcr]
      exact (comm_conj_iff c (φ q) (φ r)).2 hqr
    · rw [hBK, ← hcK]
      exact fun h1 => h.ne (Subgroup.map_injective hφinj
        (CFSG.ClassicalInvolution.Generic.conjSub_injective c h1))
  have hinvB : IsUniqueInvolution (B.map φ) (φ r) := by
    have h1 := hdP.inv.conj (φ q)
    rwa [hB', show φ q * φ r * (φ q)⁻¹ = φ r by rw [hqr, mul_inv_cancel_right]] at h1
  have hinvK1 : IsUniqueInvolution K1 r0P := by
    have h1 := hinvB.conj c
    rwa [hK1, hcr] at h1
  set ρ' := c * ρ * c⁻¹ with hρ'def
  have hρ'R : ρ' ∈ R := R.mul_mem (R.mul_mem (P_le_R hc) hρR) (R.inv_mem (P_le_R hc))
  have hρ'conj : ∀ s, ρ' * (c * φ s * c⁻¹) * ρ'⁻¹ = c * φ (x s) * c⁻¹ := fun s => by
    rw [hρ'def, hρφ]
    group
  have hcomm : ∀ s, x s = s → ρ' * (c * φ s * c⁻¹) = c * φ s * c⁻¹ * ρ' := fun s hs => by
    have h1 := hρ'conj s
    rw [hs] at h1
    calc ρ' * (c * φ s * c⁻¹) = ρ' * (c * φ s * c⁻¹) * ρ'⁻¹ * ρ' := by group
      _ = c * φ s * c⁻¹ * ρ' := by rw [h1]
  have hK0mem : ∀ y ∈ K0, ∃ a ∈ A, y = c * φ a * c⁻¹ := by
    intro y hy
    rw [← hcK] at hy
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hy
    exact ⟨a, ha, rfl⟩
  have hK1mem : ∀ y ∈ K1, ∃ b ∈ B, y = c * φ b * c⁻¹ := by
    intro y hy
    rw [← hK1] at hy
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hy
    exact ⟨b, hb, rfl⟩
  have hcK0 : ∀ y ∈ K0, ρ' * y = y * ρ' := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := hK0mem y hy
    exact hcomm a (h.fixA a ha)
  have hnK1 : ∀ y ∈ K1, ∃ z ∈ L1P, ρ' * y = z * ρ' := fun y hy => by
    obtain ⟨b, hb, rfl⟩ := hK1mem y hy
    refine ⟨c * φ (x b) * c⁻¹, (mem_K1_iff _).1 ?_, ?_⟩
    · rw [← hK1]
      exact CFSG.ClassicalInvolution.Generic.conj_mem_conjSub
        (Subgroup.mem_map_of_mem φ (h.normB b hb))
    · rw [← hρ'conj, inv_mul_cancel_right]
  have hcore : SpCore ρ' := by
    refine ⟨hcK0 _ u0_mem_K0, hcK0 _ v0_mem_K0, ?_, hnK1 _ u1_mem_K1, hnK1 _ v1_mem_K1, ?_⟩
    · rw [hρ'def, show c * ρ * c⁻¹ * (c * ρ * c⁻¹) = c * (ρ * ρ) * c⁻¹ by group, hρ2]
      group
    · intro y hyL hy
      have hyK1 : y ∈ K1 := (mem_K1_iff y).2 hyL
      obtain ⟨b, hb, rfl⟩ := hK1mem _ hyK1
      have hfix : x b = b := by
        have h1 := hρ'conj b
        rw [show ρ' * (c * φ b * c⁻¹) * ρ'⁻¹ = c * φ b * c⁻¹ by rw [hy, mul_inv_cancel_right]] at h1
        exact hφinj (by simpa using h1.symm)
      have hbb := h.cB b hb hfix
      exact hinvK1.unique _ hyK1 (by
        rw [show c * φ b * c⁻¹ * (c * φ b * c⁻¹) = c * φ (b * b) * c⁻¹ by rw [map_mul]; group,
          hbb, map_one]
        group)
  obtain ⟨g', hg', k, hk, hρ'eq⟩ := mem_R_iff.1 hρ'R
  exact sp_none hg' hk (hρ'eq ▸ hcore)

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
