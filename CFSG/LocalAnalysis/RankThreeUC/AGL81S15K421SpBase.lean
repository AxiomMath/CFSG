module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bTrans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Mono

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421BaseProof

open CFSG.Open K421MonoProof

structure MonoBase {G : Type} [Group G] (D : Mono81 G) : Type where
  B : Subgroup G
  A0_le : D.A0 ≤ B
  comm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b
  sig_mem : ∀ b ∈ B, D.s * b * D.s⁻¹ ∈ B
  exp3 : ∀ b ∈ B, b ^ 3 = 1 → b ∈ D.A0
  hilbert : ∀ u ∈ B, u * (D.s * u * D.s⁻¹) * (D.s * (D.s * u * D.s⁻¹) * D.s⁻¹) = 1 →
    ∃ v ∈ B, u = v * (D.s * v * D.s⁻¹)⁻¹

variable {G : Type} [Group G] {D : Mono81 G}

theorem MonoBase.sigPow_mem (M : MonoBase D) (k : ℕ) {b : G} (hb : b ∈ M.B) :
    D.s ^ k * b * (D.s ^ k)⁻¹ ∈ M.B := by
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := M.sig_mem _ ih
    have e : D.s ^ (k + 1) * b * (D.s ^ (k + 1))⁻¹ = D.s * (D.s ^ k * b * (D.s ^ k)⁻¹) * D.s⁻¹ := by
      group
    rw [e]
    exact h

theorem MonoBase.exists_conj_le_A0 (M : MonoBase D) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hER : ∀ g ∈ E, ∃ b ∈ M.B, ∃ k : ℕ, g = b * D.s ^ k) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ D.A0 := by
  classical
  by_cases hEB : ∀ g ∈ E, g ∈ M.B
  · refine ⟨1, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have h3 : e ^ 3 = 1 := hE.2 e he
    have := M.exp3 e (hEB e he) h3
    simpa using this
  · obtain ⟨g0, hg0E, hg0B⟩ : ∃ g0 ∈ E, g0 ∉ M.B := by
      by_contra h
      exact hEB (fun g hg => by_contra fun hn => h ⟨g, hg, hn⟩)
    obtain ⟨b0, hb0, k0, rfl⟩ := hER g0 hg0E
    have hk : k0 % 3 = 1 ∨ k0 % 3 = 2 := by
      by_contra hcon
      have h0 : k0 % 3 = 0 := by omega
      apply hg0B
      rw [D.s_pow_mod, h0, pow_zero, mul_one]
      exact hb0
    obtain ⟨u, hu, hg1⟩ : ∃ u ∈ M.B, u * D.s ∈ E := by
      rcases hk with h1 | h2
      · refine ⟨b0, hb0, ?_⟩
        rw [D.s_pow_mod, h1, pow_one] at hg0E
        exact hg0E
      · have hg0E' : b0 * D.s ^ 2 ∈ E := by
          rw [D.s_pow_mod, h2] at hg0E
          exact hg0E
        have hs4 : D.s ^ 4 = D.s := by
          rw [D.s_pow_mod]
          norm_num
        have hs2 : D.s ^ 2 * b0 * (D.s ^ 2)⁻¹ ∈ M.B := M.sigPow_mem 2 hb0
        refine ⟨b0 * (D.s ^ 2 * b0 * (D.s ^ 2)⁻¹), M.B.mul_mem hb0 hs2, ?_⟩
        have e : (b0 * D.s ^ 2) ^ 2 = b0 * (D.s ^ 2 * b0 * (D.s ^ 2)⁻¹) * D.s := by
          calc (b0 * D.s ^ 2) ^ 2 = b0 * (D.s ^ 2 * b0 * (D.s ^ 2)⁻¹) * D.s ^ 4 := by
                rw [pow_two]
                group
            _ = b0 * (D.s ^ 2 * b0 * (D.s ^ 2)⁻¹) * D.s := by rw [hs4]
        rw [← e]
        exact E.pow_mem hg0E' 2
    have hs3 : D.s ^ 3 = 1 := D.s_pow
    have hcube : u * (D.s * u * D.s⁻¹) * (D.s * (D.s * u * D.s⁻¹) * D.s⁻¹) = 1 := by
      have h3 : (u * D.s) ^ 3 = 1 := hE.2 _ hg1
      have h3' : (u * D.s) ^ 3 = u * D.s * u * D.s * u * D.s := by
        rw [pow_succ, pow_two]
        group
      calc u * (D.s * u * D.s⁻¹) * (D.s * (D.s * u * D.s⁻¹) * D.s⁻¹)
          = (u * D.s * u * D.s * u * D.s) * (D.s ^ 3)⁻¹ := by group
        _ = 1 := by rw [← h3', h3, hs3]; simp
    obtain ⟨v, hv, huv⟩ := M.hilbert u hu hcube
    have hg1' : u * D.s = v * D.s * v⁻¹ := by
      rw [huv]
      group
    set E' : Subgroup G := E.map (MulAut.conj v⁻¹).toMonoidHom with hE'
    have hE'ab : IsElemAbelian 3 E' :=
      K21bTransProof.isElemAbelian_map_inj (MulAut.conj v⁻¹).injective hE
    have hsE' : D.s ∈ E' := ⟨u * D.s, hg1, by
      show v⁻¹ * (u * D.s) * v⁻¹⁻¹ = D.s
      rw [hg1']
      group⟩
    have hE'R : E' ≤ D.R0 := by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨b, hb, k, hek⟩ := hER e he
      have hconjE : (MulAut.conj v⁻¹).toMonoidHom e = v⁻¹ * e * v := by
        show v⁻¹ * e * v⁻¹⁻¹ = v⁻¹ * e * v
        simp
      rw [hconjE, hek]
      obtain ⟨b', hb'⟩ : ∃ b' : G, b' = v⁻¹ * b * (D.s ^ k * v * (D.s ^ k)⁻¹) := ⟨_, rfl⟩
      have hb'B : b' ∈ M.B := by
        rw [hb']
        exact M.B.mul_mem (M.B.mul_mem (M.B.inv_mem hv) hb) (M.sigPow_mem k hv)
      have e1 : v⁻¹ * (b * D.s ^ k) * v = b' * D.s ^ k := by
        rw [hb']
        group
      rw [e1]
      have hmem : b' * D.s ^ k ∈ E' := by
        rw [← e1, ← hek]
        exact ⟨e, he, hconjE⟩
      have hcomm : D.s * (b' * D.s ^ k) = (b' * D.s ^ k) * D.s :=
        congrArg Subtype.val (hE'ab.1.is_comm.comm ⟨D.s, hsE'⟩ ⟨b' * D.s ^ k, hmem⟩)
      have hsb : D.s * b' = b' * D.s := by
        have h1 : D.s * b' * D.s ^ k = b' * D.s * D.s ^ k := by
          calc D.s * b' * D.s ^ k = D.s * (b' * D.s ^ k) := by rw [mul_assoc]
            _ = (b' * D.s ^ k) * D.s := hcomm
            _ = b' * (D.s ^ k * D.s) := by rw [mul_assoc]
            _ = b' * (D.s * D.s ^ k) := by rw [(Commute.self_pow D.s k).eq.symm]
            _ = b' * D.s * D.s ^ k := by rw [mul_assoc]
        exact mul_right_cancel h1
      have hcommk : Commute b' (D.s ^ k) := by
        have : Commute b' D.s := hsb.symm
        exact this.pow_right k
      have hb'3 : b' ^ 3 = 1 := by
        have h3 : (b' * D.s ^ k) ^ 3 = 1 := hE'ab.2 _ hmem
        rw [hcommk.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hs3, one_pow, mul_one] at h3
        exact h3
      obtain ⟨x, hx⟩ := D.mem_A0_iff.1 (M.exp3 b' hb'B hb'3)
      exact ⟨x, k, by rw [hx]⟩
    rcases D.exists_conj_le_A0 hE'R hE'ab with hA | ⟨-, g', hg'⟩
    · exact ⟨v⁻¹, hA⟩
    · refine ⟨g' * v⁻¹, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have := hg' (Subgroup.mem_map.mpr ⟨(MulAut.conj v⁻¹) z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩)
      have h1 : (MulAut.conj (g' * v⁻¹)) z = (MulAut.conj g') ((MulAut.conj v⁻¹) z) := by
        simp [MulAut.conj_apply, mul_assoc]
      show (MulAut.conj (g' * v⁻¹)) z ∈ D.A0
      rw [h1]
      exact this

end K421BaseProof

end CFSG.LocalAnalysis.RankThreeUC.S15
