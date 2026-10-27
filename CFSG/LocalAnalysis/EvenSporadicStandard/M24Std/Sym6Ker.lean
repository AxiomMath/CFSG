module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmega
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransDataS24
public import Certificates.Certificate24865

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint


theorem tetSig_conj {g x : S24} (hx : x ∈ m24E1l)
    (hg : ∀ p : Fin 24, tetIdx ((g : Equiv.Perm (Fin 24)) p) = tetIdx p) :
    tetSig (g * x * g⁻¹) = tetSig x := by
  obtain ⟨-, -, hall, -⟩ := Certificates.certificate24864
  have key : ∀ i : Fin 6, (((g * x * g⁻¹ : S24) : Equiv.Perm (Fin 24)) (tetRep i) = tetRep i ↔
      (x : Equiv.Perm (Fin 24)) (tetRep i) = tetRep i) := by
    intro i
    have h1 : tetIdx (((g : Equiv.Perm (Fin 24)))⁻¹ (tetRep i)) = i := by
      have h2 := hg (((g : Equiv.Perm (Fin 24)))⁻¹ (tetRep i))
      rw [perm_apply_inv, tetIdx_tetRep] at h2
      exact h2.symm
    have h3 := hall x hx (((g : Equiv.Perm (Fin 24)))⁻¹ (tetRep i))
    rw [h1] at h3
    rw [← h3]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    exact Equiv.Perm.eq_inv_iff_eq.symm
  unfold tetSig
  congr 1
  exact List.filter_congr fun i _ => decide_eq_decide.2 (key i)

theorem norm_of_mem_sxK0 {g : S24}
    (hg : g ∈ sxK0) :
    QdNorm g ∧ ∀ p : Fin 24, tetIdx ((g : Equiv.Perm (Fin 24)) p) = tetIdx p := by
  have hω := qdNorm_qdOmega
  have hω' : ∀ p : Fin 24, tetIdx (((qdOmega⁻¹ : S24) : Equiv.Perm (Fin 24)) p) = tetIdx p := by
    intro p
    have h := tetIdx_qdOmega (((qdOmega⁻¹ : S24) : Equiv.Perm (Fin 24)) p)
    rw [Subgroup.coe_inv, perm_apply_inv] at h
    rw [Subgroup.coe_inv]
    exact h.symm
  simp only [sxK0, List.mem_append, List.mem_map] at hg
  rcases hg with (hg | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
  · exact ⟨qdNorm_of_mem hg, tetIdx_of_mem hg⟩
  · refine ⟨hω.mul (qdNorm_of_mem hx), fun p => ?_⟩
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, tetIdx_qdOmega, tetIdx_of_mem hx]
  · refine ⟨(qdNorm_inv hω).mul (qdNorm_of_mem hx), fun p => ?_⟩
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hω', tetIdx_of_mem hx]

theorem length_sxK0 : sxK0.length = 192 := by
  simp only [sxK0, List.length_append, List.length_map, m24_e1_check.1]

theorem nodup_sxK0 : sxK0.Nodup := Certificates.certificate24864.2.2.2.2.2.2.2.2.2.1

theorem mem_sxK0_of_fix
    {g : S24} (hg : QdNorm g)
    (hfix : ∀ p : Fin 24, tetIdx ((g : Equiv.Perm (Fin 24)) p) = tetIdx p) : g ∈ sxK0 := by
  obtain ⟨hQlist, hQmem, hQhom, hQinj, hQfx⟩ := Certificates.certificate24849
  obtain ⟨-, -, -, hψ, -⟩ := Certificates.certificate24848
  obtain ⟨-, -, -, -, hsig, -⟩ := Certificates.certificate24864
  have henum := Certificates.certificate24865
  have hQ' : ∀ k < 64, ∀ j < 64, qdQ k = qdQ j → k = j := fun k hk j hj h =>
    hQinj k (List.mem_range.2 hk) j (List.mem_range.2 hj) h
  have hex : ∀ k, ∃ j, k < 64 → j < 64 ∧ g * qdQ k * g⁻¹ = qdQ j := by
    intro k
    by_cases hk : k < 64
    · obtain ⟨j, hj, hjq⟩ := hQlist _ ((hg _).1 (hQmem k (List.mem_range.2 hk)))
      exact ⟨j, fun _ => ⟨List.mem_range.1 hj, hjq.symm⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose φ hφ using hex
  have hφhom : ∀ k < 64, ∀ j < 64, φ (k ^^^ j) = φ k ^^^ φ j := by
    intro k hk j hj
    obtain ⟨hk1, hk2⟩ := hφ k hk
    obtain ⟨hj1, hj2⟩ := hφ j hj
    obtain ⟨hkj1, hkj2⟩ := hφ (k ^^^ j) (qd_xor_lt_64 hk hj)
    refine hQ' _ hkj1 _ (qd_xor_lt_64 hk1 hj1) ?_
    calc qdQ (φ (k ^^^ j)) = g * qdQ (k ^^^ j) * g⁻¹ := hkj2.symm
      _ = g * (qdQ k * qdQ j) * g⁻¹ := by
        rw [hQhom k (List.mem_range.2 hk) j (List.mem_range.2 hj)]
      _ = (g * qdQ k * g⁻¹) * (g * qdQ j * g⁻¹) := by group
      _ = qdQ (φ k) * qdQ (φ j) := by rw [hk2, hj2]
      _ = qdQ (φ k ^^^ φ j) := hQhom _ (List.mem_range.2 hk1) _ (List.mem_range.2 hj1)
  have hφfx : ∀ k < 64, qdFxTab.getD (φ k) 99 = qdFxTab.getD k 99 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hφ k hk
    rw [← hQfx (φ k) (List.mem_range.2 hk1), ← hQfx k (List.mem_range.2 hk), ← hk2, qdFix_conj]
  have hfx : ∀ k < 64, qdFxTab.getD k 99 = 0 → qdFxTab.getD (φ k) 99 = 0 := fun k hk h0 =>
    (hφfx k hk).trans h0
  have hpair : ∀ a b : ℕ, a < 64 → b < 64 → a ^^^ b < 64 → qdFxTab.getD a 99 = 0 →
      qdFxTab.getD b 99 = 0 → qdFxTab.getD (a ^^^ b) 99 = 0 → (φ a, φ b) ∈ qdPairs := by
    intro a b ha hb hab h1 h2 h3
    refine mem_qdPairs (hφ a ha).1 (hφ b hb).1 (hfx a ha h1) (hfx b hb h2) ?_
    rw [← hφhom a ha b hb]
    exact hfx _ hab h3
  set y : List ℕ := [φ 1, φ 2, φ 4, φ 8, φ 16, φ 32] with hy
  have hy' : ∀ i < 6, y.getD i 0 = φ (2 ^ i) := by
    intro i hi
    interval_cases i <;> simp [hy]
  have hlin := qdLin_eq hφhom hy'
  have hE : SigEnumBody y := henum _ (hpair 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide)) _ (hpair 4 8 (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide)) _ (hpair 16 32 (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide))
  have hsig' : ∀ k ∈ List.range 64, tetSigTab.getD (qdLin y k) 99 = tetSigTab.getD k 99 := by
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [← hlin k hk', ← hsig _ (List.mem_range.2 (hφ k hk').1), ← hsig k hk, ← (hφ k hk').2]
    exact tetSig_conj (hQmem k hk) hfix
  have hcent : ∀ c : S24, (∀ k < 64, g * qdQ k * g⁻¹ = c * qdQ k * c⁻¹) → c⁻¹ * g ∈ m24E1l := by
    intro c hc
    refine sxt_cent fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hQlist x hx
    have h1 := hc k (List.mem_range.1 hk)
    calc c⁻¹ * g * qdQ k = c⁻¹ * (g * qdQ k * g⁻¹) * g := by group
      _ = c⁻¹ * (c * qdQ k * c⁻¹) * g := by rw [h1]
      _ = qdQ k * (c⁻¹ * g) := by group
  simp only [sxK0, List.mem_append, List.mem_map]
  rcases hE hsig' with h1 | h1 | h1
  · left; left
    have h2 := hcent 1 fun k hk => by
      rw [(hφ k hk).2, hlin k hk, h1 k (List.mem_range.2 hk)]
      group
    simpa using h2
  · left; right
    refine ⟨qdOmega⁻¹ * g, hcent qdOmega fun k hk => ?_, by group⟩
    rw [(hφ k hk).2, hlin k hk, h1 k (List.mem_range.2 hk)]
    exact ((hψ k (List.mem_range.2 hk)).2.2.1).symm
  · right
    refine ⟨qdOmega⁻¹⁻¹ * g, hcent qdOmega⁻¹ fun k hk => ?_, by group⟩
    rw [(hφ k hk).2, hlin k hk, h1 k (List.mem_range.2 hk), inv_inv]
    exact ((hψ k (List.mem_range.2 hk)).2.2.2).symm

end CFSG.EvenSporadicStandard.M24Std.Sym6
