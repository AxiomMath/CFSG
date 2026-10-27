module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Util

@[expose] def KD264RowData (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ A : Subgroup T, IsElemAbelian p A →
    (∀ S : Subgroup T, IsElemAbelian p S → Nat.card S ≤ Nat.card A) →
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 → p ^ (k + 1) ≤ Nat.card A →
      ∃ F : Subgroup T, F ≤ A ∧ Nat.card F = p ^ k ∧
        ∃ J0 : Subgroup T, GLAPComponent p (Subgroup.centralizer (F : Set T)) J0

variable {Y : Type} [Group Y] [Finite Y]

theorem psiImage_comap {T : Type} [Group T] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (Q : Subgroup T)
    (hQ : Q ≤ (psiHom K hK e hp hp2 hZT hin B hB).range) :
    psiImage K hK e hp hp2 hZT hin B hB
      ((Q.comap (psiHom K hK e hp hp2 hZT hin B hB)).map B.subtype) = Q := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    have hwE : (w : Y) ∈ (Q.comap (psiHom K hK e hp hp2 hZT hin B hB)).map B.subtype :=
      Subgroup.mem_subgroupOf.1 hw
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.1 hwE
    have huw' : u = w := Subtype.ext huw
    rw [← huw']
    exact Subgroup.mem_comap.1 hu
  · intro hg
    obtain ⟨w, hw⟩ := (MonoidHom.mem_range).1 (hQ hg)
    refine Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨w, ?_, rfl⟩), hw⟩
    exact Subgroup.mem_comap.2 (by rw [hw]; exact hg)

theorem kd264_gen_core {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (hrow : KD264RowData p T)
    (K B : Subgroup Y) (hK : K.Normal) (e : K ≃* T) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hcore : GLAPPrimeCore p ↥K = ⊥) (hB : IsElemAbelian p B) (hBcard : p ^ 4 ≤ Nat.card B)
    (hmax : IsMaxRankIn p B ⊤) (hC : B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥) :
    ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hB' : ∀ b ∈ B, b ^ p = 1 := fun b hb => hB.2 b hb
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h := Subgroup.map_center_eq e.symm
    rw [hZT, Subgroup.map_bot] at h
    exact h.symm
  set ψ := psiHom K hK e hp hp2 hZT hin B hB' with hψ
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  set A : Subgroup T := ψ.range with hAdef
  have hAel : IsElemAbelian p A :=
    isElemAbelian_range_of_hom hB.1 (fun g => Subtype.ext (hB.2 g.1 g.2)) ψ
  have hAmax : ∀ S : Subgroup T, IsElemAbelian p S → Nat.card S ≤ Nat.card A := fun S hS =>
    card_le_range_of_elemAbelian hp hp2 hZT hin K hK hZ e B hB hmax S hS
  have hBp : IsPGroup p B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := hBp.exists_card_eq
  have hCle : C ≤ B := inf_le_left
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 (hm ▸ Subgroup.card_dvd_of_le hCle)
  have hkerC : Nat.card C = Nat.card ψ.ker :=
    card_inf_centralizer_eq_ker hp hp2 hZT hin K hK e B hB
  have hsplit : Nat.card ψ.ker * Nat.card A = Nat.card B := Subgroup.card_ker_mul_card_range ψ
  have hm4 : 4 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hm ▸ hBcard)
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      exact hC (Subgroup.eq_bot_of_card_eq C (by rw [hc, h0, pow_zero]))
    · exact h0
  have hcm : c ≤ m := by
    have hd : p ^ c ∣ p ^ m := by rw [← hc, ← hm]; exact Subgroup.card_dvd_of_le hCle
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd
  have hAcard : Nat.card A = p ^ (m - c) := by
    have h1 : p ^ c * Nat.card A = p ^ c * p ^ (m - c) := by
      calc p ^ c * Nat.card A = Nat.card ψ.ker * Nat.card A := by rw [← hkerC, hc]
        _ = Nat.card B := hsplit
        _ = p ^ m := hm
        _ = p ^ c * p ^ (m - c) := by rw [← pow_add, Nat.add_sub_cancel' hcm]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos c) h1
  rcases (show 3 ≤ c ∨ c ≤ 2 by omega) with hc3 | hc2
  ·
    obtain ⟨E, hEcard, -, hEC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
      (H := (⊥ : Subgroup Y)) (L := C) (n := 3) (by simp)
      (by rw [hc]; exact pow_dvd_pow p hc3) bot_le
    have hEB : E ≤ B := hEC.trans hCle
    refine ⟨E, hEB, CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB hEB, hEcard, ?_⟩
    have hKE : K ⊓ Subgroup.centralizer (E : Set Y) = K := by
      refine inf_eq_left.2 fun k hk => Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have hwK := (hEC hw).2
      exact ((Subgroup.mem_centralizer_iff.1 hwK) k hk).symm
    rw [hKE]
    have hcomp := CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hq hcore
    intro hbot
    have hle : K ≤ GLAPLayer p K := le_sSup hcomp
    rw [hbot] at hle
    exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hcomp (le_bot_iff.1 hle)
  ·
    have hk1 : 1 ≤ 3 - c := by omega
    have hk2 : 3 - c ≤ 2 := by omega
    have hAk : p ^ (3 - c + 1) ≤ Nat.card A := by
      rw [hAcard]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    obtain ⟨F, hFA, hFcard, J0, hJ0⟩ := hrow A hAel hAmax (3 - c) hk1 hk2 hAk
    set E : Subgroup Y := (F.comap ψ).map B.subtype with hEdef
    have hEB : E ≤ B := Subgroup.map_subtype_le _
    have hEcard : Nat.card E = p ^ 3 := by
      rw [hEdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        card_comap_eq_mul ψ F hFA, hFcard, ← hkerC, hc, ← pow_add]
      congr 1
      omega
    refine ⟨E, hEB, CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB hEB, hEcard, ?_⟩
    have hpsiE := psiImage_comap hp hp2 hZT hin K hK e B hB' F hFA
    refine glaPLayer_ne_bot_of_comp K hK e hp hp2 hZT hin B hB' E hEB (J0 := J0) ?_
    rw [hpsiE]
    exact hJ0

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
