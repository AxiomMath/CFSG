module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCPerm

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS Equiv.Perm.OnCycleFactors
open scoped commutatorElement

section One

variable {X : Type} [Group X] [Finite X] {n : ℕ}

private theorem bcOne_permX_zpow (hn : 8 ≤ n) {B : Subgroup X} (M : AhatModel X n B) {ξ : X}
    (hξ : ξ ∈ normalizer (B : Set X)) (j : ℤ) : M.permX (ξ ^ j) = M.permX ξ ^ j := by
  have h := map_zpow (M.permHom hn) (⟨ξ, hξ⟩ : ↥(normalizer (B : Set X))) j
  rw [M.permX_of_mem (zpow_mem hξ j), M.permX_of_mem hξ]
  exact h

private theorem bcOne_permData (hn : 8 ≤ n) {B : Subgroup X} (MB : AhatModel X n B) {z : X}
    {D : Subgroup X} (hzz : z * z = 1) (hDz : D ≤ centralizer ({z} : Set X))
    (hDB : D ≤ normalizer (B : Set X)) (hBD : B ⊓ centralizer ({z} : Set X) ≤ D)
    (hzN : z ∈ normalizer (B : Set X)) (hτ : MB.perm z hzN ≠ 1) (P : QuatPiece z D) :
    Nonempty (QuatPermData n) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQtN : P.Qt ≤ normalizer (B : Set X) := fun q hq => hDB (P.Qt_le hq)
  have hyQt : P.y ∈ P.Qt := P.Q_le P.y_mem
  have hxN : P.x ∈ normalizer (B : Set X) := hDB P.x_mem
  have haN : P.a ∈ normalizer (B : Set X) := hDB P.a_mem
  have hτx : MB.permX z = MB.perm z hzN := MB.permX_of_mem hzN
  have hcomm : ∀ d ∈ D, MB.permX d * MB.perm z hzN = MB.perm z hzN * MB.permX d := by
    intro d hd
    have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 (hDz hd)
    rw [← hτx, ← MB.permX_mul hn (hDB hd) hzN, ← MB.permX_mul hn hzN (hDB hd), hdz]
  let ψ : ↥P.Qt →* Perm (Fin n) := (MB.permHom hn).comp (Subgroup.inclusion hQtN)
  have hψ : ∀ q : ↥P.Qt, ψ q = MB.permX (q : X) := fun q => (MB.permX_of_mem (hQtN q.2)).symm
  let φ : ↥P.Q →* Perm (Fin n) := ψ.comp (Subgroup.inclusion P.Q_le)
  have hφ : ∀ q : ↥P.Q, φ q = MB.permX (q : X) := fun q => hψ _
  have hzQ : z ∈ P.Q := by
    have h2 := P.Q.mul_mem P.y_mem P.y_mem
    rwa [P.y_sq] at h2
  have hφz : φ ⟨z, hzQ⟩ = MB.perm z hzN := (hφ _).trans hτx
  have hpow : ∀ q : ↥P.Q, q ≠ 1 → ∃ j : ℤ, q ^ j = ⟨z, hzQ⟩ := by
    intro q hq
    have hq1 : (q : X) ≠ 1 := fun h => hq (Subtype.ext h)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (P.mem_zpowers_of_Q (q : X) q.2 hq1)
    exact ⟨j, Subtype.ext (by simpa using hj)⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    by_contra hq1
    obtain ⟨j, hj⟩ := hpow q hq1
    apply hτ
    rw [← hφz, ← hj, map_zpow, hq, one_zpow]
  have hw3 : IsPGroup 3 ↥(zpowers (MB.permX P.x)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 3)).1 P.x_three ⟨P.x, Subgroup.mem_zpowers P.x⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf (MB.permX P.x) ∣ 3 ^ k := by
      rw [← hk, MB.permX_of_mem hxN]
      have := orderOf_map_dvd (MB.permHom hn) (⟨P.x, hxN⟩ : ↥(normalizer (B : Set X)))
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card ((Nat.card_zpowers _).trans hj)
  refine ⟨{
    τ := MB.perm z hzN
    W := φ.range
    R := ψ.range
    y := MB.permX P.y
    w := MB.permX P.x
    c := MB.permX P.a
    τ_sq := perm_sq_eq_one hn MB hzN hzz
    τ_ne := hτ
    card_W := ?_
    W_zpowers := ?_
    W_comm := ?_
    W_le_R := ?_
    not_dvd_card_R := fun h16 => P.not_dvd_card_Qt (h16.trans (Subgroup.card_range_dvd ψ))
    R_comm := ?_
    y_mem := ⟨⟨P.y, hyQt⟩, hψ _⟩
    y_sq := ?_
    alt_lift := ?_
    w_three := hw3
    w_comm := hcomm _ P.x_mem
    c_comm := hcomm _ P.a_mem
    w_comm_c := ?_
    c_sq := ?_
    w_nontriv := ?_ }⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, P.card_Q]
  · rintro g ⟨q, rfl⟩ hg1
    have hq1 : q ≠ 1 := fun h => hg1 (by rw [h, map_one])
    obtain ⟨j, hj⟩ := hpow q hq1
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← map_zpow, hj, hφz]
  · rintro _ ⟨q, rfl⟩
    rw [hφ]
    exact hcomm _ (P.Qt_le (P.Q_le q.2))
  · rintro _ ⟨q, rfl⟩
    exact ⟨Subgroup.inclusion P.Q_le q, rfl⟩
  · rintro _ ⟨q, rfl⟩
    rw [hψ]
    exact hcomm _ (P.Qt_le q.2)
  · rw [← MB.permX_mul hn (hQtN hyQt) (hQtN hyQt), P.y_sq]
    exact hτx
  · intro π hπ
    obtain ⟨b, hb, hbτ, hbπ⟩ := exists_lift_alt_cycles hn MB hzN hzz π hπ
    have hbN : b ∈ normalizer (B : Set X) := Subgroup.le_normalizer hb.1
    have hbD : b ∈ D := hBD hb
    refine ⟨MB.permX b, hbτ, ?_, hbπ⟩
    rintro _ ⟨q, rfl⟩
    have hqN : (q : X) ∈ normalizer (B : Set X) := hQtN q.2
    have hmem : b * (q : X) * b⁻¹ ∈ P.Qt :=
      (Subgroup.mem_normalizer_iff.1 (P.le_normalizer_Qt hbD) (q : X)).1 q.2
    refine ⟨⟨b * (q : X) * b⁻¹, hmem⟩, ?_⟩
    calc ψ ⟨b * (q : X) * b⁻¹, hmem⟩ = MB.permX (b * (q : X) * b⁻¹) := hψ _
      _ = MB.permX b * MB.permX (q : X) * (MB.permX b)⁻¹ := MB.permX_conj hn hbN hqN
      _ = MB.permX b * ψ q * (MB.permX b)⁻¹ := by rw [hψ]
  · rw [← MB.permX_mul hn hxN haN, ← MB.permX_mul hn haN hxN, P.x_comm_a]
  · rw [← MB.permX_mul hn haN haN, P.a_sq]
    exact hτx
  · obtain ⟨q, hq, hqz⟩ := P.x_nontriv
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hqz
    have hqN : q ∈ normalizer (B : Set X) := hQtN hq
    have hcN : ⁅P.x, q⁆ ∈ normalizer (B : Set X) := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hqN) (inv_mem hxN)) (inv_mem hqN)
    refine ⟨MB.permX q, ⟨⟨q, hq⟩, hψ _⟩, Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩⟩
    calc ⁅MB.permX P.x, MB.permX q⁆ ^ j = (MB.permX ⁅P.x, q⁆) ^ j := by
          rw [MB.permX_comm hn hxN hqN]
      _ = MB.permX (⁅P.x, q⁆ ^ j) := (bcOne_permX_zpow hn MB hcN j).symm
      _ = MB.perm z hzN := by rw [hj]; exact hτx

variable {z : X} {Z : Subgroup X} {S : Sylow 2 ↥(normalizer (Z : Set X))}

private theorem bcOne_sec5Comp_K0 (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) {s : X}
    (hs : IsSec5Inv X Z s) :
    Sec5Comp X n (centralizer ({s} : Set X)) (K0 X n (centralizer ({s} : Set X))) := by
  have hZ : Z = zpowers z := h.Z_eq_zpowers h1
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hs1 : s ≠ 1 := fun h1' => hs.notMem (h1' ▸ one_mem Z)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs.sq) hs1
  obtain ⟨g, hgZ, hg1⟩ := hs.conj
  have hgz : g⁻¹ * s * g = z := by
    rw [hZ] at hgZ
    rcases (mem_zpowers_iff_of_orderOf_two hz2).1 hgZ with h0 | h0
    · exact absurd h0 hg1
    · exact h0
  have hgs : (g⁻¹)⁻¹ * z * g⁻¹ = s := by
    rw [← hgz]
    group
  obtain ⟨S', h'⟩ := h.mirror g⁻¹
  rw [hgs] at h'
  have hφz : (MulAut.conj (g⁻¹)⁻¹).toMonoidHom z = s := by simp [← hgs]
  have hZ' : Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom = zpowers s := by
    rw [hZ, MonoidHom.map_zpowers, hφz]
  have h1' : Sec5One X n (Z.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) :=
    sec5One_map_conj h1 (g⁻¹)⁻¹
  obtain ⟨A, hA, hKA⟩ := h'.exists_unique_comp h1'
  rw [hZ', normalizer_zpowers_eq_centralizer hs2] at hA hKA
  rw [hKA]
  exact hA

theorem quatPermData_of_piece (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) {s : X}
    (hs : IsSec5Inv X Z s)
    (P : QuatPiece z (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X))) :
    Nonempty (QuatPermData n) := by
  have hn : 8 ≤ n := h.maxdeg.1
  have hB := bcOne_sec5Comp_K0 h h1 hs
  let MB : AhatModel X n (K0 X n (centralizer ({s} : Set X))) := AhatModel.ofCover hB.2
  have hCsN : centralizer ({s} : Set X) ≤
      normalizer (K0 X n (centralizer ({s} : Set X)) : Set X) :=
    Sec5Data.le_normalizer_K0 X n _
  have hZ : Z = zpowers z := h.Z_eq_zpowers h1
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hz1 : z ≠ 1 := fun h1' => by
    rw [h1', orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzz : z * z = 1 := h.Z_sq_eq_one h.z_mem
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]
    exact normalizer_zpowers_eq_centralizer hz2
  have hsN : s ∈ normalizer (Z : Set X) := hs.mem
  have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.1 (hNC ▸ hsN)
  have hzC : z ∈ centralizer ({s} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hsz.symm
  have hzN := hCsN hzC
  exact bcOne_permData hn MB hzz inf_le_left (inf_le_right.trans hCsN)
    (fun b hb => ⟨hb.2, K0_le n _ hb.1⟩) hzN
    (perm_ne_one_of_mem_Z h hs h.z_mem hz1 hsz.symm hB hzN MB) P

end One

end CFSG.OddStandard.Solomon75
