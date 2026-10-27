module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.RestrictedStd.Spor
open GSThmB (IsSmallAltOrL2)

theorem m11_card_centralizerIn : ∀ u ∈ NativeSporadic.M11, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M11 u) = 48 := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, hsz, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  simp only [repSizes, m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hsz
  rw [← m11Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (m := 2) (by norm_num) [evalCodes [m11gA, m11gB] [1]]
    (by simpa using ⟨hr, hro⟩) 400 (by simpa [m11InvReps, m11InvRepWords] using hok)
  obtain ⟨r, hrm, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  simp only [List.mem_singleton] at hrm
  subst hrm
  have hcent := centralizerIn_eq_of_le m11Certificate.originalSubgroup _ hK
    (hsize _ (List.mem_singleton_self _)) (by rw [hsz, hKc, m11Certificate_originalSubgroup,
      m11_card])
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact hKc

theorem card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
    Fintype.card_fin]

theorem sixty_le_card_of_isSmallAltOrL2 {Y : Type} [Group Y] (h : IsSmallAltOrL2 Y) :
    60 ≤ Nat.card Y := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · rw [Nat.card_congr e.toEquiv]
    have h2 := card_alternatingGroup_fin n (by omega)
    rcases hn with rfl | rfl | rfl
    · rw [show Nat.factorial 5 = 120 from rfl] at h2; omega
    · rw [show Nat.factorial 6 = 720 from rfl] at h2; omega
    · rw [show Nat.factorial 7 = 5040 from rfl] at h2; omega
  · rw [GSThmB.card_of_lieModel_psl_two hp2 hL, Open.ordA]
    set q := p ^ f with hq
    have hgcd : Nat.gcd (1 + 1) (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hgpos : 0 < Nat.gcd (1 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, pow_one, Finset.Icc_self,
      Finset.prod_singleton]
    rw [Nat.le_div_iff_mul_le hgpos]
    have h24 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by nlinarith
      omega
    calc 60 * Nat.gcd 2 (q - 1) ≤ 60 * 2 := Nat.mul_le_mul_left _ hgcd
      _ ≤ 5 * 24 := by norm_num
      _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h24

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

theorem card_K_ge : 120 ≤ Nat.card c.K := by
  obtain ⟨eJ⟩ := c.quotient_J_K
  have h60 := sixty_le_card_of_isSmallAltOrL2 c.type_J
  have h1 : Nat.card (c.K ⧸ pPrimeCore 2 c.K) ≤ Nat.card c.K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card (c.K ⧸ pPrimeCore 2 c.K) =
      Nat.card (center (c.K ⧸ pPrimeCore 2 c.K)) *
        Nat.card ((c.K ⧸ pPrimeCore 2 c.K) ⧸ center (c.K ⧸ pPrimeCore 2 c.K)) := by
    rw [mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [c.card_center, Nat.card_congr (GSThmB.oddBarCenterEquiv c.K).toEquiv,
    ← Nat.card_congr eJ.toEquiv] at h2
  omega

include c in
theorem false_of_M11 (hG : NativeSporadic.IsSporadic ↥(generalizedFitting H) .M11) : False := by
  obtain ⟨e⟩ := hG
  have e' : ↥(generalizedFitting H) ≃* ↥NativeSporadic.M11 := e
  have pc := c.pairConfig e'
  set x := e' ⟨c.b, c.b_mem_G⟩ with hx
  have hK₁ : Nat.card ((c.K.subgroupOf (generalizedFitting H)).map e'.toMonoidHom) =
      Nat.card c.K := by
    rw [Subgroup.card_map_of_injective e'.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe c.K_le_G).toEquiv
  have hC : Nat.card (centralizer ({x} : Set ↥NativeSporadic.M11)) = 48 := by
    have hmap : (centralizer ({x} : Set ↥NativeSporadic.M11)).map NativeSporadic.M11.subtype =
        centralizerIn NativeSporadic.M11 (x : Equiv.Perm (Fin 11)) := by
      ext y
      simp only [mem_map, centralizerIn, mem_inf, mem_centralizer_singleton_iff, subtype_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, congrArg Subtype.val hy⟩
      · rintro ⟨hy, hyx⟩
        exact ⟨⟨y, hy⟩, Subtype.ext hyx, rfl⟩
    rw [← Subgroup.card_map_of_injective NativeSporadic.M11.subtype_injective, hmap]
    exact m11_card_centralizerIn _ x.2 (by rw [Subgroup.orderOf_coe]; exact pc.orderOf_x)
  have hle := Subgroup.card_le_of_le pc.K_le
  have := c.card_K_ge
  omega

end Config

end CFSG.ComponentClassification.Sp4Rec
