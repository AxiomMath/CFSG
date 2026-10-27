module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm MulAction CFSG.Open GL83.CompFam GL83.PiGen

section Orb

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]

theorem i271h_rank_add_pow_le {R : Subgroup (Perm Ω)} (hR : IsElemAbelian p R) (ω : Ω)
    {k c s r : ℕ} (hn : Fintype.card Ω = k * p + c) (hcp : c < p) (hs : 1 ≤ s)
    (horb : Nat.card (orbit R ω) = p ^ s) (hr : Nat.card R = p ^ r) : r + p ^ (s - 1) ≤ k + s := by
  have hp := (Fact.out : p.Prime)
  have hb := card_le_orbit_bound hR ω horb
  rw [hr] at hb
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hsn : p ^ (s' + 1) ≤ Fintype.card Ω := by
    rw [← horb]
    have h := Nat.card_le_card_of_injective (Subtype.val : (orbit R ω) → Ω) Subtype.val_injective
    rwa [Nat.card_eq_fintype_card (α := Ω)] at h
  set q := p ^ s' with hq
  have hpq : p ^ (s' + 1) = p * q := by rw [pow_succ, mul_comm]
  have hqk : q ≤ k := by
    by_contra hlt
    have : p * (k + 1) ≤ p * q := Nat.mul_le_mul_left _ (by omega)
    rw [hpq] at hsn
    nlinarith
  have hdiv : (Fintype.card Ω - p ^ (s' + 1)) / p = k - q := by
    rw [hpq, hn]
    have h1 : k * p + c - p * q = p * (k - q) + c := by
      rw [Nat.mul_sub, mul_comm k p]
      have : p * q ≤ p * k := Nat.mul_le_mul_left _ hqk
      omega
    rw [h1, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega)]
    simp
  rw [hdiv, ← pow_add] at hb
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hb
  simp only [Nat.add_sub_cancel]
  omega

end Orb

section Main

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem i271h_orbit_card_le (hp3 : 3 ≤ p) {B K : Subgroup X} {k c n : ℕ} (hk : 1 ≤ k)
    (hc1 : 1 ≤ c) (hcp : c < p) (hnk : n = k * p + c) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hB : IsElemAbelian p B) (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hrank : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) (ω : Fin n) :
    Nat.card (orbit (permHom (stab_le_normalizer B K) hn5 hn6 e).range ω) ≤ p := by
  have hp := (Fact.out : p.Prime)
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  set π := permHom (stab_le_normalizer B K) hn5 hn6 e with hπ
  set R := π.range with hR
  have hAB : stab B K ≤ B := inf_le_left
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB hAB
  have hRel : IsElemAbelian p R := isElemAbelian_range hAel π
  have hRpg : IsPGroup p R := isPGroup_of_elem hRel
  obtain ⟨r, hr⟩ := exists_card_eq_pow hRel
  have hdiv : Fintype.card (Fin n) / p = k := by
    rw [Fintype.card_fin, hnk]
    exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hRk : Nat.card R ≤ p ^ k := by
    have h := CFSG.AGLEmbedding.card_le_pow_div_of_commute (p := p) R
      (fun x hx y hy => elem_comm hRel hx hy) hRpg
    rwa [hdiv] at h
  by_cases hk1 : k = 1
  · subst hk1
    calc Nat.card (orbit R ω) ≤ Nat.card R := orbit_le_card R ω
      _ ≤ p ^ 1 := hRk
      _ = p := pow_one p
  · have hk2 : 2 ≤ k := by omega
    by_contra hlt
    obtain ⟨s, hs⟩ := hRpg.card_orbit ω
    have hs2 : 2 ≤ s := by
      by_contra hs1
      have : p ^ s ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [pow_one] at this
      exact hlt (hs ▸ this)
    have hP := i271h_rank_add_pow_le hRel ω (k := k) (c := c) (by rw [Fintype.card_fin]; exact hnk)
      hcp (by omega) hs hr
    have hrk : r ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hr ▸ hRk)
    obtain ⟨φ⟩ := exists_mulEquiv_of_center_eq_bot hZ e
    obtain ⟨V, E₀, hVK, hEK, hV0, hV2, hEel, hEV, hE₀⟩ :=
      exists_klein_elem_in_component (K := K) hp3 (by omega : 4 ≤ n) φ
    have hcount := card_conj_family_le hB hK (inf_centralizer_eq_bot_of_center_eq_bot hZ) hVK hEK
      hV0 hV2 hEel hEV
    have h1 : p ^ GLATwoLocalRank p X ≤ Nat.card B := by
      rw [card_eq_pow_pRank hB]
      exact Nat.pow_le_pow_right hp.pos hrank
    set t := (stab B K).relIndex B with ht
    have hBt : Nat.card B = t * Nat.card (stab B K) := by
      have h := Subgroup.relIndex_mul_card (H := stab B K) (K := B)
      rw [inf_eq_left.2 hAB] at h
      exact h.symm
    have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card R :=
      card_stab_eq_mul hn5 hn6 e
    have hCpos : 0 < Nat.card (cen B K) := Nat.card_pos
    have h2 : Nat.card E₀ ^ t ≤ t * Nat.card R := by
      have : Nat.card (cen B K) * Nat.card E₀ ^ t ≤ Nat.card (cen B K) * (t * Nat.card R) := by
        calc Nat.card (cen B K) * Nat.card E₀ ^ t ≤ p ^ GLATwoLocalRank p X := hcount
          _ ≤ Nat.card B := h1
          _ = Nat.card (cen B K) * (t * Nat.card R) := by rw [hBt, hAC]; ring
      exact Nat.le_of_mul_le_mul_left this hCpos
    obtain ⟨a, -, hta⟩ : ∃ a ≤ CFSG.Open.pRank p B, t = p ^ a := by
      refine (Nat.dvd_prime_pow hp).1 ?_
      rw [← card_eq_pow_pRank hB, hBt]
      exact Dvd.intro _ rfl
    have h3 : (p ^ ((n - 4) / p + if p = 3 then 1 else 0)) ^ t ≤ p ^ (a + r) := by
      calc (p ^ ((n - 4) / p + if p = 3 then 1 else 0)) ^ t ≤ Nat.card E₀ ^ t :=
            Nat.pow_le_pow_left hE₀ t
        _ ≤ t * Nat.card R := h2
        _ = p ^ (a + r) := by rw [hta, hr, pow_add]
    have h4 : ((n - 4) / p + if p = 3 then 1 else 0) * t ≤ a + r := by
      rw [← pow_mul] at h3
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
    have hdiv4 : k - 1 ≤ (n - 4) / p := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.le_div_iff_mul_le hp.pos, hnk]
      have h' : (k' + 1) * p + c - 4 = k' * p + (p + c - 4) := by rw [add_mul]; omega
      rw [h']
      exact Nat.le_add_right _ _
    have h4' : ((k - 1) + if p = 3 then 1 else 0) * t ≤ a + r :=
      le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hdiv4 _)) h4
    rw [hta] at h4'
    have hp' : p = 3 ∨ 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · have : p = 3 ∨ p = 4 := by omega
        rcases this with h3 | h4
        · exact Or.inl h3
        · exact absurd (h4 ▸ hp) (by norm_num)
      · exact Or.inr h
    exact no_big_orbit_arith hp' hk2 hrk hs2 h4' hP

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
