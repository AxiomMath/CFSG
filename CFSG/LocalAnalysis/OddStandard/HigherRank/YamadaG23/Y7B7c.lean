module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BFa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JStr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y7b_B_sq_mem_V (hH : F33Hyp s e) : ∀ b ∈ s.fr.B, b ^ 2 ∈ cen s.fr.B :=
  y5_B_sq hH

theorem y7b_B_comm_mem_V (hH : F33Hyp s e) :
    ∀ b ∈ s.fr.B, ∀ b' ∈ s.fr.B, ⁅b, b'⁆ ∈ cen s.fr.B :=
  y5_B_comm hH

theorem y7b_B_eq_JF (hH : F33Hyp s e) :
    ∀ b ∈ s.fr.B, ∃ j ∈ thompsonSubgroup s.fr.B, ∃ f ∈ s.fr.F, b = j * f := by
  have hαF : s.fr.a₁ * s.fr.a₂ ∈ s.fr.F := by
    rw [SFrame.F]
    exact Subgroup.subset_closure (by simp)
  intro b hb
  rcases y4_B_cases hH b hb with hbJ | ⟨j, hjJ, hb_eq⟩
  · exact ⟨b, hbJ, 1, Subgroup.one_mem _, by simp⟩
  · exact ⟨j, hjJ, s.fr.a₁ * s.fr.a₂, hαF, hb_eq⟩

theorem y7b_J_inf_F (hH : F33Hyp s e) :
    thompsonSubgroup s.fr.B ⊓ s.fr.F = cen s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxJ, hxF⟩ := Subgroup.mem_inf.mp hx
    exact y4_J_sq_one_mem_V hH x hxJ (by simpa [pow_two] using y54_F_sq hH x hxF)
  · intro v hv
    exact Subgroup.mem_inf.mpr ⟨y5_V_le_J hH hv, y54_V_le_F hH hv⟩

theorem y7b_V_eq_squares (hH : F33Hyp s e) :
    ∀ v ∈ cen s.fr.B, ∃ j ∈ thompsonSubgroup s.fr.B, j * j = v := by
  let J := thompsonSubgroup s.fr.B
  let ψ : ↥J →* G :=
    { toFun := fun x => (x : G) * (x : G)
      map_one' := by simp
      map_mul' := fun x y => by
        have h : (x : G) * (y : G) = (y : G) * (x : G) := y4_J_comm hH x x.2 y y.2
        show ((x * y : ↥J) : G) * ((x * y : ↥J) : G) =
          ((x : G) * (x : G)) * ((y : G) * (y : G))
        rw [Subgroup.coe_mul]
        calc ((x : G) * (y : G)) * ((x : G) * (y : G))
            = (x : G) * ((y : G) * (x : G)) * (y : G) := by group
          _ = (x : G) * ((x : G) * (y : G)) * (y : G) := by rw [h]
          _ = ((x : G) * (x : G)) * ((y : G) * (y : G)) := by group }
  have hψx : ∀ x : ↥J, ψ x = (x : G) * (x : G) := fun x => rfl
  have hker : ψ.ker = (cen s.fr.B).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      rw [hψx x] at h
      exact y4_J_sq_one_mem_V hH (x : G) x.2 (by simpa [pow_two] using h)
    · intro h
      rw [hψx x]
      simpa [pow_two] using y4_V_mul_self hH (x : G) h
  have hker_card : Nat.card ↥ψ.ker = 4 := by
    rw [hker, ← Subgroup.card_subtype J ((cen s.fr.B).subgroupOf J),
      Subgroup.map_subgroupOf_eq_of_le (H := cen s.fr.B) (K := J) (y5_V_le_J hH)]
    exact y7b_card_V hH
  have hrange_card : Nat.card ↥ψ.range = 4 := by
    have hJ : Nat.card ↥J = 16 := y4_card_J hH
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hker_card, hJ] at h
    omega
  have hrange_le : ψ.range ≤ cen s.fr.B := by
    intro x hx
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
    rw [← hy]
    exact y4_J_sq_mem_V hH (y : G) y.2
  have hRange : ψ.range = cen s.fr.B :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by
      have h1 := y7b_card_V hH
      have h2 := hrange_card
      omega)
  intro v hv
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (by rw [hRange]; exact hv)
  exact ⟨(y : G), y.2, hy⟩

theorem y7b_cent_V_of_comm_F (hH : F33Hyp s e) {n : G} (hn : n ∈ normalizer (s.fr.B : Set G))
    (h : ∀ b ∈ s.fr.B, n * b * n⁻¹ * b⁻¹ ∈ s.fr.F) : ∀ v ∈ cen s.fr.B, n * v * n⁻¹ = v := by
  intro v hv
  obtain ⟨j, hjJ, hjv⟩ := y7b_V_eq_squares hH v hv
  rw [← hjv]
  have hnj : n * j * n⁻¹ ∈ thompsonSubgroup s.fr.B := y5_J_conj s n hn j hjJ
  have hfJ : n * j * n⁻¹ * j⁻¹ ∈ thompsonSubgroup s.fr.B :=
    Subgroup.mul_mem _ hnj (Subgroup.inv_mem _ hjJ)
  have hfF : n * j * n⁻¹ * j⁻¹ ∈ s.fr.F := h j (y5_J_le_B s hjJ)
  have hfV : n * j * n⁻¹ * j⁻¹ ∈ cen s.fr.B := by
    rw [← y7b_J_inf_F hH]
    exact Subgroup.mem_inf.mpr ⟨hfJ, hfF⟩
  have hf2 : (n * j * n⁻¹ * j⁻¹) * (n * j * n⁻¹ * j⁻¹) = 1 := y4_V_mul_self hH _ hfV
  have hcomm : (n * j * n⁻¹ * j⁻¹) * j = j * (n * j * n⁻¹ * j⁻¹) :=
    y4_J_comm hH _ hfJ j hjJ
  calc n * (j * j) * n⁻¹ = (n * j * n⁻¹) * (n * j * n⁻¹) := by group
    _ = ((n * j * n⁻¹ * j⁻¹) * j) * ((n * j * n⁻¹ * j⁻¹) * j) := by group
    _ = ((n * j * n⁻¹ * j⁻¹) * (n * j * n⁻¹ * j⁻¹)) * (j * j) := by
          calc ((n * j * n⁻¹ * j⁻¹) * j) * ((n * j * n⁻¹ * j⁻¹) * j)
              = (n * j * n⁻¹ * j⁻¹) * (j * (n * j * n⁻¹ * j⁻¹)) * j := by group
            _ = (n * j * n⁻¹ * j⁻¹) * ((n * j * n⁻¹ * j⁻¹) * j) * j := by
                  rw [← hcomm]
            _ = ((n * j * n⁻¹ * j⁻¹) * (n * j * n⁻¹ * j⁻¹)) * (j * j) := by group
    _ = j * j := by rw [hf2]; group

theorem y7b_k_trans_BF (hH : F33Hyp s e) {k : G} (hk : k ∈ normIn L s.fr.B) (hk3 : k ^ 3 = 1)
    (hk1 : k ≠ 1) : ∀ u ∈ s.fr.B, u ∉ s.fr.F → ∀ v ∈ s.fr.B, v ∉ s.fr.F →
      ∃ i : ℕ, v⁻¹ * (k ^ i * u * (k ^ i)⁻¹) ∈ s.fr.F := by
  intro u huB huF v hvB hvF
  obtain ⟨ju, hjuJ, fu, hfuF, hu_eq⟩ := y7b_B_eq_JF hH u huB
  obtain ⟨jv, hjvJ, fv, hfvF, hv_eq⟩ := y7b_B_eq_JF hH v hvB
  have hVleF : cen s.fr.B ≤ s.fr.F := y54_V_le_F hH
  have hjuV : ju ∉ cen s.fr.B := fun hm => huF (hu_eq ▸ Subgroup.mul_mem _ (hVleF hm) hfuF)
  have hjvV : jv ∉ cen s.fr.B := fun hm => hvF (hv_eq ▸ Subgroup.mul_mem _ (hVleF hm) hfvF)
  have h3b : normIn L s.fr.B ≤ normIn L s.fr.F := hH.hLF.fact18.2.1.2.1
  have h3e := hH.hLF.fact18.2.1.2.2.2.2.1
  have hkord : orderOf k = 3 := by
    have hdvd : orderOf k ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hk3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · exact h
  have hkp : IsPGroup 3 (zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hkord]; norm_num)
  have hkzL : k ∉ zL L := by rw [f3_zL_eq_bot hH]; simpa using hk1
  have htrans := (h3e k hk hkp hkzL).2.2
  obtain ⟨k', hk'z, hk'v⟩ := htrans.2.2 ju hjuJ hjuV jv hjvJ hjvV
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk'z
  have hm3 : ((m % (3 : ℤ)).toNat : ℤ) = m % (3 : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
  have h1 : k ^ (m % (3 : ℤ)) = k ^ m := by simpa [hkord] using zpow_mod_orderOf k m
  have hki : k ^ (m % 3).toNat = k' := by rw [← zpow_natCast, hm3, h1, hm]
  refine ⟨(m % 3).toNat, ?_⟩
  have hVtrans : jv⁻¹ * (k ^ (m % 3).toNat * ju * (k ^ (m % 3).toNat)⁻¹) ∈ cen s.fr.B := by
    rw [hki]; exact hk'v
  have hkiN : k ^ (m % 3).toNat ∈ normIn L s.fr.B :=
    Subgroup.pow_mem (normIn L s.fr.B) hk ((m % 3).toNat)
  have hkiF : k ^ (m % 3).toNat ∈ normalizer (s.fr.F : Set G) := (h3b hkiN).2
  have hFfu : k ^ (m % 3).toNat * fu * (k ^ (m % 3).toNat)⁻¹ ∈ s.fr.F :=
    (Subgroup.mem_normalizer_iff.mp hkiF fu).mp hfuF
  rw [hu_eq, hv_eq]
  have hsplit : k ^ (m % 3).toNat * (ju * fu) * (k ^ (m % 3).toNat)⁻¹ =
      (k ^ (m % 3).toNat * ju * (k ^ (m % 3).toNat)⁻¹) *
        (k ^ (m % 3).toNat * fu * (k ^ (m % 3).toNat)⁻¹) := by group
  rw [hsplit]
  have hsplit2 : (jv * fv)⁻¹ *
      ((k ^ (m % 3).toNat * ju * (k ^ (m % 3).toNat)⁻¹) *
        (k ^ (m % 3).toNat * fu * (k ^ (m % 3).toNat)⁻¹)) =
      fv⁻¹ * (jv⁻¹ * (k ^ (m % 3).toNat * ju * (k ^ (m % 3).toNat)⁻¹)) *
        (k ^ (m % 3).toNat * fu * (k ^ (m % 3).toNat)⁻¹) := by group
  rw [hsplit2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hfvF) (hVleF hVtrans)) hFfu

theorem y7b_k_fix_BF (hH : F33Hyp s e) {k : G} (hk : k ∈ normIn L s.fr.B) (hk3 : k ^ 3 = 1)
    (hk1 : k ≠ 1) : ∀ b ∈ s.fr.B, k * b * k⁻¹ * b⁻¹ ∈ s.fr.F → b ∈ s.fr.F := by
  intro b hbB hcomm
  by_contra hbF
  have h3b : normIn L s.fr.B ≤ normIn L s.fr.F := hH.hLF.fact18.2.1.2.1
  have hB_le_N : s.fr.B ≤ normIn L s.fr.B := by
    rw [normIn]
    exact le_inf (f3_B_le_L s) Subgroup.le_normalizer
  have hbNF : b ∈ normalizer (s.fr.F : Set G) := ((hB_le_N.trans h3b) hbB).2
  have hkNF : k ∈ normalizer (s.fr.F : Set G) := (h3b hk).2
  set bF : Set G := (fun f : G => b * f) '' (s.fr.F : Set G) with hbFdef
  have hFncard : (s.fr.F : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact y7b_card_F hH
  have hBncard : (s.fr.B : Set G).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]; exact y54_card_B hH
  have hbFcard : bF.ncard ≤ 8 := by
    rw [hbFdef]
    exact (Set.ncard_image_le (f := fun f : G => b * f) (s := (s.fr.F : Set G))).trans_eq hFncard
  have hUncard : ((s.fr.F : Set G) ∪ bF).ncard ≤ 16 := by
    calc ((s.fr.F : Set G) ∪ bF).ncard ≤ (s.fr.F : Set G).ncard + bF.ncard :=
          Set.ncard_union_le _ _
      _ ≤ 8 + 8 := by omega
      _ = 16 := by norm_num
  have hsub : (s.fr.F : Set G) ∪ bF ⊆ (s.fr.B : Set G) := by
    intro x hx
    rcases hx with hxF | hxbF
    · exact y54_F_le_B hH hxF
    · rw [hbFdef] at hxbF
      obtain ⟨f, hfF, rfl⟩ := hxbF
      exact Subgroup.mul_mem _ hbB (y54_F_le_B hH hfF)
  have hne : ((s.fr.F : Set G) ∪ bF) ≠ (s.fr.B : Set G) := by
    intro heq
    have h := hUncard
    rw [heq, hBncard] at h
    omega
  have hne' : ¬ (s.fr.B : Set G) ⊆ (s.fr.F : Set G) ∪ bF := fun hle =>
    hne (Set.Subset.antisymm hsub hle)
  obtain ⟨v, hvB, hvnot⟩ := Set.exists_of_ssubset ⟨hsub, hne'⟩
  rw [Set.mem_union, not_or] at hvnot
  obtain ⟨hvF, hvbF⟩ := hvnot
  have hinv : ∀ i : ℕ, k ^ i * b * (k ^ i)⁻¹ ∈ bF := by
    intro i
    induction i with
    | zero =>
        rw [hbFdef]
        exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ i ih =>
        rw [hbFdef] at ih ⊢
        obtain ⟨f, hfF, hfeq⟩ := ih
        have hstep : k ^ (i + 1) * b * (k ^ (i + 1))⁻¹ =
            k * (k ^ i * b * (k ^ i)⁻¹) * k⁻¹ := by rw [pow_succ']; group
        rw [hstep, ← hfeq]
        have hkfF : k * f * k⁻¹ ∈ s.fr.F := (Subgroup.mem_normalizer_iff.mp hkNF f).mp hfF
        have hbcF : b⁻¹ * (k * b * k⁻¹ * b⁻¹) * b ∈ s.fr.F :=
          (Subgroup.mem_normalizer_iff''.mp hbNF (k * b * k⁻¹ * b⁻¹)).mp hcomm
        refine ⟨(b⁻¹ * (k * b * k⁻¹ * b⁻¹) * b) * (k * f * k⁻¹),
          Subgroup.mul_mem _ hbcF hkfF, ?_⟩
        rw [show k * (b * f) * k⁻¹ =
          b * ((b⁻¹ * (k * b * k⁻¹ * b⁻¹) * b) * (k * f * k⁻¹)) from by group]
  obtain ⟨i, hi⟩ := y7b_k_trans_BF hH hk hk3 hk1 b hbB hbF v hvB hvF
  have hvi := hinv i
  rw [hbFdef] at hvi
  obtain ⟨f, hfF, hfeq⟩ := hvi
  apply hvbF
  rw [hbFdef]
  refine ⟨f * (v⁻¹ * (k ^ i * b * (k ^ i)⁻¹))⁻¹,
    Subgroup.mul_mem _ hfF (Subgroup.inv_mem _ hi), ?_⟩
  rw [← hfeq]
  group

theorem y7b_relIndex_B_NLB (hH : F33Hyp s e) :
    s.fr.B.relIndex (normIn L s.fr.B) = 6 := by
  have hSec : SecProp (normIn L s.fr.B) s.fr.B
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := by
    have h := hH.hLF.fact18.2.1.2.2.1
    simpa only [f3_zL_eq_bot hH, bot_sup_eq] using h
  obtain ⟨hBn, ⟨iso⟩⟩ := hSec
  haveI := hBn
  have hq : Nat.card (↥(normIn L s.fr.B) ⧸ s.fr.B.subgroupOf (normIn L s.fr.B)) = 6 := by
    rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card]
    decide
  show (s.fr.B.subgroupOf (normIn L s.fr.B)).index = 6
  rw [Subgroup.index_eq_card]
  exact hq

end CFSG.OddStandard.HigherRank.YamadaG23
