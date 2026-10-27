module

public import CFSG.CGT.PushingUpLit.SYMB.FiveTable

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv

@[expose] def NormY (a b c d : Fin 5) (σ : Perm (Fin 5)) : Prop :=
  (σ * swap a b * σ⁻¹ = 1 ∨ σ * swap a b * σ⁻¹ = swap a b ∨ σ * swap a b * σ⁻¹ = swap c d ∨
    σ * swap a b * σ⁻¹ = swap a b * swap c d) ∧
  (σ * swap c d * σ⁻¹ = 1 ∨ σ * swap c d * σ⁻¹ = swap a b ∨ σ * swap c d * σ⁻¹ = swap c d ∨
    σ * swap c d * σ⁻¹ = swap a b * swap c d)

instance (a b c d : Fin 5) : DecidablePred (NormY a b c d) := fun σ => by
  unfold NormY; infer_instance

theorem card_NormY_le : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    (Finset.univ.filter (NormY a b c d)).card ≤ 8 := by
  set_option synthInstance.maxSize 2000 in decide +kernel

theorem normY_swap_mul_swap : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    NormY a b c d (swap a c * swap b d) := by
  set_option synthInstance.maxSize 2000 in decide +kernel

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}

omit [Finite Γ] in
theorem imgG_T_conj {σ y : Equiv.Perm (Fin 5)} (hσ : σ ∈ imgG G φ T)
    (hy : y ∈ imgG G φ (baum T)) : σ * y * σ⁻¹ ∈ imgG G φ (baum T) := by
  obtain ⟨t, htG, htT, rfl⟩ := mem_imgG.1 hσ
  obtain ⟨b, hbG, hbB, rfl⟩ := mem_imgG.1 hy
  refine mem_imgG.2 ⟨t * b * t⁻¹, G.mul_mem (G.mul_mem htG hbG) (G.inv_mem htG),
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_baum T htT) b).mp hbB, ?_⟩
  show φ ((⟨t, htG⟩ : ↥G) * ⟨b, hbG⟩ * (⟨t, htG⟩ : ↥G)⁻¹) = _
  rw [map_mul, map_mul, map_inv]

omit [Finite Γ] in
theorem eight_dvd_card_imgG (S : SymSetting G T V 5 φ ψ T') (hker : kerG G φ ≤ T) :
    8 ∣ Nat.card ↥(imgG G φ T) := by
  have hker' : φ.ker ≤ T.subgroupOf G := fun x hx => by
    rw [Subgroup.mem_subgroupOf]
    exact hker (mem_kerG.2 ⟨x.2, hx⟩)
  have h1 : (imgG G φ T).index = (T.subgroupOf G).index :=
    Subgroup.index_map_eq (T.subgroupOf G) S.data.φ_surj hker'
  have hodd : ¬ 2 ∣ (T.subgroupOf G).index := S.sylow.2.2
  have h2 := Subgroup.card_mul_index (imgG G φ T)
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [h120, h1] at h2
  have hcop : Nat.Coprime 8 (T.subgroupOf G).index := by
    have : Nat.Coprime 2 (T.subgroupOf G).index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    have h8 := Nat.Coprime.pow_left 3 this
    simpa using h8
  have h8 : 8 ∣ Nat.card ↥(imgG G φ T) * (T.subgroupOf G).index := by
    rw [h2]
    norm_num
  exact hcop.dvd_of_dvd_mul_right h8

omit [Finite Γ] in
theorem swap_mul_swap_mem_imgG (S : SymSetting G T V 5 φ ψ T') (hker : kerG G φ ≤ T)
    {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hY : imgG G φ (baum T) = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) :
    swap a c * swap b d ∈ imgG G φ T := by
  classical
  set D : Subgroup (Equiv.Perm (Fin 5)) := imgG G φ T with hD
  set F : Finset (Equiv.Perm (Fin 5)) := Finset.univ.filter (NormY a b c d) with hF
  have hu := swap_mul_self a b
  have hv := swap_mul_self c d
  have huv := swap_comm_swap hac had hbc hbd
  have hDF : (D : Set (Equiv.Perm (Fin 5))) ⊆ (F : Set (Equiv.Perm (Fin 5))) := by
    intro σ hσ
    have h1 : swap a b ∈ imgG G φ (baum T) := by
      rw [hY]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : swap c d ∈ imgG G φ (baum T) := by
      rw [hY]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have c1 := imgG_T_conj hσ h1
    have c2 := imgG_T_conj hσ h2
    rw [hY] at c1 c2
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (mem_zpowers_sup_pair hu hv huv).1 c1, (mem_zpowers_sup_pair hu hv huv).1 c2⟩)
  have hDcard : 8 ≤ Nat.card ↥D := Nat.le_of_dvd Nat.card_pos (eight_dvd_card_imgG S hker)
  have hFcard : (F : Set (Equiv.Perm (Fin 5))).ncard ≤ (D : Set (Equiv.Perm (Fin 5))).ncard := by
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact (card_NormY_le a b c d hab hcd hac had hbc hbd).trans hDcard
  have hEq := Set.eq_of_subset_of_ncard_le hDF hFcard
  have hγ : swap a c * swap b d ∈ (F : Set (Equiv.Perm (Fin 5))) := by
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      normY_swap_mul_swap a b c d hab hcd hac had hbc hbd⟩)
  rw [← hEq] at hγ
  exact hγ

end CFSG.CGT.PushingUpLit.SYMB
