module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sg
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29T

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

theorem exists_conj_of_isSylowIn {G : Type} [Group G] [Finite G] {T₁ T₂ K : Subgroup G}
    (h₁ : Seven.IsSylowIn T₁ K) (h₂ : Seven.IsSylowIn T₂ K) :
    ∃ g ∈ K, T₂ = T₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT₁, P₁, hP₁⟩ := h₁
  obtain ⟨hT₂, P₂, hP₂⟩ := h₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) P₁ P₂
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro hx
    have hxK : x ∈ K := hT₂ hx
    have h1 : (⟨x, hxK⟩ : K) ∈ ((g • P₁ : Sylow 2 K) : Subgroup K) := by
      rw [hg, hP₂]
      exact hx
    rw [mem_smul_sylow_iff, hP₁] at h1
    exact h1
  · intro hx
    have hxK : x ∈ K := by
      have := K.mul_mem (K.mul_mem g.2 (hT₁ hx)) (K.inv_mem g.2)
      rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at this
    have h1 : g⁻¹ * (⟨x, hxK⟩ : K) * g ∈ (P₁ : Subgroup K) := by
      rw [hP₁]
      exact hx
    rw [← mem_smul_sylow_iff, hg, hP₂] at h1
    exact h1

theorem factorization_two_eq {k n : ℕ} (hn : n ≠ 0) (h1 : 2 ^ k ∣ n) (h2 : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two]
  have hle : k ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn).mp h1
  rcases Nat.lt_or_ge k (padicValNat 2 n) with h | h
  · exact absurd ((pow_dvd_pow 2 h).trans pow_padicValNat_dvd) h2
  · omega

namespace Model

variable {P : Type} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

theorem isSylowIn_T [Finite P] : Seven.IsSylowIn M.T (centralizer ({ι} : Set P) ⊓ L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({ι} : Set P) ⊓ L with hCdef
  have hTC : M.T ≤ C := M.T_le
  obtain ⟨R, hR⟩ := (M.isPGroup_T.comap_subtype (K := C)).exists_le_sylow
  refine ⟨hTC, R, ?_⟩
  by_contra hne
  have hlt : M.T.comap C.subtype < R := lt_of_le_of_ne hR (Ne.symm hne)
  set R' := (R : Subgroup C).map C.subtype with hR'
  have hR'C : R' ≤ C := Subgroup.map_subtype_le _
  have hTR' : M.T ≤ R' := by
    intro x hx
    exact ⟨⟨x, hTC hx⟩, hR hx, rfl⟩
  have hR'2 : IsPGroup 2 R' := R.isPGroup'.map _
  have hcardR' : Nat.card R' = 2 ^ (2 * m + 3) := by
    obtain ⟨k, hk⟩ := hR'2.exists_card_eq
    have h1 : 2 ^ k ∣ Nat.card L := by
      rw [← hk]; exact Subgroup.card_dvd_of_le (hR'C.trans inf_le_right)
    have h2 : M.T ≠ R' := by
      intro h
      apply (ne_of_lt hlt)
      ext x
      constructor
      · intro hx; exact hR hx
      · intro hx
        show (x : P) ∈ M.T
        rw [h]
        exact ⟨x, hx, rfl⟩
    have h3 : 2 * m + 2 < k := by
      rcases Nat.lt_or_ge (2 * m + 2) k with h | h
      · exact h
      · exfalso
        apply h2
        apply Subgroup.eq_of_le_of_card_ge hTR'
        rw [hk, M.card_T]
        exact Nat.pow_le_pow_right (by norm_num) h
    have h4 : k ≤ 2 * m + 3 := by
      rcases Nat.lt_or_ge k (2 * m + 4) with h | h
      · omega
      · exact absurd ((pow_dvd_pow 2 h).trans h1) M.not_dvd_L
    rw [hk]
    congr 1
    omega
  have hfac : (Nat.card L).factorization 2 = 2 * m + 3 :=
    factorization_two_eq Nat.card_pos.ne' M.dvd_L M.not_dvd_L
  have hQL : Nat.card (M.Q.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
    rw [hfac, ← M.card_Q]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe M.Q_le_L).toEquiv
  have hRL : Nat.card (R'.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
    rw [hfac, ← hcardR']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hR'C.trans inf_le_right)).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) (Sylow.ofCard _ hQL) (Sylow.ofCard _ hRL)
  have hιR' : ι ∈ R' := hTR' M.iota_mem_T
  have hmemR : ∀ x : L, (x : P) ∈ R' ↔ (g : P)⁻¹ * x * g ∈ M.Q := by
    intro x
    have h1 := mem_smul_sylow_iff (Sylow.ofCard (M.Q.subgroupOf L) hQL) g x
    rw [hg] at h1
    exact h1
  have hιL : ι ∈ L := M.J_le_L M.z₁_mem_J |> fun _ => (M.T_le M.iota_mem_T).2
  have hy : (g : P)⁻¹ * ι * g ∈ M.Q := (hmemR ⟨ι, hιL⟩).mp hιR'
  have hyc : ∀ q ∈ M.Q, (g : P)⁻¹ * ι * g * q = q * ((g : P)⁻¹ * ι * g) := by
    intro q hq
    have hqL : q ∈ L := M.Q_le_L hq
    have h1 : (g : P) * q * (g : P)⁻¹ ∈ R' := by
      rw [hmemR ⟨(g : P) * q * (g : P)⁻¹, mul_mem (mul_mem g.2 hqL) (inv_mem g.2)⟩]
      simpa [mul_assoc] using hq
    have h2 := mem_centralizer_singleton_iff.mp (hR'C h1).1
    calc (g : P)⁻¹ * ι * g * q = (g : P)⁻¹ * (ι * ((g : P) * q * (g : P)⁻¹)) * g := by group
      _ = (g : P)⁻¹ * (((g : P) * q * (g : P)⁻¹) * ι) * g := by rw [h2]
      _ = q * ((g : P)⁻¹ * ι * g) := by group
  rcases M.center_Q hy hyc with h | h
  · have : ι = 1 := by
      have := congrArg (fun x => (g : P) * x * (g : P)⁻¹) h
      simpa [mul_assoc] using this
    exact M.iota_ne this
  · apply M.not_conj (g : P)⁻¹ (inv_mem g.2)
    rw [inv_inv, h]
    exact M.iota_comm_z₁.symm ▸ rfl

end Model

end CFSG.ComponentClassification.GSThmB.P29
