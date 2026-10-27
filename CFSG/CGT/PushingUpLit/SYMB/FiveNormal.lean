module

public import CFSG.CGT.PushingUpLit.SYMB.JoinBlock
public import CFSG.CGT.PushingUpLit.SYMB.Setting

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

omit [Finite Γ] in
theorem imgG_eq_top_of_alt_le (S : SymSetting G T V n φ ψ T') {X : Subgroup Γ}
    (hBX : baum T ≤ X) (hAX : alternatingGroup (Fin n) ≤ imgG G φ X) : imgG G φ X = ⊤ := by
  classical
  obtain ⟨t₀, ht₀⟩ := S.nonempty
  have ht₀B : t₀ ∈ imgG G φ (baum T) := by
    rw [S.baum]
    exact Subgroup.subset_closure ht₀
  have ht₀X : t₀ ∈ imgG G φ X := imgG_mono G φ hBX ht₀B
  have hodd : Equiv.Perm.sign t₀ = -1 := by
    obtain ⟨a, a', haa, rfl⟩ := S.swaps t₀ ht₀
    exact Equiv.Perm.sign_swap haa
  rw [eq_top_iff]
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact hAX (Equiv.Perm.mem_alternatingGroup.2 h1)
  · have h2 : σ * t₀⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hodd, h1]
      decide
    have h3 := (imgG G φ X).mul_mem (hAX h2) ht₀X
    simpa using h3

omit [Finite Γ] in
theorem symJoin_normal (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hJ : SymJoin G T V φ ψ E) (hno : ∀ L ∈ lSet G T, imgG G φ L ≠ ⊤) :
    G ≤ Subgroup.normalizer (E : Set Γ) := by
  classical
  set L : Subgroup Γ := G ⊓ Subgroup.normalizer (E : Set Γ) with hL
  have hLG : L ≤ G := inf_le_left
  have hBn : baum T ≤ Subgroup.normalizer (E : Set Γ) := by
    have := Subgroup.normalizer_commutator_ge_right E (baum T)
    rwa [hJ.commutator] at this
  have hBG : baum T ≤ G := (inf_le_left : baum T ≤ T).trans S.sylow.1
  have hBL : baum T ≤ L := le_inf hBG hBn
  have hEL : E ≤ L := le_inf hJ.le Subgroup.le_normalizer
  have hAL : alternatingGroup (Fin n) ≤ imgG G φ L := by
    rw [← hJ.img_eq_alt]
    exact imgG_mono G φ hEL
  have hLC : ¬ L ≤ cStarIn G T := fun hle => sym_not_alt_le_imgG S hle hAL
  by_contra hne
  have hLlt : L < G := by
    refine lt_of_le_of_ne hLG fun heq => hne ?_
    intro g hg
    have : g ∈ L := by
      rw [heq]
      exact hg
    exact this.2
  exact hno L ⟨hLlt, hBL, hLC⟩ (imgG_eq_top_of_alt_le S hBL hAL)

omit [Finite Γ] in
theorem symJoin_sup_T (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hJ : SymJoin G T V φ ψ E) (hno : ∀ L ∈ lSet G T, imgG G φ L ≠ ⊤) : G ≤ E ⊔ T := by
  classical
  have hLG : E ⊔ T ≤ G := sup_le hJ.le S.sylow.1
  have hBL : baum T ≤ E ⊔ T := (inf_le_left : baum T ≤ T).trans le_sup_right
  have hAL : alternatingGroup (Fin n) ≤ imgG G φ (E ⊔ T) := by
    rw [← hJ.img_eq_alt]
    exact imgG_mono G φ le_sup_left
  have hLC : ¬ E ⊔ T ≤ cStarIn G T := fun hle => sym_not_alt_le_imgG S hle hAL
  by_contra hne
  have hLlt : E ⊔ T < G := by
    refine lt_of_le_of_ne hLG fun heq => hne ?_
    rw [heq]
  exact hno _ ⟨hLlt, hBL, hLC⟩ (imgG_eq_top_of_alt_le S hBL hAL)

omit [Finite Γ] in
theorem sym_ker_le_pCore (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hEG : E ≤ G) (hnorm : G ≤ Subgroup.normalizer (E : Set Γ)) (hGE : G ≤ E ⊔ T)
    (hK2 : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ))) :
    kerG G φ ≤ pCoreOf 2 G := by
  classical
  have hRG : kerG G φ ≤ G := fun _ hg => (mem_kerG.1 hg).1
  have hRC : ∀ g ∈ kerG G φ, g ∈ Subgroup.centralizer (V : Set Γ) := by
    intro g hg
    obtain ⟨hgG, hg1⟩ := mem_kerG.1 hg
    have h2 : (⟨g, hgG⟩ : ↥G) ∈ φ.ker := hg1
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    exact h2.2
  have hT2 : IsPGroup 2 ↥T := S.sylow.2.1
  have hpow : ∀ g ∈ G, ∃ k : ℕ, g ^ (2 ^ k) ∈ E := by
    intro g hg
    have hTE : T ≤ Subgroup.normalizer (E : Set Γ) := S.sylow.1.trans hnorm
    have hmul : ((T ⊔ E : Subgroup Γ) : Set Γ) = (T : Set Γ) * (E : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T E hTE
    have hg' : g ∈ ((T ⊔ E : Subgroup Γ) : Set Γ) := by
      rw [sup_comm]
      exact hGE hg
    rw [hmul] at hg'
    obtain ⟨t, ht, e, he, rfl⟩ := hg'
    have : (E.subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hEG).mpr hnorm
    have htG : t ∈ G := S.sylow.1 ht
    have heG : e ∈ G := hEG he
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hmk : (QuotientGroup.mk' (E.subgroupOf G)) (⟨t * e, G.mul_mem htG heG⟩ : ↥G) ^ (2 ^ k) = 1 := by
      have h1 : (QuotientGroup.mk' (E.subgroupOf G)) (⟨e, heG⟩ : ↥G) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (by simpa [Subgroup.mem_subgroupOf] using he)
      have e1 : (⟨t * e, G.mul_mem htG heG⟩ : ↥G) = ⟨t, htG⟩ * ⟨e, heG⟩ := rfl
      rw [e1, map_mul, h1, mul_one, ← map_pow]
      have : (⟨t, htG⟩ : ↥G) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk')
      rw [this, map_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmk
    simpa using hmk
  have hR2 : IsPGroup 2 ↥(kerG G φ) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    obtain ⟨k, hk⟩ := hpow g (hRG g.2)
    have hgk : (g : Γ) ^ (2 ^ k) ∈ E ⊓ Subgroup.centralizer (V : Set Γ) :=
      ⟨hk, (Subgroup.centralizer (V : Set Γ)).pow_mem (hRC g g.2) _⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hK2) ⟨(g : Γ) ^ (2 ^ k), hgk⟩
    have hj' : orderOf ((g : Γ) ^ (2 ^ k)) = 2 ^ j :=
      (Subgroup.orderOf_coe ⟨(g : Γ) ^ (2 ^ k), hgk⟩).trans hj
    have hdvd : orderOf (g : Γ) ∣ 2 ^ (k + j) := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_add, pow_mul]
      have := pow_orderOf_eq_one ((g : Γ) ^ (2 ^ k))
      rwa [hj'] at this
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨i, by rw [← Subgroup.orderOf_coe]; exact hio⟩
  exact le_pCoreOf_of_normalizes hRG (le_normalizer_kerG G φ) hR2

omit [Finite Γ] in
theorem sym_ker_le_T (S : SymSetting G T V n φ ψ T') {E : Subgroup Γ}
    (hEG : E ≤ G) (hnorm : G ≤ Subgroup.normalizer (E : Set Γ)) (hGE : G ≤ E ⊔ T)
    (hK2 : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ))) : kerG G φ ≤ T :=
  (sym_ker_le_pCore S hEG hnorm hGE hK2).trans S.sylow.pCoreOf_le

end CFSG.CGT.PushingUpLit.SYMB
