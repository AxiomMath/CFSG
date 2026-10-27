module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Ord2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem blockU_conjR (X : Subgroup G) (g : G) : blockU (conjR X g) = conjR (blockU X) g :=
  blockU_map_equiv (MulAut.conj g⁻¹) X

theorem twoPart_eq_of_card {X : Subgroup G} {k m : ℕ} (hm : ¬ 2 ∣ m)
    (h : Nat.card X = 2 ^ k * m) : twoPart X = 2 ^ k := by
  unfold twoPart
  rw [h, Nat.factorization_mul (by positivity) (fun h0 => hm (by rw [h0]; exact dvd_zero 2)), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem nonempty_mulEquiv_conjR {Y : Type*} [Group Y] {X : Subgroup G} (g : G)
    (h : Nonempty (↥X ≃* Y)) : Nonempty (↥(conjR X g) ≃* Y) := by
  obtain ⟨e⟩ := h
  exact ⟨(X.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm.trans
    e⟩

end Generic

namespace Lin2Hyp

section Block

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem block_s {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
        IsLin2Type (L ⊓ Subgroup.centralizer ({s} : Set G)) m ∧
        blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
          blockU (L ⊓ Subgroup.centralizer ({s} : Set G))) ∨
      (n = 2 ∧
        (Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃*
            Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∧
    pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G) ∧
    twoPart (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
  obtain ⟨f₀, hf₀S, hf₀R, hf₀2, hev, hconj, -, hR1, hR2, hblk⟩ := E.exists_f₀ hcfg
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨c, hc, rfl⟩ := hconj s hs hsR hs2
  have hcL : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer ((E.Rsyl hcfg).le hc)
  have hcU : c ∈ Subgroup.normalizer (blockU L : Set G) := E.R_le_normalizer_U hcfg hc
  have hcR : c ∈ Subgroup.normalizer (thompsonJ S : Set G) := Subgroup.le_normalizer hc
  have hLc : L ⊓ Subgroup.centralizer ({c⁻¹ * f₀ * c} : Set G) =
      conjR (L ⊓ Subgroup.centralizer ({f₀} : Set G)) c := inf_centralizer_eq_conjR hcL
  have hUc : blockU L ⊓ Subgroup.centralizer ({c⁻¹ * f₀ * c} : Set G) =
      conjR (blockU L ⊓ Subgroup.centralizer ({f₀} : Set G)) c := inf_centralizer_eq_conjR hcU
  have hRc : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({c⁻¹ * f₀ * c} : Set G) : Subgroup G) =
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G) :=
    card_inf_centralizer_conj hcR
  have h2c : twoPart (conjR (L ⊓ Subgroup.centralizer ({f₀} : Set G)) c) =
      twoPart (L ⊓ Subgroup.centralizer ({f₀} : Set G)) :=
    twoPart_map_equiv (MulAut.conj c⁻¹) _
  rw [hLc, hUc, hRc, h2c]
  set Lf := L ⊓ Subgroup.centralizer ({f₀} : Set G) with hLf
  have hU := E.U_s_values hcfg hf₀S hf₀R hf₀2 hx hxS
  rcases hblk with ⟨m, hm, hm1, hshort, hlin, hU1, hO⟩ |
    ⟨hn2, ⟨hc0, hperm, hO⟩ | ⟨hc0, hperm, hO⟩⟩
  · refine ⟨Or.inl ⟨m, hm, hm1, (isShort2_conjR_iff _ c).mpr hshort,
      (isLin2Type_conjR_iff _ c m).mpr hlin, ?_⟩, ?_, ?_⟩
    · rw [blockU_conjR, ← hU1]
    · rw [conjR_pCoreOf, hO]
    · have hcardL := lin2_card_L hlin
      rw [hO] at hcardL
      have hm0 : 1 ≤ m := by omega
      have hodd : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by
        have h2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
        have h1 : 0 < (2 ^ m) ^ 2 := by positivity
        omega
      by_cases hc0 : centerOf L = ⊥
      · rw [(hU.1 hc0).1] at hcardL
        have : Nat.card Lf = 2 ^ (n + m) * ((2 ^ m) ^ 2 - 1) := by
          rw [hcardL, pow_add]; ring
        rw [twoPart_eq_of_card hodd this, hR1 hc0]
        congr 1; omega
      · rw [(hU.2 hc0).1] at hcardL
        have : Nat.card Lf = 2 ^ (3 * n / 2 + m) * ((2 ^ m) ^ 2 - 1) := by
          rw [hcardL, pow_add]; ring
        rw [twoPart_eq_of_card hodd this, hR2 hc0]
        congr 1; omega
  · have hcard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    refine ⟨Or.inr ⟨hn2, Or.inl (nonempty_mulEquiv_conjR c hperm)⟩, ?_, ?_⟩
    · rw [conjR_pCoreOf, hO]
    · obtain ⟨e⟩ := hperm
      have hL24 : Nat.card Lf = 2 ^ 3 * 3 := by
        rw [Nat.card_congr e.toEquiv, hcard]; norm_num
      rw [twoPart_eq_of_card (by norm_num) hL24, hR1 hc0]
      subst hn2
      norm_num
  · have hcard : Nat.card (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) = 48 := by
      rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)), Nat.card_zmod]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    refine ⟨Or.inr ⟨hn2, Or.inr (nonempty_mulEquiv_conjR c hperm)⟩, ?_, ?_⟩
    · rw [conjR_pCoreOf, hO]
    · obtain ⟨e⟩ := hperm
      have hL48 : Nat.card Lf = 2 ^ 4 * 3 := by
        rw [Nat.card_congr e.toEquiv, hcard]; norm_num
      rw [twoPart_eq_of_card (by norm_num) hL48, hR2 hc0]
      subst hn2
      norm_num

end Block

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
