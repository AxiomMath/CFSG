module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups Matrix.SpecialLinearGroup

section Decomp

variable {G : Type*} [Group G]

theorem hall_sylow_decomp [Finite G] {K P D : Subgroup G} (hP : IsSylowTwoOf P K)
    (hN : K ≤ Subgroup.normalizer (P : Set G)) (hD : IsHallTwoPrimeOf D K) :
    D ⊓ P = ⊥ ∧ P ⊔ D = K ∧ ∀ k ∈ K, ∃ p ∈ P, ∃ d ∈ D, k = p * d := by
  obtain ⟨hDK, hodd, e, he⟩ := hD
  have h2 : ¬ 2 ∣ Nat.card D := hodd.not_two_dvd_nat
  have hKcard : Nat.card K = 2 ^ e * Nat.card D := by
    have := Subgroup.relIndex_mul_card (H := D) (K := K)
    rw [inf_eq_left.mpr hDK, he] at this
    exact this.symm
  have hPcard : Nat.card P = 2 ^ e := by
    rw [hP.card_eq]
    unfold twoPart
    rw [hKcard, Nat.factorization_mul (by positivity) Nat.card_pos.ne']
    simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd h2,
      Nat.Prime.factorization_self Nat.prime_two]
  have hDP : D ⊓ P = ⊥ := by
    have h1 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.card D := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
      rw [hPcard]
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)).symm
    have h4 : Nat.card (D ⊓ P : Subgroup G) ∣ Nat.gcd (Nat.card D) (Nat.card P) :=
      Nat.dvd_gcd h1 h3
    rw [Nat.Coprime.gcd_eq_one hcop] at h4
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_one h4)
  have hDN : D ≤ Subgroup.normalizer (P : Set G) := hDK.trans hN
  have hcardsup := card_sup_mul_card_inf hDN
  rw [hDP, Subgroup.card_bot, mul_one] at hcardsup
  have hsupK : P ⊔ D = K := by
    have hle : P ⊔ D ≤ K := sup_le hP.le hDK
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [sup_comm, hcardsup, hKcard, hPcard]
    exact le_of_eq (mul_comm _ _)
  refine ⟨hDP, hsupK, fun k hk => ?_⟩
  rw [← hsupK] at hk
  obtain ⟨p, hp, d, hd, hpd⟩ := (mem_sup_iff_of_le_normalizer hDN).1 hk
  exact ⟨p, hp, d, hd, hpd⟩

end Decomp

section Borel

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.one_pos (h : Lin2Cfg G T M H S L n D) : 0 < n := by
  have := h.one_lt
  omega

theorem Lin2Cfg.coord (h : Lin2Cfg G T M H S L n D) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Nonempty (Adapted L (S ⊓ L) n F) :=
  exists_adapted h.one_pos h.lin2 (isSylowTwoOf_S_inf_L h.cs)

theorem Lin2Cfg.S_le_normalizer_inf (h : Lin2Cfg G T M H S L n D) :
    S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hsL := Subgroup.mem_normalizer_iff.1 (h.S_le_normalizer hs) y
  constructor
  · rintro ⟨hyS, hyL⟩
    exact ⟨S.mul_mem (S.mul_mem hs hyS) (S.inv_mem hs), hsL.1 hyL⟩
  · rintro ⟨hyS, hyL⟩
    refine ⟨?_, hsL.2 hyL⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem hs) hyS) hs
    simpa [mul_assoc] using this

theorem Lin2Cfg.normalizer_inf_le_M (h : Lin2Cfg G T M H S L n D) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ M := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  set K : Subgroup G := L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) with hK
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (h.S_le_normalizer hs) y).1 hy.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.S_le_normalizer_inf hs) hy.2)
        (Subgroup.inv_mem _ (h.S_le_normalizer_inf hs))
  have hKH : K ≤ H := inf_le_left.trans h.L_le_H
  have hXH : K ⊔ S ≤ H := sup_le hKH h.S_le_H
  have hXne : K ⊔ S ≠ H := by
    intro hX
    apply A.not_le_normalizer
    intro ℓ hℓ
    have hℓX : ℓ ∈ K ⊔ S := hX ▸ h.L_le_H hℓ
    obtain ⟨k, hk, s, hs, rfl⟩ := (mem_sup_iff_of_le_normalizer hSK).1 hℓX
    have hsL : s ∈ L := by
      have := L.mul_mem (L.inv_mem hk.1) hℓ
      simpa using this
    have hsK : s ∈ K := ⟨hsL, Subgroup.le_normalizer ⟨hs, hsL⟩⟩
    exact (K.mul_mem hk hsK).2
  have hXlt : K ⊔ S < H := lt_of_le_of_ne hXH hXne
  exact le_sup_left.trans (h.cs.maxInf (K ⊔ S) le_sup_right hXlt)

theorem Lin2Cfg.inf_M_eq (h : Lin2Cfg G T M H S L n D) :
    L ⊓ M = L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
  le_antisymm (le_inf inf_le_left
    (L_inf_M_le_normalizer h.cs h.one_pos h.lin2)) (le_inf inf_le_left h.normalizer_inf_le_M)

theorem Lin2Cfg.S_inf_L_le (h : Lin2Cfg G T M H S L n D) : S ⊓ L ≤ L ⊓ M :=
  le_inf inf_le_right (inf_le_left.trans (S_le_M h.cs))

theorem Lin2Cfg.isSylowTwoOf_inf_M (h : Lin2Cfg G T M H S L n D) :
    IsSylowTwoOf (S ⊓ L) (L ⊓ M) :=
  isSylowTwoOf_of_le_of_le (isSylowTwoOf_S_inf_L h.cs) h.S_inf_L_le inf_le_left

theorem Lin2Cfg.inf_M_le_normalizer (h : Lin2Cfg G T M H S L n D) :
    L ⊓ M ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
  h.inf_M_eq.le.trans inf_le_right

theorem Lin2Cfg.decomp (h : Lin2Cfg G T M H S L n D) :
    D ⊓ (S ⊓ L) = ⊥ ∧ (S ⊓ L) ⊔ D = L ⊓ M ∧
      ∀ k ∈ L ⊓ M, ∃ p ∈ S ⊓ L, ∃ d ∈ D, k = p * d :=
  hall_sylow_decomp h.isSylowTwoOf_inf_M h.inf_M_le_normalizer h.hall

end Borel

end CFSG.QuasithinUnique.Lin2
