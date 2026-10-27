module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltIdent

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical

section Perm

variable {n : ℕ}

theorem exists_two_ge_four (hn : 7 ≤ n) (i : Fin n) :
    ∃ s s' : Fin n, 4 ≤ (s : ℕ) ∧ 4 ≤ (s' : ℕ) ∧ s ≠ i ∧ s' ≠ i ∧ s ≠ s' := by
  set a : Fin n := ⟨4, by omega⟩
  set b : Fin n := ⟨5, by omega⟩
  set c : Fin n := ⟨6, by omega⟩
  by_cases hia : i = a
  · refine ⟨b, c, by simp [b], by simp [c], ?_, ?_, ?_⟩ <;> simp [hia, a, b, c, Fin.ext_iff]
  · by_cases hib : i = b
    · refine ⟨a, c, by simp [a], by simp [c], ?_, ?_, ?_⟩ <;> simp [hib, a, b, c, Fin.ext_iff]
    · refine ⟨a, b, by simp [a], by simp [b], fun h => hia h.symm, fun h => hib h.symm, ?_⟩
      simp [a, b, Fin.ext_iff]

theorem fix_of_commute_swaps (hn : 7 ≤ n) {φ : Perm (Fin n)}
    (hφ : ∀ a b : Fin n, 4 ≤ (a : ℕ) → 4 ≤ (b : ℕ) → a ≠ b → Commute φ (swap a b)) {i : Fin n}
    (hi : 4 ≤ (i : ℕ)) : φ i = i := by
  have key : ∀ s : Fin n, 4 ≤ (s : ℕ) → s ≠ i → φ i = i ∨ φ i = s := by
    intro s hs hsi
    by_contra hcon
    push Not at hcon
    have e := apply_apply_of_commute (hφ i s hi hs hsi.symm) i
    rw [swap_apply_left, swap_apply_of_ne_of_ne hcon.1 hcon.2] at e
    exact hsi (φ.injective e)
  obtain ⟨s, s', hs, hs', hsi, hs'i, hss⟩ := exists_two_ge_four hn i
  rcases key s hs hsi with h | h
  · exact h
  · rcases key s' hs' hs'i with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hss

theorem restrictO_swap01_mul_swap (h4 : 4 ≤ n) {a b : Fin n} (ha : 4 ≤ (a : ℕ))
    (hb : 4 ≤ (b : ℕ)) :
    StabO (swap (fourEmb h4 0) (fourEmb h4 1) * swap a b) ∧
      restrictO (swap (fourEmb h4 0) (fourEmb h4 1) * swap a b) = swap a b := by
  have hsab : StabO (swap a b) := by
    intro i
    by_cases hia : i = a
    · subst hia
      rw [swap_apply_left]
      exact ⟨fun _ => ha, fun _ => hb⟩
    · by_cases hib : i = b
      · subst hib
        rw [swap_apply_right]
        exact ⟨fun _ => hb, fun _ => ha⟩
      · rw [swap_apply_of_ne_of_ne hia hib]
  have hs := stabO_mul (stabO_swap01 h4) hsab
  refine ⟨hs, ?_⟩
  apply Equiv.ext
  intro i
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [restrictO_apply_of_ge hs hi, Perm.mul_apply, swap_apply_of_ne_of_ne]
    · intro he
      have := congrArg (fun x : Fin n => (x : ℕ)) he
      simp only [fourEmb_apply] at this
      have := (hsab i).mpr hi
      omega
    · intro he
      have := congrArg (fun x : Fin n => (x : ℕ)) he
      simp only [fourEmb_apply] at this
      have := (hsab i).mpr hi
      omega
  · push Not at hi
    rw [restrictO_apply_of_lt hs hi, swap_apply_of_ne_of_ne]
    · intro he
      rw [he] at hi
      omega
    · intro he
      rw [he] at hi
      omega

theorem exists_kOf_of_mem_kleinFour {x : Perm (Fin 4)} (hx : x ∈ kleinFour) : ∃ i, x = kOf i := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  | one => exact ⟨0, rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, rfl⟩ := ihx
    obtain ⟨j, rfl⟩ := ihy
    have : ∀ i j : Fin 4, ∃ k, kOf i * kOf j = kOf k := by decide
    exact this i j
  | inv x _ ih =>
    obtain ⟨i, rfl⟩ := ih
    have : ∀ i : Fin 4, ∃ k, (kOf i)⁻¹ = kOf k := by decide
    exact this i

theorem mul_self_of_mem_kleinFour {x : Perm (Fin 4)} (hx : x ∈ kleinFour) : x * x = 1 := by
  obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hx
  have : ∀ i : Fin 4, kOf i * kOf i = 1 := by decide
  exact this i

theorem mul_self_of_commute_kleinFour : ∀ a : Perm (Fin 4),
    a * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * a →
      a * (swap 0 2 * swap 1 3) = (swap 0 2 * swap 1 3) * a → a * a = 1 := by
  decide

end Perm

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_odd_of_mul_self {M : Type*} [Group M] {x : M} (hodd : Odd (orderOf x))
    (h2 : x * x = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n) (hc : Sec3 A R T g)
include np hc

@[expose] def HasRestrictO (hn : 7 ≤ n) : Prop :=
  ∀ (x : normalizer (A : Set G)) (hx : (x : G) ∈ A) (hs : StabO (np.ψA x)),
    np.ψB ⟨x, np.mem_normalizer_B_of_stabO hc hn hx hs⟩ = restrictO (np.ψA x)

omit np in
theorem centralizer_le_normalizer_B (hTA : T ≤ A) :
    Subgroup.centralizer (A : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
  intro k hk
  apply normalizer_T_le hc
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro t ht
  exact (mem_centralizer_iff.mp hk t (hTA ht))

theorem ψB_fix_of_mem_K (hn : 7 ≤ n) (h1 : np.HasRestrictO hc hn) {k : G}
    (hk : k ∈ Subgroup.centralizer (A : Set G)) {i : Fin n} (hi : 4 ≤ (i : ℕ)) :
    np.ψB ⟨k, centralizer_le_normalizer_B hc np.le_A hk⟩ i = i := by
  have h4 : 4 ≤ n := by omega
  refine fix_of_commute_swaps hn (fun a b ha hb hab => ?_) hi
  obtain ⟨hs, hres⟩ := restrictO_swap01_mul_swap h4 ha hb
  have hmem := mul_swap_mem_alternatingGroup (fourEmb h4) hab (show (0 : Fin 4) ≠ 1 by decide)
  rw [viaEmbeddingHom_swap] at hmem
  obtain ⟨x, hxA, hxe⟩ := np.hψA.exists_eq _ hmem
  have hs' : StabO (np.ψA ⟨x, le_normalizer hxA⟩) := by rw [hxe]; exact hs
  have hψBx := h1 ⟨x, le_normalizer hxA⟩ hxA hs'
  rw [hxe, hres] at hψBx
  rw [← hψBx, Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_iff.mp hk x hxA).symm

theorem le_of_odd_normal (hn : 7 ≤ n) (h1 : np.HasRestrictO hc hn) {N : Subgroup G}
    (hNK : N ≤ Subgroup.centralizer (A : Set G))
    (hNn : ∀ k ∈ Subgroup.centralizer (A : Set G), ∀ m ∈ N, k * m * k⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ Subgroup.centralizer (rightConjugate A g : Set G) := by
  have h4 : 4 ≤ n := by omega
  have hoddOf : ∀ m ∈ N, Odd (orderOf m) := fun m hm =>
    hodd.of_dvd_nat (N.orderOf_dvd_natCard hm)
  intro m hm
  set mB : normalizer (rightConjugate A g : Set G) :=
    ⟨m, centralizer_le_normalizer_B hc np.le_A (hNK hm)⟩
  have hfixO : ∀ i : Fin n, 4 ≤ (i : ℕ) → np.ψB mB i = i := fun i hi =>
    np.ψB_fix_of_mem_K hc hn h1 (hNK hm) hi
  have hoddψ : Odd (orderOf (np.ψB mB)) :=
    (hoddOf m hm).of_dvd_nat ((orderOf_map_dvd np.ψB mB).trans (orderOf_mk m _).dvd)
  have heven : np.ψB mB ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup]
    have h := congrArg sign (pow_orderOf_eq_one (np.ψB mB))
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (sign (np.ψB mB)) with hs | hs
    · exact hs
    · rw [hs, hoddψ.neg_one_pow] at h
      exact absurd h (by decide)
  have hAlt := mem_rootAltP_of_fix h4 heven hfixO
  rw [rootAltP_eq h4] at hAlt
  obtain ⟨a, ha, hae⟩ := hAlt
  have hcomm : ∀ v ∈ kleinFour, a * v = v * a := by
    intro v hv
    obtain ⟨r, hr, hre⟩ := np.exists_R_of_mem (show viaEmbeddingHom (fourEmb h4) v ∈ rootVP n by
      rw [rootVP_eq h4]
      exact ⟨v, hv, rfl⟩)
    have hrK : (r : G) ∈ Subgroup.centralizer (A : Set G) := hc.sylowR.le hr
    set w : normalizer (rightConjugate A g : Set G) := mB * r * mB⁻¹ * r⁻¹
    have hw : (w : G) ∈ N := by
      show m * (r : G) * m⁻¹ * (r : G)⁻¹ ∈ N
      have h2 := hNn _ hrK _ (inv_mem hm)
      have h3 : m * (r : G) * m⁻¹ * (r : G)⁻¹ = m * ((r : G) * m⁻¹ * (r : G)⁻¹) := by group
      rw [h3]
      exact mul_mem hm h2
    have hwψ : np.ψB w = viaEmbeddingHom (fourEmb h4) (a * v * a⁻¹ * v⁻¹) := by
      simp only [w, map_mul, map_inv, hre, ← hae]
    have hwV : a * v * a⁻¹ * v⁻¹ ∈ kleinFour :=
      mul_mem (conj_mem_kleinFour a hv) (inv_mem hv)
    have hoddw : Odd (orderOf (np.ψB w)) :=
      (hoddOf _ hw).of_dvd_nat ((orderOf_map_dvd np.ψB w).trans (orderOf_coe w).symm.dvd)
    rw [hwψ] at hoddw
    have h1' : viaEmbeddingHom (fourEmb h4) (a * v * a⁻¹ * v⁻¹) = 1 :=
      eq_one_of_odd_of_mul_self hoddw (by rw [← map_mul, mul_self_of_mem_kleinFour hwV, map_one])
    have h2' : a * v * a⁻¹ * v⁻¹ = 1 :=
      (viaEmbeddingHom_injective (fourEmb h4)) (h1'.trans (map_one _).symm)
    calc a * v = (a * v * a⁻¹ * v⁻¹) * v * a := by group
      _ = v * a := by rw [h2', one_mul]
  have ha2 : a * a = 1 :=
    mul_self_of_commute_kleinFour a (hcomm _ swap_mem_kleinFour_one)
      (hcomm _ swap_mem_kleinFour_two)
  have hψ1 : np.ψB mB = 1 := by
    rw [← hae] at hoddψ ⊢
    exact eq_one_of_odd_of_mul_self hoddψ (by rw [← map_mul, ha2, map_one])
  exact (np.hψB.eq_one_iff mB).mp hψ1

theorem normalizer_le_inf (hn : 7 ≤ n) (h1 : np.HasRestrictO hc hn) :
    normalizer (A : Set G) ≤ normalizer ((Subgroup.centralizer (A : Set G) ⊓
      Subgroup.centralizer (rightConjugate A g : Set G) : Subgroup G) : Set G) := by
  intro x hx
  set K := Subgroup.centralizer (A : Set G)
  set Kg := Subgroup.centralizer (rightConjugate A g : Set G)
  have hxK : x ∈ normalizer (K : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hx
  have hKN : ∀ k ∈ K, ∀ m ∈ K ⊓ Kg, k * m * k⁻¹ ∈ K ⊓ Kg := by
    intro k hk m hm
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hm.1) (inv_mem hk), ?_⟩
    have hkB := centralizer_le_normalizer_B hc np.le_A hk
    have hKgN : k ∈ normalizer (Kg : Set G) :=
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _) hkB
    exact (mem_normalizer_iff.mp hKgN m).mp hm.2
  set N := (K ⊓ Kg).map (MulAut.conj x).toMonoidHom
  have hNK : N ≤ K := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.mp hxK m).mp hm.1
  have hNn : ∀ k ∈ K, ∀ m ∈ N, k * m * k⁻¹ ∈ N := by
    rintro k hk _ ⟨m, hm, rfl⟩
    have hk' : x⁻¹ * k * x ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hxK) k).mp hk
      simpa using this
    refine ⟨x⁻¹ * k * x * m * (x⁻¹ * k * x)⁻¹, hKN _ hk' _ hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hoddN : Odd (Nat.card N) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hKt := tightlyEmbedded_centralizer_of_standard hc.hyp.standard
    have h := hKt.2 g (by rw [normalizer_centralizer_eq hc.hyp.standard]; exact hc.not_mem)
    rwa [← centralizer_rightConjugate] at h
  have hle := np.le_of_odd_normal hc hn h1 hNK hNn hoddN
  apply mem_normalizer_of_conj_mem
  intro m hm
  exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hxK m).mp hm.1, hle ⟨m, hm, rfl⟩⟩

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
