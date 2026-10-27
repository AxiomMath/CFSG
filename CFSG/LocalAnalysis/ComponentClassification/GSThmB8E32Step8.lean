module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Conf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Generic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

open S6M

abbrev fixSet (P : Set (Equiv.Perm (Fin 6))) : Set V5 := {v | ∀ t ∈ P, act t v = v}

theorem fixSet_ncard_le {P : Set (Equiv.Perm (Fin 6))} {L : List (Equiv.Perm (Fin 6))}
    (hL : ∀ t ∈ L, t ∈ P) : (fixSet P).ncard ≤ fixlen L := by
  rw [fixlen, ← ncard_eq_length]
  refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
  show (L.all fun t => veq (act t v) v) = true
  rw [List.all_eq_true]
  intro t htL
  exact veq_iff.mpr (hv t (hL t htL))

theorem card_mul_fixSet_le_of_B (P : Subgroup (Equiv.Perm (Fin 6))) (hPW : P ≤ Wsub)
    (hPc : ∀ s ∈ P, ∀ t ∈ P, s * t = t * s) {t : Equiv.Perm (Fin 6)} (htP : t ∈ P)
    (htB : t ∈ Blist) : Nat.card P * (fixSet P).ncard ≤ 16 := by
  have h2 := List.all_eq_true.mp Blist_facts.1 t htB
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨hfix8, hcent⟩, hpair⟩ := h2
  have hPC : P ≤ Csub := by
    intro s hs
    have h3 := List.all_eq_true.mp hcent s (hPW hs)
    rw [hPc s hs t htP] at h3
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h3
    exact h3
  have hdvd : Nat.card P ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [card_Csub] at this
  obtain ⟨i, hi, hiP⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_cases hex : ∃ s ∈ P, s ≠ 1 ∧ s ≠ t
  · obtain ⟨s, hs, hs1, hst⟩ := hex
    have hsC : s ∈ Clist := hPC hs
    have h4 := List.all_eq_true.mp hpair s hsC
    simp only [Bool.or_eq_true, beq_iff_eq, hs1, hst, false_or] at h4
    have hfix : (fixSet P).ncard ≤ 4 := h4 ▸ fixSet_ncard_le (L := [t, s]) (by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact htP
      · exact hs)
    interval_cases i
    · rw [hiP]; omega
    · rw [hiP]; omega
    · rw [hiP]; omega
    ·
      have hPeq : P = Csub := eq_of_le_of_card_ge hPC (by rw [card_Csub, hiP]; norm_num)
      have hfix2 : (fixSet P).ncard ≤ 2 := Blist_facts.2 ▸ fixSet_ncard_le (L := Clist) (by
        intro u hu
        rw [hPeq]
        exact hu)
      rw [hiP]
      calc 2 ^ 3 * (fixSet P).ncard ≤ 2 ^ 3 * 2 := Nat.mul_le_mul_left _ hfix2
        _ = 16 := by norm_num
  · push Not at hex
    have hcard : Nat.card P ≤ 2 := by
      have hsub : (P : Set (Equiv.Perm (Fin 6))) ⊆ {1, t} := by
        intro s hs
        by_cases hs1 : s = 1
        · exact Or.inl hs1
        · exact Or.inr (hex s hs hs1)
      calc Nat.card P = (P : Set (Equiv.Perm (Fin 6))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1, t} : Set (Equiv.Perm (Fin 6))).ncard := Set.ncard_le_ncard hsub
        _ ≤ 2 := by
          calc ({1, t} : Set (Equiv.Perm (Fin 6))).ncard ≤ ({t} : Set _).ncard + 1 :=
                Set.ncard_insert_le _ _
            _ = 2 := by rw [Set.ncard_singleton]
    have hfix : (fixSet P).ncard ≤ 8 := hfix8 ▸ fixSet_ncard_le (L := [t]) (by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rw [hu]
      exact htP)
    calc Nat.card P * (fixSet P).ncard ≤ 2 * 8 := Nat.mul_le_mul hcard hfix
      _ = 16 := by norm_num

theorem noswap_cases (P : Subgroup (Equiv.Perm (Fin 6))) (hPV : P ≤ Vsub)
    (hP : ∀ t ∈ P, t ∉ [s01, s23, s45]) : P ≤ V0sub ∨ ∀ t ∈ P, t = 1 ∨ t = t135 := by
  have hsplit : ∀ t ∈ P, t ∈ V0list ∨ t = t135 := by
    intro t ht
    have h1 := List.all_eq_true.mp Vlist_split t (hPV ht)
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1
      rcases h1 with h1 | h1 | h1 | h1
      · exact absurd (h1 ▸ (by simp : s01 ∈ [s01, s23, s45])) (hP t ht)
      · exact absurd (h1 ▸ (by simp : s23 ∈ [s01, s23, s45])) (hP t ht)
      · exact absurd (h1 ▸ (by simp : s45 ∈ [s01, s23, s45])) (hP t ht)
      · exact Or.inr h1
  by_cases h135 : t135 ∈ P
  · right
    intro t ht
    rcases hsplit t ht with h1 | h1
    · by_cases ht1 : t = 1
      · exact Or.inl ht1
      · exfalso
        have h2 := List.all_eq_true.mp t135_mul.1 t h1
        simp only [Bool.or_eq_true, beq_iff_eq, ht1, false_or, List.contains_iff_mem] at h2
        exact hP _ (mul_mem h135 ht) h2
    · exact Or.inr h1
  · left
    intro t ht
    rcases hsplit t ht with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ ht) h135

namespace E32Base

variable {X : Type} [Group X] [Finite X] (C : E32Base X)

theorem card_le_ncard {A : Subgroup X} (S : Set V5) (hA : ∀ a ∈ A, ∃ v ∈ S, C.θ v = a) :
    Nat.card A ≤ S.ncard := by
  calc Nat.card A = (A : Set X).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ (C.θ '' S).ncard := by
        refine Set.ncard_le_ncard (fun a ha => ?_) (Set.toFinite _)
        obtain ⟨v, hv, rfl⟩ := hA a ha
        exact ⟨v, hv, rfl⟩
    _ ≤ S.ncard := Set.ncard_image_le (Set.toFinite _)

theorem even_ncard : {v : V5 | isEvenB v = true}.ncard = 16 := by
  rw [ncard_eq_length]
  decide +kernel

theorem card_E0 : Nat.card C.E0 = 16 := by
  have h : (C.E0 : Set X) = C.θ '' {v | isEvenB v = true} := by
    ext e
    constructor
    · intro he
      obtain ⟨v, hv, rfl⟩ := C.mem_E0_iff.mp he
      exact ⟨v, isEvenB_iff.mpr hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact C.mem_E0_iff.mpr ⟨v, isEvenB_iff.mp hv, rfl⟩
  show Nat.card ↥((C.E0 : Set X)) = 16
  rw [h, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ C.θ_injective, even_ncard]

theorem E_sq {e : X} (he : e ∈ C.E) : e * e = 1 := by
  obtain ⟨v, rfl⟩ := C.mem_E_iff.mp he
  rw [← θ_add, C.θ_eq_one_iff]
  funext i
  exact CharTwo.add_self_eq_zero _

end E32Base

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

section Conj

variable {y : X}

theorem conj_le_W {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X)) :
    conjugate A y ≤ C.W := by
  intro f hf
  rw [mem_conjugate_iff] at hf
  have h1 := (mem_normalizer_iff.mp (inv_mem hyN) _).mp (C.E_le_W (hA hf))
  rwa [show y⁻¹ * (y * f * y⁻¹) * y⁻¹⁻¹ = f by group] at h1

theorem conj_le_N {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X)) :
    conjugate A y ≤ C.N :=
  (C.conj_le_W hA hyN).trans inf_le_right

theorem conj_E_sq {f : X} (hf : f ∈ conjugate C.E y) : f * f = 1 := by
  rw [mem_conjugate_iff] at hf
  have := C.E_sq hf
  calc f * f = y⁻¹ * ((y * f * y⁻¹) * (y * f * y⁻¹)) * y := by group
    _ = 1 := by rw [this]; group

theorem conj_E_comm {f g : X} (hf : f ∈ conjugate C.E y) (hg : g ∈ conjugate C.E y) :
    f * g = g * f := by
  rw [mem_conjugate_iff] at hf hg
  have := C.E_comm hf hg
  calc f * g = y⁻¹ * ((y * f * y⁻¹) * (y * g * y⁻¹)) * y := by group
    _ = y⁻¹ * ((y * g * y⁻¹) * (y * f * y⁻¹)) * y := by rw [this]
    _ = g * f := by group

@[expose] noncomputable def ψ {A : Subgroup X} (hA : A ≤ C.E)
    (hyN : y ∈ normalizer (C.W : Set X)) : ↥(conjugate A y) →* Equiv.Perm (Fin 6) :=
  C.π.comp (inclusion (C.conj_le_N hA hyN))

theorem mem_range_ψ {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X))
    {t : Equiv.Perm (Fin 6)} :
    t ∈ (C.ψ hA hyN).range ↔ ∃ f, ∃ hf : f ∈ conjugate A y,
      C.π ⟨f, C.conj_le_N hA hyN hf⟩ = t := by
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

theorem card_conj_eq {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X)) :
    Nat.card ↥(conjugate A y) =
      Nat.card ↥(conjugate A y ⊓ C.E) * Nat.card (C.ψ hA hyN).range := by
  have h1 := Subgroup.card_ker_mul_card_range (C.ψ hA hyN)
  have hmap : (C.ψ hA hyN).ker.map (conjugate A y).subtype = conjugate A y ⊓ C.E := by
    ext f
    constructor
    · rintro ⟨⟨f, hf⟩, hker, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hf, ?_⟩
      exact C.π_ker ⟨f, C.conj_le_N hA hyN hf⟩ ((C.conj_le_W hA hyN) hf).1 hker
    · intro hf
      obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.mp hf
      exact ⟨⟨f, hf1⟩, C.π_E (e := ⟨f, C.conj_le_N hA hyN hf1⟩) hf2, rfl⟩
  have hker : Nat.card (C.ψ hA hyN).ker = Nat.card ↥(conjugate A y ⊓ C.E) := by
    rw [← card_map_of_injective (conjugate A y).subtype_injective, hmap]
  rw [← h1, hker]

theorem fix_of_mem_conj {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X))
    {v : V5} (hv : C.θ v ∈ conjugate C.E y) :
    v ∈ fixSet ((C.ψ hA hyN).range : Set (Equiv.Perm (Fin 6))) := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ hA hyN).mp ht
  have hfE : f ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hf ⊢
    exact hA hf
  exact (C.comm_iff _ v).mp (C.conj_E_comm hfE hv)

theorem range_ψ_le_W {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X)) :
    (C.ψ hA hyN).range ≤ Wsub := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ hA hyN).mp ht
  exact C.π_W _ ((C.conj_le_W hA hyN) hf).1

theorem range_ψ_comm {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X))
    {s t : Equiv.Perm (Fin 6)} (hs : s ∈ (C.ψ hA hyN).range) (ht : t ∈ (C.ψ hA hyN).range) :
    s * t = t * s := by
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ hA hyN).mp hs
  obtain ⟨g, hg, rfl⟩ := (C.mem_range_ψ hA hyN).mp ht
  have hfE : f ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hf ⊢
    exact hA hf
  have hgE : g ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hg ⊢
    exact hA hg
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (C.conj_E_comm hfE hgE)

theorem range_ψ_sq {A : Subgroup X} (hA : A ≤ C.E) (hyN : y ∈ normalizer (C.W : Set X))
    {t : Equiv.Perm (Fin 6)} (ht : t ∈ (C.ψ hA hyN).range) : t * t = 1 := by
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ hA hyN).mp ht
  have hfE : f ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hf ⊢
    exact hA hf
  rw [← map_mul, ← map_one C.π]
  congr 1
  exact Subtype.ext (C.conj_E_sq hfE)

end Conj

theorem card_eq_ncard {A : Subgroup X} (hA : A ≤ C.E) : Nat.card A = {v | C.θ v ∈ A}.ncard := by
  have h : (A : Set X) = C.θ '' {v | C.θ v ∈ A} := by
    ext a
    constructor
    · intro ha
      obtain ⟨v, rfl⟩ := C.mem_E_iff.mp (hA ha)
      exact ⟨v, ha, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  show Nat.card ↥((A : Set X)) = _
  rw [h, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ C.θ_injective]

section Step8

variable {y : X}

theorem card_inf_le (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W) :
    Nat.card ↥(conjugate C.E y ⊓ C.E) ≤ 8 := by
  set F := conjugate C.E y with hFdef
  set K₁ := F ⊓ C.E with hK₁
  have hK1E : K₁ ≤ C.E := inf_le_right
  have hdvd : Nat.card K₁ ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le hK1E
    rwa [C.card_E] at this
  obtain ⟨i, hi, hiK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_contra hlt
  push Not at hlt
  have hF : Nat.card F = 32 := by rw [hFdef, Eight.card_conjugate_eq, C.card_E]
  have hcard : Nat.card F = Nat.card K₁ * Nat.card (C.ψ le_rfl hyN).range :=
    C.card_conj_eq le_rfl hyN
  rw [hF] at hcard
  interval_cases i
  · rw [hiK] at hlt; norm_num at hlt
  · rw [hiK] at hlt; norm_num at hlt
  · rw [hiK] at hlt; norm_num at hlt
  · rw [hiK] at hlt; norm_num at hlt
  ·
    have hPF : Nat.card (C.ψ le_rfl hyN).range = 2 := by
      rw [hiK] at hcard
      omega
    obtain ⟨t, ht, ht1⟩ := ((C.ψ le_rfl hyN).range.bot_or_exists_ne_one).resolve_left
      (fun h => by rw [h, card_bot] at hPF; norm_num at hPF)
    obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ le_rfl hyN).mp ht
    have hfW := C.conj_le_W le_rfl hyN hf
    have htW := C.π_W ⟨f, hfW.2⟩ hfW.1
    have hsub : {v | C.θ v ∈ K₁} ⊆ {v | (allV.filter fun v =>
        [C.π ⟨f, hfW.2⟩].all fun t => veq (act t v) v).contains v} := by
      intro v hv
      have := C.fix_of_mem_conj le_rfl hyN (Subgroup.mem_inf.mp hv).1 _ ht
      simp only [Set.mem_ofPred_eq, List.contains_iff_mem, List.mem_filter, mem_allV,
        List.all_cons, List.all_nil, Bool.and_true, true_and]
      exact veq_iff.mpr this
    have h16 : 16 ≤ fixlen [C.π ⟨f, hfW.2⟩] := by
      calc 16 = Nat.card K₁ := by rw [hiK]; norm_num
        _ = {v | C.θ v ∈ K₁}.ncard := C.card_eq_ncard hK1E
        _ ≤ {v | ([C.π ⟨f, hfW.2⟩].all fun t => veq (act t v) v) = true}.ncard := by
          refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
          have := hsub hv
          simp only [Set.mem_ofPred_eq, List.contains_iff_mem, List.mem_filter] at this
          exact this.2
        _ = fixlen [C.π ⟨f, hfW.2⟩] := ncard_eq_length _
    have hswap : C.π ⟨f, hfW.2⟩ ∈ [s01, s23, s45] := by
      have h1 := List.all_eq_true.mp Wlist_fix8 _ htW
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at h1
      rcases h1 with (h1 | h1) | h1
      · exact absurd h1 ht1
      · exact h1
      · omega
    have hfix16 : fixlen [C.π ⟨f, hfW.2⟩] = 16 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hswap
      rcases hswap with h1 | h1 | h1 <;> rw [h1]
      exacts [swap_fixlen.1, swap_fixlen.2.1, swap_fixlen.2.2]
    obtain ⟨e, heE, he2, hea⟩ := C.fus_a ⟨f, hfW.2⟩ hfW.1 (C.conj_E_sq hf) (isSwap_of_mem hswap)
    have hfe : f * e = e * f := by
      have hf2 := C.conj_E_sq hf
      have he2' := C.E_sq heE
      calc f * e = (e * e) * (f * e) * (f * f) := by rw [he2', hf2]; group
        _ = e * (e * f * (e * f)) * f := by group
        _ = e * f := by rw [he2]; group
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp heE
    have hv : S6M.act (C.π ⟨f, hfW.2⟩) v = v := (C.comm_iff ⟨f, hfW.2⟩ v).mp hfe
    have hTS : {v | C.θ v ∈ K₁} = {v | (([C.π ⟨f, hfW.2⟩].all fun t => veq (act t v) v)) =
        true} := by
      refine Set.eq_of_subset_of_ncard_le (fun w hw => ?_) ?_ (Set.toFinite _)
      · have := hsub hw
        simp only [Set.mem_ofPred_eq, List.contains_iff_mem, List.mem_filter] at this
        exact this.2
      · refine le_of_eq ?_
        calc {v | ([C.π ⟨f, hfW.2⟩].all fun t => veq (act t v) v) = true}.ncard
            = fixlen [C.π ⟨f, hfW.2⟩] := ncard_eq_length _
          _ = 16 := hfix16
          _ = Nat.card K₁ := by rw [hiK]; norm_num
          _ = {v | C.θ v ∈ K₁}.ncard := C.card_eq_ncard hK1E
    have hvK : C.θ v ∈ K₁ := by
      have : v ∈ {v | (([C.π ⟨f, hfW.2⟩].all fun t => veq (act t v) v)) = true} := by
        simp only [Set.mem_ofPred_eq, List.all_cons, List.all_nil, Bool.and_true]
        exact veq_iff.mpr hv
      rw [← hTS] at this
      exact this
    have hef : C.θ v * f ∈ F := mul_mem (Subgroup.mem_inf.mp hvK).1 hf
    rw [hFdef, mem_conjugate_iff] at hef
    exact hea y⁻¹ _ hef (by group)
  ·
    have h1 : K₁ = C.E := eq_of_le_of_card_ge hK1E (by rw [hiK, C.card_E]; norm_num)
    have h2 : F = C.E := by
      have hle : C.E ≤ F := h1 ▸ inf_le_left
      exact (eq_of_le_of_card_ge hle (by rw [hF, C.card_E])).symm
    apply hyW
    exact ⟨hyU, mem_normalizer_of_conjugate_eq h2⟩

theorem card_inf_mul (hyN : y ∈ normalizer (C.W : Set X)) :
    32 = Nat.card ↥(conjugate C.E y ⊓ C.E) * Nat.card (C.ψ le_rfl hyN).range := by
  rw [← C.card_E, ← Eight.card_conjugate_eq C.E y]
  exact C.card_conj_eq le_rfl hyN

theorem card_inf_mul0 (hyN : y ∈ normalizer (C.W : Set X)) :
    16 = Nat.card ↥(conjugate C.E0 y ⊓ C.E) * Nat.card (C.ψ C.E0_le_E hyN).range := by
  rw [← C.card_E0, ← Eight.card_conjugate_eq C.E0 y]
  exact C.card_conj_eq C.E0_le_E hyN

theorem card_inf_le_fix (hyN : y ∈ normalizer (C.W : Set X)) :
    Nat.card ↥(conjugate C.E y ⊓ C.E) ≤
      (fixSet ((C.ψ le_rfl hyN).range : Set (Equiv.Perm (Fin 6)))).ncard :=
  C.card_le_ncard _ fun k hk => by
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp (Subgroup.mem_inf.mp hk).2
    exact ⟨v, C.fix_of_mem_conj le_rfl hyN (Subgroup.mem_inf.mp hk).1, rfl⟩

theorem range_ψ_le_V (hyN : y ∈ normalizer (C.W : Set X)) :
    (C.ψ le_rfl hyN).range ≤ Vsub := by
  intro t ht
  have htW := C.range_ψ_le_W le_rfl hyN ht
  have hsq := C.range_ψ_sq le_rfl hyN ht
  have h1 := List.all_eq_true.mp Wlist_inv_cases t htW
  simp only [hsq, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    have hB := card_mul_fixSet_le_of_B _ (C.range_ψ_le_W le_rfl hyN)
      (fun s hs u hu => C.range_ψ_comm le_rfl hyN hs hu) ht h1
    have hK := C.card_inf_le_fix hyN
    have hcard := C.card_inf_mul hyN
    have : 32 ≤ 16 := by
      calc 32 = Nat.card ↥(conjugate C.E y ⊓ C.E) * Nat.card (C.ψ le_rfl hyN).range := hcard
        _ ≤ (fixSet ((C.ψ le_rfl hyN).range : Set (Equiv.Perm (Fin 6)))).ncard *
            Nat.card (C.ψ le_rfl hyN).range := Nat.mul_le_mul_right _ hK
        _ = Nat.card (C.ψ le_rfl hyN).range *
            (fixSet ((C.ψ le_rfl hyN).range : Set (Equiv.Perm (Fin 6)))).ncard := mul_comm _ _
        _ ≤ 16 := hB
    omega

theorem range_ψ0_le (hyN : y ∈ normalizer (C.W : Set X)) :
    (C.ψ C.E0_le_E hyN).range ≤ (C.ψ le_rfl hyN).range := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ _ hyN).mp ht
  have hfE : f ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hf ⊢
    exact C.E0_le_E hf
  exact (C.mem_range_ψ le_rfl hyN).mpr ⟨f, hfE, rfl⟩

theorem range_ψ0_noswap (hyN : y ∈ normalizer (C.W : Set X)) :
    ∀ t ∈ (C.ψ C.E0_le_E hyN).range, t ∉ [s01, s23, s45] := by
  intro t ht hts
  obtain ⟨f, hf, rfl⟩ := (C.mem_range_ψ _ hyN).mp ht
  have hfW := C.conj_le_W C.E0_le_E hyN hf
  rw [mem_conjugate_iff] at hf
  have hfe : f = y⁻¹ * (y * f * y⁻¹) * y := by group
  by_cases he1 : y * f * y⁻¹ = 1
  · have hf1 : f = 1 := by rw [hfe, he1]; group
    have : C.π ⟨f, C.conj_le_N C.E0_le_E hyN (by rwa [mem_conjugate_iff])⟩ = 1 := by
      rw [← map_one C.π]
      congr 1
      exact Subtype.ext hf1
    rw [this] at hts
    exact one_not_mem_swaps hts
  · exact C.fus_z _ hf he1 y _ hfe hfW.1 (isSwap_of_mem hts)

theorem card_inf0_le (hyN : y ∈ normalizer (C.W : Set X)) {P : List (Equiv.Perm (Fin 6))}
    (hP : ∀ t ∈ P, t ∈ (C.ψ C.E0_le_E hyN).range) :
    Nat.card ↥(conjugate C.E0 y ⊓ C.E) ≤
      {v : V5 | (isEvenB v && P.all fun t => veq (act t v) v) = true}.ncard := by
  refine C.card_le_ncard _ fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
  have hk0 : k ∈ C.E0 := by
    have h1 := mem_conjugate_iff.mp hk1
    have h2 := C.fus_sc _ h1 y (by rwa [show y⁻¹ * (y * k * y⁻¹) * y = k by group])
    rwa [show y⁻¹ * (y * k * y⁻¹) * y = k by group] at h2
  obtain ⟨v, hv, rfl⟩ := C.mem_E0_iff.mp hk0
  have hvE : C.θ v ∈ conjugate C.E y := by
    rw [mem_conjugate_iff] at hk1 ⊢
    exact C.E0_le_E hk1
  refine ⟨v, ?_, rfl⟩
  simp only [Set.mem_ofPred_eq, Bool.and_eq_true, isEvenB_iff.mpr hv, true_and,
    List.all_eq_true]
  intro t ht
  exact veq_iff.mpr (C.fix_of_mem_conj C.E0_le_E hyN hvE t (hP t ht))

theorem conj_E0_le (y : X) : conjugate C.E0 y ≤ conjugate C.E y := fun f hf => by
  rw [mem_conjugate_iff] at hf ⊢
  exact C.E0_le_E hf

theorem ncard_pair_le {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  calc ({a, b} : Set α).ncard ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

theorem range_ψ0_eq (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W) :
    (C.ψ C.E0_le_E hyN).range = V0sub := by
  set P₀ := (C.ψ C.E0_le_E hyN).range with hP₀
  have hP₀V : P₀ ≤ Vsub := (C.range_ψ0_le hyN).trans (C.range_ψ_le_V hyN)
  have hcard := C.card_inf_mul0 hyN
  have hle8 : Nat.card ↥(conjugate C.E0 y ⊓ C.E) ≤ 8 :=
    (card_le_of_le (inf_le_inf_right _ (C.conj_E0_le y))).trans (C.card_inf_le hyU hyN hyW)
  have hP2 : 2 ≤ Nat.card P₀ := by
    by_contra h
    push Not at h
    have : Nat.card P₀ ≤ 1 := by omega
    have h1 : 16 ≤ 8 * 1 := by
      calc 16 = Nat.card ↥(conjugate C.E0 y ⊓ C.E) * Nat.card P₀ := hcard
        _ ≤ 8 * 1 := Nat.mul_le_mul hle8 this
    omega
  have hne : P₀ ≠ ⊥ := fun h => by rw [h, card_bot] at hP2; omega
  obtain ⟨t, ht, ht1⟩ := P₀.bot_or_exists_ne_one.resolve_left hne
  rcases noswap_cases P₀ hP₀V (C.range_ψ0_noswap hyN) with h | h
  · have hdvd : Nat.card P₀ ∣ 2 ^ 2 := by
      have := Subgroup.card_dvd_of_le h
      rwa [card_V0sub] at this
    obtain ⟨i, hi, hiP⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases i
    · rw [hiP] at hP2; norm_num at hP2
    · exfalso
      have h1 := C.card_inf0_le hyN (P := [t]) (fun u hu => by
        rw [List.mem_singleton] at hu
        rw [hu]
        exact ht)
      have h2 := evenfix_V0_le (h ht) ht1
      simp only [List.all_cons, List.all_nil, Bool.and_true] at h1
      rw [hiP] at hcard
      omega
    · exact eq_of_le_of_card_ge h (by rw [card_V0sub, hiP]; norm_num)
  · exfalso
    have hcard2 : Nat.card P₀ ≤ 2 := by
      calc Nat.card P₀ = (P₀ : Set (Equiv.Perm (Fin 6))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1, t135} : Set (Equiv.Perm (Fin 6))).ncard :=
            Set.ncard_le_ncard (fun s hs => h s hs) (Set.toFinite _)
        _ ≤ 2 := ncard_pair_le _ _
    have ht135 : t = t135 := (h t ht).resolve_left ht1
    have h1 := C.card_inf0_le hyN (P := [t135]) (fun u hu => by
      rw [List.mem_singleton] at hu
      rw [hu, ← ht135]
      exact ht)
    have h2 : {v : V5 | (isEvenB v && [t135].all fun t => veq (act t v) v) = true}.ncard = 4 := by
      rw [ncard_eq_length]
      exact t135_facts.1
    have hP : Nat.card P₀ = 2 := le_antisymm hcard2 hP2
    rw [hP] at hcard
    omega

theorem range_ψ_eq (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W) :
    (C.ψ le_rfl hyN).range = Vsub := by
  set P := (C.ψ le_rfl hyN).range with hP
  have hPV : P ≤ Vsub := C.range_ψ_le_V hyN
  have h0 : V0sub ≤ P := (C.range_ψ0_eq hyU hyN hyW) ▸ C.range_ψ0_le hyN
  have hdvd : Nat.card P ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le hPV
    rwa [card_Vsub] at this
  have h4 : 4 ≤ Nat.card P := by
    rw [← card_V0sub]
    exact card_le_of_le h0
  obtain ⟨i, hi, hiP⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases i
  · rw [hiP] at h4; norm_num at h4
  · rw [hiP] at h4; norm_num at h4
  · exfalso
    have hPeq : P = V0sub := (eq_of_le_of_card_ge h0 (by rw [card_V0sub, hiP]; norm_num)).symm
    have hK : Nat.card ↥(conjugate C.E y ⊓ C.E) ≤ (fixSet (P : Set (Equiv.Perm (Fin 6)))).ncard :=
      C.card_inf_le_fix hyN
    have hfix : (fixSet (P : Set (Equiv.Perm (Fin 6)))).ncard ≤ 4 := by
      rw [← t135_facts.2]
      refine fixSet_ncard_le fun u hu => ?_
      rw [hPeq]
      exact hu
    have hcard := C.card_inf_mul hyN
    have hP4 : Nat.card P = 4 := by rw [hiP]; norm_num
    rw [← hP, hP4] at hcard
    omega
  · exact eq_of_le_of_card_ge hPV (by rw [card_Vsub, hiP]; norm_num)

theorem mem_inf_iff (hyU : y ∈ C.U) (hyN : y ∈ normalizer (C.W : Set X)) (hyW : y ∉ C.W)
    {k : X} : k ∈ conjugate C.E y ⊓ C.E ↔ ∃ v ∈ Klist, C.θ v = k := by
  have hPeq := C.range_ψ_eq hyU hyN hyW
  have hsub : ∀ v, C.θ v ∈ conjugate C.E y ⊓ C.E → v ∈ Klist := by
    intro v hv
    have hfix := C.fix_of_mem_conj le_rfl hyN (Subgroup.mem_inf.mp hv).1
    rw [hPeq] at hfix
    have h1 := List.all_eq_true.mp Vlist_fix.1 v (mem_allV v)
    have h2 : (Vlist.all fun t => veq (act t v) v) = true :=
      List.all_eq_true.mpr fun t ht => veq_iff.mpr (hfix t ht)
    simpa [h2] using h1
  constructor
  · intro hk
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp (Subgroup.mem_inf.mp hk).2
    exact ⟨v, hsub v hk, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hcard := C.card_inf_mul hyN
    rw [C.range_ψ_eq hyU hyN hyW, card_Vsub] at hcard
    have hK4 : Nat.card ↥(conjugate C.E y ⊓ C.E) = 4 := by omega
    have heq : {w | C.θ w ∈ conjugate C.E y ⊓ C.E} = {w : V5 | w ∈ Klist} :=
      Set.eq_of_subset_of_ncard_le (fun w hw => hsub w hw)
        (by rw [Klist_ncard, ← C.card_eq_ncard inf_le_right, hK4]) (Set.toFinite _)
    have : v ∈ {w | C.θ w ∈ conjugate C.E y ⊓ C.E} := by
      rw [heq]
      exact hv
    exact this

end Step8

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
