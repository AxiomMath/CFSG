module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical

section Perm

abbrev OSet (n : ℕ) : Type := {i : Fin n // 4 ≤ (i : ℕ)}

theorem perm_inv_apply {α : Type*} (σ : Perm α) (a : α) : σ⁻¹ (σ a) = a :=
  σ.symm_apply_apply a

theorem exists_restrict {α : Type*} {k : ℕ} (ι : Fin k ↪ α) {π : Perm α}
    (hπ : ∀ j, π (ι j) ∈ Set.range ι) : ∃ κ : Perm (Fin k), ∀ j, π (ι j) = ι (κ j) := by
  choose f hf using hπ
  have hinj : Function.Injective f := fun a b hab =>
    ι.injective (π.injective (by rw [← hf, ← hf, hab]))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun j => ?_⟩
  rw [Equiv.ofBijective_apply, hf]

variable {n : ℕ} (h : 4 ≤ n)

theorem mem_range_fourEmb_iff {i : Fin n} : i ∈ Set.range (fourEmb h) ↔ (i : ℕ) < 4 := by
  constructor
  · rintro ⟨j, rfl⟩
    rw [fourEmb_apply]
    exact j.2
  · intro hi
    exact ⟨⟨i, hi⟩, Fin.ext rfl⟩

theorem stab_of_stabO {π : Perm (Fin n)} (hπ : StabO π) (j : Fin 4) :
    π (fourEmb h j) ∈ Set.range (fourEmb h) := by
  rw [mem_range_fourEmb_iff]
  have h1 := hπ (fourEmb h j)
  rw [fourEmb_apply] at h1
  by_contra hc
  push Not at hc
  have := h1.mp hc
  have := j.2
  omega

theorem normalizesV_of_stabO {π : Perm (Fin n)} (hπ : StabO π) : NormalizesV h π := by
  obtain ⟨κ, hκ⟩ := exists_restrict (fourEmb h) (stab_of_stabO h hπ)
  set ρ := (viaEmbeddingHom (fourEmb h) κ)⁻¹ * π with hρdef
  have hρ : ∀ j, ρ (fourEmb h j) = fourEmb h j := by
    intro j
    rw [hρdef, Perm.mul_apply, hκ, Perm.inv_eq_iff_eq, viaEmbeddingHom_apply_image]
  have hπρ : π = viaEmbeddingHom (fourEmb h) κ * ρ := by rw [hρdef]; group
  intro m hm
  have e : π * viaEmbeddingHom (fourEmb h) m * π⁻¹ = viaEmbeddingHom (fourEmb h) (κ * m * κ⁻¹) := by
    rw [hπρ, map_mul, map_mul, map_inv]
    calc viaEmbeddingHom (fourEmb h) κ * ρ * viaEmbeddingHom (fourEmb h) m *
          (viaEmbeddingHom (fourEmb h) κ * ρ)⁻¹
        = viaEmbeddingHom (fourEmb h) κ * (ρ * viaEmbeddingHom (fourEmb h) m * ρ⁻¹) *
            (viaEmbeddingHom (fourEmb h) κ)⁻¹ := by group
      _ = viaEmbeddingHom (fourEmb h) κ * viaEmbeddingHom (fourEmb h) m *
            (viaEmbeddingHom (fourEmb h) κ)⁻¹ := by
          rw [(commute_of_apply_eq (fourEmb h) hρ m).eq, mul_inv_cancel_right]
  rw [e, rootVP_eq h]
  exact ⟨_, conj_mem_kleinFour κ hm, rfl⟩

include h in
theorem mem_rootAltP_of_fix {π : Perm (Fin n)} (hπA : π ∈ alternatingGroup (Fin n))
    (hfix : ∀ i : Fin n, 4 ≤ (i : ℕ) → π i = i) : π ∈ rootAltP n := by
  have hstab : StabO π := by
    intro i
    by_cases hi : 4 ≤ (i : ℕ)
    · rw [hfix i hi]
    · constructor
      · intro h'
        have h2 := hfix _ h'
        rw [π.injective h2] at h'
        exact absurd h' hi
      · intro h'
        exact absurd h' hi
  obtain ⟨κ, hκ⟩ := exists_restrict (fourEmb h) (stab_of_stabO h hstab)
  have heq : π = viaEmbeddingHom (fourEmb h) κ := by
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ Set.range (fourEmb h)
    · obtain ⟨j, rfl⟩ := hi
      rw [hκ, viaEmbeddingHom_apply_image]
    · rw [viaEmbeddingHom_apply_of_notMem _ _ hi]
      rw [mem_range_fourEmb_iff] at hi
      exact hfix i (by omega)
  rw [rootAltP_eq h]
  refine ⟨κ, (?_ : κ ∈ alternatingGroup (Fin 4)), heq.symm⟩
  rw [mem_alternatingGroup, ← sign_viaEmbeddingHom (fourEmb h), ← heq]
  exact hπA

omit h in
theorem stabO_mul {π π' : Perm (Fin n)} (hπ : StabO π) (hπ' : StabO π') : StabO (π * π') :=
  fun i => by rw [Perm.mul_apply, hπ, hπ']

omit h in
theorem stabO_inv {π : Perm (Fin n)} (hπ : StabO π) : StabO π⁻¹ := fun i => by
  rw [← hπ (π⁻¹ i), perm_apply_inv]

omit h in
theorem restrictO_mul {π π' : Perm (Fin n)} (hπ : StabO π) (hπ' : StabO π') :
    restrictO (π * π') = restrictO π * restrictO π' := by
  have hππ' := stabO_mul hπ hπ'
  apply Equiv.ext
  intro i
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [Perm.mul_apply, restrictO_apply_of_ge hππ' hi, restrictO_apply_of_ge hπ' hi,
      restrictO_apply_of_ge hπ ((hπ' i).mpr hi), Perm.mul_apply]
  · push Not at hi
    rw [Perm.mul_apply, restrictO_apply_of_lt hππ' hi, restrictO_apply_of_lt hπ' hi,
      restrictO_apply_of_lt hπ hi]

omit h in
theorem stabO_ofSubtype (q : Perm (OSet n)) : StabO (ofSubtype q) := fun i =>
  ofSubtype_apply_mem_iff_mem q i

@[expose] noncomputable def liftO (q : Perm (OSet n)) : Perm (Fin n) :=
  if sign (ofSubtype q) = 1 then ofSubtype q else swap (fourEmb h 0) (fourEmb h 1) * ofSubtype q

theorem stabO_swap01 : StabO (swap (fourEmb h 0) (fourEmb h 1)) := by
  intro i
  by_cases h0 : i = fourEmb h 0
  · subst h0
    rw [swap_apply_left, fourEmb_apply, fourEmb_apply]
    simp
  · by_cases h1 : i = fourEmb h 1
    · subst h1
      rw [swap_apply_right, fourEmb_apply, fourEmb_apply]
      simp
    · rw [swap_apply_of_ne_of_ne h0 h1]

theorem liftO_mem (q : Perm (OSet n)) : liftO h q ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, liftO]
  split_ifs with hs
  · exact hs
  · rw [Perm.sign_mul, sign_swap ((fourEmb h).injective.ne (by decide))]
    rcases Int.units_eq_one_or (sign (ofSubtype q)) with h1 | h1
    · exact absurd h1 hs
    · rw [h1]
      rfl

theorem stabO_liftO (q : Perm (OSet n)) : StabO (liftO h q) := by
  rw [liftO]
  split_ifs
  · exact stabO_ofSubtype q
  · exact stabO_mul (stabO_swap01 h) (stabO_ofSubtype q)

theorem liftO_apply_of_ge (q : Perm (OSet n)) {i : Fin n} (hi : 4 ≤ (i : ℕ)) :
    liftO h q i = ofSubtype q i := by
  rw [liftO]
  split_ifs
  · rfl
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne]
    · intro he
      have := congrArg (fun x : Fin n => (x : ℕ)) he
      simp only [fourEmb_apply] at this
      have := (ofSubtype_apply_mem_iff_mem q i).mpr hi
      omega
    · intro he
      have := congrArg (fun x : Fin n => (x : ℕ)) he
      simp only [fourEmb_apply] at this
      have := (ofSubtype_apply_mem_iff_mem q i).mpr hi
      omega

omit h in
theorem card_OSet : Fintype.card (OSet n) = n - 4 := by
  let e : OSet n ≃ Fin (n - 4) :=
    { toFun := fun i => ⟨(i : ℕ) - 4, by have := i.1.2; have := i.2; omega⟩
      invFun := fun j => ⟨⟨(j : ℕ) + 4, by have := j.2; omega⟩, by simp⟩
      left_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        simp only
        have := i.2
        omega
      right_inv := fun j => by
        apply Fin.ext
        simp }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem stabO_of_fix {π : Perm (Fin n)} (hπ : ∀ j, π (fourEmb h j) = fourEmb h j) : StabO π := by
  intro i
  by_cases hi : 4 ≤ (i : ℕ)
  · refine ⟨fun _ => hi, fun _ => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨j, hj⟩ := (mem_range_fourEmb_iff h).mpr hc
    rw [← hπ j] at hj
    have := congrArg (fun x : Fin n => (x : ℕ)) (π.injective hj)
    simp only [fourEmb_apply] at this
    have := j.2
    omega
  · push Not at hi
    have := hπ ⟨i, hi⟩
    rw [show fourEmb h ⟨i, hi⟩ = i from Fin.ext rfl] at this
    rw [this]

theorem ofSubtype_subtypePerm_of_fix {π : Perm (Fin n)}
    (hπ : ∀ j, π (fourEmb h j) = fourEmb h j) :
    ofSubtype (π.subtypePerm (p := fun i : Fin n => 4 ≤ (i : ℕ)) (stabO_of_fix h hπ)) = π := by
  refine ofSubtype_subtypePerm _ fun i hi => ?_
  by_contra hc
  push Not at hc
  apply hi
  have := hπ ⟨i, hc⟩
  rwa [show fourEmb h ⟨i, hc⟩ = i from Fin.ext rfl] at this

include h in
theorem apply_eq_of_mem_rootVP {π : Perm (Fin n)} (hπ : π ∈ rootVP n) {i : Fin n}
    (hi : 4 ≤ (i : ℕ)) : π i = i := by
  rw [rootVP_eq h] at hπ
  obtain ⟨k, -, rfl⟩ := hπ
  apply viaEmbeddingHom_apply_of_notMem
  rw [mem_range_fourEmb_iff]
  omega

end Perm

variable {G : Type} [Group G] [Finite G]

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n) (hc : Sec3 A R T g)
include np hc

theorem mem_normalizer_B_of_stabO (hn : 7 ≤ n) {x : normalizer (A : Set G)} (hx : (x : G) ∈ A)
    (hstab : StabO (np.ψA x)) : (x : G) ∈ normalizer (rightConjugate A g : Set G) :=
  normalizer_T_le hc (np.mem_normalizer_T (by omega) hx
    (normalizesV_of_stabO (by omega) hstab))

theorem ψB_eq_of_restrictO_eq (hn : 7 ≤ n) {x x' : normalizer (A : Set G)} (hx : (x : G) ∈ A)
    (hx' : (x' : G) ∈ A) (hs : StabO (np.ψA x)) (hs' : StabO (np.ψA x'))
    (heq : ∀ i : Fin n, 4 ≤ (i : ℕ) → np.ψA x i = np.ψA x' i) :
    np.ψB ⟨x, np.mem_normalizer_B_of_stabO hc hn hx hs⟩ =
      np.ψB ⟨x', np.mem_normalizer_B_of_stabO hc hn hx' hs'⟩ := by
  have h4 : 4 ≤ n := by omega
  have hu : ((x⁻¹ * x' : normalizer (A : Set G)) : G) ∈ A := mul_mem (inv_mem hx) hx'
  have hYT : np.ψA (x⁻¹ * x') ∈ rootAltP n := by
    refine mem_rootAltP_of_fix h4 ?_ fun i hi => ?_
    · have := np.hψA.map_mem _ hu
      exact this
    · rw [map_mul, map_inv, Perm.mul_apply, ← heq i hi, perm_inv_apply]
  have hK := np.YT_le hc hn (y := x⁻¹ * x') hu hYT
  have h1 : np.ψB (⟨x, np.mem_normalizer_B_of_stabO hc hn hx hs⟩⁻¹ *
      ⟨x', np.mem_normalizer_B_of_stabO hc hn hx' hs'⟩) = 1 := by
    rw [np.hψB.eq_one_iff]
    exact hK
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

omit [Finite G] hc in
theorem exists_xq (h4 : 4 ≤ n) (q : Perm (OSet n)) :
    ∃ x : normalizer (A : Set G), (x : G) ∈ A ∧ np.ψA x = liftO h4 q := by
  obtain ⟨a, ha, hae⟩ := np.hψA.exists_eq _ (liftO_mem h4 q)
  exact ⟨⟨a, le_normalizer ha⟩, ha, hae⟩

omit hc in
noncomputable def xq (h4 : 4 ≤ n) (q : Perm (OSet n)) : normalizer (A : Set G) :=
  (np.exists_xq h4 q).choose

omit [Finite G] hc in
theorem xq_mem (h4 : 4 ≤ n) (q : Perm (OSet n)) : (np.xq h4 q : G) ∈ A :=
  (np.exists_xq h4 q).choose_spec.1

omit [Finite G] hc in
theorem ψA_xq (h4 : 4 ≤ n) (q : Perm (OSet n)) : np.ψA (np.xq h4 q) = liftO h4 q :=
  (np.exists_xq h4 q).choose_spec.2

omit [Finite G] hc in
theorem stabO_xq (h4 : 4 ≤ n) (q : Perm (OSet n)) : StabO (np.ψA (np.xq h4 q)) := by
  rw [ψA_xq]
  exact stabO_liftO h4 q

theorem xq_mem_normalizer_B (hn : 7 ≤ n) (h4 : 4 ≤ n) (q : Perm (OSet n)) :
    (np.xq h4 q : G) ∈ normalizer (rightConjugate A g : Set G) :=
  np.mem_normalizer_B_of_stabO hc hn (np.xq_mem h4 q) (np.stabO_xq h4 q)

theorem ψB_xq_fix (hn : 7 ≤ n) (h4 : 4 ≤ n) (q : Perm (OSet n)) (j : Fin 4) :
    np.ψB ⟨np.xq h4 q, np.xq_mem_normalizer_B hc hn h4 q⟩ (fourEmb h4 j) = fourEmb h4 j :=
  np.ψB_apply_of_mem_A hc hn (np.xq_mem h4 q) j

noncomputable def theta (hn : 7 ≤ n) (h4 : 4 ≤ n) : Perm (OSet n) →* Perm (OSet n) :=
  MonoidHom.mk' (fun q => (np.ψB ⟨np.xq h4 q, np.xq_mem_normalizer_B hc hn h4 q⟩).subtypePerm
      (p := fun i : Fin n => 4 ≤ (i : ℕ)) (stabO_of_fix h4 (np.ψB_xq_fix hc hn h4 q)))
    (fun q q' => by
      have hmul : np.ψB ⟨np.xq h4 (q * q'), np.xq_mem_normalizer_B hc hn h4 (q * q')⟩ =
          np.ψB ⟨np.xq h4 q, np.xq_mem_normalizer_B hc hn h4 q⟩ *
            np.ψB ⟨np.xq h4 q', np.xq_mem_normalizer_B hc hn h4 q'⟩ := by
        rw [← map_mul]
        have hs := stabO_mul (np.stabO_xq h4 q) (np.stabO_xq h4 q')
        rw [← map_mul] at hs
        have h1 := np.ψB_eq_of_restrictO_eq hc hn (x := np.xq h4 (q * q'))
          (x' := np.xq h4 q * np.xq h4 q') (np.xq_mem h4 _)
          (mul_mem (np.xq_mem h4 q) (np.xq_mem h4 q')) (np.stabO_xq h4 _) hs (fun i hi => by
            rw [map_mul, Perm.mul_apply, ψA_xq, ψA_xq, ψA_xq, liftO_apply_of_ge h4 _ hi,
              liftO_apply_of_ge h4 _ hi, liftO_apply_of_ge h4 _ ((stabO_ofSubtype q' i).mpr hi),
              map_mul, Perm.mul_apply])
        rw [h1]
        rfl
      apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [subtypePerm_apply, Perm.mul_apply]
      rw [hmul, Perm.mul_apply])

theorem ψB_xq_eq (hn : 7 ≤ n) (h4 : 4 ≤ n) (q : Perm (OSet n)) :
    np.ψB ⟨np.xq h4 q, np.xq_mem_normalizer_B hc hn h4 q⟩ = ofSubtype (np.theta hc hn h4 q) :=
  (ofSubtype_subtypePerm_of_fix h4 (np.ψB_xq_fix hc hn h4 q)).symm

theorem xq_mem_centralizer (hn : 7 ≤ n) (h4 : 4 ≤ n) {q : Perm (OSet n)}
    (hq : np.theta hc hn h4 q = 1) :
    (np.xq h4 q : G) ∈ Subgroup.centralizer (rightConjugate A g : Set G) := by
  have h1 := np.ψB_xq_eq hc hn h4 q
  rw [hq, map_one] at h1
  exact (np.hψB.eq_one_iff _).mp h1

omit [Finite G] np hc in
theorem liftO_ne_one {h4 : 4 ≤ n} {q : Perm (OSet n)} (hq1 : q ≠ 1) :
    ∃ i : Fin n, 4 ≤ (i : ℕ) ∧ liftO h4 q i ≠ i := by
  by_contra hcon
  push Not at hcon
  apply hq1
  apply Equiv.ext
  intro o
  apply Subtype.ext
  have := hcon o o.2
  rw [liftO_apply_of_ge h4 q o.2, ofSubtype_apply_coe] at this
  exact this

omit [Finite G] np hc in
theorem ofSubtype_commute_swap01 (h4 : 4 ≤ n) (q : Perm (OSet n)) :
    Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * ofSubtype q = ofSubtype q * Equiv.swap (fourEmb h4 0) (fourEmb h4 1) := by
  have hq : ∀ j, ofSubtype q (fourEmb h4 j) = fourEmb h4 j := fun j =>
    ofSubtype_apply_of_not_mem q (by rw [fourEmb_apply]; have := j.2; omega)
  have h := (commute_of_apply_eq (fourEmb h4) hq (Equiv.swap 0 1)).eq
  rw [viaEmbeddingHom_swap] at h
  exact h.symm

omit [Finite G] np hc in
theorem liftO_mul_self (h4 : 4 ≤ n) {q : Perm (OSet n)} (hq2 : q * q = 1) :
    liftO h4 q * liftO h4 q = 1 := by
  have hoq : ofSubtype q * ofSubtype q = 1 := by rw [← map_mul, hq2, map_one]
  rw [liftO]
  split_ifs
  · exact hoq
  · calc Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * ofSubtype q *
          (Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * ofSubtype q)
        = Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * (ofSubtype q * Equiv.swap (fourEmb h4 0) (fourEmb h4 1)) *
            ofSubtype q := by group
      _ = Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * (Equiv.swap (fourEmb h4 0) (fourEmb h4 1) * ofSubtype q) *
            ofSubtype q := by rw [ofSubtype_commute_swap01]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, hoq]

theorem false_of_involution (hn : 7 ≤ n) (h4 : 4 ≤ n) {q : Perm (OSet n)}
    (hq : np.theta hc hn h4 q = 1) (hq2 : q * q = 1) (hq1 : q ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := np.xq h4 q with hxdef
  have hxA := np.xq_mem h4 q
  have hxK := np.xq_mem_centralizer hc hn h4 hq
  have hψx := np.ψA_xq h4 q
  have hx2 : (x : G) * x = 1 := by
    have h1 : x * x = 1 := np.injA (mul_mem hxA hxA) (one_mem A) (by
      rw [map_mul, hψx, liftO_mul_self h4 hq2, map_one])
    exact congrArg Subtype.val h1
  have hxN : (x : G) ∈ normalizer (T : Set G) :=
    np.mem_normalizer_T h4 hxA (by rw [hψx]; exact normalizesV_of_stabO h4 (stabO_liftO h4 q))
  have hzp : IsPGroup 2 (zpowers (x : G)) := by
    have hdvd : orderOf (x : G) ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hx2])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hsup : IsPGroup 2 ↥(T ⊔ zpowers (x : G)) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowT.isPGroup hzp (zpowers_le.mpr hxN)
  have hxKg : (x : G) ∈ rightConjugate (Subgroup.centralizer (A : Set G)) g := by
    rw [← centralizer_rightConjugate]
    exact hxK
  have heq := hc.sylowT.eq_of_le le_sup_left (sup_le hc.sylowT.le (zpowers_le.mpr hxKg)) hsup
  have hxT : (x : G) ∈ T := heq ▸ (le_sup_right (a := T) (mem_zpowers (x : G)))
  have hV := np.ψA_mem_of_T hxT
  obtain ⟨i, hi, hne⟩ := liftO_ne_one (h4 := h4) hq1
  rw [← hψx] at hne
  exact hne (apply_eq_of_mem_rootVP h4 hV hi)

omit [Finite G] np hc in
theorem eq_one_of_commute_three (h7 : n = 7) {q q' : Perm (OSet n)} (hq3 : q ^ 3 = 1)
    (hq1 : q ≠ 1) (hc' : q' * q = q * q') (hq2 : q' * q' = 1) : q' = 1 := by
  have hcard : Fintype.card (OSet n) = 3 := by rw [card_OSet, h7]
  let P : Perm (OSet n) ≃* Perm (Fin 3) := (Fintype.equivFinOfCardEq hcard).permCongrHom
  have key : ∀ a b : Perm (Fin 3), a ^ 3 = 1 → a ≠ 1 → b * a = a * b → b * b = 1 → b = 1 := by
    decide
  have h := key (P q) (P q') (by rw [← map_pow, hq3, map_one])
    (fun h => hq1 (P.injective (by rw [h, map_one]))) (by rw [← map_mul, ← map_mul, hc'])
    (by rw [← map_mul, hq2, map_one])
  exact P.injective (by rw [h, map_one])

omit [Finite G] np hc in
theorem sq_or_cube_eq_one (h7 : n = 7) (q : Perm (OSet n)) : q * q = 1 ∨ q ^ 3 = 1 := by
  have hcard : Fintype.card (OSet n) = 3 := by rw [card_OSet, h7]
  let P : Perm (OSet n) ≃* Perm (Fin 3) := (Fintype.equivFinOfCardEq hcard).permCongrHom
  have key : ∀ a : Perm (Fin 3), a * a = 1 ∨ a ^ 3 = 1 := by decide
  rcases key (P q) with h | h
  · exact Or.inl (P.injective (by rw [map_mul, h, map_one]))
  · exact Or.inr (P.injective (by rw [map_pow, h, map_one]))

theorem false_of_three (hn : 7 ≤ n) (h4 : 4 ≤ n) (h7 : n = 7) {q : Perm (OSet n)}
    (hq : np.theta hc hn h4 q = 1) (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := np.xq h4 q with hcdef
  have hcK := np.xq_mem_centralizer hc hn h4 hq
  have hsign : sign (ofSubtype q) = 1 := by
    rw [sign_ofSubtype]
    have h1 : sign q ^ 3 = 1 := by rw [← map_pow, hq3, map_one]
    rcases Int.units_eq_one_or (sign q) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hψc : np.ψA c = ofSubtype q := by
    rw [hcdef, ψA_xq, liftO, ite_eq_left hsign]
  set o₁ : Fin n := ⟨4, by omega⟩
  set o₂ : Fin n := ⟨5, by omega⟩
  have ho₁ : o₁ ∉ Set.range (fourEmb h4) := by rw [mem_range_fourEmb_iff]; simp [o₁]
  have ho₂ : o₂ ∉ Set.range (fourEmb h4) := by rw [mem_range_fourEmb_iff]; simp [o₂]
  have h12 : o₁ ≠ o₂ := by simp [o₁, o₂, Fin.ext_iff]
  have hmem := mul_swap_mem_alternatingGroup (fourEmb h4) h12 (show (0 : Fin 4) ≠ 1 by decide)
  obtain ⟨y, hyB, hye⟩ := np.hψB.exists_eq _ hmem
  set yB : normalizer (rightConjugate A g : Set G) := ⟨y, le_normalizer hyB⟩
  have hyR : y ∈ normalizer (R : Set G) :=
    np.mem_normalizer_R h4 (x := yB) hyB (by
      show NormalizesV h4 (np.ψB yB)
      rw [hye]
      exact normalizesV_mul_swap h4 ho₁ ho₂ _)
  have hyA : y ∈ normalizer (A : Set G) := normalizer_R_le hc hyR
  set yA : normalizer (A : Set G) := ⟨y, hyA⟩
  have hfix := np.ψA_apply_of_mem_B hc hn (y := yA) hyB
  have hyc : yA * c = c * yA := by
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hcK y hyB)
  have hy2 : yB * yB = 1 := by
    refine np.injB (mul_mem hyB hyB) (one_mem _) ?_
    rw [map_mul, hye, map_one]
    have hcomm := (commute_swap_viaEmbeddingHom (fourEmb h4) ho₁ ho₂ (Equiv.swap 0 1)).eq
    calc viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1) * Equiv.swap o₁ o₂ *
          (viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1) * Equiv.swap o₁ o₂)
        = viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1) *
            (Equiv.swap o₁ o₂ * viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1)) *
            Equiv.swap o₁ o₂ := by group
      _ = viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1) *
            (viaEmbeddingHom (fourEmb h4) (Equiv.swap 0 1) * Equiv.swap o₁ o₂) *
            Equiv.swap o₁ o₂ := by rw [hcomm]
      _ = 1 := by
          rw [← mul_assoc, ← map_mul, swap_mul_self, map_one, one_mul, swap_mul_self]
  have hyA2 : np.ψA yA * np.ψA yA = 1 := by
    rw [← map_mul]
    have h' : (y : G) * y = 1 := congrArg Subtype.val hy2
    have : yA * yA = 1 := Subtype.ext h'
    rw [this, map_one]
  set q' := (np.ψA yA).subtypePerm (p := fun i : Fin n => 4 ≤ (i : ℕ)) (stabO_of_fix h4 hfix)
  have hq'eq : ofSubtype q' = np.ψA yA := ofSubtype_subtypePerm_of_fix h4 hfix
  have hq'1 : q' = 1 := by
    refine eq_one_of_commute_three h7 hq3 hq1 (ofSubtype_injective ?_) (ofSubtype_injective ?_)
    · rw [map_mul, map_mul, hq'eq, ← hψc, ← map_mul, ← map_mul, hyc]
    · rw [map_mul, map_one, hq'eq, hyA2]
  have hψy : np.ψA yA = 1 := by rw [← hq'eq, hq'1, map_one]
  have hyK : y ∈ Subgroup.centralizer (A : Set G) := (np.hψA.eq_one_iff yA).mp hψy
  have hy2' : y * y = 1 := congrArg Subtype.val hy2
  have hzp : IsPGroup 2 (zpowers y) := by
    have hdvd : orderOf y ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hy2'])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hsup : IsPGroup 2 ↥(R ⊔ zpowers y) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup hzp (zpowers_le.mpr hyR)
  have heq := hc.sylowR.eq_of_le le_sup_left (sup_le hc.sylowR.le (zpowers_le.mpr hyK)) hsup
  have hyRmem : y ∈ R := heq ▸ (le_sup_right (a := R) (mem_zpowers y))
  have hV := np.ψB_mem_of_R (r := yB) hyRmem
  rw [hye] at hV
  have h1 := apply_eq_of_mem_rootVP h4 hV (i := o₁) (by simp [o₁])
  rw [Perm.mul_apply, swap_apply_left, viaEmbeddingHom_apply_of_notMem _ _ ho₂] at h1
  exact h12 h1.symm

omit [Finite G] np hc in
theorem exists_involution_of_normal (h8 : 8 ≤ n) {N : Subgroup (Perm (OSet n))} [N.Normal]
    (hN : N ≠ ⊥) : ∃ q ∈ N, q * q = 1 ∧ q ≠ 1 := by
  classical
  have hcard := card_OSet (n := n)
  rcases (by omega : n = 8 ∨ 9 ≤ n) with h8' | h9
  ·
    have hc4 : Fintype.card (OSet n) = 4 := by rw [hcard, h8']
    let P : Perm (OSet n) ≃* Perm (Fin 4) := (Fintype.equivFinOfCardEq hc4).permCongrHom
    have key : ∀ a : Perm (Fin 4), a ≠ 1 → (a * a = 1) ∨ (a ^ 2 * a ^ 2 = 1 ∧ a ^ 2 ≠ 1) ∨
        ∃ s : Perm (Fin 4), (s * a * s⁻¹ * a⁻¹) * (s * a * s⁻¹ * a⁻¹) = 1 ∧
          s * a * s⁻¹ * a⁻¹ ≠ 1 := by decide +kernel
    obtain ⟨⟨q, hqN⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN
    have hq1n : q ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hq1' : P q ≠ 1 := fun h => hq1n (P.injective (h.trans (map_one P).symm))
    rcases key (P q) hq1' with h | ⟨h, h'⟩ | ⟨s, h, h'⟩
    · exact ⟨q, hqN, P.injective (by rw [map_mul, h, map_one]), hq1n⟩
    · refine ⟨q ^ 2, pow_mem hqN 2, P.injective (by rw [map_mul, map_pow, h,
        map_one]), fun h1 => h' (by rw [← map_pow, h1, map_one])⟩
    · refine ⟨P.symm s * q * (P.symm s)⁻¹ * q⁻¹,
        mul_mem (‹N.Normal›.conj_mem _ hqN _) (inv_mem hqN), P.injective ?_, fun h1 => h' ?_⟩
      · simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, map_one]
        exact h
      · have := congrArg P h1
        simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, map_one] using this
  ·
    have h5 : 5 ≤ Nat.card (OSet n) := by rw [Nat.card_eq_fintype_card, hcard]; omega
    have hnt : Nontrivial N := by
      obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN
      exact ⟨⟨q, 1, hq1⟩⟩
    have hle := Equiv.Perm.alternatingGroup_le_of_normal h5 hnt
    set o : Fin 4 → OSet n := fun j => ⟨⟨(j : ℕ) + 4, by omega⟩, by simp⟩
    have hinj : ∀ i j, o i = o j → i = j := fun i j h => by
      have := congrArg (fun x : OSet n => ((x : Fin n) : ℕ)) h
      simp only [o] at this
      exact Fin.ext (by omega)
    have hne : ∀ i j : Fin 4, i ≠ j → o i ≠ o j := fun i j hij h => hij (hinj i j h)
    refine ⟨Equiv.swap (o 0) (o 1) * Equiv.swap (o 2) (o 3), hle ?_, ?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (hne 0 1 (by decide)),
        sign_swap (hne 2 3 (by decide))]
      rfl
    · have hdisj : Disjoint (Equiv.swap (o 0) (o 1)) (Equiv.swap (o 2) (o 3)) := by
        intro x
        by_cases hx : x = o 0 ∨ x = o 1
        · right
          rcases hx with rfl | rfl
          · exact swap_apply_of_ne_of_ne (hne 0 2 (by decide)) (hne 0 3 (by decide))
          · exact swap_apply_of_ne_of_ne (hne 1 2 (by decide)) (hne 1 3 (by decide))
        · left
          push Not at hx
          exact swap_apply_of_ne_of_ne hx.1 hx.2
      have hcomm : Equiv.swap (o 0) (o 1) * Equiv.swap (o 2) (o 3) =
          Equiv.swap (o 2) (o 3) * Equiv.swap (o 0) (o 1) := hdisj.commute.eq
      calc Equiv.swap (o 0) (o 1) * Equiv.swap (o 2) (o 3) *
            (Equiv.swap (o 0) (o 1) * Equiv.swap (o 2) (o 3))
          = Equiv.swap (o 0) (o 1) * (Equiv.swap (o 2) (o 3) * Equiv.swap (o 0) (o 1)) *
              Equiv.swap (o 2) (o 3) := by group
        _ = Equiv.swap (o 0) (o 1) * (Equiv.swap (o 0) (o 1) * Equiv.swap (o 2) (o 3)) *
              Equiv.swap (o 2) (o 3) := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
    · intro h
      have := congrArg (fun p : Perm (OSet n) => p (o 0)) h
      simp only [Perm.mul_apply, Perm.one_apply] at this
      rw [swap_apply_of_ne_of_ne (hne 0 2 (by decide)) (hne 0 3 (by decide)), swap_apply_left] at this
      exact hne 1 0 (by decide) this

theorem theta_injective (hn : 7 ≤ n) (h4 : 4 ≤ n) : Function.Injective (np.theta hc hn h4) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hN
  rcases (by omega : n = 7 ∨ 8 ≤ n) with h7 | h8
  · obtain ⟨⟨q, hqN⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hN
    have hq : np.theta hc hn h4 q = 1 := hqN
    have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
    rcases sq_or_cube_eq_one h7 q with h2 | h3
    · exact np.false_of_involution hc hn h4 hq h2 hq1'
    · exact np.false_of_three hc hn h4 h7 hq h3 hq1'
  · obtain ⟨q, hqN, hq2, hq1⟩ := exists_involution_of_normal h8 hN
    exact np.false_of_involution hc hn h4 hqN hq2 hq1

theorem exists_beta (hn : 7 ≤ n) (h4 : 4 ≤ n) (hn10 : n ≠ 10) :
    ∃ β : Perm (Fin n), (∀ j, β (fourEmb h4 j) = fourEmb h4 j) ∧
      ∀ (x : normalizer (A : Set G)) (hx : (x : G) ∈ A) (hs : StabO (np.ψA x)),
        np.ψB ⟨x, np.mem_normalizer_B_of_stabO hc hn hx hs⟩ =
          β * restrictO (np.ψA x) * β⁻¹ := by
  have h6 : Fintype.card (OSet n) ≠ 6 := by rw [card_OSet]; omega
  obtain ⟨β, hβ⟩ := exists_conj_of_injective h6 (np.theta hc hn h4) (np.theta_injective hc hn h4)
  refine ⟨ofSubtype β, fun j => ofSubtype_apply_of_not_mem β (by
    show ¬ 4 ≤ ((fourEmb h4 j : Fin n) : ℕ)
    rw [fourEmb_apply]
    have := j.2
    omega), fun x hx hs => ?_⟩
  set qx := (np.ψA x).subtypePerm (p := fun i : Fin n => 4 ≤ (i : ℕ)) hs with hqx
  have hres : restrictO (np.ψA x) = ofSubtype qx := restrictO_of_stabO hs
  have h1 := np.ψB_eq_of_restrictO_eq hc hn (x := x) (x' := np.xq h4 qx) hx (np.xq_mem h4 qx) hs
    (np.stabO_xq h4 qx) (fun i hi => by
      rw [ψA_xq, liftO_apply_of_ge h4 qx hi, ofSubtype_apply_of_mem qx hi, subtypePerm_apply])
  rw [h1]
  have h2 := np.ψB_xq_eq hc hn h4 qx
  rw [hβ] at h2
  rw [h2, map_mul, map_mul, map_inv, hres]

omit [Finite G] hc in
@[expose] noncomputable def conjB (h4 : 4 ≤ n) (β : Perm (Fin n))
    (hβ : ∀ j, β (fourEmb h4 j) = fourEmb h4 j) : NormPair A R T g n where
  ψA := np.ψA
  ψB := (MulAut.conj β⁻¹).toMonoidHom.comp np.ψB
  hψA := np.hψA
  hψB := isActionHom_conj np.hψB β⁻¹
  le_A := np.le_A
  le_B := np.le_B
  map_T := np.map_T
  map_R := by
    rw [map_conj_comp, np.map_R, rootVP_eq h4, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro k
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hβ' : ∀ j, β⁻¹ (fourEmb h4 j) = fourEmb h4 j := fun j => by
      rw [Perm.inv_eq_iff_eq, hβ]
    rw [(commute_of_apply_eq (fourEmb h4) hβ' k).eq, inv_mul_cancel_right]
  center_eq_bot := np.center_eq_bot

omit [Finite G] hc in
theorem conjB_ψA (h4 : 4 ≤ n) (β : Perm (Fin n)) (hβ : ∀ j, β (fourEmb h4 j) = fourEmb h4 j) :
    (np.conjB h4 β hβ).ψA = np.ψA :=
  rfl

omit [Finite G] hc in
theorem conjB_ψB (h4 : 4 ≤ n) (β : Perm (Fin n)) (hβ : ∀ j, β (fourEmb h4 j) = fourEmb h4 j)
    (y : normalizer (rightConjugate A g : Set G)) :
    (np.conjB h4 β hβ).ψB y = β⁻¹ * np.ψB y * β :=
  by simp [conjB]

theorem exists_restrictO (hn : 7 ≤ n) (hn10 : n ≠ 10) :
    ∃ np' : NormPair A R T g n, np'.ψA = np.ψA ∧
      ∀ (x : normalizer (A : Set G)) (hx : (x : G) ∈ A) (hs : StabO (np'.ψA x)),
        np'.ψB ⟨x, np'.mem_normalizer_B_of_stabO hc hn hx hs⟩ = restrictO (np'.ψA x) := by
  have h4 : 4 ≤ n := by omega
  obtain ⟨β, hβF, hβ⟩ := np.exists_beta hc hn h4 hn10
  refine ⟨np.conjB h4 β hβF, rfl, fun x hx hs => ?_⟩
  rw [conjB_ψB, hβ x hx hs]
  rw [conjB_ψA]
  group

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
