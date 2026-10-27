module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264D4EightCaseB
public import Certificates.Certificate731264

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes

@[expose] def pgu38Perm : Subgroup (Equiv.Perm (Fin 513)) :=
  Subgroup.closure {g | ∃ k < 8, permOfArr 513 gensO[k]! = g}

@[expose] def pgu38SylowPerm : Subgroup (Equiv.Perm (Fin 513)) :=
  Subgroup.closure (permsA 513 pgu38SylowGens)

theorem gensO_mem_pgu38Perm {k : ℕ} (hk : k < 8) : permOfArr 513 gensO[k]! ∈ pgu38Perm :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem X'_le_pgu38Perm : X' ≤ pgu38Perm := by
  unfold X' CFSG.YGroups.arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk7 : k < 7 := by rw [gensX_size] at hk; exact hk
  rw [gensX_getElem k hk7]
  exact gensO_mem_pgu38Perm (by omega)

theorem pgu38Perm_le_U38G : pgu38Perm ≤ U38G := by
  unfold pgu38Perm U38G CFSG.YGroups.arrClosure
  refine Subgroup.closure_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, by rw [gensO_size]; omega, rfl⟩

theorem pgu38Key_lt : ∀ p ∈ pgu38Key, p < 513 := by decide

theorem pgu38SylowGens_size : pgu38SylowGens.size = 3 := by simp [pgu38SylowGens]

@[expose] noncomputable def pgu38ClassRep (r : ℕ) : Equiv.Perm (Fin 513) :=
  permOfArr 513 pgu38ClassReps[pgu38RepIdx[r]!]!

theorem factorization_pgu38 : (16547328 : ℕ).factorization 3 = 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three,
    show (16547328 : ℕ) = 3 ^ 5 * 68096 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

section Certified


theorem rep_gensO_pgu38 {k : ℕ} (hk : k < 9) : Rep 513 gensO[k]! (permOfArr 513 gensO[k]!) :=
  rep_of_validA (gensO_valid k hk)

theorem mem_pgu38Perm_of_sift {t : Array ℕ} {T : Equiv.Perm (Fin 513)} (hT : Rep 513 t T) {k : ℕ}
    (hs : pgu38SiftX (compA 513 t
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) k)) = true) :
    T ∈ pgu38Perm := by
  have h7 := gensO_valid 7 (by norm_num)
  have hrep : Rep 513 (compA 513 t
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) k))
      (T * (permOfArr 513 gensO[7]!)⁻¹ ^ k) :=
    rep_compA hT (CFSG.Monster.B.Mathieu.rep_powArr (rep_inv_of_validA h7) k)
  have hX : T * (permOfArr 513 gensO[7]!)⁻¹ ^ k ∈ X' := sift3_mem hrep hs
  have h1 := pgu38Perm.mul_mem (X'_le_pgu38Perm hX)
    (pgu38Perm.pow_mem (gensO_mem_pgu38Perm (k := 7) (by norm_num)) k)
  rwa [inv_pow, inv_mul_cancel_right] at h1


theorem gensO_conj_mem_pgu38Perm {i : ℕ} (hi : i < 8) :
    permOfArr 513 gensO[8]! * permOfArr 513 gensO[i]! * (permOfArr 513 gensO[8]!)⁻¹ ∈
        pgu38Perm ∧
      (permOfArr 513 gensO[8]!)⁻¹ * permOfArr 513 gensO[i]! * permOfArr 513 gensO[8]! ∈
        pgu38Perm := by
  by_cases h7 : i < 7
  · have h := conj_gen_mem 1 (by norm_num) i h7
    rw [show (7 + 1 : ℕ) = 8 from rfl] at h
    exact ⟨X'_le_pgu38Perm h.1, X'_le_pgu38Perm h.2⟩
  · obtain rfl : i = 7 := by omega
    obtain ⟨-, -, -, -, -, -, h1, h2⟩ := Certificates.certificate731264
    have hg8 := gensO_valid 8 (by norm_num)
    have hg7 := rep_gensO_pgu38 (k := 7) (by norm_num)
    exact ⟨mem_pgu38Perm_of_sift (rep_conjA hg8 hg7) h1,
      mem_pgu38Perm_of_sift (rep_conjInvA hg8 hg7) h2⟩

theorem U38G_le_normalizer_pgu38Perm :
    U38G ≤ Subgroup.normalizer (pgu38Perm : Set (Equiv.Perm (Fin 513))) := by
  unfold U38G CFSG.YGroups.arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk9 : k < 9 := by rw [gensO_size] at hk; exact hk
  by_cases h8 : k < 8
  · exact Subgroup.le_normalizer (gensO_mem_pgu38Perm h8)
  · obtain rfl : k = 8 := by omega
    set g := permOfArr 513 gensO[8]! with hg
    have hgen : ∀ s ∈ {x | ∃ k < 8, permOfArr 513 gensO[k]! = x}, g * s * g⁻¹ ∈ pgu38Perm := by
      rintro s ⟨i, hi, rfl⟩
      exact (gensO_conj_mem_pgu38Perm hi).1
    have hgen' : ∀ s ∈ {x | ∃ k < 8, permOfArr 513 gensO[k]! = x}, g⁻¹ * s * g⁻¹⁻¹ ∈ pgu38Perm := by
      rintro s ⟨i, hi, rfl⟩
      rw [inv_inv]
      exact (gensO_conj_mem_pgu38Perm hi).2
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conj_closure_mem _ pgu38Perm g hgen h hh
    · intro hh
      have := conj_closure_mem _ pgu38Perm g⁻¹ hgen' (g * h * g⁻¹) hh
      simpa [mul_assoc] using this

theorem card_pgu38Perm_le : Nat.card pgu38Perm ≤ 3 * Nat.card X' := by
  classical
  set N := pgu38Perm with hNdef
  set Y : Subgroup N := X'.subgroupOf N with hYdef
  haveI hYn : Y.Normal := by
    constructor
    intro y hy g
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have h := (Subgroup.mem_normalizer_iff.mp
      (U38G_le_normalizer (pgu38Perm_le_U38G g.2)) (y : Equiv.Perm (Fin 513))).mp hy
    simpa using h
  have hg7N : permOfArr 513 gensO[7]! ∈ N := gensO_mem_pgu38Perm (by norm_num)
  set g7N : N := ⟨_, hg7N⟩ with hg7Ndef
  have hall : ∀ x : N, QuotientGroup.mk' Y x ∈ Subgroup.zpowers (QuotientGroup.mk' Y g7N) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Subgroup.closure {g | ∃ k < 8, permOfArr 513 gensO[k]! = g} := hx
    induction hx' using Subgroup.closure_induction with
    | mem x hxs =>
      obtain ⟨k, hk, rfl⟩ := hxs
      by_cases h7 : k < 7
      · have hmem : (⟨permOfArr 513 gensO[k]!, hx⟩ : N) ∈ Y := by
          rw [Subgroup.mem_subgroupOf]
          refine Subgroup.subset_closure ⟨k, by rw [gensX_size]; exact h7, ?_⟩
          rw [gensX_getElem k h7]
        have h1 : QuotientGroup.mk' Y (⟨permOfArr 513 gensO[k]!, hx⟩ : N) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hmem
        rw [h1]
        exact one_mem _
      · obtain rfl : k = 7 := by omega
        exact Subgroup.mem_zpowers _
    | one =>
      have h1 : (⟨1, hx⟩ : N) = 1 := rfl
      rw [h1, map_one]
      exact one_mem _
    | mul x y hx₁ hy₁ ihx ihy =>
      have h1 : (⟨x * y, hx⟩ : N) = ⟨x, hx₁⟩ * ⟨y, hy₁⟩ := rfl
      rw [h1, map_mul]
      exact mul_mem (ihx hx₁) (ihy hy₁)
    | inv x hx₁ ih =>
      have h1 : (⟨x⁻¹, hx⟩ : N) = (⟨x, hx₁⟩ : N)⁻¹ := rfl
      rw [h1, map_inv]
      exact inv_mem (ih hx₁)
  have htop : (⊤ : Subgroup (N ⧸ Y)) ≤ Subgroup.zpowers (QuotientGroup.mk' Y g7N) := by
    rintro q -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y q
    exact hall x
  have hq3 : (QuotientGroup.mk' Y g7N) ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨-, -, -, -, -, hcube, -, -⟩ := Certificates.certificate731264
    have h := sift3_mem
      (CFSG.Monster.B.Mathieu.rep_powArr (rep_gensO_pgu38 (k := 7) (by norm_num)) 3) hcube
    simpa using h
  have hcardQ : Nat.card (N ⧸ Y) ≤ 3 := by
    calc Nat.card (N ⧸ Y) = Nat.card (⊤ : Subgroup (N ⧸ Y)) := Subgroup.card_top.symm
      _ ≤ Nat.card (Subgroup.zpowers (QuotientGroup.mk' Y g7N)) := Subgroup.card_le_of_le htop
      _ = orderOf (QuotientGroup.mk' Y g7N) := Nat.card_zpowers _
      _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hq3
  have hY : Nat.card Y = Nat.card X' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe X'_le_pgu38Perm).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y, hY]
  exact Nat.mul_le_mul_right _ hcardQ

theorem pgu38SylowPerm_enum :
    (∀ x, x ∈ pgu38SylowPerm ↔ ∃ i < (pgu38SylowEnum ()).pts.size,
      permOfArr 513 (pgu38SylowEnum ()).pts[i]! = x) ∧
    Nat.card pgu38SylowPerm = 243 ∧
    ∀ i < (pgu38SylowEnum ()).pts.size, validA 513 (pgu38SylowEnum ()).pts[i]! = true := by
  obtain ⟨⟨henum, hsize⟩, -⟩ := Certificates.certificate731264
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec pgu38Key_lt henum
  exact ⟨hmem, hcard.trans hsize, hval⟩

theorem pgu38SylowPerm_le : pgu38SylowPerm ≤ pgu38Perm := by
  obtain ⟨⟨henum, -⟩, hgens, -⟩ := Certificates.certificate731264
  rw [pgu38SylowPerm, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < pgu38SylowGens.size := hj
  have hj3 : j < 3 := by rw [pgu38SylowGens_size] at hj'; exact hj'
  exact mem_pgu38Perm_of_sift (rep_of_validA (enumOK_gens_valid henum hj')) (allLt_spec hgens hj3)

theorem validA_pgu38ClassReps {j : ℕ} (hj : j < 10) : validA 513 pgu38ClassReps[j]! = true := by
  obtain ⟨-, -, -, hreps, -⟩ := Certificates.certificate731264
  have h := allLt_spec hreps hj
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem rep_pgu38ClassRep {r : ℕ} (hr : r < 5) :
    Rep 513 pgu38ClassReps[pgu38RepIdx[r]!]! (pgu38ClassRep r) := by
  obtain ⟨-, -, -, -, hfrob, -⟩ := Certificates.certificate731264
  have h := allLt_spec hfrob hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact rep_of_validA (validA_pgu38ClassReps h.1.1.1)

theorem exists_conj_pgu38ClassRep_of_mem_sylow {u : Equiv.Perm (Fin 513)} (hu : u ∈ pgu38SylowPerm)
    (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) :
    ∃ a ∈ pgu38Perm, ∃ r < 5, a * u * a⁻¹ = pgu38ClassRep r := by
  obtain ⟨-, -, hclass, hreps, -⟩ := Certificates.certificate731264
  obtain ⟨hmem, -, hval⟩ := pgu38SylowPerm_enum
  obtain ⟨i, hi, rfl⟩ := (hmem u).1 hu
  set L := (pgu38SylowEnum ()).pts with hL
  have hrepi := rep_of_validA (hval i hi)
  have hcl : allLt L.size (fun i =>
      !(eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 L[i]! 3) (idA 513) &&
        !eqA 513 L[i]! (idA 513)) ||
      (List.range L.size).any fun h => (List.range 10).any fun j =>
        eqA 513 (conjA 513 L[h]! L[i]!) pgu38ClassReps[j]!) = true := hclass
  have h1 := allLt_spec hcl hi
  have hA : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 L[i]! 3) (idA 513) = true :=
    (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrepi 3) rep_idA).2 hu3
  have hB : eqA 513 L[i]! (idA 513) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hu1 ((eqA_iff hrepi rep_idA).1 h)
  rw [hA, hB] at h1
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_range] at h1
  obtain ⟨h, hh, j, hj, hconj⟩ := h1
  have hbQ : permOfArr 513 L[h]! ∈ pgu38SylowPerm := (hmem _).2 ⟨h, hh, rfl⟩
  have hbN := pgu38SylowPerm_le hbQ
  have hrepT := rep_of_eqA (rep_conjA (hval h hh) hrepi) hconj
  have h2 := allLt_spec hreps hj
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq] at h2
  obtain ⟨⟨⟨-, hvC⟩, hsift⟩, r, hr, hidx, heq⟩ := h2
  have hcN := mem_pgu38Perm_of_sift (rep_of_validA hvC) hsift
  have hfin := (eqA_iff (rep_conjA hvC hrepT) (rep_pgu38ClassRep hr)).1 heq
  refine ⟨permOfArr 513 pgu38RepConj[j]! * permOfArr 513 L[h]!, pgu38Perm.mul_mem hcN hbN, r, hr,
    ?_⟩
  rw [← hfin]
  group

theorem exists_conj_frob_pgu38ClassRep {r : ℕ} (hr : r < 5) :
    ∃ h ∈ pgu38Perm,
      h * (permOfArr 513 gensO[8]! * pgu38ClassRep r * (permOfArr 513 gensO[8]!)⁻¹) * h⁻¹ =
          pgu38ClassRep r ∨
        h * (permOfArr 513 gensO[8]! * pgu38ClassRep r * (permOfArr 513 gensO[8]!)⁻¹) * h⁻¹ =
          (pgu38ClassRep r)⁻¹ := by
  obtain ⟨-, -, -, -, hfrob, -⟩ := Certificates.certificate731264
  have h1 := allLt_spec hfrob hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨hidx, hvH⟩, hsift⟩, heq⟩ := h1
  have hvR := validA_pgu38ClassReps hidx
  have hrepR := rep_of_validA hvR
  have hg8 := gensO_valid 8 (by norm_num)
  have hrepC := rep_conjA hvH (rep_conjA hg8 hrepR)
  refine ⟨permOfArr 513 pgu38FrobConj[r]!, mem_pgu38Perm_of_sift (rep_of_validA hvH) hsift, ?_⟩
  rcases heq with h | h
  · exact Or.inl ((eqA_iff hrepC hrepR).1 h)
  · exact Or.inr ((eqA_iff hrepC (rep_inv_of_validA hvR)).1 h)

theorem exists_conj_pgu38ClassRep (hcard : Nat.card pgu38Perm = 16547328)
    {n : Equiv.Perm (Fin 513)} (hn : n ∈ pgu38Perm) (hn3 : n ^ 3 = 1) (hn1 : n ≠ 1) :
    ∃ a ∈ pgu38Perm, ∃ r < 5, a * n * a⁻¹ = pgu38ClassRep r := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set n' : pgu38Perm := ⟨n, hn⟩ with hn'def
  have hn'3 : n' ^ 3 = 1 := Subtype.ext (by simpa [hn'def] using hn3)
  have hn'1 : n' ≠ 1 := fun h => hn1 (congrArg Subtype.val h)
  have hord : orderOf n' = 3 := orderOf_eq_prime hn'3 hn'1
  have hP : IsPGroup 3 (Subgroup.zpowers n') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hQcard : Nat.card (pgu38SylowPerm.subgroupOf pgu38Perm) =
      3 ^ (Nat.card pgu38Perm).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe pgu38SylowPerm_le).toEquiv,
      pgu38SylowPerm_enum.2.1, hcard, factorization_pgu38]
    norm_num
  set Q : Sylow 3 pgu38Perm := Sylow.ofCard _ hQcard with hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq pgu38Perm S Q
  have hmemS : n' ∈ (S : Subgroup pgu38Perm) := hS (Subgroup.mem_zpowers n')
  have hgn : g * n' * g⁻¹ ∈ (Q : Subgroup pgu38Perm) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map.2 ⟨n', hmemS, by simp [MulAut.conj_apply]⟩
  have hgnQ : ((g * n' * g⁻¹ : pgu38Perm) : Equiv.Perm (Fin 513)) ∈ pgu38SylowPerm := hgn
  have h3 : ((g * n' * g⁻¹ : pgu38Perm) : Equiv.Perm (Fin 513)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, conj_pow, hn'3, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have h1 : ((g * n' * g⁻¹ : pgu38Perm) : Equiv.Perm (Fin 513)) ≠ 1 := by
    intro h
    apply hn'1
    have h' : g * n' * g⁻¹ = 1 := Subtype.ext h
    calc n' = g⁻¹ * (g * n' * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  obtain ⟨a, ha, r, hr, hrep⟩ := exists_conj_pgu38ClassRep_of_mem_sylow hgnQ h3 h1
  refine ⟨a * g, pgu38Perm.mul_mem ha g.2, r, hr, ?_⟩
  rw [← hrep]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn'def]
  group

theorem pgu38Perm_conj (hcard : Nat.card pgu38Perm = 16547328) {γ : Equiv.Perm (Fin 513)}
    (hγ : γ ∈ U38G) {n : Equiv.Perm (Fin 513)} (hn : n ∈ pgu38Perm) (hn3 : n ^ 3 = 1) :
    ∃ h ∈ pgu38Perm, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ h * (γ * n * γ⁻¹) * h⁻¹ = n ^ ε := by
  have hnorm : ∀ {g x : Equiv.Perm (Fin 513)}, g ∈ U38G → x ∈ pgu38Perm →
      g * x * g⁻¹ ∈ pgu38Perm := fun {g x} hg hx =>
    (Subgroup.mem_normalizer_iff.mp (U38G_le_normalizer_pgu38Perm hg) x).mp hx
  have hγ' : γ ∈ Subgroup.closure {g | ∃ k < gensO.size, permOfArr 513 gensO[k]! = g} := hγ
  induction hγ' using Subgroup.closure_induction generalizing n with
  | mem γ hγs =>
    obtain ⟨k, hk, rfl⟩ := hγs
    have hk9 : k < 9 := by rw [gensO_size] at hk; exact hk
    by_cases h8 : k < 8
    · exact ⟨(permOfArr 513 gensO[k]!)⁻¹, inv_mem (gensO_mem_pgu38Perm h8), 1, Or.inl rfl,
        by group⟩
    · obtain rfl : k = 8 := by omega
      by_cases hn1 : n = 1
      · subst hn1
        exact ⟨1, one_mem _, 1, Or.inl rfl, by group⟩
      obtain ⟨a, ha, r, hr, hrep⟩ := exists_conj_pgu38ClassRep hcard hn hn3 hn1
      obtain ⟨b, hb, hb'⟩ := exists_conj_frob_pgu38ClassRep hr
      set g := permOfArr 513 gensO[8]! with hgdef
      have hgaN : g * a * g⁻¹ ∈ pgu38Perm := hnorm hγ ha
      have hn' : n = a⁻¹ * pgu38ClassRep r * a := by rw [← hrep]; group
      refine ⟨a⁻¹ * b * (g * a * g⁻¹), mul_mem (mul_mem (inv_mem ha) hb) hgaN, ?_⟩
      rw [hn']
      rcases hb' with h1 | h1
      · refine ⟨1, Or.inl rfl, ?_⟩
        calc a⁻¹ * b * (g * a * g⁻¹) * (g * (a⁻¹ * pgu38ClassRep r * a) * g⁻¹) *
              (a⁻¹ * b * (g * a * g⁻¹))⁻¹ =
            a⁻¹ * (b * (g * pgu38ClassRep r * g⁻¹) * b⁻¹) * a := by group
          _ = a⁻¹ * pgu38ClassRep r * a := by rw [h1]
          _ = (a⁻¹ * pgu38ClassRep r * a) ^ (1 : ℤ) := (zpow_one _).symm
      · refine ⟨-1, Or.inr rfl, ?_⟩
        calc a⁻¹ * b * (g * a * g⁻¹) * (g * (a⁻¹ * pgu38ClassRep r * a) * g⁻¹) *
              (a⁻¹ * b * (g * a * g⁻¹))⁻¹ =
            a⁻¹ * (b * (g * pgu38ClassRep r * g⁻¹) * b⁻¹) * a := by group
          _ = a⁻¹ * (pgu38ClassRep r)⁻¹ * a := by rw [h1]
          _ = (a⁻¹ * pgu38ClassRep r * a) ^ (-1 : ℤ) := by rw [zpow_neg_one]; group
  | one => exact ⟨1, one_mem _, 1, Or.inl rfl, by group⟩
  | mul γ₁ γ₂ hγ₁ hγ₂ ih₁ ih₂ =>
    have hm : γ₂ * n * γ₂⁻¹ ∈ pgu38Perm := hnorm hγ₂ hn
    have hm3 : (γ₂ * n * γ₂⁻¹) ^ 3 = 1 := by rw [conj_pow, hn3]; group
    obtain ⟨h₂, hh₂, ε₂, hε₂, he₂⟩ := ih₂ hγ₂ hn hn3
    obtain ⟨h₁, hh₁, ε₁, hε₁, he₁⟩ := ih₁ hγ₁ hm hm3
    refine ⟨h₂ * h₁, mul_mem hh₂ hh₁, ε₁ * ε₂, ?_, ?_⟩
    · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> norm_num
    · calc h₂ * h₁ * (γ₁ * γ₂ * n * (γ₁ * γ₂)⁻¹) * (h₂ * h₁)⁻¹ =
            h₂ * (h₁ * (γ₁ * (γ₂ * n * γ₂⁻¹) * γ₁⁻¹) * h₁⁻¹) * h₂⁻¹ := by group
        _ = h₂ * (γ₂ * n * γ₂⁻¹) ^ ε₁ * h₂⁻¹ := by rw [he₁]
        _ = (h₂ * (γ₂ * n * γ₂⁻¹) * h₂⁻¹) ^ ε₁ := (conj_zpow).symm
        _ = (n ^ ε₂) ^ ε₁ := by rw [he₂]
        _ = n ^ (ε₁ * ε₂) := by rw [← zpow_mul, mul_comm]
  | inv γ hγ₀ ih =>
    have hγi : γ⁻¹ ∈ U38G := inv_mem hγ₀
    have hm : γ⁻¹ * n * γ⁻¹⁻¹ ∈ pgu38Perm := hnorm hγi hn
    have hm3 : (γ⁻¹ * n * γ⁻¹⁻¹) ^ 3 = 1 := by rw [conj_pow, hn3]; group
    obtain ⟨h, hh, ε, hε, he⟩ := ih hγ₀ hm hm3
    have he' : h * n * h⁻¹ = (γ⁻¹ * n * γ⁻¹⁻¹) ^ ε := by
      rw [← he]
      group
    have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    refine ⟨h⁻¹, inv_mem hh, ε, hε, ?_⟩
    calc h⁻¹ * (γ⁻¹ * n * γ⁻¹⁻¹) * h⁻¹⁻¹ = h⁻¹ * ((γ⁻¹ * n * γ⁻¹⁻¹) ^ ε) ^ ε * h := by
          rw [← zpow_mul, hεε, zpow_one, inv_inv h]
      _ = h⁻¹ * (h * n * h⁻¹) ^ ε * h := by rw [he']
      _ = n ^ ε := by rw [conj_zpow]; group

theorem commutator_mem_pgu38Perm {a b : Equiv.Perm (Fin 513)} (ha : a ∈ U38G) (hb : b ∈ U38G) :
    a * b * a⁻¹ * b⁻¹ ∈ pgu38Perm := by
  classical
  set G := U38G with hGdef
  set Y : Subgroup G := pgu38Perm.subgroupOf G with hYdef
  haveI hYn : Y.Normal := by
    constructor
    intro y hy g
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have h := (Subgroup.mem_normalizer_iff.mp (U38G_le_normalizer_pgu38Perm g.2)
      (y : Equiv.Perm (Fin 513))).mp hy
    simpa using h
  have hg8G : permOfArr 513 gensO[8]! ∈ G :=
    Subgroup.subset_closure ⟨8, by rw [gensO_size]; norm_num, rfl⟩
  set g8G : G := ⟨_, hg8G⟩ with hg8Gdef
  have hall : ∀ x : G, QuotientGroup.mk' Y x ∈ Subgroup.zpowers (QuotientGroup.mk' Y g8G) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Subgroup.closure {g | ∃ k < gensO.size, permOfArr 513 gensO[k]! = g} := hx
    induction hx' using Subgroup.closure_induction with
    | mem x hxs =>
      obtain ⟨k, hk, rfl⟩ := hxs
      have hk9 : k < 9 := by rw [gensO_size] at hk; exact hk
      by_cases h8 : k < 8
      · have hmem : (⟨permOfArr 513 gensO[k]!, hx⟩ : G) ∈ Y := by
          rw [Subgroup.mem_subgroupOf]
          exact gensO_mem_pgu38Perm h8
        have h1 : QuotientGroup.mk' Y (⟨permOfArr 513 gensO[k]!, hx⟩ : G) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hmem
        rw [h1]
        exact one_mem _
      · obtain rfl : k = 8 := by omega
        exact Subgroup.mem_zpowers _
    | one =>
      have h1 : (⟨1, hx⟩ : G) = 1 := rfl
      rw [h1, map_one]
      exact one_mem _
    | mul x y hx₁ hy₁ ihx ihy =>
      have h1 : (⟨x * y, hx⟩ : G) = ⟨x, hx₁⟩ * ⟨y, hy₁⟩ := rfl
      rw [h1, map_mul]
      exact mul_mem (ihx hx₁) (ihy hy₁)
    | inv x hx₁ ih =>
      have h1 : (⟨x⁻¹, hx⟩ : G) = (⟨x, hx₁⟩ : G)⁻¹ := rfl
      rw [h1, map_inv]
      exact inv_mem (ih hx₁)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hall ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hall ⟨b, hb⟩)
  have hc : QuotientGroup.mk' Y ((⟨a, ha⟩ : G) * ⟨b, hb⟩ * (⟨a, ha⟩ : G)⁻¹ * (⟨b, hb⟩ : G)⁻¹) =
      1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hi, ← hj]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
  simpa using hc

end Certified

section FieldAut

open CFSG.RankThree.PartTwo

theorem exists_inv_aut_pgu38_projImage_glPi {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) :
    ∃ (τ : MulAut ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)))
      (d : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))),
      τ d = d⁻¹ ∧ d ^ 2 ∉ (CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)).subgroupOf
        (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPi : Sec4.PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; rfl⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K := hPi.unitary
  haveI : CharP K 2 := hU.charP
  have hcardK : Fintype.card K = 64 := by rw [Fintype.card_eq_nat_card, hK]; norm_num
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 3 with hσ
  have hσa : ∀ x, σ x = x ^ 8 := fun x => by
    rw [hσ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    norm_num
  have hbar : ∀ x, hU.bar x = σ x := fun x => by
    rw [hU.bar_apply, hσa]
    norm_num
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσa, hσa, ← pow_mul]
    have h := FiniteField.pow_card x
    rw [hcardK] at h
    simpa using h
  set F : MulAut (GL (Fin 3) K) := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut σ
    with hFdef
  have hFcoe : ∀ A : GL (Fin 3) K, ((F A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K).map σ := fun A => rfl
  have hFF : ∀ A, F (F A) = A := fun A => Units.ext (by
    rw [hFcoe, hFcoe, Matrix.map_map]
    ext i j
    simp [hσσ])
  have hFmem : ∀ A ∈ Sec4.glPi false 3 (2 ^ 3) K, F A ∈ Sec4.glPi false 3 (2 ^ 3) K := by
    intro A hA
    rw [Sec4.mem_glPi_false hU] at hA ⊢
    rw [hFcoe]
    have h1 : ((A : Matrix (Fin 3) (Fin 3) K).map σ).map hU.bar =
        ((A : Matrix (Fin 3) (Fin 3) K).map hU.bar).map σ := by
      have hc : (⇑hU.bar ∘ ⇑σ) = (⇑σ ∘ ⇑hU.bar) := funext fun x => by
        simp only [Function.comp, hbar]
      rw [Matrix.map_map, Matrix.map_map, hc]
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul (f := σ), hA,
      Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hFglPi : (Sec4.glPi false 3 (2 ^ 3) K).map (F : GL (Fin 3) K →* GL (Fin 3) K) =
      Sec4.glPi false 3 (2 ^ 3) K := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro A hA
      exact hFmem A hA
    · intro A hA
      exact ⟨F A, hFmem A hA, hFF A⟩
  set FP : MulAut (Matrix.ProjGenLinGroup (Fin 3) K) :=
    QuotientGroup.congr (Subgroup.center (GL (Fin 3) K)) (Subgroup.center (GL (Fin 3) K)) F
      (Subgroup.map_center_eq F) with hFPdef
  have hFPmk : ∀ A, FP (Matrix.ProjGenLinGroup.mk A) = Matrix.ProjGenLinGroup.mk (F A) :=
    fun A => QuotientGroup.congr_mk _ _ _ _ A
  have hPmap : (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)).map
      (FP : Matrix.ProjGenLinGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) =
      CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K) := by
    unfold CFSG.PGLModel.projImage
    rw [Subgroup.map_map]
    have h1 : (FP : Matrix.ProjGenLinGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).comp
        Matrix.ProjGenLinGroup.mk =
        Matrix.ProjGenLinGroup.mk.comp (F : GL (Fin 3) K →* GL (Fin 3) K) :=
      MonoidHom.ext hFPmk
    rw [h1, ← Subgroup.map_map, hFglPi]
  set τ : MulAut ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) :=
    (FP.subgroupMap _).trans (MulEquiv.subgroupCongr hPmap) with hτdef
  have hτ : ∀ p, ((τ p : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) :
      Matrix.ProjGenLinGroup (Fin 3) K) = FP p := fun p => rfl
  have hcardU : Fintype.card Kˣ = 63 := by rw [Fintype.card_units, hcardK]
  obtain ⟨μ, hμ9, hμ3⟩ : ∃ μ : Kˣ, μ ^ 9 = 1 ∧ μ ^ 3 ≠ 1 := by
    obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hordζ : orderOf ζ = 63 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, hcardU]
    refine ⟨ζ ^ 7, ?_, ?_⟩
    · rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hordζ])
    · rw [← pow_mul]
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hordζ] at h1
      norm_num at h1
  have hμ9K : (μ : K) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hμ9, Units.val_one]
  set dv : Fin 3 → K := ![(μ : K), 1, 1] with hdv
  set dw : Fin 3 → K := ![((μ⁻¹ : Kˣ) : K), 1, 1] with hdw
  have hvw : (fun i => dv i * dw i) = fun _ => (1 : K) := by
    funext i
    fin_cases i <;> simp [hdv, hdw]
  have hwv : (fun i => dw i * dv i) = fun _ => (1 : K) := by
    funext i
    fin_cases i <;> simp [hdv, hdw]
  set D : GL (Fin 3) K := ⟨Matrix.diagonal dv, Matrix.diagonal dw,
    by rw [Matrix.diagonal_mul_diagonal, hvw, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, hwv, Matrix.diagonal_one]⟩ with hDdef
  have hDcoe : (D : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal dv := rfl
  have hμ8 : (μ : K) ^ 8 * μ = 1 := by rw [← pow_succ]; exact hμ9K
  have hDmem : D ∈ Sec4.glPi false 3 (2 ^ 3) K := by
    rw [Sec4.mem_glPi_false hU, hDcoe, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    rw [show (fun i => hU.bar (dv i) * dv i) = fun _ => (1 : K) from ?_, Matrix.diagonal_one]
    funext i
    fin_cases i
    · simp [hdv, hbar, hσa, hμ8]
    · simp [hdv]
    · simp [hdv]
  set d : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) :=
    ⟨Matrix.ProjGenLinGroup.mk D, ⟨D, hDmem, rfl⟩⟩ with hddef
  refine ⟨τ, d, ?_, ?_⟩
  · apply Subtype.ext
    rw [hτ, Subgroup.coe_inv]
    show FP (Matrix.ProjGenLinGroup.mk D) = (Matrix.ProjGenLinGroup.mk D)⁻¹
    rw [hFPmk, ← map_inv]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    rw [Units.val_mul, hFcoe, hDcoe, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
      Units.val_one]
    rw [show (fun i => σ (dv i) * dv i) = fun _ => (1 : K) from ?_, Matrix.diagonal_one]
    funext i
    fin_cases i
    · simp [hdv, hσa, hμ8]
    · simp [hdv]
    · simp [hdv]
  · intro hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have h1 : ((d ^ 2 : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))) :
        Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk (D ^ 2) := by
      rw [Subgroup.coe_pow, map_pow]
    rw [h1] at hmem
    obtain ⟨B, hB, hBeq⟩ := hmem
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hBeq
    have hdetB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := ((Sec4.mem_slPi_false hU).mp hB).1
    have hdet := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hu
    simp only [Units.val_mul, Matrix.det_mul, hdetB, one_mul,
      Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, Matrix.det_pow, hDcoe,
      Matrix.det_diagonal, Fin.prod_univ_three, hdv] at hdet
    have hsc : ((Matrix.scalar (Fin 3)) (u : K)).det = (u : K) ^ 3 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
      ring
    have hrhs : (![(μ : K), 1, 1] 0 * ![(μ : K), 1, 1] 1 * ![(μ : K), 1, 1] 2) ^ 2 =
        (μ : K) ^ 2 := by simp
    have hdet' : (u : K) ^ 3 = (μ : K) ^ 2 := by rw [← hsc, ← hrhs]; exact hdet
    have hu3 : u ^ 3 = μ ^ 2 := Units.ext (by simpa using hdet')
    have hu63 : u ^ 63 = 1 := by rw [← hcardU]; exact pow_card_eq_one
    have hμ6 : μ ^ 6 = 1 := by
      have h2 : μ ^ 42 = 1 := by
        calc μ ^ 42 = (μ ^ 2) ^ 21 := by rw [← pow_mul]
          _ = (u ^ 3) ^ 21 := by rw [hu3]
          _ = 1 := by rw [← pow_mul]; exact hu63
      calc μ ^ 6 = (μ ^ 9) ^ 4 * μ ^ 6 := by rw [hμ9, one_pow, one_mul]
        _ = μ ^ 42 := by rw [← pow_mul, ← pow_add]
        _ = 1 := h2
    apply hμ3
    calc μ ^ 3 = μ ^ 9 * (μ ^ 6)⁻¹ := by rw [← pow_sub _ (by norm_num : 6 ≤ 9)]
      _ = 1 := by rw [hμ9, hμ6, inv_one, mul_one]

end FieldAut

section Embedding

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2 (PGUThreeEightData pguModelData)


theorem exists_pgu38Embed {C : Type} [Group C] [Finite C] {M : Subgroup C}
    (hdata : PGUThreeEightData C M) (hchar : M.Characteristic) :
    ∃ Φ : C →* U38G, Function.Injective Φ ∧
      (∀ c, ((Φ c : U38G) : Equiv.Perm (Fin 513)) ∈ X' ↔ c ∈ M) ∧
      (∀ x ∈ X', ∃ c, ((Φ c : U38G) : Equiv.Perm (Fin 513)) = x) ∧
      ∀ θ : MulAut C, ∃ γ : U38G, ∀ c, Φ (θ c) = γ * Φ c * γ⁻¹ := by
  classical
  haveI := hdata.normal
  obtain ⟨e₀⟩ := nonempty_equiv_X' hdata.model
  let ρ : U38G ≃* MulAut X' := MulEquiv.ofBijective rhoU38 (rhoU38_bijective (X := M) hdata.model)
  let κ : C →* MulAut M := MulAut.conjNormal
  have hκ : Function.Injective κ := by
    refine (injective_iff_map_eq_one κ).2 fun x hx => hdata.faithful x fun m hm => ?_
    have h1 := congrArg (fun φ : MulAut M => ((φ ⟨m, hm⟩ : M) : C)) hx
    simp only [κ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * m = (x * m * x⁻¹) * x := by group
      _ = m * x := by rw [h1]
  let Φ : C →* U38G := ρ.symm.toMonoidHom.comp ((MulAut.congr e₀).toMonoidHom.comp κ)
  have hΦ : ∀ c, ρ (Φ c) = MulAut.congr e₀ (κ c) := fun c => ρ.apply_symm_apply _
  have hΦinj : Function.Injective Φ :=
    ρ.symm.injective.comp ((MulAut.congr e₀).injective.comp hκ)
  have hΦM : ∀ m : M, Φ (m : C) =
      ⟨(e₀ m : Equiv.Perm (Fin 513)), (X'_le_pgu38Perm.trans pgu38Perm_le_U38G) (e₀ m).2⟩ := by
    intro m
    apply ρ.injective
    rw [hΦ]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [MulEquiv.ofBijective_apply, rhoU38_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    have h1 : κ (m : C) (e₀.symm x) = m * e₀.symm x * m⁻¹ :=
      Subtype.ext (MulAut.conjNormal_apply _ _)
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp
  refine ⟨Φ, hΦinj, fun c => ⟨fun hc => ?_, fun hc => ?_⟩, fun x hx => ?_, fun θ => ?_⟩
  · set m : M := e₀.symm ⟨_, hc⟩ with hmdef
    have h1 : Φ (m : C) = Φ c := by
      rw [hΦM]
      apply Subtype.ext
      simp [hmdef]
    rw [← hΦinj h1]
    exact m.2
  · have h1 := hΦM ⟨c, hc⟩
    rw [show ((⟨c, hc⟩ : M) : C) = c from rfl] at h1
    rw [h1]
    exact (e₀ ⟨c, hc⟩).2
  · refine ⟨(e₀.symm ⟨x, hx⟩ : C), ?_⟩
    rw [hΦM]
    simp
  · have hθM : M.map (θ : C →* C) = M := Subgroup.characteristic_iff_map_eq.mp hchar θ
    let α : MulAut M := (θ.subgroupMap M).trans (MulEquiv.subgroupCongr hθM)
    have hα : ∀ m : M, ((α m : M) : C) = θ m := fun m => rfl
    have hαs : ∀ m : M, θ ((α.symm m : M) : C) = m := fun m => by
      have h1 := congrArg Subtype.val (α.apply_symm_apply m)
      rw [hα] at h1
      exact h1
    have hκθ : ∀ c, κ (θ c) = α * κ c * α⁻¹ := by
      intro c
      refine MulEquiv.ext fun m => Subtype.ext ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
      simp only [κ, MulAut.conjNormal_apply, hα]
      rw [map_mul, map_mul, map_inv, hαs]
    refine ⟨ρ.symm (MulAut.congr e₀ α), fun c => ρ.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hΦ, hΦ, hκθ, map_mul, map_mul,
      map_inv]

end Embedding

section Classes

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2 (pguModelData)
open CFSG.RankThree.PartTwo


theorem pgu38_aut_conj_or_inv_model {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2)
    (θ : MulAut ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)))
    {b : ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))} (hb : b ^ 3 = 1) :
    ∃ h, h * θ b * h⁻¹ = b ∨ h * θ b * h⁻¹ = b⁻¹ := by
  classical
  have hPi : Sec4.PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; rfl⟩
  have hdata := pguModelData hK
  have hcomm := Sec13.commutator_projImage_glPi hPi (by norm_num : 2 < 2 ^ 3)
  have hchar : ((CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ 3) K)).subgroupOf
      (CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K))).Characteristic := by
    rw [← hcomm]
    infer_instance
  have hcardP : Nat.card ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 3) K)) = 16547328 := by
    rw [Sec16.ProofKSL3Two.card_projImage_glPi hPi, Sec13.card_slPi_three hPi]
    norm_num
  obtain ⟨Φ, hΦinj, hΦX, hΦX', hΦaut⟩ := exists_pgu38Embed hdata hchar
  obtain ⟨τ, d, hτd, hd2⟩ := exists_inv_aut_pgu38_projImage_glPi hK
  set H : Subgroup (Equiv.Perm (Fin 513)) := Φ.range.map U38G.subtype with hHdef
  have hmemH : ∀ x, x ∈ H ↔ ∃ c, ((Φ c : U38G) : Equiv.Perm (Fin 513)) = x := by
    intro x
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Φ c, ⟨c, rfl⟩, rfl⟩
  have hcardH : Nat.card H = 16547328 := by
    rw [hHdef, Subgroup.card_map_of_injective U38G.subtype_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, hcardP]
  have hX'H : X' ≤ H := fun x hx => (hmemH x).2 (hΦX' x hx)
  obtain ⟨γ, hγ⟩ := hΦaut τ
  have hd' : Φ d⁻¹ = γ * Φ d * γ⁻¹ := by rw [← hτd, hγ]
  have hx : Φ (d ^ 2)⁻¹ = γ * Φ d * γ⁻¹ * (Φ d)⁻¹ := by
    rw [← hd', ← map_inv, ← map_mul]
    congr 1
    group
  have hxN : ((Φ (d ^ 2)⁻¹ : U38G) : Equiv.Perm (Fin 513)) ∈ pgu38Perm := by
    rw [hx]
    simpa using commutator_mem_pgu38Perm γ.2 (Φ d).2
  have hxX' : ((Φ (d ^ 2)⁻¹ : U38G) : Equiv.Perm (Fin 513)) ∉ X' := fun h =>
    hd2 (inv_mem_iff.mp ((hΦX _).mp h))
  set J := H ⊓ pgu38Perm with hJdef
  have hX'J : X' ≤ J := le_inf hX'H X'_le_pgu38Perm
  have hxJ : ((Φ (d ^ 2)⁻¹ : U38G) : Equiv.Perm (Fin 513)) ∈ J :=
    ⟨(hmemH _).2 ⟨_, rfl⟩, hxN⟩
  have hJH : J = H := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hX'J
    rw [card_X'] at hk
    have hJd : Nat.card J ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
    rw [hk, hcardH, show (16547328 : ℕ) = 5515776 * 3 by norm_num] at hJd
    have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hJd
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with rfl | rfl
    · exfalso
      have hXJ : X' = J := Subgroup.eq_of_le_of_card_ge hX'J (by rw [hk, card_X', mul_one])
      exact hxX' (hXJ ▸ hxJ)
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hcardH])
  have hHN : H ≤ pgu38Perm := by
    rw [← hJH]
    exact inf_le_right
  have hcardN : Nat.card pgu38Perm = 16547328 := by
    apply le_antisymm
    · have h := card_pgu38Perm_le
      rw [card_X'] at h
      exact h.trans (by norm_num)
    · rw [← hcardH]
      exact Subgroup.card_le_of_le hHN
  have hHeq : H = pgu38Perm := Subgroup.eq_of_le_of_card_ge hHN (by rw [hcardN, hcardH])
  obtain ⟨γθ, hγθ⟩ := hΦaut θ
  have hn : ((Φ b : U38G) : Equiv.Perm (Fin 513)) ∈ pgu38Perm := hHN ((hmemH _).2 ⟨b, rfl⟩)
  have hn3 : ((Φ b : U38G) : Equiv.Perm (Fin 513)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hb, map_one, Subgroup.coe_one]
  obtain ⟨h', hh', ε, hε, he⟩ := pgu38Perm_conj hcardN γθ.2 hn hn3
  obtain ⟨h, rfl⟩ := (hmemH h').1 (hHeq ▸ hh')
  have hfin : Φ (h * θ b * h⁻¹) = Φ (b ^ ε) := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, hγθ, map_zpow]
    simpa using he
  have hfin' := hΦinj hfin
  rcases hε with rfl | rfl
  · exact ⟨h, Or.inl (by rw [hfin', zpow_one])⟩
  · exact ⟨h, Or.inr (by rw [hfin', zpow_neg_one])⟩

theorem pgu38OrderThreeAutClasses_holds : PGU38OrderThreeAutClasses := by
  intro C _ hC θ b hb
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hC
  obtain ⟨h, hh⟩ := pgu38_aut_conj_or_inv_model hK (MulAut.congr e θ) (b := e b)
    (by rw [← map_pow, hb, map_one])
  have hθ : MulAut.congr e θ (e b) = e (θ b) := by simp [MulAut.congr_apply]
  rw [hθ] at hh
  refine ⟨e.symm h, ?_⟩
  rcases hh with hh | hh
  · left
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hh]
  · right
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hh, map_inv]

end Classes

section Main


set_option linter.unusedSectionVars false

theorem d4EightTrialityInnerPairs_holds : D4EightTrialityInnerPairs :=
  d4EightTrialityInnerPairs_of_pgu38 pgu38OrderThreeAutClasses_holds

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
