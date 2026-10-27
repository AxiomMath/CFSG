module

public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

variable {X : Type*} [Group X] [Finite X]

theorem not_two_dvd_card_comap {N : Subgroup X} [N.Normal] (hN : ¬ 2 ∣ Nat.card N) {p : ℕ}
    (hp2 : p ≠ 2) (hp : p.Prime) {Q : Subgroup (X ⧸ N)} (hQ : IsPGroup p Q) :
    ¬ 2 ∣ Nat.card (Q.comap (QuotientGroup.mk' N)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  have : Fintype (Q.comap (QuotientGroup.mk' N)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hm2 : (m : X) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hm
    rw [← hm]
    exact pow_orderOf_eq_one _
  have hyQ : QuotientGroup.mk' N (m : X) ∈ Q := m.2
  obtain ⟨k, hk⟩ := hQ ⟨_, hyQ⟩
  have hk' : (QuotientGroup.mk' N (m : X)) ^ p ^ k = 1 := congrArg Subtype.val hk
  have hgcd : Nat.gcd (p ^ k) 2 = 1 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hy1 : QuotientGroup.mk' N (m : X) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hk', by rw [← map_pow, hm2, map_one]⟩
    rwa [hgcd, pow_one] at this
  have hmN : (m : X) ∈ N := (QuotientGroup.eq_one_iff _).mp hy1
  apply hN
  have := orderOf_dvd_natCard (⟨m, hmN⟩ : N)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hm] at this

theorem map_eq_of_fusionIsSylowIn {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] (f : X →* Y)
    {P M : Subgroup X} (hP : fusionIsSylowIn p P M) (hM : IsPGroup p (M.map f)) :
    P.map f = M.map f := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_fusionIsSylowIn hP
  have : Finite M := inferInstance
  let S' : Sylow p (M.map f) := S.mapSurjective (f.subgroupMap_surjective M)
  have htop : (S' : Subgroup (M.map f)) = ⊤ :=
    le_antisymm le_top (S'.3 (hM.to_subgroup ⊤) le_top).le
  have h1 : ((S : Subgroup M).map M.subtype).map f =
      (((S : Subgroup M).map (f.subgroupMap M)).map (M.map f).subtype) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1, ← Sylow.coe_mapSurjective (f.subgroupMap_surjective M), htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem le_normalizer_of_forall_le {A M S : Subgroup X} {p : ℕ} (hSM : S ≤ M)
    (hSp : IsPGroup p S) (hall : ∀ R : Subgroup X, R ≤ M → IsPGroup p R → R ≤ S)
    (hAM : A ≤ Subgroup.normalizer (M : Set X)) : A ≤ Subgroup.normalizer (S : Set X) := by
  intro a ha
  have hle1 : conjSub a⁻¹ S ≤ S := by
    refine hall _ ?_ (hSp.map _)
    have h1 := conjSub_mono (g := a⁻¹) hSM
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ (hAM ha))] at h1
  have heq : conjSub a⁻¹ S = S := Subgroup.eq_of_le_of_card_ge hle1 (by rw [card_conjSub])
  have := mem_normalizer_of_conjSub_eq heq
  simpa using this

theorem isPGroup_two_center (hO : ∀ N : Subgroup X, N.Normal → ¬ 2 ∣ Nat.card N → N = ⊥) :
    IsPGroup 2 (Subgroup.center X) := by
  intro z
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : X)).ne'
  refine ⟨k, Subtype.ext ?_⟩
  set w := (z : X) ^ 2 ^ k with hw
  have hwc : w ∈ Subgroup.center X := (Subgroup.center X).pow_mem z.2 _
  have hnormal : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hwc hx) g
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hord_w : orderOf w = m := by
    rw [hw, orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hord, Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hbot := hO _ hnormal (by
    rw [Nat.card_zpowers, hord_w]
    exact fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))
  have : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
  rw [hbot] at this
  simpa using Subgroup.mem_bot.mp this

section QuotOdd

variable {N : Subgroup X} [N.Normal]

theorem fusionIsSylowIn_sup_of_isMaxInv (hN : ¬ 2 ∣ Nat.card N) {A : Subgroup X}
    (hA : IsPGroup 2 A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup X}
    (hP : IsMaxInv A p P) : fusionIsSylowIn p P (P ⊔ N) ∧ ¬ 2 ∣ Nat.card (P ⊔ N : Subgroup X) := by
  have hp : p.Prime := Fact.out
  have hcomap : (P.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = P ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hodd : ¬ 2 ∣ Nat.card (P ⊔ N : Subgroup X) := by
    rw [← hcomap]
    exact not_two_dvd_card_comap hN hp2 hp (hP.isInv.1.map _)
  have hAM : A ≤ Subgroup.normalizer ((P ⊔ N : Subgroup X) : Set X) :=
    le_normalizer_sup hP.isInv.2 le_normalizer_of_normal
  obtain ⟨S, hS, hPS, hAS⟩ := exists_invariant_sylow_containing Nat.prime_two hp hA hodd hAM
    le_sup_left hP.isInv.1 hP.isInv.2
  have hSP := hP.eq_of_le ⟨hS.2.1, hAS⟩ hPS
  rw [hSP] at hS
  exact ⟨hS, hodd⟩

theorem isMaxInv_map_mk (hN : ¬ 2 ∣ Nat.card N) {A : Subgroup X} (hA : IsPGroup 2 A) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsMaxInv A p P) :
    IsMaxInv (A.map (QuotientGroup.mk' N)) p (P.map (QuotientGroup.mk' N)) := by
  have hp : p.Prime := Fact.out
  set f := QuotientGroup.mk' N with hf
  refine ⟨⟨hP.isInv.1.map _, (Subgroup.map_mono hP.isInv.2).trans (Subgroup.le_normalizer_map f)⟩,
    fun Q hQ hle => ?_⟩
  set M := Q.comap f with hM
  have hPM : P ≤ M := fun x hx => hle ⟨x, hx, rfl⟩
  have hModd : ¬ 2 ∣ Nat.card M := not_two_dvd_card_comap hN hp2 hp hQ.1
  have hAM : A ≤ Subgroup.normalizer (M : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have ha' := hQ.2 (Subgroup.mem_map_of_mem f ha)
    simp only [hM, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp ha' (f x)
  obtain ⟨S, hS, hPS, hAS⟩ := exists_invariant_sylow_containing Nat.prime_two hp hA hModd hAM
    hPM hP.isInv.1 hP.isInv.2
  have hSP := hP.eq_of_le ⟨hS.2.1, hAS⟩ hPS
  rw [hSP] at hS
  have hMQ : M.map f = Q := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective N) Q
  have := map_eq_of_fusionIsSylowIn f hS (by rw [hMQ]; exact hQ.1)
  rw [this, hMQ]

theorem exists_mem_normalizer_of_mk (A : Sylow 2 X) {y : X ⧸ N}
    (hy : y ∈ Subgroup.normalizer
      (((A : Subgroup X).map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N))) :
    ∃ x ∈ Subgroup.normalizer ((A : Subgroup X) : Set X), QuotientGroup.mk' N x = y := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N y
  set f := QuotientGroup.mk' N with hf
  set M := (A : Subgroup X) ⊔ N with hMdef
  have hM : ((A : Subgroup X).map f).comap f = M := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hle : conjSub x₀ (A : Subgroup X) ≤ M := by
    intro z hz
    rw [← hM]
    rw [mem_conjSub] at hz
    have := conj_inv_mem_of_mem_normalizer hy (Subgroup.mem_map_of_mem f hz)
    simp only [map_mul, map_inv] at this
    simpa [Subgroup.mem_comap, mul_assoc] using this
  have hAM : (A : Subgroup X) ≤ M := le_sup_left
  let S₁ : Sylow 2 M := A.subtype hAM
  have hA₂ : ((x₀⁻¹ • A : Sylow 2 X) : Subgroup X) = conjSub x₀ (A : Subgroup X) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, conjSub]
    rfl
  let S₂ : Sylow 2 M := (x₀⁻¹ • A).subtype (hA₂ ▸ hle)
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S₁ S₂
  have hS₁ : (S₁ : Subgroup M).map M.subtype = A := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hAM]
  have hS₂ : (S₂ : Subgroup M).map M.subtype = conjSub x₀ (A : Subgroup X) := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le (hA₂ ▸ hle), hA₂]
  have key : (A : Subgroup X).map (MulAut.conj (m : X)).toMonoidHom =
      conjSub x₀ (A : Subgroup X) := by
    rw [← hS₂, ← hm, map_subtype_smul_sylow, hS₁]
  have hmM : (m : X) ∈ N ⊔ (A : Subgroup X) := by rw [sup_comm]; exact m.2
  obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_left.mp hmM
  have key' : conjSub x₀ (A : Subgroup X) = conjSub n⁻¹ (A : Subgroup X) := by
    rw [← key, ← hna, conjSub]
    ext z
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    constructor
    · intro hz
      have := conj_mem_of_mem_normalizer (Subgroup.le_normalizer ha) hz
      simpa [mul_assoc] using this
    · intro hz
      have := conj_inv_mem_of_mem_normalizer (Subgroup.le_normalizer ha) hz
      simpa [mul_assoc] using this
  refine ⟨x₀ * n, mem_normalizer_of_conjSub_eq ?_, ?_⟩
  · rw [conjSub_mul, key', conjSub_conjSub_inv]
  · have hfn : f n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hfn, mul_one]

end QuotOdd

theorem nconj_of_quotient_odd {N : Subgroup X} [N.Normal] (hN : ¬ 2 ∣ Nat.card N) (A : Sylow 2 X)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : ∀ Q Q' : Subgroup (X ⧸ N), IsMaxInv ((A : Subgroup X).map (QuotientGroup.mk' N)) p Q →
      IsMaxInv ((A : Subgroup X).map (QuotientGroup.mk' N)) p Q' →
      NConj ((A : Subgroup X).map (QuotientGroup.mk' N)) Q Q')
    {P P' : Subgroup X} (hP : IsMaxInv (A : Subgroup X) p P)
    (hP' : IsMaxInv (A : Subgroup X) p P') : NConj (A : Subgroup X) P P' := by
  have hp : p.Prime := Fact.out
  set f := QuotientGroup.mk' N with hf
  obtain ⟨y, hy, hyP⟩ := hQ _ _ (isMaxInv_map_mk hN A.isPGroup' hp2 hP)
    (isMaxInv_map_mk hN A.isPGroup' hp2 hP')
  obtain ⟨x, hx, rfl⟩ := exists_mem_normalizer_of_mk A hy
  have hP₁ := hP.conjSub hx
  have hmap : (conjSub x P).map f = P'.map f := by rw [map_conjSub, hyP]
  have hsup : conjSub x P ⊔ N = P' ⊔ N := by
    have h1 := congrArg (Subgroup.comap f) hmap
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  obtain ⟨hS₁, -⟩ := fusionIsSylowIn_sup_of_isMaxInv hN A.isPGroup' hp2 hP₁
  rw [hsup] at hS₁
  obtain ⟨hS', hodd⟩ := fusionIsSylowIn_sup_of_isMaxInv hN A.isPGroup' hp2 hP'
  obtain ⟨c, hc, hcP⟩ := exists_conj_of_invariant_sylows Nat.prime_two hp A.isPGroup' hodd
    (le_normalizer_sup hP'.isInv.2 le_normalizer_of_normal) hS₁ hS' hP₁.isInv.2 hP'.isInv.2
  refine ⟨x * c⁻¹, Subgroup.mul_mem _ hx
    (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hc).2)), ?_⟩
  rw [hcP, conjSub_eq_map_conj, conjSub_mul]

section QuotCenter

variable {Z : Subgroup X} [Z.Normal]

theorem exists_normal_sylow_comap (hZc : Z ≤ Subgroup.center X) {p : ℕ} [Fact p.Prime]
    {Q : Subgroup (X ⧸ Z)} (hQ : IsPGroup p Q) :
    ∃ S : Subgroup X, fusionIsSylowIn p S (Q.comap (QuotientGroup.mk' Z)) ∧
      (∀ R : Subgroup X, R ≤ Q.comap (QuotientGroup.mk' Z) → IsPGroup p R → R ≤ S) ∧
      S.map (QuotientGroup.mk' Z) = Q := by
  set f := QuotientGroup.mk' Z with hf
  set M := Q.comap f with hM
  have hnil : Group.IsNilpotent M := by
    have : Group.IsNilpotent Q := hQ.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center (f.subgroupComap Q) ?_
    intro m hm
    have hmZ : (m : X) ∈ Z := by
      have h := MonoidHom.mem_ker.mp hm
      have h' : f (m : X) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hmZ) g)
  have hall := (Group.isNilpotent_of_finite_tfae (G := M)).out 1 4
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p M))
  have hS₀n : (S₀ : Subgroup M).Normal := hall.mp hnil p inferInstance S₀
  have hSsyl := fusionIsSylowIn_map S₀
  refine ⟨(S₀ : Subgroup M).map M.subtype, hSsyl, fun R hRM hR => ?_, ?_⟩
  · have hle : R.subgroupOf M ≤ S₀ := by
      obtain ⟨S₁, hS₁⟩ := (hR.comap_subtype (K := M)).exists_le_sylow
      have : Unique (Sylow p M) := Sylow.unique_of_normal S₀ hS₀n
      rw [Subsingleton.elim S₁ S₀] at hS₁
      exact hS₁
    have := Subgroup.map_mono (f := M.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hRM] at this
  · rw [map_eq_of_fusionIsSylowIn f hSsyl (by
      rw [hM, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]; exact hQ),
      hM, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]

theorem isMaxInv_map_mk_center (hZc : Z ≤ Subgroup.center X) {A : Subgroup X} {p : ℕ}
    [Fact p.Prime] {P : Subgroup X} (hP : IsMaxInv A p P) :
    IsMaxInv (A.map (QuotientGroup.mk' Z)) p (P.map (QuotientGroup.mk' Z)) := by
  set f := QuotientGroup.mk' Z with hf
  refine ⟨⟨hP.isInv.1.map _, (Subgroup.map_mono hP.isInv.2).trans (Subgroup.le_normalizer_map f)⟩,
    fun Q hQ hle => ?_⟩
  set M := Q.comap f with hM
  have hPM : P ≤ M := fun x hx => hle ⟨x, hx, rfl⟩
  have hAM : A ≤ Subgroup.normalizer (M : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have ha' := hQ.2 (Subgroup.mem_map_of_mem f ha)
    simp only [hM, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp ha' (f x)
  obtain ⟨S, hS, hSall, hSQ⟩ := exists_normal_sylow_comap hZc hQ.1
  have hPS : P ≤ S := hSall P hPM hP.isInv.1
  have hAS : A ≤ Subgroup.normalizer (S : Set X) := by
    intro a ha
    have hle1 : conjSub a⁻¹ S ≤ S := by
      refine hSall _ ?_ (hS.2.1.map _)
      have h1 := conjSub_mono (g := a⁻¹) hS.1
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ (hAM ha))] at h1
    have heq : conjSub a⁻¹ S = S := Subgroup.eq_of_le_of_card_ge hle1 (by rw [card_conjSub])
    have := mem_normalizer_of_conjSub_eq heq
    simpa using this
  have hSP := hP.eq_of_le ⟨hS.2.1, hAS⟩ hPS
  rw [← hSQ, hSP]

theorem nconj_of_quotient_center (hZc : Z ≤ Subgroup.center X) (hZ2 : IsPGroup 2 Z)
    (A : Sylow 2 X) {p : ℕ} [Fact p.Prime]
    (hQ : ∀ Q Q' : Subgroup (X ⧸ Z), IsMaxInv ((A : Subgroup X).map (QuotientGroup.mk' Z)) p Q →
      IsMaxInv ((A : Subgroup X).map (QuotientGroup.mk' Z)) p Q' →
      NConj ((A : Subgroup X).map (QuotientGroup.mk' Z)) Q Q')
    {P P' : Subgroup X} (hP : IsMaxInv (A : Subgroup X) p P)
    (hP' : IsMaxInv (A : Subgroup X) p P') : NConj (A : Subgroup X) P P' := by
  set f := QuotientGroup.mk' Z with hf
  obtain ⟨y, hy, hyP⟩ := hQ _ _ (isMaxInv_map_mk_center hZc hP) (isMaxInv_map_mk_center hZc hP')
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
  rw [← hf] at hy hyP
  have hZA : Z ≤ (A : Subgroup X) := hZ2.le_sylow_of_normal A
  have hx : x ∈ Subgroup.normalizer ((A : Subgroup X) : Set X) := by
    apply mem_normalizer_of_conjSub_eq
    have hle : conjSub x (A : Subgroup X) ≤ A := by
      intro z hz
      rw [mem_conjSub] at hz
      have hz'' : z ∈ ((A : Subgroup X).map f).comap f := by
        have := conj_inv_mem_of_mem_normalizer hy (Subgroup.mem_map_of_mem f hz)
        simp only [map_mul, map_inv] at this
        simpa [Subgroup.mem_comap, mul_assoc] using this
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZA] at hz''
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hP₁ := hP.conjSub hx
  have hmap : (conjSub x P).map f = P'.map f := by rw [map_conjSub, hyP]
  have hPM₁ : conjSub x P ≤ (P'.map f).comap f := by
    rw [← hmap]; exact Subgroup.le_comap_map _ _
  have hP'M : P' ≤ (P'.map f).comap f := Subgroup.le_comap_map _ _
  obtain ⟨S, hS, hSall, -⟩ := exists_normal_sylow_comap hZc (hP'.isInv.1.map f)
  have hAM : (A : Subgroup X) ≤ Subgroup.normalizer (((P'.map f).comap f : Subgroup X) : Set X) :=
    le_normalizer_comap f ((Subgroup.map_mono hP'.isInv.2).trans (Subgroup.le_normalizer_map f))
  have hAS := le_normalizer_of_forall_le hS.1 hS.2.1 hSall hAM
  have e1 := hP₁.eq_of_le ⟨hS.2.1, hAS⟩ (hSall _ hPM₁ hP₁.isInv.1)
  have e2 := hP'.eq_of_le ⟨hS.2.1, hAS⟩ (hSall _ hP'M hP'.isInv.1)
  exact ⟨x, hx, by rw [← e2, e1]⟩

end QuotCenter

end CFSG.Goldschmidt.G310
