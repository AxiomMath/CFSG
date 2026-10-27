module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.B

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_two_of_sq_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A] (T : Subgroup A)
    (hT : ∀ x ∈ T, x * x = 1) : Nat.card T ≤ 2 := by
  classical
  have := Fintype.ofFinite A
  have h2 := IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num)
  have hinj : Function.Injective
      (fun t : T => (⟨(t : A), by simpa [pow_two] using hT t t.2⟩ : {x : A // x ^ 2 = 1})) := by
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext this
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card {x : A // x ^ 2 = 1} = (Finset.univ.filter (fun x : A => x ^ 2 = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem cyclic_invol_unique [Finite G] {F : Subgroup G} (hF : IsCyclic ↥F) {a b : G}
    (ha : a ∈ F) (hb : b ∈ F) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  classical
  have := Fintype.ofFinite ↥F
  have h := IsCyclic.card_pow_eq_one_le (α := ↥F) (n := 2) (by norm_num)
  by_contra hab
  let a' : ↥F := ⟨a, ha⟩
  let b' : ↥F := ⟨b, hb⟩
  have hsub : ({1, a', b'} : Finset ↥F) ⊆ Finset.univ.filter (fun x : ↥F => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [a', b', pow_two, Subtype.ext_iff, ha2, hb2]
  have hcard : ({1, a', b'} : Finset ↥F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro e
      simp only [Finset.mem_singleton] at e
      exact hab (congrArg Subtype.val e)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_⟩
      · intro e; exact ha1 (congrArg Subtype.val e).symm
      · intro e; exact hb1 (congrArg Subtype.val e).symm
  have := Finset.card_le_card hsub
  omega

theorem mem_of_orderOf_le [Finite G] {F Q : Subgroup G} (hF : IsCyclic ↥F) (hQF : Q ≤ F)
    (h2F : IsPGroup 2 ↥F) {f : G} (hf : f ∈ F) (hle : orderOf f ≤ Nat.card Q) : f ∈ Q := by
  classical
  have := Fintype.ofFinite ↥F
  have := Fintype.ofFinite ↥Q
  have h2Q : IsPGroup 2 ↥Q :=
    h2F.of_injective (Subgroup.inclusion hQF) (Subgroup.inclusion_injective hQF)
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).1 h2Q
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2F) ⟨f, hf⟩
  have hk' : orderOf f = 2 ^ k := by simpa using hk
  have hkc : k ≤ c := by
    have : 2 ^ k ≤ 2 ^ c := by rw [← hk', ← hc]; exact hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hfpow : f ^ (2 ^ c) = 1 := by
    have : f ^ (2 ^ k) = 1 := by rw [← hk']; exact pow_orderOf_eq_one f
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkc
    rw [hj, pow_add, pow_mul, this, one_pow]
  have hcard := IsCyclic.card_pow_eq_one_le (α := ↥F) (n := 2 ^ c) (by positivity)
  let T : Finset ↥F := Finset.univ.filter (fun x : ↥F => x ^ (2 ^ c) = 1)
  let ι : ↥Q → ↥F := fun q => ⟨q.1, hQF q.2⟩
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (by simpa [ι] using congrArg Subtype.val h)
  have hQT : Finset.univ.image ι ⊆ T := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨q, rfl⟩ := hx
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, ι]
    apply Subtype.ext
    have h1 : (q : ↥Q) ^ (2 ^ c) = 1 := by rw [← hc]; exact pow_card_eq_one'
    simpa using congrArg Subtype.val h1
  have hcardQ : (Finset.univ.image ι).card = 2 ^ c := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ← hc, Nat.card_eq_fintype_card]
  have hTeq : Finset.univ.image ι = T :=
    Finset.eq_of_subset_of_card_le hQT (by rw [hcardQ]; exact hcard)
  have hfT : (⟨f, hf⟩ : ↥F) ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext (by simpa using hfpow)
  rw [← hTeq] at hfT
  simp only [Finset.mem_image, Finset.mem_univ, true_and, ι] at hfT
  obtain ⟨q, hq⟩ := hfT
  have := congrArg Subtype.val hq
  simp only at this
  rw [← this]
  exact q.2

theorem card_le_four_of_cyclic_quot [Finite G] {N P F E : Subgroup G} (hFN : F ≤ N)
    (hnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P) (hprod : ∀ n ∈ N, ∃ p ∈ P, ∃ f ∈ F, n = p * f)
    (hF : IsCyclic ↥F)
    (hrk : ∀ a ∈ P, ∀ b ∈ P, a * a = 1 → b * b = 1 → a * b = b * a → a = 1 ∨ b = 1 ∨ a = b)
    (hE : E ≤ N) (hEx : ∀ a ∈ E, a * a = 1) :
    Nat.card E ≤ 4 := by
  classical
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := hEx (a * b) (E.mul_mem ha hb)
    have h2 := hEx a ha
    have h3 := hEx b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
    have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, ha', hb'] at hab'
    exact hab'.symm
  set P' : Subgroup ↥N := P.subgroupOf N with hP'
  have hPnormal : P'.Normal := ⟨fun n hn g => by
    rw [hP', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm (g : G) g.2 (n : G) hn⟩
  let π : ↥N →* ↥N ⧸ P' := QuotientGroup.mk' P'
  let ι : ↥F →* ↥N := (Subgroup.inclusion hFN)
  have hsurj : Function.Surjective (π.comp ι) := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, f, hf, hnpf⟩ := hprod n n.2
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [MonoidHom.comp_apply, π, ι]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (⟨f, hFN hf⟩ : ↥N)⁻¹ * n ∈ P'
    rw [hP', Subgroup.mem_subgroupOf]
    show f⁻¹ * (n : G) ∈ P
    rw [hnpf]
    have : f⁻¹ * (p * f) = (f⁻¹ * p * f⁻¹⁻¹) := by group
    rw [this]
    have := hnorm f⁻¹ (hFN (F.inv_mem hf)) p hp
    exact this
  have hcyc : IsCyclic (↥N ⧸ P') := isCyclic_of_surjective (π.comp ι) hsurj
  let φ : ↥E →* ↥N ⧸ P' := π.comp (Subgroup.inclusion hE)
  have hrange : Nat.card φ.range ≤ 2 := by
    apply card_le_two_of_sq_eq_one
    rintro x ⟨e, rfl⟩
    rw [← map_mul]
    have : e * e = 1 := by
      apply Subtype.ext
      simpa using hEx e e.2
    rw [this, map_one]
  have hkerP : ∀ x : φ.ker, ((x : ↥E) : G) ∈ P := by
    intro x
    have := x.2
    rw [MonoidHom.mem_ker] at this
    simp only [φ, MonoidHom.comp_apply, π, QuotientGroup.mk'_apply] at this
    have h2 := (QuotientGroup.eq_one_iff _).1 this
    exact (Subgroup.mem_subgroupOf).1 h2
  have hker : Nat.card φ.ker ≤ 2 := by
    by_cases hbot : ∀ x : φ.ker, x = 1
    · have : Subsingleton φ.ker := ⟨fun a b => (hbot a).trans (hbot b).symm⟩
      have := Finite.card_le_one_iff_subsingleton.2 this
      omega
    · push Not at hbot
      obtain ⟨x, hx1⟩ := hbot
      have hx2 : ((x : ↥E) : G) * ((x : ↥E) : G) = 1 := hEx _ (x : ↥E).2
      have hle : (⊤ : Subgroup φ.ker) ≤ zpowers x := by
        intro w _
        rcases hrk _ (hkerP w) _ (hkerP x) (hEx _ (w : ↥E).2) hx2
            (hEc _ (w : ↥E).2 _ (x : ↥E).2) with h | h | h
        · have : w = 1 := by apply Subtype.ext; apply Subtype.ext; simpa using h
          rw [this]; exact one_mem _
        · exact absurd (by apply Subtype.ext; apply Subtype.ext; simpa using h) hx1
        · have : w = x := by apply Subtype.ext; apply Subtype.ext; exact h
          rw [this]; exact mem_zpowers x
      have h1 : Nat.card (⊤ : Subgroup φ.ker) ≤ Nat.card (zpowers x) :=
        Subgroup.card_le_of_le hle
      have h2 : Nat.card (⊤ : Subgroup φ.ker) = Nat.card φ.ker := by
        rw [Subgroup.card_top]
      have h3 : Nat.card (zpowers x) = orderOf x := Nat.card_zpowers x
      have h4 : orderOf x = 2 := by
        apply orderOf_eq_prime
        · apply Subtype.ext; apply Subtype.ext
          simpa [pow_two] using hx2
        · exact hx1
      omega
  have hcard := Subgroup.card_mul_index φ.ker
  have hidx : φ.ker.index = Nat.card φ.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  rw [hidx] at hcard
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
    _ = 4 := by norm_num

theorem relIndex_ne_zero' [Finite G] {H K : Subgroup G} : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem card_subgroup_le_finset [Finite G] (E : Subgroup G) (T : Finset G) (h : ∀ e ∈ E, e ∈ T) :
    Nat.card E ≤ T.card := by
  classical
  have hinj : Function.Injective (fun e : E => (⟨(e : G), h e e.2⟩ : ↥T)) := by
    intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem eq_sup_zpowers_of_relIndex_le_two [Finite G] {S H : Subgroup G} (hHS : H ≤ S)
    (hidx : H.relIndex S ≤ 2) {y : G} (hy : y ∈ S) (hyH : y ∉ H) : S = H ⊔ zpowers y := by
  have hle : H ⊔ zpowers y ≤ S := sup_le hHS (zpowers_le.2 hy)
  by_contra hne
  have hlt : H ⊔ zpowers y < S := lt_of_le_of_ne hle (fun h => hne h.symm)
  have h1 : H.relIndex (H ⊔ zpowers y) * (H ⊔ zpowers y).relIndex S = H.relIndex S :=
    Subgroup.relIndex_mul_relIndex H (H ⊔ zpowers y) S le_sup_left hle
  have hpos1 : H.relIndex (H ⊔ zpowers y) ≠ 0 := relIndex_ne_zero'
  have hne1 : H.relIndex (H ⊔ zpowers y) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hyH (h (mem_sup_right (mem_zpowers y)))
  have hne2 : (H ⊔ zpowers y).relIndex S ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact (not_le_of_gt hlt) h
  have hpos2 : (H ⊔ zpowers y).relIndex S ≠ 0 := relIndex_ne_zero'
  have : 2 * 2 ≤ H.relIndex (H ⊔ zpowers y) * (H ⊔ zpowers y).relIndex S :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem mem_or_mul_inv_mem [Finite G] {S H : Subgroup G} (hidx : H.relIndex S ≤ 2)
    {y : G} (hy : y ∈ S) (hyH : y ∉ H) {e : G} (he : e ∈ S) : e ∈ H ∨ e * y⁻¹ ∈ H := by
  by_cases heH : e ∈ H
  · exact Or.inl heH
  · right
    have h2 : H.relIndex S = 2 := by
      have : H.relIndex S ≠ 1 := by
        intro h
        rw [Subgroup.relIndex_eq_one] at h
        exact hyH (h hy)
      have : H.relIndex S ≠ 0 := relIndex_ne_zero'
      omega
    have hidx2 : (H.subgroupOf S).index = 2 := h2
    have hn1 : (⟨y, hy⟩ : S) ∉ H.subgroupOf S := hyH
    have hn2 : (⟨e, he⟩ : S) ∉ H.subgroupOf S := heH
    have hn1' : (⟨y, hy⟩ : S)⁻¹ ∉ H.subgroupOf S := fun h => hn1 ((H.subgroupOf S).inv_mem_iff.1 h)
    have := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨e, he⟩ : S))
      (b := (⟨y, hy⟩ : S)⁻¹)).2 (iff_of_false hn2 hn1')
    exact this

open QuaternionGroup in
theorem quat_invol {m : ℕ} [NeZero m] (x : QuaternionGroup m) (hx : x * x = 1) :
    x = 1 ∨ x = QuaternionGroup.a (m : ZMod (2 * m)) := by
  cases x with
  | a i =>
    rw [a_mul_a, one_def] at hx
    have h1 : i + i = 0 := by injection hx
    have h2 : (2 * i.val : ℕ) ≡ 0 [MOD 2 * m] := by
      have : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        have : (2 : ZMod (2 * m)) * i = i + i := by ring
        rw [this, h1]
      exact Nat.modEq_zero_iff_dvd.2 ((ZMod.natCast_eq_zero_iff _ _).1 this)
    have hdvd : m ∣ i.val :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num) (Nat.modEq_zero_iff_dvd.1 h2)
    have hlt : i.val < 2 * m := ZMod.val_lt i
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : m * 2 ≤ m * k := Nat.mul_le_mul_left m hk2
      have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      omega
    interval_cases k
    · left
      have h0 : i.val = 0 := by simpa using hk
      have : i = 0 := (ZMod.val_eq_zero i).1 h0
      rw [this, one_def]
    · right
      have hv : i.val = m := by simpa using hk
      have : i = (m : ZMod (2 * m)) :=
        calc i = (i.val : ZMod (2 * m)) := (ZMod.natCast_zmod_val i).symm
          _ = (m : ZMod (2 * m)) := by rw [hv]
      rw [this]
  | xa i =>
    exfalso
    rw [xa_mul_xa, one_def] at hx
    have h2 : ((m : ZMod (2 * m)) + i - i) = 0 := by injection hx
    have h3 : (m : ZMod (2 * m)) = 0 := by rwa [add_sub_cancel_right] at h2
    have h4 := (ZMod.natCast_eq_zero_iff m (2 * m)).1 h3
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have := Nat.le_of_dvd hm h4
    omega

theorem quat_sub_invol {P : Subgroup G} {m : ℕ} [NeZero m] (e : ↥P ≃* QuaternionGroup m) {z : G}
    (hz : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∀ p ∈ P, p * p = 1 → p = 1 ∨ p = z := by
  intro p hp hp2
  have hmul : ∀ w : ↥P, w * w = 1 → w = 1 ∨ w = e.symm (QuaternionGroup.a (m : ZMod (2 * m))) := by
    intro w hw
    have h1 : e w * e w = 1 := by rw [← map_mul, hw, map_one]
    rcases quat_invol (e w) h1 with h | h
    · left
      exact e.injective (by rw [h, map_one])
    · right
      exact e.injective (by rw [h]; simp)
  have hz' : (⟨z, hz⟩ : ↥P) = e.symm (QuaternionGroup.a (m : ZMod (2 * m))) := by
    rcases hmul ⟨z, hz⟩ (Subtype.ext (by simpa using hz2)) with h | h
    · exact absurd (congrArg Subtype.val h) hz1
    · exact h
  rcases hmul ⟨p, hp⟩ (Subtype.ext (by simpa using hp2)) with h | h
  · left
    exact congrArg Subtype.val h
  · right
    have : (⟨p, hp⟩ : ↥P) = ⟨z, hz⟩ := h.trans hz'.symm
    exact congrArg Subtype.val this

theorem nilpotencyClass_le_one_of_comm {A : Type*} [Group A] (hab : ∀ a b : A, a * b = b * a) :
    Group.nilpotencyClass A ≤ 1 := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hab }
  exact CommGroup.nilpotencyClass_le_one

theorem nilpotencyClass_le_of_card (p : ℕ) [hp : Fact p.Prime] :
    ∀ (m : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = p ^ m → IsPGroup p X →
      ¬ (∀ a b : X, a * b = b * a) → Group.nilpotencyClass X + 1 ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X _ _ hcard hX hnab
  have hnil : Group.IsNilpotent X := hX.isNilpotent
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    apply hnab
    interval_cases m
    · have : Subsingleton X := by
        rw [← Finite.card_le_one_iff_subsingleton]; simp [hcard]
      intro a b; exact Subsingleton.elim _ _
    · have hc : IsCyclic X := isCyclic_of_prime_card (p := p) (by simpa using hcard)
      intro a b
      exact (hc.isMulCommutative).is_comm.comm a b
    · intro a b
      exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm a b
  have hnt : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by omega) hp.out.one_lt
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hcard (by omega)
  have hkm : k ≤ m := by
    have h1 : Nat.card (Subgroup.center X) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
    rw [hk, hcard] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h1
  have hq : Nat.card (X ⧸ Subgroup.center X) = p ^ (m - k) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hk, hcard] at h1
    have h2 : p ^ m = p ^ (m - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hkm]
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos _) h1).symm
  have hqp : IsPGroup p (X ⧸ Subgroup.center X) := hX.to_quotient _
  have hcl := Group.nilpotencyClass_quotient_center (G := X)
  have hcpos : 1 ≤ Group.nilpotencyClass X := by
    by_contra h0
    push Not at h0
    have : Group.nilpotencyClass X = 0 := by omega
    have hs := (Group.nilpotencyClass_zero_iff_subsingleton).1 this
    exact hnab (fun a b => Subsingleton.elim _ _)
  by_cases hab : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a
  · have hle := nilpotencyClass_le_one_of_comm hab
    omega
  · have hlt : m - k < m := by omega
    have := ih (m - k) hlt (X ⧸ Subgroup.center X) hq hqp hab
    omega

theorem maxClass_of_lcs (X : Type) [Group X] [Finite X] (hX : IsPGroup 2 X)
    (hnab : ¬ IsMulCommutative X) (m : ℕ) (hm : Nat.card X = 2 ^ m)
    (hl : (⊤ : Subgroup X).lowerCentralSeries (m - 2) ≠ ⊥) :
    IsPGroup 2 X ∧ ¬ IsMulCommutative X ∧ ∃ _ : Group.IsNilpotent X,
      Nat.card X = 2 ^ (Group.nilpotencyClass X + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent X := hX.isNilpotent
  have hnab' : ¬ (∀ a b : X, a * b = b * a) := fun h => hnab ⟨⟨h⟩⟩
  have h1 := nilpotencyClass_le_of_card 2 m X hm hX hnab'
  have h2 : m - 1 ≤ Group.nilpotencyClass X := by
    by_contra hlt
    push Not at hlt
    apply hl
    have hle : (⊤ : Subgroup X).lowerCentralSeries (m - 2) ≤ (⊤ : Subgroup X).lowerCentralSeries
        (Group.nilpotencyClass X) :=
      Subgroup.lowerCentralSeries_antitone _ (by omega : Group.nilpotencyClass X ≤ m - 2)
    rw [Subgroup.lowerCentralSeries_nilpotencyClass] at hle
    exact le_bot_iff.1 hle
  refine ⟨hX, hnab, hnil, ?_⟩
  have : Group.nilpotencyClass X + 1 = m := by omega
  rw [this, hm]

theorem comm_of_forall_sq {E : Subgroup G} (hEx : ∀ a ∈ E, a * a = 1) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have h1 := hEx (a * b) (E.mul_mem ha hb)
  have h2 := hEx a ha
  have h3 := hEx b hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, ha', hb'] at hab'
  exact hab'.symm

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.B
