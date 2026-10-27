module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem card_le_of_isCyclic_of_pow_eq_one {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q]
    (S : Subgroup Q) (hS : ∀ x ∈ S, x ^ p = 1) : Nat.card S ≤ p := by
  have hp : p.Prime := Fact.out
  have : IsCyclic S := Subgroup.isCyclic S
  have hexp : Monoid.exponent S ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hS x x.2)
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp.pos hexp

theorem pRank_sup_le_two {T C : Subgroup X} (hTcard : Nat.card T = p ^ 3)
    (hTna : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a) (hC : IsCyclic C)
    (hCT : C ≤ Subgroup.centralizer (T : Set X)) (hΩ : ∀ c ∈ C, c ^ p = 1 → c ∈ T) :
    Open.pRank p (T ⊔ C) ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hCN : C ≤ Subgroup.normalizer (T : Set X) :=
    hCT.trans (Subgroup.centralizer_le_normalizer _)
  have hMN : T ⊔ C ≤ Subgroup.normalizer (T : Set X) := sup_le Subgroup.le_normalizer hCN
  have hdecomp : ∀ x ∈ T ⊔ C, ∃ t ∈ T, ∃ c ∈ C, t * c = x := by
    intro x hx
    have hx' : x ∈ ((T ⊔ C : Subgroup X) : Set X) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left T C hCN] at hx'
    obtain ⟨t, ht, c, hc, rfl⟩ := hx'
    exact ⟨t, ht, c, hc, rfl⟩
  refine csSup_le' fun k hk => ?_
  obtain ⟨E, hEM, hEel, hEcard⟩ := hk
  set M : Subgroup X := T ⊔ C
  have hNn : (T.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hMN
  let q : M →* M ⧸ T.subgroupOf M := QuotientGroup.mk' (T.subgroupOf M)
  have hqcyc : IsCyclic (M ⧸ T.subgroupOf M) := by
    let f : C →* M ⧸ T.subgroupOf M := q.comp (Subgroup.inclusion le_sup_right)
    refine isCyclic_of_surjective f fun y => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (T.subgroupOf M) y
    obtain ⟨t, ht, c, hc, htc⟩ := hdecomp m m.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show q (Subgroup.inclusion le_sup_right ⟨c, hc⟩) = q m
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_right ⟨c, hc⟩)⁻¹ * m : M) ∈ T.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    show c⁻¹ * (m : X) ∈ T
    have e : c⁻¹ * (m : X) = c⁻¹ * t * c := by rw [← htc, mul_assoc]
    rw [e]
    have hct : c⁻¹ * t * c = t := by
      have := Subgroup.mem_centralizer_iff.mp (hCT hc) t ht
      calc c⁻¹ * t * c = c⁻¹ * (t * c) := by rw [mul_assoc]
        _ = c⁻¹ * (c * t) := by rw [this]
        _ = t := by group
    rw [hct]
    exact ht
  let ψ : E →* M ⧸ T.subgroupOf M := q.comp (Subgroup.inclusion hEM)
  have hrange : Nat.card ψ.range ≤ p := by
    refine card_le_of_isCyclic_of_pow_eq_one ψ.range ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hEel.2 x x.2)
    rw [this, map_one]
  have hkerT : ∀ x : E, x ∈ ψ.ker → (x : X) ∈ T := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (Subgroup.inclusion hEM x : M) ∈ T.subgroupOf M :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact h1
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hEel.1) ⟨x, hx⟩ ⟨y, hy⟩)
  have hker_le : Nat.card ψ.ker ≤ p ^ 2 := by
    set A : Subgroup X := ψ.ker.map E.subtype
    have hAcard : Nat.card A = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective E.subtype_injective
    have hAT : A ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact hkerT x hx
    have hAp : IsPGroup p A := by
      refine IsPGroup.of_card (n := 3) ?_ |>.to_le hAT |> fun h => h
      exact hTcard
    obtain ⟨j, hj⟩ := hAp.exists_card_eq
    have hdvd : p ^ j ∣ p ^ 3 := by
      rw [← hj, ← hTcard]
      exact Subgroup.card_dvd_of_le hAT
    have hj3 : j ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
    by_contra hlt
    push Not at hlt
    have hj3' : j = 3 := by
      rw [← hAcard, hj] at hlt
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      omega
    have hAeq : A = T := Subgroup.eq_of_le_of_card_ge hAT (by rw [hj, hj3', hTcard])
    obtain ⟨a, ha, b, hb, hab⟩ := hTna
    apply hab
    rw [← hAeq] at ha hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    exact hEcomm _ x.2 _ y.2
  have hcardE : Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.index_ker ψ, Subgroup.card_mul_index]
  have hfinal : Nat.card E ≤ p ^ 2 := by
    by_cases hr1 : Nat.card ψ.range = 1
    · rw [hcardE, hr1, mul_one]
      exact hker_le
    by_cases hk1 : Nat.card ψ.ker ≤ p
    · rw [hcardE, pow_two]
      exact Nat.mul_le_mul hk1 hrange
    exfalso
    obtain ⟨y, hy1⟩ : ∃ y : ψ.range, y ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hr1
      exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [hall a, hall b]⟩, ⟨1⟩⟩
    obtain ⟨e, he⟩ := y.2
    have heT : (e : X) ∉ T := by
      intro heT
      apply hy1
      apply Subtype.ext
      rw [← he]
      show q (Subgroup.inclusion hEM e) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact heT
    obtain ⟨t, ht, c, hc, htc⟩ := hdecomp e (hEM e.2)
    have htcomm : ∀ f ∈ E, f ∈ T → t * f = f * t := by
      intro f hfE hfT
      have hcf : c * f = f * c := (Subgroup.mem_centralizer_iff.mp (hCT hc) f hfT).symm
      have hef : (e : X) * f = f * e := hEcomm _ e.2 _ hfE
      rw [← htc] at hef
      calc t * f = t * f * c * c⁻¹ := by group
        _ = t * (f * c) * c⁻¹ := by rw [mul_assoc t f c]
        _ = t * (c * f) * c⁻¹ := by rw [hcf]
        _ = (t * c) * f * c⁻¹ := by group
        _ = f * (t * c) * c⁻¹ := by rw [hef]
        _ = f * t := by group
    by_cases htE : t ∈ E
    ·
      have hcE : c ∈ E := by
        have e2 : c = t⁻¹ * e := by rw [← htc]; group
        rw [e2]
        exact E.mul_mem (E.inv_mem htE) e.2
      have hcT : c ∈ T := hΩ c hc (hEel.2 c hcE)
      exact heT (htc ▸ T.mul_mem ht hcT)
    ·
      set A : Subgroup X := ψ.ker.map E.subtype
      have hAcard : Nat.card A = Nat.card ψ.ker :=
        Subgroup.card_map_of_injective E.subtype_injective
      have hAT : A ≤ T := by
        rintro _ ⟨x, hx, rfl⟩
        exact hkerT x hx
      have hAE : A ≤ E := Subgroup.map_subtype_le _
      have hAp : IsPGroup p A := (IsPGroup.of_card (n := 3) hTcard).to_le hAT
      obtain ⟨j, hj⟩ := hAp.exists_card_eq
      have hj2 : j = 2 := by
        have h1 : p ^ j ≤ p ^ 2 := by rw [← hj, hAcard]; exact hker_le
        have h2 : p < p ^ j := by rw [← hj, hAcard]; omega
        have h1' := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
        have h2' : 1 < j :=
          (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rw [pow_one]; exact h2)
        omega
      set B : Subgroup X := A ⊔ Subgroup.zpowers t
      have hBT : B ≤ T := sup_le hAT (Subgroup.zpowers_le.mpr ht)
      have htA : t ∉ A := fun h => htE (hAE h)
      have hAB : A < B := lt_of_le_of_ne le_sup_left fun h =>
        htA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      have hBcard : Nat.card B = p ^ 3 := by
        have hBp : IsPGroup p B := (IsPGroup.of_card (n := 3) hTcard).to_le hBT
        obtain ⟨i, hi⟩ := hBp.exists_card_eq
        have hdvd : p ^ i ∣ p ^ 3 := by
          rw [← hi, ← hTcard]
          exact Subgroup.card_dvd_of_le hBT
        have hi3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
        have hlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt hAB
        rw [hj, hj2, hi] at hlt
        have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
        have : i = 3 := by omega
        rw [hi, this]
      have hBeq : B = T := Subgroup.eq_of_le_of_card_ge hBT (by rw [hBcard, hTcard])
      have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
        hEcomm x (hAE hx) y (hAE hy)
      have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
        have hgen : ∀ x ∈ (A : Set X) ∪ {t}, ∀ y ∈ (A : Set X) ∪ {t}, x * y = y * x := by
          rintro x (hx | hx) y (hy | hy)
          · exact hAcomm x hx y hy
          · rw [Set.mem_singleton_iff.mp hy]
            exact (htcomm x (hAE hx) (hAT hx)).symm
          · rw [Set.mem_singleton_iff.mp hx]
            exact htcomm y (hAE hy) (hAT hy)
          · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
        have hBcl : B = Subgroup.closure ((A : Set X) ∪ {t}) := by
          rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
        intro x hx y hy
        rw [hBcl] at hx hy
        have hc := Subgroup.isMulCommutative_closure (k := (A : Set X) ∪ {t})
          (fun a ha b hb _ => hgen a ha b hb)
        exact congrArg Subtype.val ((isMulCommutative_iff.mp hc) ⟨x, hx⟩ ⟨y, hy⟩)
      obtain ⟨a, ha, b, hb, hab⟩ := hTna
      rw [← hBeq] at ha hb
      exact hab (hBcomm a ha b hb)
  rw [hEcard] at hfinal
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hfinal

@[expose] def S2Lemma : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime] (T C : Subgroup X),
    Nat.card T = p ^ 3 → (∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a) → IsCyclic C →
    C ≤ Subgroup.centralizer (T : Set X) → (∀ c ∈ C, c ^ p = 1 → c ∈ T) →
    Open.pRank p (T ⊔ C) ≤ 2

theorem s2Lemma : S2Lemma := fun _ _ _ _ _ _ _ h1 h2 h3 h4 h5 => pRank_sup_le_two h1 h2 h3 h4 h5

end CFSG.AGLEmbedding
