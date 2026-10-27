module

public import CFSG.RankThree.Transfer.FixedPoints

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup MulAction CFSG.RankThree.Transfer

section Generic

variable {P α A : Type*} [Group P] [MulAction P α]

theorem card_fiber_modEq [Finite α] (hP : IsPGroup 2 P) (F : α → A)
    (hinv : ∀ (p : P) (x : α), F (p • x) = F x) (a : A) :
    Nat.card {x : α // F x = a} ≡ Nat.card {x : fixedPoints P α // F x = a} [MOD 2] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : SubMulAction P α :=
    { carrier := {x | F x = a}
      smul_mem' := fun p x hx => by simpa [hinv] using hx }
  have h := hP.card_modEq_card_fixedPoints ↥S
  have e1 : Nat.card ↥S = Nat.card {x : α // F x = a} := rfl
  have e2 : Nat.card (fixedPoints P ↥S) = Nat.card {x : fixedPoints P α // F x = a} := by
    refine Nat.card_congr
      { toFun := fun s => ⟨⟨s.1.1, fun p => congrArg Subtype.val (s.2 p)⟩, s.1.2⟩
        invFun := fun s => ⟨⟨s.1.1, s.2⟩, fun p => Subtype.ext (s.1.2 p)⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
  rw [e1, e2] at h
  exact h

variable [CommGroup A]

theorem prod_eq_prod_fixedPoints [Finite α] [Fintype α] [Fintype A] [DecidableEq A]
    [Fintype (fixedPoints P α)] (hP : IsPGroup 2 P) (F : α → A)
    (hinv : ∀ (p : P) (x : α), F (p • x) = F x) (hsq : ∀ x, F x * F x = 1) :
    ∏ x : α, F x = ∏ x : fixedPoints P α, F x := by
  classical
  have hfib : ∀ {β : Type _} [Fintype β] (G : β → A), ∏ x : β, G x =
      ∏ a : A, a ^ Nat.card {x : β // G x = a} := by
    intro β _ G
    rw [← Finset.prod_fiberwise Finset.univ G G]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_congr rfl (fun x hx => (Finset.mem_filter.1 hx).2), Finset.prod_const,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hfib F, hfib (fun x : fixedPoints P α => F x)]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hm := card_fiber_modEq hP F hinv a
  by_cases ha : ∃ x, F x = a
  · obtain ⟨x, rfl⟩ := ha
    have h2 : F x ^ 2 = 1 := by rw [sq]; exact hsq x
    rw [pow_eq_pow_mod _ h2, pow_eq_pow_mod (Nat.card {y : fixedPoints P α // F y = F x}) h2]
    congr 1
  · push Not at ha
    have h1 : Nat.card {x : α // F x = a} = 0 := by
      rw [Nat.card_eq_zero]; exact Or.inl ⟨fun x => ha x.1 x.2⟩
    have h2 : Nat.card {x : fixedPoints P α // F x = a} = 0 := by
      rw [Nat.card_eq_zero]; exact Or.inl ⟨fun x => ha x.1 x.2⟩
    rw [h1, h2]

end Generic

section Transfer

variable {G : Type} [Group G]

theorem hom_eq_one_of_simple {A : Type*} [CommGroup A] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (f : G →* A) : f = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h
    apply hab
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  · ext g
    have : g ∈ f.ker := h ▸ Subgroup.mem_top g
    simpa using this

variable [Finite G] {t : G} {K : Subgroup G}

theorem prod_fixed_cosets_eq_one [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht : t * t = 1) {A : Type*} [CommGroup A] (ψ : K →* A) [Fintype (G ⧸ K)]
    [DecidableEq (G ⧸ K)] :
    ∏ X : G ⧸ K, (if t • X = X then cosetValue ψ t X else 1) = 1 := by
  have h1 : ψ.transfer t = 1 := by rw [hom_eq_one_of_simple hnonab ψ.transfer]; rfl
  have h2 : ψ.transfer t = ∏ X : G ⧸ K, (if t • X = X then cosetValue ψ t X else 1) := by
    refine transfer_eq_prod_fixed_of_orderOf_lt ψ t ?_
    intro h hlt
    have h2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht)
    have h3 : orderOf (h : G) = 1 := by
      have := orderOf_pos (h : G)
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have h4 : (h : G) = 1 := orderOf_eq_one_iff.1 h3
    have h5 : h = 1 := Subtype.ext h4
    rw [h5, map_one]
  rw [← h2]
  exact h1

omit [Finite G] in
theorem fixedIf_smul {A : Type*} [CommGroup A] (ψ : K →* A) [DecidableEq (G ⧸ K)] {P : Subgroup G}
    (hPt : ∀ p ∈ P, p * t = t * p) (p : P) (X : G ⧸ K) :
    (if t • (p • X) = p • X then cosetValue ψ t (p • X) else 1) =
      (if t • X = X then cosetValue ψ t X else 1) := by
  induction X using QuotientGroup.induction_on with
  | H x =>
    have hp : (p : G) * t = t * p := hPt p p.2
    have hsm : p • (x : G ⧸ K) = (((p : G) * x : G) : G ⧸ K) := rfl
    have hconj : ((p : G) * x)⁻¹ * t * ((p : G) * x) = x⁻¹ * t * x := by
      have : t * (p : G) = (p : G) * t := hp.symm
      calc ((p : G) * x)⁻¹ * t * ((p : G) * x) = x⁻¹ * ((p : G)⁻¹ * (t * (p : G))) * x := by group
        _ = x⁻¹ * ((p : G)⁻¹ * ((p : G) * t)) * x := by rw [this]
        _ = x⁻¹ * t * x := by group
    rw [hsm]
    by_cases hx : x⁻¹ * t * x ∈ K
    · have hx' : ((p : G) * x)⁻¹ * t * ((p : G) * x) ∈ K := by rw [hconj]; exact hx
      have e1 : t • (((p : G) * x : G) : G ⧸ K) = (((p : G) * x : G) : G ⧸ K) :=
        smul_coe_eq_iff.2 hx'
      have e2 : t • (x : G ⧸ K) = x := smul_coe_eq_iff.2 hx
      simp only [e1, e2, ↓reduceIte, cosetValue_coe ψ hx', cosetValue_coe ψ hx]
      exact congrArg ψ (Subtype.ext hconj)
    · have hx' : ¬ ((p : G) * x)⁻¹ * t * ((p : G) * x) ∈ K := by rw [hconj]; exact hx
      have e1 : ¬ t • (((p : G) * x : G) : G ⧸ K) = (((p : G) * x : G) : G ⧸ K) :=
        fun h => hx' (smul_coe_eq_iff.1 h)
      have e2 : ¬ t • (x : G ⧸ K) = x := fun h => hx (smul_coe_eq_iff.1 h)
      simp only [e1, e2, ↓reduceIte]

omit [Finite G] in
theorem coe_mem_fixedPoints_iff {P : Subgroup G} (x : G) :
    (x : G ⧸ K) ∈ fixedPoints P (G ⧸ K) ↔ ∀ p ∈ P, x⁻¹ * p * x ∈ K := by
  rw [mem_fixedPoints]
  constructor
  · intro h p hp
    exact smul_coe_eq_iff.1 (h ⟨p, hp⟩)
  · intro h p
    exact smul_coe_eq_iff.2 (h p p.2)

theorem prod_fixedPoints_eq_one [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht : t * t = 1) {P : Subgroup G} (hP : IsPGroup 2 P) (htP : t ∈ P)
    (hPt : ∀ p ∈ P, p * t = t * p) {A : Type*} [CommGroup A] [Finite A] (ψ : K →* A)
    [Fintype (fixedPoints P (G ⧸ K))] :
    ∏ X : fixedPoints P (G ⧸ K), cosetValue ψ t X = 1 := by
  classical
  have : Fintype (G ⧸ K) := Fintype.ofFinite _
  have : Fintype A := Fintype.ofFinite _
  have : DecidableEq (G ⧸ K) := Classical.decEq _
  have hF := prod_eq_prod_fixedPoints (P := P) (α := G ⧸ K) hP
    (fun X => if t • X = X then cosetValue ψ t X else 1) (fixedIf_smul ψ hPt) (by
      intro X
      split_ifs with hX
      · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
        have hx : x⁻¹ * t * x ∈ K := smul_coe_eq_iff.1 hX
        rw [cosetValue_coe ψ hx, ← map_mul]
        have : (⟨x⁻¹ * t * x, hx⟩ : K) * ⟨x⁻¹ * t * x, hx⟩ = 1 := by
          apply Subtype.ext
          show (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1
          calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
            _ = 1 := by rw [ht]; group
        rw [this, map_one]
      · exact one_mul 1)
  rw [prod_fixed_cosets_eq_one hnonab ht ψ] at hF
  have hfix : ∀ X : fixedPoints P (G ⧸ K), t • (X : G ⧸ K) = X := fun X => X.2 ⟨t, htP⟩
  calc ∏ X : fixedPoints P (G ⧸ K), cosetValue ψ t X
      = ∏ X : fixedPoints P (G ⧸ K),
          (if t • (X : G ⧸ K) = X then cosetValue ψ t X else 1) :=
        Finset.prod_congr rfl fun X _ => by simp [hfix X]
    _ = 1 := hF.symm

theorem exists_conj_ne_centralizing [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht : t * t = 1) {P : Subgroup G} (hP : IsPGroup 2 P) (htP : t ∈ P)
    (hPt : ∀ p ∈ P, p * t = t * p) {A : Type*} [CommGroup A] [Finite A]
    (ψ : centralizer ({t} : Set G) →* A)
    (hψ : ψ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ ∀ p ∈ P, p * (g * t * g⁻¹) = (g * t * g⁻¹) * p := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype (fixedPoints P (G ⧸ centralizer ({t} : Set G))) := Fintype.ofFinite _
  have h1 := prod_fixedPoints_eq_one (K := centralizer ({t} : Set G)) hnonab ht hP htP hPt ψ
  have hmemM : ∀ p ∈ P, p ∈ centralizer ({t} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.2 (hPt p hp)
  have hone : ((1 : G) : G ⧸ centralizer ({t} : Set G)) ∈
      fixedPoints P (G ⧸ centralizer ({t} : Set G)) := by
    rw [coe_mem_fixedPoints_iff]
    intro p hp
    simpa using hmemM p hp
  have hall : ∀ X : fixedPoints P (G ⧸ centralizer ({t} : Set G)), X = ⟨_, hone⟩ := by
    rintro ⟨X, hX⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
    rw [coe_mem_fixedPoints_iff] at hX
    have hxt : x * t * x⁻¹ = t := by
      by_contra hne
      obtain ⟨p, hp, hpne⟩ := hcon x hne
      apply hpne
      have h := mem_centralizer_singleton_iff.1 (hX p hp)
      calc p * (x * t * x⁻¹) = x * ((x⁻¹ * p * x) * t) * x⁻¹ := by group
        _ = x * (t * (x⁻¹ * p * x)) * x⁻¹ := by rw [h]
        _ = (x * t * x⁻¹) * p := by group
    have hxM : x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [hxt]
    apply Subtype.ext
    show (x : G ⧸ centralizer ({t} : Set G)) = ((1 : G) : G ⧸ centralizer ({t} : Set G))
    rw [QuotientGroup.eq]
    simpa using inv_mem hxM
  rw [Fintype.prod_eq_single (⟨_, hone⟩ : fixedPoints P (G ⧸ centralizer ({t} : Set G)))
    (fun X hX => absurd (hall X) hX)] at h1
  have ht1 : (1 : G)⁻¹ * t * 1 ∈ centralizer ({t} : Set G) := by simpa using hmemM t htP
  have h2 := cosetValue_coe ψ ht1
  apply hψ
  rw [← h1]
  show ψ ⟨t, _⟩ = cosetValue ψ t (((1 : G) : G ⧸ centralizer ({t} : Set G)))
  rw [h2]
  congr 1
  exact Subtype.ext (by simp)

theorem even_card_ne_one_of_prod_eq_one {β : Type*} [Fintype β]
    (g : β → Multiplicative (ZMod 2)) (h : ∏ x, g x = 1) : Even (Nat.card {x // g x ≠ 1}) := by
  classical
  set ζ : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1 with hζ
  have hg : ∀ x, g x ≠ 1 → g x = ζ := by
    intro x hx
    have hall : ∀ a : Multiplicative (ZMod 2), a ≠ 1 → a = ζ := by decide
    exact hall _ hx
  have h1 : ∏ x, g x = ζ ^ Nat.card {x // g x ≠ 1} := by
    rw [← Finset.prod_filter_ne_one, Finset.prod_congr rfl
      (fun x hx => hg x (Finset.mem_filter.1 hx).2), Finset.prod_const, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [h1] at h
  have h2 : ((Nat.card {x // g x ≠ 1} : ℕ) : ZMod 2) = 0 := by
    have : Multiplicative.ofAdd ((Nat.card {x // g x ≠ 1} : ℕ) • (1 : ZMod 2)) = 1 := by
      rw [ofAdd_nsmul]; exact h
    have h3 := congrArg Multiplicative.toAdd this
    simpa using h3
  exact even_iff_two_dvd.2 ((ZMod.natCast_eq_zero_iff _ 2).1 h2)

theorem even_card_fixed_ne_one [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht : t * t = 1) {P : Subgroup G} (hP : IsPGroup 2 P) (htP : t ∈ P)
    (hPt : ∀ p ∈ P, p * t = t * p) (φ : K →* Multiplicative (ZMod 2))
    [Fintype (fixedPoints P (G ⧸ K))] :
    Even (Nat.card {X : fixedPoints P (G ⧸ K) // cosetValue φ t X ≠ 1}) :=
  even_card_ne_one_of_prod_eq_one _ (prod_fixedPoints_eq_one hnonab ht hP htP hPt φ)

end Transfer

end CFSG.EvenSporadicStandard.McLStd
