module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FourthPower
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeFixedPoints
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CharacteristicQuotientActions

public section

namespace CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Finite G]

@[expose] def centralFixed (S : Subgroup G) {P : Type*} [Group P] (φ : S →* MulAut P) :
    Subgroup P where
  carrier := {x | ∀ e ∈ Subgroup.center S, φ e x = x}
  mul_mem' := fun {a b} ha hb e he => by rw [map_mul, ha e he, hb e he]
  one_mem' := fun e _ => map_one _
  inv_mem' := fun {a} ha e he => by rw [map_inv, ha e he]

omit [Finite G] in
theorem mem_centralFixed {S : Subgroup G} {P : Type*} [Group P] {φ : S →* MulAut P} {x : P} :
    x ∈ centralFixed S φ ↔ ∀ e ∈ Subgroup.center S, φ e x = x := Iff.rfl

theorem card_eq_card_centralFixed_mul_pow_of_module {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (φV : (S : Subgroup G) →* AddMonoid.End V) :
    ∃ m : ℕ, Nat.card V = Nat.card {v : V // ∀ e ∈ Subgroup.center (S : Subgroup G),
      φV e v = v} * p ^ (4 * m) := by
  classical
  let ρ : (S : Subgroup G) →* Module.End (ZMod p) V :=
    { toFun := fun g => (φV g).toZModLinearMap p
      map_one' := by
        refine LinearMap.ext fun x => ?_
        show φV 1 x = x
        rw [map_one]; rfl
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        show φV (g * h) x = φV g (φV h x)
        rw [map_mul]; rfl }
  have hρ : ∀ g (x : V), ρ g x = φV g x := fun g x => rfl
  have hk : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨m, hm⟩ := (unitary_four_cross_characteristic_central_codimension hT S U hSU hk ρ).2
  set W := (⨅ e : Subgroup.center (S : Subgroup G),
    LinearMap.ker (ρ (e : (S : Subgroup G)) - 1) : Submodule (ZMod p) V) with hWdef
  have hmemW : ∀ x : V, x ∈ W ↔ ∀ e ∈ Subgroup.center (S : Subgroup G), φV e x = x := by
    intro x
    rw [hWdef, Submodule.mem_iInf]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hρ]
    exact ⟨fun h e he => h ⟨e, he⟩, fun h e => h e e.2⟩
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hcardW : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hle : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) V := Submodule.finrank_le W
  have hWF : Nat.card W = Nat.card {v : V // ∀ e ∈ Subgroup.center (S : Subgroup G),
      φV e v = v} :=
    Nat.card_congr
      { toFun := fun w => ⟨w, (hmemW w).mp w.2⟩
        invFun := fun v => ⟨v, (hmemW v).mpr v.2⟩
        left_inv := fun w => rfl
        right_inv := fun v => rfl }
  refine ⟨m, ?_⟩
  rw [hcardV, ← hWF, hcardW, ← pow_add]
  congr 1
  omega

theorem card_eq_card_centralFixed_inf_mul_pow {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Type} [Group P] [Finite P]
    (φ : (S : Subgroup G) →* MulAut P) (A : Subgroup P) (hAc : A ≤ Subgroup.center P)
    (hAexp : ∀ a ∈ A, a ^ p = 1) (hAinv : ∀ g, ∀ a ∈ A, φ g a ∈ A) :
    ∃ m : ℕ, Nat.card A = Nat.card (centralFixed (S : Subgroup G) φ ⊓ A : Subgroup P) *
      p ^ (4 * m) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hAc b.2) a) }
  let _ : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hAexp _ (Additive.toMul x).2))
  let ψ : ↥(S : Subgroup G) → A →* A := fun g =>
    { toFun := fun a => ⟨φ g a, hAinv g a a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  let φV : (S : Subgroup G) →* AddMonoid.End (Additive A) :=
    { toFun := fun g => MonoidHom.toAdditive (ψ g)
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        show φ 1 ((Additive.toMul x : A) : P) = ((Additive.toMul x : A) : P)
        rw [map_one]; rfl
      map_mul' := fun g h => by
        refine AddMonoidHom.ext fun x => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        show φ (g * h) ((Additive.toMul x : A) : P) = φ g (φ h ((Additive.toMul x : A) : P))
        rw [map_mul]; rfl }
  obtain ⟨m, hm⟩ := card_eq_card_centralFixed_mul_pow_of_module hT S U hSU hp2 φV
  refine ⟨m, ?_⟩
  rw [Nat.card_congr Additive.toMul.symm, hm]
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun v => ⟨((Additive.toMul v.1 : A) : P), ⟨fun e he => by
          have := congrArg (fun y : Additive A => ((Additive.toMul y : A) : P)) (v.2 e he)
          exact this, (Additive.toMul v.1).2⟩⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x, x.2.2⟩, fun e he => by
          apply Additive.toMul.injective; apply Subtype.ext; exact x.2.1 e he⟩
      left_inv := fun v => rfl
      right_inv := fun x => rfl }

omit [Finite G] in
theorem card_subgroupOf_eq_card_inf {P : Type*} [Group P] (H K : Subgroup P) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup P) := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]

theorem unitary_four_coprime_centralizer_index_fourth_power {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Type} [Group P] [Finite P] (hP : IsPGroup p P)
    (φ : (S : Subgroup G) →* MulAut P) :
    ∃ m : ℕ, (centralFixed (S : Subgroup G) φ).index = p ^ (4 * m) ∧
      (centralFixed (S : Subgroup G) φ ≠ ⊤ →
        p ^ 4 ∣ (centralFixed (S : Subgroup G) φ).index) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  suffices H : ∀ n : ℕ, ∀ (P : Type) [Group P] [Finite P], Nat.card P = n → IsPGroup p P →
      ∀ φ : (S : Subgroup G) →* MulAut P,
        ∃ m : ℕ, (centralFixed (S : Subgroup G) φ).index = p ^ (4 * m) by
    obtain ⟨m, hm⟩ := H _ P rfl hP φ
    refine ⟨m, hm, fun hne => ?_⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, pow_zero, Subgroup.index_eq_one] at hm
      exact hne hm
    rw [hm]
    exact pow_dvd_pow p (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hcard hP φ
  by_cases htriv : Nat.card P = 1
  · refine ⟨0, ?_⟩
    rw [mul_zero, pow_zero, Subgroup.index_eq_one]
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp htriv).1
    rw [eq_top_iff]
    intro x _ e _
    exact Subsingleton.elim _ _
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.card_pos (α := P)
    omega
  let A : Subgroup P :=
    { carrier := {z | z ∈ Subgroup.center P ∧ z ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [(show Commute a b from Subgroup.mem_center_iff.mp hb.1 a).mul_pow, ha.2, hb.2,
          one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hAc : A ≤ Subgroup.center P := fun z hz => hz.1
  have hAexp : ∀ a ∈ A, a ^ p = 1 := fun a ha => ha.2
  have hAinv : ∀ σ : MulAut P, ∀ a ∈ A, σ a ∈ A := by
    intro σ a ha
    refine ⟨?_, by rw [← map_pow, ha.2, map_one]⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha.1 g']
  have hAnt : ∃ a ∈ A, a ≠ 1 := by
    have hZnt : Nontrivial (Subgroup.center P) := hP.center_nontrivial
    have hZp : p ∣ Nat.card (Subgroup.center P) := by
      rcases (hP.to_subgroup (Subgroup.center P)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card).ne'
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) p hZp
    refine ⟨(z : P), ⟨z.2, ?_⟩, ?_⟩
    · rw [← Subgroup.orderOf_coe] at hz
      rw [← hz]; exact pow_orderOf_eq_one _
    · intro h
      have : z = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz
      exact hp.one_lt.ne hz
  have hAnormal : A.Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_center_iff.mp (hAc ha) g, mul_inv_cancel_right]; exact ha⟩
  have hAchar : A.Characteristic := by
    refine ⟨fun σ => le_antisymm ?_ ?_⟩
    · intro a ha
      have := hAinv σ.symm _ ha
      simpa using this
    · intro a ha
      exact hAinv σ a ha
  let Q := P ⧸ A
  let φQ : (S : Subgroup G) →* MulAut Q :=
    (CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction A).comp φ
  have hφQ : ∀ g (x : P), φQ g (QuotientGroup.mk x) = QuotientGroup.mk (φ g x) := by
    intro g x
    exact CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction_apply A (φ g) x
  have hcardQ : Nat.card Q < n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    obtain ⟨a, haA, ha1⟩ := hAnt
    have h2 : 1 < Nat.card A := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨a, haA⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    have h3 : 0 < Nat.card Q := Nat.card_pos
    rw [← hcard]
    calc Nat.card Q = Nat.card Q * 1 := (mul_one _).symm
      _ < Nat.card Q * Nat.card A := Nat.mul_lt_mul_of_pos_left h2 h3
      _ = Nat.card P := h1.symm
  obtain ⟨m₁, hm₁⟩ := ih _ hcardQ Q rfl (hP.to_quotient A) φQ
  set F := centralFixed (S : Subgroup G) φ with hF
  have hodd : ¬ 2 ∣ Nat.card P := by
    intro h2
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hFQ : centralFixed (S : Subgroup G) φQ = F.map (QuotientGroup.mk' A) := by
    apply le_antisymm
    · intro y hy
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hxy, hx⟩ := CFSG.LargeEvenClassification.Helpers.coprime_fixed_point_lift
        Nat.prime_two (S.isPGroup'.to_subgroup (Subgroup.center (S : Subgroup G)))
        (φ.comp (Subgroup.center (S : Subgroup G)).subtype)
        (φQ.comp (Subgroup.center (S : Subgroup G)).subtype)
        (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
        (fun e x => (hφQ e x).symm) hodd y (fun e => hy e e.2)
      exact ⟨x, fun e he => hx ⟨e, he⟩, hxy⟩
    · rintro _ ⟨x, hx, rfl⟩ e he
      change φQ e (QuotientGroup.mk x) = QuotientGroup.mk x
      rw [hφQ, hx e he]
  have hidxQ : (centralFixed (S : Subgroup G) φQ).index = (F ⊔ A).index := by
    rw [hFQ, Subgroup.index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective A), Subgroup.index_top, mul_one]
  obtain ⟨m₂, hm₂⟩ := card_eq_card_centralFixed_inf_mul_pow hT S U hSU hp hp2 φ A hAc hAexp
    (fun g a ha => hAinv (φ g) a ha)
  have hsup := Subgroup.relIndex_sup_right F A
  have hcA := Subgroup.card_mul_index (A.subgroupOf (F ⊔ A))
  have hcF := Subgroup.card_mul_index (A.subgroupOf F)
  rw [card_subgroupOf_eq_card_inf, inf_of_le_left le_sup_right] at hcA
  rw [card_subgroupOf_eq_card_inf] at hcF
  have hrel : A.relIndex (F ⊔ A) = A.relIndex F := hsup
  unfold Subgroup.relIndex at hrel
  have hPF := Subgroup.card_mul_index F
  have hPFA := Subgroup.card_mul_index (F ⊔ A)
  rw [hidxQ] at hm₁
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have key : Nat.card F * F.index = Nat.card F * (p ^ (4 * m₁) * p ^ (4 * m₂)) := by
    rw [hPF, ← hPFA, hm₁, ← hcA, hrel, hm₂, inf_comm, ← hcF]
    ring
  refine ⟨m₁ + m₂, ?_⟩
  rw [Nat.eq_of_mul_eq_mul_left hFpos key, ← pow_add]
  ring_nf

end CFSG.LyonsUnitaryFour
