module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
open scoped commutatorElement

theorem not_sq_dvd_card_of_quasisimple {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) {J : Subgroup Y} (hJ : PerfectSectionsAltSqC p J) {X : Subgroup Y}
    (hXJ : X ≤ J) (hX : CFSG.Open.IsQuasisimple ↥X) : ¬ p ^ 2 ∣ Nat.card X := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  exact not_sq_dvd_card_of_quasisimple_of_altSqC hp hJ hXJ hX

theorem exists_hom_alternating_of_hom_prod {X : Type*} [Group X] {p : ℕ}
    (hX : CFSG.Open.IsQuasisimple X) (f : X →* alternatingGroup (Fin p) × alternatingGroup (Fin p))
    (hf : f.ker ≤ Subgroup.center X) :
    ∃ φ : X →* alternatingGroup (Fin p), φ.ker ≤ Subgroup.center X := by
  set g₁ := (MonoidHom.fst _ _).comp f
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX g₁.ker with h | h
  · exact ⟨g₁, h⟩
  · refine ⟨(MonoidHom.snd _ _).comp f, fun x hx => hf ?_⟩
    have h1 : (f x).1 = 1 := by
      have : x ∈ g₁.ker := h ▸ Subgroup.mem_top x
      exact this
    exact Prod.ext h1 hx

theorem eq_one_of_mem_center_of_pow_eq_one {R : Type*} [Group R] [Finite R] {p : ℕ}
    (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center R)) {a : R}
    (ha : a ∈ Subgroup.center R) (hap : a ^ p = 1) : a = 1 := by
  set z : Subgroup.center R := ⟨a, ha⟩
  have hz : z ^ p = 1 := Subtype.ext hap
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hz) with h | h
  · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h)
  · exact absurd (h ▸ orderOf_dvd_natCard z) hZ

theorem mem_center_of_mul_mem_normal {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {A : Subgroup G} (hA : CFSG.Open.IsQuasisimple ↥A) (hAN : ¬ A ≤ N) {a g : G} (ha : a ∈ A)
    (hg : ∀ a' ∈ A, a' * g = g * a') (hag : a * g ∈ N) :
    (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
  have hNc : N.comap A.subtype ≤ Subgroup.center ↥A := by
    rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hA
      (N.comap A.subtype) with h | h
    · exact h
    · exact absurd (fun x hx => (show (⟨x, hx⟩ : ↥A) ∈ N.comap A.subtype from h ▸ trivial))
        hAN
  have hcomm : ∀ w : ↥A, ⁅w, (⟨a, ha⟩ : ↥A)⁆ ∈ Subgroup.center ↥A := by
    intro w
    apply hNc
    show (w : G) * a * (w : G)⁻¹ * a⁻¹ ∈ N
    have h1 : (w : G) * (a * g) * (w : G)⁻¹ * (a * g)⁻¹ ∈ N :=
      N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hag _) (N.inv_mem hag)
    have hg' : g * (w : G)⁻¹ = (w : G)⁻¹ * g := by
      have := hg _ (A.inv_mem w.2)
      exact this.symm
    have h2 : (w : G) * (a * g) * (w : G)⁻¹ * (a * g)⁻¹ = (w : G) * a * (w : G)⁻¹ * a⁻¹ := by
      calc (w : G) * (a * g) * (w : G)⁻¹ * (a * g)⁻¹
          = (w : G) * a * (g * (w : G)⁻¹) * g⁻¹ * a⁻¹ := by group
        _ = (w : G) * a * ((w : G)⁻¹ * g) * g⁻¹ * a⁻¹ := by rw [hg']
        _ = (w : G) * a * (w : G)⁻¹ * a⁻¹ := by group
    rwa [h2] at h1
  have hperf : Group.IsPerfect ↥A := ⟨hA.1⟩
  have hc := ComponentClassification.Quasisimple.center_comap_of_central_kernel
    (QuotientGroup.mk' (Subgroup.center ↥A)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rw [← hc, Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥A) y
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem]
  simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using hcomm w


theorem le_normal_of_commuting_quasisimple {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {N : Subgroup G} [N.Normal] (hN : ¬ p ^ 2 ∣ N.index) {A B : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple ↥A) (hB : CFSG.Open.IsQuasisimple ↥B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hpA : p ∣ Nat.card A) (hpB : p ∣ Nat.card B)
    (hA2 : ¬ p ^ 2 ∣ Nat.card A) (hB2 : ¬ p ^ 2 ∣ Nat.card B) : A ≤ N ∨ B ≤ N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAN, hBN⟩ := hcon
  have : Fact p.Prime := ⟨hp⟩
  have hZA : ¬ p ∣ Nat.card (Subgroup.center ↥A) := not_dvd_card_center_of_perfect hA.1 hA2
  have hZB : ¬ p ∣ Nat.card (Subgroup.center ↥B) := not_dvd_card_center_of_perfect hB.1 hB2
  let ψ : ↥A × ↥B →* G ⧸ N := (QuotientGroup.mk' N).comp
    (MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hAB a a.2 b b.2))
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) p hd
    have hk1 : ψ (k : ↥A × ↥B) = 1 := k.2
    have hmem : ((k : ↥A × ↥B).1 : G) * ((k : ↥A × ↥B).2 : G) ∈ N := by
      have : QuotientGroup.mk' N (((k : ↥A × ↥B).1 : G) * ((k : ↥A × ↥B).2 : G)) = 1 := hk1
      exact (QuotientGroup.eq_one_iff _).1 this
    have hpow : (k : ↥A × ↥B) ^ p = 1 := by
      have := pow_orderOf_eq_one k
      rw [hk] at this
      exact congrArg Subtype.val this
    have hp1 : (k : ↥A × ↥B).1 ^ p = 1 := by
      simpa using congrArg Prod.fst hpow
    have hp2 : (k : ↥A × ↥B).2 ^ p = 1 := by
      simpa using congrArg Prod.snd hpow
    have h1 : (k : ↥A × ↥B).1 ∈ Subgroup.center ↥A :=
      mem_center_of_mul_mem_normal hA hAN (k : ↥A × ↥B).1.2 (g := ((k : ↥A × ↥B).2 : G))
        (fun a' ha' => hAB a' ha' _ (k : ↥A × ↥B).2.2) hmem
    have h2 : (k : ↥A × ↥B).2 ∈ Subgroup.center ↥B :=
      mem_center_of_mul_mem_normal hB hBN (k : ↥A × ↥B).2.2 (g := ((k : ↥A × ↥B).1 : G))
        (fun b' hb' => (hAB _ (k : ↥A × ↥B).1.2 b' hb').symm)
        (by rwa [← hAB _ (k : ↥A × ↥B).1.2 _ (k : ↥A × ↥B).2.2])
    have e1 : (k : ↥A × ↥B).1 = 1 :=
      eq_one_of_mem_center_of_pow_eq_one hp hZA h1 hp1
    have e2 : (k : ↥A × ↥B).2 = 1 :=
      eq_one_of_mem_center_of_pow_eq_one hp hZB h2 hp2
    have hk0 : k = 1 := Subtype.ext (Prod.ext e1 e2)
    rw [hk0, orderOf_one] at hk
    exact hp.one_lt.ne hk
  have hdvd : p ^ 2 ∣ Nat.card (↥A × ↥B) := by
    rw [Nat.card_prod, sq]
    exact mul_dvd_mul hpA hpB
  have hrange : p ^ 2 ∣ Nat.card ψ.range := by
    rw [← Subgroup.card_ker_mul_card_range ψ] at hdvd
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hker)) hdvd
  exact hN (hrange.trans (by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _))

theorem exists_hom_alternating_of_le_normal {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    {V X : Subgroup Y} (hXV : X ≤ V) (hX : CFSG.Open.IsQuasisimple ↥X) (hp : p.Prime)
    (hpX : p ∣ Nat.card X) {N : Subgroup ↥V}
    (hXN : ∀ x (hx : x ∈ X), (⟨x, hXV hx⟩ : ↥V) ∈ N)
    {f : ↥V →* alternatingGroup (Fin p) × alternatingGroup (Fin p)}
    (hf : p.Coprime (Nat.card ↥(f.ker ⊓ N))) :
    ∃ φ : ↥X →* alternatingGroup (Fin p), φ.ker ≤ Subgroup.center ↥X := by
  set f' := f.comp (Subgroup.inclusion hXV)
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX f'.ker with h | h
  · exact exists_hom_alternating_of_hom_prod hX f' h
  · exfalso
    have hle : X.subgroupOf V ≤ f.ker ⊓ N := by
      intro v hv
      refine ⟨?_, hXN v.1 hv⟩
      have : (⟨v.1, hv⟩ : ↥X) ∈ f'.ker := h ▸ Subgroup.mem_top _
      exact this
    have h1 : Nat.card (X.subgroupOf V) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXV).toEquiv
    have h2 := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) hf
    rw [h1] at h2
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h2 hpX)

theorem exists_hom_alternating_of_commuting {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) {J : Subgroup Y} (hJ : PerfectSectionsAltSqC p J)
    {X₁ X₂ : Subgroup Y} (h₁ : X₁ ≤ J) (h₂ : X₂ ≤ J)
    (hq₁ : CFSG.Open.IsQuasisimple ↥X₁) (hq₂ : CFSG.Open.IsQuasisimple ↥X₂)
    (hc : X₂ ≤ Subgroup.centralizer (X₁ : Set Y))
    (hp₁ : p ∣ Nat.card X₁) (hp₂ : p ∣ Nat.card X₂) :
    (∃ φ : ↥X₁ →* alternatingGroup (Fin p), φ.ker ≤ Subgroup.center ↥X₁) ∨
    (∃ φ : ↥X₂ →* alternatingGroup (Fin p), φ.ker ≤ Subgroup.center ↥X₂) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hA2 := not_sq_dvd_card_of_quasisimple hp57 hJ h₁ hq₁
  have hB2 := not_sq_dvd_card_of_quasisimple hp57 hJ h₂ hq₂
  set V : Subgroup Y := X₁ ⊔ X₂ with hV
  have hVJ : V ≤ J := sup_le h₁ h₂
  have hVperf : ⁅V, V⁆ = V := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem hg₁ hg₂) (V.inv_mem hg₁)) (V.inv_mem hg₂)
    · refine sup_le ?_ ?_
      · rw [← commutator_eq_self_of_open_isQuasisimple hq₁]
        exact Subgroup.commutator_mono le_sup_left le_sup_left
      · rw [← commutator_eq_self_of_open_isQuasisimple hq₂]
        exact Subgroup.commutator_mono le_sup_right le_sup_right
  obtain ⟨N, hN, hNi, f, hf⟩ := hJ V hVJ hVperf
  have := hN
  have hX₁V : X₁ ≤ V := le_sup_left
  have hX₂V : X₂ ≤ V := le_sup_right
  have hAq : CFSG.Open.IsQuasisimple ↥(X₁.subgroupOf V) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hX₁V) hq₁
  have hBq : CFSG.Open.IsQuasisimple ↥(X₂.subgroupOf V) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hX₂V) hq₂
  have hcardA : Nat.card (X₁.subgroupOf V) = Nat.card X₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁V).toEquiv
  have hcardB : Nat.card (X₂.subgroupOf V) = Nat.card X₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂V).toEquiv
  have hAB : ∀ a ∈ X₁.subgroupOf V, ∀ b ∈ X₂.subgroupOf V, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.1 (hc hb) a.1 ha
    exact this
  rcases le_normal_of_commuting_quasisimple hp hNi hAq hBq hAB (hcardA ▸ hp₁) (hcardB ▸ hp₂)
      (hcardA ▸ hA2) (hcardB ▸ hB2) with hAN | hBN
  · exact Or.inl (exists_hom_alternating_of_le_normal hX₁V hq₁ hp hp₁
      (fun x hx => hAN (show (⟨x, hX₁V hx⟩ : ↥V) ∈ X₁.subgroupOf V from hx)) hf)
  · exact Or.inr (exists_hom_alternating_of_le_normal hX₂V hq₂ hp hp₂
      (fun x hx => hBN (show (⟨x, hX₂V hx⟩ : ↥V) ∈ X₂.subgroupOf V from hx)) hf)

theorem not_ker_le_center_of_noAp {Y : Type} [Group Y] [Finite Y] {p : ℕ} {X : Subgroup Y}
    (h : NoAp p (↥X ⧸ Subgroup.center ↥X)) (φ : ↥X →* alternatingGroup (Fin p)) :
    ¬ φ.ker ≤ Subgroup.center ↥X := by
  intro hker
  let g : ↥X ⧸ φ.ker →* ↥X ⧸ Subgroup.center ↥X :=
    QuotientGroup.map φ.ker (Subgroup.center ↥X) (MonoidHom.id _) (by simpa using hker)
  let r : ↥φ.range ≃* ↥X ⧸ φ.ker := (QuotientGroup.quotientKerEquivRange φ).symm
  have hg : Function.Surjective (g.comp r.toMonoidHom) := by
    intro s
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨r.symm (QuotientGroup.mk w), ?_⟩
    change g (r (r.symm (QuotientGroup.mk w))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  exact h ↥φ.range φ.range.subtype Subtype.val_injective (g.comp r.toMonoidHom) hg

theorem false_of_commuting_noAp {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) {J : Subgroup Y} (hJ : PerfectSectionsAltSqC p J)
    {X₁ X₂ : Subgroup Y} (h₁ : X₁ ≤ J) (h₂ : X₂ ≤ J)
    (hq₁ : CFSG.Open.IsQuasisimple ↥X₁) (hq₂ : CFSG.Open.IsQuasisimple ↥X₂)
    (hc : X₂ ≤ Subgroup.centralizer (X₁ : Set Y))
    (hp₁ : p ∣ Nat.card X₁) (hp₂ : p ∣ Nat.card X₂)
    (hn₁ : NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁)) (hn₂ : NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂)) :
    False := by
  rcases exists_hom_alternating_of_commuting hp57 hJ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact not_ker_le_center_of_noAp hn₁ φ hφ
  · exact not_ker_le_center_of_noAp hn₂ φ hφ

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
