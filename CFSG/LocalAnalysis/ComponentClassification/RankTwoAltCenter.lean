module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltStructure
public import CFSG.Alternating.Multipliers.Main
public import CFSG.Permutation.Embedding

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
  CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers
open scoped commutatorElement

theorem commutatorElement_mul_central {Y : Type*} [Group Y] {a b z w : Y} (hz : z ∈ center Y)
    (hw : w ∈ center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ x : Y, z * x * z⁻¹ = x := fun x => by
    rw [← mem_center_iff.1 hz x, mul_inv_cancel_right]
  have hw' : ∀ x : Y, w * x * w⁻¹ = x := fun x => by
    rw [← mem_center_iff.1 hw x, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [hz']; group
    _ = ⁅a, b⁆ := by rw [hw', commutatorElement_def]

export CFSG.Permutation (viaEmbeddingHom_swap)

theorem spin_commutator_ne_one {m : ℕ} {a b c d : Fin (m + 2)} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {x y : Spin.E (m + 2)}
    (hx : (Spin.psi x : Perm (Fin (m + 2))) = swap a b * swap c d)
    (hy : (Spin.psi y : Perm (Fin (m + 2))) = swap a c * swap b d) : ⁅x, y⁆ ≠ 1 := by
  set d₁ : Spin.H (m + 2) := ⟨Spin.dd hab hcd, subset_closure ⟨a, b, c, d, hab, hcd, rfl⟩⟩
  set d₂ : Spin.H (m + 2) := ⟨Spin.dd hac hbd, subset_closure ⟨a, c, b, d, hac, hbd, rfl⟩⟩
  have hz : ∀ u v : Spin.H (m + 2), Spin.permH u = Spin.permH v →
      v⁻¹ * u ∈ center (Spin.H (m + 2)) := by
    intro u v huv
    apply Spin.ker_permH_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  have hx' : Spin.permH (x : Spin.H (m + 2)) = Spin.permH d₁ := by
    rw [show Spin.permH d₁ = swap a b * swap c d from Spin.perm_dd hab hcd]
    exact hx
  have hy' : Spin.permH (y : Spin.H (m + 2)) = Spin.permH d₂ := by
    rw [show Spin.permH d₂ = swap a c * swap b d from Spin.perm_dd hac hbd]
    exact hy
  have h1 : ⁅(x : Spin.H (m + 2)), (y : Spin.H (m + 2))⁆ = ⁅d₁, d₂⁆ := by
    rw [show (x : Spin.H (m + 2)) = d₁ * (d₁⁻¹ * x) by group,
      show (y : Spin.H (m + 2)) = d₂ * (d₂⁻¹ * y) by group,
      commutatorElement_mul_central (hz _ _ hx') (hz _ _ hy')]
  have h2 : ((⁅d₁, d₂⁆ : Spin.H (m + 2)) : Spin.monomial (m + 2)) = Spin.negOne := by
    have := Spin.commutator_dd hab hac had hbc hbd hcd
    simpa [commutatorElement_def, d₁, d₂] using this
  intro h
  apply Spin.negOne_ne_one (n := m + 2)
  rw [← h2, ← h1]
  have := congrArg (fun z : Spin.E (m + 2) => ((z : Spin.H (m + 2)) : Spin.monomial (m + 2))) h
  simpa [commutatorElement_def] using this

theorem mul_ne_mul_of_card_ker_eq_two {P : Type} [Group P] [Group.IsPerfect P] {n : ℕ}
    (hn : 8 ≤ n) {π : P →* alternatingGroup (Fin n)} (hπs : Function.Surjective π)
    (hπk : π.ker ≤ center P) (h2 : Nat.card π.ker = 2) (ι : Fin 4 ↪ Fin n) {x y : P}
    (hx : (π x : Perm (Fin n)) = viaEmbeddingHom ι (swap 0 1 * swap 2 3))
    (hy : (π y : Perm (Fin n)) = viaEmbeddingHom ι (swap 0 2 * swap 1 3)) : x * y ≠ y * x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 3 ≤ m := by omega
  have : Group.IsPerfect (alternatingGroup (Fin (m + 2))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  have hne' : ∀ i j : Fin 4, i ≠ j → ι i ≠ ι j := fun i j h => ι.injective.ne h
  have hx' : (π x : Perm (Fin (m + 2))) = swap (ι 0) (ι 1) * swap (ι 2) (ι 3) := by
    rw [hx, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  have hy' : (π y : Perm (Fin (m + 2))) = swap (ι 0) (ι 2) * swap (ι 1) (ι 3) := by
    rw [hy, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  set uP := hopfLift π hπs hπk with huP
  set uE := hopfLift Spin.psi (Spin.psi_surjective hm) Spin.ker_psi_le_center with huE
  obtain ⟨xU, hxU⟩ := hopfCoverMap_surjective (S := alternatingGroup (Fin (m + 2))) (π x)
  obtain ⟨yU, hyU⟩ := hopfCoverMap_surjective (S := alternatingGroup (Fin (m + 2))) (π y)
  have hcP : ∀ u, π (uP u) = hopfCoverMap _ u := fun u =>
    congrArg (fun f => f u) (comp_hopfLift π hπs hπk)
  have hcE : ∀ u, Spin.psi (uE u) = hopfCoverMap _ u := fun u =>
    congrArg (fun f => f u) (comp_hopfLift Spin.psi (Spin.psi_surjective hm) Spin.ker_psi_le_center)
  have hπc : ⁅π x, π y⁆ = 1 := by
    apply Subtype.ext
    have h : (π x : Perm (Fin (m + 2))) * (π y : Perm (Fin (m + 2))) *
        ((π x : Perm (Fin (m + 2))))⁻¹ * ((π y : Perm (Fin (m + 2))))⁻¹ = 1 := by
      rw [hx, hy, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
        show (swap 0 1 * swap 2 3 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) *
          (swap 0 1 * swap 2 3)⁻¹ * (swap 0 2 * swap 1 3)⁻¹ = 1 by decide, map_one]
    simpa [commutatorElement_def] using h
  have hmem : ⁅xU, yU⁆ ∈ hopfMultiplier (alternatingGroup (Fin (m + 2))) := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hxU, hyU, hπc]
  have hne : ⁅xU, yU⁆ ≠ 1 := by
    intro h
    refine spin_commutator_ne_one (hne' 0 1 (by decide)) (hne' 0 2 (by decide))
      (hne' 0 3 (by decide)) (hne' 1 2 (by decide)) (hne' 1 3 (by decide)) (hne' 2 3 (by decide))
      (x := uE xU) (y := uE yU) ?_ ?_ (by rw [← map_commutatorElement, h, map_one])
    · rw [hcE, hxU, hx']
    · rw [hcE, hyU, hy']
  have hMcard := card_hopfMultiplier_alternatingGroup hn
  have hmap := map_hopfMultiplier_hopfLift π hπs hπk
  have hfin : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hfinM : Finite (hopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
  let f : hopfMultiplier (alternatingGroup (Fin (m + 2))) → π.ker := fun k =>
    ⟨uP k, by rw [← hmap]; exact ⟨k, k.2, rfl⟩⟩
  have hfsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    exact ⟨⟨k, hk⟩, rfl⟩
  have hfbij : Function.Bijective f :=
    Function.Surjective.bijective_of_nat_card_le hfsurj (by rw [hMcard, h2])
  intro hxy
  have hcen : ∀ (u : HopfCover (alternatingGroup (Fin (m + 2)))) (z : P), π (uP u) = π z →
      z⁻¹ * uP u ∈ center P := by
    intro u z hu
    apply hπk
    rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel]
  have h1 : ⁅uP xU, uP yU⁆ = 1 := by
    rw [show uP xU = x * (x⁻¹ * uP xU) by group, show uP yU = y * (y⁻¹ * uP yU) by group,
      commutatorElement_mul_central (hcen xU x (by rw [hcP, hxU]))
        (hcen yU y (by rw [hcP, hyU])), commutatorElement_def, hxy]
    group
  have h3 : f ⟨⁅xU, yU⁆, hmem⟩ = f 1 := by
    apply Subtype.ext
    simp only [f, map_commutatorElement, h1]
    rfl
  exact hne (congrArg Subtype.val (hfbij.1 h3))

section Cover

variable {P : Type} [Group P]

theorem card_ker_dvd_two (hP : commutator P = ⊤) {n : ℕ} (hn : 8 ≤ n)
    {π : P →* alternatingGroup (Fin n)} (hπs : Function.Surjective π) (hπk : π.ker ≤ center P) :
    Nat.card π.ker ∣ 2 := by
  have : Group.IsPerfect P := (Group.isPerfect_def).2 hP
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin n))) (hopfLift π hπs hπk)
  rwa [map_hopfMultiplier_hopfLift π hπs hπk, card_hopfMultiplier_alternatingGroup hn] at h

theorem card_ker_dvd_two_five (hP : commutator P = ⊤)
    {π : P →* alternatingGroup (Fin 5)} (hπs : Function.Surjective π) (hπk : π.ker ≤ center P) :
    Nat.card π.ker ∣ 2 := by
  have : Group.IsPerfect P := (Group.isPerfect_def).2 hP
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin 5))) (hopfLift π hπs hπk)
  rwa [map_hopfMultiplier_hopfLift π hπs hπk, hopfMultiplier_alternatingGroup_five.2] at h

theorem eq_one_of_dvd_two_of_odd {k : ℕ} (h : k ∣ 2) (hodd : Odd k) : k = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
  · exact h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

@[expose] noncomputable def quotCenterHom {n : ℕ} (e : P ⧸ center P ≃* alternatingGroup (Fin n)) :
    P →* alternatingGroup (Fin n) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center P))

theorem quotCenterHom_surjective {n : ℕ} (e : P ⧸ center P ≃* alternatingGroup (Fin n)) :
    Function.Surjective (quotCenterHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_quotCenterHom {n : ℕ} (e : P ⧸ center P ≃* alternatingGroup (Fin n)) :
    (quotCenterHom e).ker = center P := by
  ext x
  simp only [quotCenterHom, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem center_eq_bot_of_odd (hP : commutator P = ⊤) {n : ℕ} (hn : 8 ≤ n)
    (e : P ⧸ center P ≃* alternatingGroup (Fin n)) (hodd : Odd (Nat.card (center P))) :
    center P = ⊥ := by
  have h := card_ker_dvd_two hP hn (quotCenterHom_surjective e) (ker_quotCenterHom e).le
  rw [ker_quotCenterHom] at h
  exact Subgroup.eq_bot_of_card_eq _ (eq_one_of_dvd_two_of_odd h hodd)

theorem center_eq_bot_of_odd_five (hP : commutator P = ⊤)
    (e : P ⧸ center P ≃* alternatingGroup (Fin 5)) (hodd : Odd (Nat.card (center P))) :
    center P = ⊥ := by
  have h := card_ker_dvd_two_five hP (quotCenterHom_surjective e) (ker_quotCenterHom e).le
  rw [ker_quotCenterHom] at h
  exact Subgroup.eq_bot_of_card_eq _ (eq_one_of_dvd_two_of_odd h hodd)

end Cover

section Restrict

variable {G : Type} [Group G] {A : Subgroup G} {W : Type*} [Group W] {X : Subgroup W}
  {ψ : normalizer (A : Set G) →* W}

@[expose] noncomputable def restrictA (hψ : IsActionHom A X ψ) : ↥A →* ↥X :=
  (ψ.comp (Subgroup.inclusion le_normalizer)).codRestrict X fun a => hψ.map_mem a a.2

theorem restrictA_coe (hψ : IsActionHom A X ψ) (a : ↥A) :
    ((restrictA hψ a : ↥X) : W) = ψ ⟨a, le_normalizer a.2⟩ :=
  rfl

theorem restrictA_surjective (hψ : IsActionHom A X ψ) : Function.Surjective (restrictA hψ) := by
  intro x
  obtain ⟨a, ha, hax⟩ := hψ.exists_eq x x.2
  exact ⟨⟨a, ha⟩, Subtype.ext hax⟩

theorem ker_restrictA (hψ : IsActionHom A X ψ) : (restrictA hψ).ker = center ↥A := by
  ext a
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h b
    have h1 : ψ ⟨a, le_normalizer a.2⟩ = 1 := congrArg Subtype.val h
    have h2 := (hψ.eq_one_iff _).mp h1
    exact Subtype.ext (mem_centralizer_iff.mp h2 b b.2)
  · intro h
    apply Subtype.ext
    show ψ ⟨a, le_normalizer a.2⟩ = 1
    rw [hψ.eq_one_iff, mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (h ⟨b, hb⟩)

end Restrict

section Center

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
  (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
include hc h32 h4 h34 h2 hOut

theorem odd_card_center {n : ℕ} (hn : 8 ≤ n) {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) : Odd (Nat.card (center ↥A)) := by
  have hperf : commutator ↥A = ⊤ := hc.hyp.standard.1.1
  have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hperf
  by_contra hodd
  have hdvd := card_ker_dvd_two hperf hn (restrictA_surjective hψ) (ker_restrictA hψ).le
  rw [ker_restrictA hψ] at hdvd
  have hZ2 : Nat.card (center ↥A) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (h ▸ odd_one) hodd
    · exact h
  obtain ⟨ι, hι⟩ := exists_eq_kleinFour_map hc h32 h4 h34 h2 hOut (by omega) hψ
  have hmemE : ∀ k ∈ kleinFour, ∃ t : normalizer (A : Set G), (t : G) ∈ T ∧
      ψ t = viaEmbeddingHom ι k := by
    intro k hk
    have : viaEmbeddingHom ι k ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := by
      rw [hι]
      exact ⟨k, hk, rfl⟩
    obtain ⟨t, ht, hte⟩ := this
    exact ⟨t, ht, hte⟩
  obtain ⟨t₁, ht₁, hψ₁⟩ := hmemE _ (subset_closure (Set.mem_insert _ _))
  obtain ⟨t₂, ht₂, hψ₂⟩ := hmemE _ (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hpart : ∀ t : normalizer (A : Set G), (t : G) ∈ T → ∃ (p : G) (hp : p ∈ A) (r : G),
      r ∈ R ∧ (t : G) = p * r ∧ ψ ⟨p, le_normalizer hp⟩ = ψ t := by
    intro t ht
    obtain ⟨p, hp, r, hr, he⟩ := exists_mul_of_mem_T hc h32 h4 h34 ht
    refine ⟨p, hp, r, hr, he, ?_⟩
    have hrN : r ∈ normalizer (A : Set G) := R_le_normalizer hc hr
    have hr1 : ψ ⟨r, hrN⟩ = 1 := (hψ.eq_one_iff _).mpr (R_le_centralizer hc hr)
    rw [show t = ⟨p, le_normalizer hp⟩ * ⟨r, hrN⟩ from Subtype.ext he, map_mul, hr1, mul_one]
  obtain ⟨p₁, hp₁, r₁, hr₁, he₁, hψp₁⟩ := hpart t₁ ht₁
  obtain ⟨p₂, hp₂, r₂, hr₂, he₂, hψp₂⟩ := hpart t₂ ht₂
  have hTc : Commute (t₁ : G) t₂ :=
    congrArg Subtype.val ((hc.elemT h32).1.is_comm.comm (⟨_, ht₁⟩ : T) ⟨_, ht₂⟩)
  have hRc : Commute r₁ r₂ :=
    congrArg Subtype.val ((hc.elemR h32).1.is_comm.comm (⟨_, hr₁⟩ : R) ⟨_, hr₂⟩)
  have htr : ∀ {t r : G}, t ∈ T → r ∈ R → Commute t r := fun ht hr =>
    (mem_centralizer_iff.mp (hc.le_centralizer ht) _ hr).symm
  have hp₁' : p₁ = t₁ * r₁⁻¹ := by rw [he₁]; group
  have hp₂' : p₂ = t₂ * r₂⁻¹ := by rw [he₂]; group
  have hpc : Commute p₁ p₂ := by
    rw [hp₁', hp₂']
    exact (hTc.mul_right (htr ht₁ hr₂).inv_right).mul_left
      (((htr ht₂ hr₁).symm.mul_right hRc.inv_right).inv_left)
  refine mul_ne_mul_of_card_ker_eq_two hn (restrictA_surjective hψ) (ker_restrictA hψ).le
    (by rw [ker_restrictA hψ]; exact hZ2) ι (x := ⟨p₁, hp₁⟩) (y := ⟨p₂, hp₂⟩) ?_ ?_
    (Subtype.ext hpc.eq)
  · rw [restrictA_coe]
    exact hψp₁.trans hψ₁
  · rw [restrictA_coe]
    exact hψp₂.trans hψ₂

theorem center_eq_bot {n : ℕ} (hn : 8 ≤ n) {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) : center ↥A = ⊥ := by
  have hperf : commutator ↥A = ⊤ := hc.hyp.standard.1.1
  have h := card_ker_dvd_two hperf hn (restrictA_surjective hψ) (ker_restrictA hψ).le
  rw [ker_restrictA hψ] at h
  exact Subgroup.eq_bot_of_card_eq _
    (eq_one_of_dvd_two_of_odd h (odd_card_center hc h32 h4 h34 h2 hOut hn hψ))

end Center

end CFSG.ComponentClassification.RankTwoAlt
