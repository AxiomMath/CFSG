module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThreePair

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Three

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

theorem odd_card_commutator_outer_of_cover {L : Type*} [Group L] (hL : commutator L = ⊤) {n : ℕ}
    (hn : 6 ≤ n) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    Odd (Nat.card (commutator (outerAutomorphismGroup L))) := by
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hL
  have hcomm : IsMulCommutative (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) := by
    rcases (by omega : n = 6 ∨ 7 ≤ n) with rfl | h7
    · exact CatalogueSchreierAlternating.DegreeSix.outer_commutative
    · have hdvd := CatalogueSchreierAlternating.outer_card_dvd_two_outside_six (Or.inr h7)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · have : Subsingleton (OuterAutomorphisms.Outer (alternatingGroup (Fin n))) :=
          (Nat.card_eq_one_iff_unique.mp h1).1
        exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have := isCyclic_of_prime_card h2
        infer_instance
  have hQ : IsMulCommutative (OuterAutomorphisms.Outer (L ⧸ center L)) :=
    ⟨⟨fun a b => (OuterAutomorphisms.equivalence e).injective (by
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _)⟩⟩
  set φ : OuterAutomorphisms.Outer L →* OuterAutomorphisms.Outer (L ⧸ center L) :=
    QuotientGroup.map _ _ (PerfectAutomorphisms.centerQuotientHom L)
      OuterAutomorphisms.centerQuotient_inner_le with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (OuterAutomorphisms.inner L) q
    rw [MonoidHom.mem_ker, hφdef, QuotientGroup.mk'_apply, QuotientGroup.map_mk,
      QuotientGroup.eq_one_iff] at hq
    obtain ⟨q', hq'⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center L) q'
    have h2 : MulAut.conj x = a :=
      PerfectAutomorphisms.centerQuotientHom_injective L
        ((OuterAutomorphisms.centerQuotient_conj x).trans hq')
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← h2]
    exact ⟨x, rfl⟩
  have hL' : IsMulCommutative (OuterAutomorphisms.Outer L) :=
    ⟨⟨fun a b => hφ (by rw [map_mul, map_mul]; exact hQ.is_comm.comm _ _)⟩⟩
  have h : commutator (OuterAutomorphisms.Outer L) = ⊥ := (commutator_eq_bot_iff _).mpr hL'
  show Odd (Nat.card (commutator (OuterAutomorphisms.Outer L)))
  rw [h, Subgroup.card_bot]
  exact odd_one

section Transport

variable {G : Type} [Group G] {n : ℕ}

theorem mem_center_conjEquiv_iff {A : Subgroup G} (g : G) (b : ↥(rightConjugate A g)) :
    conjEquiv A g b ∈ center ↥A ↔ b ∈ center ↥(rightConjugate A g) := by
  have h := Subgroup.map_center_eq (conjEquiv A g)
  constructor
  · intro hb
    rw [← h] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    rwa [(conjEquiv A g).injective hbb'] at hb'
  · intro hb
    rw [← h]
    exact ⟨b, hb, rfl⟩

@[expose] def Cov.conj {A : Subgroup G} (c : Cov A n) (g : G) : Cov (rightConjugate A g) n where
  π := c.π.comp (conjEquiv A g).toMonoidHom
  surjective x := by
    obtain ⟨a, ha⟩ := c.surjective x
    exact ⟨(conjEquiv A g).symm a, by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, ha]⟩
  ker_eq := by
    ext b
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
      c.ker_eq, mem_center_conjEquiv_iff]
  θ := c.θ.comp (conjN A g)
  θ_apply y b := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [c.θ_apply]
    congr 1
    apply Subtype.ext
    simp only [conjN_coe, conjEquiv_apply]
    group
  θ_eq_one_iff y := by
    rw [MonoidHom.comp_apply, c.θ_eq_one_iff, conjN_coe, AS76b.centralizer_rightConjugate,
      mem_rightConjugate_iff]

@[expose] def Side.conj {A S : Subgroup G} (s : Side A S n) (g : G) {S' : Subgroup G}
    (hS' : ∀ x : G, x ∈ S' ↔ g * x * g⁻¹ ∈ S) : Side (rightConjugate A g) S' n where
  toCov := s.toCov.conj g
  le x hx := (mem_rightConjugate_iff A g x).mpr (s.le ((hS' x).mp hx))
  map_eq := by
    ext u
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact s.mem_of_mem ((hS' b).mp (mem_subgroupOf.mp hb))
    · intro hu
      obtain ⟨t, ht, rfl⟩ := s.exists_of_mem hu
      have hb : g⁻¹ * t * g ∈ rightConjugate A g := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using s.le ht
      have hb' : g⁻¹ * t * g ∈ S' := by
        rw [hS']
        simpa [mul_assoc] using ht
      refine ⟨⟨g⁻¹ * t * g, hb⟩, mem_subgroupOf.mpr hb', ?_⟩
      change s.π (conjEquiv A g ⟨g⁻¹ * t * g, hb⟩) = _
      congr 1
      apply Subtype.ext
      rw [conjEquiv_apply]
      group

end Transport

section PartB

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

omit [Finite G] in
theorem mul_self_mul_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    (x * y) * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

omit [Finite G] in
theorem conj_mul_self {x p : G} (hp : p * p = 1) : (x * p * x⁻¹) * (x * p * x⁻¹) = 1 := by
  rw [show x * p * x⁻¹ * (x * p * x⁻¹) = x * (p * p) * x⁻¹ by group, hp, mul_one, mul_inv_cancel]

theorem le_of_odd_center (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) {n : ℕ} (hn : 7 ≤ n)
    {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) (hodd : Odd (Nat.card (center ↥A))) :
    T ≤ A := by
  obtain ⟨ι, hι⟩ := exists_eq_kleinFour_map hc h32 h4 h34 h2 hOut hn hψ
  have hinj : ∀ u v : normalizer (A : Set G), (u : G) ∈ A → (v : G) ∈ A → (u : G) * u = 1 →
      (v : G) * v = 1 → ψ u = ψ v → u = v := by
    intro u v hu hv hu2 hv2 huv
    have h := (Cov.ofPerm hψ (by omega)).eq_of_π_eq hodd (a := ⟨u, hu⟩) (b := ⟨v, hv⟩)
      (Subtype.ext hu2) (Subtype.ext hv2) (Subtype.ext huv)
    exact Subtype.ext (congrArg (fun w : ↥A => (w : G)) h)
  have hmemE : ∀ k ∈ kleinFour, ∃ t : normalizer (A : Set G), (t : G) ∈ T ∧
      ψ t = viaEmbeddingHom ι k := by
    intro k hk
    have : viaEmbeddingHom ι k ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := by
      rw [hι]
      exact ⟨k, hk, rfl⟩
    obtain ⟨t, ht, hte⟩ := this
    exact ⟨t, ht, hte⟩
  have hd₁ : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ kleinFour := subset_closure (Set.mem_insert _ _)
  have hd₂ : (swap 0 2 * swap 1 3 : Perm (Fin 4)) ∈ kleinFour :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨t₁, ht₁, hψ₁⟩ := hmemE _ hd₁
  obtain ⟨t₂, ht₂, hψ₂⟩ := hmemE _ hd₂
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
  have hT2 : ∀ {t : G}, t ∈ T → t * t = 1 := fun ht => by
    have h := (hc.elemT h32).2 _ ht
    rwa [sq] at h
  have hR2 : ∀ {r : G}, r ∈ R → r⁻¹ * r⁻¹ = 1 := fun hr => by
    have h := (hc.elemR h32).2 _ hr
    rw [sq] at h
    rw [← mul_inv_rev, h, inv_one]
  have hp₁' : p₁ = t₁ * r₁⁻¹ := by rw [he₁]; group
  have hp₂' : p₂ = t₂ * r₂⁻¹ := by rw [he₂]; group
  have hp₁2 : p₁ * p₁ = 1 := by
    rw [hp₁']
    exact mul_self_mul_of_commute (hT2 ht₁) (hR2 hr₁) (htr ht₁ hr₁).inv_right.eq
  have hp₂2 : p₂ * p₂ = 1 := by
    rw [hp₂']
    exact mul_self_mul_of_commute (hT2 ht₂) (hR2 hr₂) (htr ht₂ hr₂).inv_right.eq
  have hpc : Commute p₁ p₂ := by
    rw [hp₁', hp₂']
    exact (hTc.mul_right (htr ht₁ hr₂).inv_right).mul_left
      (((htr ht₂ hr₁).symm.mul_right hRc.inv_right).inv_left)
  have hp₁₂2 : (p₁ * p₂) * (p₁ * p₂) = 1 := mul_self_mul_of_commute hp₁2 hp₂2 hpc.eq
  have hp₂₁2 : (p₂ * p₁) * (p₂ * p₁) = 1 := mul_self_mul_of_commute hp₂2 hp₁2 hpc.symm.eq
  have hne1 : ∀ t : normalizer (A : Set G), ∀ k : Perm (Fin 4), k ≠ 1 →
      ψ t = viaEmbeddingHom ι k → (t : G) ≠ 1 := by
    intro t k hk hte h
    have ht : t = 1 := Subtype.ext h
    rw [ht, map_one] at hte
    exact hk ((viaEmbeddingHom_injective ι) (hte.symm.trans (map_one _).symm))
  have ht₁1 := hne1 t₁ _ (by decide) hψ₁
  have ht₂1 := hne1 t₂ _ (by decide) hψ₂
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_not_mem_range ι (by omega)
  obtain ⟨x₁, hx₁, hψx₁⟩ := hψ.exists_eq _
    (mul_swap_mem_alternatingGroup ι hab (show (0 : Fin 4) ≠ 1 by decide))
  obtain ⟨x₂, hx₂, hψx₂⟩ := hψ.exists_eq _
    (mul_swap_mem_alternatingGroup ι hab (show (0 : Fin 4) ≠ 2 by decide))
  set xN₁ : normalizer (A : Set G) := ⟨x₁, le_normalizer hx₁⟩
  set xN₂ : normalizer (A : Set G) := ⟨x₂, le_normalizer hx₂⟩
  set pN₁ : normalizer (A : Set G) := ⟨p₁, le_normalizer hp₁⟩
  set pN₂ : normalizer (A : Set G) := ⟨p₂, le_normalizer hp₂⟩
  have hmemA : ∀ {u v : G}, u ∈ A → v ∈ A → u * v * u⁻¹ ∈ A := fun hu hv =>
    mul_mem (mul_mem hu hv) (inv_mem hu)
  have c11 : x₁ * p₁ * x₁⁻¹ = p₁ := by
    have h := hinj (xN₁ * pN₁ * xN₁⁻¹) pN₁ (hmemA hx₁ hp₁) hp₁ (conj_mul_self hp₁2) hp₁2 (by
      rw [map_mul, map_mul, map_inv, hψx₁, hψp₁, hψ₁, conj_mul_swap ι ha hb,
        show (swap 0 1 : Perm (Fin 4)) * (swap 0 1 * swap 2 3) * (swap 0 1)⁻¹ =
          swap 0 1 * swap 2 3 by decide])
    exact congrArg Subtype.val h
  have hprod : ψ (pN₁ * pN₂) =
      viaEmbeddingHom ι (swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)) := by
    rw [map_mul, hψp₁, hψp₂, hψ₁, hψ₂, ← map_mul]
  have hprod' : ψ (pN₂ * pN₁) =
      viaEmbeddingHom ι (swap 0 2 * swap 1 3 * (swap 0 1 * swap 2 3)) := by
    rw [map_mul, hψp₁, hψp₂, hψ₁, hψ₂, ← map_mul]
  have c12 : x₁ * p₂ * x₁⁻¹ = p₁ * p₂ := by
    have h := hinj (xN₁ * pN₂ * xN₁⁻¹) (pN₁ * pN₂) (hmemA hx₁ hp₂) (mul_mem hp₁ hp₂)
      (conj_mul_self hp₂2) hp₁₂2 (by
      rw [hprod, map_mul, map_mul, map_inv, hψx₁, hψp₂, hψ₂, conj_mul_swap ι ha hb,
        show (swap 0 1 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) * (swap 0 1)⁻¹ =
          swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) by decide])
    exact congrArg Subtype.val h
  have c22 : x₂ * p₂ * x₂⁻¹ = p₂ := by
    have h := hinj (xN₂ * pN₂ * xN₂⁻¹) pN₂ (hmemA hx₂ hp₂) hp₂ (conj_mul_self hp₂2) hp₂2 (by
      rw [map_mul, map_mul, map_inv, hψx₂, hψp₂, hψ₂, conj_mul_swap ι ha hb,
        show (swap 0 2 : Perm (Fin 4)) * (swap 0 2 * swap 1 3) * (swap 0 2)⁻¹ =
          swap 0 2 * swap 1 3 by decide])
    exact congrArg Subtype.val h
  have c21 : x₂ * p₁ * x₂⁻¹ = p₂ * p₁ := by
    have h := hinj (xN₂ * pN₁ * xN₂⁻¹) (pN₂ * pN₁) (hmemA hx₂ hp₁) (mul_mem hp₂ hp₁)
      (conj_mul_self hp₁2) hp₂₁2 (by
      rw [hprod', map_mul, map_mul, map_inv, hψx₂, hψp₁, hψ₁, conj_mul_swap ι ha hb,
        show (swap 0 2 : Perm (Fin 4)) * (swap 0 1 * swap 2 3) * (swap 0 2)⁻¹ =
          swap 0 2 * swap 1 3 * (swap 0 1 * swap 2 3) by decide])
    exact congrArg Subtype.val h
  have hr₁1 := eq_one_of_conj hc h32 ht₁ ht₂ hr₁ hr₂ he₁ he₂ hx₁ c11 c12 ht₁1
  have hr₂1 := eq_one_of_conj hc h32 ht₂ ht₁ hr₂ hr₁ he₂ he₁ hx₂ c22 c21 ht₂1
  have ht₁A : (t₁ : G) ∈ A := by rw [he₁, hr₁1, mul_one]; exact hp₁
  have ht₂A : (t₂ : G) ∈ A := by rw [he₂, hr₂1, mul_one]; exact hp₂
  intro t ht
  have htN : t ∈ normalizer (A : Set G) := hc.le_normalizer ht
  have hE : ψ ⟨t, htN⟩ ∈ (closure {t₁, t₂}).map ψ := by
    have h1 : ψ ⟨t, htN⟩ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := ⟨_, ht, rfl⟩
    rw [hι, kleinFour, MonoidHom.map_closure] at h1
    rw [MonoidHom.map_closure, Set.image_pair, hψ₁, hψ₂]
    simpa [Set.image_pair] using h1
  obtain ⟨u, hu, hut⟩ := hE
  have huTA : u ∈ (T ⊓ A).subgroupOf (normalizer (A : Set G)) := by
    refine (closure_le _).mpr ?_ hu
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_inf.mpr ⟨ht₁, ht₁A⟩
    · exact Subgroup.mem_inf.mpr ⟨ht₂, ht₂A⟩
  have huTA' : (u : G) ∈ T ⊓ A := huTA
  obtain ⟨huT, huA⟩ := Subgroup.mem_inf.mp huTA'
  have hk : (u⁻¹ * ⟨t, htN⟩ : normalizer (A : Set G)) = 1 := by
    have hC : ((u⁻¹ * ⟨t, htN⟩ : normalizer (A : Set G)) : G) ∈
        T ⊓ Subgroup.centralizer (A : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem huT) ht, ?_⟩
      rw [← hψ.eq_one_iff, map_mul, map_inv, hut, inv_mul_cancel]
    obtain ⟨⟨-, -, -, hTC⟩, -⟩ :=
      Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp hc.not_mem hc.sylowT hc.le_normalizer hOut
    rw [hTC, mem_bot] at hC
    exact Subtype.ext hC
  have htu : (⟨t, htN⟩ : normalizer (A : Set G)) = u := (inv_mul_eq_one.mp hk).symm
  have : t = (u : G) := congrArg Subtype.val htu
  rw [this]
  exact huA

theorem exists_side_ge_seven (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) {n : ℕ} (hn : 7 ≤ n)
    (e : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) (hodd : Odd (Nat.card (center ↥A))) :
    Nonempty (Side A T n) := by
  have hOut := odd_card_commutator_outer_of_cover hc.hyp.standard.1.1 (by omega) e
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (autModel_perm (Or.inr hn)) hc.hyp.standard.1.1 e
  obtain ⟨ψ', hψ', hT⟩ := exists_normalized hc h32 h4 h34 h2 hOut hn hψ
  have hTA := le_of_odd_center hc h32 h4 h34 h2 hOut hn hψ' hodd
  refine ⟨{ toCov := Cov.ofPerm hψ' (by omega), le := hTA, map_eq := ?_ }⟩
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_rootV_iff_coe, ← hT]
    exact ⟨⟨a, le_normalizer a.2⟩, mem_subgroupOf.mpr (mem_subgroupOf.mp ha), rfl⟩
  · intro hu
    rw [mem_rootV_iff_coe, ← hT] at hu
    obtain ⟨t, ht, htu⟩ := hu
    have htT : (t : G) ∈ T := mem_subgroupOf.mp ht
    exact ⟨⟨t, hTA htT⟩, mem_subgroupOf.mpr htT, Subtype.ext htu⟩

theorem exists_side_six (hc : Sec3 A R T g) (h32 : Lemma32)
    (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (e : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6)) (hodd : Odd (Nat.card (center ↥A))) :
    Nonempty (Side A T 6) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hc.hyp.standard.1.1
  have hZ6 : center (alternatingGroup (Fin 6)) = ⊥ :=
    CatalogueSchreierAlternating.DegreeSix.center_eq_bot
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZ6) hA e
  set c := Cov.ofMulAut hψ hZ6 with hcdef
  have hOut := odd_card_commutator_outer_of_cover hA (by norm_num) e
  obtain ⟨⟨hTab, hT4, -, -⟩, -, -, -⟩ := Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp
    hc.not_mem hc.sylowT hc.le_normalizer hOut
  have hRK := R_le_centralizer hc
  have hcommAR : ∀ {p r : G}, p ∈ A → r ∈ R → p * r = r * p := fun hp hr =>
    mem_centralizer_iff.mp (hRK hr) _ hp
  have hR2 : ∀ r ∈ R, r * r = 1 := fun r hr => by
    have h := (hc.elemR h32).2 r hr
    rwa [sq] at h
  have huniq : ∀ (p p' : ↥A) {r r' : G}, r ∈ R → r' ∈ R → (p : G) * r = p' * r' → p = p' := by
    intro p p' r r' hr hr' h
    have hz : (p' : G)⁻¹ * p = r' * r⁻¹ := by
      calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * r) * r⁻¹ := by group
        _ = (p' : G)⁻¹ * (p' * r') * r⁻¹ := by rw [h]
        _ = r' * r⁻¹ := by group
    have hzR : r' * r⁻¹ ∈ R := mul_mem hr' (inv_mem hr)
    have h1 := eq_one_of_mem_inf_centralizer hodd (mul_mem (inv_mem p'.2) p.2)
      (by rw [hz]; exact hRK hzR) (by rw [hz]; exact hR2 _ hzR)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hpart : ∀ t : ↥T, ∃ p : ↥A, ∃ r ∈ R, (t : G) = p * r := fun t => by
    obtain ⟨p, hp, r, hr, he⟩ := exists_mul_of_mem_T hc h32 h4 h34 t.2
    exact ⟨⟨p, hp⟩, r, hr, he⟩
  choose pf rf hrf hpf using hpart
  let π : ↥T →* ↥A :=
    { toFun := pf
      map_one' := huniq _ _ (hrf 1) (one_mem R) (by rw [← hpf]; simp)
      map_mul' := fun t t' => huniq _ _ (hrf (t * t')) (mul_mem (hrf t) (hrf t')) (by
        calc ((pf (t * t') : ↥A) : G) * rf (t * t') = (t : G) * t' := by rw [← hpf]; rfl
          _ = (pf t : G) * (rf t * (pf t' : G)) * rf t' := by rw [hpf t, hpf t']; group
          _ = (pf t : G) * ((pf t' : G) * rf t) * rf t' := by
            rw [← hcommAR (pf t').2 (hrf t)]
          _ = ((pf t * pf t' : ↥A) : G) * (rf t * rf t') := by
            simp only [Subgroup.coe_mul]
            group) }
  have hπ : ∀ t : ↥T, (t : G) = π t * rf t := hpf
  have hπinj : Function.Injective π := (injective_iff_map_eq_one π).mpr fun t ht => by
    have h1 : (t : G) = rf t := by rw [hπ t, ht]; simp
    have hmem : (t : G) ∈ R ⊓ T := Subgroup.mem_inf.mpr ⟨by rw [h1]; exact hrf t, t.2⟩
    rw [hc.inf_eq_bot, mem_bot] at hmem
    exact Subtype.ext hmem
  have hπ2 : ∀ t : ↥T, π t * π t = 1 := fun t => by
    rw [← map_mul]
    have : t * t = 1 := Subtype.ext (by have := hTab.2 _ t.2; rwa [sq] at this)
    rw [this, map_one]
  set φ : ↥T →* alternatingGroup (Fin 6) := c.π.comp π with hφ
  have hφinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr fun t ht => by
    have hz : π t ∈ center ↥A := by rw [← c.ker_eq]; exact ht
    exact hπinj ((eq_one_of_mul_self_of_odd hodd hz (hπ2 t)).trans (map_one π).symm)
  have hPcard : 4 ≤ Nat.card φ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact hT4
  have hP2 : ∀ z ∈ φ.range, z * z = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_mul]
    have : t * t = 1 := Subtype.ext (by have := hTab.2 _ t.2; rwa [sq] at this)
    rw [this, map_one]
  have hPcomm : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩
    rw [← map_mul, ← map_mul, hTab.1.is_comm.comm t t']
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one hPcard
  obtain ⟨φ0, hφa, hφb⟩ := exists_mulAut_pair (hP2 a ha) (hP2 b hb) ha1 hb1 hab
    (hPcomm a ha b hb)
  set c' := c.relabel φ0 with hc'
  have hψπ : ∀ t : ↥T, c'.π (π t) = φ0 (φ t) := fun t => rfl
  have hne : (φ0 a : Perm (Fin 6)) ≠ φ0 b := fun h => hab (φ0.injective (Subtype.ext h))
  have hPV : ∀ z ∈ φ.range, (φ0 z : Perm (Fin 6)) = 1 ∨ InV0 (φ0 z : Perm (Fin 6)) := by
    intro z hz
    have hcz : ∀ w ∈ φ.range, (φ0 z : Perm (Fin 6)) * φ0 w = φ0 w * φ0 z := fun w hw => by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hPcomm z hz w hw]
    have hcu : ∀ u, InV0 u → (φ0 z : Perm (Fin 6)) * u = u * φ0 z := by
      intro u hu
      rcases inV0_cover hφa hφb hne hu with rfl | rfl | rfl
      · exact hcz a ha
      · exact hcz b hb
      · rw [← Subgroup.coe_mul, ← map_mul]
        exact hcz _ (mul_mem ha hb)
    exact eq_one_or_inV0_of_commute (mem_alternatingGroup.mp (φ0 z).2) (hcu _ (Or.inl rfl))
      (hcu _ (Or.inr (Or.inl rfl)))
  have hVP : ∀ u, InV0 u → ∃ z ∈ φ.range, (φ0 z : Perm (Fin 6)) = u := by
    intro u hu
    rcases inV0_cover hφa hφb hne hu with h | h | h
    · exact ⟨a, ha, h.symm⟩
    · exact ⟨b, hb, h.symm⟩
    · exact ⟨a * b, mul_mem ha hb, by rw [map_mul]; exact h.symm⟩
  have hu1 : InV0 (swap 0 1 * swap 2 3 : Perm (Fin 6)) := Or.inl rfl
  have hu2 : InV0 (swap 0 2 * swap 1 3 : Perm (Fin 6)) := Or.inr (Or.inl rfl)
  obtain ⟨_, ⟨t₁, rfl⟩, ht₁⟩ := hVP _ hu1
  obtain ⟨_, ⟨t₂, rfl⟩, ht₂⟩ := hVP _ hu2
  rw [← hψπ] at ht₁ ht₂
  set p₁ := π t₁ with hp₁
  set p₂ := π t₂ with hp₂
  obtain ⟨x₁, hx₁⟩ := c'.surjective ⟨swap 0 1 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩
  obtain ⟨x₂, hx₂⟩ := c'.surjective ⟨swap 0 2 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩
  have hψx₁ : (c'.π x₁ : Perm (Fin 6)) = swap 0 1 * swap 4 5 := by rw [hx₁]
  have hψx₂ : (c'.π x₂ : Perm (Fin 6)) = swap 0 2 * swap 4 5 := by rw [hx₂]
  have hrel : ∀ (x y z : ↥A), y * y = 1 → z * z = 1 →
      (c'.π x : Perm (Fin 6)) * c'.π y * (c'.π x : Perm (Fin 6))⁻¹ = c'.π z →
      (x : G) * y * (x : G)⁻¹ = z := by
    intro x y z hy hz h
    have hxy : (x * y * x⁻¹) * (x * y * x⁻¹) = 1 := conj_mul_self hy
    have : x * y * x⁻¹ = z :=
      c'.eq_of_π_eq hodd hxy hz (Subtype.ext (by simpa [map_mul, map_inv] using h))
    exact congrArg Subtype.val this
  have hp₁2 : p₁ * p₁ = 1 := hπ2 t₁
  have hp₂2 : p₂ * p₂ = 1 := hπ2 t₂
  have hp₁₂2 : (p₁ * p₂) * (p₁ * p₂) = 1 := by rw [hp₁, hp₂, ← map_mul]; exact hπ2 _
  have hp₂₁2 : (p₂ * p₁) * (p₂ * p₁) = 1 := by rw [hp₁, hp₂, ← map_mul]; exact hπ2 _
  have c11 : (x₁ : G) * p₁ * (x₁ : G)⁻¹ = p₁ := hrel _ _ _ hp₁2 hp₁2 (by
    rw [hψx₁, ht₁]
    decide)
  have c12 : (x₁ : G) * p₂ * (x₁ : G)⁻¹ = p₁ * p₂ := by
    have := hrel x₁ p₂ (p₁ * p₂) hp₂2 hp₁₂2 (by
      rw [hψx₁, map_mul, Subgroup.coe_mul, ht₁, ht₂]
      decide)
    rw [this, Subgroup.coe_mul]
  have c22 : (x₂ : G) * p₂ * (x₂ : G)⁻¹ = p₂ := hrel _ _ _ hp₂2 hp₂2 (by
    rw [hψx₂, ht₂]
    decide)
  have c21 : (x₂ : G) * p₁ * (x₂ : G)⁻¹ = p₂ * p₁ := by
    have := hrel x₂ p₁ (p₂ * p₁) hp₁2 hp₂₁2 (by
      rw [hψx₂, map_mul, Subgroup.coe_mul, ht₁, ht₂]
      decide)
    rw [this, Subgroup.coe_mul]
  have hne1 : ∀ t : ↥T, (c'.π (π t) : Perm (Fin 6)) ≠ 1 → (t : G) ≠ 1 := by
    intro t h ht
    apply h
    rw [show t = 1 from Subtype.ext ht, map_one, map_one]
    rfl
  have ht₁1 := hne1 t₁ (by rw [ht₁]; decide)
  have ht₂1 := hne1 t₂ (by rw [ht₂]; decide)
  have hr₁ := eq_one_of_conj hc h32 t₁.2 t₂.2 (hrf t₁) (hrf t₂) (hπ t₁) (hπ t₂) x₁.2 c11 c12 ht₁1
  have hr₂ := eq_one_of_conj hc h32 t₂.2 t₁.2 (hrf t₂) (hrf t₁) (hπ t₂) (hπ t₁) x₂.2 c22 c21 ht₂1
  have hp₁T : (p₁ : G) ∈ T := by
    have h := hπ t₁
    rw [hr₁, mul_one] at h
    rw [← h]
    exact t₁.2
  have hp₂T : (p₂ : G) ∈ T := by
    have h := hπ t₂
    rw [hr₂, mul_one] at h
    rw [← h]
    exact t₂.2
  have hπT : ∀ t : ↥T, ((π t : ↥A) : G) ∈ T := by
    intro t
    rcases hPV (φ t) ⟨t, rfl⟩ with h | h
    · rw [← hψπ] at h
      have : π t = 1 := c'.eq_of_π_eq hodd (hπ2 t) (mul_one 1)
        (Subtype.ext (by rw [h, map_one]; rfl))
      rw [this]
      exact one_mem T
    · rw [← hψπ] at h
      have h12 : (swap 0 1 * swap 2 3 : Perm (Fin 6)) ≠ swap 0 2 * swap 1 3 := by decide
      rcases inV0_cover hu1 hu2 h12 h with h' | h' | h'
      · rw [← ht₁] at h'
        rw [c'.eq_of_π_eq hodd (hπ2 t) hp₁2 (Subtype.ext h')]
        exact hp₁T
      · rw [← ht₂] at h'
        rw [c'.eq_of_π_eq hodd (hπ2 t) hp₂2 (Subtype.ext h')]
        exact hp₂T
      · rw [← ht₁, ← ht₂, ← Subgroup.coe_mul, ← map_mul] at h'
        rw [c'.eq_of_π_eq hodd (hπ2 t) hp₁₂2 (Subtype.ext h'), Subgroup.coe_mul]
        exact mul_mem hp₁T hp₂T
  have hTA : T ≤ A := by
    intro t ht
    have hr1 : rf ⟨t, ht⟩ = 1 := by
      have hmem : rf ⟨t, ht⟩ ∈ R ⊓ T := Subgroup.mem_inf.mpr ⟨hrf _, by
        have e' : rf ⟨t, ht⟩ = ((π ⟨t, ht⟩ : ↥A) : G)⁻¹ * t := by
          rw [eq_inv_mul_iff_mul_eq]
          exact (hπ ⟨t, ht⟩).symm
        rw [e']
        exact mul_mem (inv_mem (hπT _)) ht⟩
      rwa [hc.inf_eq_bot, mem_bot] at hmem
    have e' : t = ((π ⟨t, ht⟩ : ↥A) : G) := by
      have := hπ ⟨t, ht⟩
      rw [hr1, mul_one] at this
      exact this
    rw [e']
    exact (π ⟨t, ht⟩).2
  have hπself : ∀ t : ↥T, ((π t : ↥A) : G) = t := by
    intro t
    have := huniq (π t) ⟨t, hTA t.2⟩ (hrf t) (one_mem R) (by rw [← hπ t, mul_one])
    rw [this]
  refine ⟨{ toCov := c', le := hTA, map_eq := ?_ }⟩
  ext u
  constructor
  · rintro ⟨a, haT, rfl⟩
    have haT' : (a : G) ∈ T := mem_subgroupOf.mp haT
    have h1 : π ⟨a, haT'⟩ = a := Subtype.ext (hπself ⟨a, haT'⟩)
    rw [mem_rootV_six_iff, ← h1, hψπ]
    exact hPV _ ⟨_, rfl⟩
  · intro hu
    rw [mem_rootV_six_iff] at hu
    rcases hu with h | h
    · refine ⟨1, one_mem _, ?_⟩
      rw [map_one]
      exact Subtype.ext (by rw [h]; rfl)
    · obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hVP _ h
      rw [← hψπ] at ht
      exact ⟨π t, mem_subgroupOf.mpr (by rw [hπself t]; exact t.2), Subtype.ext ht⟩

theorem exists_side (hc : Sec3 A R T g) (h32 : Lemma32)
    (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) (hodd : Odd (Nat.card (center ↥A))) :
    Nonempty (Side A T n) := by
  rcases hn with rfl | rfl
  · exact exists_side_six hc h32 h4 h34 h2 e hodd
  · exact exists_side_ge_seven hc h32 h4 h34 h2 le_rfl e hodd

theorem exists_sides (hc : Sec3 A R T g) (h32 : Lemma32)
    (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) (hodd : Odd (Nat.card (center ↥A))) :
    Nonempty (Side A T n) ∧ Nonempty (Side (rightConjugate A g) R n) := by
  refine ⟨exists_side hc h32 h4 h34 h2 hn e hodd, ?_⟩
  obtain ⟨s⟩ := exists_side hc.swap h32 h4 h34 h2 hn e hodd
  refine ⟨s.conj g fun x => ?_⟩
  rw [mem_rightConjugate_iff]
  simp [mul_assoc]

end PartB

end CFSG.ComponentClassification.RankTwoAlt.Three
