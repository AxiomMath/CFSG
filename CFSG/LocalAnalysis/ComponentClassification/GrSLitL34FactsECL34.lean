module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped commutatorElement

theorem g₁_mem_centralizer_r₂ : g₁ ∈ centralizer {r₂} := by
  have h : comp 42 g₁T r₂T = comp 42 r₂T g₁T := by decide
  have h2 : TabRep (comp 42 g₁T r₂T) (r₂ * g₁) := by
    rw [h]
    exact tabRep_r₂.comp tabRep_g₁
  exact mem_centralizer_singleton_iff.mpr ((tabRep_g₁.comp tabRep_r₂).perm_eq h2)

theorem g₂_mem_centralizer_r₂ : g₂ ∈ centralizer {r₂} := by
  have h : comp 42 g₂T r₂T = comp 42 r₂T g₂T := by decide
  have h2 : TabRep (comp 42 g₂T r₂T) (r₂ * g₂) := by
    rw [h]
    exact tabRep_r₂.comp tabRep_g₂
  exact mem_centralizer_singleton_iff.mpr ((tabRep_g₂.comp tabRep_r₂).perm_eq h2)

theorem foldl_mem_centralizer_r₂ {w : List ℕ} (hw : ∀ j ∈ w, j = 0 ∨ j = 1)
    {g : Equiv.Perm (Fin 42)} (hg : g ∈ centralizer {r₂}) :
    w.foldl (fun g j => g * genS j) g ∈ centralizer {r₂} := by
  induction w generalizing g with
  | nil => exact hg
  | cons j w ih =>
    rw [List.foldl_cons]
    refine ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)) (mul_mem hg ?_)
    rcases hw j List.mem_cons_self with rfl | rfl
    · exact g₁_mem_centralizer_r₂
    · exact g₂_mem_centralizer_r₂

theorem wordPerm_mem_C₂ {w : List ℕ} (hw : ∀ j ∈ w, j = 0 ∨ j = 1) :
    wordPerm w ∈ centralizer {r₂} ⊓ S :=
  mem_inf.mpr ⟨foldl_mem_centralizer_r₂ hw (one_mem _), wordPerm_mem w⟩

theorem exists_aut_realization {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (hL : Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2) {τ : MulAut G} (hτ : orderOf τ = 2)
    (hτo : τ ∉ HarrisLit.innAut G) :
    ∃ q : G →* Equiv.Perm (Fin 42), (∀ e, q e ∈ S) ∧ (∀ s ∈ S, ∃ e, q e = s) ∧
      q.ker = center G ∧ ∃ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
        ∀ e, q (τ e) = ρ * q e * ρ⁻¹ := by
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL
  set q₀ : G →* Equiv.Perm (Fin 42) :=
    S.subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (center G))) with hq₀
  have hqS : ∀ e, q₀ e ∈ S := fun e => (ψ (QuotientGroup.mk e)).2
  have hqsurj : ∀ s ∈ S, ∃ e, q₀ e = s := by
    intro s hs
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (ψ.symm ⟨s, hs⟩)
    refine ⟨e, ?_⟩
    change ((ψ (QuotientGroup.mk e) : S) : Equiv.Perm (Fin 42)) = s
    rw [he, MulEquiv.apply_symm_apply]
  have hqker : q₀.ker = center G := by
    ext e
    rw [MonoidHom.mem_ker]
    change ((ψ (QuotientGroup.mk e) : S) : Equiv.Perm (Fin 42)) = 1 ↔ _
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hττ : ∀ e, τ (τ e) = e := by
    have h2 : τ * τ = 1 := by rw [← pow_two, ← hτ, pow_orderOf_eq_one]
    intro e
    rw [← MulAut.mul_apply, h2, MulAut.one_apply]
  obtain ⟨r, hrR, hr⟩ := exists_realization q₀ hqS hqsurj τ (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff τ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have h1 := hr (τ e)
      rw [hττ e, hr e] at h1
      calc q₀ e * (r * r) = r * (r * q₀ e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q₀ e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  have hrS : r ∉ S := by
    intro hrS
    obtain ⟨e₀, he₀⟩ := hqsurj r hrS
    apply hτo
    have h1 : (MulAut.conj e₀)⁻¹ * τ = 1 := by
      apply eq_one_of_mul_inv_mem_center
      intro y
      rw [← hqker, MonoidHom.mem_ker, MulAut.mul_apply, ← map_inv MulAut.conj e₀,
        MulAut.conj_apply]
      simp only [map_mul, map_inv, hr y, he₀]
      group
    exact ⟨e₀, eq_of_inv_mul_eq_one h1⟩
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  have hconj : ∃ ρ : Equiv.Perm (Fin 42), (ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) ∧
      ∃ c ∈ R, r = c * ρ * c⁻¹ := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · exact ⟨r₂, Or.inl rfl, eq_conj_of_isConj h⟩
    · exact ⟨r₃, Or.inr (Or.inl rfl), eq_conj_of_isConj h⟩
    · exact ⟨r₄, Or.inr (Or.inr rfl), eq_conj_of_isConj h⟩
  obtain ⟨ρ, hρ, c, hcR, hc⟩ := hconj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
  refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q₀, hS', hsurj', by rw [hker', hqker], ρ, hρ,
    fun e => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr e, hc]
  group

theorem false_of_L34_sixteen {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G)
    (hL : Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2) (h16 : Nat.card (center G) = 16)
    {τ : MulAut G} (hτ : orderOf τ = 2) (hτo : τ ∉ HarrisLit.innAut G) {K : Subgroup G}
    (hKτ : K ≤ HarrisLit.fixedPoints τ) (hKZ : K ⊓ center G = ⊥) (hK : 168 ≤ Nat.card K) :
    False := by
  have : Group.IsPerfect G := hq.1
  obtain ⟨q, hqS, hqsurj, hqker, ρ, hρ, hτρ⟩ := exists_aut_realization hL hτ hτo
  have hKC : ∀ k : K, q k ∈ centralizer {ρ} ⊓ S := by
    intro k
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hqS k⟩
    have h1 := hτρ k
    rw [HarrisLit.mem_fixedPoints.mp (hKτ k.2)] at h1
    calc q k * ρ = ρ * q k * ρ⁻¹ * ρ := by rw [← h1]
      _ = ρ * q k := by group
  let φ : K →* ↥(centralizer {ρ} ⊓ S) := (q.comp K.subtype).codRestrict _ hKC
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : q (k : G) = 1 := congrArg Subtype.val hk
    have h2 : (k : G) ∈ K ⊓ center G := ⟨k.2, hqker ▸ h1⟩
    rw [hKZ, mem_bot] at h2
    exact Subtype.ext h2
  have hcard : Nat.card K ≤ Nat.card ↥(centralizer {ρ} ⊓ S) := Nat.card_le_card_of_injective φ hφ
  rcases hρ with rfl | rfl | rfl
  · have hC : Nat.card ↥(centralizer {r₂} ⊓ S) = 168 := card_C₂
    have hsurj : Function.Surjective φ :=
      (Function.Injective.bijective_of_nat_card_le hφ (by omega)).2
    obtain ⟨k₁, hk₁⟩ := hsurj ⟨_, wordPerm_mem_C₂ (w := tg 1) (by decide)⟩
    obtain ⟨k₄, hk₄⟩ := hsurj ⟨_, wordPerm_mem_C₂ (w := tg 4) (by decide)⟩
    have hq₁ : q k₁ = wordPerm (tg 1) := congrArg Subtype.val hk₁
    have hq₄ : q k₄ = wordPerm (tg 4) := congrArg Subtype.val hk₄
    obtain ⟨l, hl, hls⟩ := exists_lam (Group.IsPerfect.commutator_eq_top) q hqS hqsurj hqker.le
    have hql : ∀ c, q (l c) = sigma c := fun c => by rw [← MonoidHom.comp_apply, hl]
    have hcen : ∀ {k : ℕ} {x : G}, k < 64 → q x = wordPerm (tg k) →
        (l (cv (tw k)))⁻¹ * x ∈ center G := fun hk hx => by
      rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hql, sigma_tw _ hk, hx, inv_mul_cancel]
    have hcomm : ⁅(k₁ : G), (k₄ : G)⁆ = l z₁ ^ 2 := by
      rw [show (k₁ : G) = l (cv (tw 1)) * ((l (cv (tw 1)))⁻¹ * k₁) by group,
        show (k₄ : G) = l (cv (tw 4)) * ((l (cv (tw 4)))⁻¹ * k₄) by group,
        CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hcen (by norm_num) hq₁)
          (hcen (by norm_num) hq₄), ← map_commutatorElement, commutatorElement_def]
      have h := comm_spec (d := (1, 4, 2, 0, 0)) (by decide)
      simp only [pow_zero, mul_one] at h
      rw [h, map_pow]
    have hz1 : l z₁ ^ 2 = 1 := by
      have hmK : ⁅(k₁ : G), (k₄ : G)⁆ ∈ K := by
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem k₁.2 k₄.2) (K.inv_mem k₁.2)) (K.inv_mem k₄.2)
      have hmZ : ⁅(k₁ : G), (k₄ : G)⁆ ∈ center G := by
        rw [hcomm, ← hqker, MonoidHom.mem_ker, map_pow, hql, sigma_z₁, one_pow]
      have h := mem_inf.mpr ⟨hmK, hmZ⟩
      rw [hKZ, mem_bot, hcomm] at h
      exact h
    have h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1 := by
      intro e he he3
      rw [hqker] at he
      have hd16 : orderOf (⟨e, he⟩ : center G) ∣ 16 := h16 ▸ orderOf_dvd_natCard _
      have hd3 : orderOf (⟨e, he⟩ : center G) ∣ 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_dvd_of_pow_eq_one he3
      have h1 : orderOf (⟨e, he⟩ : center G) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by norm_num) hd16 hd3
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    have hz2 : l z₂ ^ 4 = 1 := by rw [← map_pow, z₂_pow, map_one]
    have hmem : ∀ x : Fin 2 × Fin 4, l z₁ ^ x.1.val * l z₂ ^ x.2.val ∈ center G := fun x => by
      rw [← hqker]
      exact (mem_ker_iff hl hls h3).mpr ⟨_, _, rfl⟩
    have hs : Function.Surjective (fun x : Fin 2 × Fin 4 => (⟨_, hmem x⟩ : center G)) := by
      rintro ⟨z, hz⟩
      rw [← hqker] at hz
      obtain ⟨i, j, rfl⟩ := (mem_ker_iff hl hls h3).mp hz
      refine ⟨(⟨i % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      simp only
      rw [← pow_eq_pow_mod i hz1, ← pow_eq_pow_mod j hz2]
    have := Nat.card_le_card_of_surjective _ hs
    rw [h16, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2),
      Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, Fintype.card_fin] at this
    omega
  · have hC : Nat.card ↥(centralizer {r₃} ⊓ S) = 60 := card_C₃
    omega
  · have hC : Nat.card ↥(centralizer {r₄} ⊓ S) = 72 := card_C₄
    omega

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
