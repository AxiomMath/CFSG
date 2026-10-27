module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement
open CFSG.Open

variable {Q₁ Q₂ S : Type} [Group Q₁] [Group Q₂] [Group S]

theorem commutatorElement_mul_central {G : Type} [Group G] {c c' : G}
    (hc : c ∈ Subgroup.center G) (hc' : c' ∈ Subgroup.center G) (d d' : G) :
    ⁅c * d, c' * d'⁆ = ⁅d, d'⁆ := by
  have h1 := Subgroup.mem_center_iff.1 hc
  have h2 := Subgroup.mem_center_iff.1 hc'
  have hz := Subgroup.mem_center_iff.1 (mul_mem hc hc')
  have e1 : c * d * (c' * d') = (c * c') * (d * d') := by
    rw [mul_assoc, ← mul_assoc d, h2 d]
    simp only [mul_assoc]
  have e2 : c' * d' * (c * d) = (c * c') * (d' * d) := by
    rw [mul_assoc, ← mul_assoc d', h1 d', ← h1 c']
    simp only [mul_assoc]
  have key : ∀ a b : G, ⁅a, b⁆ = a * b * (b * a)⁻¹ := fun a b => by
    rw [commutatorElement_def, mul_inv_rev, mul_assoc (a * b)]
  rw [key, key, e1, e2, mul_inv_rev, ← mul_assoc, mul_assoc (c * c') (d * d'),
    ← hz ((d * d') * (d' * d)⁻¹), mul_inv_cancel_right]

def fibreProduct (π₁ : Q₁ →* S) (π₂ : Q₂ →* S) : Subgroup (Q₁ × Q₂) :=
  MonoidHom.eqLocus (π₁.comp (MonoidHom.fst Q₁ Q₂)) (π₂.comp (MonoidHom.snd Q₁ Q₂))

theorem mem_fibreProduct {π₁ : Q₁ →* S} {π₂ : Q₂ →* S} {x : Q₁ × Q₂} :
    x ∈ fibreProduct π₁ π₂ ↔ π₁ x.1 = π₂ x.2 := Iff.rfl


variable {π₁ : Q₁ →* S} {π₂ : Q₂ →* S}

theorem map_fst_fibreProduct (h₂ : Function.Surjective π₂) :
    (fibreProduct π₁ π₂).map (MonoidHom.fst Q₁ Q₂) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, hb⟩ := h₂ (π₁ a)
  exact ⟨(a, b), hb.symm, rfl⟩

theorem map_snd_fibreProduct (h₁ : Function.Surjective π₁) :
    (fibreProduct π₁ π₂).map (MonoidHom.snd Q₁ Q₂) = ⊤ := by
  refine eq_top_iff.2 fun b _ => ?_
  obtain ⟨a, ha⟩ := h₁ (π₂ b)
  exact ⟨(a, b), ha, rfl⟩

abbrev fibreCore (π₁ : Q₁ →* S) (π₂ : Q₂ →* S) : Subgroup (Q₁ × Q₂) :=
  ⁅fibreProduct π₁ π₂, fibreProduct π₁ π₂⁆

theorem fibreCore_le : fibreCore π₁ π₂ ≤ fibreProduct π₁ π₂ :=
  Subgroup.commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem map_fst_fibreCore (h₂ : Function.Surjective π₂) (hp₁ : commutator Q₁ = ⊤) :
    (fibreCore π₁ π₂).map (MonoidHom.fst Q₁ Q₂) = ⊤ := by
  rw [Subgroup.map_commutator, map_fst_fibreProduct h₂]
  exact hp₁

theorem map_snd_fibreCore (h₁ : Function.Surjective π₁) (hp₂ : commutator Q₂ = ⊤) :
    (fibreCore π₁ π₂).map (MonoidHom.snd Q₁ Q₂) = ⊤ := by
  rw [Subgroup.map_commutator, map_snd_fibreProduct h₁]
  exact hp₂

theorem exists_central_mul_fibreCore (h₂ : Function.Surjective π₂)
    (hc₂ : π₂.ker ≤ Subgroup.center Q₂) (hp₁ : commutator Q₁ = ⊤)
    {x : Q₁ × Q₂} (hx : x ∈ fibreProduct π₁ π₂) :
    ∃ c ∈ Subgroup.center (Q₁ × Q₂), ∃ d ∈ fibreCore π₁ π₂, x = c * d := by
  have hx1 : x.1 ∈ (fibreCore π₁ π₂).map (MonoidHom.fst Q₁ Q₂) := by
    rw [map_fst_fibreCore h₂ hp₁]; trivial
  obtain ⟨d, hd, hd1⟩ := hx1
  refine ⟨x * d⁻¹, ?_, d, hd, by group⟩
  have hc : x * d⁻¹ ∈ fibreProduct π₁ π₂ := mul_mem hx (inv_mem (fibreCore_le hd))
  have h1 : (x * d⁻¹).1 = 1 := by
    simp only [Prod.fst_mul, Prod.fst_inv]
    rw [show d.1 = x.1 from hd1, mul_inv_cancel]
  have h2 : (x * d⁻¹).2 ∈ Subgroup.center Q₂ := by
    refine hc₂ ?_
    rw [MonoidHom.mem_ker, ← mem_fibreProduct.1 hc, h1, map_one]
  rw [Subgroup.center_prod]
  exact ⟨h1 ▸ Subgroup.one_mem _, h2⟩

theorem fibreCore_perfect (h₂ : Function.Surjective π₂)
    (hc₂ : π₂.ker ≤ Subgroup.center Q₂) (hp₁ : commutator Q₁ = ⊤) :
    ⁅fibreCore π₁ π₂, fibreCore π₁ π₂⁆ = fibreCore π₁ π₂ := by
  refine le_antisymm (Subgroup.commutator_mono fibreCore_le fibreCore_le) ?_
  refine Subgroup.commutator_le.2 fun g hg h hh => ?_
  obtain ⟨c, hc, d, hd, rfl⟩ := exists_central_mul_fibreCore h₂ hc₂ hp₁ hg
  obtain ⟨c', hc', d', hd', rfl⟩ := exists_central_mul_fibreCore h₂ hc₂ hp₁ hh
  rw [commutatorElement_mul_central hc hc']
  exact Subgroup.commutator_mem_commutator hd hd'

theorem mem_center_of_fibre (hc₁ : π₁.ker ≤ Subgroup.center Q₁)
    (hc₂ : π₂.ker ≤ Subgroup.center Q₂) {x : Q₁ × Q₂} (hx : x ∈ fibreProduct π₁ π₂)
    (h1 : π₁ x.1 = 1) : x ∈ Subgroup.center (Q₁ × Q₂) := by
  rw [Subgroup.center_prod]
  exact ⟨hc₁ h1, hc₂ (by rw [MonoidHom.mem_ker, ← mem_fibreProduct.1 hx, h1])⟩


abbrev fibreCoreProj (π₁ : Q₁ →* S) (π₂ : Q₂ →* S) : ↥(fibreCore π₁ π₂) →* S :=
  π₁.comp ((MonoidHom.fst Q₁ Q₂).comp (fibreCore π₁ π₂).subtype)

theorem fibreCoreProj_surjective (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (hp₁ : commutator Q₁ = ⊤) : Function.Surjective (fibreCoreProj π₁ π₂) := by
  intro s
  obtain ⟨a, rfl⟩ := h₁ s
  have ha : a ∈ (fibreCore π₁ π₂).map (MonoidHom.fst Q₁ Q₂) := by
    rw [map_fst_fibreCore h₂ hp₁]; trivial
  obtain ⟨d, hd, rfl⟩ := ha
  exact ⟨⟨d, hd⟩, rfl⟩

theorem isSimpleGroup_of_quasisimple {Q : Type} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) (π : Q →* S)
    (hπ : Function.Surjective π) (hk : π.ker = Subgroup.center Q) : IsSimpleGroup S := by
  haveI := hQ.2
  exact ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)).symm.isSimpleGroup

theorem center_eq_bot_of_quasisimple {Q : Type} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) (π : Q →* S)
    (hπ : Function.Surjective π) (hk : π.ker = Subgroup.center Q) :
    Subgroup.center S = ⊥ := by
  haveI := isSimpleGroup_of_quasisimple hQ π hπ hk
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
    fun htop => ?_
  have hcomm : commutator S = ⊥ := (commutator_eq_bot_iff_center_eq_top S).2 htop
  have hle : commutator Q ≤ π.ker := by
    rw [← MonoidHom.comap_bot, ← Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ, ← commutator_def, hcomm]
  rw [hQ.1, hk] at hle
  haveI := hQ.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (QuotientGroup.eq.2 (hle trivial))


theorem fibreCoreProj_ker (hQ₁ : CFSG.Open.IsQuasisimple Q₁) (h₁ : Function.Surjective π₁)
    (h₂ : Function.Surjective π₂) (hk₁ : π₁.ker = Subgroup.center Q₁)
    (hc₂ : π₂.ker ≤ Subgroup.center Q₂) :
    (fibreCoreProj π₁ π₂).ker = Subgroup.center ↥(fibreCore π₁ π₂) := by
  apply le_antisymm
  · intro x hx
    have hxc := mem_center_of_fibre hk₁.le hc₂ (fibreCore_le x.2) hx
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact (Subgroup.mem_center_iff.1 hxc) g
  · intro x hx
    have hS := center_eq_bot_of_quasisimple hQ₁ π₁ h₁ hk₁
    have hcen : fibreCoreProj π₁ π₂ x ∈ Subgroup.center S := by
      refine Subgroup.mem_center_iff.2 fun s => ?_
      obtain ⟨g, rfl⟩ := fibreCoreProj_surjective h₁ h₂ hQ₁.1 s
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx) g]
    rw [hS] at hcen
    exact hcen

theorem fibreCore_isQuasisimple (hQ₁ : CFSG.Open.IsQuasisimple Q₁) (h₁ : Function.Surjective π₁)
    (h₂ : Function.Surjective π₂) (hk₁ : π₁.ker = Subgroup.center Q₁)
    (hc₂ : π₂.ker ≤ Subgroup.center Q₂) : CFSG.Open.IsQuasisimple ↥(fibreCore π₁ π₂) := by
  refine ⟨?_, ?_⟩
  · apply Subgroup.map_injective (fibreCore π₁ π₂).subtype_injective
    rw [Subgroup.map_subtype_commutator, fibreCore_perfect h₂ hc₂ hQ₁.1,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · haveI := isSimpleGroup_of_quasisimple hQ₁ π₁ h₁ hk₁
    exact ((QuotientGroup.quotientMulEquivOfEq (fibreCoreProj_ker hQ₁ h₁ h₂ hk₁ hc₂).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (fibreCoreProj_surjective h₁ h₂ hQ₁.1))).isSimpleGroup


theorem card_eq_card_mul_center {Q : Type} [Group Q] (π : Q →* S) (hπ : Function.Surjective π)
    (hk : π.ker = Subgroup.center Q) :
    Nat.card Q = Nat.card S * Nat.card (Subgroup.center Q) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)]
  congr 1
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)).toEquiv

theorem exists_mulEquiv_of_centre_prime [Finite Q₁] [Finite Q₂] {ℓ : ℕ}
    (hQ₁ : CFSG.Open.IsQuasisimple Q₁) (hQ₂ : CFSG.Open.IsQuasisimple Q₂)
    (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (hk₁ : π₁.ker = Subgroup.center Q₁) (hk₂ : π₂.ker = Subgroup.center Q₂)
    (hz₁ : Nat.card (Subgroup.center Q₁) = ℓ) (hz₂ : Nat.card (Subgroup.center Q₂) = ℓ)
    (hbound : ∀ (D : Type) [Group D] [Finite D], CFSG.Open.IsQuasisimple D →
      ∀ ρ : D →* S, Function.Surjective ρ → ρ.ker = Subgroup.center D →
        IsPGroup ℓ (Subgroup.center D) → Nat.card (Subgroup.center D) ≤ ℓ) :
    ∃ f : Q₁ ≃* Q₂, π₂.comp f.toMonoidHom = π₁ := by
  set D := fibreCore π₁ π₂
  have hDq := fibreCore_isQuasisimple hQ₁ h₁ h₂ hk₁ hk₂.le
  have hker := fibreCoreProj_ker hQ₁ h₁ h₂ hk₁ hk₂.le
  have hρ := fibreCoreProj_surjective h₁ h₂ hQ₁.1
  have hpg : IsPGroup ℓ (Subgroup.center ↥D) := by
    intro x
    refine ⟨1, ?_⟩
    have hx : (x : ↥D) ∈ (fibreCoreProj π₁ π₂).ker := by rw [hker]; exact x.2
    have hxc := mem_center_of_fibre hk₁.le hk₂.le (fibreCore_le (x : ↥D).2) hx
    rw [Subgroup.center_prod] at hxc
    have e1 : (((x : ↥D) : Q₁ × Q₂).1) ^ ℓ = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center Q₁) (x := ⟨_, hxc.1⟩)
      rw [hz₁] at h
      exact congrArg Subtype.val h
    have e2 : (((x : ↥D) : Q₁ × Q₂).2) ^ ℓ = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center Q₂) (x := ⟨_, hxc.2⟩)
      rw [hz₂] at h
      exact congrArg Subtype.val h
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e1 e2
  have hbd := hbound ↥D hDq (fibreCoreProj π₁ π₂) hρ hker hpg
  have hcardD := card_eq_card_mul_center _ hρ hker
  have hcard1 := card_eq_card_mul_center π₁ h₁ hk₁
  have hcard2 := card_eq_card_mul_center π₂ h₂ hk₂
  let φ₁ : ↥D →* Q₁ := (MonoidHom.fst Q₁ Q₂).comp D.subtype
  let φ₂ : ↥D →* Q₂ := (MonoidHom.snd Q₁ Q₂).comp D.subtype
  have hs1 : Function.Surjective φ₁ := fun a => by
    obtain ⟨d, hd, rfl⟩ : a ∈ D.map (MonoidHom.fst Q₁ Q₂) := by
      rw [map_fst_fibreCore h₂ hQ₁.1]; trivial
    exact ⟨⟨d, hd⟩, rfl⟩
  have hs2 : Function.Surjective φ₂ := fun b => by
    obtain ⟨d, hd, rfl⟩ : b ∈ D.map (MonoidHom.snd Q₁ Q₂) := by
      rw [map_snd_fibreCore h₁ hQ₂.1]; trivial
    exact ⟨⟨d, hd⟩, rfl⟩
  have heq1 : Nat.card ↥D = Nat.card Q₁ := le_antisymm
    (by rw [hcardD, hcard1, hz₁]; exact Nat.mul_le_mul_left _ hbd)
    (Nat.card_le_card_of_surjective φ₁ hs1)
  have heq2 : Nat.card ↥D = Nat.card Q₂ := le_antisymm
    (by rw [hcardD, hcard2, hz₂]; exact Nat.mul_le_mul_left _ hbd)
    (Nat.card_le_card_of_surjective φ₂ hs2)
  let e₁ := MulEquiv.ofBijective φ₁ ((Nat.bijective_iff_surjective_and_card φ₁).2 ⟨hs1, heq1⟩)
  let e₂ := MulEquiv.ofBijective φ₂ ((Nat.bijective_iff_surjective_and_card φ₂).2 ⟨hs2, heq2⟩)
  refine ⟨e₁.symm.trans e₂, ?_⟩
  ext a
  have hd : ((e₁.symm a : ↥D) : Q₁ × Q₂).1 = a := e₁.apply_symm_apply a
  show π₂ ((e₁.symm a : ↥D) : Q₁ × Q₂).2 = π₁ a
  rw [← mem_fibreProduct.1 (fibreCore_le (e₁.symm a).2), hd]


theorem fibreCore_fst_bijective [Finite Q₁] [Finite Q₂] (hQ₁ : CFSG.Open.IsQuasisimple Q₁)
    (h₁ : Function.Surjective π₁) (h₂ : Function.Surjective π₂)
    (hk₁ : π₁.ker = Subgroup.center Q₁) (hc₂ : π₂.ker ≤ Subgroup.center Q₂)
    (hle : Nat.card (Subgroup.center ↥(fibreCore π₁ π₂)) ≤ Nat.card (Subgroup.center Q₁)) :
    Function.Bijective ((MonoidHom.fst Q₁ Q₂).comp (fibreCore π₁ π₂).subtype) := by
  have hker := fibreCoreProj_ker hQ₁ h₁ h₂ hk₁ hc₂
  have hρ := fibreCoreProj_surjective h₁ h₂ hQ₁.1
  have hs1 : Function.Surjective ((MonoidHom.fst Q₁ Q₂).comp (fibreCore π₁ π₂).subtype) :=
    fun a => by
      obtain ⟨d, hd, rfl⟩ : a ∈ (fibreCore π₁ π₂).map (MonoidHom.fst Q₁ Q₂) := by
        rw [map_fst_fibreCore h₂ hQ₁.1]; trivial
      exact ⟨⟨d, hd⟩, rfl⟩
  refine (Nat.bijective_iff_surjective_and_card _).2 ⟨hs1, le_antisymm ?_
    (Nat.card_le_card_of_surjective _ hs1)⟩
  rw [card_eq_card_mul_center _ hρ hker, card_eq_card_mul_center π₁ h₁ hk₁]
  exact Nat.mul_le_mul_left _ hle

open CFSG.Yardstones.Md0ec50421ce4 in
theorem maximalOddCover_of_oddBound (i : TauCeti.CFSGIndex) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (π : Q →* i.Group) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center Q) (hZ : Nat.card (Subgroup.center Q) = 3)
    (hbound : ∀ (D : Type) [Group D] [Finite D], CFSG.Open.IsQuasisimple D →
      ∀ ρ : D →* i.Group, Function.Surjective ρ → ρ.ker = Subgroup.center D →
        Odd (Nat.card (Subgroup.center D)) → Nat.card (Subgroup.center D) ∣ 3) :
    MaximalOddCover Q i := by
  haveI hsimple := isSimpleGroup_of_quasisimple hQ π hπ hker
  have hS := center_eq_bot_of_quasisimple hQ π hπ hker
  have h3 : Odd (Nat.card (Subgroup.center Q)) := hZ ▸ by decide
  refine ⟨inferInstance, hQ, hsimple, ?_, π, hπ, hker, ?_, h3, ?_⟩
  · by_contra h
    push_neg at h
    obtain ⟨a, ha⟩ := exists_ne (1 : i.Group)
    have hac : a ∈ Subgroup.center i.Group := Subgroup.mem_center_iff.2 fun g => h g a
    rw [hS] at hac
    exact ha hac
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hZ
  · intro U _ _ hU ρ hρ hρk hUodd
    have hker' := fibreCoreProj_ker hQ hπ hρ hker hρk.le
    have hDq := fibreCore_isQuasisimple hQ hπ hρ hker hρk.le
    have hρD := fibreCoreProj_surjective (π₂ := ρ) hπ hρ hQ.1
    have hodd : Odd (Nat.card (Subgroup.center ↥(fibreCore π ρ))) := by
      have hsub : (Subgroup.center ↥(fibreCore π ρ)).map (fibreCore π ρ).subtype ≤
          (Subgroup.center Q).prod (Subgroup.center U) := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ (fibreCoreProj π ρ).ker := by rw [hker']; exact hx
        have := mem_center_of_fibre hker.le hρk.le (fibreCore_le x.2) hx'
        rwa [Subgroup.center_prod] at this
      have hdvd := Subgroup.card_dvd_of_le hsub
      rw [Subgroup.card_map_of_injective (fibreCore π ρ).subtype_injective,
        Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at hdvd
      exact Odd.of_dvd_nat (h3.mul hUodd) hdvd
    have hbd := hbound _ hDq _ hρD hker' hodd
    have hle : Nat.card (Subgroup.center ↥(fibreCore π ρ)) ≤ Nat.card (Subgroup.center Q) :=
      hZ ▸ Nat.le_of_dvd (by norm_num) hbd
    let e₁ := MulEquiv.ofBijective _ (fibreCore_fst_bijective hQ hπ hρ hker hρk.le hle)
    have hs2 : Function.Surjective ((MonoidHom.snd Q U).comp (fibreCore π ρ).subtype) :=
      fun b => by
        obtain ⟨d, hd, rfl⟩ : b ∈ (fibreCore π ρ).map (MonoidHom.snd Q U) := by
          rw [map_snd_fibreCore hπ hU.1]; trivial
        exact ⟨⟨d, hd⟩, rfl⟩
    refine ⟨((MonoidHom.snd Q U).comp (fibreCore π ρ).subtype).comp e₁.symm.toMonoidHom,
      hs2.comp e₁.symm.surjective, ?_⟩
    ext a
    have hd : ((e₁.symm a : ↥(fibreCore π ρ)) : Q × U).1 = a := e₁.apply_symm_apply a
    show ρ ((e₁.symm a : ↥(fibreCore π ρ)) : Q × U).2 = π a
    rw [← mem_fibreProduct.1 (fibreCore_le (e₁.symm a).2), hd]

end CFSG.LocalAnalysis.GLTheoremA
