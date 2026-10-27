module

public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplit

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open scoped Pointwise commutatorElement

theorem card_map_mul_card_inf_ker {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (H : Subgroup A) : Nat.card (H.map f) * Nat.card (H ⊓ f.ker : Subgroup A) = Nat.card H := by
  set g : H →* B := f.comp H.subtype with hg
  have hrange : g.range = H.map f := by
    rw [hg, MonoidHom.range_comp, range_subtype]
  have hker : g.ker = f.ker.subgroupOf H := by
    rw [hg, ← MonoidHom.comap_ker]
    rfl
  have h1 : Nat.card g.range = Nat.card (H ⧸ g.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv).symm
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  have h3 : Nat.card g.ker = Nat.card (H ⊓ f.ker : Subgroup A) := by
    rw [hker]
    have : Nat.card ((f.ker.subgroupOf H).map H.subtype) = Nat.card (f.ker.subgroupOf H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at this
    exact this.symm
  rw [← hrange, h1, ← h3, ← h2]

variable {G : Type*} [Group G]

theorem mem_centralizer_of_commutator_mem {N X Z : Subgroup G} (hperf : N ≤ ⁅N, N⁆ ⊔ X)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hZN : Z ≤ centralizer (N : Set G))
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    {x : G} (hxX : x ∈ X) (hx : ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ Z) :
    x ∈ centralizer (N : Set G) := by
  have hcen : ∀ z ∈ Z, ∀ n ∈ N, n * z = z * n := fun z hz n hn =>
    (mem_centralizer_iff.1 (hZN hz)) n hn
  have hmul : ∀ a ∈ N, ∀ b ∈ N, x * (a * b) * x⁻¹ * (a * b)⁻¹ =
      (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
    intro a ha b hb
    have hc := hcen _ (hx b hb) a ha
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹
        = (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹)) * a⁻¹ := by group
      _ = (x * a * x⁻¹ * a⁻¹) * ((x * b * x⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [hc]
      _ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
  set C : Subgroup G := N ⊓ centralizer ({x} : Set G) with hCdef
  have hcomm : ⁅N, N⁆ ≤ C := by
    rw [commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ N := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine mem_inf.2 ⟨hab, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hinv : ∀ c ∈ N, x * c⁻¹ * x⁻¹ * c⁻¹⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ := by
      intro c hc
      have h1 := hmul c hc c⁻¹ (inv_mem hc)
      rw [mul_inv_cancel, show x * 1 * x⁻¹ * 1⁻¹ = 1 by group] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have e := hmul (a * b) (mul_mem ha hb) (a⁻¹ * b⁻¹) (mul_mem (inv_mem ha) (inv_mem hb))
    rw [hmul a ha b hb, hmul a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb), hinv a ha, hinv b hb] at e
    have hab' : a * b * (a⁻¹ * b⁻¹) = ⁅a, b⁆ := by rw [commutatorElement_def]; group
    rw [hab'] at e
    have hz : (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) * ((x * a * x⁻¹ * a⁻¹)⁻¹ *
        (x * b * x⁻¹ * b⁻¹)⁻¹) = 1 := by
      rw [hZab _ (hx a ha) _ (hx b hb)]
      group
    rw [hz] at e
    have : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      calc x * ⁅a, b⁆ * x⁻¹ = (x * ⁅a, b⁆ * x⁻¹ * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by group
        _ = ⁅a, b⁆ := by rw [e, one_mul]
    calc ⁅a, b⁆ * x = (x * ⁅a, b⁆ * x⁻¹) * x := by rw [this]
      _ = x * ⁅a, b⁆ := by group
  have hX : X ≤ centralizer ({x} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact (hXab _ hy _ hxX)
  rw [mem_centralizer_iff]
  intro n hn
  have hn' := hperf hn
  have hle : ⁅N, N⁆ ⊔ X ≤ centralizer ({x} : Set G) :=
    sup_le (hcomm.trans inf_le_right) hX
  exact mem_centralizer_singleton_iff.1 (hle hn')

section Images

variable {N : Subgroup G} {Q : Type*} [Group Q] (π : N →* Q)

theorem commutator_subgroupOf {H K : Subgroup G} (hH : H ≤ N) (hK : K ≤ N) :
    (⁅H, K⁆).subgroupOf N = ⁅H.subgroupOf N, K.subgroupOf N⁆ := by
  apply Subgroup.map_injective N.subtype_injective
  rw [map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hH, inf_of_le_left hK, inf_of_le_left]
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hH ha) (hK hb)) (inv_mem (hH ha))) (inv_mem (hK hb))

theorem map_subgroupOf_sup {H K : Subgroup G} (hH : H ≤ N) (hK : K ≤ N) :
    ((H ⊔ K).subgroupOf N).map π = (H.subgroupOf N).map π ⊔ (K.subgroupOf N).map π := by
  rw [Subgroup.subgroupOf_sup hH hK, Subgroup.map_sup]

theorem map_subgroupOf_commutator {H K : Subgroup G} (hH : H ≤ N) (hK : K ≤ N) :
    ((⁅H, K⁆).subgroupOf N).map π = ⁅(H.subgroupOf N).map π, (K.subgroupOf N).map π⁆ := by
  rw [commutator_subgroupOf hH hK, map_commutator]

theorem map_subgroupOf_le_centralizer {H K : Subgroup G} (hHK : H ≤ centralizer (K : Set G)) :
    (H.subgroupOf N).map π ≤ centralizer (((K.subgroupOf N).map π : Subgroup Q) : Set Q) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have := (mem_centralizer_iff.1 (hHK (mem_subgroupOf.1 hh))) (k : G) (mem_subgroupOf.1 hk)
  rw [← map_mul, ← map_mul]
  exact congrArg π (Subtype.ext this)

theorem map_subgroupOf_conj {H : Subgroup G} {g : G} (hg : g ∈ N) :
    ((H.map (MulAut.conj g).toMonoidHom).subgroupOf N).map π =
      ((H.subgroupOf N).map π).map (MulAut.conj (π ⟨g, hg⟩)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, mem_map_equiv] at hn
    refine ⟨π (⟨g, hg⟩⁻¹ * n * ⟨g, hg⟩), ⟨⟨g, hg⟩⁻¹ * n * ⟨g, hg⟩, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      simpa [MulAut.conj_symm_apply] using hn
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf, mem_map_equiv]
      have := mem_subgroupOf.1 hn
      simp only [MulAut.conj_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [show g⁻¹ * (g * (n : G) * g⁻¹) * g = n by group]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem map_subgroupOf_normal (hπ : Function.Surjective π) {H : Subgroup G}
    (hNH : N ≤ normalizer (H : Set G)) (hHN : H ≤ N) : ((H.subgroupOf N).map π).Normal := by
  have : (H.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hHN).2 hNH
  exact this.map π hπ

theorem map_subgroupOf_self (hπ : Function.Surjective π) : (N.subgroupOf N).map π = ⊤ := by
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hπ]

end Images

theorem map_subgroupOf_le_normalizer {N : Subgroup G} {Q : Type*} [Group Q] (π : N →* Q)
    {H K : Subgroup G} (hHK : H ≤ normalizer (K : Set G)) :
    (H.subgroupOf N).map π ≤ normalizer (((K.subgroupOf N).map π : Subgroup Q) : Set Q) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  have hhN := hHK (mem_subgroupOf.1 hh)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨h * k * h⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact (mem_normalizer_iff.1 hhN _).1 (mem_subgroupOf.1 hk)
  · intro hy
    obtain ⟨k, hk, hk'⟩ := hy
    refine ⟨h⁻¹ * k * h, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      have := (mem_normalizer_iff.1 (inv_mem hhN) _).1 (mem_subgroupOf.1 hk)
      simpa using this
    · simp only [map_mul, map_inv, hk']
      group

theorem map_conj_eq_of_mem_normalizer {N : Subgroup G} {t : G}
    (ht : t ∈ normalizer (N : Set G)) : N.map (MulAut.conj t).toMonoidHom = N := by
  ext y
  rw [mem_map_equiv]
  have := (mem_normalizer_iff.1 (inv_mem ht) y)
  simp only [MulAut.conj_symm_apply, inv_inv] at this ⊢
  exact this.symm

@[expose] noncomputable def conjRestrict {N : Subgroup G} {t : G}
    (ht : t ∈ normalizer (N : Set G)) : N ≃* N :=
  ((MulAut.conj t).subgroupMap N).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer ht))

theorem coe_conjRestrict {N : Subgroup G} {t : G} (ht : t ∈ normalizer (N : Set G)) (n : N) :
    (conjRestrict ht n : G) = t * n * t⁻¹ := rfl

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

theorem mem_normalizer_inf_centralizer {X N : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hN : g ∈ normalizer (N : Set G)) :
    g ∈ normalizer ((X ⊓ centralizer (N : Set G) : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [map_inf_centralizer, map_conj_eq_of_mem_normalizer hX, map_conj_eq_of_mem_normalizer hN]

theorem exists_perfect_commuting_factor_of_ambient [Finite G]
    {K : Type*} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m)
    {N X Λ S F E : Subgroup G} {t r : G}
    (hXΛ : X ≤ Λ) (hΛN : Λ ≤ N) (hNΛ : N ≤ normalizer (Λ : Set G))
    (hNX : N ≤ normalizer (X : Set G))
    (hXsq : ∀ x ∈ X, x * x = 1) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (htN : t ∈ normalizer (N : Set G)) (htX : t ∈ normalizer (X : Set G))
    (hΛt : Λ ⊔ Λ.map (MulAut.conj t).toMonoidHom = N)
    (hcomm : ⁅Λ, Λ.map (MulAut.conj t).toMonoidHom⁆ ≤ X)
    (hperfN : N ≤ ⁅N, N⁆ ⊔ X)
    (θ₁ : Λ →* Matrix.SpecialLinearGroup (Fin 2) K) (hθ₁ : Function.Surjective θ₁)
    (hker : θ₁.ker = X.subgroupOf Λ)
    (hXS : X ≤ S) (hV : ∃ P : Sylow 2 Λ, (P : Subgroup Λ).map Λ.subtype = S ⊓ Λ)
    (hEV : E ≤ S ⊓ Λ) (hE : IsElementaryAbelian 2 E) (hEX : X ⊔ E = S ⊓ Λ)
    (hrN : r ∈ N) (hgen : Λ ≤ (S ⊓ Λ) ⊔ (S ⊓ Λ).map (MulAut.conj r).toMonoidHom)
    (hVn : S ⊓ Λ ≤ normalizer ((((S ⊓ Λ).map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj r).toMonoidHom : Subgroup G) : Set G))
    (hFX : F ≤ X) (hFS : F ≤ centralizer (S : Set G))
    (hσF : F.map (MulAut.conj t).toMonoidHom = F)
    (hZF : X ⊓ centralizer (N : Set G) ≤ F)
    (hFr : F ⊓ F.map (MulAut.conj r).toMonoidHom ≤ centralizer (N : Set G))
    (hcX : Nat.card X = (2 ^ m) ^ 4 * Nat.card (X ⊓ centralizer (N : Set G) : Subgroup G))
    (hcF : (2 ^ m) ^ 2 * Nat.card (X ⊓ centralizer (N : Set G) : Subgroup G) ≤ Nat.card F) :
    ∃ P : Subgroup G, P ≤ Λ ∧ ⁅P, P⁆ = P ∧ P ⊔ X = Λ ∧
      ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      ∀ R : Subgroup G, R ≤ Λ → ⁅R, R⁆ = R → R ≤ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := X ⊓ centralizer (N : Set G) with hZdef
  have hZX : Z ≤ X := inf_le_left
  have hXN : X ≤ N := hXΛ.trans hΛN
  have hZN : Z ≤ N := hZX.trans hXN
  have hZC : Z ≤ centralizer (N : Set G) := inf_le_right
  have hNZ : N ≤ normalizer (Z : Set G) := fun n hn =>
    mem_normalizer_inf_centralizer (hNX hn) (le_normalizer hn)
  have htZ : t ∈ normalizer (Z : Set G) := mem_normalizer_inf_centralizer htX htN
  have hZF' : Z ≤ F := hZF
  set Z' : Subgroup N := Z.subgroupOf N with hZ'def
  haveI hZ'n : Z'.Normal := (normal_subgroupOf_iff_le_normalizer hZN).2 hNZ
  set π : N →* N ⧸ Z' := QuotientGroup.mk' Z' with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z'
  have hπker : π.ker = Z' := QuotientGroup.ker_mk' Z'
  have hπ1 : ∀ n : N, π n = 1 ↔ (n : G) ∈ Z := fun n => by
    rw [← MonoidHom.mem_ker, hπker, mem_subgroupOf]
  set τ : N ≃* N := conjRestrict htN with hτdef
  have hτ : ∀ n : N, (τ n : G) = t * n * t⁻¹ := fun n => coe_conjRestrict htN n
  have hτsymm : ∀ n : N, (τ.symm n : G) = t⁻¹ * n * t := fun n => by
    have := hτ (τ.symm n)
    rw [MulEquiv.apply_symm_apply] at this
    calc (τ.symm n : G) = t⁻¹ * (t * (τ.symm n : G) * t⁻¹) * t := by group
      _ = t⁻¹ * n * t := by rw [← this]
  have hτZ : Z'.map τ.toMonoidHom = Z' := by
    ext y
    rw [mem_map_equiv, hZ'def, mem_subgroupOf, mem_subgroupOf, hτsymm]
    have := mem_normalizer_iff.1 (inv_mem htZ) (y : G)
    simp only [inv_inv] at this
    exact this.symm
  set σ : MulAut (N ⧸ Z') := QuotientGroup.congr Z' Z' τ hτZ with hσdef
  have hσπ : ∀ n : N, σ (π n) = π (τ n) := fun n => QuotientGroup.congr_mk' Z' Z' τ hτZ n
  have himg_t : ∀ H : Subgroup G, H ≤ N →
      ((H.subgroupOf N).map π).map σ.toMonoidHom =
        ((H.map (MulAut.conj t).toMonoidHom).subgroupOf N).map π := by
    intro H hHN
    ext q
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨τ h, ?_, (hσπ h).symm⟩
      rw [SetLike.mem_coe, mem_subgroupOf, hτ]
      exact ⟨h, mem_subgroupOf.1 hh, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hn
      obtain ⟨h, hh, hhn⟩ := hn
      have hhN : h ∈ N := hHN hh
      refine ⟨π ⟨h, hhN⟩, ⟨⟨h, hhN⟩, mem_subgroupOf.2 hh, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hσπ]
      congr 1
      apply Subtype.ext
      rw [hτ]
      exact hhn
  have hcard_img : ∀ H : Subgroup G, Z ≤ H → H ≤ N →
      Nat.card ((H.subgroupOf N).map π) * Nat.card Z = Nat.card H := by
    intro H hZH hHN
    have h1 := card_map_mul_card_inf_ker π (H.subgroupOf N)
    have h2 : H.subgroupOf N ⊓ π.ker = Z' := by
      rw [hπker, hZ'def]
      exact inf_of_le_right (fun x hx => mem_subgroupOf.2 (hZH (mem_subgroupOf.1 hx)))
    have h3 : Nat.card Z' = Nat.card Z := by
      rw [hZ'def]
      have : Nat.card ((Z.subgroupOf N).map N.subtype) = Nat.card (Z.subgroupOf N) :=
        Subgroup.card_map_of_injective N.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hZN] at this
      exact this.symm
    have h4 : Nat.card (H.subgroupOf N) = Nat.card H := by
      have : Nat.card ((H.subgroupOf N).map N.subtype) = Nat.card (H.subgroupOf N) :=
        Subgroup.card_map_of_injective N.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hHN] at this
      exact this.symm
    rw [h2, h3, h4] at h1
    exact h1
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hmem_img : ∀ (H : Subgroup G) (n : N), (n : G) ∈ H → π n ∈ (H.subgroupOf N).map π :=
    fun H n hn => ⟨n, mem_subgroupOf.2 hn, rfl⟩
  have hpre_img : ∀ (H : Subgroup G), Z ≤ H → ∀ n : N, π n ∈ (H.subgroupOf N).map π →
      (n : G) ∈ H := by
    intro H hZH n hn
    obtain ⟨h, hh, hhn⟩ := hn
    have : ((h⁻¹ * n : N) : G) ∈ Z := by
      rw [← hπ1, map_mul, map_inv, hhn, inv_mul_cancel]
    have := mul_mem (mem_subgroupOf.1 hh) (hZH this)
    simpa using this
  have hΛtN : Λ.map (MulAut.conj t).toMonoidHom ≤ N := le_sup_right.trans hΛt.le
  have hVN : S ⊓ Λ ≤ N := inf_le_right.trans hΛN
  have hFN : F ≤ N := hFX.trans hXN
  have hEN : E ≤ N := hEV.trans hVN
  have hVtN : (S ⊓ Λ).map (MulAut.conj t).toMonoidHom ≤ N :=
    (map_mono hVN).trans (map_conj_eq_of_mem_normalizer htN).le
  have hVrN : (S ⊓ Λ).map (MulAut.conj r).toMonoidHom ≤ N :=
    (map_mono hVN).trans (map_conj_eq_of_mem_normalizer (le_normalizer hrN)).le
  have hVtrN : ((S ⊓ Λ).map (MulAut.conj t).toMonoidHom).map (MulAut.conj r).toMonoidHom ≤ N :=
    (map_mono hVtN).trans (map_conj_eq_of_mem_normalizer (le_normalizer hrN)).le
  have hFrN : F.map (MulAut.conj r).toMonoidHom ≤ N :=
    (map_mono hFN).trans (map_conj_eq_of_mem_normalizer (le_normalizer hrN)).le
  haveI hXn : ((X.subgroupOf N).map π).Normal := map_subgroupOf_normal π hπ hNX hXN
  haveI hΛn : ((Λ.subgroupOf N).map π).Normal := map_subgroupOf_normal π hπ hNΛ hΛN
  have hσX : ((X.subgroupOf N).map π).map σ.toMonoidHom = (X.subgroupOf N).map π := by
    rw [himg_t X hXN, map_conj_eq_of_mem_normalizer htX]
  have hσΛ : ((Λ.subgroupOf N).map π).map σ.toMonoidHom =
      ((Λ.map (MulAut.conj t).toMonoidHom).subgroupOf N).map π := himg_t Λ hΛN
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hXab a (hZX ha) b (hZX hb)
  have hcen : (X.subgroupOf N).map π ⊓ center (N ⧸ Z') = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨ξ, hξ, rfl⟩, hc⟩
    rw [mem_bot, hπ1]
    have hξX : (ξ : G) ∈ X := mem_subgroupOf.1 hξ
    have hξC := mem_centralizer_of_commutator_mem hperfN hXab hZC hZab hξX (fun n hn => by
      have h1 := (mem_center_iff.1 hc) (π ⟨n, hn⟩)
      have h2 : π (ξ * ⟨n, hn⟩ * ξ⁻¹ * (⟨n, hn⟩ : N)⁻¹) = 1 := by
        simp only [map_mul, map_inv, ← h1]
        group
      exact (hπ1 _).1 h2)
    exact mem_inf.2 ⟨hξX, hξC⟩
  set πΛ : Λ →* (Λ.subgroupOf N).map π :=
    (π.comp (inclusion hΛN)).codRestrict _ (fun l => ⟨inclusion hΛN l,
      mem_subgroupOf.2 l.2, rfl⟩) with hπΛdef
  have hπΛ : Function.Surjective πΛ := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n, mem_subgroupOf.1 hn⟩, Subtype.ext rfl⟩
  have hπΛker : πΛ.ker ≤ θ₁.ker := by
    intro l hl
    rw [hker, mem_subgroupOf]
    have : π (inclusion hΛN l) = 1 := congrArg Subtype.val hl
    exact hZX ((hπ1 _).1 this)
  set θ : (Λ.subgroupOf N).map π →* Matrix.SpecialLinearGroup (Fin 2) K :=
    πΛ.liftOfRightInverse (Function.surjInv hπΛ) (Function.rightInverse_surjInv hπΛ)
      ⟨θ₁, hπΛker⟩ with hθdef
  have hθπ : ∀ l : Λ, θ (πΛ l) = θ₁ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hθsurj : Function.Surjective θ := by
    intro g
    obtain ⟨l, rfl⟩ := hθ₁ g
    exact ⟨πΛ l, hθπ l⟩
  have hθker : θ.ker = ((X.subgroupOf N).map π).subgroupOf ((Λ.subgroupOf N).map π) := by
    ext q
    obtain ⟨l, rfl⟩ := hπΛ q
    rw [MonoidHom.mem_ker, hθπ, ← MonoidHom.mem_ker, hker, mem_subgroupOf, mem_subgroupOf]
    constructor
    · intro hl
      exact hmem_img X (inclusion hΛN l) hl
    · intro hl
      exact hpre_img X hZX (inclusion hΛN l) hl
  have hVhat : ∃ P : Sylow 2 ((Λ.subgroupOf N).map π),
      (P : Subgroup _).map ((Λ.subgroupOf N).map π).subtype = ((S ⊓ Λ).subgroupOf N).map π := by
    obtain ⟨P₀, hP₀⟩ := hV
    refine ⟨P₀.mapSurjective hπΛ, ?_⟩
    rw [Sylow.coe_mapSurjective]
    ext q
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨inclusion hΛN p, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf, ← hP₀]
      exact ⟨p, hp, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      have hnV : (n : G) ∈ S ⊓ Λ := mem_subgroupOf.1 hn
      rw [← hP₀] at hnV
      obtain ⟨p, hp, hpn⟩ := hnV
      refine ⟨πΛ p, ⟨p, hp, rfl⟩, ?_⟩
      show π (inclusion hΛN p) = π n
      congr 1
      exact Subtype.ext hpn
  set rh : N ⧸ Z' := π ⟨r, hrN⟩ with hrh
  have hconjV : (((S ⊓ Λ).subgroupOf N).map π).map (MulAut.conj rh).toMonoidHom =
      (((S ⊓ Λ).map (MulAut.conj r).toMonoidHom).subgroupOf N).map π :=
    (map_subgroupOf_conj π hrN).symm
  have hgen' : (Λ.subgroupOf N).map π ≤ ((S ⊓ Λ).subgroupOf N).map π ⊔
      (((S ⊓ Λ).subgroupOf N).map π).map (MulAut.conj rh).toMonoidHom := by
    rw [hconjV, ← map_subgroupOf_sup π hVN hVrN]
    exact map_mono (fun x hx => mem_subgroupOf.2 (hgen (mem_subgroupOf.1 hx)))
  have hVn' : ((S ⊓ Λ).subgroupOf N).map π ≤ normalizer
      (((((S ⊓ Λ).subgroupOf N).map π).map σ.toMonoidHom).map (MulAut.conj rh).toMonoidHom :
        Set (N ⧸ Z')) := by
    rw [himg_t _ hVN, ← map_subgroupOf_conj π hrN]
    exact map_subgroupOf_le_normalizer π hVn
  have hFV' : (F.subgroupOf N).map π ≤
      centralizer ((((S ⊓ Λ).subgroupOf N).map π : Subgroup (N ⧸ Z')) : Set (N ⧸ Z')) :=
    map_subgroupOf_le_centralizer π (hFS.trans (centralizer_le (SetLike.coe_subset_coe.2
      inf_le_left)))
  have hσF' : ((F.subgroupOf N).map π).map σ.toMonoidHom = (F.subgroupOf N).map π := by
    rw [himg_t F hFN, hσF]
  have hFr' : (F.subgroupOf N).map π ⊓ ((F.subgroupOf N).map π).map (MulAut.conj rh).toMonoidHom
      = ⊥ := by
    have hZFr : Z ≤ F.map (MulAut.conj r).toMonoidHom := by
      rw [← map_conj_eq_of_mem_normalizer (hNZ hrN)]
      exact map_mono hZF'
    rw [← map_subgroupOf_conj π hrN, eq_bot_iff]
    rintro q ⟨⟨f, hf, rfl⟩, hq⟩
    rw [mem_bot]
    have hf' : (f : G) ∈ F.map (MulAut.conj r).toMonoidHom := hpre_img _ hZFr f hq
    have hfF : (f : G) ∈ F := mem_subgroupOf.1 hf
    rw [hπ1]
    exact mem_inf.2 ⟨hFX hfF, hFr (mem_inf.2 ⟨hfF, hf'⟩)⟩
  have hcX' : Nat.card ((X.subgroupOf N).map π) = (2 ^ m) ^ 4 := by
    have h := hcard_img X hZX hXN
    rw [hcX] at h
    exact Nat.eq_of_mul_eq_mul_right hZpos h
  have hcF' : (2 ^ m) ^ 2 ≤ Nat.card ((F.subgroupOf N).map π) := by
    have h := hcard_img F hZF' hFN
    have : (2 ^ m) ^ 2 * Nat.card Z ≤ Nat.card ((F.subgroupOf N).map π) * Nat.card Z := by
      rw [h]; exact hcF
    exact Nat.le_of_mul_le_mul_right this hZpos
  have hEhat : IsElementaryAbelian 2 ((E.subgroupOf N).map π) := by
    haveI := hE
    haveI := IsElementaryAbelian.subgroupOf (p := 2) (H := E) (K := N) hEN
    exact IsElementaryAbelian.map π
  obtain ⟨Ph, hPhn, hPh, hPhΛ, hPhX, hPhσ, hPhmax⟩ := exists_perfect_commuting_factor hK hm
    (X := (X.subgroupOf N).map π) (Λ := (Λ.subgroupOf N).map π)
    (V := ((S ⊓ Λ).subgroupOf N).map π) (F := (F.subgroupOf N).map π)
    (E := (E.subgroupOf N).map π) (r := rh) (σ := σ)
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, show x * x = 1 from Subtype.ext
      (hXsq _ (mem_subgroupOf.1 hx)), map_one])
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [← map_mul, ← map_mul,
      show x * y = y * x from Subtype.ext (hXab _ (mem_subgroupOf.1 hx) _
        (mem_subgroupOf.1 hy))])
    hσX hcen (map_mono (fun x hx => mem_subgroupOf.2 (hXΛ (mem_subgroupOf.1 hx))))
    (by rw [hσΛ, ← map_subgroupOf_sup π hΛN hΛtN, hΛt, map_subgroupOf_self π hπ])
    (by rw [hσΛ, ← map_subgroupOf_commutator π hΛN hΛtN]
        exact map_mono (fun x hx => mem_subgroupOf.2 (hcomm (mem_subgroupOf.1 hx))))
    θ hθsurj hθker hVhat
    (map_mono (fun x hx => mem_subgroupOf.2 (le_inf hXS hXΛ (mem_subgroupOf.1 hx))))
    (map_mono (fun x hx => mem_subgroupOf.2 (hEV (mem_subgroupOf.1 hx)))) hEhat
    (by rw [← map_subgroupOf_sup π hXN hEN, hEX])
    (mem_normalizer_of_normal _ rh) hgen' hVn'
    (map_mono (fun x hx => mem_subgroupOf.2 (hFX (mem_subgroupOf.1 hx)))) hFV' hσF' hFr'
    hcX' hcF'
  have hself : ∀ H : Subgroup G, ⁅H, H⁆ ≤ H := fun H => by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  set Pt : Subgroup G := (Ph.comap π).map N.subtype with hPtdef
  have hPtN : Pt ≤ N := map_subtype_le _
  have hmemPt : ∀ n : N, (n : G) ∈ Pt ↔ π n ∈ Ph := fun n => by
    constructor
    · rintro ⟨m, hm, hmn⟩
      have : m = n := Subtype.ext hmn
      rw [← this]
      exact hm
    · intro h
      exact ⟨n, h, rfl⟩
  have hZPt : Z ≤ Pt := fun z hz => (hmemPt ⟨z, hZN hz⟩).2 (by
    rw [(hπ1 _).2 hz]
    exact one_mem _)
  have hPtΛ : Pt ≤ Λ := by
    rintro _ ⟨n, hn, rfl⟩
    exact hpre_img Λ (hZX.trans hXΛ) n (hPhΛ hn)
  set P : Subgroup G := ⁅Pt, Pt⁆ with hPdef
  have hPPt : P ≤ Pt := hself Pt
  have hPN : P ≤ N := hPPt.trans hPtN
  have hPtPZ : Pt ≤ P ⊔ Z := by
    rintro _ ⟨n, hn, rfl⟩
    have hmap : (⁅Ph.comap π, Ph.comap π⁆).map π = Ph := by
      rw [map_commutator, map_comap_eq_self_of_surjective hπ, hPh]
    have hn' : π n ∈ (⁅Ph.comap π, Ph.comap π⁆).map π := by
      rw [hmap]
      exact hn
    obtain ⟨p, hp, hpn⟩ := hn'
    have hpP : (p : G) ∈ P := by
      have : (⁅Ph.comap π, Ph.comap π⁆).map N.subtype = P := by
        rw [map_commutator]
      rw [← this]
      exact ⟨p, hp, rfl⟩
    have hz : ((p⁻¹ * n : N) : G) ∈ Z := by
      rw [← hπ1, map_mul, map_inv, hpn, inv_mul_cancel]
    have e : (n : G) = p * ((p⁻¹ * n : N) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show (n : G) ∈ P ⊔ Z
    rw [e]
    exact mul_mem (mem_sup_left hpP) (mem_sup_right hz)
  have hZcen : Z ≤ centralizer ((P ⊔ Z : Subgroup G) : Set G) :=
    hZC.trans (centralizer_le (SetLike.coe_subset_coe.2 (sup_le hPN hZN)))
  have hPperf : ⁅P, P⁆ = P := by
    refine le_antisymm (hself P) ?_
    calc P = ⁅Pt, Pt⁆ := rfl
      _ ≤ ⁅P ⊔ Z, P ⊔ Z⁆ := commutator_mono hPtPZ hPtPZ
      _ ≤ ⁅P, P⁆ := commutator_sup_le_of_le_centralizer hZcen
  have hPX : P ⊔ X = Λ := by
    refine le_antisymm (sup_le (hPPt.trans hPtΛ) hXΛ) ?_
    intro l hl
    have hlN : l ∈ N := hΛN hl
    have h1 : π ⟨l, hlN⟩ ∈ Ph ⊔ (X.subgroupOf N).map π := by
      rw [hPhX]
      exact hmem_img Λ ⟨l, hlN⟩ hl
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Ph _
      (fun g _ => mem_normalizer_of_normal _ g)] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 h1
    obtain ⟨na, rfl⟩ := hπ a
    obtain ⟨ξ, hξ, rfl⟩ := hb
    have hz : ((ξ⁻¹ * na⁻¹ * ⟨l, hlN⟩ : N) : G) ∈ Z := by
      rw [← hπ1, map_mul, map_mul, map_inv, map_inv, ← hab]
      group
    have hnaP : (na : G) ∈ P ⊔ Z := hPtPZ ((hmemPt na).2 ha)
    have e : l = (na : G) * ξ * ((ξ⁻¹ * na⁻¹ * ⟨l, hlN⟩ : N) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    refine mul_mem (mul_mem ((sup_le_sup_left hZX P) hnaP)
      (mem_sup_right (mem_subgroupOf.1 hξ))) (mem_sup_right (hZX hz))
  have hPtt : ⁅Pt, Pt.map (MulAut.conj t).toMonoidHom⁆ ≤ Z := by
    rw [commutator_le]
    rintro _ ⟨n, hn, rfl⟩ _ ⟨_, ⟨n', hn', rfl⟩, rfl⟩
    have hc : ⁅π n, σ (π n')⁆ = 1 := by
      have : ⁅π n, σ (π n')⁆ ∈ ⁅Ph, Ph.map σ.toMonoidHom⁆ :=
        commutator_mem_commutator hn ⟨π n', hn', rfl⟩
      rwa [hPhσ, mem_bot] at this
    rw [hσπ, ← map_commutatorElement, hπ1] at hc
    have e : ((⁅n, τ n'⁆ : N) : G) = ⁅(n : G), t * (n' : G) * t⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ]
    show ⁅(n : G), t * (n' : G) * t⁻¹⁆ ∈ Z
    rw [← e]
    exact hc
  have hPPt' : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ ≤ Z :=
    (commutator_mono hPPt (map_mono hPPt)).trans hPtt
  have hcen' : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ ≤ centralizer (P : Set G) :=
    hPPt'.trans (hZC.trans (centralizer_le (SetLike.coe_subset_coe.2 hPN)))
  have h1 : ⁅⁅P, P.map (MulAut.conj t).toMonoidHom⁆, P⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 hcen'
  have h2 : ⁅⁅P.map (MulAut.conj t).toMonoidHom, P⁆, P⁆ = ⊥ := by
    rw [commutator_comm (P.map (MulAut.conj t).toMonoidHom) P]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hPperf] at h3
  have hmax : ∀ R : Subgroup G, R ≤ Λ → ⁅R, R⁆ = R → R ≤ P := by
    intro R hRΛ hRperf
    have hRN : R ≤ N := hRΛ.trans hΛN
    have hRh : (R.subgroupOf N).map π ≤ Ph := by
      refine hPhmax _ (map_mono fun x hx => mem_subgroupOf.2 (hRΛ (mem_subgroupOf.1 hx))) ?_
      rw [← map_subgroupOf_commutator π hRN hRN, hRperf]
    have hRPt : R ≤ Pt := fun x hx =>
      (hmemPt ⟨x, hRN hx⟩).2 (hRh (hmem_img R ⟨x, hRN hx⟩ hx))
    calc R = ⁅R, R⁆ := hRperf.symm
      _ ≤ P := commutator_mono hRPt hRPt
  exact ⟨P, hPPt.trans hPtΛ, hPperf, hPX, h3, hmax⟩

end CFSG.LocalAnalysis.EvenBN.Common
