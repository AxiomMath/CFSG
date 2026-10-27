module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem characteristic_of_forall_mem {H : Subgroup G} (h : ∀ φ : MulAut G, ∀ x ∈ H, φ x ∈ H) :
    H.Characteristic :=
  characteristic_iff_le_comap.2 fun φ x hx => h φ x hx

theorem char_apply_mem {H : Subgroup G} (hH : H.Characteristic) (φ : MulAut G) {x : G}
    (hx : x ∈ H) : φ x ∈ H :=
  characteristic_iff_le_comap.1 hH φ hx

theorem characteristic_centralizer (K : Subgroup G) [hK : K.Characteristic] :
    (centralizer (K : Set G)).Characteristic := by
  refine characteristic_of_forall_mem fun φ x hx => mem_centralizer_iff.2 fun k hk => ?_
  have hk' : φ.symm k ∈ K := char_apply_mem hK φ.symm hk
  have h := mem_centralizer_iff.1 hx _ hk'
  calc k * φ x = φ (φ.symm k * x) := by simp
    _ = φ (x * φ.symm k) := by rw [h]
    _ = φ x * k := by simp

theorem characteristic_inf (H K : Subgroup G) [hH : H.Characteristic] [hK : K.Characteristic] :
    (H ⊓ K).Characteristic :=
  characteristic_of_forall_mem fun φ _ hx => ⟨char_apply_mem hH φ hx.1, char_apply_mem hK φ hx.2⟩

theorem characteristic_sup (H K : Subgroup G) [hH : H.Characteristic] [hK : K.Characteristic] :
    (H ⊔ K).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro φ
  rw [Subgroup.map_sup, characteristic_iff_map_eq.1 hH, characteristic_iff_map_eq.1 hK]

theorem mk_mem_center_iff {N : Subgroup G} [N.Normal] {x : G} :
    (x : G ⧸ N) ∈ center (G ⧸ N) ↔ ∀ g : G, ⁅x, g⁆ ∈ N := by
  have key : ∀ g : G, ⁅x, g⁆ ∈ N ↔ (g : G ⧸ N) * x = x * g := by
    intro g
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' N ⁅x, g⁆ = 1 ↔ _
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, eq_comm]
    rfl
  rw [mem_center_iff]
  refine ⟨fun h g => (key g).2 (h g), fun h g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact (key g).1 (h g)

theorem commutatorElement_mem_swap {N : Subgroup G} {x g : G} (h : ⁅g, x⁆ ∈ N) :
    ⁅x, g⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact inv_mem h

@[expose] def centralTorsionMod (N C : Subgroup G) [N.Normal] (hNC : N ≤ centralizer (C : Set G))
    (p : ℕ) : Subgroup G where
  carrier := {x | x ∈ C ∧ (∀ g : G, ⁅x, g⁆ ∈ N) ∧ x ^ p ∈ N}
  mul_mem' := by
    rintro x y ⟨hxC, hxN, hxp⟩ ⟨hyC, hyN, hyp⟩
    refine ⟨mul_mem hxC hyC, fun g => ?_, ?_⟩
    · have e : ⁅x * y, g⁆ = x * ⁅y, g⁆ * x⁻¹ * ⁅x, g⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem (Normal.conj_mem inferInstance _ (hyN g) x) (hxN g)
    · have hc : ⁅y, x⁆ ∈ N := hyN x
      have hcx : Commute x ⁅y, x⁆ := mem_centralizer_iff.1 (hNC hc) x hxC
      have hcy : Commute y ⁅y, x⁆ := mem_centralizer_iff.1 (hNC hc) y hyC
      rw [mul_pow_eq_of_commute hcx hcy]
      exact mul_mem (mul_mem hxp hyp) (pow_mem hc _)
  one_mem' := ⟨one_mem C, fun g => by rw [commutatorElement_one_left]; exact one_mem N, by
    rw [one_pow]; exact one_mem N⟩
  inv_mem' := by
    rintro x ⟨hxC, hxN, hxp⟩
    refine ⟨inv_mem hxC, fun g => ?_, by rw [inv_pow]; exact inv_mem hxp⟩
    rw [commutatorElement_inv_left]
    have h := Normal.conj_mem inferInstance _ (commutatorElement_mem_swap (hxN g)) x⁻¹
    rwa [inv_inv] at h

theorem mem_centralTorsionMod {N C : Subgroup G} [N.Normal] {hNC : N ≤ centralizer (C : Set G)}
    {p : ℕ} {x : G} :
    x ∈ centralTorsionMod N C hNC p ↔ x ∈ C ∧ (∀ g : G, ⁅x, g⁆ ∈ N) ∧ x ^ p ∈ N :=
  Iff.rfl

end General

@[expose] def IsThompsonCritical {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  C.Characteristic ∧ (frattini C).map C.subtype ≤ C ⊓ centralizer (C : Set G) ∧
    ⁅(⊤ : Subgroup G), C⁆ ≤ C ⊓ centralizer (C : Set G) ∧
      centralizer (C : Set G) = C ⊓ centralizer (C : Set G)

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

theorem thompson_critical_subgroup (hP : IsPGroup p P) :
    (∃ C : Subgroup P, IsThompsonCritical C) ∧
      ∀ C : Subgroup P, IsThompsonCritical C → Nontrivial P → C ≠ ⊥ := by
  refine ⟨?_, ?_⟩
  swap
  · rintro C ⟨-, -, -, hcen⟩ hnt rfl
    obtain ⟨g, hg⟩ := exists_ne (1 : P)
    have hgc : g ∈ centralizer ((⊥ : Subgroup P) : Set P) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [SetLike.mem_coe, mem_bot] at hh
      rw [hh, one_mul, mul_one]
    rw [hcen] at hgc
    exact hg (mem_bot.1 hgc.1)
  let S : Set (Subgroup P) := {K | K.Characteristic ∧
    (frattini K).map K.subtype ≤ K ⊓ centralizer (K : Set P) ∧
      ⁅(⊤ : Subgroup P), K⁆ ≤ K ⊓ centralizer (K : Set P)}
  have hbot : (⊥ : Subgroup P) ∈ S := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := mem_map.1 hx
      have := y.2
      rw [mem_bot] at this
      rw [subtype_apply, this]
      exact one_mem _
    · rw [commutator_bot_right]
      exact bot_le
  obtain ⟨K, hKmax⟩ := S.toFinite.exists_maximal ⟨⊥, hbot⟩
  obtain ⟨hKc, hKΦ, hKcomm⟩ := hKmax.prop
  refine ⟨K, hKc, hKΦ, hKcomm, ?_⟩
  by_contra hne
  set C₀ := centralizer (K : Set P) with hC₀def
  set Z := K ⊓ C₀ with hZdef
  have : C₀.Characteristic := characteristic_centralizer K
  have : Z.Characteristic := characteristic_inf K C₀
  have hZC₀ : Z ≤ C₀ := inf_le_right
  have hlt : Z < C₀ := lt_of_le_of_ne hZC₀ fun h => hne h.symm
  obtain ⟨b, hbC₀, hbZ, hbp, B, -, -, -, hbB, -, hBcomm⟩ := exists_central_extension hP hlt
  have hZcen : Z ≤ centralizer (C₀ : Set P) := by
    rw [le_centralizer_iff]
    exact centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)
  set X := centralTorsionMod Z C₀ hZcen p with hXdef
  have hXchar : X.Characteristic := by
    refine characteristic_of_forall_mem fun φ x hx => ?_
    obtain ⟨hxC, hxN, hxp⟩ := mem_centralTorsionMod.1 hx
    refine mem_centralTorsionMod.2 ⟨char_apply_mem inferInstance φ hxC, fun g => ?_, ?_⟩
    · have h := char_apply_mem (inferInstance : Z.Characteristic) φ (hxN (φ.symm g))
      rwa [map_commutatorElement, MulEquiv.apply_symm_apply] at h
    · rw [← map_pow]
      exact char_apply_mem inferInstance φ hxp
  have hbX : b ∈ X := mem_centralTorsionMod.2 ⟨hbC₀, hBcomm b hbB, hbp⟩
  have hKcen : ∀ k ∈ K, ∀ g : P, ⁅k, g⁆ ∈ Z := fun k hk g =>
    commutatorElement_mem_swap (hKcomm (commutator_mem_commutator (mem_top g) hk))
  have hKpow : ∀ k ∈ K, k ^ p ∈ Z := fun k hk =>
    hKΦ (mem_map_of_mem K.subtype (pow_mem_frattini (hP.to_subgroup K) ⟨k, hk⟩))
  let T : Subgroup (P ⧸ Z) :=
    { carrier := {a | a ∈ center (P ⧸ Z) ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (mem_center_iff.1 hb.1 a), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemT : ∀ x : P, (∀ g : P, ⁅x, g⁆ ∈ Z) → x ^ p ∈ Z → (x : P ⧸ Z) ∈ T := fun x h1 h2 =>
    ⟨mk_mem_center_iff.2 h1, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact h2⟩
  set H := K ⊔ X with hHdef
  have hHT : H.map (QuotientGroup.mk' Z) ≤ T := by
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨k, hk, rfl⟩
      exact hmemT k (hKcen k hk) (hKpow k hk)
    · rintro _ ⟨x, hx, rfl⟩
      exact hmemT x (mem_centralTorsionMod.1 hx).2.1 (mem_centralTorsionMod.1 hx).2.2
  have hHmod : ∀ h ∈ H, (∀ g : P, ⁅h, g⁆ ∈ Z) ∧ h ^ p ∈ Z := by
    intro h hh
    have hT := hHT (mem_map_of_mem _ hh)
    refine ⟨mk_mem_center_iff.1 hT.1, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hT.2
  have : H.Characteristic := characteristic_sup K X
  have hZH : Z ≤ H ⊓ centralizer (H : Set P) := by
    refine le_inf (inf_le_left.trans le_sup_left) ?_
    rw [le_centralizer_iff, sup_le_iff]
    refine ⟨le_centralizer_iff.1 hZC₀, ?_⟩
    exact (show X ≤ C₀ from fun x hx => (mem_centralTorsionMod.1 hx).1).trans
      (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))
  have hHS : H ∈ S := by
    refine ⟨inferInstance, ?_, ?_⟩
    · have hΦ : frattini H ≤ Z.subgroupOf H :=
        frattini_le_of_commutator_pow_mem (p := p) (Z.subgroupOf H)
          (fun a b => (hHmod a a.2).1 b) (fun a => by
            rw [mem_subgroupOf, coe_pow]
            exact (hHmod a a.2).2)
      refine (map_mono hΦ).trans ?_
      rw [subgroupOf_map_subtype]
      exact inf_le_left.trans hZH
    · rw [commutator_le]
      intro g _ h hh
      exact hZH (commutatorElement_mem_swap ((hHmod h hh).1 g))
  have hHK : H ≤ K := hKmax.2 hHS le_sup_left
  have hbK : b ∈ K := hHK (mem_sup_right hbX)
  exact hbZ ⟨hbK, hbC₀⟩

end CFSG.SectionRank.Ccomm
