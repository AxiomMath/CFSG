module

public import CFSG.GH74.Uniqueness.Section13Dict
public import CFSG.GH74.Uniqueness.Section12Center
public import CFSG.GH74.Uniqueness.Bender.Unitary36d
public import CFSG.GH74.Uniqueness.Bender.Unitary

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

section Perfect

theorem A6.commutator_eq_top_of_psl2 {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (φ : G ≃* Theory.Comparator.PSL2Model n) : commutator G = ⊤ := by
  have hB : Bender.BenderType G n 1 1 := .linear n hn φ
  have : IsSimpleGroup G := hB.isSimple
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator G) with h | h
  · exfalso
    apply hB.isSimpleBenderGroup.not_commutative
    intro x y
    have h1 : (⊤ : Subgroup G) ≤ centralizer ((⊤ : Subgroup G) : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp h
    exact mem_centralizer_iff.mp (h1 (mem_top y)) x (mem_top x)
  · exact h

theorem A6.commutator_self_eq_of_psl2 {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    {I : Subgroup G} (φ : ↥I ≃* Theory.Comparator.PSL2Model n) : ⁅I, I⁆ = I := by
  have h1 := A6.commutator_eq_top_of_psl2 hn φ
  have h2 : (commutator ↥I).map I.subtype = ⁅I, I⁆ := by
    change (⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ : Subgroup ↥I).map I.subtype = ⁅I, I⁆
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem A6.commutatorElement_mul_central {G : Type*} [Group G] (x y : G) {c d : G}
    (hc : c ∈ center G) (hd : d ∈ center G) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' := mem_center_iff.mp hc
  have hd' := mem_center_iff.mp hd
  rw [commutatorElement_def, commutatorElement_def]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹ = x * (c * y) * (d * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        group
    _ = x * (y * c) * (c⁻¹ * d) * x⁻¹ * d⁻¹ * y⁻¹ := by
        rw [← hc' y, ← mem_center_iff.mp (inv_mem hc) d]
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [← hd' x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Perfect

theorem A6.exists_psl2_centralized
    {X : Type} [Group X] [Finite X] {F Y E : Subgroup X} {n e : ℕ}
    (hB : Bender.BenderType (↥F ⧸ center ↥F) n 3 e) (hodd : Odd (Nat.card (center ↥F)))
    (hYN : Y ≤ normalizer (F : Set X)) (hYodd : Odd (Nat.card Y))
    (hEF : E ≤ F) (hE : ∀ x ∈ E, x * x = 1) (hEcard : Nat.card E = 2 ^ n)
    (hYE : ∀ a ∈ Y, ∀ x ∈ E, a * x = x * a) :
    ∃ W : Subgroup X, W ≤ F ∧ E ≤ W ∧ (∀ a ∈ Y, ∀ w ∈ W, a * w = w * a) ∧
      Nonempty (↥W ≃* Theory.Comparator.PSL2Model n) := by
  classical
  have hn : 2 ≤ n := by
    rcases hB.cases' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, hn⟩
    · omega
    · omega
    · exact hn
  set π := QuotientGroup.mk' (center ↥F) with hπ
  set Eb : Subgroup (↥F ⧸ center ↥F) := (E.subgroupOf F).map π with hEb
  have hEbsq : ∀ x ∈ Eb, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hE _ hx), map_one]
  obtain ⟨P, hEP⟩ := (Bender.isPGroup_two_of_mul_self_eq_one hEbsq).exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore P
  have hinjE : ∀ x ∈ E.subgroupOf F, π x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ center ↥F := (QuotientGroup.eq_one_iff _).mp hx1
    have hx2 : x ^ 2 ^ 1 = 1 := Subtype.ext (by rw [pow_one, sq]; exact hE _ hx)
    exact (A6.eq_of_inv_mul_mem_two hodd le_rfl hx2 (one_pow (2 ^ 0))
      (by rw [mul_one]; exact inv_mem hxc))
  have hEZ : Eb = Bender.rootCenter (P : Subgroup (↥F ⧸ center ↥F)) := by
    apply Subgroup.eq_of_le_of_card_ge (hc.elemAbelian_le_rootCenter hEP hEbsq)
    rw [hc.card_center, hEb, A6.card_map_of_ker π _ hinjE, A6.card_subgroupOf hEF, hEcard]
  set N := normalizer (F : Set X) with hN
  set Yb : Subgroup (MulAut (↥F ⧸ center ↥F)) := (Y.subgroupOf N).map (A6.barHom F) with hYb
  have hYbodd : Odd (Nat.card Yb) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd (H := Y.subgroupOf N) (A6.barHom F))
    rw [A6.card_subgroupOf hYN]
    exact hYodd
  have hYbC : Yb ≤ Bender.autCentralizer (Bender.rootCenter (P : Subgroup (↥F ⧸ center ↥F))) := by
    rintro _ ⟨a, ha, rfl⟩ z hz
    rw [← hEZ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have ha' : (a : X) ∈ Y := ha
    have hx' : (x : X) ∈ E := hx
    have hax : (a : X) * x * (a : X)⁻¹ = x := by
      rw [hYE a ha' x hx', mul_inv_cancel_right]
    rw [A6.barHom_mk]
    congr 1
    exact Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; exact hax)
  obtain ⟨t', I, D₃, -, -, ⟨φI⟩, hZI, -, -, -, -, -, -, -, -, -, -, hCA⟩ :=
    hB.lemma_3_6_d_unitary P
  obtain ⟨Ib, ⟨φb⟩, hZIb, hfixIb⟩ : ∃ Ib : Subgroup (↥F ⧸ center ↥F),
      Nonempty (↥Ib ≃* Theory.Comparator.PSL2Model n) ∧
      Bender.rootCenter (P : Subgroup (↥F ⧸ center ↥F)) ≤ Ib ∧ ∀ σ ∈ Yb, ∀ k ∈ Ib, σ k = k := by
    by_cases hbot : Yb = ⊥
    · refine ⟨I, ⟨φI⟩, hZI, fun σ hσ k _ => ?_⟩
      rw [hbot, Subgroup.mem_bot] at hσ
      rw [hσ, MulAut.one_apply]
    · obtain ⟨ρ, hρ, hρk⟩ := hCA Yb hYbC hYbodd hbot
      refine ⟨I.map (MulAut.conj ρ⁻¹).toMonoidHom,
        ⟨(I.equivMapOfInjective _ (MulAut.conj ρ⁻¹).injective).symm.trans φI⟩, ?_, ?_⟩
      · intro z hz
        have hzc : ρ * z * ρ⁻¹ = z := by
          rw [(Bender.mem_rootCenter_iff.mp hz).2 ρ hρ, mul_inv_cancel_right]
        refine ⟨z, hZI hz, ?_⟩
        change ρ⁻¹ * z * ρ⁻¹⁻¹ = z
        rw [inv_inv]
        calc ρ⁻¹ * z * ρ = ρ⁻¹ * (ρ * z * ρ⁻¹) * ρ := by rw [hzc]
          _ = z := by group
      · rintro σ hσ _ ⟨i, hi, rfl⟩
        refine (hρk ((MulAut.conj ρ⁻¹).toMonoidHom i)).mpr ?_ σ hσ
        change ρ * (ρ⁻¹ * i * ρ⁻¹⁻¹) * ρ⁻¹ ∈ _
        rw [inv_inv, show ρ * (ρ⁻¹ * i * ρ) * ρ⁻¹ = i by group]
        exact mem_sup_right hi
  set W₀ : Subgroup ↥F := Ib.comap π with hW₀
  set W₁ : Subgroup ↥F := ⁅W₀, W₀⁆ with hW₁
  have hπW₀ : W₀.map π = Ib :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Ib
  have hπW₁ : W₁.map π = Ib := by
    rw [hW₁, Subgroup.map_commutator, hπW₀]
    exact A6.commutator_self_eq_of_psl2 hn φb
  have hW₁Z : ∀ w ∈ W₁, w ∈ center ↥F → w = 1 := by
    set R : Subgroup ↥W₀ := (center ↥F).subgroupOf W₀ with hR
    have hRc : R ≤ center ↥W₀ := by
      intro r hr
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hr g)
    have : R.Normal := Subgroup.normal_of_le_center hRc
    have hcW₀ : center ↥F ≤ W₀ := by
      intro z hz
      change π z ∈ Ib
      have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      rw [h1]
      exact Ib.one_mem
    have hRodd : Odd (Nat.card R) := by
      rw [hR, A6.card_subgroupOf hcW₀]
      exact hodd
    let π₀ : ↥W₀ →* ↥Ib := (π.comp W₀.subtype).codRestrict Ib (fun w => w.2)
    have hπ₀s : Function.Surjective π₀ := by
      rintro ⟨k, hk⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) k
      exact ⟨⟨g, hk⟩, rfl⟩
    have hker : π₀.ker = R := by
      ext w
      rw [MonoidHom.mem_ker, hR, mem_subgroupOf]
      constructor
      · intro h1
        have h2 : π (w : ↥F) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    let ψ : ↥W₀ ⧸ R ≃* ↥Ib := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π₀ hπ₀s)
    have hBI : Bender.BenderType ↥Ib n 1 1 := .linear n hn φb
    have hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Q : Sylow p (↥W₀ ⧸ R),
        IsCyclic (Q : Subgroup (↥W₀ ⧸ R)) := by
      intro p hp hp2 Q
      have : Fact p.Prime := ⟨hp⟩
      have h1 := hBI.isCyclic_sylow_of_odd (Or.inl rfl) hp2
        (Q.mapSurjective (f := ψ.toMonoidHom) ψ.surjective)
      have h2 : IsCyclic ↥((Q : Subgroup (↥W₀ ⧸ R)).map ψ.toMonoidHom) := h1
      exact ((Q : Subgroup (↥W₀ ⧸ R)).equivMapOfInjective ψ.toMonoidHom ψ.injective).isCyclic.mpr h2
    have hint := inf_commutator_eq_bot_of_odd_central hRc hRodd hcyc
    intro w hw hwc
    have hW₁eq : W₁ = (commutator ↥W₀).map W₀.subtype := by
      change ⁅W₀, W₀⁆ = (⁅(⊤ : Subgroup ↥W₀), (⊤ : Subgroup ↥W₀)⁆ : Subgroup ↥W₀).map W₀.subtype
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hW₁eq] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h1 : w' ∈ R ⊓ commutator ↥W₀ := ⟨hwc, hw'⟩
    rw [hint, mem_bot] at h1
    rw [h1, map_one]
  refine ⟨W₁.map F.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxF := hEF hx
    have hxI : π ⟨x, hxF⟩ ∈ Ib := hZIb (hEZ ▸ ⟨⟨x, hxF⟩, hx, rfl⟩)
    rw [← hπW₁] at hxI
    obtain ⟨w, hw, hwx⟩ := hxI
    set ζ : ↥F := w⁻¹ * ⟨x, hxF⟩ with hζ
    have hζc : ζ ∈ center ↥F := QuotientGroup.eq.mp hwx
    have hxw : (⟨x, hxF⟩ : ↥F) = w * ζ := by rw [hζ, mul_inv_cancel_left]
    have hxx : (⟨x, hxF⟩ : ↥F) * ⟨x, hxF⟩ = 1 := Subtype.ext (hE x hx)
    have hcomm : ∀ g : ↥F, g * ζ = ζ * g := mem_center_iff.mp hζc
    have hsq : (w * w) * (ζ * ζ) = 1 := by
      rw [← hxx, hxw]
      calc w * w * (ζ * ζ) = w * (w * ζ) * ζ := by group
        _ = w * (ζ * w) * ζ := by rw [hcomm w]
        _ = w * ζ * (w * ζ) := by group
    have hww : w * w ∈ center ↥F := by
      have : w * w = (ζ * ζ)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact inv_mem (mul_mem hζc hζc)
    have hw1 : w * w = 1 := hW₁Z _ (mul_mem hw hw) hww
    have hζζ : ζ * ζ = 1 := by rwa [hw1, one_mul] at hsq
    have hζ2 : ζ ^ 2 ^ 1 = 1 := by rw [pow_one, sq]; exact hζζ
    have hζ1 : (1 : ↥F) = ζ := A6.eq_of_inv_mul_mem_two hodd le_rfl (one_pow (2 ^ 0)) hζ2
      (by rw [inv_one, one_mul]; exact hζc)
    refine ⟨w, hw, ?_⟩
    have : (⟨x, hxF⟩ : ↥F) = w := by rw [hxw, ← hζ1, mul_one]
    rw [← this]
    rfl
  ·
    rintro a ha _ ⟨w, hw, rfl⟩
    have haN : a ∈ N := hYN ha
    set σ : MulAut ↥F := F.normalizerMonoidHom ⟨a, haN⟩ with hσ
    have hσv : ∀ g : ↥F, ((σ g : ↥F) : X) = a * g * a⁻¹ := fun g =>
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    have hcen : ∀ g ∈ W₀, g⁻¹ * σ g ∈ center ↥F := by
      intro g hg
      have h1 : A6.barHom F ⟨a, haN⟩ (π g) = π g :=
        hfixIb _ ⟨⟨a, haN⟩, ha, rfl⟩ (π g) hg
      rw [A6.barHom_mk] at h1
      exact QuotientGroup.eq.mp h1.symm
    have hWC : W₁ ≤ (centralizer ({a} : Set X)).subgroupOf F := by
      rw [hW₁, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have h1 : σ ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆ := by
        rw [map_commutatorElement]
        have e1 : σ g₁ = g₁ * (g₁⁻¹ * σ g₁) := by rw [mul_inv_cancel_left]
        have e2 : σ g₂ = g₂ * (g₂⁻¹ * σ g₂) := by rw [mul_inv_cancel_left]
        rw [e1, e2]
        exact A6.commutatorElement_mul_central g₁ g₂ (hcen g₁ hg₁) (hcen g₂ hg₂)
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      have h2 := congrArg Subtype.val h1
      rw [hσv] at h2
      calc ((⁅g₁, g₂⁆ : ↥F) : X) * a = (a * ⁅g₁, g₂⁆ * a⁻¹) * a := by rw [h2]
        _ = a * ⁅g₁, g₂⁆ := by group
    have h3 := mem_centralizer_singleton_iff.mp (hWC hw)
    exact h3.symm
  ·
    have hinj : Function.Injective (π.comp W₁.subtype) := by
      rw [injective_iff_map_eq_one]
      intro w hw1
      exact Subtype.ext (hW₁Z w w.2 ((QuotientGroup.eq_one_iff _).mp hw1))
    let f : ↥W₁ →* ↥Ib := (π.comp W₁.subtype).codRestrict Ib (fun w => by
      rw [← hπW₁]
      exact ⟨w, w.2, rfl⟩)
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), ?_⟩
      rintro ⟨k, hk⟩
      rw [← hπW₁] at hk
      obtain ⟨w, hw, rfl⟩ := hk
      exact ⟨⟨w, hw⟩, rfl⟩
    exact ⟨((W₁.equivMapOfInjective F.subtype F.subtype_injective).symm.trans
      (MulEquiv.ofBijective f hf)).trans φb⟩

end CFSG.GH74.Uniqueness
