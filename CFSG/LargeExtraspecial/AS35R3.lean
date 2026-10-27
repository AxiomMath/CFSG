module

public import CFSG.LargeExtraspecial.AS35Fis
public import CFSG.LargeExtraspecial.AS35R3Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

namespace AS35R3

variable {X : Type} [Group X] {E : Set X}

theorem not_tripleProperty_of_twin {a y b : X} (ha : a ∈ E) (hy : y ∈ E) (hb : b ∈ E)
    (ha2 : a * a = 1) (hay : a ≠ y) (hcomm : a * y = y * a)
    (htwin : ∀ w ∈ E, w * a = a * w ↔ w * y = y * w) (hab : a * b ≠ b * a) :
    ¬ TripleProperty E := by
  intro hT
  have hby : b * y ≠ y * b := fun h => hab ((htwin b hb).2 h).symm
  have hmem : y ∈ ySet E a b := by
    refine ⟨hy, fun s hs => ⟨hs.1.1, ?_, (htwin s hs.1.1).1 hs.1.2.2⟩⟩
    rintro rfl
    exact hby hs.2.2.2.symm
  rcases hT a b ha hb hab hmem with h | h | h
  · exact hay h.symm
  · rw [h] at hcomm
    exact hab hcomm
  · rw [Set.mem_singleton_iff] at h
    rw [h] at hcomm
    apply hab
    have e1 : a * (a * b * a) = b * a := by rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
    have e2 : a * b * a * a = a * b := by rw [mul_assoc, ha2, mul_one]
    rw [e1, e2] at hcomm
    exact hcomm.symm

theorem not_tripleProperty_of_hasNormalPSubgroup (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : HasNormalPSubgroup 2 X) : ¬ TripleProperty E := by
  obtain ⟨x, y, hxy, hne⟩ := Pair.exists_isTwin_ne hP hZ h2
  obtain ⟨b, hb, hxb⟩ := O2Twin.exists_not_commute_of_mem hP hZ hxy.1
  exact not_tripleProperty_of_twin hxy.1 hxy.2.1 hb (Pair.mul_self hP hxy.1) hne hxy.2.2.1
    hxy.2.2.2 hxb

theorem eq_one_or_eq_of_mem (hP : Pair X E) (hZ : center X = ⊥)
    (hS : IsSimpleGroup (_root_.commutator X)) (hna : ∃ a b : _root_.commutator X, a * b ≠ b * a)
    (hT : TripleProperty E) {d : X} (hd : d ∈ E)
    (hL : ¬ HasNormalPSubgroup 2 (LocalQuotient E d)) {P : Subgroup X}
    (hPC : P ≤ centralizer {d}) (hPn : ∀ c ∈ centralizer {d}, ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) {y : X} (hy : y ∈ P) : y = 1 ∨ y = d := by
  have hLC : LocalGroup E d ≤ centralizer {d} := by
    rw [LocalGroup, closure_le]
    intro f hf
    exact mem_centralizer_singleton_iff.mpr hf.2.2
  have hNn : ((P ⊓ LocalGroup E d).subgroupOf (LocalGroup E d)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro x l hx hl
    exact Subgroup.mem_inf.mpr ⟨hPn l (hLC hl) x hx.1, (LocalGroup E d).mul_mem
      ((LocalGroup E d).mul_mem hl hx.2) ((LocalGroup E d).inv_mem hl)⟩
  have hN2 : IsPGroup 2 ((P ⊓ LocalGroup E d).subgroupOf (LocalGroup E d)) := fun x => by
    obtain ⟨k, hk⟩ := hP2 ⟨((x : LocalGroup E d) : X), x.2.1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hbar : ((P ⊓ LocalGroup E d).subgroupOf (LocalGroup E d)).map
      (QuotientGroup.mk' (center (LocalGroup E d))) = ⊥ := by
    by_contra hne
    exact hL ⟨_, hNn.map _ (QuotientGroup.mk'_surjective _), hne, hN2.map _⟩
  have hcen : ∀ x : LocalGroup E d, (x : X) ∈ P → x ∈ center (LocalGroup E d) := by
    intro x hx
    have hm : QuotientGroup.mk' (center (LocalGroup E d)) x ∈
        ((P ⊓ LocalGroup E d).subgroupOf (LocalGroup E d)).map
          (QuotientGroup.mk' (center (LocalGroup E d))) := mem_map_of_mem _ ⟨hx, x.2⟩
    rw [hbar, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
    exact hm
  have hyd : y * d = d * y := mem_centralizer_singleton_iff.mp (hPC hy)
  refine Pair.eq_one_or_eq_of_centralizes hP hZ hS hna hT hd hyd fun f hf => ?_
  have hfd : f * d = d * f := hf.2.2
  have hf' : y * f * y⁻¹ ∈ LocalClass E d := by
    refine ⟨Pair.conj_mem hP hf.1 y, fun h => hf.2.1 ?_, ?_⟩
    · calc f = y⁻¹ * (y * f * y⁻¹) * y := by group
        _ = d := by rw [h, mul_assoc, ← hyd, ← mul_assoc, inv_mul_cancel, one_mul]
    · calc y * f * y⁻¹ * d = y * f * (y⁻¹ * d) := by group
        _ = y * f * (d * y⁻¹) := by
          rw [show y⁻¹ * d = d * y⁻¹ by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hyd, mul_assoc, mul_inv_cancel, mul_one]]
        _ = y * (f * d) * y⁻¹ := by group
        _ = y * (d * f) * y⁻¹ := by rw [hfd]
        _ = (y * d) * f * y⁻¹ := by group
        _ = d * (y * f * y⁻¹) := by rw [hyd]; group
  have hmemP : f⁻¹ * (y * f * y⁻¹) ∈ P := by
    have h1 : f⁻¹ * y * f⁻¹⁻¹ ∈ P := hPn f⁻¹ (inv_mem (hLC (mem_localGroup hf))) y hy
    rw [inv_inv] at h1
    have h2 : f⁻¹ * y * f * y⁻¹ ∈ P := mul_mem h1 (inv_mem hy)
    simpa [mul_assoc] using h2
  have heq : starImage E d ⟨f, hf⟩ = starImage E d ⟨_, hf'⟩ := by
    rw [starImage, starImage, QuotientGroup.eq]
    exact hcen _ hmemP
  have h : f = y * f * y⁻¹ :=
    congrArg Subtype.val (Pair.starImage_injective_of_simple hP hZ hS hd heq)
  calc y * f = y * f * y⁻¹ * y := by group
    _ = f * y := by rw [← h]

end AS35R3

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem false_of_case5 [IsSimpleGroup G] (hn : 3 ≤ S.width) {m : ℕ} (hm : 5 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmodel : fischerCentralQuotientModel {g : G | IsConj S.z g}
      (closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff _).1 hmodel
  obtain ⟨v, hv, hvd⟩ := mem_D3_iff.1 ((hψ S.z).1 (IsConj.refl _))
  rcases Nat.lt_or_ge m 6 with h6 | h6
  ·
    obtain rfl : m = 5 := by omega
    have hQ : 2 ^ 7 ∣ Nat.card G := by
      have h1 : Nat.card S.QG ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
      rw [Setting.QG, Subgroup.card_map_of_injective S.M.subtype_injective, S.card_Q_eq] at h1
      exact (pow_dvd_pow 2 (by omega)).trans h1
    have : IsSimpleGroup (R3 f) := ψ.symm.isSimpleGroup
    have hna : ∃ a b : R3 f, a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
      exact ⟨ψ x, ψ y, fun h => hxy (ψ.injective (by rw [map_mul, map_mul, h]))⟩
    have hG := AS35R3.card_R3_dvd_of_isSimpleGroup hf hna
    rw [← Nat.card_congr ψ.toEquiv] at hG
    have := hQ.trans hG
    norm_num at this
  ·
    have hP := pair_R3 hf (by omega)
    have hZ := center_R3_eq_bot hf (by omega)
    have : IsSimpleGroup (_root_.commutator G) := S.isSimpleGroup_commutator
    have hS : IsSimpleGroup (_root_.commutator (R3 f)) :=
      Recognition.R3.isSimpleGroup_commutator_of_mulEquiv ψ
    have hcomm : _root_.commutator (R3 f) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective, ← S.commutator_eq_top,
        _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ ψ.surjective]
    have hna : ∃ a b : _root_.commutator (R3 f), a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := S.exists_mul_ne_mul
      refine ⟨⟨ψ x, hcomm ▸ mem_top _⟩, ⟨ψ y, hcomm ▸ mem_top _⟩, fun h => hxy (ψ.injective ?_)⟩
      have h' := congrArg Subtype.val h
      simpa only [Subgroup.coe_mul, map_mul] using h'
    have hL : ¬ HasNormalPSubgroup 2 (LocalQuotient (D3 f) (reflBar f v)) := by
      rintro ⟨N, hNn, hN1, hN2⟩
      obtain ⟨f', hf', -, Φ, -⟩ := exists_localQuotient_equiv hf (by omega) hv
      refine AS35R3.not_tripleProperty_of_hasNormalPSubgroup (pair_R3 hf' (by omega))
        (center_R3_eq_bot hf' (by omega))
        ⟨N.map Φ.toMonoidHom, hNn.map _ Φ.surjective, fun h => hN1 ?_, hN2.map _⟩
        (tripleProperty_D3 hf' (by omega))
      rwa [Subgroup.map_eq_bot_iff_of_injective _ Φ.injective] at h
    set S' := S.map ψ
    have hd : reflBar f v ∈ D3 f := mem_D3_iff.2 ⟨v, hv, rfl⟩
    have hP2 : IsPGroup 2 S'.QG := fun g =>
      ⟨2, Subtype.ext (by simpa using S'.pow_four_eq_one g.2)⟩
    have key : ∀ w ∈ S'.QG, w = 1 ∨ w = ψ S.z := fun w hw => by
      have h := AS35R3.eq_one_or_eq_of_mem hP hZ hS hna (tripleProperty_D3 hf hm) hd hL
        (P := S'.QG) (by rw [hvd]; exact S'.QG_le_M) (fun c hc x hx => by
          rw [hvd] at hc
          exact S'.conj_mem_QG hc hx) hP2 hw
      rwa [hvd] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := S'.exists_mem_QG_mul_ne
    rcases key x hx with rfl | rfl <;> rcases key y hy with rfl | rfl <;> simp at hxy

end Setting

end CFSG.LargeExtraspecial
