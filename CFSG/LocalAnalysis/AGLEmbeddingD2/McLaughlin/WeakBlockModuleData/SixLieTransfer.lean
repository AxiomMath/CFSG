module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem exists_mem_of_normalizer_cover {X : Type*} [Group X]
    (hX : ∀ ψ : X ≃* X, ∃ a : X, ∀ x, ψ x = a * x * a⁻¹) (A : Subgroup Q) (hA : ⁅A, A⁆ = A)
    (e : A ⧸ Subgroup.center A ≃* X) {u : Q} (hu : u ∈ Subgroup.normalizer (A : Set Q)) :
    ∃ a ∈ A, a⁻¹ * u ∈ Subgroup.centralizer (A : Set Q) := by
  set ψ0 : A ≃* A := conjOnNormalizer A u hu with hψ0
  have hcen : (Subgroup.center A).map ψ0.toMonoidHom = Subgroup.center A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_center_iff.mp hw
      refine Subgroup.mem_center_iff.mpr fun a => ?_
      have := hw' (ψ0.symm a)
      have h2 := congrArg ψ0 this
      simpa using h2
    · intro hz
      have hz' := Subgroup.mem_center_iff.mp hz
      refine ⟨ψ0.symm z, Subgroup.mem_center_iff.mpr fun a => ?_, by simp⟩
      have := hz' (ψ0 a)
      have h2 := congrArg ψ0.symm this
      simpa using h2
  set ψ1 : A ⧸ Subgroup.center A ≃* A ⧸ Subgroup.center A :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center A) ψ0 hcen with hψ1
  set ψ : X ≃* X := (e.symm.trans ψ1).trans e with hψ
  obtain ⟨a, ha⟩ := hX ψ
  obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hz : ∀ x : A, ∃ z : A, z ∈ Subgroup.center A ∧
      ((u * (x : Q) * u⁻¹ : Q)) = (a' : Q) * x * (a' : Q)⁻¹ * z := by
    intro x
    have h1 := ha (e (x : A ⧸ Subgroup.center A))
    have h2 : ψ (e (x : A ⧸ Subgroup.center A)) =
        e ((ψ0 x : A) : A ⧸ Subgroup.center A) := by
      simp [hψ, hψ1]
      rfl
    rw [h2] at h1
    have hae : a = e (a' : A ⧸ Subgroup.center A) := by rw [ha']; simp
    have h3 : ((ψ0 x : A) : A ⧸ Subgroup.center A) =
        ((a' * x * a'⁻¹ : A) : A ⧸ Subgroup.center A) := by
      apply e.injective
      calc e ((ψ0 x : A) : A ⧸ Subgroup.center A) = a * e (x : A ⧸ Subgroup.center A) * a⁻¹ := h1
        _ = e ((a' * x * a'⁻¹ : A) : A ⧸ Subgroup.center A) := by
          rw [hae]; simp [map_mul]
    have h4 := QuotientGroup.eq.mp h3.symm
    refine ⟨(a' * x * a'⁻¹)⁻¹ * ψ0 x, h4, ?_⟩
    have hψx := conjOnNormalizer_apply A u hu x
    simp only [hψ0, Subgroup.coe_mul, Subgroup.coe_inv, hψx]
    group
  have hc : (a' : Q)⁻¹ * u ∈ Subgroup.centralizer (A : Set Q) := by
    refine mem_centralizer_of_trivial_mod_center hA ?_ ?_
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer a'.2)) hu
    · intro x hx b hb
      obtain ⟨z, hzc, hzx⟩ := hz ⟨x, hx⟩
      have hzc' := Subgroup.mem_center_iff.mp hzc
      have : (a' : Q)⁻¹ * u * x * ((a' : Q)⁻¹ * u)⁻¹ * x⁻¹ = (z : Q) := by
        have e1 : (a' : Q)⁻¹ * u * x * ((a' : Q)⁻¹ * u)⁻¹ * x⁻¹ =
            (a' : Q)⁻¹ * (u * x * u⁻¹) * a' * x⁻¹ := by group
        rw [e1]
        simp only at hzx
        rw [hzx]
        have e2 : (a' : Q)⁻¹ * ((a' : Q) * x * (a' : Q)⁻¹ * z) * a' * x⁻¹ =
            x * ((a' : Q)⁻¹ * z * a') * x⁻¹ := by group
        rw [e2]
        have e3 : ((a' : Q)⁻¹ * z * a') = z := by
          have h5 : ((a' : Q) * z) = (z : Q) * a' := congrArg Subtype.val (hzc' a')
          calc (a' : Q)⁻¹ * z * a' = (a' : Q)⁻¹ * ((z : Q) * a') := by group
            _ = (a' : Q)⁻¹ * ((a' : Q) * z) := by rw [h5]
            _ = z := by group
        rw [e3]
        have h6 : (x : Q) * z = (z : Q) * x := congrArg Subtype.val (hzc' ⟨x, hx⟩)
        calc (x : Q) * z * x⁻¹ = ((z : Q) * x) * x⁻¹ := by rw [h6]
          _ = z := by group
      rw [this]
      exact congrArg Subtype.val (hzc' ⟨b, hb⟩)
  exact ⟨a', a'.2, hc⟩

theorem normalizer_le_of_normalizer_sylow_le {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (T : Sylow p Y) {J : Subgroup Y}
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    Subgroup.normalizer (J : Set Y) ≤ J := by
  have hTJ : (T : Subgroup Y) ≤ J := Subgroup.le_normalizer.trans hNJ
  set G' : Subgroup Y := Subgroup.normalizer (J : Set Y) with hG'
  have hJG : J ≤ G' := Subgroup.le_normalizer
  have hTG : (T : Subgroup Y) ≤ G' := hTJ.trans hJG
  let P' : Sylow p G' := T.subtype hTG
  set N' : Subgroup G' := J.subgroupOf G' with hN'
  haveI hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 le_rfl
  have hP'N' : (P' : Subgroup G') ≤ N' := by
    rw [Sylow.coe_subtype]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hTJ (Subgroup.mem_subgroupOf.mp hx))
  have hfr := Sylow.normalizer_sup_eq_top' (N := N') P' hP'N'
  intro x hx
  have hx' : (⟨x, hx⟩ : G') ∈ Subgroup.normalizer (P' : Set G') ⊔ N' := by
    rw [hfr]; exact Subgroup.mem_top _
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hn' : (n : Y) ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
    have hc : (P' : Subgroup G') = (T : Subgroup Y).subgroupOf G' := T.coe_subtype hTG
    have : n ∈ Subgroup.normalizer (((T : Subgroup Y).subgroupOf G' : Subgroup G') : Set G') := by
      rw [← hc]; exact hn
    rw [← Subgroup.subgroupOf_normalizer_eq hTG] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hk' : (k : Y) ∈ J := Subgroup.mem_subgroupOf.mp hk
  have : x = (n : Y) * (k : Y) := by
    have := congrArg Subtype.val hnk
    simpa using this.symm
  rw [this]
  exact J.mul_mem (hNJ hn') hk'

theorem card_map_eq_of_inj_on {A B : Type*} [Group A] [Group B] (f : A →* B) {V : Subgroup A}
    (h : ∀ x ∈ V, f x = 1 → x = 1) : Nat.card (V.map f) = Nat.card V := by
  have hinj : Function.Injective (f.comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (h x.1 x.2 hx)
  have hr : (f.comp V.subtype).range = V.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_line_of_cover [Finite Q] {Lb P E N : Subgroup Q} (hPL : P ≤ Lb) (hEP : E ≤ P)
    (hperf : ⁅Lb, Lb⁆ = Lb)
    (hX : ∀ ψ : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* (↥Lb ⧸ Subgroup.center ↥Lb),
      ∃ a, ∀ x, ψ x = a * x * a⁻¹)
    (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥Lb))) (hE3 : IsPGroup 3 E)
    (hNLb : N ≤ Subgroup.normalizer (Lb : Set Q)) (hNE : N ≤ Subgroup.normalizer (E : Set Q))
    (hNP : N ≤ Subgroup.normalizer (P : Set Q))
    (hself : Subgroup.normalizer
        (((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) : Subgroup _) : Set _) ≤
      (P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    (E₁ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb))
    (hE₁ : E₁ ≤ (E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    (hcard : Nat.card E₁ = 3)
    (hline : (P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) ⊓
        Subgroup.normalizer
          (((E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) : Subgroup _) :
            Set _) ≤ Subgroup.normalizer (E₁ : Set _)) :
    ∃ W : Subgroup Q, W ≤ E ∧ Nat.card W = 3 ∧ N ≤ Subgroup.normalizer (W : Set Q) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  have hEL : E ≤ Lb := hEP.trans hPL
  have hE'3 : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEL).symm
  have hinj : ∀ x ∈ E', ρ x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hE'3 ⟨x, hx⟩
    have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥Lb) := Subgroup.orderOf_dvd_natCard _ hxc
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hZ3) h3 h2)
  set W' : Subgroup ↥Lb := E' ⊓ E₁.comap ρ with hW'
  have hWmap : W'.map ρ = E₁ := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_inf.mp hw).2
    · intro y hy
      obtain ⟨e, he, rfl⟩ := hE₁ hy
      exact ⟨e, ⟨he, hy⟩, rfl⟩
  have hcardW' : Nat.card W' = 3 := by
    rw [← hcard, ← hWmap]
    exact (card_map_eq_of_inj_on ρ fun x hx => hinj x (Subgroup.mem_inf.mp hx).1).symm
  have hE'map : E'.map Lb.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEL
  refine ⟨W'.map Lb.subtype, (Subgroup.map_mono inf_le_left).trans hE'map.le, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Lb.subtype_injective, hcardW']
  · intro n hn
    obtain ⟨l, hl, hc⟩ := exists_mem_of_normalizer_cover hX Lb hperf (MulEquiv.refl _) (hNLb hn)
    set c : Q := l⁻¹ * n with hcdef
    have hnlc : n = l * c := by rw [hcdef]; group
    have hcL : ∀ h ∈ Lb, h * c = c * h := fun h hh => by
      have := Subgroup.mem_centralizer_iff.mp hc h hh
      exact this
    have hcN : ∀ X : Subgroup Q, X ≤ Lb → c ∈ Subgroup.normalizer (X : Set Q) := by
      intro X hX
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      have : c * x * c⁻¹ = x := by rw [← hcL x (hX hx), mul_inv_cancel_right]
      rw [this]; exact hx
    have hlN : ∀ X : Subgroup Q, X ≤ Lb → n ∈ Subgroup.normalizer (X : Set Q) →
        l ∈ Subgroup.normalizer (X : Set Q) := by
      intro X hX hnX
      have : l = n * c⁻¹ := by rw [hnlc]; group
      rw [this]
      exact Subgroup.mul_mem _ hnX (Subgroup.inv_mem _ (hcN X hX))
    have hlE : l ∈ Subgroup.normalizer (E : Set Q) := hlN E hEL (hNE hn)
    have hlP : l ∈ Subgroup.normalizer (P : Set Q) := hlN P hPL (hNP hn)
    set l' : ↥Lb := ⟨l, hl⟩ with hl'
    have hl'P : l' ∈ Subgroup.normalizer (P' : Set ↥Lb) := by
      apply Subgroup.mem_normalizer_fintype
      intro p hp
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hlP p).mp (Subgroup.mem_subgroupOf.mp hp))
    have hl'E : l' ∈ Subgroup.normalizer (E' : Set ↥Lb) := by
      apply Subgroup.mem_normalizer_fintype
      intro p hp
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hlE p).mp (Subgroup.mem_subgroupOf.mp hp))
    have hρJ : ρ l' ∈ P'.map ρ :=
      hself ((Subgroup.le_normalizer_map ρ) ⟨l', hl'P, rfl⟩)
    have hρE : ρ l' ∈ Subgroup.normalizer ((E'.map ρ : Subgroup _) : Set _) :=
      (Subgroup.le_normalizer_map ρ) ⟨l', hl'E, rfl⟩
    have hρ1 : ρ l' ∈ Subgroup.normalizer (E₁ : Set _) := hline ⟨hρJ, hρE⟩
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨w, hw, rfl⟩
    change n * (w : Q) * n⁻¹ ∈ ((W'.map Lb.subtype : Subgroup Q) : Set Q)
    have hwc : c * (w : Q) = (w : Q) * c := (hcL w w.2).symm
    have hnw : n * (w : Q) * n⁻¹ = l * (w : Q) * l⁻¹ := by
      rw [hnlc]
      calc l * c * (w : Q) * (l * c)⁻¹ = l * (c * (w : Q)) * c⁻¹ * l⁻¹ := by group
        _ = l * ((w : Q) * c) * c⁻¹ * l⁻¹ := by rw [hwc]
        _ = l * (w : Q) * l⁻¹ := by group
    rw [hnw]
    have hw1 := (Subgroup.mem_inf.mp hw).1
    have hw2 := (Subgroup.mem_inf.mp hw).2
    refine ⟨l' * w * l'⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by simp [hl']⟩
    ·
      have hwE : (w : Q) ∈ E := Subgroup.mem_subgroupOf.mp hw1
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp hlE (w : Q)).mp hwE)
    ·
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hρ1 _).mp hw2

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
