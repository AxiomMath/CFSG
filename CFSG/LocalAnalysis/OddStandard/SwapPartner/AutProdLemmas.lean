module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple


public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

theorem card_le_card_inf_centralizer_mul {X : Type*} [Group X] [Finite X] (S Y : Subgroup X)
    (x : X) (h : ∀ z ∈ S, z * x * z⁻¹ * x⁻¹ ∈ Y) :
    Nat.card S ≤ Nat.card (S ⊓ centralizer ({x} : Set X) : Subgroup X) * Nat.card Y := by
  let H : Subgroup S := (S ⊓ centralizer ({x} : Set X)).subgroupOf S
  let φ : S → Y := fun z => ⟨z.1 * x * z.1⁻¹ * x⁻¹, h z.1 z.2⟩
  have hφ : ∀ a b : S, QuotientGroup.leftRel H a b → φ a = φ b := by
    intro a b hab
    apply Subtype.ext
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have hmem : ((a⁻¹ * b : S) : X) ∈ centralizer ({x} : Set X) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hab')).2
    have hcomm : ((a⁻¹ * b : S) : X) * x = x * ((a⁻¹ * b : S) : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem
    have hcomm' : (a.1⁻¹ * b.1) * x = x * (a.1⁻¹ * b.1) := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcomm
    show a.1 * x * a.1⁻¹ * x⁻¹ = b.1 * x * b.1⁻¹ * x⁻¹
    have h1 : a.1 * x * a.1⁻¹ = b.1 * x * b.1⁻¹ := by
      calc a.1 * x * a.1⁻¹
          = (a.1 * (x * (a.1⁻¹ * b.1))) * b.1⁻¹ := by group
        _ = (a.1 * ((a.1⁻¹ * b.1) * x)) * b.1⁻¹ := by rw [← hcomm']
        _ = b.1 * x * b.1⁻¹ := by group
    rw [h1]
  let φbar : S ⧸ H → Y := Quotient.lift φ hφ
  have hinj : Function.Injective φbar := by
    intro a b hab
    revert hab
    refine Quotient.inductionOn₂ a b ?_
    intro a' b' hab
    have hval : a'.1 * x * a'.1⁻¹ * x⁻¹ = b'.1 * x * b'.1⁻¹ * x⁻¹ := by
      have := congrArg Subtype.val hab
      simpa [φbar, φ] using this
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨S.mul_mem (S.inv_mem a'.2) b'.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a'.1 * x * a'.1⁻¹ = b'.1 * x * b'.1⁻¹ :=
      mul_right_cancel hval
    have hcomm' : (a'.1⁻¹ * b'.1) * x = x * (a'.1⁻¹ * b'.1) := by
      calc (a'.1⁻¹ * b'.1) * x
          = a'.1⁻¹ * (b'.1 * x * b'.1⁻¹) * b'.1 := by group
        _ = a'.1⁻¹ * (a'.1 * x * a'.1⁻¹) * b'.1 := by rw [← h1]
        _ = x * (a'.1⁻¹ * b'.1) := by group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcomm'
  have hle : Nat.card (S ⧸ H) ≤ Nat.card Y := Nat.card_le_card_of_injective φbar hinj
  have hS : Nat.card S = Nat.card (S ⧸ H) * Nat.card H :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup H
  have hH : Nat.card H = Nat.card (S ⊓ centralizer ({x} : Set X) : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : S ⊓ centralizer ({x} : Set X) ≤ S)).toEquiv
  calc Nat.card S = Nat.card (S ⧸ H) * Nat.card H := hS
    _ ≤ Nat.card Y * Nat.card H := Nat.mul_le_mul hle le_rfl
    _ = Nat.card Y * Nat.card (S ⊓ centralizer ({x} : Set X) : Subgroup X) := by rw [hH]
    _ = Nat.card (S ⊓ centralizer ({x} : Set X) : Subgroup X) * Nat.card Y := by
        rw [Nat.mul_comm]

theorem card_comap_eq_of_le_range {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    (B : Subgroup G') (hB : B ≤ f.range) :
    Nat.card (B.comap f) = Nat.card B * Nat.card f.ker := by
  let f' : B.comap f →* B :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hsurj : Function.Surjective f' := by
    intro b
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hB b.2)
    refine ⟨⟨g, show f g ∈ B from by rw [hg]; exact b.2⟩, ?_⟩
    ext
    change f g = (b : G')
    exact hg
  have hker : f'.ker = f.ker.subgroupOf (B.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      exact hx
  have hle : f.ker ≤ B.comap f := by
    intro y hy
    show f y ∈ B
    rw [MonoidHom.mem_ker.mp hy]
    exact B.one_mem
  have hcardquot : Nat.card ((B.comap f) ⧸ f'.ker) = Nat.card B :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hsurj).toEquiv
  have hkercard : Nat.card f'.ker = Nat.card f.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  calc Nat.card (B.comap f)
      = Nat.card ((B.comap f) ⧸ f'.ker) * Nat.card f'.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker
    _ = Nat.card B * Nat.card f'.ker := by rw [hcardquot]
    _ = Nat.card B * Nat.card f.ker := by rw [hkercard]

theorem two_mul_card_le_card_centralizer {X : Type*} [Group X] [Finite X] (M N : Subgroup X)
    (x : X) (hMN : M ≤ N) (hMx : M ≤ centralizer ({x} : Set X)) (hx : x ∉ N) :
    2 * Nat.card M ≤ Nat.card (centralizer ({x} : Set X)) := by
  have hxM : ∀ m : X, m ∈ M → x * m ∈ centralizer ({x} : Set X) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm' : m * x = x * m := Subgroup.mem_centralizer_singleton_iff.mp (hMx hm)
    calc (x * m) * x = x * (m * x) := by group
      _ = x * (x * m) := by rw [hm']
  let ψ : M × Bool → centralizer ({x} : Set X) := fun p =>
    match p.2 with
    | true => ⟨x * p.1.1, hxM p.1.1 p.1.2⟩
    | false => ⟨p.1.1, hMx p.1.2⟩
  have hinj : Function.Injective ψ := by
    rintro ⟨m, b⟩ ⟨m', b'⟩ h
    cases b <;> cases b'
    · rw [Subtype.ext_iff] at h
      dsimp only [ψ] at h
      exact Prod.ext (Subtype.ext h) rfl
    · exfalso
      rw [Subtype.ext_iff] at h
      dsimp only [ψ] at h
      apply hx
      have hxeq : x = m.1 * m'.1⁻¹ := by rw [h]; group
      rw [hxeq]
      exact N.mul_mem (hMN m.2) (N.inv_mem (hMN m'.2))
    · exfalso
      rw [Subtype.ext_iff] at h
      dsimp only [ψ] at h
      apply hx
      have hxeq : x = m'.1 * m.1⁻¹ := by rw [← h]; group
      rw [hxeq]
      exact N.mul_mem (hMN m'.2) (N.inv_mem (hMN m.2))
    · rw [Subtype.ext_iff] at h
      dsimp only [ψ] at h
      exact Prod.ext (Subtype.ext (mul_left_cancel h)) rfl
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hle : Nat.card (M × Bool) ≤ Nat.card (centralizer ({x} : Set X)) :=
    Nat.card_le_card_of_injective ψ hinj
  rw [Nat.card_prod, hbool, Nat.mul_comm] at hle
  exact hle

theorem card_le_of_injective_prod {D P₁ P₂ : Type*} [Group D] [Group P₁] [Group P₂]
    [Finite P₁] [Finite P₂] (hD : IsSimpleGroup D) (f : D →* P₁ × P₂)
    (hf : Function.Injective f) (C₁ : Subgroup P₁) (C₂ : Subgroup P₂)
    (h : ∀ d, (f d).1 ∈ C₁ ∧ (f d).2 ∈ C₂) :
    Nat.card D ≤ Nat.card C₁ ∨ Nat.card D ≤ Nat.card C₂ := by
  haveI : Nontrivial D := hD.toNontrivial
  let f₁ : D →* P₁ := (MonoidHom.fst P₁ P₂).comp f
  let f₂ : D →* P₂ := (MonoidHom.snd P₁ P₂).comp f
  have hker₁ : f₁.ker = ⊥ ∨ f₁.ker = ⊤ := hD.eq_bot_or_eq_top_of_normal f₁.ker
  have hker₂ : f₂.ker = ⊥ ∨ f₂.ker = ⊤ := hD.eq_bot_or_eq_top_of_normal f₂.ker
  rcases hker₁ with h1 | h1
  · left
    have hinj : Function.Injective f₁ := (MonoidHom.ker_eq_bot_iff f₁).mp h1
    let g₁ : D → C₁ := fun d => ⟨f₁ d, (h d).1⟩
    have hg₁ : Function.Injective g₁ := by
      intro a b hab
      apply hinj
      exact congrArg Subtype.val hab
    exact Nat.card_le_card_of_injective g₁ hg₁
  · rcases hker₂ with h2 | h2
    · right
      have hinj : Function.Injective f₂ := (MonoidHom.ker_eq_bot_iff f₂).mp h2
      let g₂ : D → C₂ := fun d => ⟨f₂ d, (h d).2⟩
      have hg₂ : Function.Injective g₂ := by
        intro a b hab
        apply hinj
        exact congrArg Subtype.val hab
      exact Nat.card_le_card_of_injective g₂ hg₂
    · exfalso
      have h1' : ∀ d, f₁ d = 1 := fun d => by
        have : d ∈ f₁.ker := by rw [h1]; exact Subgroup.mem_top d
        exact MonoidHom.mem_ker.mp this
      have h2' : ∀ d, f₂ d = 1 := fun d => by
        have : d ∈ f₂.ker := by rw [h2]; exact Subgroup.mem_top d
        exact MonoidHom.mem_ker.mp this
      obtain ⟨a, ha⟩ := exists_ne (1 : D)
      have hfa : f a = 1 := by
        apply Prod.ext
        · simpa [f₁] using h1' a
        · simpa [f₂] using h2' a
      have hf1 : f 1 = 1 := by
        apply Prod.ext
        · simpa [f₁] using h1' 1
        · simpa [f₂] using h2' 1
      exact ha (hf (hfa.trans hf1.symm))

theorem mem_of_sign_eq_of_prod_le (I : Subgroup (Perm (Fin 8) × Perm (Fin 8)))
    (hA : ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ I)
    {g : Perm (Fin 8) × Perm (Fin 8)} (hg : g ∈ I) (hg1 : sign g.1 = -1) (hg2 : sign g.2 = -1)
    {u v : Perm (Fin 8)} (huv : sign u = sign v) : (u, v) ∈ I := by
  rcases Int.units_eq_one_or (sign u) with hu | hu
  · have hv : sign v = 1 := by rw [hu] at huv; exact huv.symm
    exact hA u (Equiv.Perm.mem_alternatingGroup.mpr hu) v
      (Equiv.Perm.mem_alternatingGroup.mpr hv)
  · have hv : sign v = -1 := by rw [hu] at huv; exact huv.symm
    have h1 : sign (g.1⁻¹ * u) = 1 := by
      rw [map_mul, Equiv.Perm.sign_inv, hg1, hu]
      exact Int.units_mul_self (-1)
    have h2 : sign (g.2⁻¹ * v) = 1 := by
      rw [map_mul, Equiv.Perm.sign_inv, hg2, hv]
      exact Int.units_mul_self (-1)
    have hmem := I.mul_mem hg
      (hA (g.1⁻¹ * u) (Equiv.Perm.mem_alternatingGroup.mpr h1)
        (g.2⁻¹ * v) (Equiv.Perm.mem_alternatingGroup.mpr h2))
    have heq : g * (g.1⁻¹ * u, g.2⁻¹ * v) = (u, v) := by
      ext <;> simp [Equiv.Perm.mul_apply]
    rwa [heq] at hmem

theorem card_eq_of_prod_le (I : Subgroup (Perm (Fin 8) × Perm (Fin 8)))
    (hA : ∀ a ∈ alternatingGroup (Fin 8), ∀ b ∈ alternatingGroup (Fin 8), (a, b) ∈ I)
    {g : Perm (Fin 8) × Perm (Fin 8)} (hg : g ∈ I) (hg1 : sign g.1 = -1) (hg2 : sign g.2 = -1) :
    2 * Nat.card I = 40320 ^ 2 ∨ Nat.card I = 40320 ^ 2 := by
  let φ : Perm (Fin 8) × Perm (Fin 8) →* ℤˣ :=
    { toFun := fun w => sign w.1 * sign w.2
      map_one' := by simp
      map_mul' := by intro a b; simp [map_mul, mul_assoc, mul_left_comm, mul_comm] }
  have hsurj : Function.Surjective φ := by
    intro y
    rcases Int.units_eq_one_or y with rfl | rfl
    · exact ⟨1, by simp [φ]⟩
    · refine ⟨(Equiv.swap (0 : Fin 8) 1, 1), ?_⟩
      simp [φ, Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1)]
  let P : Subgroup (Perm (Fin 8) × Perm (Fin 8)) := φ.ker
  have hP_le_I : P ≤ I := by
    intro w hw
    have hw' : sign w.1 * sign w.2 = 1 := by simpa [P, φ] using hw
    have hsign : sign w.1 = sign w.2 := by
      rcases Int.units_eq_one_or (sign w.1) with h1 | h1
      · have h2 : sign w.2 = 1 := by rw [h1] at hw'; simpa using hw'
        rw [h1, h2]
      · have h2 : sign w.2 = -1 := by
          rw [h1] at hw'
          have hneg : (-1 : ℤˣ) * (-1) = 1 := Int.units_mul_self (-1)
          exact mul_left_cancel (hw'.trans hneg.symm)
        rw [h1, h2]
    simpa using mem_of_sign_eq_of_prod_le I hA hg hg1 hg2 hsign
  have hcardperm : Nat.card (Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcardPP : Nat.card (Perm (Fin 8) × Perm (Fin 8)) = 40320 ^ 2 := by
    rw [Nat.card_prod, hcardperm]
    norm_num [pow_two]
  have hcardPP2 : Nat.card (Perm (Fin 8) × Perm (Fin 8)) = 2 * Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker]
    congr 1
    · rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hdvd1 : Nat.card P ∣ Nat.card I := Subgroup.card_dvd_of_le hP_le_I
  have hdvd2 : Nat.card I ∣ 2 * Nat.card P := by
    rw [← hcardPP2]
    exact Subgroup.card_subgroup_dvd_card I
  obtain ⟨k, hk⟩ := hdvd1
  obtain ⟨l, hl⟩ := hdvd2
  have hkl : k * l = 2 := by
    have hp : 0 < Nat.card P := Nat.card_pos
    have hcancel : Nat.card P * (k * l) = Nat.card P * 2 := by
      calc Nat.card P * (k * l) = (Nat.card P * k) * l := by ring
        _ = Nat.card I * l := by rw [← hk]
        _ = 2 * Nat.card P := hl.symm
        _ = Nat.card P * 2 := by ring
    exact Nat.mul_left_cancel hp hcancel
  rcases (Nat.dvd_prime Nat.prime_two).mp ⟨l, hkl.symm⟩ with hk1 | hk2
  · left
    rw [hk, hk1, Nat.mul_one, ← hcardPP2]
    exact hcardPP
  · right
    rw [hk, hk2, Nat.mul_comm, ← hcardPP2]
    exact hcardPP

@[expose] noncomputable def twistedDiag (a : Perm (Fin 8)) :
    Subgroup (Perm (Fin 8) × Perm (Fin 8)) :=
  ((MulAut.conj a).toMonoidHom.prod (MonoidHom.id (Perm (Fin 8)))).range

theorem mem_twistedDiag_iff {a u v : Perm (Fin 8)} :
    (u, v) ∈ twistedDiag a ↔ u = a * v * a⁻¹ := by
  simp only [twistedDiag, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    have h1 : MulAut.conj a w = u := by
      have := congrArg Prod.fst hw
      simpa using this
    have h2 : w = v := by
      have := congrArg Prod.snd hw
      simpa using this
    rw [← h2, ← h1, MulAut.conj_apply]
  · intro h
    exact ⟨v, by ext <;> simp [MulAut.conj_apply, h]⟩

theorem card_twistedDiag (a : Perm (Fin 8)) : Nat.card (twistedDiag a) = 40320 := by
  let ψ : Perm (Fin 8) →* Perm (Fin 8) × Perm (Fin 8) :=
    (MulAut.conj a).toMonoidHom.prod (MonoidHom.id (Perm (Fin 8)))
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have := congrArg Prod.snd hxy
    simpa [ψ] using this
  have hcardperm : Nat.card (Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  calc Nat.card (twistedDiag a) = Nat.card ψ.range := rfl
    _ = Nat.card (Perm (Fin 8)) :=
        (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
    _ = 40320 := hcardperm

theorem sign_eq_of_mem_twistedDiag {a : Perm (Fin 8)} {g : Perm (Fin 8) × Perm (Fin 8)}
    (hg : g ∈ twistedDiag a) : sign g.1 = sign g.2 := by
  have h := mem_twistedDiag_iff.mp hg
  rw [h, map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm (sign a) (sign g.2)

end CFSG.OddStandard.AltStdSec.SwapPartner
