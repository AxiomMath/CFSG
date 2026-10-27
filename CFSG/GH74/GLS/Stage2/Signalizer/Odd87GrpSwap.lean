module

public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG
open scoped commutatorElement

theorem not_isPGroup_quotient_center {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hQ : IsQuasisimple Q) : ¬ IsPGroup p (Q ⧸ center Q) := by
  intro hP
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  have hcen : center (Q ⧸ center Q) = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with h | h
    · exact absurd h hP.bot_lt_center.ne'
    · exact h
  exact hab ((mem_center_iff.mp (hcen ▸ mem_top a) b).symm)

theorem exists_mul_of_mem_sup {A : Type*} [Group A] {J₁ J₂ : Subgroup A}
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) {x : A} (hx : x ∈ J₁ ⊔ J₂) :
    ∃ a ∈ J₁, ∃ b ∈ J₂, a * b = x := by
  let K : Subgroup A :=
    { carrier := {x | ∃ a ∈ J₁, ∃ b ∈ J₂, a * b = x}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have h := hcomm a' ha' b hb
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb) }
  have hle : J₁ ⊔ J₂ ≤ K :=
    sup_le (fun a ha => ⟨a, ha, 1, one_mem _, mul_one a⟩)
      (fun b hb => ⟨1, one_mem _, b, hb, one_mul b⟩)
  exact hle hx

theorem central_of_prod_mem {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {J₁ J₂ P : Subgroup A} (hJ₁ : IsQuasisimple ↥J₁)
    (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) (hP : IsPGroup p ↥P)
    (hnorm : ∀ g ∈ J₁, ∃ g' ∈ J₂, ∀ y ∈ P, (g * g') * y * (g * g')⁻¹ ∈ P)
    {a b : A} (ha : a ∈ J₁) (hb : b ∈ J₂) (hab : a * b ∈ P) :
    ∀ c ∈ J₁, c * a = a * c := by
  let φ : ↥J₁ × ↥J₂ →* A :=
    J₁.subtype.noncommCoprod J₂.subtype (fun m n => hcomm m m.2 n n.2)
  let S : Subgroup ↥J₁ := (P.comap φ).map (MonoidHom.fst ↥J₁ ↥J₂)
  have hmemS : ∀ n : ↥J₁, n ∈ S ↔ ∃ b' : ↥J₂, (n : A) * b' ∈ P := by
    intro n
    constructor
    · rintro ⟨⟨n', b'⟩, hx, rfl⟩
      exact ⟨b', hx⟩
    · rintro ⟨b', hx⟩
      exact ⟨(n, b'), hx, rfl⟩
  have hS : S.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨b', hb'⟩ := (hmemS n).mp hn
    obtain ⟨g', hg'J, hg'⟩ := hnorm g g.2
    refine (hmemS _).mpr ⟨⟨g' * b' * g'⁻¹, mul_mem (mul_mem hg'J b'.2) (inv_mem hg'J)⟩, ?_⟩
    let w : ↥J₁ × ↥J₂ := (g, ⟨g', hg'J⟩)
    have e : φ (w * (n, b') * w⁻¹) = φ w * φ (n, b') * (φ w)⁻¹ := by
      simp only [map_mul, map_inv]
    have h1 : φ (w * (n, b') * w⁻¹) ∈ P := by
      rw [e]
      exact hg' _ hb'
    exact h1
  rcases LocalCores.quasisimple_normal_subgroups hJ₁ hS with h | h
  · exfalso
    refine not_isPGroup_quotient_center hp hJ₁ (fun q => ?_)
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b', hb'⟩ := (hmemS n).mp (h ▸ mem_top n)
    obtain ⟨k, hk⟩ := hP ⟨(n : A) * b', hb'⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff]
    intro g
    have h1 : ((n : A) * b') ^ (p ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hc : Commute (n : A) (b' : A) := hcomm n n.2 b' b'.2
    rw [hc.mul_pow] at h1
    have h2 : (n : A) ^ (p ^ k) = ((b' : A) ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (n : A) ^ (p ^ k) ∈ J₂ := by
      rw [h2]
      exact inv_mem (pow_mem b'.2 _)
    exact Subtype.ext (hcomm g g.2 _ h3)
  · intro c hc
    have ha' : (⟨a, ha⟩ : ↥J₁) ∈ S := (hmemS _).mpr ⟨⟨b, hb⟩, hab⟩
    exact congrArg Subtype.val (mem_center_iff.mp (h ha') ⟨c, hc⟩)

theorem eq_bot_of_le_center_of_normal {A : Type*} [Group A] {p : ℕ} (hop : pCore p A = ⊥)
    {J P : Subgroup A} (hJ : J.Normal) (hPJ : P ≤ J)
    (hPc : ∀ x ∈ P, ∀ j ∈ J, j * x = x * j) (hP : IsPGroup p ↥P) : P = ⊥ := by
  let R : Subgroup A :=
    { carrier := {x | x ∈ J ∧ (∀ j ∈ J, j * x = x * j) ∧ ∃ k : ℕ, x ^ (p ^ k) = 1}
      one_mem' := ⟨one_mem _, fun j _ => by simp, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxJ, hxc, k, hk⟩ ⟨hyJ, hyc, l, hl⟩
        refine ⟨mul_mem hxJ hyJ, fun j hj => ?_, k + l, ?_⟩
        · rw [← mul_assoc, hxc j hj, mul_assoc, hyc j hj, mul_assoc]
        · have hxy : Commute x y := hyc x hxJ
          have h1 : x ^ (p ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
          have h2 : y ^ (p ^ (k + l)) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
          rw [hxy.mul_pow, h1, h2, mul_one]
      inv_mem' := by
        rintro x ⟨hxJ, hxc, k, hk⟩
        refine ⟨inv_mem hxJ, fun j hj => ?_, k, by rw [inv_pow, hk, inv_one]⟩
        exact Commute.inv_right (hxc j hj) }
  have hRn : R.Normal := by
    refine ⟨fun r hr g => ?_⟩
    obtain ⟨hrJ, hrc, k, hk⟩ := hr
    refine ⟨hJ.conj_mem r hrJ g, fun j hj => ?_, k, ?_⟩
    · have hj' : g⁻¹ * j * g ∈ J := by simpa using hJ.conj_mem j hj g⁻¹
      have h1 := hrc (g⁻¹ * j * g) hj'
      calc j * (g * r * g⁻¹) = g * ((g⁻¹ * j * g) * r) * g⁻¹ := by group
        _ = g * (r * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
        _ = g * r * g⁻¹ * j := by group
    · rw [conj_pow, hk]
      group
  have hRp : IsPGroup p ↥R := by
    intro x
    obtain ⟨k, hk⟩ := x.2.2.2
    exact ⟨k, Subtype.ext hk⟩
  have hle : R ≤ pCore p A := le_sSup ⟨hRn, hRp⟩
  rw [hop] at hle
  have hPR : P ≤ R := by
    intro x hx
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact ⟨hPJ hx, hPc x hx, k, by simpa using congrArg Subtype.val hk⟩
  exact le_bot_iff.mp (hPR.trans hle)

theorem swap_false {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup A} (hXp : IsPGroup p ↥X) {z : A} (hz2 : z * z = 1)
    (hinv : ∀ c : A, c * z = z * c → c ∈ normalizer (X : Set A))
    (hop : pCore p A = ⊥)
    {J₁ J₂ : Subgroup A} (h₁ : IsComponent J₁) (h₂ : IsComponent J₂) (hne : J₁ ≠ J₂)
    (hnorm : (J₁ ⊔ J₂).Normal)
    (hX₁ : X ≤ normalizer (J₁ : Set A)) (hX₂ : X ≤ normalizer (J₂ : Set A))
    (hz₁ : J₁.map (MulAut.conj z).toMonoidHom = J₂)
    (hJX : ⁅J₁, X⁆ ≠ ⊥) : False := by
  have _hp2 := hp2
  have _hX₁ := hX₁
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
    have h := (LocalCores.distinct_components_commute h₁ h₂).resolve_left hne
    intro a ha b hb
    have h' := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at h'
    exact commutatorElement_eq_one_iff_mul_comm.mp h'
  have hcomm' : ∀ b ∈ J₂, ∀ a ∈ J₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hzz : ∀ a : A, z * (z * a * z⁻¹) * z⁻¹ = a := by
    intro a
    calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
      _ = a := by rw [hz2]; group
  have hz12 : ∀ a ∈ J₁, z * a * z⁻¹ ∈ J₂ := by
    intro a ha
    rw [← hz₁]
    exact Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have hz21 : ∀ b ∈ J₂, z * b * z⁻¹ ∈ J₁ := by
    intro b hb
    rw [← hz₁] at hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    have h : z * ((MulAut.conj z).toMonoidHom a) * z⁻¹ = a := by
      simpa [MulAut.conj_apply] using hzz a
    rw [h]
    exact ha
  have hδz : ∀ a ∈ J₁, (a * (z * a * z⁻¹)) * z = z * (a * (z * a * z⁻¹)) := by
    intro a ha
    have hc := hcomm a ha _ (hz12 a ha)
    have hzinv : z⁻¹ = z := (eq_inv_of_mul_eq_one_left hz2).symm
    calc a * (z * a * z⁻¹) * z = a * (z * a) := by group
      _ = a * z * a := by group
      _ = (z * z) * a * z⁻¹ * a := by rw [hz2, one_mul, hzinv]
      _ = z * ((z * a * z⁻¹) * a) := by group
      _ = z * (a * (z * a * z⁻¹)) := by rw [hc]
  have hδP : ∀ a ∈ J₁, ∀ y ∈ X ⊓ (J₁ ⊔ J₂),
      (a * (z * a * z⁻¹)) * y * (a * (z * a * z⁻¹))⁻¹ ∈ X ⊓ (J₁ ⊔ J₂) := by
    intro a ha y hy
    refine mem_inf.mpr ⟨?_, hnorm.conj_mem y (mem_inf.mp hy).2 _⟩
    exact (mem_normalizer_iff.mp (hinv _ (hδz a ha)) y).mp (mem_inf.mp hy).1
  have hP : IsPGroup p ↥(X ⊓ (J₁ ⊔ J₂)) := hXp.to_le inf_le_left
  have hnormJ₁ : ∀ g ∈ J₁, ∃ g' ∈ J₂, ∀ y ∈ X ⊓ (J₁ ⊔ J₂),
      (g * g') * y * (g * g')⁻¹ ∈ X ⊓ (J₁ ⊔ J₂) :=
    fun g hg => ⟨z * g * z⁻¹, hz12 g hg, fun y hy => hδP g hg y hy⟩
  have hnormJ₂ : ∀ g ∈ J₂, ∃ g' ∈ J₁, ∀ y ∈ X ⊓ (J₁ ⊔ J₂),
      (g * g') * y * (g * g')⁻¹ ∈ X ⊓ (J₁ ⊔ J₂) := by
    intro g hg
    refine ⟨z * g * z⁻¹, hz21 g hg, fun y hy => ?_⟩
    have e : g * (z * g * z⁻¹) = (z * g * z⁻¹) * (z * (z * g * z⁻¹) * z⁻¹) := by
      rw [hzz g]
      exact hcomm' g hg _ (hz21 g hg)
    rw [e]
    exact hδP _ (hz21 g hg) y hy
  have hcentral : ∀ x ∈ X ⊓ (J₁ ⊔ J₂), ∀ j ∈ J₁ ⊔ J₂, j * x = x * j := by
    intro x hx j hj
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (mem_inf.mp hx).2
    have hab : a * b ∈ X ⊓ (J₁ ⊔ J₂) := hx
    have hba : b * a ∈ X ⊓ (J₁ ⊔ J₂) := by
      rw [← hcomm a ha b hb]
      exact hab
    have hA : ∀ c ∈ J₁, c * a = a * c :=
      central_of_prod_mem hp h₁.1 hcomm hP hnormJ₁ ha hb hab
    have hB : ∀ c ∈ J₂, c * b = b * c :=
      central_of_prod_mem hp h₂.1 hcomm' hP hnormJ₂ hb ha hba
    have hle : J₁ ⊔ J₂ ≤ centralizer ({a * b} : Set A) := by
      refine sup_le (fun c hc => ?_) (fun c hc => ?_)
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        calc a * b * c = a * (b * c) := by group
          _ = a * (c * b) := by rw [hcomm c hc b hb]
          _ = a * c * b := by group
          _ = c * a * b := by rw [hA c hc]
          _ = c * (a * b) := by group
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        calc a * b * c = a * (b * c) := by group
          _ = a * (c * b) := by rw [hB c hc]
          _ = a * c * b := by group
          _ = c * a * b := by rw [hcomm a ha c hc]
          _ = c * (a * b) := by group
    exact ((mem_centralizer_iff.mp (hle hj)) (a * b) rfl).symm
  have hbot : X ⊓ (J₁ ⊔ J₂) = ⊥ :=
    eq_bot_of_le_center_of_normal hop hnorm inf_le_right hcentral hP
  have hxδ : ∀ x ∈ X, ∀ a ∈ J₁, x * (a * (z * a * z⁻¹)) = (a * (z * a * z⁻¹)) * x := by
    intro x hx a ha
    have hδJ : a * (z * a * z⁻¹) ∈ J₁ ⊔ J₂ :=
      mul_mem (mem_sup_left ha) (mem_sup_right (hz12 a ha))
    have h1 : x * (a * (z * a * z⁻¹)) * x⁻¹ * (a * (z * a * z⁻¹))⁻¹ ∈ X ⊓ (J₁ ⊔ J₂) := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h2 := (mem_normalizer_iff.mp (hinv _ (hδz a ha)) x⁻¹).mp (inv_mem hx)
        have h3 := mul_mem hx h2
        simpa [mul_assoc] using h3
      · exact mul_mem (hnorm.conj_mem _ hδJ x) (inv_mem hδJ)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hkey : ∀ a ∈ J₁, ∀ x ∈ X, a⁻¹ * (x * a * x⁻¹) ∈ J₂ := by
    intro a ha x hx
    have ha' : z * a * z⁻¹ ∈ J₂ := hz12 a ha
    have hu' : x * (z * a * z⁻¹) * x⁻¹ ∈ J₂ := (mem_normalizer_iff.mp (hX₂ hx) _).mp ha'
    have h1 : (x * a * x⁻¹) * (x * (z * a * z⁻¹) * x⁻¹) = a * (z * a * z⁻¹) := by
      calc (x * a * x⁻¹) * (x * (z * a * z⁻¹) * x⁻¹)
          = x * (a * (z * a * z⁻¹)) * x⁻¹ := by group
        _ = a * (z * a * z⁻¹) := by rw [hxδ x hx a ha]; group
    have h2 : a⁻¹ * (x * a * x⁻¹) = (z * a * z⁻¹) * (x * (z * a * z⁻¹) * x⁻¹)⁻¹ := by
      calc a⁻¹ * (x * a * x⁻¹)
          = a⁻¹ * ((x * a * x⁻¹) * (x * (z * a * z⁻¹) * x⁻¹))
              * (x * (z * a * z⁻¹) * x⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * (z * a * z⁻¹)) * (x * (z * a * z⁻¹) * x⁻¹)⁻¹ := by rw [h1]
        _ = (z * a * z⁻¹) * (x * (z * a * z⁻¹) * x⁻¹)⁻¹ := by group
    rw [h2]
    exact mul_mem ha' (inv_mem hu')
  have hcomJ : ∀ a ∈ J₁, ∀ x ∈ X, ⁅a, x⁆ ∈ centralizer (J₁ : Set A) := by
    intro a ha x hx
    have h := hkey a⁻¹ (inv_mem ha) x hx
    have h' : ⁅a, x⁆ ∈ J₂ := by
      have e : ⁅a, x⁆ = a⁻¹⁻¹ * (x * a⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact h
    rw [mem_centralizer_iff]
    intro c hc
    exact hcomm c hc _ h'
  have hle : ⁅J₁, X⁆ ≤ centralizer (J₁ : Set A) :=
    Subgroup.commutator_le.mpr hcomJ
  have hdc : ⁅⁅J₁, X⁆, J₁⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  exact hJX (LocalCores.perfect_double_commutator h₁.1.1 hdc)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
