module

public import CFSG.GH74.GLS.Stage2.Final.L26.Pair
public import CFSG.LieType.HighestRoot.SL2Outer

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement


theorem exists_pComponent_lift {X : Type} [Group X] [Finite X]
    {K : Subgroup (X ⧸ pPrimeCore 2 X)} (hK : IsComponent K) :
    ∃ J : Subgroup X, IsPComponent 2 J ∧ J.map (QuotientGroup.mk' (pPrimeCore 2 X)) = K := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let 𝒮 : Set (Subgroup X) := {J | J.IsSubnormal ∧ J.map π = K}
  have hne : (K.comap π) ∈ 𝒮 :=
    ⟨hK.2.comap π, Subgroup.map_comap_eq_self_of_surjective hsurj K⟩
  obtain ⟨J, hJ, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min 𝒮 ⟨_, hne⟩
  refine ⟨J, ⟨K, hK, hJ.1, hJ.2, fun J' hJ' hsub hmap => hmin J' ⟨hsub, hmap⟩ hJ'⟩, hJ.2⟩

theorem isComponent_map_bar {X : Type} [Group X] [Finite X] {J : Subgroup X} (hJ : IsComponent J) :
    IsComponent (J.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  have hnot : ¬ J ≤ (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolv : Group.IsSolvable ↥J := by
      have := CFSG.GH74.GLS.Stage2.Final.Thm4.pPrimeCore_solvable (X := X)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolv
  exact ⟨isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

theorem exists_noncomm_of_isComponent {Y : Type} [Group Y] {K : Subgroup Y} (hK : IsComponent K) :
    ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  obtain ⟨_, _, a, b, hab⟩ := hK.1
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', a'.2, b', b'.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)


section Pair

variable {X : Type} [Group X] [Finite X] {L₁ L₂ : Subgroup (X ⧸ pPrimeCore 2 X)}

theorem comp_eq_of_map_eq {Γ Γ' : Subgroup X} (hΓ : IsComponent Γ) (hΓ' : IsComponent Γ')
    (hmap : Γ.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Γ'.map (QuotientGroup.mk' (pPrimeCore 2 X))) :
    Γ = Γ' := by
  rcases distinct_components_commute hΓ hΓ' with h | h
  · exact h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isComponent (isComponent_map_bar hΓ)
    apply hab
    obtain ⟨a', ha', rfl⟩ := ha
    rw [hmap] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hcomm := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha' |> fun hh => hh
    have h1 : a' * b' = b' * a' := by
      have := Subgroup.mem_centralizer_iff.mp (hcomm) b' hb'
      exact this.symm
    show (QuotientGroup.mk' (pPrimeCore 2 X)) a' * (QuotientGroup.mk' (pPrimeCore 2 X)) b' = _
    rw [← map_mul, ← map_mul, h1]


theorem exists_component_over
    (hlift : ∀ J : Subgroup X, IsPComponent 2 J → J ≤ layer X)
    (hc₁ : IsComponent L₁) (hne : L₁ ≠ L₂) (hc₂ : IsComponent L₂)
    (hcomps : ∀ K : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent K → K = L₁ ∨ K = L₂) :
    ∃ Γ : Subgroup X, IsComponent Γ ∧ Γ.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₁ := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  by_contra hcon
  push Not at hcon
  have hall : ∀ Γ : Subgroup X, IsComponent Γ → Γ.map π ≤ L₂ := by
    intro Γ hΓ
    rcases hcomps _ (isComponent_map_bar hΓ) with h | h
    · exact absurd h (hcon Γ hΓ)
    · exact h.le
  have hlay : layer X ≤ L₂.comap π := by
    refine sSup_le fun Γ hΓ => ?_
    exact Subgroup.map_le_iff_le_comap.mp (hall Γ hΓ)
  obtain ⟨J, hJ, hJmap⟩ := exists_pComponent_lift hc₁
  have h1 : L₁ ≤ L₂ := by
    rw [← hJmap]
    exact Subgroup.map_le_iff_le_comap.mpr ((hlift J hJ).trans hlay)
  rcases distinct_components_commute hc₁ hc₂ with h | h
  · exact hne h
  · obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isComponent hc₁
    apply hab
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
    exact (Subgroup.mem_centralizer_iff.mp this b (h1 hb)).symm

theorem exists_two_components
    (hlift : ∀ J : Subgroup X, IsPComponent 2 J → J ≤ layer X)
    (hc₁ : IsComponent L₁) (hc₂ : IsComponent L₂) (hne : L₁ ≠ L₂)
    (hcomps : ∀ K : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent K → K = L₁ ∨ K = L₂) :
    ∃ Γ₁ Γ₂ : Subgroup X, IsComponent Γ₁ ∧ IsComponent Γ₂ ∧
      Γ₁.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₁ ∧
      Γ₂.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₂ ∧
      (∀ Γ : Subgroup X, IsComponent Γ → Γ = Γ₁ ∨ Γ = Γ₂) ∧ Γ₁ ≠ Γ₂ ∧ ⁅Γ₁, Γ₂⁆ = ⊥ := by
  obtain ⟨Γ₁, h₁, e₁⟩ := exists_component_over hlift hc₁ hne hc₂ hcomps
  obtain ⟨Γ₂, h₂, e₂⟩ := exists_component_over hlift hc₂ hne.symm hc₁
    (fun K hK => (hcomps K hK).symm)
  have hne' : Γ₁ ≠ Γ₂ := by
    intro h
    apply hne
    rw [← e₁, ← e₂, h]
  refine ⟨Γ₁, Γ₂, h₁, h₂, e₁, e₂, fun Γ hΓ => ?_, hne', ?_⟩
  · rcases hcomps _ (isComponent_map_bar hΓ) with h | h
    · exact Or.inl (comp_eq_of_map_eq hΓ h₁ (h.trans e₁.symm))
    · exact Or.inr (comp_eq_of_map_eq hΓ h₂ (h.trans e₂.symm))
  · rcases distinct_components_commute h₁ h₂ with h | h
    · exact absurd h hne'
    · exact h

end Pair



variable {Q : Type} [Group Q]

structure PairShape [Finite Q] (L₁ L₂ : Subgroup Q) : Prop where
  c₁ : IsComponent L₁
  c₂ : IsComponent L₂
  ne : L₁ ≠ L₂
  comps : ∀ K : Subgroup Q, IsComponent K → K = L₁ ∨ K = L₂
  fitting : generalizedFitting Q = L₁ ⊔ L₂
  center₁ : ∀ a ∈ L₁, (∀ l ∈ L₁, a * l = l * a) → a * a = 1
  center₂ : ∀ a ∈ L₂, (∀ l ∈ L₂, a * l = l * a) → a * a = 1
  out₁ : ∀ α β : MulAut ↥L₁, ∃ y : ↥L₁, α * β * α⁻¹ * β⁻¹ = MulAut.conj y
  out₂ : ∀ α β : MulAut ↥L₂, ∃ y : ↥L₂, α * β * α⁻¹ * β⁻¹ = MulAut.conj y

variable {L₁ L₂ : Subgroup Q}

theorem PairShape.comm [Finite Q] (h : PairShape L₁ L₂) : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
  intro a ha b hb
  rcases distinct_components_commute h.c₁ h.c₂ with he | hc
  · exact absurd he h.ne
  · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm

@[expose, reducible] def cj (q : Q) (K : Subgroup Q) : Subgroup Q := K.map (MulAut.conj q).toMonoidHom

theorem mem_cj {K : Subgroup Q} {q x : Q} : x ∈ cj q K ↔ q⁻¹ * x * q ∈ K := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cj_eq_iff {K : Subgroup Q} {q : Q} : cj q K = K ↔ q ∈ normalizer (K : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have h1 : q * x * q⁻¹ ∈ cj q K ↔ q * x * q⁻¹ ∈ K := by rw [h]
    rw [mem_cj] at h1
    have e : q⁻¹ * (q * x * q⁻¹) * q = x := by group
    rw [e] at h1
    exact h1.trans Iff.rfl
  · intro h
    ext y
    rw [mem_cj]
    have h1 := h (q⁻¹ * y * q)
    have e : q * (q⁻¹ * y * q) * q⁻¹ = y := by group
    rw [e] at h1
    exact h1

theorem cj_cj {K : Subgroup Q} {q q' : Q} : cj q (cj q' K) = cj (q * q') K := by
  ext x
  simp only [mem_cj]
  simp [mul_assoc]

theorem cj_one {K : Subgroup Q} : cj (1 : Q) K = K := by
  ext x; simp

theorem cj_injective {q : Q} : Function.Injective (cj q : Subgroup Q → Subgroup Q) :=
  Subgroup.map_injective (MulAut.conj q).injective

theorem isComponent_cj {K : Subgroup Q} (hK : IsComponent K) (q : Q) : IsComponent (cj q K) :=
  isComponent_map_mulEquiv (MulAut.conj q) hK

theorem PairShape.cj_cases [Finite Q] (h : PairShape L₁ L₂) (q : Q) : cj q L₁ = L₁ ∨ cj q L₁ = L₂ :=
  h.comps _ (isComponent_cj h.c₁ q)

theorem PairShape.cj_fix [Finite Q] (h : PairShape L₁ L₂) {q : Q} (hq : cj q L₁ = L₁) : cj q L₂ = L₂ := by
  rcases h.comps _ (isComponent_cj h.c₂ q) with h2 | h2
  · exact absurd (cj_injective (h2.trans hq.symm)) h.ne.symm
  · exact h2

theorem PairShape.cj_swap [Finite Q] (h : PairShape L₁ L₂) {q : Q} (hq : cj q L₁ = L₂) : cj q L₂ = L₁ := by
  rcases h.comps _ (isComponent_cj h.c₂ q) with h2 | h2
  · exact h2
  · exact absurd (cj_injective (hq.trans h2.symm)) h.ne

theorem PairShape.cj_mul_swap [Finite Q] (h : PairShape L₁ L₂) {a b : Q} (ha : cj a L₁ ≠ L₁) (hb : cj b L₁ ≠ L₁) :
    cj (a * b) L₁ = L₁ := by
  have ha2 := (h.cj_cases a).resolve_left ha
  have hb2 := (h.cj_cases b).resolve_left hb
  rw [← cj_cj, hb2, h.cj_swap ha2]


theorem PairShape.normalizer_normal [Finite Q] (h : PairShape L₁ L₂) {q n : Q}
    (hn : n ∈ normalizer (L₁ : Set Q)) : q * n * q⁻¹ ∈ normalizer (L₁ : Set Q) := by
  by_cases hq : q ∈ normalizer (L₁ : Set Q)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hq hn) (Subgroup.inv_mem _ hq)
  · have hq' : cj q L₁ ≠ L₁ := fun e => hq (cj_eq_iff.mp e)
    have hqi : cj q⁻¹ L₁ ≠ L₁ := fun e => hq (by
      have := Subgroup.inv_mem _ (cj_eq_iff.mp e)
      simpa using this)
    have h1 := (h.cj_cases q).resolve_left hq'
    have h2 := (h.cj_cases q⁻¹).resolve_left hqi
    rw [← cj_eq_iff, ← cj_cj, ← cj_cj, h2, h.cj_fix (cj_eq_iff.mpr hn), h.cj_swap h1]

theorem PairShape.comm_mem_normalizer [Finite Q] (h : PairShape L₁ L₂) (a b : Q) :
    ⁅a, b⁆ ∈ normalizer (L₁ : Set Q) := by
  have hN := fun {q n : Q} (hn : n ∈ normalizer (L₁ : Set Q)) => h.normalizer_normal (q := q) hn
  by_cases ha : a ∈ normalizer (L₁ : Set Q) <;> by_cases hb : b ∈ normalizer (L₁ : Set Q)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  · have : b * a⁻¹ * b⁻¹ ∈ normalizer (L₁ : Set Q) := hN (Subgroup.inv_mem _ ha)
    have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact Subgroup.mul_mem _ ha this
  · have : a * b * a⁻¹ ∈ normalizer (L₁ : Set Q) := hN hb
    have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hb)
  · have hab : a * b ∈ normalizer (L₁ : Set Q) := by
      rw [← cj_eq_iff]
      exact h.cj_mul_swap (fun e => ha (cj_eq_iff.mp e)) (fun e => hb (cj_eq_iff.mp e))
    have hai : a⁻¹ * b⁻¹ ∈ normalizer (L₁ : Set Q) := by
      rw [← cj_eq_iff]
      refine h.cj_mul_swap (fun e => ha ?_) (fun e => hb ?_)
      · have := Subgroup.inv_mem _ (cj_eq_iff.mp e); simpa using this
      · have := Subgroup.inv_mem _ (cj_eq_iff.mp e); simpa using this
    have e : ⁅a, b⁆ = (a * b) * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact Subgroup.mul_mem _ hab hai


def innerNorm (L : Subgroup Q) : Subgroup Q where
  carrier := {q | q ∈ normalizer (L : Set Q) ∧ ∃ y ∈ L, ∀ x ∈ L, q * x * q⁻¹ = y * x * y⁻¹}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro q q' ⟨hq, y, hy, hqy⟩ ⟨hq', y', hy', hqy'⟩
    refine ⟨Subgroup.mul_mem _ hq hq', y * y', L.mul_mem hy hy', fun x hx => ?_⟩
    have hx' : y' * x * y'⁻¹ ∈ L := L.mul_mem (L.mul_mem hy' hx) (L.inv_mem hy')
    calc q * q' * x * (q * q')⁻¹ = q * (q' * x * q'⁻¹) * q⁻¹ := by group
      _ = q * (y' * x * y'⁻¹) * q⁻¹ := by rw [hqy' x hx]
      _ = y * (y' * x * y'⁻¹) * y⁻¹ := hqy _ hx'
      _ = (y * y') * x * (y * y')⁻¹ := by group
  inv_mem' := by
    rintro q ⟨hq, y, hy, hqy⟩
    refine ⟨Subgroup.inv_mem _ hq, y⁻¹, L.inv_mem hy, fun x hx => ?_⟩
    have hx' : q⁻¹ * x * q ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hq) x).mp hx
      simpa using this
    have h1 := hqy (q⁻¹ * x * q) hx'
    have e : q * (q⁻¹ * x * q) * q⁻¹ = x := by group
    rw [e] at h1
    calc q⁻¹ * x * q⁻¹⁻¹ = q⁻¹ * x * q := by simp
      _ = y⁻¹ * (y * (q⁻¹ * x * q) * y⁻¹) * y⁻¹⁻¹ := by group
      _ = y⁻¹ * x * y⁻¹⁻¹ := by rw [← h1]


theorem PairShape.comm_mem_innerNorm₁ [Finite Q] (h : PairShape L₁ L₂) {a b : Q}
    (ha : a ∈ normalizer (L₁ : Set Q)) (hb : b ∈ normalizer (L₁ : Set Q)) :
    ⁅a, b⁆ ∈ innerNorm L₁ := by
  set ρ := L₁.normalizerMonoidHom
  have hρ : ∀ (g : normalizer (L₁ : Set Q)) (x : L₁), ((ρ g x : L₁) : Q) = g * x * g⁻¹ :=
    fun g x => rfl
  set na : normalizer (L₁ : Set Q) := ⟨a, ha⟩
  set nb : normalizer (L₁ : Set Q) := ⟨b, hb⟩
  obtain ⟨y, hy⟩ := h.out₁ (ρ na) (ρ nb)
  have hρab : ρ ⁅na, nb⁆ = ρ na * ρ nb * (ρ na)⁻¹ * (ρ nb)⁻¹ := by
    rw [map_commutatorElement, commutatorElement_def]
  refine ⟨?_, y, y.2, fun x hx => ?_⟩
  · exact h.comm_mem_normalizer a b
  · have := congrArg (fun γ : MulAut L₁ => ((γ ⟨x, hx⟩ : L₁) : Q)) (hρab.trans hy)
    simp only [hρ, MulAut.conj_apply] at this
    simpa [na, nb, commutatorElement_def] using this


theorem PairShape.symm [Finite Q] (h : PairShape L₁ L₂) : PairShape L₂ L₁ where
  c₁ := h.c₂
  c₂ := h.c₁
  ne := h.ne.symm
  comps K hK := (h.comps K hK).symm
  fitting := by rw [h.fitting, sup_comm]
  center₁ := h.center₂
  center₂ := h.center₁
  out₁ := h.out₂
  out₂ := h.out₁

theorem PairShape.perfect_le [Finite Q] (h : PairShape L₁ L₂) {P : Subgroup Q} (hP : ⁅P, P⁆ = P) :
    P ≤ L₁ ⊔ L₂ := by
  have hN : ∀ q ∈ P, q ∈ normalizer (L₁ : Set Q) := by
    intro q hq
    have hq' : q ∈ ⁅P, P⁆ := by rw [hP]; exact hq
    have : ⁅P, P⁆ ≤ normalizer (L₁ : Set Q) :=
      Subgroup.commutator_le.mpr fun a _ b _ => h.comm_mem_normalizer a b
    exact this hq'
  have hN₂ : ∀ q ∈ P, q ∈ normalizer (L₂ : Set Q) := fun q hq =>
    cj_eq_iff.mp (h.cj_fix (cj_eq_iff.mpr (hN q hq)))
  have h1 : P ≤ innerNorm L₁ := hP ▸ Subgroup.commutator_le.mpr
    (fun a ha b hb => h.comm_mem_innerNorm₁ (hN a ha) (hN b hb))
  have h2 : P ≤ innerNorm L₂ := hP ▸ Subgroup.commutator_le.mpr
    (fun a ha b hb => h.symm.comm_mem_innerNorm₁ (hN₂ a ha) (hN₂ b hb))
  intro p hp
  obtain ⟨-, a₁, ha₁, hpa₁⟩ := h1 hp
  obtain ⟨-, a₂, ha₂, hpa₂⟩ := h2 hp
  have hcom : ∀ x ∈ L₁, ∀ w ∈ L₂, x * w = w * x := h.comm
  set c : Q := (a₁ * a₂)⁻¹ * p with hc
  have hc1 : ∀ x ∈ L₁, c * x * c⁻¹ = x := by
    intro x hx
    have e1 := hpa₁ x hx
    have e2 : a₂ * x = x * a₂ := (hcom x hx a₂ ha₂).symm
    calc c * x * c⁻¹ = (a₁ * a₂)⁻¹ * (p * x * p⁻¹) * (a₁ * a₂) := by simp [hc, mul_assoc]
      _ = a₂⁻¹ * (a₁⁻¹ * (a₁ * x * a₁⁻¹) * a₁) * a₂ := by rw [e1]; group
      _ = a₂⁻¹ * x * a₂ := by group
      _ = x := by rw [mul_assoc, ← e2]; group
  have hc2 : ∀ x ∈ L₂, c * x * c⁻¹ = x := by
    intro x hx
    have e1 := hpa₂ x hx
    have e2 : a₁ * x = x * a₁ := hcom a₁ ha₁ x hx
    have e3 : a₁ * a₂ = a₂ * a₁ := hcom a₁ ha₁ a₂ ha₂
    calc c * x * c⁻¹ = (a₁ * a₂)⁻¹ * (p * x * p⁻¹) * (a₁ * a₂) := by simp [hc, mul_assoc]
      _ = a₂⁻¹ * a₁⁻¹ * (a₂ * x * a₂⁻¹) * (a₁ * a₂) := by rw [e1]; group
      _ = x := by
        have e4 : a₁⁻¹ * (a₂ * x * a₂⁻¹) * a₁ = a₂ * x * a₂⁻¹ := by
          have hx2 : a₂ * x * a₂⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem ha₂ hx) (L₂.inv_mem ha₂)
          have := hcom a₁⁻¹ (L₁.inv_mem ha₁) _ hx2
          calc a₁⁻¹ * (a₂ * x * a₂⁻¹) * a₁ = (a₂ * x * a₂⁻¹) * a₁⁻¹ * a₁ := by rw [this]
            _ = a₂ * x * a₂⁻¹ := by group
        calc a₂⁻¹ * a₁⁻¹ * (a₂ * x * a₂⁻¹) * (a₁ * a₂)
            = a₂⁻¹ * (a₁⁻¹ * (a₂ * x * a₂⁻¹) * a₁) * a₂ := by group
          _ = a₂⁻¹ * (a₂ * x * a₂⁻¹) * a₂ := by rw [e4]
          _ = x := by group
  have hcent : c ∈ centralizer (generalizedFitting Q : Set Q) := by
    rw [h.fitting]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : L₁ ⊔ L₂ ≤ centralizer ({c} : Set Q) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hc1 a ha
        exact (by calc a * c = (c * a * c⁻¹) * c := by rw [this]
                          _ = c * a := by group)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hc2 a ha
        exact (by calc a * c = (c * a * c⁻¹) * c := by rw [this]
                          _ = c * a := by group)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hcf : c ∈ generalizedFitting Q := centralizer_generalizedFitting_le Q hcent
  rw [h.fitting] at hcf
  have hp' : p = a₁ * a₂ * c := by rw [hc]; group
  rw [hp']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)) hcf


theorem PairShape.cj_fix_of_odd [Finite Q] (h : PairShape L₁ L₂) {q : Q} (hq : Odd (orderOf q)) :
    cj q L₁ = L₁ := by
  by_contra hne
  have hq2 : cj q L₁ = L₂ := (h.cj_cases q).resolve_left hne
  have hq1 : cj q L₂ = L₁ := h.cj_swap hq2
  have key : ∀ n : ℕ, cj (q ^ (2 * n)) L₁ = L₁ ∧ cj (q ^ (2 * n + 1)) L₁ = L₂ := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using cj_one, by simpa using hq2⟩
    | succ n ih =>
      have e1 : q ^ (2 * (n + 1)) = q ^ (2 * n + 1) * q := by rw [← pow_succ]; ring_nf
      have e2 : q ^ (2 * (n + 1) + 1) = q ^ (2 * (n + 1)) * q := by rw [← pow_succ]
      have h1 : cj (q ^ (2 * (n + 1))) L₁ = L₁ := by
        rw [e1, ← cj_cj, hq2, h.cj_swap ih.2]
      refine ⟨h1, ?_⟩
      rw [e2, ← cj_cj, hq2, h.cj_fix h1]
  obtain ⟨m, hm⟩ := hq
  have hpow : q ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one q
  have := (key m).2
  rw [hpow, cj_one] at this
  exact h.ne this

theorem PairShape.eq_one_of_odd_centralizes [Finite Q] (h : PairShape L₁ L₂) {q : Q}
    (hq : Odd (orderOf q)) (h1 : ∀ x ∈ L₁, q * x = x * q) (h2 : ∀ x ∈ L₂, q * x = x * q) : q = 1 := by
  have hcent : q ∈ centralizer (generalizedFitting Q : Set Q) := by
    rw [h.fitting, Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : L₁ ⊔ L₂ ≤ centralizer ({q} : Set Q) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h1 a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h2 a ha).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hmem : q ∈ L₁ ⊔ L₂ := h.fitting ▸ centralizer_generalizedFitting_le Q hcent
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute h.comm hmem
  have ha1 : ∀ l ∈ L₁, a * l = l * a := by
    intro l hl
    have e : l * a * b = a * l * b := by
      calc l * a * b = l * (a * b) := by group
        _ = l * q := by rw [hab]
        _ = q * l := (h1 l hl).symm
        _ = a * b * l := by rw [hab]
        _ = a * (b * l) := by group
        _ = a * (l * b) := by rw [(h.comm l hl b hb).symm]
        _ = a * l * b := by group
    exact (mul_right_cancel e).symm
  have hb2 : ∀ l ∈ L₂, b * l = l * b := by
    intro l hl
    have e : a * (b * l) = a * (l * b) := by
      calc a * (b * l) = a * b * l := by group
        _ = q * l := by rw [hab]
        _ = l * q := (h2 l hl)
        _ = l * (a * b) := by rw [hab]
        _ = (l * a) * b := by group
        _ = (a * l) * b := by rw [← h.comm a ha l hl]
        _ = a * (l * b) := by group
    exact mul_left_cancel e
  have haa : a * a = 1 := h.center₁ a ha ha1
  have hbb : b * b = 1 := h.center₂ b hb hb2
  have hq2 : q ^ 2 = 1 := by
    have hab' := h.comm a ha b hb
    rw [hab, sq]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab']
      _ = a * a * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hq2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h2'
  · exact orderOf_eq_one_iff.mp h1'
  · rw [h2'] at hq
    exact absurd hq (by decide)


def mulAutCongr {J S : Type*} [Group J] [Group S] (e : J ≃* S) : MulAut J →* MulAut S where
  toFun γ := e.symm.trans (γ.trans e)
  map_one' := by
    ext x
    simp
  map_mul' γ δ := by
    ext x
    simp

theorem mulAutCongr_apply {J S : Type*} [Group J] [Group S] (e : J ≃* S) (γ : MulAut J) (x : J) :
    mulAutCongr e γ (e x) = e (γ x) := by
  simp [mulAutCongr]

theorem out_of_hasSL2Model {K : Type} [Group K] {P : ℕ → Prop} (hP : ∀ n, P n → Odd n)
    (h : HasSL2Model K P) (α β : MulAut K) : ∃ y : K, α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  obtain ⟨F, hF, hFin, hPF, ⟨e0⟩⟩ := h
  let e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F := e0.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  obtain ⟨y', hy'⟩ := CFSG.ComponentClassification.RankTwoOddLie.sl2OuterComm F (hP _ hPF)
    (mulAutCongr e α) (mulAutCongr e β)
  refine ⟨e.symm y', ?_⟩
  ext x
  apply e.injective
  have h1 : e ((α * β * α⁻¹ * β⁻¹) x) = (mulAutCongr e (α * β * α⁻¹ * β⁻¹)) (e x) :=
    (mulAutCongr_apply e _ x).symm
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hy']
  simp [MulAut.conj_apply]


theorem mul_self_eq_one_of_card_le_two {Z : Type*} [Group Z] [Finite Z] (hZ : Nat.card Z ≤ 2) (w : Z) : w * w = 1 := by
  have h := pow_card_eq_one' (G := Z) (x := w)
  have hpos : 0 < Nat.card Z := Nat.card_pos
  interval_cases hc : Nat.card Z
  · rw [pow_one] at h; rw [h, one_mul]
  · rw [← sq]; exact h

theorem PairShape.of_stage1Pair {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Stage1Pair G z S q L₁ L₂) : PairShape L₁ L₂ := by
  have hmem : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ ∨ K = L₂ := by
    intro K hK
    have : K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := hK
    rw [h.comps] at this
    simpa using this
  have hc₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [h.comps]; exact Set.mem_insert _ _
    exact this
  have hc₂ : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [h.comps]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact this
  have hctr : ∀ {L : Subgroup (CentralizerBar z)}, HasSL2Model ↥L (fun r => r = q) →
      ∀ a ∈ L, (∀ l ∈ L, a * l = l * a) → a * a = 1 := by
    intro L hL a ha hcomm
    have hcard := CFSG.GH74.GLS.Stage2.Final.L26.card_center_le_two_of_hasSL2Model hL
    have hw : (⟨a, ha⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    have := mul_self_eq_one_of_card_le_two hcard (⟨⟨a, ha⟩, hw⟩ : ↥(center ↥L))
    have h2 := congrArg (fun w : ↥(center ↥L) => ((w : ↥L) : CentralizerBar z)) this
    simpa using h2
  exact
    { c₁ := hc₁
      c₂ := hc₂
      ne := h.ne
      comps := hmem
      fitting := by rw [h.fitting, h.prod.1]
      center₁ := hctr h.sl₁
      center₂ := hctr h.sl₂
      out₁ := out_of_hasSL2Model (fun n (hn : n = q) => hn ▸ h.odd) h.sl₁
      out₂ := out_of_hasSL2Model (fun n (hn : n = q) => hn ▸ h.odd) h.sl₂ }


section Lift

variable {X : Type} [Group X] {L₁ L₂ : Subgroup (X ⧸ pPrimeCore 2 X)} {Γ₁ Γ₂ : Subgroup X}

structure TwoComps (L₁ L₂ : Subgroup (X ⧸ pPrimeCore 2 X)) (Γ₁ Γ₂ : Subgroup X) : Prop where
  c₁ : IsComponent Γ₁
  c₂ : IsComponent Γ₂
  map₁ : Γ₁.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₁
  map₂ : Γ₂.map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₂
  all : ∀ Γ : Subgroup X, IsComponent Γ → Γ = Γ₁ ∨ Γ = Γ₂
  ne : Γ₁ ≠ Γ₂
  comm : ⁅Γ₁, Γ₂⁆ = ⊥

theorem map_cj (t : X) (Γ : Subgroup X) :
    (cj t Γ).map (QuotientGroup.mk' (pPrimeCore 2 X)) =
      cj (QuotientGroup.mk' (pPrimeCore 2 X) t) (Γ.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  unfold cj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem TwoComps.layer_eq (T : TwoComps L₁ L₂ Γ₁ Γ₂) : layer X = Γ₁ ⊔ Γ₂ := by
  apply le_antisymm
  · refine sSup_le fun Γ hΓ => ?_
    rcases T.all Γ hΓ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (component_le_layer T.c₁) (component_le_layer T.c₂)

theorem TwoComps.map_layer (T : TwoComps L₁ L₂ Γ₁ Γ₂) :
    (layer X).map (QuotientGroup.mk' (pPrimeCore 2 X)) = L₁ ⊔ L₂ := by
  rw [T.layer_eq, Subgroup.map_sup, T.map₁, T.map₂]

theorem TwoComps.perfect_le [Finite X] (h : PairShape L₁ L₂) (T : TwoComps L₁ L₂ Γ₁ Γ₂)
    {P : Subgroup X} (hP : ⁅P, P⁆ = P) : P ≤ layer X := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have h1 : ⁅P.map π, P.map π⁆ = P.map π := by rw [← Subgroup.map_commutator, hP]
  have h2 : P.map π ≤ L₁ ⊔ L₂ := h.perfect_le h1
  have h3 : P ≤ ((layer X).map π).comap π := by
    rw [T.map_layer]
    exact Subgroup.map_le_iff_le_comap.mp h2
  rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h3
  have hc : (layer X).Characteristic := layer_characteristic
  have hn : (layer X).Normal := inferInstance
  exact CFSG.GH74.GLS.Stage2.Final.Thm4.perfect_le_of_le_sup_solvable
    (CFSG.GH74.GLS.Stage2.Final.Thm4.pPrimeCore_solvable (X := X))
    (Subgroup.isPerfect_iff.mpr hP) h3

theorem TwoComps.cj_swap [Finite X] (h : PairShape L₁ L₂) (T : TwoComps L₁ L₂ Γ₁ Γ₂) {t : X}
    (ht : cj (QuotientGroup.mk' (pPrimeCore 2 X) t) L₁ = L₂) : cj t Γ₁ = Γ₂ ∧ cj t Γ₂ = Γ₁ := by
  have ht2 : cj (QuotientGroup.mk' (pPrimeCore 2 X) t) L₂ = L₁ := h.cj_swap ht
  refine ⟨comp_eq_of_map_eq (isComponent_cj T.c₁ t) T.c₂ ?_, comp_eq_of_map_eq (isComponent_cj T.c₂ t) T.c₁ ?_⟩
  · rw [map_cj, T.map₁, ht, T.map₂]
  · rw [map_cj, T.map₂, ht2, T.map₁]

theorem TwoComps.cj_fix_of_odd [Finite X] (h : PairShape L₁ L₂) (T : TwoComps L₁ L₂ Γ₁ Γ₂) {x : X}
    (hx : Odd (orderOf x)) : cj x Γ₁ = Γ₁ ∧ cj x Γ₂ = Γ₂ := by
  have hodd : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x)) :=
    Odd.of_dvd_nat hx (orderOf_map_dvd _ _)
  have h1 := h.cj_fix_of_odd hodd
  have h2 := h.cj_fix h1
  refine ⟨comp_eq_of_map_eq (isComponent_cj T.c₁ x) T.c₁ ?_, comp_eq_of_map_eq (isComponent_cj T.c₂ x) T.c₂ ?_⟩
  · rw [map_cj, T.map₁, h1]
  · rw [map_cj, T.map₂, h2]

theorem TwoComps.mem_odd_of_centralizes [Finite X] (h : PairShape L₁ L₂) (T : TwoComps L₁ L₂ Γ₁ Γ₂) {x : X}
    (hx : Odd (orderOf x)) (h1 : ∀ a ∈ Γ₁, x * a = a * x) (h2 : ∀ a ∈ Γ₂, x * a = a * x) :
    x ∈ pPrimeCore 2 X := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hodd : Odd (orderOf (π x)) := Odd.of_dvd_nat hx (orderOf_map_dvd _ _)
  have hπ1 : π x = 1 := by
    refine h.eq_one_of_odd_centralizes hodd (fun a ha => ?_) (fun a ha => ?_)
    · rw [← T.map₁] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      rw [← map_mul, ← map_mul, h1 a' ha']
    · rw [← T.map₂] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      rw [← map_mul, ← map_mul, h2 a' ha']
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ1

end Lift

theorem layer_comm_pPrimeCore {X : Type} [Group X] [Finite X] :
    ∀ a ∈ pPrimeCore 2 X, ∀ l ∈ layer X, a * l = l * a := by
  intro a ha l hl
  have hn : (pPrimeCore 2 X).Normal := inferInstance
  have h := (component_solvable_centralizer (G := X) (R := pPrimeCore 2 X)
    (CFSG.GH74.GLS.Stage2.Final.Thm4.pPrimeCore_solvable) hn.isSubnormal).2
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hl
  exact Subgroup.mem_centralizer_iff.mp this a ha

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
