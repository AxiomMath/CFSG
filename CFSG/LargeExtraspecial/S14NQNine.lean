module

public import CFSG.LargeExtraspecial.S14Nine
public import CFSG.LargeExtraspecial.S14W4SetNQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

structure Lattice6 (S : Setting G) (g : G) (t : S.O) (U₁ U₂ : Subgroup S.O) : Prop where
  t_le₁ : zpowers t ≤ U₁
  le₁ : U₁ ≤ Nbar S g t
  t_le₂ : zpowers t ≤ U₂
  le₂ : U₂ ≤ Nbar S g t
  inv₁ : ∀ r ∈ Rbar S g t, ∀ u ∈ U₁, r * u * r⁻¹ ∈ U₁
  inv₂ : ∀ r ∈ Rbar S g t, ∀ u ∈ U₂, r * u * r⁻¹ ∈ U₂
  inf_eq : U₁ ⊓ U₂ = zpowers t
  card₁ : Nat.card U₁ = 2 ^ 5
  card₂ : Nat.card U₂ = 2 ^ 5
  cases : ∀ D : Subgroup S.O, zpowers t ≤ D → D ≤ Nbar S g t →
    (∀ r ∈ Rbar S g t, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
      D = zpowers t ∨ D = U₁ ∨ D = U₂ ∨ D = Nbar S g t

namespace Lattice6

variable {U₁ U₂ : Subgroup S.O}

theorem symm (L : Lattice6 S g t U₁ U₂) : Lattice6 S g t U₂ U₁ where
  t_le₁ := L.t_le₂
  le₁ := L.le₂
  t_le₂ := L.t_le₁
  le₂ := L.le₁
  inv₁ := L.inv₂
  inv₂ := L.inv₁
  inf_eq := by rw [inf_comm]; exact L.inf_eq
  card₁ := L.card₂
  card₂ := L.card₁
  cases D h1 h2 h3 := by
    rcases L.cases D h1 h2 h3 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

theorem ne_zpowers (L : Lattice6 S g t U₁ U₂) (hct : Nat.card (zpowers t) = 2) :
    U₁ ≠ zpowers t := by
  intro h
  have h1 := L.card₁
  rw [h, hct] at h1
  norm_num at h1

theorem not_le (L : Lattice6 S g t U₁ U₂) (hct : Nat.card (zpowers t) = 2) : ¬ U₂ ≤ U₁ :=
  fun h => L.symm.ne_zpowers hct (by rw [← L.inf_eq, inf_eq_right.mpr h])

theorem eq_of_le (L : Lattice6 S g t U₁ U₂) (hct : Nat.card (zpowers t) = 2) {D : Subgroup S.O}
    (h1 : zpowers t ≤ D) (h2 : D ≤ U₁) (h3 : ∀ r ∈ Rbar S g t, ∀ d ∈ D, r * d * r⁻¹ ∈ D) :
    D = zpowers t ∨ D = U₁ := by
  rcases L.cases D h1 (h2.trans L.le₁) h3 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h ▸ h2) (L.not_le hct)
  · exact absurd (L.le₂.trans (h ▸ h2)) (L.not_le hct)

theorem sup_eq (L : Lattice6 S g t U₁ U₂) (hct : Nat.card (zpowers t) = 2) :
    U₁ ⊔ U₂ = Nbar S g t := by
  have hinv : ∀ r ∈ Rbar S g t, ∀ d ∈ U₁ ⊔ U₂, r * d * r⁻¹ ∈ U₁ ⊔ U₂ := by
    intro r hr d hd
    have hle : (U₁ ⊔ U₂).map (MulAut.conj r).toMonoidHom ≤ U₁ ⊔ U₂ := by
      rw [Subgroup.map_sup]
      refine sup_le_sup (map_le_iff_le_comap.mpr fun u hu => L.inv₁ r hr u hu)
        (map_le_iff_le_comap.mpr fun u hu => L.inv₂ r hr u hu)
    exact hle ⟨d, hd, rfl⟩
  rcases L.cases _ (L.t_le₁.trans le_sup_left) (sup_le L.le₁ L.le₂) hinv with h | h | h | h
  · exact absurd (by rw [← h]; exact le_sup_left) (L.ne_zpowers hct ∘ fun h' =>
      le_antisymm h' L.t_le₁)
  · exact absurd (h ▸ le_sup_right) (L.not_le hct)
  · exact absurd (h ▸ le_sup_left) (L.symm.not_le hct)
  · exact h

end Lattice6

theorem conj_mem_Rbar_of_mem_Ct {c r : S.O} (hc : c ∈ Ct S t) (hr : r ∈ Rbar S g t) :
    c * r * c⁻¹ ∈ Rbar S g t := by
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = c := hc.1
  have hkt : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact mem_centralizer_singleton_iff.mp hc.2
  have := conj_mem_Rbar hkt hr
  rwa [hk] at this

theorem false_of_commutator_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) (hct : Nat.card (zpowers t) = 2)
    (htN : t ∈ Nbar S g t) (hN2 : IsPGroup 2 (Nbar S g t)) (h7 : Concl14_7 S g t)
    {U₁ U₂ : Subgroup S.O} (L : Lattice6 S g t U₁ U₂)
    (hD : ⁅Nbar S g t, FCt S t⁆ = U₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := FCt S t with hFdef
  have hNF : Nbar S g t ≤ F := Nbar_le_FCt haQ hN2
  have hFC : F ≤ Ct S t := map_subtype_le _
  have hF2 : IsPGroup 2 F := h7.2.map _
  have hFt : ∀ f ∈ F, f * t = t * f := fun f hf => mem_centralizer_singleton_iff.mp (hFC hf).2
  have hFN : ∀ f ∈ F, ∀ n ∈ Nbar S g t, f * n * f⁻¹ ∈ Nbar S g t :=
    fun f hf n hn => conj_mem_Nbar_of_mem_Ct haQ (hFC hf) hn
  have hFR : ∀ f ∈ F, ∀ r ∈ Rbar S g t, f * r * f⁻¹ ∈ Rbar S g t :=
    fun f hf r hr => conj_mem_Rbar_of_mem_Ct (hFC hf) hr
  have hNt : ∀ n ∈ Nbar S g t, n * t = t * n :=
    fun n hn => commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
  have hU₁F : ∀ f ∈ F, ∀ u ∈ U₁, f * u * f⁻¹ ∈ U₁ := by
    intro f hf u hu
    have h1 : u * f * u⁻¹ * f⁻¹ ∈ U₁ := by
      rw [← hD]
      have := commutator_mem_commutator (L.le₁ hu) hf
      rwa [commutatorElement_def] at this
    have e : f * u * f⁻¹ = (u * f * u⁻¹ * f⁻¹)⁻¹ * u := by group
    rw [e]
    exact mul_mem (inv_mem h1) hu
  have hU₂F : ∀ f ∈ F, ∀ u ∈ U₂, f * u * f⁻¹ ∈ U₂ := by
    intro f hf
    set U₂' := U₂.map (MulAut.conj f).toMonoidHom with hU₂'
    have hmem : ∀ x, x ∈ U₂' ↔ f⁻¹ * x * f ∈ U₂ := by
      intro x
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [mul_assoc] using hu
      · intro hx
        exact ⟨_, hx, by simp [mul_assoc]⟩
    have hconj : ∀ u ∈ U₂, f * u * f⁻¹ ∈ U₂' := fun u hu =>
      (hmem _).mpr (by simpa [mul_assoc] using hu)
    have h1 : zpowers t ≤ U₂' := by
      rw [zpowers_le, hmem, mul_assoc, ← hFt f hf, inv_mul_cancel_left]
      exact L.t_le₂ (mem_zpowers t)
    have h2 : U₂' ≤ Nbar S g t := by
      rintro _ ⟨u, hu, rfl⟩
      exact hFN f hf u (L.le₂ hu)
    have h3 : ∀ r ∈ Rbar S g t, ∀ d ∈ U₂', r * d * r⁻¹ ∈ U₂' := by
      intro r hr d hd
      rw [hmem] at hd ⊢
      have hr' : f⁻¹ * r * f ∈ Rbar S g t := by
        have := hFR f⁻¹ (inv_mem hf) r hr
        rwa [inv_inv] at this
      have e : f⁻¹ * (r * d * r⁻¹) * f =
          (f⁻¹ * r * f) * (f⁻¹ * d * f) * (f⁻¹ * r * f)⁻¹ := by group
      rw [e]
      exact L.inv₂ _ hr' _ hd
    have hcard : Nat.card U₂' = 2 ^ 5 := by
      rw [hU₂', Subgroup.card_map_of_injective (f := (MulAut.conj f).toMonoidHom)
        (MulAut.conj f).injective]
      exact L.card₂
    rcases L.cases U₂' h1 h2 h3 with h | h | h | h
    · rw [h, hct] at hcard
      norm_num at hcard
    · refine absurd (fun u hu => ?_) (L.not_le hct)
      have h4 : f * u * f⁻¹ ∈ U₁ := h ▸ hconj u hu
      have := hU₁F f⁻¹ (inv_mem hf) _ h4
      simpa [mul_assoc] using this
    · intro u hu
      rw [← h]
      exact hconj u hu
    · have heq : U₁ = U₂' :=
        Subgroup.eq_of_le_of_card_ge (h ▸ L.le₁) (by rw [hcard, L.card₁])
      exact absurd (L.le₂.trans (h ▸ heq.ge)) (L.not_le hct)
  have hU₂c : ∀ f ∈ F, ∀ u ∈ U₂, u * f * u⁻¹ * f⁻¹ ∈ zpowers t := by
    intro f hf u hu
    rw [← L.inf_eq]
    refine ⟨?_, ?_⟩
    · rw [← hD]
      have := commutator_mem_commutator (L.le₂ hu) hf
      rwa [commutatorElement_def] at this
    · have e : u * f * u⁻¹ * f⁻¹ = u * (f * u⁻¹ * f⁻¹) := by group
      rw [e]
      exact mul_mem hu (hU₂F f hf _ (inv_mem hu))
  set M := ⁅U₁, F⁆ with hM
  have hMU : M ≤ U₁ := commutator_le.mpr fun u hu f hf => by
    rw [commutatorElement_def]
    have e : u * f * u⁻¹ * f⁻¹ = u * (f * u⁻¹ * f⁻¹) := by group
    rw [e]
    exact mul_mem hu (hU₁F f hf _ (inv_mem hu))
  have hRM : ∀ r ∈ Rbar S g t, ∀ d ∈ M, r * d * r⁻¹ ∈ M := fun r hr d hd =>
    conj_mem_commutator (fun u hu => L.inv₁ r hr u hu) (fun f hf => conj_mem_FCt haQ hr hf) hd
  have hinv : ∀ r ∈ Rbar S g t, ∀ d ∈ M ⊔ zpowers t, r * d * r⁻¹ ∈ M ⊔ zpowers t := by
    intro r hr d hd
    have hle : (M ⊔ zpowers t).map (MulAut.conj r).toMonoidHom ≤ M ⊔ zpowers t := by
      rw [Subgroup.map_sup]
      refine sup_le_sup (map_le_iff_le_comap.mpr fun u hu => hRM r hr u hu)
        (map_le_iff_le_comap.mpr ?_)
      rw [zpowers_le]
      change r * t * r⁻¹ ∈ zpowers t
      rw [commute_of_mem_Rbar haQ hr, mul_inv_cancel_right]
      exact mem_zpowers t
    exact hle ⟨d, hd, rfl⟩
  rcases L.eq_of_le hct le_sup_right (sup_le hMU L.t_le₁) hinv with h | h
  ·
    have hMt : M ≤ zpowers t := le_sup_left.trans h.le
    let C' : Subgroup S.O :=
      { carrier := {n | n ∈ Nbar S g t ∧ ∀ f ∈ F, n * f * n⁻¹ * f⁻¹ ∈ zpowers t}
        mul_mem' := by
          rintro x y ⟨hx, hxf⟩ ⟨hy, hyf⟩
          refine ⟨mul_mem hx hy, fun f hf => ?_⟩
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hyf f hf)
          have hxc : x * t ^ k * x⁻¹ = t ^ k := by
            rw [(Commute.zpow_right (hNt x hx) k).eq, mul_inv_cancel_right]
          have e : x * y * f * (x * y)⁻¹ * f⁻¹ =
              (x * (y * f * y⁻¹ * f⁻¹) * x⁻¹) * (x * f * x⁻¹ * f⁻¹) := by group
          rw [e, ← hk, hxc]
          exact mul_mem (zpow_mem_zpowers t k) (hxf f hf)
        one_mem' := ⟨one_mem _, fun f _ => by simp⟩
        inv_mem' := by
          rintro x ⟨hx, hxf⟩
          refine ⟨inv_mem hx, fun f hf => ?_⟩
          obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hxf f hf)
          have e : x⁻¹ * f * x⁻¹⁻¹ * f⁻¹ = x⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹ * x := by group
          have hxc : x⁻¹ * t ^ (-k) * x = t ^ (-k) := by
            rw [mul_assoc, ← (Commute.zpow_right (hNt x hx) (-k)).eq, inv_mul_cancel_left]
          rw [e, ← hk, ← zpow_neg, hxc]
          exact zpow_mem_zpowers t (-k) }
    have hU₁C : U₁ ≤ C' := fun u hu => ⟨L.le₁ hu, fun f hf => hMt (by
      have := commutator_mem_commutator hu hf
      rwa [commutatorElement_def] at this)⟩
    have hU₂C : U₂ ≤ C' := fun u hu => ⟨L.le₂ hu, fun f hf => hU₂c f hf u hu⟩
    have hNC : Nbar S g t ≤ C' := L.sup_eq hct ▸ sup_le hU₁C hU₂C
    have hDt : U₁ ≤ zpowers t := by
      rw [← hD]
      refine commutator_le.mpr fun n hn f hf => ?_
      rw [commutatorElement_def]
      exact (hNC hn).2 f hf
    exact L.ne_zpowers hct (le_antisymm hDt L.t_le₁)
  ·
    have hFF : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ ∈ F := fun f hf f' hf' =>
      mul_mem (mul_mem hf hf') (inv_mem hf)
    have hFM : ∀ f ∈ F, ∀ d ∈ M, f * d * f⁻¹ ∈ M := fun f hf d hd =>
      conj_mem_commutator (fun u hu => hU₁F f hf u hu) (hFF f hf) hd
    set M₂ := ⁅M, F⁆ with hM₂
    have hFM₂ : ∀ f ∈ F, ∀ d ∈ M₂, f * d * f⁻¹ ∈ M₂ := fun f hf d hd =>
      conj_mem_commutator (fun u hu => hFM f hf u hu) (hFF f hf) hd
    let C'' : Subgroup S.O :=
      { carrier := {u | u ∈ F ∧ ∀ f ∈ F, u * f * u⁻¹ * f⁻¹ ∈ M₂}
        mul_mem' := by
          rintro x y ⟨hx, hxf⟩ ⟨hy, hyf⟩
          refine ⟨mul_mem hx hy, fun f hf => ?_⟩
          have e : x * y * f * (x * y)⁻¹ * f⁻¹ =
              (x * (y * f * y⁻¹ * f⁻¹) * x⁻¹) * (x * f * x⁻¹ * f⁻¹) := by group
          rw [e]
          exact mul_mem (hFM₂ x hx _ (hyf f hf)) (hxf f hf)
        one_mem' := ⟨one_mem _, fun f _ => by simp⟩
        inv_mem' := by
          rintro x ⟨hx, hxf⟩
          refine ⟨inv_mem hx, fun f hf => ?_⟩
          have e : x⁻¹ * f * x⁻¹⁻¹ * f⁻¹ = x⁻¹ * (x * f * x⁻¹ * f⁻¹)⁻¹ * x⁻¹⁻¹ := by group
          rw [e]
          exact hFM₂ _ (inv_mem hx) _ (inv_mem (hxf f hf)) }
    have hMC : M ≤ C'' := fun d hd => ⟨hNF (L.le₁ (hMU hd)), fun f hf => by
      have := commutator_mem_commutator hd hf
      rwa [commutatorElement_def] at this⟩
    have htC : zpowers t ≤ C'' := by
      rw [zpowers_le]
      refine ⟨hNF htN, fun f hf => ?_⟩
      rw [← hFt f hf, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    have hU₁C : U₁ ≤ C'' := h ▸ sup_le hMC htC
    have hMM₂ : M ≤ M₂ := commutator_le.mpr fun u hu f hf => by
      rw [commutatorElement_def]
      exact (hU₁C hu).2 f hf
    have hM₂M : M₂ ≤ M := commutator_mono hMU le_rfl
    have hM1 : M ≠ ⊥ := by
      intro h0
      rw [h0, bot_sup_eq] at h
      exact L.ne_zpowers hct h.symm
    exact commutator_ne_of_le hF2 (hMU.trans (L.le₁.trans hNF)) hM1 (le_antisymm hM₂M hMM₂)

theorem claim14_9Plus6_of_nqPlus6 (hNQ6 : NQPlus6Stmt) : Claim14_9Plus6 := by
  intro G _ _ _ S g t hSt hocc hext _ h7 _
  obtain ⟨U₁, U₂, h1, h2, h3, h4, h5, h6, h7', h8, h9, h10⟩ := hNQ6 G S g t hSt hocc hext
  have L : Lattice6 S g t U₁ U₂ := ⟨h1, h2, h3, h4, h5, h6, h7', h8, h9, h10⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := hSt.hyp4.conj_mem
  have ht1 := hSt.ne_one
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have hct : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hNF := Nbar_le_FCt haQ hext.1
  have hFC : FCt S t ≤ Ct S t := map_subtype_le _
  have hF2 : IsPGroup 2 (FCt S t) := h7.2.map _
  have hDN : ⁅Nbar S g t, FCt S t⁆ ≤ Nbar S g t := commutator_le.mpr fun n hn f hf => by
    have e : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hn (conj_mem_Nbar_of_mem_Ct haQ (hFC hf) (inv_mem hn))
  have htD : zpowers t ≤ ⁅Nbar S g t, FCt S t⁆ := by
    rw [zpowers_le]
    obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN ht1 fun y hy =>
      (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
    have := commutator_mem_commutator ha (hNF hb)
    rwa [commutatorElement_def, hab] at this
  have hDR : ∀ r ∈ Rbar S g t, ∀ d ∈ ⁅Nbar S g t, FCt S t⁆,
      r * d * r⁻¹ ∈ ⁅Nbar S g t, FCt S t⁆ :=
    fun r hr _ hd => conj_mem_commutator (fun _ hn => conj_mem_Nbar_of_mem_Rbar haQ hr hn)
      (fun _ hf => conj_mem_FCt haQ hr hf) hd
  have hN1 : Nbar S g t ≠ ⊥ := fun h => ht1 (by rwa [h, mem_bot] at htN)
  rcases L.cases _ htD hDN hDR with hDt | hD1 | hD2 | hDe
  · refine le_antisymm (fun f hf => h7.1 f (hFC hf).1 fun y hy => ?_) hNF
    rw [← hDt]
    have := commutator_mem_commutator hy hf
    rw [commutatorElement_def] at this
    have e : f * y * f⁻¹ * y⁻¹ = (y * f * y⁻¹ * f⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem this
  · exact (false_of_commutator_eq haQ hct htN hext.1 h7 L hD1).elim
  · exact (false_of_commutator_eq haQ hct htN hext.1 h7 L.symm hD2).elim
  · exact absurd hDe (commutator_ne_of_le hF2 hNF hN1)

end CFSG.LargeExtraspecial.S14
