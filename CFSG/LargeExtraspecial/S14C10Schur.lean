module

public import CFSG.LargeExtraspecial.S14Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

theorem comm_mem_zpowers_of_irred {X : Type*} [Group X] {N R : Subgroup X} {t x : X}
    (htN : t ∈ N) (htc : ∀ n ∈ N, n * t = t * n)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ zpowers t)
    (hsq : ∀ a ∈ N, a * a ∈ zpowers t) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hxt : x * t = t * x) (hx2 : x * x ∈ N) (hxR : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ N)
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hRt : ∀ r ∈ R, r * t = t * r)
    (hirr : ∀ D : Subgroup X, zpowers t ≤ D → D ≤ N →
      (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) → D = zpowers t ∨ D = N) :
    ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ zpowers t := by
  have hz : ∀ c ∈ zpowers t, ∀ y : X, y * t = t * y → y * c * y⁻¹ = c := by
    rintro c ⟨i, rfl⟩ y hy
    simp only
    rw [((Commute.zpow_right (show Commute y t from hy) i)).eq, mul_inv_cancel_right]
  have hzN : ∀ c ∈ zpowers t, ∀ n ∈ N, n * c * n⁻¹ = c := fun c hc n hn => hz c hc n (htc n hn)
  let D : Subgroup X :=
    { carrier := {n | n ∈ N ∧ x * n * x⁻¹ * n⁻¹ ∈ zpowers t}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e, hzN _ hb' a ha]
        exact mul_mem ha' hb'
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e, hzN _ (inv_mem ha') a⁻¹ (inv_mem ha)]
        exact inv_mem ha' }
  have hD1 : zpowers t ≤ D := fun c hc =>
    ⟨zpowers_le.mpr htN hc, by rw [hz c hc x hxt, mul_inv_cancel]; exact one_mem _⟩
  have hD2 : D ≤ N := fun _ hd => hd.1
  have hD3 : ∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D := by
    rintro r hr d ⟨hd, hd'⟩
    have hm := hxR r hr
    have he := hRN r hr d hd
    refine ⟨he, ?_⟩
    have e : x * (r * d * r⁻¹) * x⁻¹ * (r * d * r⁻¹)⁻¹ =
        ((x * r * x⁻¹ * r⁻¹) * (r * (x * d * x⁻¹ * d⁻¹) * r⁻¹) * (x * r * x⁻¹ * r⁻¹)⁻¹) *
          ((x * r * x⁻¹ * r⁻¹) * (r * d * r⁻¹) * (x * r * x⁻¹ * r⁻¹)⁻¹ * (r * d * r⁻¹)⁻¹) := by
      group
    rw [e, hz _ hd' r (hRt r hr), hzN _ hd' _ hm]
    exact mul_mem hd' (hcomm _ hm _ he)
  rcases hirr D hD1 hD2 hD3 with hD | hD
  · intro n hn
    by_contra hcon
    have hm : x * n * x⁻¹ * n⁻¹ ∈ N := mul_mem (hxN n hn) (inv_mem hn)
    have hmD : x * n * x⁻¹ * n⁻¹ ∈ D := by
      refine ⟨hm, ?_⟩
      have hu : x * n * x⁻¹ ∈ N := hxN n hn
      have e : x * (x * n * x⁻¹ * n⁻¹) * x⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ =
          ((x * x) * n * (x * x)⁻¹ * n⁻¹) * ((n * (x * n * x⁻¹)⁻¹) * (n * (x * n * x⁻¹)⁻¹)) := by
        group
      rw [e]
      exact mul_mem (hcomm _ hx2 _ hn) (hsq _ (mul_mem hn (inv_mem hu)))
    rw [hD] at hmD
    exact hcon hmD
  · intro n hn
    rw [← hD] at hn
    exact hn.2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_zpowers_of_mem_center_Nbar {t : S.O} (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (htN : t ∈ Nbar S g t) (ht1 : t ≠ 1) (htc : ∀ y ∈ Nbar S g t, t * y = y * t)
    {c : Nbar S g t} (hc : c ∈ center (Nbar S g t)) : (c : S.O) ∈ zpowers t := by
  have htc' : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (htc v v.2).symm
  by_cases h1 : c = 1
  · rw [h1]
    exact one_mem _
  · have := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hext hc htc' h1
      (fun e => ht1 (congrArg Subtype.val e))
    rw [this]
    exact mem_zpowers t

theorem mem_Nbar_of_sq_mem (hNQ : NQIrredStmt) [IsSimpleGroup G] {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (h8b : c ≠ .omegaPlus8b) (h6 : c ≠ .omegaPlus6) (h7 : Concl14_7 S g t) {x : S.O}
    (hx : x ∈ Ct S t) (hx2 : x * x ∈ Nbar S g t)
    (hxR : ∀ r ∈ Rbar S g t, x * r * x⁻¹ * r⁻¹ ∈ Nbar S g t) : x ∈ Nbar S g t := by
  have haQ := hSt.hyp4.conj_mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have hcen : ∀ c : Nbar S g t, c ∈ center (Nbar S g t) → (c : S.O) ∈ zpowers t :=
    fun _ hc => mem_zpowers_of_mem_center_Nbar hext htN hSt.ne_one htc hc
  refine h7.1 x hx.1 (comm_mem_zpowers_of_irred (R := Rbar S g t) htN
    (fun n hn => (htc n hn).symm) ?_ ?_ (fun n hn => conj_mem_Nbar_of_mem_Ct haQ hx hn)
    (mem_centralizer_singleton_iff.mp hx.2) hx2 hxR
    (fun r hr n hn => conj_mem_Nbar_of_mem_Rbar haQ hr hn)
    (fun r hr => commute_of_mem_Rbar haQ hr)
    (fun D h1 h2 h3 => hNQ G S g t c hSt hocc hext h8b h6 D h1 h2 h3))
  · intro a ha b hb
    have := hcen _ (CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center hext
      ⟨a, ha⟩ ⟨b, hb⟩)
    simpa [commutatorElement_def] using this
  · intro a ha
    have := hcen _ (CFSG.RankThree.Literature.FSmith.sq_mem_center hext ⟨a, ha⟩)
    simpa [pow_two] using this

end CFSG.LargeExtraspecial.S14
