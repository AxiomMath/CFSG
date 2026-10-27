module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinThreeB
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinMap

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution

variable {Y : Type} [Group Y]

structure TwinHyp (L R : Subgroup Y) (S : Sylow 2 R) (t : Y) : Prop where
  datum : TightDatum R S t
  mem : t ∈ L
  not_central : ∃ l ∈ L, l * t ≠ t * l
  gen : GH74.Gen4 ↥L
  cent : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L
  rc : ∀ r ∈ R, (∀ l ∈ L, r * l = l * r) → r = 1
  zc : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → ∀ g : Y, g * z = z * g

variable {L : Subgroup Y} {F' : Type} [Field F'] {x t : Y} {J₂ J₄ : Subgroup Y} {R : Subgroup Y}
  {S : Sylow 2 R}

theorem Frame.good [Finite Y] [Finite F'] (hfr : Frame L F' x t J₂ J₄) [L.Normal]
    (hodd : Odd (Nat.card F')) (h3 : Nat.card F' = 3 → Frame3 L F' x t J₂ J₄)
    (hD : TightDatum R S t) (hgen : GH74.Gen4 ↥L)
    (hCL : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L)
    (hRC : ∀ r ∈ R, (∀ l ∈ L, r * l = l * r) → r = 1)
    (hA : FrameOuterQ8Free ↥L (J₂.subgroupOf L) (J₄.subgroupOf L)) : GoodThreeElement R t := by
  have hLn : L.Normal := inferInstance
  by_cases hc3 : Nat.card F' = 3
  · have hfr3 := h3 hc3
    rcases hfr3.inter_cases hLn hD with ⟨n, hnR, hnL, hn⟩ | hRL
    · exact hfr3.good hLn hD hnR hnL hn
    · exfalso
      obtain ⟨e₂⟩ := hfr.equiv₂
      obtain ⟨e₄⟩ := hfr.equiv₄
      exact hfr.false_of_outer hodd hD
        (comm_of_inter hD hLn hfr.le₂ hfr.cent₂ (oddGenerated_of_equiv_sl2 hodd e₂) hRL)
        (comm_of_inter hD hLn hfr.le₄ hfr.cent₄ (oddGenerated_of_equiv_sl2 hodd e₄) hRL)
        hgen hCL hRC hA
  · exfalso
    have h1 : 1 < Nat.card F' := Finite.one_lt_card
    have h4 : 4 ≤ Nat.card F' := by
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨h₂, h₄⟩ := hfr.datum_comm hLn hodd h4 hD
    exact hfr.false_of_outer hodd hD h₂ h₄ hgen hCL hRC hA

theorem TwinHyp.good_of_model [Finite Y] [Finite F'] [L.Normal] (h : TwinHyp L R S t)
    {K : Type} [Group K] (hodd : Odd (Nat.card F')) {x₀ y₀ : K} {J₂ J₄ : Subgroup K}
    (hfr : Frame (⊤ : Subgroup K) F' x₀ y₀ J₂ J₄)
    (h3 : Nat.card F' = 3 → Frame3 (⊤ : Subgroup K) F' x₀ y₀ J₂ J₄)
    (hconj : ∀ u : K, u * u = 1 → u ∉ Subgroup.center K → ∃ g, g * u * g⁻¹ = y₀)
    (hA : FrameOuterQ8Free K J₂ J₄) (e₀ : ↥L ≃* K) : GoodThreeElement R t := by
  obtain ⟨u, hu0⟩ : ∃ u : ↥L, (u : Y) = t := ⟨⟨t, h.mem⟩, rfl⟩
  have hu : e₀ u * e₀ u = 1 := by
    rw [← map_mul, show u * u = 1 from Subtype.ext (by
      rw [Subgroup.coe_mul, hu0]; exact t_mul_self h.datum), map_one]
  have huc : e₀ u ∉ Subgroup.center K := fun hc => by
    obtain ⟨l, hl, hlt⟩ := h.not_central
    apply hlt
    have h1 := Subgroup.mem_center_iff.mp hc (e₀ ⟨l, hl⟩)
    rw [← map_mul, ← map_mul, e₀.injective.eq_iff] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, hu0] at h2
  obtain ⟨g, hg⟩ := hconj _ hu huc
  set e : K ≃* ↥L := (MulAut.conj g).symm.trans e₀.symm with he
  have hey : ((e y₀ : ↥L) : Y) = t := by
    rw [← hg, ← hu0]
    simp [he, mul_assoc]
  have hfrL := hfr.map e
  rw [hey] at hfrL
  refine hfrL.good hodd (fun hc3 => ?_) h.datum h.gen h.cent h.rc (hA.map e)
  have hfr3 := h3 hc3
  have hx : ∀ y : Y, y * e x₀ = e x₀ * y := h.zc _ (e x₀).2 fun l hl => by
    obtain ⟨k, hk⟩ := e.surjective ⟨l, hl⟩
    have hk' : (e k : Y) = l := congrArg Subtype.val hk
    rw [← hk', ← coe_map_mul, ← coe_map_mul, hfr3.central k]
  have := hfr3.map e hx
  rwa [hey] at this

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
