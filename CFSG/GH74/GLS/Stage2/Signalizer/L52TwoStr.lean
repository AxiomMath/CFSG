module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27

section Aux

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_of_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : Commute a b := hAB a ha b hb
        rw [mul_inv_rev]
        exact hc.inv_inv.eq.symm }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBP : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact (sup_le hAP hBP) hx

end Aux

section Main

variable {G : Type} [Group G] [Finite G]

theorem hstr_of_direct_product {z t : G} {S T D : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ((U4 z t : Subgroup G) : Set G)))
    (hTS : T ≤ S)
    (hD : CFSG.GH74.GLS.IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
      (S ⊓ centralizer ({t} : Set G))) :
    Hstr z t := by
  obtain ⟨hsup, hcomm, hinf⟩ := hD
  intro Q hQC hQ2 hUQ hQU
  have htU : t ∈ U4 z t := mem_sup_right (mem_zpowers t)
  have hTE : ∀ y ∈ T, y ∈ U4 z t ⊔ D := by
    intro y hy
    rw [hsup]
    refine Subgroup.mem_inf.2 ⟨hTS hy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (hT.le hy) t htU).symm
  obtain ⟨q, hqQ, hqU⟩ : ∃ q ∈ Q, q ∉ U4 z t := by
    by_contra hcon
    exact hQU (le_antisymm (fun q hq => by_contra fun h => hcon ⟨q, hq, h⟩) hUQ)
  obtain ⟨c, hcC, hcT⟩ := exists_conj_le_of_isSylowOf hT hQC hQ2
  have hcU : ∀ y ∈ U4 z t, c⁻¹ * y * c = y := by
    intro y hy
    have h := Subgroup.mem_centralizer_iff.1 hcC y hy
    calc c⁻¹ * y * c = c⁻¹ * (y * c) := by group
      _ = y := by rw [h]; group
  obtain ⟨u, hu', d, hd, hqud⟩ := exists_mul_of_mem_sup_of_comm hcomm (hTE _ (hcT q hqQ))
  have hd0Q : u⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem (hUQ hu')) hqQ
  have hcd : c⁻¹ * (u⁻¹ * q) * c = d := by
    have h1 : c⁻¹ * (u⁻¹ * q) * c = (c⁻¹ * u⁻¹ * c) * (c⁻¹ * q * c) := by group
    rw [h1, hcU _ (Subgroup.inv_mem _ hu'), hqud]
    group
  have hd01 : u⁻¹ * q ≠ 1 := by
    intro h
    apply hqU
    have : q = u := by
      have h' : q = u * (u⁻¹ * q) := by group
      rw [h', h, mul_one]
    rw [this]
    exact hu'
  have hdvd : 2 ∣ orderOf (u⁻¹ * q) := by
    have hne : (⟨u⁻¹ * q, hd0Q⟩ : ↥Q) ≠ 1 := fun h => hd01 (congrArg Subtype.val h)
    have := hQ2.dvd_orderOf hne
    rwa [Subgroup.orderOf_mk] at this
  have he2 : orderOf ((u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hdvd
  refine ⟨(u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2), Q.pow_mem hd0Q _, he2, fun heU => ?_⟩
  have hcon : c⁻¹ * (u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2) * c = d ^ (orderOf (u⁻¹ * q) / 2) := by
    rw [← hcd]
    simpa using (conj_pow (a := c⁻¹) (b := u⁻¹ * q) (i := orderOf (u⁻¹ * q) / 2)).symm
  have heD : (u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2) ∈ D := by
    rw [← hcU _ heU, hcon]
    exact D.pow_mem hd _
  have h1 : (u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2) = 1 := by
    have : (u⁻¹ * q) ^ (orderOf (u⁻¹ * q) / 2) ∈ U4 z t ⊓ D := ⟨heU, heD⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  rw [h1, orderOf_one] at he2
  exact absurd he2 (by decide)

theorem hstr_of_ctx {z t : G} (_hu : UData z t) {S T : Subgroup G}
    (_hSz : ∀ s ∈ S, s * z = z * s) (_hzS : z ∈ S) (_htS : t ∈ S)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ((U4 z t : Subgroup G) : Set G)))
    (hTS : T ≤ S)
    (hD : ∃ D : Subgroup G, CFSG.GH74.GLS.IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
      (S ⊓ centralizer ({t} : Set G)) ∧ IsDihedral ↥D) :
    Hstr z t := by
  obtain ⟨D, hD', -⟩ := hD
  exact hstr_of_direct_product hT hTS hD'

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
