module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

structure Setup (L A C : Subgroup G) (z : G) : Prop where
  hs : LocalSetting G L z
  hAL : A ≤ L
  hF : SextetFacts L A
  hC : CData A z C
  hCe : ∀ c ∈ C, c * c = 1

variable (h : Setup L A C z)
include h

theorem mem_A_of_comm {c : G} (hc : c ∈ C) (hcz : c * z = z * c) : c ∈ A := by
  have hcA : ∀ a ∈ A, c * a = a * c := fun a ha => Quad.lam_comm (h.hC.C_le hc) ha
  obtain ⟨l, hl, hcl | hcl⟩ := Quad.exists_mem_L h.hs hcz
  · rw [hcl] at hc hcA ⊢
    exact h.hF.cent l hl hcA
  · exfalso
    rw [hcl] at hc hcA
    have hlA : l ∈ A := by
      refine h.hF.cent l hl fun a ha => ?_
      have h1 : l * z * a = a * (l * z) := hcA a ha
      have h2 : z * a = a * z := Quad.z_comm_A h.hs h.hAL ha
      have : l * a * z = a * l * z := by
        calc l * a * z = l * (a * z) := by group
          _ = l * (z * a) := by rw [h2]
          _ = l * z * a := by group
          _ = a * (l * z) := h1
          _ = a * l * z := by group
      exact mul_right_cancel this
    apply h.hC.z_not_mem
    have e : z = l⁻¹ * (l * z) := by group
    rw [e]
    exact mul_mem (inv_mem (h.hC.A_le hlA)) hc

theorem mem_A_of_mem_L {c : G} (hc : c ∈ C) (hcL : c ∈ L) : c ∈ A :=
  mem_A_of_comm h hc (Quad.comm_z h.hs hcL)

theorem mem_egNL_of {l : G} (hlL : l ∈ L) (hlN : l ∈ normalizer (C : Set G)) :
    l ∈ egNL L A := by
  refine mem_inf.2 ⟨mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hlL⟩
  · exact mem_A_of_mem_L h ((mem_normalizer_iff.1 hlN x).1 (h.hC.A_le hx))
      (L.mul_mem (L.mul_mem hlL (h.hAL hx)) (L.inv_mem hlL))
  · have hxC : x ∈ C := (mem_normalizer_iff.1 hlN x).2 (h.hC.A_le hx)
    have hxL : x ∈ L := by
      have e : x = l⁻¹ * (l * x * l⁻¹) * l := by group
      rw [e]
      exact L.mul_mem (L.mul_mem (L.inv_mem hlL) (h.hAL hx)) hlL
    exact mem_A_of_mem_L h hxC hxL

theorem egM_le_normalizer_C : egM A z ≤ normalizer (C : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => h.hC.norm n hn x hx, fun hx => ?_⟩
  have := h.hC.norm n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using this

theorem z_mem_normalizer_C : z ∈ normalizer (C : Set G) :=
  egM_le_normalizer_C h Quad.z_mem_egM

theorem egNL_le_normalizer_C : egNL L A ≤ normalizer (C : Set G) := fun _ hn =>
  egM_le_normalizer_C h (Quad.nl_le_egM h.hs h.hAL hn)

@[expose] noncomputable def zt : egQD C :=
  QuotientGroup.mk (⟨z, z_mem_normalizer_C h⟩ : normalizer (C : Set G))

@[expose] noncomputable def psi : egNL L A →* egQD C :=
  (QuotientGroup.mk' (C.subgroupOf (normalizer (C : Set G)))).comp
    (inclusion (egNL_le_normalizer_C h))

theorem orderOf_zt : orderOf (zt h) = 2 := by
  apply orderOf_eq_prime
  · rw [zt, sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine mem_subgroupOf.2 ?_
    show z * z ∈ C
    rw [Quad.z_mul_self h.hs]
    exact one_mem _
  · rw [zt, Ne, QuotientGroup.eq_one_iff]
    exact fun hh => h.hC.z_not_mem (mem_subgroupOf.1 hh)

theorem psi_comm (y : egNL L A) : psi h y * zt h = zt h * psi h y := by
  rw [psi, zt, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Quad.nl_comm_z h.hs y.2)

theorem ker_psi : (psi h).ker = A.subgroupOf (egNL L A) := by
  ext y
  rw [MonoidHom.mem_ker, psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, coe_inclusion]
  exact ⟨fun hh => mem_A_of_mem_L h hh (mem_inf.1 y.2).2, fun hh => h.hC.A_le hh⟩

theorem centralizer_quot_eq : centralizer ({zt h} : Set (egQD C)) =
    (psi h).range ⊔ zpowers (zt h) := by
  have hzN := z_mem_normalizer_C h
  have hHN := egNL_le_normalizer_C h
  have hzi := Quad.z_inv h.hs
  have hzz := Quad.z_mul_self h.hs
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    rw [mem_centralizer_singleton_iff] at hx
    obtain ⟨⟨n, hnN⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : ((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (C : Set G))⁻¹ * (⟨z, hzN⟩ * ⟨n, hnN⟩)) ∈
        C.subgroupOf (normalizer (C : Set G)) :=
      QuotientGroup.eq.1 (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hx)
    have hc : z⁻¹ * n⁻¹ * z * n ∈ C := by
      have h2 := mem_subgroupOf.1 h1
      have e : (((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (C : Set G))⁻¹ *
          (⟨z, hzN⟩ * ⟨n, hnN⟩) : normalizer (C : Set G)) : G) = z⁻¹ * n⁻¹ * z * n := by
        show (n * z)⁻¹ * (z * n) = z⁻¹ * n⁻¹ * z * n
        group
      rwa [e] at h2
    have hwz : n * z⁻¹ * n⁻¹ * z ∈ C := by
      have h3 := (mem_normalizer_iff.1 hnN _).1 hc
      have e : n * (z⁻¹ * n⁻¹ * z * n) * n⁻¹ = n * z⁻¹ * n⁻¹ * z := by group
      rwa [e] at h3
    have hdC : z * (n * z * n⁻¹) ∈ C := by
      have h4 := inv_mem hwz
      have e : (n * z⁻¹ * n⁻¹ * z)⁻¹ = z * (n * z * n⁻¹) := by
        simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]
      rwa [e] at h4
    have hw2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
      calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
    set d := z * (n * z * n⁻¹) with hd_def
    have hzd : z * d = n * z * n⁻¹ := by rw [hd_def, ← mul_assoc, hzz, one_mul]
    have hd2 : d * d = 1 := h.hCe _ hdC
    have h5 : z * d * z * d = d * d := by
      rw [hd2]
      calc z * d * z * d = (z * d) * (z * d) := by group
        _ = 1 := by rw [hzd]; exact hw2
    have h6 : z * d * z = d := mul_right_cancel h5
    have hdz : d * z = z * d := by
      calc d * z = (z * z) * d * z := by rw [hzz, one_mul]
        _ = z * (z * d * z) := by group
        _ = z * d := by rw [h6]
    have hdA : d ∈ A := mem_A_of_comm h hdC hdz
    obtain ⟨d', hd'C, hd'⟩ := h.hC.onto d hdA
    have hconj : d' * z * d'⁻¹ = n * z * n⁻¹ := by
      rw [← hzd, ← hd', hzi]
      calc d' * z * d'⁻¹ = (z * z) * d' * z * d'⁻¹ := by rw [hzz, one_mul]
        _ = z * (z * d' * z * d'⁻¹) := by group
    have hmz : (d'⁻¹ * n) * z = z * (d'⁻¹ * n) := by
      have e1 : (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = z := by
        calc (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = d'⁻¹ * (n * z * n⁻¹) * d' := by group
          _ = d'⁻¹ * (d' * z * d'⁻¹) * d' := by rw [hconj]
          _ = z := by group
      calc (d'⁻¹ * n) * z = (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ * (d'⁻¹ * n) := by group
        _ = z * (d'⁻¹ * n) := by rw [e1]
    have hmN : d'⁻¹ * n ∈ normalizer (C : Set G) :=
      mul_mem (inv_mem (le_normalizer hd'C)) hnN
    have hnd : n⁻¹ * d'⁻¹ * n ∈ C := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) d'⁻¹).1 (inv_mem hd'C)
      rwa [inv_inv] at this
    obtain ⟨l, hlL, hm | hm⟩ := Quad.exists_mem_L h.hs hmz
    · have hlN : l ∈ normalizer (C : Set G) := hm ▸ hmN
      have hlH := mem_egNL_of h hlL hlN
      refine mem_sup_left ⟨⟨l, hlH⟩, ?_⟩
      show (QuotientGroup.mk ⟨l, hHN hlH⟩ : egQD C) = QuotientGroup.mk ⟨n, hnN⟩
      refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
      show l⁻¹ * n ∈ C
      rw [← hm]
      have e : (d'⁻¹ * n)⁻¹ * n = n⁻¹ * d'⁻¹⁻¹ * n := by group
      rw [e, inv_inv]
      have := (mem_normalizer_iff.1 (inv_mem hnN) d').1 hd'C
      rwa [inv_inv] at this
    · have hl : l = d'⁻¹ * n * z⁻¹ := by rw [hm]; group
      have hlN : l ∈ normalizer (C : Set G) := by
        rw [hl]
        exact mul_mem hmN (inv_mem hzN)
      have hlH := mem_egNL_of h hlL hlN
      have e : (QuotientGroup.mk ⟨n, hnN⟩ : egQD C) =
          psi h ⟨l, hlH⟩ * zt h := by
        show (QuotientGroup.mk ⟨n, hnN⟩ : egQD C) =
          QuotientGroup.mk ⟨l, hHN hlH⟩ * QuotientGroup.mk ⟨z, hzN⟩
        rw [← QuotientGroup.mk_mul]
        refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
        show n⁻¹ * (l * z) ∈ C
        rw [← hm]
        have e2 : n⁻¹ * (d'⁻¹ * n) = n⁻¹ * d'⁻¹ * n := by group
        rw [e2]
        exact hnd
      rw [e]
      exact mul_mem (mem_sup_left ⟨⟨l, hlH⟩, rfl⟩) (mem_sup_right (mem_zpowers _))
  · rintro _ ⟨y, rfl⟩
    exact mem_centralizer_singleton_iff.2 (psi_comm h y)
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

theorem zt_not_mem_range : zt h ∉ (psi h).range := by
  rintro ⟨y, hy⟩
  have hzN := z_mem_normalizer_C h
  have h2 : (QuotientGroup.mk (inclusion (egNL_le_normalizer_C h) y) : egQD C) =
      QuotientGroup.mk ⟨z, hzN⟩ := hy
  have h1 := QuotientGroup.eq.1 h2
  have hc : (y : G)⁻¹ * z ∈ C := mem_subgroupOf.1 h1
  have hyL : (y : G) ∈ L := (mem_inf.1 y.2).2
  have hyz : (y : G) * z = z * y := Quad.nl_comm_z h.hs y.2
  have hyiz : (y : G)⁻¹ * z = z * (y : G)⁻¹ := by
    calc (y : G)⁻¹ * z = (y : G)⁻¹ * (z * y) * (y : G)⁻¹ := by group
      _ = (y : G)⁻¹ * (y * z) * (y : G)⁻¹ := by rw [hyz]
      _ = z * (y : G)⁻¹ := by group
  have hcz : ((y : G)⁻¹ * z) * z = z * ((y : G)⁻¹ * z) := by
    calc ((y : G)⁻¹ * z) * z = (z * (y : G)⁻¹) * z := by rw [hyiz]
      _ = z * ((y : G)⁻¹ * z) := by group
  have hcA := mem_A_of_comm h hc hcz
  apply Quad.z_not_mem h.hs
  have e : z = y * ((y : G)⁻¹ * z) := by group
  rw [e]
  exact L.mul_mem hyL (h.hAL hcA)

end CSide

end CFSG.EvenSporadicStandard.M24Std
