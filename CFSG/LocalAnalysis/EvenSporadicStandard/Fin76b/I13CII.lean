module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Cl1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Sig2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13E8

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

structure CaseII (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : Prop where
  pi : EPi E π
  cs : SigmaCS E π
  range : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
    π a ∈ alternatingGroup (Fin 5) ∧ π b ∈ alternatingGroup (Fin 5)

include c

theorem z_not_mem_Zs : z ∉ c.Zs := by
  intro hz
  rcases c.mem_Zs.1 hz with h | h | h | h
  · exact c.h.z_ne h
  · exact c.h.z_ne_t h
  · exact c.hα.ne_z h.symm
  · apply c.hα.ne_zt
    calc α = α * (t * t) := by rw [c.h.t_sq, mul_one]
      _ = (α * t) * t := by group
      _ = z * t := by rw [← h]

theorem zt_not_mem_Zs : z * t ∉ c.Zs := by
  intro hz
  rcases c.mem_Zs.1 hz with h | h | h | h
  · apply c.h.z_ne_t
    have h1 : z * t = t * t := by rw [h, c.h.t_sq]
    exact mul_right_cancel h1
  · apply c.h.z_ne
    have h1 : z * t = 1 * t := by rw [h, one_mul]
    exact mul_right_cancel h1
  · exact c.hα.ne_zt h.symm
  · exact c.hα.ne_z (mul_right_cancel h).symm

theorem Zs_le_S : c.Zs ≤ S := by
  intro u hu
  rcases c.mem_Zs.1 hu with h | h | h | h
  · rw [h]; exact S.one_mem
  · rw [h]; exact c.h.t_mem_S
  · rw [h]; exact c.hα.mem
  · rw [h]; exact mul_mem c.hα.mem c.h.t_mem_S

theorem not_conj_z_of_mem_Zs {y : G} (hy : y ∈ c.Zs) (hyz : ∃ g : G, y = g * z * g⁻¹) :
    False := by
  obtain ⟨g, hg⟩ := hyz
  rw [hg] at hy
  rcases c.h.h67 g (c.Zs_le_S hy) with h | h
  · rw [h] at hy
    exact c.z_not_mem_Zs hy
  · rw [h] at hy
    exact c.zt_not_mem_Zs hy

variable {c}

theorem IsRs.Rhat_prod {π : MulAut ↥E →* Equiv.Perm (Fin 5)} {Rs : Subgroup G}
    (hR : c.IsRs Rs) (hII : c.CaseII π) :
    ∃ S₁ S₂ : Subgroup (MulAut ↥E), IsPGroup 2 S₁ ∧ IsPGroup 2 S₂ ∧
      S₁ ≤ (alternatingGroup (Fin 5)).comap π ∧ S₂ ≤ (alternatingGroup (Fin 5)).comap π ∧
      (∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → P ≤ (alternatingGroup (Fin 5)).comap π →
        S₁ ≤ P → P ≤ S₁) ∧
      (∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → P ≤ (alternatingGroup (Fin 5)).comap π →
        S₂ ≤ P → P ≤ S₂) ∧
      c.Rhat (Rs ⊓ c.N1) = S₁.prod S₂ := by
  set A : Subgroup (MulAut ↥E) := (alternatingGroup (Fin 5)).comap π with hA
  have hrange : c.rho.range = A.prod A := by
    ext ⟨a, b⟩
    rw [hII.range a b, Subgroup.mem_prod, hA, Subgroup.mem_comap, Subgroup.mem_comap]
  obtain ⟨heq, h1, h2, h3, h4, h5, h6⟩ := eq_prod_of_max (Θ₁ := A) (Θ₂ := A)
    (Rhat_pgroup hR.R_pgroup) ((c.Rhat_le_range _).trans hrange.le)
    (fun P hP hPle hle => hR.Rhat_max P hP (by rw [hrange]; exact hPle) hle)
  exact ⟨_, _, h1, h2, h3, h4, h5, h6, heq⟩

theorem IsRs.card_cent_Rhat_ge {π : MulAut ↥E →* Equiv.Perm (Fin 5)} {Rs : Subgroup G}
    (hR : c.IsRs Rs) (hII : c.CaseII π) {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1) :
    256 ≤ Nat.card ↥(c.Rhat (Rs ⊓ c.N1) ⊓ centralizer
      ({c.rho ⟨y, hy.2⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
  obtain ⟨S₁, S₂, h1, h2, hA1, hA2, hm1, hm2, hRh⟩ := hR.Rhat_prod hII
  have hρy : c.rho ⟨y, hy.2⟩ ∈ c.Rhat (Rs ⊓ c.N1) := c.mem_Rhat.2 ⟨⟨y, hy.2⟩, hy, rfl⟩
  rw [hRh] at hρy
  have hsq : c.rho ⟨y, hy.2⟩ * c.rho ⟨y, hy.2⟩ = 1 := by
    rw [← map_mul, ← map_one c.rho]
    congr 1
    exact Subtype.ext hy2
  have e1 : (c.rho ⟨y, hy.2⟩).1 * (c.rho ⟨y, hy.2⟩).1 = 1 := congrArg Prod.fst hsq
  have e2 : (c.rho ⟨y, hy.2⟩).2 * (c.rho ⟨y, hy.2⟩).2 = 1 := congrArg Prod.snd hsq
  have c1 := c.cs_general hII.pi hII.cs h1 hA1 hm1 hρy.1 e1
  have c2 := c.cs_general hII.pi hII.cs h2 hA2 hm2 hρy.2 e2
  have h3 := card_cent_prod_ge c1 c2
  rw [hRh]
  exact h3

variable (c)

include c

theorem false_of_big_cent {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRN : R ≤ c.N1)
    (hZR : c.Zs ≤ R) (hKR : R ⊓ c.KR ≤ c.Zs) {y : G} (hy : y ∈ R) (hyZ : y ∉ c.Zs)
    (hyz : ∃ g : G, y = g * z * g⁻¹)
    (hbig : 256 ≤ Nat.card ↥(c.Rhat R ⊓ centralizer
      ({c.rho ⟨y, hRN hy⟩} : Set (MulAut ↥E × MulAut ↥E)))) : False := by
  have hcl := c.card_cent_Rhat_le hRN hZR hKR hy
  have hT0 := c.card_T0_le
  have hcent : 256 ≤ Nat.card ↥(R ⊓ centralizer ({y} : Set G)) := le_trans hbig hcl
  set C : Subgroup G := R ⊓ centralizer ({y} : Set G) with hC
  have hC2 : IsPGroup 2 C := hR2.to_le inf_le_left
  have hCy : C ≤ centralizer ({y} : Set G) := inf_le_right
  have hCbig : 2 * Nat.card T₀ ≤ Nat.card C := by omega
  have hbound := c.center_card_le hyz hC2 hCy hCbig
  have hyC : y ∈ C := ⟨hy, mem_centralizer_singleton_iff.2 rfl⟩
  have hZmem : ∀ a ∈ c.Zs, a ∈ C := fun a ha =>
    ⟨hZR ha, mem_centralizer_singleton_iff.2 (c.Zs_comm_N1 ha (hRN hy)).symm⟩
  set Cs : Set G := {a : G | a ∈ C ∧ ∀ u ∈ C, a * u = u * a} with hCs
  have hCs_Zs : ∀ a ∈ c.Zs, a ∈ Cs := fun a ha =>
    ⟨hZmem a ha, fun u hu => (c.Zs_comm_N1 ha (hRN hu.1)).symm⟩
  have hCs_yZ : ∀ a ∈ c.Zs, y * a ∈ Cs := by
    intro a ha
    refine ⟨mul_mem hyC (hZmem a ha), fun u hu => ?_⟩
    have hu1 : u * y = y * u := mem_centralizer_singleton_iff.1 hu.2
    have hu2 : u * a = a * u := c.Zs_comm_N1 ha (hRN hu.1)
    calc y * a * u = y * (a * u) := by group
      _ = y * (u * a) := by rw [hu2]
      _ = (y * u) * a := by group
      _ = (u * y) * a := by rw [hu1]
      _ = u * (y * a) := by group
  have hsub : (c.Zs : Set G) ∪ (fun a => y * a) '' (c.Zs : Set G) ⊆ Cs := by
    rintro _ (ha | ⟨a, ha, rfl⟩)
    · exact hCs_Zs _ ha
    · exact hCs_yZ _ ha
  have hdisj : Disjoint (c.Zs : Set G) ((fun a => y * a) '' (c.Zs : Set G)) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, hb, rfl⟩
    apply hyZ
    have e : y = (y * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem ha (inv_mem hb)
  have h8 : Set.ncard ((c.Zs : Set G) ∪ (fun a => y * a) '' (c.Zs : Set G)) = 8 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (mul_right_injective y)]
    have h4 : Set.ncard (c.Zs : Set G) = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact c.card_Zs'
    omega
  have h9 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem not_conj_z_of_mem_R {π : MulAut ↥E →* Equiv.Perm (Fin 5)} {Rs : Subgroup G}
    (hR : c.IsRs Rs) (hII : c.CaseII π) {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1)
    (hyz : ∃ g : G, y = g * z * g⁻¹) : False := by
  by_cases hyZ : y ∈ c.Zs
  · exact c.not_conj_z_of_mem_Zs hyZ hyz
  exact c.false_of_big_cent hR.R_pgroup (inf_le_right : (Rs ⊓ c.N1 : Subgroup G) ≤ c.N1)
    hR.Zs_le_R hR.R_inf_KR_le hy hyZ hyz (hR.card_cent_Rhat_ge hII hy hy2)

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
