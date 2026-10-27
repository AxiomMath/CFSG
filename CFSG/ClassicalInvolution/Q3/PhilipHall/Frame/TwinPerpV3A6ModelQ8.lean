module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelSmall
public import Certificates.Certificate517504

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin Certificates.S5Rows
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

theorem ncard_conjSet_conjSub (a g : AE6Om) (J : Subgroup AE6Om) :
    Set.ncard {J' | ∃ c ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set AE6Om),
      conjSub c (conjSub g⁻¹ J) = J'} =
    Set.ncard {J' | ∃ c ∈ Subgroup.centralizer ({a} : Set AE6Om), conjSub c J = J'} := by
  have himg : (conjSub g) '' {J' | ∃ c ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set AE6Om),
      conjSub c (conjSub g⁻¹ J) = J'} =
      {J' | ∃ c ∈ Subgroup.centralizer ({a} : Set AE6Om), conjSub c J = J'} := by
    ext K
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨g * c * g⁻¹, ?_, by rw [conjSub_mul, conjSub_mul]⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g * c * g⁻¹ * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [hc]
        _ = a * (g * c * g⁻¹) := by group
    · rintro ⟨d, hd, rfl⟩
      refine ⟨conjSub (g⁻¹ * d * g) (conjSub g⁻¹ J), ⟨g⁻¹ * d * g, ?_, rfl⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hd ⊢
        calc g⁻¹ * d * g * (g⁻¹ * a * g) = g⁻¹ * (d * a) * g := by group
          _ = g⁻¹ * (a * d) * g := by rw [hd]
          _ = g⁻¹ * a * g * (g⁻¹ * d * g) := by group
      · rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
  rw [← himg, Set.ncard_image_of_injective _
    (CFSG.ClassicalInvolution.Generic.conjSub_injective g)]


theorem smallQ8_conj_z0 {a : AE6Om} {J : Subgroup AE6Om} (hJ : AE6SmallQ8 a J) :
    ∃ g : AE6Om, g * ae6ModelZ * g⁻¹ = a := by
  obtain ⟨i, j, hij, hii, hJeq⟩ := exists_pair_of_smallQ8 hJ
  have hcore : ∀ t ∈ J, t ∈ pCoreOf 2 (Subgroup.centralizer ({a} : Set AE6Om)) :=
    fun t ht => hJ.2.2.1 ht
  obtain ⟨x, hx⟩ := exists_conj_le_of_odd_index index_sylow
    (isPGroup_pCoreOf (Subgroup.centralizer ({a} : Set AE6Om)))
  have haJ : a ∈ J := hJ.2.1.mem
  have ha1 := hx a (hcore a haJ)
  have hSc : (sQ ()).originalSubgroup = Subgroup.closure {g | g ∈ sGens ()} := by
    rw [sQ, certificate_originalSubgroup]
  have ho : orderOf ((x⁻¹ * a * x : AE6Om) : Equiv.Perm (Fin 360)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← Subgroup.coe_pow, sq]
      have h2 : x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
      rw [h2, hJ.2.1.sq]
      simp
    · intro h1
      apply hJ.2.1.ne_one
      have h2 : x⁻¹ * a * x = 1 := Subtype.ext h1
      calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = 1 := by rw [h2]; group
  have hr : ((x⁻¹ * a * x : AE6Om) : Equiv.Perm (Fin 360)) ∈
      Subgroup.closure {g | g ∈ sGens ()} := by
    rw [← hSc]
    exact Subgroup.mem_subgroupOf.mp ha1
  have hcut : ∀ h ∈ Subgroup.centralizer ({x⁻¹ * a * x} : Set AE6Om), ∀ t ∈ J,
      ((h⁻¹ * (x⁻¹ * t * x) * h : AE6Om) : Equiv.Perm (Fin 360)) ∈
        (sQ ()).originalSubgroup := by
    intro h hh t ht
    have hh' : x * h * x⁻¹ ∈ Subgroup.centralizer ({a} : Set AE6Om) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
      calc x * h * x⁻¹ * a = x * (h * (x⁻¹ * a * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * h) * x⁻¹ := by rw [hh]
        _ = a * (x * h * x⁻¹) := by group
    have h2 := hx _ (conj_mem_pCoreOf (Subgroup.inv_mem _ hh') (hcore t ht))
    have h4 : x⁻¹ * ((x * h * x⁻¹)⁻¹ * t * (x * h * x⁻¹)⁻¹⁻¹) * x = h⁻¹ * (x⁻¹ * t * x) * h := by
      group
    rw [h4] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hiJ : i ∈ J := hJeq ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hjJ : j ∈ J :=
    hJeq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hjj : j * j = i * i := by
    rw [← sq, ← sq]
    exact hij.2.2.1.symm
  have hiji : i * j * i = j := by
    rw [q8Rel_mul_j hij]
    group
  have hii' : (x⁻¹ * i * x) * (x⁻¹ * i * x) = x⁻¹ * a * x := by
    rw [← hii]
    group
  have hjj' : (x⁻¹ * j * x) * (x⁻¹ * j * x) = x⁻¹ * a * x := by
    rw [← hii, ← hjj]
    group
  have hiji' : (x⁻¹ * i * x) * (x⁻¹ * j * x) * (x⁻¹ * i * x) = x⁻¹ * j * x := by
    calc (x⁻¹ * i * x) * (x⁻¹ * j * x) * (x⁻¹ * i * x) = x⁻¹ * (i * j * i) * x := by group
      _ = x⁻¹ * j * x := by rw [hiji]
  rcases Certificates.certificate517504 _ hr ho _ (x⁻¹ * i * x).2 _ (x⁻¹ * j * x).2
      (by rw [← Subgroup.coe_mul, hii']) (by rw [← Subgroup.coe_mul, hjj'])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hiji'])
      (fun h hh hc => by
        have hcen : (⟨h, hh⟩ : AE6Om) ∈ Subgroup.centralizer ({x⁻¹ * a * x} : Set AE6Om) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext hc
        rw [← hSc]
        exact ⟨hcut _ hcen i hiJ, hcut _ hcen j hjJ⟩) with ⟨c, hc, hrc⟩ | h5
  · have hcO : c ∈ omegaT := sQ_le (by rw [hSc]; exact hc)
    refine ⟨x * ⟨c, hcO⟩, ?_⟩
    have h1 : (⟨c, hcO⟩ : AE6Om) * ae6ModelZ * (⟨c, hcO⟩ : AE6Om)⁻¹ = x⁻¹ * a * x := by
      apply Subtype.ext
      rw [hrc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_ae6ModelZ]
    calc x * ⟨c, hcO⟩ * ae6ModelZ * (x * ⟨c, hcO⟩)⁻¹ =
        x * ((⟨c, hcO⟩ : AE6Om) * ae6ModelZ * (⟨c, hcO⟩ : AE6Om)⁻¹) * x⁻¹ := by group
      _ = a := by rw [h1]; group
  · exfalso
    have hJ2 : Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om) = conjSub x⁻¹ J := by
      rw [hJeq, CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair, inv_inv]
    have hn := ncard_conjSet_conjSub a x J
    rw [← hJ2] at hn
    let φ : Subgroup AE6Om → Subgroup (Equiv.Perm (Fin 360)) := fun L => L.map omegaT.subtype
    have hφ : Function.Injective φ := Subgroup.map_injective omegaT.subtype_injective
    have hK : (Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om)).map omegaT.subtype =
        Subgroup.closure {((x⁻¹ * i * x : AE6Om) : Equiv.Perm (Fin 360)),
          ((x⁻¹ * j * x : AE6Om) : Equiv.Perm (Fin 360))} := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    have hsub : {J' | ∃ c ∈ omegaT,
        c * ((x⁻¹ * a * x : AE6Om) : Equiv.Perm (Fin 360)) =
          ((x⁻¹ * a * x : AE6Om) : Equiv.Perm (Fin 360)) * c ∧
        (Subgroup.closure {((x⁻¹ * i * x : AE6Om) : Equiv.Perm (Fin 360)),
          ((x⁻¹ * j * x : AE6Om) : Equiv.Perm (Fin 360))}).map (MulAut.conj c).toMonoidHom =
          J'} ⊆
        φ '' {J' | ∃ c ∈ Subgroup.centralizer ({x⁻¹ * a * x} : Set AE6Om),
          conjSub c (Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om)) = J'} := by
      rintro _ ⟨c, hc, hcr, rfl⟩
      refine ⟨conjSub ⟨c, hc⟩ (Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om)),
        ⟨⟨c, hc⟩, ?_, rfl⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext hcr
      · simp only [φ]
        rw [← hK, conjSub, Subgroup.map_map, Subgroup.map_map]
        refine congrArg (fun f => Subgroup.map f _) (MonoidHom.ext fun y => ?_)
        simp [MulAut.conj_apply]
    have hfin : (φ '' {J' | ∃ c ∈ Subgroup.centralizer ({x⁻¹ * a * x} : Set AE6Om),
        conjSub c (Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om)) = J'}).Finite := by
      refine ((Set.finite_univ (α := AE6Om)).image fun c =>
        φ (conjSub c (Subgroup.closure ({x⁻¹ * i * x, x⁻¹ * j * x} : Set AE6Om)))).subset ?_
      rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
      exact ⟨c, Set.mem_univ _, rfl⟩
    have h6 := h5.trans (Set.ncard_le_ncard hsub hfin)
    rw [Set.ncard_image_of_injective _ hφ, hn] at h6
    have := hJ.2.2.2
    omega

theorem ae6ModelQ8_proved : AE6ModelQ8 := by
  intro a b J J' hJ hJ'
  obtain ⟨g₁, hg₁⟩ := smallQ8_conj_z0 hJ
  obtain ⟨g₂, hg₂⟩ := smallQ8_conj_z0 hJ'
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [← hg₁, ← hg₂]
  group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
