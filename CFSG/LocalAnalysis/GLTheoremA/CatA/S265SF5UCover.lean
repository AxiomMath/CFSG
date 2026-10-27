module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Mathlib.GroupTheory.IsPerfect
import CFSG.LieType.Steinberg.CentralExt.PerfectLift
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.RankThree.CentralLift.ClassicalCoverTools
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (gramSU normOneScalars unitarySU_eq_gramSU)
open CFSG.Open (StatedSU)
open CFSG.LieType.Steinberg.CentralExt.SUOdd (isPerfect_statedSU_odd
  statedSU_odd_exists_section_of_central)

variable {m : ℕ} {F : Type} [Field F]

private theorem isPerfect_gramSU_five (hF : UnitaryFieldData 2 m F) :
    Group.IsPerfect ↥(gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) := by
  haveI := hF.finite
  haveI : CharP F 2 := hF.charP
  haveI := isPerfect_statedSU_odd (p := 2) (f := m) (F := F)
    (by rw [hF.card, ← pow_mul, mul_comm]) (n := 5) (by norm_num)
    (fun hh => absurd (Prod.mk.inj hh).1 (by norm_num))
  have hHS : StatedSU 5 (2 ^ m) F =
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := unitarySU_eq_gramSU hF 5
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hHS).toMonoidHom)
    (MulEquiv.subgroupCongr hHS).surjective

section Cert


theorem exists_su5_cover (hF : UnitaryFieldData 2 m F) {L : Type} [Group L] [Finite L]
    (hL : Group.IsPerfect L)
    (θ : L ⧸ Subgroup.center L ≃* primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
    ∃ α : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) →* L,
      Function.Surjective α ∧
      (∀ g, θ (α g : L ⧸ Subgroup.center L) =
        (g : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))) ∧
      (normOneScalars hF (gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) 5).map α =
        Subgroup.center L := by
  haveI := hF.finite
  haveI : CharP F 2 := hF.charP
  obtain ⟨β, hβs, hβk, hβ⟩ : ∃ β : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) →*
      primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F), Function.Surjective β ∧
      β.ker = normOneScalars hF (gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) 5 ∧
      ∀ g, β g = (g : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :=
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _, fun _ => rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : L →* primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      ∀ l, η l = θ (l : L ⧸ Subgroup.center L) :=
    ⟨θ.toMonoidHom.comp (QuotientGroup.mk' _), fun _ => rfl⟩
  have hηs : Function.Surjective η := fun z => by
    obtain ⟨q, rfl⟩ := θ.surjective z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, hη l⟩
  have hηk : η.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker, hη, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff]
  set Pb := (β.comp (MonoidHom.fst _ L)).eqLocus (η.comp (MonoidHom.snd _ L))
  have hmem : ∀ y : ↥(gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) × L,
      y ∈ Pb ↔ β y.1 = η y.2 := fun _ => Iff.rfl
  set ρ := (MonoidHom.fst _ L).comp Pb.subtype
  have hρs : Function.Surjective ρ := fun g => by
    obtain ⟨l, hl⟩ := hηs (β g)
    exact ⟨⟨(g, l), (hmem _).2 hl.symm⟩, rfl⟩
  have hρc : ρ.ker ≤ Subgroup.center ↥Pb := by
    intro y hy
    have h1 : y.1.1 = 1 := MonoidHom.mem_ker.1 hy
    have h2 : y.1.2 ∈ Subgroup.center L := by
      rw [← hηk, MonoidHom.mem_ker, ← (hmem _).1 y.2, h1, map_one]
    refine Subgroup.mem_center_iff.2 fun z => Subtype.ext (Prod.ext ?_
      (Subgroup.mem_center_iff.1 h2 z.1.2))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  have hHS : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      StatedSU 5 (2 ^ m) F := (unitarySU_eq_gramSU hF 5).symm
  set e := MulEquiv.subgroupCongr hHS
  have hπk : (e.toMonoidHom.comp ρ).ker ≤ Subgroup.center ↥Pb := fun x hx => by
    have h1 : e (ρ x) = 1 := MonoidHom.mem_ker.1 hx
    exact hρc (MonoidHom.mem_ker.2 ((map_eq_one_iff e e.injective).1 h1))
  obtain ⟨s, hs⟩ := statedSU_odd_exists_section_of_central (p := 2) (f := m) (F := F)
    (by rw [hF.card, ← pow_mul, mul_comm]) hF.one_le (n := 5) (by norm_num) (by decide)
    (fun hh => absurd (Prod.mk.inj hh).1 (by norm_num)) (π := e.toMonoidHom.comp ρ)
    (e.surjective.comp hρs) hπk
  have hρs' : ∀ g, ρ (s (e g)) = g := fun g => by
    have h1 : e (ρ (s (e g))) = e g := hs (e g)
    exact e.injective h1
  set α := (MonoidHom.snd _ L).comp (Pb.subtype.comp (s.comp e.toMonoidHom))
  have hηα : η.comp α = β := MonoidHom.ext fun g => by
    have h1 := ((hmem _).1 (s (e g)).2).symm
    rw [show (s (e g)).1.1 = g from hρs' g] at h1
    exact h1
  obtain ⟨hsurj, -, hmap, -, -⟩ :=
    CFSG.RankThree.CentralLift.cover_map_of_comp_eq hβs hηk.le hηα
  refine ⟨α, hsurj, fun g => (hη (α g)).symm.trans ((DFunLike.congr_fun hηα g).trans (hβ g)),
    ?_⟩
  rw [← hβk, hmap, hηk]

end Cert

theorem conj_apply_eq_of_cover {Ω : Type} [Group Ω] {K : Subgroup Ω}
    (hF : UnitaryFieldData 2 m F)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃*
      primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
    {α : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) →* ↥K}
    (hα : ∀ g, θ (α g : ↥K ⧸ Subgroup.center ↥K) =
      (g : primeFormP hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)))
    {b : Ω} (hb : b ∈ Subgroup.normalizer (K : Set Ω))
    {A : primeFormUnitary hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)}
    (hbA : ∀ k k' : ↥K, (k' : Ω) = b * k * b⁻¹ →
      θ (k' : ↥K ⧸ Subgroup.center ↥K) =
        primeFormConjHom hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A
          (θ (k : ↥K ⧸ Subgroup.center ↥K)))
    (g : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
    b * (α g : Ω) * b⁻¹ =
      α (primeFormConjSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A g) := by
  haveI := isPerfect_gramSU_five hF
  obtain ⟨c, hc⟩ : ∃ c : MulAut ↥K, ∀ k : ↥K, (c k : Ω) = b * k * b⁻¹ :=
    ⟨Subgroup.normalizerMonoidHom (H := K) ⟨b, hb⟩, fun _ => rfl⟩
  have key := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
    (π := QuotientGroup.mk' (Subgroup.center ↥K)) (QuotientGroup.ker_mk' _).le
    (β₁ := c.toMonoidHom.comp α)
    (β₂ := α.comp (primeFormConjSU hF ((1 : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F) A).toMonoidHom) (MonoidHom.ext fun g' => θ.injective ?_)
  · exact (hc (α g)).symm.trans (congrArg Subtype.val (DFunLike.congr_fun key g))
  change θ (c (α g') : ↥K ⧸ Subgroup.center ↥K) =
    θ (α (primeFormConjSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) A g') :
      ↥K ⧸ Subgroup.center ↥K)
  rw [hbA (α g') (c (α g')) (hc _), hα, hα, primeFormConjHom_mk]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
