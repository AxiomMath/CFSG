module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

omit [Finite G] in
private theorem gen49t_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

private theorem gen49t_exists_mem_U (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R) :
    ∃ u ∈ R, u ∈ gen5U (P : Subgroup G) x ∧ u ≠ 1 := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := hl.generic
  obtain ⟨hdec, -, -, hord⟩ := gen5_P_decomp hG hl
  obtain ⟨-, hPab⟩ := gen5_P_abelian hG hl
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hXR : zpowers x ≤ R := zpowers_le.mpr hxR
  obtain ⟨r, hrR, hrx⟩ : ∃ r ∈ R, r ∉ zpowers x := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun r hr => h r hr)
    rw [hRc, hXc] at h1
    have := (gen5_prime hl).one_lt
    nlinarith
  have hZU : (P : Subgroup G) ⊓ centralizer ((gen5L x : Subgroup G) : Set G) ≤
      normalizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G) := by
    refine le_trans (fun z hz => ?_) (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro u hu
    have h := hPab.is_comm.comm ⟨z, hz.1⟩ ⟨u, hu.1⟩
    exact (congrArg Subtype.val h).symm
  have hrPU : r ∈ ((gen5U (P : Subgroup G) x ⊔ ((P : Subgroup G) ⊓
      centralizer ((gen5L x : Subgroup G) : Set G)) : Subgroup G) : Set G) := by
    rw [← hdec]
    exact hRP hrR
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZU, Set.mem_mul] at hrPU
  obtain ⟨u, hu, z, hz, hrz⟩ := hrPU
  have huz : Commute u z := by
    have h := hPab.is_comm.comm ⟨u, hu.1⟩ ⟨z, hz.1⟩
    exact congrArg Subtype.val h
  have hzp : z ^ p = 1 := by
    have h1 : r ^ p = 1 := hRe.2 r hrR
    rw [← hrz, huz.mul_pow, (gen5_U_elemAbelian hG hl).1.2 u hu, one_mul] at h1
    exact h1
  have hzx : z ∈ zpowers x := by
    by_cases hz1 : z = 1
    · rw [hz1]; exact one_mem _
    · rw [← hord z hz hz1 hzp]
      exact mem_zpowers z
  have huR : u ∈ R := by
    have : u = r * z⁻¹ := by rw [← hrz]; group
    rw [this]
    exact R.mul_mem hrR (R.inv_mem (hXR hzx))
  refine ⟨u, huR, hu, fun hu1 => hrx ?_⟩
  rw [← hrz, hu1, one_mul]
  exact hzx

private theorem gen49t_centralizer_inf_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (KL : KFactL2UnipotentCoprime) {R : Subgroup G} (hRP : R ≤ (P : Subgroup G))
    (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    {F : Subgroup G} (hF : ¬ p ∣ Nat.card F) (hRF : R ≤ normalizer (F : Set G)) :
    F ⊓ centralizer ({x} : Set G) ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨u, huR, huU, hu1⟩ := gen49t_exists_mem_U hG hl hRP hRe hRc hxR
  have huC : u ∈ centralizer ({x} : Set G) := (gen5_P_abelian hG hl).1 (hRP huR)
  have hup : u ^ p = 1 := (gen5_U_elemAbelian hG hl).1.2 u huU
  have hV : (F ⊓ centralizer ({x} : Set G)) ⊓ gen5L x = ⊥ := by
    refine KL p (gen5_five_le hG hl) (gen5L x) (gen5_psl hG hl) u huU.2 (orderOf_eq_prime hup hu1)
      _ inf_le_right (fun h => hF (h.trans (Subgroup.card_dvd_of_le
        (inf_le_left.trans inf_le_left)))) ?_
    exact gen49t_mem_normalizer_inf (gen49t_mem_normalizer_inf (hRF huR)
      (Subgroup.le_normalizer huC)) (Subgroup.le_normalizer huU.2)
  intro f hf
  obtain ⟨hfF, hfC⟩ := hf
  have hfN : f ∈ normalizer ((gen5L x : Subgroup G) : Set G) := gen5_centralizer_le_normalizer x hfC
  have hc : f * (u * f⁻¹ * u⁻¹) ∈ (F ⊓ centralizer ({x} : Set G)) ⊓ gen5L x := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hRF huR) f⁻¹).mp (F.inv_mem hfF)
      exact F.mul_mem hfF h
    · exact (centralizer ({x} : Set G)).mul_mem hfC ((centralizer ({x} : Set G)).mul_mem
        ((centralizer ({x} : Set G)).mul_mem huC ((centralizer ({x} : Set G)).inv_mem hfC))
        ((centralizer ({x} : Set G)).inv_mem huC))
    · have h := (Subgroup.mem_normalizer_iff.mp hfN u).mp huU.2
      have e : f * (u * f⁻¹ * u⁻¹) = f * u * f⁻¹ * u⁻¹ := by group
      rw [e]
      exact (gen5L x).mul_mem h ((gen5L x).inv_mem huU.2)
  rw [hV, Subgroup.mem_bot] at hc
  have hfu : f ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : f * u * f⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    exact mul_inv_eq_one.mp (by simpa [mul_assoc] using e)
  exact gen5_centralizer_le hG hl huU hu1 hfu

theorem gen49_invariant_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (KL : KFactL2UnipotentCoprime) {R : Subgroup G} (hRP : R ≤ (P : Subgroup G))
    (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    {F : Subgroup G} (hF : ¬ p ∣ Nat.card F) (hRF : R ≤ normalizer (F : Set G)) : F ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hFx := gen49t_centralizer_inf_le hG hl KL hRP hRe hRc hxR hF hRF
  obtain ⟨hU, -, hPab⟩ := generic_central_abelian hG.setting hG.d1 hG.u0 hG.layer hl.sigma
    hl.core hl.fail hl.larger hl.generic
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := hl.generic
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    (gen5_prime hl) R F (fun u => Subtype.ext (hRe.2 u u.2)) hRc hF hRF]
  refine iSup_le fun u => iSup_le fun hu1 => ?_
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  by_cases hux : (u : G) ∈ zpowers x
  · have hxu : x ∈ zpowers (u : G) := by
      rw [← eq_zpowers_of_card_eq_prime hXc hux hu1']
      exact mem_zpowers x
    have hC : centralizer ((zpowers (u : G) : Subgroup G) : Set G) =
        centralizer ({(u : G)} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    refine le_trans (inf_le_inf_left F ?_) hFx
    rw [← hC]
    exact centralizer_le (Set.singleton_subset_iff.mpr hxu)
  · exact inf_le_right.trans (centralizer_le_of_not_mem_zpowers hG.setting hl.sigma hl.core hU hPab
      (hRP u.2) hu1' (hRe.2 u u.2) hux)

end CFSG.LocalAnalysis.RankThreeTheoremC
