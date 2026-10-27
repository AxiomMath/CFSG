module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

theorem sec125_mem_normalizer_of_conj {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 := h' _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [e] at h1

theorem sec125_conj_mem_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) {g x : G}
    (hg : g ∈ secCMt t S L) (hx : x ∈ secV t S L E) : g * x * g⁻¹ ∈ secV t S L E := by
  obtain ⟨hgM, hgt⟩ := Subgroup.mem_inf.mp hg
  have hgE : g ∈ normalizer (E : Set G) := sec12E_sylow_normal F hE hgM
  have hgL : g ∈ normalizer (L : Set G) := F.hCt hgt
  have hle : secV t S L E ≤ (secV t S L E).comap (MulAut.conj g).toMonoidHom := by
    rw [secV, Subgroup.commutator_le]
    intro e he y hy
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hid : g * ⁅e, y⁆ * g⁻¹ = ⁅g * e * g⁻¹, g * y * g⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hid]
    refine Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hgE e).mp he) ?_
    exact Subgroup.mem_inf.mpr
      ⟨(secM t S L).mul_mem ((secM t S L).mul_mem hgM hy.1) ((secM t S L).inv_mem hgM),
        (Subgroup.mem_normalizer_iff.mp hgL y).mp hy.2⟩
  have h := Subgroup.mem_comap.mp (hle hx)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem sec125_CMt_le_N (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secCMt t S L ≤ secN (secV t S L E) := by
  intro g hg
  refine sec125_mem_normalizer_of_conj (fun x hx => sec125_conj_mem_V F hE hg hx) ?_
  intro x hx
  have h1 := sec125_conj_mem_V F hE ((secCMt t S L).inv_mem hg) hx
  rwa [inv_inv] at h1

theorem sec125_conj_mem_A (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) {n : G} (hn : n ∈ secN (secV t S L E))
    (hnt : t * n = n * t) {a : G} (ha : a ∈ secA t S L) : n * a * n⁻¹ ∈ secA t S L := by
  have haE : a ∈ E := sec120_A_le_E F hE ha
  have hnV : n ∈ normalizer (secV t S L E : Set G) := hn
  have hnt' : n * t * n⁻¹ = t := by rw [← hnt]; group
  have hnt'' : n⁻¹ * t * n = t := by
    calc n⁻¹ * t * n = n⁻¹ * (t * n) := by group
      _ = n⁻¹ * (n * t) := by rw [hnt]
      _ = t := by group
  have hxE : n * a * n⁻¹ ∈ E := by
    rcases h.mem_E.mp haE with hV | ⟨v, hv, rfl⟩
    · exact h.V_le ((Subgroup.mem_normalizer_iff.mp hnV a).mp hV)
    · have e : n * (v * t) * n⁻¹ = (n * v * n⁻¹) * t := by
        calc n * (v * t) * n⁻¹ = (n * v * n⁻¹) * (n * t * n⁻¹) := by group
          _ = (n * v * n⁻¹) * t := by rw [hnt']
      rw [e]
      exact E.mul_mem (h.V_le ((Subgroup.mem_normalizer_iff.mp hnV v).mp hv)) h.t_mem
  refine (sec120_f_eq_one_iff F hE hxE).mp ?_
  have hat : a * t = t * a :=
    sec12E_A_comm F ha (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hxt : (n * a * n⁻¹) * t = t * (n * a * n⁻¹) := by
    calc (n * a * n⁻¹) * t = n * a * (n⁻¹ * t * n) * n⁻¹ := by group
      _ = n * (a * t) * n⁻¹ := by rw [hnt'']; group
      _ = n * (t * a) * n⁻¹ := by rw [hat]
      _ = (n * t * n⁻¹) * (n * a * n⁻¹) := by group
      _ = t * (n * a * n⁻¹) := by rw [hnt']
  change n * a * n⁻¹ * t * (n * a * n⁻¹)⁻¹ * t⁻¹ = 1
  rw [hxt]
  group

theorem sec125_CNt_le_CMt (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) :
    secN (secV t S L E) ⊓ centralizer ({t} : Set G) ≤ secCMt t S L := by
  intro n hn
  obtain ⟨hnN, hnC⟩ := Subgroup.mem_inf.mp hn
  have hnt : t * n = n * t := Subgroup.mem_centralizer_iff.mp hnC t (Set.mem_singleton t)
  have hnt' : t * n⁻¹ = n⁻¹ * t := by
    calc t * n⁻¹ = n⁻¹ * (n * t) * n⁻¹ := by group
      _ = n⁻¹ * (t * n) * n⁻¹ := by rw [hnt]
      _ = n⁻¹ * t := by group
  refine Subgroup.mem_inf.mpr ⟨?_, hnC⟩
  refine sec125_mem_normalizer_of_conj (fun a ha => sec125_conj_mem_A F hE h hnN hnt ha) ?_
  intro a ha
  have h1 := sec125_conj_mem_A F hE h ((secN (secV t S L E)).inv_mem hnN) hnt' ha
  rwa [inv_inv] at h1

theorem sec125_CNt_eq_CMt (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (h : Sec125Core t (secV t S L E) E) :
    secN (secV t S L E) ⊓ centralizer ({t} : Set G) = secCMt t S L :=
  le_antisymm (sec125_CNt_le_CMt F hE h) fun g hg =>
    Subgroup.mem_inf.mpr ⟨sec125_CMt_le_N F hE hg, (Subgroup.mem_inf.mp hg).2⟩

end CFSG.OddStandard.SmallF3.Omega
