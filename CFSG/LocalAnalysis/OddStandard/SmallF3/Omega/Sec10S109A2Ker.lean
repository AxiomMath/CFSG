module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec10A2Act (t z : G) (K1 K2 T : Subgroup G) (f : ↥T →* MulAut ↥(K1 ⊔ K2)) : Prop :=
  ∀ (y : ↥T) (k : ↥(K1 ⊔ K2)), ∃ n ∈ oddCoreIn (secK0 t z),
    (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥(K1 ⊔ K2)) : G)

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}

theorem sec10A2_cases_cent_K0 {w : G} (hw : w = 1 ∨ w = t ∨ w = z ∨ w = t * z) :
    ∀ x ∈ secK0 t z, w * x = x * w := by
  intro x hx
  obtain ⟨hxt, hxz⟩ := Subgroup.mem_inf.mp (sec10D_K0_le t z hx)
  have ht : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
  have hz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxz
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · exact ht.symm
  · exact hz.symm
  · calc t * z * x = t * (z * x) := by group
      _ = t * (x * z) := by rw [hz]
      _ = (t * x) * z := by group
      _ = (x * t) * z := by rw [ht]
      _ = x * (t * z) := by group

theorem sec10A2_ker_S (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    {f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)} (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f)
    {u : ↥(S ⊔ zpowers g)} (huS : (u : G) ∈ S) (hu1 : f u = 1) :
    (u : G) = 1 ∨ (u : G) = t ∨ (u : G) = z ∨ (u : G) = t * z := by
  obtain ⟨ht2, hz2, -, -, -, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  obtain ⟨hpsp, -, -, -, hSN, -⟩ := hb G t L S z hctx.toSec10Z
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hOC := sec10L104_oddK0_le_centralizer h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb
    hctx.toSec10Ctx
  have hKL : K1 ⊔ K2 ≤ L :=
    sup_le (hctx.pocket1.2.1.trans inf_le_left) (hctx.pocket2.2.1.trans inf_le_left)
  have hD := sec10A2_split h3 h hf hb hctx.toSec10Ctx
  have huN : (u : G) ∈ normalizer (L : Set G) := hSN huS
  have hcomm : ∀ k ∈ K1 ⊔ K2, (u : G) * k = k * (u : G) := by
    intro k hk
    have h1 := (hD.act_eq_one_iff f hfs u).mp hu1 k hk
    have h2 : (u : G) * k * (u : G)⁻¹ * k⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp huN k).mp (hKL hk)) (L.inv_mem (hKL hk))
    have h3' : (u : G) * k * (u : G)⁻¹ * k⁻¹ ∈ L ⊓ centralizer (L : Set G) := ⟨h2, hOC h1⟩
    rw [hLC] at h3'
    have h4 : (u : G) * k * (u : G)⁻¹ * k⁻¹ = 1 := by simpa using h3'
    calc (u : G) * k = ((u : G) * k * (u : G)⁻¹ * k⁻¹) * (k * (u : G)) := by group
      _ = k * (u : G) := by rw [h4, one_mul]
  have hyC : (u : G) ∈ centralizer (L : Set G) ⊔ zpowers z :=
    hf.centK5 G L hpsp z hctx.toSec10Z.pocket.1 K1 K2 hctx.pocket1 hctx.pocket2 hctx.ne (u : G)
      huN hcomm
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hcz : ∀ c ∈ centralizer (L : Set G), ∀ w ∈ zpowers z, c * w = w * c := by
    intro c hc w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hzc : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z hzL
    exact (Commute.zpow_right (show Commute c z from hzc.symm) n).eq
  obtain ⟨c, hc, w, hw, huc⟩ := exists_mul_of_mem_sup_of_commute hcz hyC
  have hwS : w ∈ S := Subgroup.zpowers_le.mpr hctx.mem_S hw
  have hcS : c ∈ S := by
    have e : c = (u : G) * w⁻¹ := by rw [huc]; group
    rw [e]
    exact S.mul_mem huS (S.inv_mem hwS)
  have hct : c ∈ zpowers t := by
    have := h.l106 G t L S z K1 K2 hctx.toSec10Ctx
    rw [← this]
    exact ⟨hc, hcS⟩
  rw [huc]
  rcases sec10D_eq_one_or_of_mem_zpowers ht2 hct with h1 | h1 <;>
    rcases sec10D_eq_one_or_of_mem_zpowers hz2 hw with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem sec10A2_z_mem_secB (hf : Asc82Facts10) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) : z ∈ secB S L := by
  obtain ⟨-, -, hBC, -⟩ := sec10BData_of hb hf.b5 hctx.toSec10Z
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  rw [← hBC]
  exact ⟨Subgroup.mem_centralizer_iff.mpr fun b hb' => hctx.central b (secB_le_S S L hb'), hzL⟩

theorem sec10A2_S_le_M (h3 : Asc82Sec3Res10) (hctx : Sec10Ctx G t L S z K1 K2) :
    S ≤ secM t S L := fun s hs =>
  sec10A_cent_mem_M h3.l36 hctx (Subgroup.le_normalizer hs)
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs))

theorem sec10A2_ker_le_S (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    {f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)} (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f)
    {y : ↥(S ⊔ zpowers g)} (hy : f y = 1) : (y : G) ∈ S := by
  by_contra hyS
  have hgyS : g⁻¹ * (y : G) ∈ S := (sec10A2_T_cases hb hctx (y : G) y.2).resolve_left hyS
  have hT : S ⊔ zpowers g ≤ normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hctx.norm)
  have htS : t ∈ S := (hb G t L S z hctx.toSec10Z).2.2.2.1
  have hAS : secA t S L ≤ S := sup_le (secB_le_S S L) (Subgroup.zpowers_le.mpr htS)
  have hzA : z ∈ secA t S L :=
    Subgroup.mem_sup_left (sec10A2_z_mem_secB hf hb hctx.toSec10Ctx)
  have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have key : ∀ y' : ↥(S ⊔ zpowers g), f y' = 1 → ∀ a ∈ secA t S L,
      (y' : G) * a * (y' : G)⁻¹ ∈ secA t S L := by
    intro y' hy' a ha
    have haS : a ∈ S := hAS ha
    have hy'N : (y' : G) ∈ normalizer (S : Set G) := hT y'.2
    have hc : (y' : G) * a * (y' : G)⁻¹ * a⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.mp hy'N a).mp haS) (S.inv_mem haS)
    let aT : ↥(S ⊔ zpowers g) := ⟨a, Subgroup.mem_sup_left haS⟩
    let cT : ↥(S ⊔ zpowers g) := y' * aT * y'⁻¹ * aT⁻¹
    have hcT : f cT = 1 := by simp [cT, hy']
    have hcT' : (cT : G) = (y' : G) * a * (y' : G)⁻¹ * a⁻¹ := rfl
    have hker := sec10A2_ker_S h3 h hf hb hctx hfs (u := cT) (by rw [hcT']; exact hc) hcT
    have hmem : (cT : G) ∈ secA t S L := by
      rcases hker with h1 | h1 | h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact htA
      · rw [h1]; exact hzA
      · rw [h1]; exact Subgroup.mul_mem _ htA hzA
    have e : (y' : G) * a * (y' : G)⁻¹ = (cT : G) * a := by rw [hcT']; group
    rw [e]
    exact Subgroup.mul_mem _ hmem ha
  have hyM : (y : G) ∈ secM t S L := by
    show (y : G) ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    refine sec10W_mem_normalizer_of (key y hy) (fun a ha => ?_)
    have := key y⁻¹ (by rw [map_inv, hy, inv_one]) a ha
    simpa using this
  have hg : g ∈ secM t S L := by
    have e : g = (y : G) * (g⁻¹ * (y : G))⁻¹ := by group
    rw [e]
    exact (secM t S L).mul_mem hyM (sec10A2_S_le_M h3 hctx.toSec10Ctx (S.inv_mem hgyS))
  exact hctx.not_M hg

theorem sec10A2_T_sq_mem_S (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∀ y ∈ S ⊔ zpowers g, y * y ∈ S := by
  intro y hy
  rcases sec10A2_T_cases hb hctx y hy with h1 | h1
  · exact S.mul_mem h1 h1
  · have hg' : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hctx.norm
    have hconj : g⁻¹ * (g⁻¹ * y) * g ∈ S := by
      have := (hg' (g⁻¹ * (g⁻¹ * y) * g)).mpr
      refine this ?_
      have e : g * (g⁻¹ * (g⁻¹ * y) * g) * g⁻¹ = g⁻¹ * y := by group
      rw [e]
      exact h1
    have e : y * y = (g * g) * (g⁻¹ * (g⁻¹ * y) * g) * (g⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem (S.mul_mem (sec10A2_sq_mem_S hb hctx) hconj) h1

theorem sec10A2_sq_cent (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g)
    {f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2)} (hfs : Sec10A2Act t z K1 K2 (S ⊔ zpowers g) f)
    {y : ↥(S ⊔ zpowers g)} (hy2 : f y * f y = 1) :
    ∀ x ∈ secK0 t z, (y : G) * (y : G) * x = x * ((y : G) * (y : G)) := by
  have hsq : (y : G) * (y : G) ∈ S := sec10A2_T_sq_mem_S hb hctx (y : G) y.2
  have hker := sec10A2_ker_S h3 h hf hb hctx hfs (u := y * y) hsq (by rw [map_mul, hy2])
  exact sec10A2_cases_cent_K0 hker

end CFSG.OddStandard.SmallF3.Omega
