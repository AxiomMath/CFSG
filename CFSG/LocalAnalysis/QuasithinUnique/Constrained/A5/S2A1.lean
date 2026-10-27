module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Frat

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem cj_baum {g : G} (hg : g ∈ S) : cj g (baum S) = baum S :=
  mem_normalizer_iff_cj.1 (normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg))

omit [Finite G] in
theorem cj_s2I {g : G} (hg : g ∈ S) (L' : Subgroup G) :
    cj g (s2I S L') = s2I S (cj g L') := by
  unfold s2I
  rw [cj_inf, cj_baum hg, cj_centralizer]

section PiHelpers

variable {L' : Subgroup G}

theorem pf_mem_im (D : PiData L') {A : Subgroup G} (hA : A ≤ Subgroup.normalizer (L' : Set G))
    {y : G} (hy : y ∈ A) : D.pf y ∈ D.im A :=
  (D.mem_im_pf hA).2 ⟨y, hy, rfl⟩

omit [Finite G] in
theorem im_two (D : PiData L') {K : Subgroup G} (hK : IsPGroup 2 ↥K) :
    ∀ σ ∈ D.im K, ∃ k : ℕ, σ ^ 2 ^ k = 1 := by
  intro σ hσ
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hσ
  obtain ⟨k, hk⟩ := hK ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h1 : y ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [← map_pow, h1, map_one]

end PiHelpers

omit [Finite G] in
theorem s2I_le_baum : s2I S L ≤ baum S := inf_le_left

omit [Finite G] in
theorem s2SI_le_S : s2SI S L ≤ S := inf_le_left

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem isPGroup_S : IsPGroup 2 ↥S := c.data.cs.setting.isPGroup.to_le c.data.cs.le_T

theorem R_le_SI : baum S ≤ s2SI S L := le_inf (C1GN.baum_le S) c.rn₁

theorem U₂_le_I : blockU (cj t L) ≤ s2I S L :=
  le_inf c.u₂R fun u hu => by
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    exact c.data.comm_elem l hl u (Data.U₂_le_L₂ hu)

theorem I_le_normalizer₂ : s2I S L ≤ Subgroup.normalizer (cj t L : Set G) :=
  s2I_le_baum.trans c.rn₂

theorem SI_le_normalizer₂ : s2SI S L ≤ Subgroup.normalizer (cj t L : Set G) :=
  c.data.SI_le_normalizer_L₂

theorem isPGroup_I : IsPGroup 2 ↥(s2I S L) :=
  c.isPGroup_S.to_le (s2I_le_baum.trans (C1GN.baum_le S))

theorem isPGroup_SI : IsPGroup 2 ↥(s2SI S L) := c.isPGroup_S.to_le s2SI_le_S

theorem I_inf_D₂_le : s2I S L ⊓ s2I S (cj t L) ≤ baumD S L := by
  have h := c.data
  rintro d ⟨hdI, hd⟩
  refine ⟨hdI.1, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
  rw [h.join] at hx
  obtain ⟨l, hl, l₂, hl₂, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer h.L₂_le_normalizer).1 hx
  have e1 := Subgroup.mem_centralizer_iff.1 hdI.2 l hl
  have e2 := Subgroup.mem_centralizer_iff.1 hd.2 l₂ hl₂
  calc l * l₂ * d = l * (l₂ * d) := by group
    _ = l * (d * l₂) := by rw [e2]
    _ = (l * d) * l₂ := by group
    _ = (d * l) * l₂ := by rw [e1]
    _ = d * (l * l₂) := by group

theorem Phi_le_Q₂ {P₂ : A5Pi (cj t L)} (hI : P₂.im (s2I S L) = Estd) :
    frattiniOf (s2I S L) ≤ s2Q1 S (cj t L) := by
  have hIN := c.I_le_normalizer₂
  have hmem : ∀ {y : G}, y ∈ s2I S L → P₂.pf y ∈ Estd := fun {y} hy =>
    hI ▸ pf_mem_im P₂.toPiData hIN hy
  have hQ : ∀ {z : G}, z ∈ s2I S L → P₂.pf z = 1 → z ∈ s2Q1 S (cj t L) := by
    intro z hz h1
    rw [c.q₂]
    refine ⟨s2I_le_baum hz, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    exact (comm_of_pf_eq_one P₂.toPiData (hIN hz) h1 v hv).symm
  refine frat_le_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · have hxy : x * y * x⁻¹ * y⁻¹ ∈ s2I S L :=
      (s2I S L).mul_mem ((s2I S L).mul_mem ((s2I S L).mul_mem hx hy) ((s2I S L).inv_mem hx))
        ((s2I S L).inv_mem hy)
    refine hQ hxy ?_
    have hxN := hIN hx
    have hyN := hIN hy
    rw [P₂.toPiData.pf_mul (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN),
      P₂.toPiData.pf_mul (mul_mem hxN hyN) (inv_mem hxN), P₂.toPiData.pf_mul hxN hyN,
      P₂.toPiData.pf_inv hxN, P₂.toPiData.pf_inv hyN]
    have hc := Eset_comm _ (hmem hx) _ (hmem hy)
    have hs := Eset_sq _ (hmem hx)
    have hs' := Eset_sq _ (hmem hy)
    have e1 : (P₂.pf x)⁻¹ = P₂.pf x := inv_eq_of_mul_eq_one_right hs
    have e2 : (P₂.pf y)⁻¹ = P₂.pf y := inv_eq_of_mul_eq_one_right hs'
    rw [e1, e2]
    calc P₂.pf x * P₂.pf y * P₂.pf x * P₂.pf y = P₂.pf x * (P₂.pf y * P₂.pf x) * P₂.pf y := by
          group
      _ = P₂.pf x * (P₂.pf x * P₂.pf y) * P₂.pf y := by rw [hc]
      _ = (P₂.pf x * P₂.pf x) * (P₂.pf y * P₂.pf y) := by group
      _ = 1 := by rw [hs, hs', one_mul]
  · refine hQ ((s2I S L).pow_mem hx 2) ?_
    have hxN := hIN hx
    rw [pow_two, P₂.toPiData.pf_mul hxN hxN]
    exact Eset_sq _ (hmem hx)

theorem Phi_decomp {P₂ : A5Pi (cj t L)} (hI : P₂.im (s2I S L) = Estd) {f : G}
    (hf : f ∈ frattiniOf (s2I S L)) : ∃ u ∈ blockU (cj t L), ∃ d ∈ baumD S L, f = u * d := by
  have hfI : f ∈ s2I S L := Subgroup.map_subtype_le _ hf
  have hfQ : f ∈ s2Q1 S (cj t L) := c.Phi_le_Q₂ hI hf
  obtain ⟨hc2, hi2, hs2⟩ := c.dir₂
  have hDN : s2I S (cj t L) ≤ Subgroup.normalizer (blockU (cj t L) : Set G) :=
    C5.le_normalizer_of_commute fun i hi u hu => by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2 hu
      exact Subgroup.mem_centralizer_iff.mp this i hi
  rw [← hs2] at hfQ
  obtain ⟨u, hu, d, hd, hfud⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDN).1 hfQ
  refine ⟨u, hu, d, c.I_inf_D₂_le ⟨?_, hd⟩, hfud⟩
  have hdeq : d = u⁻¹ * f := by rw [hfud]; group
  rw [hdeq]
  exact (s2I S L).mul_mem ((s2I S L).inv_mem (c.U₂_le_I hu)) hfI

end Ctx

end CFSG.QuasithinUnique.A5.S2
