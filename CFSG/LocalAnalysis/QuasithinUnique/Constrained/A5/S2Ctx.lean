module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Count
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCPf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Pi

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

section PiHelpers

variable {L' : Subgroup G}

omit [Finite G] in
theorem pf_eq_one_of_comm (D : PiData L') {y : G} (hy : y ∈ Subgroup.normalizer (L' : Set G))
    (hc : ∀ u ∈ blockU L', y * u = u * y) : D.pf y = 1 := by
  rw [D.pf_eq hy, D.hker ⟨y, hy⟩]
  intro u hu
  calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [hc u hu]
    _ = u := by group

omit [Finite G] in
theorem comm_of_pf_eq_one (D : PiData L') {y : G} (hy : y ∈ Subgroup.normalizer (L' : Set G))
    (h1 : D.pf y = 1) : ∀ u ∈ blockU L', y * u = u * y := by
  intro u hu
  rw [D.pf_eq hy, D.hker ⟨y, hy⟩] at h1
  have := h1 u hu
  calc y * u = (y * u * y⁻¹) * y := by group
    _ = u * y := by rw [this]

end PiHelpers

namespace Data

variable {t : G} (h : Data T M H S L t)
include h

theorem double₁ : conjJoin S L ≠ L := by
  intro hh
  apply h.ne
  have hle : cj t L ≤ L := by
    have := h.L₂_le_L₀
    rwa [hh] at this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])

end Data

structure Ctx (T M H S L : Subgroup G) (t : G) : Prop where
  data : Data T M H S L t
  rn₁ : baum S ≤ Subgroup.normalizer (L : Set G)
  rn₂ : baum S ≤ Subgroup.normalizer (cj t L : Set G)
  u₁q : blockU L ≤ s2Q1 S L
  u₂q : blockU (cj t L) ≤ s2Q1 S (cj t L)
  q₁ : s2Q1 S L = baum S ⊓ Subgroup.centralizer (blockU L : Set G)
  q₂ : s2Q1 S (cj t L) = baum S ⊓ Subgroup.centralizer (blockU (cj t L) : Set G)
  dir₁ : IsInternalDirect (blockU L) (s2I S L) (s2Q1 S L)
  dir₂ : IsInternalDirect (blockU (cj t L)) (s2I S (cj t L)) (s2Q1 S (cj t L))
  poH : pCoreOf 2 H = baumD S L ⊔ blockU0 S L
  maxQ : IsMaxElemAbelian S (pCoreOf 2 H)
  baumJ : baum S = thompsonJ S
  std₁ : ∃ P : A5Pi L, P.im (baum S) = Estd ∧ P.im (thompsonJ S) = Estd
  std₂ : ∃ P : A5Pi (cj t L), P.im (baum S) = Estd ∧ P.im (thompsonJ S) = Estd

theorem ctx_of (hC54 : LemmaC54_3_s2) (h567 : Lemma245_C56_7) {t : G} (h : Data T M H S L t) :
    Ctx T M H S L t := by
  obtain ⟨rn₁, u₁q, q₁, dir₁, -⟩ := hC54 G T M H S L h.cs h.alt5 h.double₁
  obtain ⟨rn₂, u₂q, q₂, dir₂, -⟩ :=
    hC54 G T M H S (cj t L) h.cs₂ h.alt5₂ h.cfg₂.double
  obtain ⟨M₀, hSM₀, hM₀T, hidx⟩ := C56.exists_index_two h.cs
  obtain ⟨-, -, -, poH, maxQ, baumJ, -⟩ := h567 G T M H S L h.cs M₀ hSM₀ hM₀T hidx
  exact ⟨h, rn₁, rn₂, u₁q, u₂q, q₁, q₂, dir₁, dir₂, poH, maxQ, baumJ,
    exists_std2 hC54 h.cs h.alt5 h.double₁, exists_std2 hC54 h.cs₂ h.alt5₂ h.cfg₂.double⟩

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem u₁R : blockU L ≤ baum S := c.u₁q.trans (c.q₁ ▸ inf_le_left)

theorem u₂R : blockU (cj t L) ≤ baum S := c.u₂q.trans (c.q₂ ▸ inf_le_left)

theorem Q_inf_le : s2Q1 S L ⊓ s2Q1 S (cj t L) ≤ pCoreOf 2 H := by
  have h := c.data
  rintro q ⟨hq1, hq2⟩
  obtain ⟨hc1, hi1, hs1⟩ := c.dir₁
  obtain ⟨hc2, hi2, hs2⟩ := c.dir₂
  have hIN : s2I S L ≤ Subgroup.normalizer (blockU L : Set G) :=
    C5.le_normalizer_of_commute fun i hi u hu => by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1 hu
      exact Subgroup.mem_centralizer_iff.mp this i hi
  have hDN : s2I S (cj t L) ≤ Subgroup.normalizer (blockU (cj t L) : Set G) :=
    C5.le_normalizer_of_commute fun i hi u hu => by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2 hu
      exact Subgroup.mem_centralizer_iff.mp this i hi
  rw [← hs1] at hq1
  obtain ⟨u₁, hu₁, i, hi, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hIN).1 hq1
  have hu₁Q₂ : u₁ ∈ s2Q1 S (cj t L) := by
    rw [c.q₂]
    exact ⟨c.u₁R hu₁, Subgroup.mem_centralizer_iff.2 fun v hv => (h.comm_U u₁ hu₁ v hv).symm⟩
  have hiQ₂ : i ∈ s2Q1 S (cj t L) := by
    have := (s2Q1 S (cj t L)).mul_mem ((s2Q1 S (cj t L)).inv_mem hu₁Q₂) hq2
    simpa using this
  rw [← hs2] at hiQ₂
  obtain ⟨u₂, hu₂, d, hd, hid⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDN).1 hiQ₂
  have hu₂I : u₂ ∈ s2I S L :=
    ⟨c.u₂R hu₂, Subgroup.mem_centralizer_iff.2 fun l hl =>
      (h.comm_elem l hl u₂ (Data.U₂_le_L₂ hu₂))⟩
  have hdI : d ∈ s2I S L := by
    have : d = u₂⁻¹ * i := by rw [hid]; group
    rw [this]
    exact (s2I S L).mul_mem ((s2I S L).inv_mem hu₂I) hi
  have hdD : d ∈ baumD S L := by
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
  have hU : blockU0 S L = blockU L ⊔ blockU (cj t L) := h.blockU0_eq
  have hu₁P : u₁ ∈ pCoreOf 2 H := by
    rw [c.poH]
    exact Subgroup.mem_sup_right (by rw [hU]; exact Subgroup.mem_sup_left hu₁)
  have hu₂P : u₂ ∈ pCoreOf 2 H := by
    rw [c.poH]
    exact Subgroup.mem_sup_right (by rw [hU]; exact Subgroup.mem_sup_right hu₂)
  have hdP : d ∈ pCoreOf 2 H := by
    rw [c.poH]
    exact Subgroup.mem_sup_left hdD
  have : u₁ * i = u₁ * (u₂ * d) := by rw [hid]
  rw [this]
  exact (pCoreOf 2 H).mul_mem hu₁P ((pCoreOf 2 H).mul_mem hu₂P hdP)

theorem A_le {P₁ : A5Pi L} {P₂ : A5Pi (cj t L)} (hE₁ : P₁.im (baum S) = Estd)
    (hE₂ : P₂.im (baum S) = Estd) {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ≤ s2Q1 S L ⊔ s2Q1 S (cj t L) :=
  c.data.A_le_sup_Q P₁ P₂ hE₁ hE₂ c.rn₁ c.rn₂ c.u₁R c.u₂R c.q₁ c.q₂ c.poH c.maxQ c.Q_inf_le hA
    ((GammaExtra.le_thompsonJ hA).trans c.baumJ.ge)

theorem R_le {P₁ : A5Pi L} {P₂ : A5Pi (cj t L)} (hE₁ : P₁.im (baum S) = Estd)
    (hE₂ : P₂.im (baum S) = Estd) : baum S ≤ s2Q1 S L ⊔ s2Q1 S (cj t L) := by
  rw [c.baumJ]
  exact GammaExtra.thompsonJ_le fun A hA => c.A_le hE₁ hE₂ hA

theorem Q₂_le_normalizer_Q₁ : s2Q1 S (cj t L) ≤ Subgroup.normalizer (s2Q1 S L : Set G) := by
  have hQ₂R : s2Q1 S (cj t L) ≤ baum S := c.q₂ ▸ inf_le_left
  exact hQ₂R.trans ((le_sup_right : baum S ≤ L ⊔ baum S).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ baum S)))

theorem exists_P₂ : ∃ P₂ : A5Pi (cj t L), P₂.im (baum S) = Estd ∧ P₂.im (s2I S L) = Estd := by
  have h := c.data
  obtain ⟨P₁, hE₁, -⟩ := c.std₁
  obtain ⟨P₂, hE₂, -⟩ := c.std₂
  refine ⟨P₂, hE₂, le_antisymm (hE₂ ▸ P₂.im_mono inf_le_left) ?_⟩
  intro σ hσ
  have hσ' : σ ∈ P₂.im (baum S) := hE₂ ▸ hσ
  obtain ⟨r, hr, hrσ⟩ := (P₂.toPiData.mem_im_pf c.rn₂).1 hσ'
  have hr12 : r ∈ s2Q1 S L ⊔ s2Q1 S (cj t L) := c.R_le hE₁ hE₂ hr
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ :=
    (Lin2.mem_sup_iff_of_le_normalizer c.Q₂_le_normalizer_Q₁).1 hr12
  obtain ⟨hc1, hi1, hs1⟩ := c.dir₁
  have hIN : s2I S L ≤ Subgroup.normalizer (blockU L : Set G) :=
    C5.le_normalizer_of_commute fun i hi u hu => by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1 hu
      exact Subgroup.mem_centralizer_iff.mp this i hi
  have hq₁' := hq₁
  rw [← hs1] at hq₁'
  obtain ⟨u, hu, i, hi, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hIN).1 hq₁'
  have hQ₁R : s2Q1 S L ≤ baum S := c.q₁ ▸ inf_le_left
  have hQ₂R : s2Q1 S (cj t L) ≤ baum S := c.q₂ ▸ inf_le_left
  have huN : u ∈ Subgroup.normalizer (cj t L : Set G) :=
    h.L_le_normalizer₂ (Data.U₁_le_L hu)
  have hiN : i ∈ Subgroup.normalizer (cj t L : Set G) := c.rn₂ (inf_le_left (a := baum S) hi)
  have hq₂N : q₂ ∈ Subgroup.normalizer (cj t L : Set G) := c.rn₂ (hQ₂R hq₂)
  have hpu : P₂.pf u = 1 :=
    pf_eq_one_of_comm P₂.toPiData huN fun v hv => h.comm_U u hu v hv
  have hpq₂ : P₂.pf q₂ = 1 := by
    refine pf_eq_one_of_comm P₂.toPiData hq₂N fun v hv => ?_
    have hq₂C : q₂ ∈ Subgroup.centralizer (blockU (cj t L) : Set G) := by
      have := hq₂
      rw [c.q₂] at this
      exact this.2
    exact Subgroup.mem_centralizer_iff.mp hq₂C v hv |>.symm
  have hr : P₂.pf (u * i * q₂) = P₂.pf i := by
    rw [P₂.toPiData.pf_mul (mul_mem huN hiN) hq₂N, P₂.toPiData.pf_mul huN hiN, hpu, hpq₂]
    simp
  rw [← hrσ, hr]
  exact (P₂.toPiData.mem_im_pf (inf_le_left.trans c.rn₂)).2 ⟨i, hi, rfl⟩

end Ctx

end CFSG.QuasithinUnique.A5.S2
