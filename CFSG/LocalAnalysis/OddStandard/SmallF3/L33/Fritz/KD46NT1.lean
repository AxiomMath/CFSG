module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NQ1
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NT1

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

theorem cols_of_mem_T₁ (H : Hyp S R) {g : X} (hg : g ∈ R) :
    ∃ e f p q : Fin 2, ∀ i, I.μ ⟨g, I.R_le H hg⟩ (bas i) = tCols e f p q 0 i := by
  have htB : t ∈ S.B := subset_closure (by simp)
  have hgB := (conj_mem_B_N S) (H.le_normalizer hg) htB
  have hgc : ConjTo t (g * t * g⁻¹) := ⟨g, rfl⟩
  obtain ⟨w, hw⟩ := I.eq_wV (I.conj_wV_mem (I.R_le H hg) (0, 0, 1, 0))
  have htw : I.wV (0, 0, 1, 0) = t := by simp [wV]
  rw [htw] at hw
  have hc := hgc
  rw [hw, I.conjTo_wV_iff H.fus] at hc
  have hB := hgB
  rw [hw, I.wV_mem_B_iff] at hB
  obtain ⟨e, b, c, f⟩ := w
  simp only at hc hB
  subst hc hB
  obtain ⟨p, q, a, hpqa⟩ := I.exists_tCols H hg hw
  have ha : a = 0 := by
    have h1 := I.μ_ki H ⟨g, I.R_le H hg⟩
    rw [hpqa 3] at h1
    have : (tCols e f p q a 3).1 = (bas 3).1 := congrArg Prod.fst h1
    simpa [tCols, bas] using this
  subst ha
  exact ⟨e, f, p, q, hpqa⟩

theorem inv_mul_mem_centralizer_of_μ {n m : normalizer (I.E : Set X)}
    (h : ∀ i, I.μ n (bas i) = I.μ m (bas i)) : ((n⁻¹ * m : normalizer (I.E : Set X)) : X) ∈
      centralizer (I.E : Set X) := by
  apply (I.μ_eq_id_iff _).mp
  intro i
  rw [I.μ_mul, ← h i, ← I.μ_mul, inv_mul_cancel, I.μ_one]

theorem commutator_mem_centralizer (H : Hyp S R) {g h : X} (hg : g ∈ R) (hh : h ∈ R) :
    g * h * g⁻¹ * h⁻¹ ∈ centralizer (I.E : Set X) := by
  obtain ⟨e, f, p, q, hgc⟩ := I.cols_of_mem_T₁ H hg
  obtain ⟨e', f', p', q', hhc⟩ := I.cols_of_mem_T₁ H hh
  set G : normalizer (I.E : Set X) := ⟨g, I.R_le H hg⟩
  set Hh : normalizer (I.E : Set X) := ⟨h, I.R_le H hh⟩
  have hcomm : ∀ i, I.μ (G * Hh) (bas i) = I.μ (Hh * G) (bas i) := by
    intro i
    rw [I.μ_comp hgc hhc, I.μ_comp hhc hgc]
    exact tCols_comm e f p q e' f' p' q' i
  have h1 := I.inv_mul_mem_centralizer_of_μ (fun i => (hcomm i).symm)
  have h2 : g * h * g⁻¹ * h⁻¹ = (h * g) * ((h * g)⁻¹ * (g * h)) * (h * g)⁻¹ := by group
  rw [h2]
  have hhgN : h * g ∈ normalizer (I.E : Set X) := mul_mem (I.R_le H hh) (I.R_le H hg)
  exact I.conj_mem_centralizerE hhgN (by simpa using h1)

end Inst

theorem Hyp.commutator_mem_B (H : Hyp S R) {g h : X} (hg : g ∈ R) (hh : h ∈ R) :
    g * h * g⁻¹ * h⁻¹ ∈ S.B := by
  set c := g * h * g⁻¹ * h⁻¹ with hc
  have hcT₁ : c ∈ R := mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hmemE : ∀ I : Inst S, c ∈ I.E := by
    intro I
    have hcC := I.commutator_mem_centralizer H hg hh
    have hct : c ∈ S.TE := by
      have hcCt : c ∈ centralizer ({t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hcC) t I.t_mem_E).symm
      rw [← H.inf_C]
      exact mem_inf.mpr ⟨hcT₁, hcCt⟩
    rcases I.yi_or with hy | hy
    · have := (KD46.mem_E_of_commute S) (Or.inl rfl) hct (fun e he => by
        have h1 := (mem_centralizer_iff.mp hcC) e (by rw [Inst.E, hy]; exact he)
        exact h1.symm)
      rw [Inst.E, hy]; exact this
    · have := (KD46.mem_E_of_commute S) (Or.inr rfl) hct (fun e he => by
        have h1 := (mem_centralizer_iff.mp hcC) e (by rw [Inst.E, hy]; exact he)
        exact h1.symm)
      rw [Inst.E, hy]; exact this
  exact (KD46.mem_B_of_mem_E_inter S) (hmemE (inst₁ S)) (hmemE (inst₂ S))

theorem Hyp.conj_mem_T₁ (H : Hyp S R) {S₁ : Subgroup X} (hTS : R ≤ S₁)
    (hS₁ : Nat.card S₁ = 256) {s g : X} (hs : s ∈ S₁) (hg : g ∈ R) : s * g * s⁻¹ ∈ R := by
  have hcard : Nat.card R = 128 := by rw [H.card, (card_TE S)]
  have hidx : (R.subgroupOf S₁).index = 2 := by
    have h1 := (R.subgroupOf S₁).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv, hcard, hS₁] at h1
    omega
  have hn := Subgroup.normal_of_index_eq_two hidx
  have := hn.conj_mem ⟨g, hTS hg⟩ (by rw [mem_subgroupOf]; exact hg) ⟨s, hs⟩
  rwa [mem_subgroupOf] at this

theorem Hyp.commutator_mem (H : Hyp S R) {g h : X} (hg : g ∈ R) (hh : h ∈ R) :
    ∃ a d : Fin 2, g * h * g⁻¹ * h⁻¹ = S.z ^ (a : ℕ) * S.k ^ (d : ℕ) := by
  set I := (inst₁ S)
  obtain ⟨S₁, -, hS₁N, -, hTS, hS₁c, hS₁C⟩ := I.exists_S₁ H
  obtain ⟨-, -, hreal⟩ := I.Q₁_props H hS₁N hS₁c hS₁C
  obtain ⟨ε, -, -, -, -, -, w', hw', -, -, hw'c⟩ := I.exists_vww H
  have hw'K : w' ∈ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) := by
    rw [I.oddTwoCoreIn_eq H]
    refine ⟨⟨w', hw'⟩, ?_, rfl⟩
    show I.blockHom H ⟨w', hw'⟩ ∈ transl
    intro j
    rw [I.blockHom_apply, I.blockHom_apply, I.μ_eq_lin, I.μ_eq_lin _ (pt 0),
      show (fun i => I.μ ⟨w', hw'⟩ (bas i)) = w'C ε from funext hw'c]
    exact w'C_transl ε j
  obtain ⟨q, hq, hqw⟩ := hreal w' hw'K
  have hqS : q ∈ S₁ := hq.1
  have hqN : q ∈ normalizer (I.E : Set X) := hS₁N hqS
  have hqc : ∀ i, I.μ ⟨q, hqN⟩ (bas i) = w'C ε i := by
    intro i
    have h1 := (I.μ_eq_id_iff ⟨q⁻¹ * w', mul_mem (inv_mem hqN) hw'⟩).mpr hqw i
    have e : (⟨w', hw'⟩ : normalizer (I.E : Set X)) =
        ⟨q, hqN⟩ * ⟨q⁻¹ * w', mul_mem (inv_mem hqN) hw'⟩ := Subtype.ext (by simp)
    have h2 := hw'c i
    rw [e, I.μ_mul, h1] at h2
    exact h2
  set b := g * h * g⁻¹ * h⁻¹ with hb
  have hbB := H.commutator_mem_B hg hh
  have hqb : q * b * q⁻¹ ∈ S.B := by
    have e : q * b * q⁻¹ = (q * g * q⁻¹) * (q * h * q⁻¹) * (q * g * q⁻¹)⁻¹ * (q * h * q⁻¹)⁻¹ := by
      rw [hb]; group
    rw [e]
    exact H.commutator_mem_B (H.conj_mem_T₁ hTS hS₁c hqS hg) (H.conj_mem_T₁ hTS hS₁c hqS hh)
  have hbE : b ∈ I.E := I.B_le_E hbB
  obtain ⟨w, hw⟩ := I.eq_wV hbE
  have hwB : I.wV w ∈ S.B := hw ▸ hbB
  rw [I.wV_mem_B_iff] at hwB
  have hqw' : q * b * q⁻¹ = I.wV (lin (w'C ε) w) := by
    rw [hw]
    have h1 := I.conj_wV ⟨q, hqN⟩ w
    rw [I.μ_eq_lin, show (fun i => I.μ ⟨q, hqN⟩ (bas i)) = w'C ε from funext hqc] at h1
    exact h1
  have hqwB := hqb
  rw [hqw', I.wV_mem_B_iff] at hqwB
  obtain ⟨a, b', c, d⟩ := w
  simp only at hwB
  subst hwB
  have hc : c = 0 := w'C_yi ε a c d hqwB
  subst hc
  refine ⟨a, d, ?_⟩
  rw [hw]
  simp [Inst.wV, I, inst₁]

end CFSG.OddStandard.SmallF3.L33.KD.KD46
