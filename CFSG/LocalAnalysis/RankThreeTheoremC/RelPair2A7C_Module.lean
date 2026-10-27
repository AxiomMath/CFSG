module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

theorem a7q_a7Five_ne_bot : a7Five ≠ ⊥ := by
  intro h
  have hc : cTwo ∈ a7Five :=
    mem_a7Five_iff.mpr ⟨eNine_le_alternatingGroup cTwo_mem_eNine, by decide, by decide⟩
  rw [h, Subgroup.mem_bot] at hc
  exact absurd hc (by decide)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a7q_commutator_subgroupOf {A B M : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    ⁅A.subgroupOf M, B.subgroupOf M⁆ = (⁅A, B⁆ : Subgroup G).subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hA hB)]

omit [Finite G] in
theorem a7q_le_normalizer_commutator {M A B : Subgroup G} (hA : M ≤ normalizer (A : Set G))
    (hB : M ≤ normalizer (B : Set G)) : M ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

omit [Finite G] in
theorem a7q_le_normalizer_centralizer {M A : Subgroup G} (hA : M ≤ normalizer (A : Set G)) :
    M ≤ normalizer (centralizer (A : Set G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro a ha
  have ha' : g⁻¹ * a * g ∈ A := by
    simpa using Subgroup.le_normalizer_iff.mp hA g⁻¹ (inv_mem hg) a ha
  have key := hc _ ha'
  calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * a := by group

theorem a7q_eq_bot_of_isPerfect {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : Group.IsPerfect P) (hp : IsPGroup p P) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isNilpotent P hp.isNilpotent

omit [Finite G] in
theorem a7q_commutator_le_of_perfect {M N P X : Subgroup G} (hP : Group.IsPerfect P)
    (hPM : P ≤ M) (hXM : X ≤ M) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (h : ⁅⁅P, X⁆, P⁆ ≤ N) : ⁅P, X⁆ ≤ N := by
  have : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hPX : ⁅P, X⁆ ≤ M := Subgroup.commutator_le_of_le hPM hXM
  have : Group.IsPerfect (P.subgroupOf M) := by
    rw [Subgroup.isPerfect_iff, a7q_commutator_subgroupOf hPM hPM,
      Subgroup.isPerfect_iff.mp hP]
  have key := CFSG.LocalCores.perfect_double_commutator
    (Group.IsPerfect.map (QuotientGroup.mk' (N.subgroupOf M)) (H := P.subgroupOf M))
    (X := (X.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) (by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
        a7q_commutator_subgroupOf hPM hXM, a7q_commutator_subgroupOf hPX hPM,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact fun g hg => h hg)
  rw [← Subgroup.map_commutator, a7q_commutator_subgroupOf hPM hXM, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at key
  exact fun g hg => key (show (⟨g, hPX hg⟩ : M) ∈ (⁅P, X⁆ : Subgroup G).subgroupOf M from hg)

theorem a7q_le_of_le_commutator_sup {p : ℕ} [Fact p.Prime] {P A B : Subgroup G}
    (hP : IsPGroup p P) (hAB : A ≤ B) (hBP : B ≤ P) (hA : P ≤ normalizer (A : Set G))
    (h : B ≤ ⁅B, P⁆ ⊔ A) : B ≤ A := by
  have : (A.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hA
  have hnil : Group.IsNilpotent (↥P ⧸ A.subgroupOf P) := (hP.to_quotient _).isNilpotent
  have hBP' : ⁅B, P⁆ ≤ P := Subgroup.commutator_le_of_le hBP le_rfl
  have h1 : (B.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P)) ≤
      ⁅(B.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P)), ⊤⁆ := by
    have h2 : B.subgroupOf P ≤ ⁅B.subgroupOf P, ⊤⁆ ⊔ A.subgroupOf P := by
      rw [← Subgroup.subgroupOf_self P, a7q_commutator_subgroupOf hBP le_rfl,
        ← Subgroup.subgroupOf_sup hBP' (hAB.trans hBP)]
      exact fun x hx => h hx
    have h3 := Subgroup.map_mono (f := QuotientGroup.mk' (A.subgroupOf P)) h2
    rwa [Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge, sup_bot_eq] at h3
  have hle : ∀ n, (B.subgroupOf P).map (QuotientGroup.mk' (A.subgroupOf P)) ≤
      (⊤ : Subgroup (↥P ⧸ A.subgroupOf P)).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact h1.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have hbot := hle n
  rw [hn, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact fun b hb => hbot (show (⟨b, hBP hb⟩ : P) ∈ B.subgroupOf P from hb)

omit [Finite G] in
theorem a7q_pCoreOf_le_a7I {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) : pCoreOf 2 H ≤ a7I H ι := by
  obtain ⟨Q, hQ⟩ := hF.sylow
  intro g hg
  rw [← hQ] at hg
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨h, hh, hhk⟩ := Subgroup.mem_map.mp k.2
  have h1 : ι h = 1 := by
    rw [← MonoidHom.mem_ker, hF.ker_eq]
    exact hh
  exact mem_a7I_iff.mpr ⟨h, h1 ▸ one_mem _, hhk⟩

theorem A7Frame.exists_module {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {Y Y₁ : Subgroup G} (hYI : Y ≤ a7I H ι)
    (hYx : CFSG.AGLEmbedding.InClassXBlock Y) (hY₁Y : Y₁ ≤ Y)
    (hY₁n : a7I H ι ≤ normalizer (Y₁ : Set G)) (hperf : Group.IsPerfect Y₁)
    (hι : (Y₁.subgroupOf H).map ι = a7Five) :
    ⁅pCoreOf 2 H, Y₁⁆ ≤ a7W H ∧ ⁅pCoreOf 2 H, Y₁⁆ ≠ ⊥ ∧
      ⁅(⁅pCoreOf 2 H, Y₁⁆ : Subgroup G), Y₁⁆ = ⁅pCoreOf 2 H, Y₁⁆ := by
  obtain ⟨-, -, ⟨hUQC, hU2⟩, -, -, hirr⟩ := hYx.1
  have hS₀I : pCoreOf 2 H ≤ a7I H ι := a7q_pCoreOf_le_a7I hF
  have hIS : a7I H ι ≤ normalizer (pCoreOf 2 H : Set G) := (a7I_le H ι).trans hF.H_norm.ge
  have hY₁I : Y₁ ≤ a7I H ι := hY₁Y.trans hYI
  set S₀ := pCoreOf 2 H
  set I := a7I H ι
  set R : Subgroup G := ⁅S₀, Y₁⁆
  have hIR : I ≤ normalizer (R : Set G) := a7q_le_normalizer_commutator hIS hY₁n
  have hRS : R ≤ S₀ := le_normalizer_iff_commutator_le_left.mp (hY₁I.trans hIS)
  have hRY₁ : R ≤ Y₁ := le_normalizer_iff_commutator_le_right.mp (hS₀I.trans hY₁n)
  have hRQ : R ≤ CFSG.QuasithinUnique.blockQ Y := by
    refine (le_inf hRS hRY₁).trans ?_
    refine normal_pGroup_le_pCoreOf 2 (S₀ ⊓ Y₁) Y (inf_le_right.trans hY₁Y) ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right.trans hY₁Y)).mpr
      ((le_inf (hYI.trans hIS) (hYI.trans hY₁n)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hRR : ⁅R, Y₁⁆ = R := by
    refine le_antisymm (le_normalizer_iff_commutator_le_left.mp (hY₁I.trans hIR)) ?_
    have hN : ⁅R, Y₁⁆ ≤ I :=
      ((le_normalizer_iff_commutator_le_left.mp (hY₁I.trans hIR)).trans hRS).trans hS₀I
    have key := a7q_commutator_le_of_perfect hperf hY₁I hS₀I hN
      (a7q_le_normalizer_commutator hIR hY₁n)
      (by rw [Subgroup.commutator_comm Y₁ S₀])
    rwa [Subgroup.commutator_comm Y₁ S₀] at key
  have hRU : R ≤ CFSG.QuasithinUnique.blockU Y :=
    hRR.ge.trans (Subgroup.commutator_mono hRQ hY₁Y)
  have hcomm : ∀ a ∈ CFSG.QuasithinUnique.blockU Y, ∀ b ∈ CFSG.QuasithinUnique.blockU Y,
      a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp ((hUQC.trans inf_le_right) ha) b
      ((hUQC.trans inf_le_left) hb)).symm
  have hR0 : R ≠ ⊥ := by
    intro hR
    have hY₁C : Y₁ ≤ centralizer (S₀ : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR)
    have hY₁S : Y₁ ≤ S₀ := (le_inf (hY₁I.trans (a7I_le H ι)) hY₁C).trans hF.charTwo
    have hY₁bot : Y₁ = ⊥ := a7q_eq_bot_of_isPerfect hperf ((pCoreOf_isPGroup 2 H).to_le hY₁S)
    apply a7q_a7Five_ne_bot
    rw [← hι, hY₁bot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hTY : ⁅⁅R, S₀⁆, Y₁⁆ = ⊥ := by
    have hTR : ⁅R, S₀⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp (hS₀I.trans hIR)
    have hYT : Y ≤ normalizer ((⁅R, S₀⁆ : Subgroup G) : Set G) :=
      a7q_le_normalizer_commutator (hYI.trans hIR) (hYI.trans hIS)
    have hYZ : Y ≤ normalizer (CFSG.QuasithinUnique.blockZ Y : Set G) :=
      (le_inf (Subgroup.normalizer_commutator_ge_right _ _)
        (a7q_le_normalizer_centralizer Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases hirr (⁅R, S₀⁆ ⊔ CFSG.QuasithinUnique.blockZ Y) le_sup_right
        (sup_le (hTR.trans hRU) inf_le_left)
        ((le_inf hYT hYZ).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)) with h | h
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((le_sup_left.trans h.le).trans (inf_le_right.trans (Subgroup.centralizer_le hY₁Y)))
    · exfalso
      have hS₀n : S₀ ≤ normalizer ((R ⊓ centralizer (Y₁ : Set G) : Subgroup G) : Set G) :=
        (le_inf (hS₀I.trans hIR) (a7q_le_normalizer_centralizer (hS₀I.trans hY₁n))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hTZ : ⁅R, S₀⁆ ≤ normalizer (CFSG.QuasithinUnique.blockZ Y : Set G) := by
        intro t ht
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
        exact fun z hz => hcomm z hz.1 t (hTR.trans hRU ht)
      have hle := a7q_le_of_le_commutator_sup (pCoreOf_isPGroup 2 H) inf_le_left hRS hS₀n (by
        intro r hr
        have hr' : r ∈ ((⁅R, S₀⁆ ⊔ CFSG.QuasithinUnique.blockZ Y : Subgroup G) : Set G) := by
          rw [h]
          exact hRU hr
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTZ] at hr'
        obtain ⟨t, ht, z, hz, rfl⟩ := hr'
        refine Subgroup.mul_mem_sup ht ⟨?_, Subgroup.centralizer_le hY₁Y hz.2⟩
        simpa using R.mul_mem (R.inv_mem (hTR ht)) hr)
      apply hR0
      rw [← hRR]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans inf_le_right)
  have hRR' : ⁅R, R⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b (hRU hb) a (hRU ha)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := R) (H₂ := Y₁) (H₃ := S₀)
    (by rw [Subgroup.commutator_comm Y₁ S₀]; exact hRR')
    (by rw [Subgroup.commutator_comm S₀ R]; exact hTY)
  rw [hRR] at h3
  have hRC : R ≤ centralizer (S₀ : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact ⟨fun r hr => Subgroup.subset_closure ⟨⟨hRS hr, hRC hr⟩, hU2 r (hRU hr)⟩, hR0, hRR⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
