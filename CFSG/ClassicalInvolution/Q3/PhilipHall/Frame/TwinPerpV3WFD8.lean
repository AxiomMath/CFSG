module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf69Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section D8outer




variable {n : ℕ}


section D8

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.cent_E (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) {v : Y} (hvE : v ∈ Subgroup.closure ({t, s, e} : Set Y)) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set Y) ≤
      Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
  obtain ⟨n', hn'N, hn'⟩ := hfr.r4 hB h hxo hxt hxM hmv hs he v hvE hv1
  intro c hc
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcn : (n'⁻¹ * c * n') * t = t * (n'⁻¹ * c * n') := by
    have h1 : c * (n' * t * n'⁻¹) = (n' * t * n'⁻¹) * c := by rw [hn']; exact hc'
    calc (n'⁻¹ * c * n') * t = n'⁻¹ * (c * (n' * t * n'⁻¹)) * n' := by group
      _ = n'⁻¹ * ((n' * t * n'⁻¹) * c) * n' := by rw [h1]
      _ = t * (n'⁻¹ * c * n') := by group
  have hmem := hfr.ct_mem_N hB h hxo hxt hxM hmv hs he hcn
  have : c = n' * (n'⁻¹ * c * n') * n'⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'N hmem) (Subgroup.inv_mem _ hn'N)

theorem WFFrame.trans (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) :
    ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K,
      ∃ g ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y), conjSub g K = J := by
  have hΩ := h.hyp
  have hP := h.partI
  have h2g := h.exit.2.2.2.1
  have hd := h.hStd.datum
  have hK : K ∈ CoreAssembly.conjClass (tightCore R) := hd.mem
  have hz : IsUniqueInvolution K t := hd.hz
  have htm : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hperp : ∀ i, KPerp (CoreAssembly.conjClass (tightCore R)) (M i) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (M i) := fun i =>
    kPerp_datum h.hStd.perp (hfr.mem i).1 (h.uniqInv (hfr.mem i))
  have key : ∀ W₁ : Subgroup Y, W₁ ∈ WSet (CoreAssembly.conjClass (tightCore R)) → t ∈ W₁ →
      ∀ J' : Subgroup Y, J' ∈ CoreAssembly.conjClass (tightCore R) →
      (∃ T ∈ DSet (CoreAssembly.conjClass (tightCore R)) W₁, IsSylow2In T J') →
      ∃ g ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y),
        conjSub g K = J' := by
    intro W₁ hW₁ htW₁ J' hJ'Ω ⟨T, hTD, hTJ'⟩
    have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W₁ := Q3CL.T8.ctxOf hP hW₁
    have hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W₁ :=
      twin_mem_DSet hP h2g hW₁ htW₁ hK hz
    have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W₁, ρ.K = K :=
      ⟨Q3CL.T8.mkRep hP hW₁ hK hKD hKsyl, rfl⟩
    obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W₁, σ.K = J' :=
      ⟨Q3CL.T8.mkRep hP hW₁ hJ'Ω hTD hTJ', rfl⟩
    have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W₁ :=
      not_dbarConnected_of_wyl' hP hd (kPerp_datum h.hStd.perp hd.mem hd.hz) hW₁ ρ hρK
        (h.hStd.wyl W₁ hW₁)
    obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ
    refine ⟨m, ?_, by rw [← hσK, ← hmK, hρK]⟩
    have hMH : MGrp (CoreAssembly.conjClass (tightCore R)) W₁ ≤
        Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
      refine iSup₂_le fun R' hR' => ?_
      obtain ⟨KR, hKR, hRK⟩ := exists_isSylow2In_of_mem_RSet hR'.1
      have hKRR : KR = R' := hRK.2.2 KR le_rfl (h2g KR hKR) hRK.1
      obtain ⟨zR, hzR⟩ := Sec6Gen.exists_uniqueInvolution hΩ hKR
      have hRc : R' ≤ Subgroup.centralizer ({zR} : Set Y) := fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hzR.commute_of_mem (hKRR ▸ hr)).symm
      have hzE : zR ∈ Subgroup.closure ({t, s, e} : Set Y) := by
        by_cases htw : KR ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K
        · have := (hzR.eq (isUniqueInvolution_of_mem_twinSet hz htw))
          rw [this]; exact htm
        · have hne0 : KR ≠ M 0 := fun e1 => htw (e1 ▸ hfr.mem 0)
          have hnb : M 0 ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) KR := by
            intro hnb
            have h1 := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hKR (hfr.mem 0).1 hnb
            have h2 : KR ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (M 0) :=
              Set.mem_insert_of_mem _ h1
            rw [hperp 0] at h2
            exact htw (by
              rw [← twinSet_eq_of_mem_twinSet hd.hz (hfr.mem 0)]; exact h2)
          have hq8R : Q8Facts KR zR := by
            obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h2g KR hKR
            exact q8Facts_of_iso hzR e
          have hRD : KR ∈ DSet (CoreAssembly.conjClass (tightCore R)) W₁ := hKRR ▸ hR'
          obtain ⟨w, hwK, hwW, hww⟩ := exists_gen_sq hΩ hW₁ hKR hRD (h2g KR hKR) hq8R
          obtain ⟨kk, hkk, hprod, -⟩ := hfr.frame_rel h hW₁ htW₁ hKR hRD hzR hne0 hnb
            (w := w) (Subgroup.mem_inf.mpr ⟨hwK, hwW⟩) hww
          rw [← hprod]
          exact hfr.frame_mem_E hB h hxo hxt hxM hmv hs he hW₁ htW₁
            (fun i => ⟨(Subgroup.mem_inf.mp (hkk i).1).1, (Subgroup.mem_inf.mp (hkk i).1).2,
              (hkk i).2⟩)
      exact hRc.trans (hfr.cent_E hB h hxo hxt hxM hmv hs he hzE hzR.ne_one)
    exact hMH hm
  have step : ∀ J' : Subgroup Y, dstarAdj (CoreAssembly.conjClass (tightCore R)) K J' →
      ∃ g ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y),
        conjSub g K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h' | h'
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h'
      have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h'
      have hzW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2
      exact key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
  intro J hJ
  have hJ' : Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, Subgroup.one_mem _, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj (CoreAssembly.conjClass (tightCore R)) K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h' | h'⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]

theorem exists_sq_of_cyclic {J U : Subgroup Y} {z : Y} (hJq : Q8Facts J z) (hUJ : U ≤ J)
    (hcyc : IsCyclic ↥U) (h4 : 4 ≤ Nat.card ↥U) : ∃ g ∈ U, g * g = z := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥U := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgJ : (g : Y) ∈ J := hUJ g.2
  refine ⟨g, g.2, ?_⟩
  rcases hJq.sq_cases _ hgJ with e | e
  · exfalso
    have h2 : orderOf g ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply Subtype.ext
      show (g : Y) ^ 2 = 1
      rw [pow_two]; exact e
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · exact e

theorem cent_form {J W₁ : Subgroup Y} {t b g : Y} (hJq : Q8Facts J t) (hb : b ∈ J) (hbW : b ∈ W₁)
    (hb2 : b * b = t) (htW : t ∈ W₁) (hg : g ∈ J) (hgb : g * b = b * g) :
    (g = 1 ∨ g = t) ∨ (g ∈ W₁ ∧ g * g = t) := by
  rcases hJq.cent_cyc b hb hb2 g hg hgb with e | e | e | e
  · exact Or.inl (Or.inl e)
  · exact Or.inr ⟨by rw [e]; exact hbW, by rw [e]; exact hb2⟩
  · exact Or.inl (Or.inr e)
  · refine Or.inr ⟨by rw [e]; exact W₁.mul_mem hbW htW, ?_⟩
    rw [e]
    have hc : b * t = t * b := (hJq.z_central b hb).symm
    calc b * t * (b * t) = b * (t * b) * t := by group
      _ = b * (b * t) * t := by rw [← hc]
      _ = (b * b) * (t * t) := by group
      _ = t := by rw [hb2, hJq.z_sq, mul_one]

theorem WFFrame.centralizers_printed (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) {s e : Y} (hs : s = a 0 * a 1 * a 2 * a 3)
    (he : e = x * s * x⁻¹) :
    ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      K ⊓ W' ∈ USet (CoreAssembly.conjClass (tightCore R)) →
        TwinDisc.CentralizersPrinted (CoreAssembly.conjClass (tightCore R)) K W'
          (Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y)) := by
  intro W' hW' hU J hJ a' ha' ha'W ha'1 ha'2
  have hΩ := h.hyp
  have h2g := h.exit.2.2.2.1
  have hd := h.hStd.datum
  have hK : K ∈ CoreAssembly.conjClass (tightCore R) := hd.mem
  have hz : IsUniqueInvolution K t := hd.hz
  have hperpK := kPerp_datum h.hStd.perp hd.mem hd.hz
  have hJtw : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
    rw [← hperpK]; exact hJ
  have hKtw : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hK hz
  have hKq : Q8Facts K t := h.q8 hKtw
  have hJq : Q8Facts J t := h.q8 hJtw
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨g₀, hg₀U, hg₀⟩ := exists_sq_of_cyclic hKq inf_le_left hcyc h4
  have htW' : t ∈ W' := by rw [← hg₀]; exact W'.mul_mem (Subgroup.mem_inf.mp hg₀U).2 (Subgroup.mem_inf.mp hg₀U).2
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := fun c hc =>
    hfr.ct_mem_N hB h hxo hxt hxM hmv hs he (Subgroup.mem_centralizer_singleton_iff.mp hc)
  by_cases hJK : J = K
  ·
    subst hJK
    have : a' ∈ J := by simpa using ha'
    have e1 : a' = t := (hz.unique a' this ha'2).resolve_left ha'1
    rw [e1]; exact hCt
  · have hcomm : Commutes K J := h.comm hKtw hJtw (Ne.symm hJK)
    obtain ⟨k, hk, j, hj, hkj⟩ := mem_sup2 hcomm ha'
    have hKD := twin_mem_DSet h.partI h2g hW' htW' hK hz
    have hJD := twin_mem_DSet h.partI h2g hW' htW' hJtw.1 (h.uniqInv hJtw)
    obtain ⟨bK, hbKK, hbKW, hbK2⟩ := exists_gen_sq hΩ hW' hK hKD (h2g K hK) hKq
    obtain ⟨bJ, hbJJ, hbJW, hbJ2⟩ := exists_gen_sq hΩ hW' hJtw.1 hJD (h2g J hJtw.1) hJq
    have hab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW'
    have hkb : k * bK = bK * k := by
      have h1 : a' * bK = bK * a' := hab _ ha'W _ hbKW
      have h2 : j * bK = bK * j := (hcomm bK hbKK j hj).symm
      rw [hkj] at h1
      have h3 : k * bK * j = bK * k * j := by
        calc k * bK * j = k * (bK * j) := mul_assoc _ _ _
          _ = k * (j * bK) := by rw [h2]
          _ = k * j * bK := (mul_assoc _ _ _).symm
          _ = bK * (k * j) := h1
          _ = bK * k * j := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    have hjb : j * bJ = bJ * j := by
      have h1 : a' * bJ = bJ * a' := hab _ ha'W _ hbJW
      have h2 : k * bJ = bJ * k := hcomm k hk bJ hbJJ
      rw [hkj] at h1
      have h3 : k * (j * bJ) = k * (bJ * j) := by
        calc k * (j * bJ) = k * j * bJ := (mul_assoc _ _ _).symm
          _ = bJ * (k * j) := h1
          _ = (bJ * k) * j := (mul_assoc _ _ _).symm
          _ = (k * bJ) * j := by rw [h2]
          _ = k * (bJ * j) := mul_assoc _ _ _
      exact mul_left_cancel h3
    have hkf := cent_form hKq hbKK hbKW hbK2 htW' hk hkb
    have hjf := cent_form hJq hbJJ hbJW hbJ2 htW' hj hjb
    have hkjsq : a' * a' = (k * k) * (j * j) := by
      rw [hkj]
      have := hcomm k hk j hj
      calc k * j * (k * j) = k * (j * k) * j := by group
        _ = k * (k * j) * j := by rw [← this]
        _ = (k * k) * (j * j) := by group
    have ht := hKq.z_sq
    have hz1 : t ≠ 1 := hKq.z_ne
    have hsqs : (k * k) * (j * j) = 1 := hkjsq.symm.trans ha'2
    have ha't : a' = t → Subgroup.centralizer ({a'} : Set Y) ≤
        Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := fun e1 => by
      rw [e1]; exact hCt
    rcases hkf with (e1 | e1) | ⟨hkW, hk2⟩ <;> rcases hjf with (e2 | e2) | ⟨hjW, hj2⟩
    · exact absurd (by rw [hkj, e1, e2]; simp) ha'1
    · exact ha't (by rw [hkj, e1, e2]; simp)
    · rw [e1, hj2] at hsqs; simp at hsqs; exact absurd hsqs hz1
    · exact ha't (by rw [hkj, e1, e2]; simp)
    · exact absurd (by rw [hkj, e1, e2, ht]) ha'1
    · rw [e1, hj2, ht] at hsqs; simp at hsqs; exact absurd hsqs hz1
    · rw [e2, hk2] at hsqs; simp at hsqs; exact absurd hsqs hz1
    · rw [e2, hk2, ht] at hsqs; simp at hsqs; exact absurd hsqs hz1
    · rw [hkj]
      exact hfr.r5 hB h hxo hxt hxM hmv hs he hW' htW' hKtw hJtw (Ne.symm hJK)
        (Subgroup.mem_inf.mpr ⟨hk, hkW⟩) (Subgroup.mem_inf.mpr ⟨hj, hjW⟩)
        (orderOf_four_of_sq hk2 ht hz1) (orderOf_four_of_sq hj2 ht hz1)

theorem wfStepD_of_B0 (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hB : WFB0 n) : WFStepD n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W h x hxo hxt hxM hmv'
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  have hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x := fun i => hmv' (M i) (hfr.mem i)
  obtain ⟨s, hs⟩ : ∃ s, s = a 0 * a 1 * a 2 * a 3 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = x * s * x⁻¹ := ⟨_, rfl⟩
  have hd := h.hStd.datum
  have hcore : TwinCoreHyp n Y R S t := h.hStd.perp.core.toHyp
  have htop : Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) = ⊤ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.thmEW_apply hEW hcit hP hcore hd.mem hd.hK' hd.hne
      (hfr.trans hB h hxo hxt hxM hmv hs he) (hfr.centralizers_printed hB h hxo hxt hxM hmv hs he)
  have hEN : (Subgroup.closure ({t, s, e} : Set Y)).Normal := by
    refine ⟨fun p hp g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (Subgroup.closure ({t, s, e} : Set Y) : Set Y) := by
      rw [htop]; exact Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp hg p).mp hp
  have hP2 : IsPGroup 2 ↥(M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3) := by
    have := (v3_P_normalTwo h.hStd h.exit.2.2.2.1).2.1
    rwa [← hfr.sup_eq]
  have hP : ∀ i, ∀ m ∈ M i, m ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := fun i m hm => le_sup4 M i hm
  have hsP : s ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
    rw [hs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hP 0 _ (hfr.haM 0))
      (hP 1 _ (hfr.haM 1))) (hP 2 _ (hfr.haM 2))) (hP 3 _ (hfr.haM 3))
  have heP : e ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
    have e1 : e = (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by
      rw [he, hs]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hP 0 _ (hfr.act_mem hxM 0 (hfr.haM 0))) (hP 1 _ (hfr.act_mem hxM 1 (hfr.haM 1))))
      (hP 2 _ (hfr.act_mem hxM 2 (hfr.haM 2)))) (hP 3 _ (hfr.act_mem hxM 3 (hfr.haM 3)))
  have htP : t ∈ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := hP 0 _ (h.q8 (hfr.mem 0)).z_mem
  have hEP : Subgroup.closure ({t, s, e} : Set Y) ≤ M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact htP
    · exact hsP
    · exact heP
  have hE2 : IsPGroup 2 ↥(Subgroup.closure ({t, s, e} : Set Y)) := hP2.to_le hEP
  have hbot := TwinSecXg.normalTwo_eq_bot_of_fstar_simple hcore.simple hcore.nonab hEN hE2
  have htE : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  rw [hbot] at htE
  exact (h.q8 (hfr.mem 0)).z_ne (Subgroup.mem_bot.mp htE)

end D8

end D8outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
