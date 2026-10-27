module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinModel

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement

section Subnormal

variable {K G : Type*} [Group K] [Group G]

theorem le_of_isSubnormal_open {T X : Subgroup G} (h : CFSG.Open.IsSubnormal T X) : T ≤ X :=
  h.le

theorem isSubnormal_comap_inf (ψ : K →* G) {X T : Subgroup G} (H : Subgroup K)
    (hH : ∀ h ∈ H, ψ h ∈ X) (hT : CFSG.Open.IsSubnormal T X) :
    CFSG.Open.IsSubnormal (T.comap ψ ⊓ H) H := by
  induction hT with
  | refl T =>
    have : T.comap ψ ⊓ H = H := inf_eq_right.2 fun h hh => hH h hh
    rw [this]
    exact CFSG.Open.IsSubnormal.refl H
  | @step T M X hTM hN hM ih =>
    have hle : T.comap ψ ⊓ H ≤ M.comap ψ ⊓ H := inf_le_inf_right H (Subgroup.comap_mono hTM)
    refine CFSG.Open.IsSubnormal.step hle ?_ (ih hH)
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro n g hn hg
    refine Subgroup.mem_inf.2 ⟨?_, H.mul_mem (H.mul_mem hg.2 hn.2) (H.inv_mem hg.2)⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.normal_subgroupOf_iff hTM).1 hN (ψ n) (ψ g) hn.1 hg.1

end Subnormal

section Cover

variable {K G : Type*} [Group K] [Group G]

theorem conj_mem_commutator_of_mem {M : Subgroup K} {g n : K} (hg : g ∈ M) (hn : n ∈ ⁅M, M⁆) :
    g * n * g⁻¹ ∈ ⁅M, M⁆ := by
  have h : ⁅M, M⁆ ≤ (⁅M, M⁆).comap (MulAut.conj g).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := conjugate_commutatorElement a b g
    rw [e]
    exact Subgroup.commutator_mem_commutator (M.mul_mem (M.mul_mem hg ha) (M.inv_mem hg))
      (M.mul_mem (M.mul_mem hg hb) (M.inv_mem hg))
  exact h hn

theorem commutator_eq_of_isQuasisimple {T : Subgroup G} (hT : CFSG.Open.IsQuasisimple ↥T) :
    ⁅T, T⁆ = T := by
  have : Group.IsPerfect ↥T := ⟨hT.1⟩
  exact Subgroup.isPerfect_iff.mp this

theorem isComponentOf_commutator_comap (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) (s : K)
    {X T : Subgroup G} (hXs : ∀ g ∈ X, g * ψ s = ψ s * g)
    (hH : ∀ h ∈ Subgroup.centralizer ({s} : Set K), ψ h ∈ X)
    (hTX : CFSG.Open.IsSubnormal T X) (hTr : T ≤ ψ.range) (hTq : CFSG.Open.IsQuasisimple ↥T) :
    CFSG.Open.IsComponentOf ⁅T.comap ψ, T.comap ψ⁆ (Subgroup.centralizer ({s} : Set K)) := by
  set M := T.comap ψ with hM
  set Q := ⁅M, M⁆ with hQ
  have hQM : Q ≤ M := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hQq : CFSG.Open.IsQuasisimple ↥Q := by
    have hL' : CFSG.Open.IsQuasisimple ↥(T.subgroupOf ψ.range) :=
      (open_isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hTr)).2 hTq
    have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center K := by
      rwa [MonoidHom.ker_rangeRestrict]
    have hcomap : (T.subgroupOf ψ.range).comap ψ.rangeRestrict = M := by
      ext x
      rfl
    have := isQuasisimple_commutator_comap ψ.rangeRestrict ψ.rangeRestrict_surjective hker' hL'
    rwa [hcomap] at this
  have hQperf : Q ≤ ⁅Q, Q⁆ := (commutator_eq_of_isQuasisimple hQq).symm.le
  have hTX' : T ≤ X := le_of_isSubnormal_open hTX
  have hQs : Q ≤ Subgroup.centralizer ({s} : Set K) := by
    have hc : ∀ r ∈ Q, ⁅s, r⁆ ∈ Subgroup.center K := by
      intro r hr
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      have h2 := hXs (ψ r) (hTX' (hQM hr))
      calc ψ s * ψ r * (ψ s)⁻¹ * (ψ r)⁻¹ = (ψ r * ψ s) * (ψ s)⁻¹ * (ψ r)⁻¹ := by rw [h2]
        _ = 1 := by group
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.2
      (commutes_of_commutator_mem_center hQperf hc r hr).symm
  refine ⟨hQs, ?_, hQq⟩
  have hle : Q ≤ M ⊓ Subgroup.centralizer ({s} : Set K) := le_inf hQM hQs
  refine CFSG.Open.IsSubnormal.step hle ?_ (isSubnormal_comap_inf ψ _ hH hTX)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro n g hn hg
  exact conj_mem_commutator_of_mem hg.1 hn

end Cover

section Join

variable {K G : Type*} [Group K] [Group G]

theorem commutatorElement_mul_central {q q' z z' : K} (hz : z ∈ Subgroup.center K)
    (hz' : z' ∈ Subgroup.center K) : ⁅q * z, q' * z'⁆ = ⁅q, q'⁆ := by
  have h1 : ∀ g : K, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.mp hz g]
    group
  have h2 : ∀ g : K, z' * g * z'⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.mp hz' g]
    group
  have h3 : ⁅q * z, q' * z'⁆ = ⁅q, q' * z'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc q * z * (q' * z') * (q * z)⁻¹ * (q' * z')⁻¹
        = q * (z * (q' * z') * z⁻¹) * q⁻¹ * (q' * z')⁻¹ := by group
      _ = q * (q' * z') * q⁻¹ * (q' * z')⁻¹ := by rw [h1]
  have h4 : ⁅q, q' * z'⁆ = ⁅q, q'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc q * (q' * z') * q⁻¹ * (q' * z')⁻¹ = q * q' * (z' * q⁻¹ * z'⁻¹) * q'⁻¹ := by group
      _ = q * q' * q⁻¹ * q'⁻¹ := by rw [h2]
  rw [h3, h4]

theorem le_iSup_components_of_map_le {ι : Type*} (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (s : K) {X : Subgroup G} (hXs : ∀ g ∈ X, g * ψ s = ψ s * g)
    (hH : ∀ h ∈ Subgroup.centralizer ({s} : Set K), ψ h ∈ X) (T : ι → Subgroup G)
    (hTr : ∀ i, T i ≤ ψ.range)
    (hT : ∀ i, T i = ⊥ ∨ (CFSG.Open.IsSubnormal (T i) X ∧ CFSG.Open.IsQuasisimple ↥(T i)))
    {R : Subgroup K} (hR : R ≤ ⁅R, R⁆) (hRT : R.map ψ ≤ ⨆ i, T i) :
    R ≤ ⨆ (Q : Subgroup K)
      (_ : CFSG.Open.IsComponentOf Q (Subgroup.centralizer ({s} : Set K))), Q := by
  set N : Subgroup K := ⨆ i, ⁅(T i).comap ψ, (T i).comap ψ⁆ with hN
  have hbot : ⁅ψ.ker, ψ.ker⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hker.trans (Subgroup.center_le_centralizer _))
  have hperf : ∀ i, ⁅T i, T i⁆ = T i := fun i => (hT i).elim
    (fun h => by rw [h]; exact Subgroup.commutator_bot_left _) fun h =>
      commutator_eq_of_isQuasisimple h.2
  have hmap : ∀ i, (⁅(T i).comap ψ, (T i).comap ψ⁆).map ψ = T i := by
    intro i
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.2 (hTr i), hperf i]
  have hNle : N ≤ ⨆ (Q : Subgroup K)
      (_ : CFSG.Open.IsComponentOf Q (Subgroup.centralizer ({s} : Set K))), Q := by
    refine iSup_le fun i => ?_
    rcases hT i with h | ⟨hs, hq⟩
    · have : ⁅(T i).comap ψ, (T i).comap ψ⁆ = ⊥ := by
        rw [h, MonoidHom.comap_bot]
        exact hbot
      rw [this]
      exact bot_le
    · exact le_iSup₂_of_le _ (isComponentOf_commutator_comap ψ hker s hXs hH hs (hTr i) hq)
        le_rfl
  refine le_trans ?_ hNle
  have hψN : N.map ψ = ⨆ i, T i := by
    rw [hN, Subgroup.map_iSup]
    exact iSup_congr hmap
  refine hR.trans (Subgroup.commutator_le.2 fun r hr r' hr' => ?_)
  have hex : ∀ r ∈ R, ∃ q ∈ N, ∃ z ∈ Subgroup.center K, r = q * z := by
    intro r hr
    have h1 : ψ r ∈ N.map ψ := by
      rw [hψN]
      exact hRT (Subgroup.mem_map_of_mem ψ hr)
    obtain ⟨q, hq, hqr⟩ := h1
    refine ⟨q, hq, q⁻¹ * r, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqr, inv_mul_cancel]
  obtain ⟨q, hq, z, hz, rfl⟩ := hex r hr
  obtain ⟨q', hq', z', hz', rfl⟩ := hex r' hr'
  rw [commutatorElement_mul_central hz hz', commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hq hq') (N.inv_mem hq)) (N.inv_mem hq')

end Join

section Conj

variable {K M : Type*} [Group K] [Group M]

theorem exists_cover_of_conj_centralizer (Φ : K →* M) (hker : Φ.ker ≤ Subgroup.center K)
    (G R : Subgroup M) (hRG : R ≤ G) (hΦR : ∀ y, Φ y ∈ R) (hrange : Φ.range = ⁅R, R⁆) (w : M)
    (hw : w ∈ G) (s : K) (X : Subgroup G)
    (hcent : (R ⊓ Subgroup.centralizer {Φ s}).map (MulAut.conj w).toMonoidHom =
      X.map G.subtype) :
    ∃ ψ : K →* G, ψ.ker ≤ Subgroup.center K ∧ (∀ g ∈ X, g * ψ s = ψ s * g) ∧
      (∀ h ∈ Subgroup.centralizer ({s} : Set K), ψ h ∈ X) ∧
      (∀ P : Subgroup G, P ≤ X → ⁅P, P⁆ = P → P ≤ ψ.range) := by
  let Φ' : K →* G := Φ.codRestrict G (fun y => hRG (hΦR y))
  let ψ : K →* G := (MulAut.conj (⟨w, hw⟩ : G)).toMonoidHom.comp Φ'
  have hψ : ∀ y, ((ψ y : G) : M) = w * Φ y * w⁻¹ := fun y => rfl
  have hXmem : ∀ g ∈ X, ∃ y ∈ R ⊓ Subgroup.centralizer {Φ s}, w * y * w⁻¹ = (g : M) := by
    intro g hg
    have hmem : (g : M) ∈ X.map G.subtype := ⟨g, hg, rfl⟩
    rw [← hcent] at hmem
    obtain ⟨y, hy, hyg⟩ := hmem
    exact ⟨y, hy, by simpa using hyg⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro y hy
    refine hker ?_
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 := congrArg (fun g : G => (g : M)) hy
    simp only [hψ] at h1
    have h2 : w * Φ y = w := mul_inv_eq_one.1 h1
    exact mul_eq_left.1 h2
  · intro g hg
    obtain ⟨y, hy, hyg⟩ := hXmem g hg
    have hyx : y * Φ s = Φ s * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    apply Subtype.ext
    show (g : M) * ((ψ s : G) : M) = ((ψ s : G) : M) * (g : M)
    rw [hψ, ← hyg]
    calc w * y * w⁻¹ * (w * Φ s * w⁻¹) = w * (y * Φ s) * w⁻¹ := by group
      _ = w * (Φ s * y) * w⁻¹ := by rw [hyx]
      _ = w * Φ s * w⁻¹ * (w * y * w⁻¹) := by group
  · intro h' hh'
    have hcomm : Φ h' * Φ s = Φ s * Φ h' := by
      calc Φ h' * Φ s = Φ (h' * s) := (map_mul Φ h' s).symm
        _ = Φ (s * h') := by rw [Subgroup.mem_centralizer_singleton_iff.1 hh']
        _ = Φ s * Φ h' := map_mul Φ s h'
    have hmem : w * Φ h' * w⁻¹ ∈
        (R ⊓ Subgroup.centralizer {Φ s}).map (MulAut.conj w).toMonoidHom :=
      ⟨Φ h', ⟨hΦR h', Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩, rfl⟩
    rw [hcent] at hmem
    obtain ⟨g, hg, hgψ⟩ := hmem
    have : g = ψ h' := Subtype.ext (hgψ.trans (hψ h').symm)
    rw [← this]
    exact hg
  · intro P hPX hPperf g hg
    let c : M →* M := (MulAut.conj w⁻¹).toMonoidHom
    set P₁ : Subgroup M := P.map (c.comp G.subtype) with hP₁
    have hP₁R : P₁ ≤ R := by
      rintro _ ⟨g', hg', rfl⟩
      obtain ⟨y', hy', hy'g⟩ := hXmem g' (hPX hg')
      have : (c.comp G.subtype) g' = y' := by
        show w⁻¹ * (g' : M) * w⁻¹⁻¹ = y'
        rw [← hy'g]
        group
      rw [this]
      exact hy'.1
    have hP₁perf : ⁅P₁, P₁⁆ = P₁ := by rw [hP₁, ← Subgroup.map_commutator, hPperf]
    have hP₁range : P₁ ≤ Φ.range := by
      rw [hrange]
      calc P₁ = ⁅P₁, P₁⁆ := hP₁perf.symm
        _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hP₁R hP₁R
    obtain ⟨y₀, hy₀⟩ := hP₁range ⟨g, hg, rfl⟩
    refine ⟨y₀, Subtype.ext ?_⟩
    rw [hψ, hy₀]
    show w * (w⁻¹ * (g : M) * w⁻¹⁻¹) * w⁻¹ = g
    group

end Conj

end CFSG.ClassicalInvolution.Balance.Bootstrap
