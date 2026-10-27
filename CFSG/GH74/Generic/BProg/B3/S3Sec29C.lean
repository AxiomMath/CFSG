module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29K26
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_central_of_isSylowOf {y : G} {R M : Subgroup G} (hR : IsSylowOf 2 R M) (hyM : y ∈ M)
    (hy : orderOf y = 2) (hc : ∀ m ∈ M, m * y = y * m) : y ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hR
  set yM : ↥M := ⟨y, hyM⟩ with hyMdef
  have hyM2 : orderOf yM = 2 := (Subgroup.orderOf_mk y hyM).trans hy
  have hN : (zpowers yM).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : g * yM = yM * g := Subtype.ext (hc (g : G) g.2)
    have h2 : g * yM ^ k * g⁻¹ = yM ^ k := by
      have := (Commute.zpow_right (show Commute g yM from hcomm) k).eq
      rw [this]; group
    rw [h2]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hp : IsPGroup 2 (zpowers yM) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyM2, pow_one])
  have hle := hp.le_sylow_of_normal Q
  exact ⟨yM, hle (Subgroup.mem_zpowers _), rfl⟩

omit [Finite G] in
theorem piC_step {v r : G} {M : Subgroup G} (hrv : r ∈ centralizer ({v} : Set G))
    (hrM : r ∈ normalizer (M : Set G)) :
    ∀ c ∈ S3.imgBar v M, piC v r * c * (piC v r)⁻¹ ∈ S3.imgBar v M := by
  intro c hc
  obtain ⟨g, hgM, rfl⟩ := S3.mem_imgBar.1 hc
  refine S3.mem_imgBar.2 ⟨⟨r, hrv⟩ * g * ⟨r, hrv⟩⁻¹, ?_, ?_⟩
  · show r * (g : G) * r⁻¹ ∈ M
    exact (Subgroup.mem_normalizer_iff.1 hrM g).1 hgM
  · rw [piC_of_mem v hrv, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem piC_mem_normalizer {v r : G} {M : Subgroup G} (hrv : r ∈ centralizer ({v} : Set G))
    (hrM : r ∈ normalizer (M : Set G)) :
    piC v r ∈ normalizer ((S3.imgBar v M : Subgroup (CentralizerBar v)) :
      Set (CentralizerBar v)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => piC_step hrv hrM c hc, fun hc => ?_⟩
  have h := piC_step (inv_mem hrv) (inv_mem hrM) _ hc
  rw [piC_inv v hrv] at h
  simpa [mul_assoc] using h

theorem mem_cSec_of_piC {v r : G} {M : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (hrv : r ∈ centralizer ({v} : Set G))
    (h : ∀ g ∈ M, piC v r * piC v g * (piC v r)⁻¹ = piC v g) : r ∈ cSec M := by
  refine TwoThin.mem_centralizerSection_of_map_eq hM.1 (TwoThin.isPCompIn_two_iff.mp hM).2 hrv ?_
  intro m hm
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.1 hm
  have := h (m : G) hmM
  rw [piC_of_mem v hrv, piC_of_mem v m.2] at this
  rw [map_mul, map_mul, map_inv]
  exact this

theorem piC_of_mem_cSec {v r : G} {M : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (hrv : r ∈ centralizer ({v} : Set G))
    (hr : r ∈ cSec M) : ∀ g ∈ M, piC v r * piC v g * (piC v r)⁻¹ = piC v g := by
  intro g hg
  have hgC : g ∈ centralizer ({v} : Set G) := hM.1 hg
  have h := C3.Layer1.PumpCalc.map_eq_of_mem_cSec hM hrv hr ⟨g, hgC⟩
    (Subgroup.mem_subgroupOf.2 hg)
  rw [piC_of_mem v hrv, piC_of_mem v hgC]
  rw [map_mul, map_mul, map_inv] at h
  exact h


@[expose] def autFixing {Kt : Type} [Group Kt] (S : Subgroup Kt) : Subgroup (MulAut Kt) where
  carrier := {σ | ∀ s ∈ S, σ s = s}
  one_mem' := fun s _ => rfl
  mul_mem' := fun {a b} ha hb s hs => by
    show a (b s) = s
    rw [hb s hs, ha s hs]
  inv_mem' := fun {a} ha s hs => by
    have h := ha s hs
    calc (a⁻¹ : MulAut Kt) s = (a⁻¹ : MulAut Kt) (a s) := by rw [h]
      _ = s := by simp

@[expose] def S16cKG : Prop :=
  ∀ (Kt : Type) [Group Kt] [Finite Kt], QShape3 Kt → (∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) →
    ∀ (u : Kt) (S : Subgroup Kt), orderOf u = 2 → IsPCompIn 2 (centralizer ({u} : Set Kt)) S →
      (∀ a ∈ centralizer ({u} : Set Kt), ∀ b ∈ centralizer ({u} : Set Kt), ⁅a, b⁆ ∈ S) →
        Group.IsSolvable ↥(autFixing S)

omit [Finite G] in
theorem qShape3_of_model {v : G} {M : Subgroup G}
    (hmodel : ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧
      5 ≤ p ^ f ∧ LieModel ↥(S3.imgBar v M) t 3 p f) : QShape3 ↥(S3.imgBar v M) := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := hmodel
  refine ⟨p, f, hp, hp2, by omega, ?_⟩
  rcases ht with rfl | rfl
  · exact Or.inl hmod
  · exact Or.inr hmod

omit [Finite G] in
theorem centerless_of_center_eq_bot {v : G} {M : Subgroup G} (hcen : center ↥(S3.imgBar v M) = ⊥) :
    ∀ z : ↥(S3.imgBar v M), (∀ g : ↥(S3.imgBar v M), g * z = z * g) → z = 1 := by
  intro z hz
  have hmem : z ∈ center ↥(S3.imgBar v M) := Subgroup.mem_center_iff.2 fun g => hz g
  rw [hcen, Subgroup.mem_bot] at hmem
  exact hmem

theorem exists_layerHyp_comm {v : G} {M : Subgroup G} {y : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (hyM : y ∈ M) (hy : orderOf y = 2)
    (hcen : center ↥(S3.imgBar v M) = ⊥)
    (hmodel : ∃ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ p.Prime ∧ p ≠ 2 ∧
      5 ≤ p ^ f ∧ LieModel ↥(S3.imgBar v M) t 3 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup ↥(S3.imgBar v M)),
      S3L3Lift.LayerHyp v hM.1 hyM S F ∧
      (∀ a ∈ centralizer ({S3L3Lift.yK v hM.1 hyM} : Set ↥(S3.imgBar v M)),
        ∀ b ∈ centralizer ({S3L3Lift.yK v hM.1 hyM} : Set ↥(S3.imgBar v M)), ⁅a, b⁆ ∈ S) ∧
      (∀ σ : MulAut ↥(S3.imgBar v M), σ * σ = 1 → (∀ s ∈ S, σ s = s) →
        σ = 1 ∨ σ = MulAut.conj (S3L3Lift.yK v hM.1 hyM)) := by
  have hq3 : QShape3 ↥(S3.imgBar v M) := qShape3_of_model hmodel
  have hZ := centerless_of_center_eq_bot hcen
  obtain ⟨F, hF, hFin, S, hodd, h5', e, huS, -, hcomm, hSc, hB4⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ (S3L3Lift.orderOf_yK v hM.1 hyM hy)
  exact ⟨F, hF, hFin, S, ⟨hodd, by omega, e, huS, hSc, fun M' hM' =>
    S3L3Lift.eq_of_isPCompIn_centralizer hSc hcomm hM'⟩, hcomm, hB4⟩

theorem fixes_S {v : G} {M : Subgroup G} {y : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (hyM : y ∈ M) (hy : orderOf y = 2)
    {F : Type} [Field F] [Finite F] {S : Subgroup ↥(S3.imgBar v M)}
    (hS : S3L3Lift.LayerHyp v hM.1 hyM S F) {t : G} (htv : t ∈ centralizer ({v} : Set G))
    (htL : t ∈ cSec (Ly29 M y)) :
    ∀ s ∈ S, (s : CentralizerBar v) * piC v t = piC v t * (s : CentralizerBar v) := by
  have hMC : M ≤ centralizer ({v} : Set G) := hM.1
  obtain ⟨L, hL, -⟩ := hS.exists_comp hy
  have hLy : pLayerOf 2 (M ⊓ centralizer ({y} : Set G)) = L := hS.pLayerOf_eq hy hL
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hS.psi_data hy hL
  have hLy' : Ly29 M y = L := hLy
  have htL' : t ∈ cSec L := hLy' ▸ htL
  intro s hs
  obtain ⟨⟨l, hl⟩, hls⟩ := hψs ⟨s, hs⟩
  have hs_eq : (s : CentralizerBar v) = piC v l := by rw [← hψc l hl, hls]
  have hlC : l ∈ centralizer ({v} : Set G) := hMC (Subgroup.mem_inf.1 (hL.1 hl)).1
  have hc1 : ⁅l, t⁆ ∈ pPrimeCoreOf 2 L := htL'.2.2 l hl
  have h1 : piC v ⁅l, t⁆ = 1 := by
    obtain ⟨z, hz, hzv⟩ := hc1
    have hzk : z ∈ ψ.ker := hψk ▸ hz
    have h2 := hψc (z : G) z.2
    have h3 : ψ ⟨(z : G), z.2⟩ = 1 := hzk
    rw [h3] at h2
    rw [← hzv]
    exact h2.symm
  rw [S3L3Facts.piC_commutator v hlC htv, ← hs_eq, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

@[expose] def FixesLayer (v : G) (M : Subgroup G) (y : G) (P : Subgroup G) : Prop :=
  ∀ (hM : M ≤ centralizer ({v} : Set G)) (hyM : y ∈ M) {F : Type} [Field F] [Finite F]
    (S : Subgroup ↥(S3.imgBar v M)), S3L3Lift.LayerHyp v hM hyM S F →
      ∀ t ∈ P, ∀ s ∈ S, (s : CentralizerBar v) * piC v t = piC v t * (s : CentralizerBar v)

theorem fixesLayer_of_cSec {v : G} {M : Subgroup G} {y : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (hy : orderOf y = 2) {P : Subgroup G}
    (hPv : P ≤ centralizer ({v} : Set G)) (hPL : P ≤ cSec (Ly29 M y)) : FixesLayer v M y P :=
  fun _ hyM _ _ _ _ hS _ ht s hs => fixes_S hM hyM hy hS (hPv ht) (hPL ht) s hs

theorem mem_normalizer_of_comm {v : G} {M : Subgroup G} {y g : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M)
    (hZ : ∀ z : ↥M ⧸ pPrimeCore 2 ↥M, (∀ k, k * z = z * k) → z = 1) (hyM : y ∈ M)
    (hy : orderOf y = 2) (hgv : g ∈ centralizer ({v} : Set G)) (hgy : g * y = y * g) :
    g ∈ normalizer (M : Set G) := by
  have hX : (centralizer ({v} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({v} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgv)
  have hM' : IsPCompIn 2 (centralizer ({v} : Set G)) (M.map (MulAut.conj g).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hM g
    rwa [hX] at this
  by_contra hne
  have hMne : M.map (MulAut.conj g).toMonoidHom ≠ M := fun he =>
    hne (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have h1 : M.map (MulAut.conj g).toMonoidHom ≤ cSec M :=
    Stage1.Thm2.Recip.le_cSec_of_ne hM' hM hMne
  have hyM' : y ∈ M.map (MulAut.conj g).toMonoidHom := ⟨y, hyM, by
    show g * y * g⁻¹ = y
    rw [hgy]
    group⟩
  have hy2 : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hy1 : y = 1 := S3Ctx29.eq_one_of_mem_cSec hZ (Subgroup.zpowers_le.2 hyM) hy2
    (Subgroup.mem_zpowers y) (h1 hyM')
  rw [hy1, orderOf_one] at hy
  omega

theorem unique_involution {v : G} {M : Subgroup G} {y : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (h3 : QShape3 (↥M ⧸ pPrimeCore 2 ↥M))
    (hyM : y ∈ M) (hy : orderOf y = 2) {P : Subgroup G} (hPv : P ≤ centralizer ({v} : Set G))
    (hPM : P ≤ normalizer (M : Set G)) (hPL : FixesLayer v M y P) :
    ∀ r ∈ P, r * r ∈ cSec M → r ∈ cSec M ∨ r * y⁻¹ ∈ cSec M := by
  intro r hrP hrr
  have hMC : M ≤ centralizer ({v} : Set G) := hM.1
  obtain ⟨hcen, hmodel⟩ := S3Ctx29K26.model_centerless_of_ctx hM h3
  obtain ⟨F, hF, hFin, S, hS, -, hB4⟩ := exists_layerHyp_comm hM hyM hy hcen hmodel
  have hrv : r ∈ centralizer ({v} : Set G) := hPv hrP
  have hyC : y ∈ centralizer ({v} : Set G) := hMC hyM
  have hfix : ∀ s ∈ S, (s : CentralizerBar v) * piC v r = piC v r * (s : CentralizerBar v) :=
    fun s hs => hPL hM.1 hyM S hS r hrP s hs
  let σ : MulAut ↥(S3.imgBar v M) := TwoThin.conjAut (piC_mem_normalizer hrv (hPM hrP))
  have hσ : ∀ c : ↥(S3.imgBar v M), ((σ c : ↥(S3.imgBar v M)) : CentralizerBar v) =
      piC v r * (c : CentralizerBar v) * (piC v r)⁻¹ := fun c => rfl
  have hσσ : σ * σ = 1 := by
    ext c
    obtain ⟨g, hgM, hgc⟩ := S3.mem_imgBar.1 c.2
    have hrrC : r * r ∈ centralizer ({v} : Set G) := mul_mem hrv hrv
    have h1 := piC_of_mem_cSec hM hrrC hrr (g : G) hgM
    rw [piC_mul v hrv hrv, piC_of_mem v g.2] at h1
    have h1' : (piC v r * piC v r) * (c : CentralizerBar v) * (piC v r * piC v r)⁻¹ = c := by
      rw [← hgc]; exact h1
    show piC v r * (piC v r * (c : CentralizerBar v) * (piC v r)⁻¹) * (piC v r)⁻¹ = c
    calc piC v r * (piC v r * (c : CentralizerBar v) * (piC v r)⁻¹) * (piC v r)⁻¹
        = (piC v r * piC v r) * (c : CentralizerBar v) * (piC v r * piC v r)⁻¹ := by group
      _ = c := h1'
  have hσS : ∀ s ∈ S, σ s = s := by
    intro s hs
    apply Subtype.ext
    rw [hσ, mul_inv_eq_iff_eq_mul]
    exact (hfix s hs).symm
  have hmemKB : ∀ g ∈ M, piC v g ∈ S3.imgBar v M := fun g hg =>
    S3.mem_imgBar.2 ⟨⟨g, hMC hg⟩, hg, (piC_of_mem v (hMC hg)).symm⟩
  rcases hB4 σ hσσ hσS with h1 | h2
  · left
    refine mem_cSec_of_piC hM hrv fun g hg => ?_
    have := congrArg (fun τ : MulAut ↥(S3.imgBar v M) => ((τ ⟨piC v g, hmemKB g hg⟩ :
      ↥(S3.imgBar v M)) : CentralizerBar v)) h1
    exact this
  · right
    have hyC' : y⁻¹ ∈ centralizer ({v} : Set G) := inv_mem hyC
    refine mem_cSec_of_piC hM (mul_mem hrv hyC') fun g hg => ?_
    have hg'M : y⁻¹ * g * y ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hyM) hg) hyM
    have h2' := congrArg (fun τ : MulAut ↥(S3.imgBar v M) => ((τ ⟨piC v (y⁻¹ * g * y), hmemKB _ hg'M⟩ :
      ↥(S3.imgBar v M)) : CentralizerBar v)) h2
    have hRR : (((MulAut.conj (S3L3Lift.yK v hMC hyM) : MulAut ↥(S3.imgBar v M))
        ⟨piC v (y⁻¹ * g * y), hmemKB _ hg'M⟩ : ↥(S3.imgBar v M)) : CentralizerBar v) =
        piC v y * piC v (y⁻¹ * g * y) * (piC v y)⁻¹ := rfl
    have h2'' : piC v r * piC v (y⁻¹ * g * y) * (piC v r)⁻¹ =
        piC v y * piC v (y⁻¹ * g * y) * (piC v y)⁻¹ :=
      (hσ ⟨piC v (y⁻¹ * g * y), hmemKB _ hg'M⟩).symm.trans (h2'.trans hRR)
    have e1 : piC v (y⁻¹ * g * y) = (piC v y)⁻¹ * piC v g * piC v y := by
      rw [piC_mul v (mul_mem hyC' (hMC hg)) hyC, piC_mul v hyC' (hMC hg), piC_inv v hyC]
    have e2 : piC v (r * y⁻¹) = piC v r * (piC v y)⁻¹ := by
      rw [piC_mul v hrv hyC', piC_inv v hyC]
    rw [e2]
    rw [e1] at h2''
    calc piC v r * (piC v y)⁻¹ * piC v g * (piC v r * (piC v y)⁻¹)⁻¹
        = piC v r * ((piC v y)⁻¹ * piC v g * piC v y) * (piC v r)⁻¹ := by group
      _ = piC v y * ((piC v y)⁻¹ * piC v g * piC v y) * (piC v y)⁻¹ := h2''
      _ = piC v g := by group


@[expose] noncomputable def actHom {v : G} {M P : Subgroup G} (hPv : P ≤ centralizer ({v} : Set G))
    (hPM : P ≤ normalizer (M : Set G)) : ↥P →* MulAut ↥(S3.imgBar v M) where
  toFun r := TwoThin.conjAut (piC_mem_normalizer (hPv r.2) (hPM r.2))
  map_one' := MulEquiv.ext fun c => Subtype.ext (by
    show piC v ((1 : ↥P) : G) * (c : CentralizerBar v) * (piC v ((1 : ↥P) : G))⁻¹ = c
    simp [piC_one])
  map_mul' r1 r2 := MulEquiv.ext fun c => Subtype.ext (by
    show piC v ((r1 * r2 : ↥P) : G) * (c : CentralizerBar v) * (piC v ((r1 * r2 : ↥P) : G))⁻¹ =
      piC v (r1 : G) * (piC v (r2 : G) * (c : CentralizerBar v) * (piC v (r2 : G))⁻¹) *
        (piC v (r1 : G))⁻¹
    rw [Subgroup.coe_mul, piC_mul v (hPv r1.2) (hPv r2.2)]
    group)

omit [Finite G] in
theorem actHom_apply {v : G} {M P : Subgroup G} (hPv : P ≤ centralizer ({v} : Set G))
    (hPM : P ≤ normalizer (M : Set G)) (r : ↥P) (c : ↥(S3.imgBar v M)) :
    (((actHom hPv hPM r) c : ↥(S3.imgBar v M)) : CentralizerBar v) =
      piC v (r : G) * (c : CentralizerBar v) * (piC v (r : G))⁻¹ := rfl

theorem perfectCore_le_cSec (hKG : S16cKG) {v : G} {M : Subgroup G} {y : G}
    (hM : IsPCompIn 2 (centralizer ({v} : Set G)) M) (h3 : QShape3 (↥M ⧸ pPrimeCore 2 ↥M))
    (hyM : y ∈ M) (hy : orderOf y = 2) {P : Subgroup G} (hPv : P ≤ centralizer ({v} : Set G))
    (hPM : P ≤ normalizer (M : Set G)) (hPL : FixesLayer v M y P) :
    perfectCoreOf P ≤ cSec M := by
  have hMC : M ≤ centralizer ({v} : Set G) := hM.1
  obtain ⟨hcen, hmodel⟩ := S3Ctx29K26.model_centerless_of_ctx hM h3
  obtain ⟨F, hF, hFin, S, hS, hcomm, hB4⟩ := exists_layerHyp_comm hM hyM hy hcen hmodel
  have hsolv : Group.IsSolvable ↥(autFixing S) :=
    hKG ↥(S3.imgBar v M) (qShape3_of_model hmodel) (centerless_of_center_eq_bot hcen)
      (S3L3Lift.yK v hM.1 hyM) S (S3L3Lift.orderOf_yK v hM.1 hyM hy) hS.comp hcomm
  have hfixP : ∀ r : ↥P, actHom hPv hPM r ∈ autFixing S := by
    intro r s hs
    apply Subtype.ext
    rw [actHom_apply, mul_inv_eq_iff_eq_mul]
    exact (hPL hM.1 hyM S hS r r.2 s hs).symm
  let ρ : ↥P →* ↥(autFixing S) := (actHom hPv hPM).codRestrict (autFixing S) hfixP
  obtain ⟨n, hn⟩ := hsolv
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ derivedSeries ↥P n := (Subgroup.mem_iInf.1 hx) n
  have h1 : ρ x ∈ derivedSeries ↥(autFixing S) n := by
    have := Subgroup.mem_map_of_mem ρ hx'
    exact map_derivedSeries_le_derivedSeries ρ n this
  rw [hn, Subgroup.mem_bot] at h1
  have h2 : actHom hPv hPM x = 1 := congrArg Subtype.val h1
  refine mem_cSec_of_piC hM (hPv x.2) fun g hg => ?_
  have hg' : piC v g ∈ S3.imgBar v M :=
    S3.mem_imgBar.2 ⟨⟨g, hMC hg⟩, hg, (piC_of_mem v (hMC hg)).symm⟩
  have := congrArg (fun τ : MulAut ↥(S3.imgBar v M) => ((τ ⟨piC v g, hg'⟩ : ↥(S3.imgBar v M)) :
    CentralizerBar v)) h2
  exact this

end S3Sec29C

end CFSG.GH74.Generic.BProg.B3
