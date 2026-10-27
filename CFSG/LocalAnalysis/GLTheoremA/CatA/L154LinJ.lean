module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinPsl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Fld
public import CFSG.GH74.L5U5.Models
public import CFSG.Models.PGLSimple
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open scoped commutatorElement MatrixGroups

theorem twist_mem_statedSL {d : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (B : GL (Fin d) K)
    {g : GL (Fin d) K} (hg : g ∈ StatedSL d K) : B * glMap σ g * B⁻¹ ∈ StatedSL d K := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det] at hg ⊢
  exact slTwist_mem σ B hg

theorem lin_J_equiv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {d : ℕ} {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) (hd : 2 ≤ d)
    (θ : PSimple p S ≃* LargeEvenProj (StatedSL d K)) (A B : GL (Fin d) K) (σ : K ≃+* K)
    (φx ψ : MulAut (LargeEvenProj (StatedSL d K)))
    (hA : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φx (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hψ : ∀ g g' : ↥(StatedSL d K), (g' : GL (Fin d) K) = B * glMap σ (g : GL (Fin d) K) * B⁻¹ →
      ψ (LargeEvenProjMk (StatedSL d K) g) = LargeEvenProjMk (StatedSL d K) g')
    (hindx : LargeEvenInduces θ (indRel p S x) φx) (hindy : LargeEvenInduces θ (indRel p S y) ψ) :
    ∃ (d₁ : ℕ) (D₁ : Type) (_ : Field D₁) (_ : Finite D₁) (ι : GL (Fin d₁) D₁ →* GL (Fin d) K)
      (E : Matrix (Fin d) (Fin d) K) (e₀ : PSimple p J ≃* LargeEvenProj (StatedSL d₁ D₁)),
      (2 : D₁) = 0 ∧ 2 ≤ d₁ ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 2) ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 3) ∧
      Function.Injective ι ∧ E ≠ 0 ∧
      (∀ c : K, ∃ t ∈ StatedSL d₁ D₁, ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • E) ∧
      ∀ m : ↥(StatedSL d₁ D₁), ∃ (m' : ↥(StatedSL d₁ D₁)) (z : Kˣ),
        MulAut.congr e₀ (MI.indAut p J y hJy) (LargeEvenProjMk (StatedSL d₁ D₁) m) =
          LargeEvenProjMk (StatedSL d₁ D₁) m' ∧
        (ι (m' : GL (Fin d₁) D₁) : GL (Fin d) K) =
          Matrix.GeneralLinearGroup.scalar (Fin d) z * (B * glMap σ (ι (m : GL (Fin d₁) D₁)) * B⁻¹) := by
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hφx : φx = MulAut.congr θ (MI.indAut p S x hxN) := (MI.induces_indRel_iff hxN θ).1 hindx
  have hpow : φx ^ p = 1 := by rw [hφx, ← map_pow, l154_indAut_pow_eq_one hxN hxp, map_one]
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (S ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [l154_centralizer_inv_singleton]
    exact hJ
  have hT := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  set JP : Subgroup (LargeEvenProj (StatedSL d K)) := (chevTransfer p S J).map θ.toMonoidHom with hJPdef
  have hcompat : ∀ k : PSimple p S, θ (MI.indAut p S x hxN k) = φx (θ k) := by
    intro k
    rw [hφx]
    simp [MulAut.congr_apply]
  have hJP : GLAPComponent p (fixSubgroup φx) JP :=
    glaPComponent_map_fixSubgroup θ.toMonoidHom
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 θ.injective]; exact bot_le) (MI.indAut p S x hxN) φx hcompat
      θ.surjective hp hT
  obtain ⟨d₁, D₁, instD, finD, ι, ιSL, h2', hd₁, h22, h23, hιinj, hιSL, hJPeq, E, hE, hTv⟩ :=
    exists_linPsl h2 (by omega) A hp hp2 φx hA hpow JP hJP
  let ρS : ↥S →* LargeEvenProj (StatedSL d K) := θ.toMonoidHom.comp (chevQuotHom p S)
  let ρJ : ↥J →* LargeEvenProj (StatedSL d K) := ρS.comp (Subgroup.inclusion hJS)
  let Ψ : ↥(StatedSL d₁ D₁) →* LargeEvenProj (StatedSL d K) :=
    (LargeEvenProjMk (StatedSL d K)).comp ιSL
  let q₁ : ↥(StatedSL d₁ D₁) →* LargeEvenProj (StatedSL d₁ D₁) := LargeEvenProjMk (StatedSL d₁ D₁)
  have hιSLinj : Function.Injective ιSL := fun a b hab =>
    Subtype.ext (hιinj (by rw [← hιSL, ← hιSL, hab]))
  have hperfJ : commutator ↥J = ⊤ := by
    have h1 := Subgroup.map_subtype_commutator J
    rw [glaPComponent_perfect hJ] at h1
    have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)
  have hρJmem : ∀ l : ↥J, ρJ l ∈ JP := by
    intro l
    rw [hJPdef]
    refine Subgroup.mem_map.2 ⟨chevQuotHom p S ⟨l.1, hJS l.2⟩, ?_, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hmemJP : ∀ z ∈ JP, ∃ l : ↥J, ρJ l = z := by
    intro z hz
    rw [hJPdef] at hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hc
    exact ⟨⟨s.1, Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩
  have hρΨ : ∀ l : ↥J, ∃ m, Ψ m = ρJ l := by
    intro l
    have h1 : ρJ l ∈ ιSL.range.map (LargeEvenProjMk (StatedSL d K)) := hJPeq ▸ hρJmem l
    obtain ⟨g, ⟨m, rfl⟩, hg⟩ := Subgroup.mem_map.1 h1
    exact ⟨m, hg⟩
  have hΨρ : ∀ m, ∃ l : ↥J, ρJ l = Ψ m := by
    intro m
    have h1 : Ψ m ∈ JP := by
      rw [hJPeq]
      exact Subgroup.mem_map.2 ⟨ιSL m, ⟨m, rfl⟩, rfl⟩
    exact hmemJP _ h1
  have hcen₁ : ∀ m : ↥(StatedSL d₁ D₁), q₁ m = 1 → m ∈ Subgroup.center ↥(StatedSL d₁ D₁) := by
    intro m hm
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := D₁) d₁]
    exact (QuotientGroup.eq_one_iff m).1 hm
  have hcen₁' : ∀ m : ↥(StatedSL d₁ D₁), m ∈ Subgroup.center ↥(StatedSL d₁ D₁) → q₁ m = 1 := by
    intro m hm
    rw [CFSG.GH74.L5U5.center_statedSL_eq (F := D₁) d₁] at hm
    exact (QuotientGroup.eq_one_iff m).2 hm
  have hker₁ : ∀ m, Ψ m = 1 → q₁ m = 1 := by
    intro m hm
    apply hcen₁'
    have hc : ιSL m ∈ Subgroup.center ↥(StatedSL d K) := ker_projMk_le_center hm
    refine Subgroup.mem_center_iff.2 fun m' => ?_
    apply hιSLinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (ιSL m')
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift ρJ Ψ q₁ hρΨ hker₁
  have hΘsurj : Function.Surjective Θ := by
    intro r
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨l, hl⟩ := hΨρ m
    exact ⟨l, hΘ l m hl.symm⟩
  have hρJker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : chevQuotHom p S ⟨l.1, hJS l.2⟩ = 1 := by
      have : θ (chevQuotHom p S ⟨l.1, hJS l.2⟩) = 1 := hl
      exact (map_eq_one_iff _ θ.injective).1 this
    have h2 : (QuotientGroup.mk (⟨l.1, hJS l.2⟩ : ↥S) : PQuot p S) ∈ Subgroup.center (PQuot p S) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 : ∀ s : ↥S, s * ⟨l.1, hJS l.2⟩ = ⟨l.1, hJS l.2⟩ * s := by
      intro s
      have h4 := Subgroup.mem_center_iff.1 h2 (QuotientGroup.mk s)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hSp, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4 |>.symm ▸ rfl
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h5 := h3 ⟨j.1, hJS j.2⟩
    show (j : Ω) * (l : Ω) = (l : Ω) * (j : Ω)
    exact congrArg Subtype.val h5
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨m, hm⟩ := hρΨ l
    have hqm : q₁ m = 1 := by rw [← hΘ l m hm]; exact hl
    have hmc := hcen₁ m hqm
    refine mem_center_of_commutator_mem_center hperfJ fun j => ?_
    apply hρJker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    obtain ⟨m', hm'⟩ := hρΨ j
    rw [← hm, ← hm', ← map_commutatorElement]
    have : ⁅m, m'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hmc m').symm
    rw [this, map_one]
  have hR₁ : IsSimpleGroup (LargeEvenProj (StatedSL d₁ D₁)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL D₁ hd₁ h22 h23
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hR₁ Θ hΘsurj hΘker
  refine ⟨d₁, D₁, instD, finD, ι, E, e₀, h2', hd₁, h22, h23, hιinj, hE, hTv, fun m => ?_⟩
  obtain ⟨l, hl⟩ := hΨρ m
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hJy
  have hl'mem : y⁻¹ * (l : Ω) * y ∈ J := by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, hl'mem⟩
  have hρl' : ρJ l' = ψ (ρJ l) :=
    (hindy (QuotientGroup.mk ⟨l.1, hJS l.2⟩) (QuotientGroup.mk ⟨l'.1, hJS l'.2⟩)
      ⟨⟨l.1, hJS l.2⟩, ⟨l'.1, hJS l'.2⟩, rfl, rfl, rfl⟩).symm
  have hgmem : B * glMap σ (ιSL m : GL (Fin d) K) * B⁻¹ ∈ StatedSL d K :=
    twist_mem_statedSL σ B (ιSL m).2
  have hψm : ψ (Ψ m) = LargeEvenProjMk (StatedSL d K) ⟨_, hgmem⟩ := hψ (ιSL m) ⟨_, hgmem⟩ rfl
  obtain ⟨m', hm'⟩ := hρΨ l'
  have hπeq : LargeEvenProjMk (StatedSL d K) (ιSL m') = LargeEvenProjMk (StatedSL d K) ⟨_, hgmem⟩ := by
    show Ψ m' = _
    rw [hm', hρl', hl, hψm]
  obtain ⟨c, hc⟩ := (projMk_eq_iff (ιSL m') ⟨_, hgmem⟩).1 hπeq
  have hc2 : Matrix.GeneralLinearGroup.scalar (Fin d) c =
      (ι (m' : GL (Fin d₁) D₁))⁻¹ * (B * glMap σ (ι (m : GL (Fin d₁) D₁)) * B⁻¹) := by
    have h3 : (ιSL m' : GL (Fin d) K) = ι (m' : GL (Fin d₁) D₁) := hιSL m'
    have h4 : (ιSL m : GL (Fin d) K) = ι (m : GL (Fin d₁) D₁) := hιSL m
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c =
        ((ιSL m' : ↥(StatedSL d K)) : GL (Fin d) K)⁻¹ *
          (B * glMap σ ((ιSL m : ↥(StatedSL d K)) : GL (Fin d) K) * B⁻¹) := hc
    rw [hc', h3, h4]
  refine ⟨m', c⁻¹, ?_, ?_⟩
  · have e1 : q₁ m = e₀ (QuotientGroup.mk (QuotientGroup.mk l)) := by
      rw [he₀ l]
      exact (hΘ l m hl.symm).symm
    have e2 : q₁ m' = e₀ (QuotientGroup.mk (QuotientGroup.mk l')) := by
      rw [he₀ l']
      exact (hΘ l' m' hm').symm
    have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk l') :=
      MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, rfl⟩
    show MulAut.congr e₀ (MI.indAut p J y hJy) (q₁ m) = q₁ m'
    rw [e1, e2, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, e3]
  · have h1 : ι (m' : GL (Fin d₁) D₁) * Matrix.GeneralLinearGroup.scalar (Fin d) c =
        B * glMap σ (ι (m : GL (Fin d₁) D₁)) * B⁻¹ := by
      rw [hc2]
      group
    rw [← h1, ← mul_assoc, scalar_mul_comm c⁻¹ (ι (m' : GL (Fin d₁) D₁)), mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, mul_one]

end CFSG.LocalAnalysis.GLTheoremA.K155X
