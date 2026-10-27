module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1918b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1918c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

@[expose] def TwoCentral (F : Type*) [Group F] : Prop :=
  ∀ S : Subgroup F, S.Normal → IsPGroup 2 S → S ≤ Subgroup.center F

theorem twoCentral_of_isQuasisimple {F : Type*} [Group F] [Finite F] (hF : CFSG.IsQuasisimple F) :
    TwoCentral F := by
  intro S hS h2
  obtain ⟨-, hsimple, a, b, hab⟩ := hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : F →* F ⧸ Subgroup.center F := QuotientGroup.mk' (Subgroup.center F)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : (S.map π).Normal := hS.map π hπs
  rcases hsimple.eq_bot_or_eq_top_of_normal (S.map π) with hbot | htop
  · intro s hs
    have h1 : π s ∈ S.map π := Subgroup.mem_map_of_mem π hs
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff s).mp h1
  · exfalso
    have hP : IsPGroup 2 (F ⧸ Subgroup.center F) := by
      intro g
      have hg : g ∈ S.map π := htop ▸ Subgroup.mem_top g
      obtain ⟨s, hs, rfl⟩ := hg
      obtain ⟨k, hk⟩ := h2 ⟨s, hs⟩
      exact ⟨k, by rw [← map_pow]; exact (congrArg (fun u : S => π u) hk).trans (map_one π)⟩
    haveI := hsimple.toNontrivial
    have hZ := hP.center_nontrivial
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (F ⧸ Subgroup.center F))
      with h0 | h1
    · rw [h0] at hZ
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
    · apply hab
      have hb : b ∈ Subgroup.center (F ⧸ Subgroup.center F) := h1 ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)

theorem commute_of_twoCentral {F R : Subgroup G} (hperf : Group.IsPerfect ↥F) (hF : TwoCentral ↥F)
    (hR : IsPGroup 2 ↥R) (hFR : ∀ f ∈ F, ∀ r ∈ R, f * r * f⁻¹ ∈ R)
    (hRF : ∀ r ∈ R, ∀ f ∈ F, r * f * r⁻¹ ∈ F) : ∀ r ∈ R, ∀ f ∈ F, r * f = f * r := by
  set S : Subgroup ↥F := R.subgroupOf F with hSdef
  have hSn : S.Normal := ⟨fun s hs g => by
    rw [hSdef, Subgroup.mem_subgroupOf] at hs ⊢
    exact hFR g g.2 s hs⟩
  have hS2 : IsPGroup 2 ↥S := hR.comap_of_injective F.subtype F.subtype_injective
  have hSZ := hF S hSn hS2
  intro r hr
  have hmemF : ∀ f ∈ F, ⁅r, f⁆ ∈ F := fun f hf => by
    rw [commutatorElement_def]
    exact mul_mem (hRF r hr f hf) (inv_mem hf)
  have hmemR : ∀ f ∈ F, ⁅r, f⁆ ∈ R := fun f hf => by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hr ?_
    have := hFR f hf r⁻¹ (inv_mem hr)
    rwa [← mul_assoc]
  have hcen : ∀ f (hf : f ∈ F), (⟨⁅r, f⁆, hmemF f hf⟩ : ↥F) ∈ Subgroup.center ↥F := fun f hf =>
    hSZ (show (⟨⁅r, f⁆, hmemF f hf⟩ : ↥F) ∈ S by
      rw [hSdef, Subgroup.mem_subgroupOf]
      exact hmemR f hf)
  let φ : ↥F →* ↥(Subgroup.center ↥F) :=
    { toFun := fun f => ⟨⟨⁅r, (f : G)⁆, hmemF f f.2⟩, hcen f f.2⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.mp (hcen b b.2) a
        have hb' : (a : G) * ⁅r, (b : G)⁆ = ⁅r, (b : G)⁆ * a := by
          have := congrArg Subtype.val hb
          simpa using this
        change ⁅r, (a : G) * (b : G)⁆ = ⁅r, (a : G)⁆ * ⁅r, (b : G)⁆
        have h1 : ⁅r, (a : G) * (b : G)⁆ = ⁅r, (a : G)⁆ * ((a : G) * ⁅r, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h1, hb', mul_inv_cancel_right] }
  have hφ := CFSG.RankThree.PartOne.KCUnitary.eq_one_of_perfect_of_comm hperf
    (fun u v : ↥(Subgroup.center ↥F) => Subtype.ext (Subgroup.mem_center_iff.mp v.2 u)) φ
  intro f hf
  have h1 := congrArg (fun u : ↥(Subgroup.center ↥F) => ((u : ↥F) : G)) (hφ ⟨f, hf⟩)
  have h2 : ⁅r, f⁆ = 1 := by simpa [φ] using h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem twoCentral_of_iSup {F : Subgroup G} {ι : Sort*} (L : ι → Subgroup G)
    (hLF : ∀ i, L i ≤ F) (hLn : ∀ i, ((L i).subgroupOf F).Normal)
    (hLq : ∀ i, CFSG.IsQuasisimple ↥(L i)) (hfin : ∀ i, Finite ↥(L i)) (hsup : (⨆ i, L i) = F) :
    TwoCentral ↥F := by
  intro S hS h2
  set S' : Subgroup G := S.map F.subtype with hS'
  have hS'2 : IsPGroup 2 ↥S' := h2.map F.subtype
  have hcomm : ∀ s ∈ S', ∀ i, ∀ l ∈ L i, s * l = l * s := by
    intro s hs i
    haveI := hfin i
    refine commute_of_twoCentral (hLq i).1 (twoCentral_of_isQuasisimple (hLq i)) hS'2
      (fun l hl s' hs' => ?_) (fun s' hs' l hl => ?_) s hs
    · obtain ⟨t, ht, rfl⟩ := hs'
      have := hS.conj_mem t ht ⟨l, hLF i hl⟩
      exact ⟨_, this, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := hs'
      have h1 := (hLn i).conj_mem ⟨l, hLF i hl⟩ (Subgroup.mem_subgroupOf.mpr hl) t
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1
  intro s hs
  rw [Subgroup.mem_center_iff]
  intro g
  have hsS' : (s : G) ∈ S' := ⟨s, hs, rfl⟩
  have hle : (⨆ i, L i) ≤ Subgroup.centralizer {(s : G)} := by
    refine iSup_le fun i l hl => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm s hsS' i l hl).symm
  have hg : (g : G) ∈ ⨆ i, L i := by rw [hsup]; exact g.2
  have hgs := Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  exact Subtype.ext hgs

theorem exists_component {ι : Type*} [Finite ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ a b : G, a ∈ H i → b ∈ H j → Commute a b)
    (hind : iSupIndep H) {y : G} (hy : y ∈ ⨆ i, H i) (i₀ : ι) :
    ∃ w ∈ H i₀, ∃ z ∈ ⨆ (i : ι) (_ : i ≠ i₀), H i, y = w * z ∧
      ∀ m : ℕ, y ^ m = 1 → w ^ m = 1 := by
  have := Fintype.ofFinite ι
  set Φ := Subgroup.noncommPiCoprod hcomm with hΦ
  have hinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : Φ.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  obtain ⟨c, rfl⟩ : y ∈ Φ.range := hrange ▸ hy
  refine ⟨c i₀, (c i₀).2, Φ (Function.update c i₀ 1), ?_, ?_, ?_⟩
  · rw [hΦ, Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [Function.update_of_ne hi]
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi (c i).2)
  · have hc : c = Pi.mulSingle i₀ (c i₀) * Function.update c i₀ 1 := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Pi.mulSingle_apply, hi, Function.update_of_ne hi]
    conv_lhs => rw [hc]
    rw [map_mul, hΦ, Subgroup.noncommPiCoprod_mulSingle]
  · intro m hm
    have h1 : Φ (c ^ m) = Φ 1 := by rw [map_pow, hm, map_one]
    have h2 := hinj h1
    have := congrArg (fun u : (i : ι) → H i => ((u i₀ : H i₀) : G)) h2
    simpa using this

theorem pCoreOf_map_of_injective {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    (p : ℕ) (C : Subgroup G) : pCoreOf p (C.map f) = (pCoreOf p C).map f := by
  let e : ↥C ≃* ↥(C.map f) := C.equivMapOfInjective f hf
  have hcomp : (C.map f).subtype.comp e.toMonoidHom = f.comp C.subtype := by
    ext x
    rfl
  simp only [pCoreOf]
  rw [← CFSG.pCore_map_iso p e, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem conj_mem_pCoreOf {p : ℕ} {C : Subgroup G} {c t : G} (hc : c ∈ C) (ht : t ∈ pCoreOf p C) :
    c * t * c⁻¹ ∈ pCoreOf p C := by
  obtain ⟨t', ht', rfl⟩ := ht
  have := (CFSG.pCore_normal (p := p) (G := ↥C)).conj_mem t' ht' ⟨c, hc⟩
  exact ⟨_, this, rfl⟩

theorem isPGroup_pCoreOf (p : ℕ) (C : Subgroup G) : IsPGroup p ↥(pCoreOf p C) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥C)).map C.subtype

theorem pCoreOf_le (p : ℕ) (C : Subgroup G) : pCoreOf p C ≤ C := by
  rintro _ ⟨t, -, rfl⟩
  exact t.2

theorem le_pCoreOf {p : ℕ} {C P : Subgroup G} (hPC : P ≤ C)
    (hPn : ∀ c ∈ C, ∀ t ∈ P, c * t * c⁻¹ ∈ P) (hP : IsPGroup p ↥P) : P ≤ pCoreOf p C := by
  intro t ht
  have hN : (P.subgroupOf C).Normal := ⟨fun s hs g => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hPn g g.2 s hs⟩
  have hp : IsPGroup p ↥(P.subgroupOf C) := hP.comap_of_injective C.subtype C.subtype_injective
  have hle : P.subgroupOf C ≤ CFSG.pCore p ↥C := le_sSup ⟨hN, hp⟩
  exact ⟨⟨t, hPC ht⟩, hle (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

@[expose] def GroupStepAt (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ a b : T, orderOf a = p → b ^ p = 1 → a * b = b * a →
    ∀ t ∈ pCoreOf 2 (Subgroup.centralizer ({a} : Set T)), b * t = t * b

theorem innerStepAt_of_groupStepAt {T : Type} [Group T] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) (h : GroupStepAt p T) :
    Inputs1918.InnerStepAt p T := by
  intro x y hx hy hxo hyp hxy t ht
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hao : orderOf a = p := by rw [← hxo]; exact (orderOf_injective _ hinj a).symm
  have hbp : b ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
  have hab : a * b = b * a := hinj (by rw [map_mul, map_mul, hxy])
  have hC : innerAut T ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) =
      (Subgroup.centralizer ({a} : Set T)).map (MulAut.conj : T →* MulAut T) := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨⟨g, rfl⟩, hg⟩ := Subgroup.mem_inf.mp hφ
      refine ⟨g, ?_, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hg'])
    · rintro ⟨g, hg, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
      refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg']
  rw [hC, pCoreOf_map_of_injective hinj] at ht
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have := h a b hao hbp hab t₀ ht₀
  rw [← map_mul, ← map_mul, this]

theorem commute_of_lift {H T : Type*} [Group H] [Group T] (ρ : H →* T)
    (hker : ∀ u ∈ ρ.ker, u ^ 2 = 1) {p : ℕ} (hp2 : Odd p) {x : H}
    (hcent : Subgroup.centralizer ({ρ x} : Set T) =
      (Subgroup.centralizer ({x} : Set H)).map ρ)
    (hcore : ∀ P : Subgroup H, P ≤ Subgroup.centralizer {x} →
      (∀ g ∈ Subgroup.centralizer ({x} : Set H), ∀ n ∈ P, g * n * g⁻¹ ∈ P) → IsPGroup 2 ↥P →
        ∀ y ∈ Subgroup.centralizer ({x} : Set H), y ^ p = 1 → ∀ n ∈ P, y * n = n * y)
    {b : T} (hb : b * ρ x = ρ x * b) (hbp : b ^ p = 1) :
    ∀ t ∈ pCoreOf 2 (Subgroup.centralizer ({ρ x} : Set T)), b * t = t * b := by
  intro t ht
  set C := Subgroup.centralizer ({ρ x} : Set T) with hC
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hb
  rw [hcent] at hbC
  obtain ⟨y₀, hy₀, rfl⟩ := hbC
  set y := y₀ ^ (p + 1) with hydef
  have hyC : y ∈ Subgroup.centralizer ({x} : Set H) := pow_mem hy₀ _
  have hρy : ρ y = ρ y₀ := by rw [hydef, map_pow, pow_succ, hbp, one_mul]
  have hyp : y ^ p = 1 := by
    have h1 : y₀ ^ p ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, hbp]
    have h2 := hker _ h1
    obtain ⟨k, hk⟩ := hp2.add_one
    rw [hydef, ← pow_mul, show (p + 1) * p = p * 2 * k by rw [hk]; ring, pow_mul, pow_mul, h2,
      one_pow]
  set P : Subgroup H := (pCoreOf 2 C).comap ρ ⊓ Subgroup.centralizer ({x} : Set H) with hP
  have hPC : P ≤ Subgroup.centralizer {x} := inf_le_right
  have hPn : ∀ g ∈ Subgroup.centralizer ({x} : Set H), ∀ n ∈ P, g * n * g⁻¹ ∈ P := by
    intro g hg n hn
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hg (Subgroup.mem_inf.mp hn).2) (inv_mem hg)⟩
    show ρ (g * n * g⁻¹) ∈ pCoreOf 2 C
    rw [map_mul, map_mul, map_inv]
    have hgC : ρ g ∈ C := by rw [hcent]; exact Subgroup.mem_map_of_mem ρ hg
    exact conj_mem_pCoreOf hgC (Subgroup.mem_inf.mp hn).1
  have hP2 : IsPGroup 2 ↥P := by
    have hk : IsPGroup 2 ↥ρ.ker := fun u => ⟨1, Subtype.ext (by simpa using hker u u.2)⟩
    exact ((isPGroup_pCoreOf 2 C).comap_of_ker_isPGroup ρ hk).to_le inf_le_left
  have htC : t ∈ C := pCoreOf_le 2 C ht
  rw [hcent] at htC
  obtain ⟨t₁, ht₁, rfl⟩ := htC
  have ht₁P : t₁ ∈ P := Subgroup.mem_inf.mpr ⟨ht, ht₁⟩
  have := hcore P hPC hPn hP2 y hyC hyp t₁ ht₁P
  rw [← hρy, ← map_mul, ← map_mul, this]

end General

section Symplectic

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_smul_of_commute {x g : StatedSp r K} (hg : Commute (spEnd g) (spEnd x)) {a : K[X]}
    (c : AdjoinRoot a) (v : primaryComponent (spEnd x) a) :
    spEnd g ((c • v : primaryComponent (spEnd x) a) : Fin r ⊕ Fin r → K) =
      ((c • (⟨spEnd g v, apply_mem_primaryComponent hg v.2⟩ :
        primaryComponent (spEnd x) a) : primaryComponent (spEnd x) a) : Fin r ⊕ Fin r → K) := by
  set ρ := commutantRestrict a (⟨spEnd g, (mem_commutant _).mpr hg⟩ : commutant (spEnd x))
  have h1 : (ρ (c • v) : Fin r ⊕ Fin r → K) = spEnd g ((c • v : primaryComponent (spEnd x) a) :
      Fin r ⊕ Fin r → K) := rfl
  rw [← h1, map_smul]
  rfl

theorem commute_spEnd_of_mul_comm {x g : StatedSp r K} (hg : g * x = x * g) :
    Commute (spEnd g) (spEnd x) := by
  change spEnd g * spEnd x = spEnd x * spEnd g
  rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hg]

theorem spEnd_mul_eq (g g' : StatedSp r K) : spEnd (g * g') = spEnd g * spEnd g' := by
  change ((spLin r K (g * g') : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_mul, Units.val_mul]

theorem spEnd_one_eq : spEnd (1 : StatedSp r K) = 1 := by
  change ((spLin r K 1 : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
    Module.End K (Fin r ⊕ Fin r → K)) = _
  rw [map_one, Units.val_one]

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
  · subst h
    exact absurd hp (by norm_num)
  · exact h

variable [Finite K]

theorem sp_commute {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hK2 : Nat.card K ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p) {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hsq : Squarefree (minpoly K (spEnd x)))
    {P : Subgroup (StatedSp r K)} (hPC : P ≤ Subgroup.centralizer {x})
    (hPn : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ n ∈ P, g * n * g⁻¹ ∈ P)
    (hP2 : IsPGroup 2 ↥P) {y : StatedSp r K} (hy : y ∈ Subgroup.centralizer {x})
    (hyp : y ^ p = 1) {n : StatedSp r K} (hn : n ∈ P) : y * n = n * y := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hnC := hPC hn
  have hny : Commute (spEnd n) (spEnd x) :=
    commute_spEnd_of_mul_comm (Subgroup.mem_centralizer_singleton_iff.mp hnC)
  have hyx : Commute (spEnd y) (spEnd x) :=
    commute_spEnd_of_mul_comm (Subgroup.mem_centralizer_singleton_iff.mp hy)
  apply spLin_injective
  apply Units.ext
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  change spEnd y * spEnd n = spEnd n * spEnd y
  refine ext_primaryComponent hsq fun a ha v hv => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  by_cases ha1 : a = X - 1
  ·
    subst ha1
    obtain ⟨hcomm, hindep, hgen⟩ := blocks.directProduct
    have hfin : Finite ↥(reciprocalOrbits (spEnd x)) := by
      have : (reciprocalOrbits (spEnd x)).Finite := (Finset.finite_toSet _).image _
      exact this.to_subtype
    let H : ↥(reciprocalOrbits (spEnd x)) → Subgroup (StatedSp r K) :=
      fun O => spSupported x (O : Set K[X])
    have hcomm' : Pairwise fun i j => ∀ a b : StatedSp r K, a ∈ H i → b ∈ H j → Commute a b :=
      fun i j hij a b ha hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
    have hrecX : reciprocalPolynomial (X - 1 : K[X]) = X - 1 :=
      CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_X_sub_one
    let O₀ : ↥(reciprocalOrbits (spEnd x)) :=
      ⟨{X - 1, reciprocalPolynomial (X - 1)}, ⟨X - 1, ha, rfl⟩⟩
    have hO₀ : (O₀ : Set K[X]) = {X - 1} := by
      show ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1}
      rw [hrecX, Set.pair_eq_singleton]
    have hy' : y ∈ ⨆ O, H O := by rw [hgen]; exact hy
    obtain ⟨w, hw, z, hz, hyz, hwp⟩ := exists_component H hcomm' hindep hy' O₀
    let Fix : Subgroup (StatedSp r K) :=
      { carrier := {g | ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd g u = u}
        mul_mem' := fun {g g'} hg hg' u hu => by
          rw [spEnd_mul_eq, Module.End.mul_apply, hg' u hu, hg u hu]
        one_mem' := fun u _ => by rw [spEnd_one_eq]; rfl
        inv_mem' := fun {g} hg u hu => by
          have h1 := hg u hu
          calc spEnd g⁻¹ u = spEnd g⁻¹ (spEnd g u) := by rw [h1]
            _ = u := by
              rw [← Module.End.mul_apply, ← spEnd_mul_eq, inv_mul_cancel, spEnd_one_eq]
              rfl }
    have hzF : z ∈ Fix := by
      refine (iSup₂_le fun O hO => ?_ : (⨆ (i : ↥(reciprocalOrbits (spEnd x))) (_ : i ≠ O₀), H i) ≤ Fix) hz
      intro g hg u hu
      refine (mem_spSupported.mp hg).2 (X - 1) ha ?_ u hu
      intro hXO
      apply hO
      obtain ⟨c, hc, hcO⟩ := O.2
      have hcO : ({c, reciprocalPolynomial c} : Set K[X]) = (O : Set K[X]) := hcO
      have hc1 : c = X - 1 := by
        have hXO' : (X - 1 : K[X]) ∈ ({c, reciprocalPolynomial c} : Set K[X]) := by
          rw [hcO]; exact hXO
        rcases hXO' with h | h
        · exact h.symm
        · rw [Set.mem_singleton_iff] at h
          exact blocks.bijOn.injOn hc ha (by rw [← h, hrecX])
      apply Subtype.ext
      rw [← hcO, hc1]
    have hwF : w ∈ spFixedFactor x := by
      have : H O₀ = spFixedFactor x := by
        show spSupported x (O₀ : Set K[X]) = spSupported x {X - 1}
        rw [hO₀]
      rw [← this]
      exact hw
    have hyw : ∀ u ∈ primaryComponent (spEnd x) (X - 1), spEnd y u = spEnd w u := by
      intro u hu
      rw [hyz, spEnd_mul_eq, Module.End.mul_apply, hzF u hu]
    have hnv : spEnd n v ∈ primaryComponent (spEnd x) (X - 1) :=
      apply_mem_primaryComponent hny hv
    by_cases hl : SpFixedListed x
    ·
      have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := fun h => hK2 h.2
      have hq := spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42
      have hfinF : Finite ↥(spFixedFactor x) := inferInstance
      have hnw := commute_of_twoCentral hq.1 (twoCentral_of_isQuasisimple hq) hP2
        (fun g hg m hm => hPn g (spFixedFactor_le_centralizer x hg) m hm)
        (fun m hm g hg => spFixedFactor_normalized x m (hPC hm) g hg) n hn w hwF
      rw [hyw _ hnv, hyw v hv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul_eq,
        ← spEnd_mul_eq, hnw]
    ·
      have hw1 : w = 1 := eq_one_of_not_listed hp hp5 blocks hl hwF (hwp p hyp)
      rw [hyw _ hnv, hyw v hv, hw1, spEnd_one_eq]
      rfl
  ·
    have facts := spBlockFacts_nontrivial hp5 hq2 blocks ⟨a, ha⟩ ha1
    have hnG : spLin r K n ∈ gl_centralizer (spLin r K x) := mem_gl_centralizer.mpr hny
    obtain ⟨c, hc⟩ := facts.scalar (spLin r K n) hnG (fun hm g hg => by
      have hq := spPull_isQuasisimple facts hm
      have hcommF := commute_of_twoCentral hq.1 (twoCentral_of_isQuasisimple hq) hP2
        (fun g hg m hm => hPn g (spPull_le_centralizer x a hg) m hm)
        (fun m hm g hg => spPull_normalized x a m (hPC hm) g hg)
      have hgU : g ∈ unitaryCentralizer (spForm r K) (spLin r K x) :=
        specialBlock_le_unitaryCentralizer hg
      rw [unitaryCentralizer_spForm_eq_map] at hgU
      obtain ⟨g₀, -, rfl⟩ := hgU
      have hg₀ : g₀ ∈ spPull x a := hg
      have := hcommF n hn g₀ hg₀
      change spLin r K n * spLin r K g₀ = spLin r K g₀ * spLin r K n
      rw [← map_mul, ← map_mul, this])
    have hyv : spEnd y v ∈ primaryComponent (spEnd x) a := apply_mem_primaryComponent hyx hv
    have h1 := hc ⟨v, hv⟩
    have h2 := hc ⟨spEnd y v, hyv⟩
    change spEnd n v = _ at h1
    change spEnd n (spEnd y v) = _ at h2
    rw [h1, h2, spEnd_smul_of_commute hyx c ⟨v, hv⟩]

theorem groupStepAt_statedSp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hK2 : Nat.card K ≠ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hr : 1 ≤ r) :
    GroupStepAt p (StatedProj (StatedSp r K)) := by
  intro a b ha hbp hab t ht
  obtain ⟨⟨x, ⟨hxa, hxp⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf
    hK hp (by omega) hpℓ hr a ha
  have blocks := hblocks x hxa hxp
  subst hxa
  have hx : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hcharK : CharP K ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  refine commute_of_lift (proj r K) (fun u hu => sq_eq_one_of_proj_eq_one hr hu)
    (hp.odd_of_ne_two (by omega)) blocks.centralizer_eq ?_ hab.symm hbp t ht
  intro P hPC hPn hP2 y hy hyp n hn
  exact sp_commute hℓ hf hK hK2 hp (five_le_of_prime hp hp3) blocks hsq hPC hPn hP2 hy hyp hn

theorem innerStepAt_statedSp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hK2 : Nat.card K ≠ 2) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r) :
    Inputs1918.InnerStepAt p (StatedProj (StatedSp r K)) :=
  innerStepAt_of_groupStepAt
    (spProj_facts hℓ hf hK hr (fun h => hK2 (hK.trans h.2))).2.2
    (groupStepAt_statedSp hℓ hf hK hK2 hp hp3 hpℓ (by omega))

end Symplectic

section Orthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

theorem conj_mem_pCoreOf_inf {G : Type*} [Group G] {M N : Subgroup G}
    (hN : ∀ m ∈ M, ∀ g ∈ N, m * g * m⁻¹ ∈ N) {m : G} (hm : m ∈ M) {t : G}
    (ht : t ∈ pCoreOf 2 (M ⊓ N)) : m * t * m⁻¹ ∈ pCoreOf 2 (M ⊓ N) := by
  set S := (pCoreOf 2 (M ⊓ N)).map (MulAut.conj m).toMonoidHom with hS
  have hSle : S ≤ M ⊓ N := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' := pCoreOf_le 2 (M ⊓ N) hs
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hm (Subgroup.mem_inf.mp hs').1) (inv_mem hm),
      hN m hm s (Subgroup.mem_inf.mp hs').2⟩
  have hSn : ∀ c ∈ M ⊓ N, ∀ u ∈ S, c * u * c⁻¹ ∈ S := by
    rintro c hc _ ⟨s, hs, rfl⟩
    have hc' : m⁻¹ * c * m ∈ M ⊓ N := by
      have hcM := (Subgroup.mem_inf.mp hc).1
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hm) hcM) hm, ?_⟩
      have := hN m⁻¹ (inv_mem hm) c (Subgroup.mem_inf.mp hc).2
      rwa [inv_inv] at this
    refine ⟨(m⁻¹ * c * m) * s * (m⁻¹ * c * m)⁻¹, conj_mem_pCoreOf hc' hs, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hS2 : IsPGroup 2 ↥S := (isPGroup_pCoreOf 2 (M ⊓ N)).map _
  have hle := le_pCoreOf hSle hSn hS2
  exact hle ⟨t, ht, rfl⟩

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

theorem orth_commute (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {P : Subgroup (V ≃ₗ[K] V)} (hPM : P ≤ isometryCentralizer Q x) (hPΩ : P ≤ orthDerived Q)
    (hPn : ∀ g ∈ isometryCentralizer Q x, ∀ n ∈ P, g * n * g⁻¹ ∈ P) (hP2 : IsPGroup 2 ↥P)
    {y : V ≃ₗ[K] V} (hyM : y ∈ isometryCentralizer Q x) (hyΩ : y ∈ orthDerived Q)
    (hyp : y ^ p = 1) {n : V ≃ₗ[K] V} (hn : n ∈ P) : y * n = n * y := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hnM := hPM hn
  have hnΩ := hPΩ hn
  have hnC : n ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hnM).2
  have hyC : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hyM).2
  have hsq := hx.squarefree_minpoly
  suffices h : (y * n).toLinearMap = (n * y).toLinearMap from
    LinearEquiv.ext fun v => LinearMap.congr_fun h v
  refine ext_primaryComponent hsq fun a ha v hv => ?_
  change y (n v) = n (y v)
  by_cases ha1 : a = X - 1
  ·
    subst ha1
    have hvW : v ∈ fixedSpace x := by rw [fixedSpace_eq_primaryComponent]; exact hv
    by_cases hd : finrank K (fixedSpace x) ≤ 2
    · obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
      have hc := hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hd hnM hnΩ hyM hyΩ
      have h1 := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨v, hvW⟩ : V)) hc.eq
      exact h1.symm
    · have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
      have hQW := hx.polarBilin_fixed_nondegenerate
      obtain ⟨hexc, hcov⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
        hQW h3
      set O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) with hOdef
      have hfinO : Finite (fixedSpace x ≃ₗ[K] fixedSpace x) := finite_linearEquiv
      let ψ : ↥(isometryCentralizer Q x) →* ↥O :=
        (isometryRestrictFixed Q x).codRestrict O isometryRestrictFixed_mem_orthogonalGroup
      have hψs : Function.Surjective ψ := by
        intro o
        obtain ⟨g, hg⟩ := restrictFixed_surjective hx o.1 o.2
        exact ⟨⟨g.1, supportedBlock_le_isometryCentralizer _ g.2⟩, Subtype.ext hg⟩
      set yW := ψ ⟨y, hyM⟩ with hyWdef
      set nW := ψ ⟨n, hnM⟩ with hnWdef
      have hyWp : yW ^ p = 1 := by
        rw [hyWdef, ← map_pow]
        have : (⟨y, hyM⟩ : ↥(isometryCentralizer Q x)) ^ p = 1 := Subtype.ext hyp
        rw [this, map_one]
      suffices hc : nW * yW = yW * nW by
        have h1 := congrArg (fun o : ↥O => ((o : fixedSpace x ≃ₗ[K] fixedSpace x) ⟨v, hvW⟩ : V)) hc
        exact h1.symm
      by_cases hsmall : SmallFixedException (Q.comp (fixedSpace x).subtype)
      · have hyW1 : yW = 1 := by
          rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hyWp) with h1 | h1
          · exact orderOf_eq_one_iff.mp h1
          · exact absurd h1 (hexc hsmall yW p hp hp3)
        rw [hyW1, one_mul, mul_one]
      · obtain ⟨hperf, ⟨m, L, -, -, hsup, hL, -⟩, hprime⟩ := hcov hsmall
        have hTC : TwoCentral ↥(commutator ↥O) :=
          twoCentral_of_iSup L (fun i => (hL i).2.1) (fun i => (hL i).2.2) (fun i => (hL i).1)
            (fun i => inferInstance) hsup
        set R : Subgroup ↥O := (P.subgroupOf (isometryCentralizer Q x)).map ψ with hRdef
        have hR2 : IsPGroup 2 ↥R :=
          (hP2.comap_of_injective _ (Subgroup.subtype_injective _)).map ψ
        have hPn' : (P.subgroupOf (isometryCentralizer Q x)).Normal := ⟨fun s hs g => by
          rw [Subgroup.mem_subgroupOf] at hs ⊢
          exact hPn g g.2 s hs⟩
        have hRn : R.Normal := hPn'.map ψ hψs
        have hnWR : nW ∈ R := ⟨⟨n, hnM⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
        have hyWF : yW ∈ commutator ↥O := by
          haveI : Fact p.Prime := ⟨hp⟩
          by_cases h1 : yW = 1
          · rw [h1]; exact one_mem _
          · exact hprime yW p hp hp3 (orderOf_eq_prime hyWp h1)
        exact commute_of_twoCentral hperf hTC hR2 (fun f _ r hr => hRn.conj_mem r hr f)
          (fun r _ f hf => (inferInstance : (commutator ↥O).Normal).conj_mem f hf r) nW hnWR yW hyWF
  ·
    have hirr : Irreducible a := irreducible_of_mem_primaryFactors ha
    haveI : Fact (Irreducible a) := ⟨hirr⟩
    set γn := centralizerGL x a ⟨n, hnC⟩ with hγn
    set γy := centralizerGL x a ⟨y, hyC⟩ with hγy
    suffices hc : (γy : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a)) * γn =
        γn * γy by
      have h1 := congrArg (fun φ : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a) =>
        (φ ⟨v, hv⟩ : V)) hc
      exact h1
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap a
    · have hq := hx.quasisimple_specialBlock hp hp3 ha ha1 hm
      have hcommF := commute_of_twoCentral hq.1 (twoCentral_of_isQuasisimple hq) hP2
        (fun f hf r hr => hPn f (specialBlock_le_isometryCentralizer a hf) r hr)
        (fun r hr f hf => conj_mem_specialBlock (hPM hr) hf) n hn
      obtain ⟨c, hcγ⟩ : ∃ c : AdjoinRoot a, ∀ w, (γn : Module.End (AdjoinRoot a)
          (primaryComponent x.toLinearMap a)) w = c • w := by
        by_cases hself : a = reciprocalPolynomial a
        ·
          obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
            hx.exists_selfDual_hermitian hp2 ha ha1 hself
          have hd : finrank K (AdjoinRoot a) = 2 * d := by
            rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
          obtain ⟨ℓ, f, hU, hq', hbar⟩ := exists_unitaryFieldData K (AdjoinRoot a) hd
          have hbar' : ∀ z, frobPow K (AdjoinRoot a) d z = hU.bar z := fun z => by
            rw [hbar, frobPow_apply]
          let B : primaryComponent x.toLinearMap a →ₛₗ[hU.bar]
              primaryComponent x.toLinearMap a →ₗ[AdjoinRoot a] AdjoinRoot a :=
            LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
              (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
              (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
          have hBH : ∀ u w, B u w = H u w := fun u w => rfl
          have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
          have hBl : B.SeparatingLeft := by
            intro u hu
            refine Subtype.ext (hx.eq_zero_of_polar_selfdual ha hself u.2 fun w hw => ?_)
            have h1 := hH u ⟨w, hw⟩ 1
            rw [mul_one, one_smul] at h1
            have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
            rw [h2, map_zero] at h1
            exact h1.symm
          have hrange : (specialBlockGL Q x a).range =
              CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
            rw [range_specialBlockGL, CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup]
            congr 1
            ext γ
            rw [hx.mem_range_blockGL_selfDual_iff ha ha1 hself H hH,
              CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
            exact Iff.rfl
          have hq2 : 2 ≤ ℓ ^ (f * d) := by
            have hd1 : 1 ≤ d := by
              have := hirr.natDegree_pos
              omega
            have hK2 : 2 ≤ Nat.card K := by
              have := Fintype.ofFinite K
              rw [Nat.card_eq_fintype_card]
              exact Fintype.one_lt_card
            have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq', pow_mul]
            have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow (by omega) _
            omega
          refine CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hU hBsymm
            hBl hm hq2 _ fun δ hδ => ?_
          rw [← hrange] at hδ
          obtain ⟨g, rfl⟩ := hδ
          refine LinearMap.ext fun w => Subtype.ext ?_
          change n (g.1 w) = g.1 (n w)
          have := hcommF g.1 g.2
          exact congrArg (fun φ : V ≃ₗ[K] V => φ w) this
        ·
          refine CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_linear hm _
            fun δ hδ => ?_
          let u : SpecialLinearGroup (AdjoinRoot a) (primaryComponent x.toLinearMap a) :=
            ⟨LinearMap.GeneralLinearGroup.toLinearEquiv δ, Units.ext (by
              rw [LinearEquiv.coe_det]; exact hδ)⟩
          obtain ⟨g, hg⟩ := hx.specialToSL_surjective_paired ha hself u
          have hδg : ∀ w, ((δ : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a)) w :
              V) = g.1 w := by
            intro w
            have := congrArg (fun s : SpecialLinearGroup (AdjoinRoot a)
              (primaryComponent x.toLinearMap a) =>
                (((s : primaryComponent x.toLinearMap a ≃ₗ[AdjoinRoot a]
                  primaryComponent x.toLinearMap a) w : primaryComponent x.toLinearMap a) : V)) hg
            exact this.symm
          refine LinearMap.ext fun w => Subtype.ext ?_
          change n ((δ : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a)) w : V) =
            ((δ : Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a))
              ⟨n w, apply_mem_primaryComponent_of_mem_centralizer hnC w.2⟩ : V)
          rw [hδg, hδg]
          have := hcommF g.1 g.2
          exact congrArg (fun φ : V ≃ₗ[K] V => φ w) this
      refine LinearMap.ext fun w => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hcγ, hcγ, map_smul]
    · have hm1 : primaryMultiplicity x.toLinearMap a ≤ 1 := by omega
      exact CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one hm1 _ _

theorem groupStepAt_projOrthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K) : GroupStepAt p (ProjOrthDerived Q) := by
  intro a b ha hbp hab t ht
  obtain ⟨-, -, hZcard, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp (by omega) a ha
  subst hxa
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hker : ∀ u ∈ ρ.ker, u ^ 2 = 1 := by
    intro u hu
    rw [hρ, QuotientGroup.ker_mk'] at hu
    have hord : orderOf (⟨u, hu⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
    have hle : orderOf (⟨u, hu⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ≤ 2 :=
      (Nat.le_of_dvd hpos hord).trans hZcard
    have hop : 0 < orderOf (⟨u, hu⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) :=
      orderOf_pos _
    have h2 : orderOf (⟨u, hu⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      interval_cases h : orderOf (⟨u, hu⟩ : ↥((scalars K V).subgroupOf (orthDerived Q)))
      · exact one_dvd _
      · exact dvd_refl _
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h2)
  refine commute_of_lift ρ hker (hp.odd_of_ne_two (by omega)) (x := x) hcent ?_ hab.symm hbp t ht
  intro P hPC hPn hP2 y hy hyp n hn
  set M := isometryCentralizer Q (x : V ≃ₗ[K] V) with hM
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup
  have hCM : ∀ g : ↥(orthDerived Q), g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) →
      (g : V ≃ₗ[K] V) ∈ M ⊓ orthDerived Q := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hΩO g.2, ?_⟩, g.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact congrArg Subtype.val hg
  set P₀ := pCoreOf 2 (M ⊓ orthDerived Q) with hP₀
  have hΩn : ∀ m ∈ M, ∀ g ∈ orthDerived Q, m * g * m⁻¹ ∈ orthDerived Q := fun m hm g hg =>
    CFSG.RankThree.PartOne.KCUnitary.conj_mem_commutator_self (Subgroup.mem_inf.mp hm).1 hg
  have hP'le : P.map (orthDerived Q).subtype ≤ P₀ := by
    refine le_pCoreOf ?_ ?_ (hP2.map _)
    · rintro _ ⟨g, hg, rfl⟩
      exact hCM g (hPC hg)
    · rintro c hc _ ⟨g, hg, rfl⟩
      have hcC : (⟨c, (Subgroup.mem_inf.mp hc).2⟩ : ↥(orthDerived Q)) ∈
          Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp
          (Subgroup.mem_inf.mp hc).1).2
        exact this
      exact ⟨_, hPn _ hcC g hg, rfl⟩
  have hP₀M : P₀ ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hP₀Ω : P₀ ≤ orthDerived Q := (pCoreOf_le 2 _).trans inf_le_right
  have hyM := hCM y hy
  have key := orth_commute hQ hp hp3 hx hP₀M hP₀Ω
    (fun g hg t ht => conj_mem_pCoreOf_inf hΩn hg ht) (isPGroup_pCoreOf 2 _)
    (Subgroup.mem_inf.mp hyM).1 (Subgroup.mem_inf.mp hyM).2
    (by have := congrArg Subtype.val hyp; simpa using this)
    (hP'le ⟨n, hn, rfl⟩)
  exact Subtype.ext key

theorem innerStepAt_projOrthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K) : Inputs1918.InnerStepAt p (ProjOrthDerived Q) :=
  innerStepAt_of_groupStepAt
    (conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KCOrthogonalModel.center_projOrthDerived_eq_bot hQ hT))
    (groupStepAt_projOrthDerived hQ hT hp hp3 hpl)

end Orthogonal

section Catalogue

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem innerStepAt_of_PSp {S : Type} [Group S] {r : ℕ} (h : StatedClassicalModel S .PSp r 3 1)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : Inputs1918.InnerStepAt p S := by
  obtain ⟨⟨-, -, hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := id h
  have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
  exact Inputs1918.InnerStepAt.of_mulEquiv e (innerStepAt_statedSp Nat.prime_three le_rfl hK
    (by rw [hK3]; norm_num) hp hp3 (by omega) hr)

theorem innerStepAt_of_POmegaOdd {S : Type} [Group S] {r : ℕ}
    (h : StatedClassicalModel S .POmegaOdd r 3 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  exact Inputs1918.InnerStepAt.of_mulEquiv ((coordinateOddWitnessEquiv K e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalD4.bridgeEquiv _ (by omega)))
    (innerStepAt_projOrthDerived hnd hT hp hp3 (by rw [hchar]; omega))

theorem innerStepAt_of_POmegaPlus {S : Type} [Group S] {r : ℕ}
    (h : StatedClassicalModel S .POmegaPlus r 3 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨⟨-, -, hr⟩, K, _, _, hK, ⟨e⟩⟩ := id h
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  exact Inputs1918.InnerStepAt.of_mulEquiv ((coordinatePlusWitnessEquiv K e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalD4.bridgeEquiv _ (by omega)))
    (innerStepAt_projOrthDerived hnd hT hp hp3 (by rw [hchar]; omega))

theorem innerStepAt_of_POmegaMinus {S : Type} [Group S] {r : ℕ}
    (h : StatedClassicalModel S .POmegaMinus r 3 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨⟨-, -, hr⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  exact Inputs1918.InnerStepAt.of_mulEquiv ((coordinateMinusWitnessEquiv K _ b c e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalD4.bridgeEquiv _ (by omega)))
    (innerStepAt_projOrthDerived hnd hT hp hp3 (by rw [hchar]; omega))

theorem p_exp_of_card_three {q : TauCeti.PrimePower} (hq : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  refine ⟨Inputs1918.p_eq_three_of_card hq, ?_⟩
  have h := hq
  rw [TauCeti.PrimePower.card_def] at h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_three).1 h).2

theorem innerStepAt_cat_B {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨hq3, hqe⟩ := p_exp_of_card_three hq
  rcases CFSG.Models.lieModel_B r q hv e with ⟨hadm, hcm | ⟨hn0, -⟩⟩ | ⟨hadm, hcm | ⟨hn0, -⟩⟩
  · rw [hq3, hqe] at hcm
    exact innerStepAt_of_PSp hcm hp hp3
  · exact absurd hn0 (by have := hadm.2.2.1; omega)
  · rw [hq3, hqe] at hcm
    exact innerStepAt_of_POmegaOdd hcm hp hp3
  · exact absurd hn0 (by have := hadm.2.2.1; omega)

theorem innerStepAt_cat_C {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) (hq : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨hq3, hqe⟩ := p_exp_of_card_three hq
  obtain ⟨hadm, hcm | ⟨hn0, -⟩⟩ := CFSG.Models.lieModel_C r q hv e
  · rw [hq3, hqe] at hcm
    exact innerStepAt_of_PSp hcm hp hp3
  · exact absurd hn0 (by have := hadm.2.2.1; omega)

theorem innerStepAt_cat_D {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    Inputs1918.InnerStepAt p S := by
  obtain ⟨hq3, hqe⟩ := p_exp_of_card_three hq
  obtain ⟨hadm, hcm | ⟨hn0, -⟩⟩ := CFSG.Models.lieModel_D r q hv e
  · rw [hq3, hqe] at hcm
    exact innerStepAt_of_POmegaPlus hcm hp hp3
  · exact absurd hn0 (by have := hadm.2.2; omega)

theorem innerStepAt_cat_twistedD {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : Inputs1918.InnerStepAt p S := by
  obtain ⟨hq3, hqe⟩ := p_exp_of_card_three hq
  obtain ⟨hadm, hcm | ⟨hn0, -⟩⟩ := CFSG.Models.lieModel_twistedD r q hv e
  · rw [hq3, hqe] at hcm
    exact innerStepAt_of_POmegaMinus hcm hp hp3
  · exact absurd hn0 (by have := hadm.2.2; omega)

end Catalogue

section Assembly

theorem innerStepAt_of_isLieOverField
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hE8 : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → Subgroup.center S = ⊥ →
      ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid), q.card = 3 →
        (S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) → Inputs1918.InnerStepAt p S)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hlie : Prop1116Design.IsLieOverField 3 S) : Inputs1918.InnerStepAt p S := by
  haveI := hS
  obtain ⟨idx, ⟨e⟩, hfo⟩ := hlie
  rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with hZ | hZ
  swap
  · exact Inputs1918.innerStepAt_of_center_eq_top hp hZ
  let eS : S ≃* (TauCeti.CFSGIndex.lie idx).Group :=
    (Prop1116Design.mulEquivQuotCenterOfEqBot hZ).trans e
  obtain ⟨d, hv⟩ := idx
  have hc := Inputs1918.char_exp_of_fieldOrder_three hfo
  cases d with
  | A r q => exact Inputs1918.innerStepAt_cat_A r q hv (by simpa using hfo) eS hp hp3
  | twistedA r q => exact Inputs1918.innerStepAt_cat_twistedA r q hv (by simpa using hfo) eS hp hp3
  | B r q => exact innerStepAt_cat_B r q hv (by simpa using hfo) eS hp hp3
  | C r q => exact innerStepAt_cat_C r q hv (by simpa using hfo) eS hp hp3
  | D r q => exact innerStepAt_cat_D r q hv (by simpa using hfo) eS hp hp3
  | twistedD r q => exact innerStepAt_cat_twistedD r q hv (by simpa using hfo) eS hp hp3
  | E6 q => exact Inputs1918.innerStepAt_cat_E6 hZ q hv (by simpa using hfo) eS hp hp3
  | E7 q => exact Inputs1918.innerStepAt_cat_E7 hZ q hv (by simpa using hfo) eS hp hp3
  | E8 q => exact hE8 S hS hZ q hv (by simpa using hfo) eS
  | F4 q => exact Inputs1918.innerStepAt_cat_F4 hZ q hv (by simpa using hfo) eS hp hp3
  | G2 q => exact Inputs1918.innerStepAt_cat_G2 hZ q hv (by simpa using hfo) eS hp hp3
  | twistedE6 q =>
    exact Inputs1918.innerStepAt_cat_twistedE6 hZ q hv (by simpa using hfo) eS hp hp3
  | trialityD4 q =>
    exact Inputs1918.innerStepAt_cat_trialityD4 hZ q hv (by simpa using hfo) eS hp hp3
  | suzuki m =>
    simp only [TauCeti.LieTypeIndex.characteristic_suzuki] at hc
    omega
  | reeG2 m =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hm : 1 ≤ m := by simpa using hr
    simp only [TauCeti.LieTypeIndex.fieldExponent_reeG2] at hc
    omega
  | reeF4 m =>
    simp only [TauCeti.LieTypeIndex.characteristic_reeF4] at hc
    omega
  | tits =>
    simp only [TauCeti.LieTypeIndex.characteristic_tits] at hc
    omega

theorem input19_18S13_holds
    :
    ∀ (S : Type) [Group S] [Finite S],
      ((IsSimpleGroup S ∧ Prop1116Design.IsLieOverField 3 S) ∨ IsLpType 3 (3 ^ 13) S) →
        IsWeaklyLocallyOTwoBalancedWrtP 13 1 S := by
  intro S _ _ hS
  have hp : Nat.Prime 13 := by norm_num
  rcases hS with ⟨hsimp, hlie⟩ | hL
  · refine BalanceFromYS.isWeaklyLocallyOTwoBalancedWrtP_of_inner hp (by norm_num)
      (Inputs1918.input7_1Chev3_holds 13 hp (by norm_num) S hsimp hlie)
      (innerStepAt_of_isLieOverField hp (by norm_num)
        (fun S' _ _ _ hZ q hv hq e' => Inputs1918.innerStepAt_cat_E8 hZ q hv hq e' hp
          (by norm_num) (by norm_num)) hsimp hlie)
  · exact Inputs1918.input19_18b_holds S hL

theorem input19_18_holds
    : Lemma123.Input19_18 := by
  intro Y _ _ hq _ hform
  rcases hform with h1 | h1
  · refine Inputs123a.isWeaklyLocallyOTwoBalancedWrtP_of_quot hq.1
      (input19_18S13_holds _ (Or.inl ⟨hq.2, ?_⟩))
    obtain ⟨idx, ⟨e⟩, hidx⟩ := h1
    exact ⟨idx, ⟨(Prop1116Design.mulEquivQuotCenterOfEqBot
      (Inputs123a.center_quot_eq_bot hq)).symm.trans e⟩, hidx⟩
  · exact input19_18S13_holds Y (Or.inr h1)

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1918c
