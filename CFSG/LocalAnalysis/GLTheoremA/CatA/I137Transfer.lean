module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137Tr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {J : Subgroup G} {g : G} :
    g ∈ GLAPPrimeCoreOf p J ↔ ∃ h ∈ GLAPPrimeCore p ↥J, (h : G) = g := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem le_glaPPrimeCore_of_normal {p : ℕ} {H : Type} [Group H] (M : Subgroup H) [M.Normal]
    (hM : Nat.Coprime p (Nat.card M)) : M ≤ GLAPPrimeCore p H :=
  le_sSup ⟨inferInstance, hM⟩

theorem coprime_card_glaPPrimeCore {p : ℕ} (hp : p.Prime) (J : Subgroup G) [Finite G] :
    Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.pPrimeCore_coprime_card

theorem comap_glaPPrimeCore_le {p : ℕ} (hp : p.Prime) [Finite G] {I J : Subgroup G} (hIJ : I ≤ J) :
    (GLAPPrimeCore p ↥J).comap (Subgroup.inclusion hIJ) ≤ GLAPPrimeCore p ↥I := by
  have hdvd : Nat.card ((GLAPPrimeCore p ↥J).comap (Subgroup.inclusion hIJ)) ∣
      Nat.card (GLAPPrimeCore p ↥J) :=
    Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hIJ)
  have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCore p ↥J).comap (Subgroup.inclusion hIJ))) :=
    Nat.Coprime.coprime_dvd_right hdvd (coprime_card_glaPPrimeCore hp J)
  exact le_glaPPrimeCore_of_normal _ hcop

@[expose] noncomputable def piJ (p : ℕ) (J : Subgroup G) : ↥J →* PQuot p J :=
  QuotientGroup.mk' (GLAPPrimeCore p ↥J)

@[expose] noncomputable def psiI (p : ℕ) (I : Subgroup G) : ↥I →* PSimple p I :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p I))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥I))

theorem psiI_surjective (p : ℕ) (I : Subgroup G) : Function.Surjective (psiI p I) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem psiI_eq_one_of_mem {p : ℕ} {I : Subgroup G} {z : ↥I} (hz : z ∈ GLAPPrimeCore p ↥I) :
    psiI p I z = 1 := by
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥I) z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  unfold psiI
  simp only [MonoidHom.comp_apply, h1, map_one]

theorem psiI_eq_one_of_central {p : ℕ} (hp : p.Prime) [Finite G] {I J : Subgroup G} (hIJ : I ≤ J)
    (i : ↥I) (hcen : QuotientGroup.mk' (GLAPPrimeCore p ↥J) (Subgroup.inclusion hIJ i) ∈
      Subgroup.center (PQuot p J)) : psiI p I i = 1 := by
  have key : QuotientGroup.mk' (GLAPPrimeCore p ↥I) i ∈ Subgroup.center (PQuot p I) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥I) g
    rw [Subgroup.mem_center_iff] at hcen
    have hc := hcen (QuotientGroup.mk' (GLAPPrimeCore p ↥J) (Subgroup.inclusion hIJ j))
    have hc' : QuotientGroup.mk' (GLAPPrimeCore p ↥J) (Subgroup.inclusion hIJ j * Subgroup.inclusion hIJ i) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥J) (Subgroup.inclusion hIJ i * Subgroup.inclusion hIJ j) := by
      rw [map_mul, map_mul]
      exact hc
    have h2 := (QuotientGroup.eq).1 hc'
    have h3 : (j * i)⁻¹ * (i * j) ∈ GLAPPrimeCore p ↥I :=
      comap_glaPPrimeCore_le hp hIJ (by simpa [map_mul, map_inv] using h2)
    rw [← map_mul, ← map_mul]
    exact (QuotientGroup.eq).2 h3
  unfold psiI
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact key

section Factor

variable {H Q M : Type} [Group H] [Group Q] [Group M]

@[expose] noncomputable def factorThrough (φ : H →* Q) (ψ : H →* M) (hker : φ.ker ≤ ψ.ker) :
    φ.range →* M :=
  (QuotientGroup.lift φ.ker ψ hker).comp (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom

theorem factorThrough_apply (φ : H →* Q) (ψ : H →* M) (hker : φ.ker ≤ ψ.ker) (h : H) :
    factorThrough φ ψ hker ⟨φ h, ⟨h, rfl⟩⟩ = ψ h := by
  have hk : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ h, ⟨h, rfl⟩⟩ =
      (QuotientGroup.mk h : H ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show QuotientGroup.lift φ.ker ψ hker ((QuotientGroup.quotientKerEquivRange φ).symm ⟨φ h, ⟨h, rfl⟩⟩) = ψ h
  rw [hk]
  rfl

theorem factorThrough_surjective (φ : H →* Q) (ψ : H →* M) (hker : φ.ker ≤ ψ.ker)
    (hψ : Function.Surjective ψ) : Function.Surjective (factorThrough φ ψ hker) := by
  intro y
  obtain ⟨h, rfl⟩ := hψ y
  exact ⟨⟨φ h, ⟨h, rfl⟩⟩, factorThrough_apply φ ψ hker h⟩

end Factor

theorem psiI_comp_inclusion_surjective {p : ℕ} {I I₀ : Subgroup G} (hI₀I : I₀ ≤ I)
    (hO : I₀ ⊔ GLAPPrimeCoreOf p I = I) :
    Function.Surjective ((psiI p I).comp (Subgroup.inclusion hI₀I)) := by
  have hsup : ∀ x : ↥I, x ∈ I₀.subgroupOf I ⊔ GLAPPrimeCore p ↥I := by
    have hle : I₀ ⊔ GLAPPrimeCoreOf p I ≤
        ((I₀.subgroupOf I) ⊔ GLAPPrimeCore p ↥I).map I.subtype := by
      apply sup_le
      · intro g hg
        exact Subgroup.mem_map_of_mem I.subtype
          (Subgroup.mem_sup_left (show (⟨g, hI₀I hg⟩ : ↥I) ∈ I₀.subgroupOf I from hg))
      · intro g hg
        obtain ⟨h, hh, rfl⟩ := mem_glaPPrimeCoreOf_iff.1 hg
        exact Subgroup.mem_map_of_mem I.subtype (Subgroup.mem_sup_right hh)
    intro x
    have hx : (x : G) ∈ ((I₀.subgroupOf I) ⊔ GLAPPrimeCore p ↥I).map I.subtype :=
      hle (by rw [hO]; exact x.2)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  intro q
  obtain ⟨x, rfl⟩ := psiI_surjective p I q
  obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 (hsup x)
  refine ⟨⟨y.1, (Subgroup.mem_subgroupOf).1 hy⟩, ?_⟩
  rw [← hyz, map_mul, psiI_eq_one_of_mem hz, mul_one]
  rfl

theorem mem_barX_iff {p : ℕ} {J K : Subgroup G} {u : PQuot p J} :
    u ∈ barX p J K ↔ ∃ k : ↥J, (k : G) ∈ K ∧ piJ p J k = u := by
  unfold barX
  constructor
  · intro hu
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨k, Subgroup.mem_subgroupOf.1 hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk)

theorem piJ_conj_mem_barX {p : ℕ} {J S : Subgroup G} (hSJ : S ≤ J) {a s : ↥J}
    (hs : (s : G) ∈ S)
    (ha : (a : G) ∈ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G)) :
    piJ p J (a * s * a⁻¹) ∈ barX p J S := by
  set W : Subgroup G := ((barX p J S).comap (piJ p J)).map J.subtype with hWdef
  have hS_le : S ≤ W := by
    intro g hg
    have hgJ : g ∈ J := hSJ hg
    refine Subgroup.mem_map.2 ⟨⟨g, hgJ⟩, ?_, rfl⟩
    show piJ p J ⟨g, hgJ⟩ ∈ barX p J S
    exact mem_barX_iff.2 ⟨⟨g, hgJ⟩, hg, rfl⟩
  have hO_le : GLAPPrimeCoreOf p J ≤ W := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := mem_glaPPrimeCoreOf_iff.1 hg
    refine Subgroup.mem_map.2 ⟨h, ?_, rfl⟩
    show piJ p J h ∈ barX p J S
    have h1 : piJ p J h = 1 := by
      unfold piJ
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hh
    rw [h1]
    exact Subgroup.one_mem _
  have hW : S ⊔ GLAPPrimeCoreOf p J ≤ W := sup_le hS_le hO_le
  have hmem : (a : G) * (s : G) * (a : G)⁻¹ ∈ S ⊔ GLAPPrimeCoreOf p J := by
    have hs' : (s : G) ∈ S ⊔ GLAPPrimeCoreOf p J := Subgroup.mem_sup_left hs
    exact (Subgroup.mem_normalizer_iff.1 ha (s : G)).1 hs'
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 (hW hmem)
  have hay : a * s * a⁻¹ = y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hyeq.symm)
  rw [hay]
  exact Subgroup.mem_comap.1 hy

theorem isPGroup_barX {p : ℕ} {J S : Subgroup G} (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) :
    IsPGroup 2 (barX p J S) := by
  unfold barX
  exact (hS2.comap_subtype (K := J)).map _

theorem barX_map_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite G] {J S : Subgroup G}
    (hSJ : S ≤ J) (hS2 : IsPGroup 2 S) (hSn : ¬ S ≤ GLAPPrimeCoreOf p J) :
    (barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J))) ≠ ⊥ := by
  intro hbot
  have hcen : barX p J S ≤ Subgroup.center (PQuot p J) := by
    intro u hu
    have hu' : QuotientGroup.mk' (Subgroup.center (PQuot p J)) u ∈
        (⊥ : Subgroup (PQuot p J ⧸ Subgroup.center (PQuot p J))) :=
      hbot ▸ Subgroup.mem_map_of_mem _ hu
    exact (QuotientGroup.eq_one_iff u).1 (Subgroup.mem_bot.1 hu')
  haveI : (barX p J S).Normal :=
    { conj_mem := fun n hn g => by
        have hc := Subgroup.mem_center_iff.1 (hcen hn) g
        have hgn : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        rw [hgn]
        exact hn }
  have hcop : Nat.Coprime p (Nat.card (barX p J S)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_barX hS2 hSJ)
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hle : barX p J S ≤ GLAPPrimeCore p (PQuot p J) := le_glaPPrimeCore_of_normal _ hcop
  haveI : Fact p.Prime := ⟨hp⟩
  have hbot2 : GLAPPrimeCore p (PQuot p J) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥J) p
  rw [hbot2] at hle
  apply hSn
  intro g hg
  have hgJ : g ∈ J := hSJ hg
  have hmem : piJ p J ⟨g, hgJ⟩ ∈ barX p J S := mem_barX_iff.2 ⟨⟨g, hgJ⟩, hg, rfl⟩
  have h1 : piJ p J ⟨g, hgJ⟩ = 1 := Subgroup.mem_bot.1 (hle hmem)
  rw [mem_glaPPrimeCoreOf_iff]
  refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
  unfold piJ at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

@[expose] noncomputable def phi0 (p : ℕ) {J I₀ : Subgroup G} (hI₀J : I₀ ≤ J) :
    ↥I₀ →* (PQuot p J ⧸ Subgroup.center (PQuot p J)) :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp
    ((piJ p J).comp (Subgroup.inclusion hI₀J))

theorem phi0_ker_le {p : ℕ} (hp : p.Prime) [Finite G] {I J I₀ : Subgroup G} (hIJ : I ≤ J)
    (hI₀I : I₀ ≤ I) :
    (phi0 p (hI₀I.trans hIJ)).ker ≤ ((psiI p I).comp (Subgroup.inclusion hI₀I)).ker := by
  intro i hi
  rw [MonoidHom.mem_ker] at hi ⊢
  have hcen : piJ p J (Subgroup.inclusion (hI₀I.trans hIJ) i) ∈ Subgroup.center (PQuot p J) := by
    have h1 : QuotientGroup.mk' (Subgroup.center (PQuot p J))
        (piJ p J (Subgroup.inclusion (hI₀I.trans hIJ) i)) = 1 := hi
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact psiI_eq_one_of_central hp hIJ (Subgroup.inclusion hI₀I i) hcen

theorem phi0_conj_mem {p : ℕ} {J S I₀ : Subgroup G} (hI₀J : I₀ ≤ J) (hSJ : S ≤ J)
    (hI₀N : I₀ ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G))
    (a : ↥I₀) (t : PQuot p J ⧸ Subgroup.center (PQuot p J))
    (ht : t ∈ (barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J)))) :
    phi0 p hI₀J a * t * (phi0 p hI₀J a)⁻¹ ∈
      (barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J))) := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ht
  obtain ⟨s, hs, rfl⟩ := mem_barX_iff.1 hu
  have ha : ((Subgroup.inclusion hI₀J a : ↥J) : G) ∈
      Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) := hI₀N a.2
  have hm := piJ_conj_mem_barX hSJ hs ha
  have hmap : phi0 p hI₀J a * QuotientGroup.mk' (Subgroup.center (PQuot p J)) (piJ p J s) *
      (phi0 p hI₀J a)⁻¹ = QuotientGroup.mk' (Subgroup.center (PQuot p J))
        (piJ p J (Subgroup.inclusion hI₀J a * s * (Subgroup.inclusion hI₀J a)⁻¹)) := by
    unfold phi0
    simp only [MonoidHom.comp_apply, ← map_mul, ← map_inv]
  rw [hmap]
  exact Subgroup.mem_map_of_mem _ hm

theorem phi0_mem_normalizer {p : ℕ} {J S I₀ : Subgroup G} (hI₀J : I₀ ≤ J) (hSJ : S ≤ J)
    (hI₀N : I₀ ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G))
    (a : ↥I₀) :
    phi0 p hI₀J a ∈ Subgroup.normalizer
      (((barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J)))) : Set _) := by
  set T := (barX p J S).map (QuotientGroup.mk' (Subgroup.center (PQuot p J))) with hT
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact phi0_conj_mem hI₀J hSJ hI₀N a h hh
  · intro hh
    have h2 := phi0_conj_mem hI₀J hSJ hI₀N a⁻¹ _ hh
    have h3 : phi0 p hI₀J a⁻¹ = (phi0 p hI₀J a)⁻¹ := map_inv _ a
    have e : (phi0 p hI₀J a)⁻¹ * (phi0 p hI₀J a * h * (phi0 p hI₀J a)⁻¹) *
        (phi0 p hI₀J a) = h := by group
    rw [h3, inv_inv, e] at h2
    exact h2

end CFSG.LocalAnalysis.GLTheoremA.I137Tr
