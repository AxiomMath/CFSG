module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatZ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentZRed
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3PointIrr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial (pointRadical mem_pointRadical card_pointRadical)
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open scoped commutatorElement Pointwise

namespace Sec3SHat

variable {G : Type} [Group G]

theorem le_oddCoreIn_of_odd {N L : Subgroup G} (hNL : N ≤ L)
    (hLN : L ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ AS76b.oddCoreIn L := by
  have hn : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hodd' : Odd (Nat.card (N.subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv]
  have h := AS76b.le_assemblyOddCore hn hodd'
  intro x hx
  exact ⟨⟨x, hNL hx⟩, h hx, rfl⟩

theorem le_of_perfect {F C R : Subgroup G} (hF : ⁅F, F⁆ = F) (hCF : C ≤ F)
    (hFC : F ≤ normalizer (C : Set G)) (hRF : R ≤ F) [Group.IsSolvable R]
    (hdec : ∀ f ∈ F, ∃ c ∈ C, ∃ r ∈ R, f = c * r) : F ≤ C := by
  set N := C.subgroupOf F with hNdef
  have hN : N.Normal := (normal_subgroupOf_iff_le_normalizer hCF).mpr hFC
  let π : ↥F →* ↥F ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  let ψ : ↥R →* ↥F ⧸ N := π.comp (Subgroup.inclusion hRF)
  have hψ : Function.Surjective ψ := by
    intro w
    obtain ⟨f, rfl⟩ := hπ w
    obtain ⟨c, hc, r, hr, hfcr⟩ := hdec f f.2
    refine ⟨⟨r, hr⟩, ?_⟩
    have hf : f = ⟨c, hCF hc⟩ * Subgroup.inclusion hRF ⟨r, hr⟩ := Subtype.ext hfcr
    have hc1 : π ⟨c, hCF hc⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hc)
    change π (Subgroup.inclusion hRF ⟨r, hr⟩) = π f
    rw [hf, map_mul, hc1, one_mul]
  have : Group.IsSolvable (↥F ⧸ N) := Group.isSolvable_of_surjective hψ
  have hcF : commutator ↥F = ⊤ := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_subtype_commutator, hF, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcQ : commutator (↥F ⧸ N) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective π hπ, ← Subgroup.map_commutator,
      ← commutator_def, hcF]
  have hsub : Subsingleton (↥F ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥F ⧸ N)).ne hcQ
  intro f hf
  have h1 : π ⟨f, hf⟩ = 1 := Subsingleton.elim _ _
  exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

section PointRadical

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem conj_mem_pointRadical {g t : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) {a : V} (hga : g a = a)
    (ht : t ∈ pointRadical q a) : g * t * g⁻¹ ∈ pointRadical q a := by
  obtain ⟨htO, hta, h1, h2⟩ := ht
  have hginv : ∀ v, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hga' : g⁻¹ a = a := by
    calc g⁻¹ a = g⁻¹ (g a) := by rw [hga]
      _ = a := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  refine ⟨mul_mem (mul_mem hg htO) (inv_mem hg), ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hga', hta, hga]
  · have hx' : polar q a (g⁻¹ x) = 0 := by
      rw [← hga', TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (inv_mem hg), hx]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h1 _ hx')
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    calc c • a = g (c • a) := by rw [map_smul, hga]
      _ = g (t (g⁻¹ x) - g⁻¹ x) := by rw [hc]
      _ = g (t (g⁻¹ x)) - x := by rw [map_sub, hginv]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have e : g (t (g⁻¹ v)) - v = g (t (g⁻¹ v) - g⁻¹ v) := by rw [map_sub, hginv]
    rw [e, ← hga, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, h2]

variable [FiniteDimensional (ZMod 2) V]

theorem comm_of_mem_pointRadical (hq : q.polarBilin.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    (ha : q a = 0) {s t : V ≃ₗ[ZMod 2] V} (hs : s ∈ pointRadical q a)
    (ht : t ∈ pointRadical q a) : s * t = t * s := by
  obtain ⟨u, hau, rfl⟩ := (CFSG.LargeExtraspecial.mem_pointRadical_iff hq ha0 ha).mp hs
  obtain ⟨u', hau', rfl⟩ := (CFSG.LargeExtraspecial.mem_pointRadical_iff hq ha0 ha).mp ht
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_mul hau hau',
    CFSG.ClassicalGroups.Orthogonal.eichler_mul hau' hau, add_comm]

theorem mul_self_of_mem_pointRadical (hq : q.polarBilin.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    (ha : q a = 0) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ pointRadical q a) : t * t = 1 := by
  obtain ⟨u, hau, rfl⟩ := (CFSG.LargeExtraspecial.mem_pointRadical_iff hq ha0 ha).mp ht
  exact CFSG.LargeExtraspecial.eichler_mul_self hau

end PointRadical

end Sec3SHat

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem oddCoreIn_CF_le :
    AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) := by
  set C₁ := sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hC₁
  refine Sec3SHat.le_oddCoreIn_of_odd ((AS76b.oddCoreIn_le C₁).trans inf_le_right)
    (fun c hc => ?_) (AS76b.odd_card_oddCoreIn C₁)
  have hcN : c ∈ H.xsub.N := centralizer_le_normalizer _ hc
  exact AS76b.normalizer_le_normalizer_oddCoreIn C₁
    (mem_normalizer_inf (H.N_le_normalizer_F hcN) (AS81.mem_normalizer_centralizer hcN))

theorem oddCoreIn_le_centralizer_F (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hOB : AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (B₀ : Set G)) :
    AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G) := by
  set Fs := sec3F (Q₀ ⊔ Q) with hFs
  set C₁ := Fs ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) with hC₁
  set R₃ := AS76b.oddCoreIn C₁ with hR₃
  have hR₃C₁ : R₃ ≤ C₁ := AS76b.oddCoreIn_le C₁
  have hR₃F : R₃ ≤ Fs := hR₃C₁.trans inf_le_left
  have hR₃Q : R₃ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := hR₃C₁.trans inf_le_right
  have hFR : Fs ≤ normalizer (R₃ : Set G) := fun f hf =>
    AS76b.normalizer_le_normalizer_oddCoreIn C₁ (mem_normalizer_inf (le_normalizer hf)
      (AS81.mem_normalizer_centralizer (H.F_le_N hf)))
  set C₃ := Fs ⊓ centralizer (R₃ : Set G) with hC₃
  have hFC₃ : Fs ≤ normalizer (C₃ : Set G) := fun f hf =>
    mem_normalizer_inf (le_normalizer hf) (AS81.mem_normalizer_centralizer (hFR hf))
  have hB₀C₃ : B₀ ≤ C₃ := fun b hb => mem_inf.mpr ⟨H.B₀_le_F hb,
    mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hOB (H.oddCoreIn_CF_le hr)) b hb).symm⟩
  set Ω := omegaGroup H.xsub.q H.xsub.q_nondegenerate with hΩdef
  set K := (C₃.subgroupOf Fs).map H.ρF with hK
  have hKΩ : K ≤ Ω := by
    rintro _ ⟨f, -, rfl⟩
    exact H.ρF_mem_omega f
  have hsimple : IsSimpleGroup ↥Ω :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le H.xsub.q_nondegenerate
      (by rw [H.finrank_Qt]; norm_num)
  have hKn : (K.subgroupOf Ω).Normal := by
    refine ⟨fun k hk ω => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    obtain ⟨f, hf⟩ := H.exists_F_of_omega hΩ ω.2
    obtain ⟨c, hc, hck⟩ := hk
    have hc' : (c : G) ∈ C₃ := hc
    refine ⟨f * c * f⁻¹, ?_, ?_⟩
    · show ((f * c * f⁻¹ : ↥Fs) : G) ∈ C₃
      exact (mem_normalizer_iff.mp (hFC₃ f.2) c).mp hc'
    · rw [map_mul, map_mul, map_inv, hf, hck]
      rfl
  have hΩK : Ω ≤ K := by
    rcases hKn.eq_bot_or_eq_top with h | h
    · exfalso
      have hle : H.ρB₀ ≤ K := by
        rintro _ ⟨b, rfl⟩
        exact ⟨⟨b, H.B₀_le_F b.2⟩, mem_subgroupOf.mpr (hB₀C₃ b.2), rfl⟩
      have hbot : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        have hk' : (⟨k, hKΩ hk⟩ : ↥Ω) ∈ K.subgroupOf Ω := mem_subgroupOf.mpr hk
        rw [h, mem_bot] at hk'
        rw [mem_bot]
        exact congrArg Subtype.val hk'
      have hle' : H.ρB₀ ≤ ⊥ := hbot ▸ hle
      have hc := H.card_ρB₀
      rw [le_bot_iff.mp hle', card_bot] at hc
      norm_num at hc
    · intro k hk
      have hk' : (⟨k, hk⟩ : ↥Ω) ∈ K.subgroupOf Ω := by rw [h]; exact mem_top _
      exact mem_subgroupOf.mp hk'
  have hQ₁R : Q₀ ⊔ Q ≤ normalizer (R₃ : Set G) := fun w hw =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hR₃Q hr) w hw).symm)
  have hdec : ∀ f ∈ Fs, ∃ c ∈ C₃, ∃ r ∈ R₃, f = c * r := by
    intro f hf
    obtain ⟨c', hc'', hc'f⟩ := hΩK (H.ρF_mem_omega ⟨f, hf⟩)
    have hc' : (c' : G) ∈ C₃ := hc''
    have hker : c'⁻¹ * ⟨f, hf⟩ ∈ H.ρF.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc'f, inv_mul_cancel]
    rw [H.ker_ρF hQF, mem_subgroupOf] at hker
    have hset : (((Q₀ ⊔ Q) ⊔ R₃ : Subgroup G) : Set G) =
        ((Q₀ ⊔ Q : Subgroup G) : Set G) * (R₃ : Set G) :=
      coe_mul_of_left_le_normalizer_right _ _ hQ₁R
    have hmem : ((c'⁻¹ * ⟨f, hf⟩ : ↥Fs) : G) ∈ (((Q₀ ⊔ Q) ⊔ R₃ : Subgroup G) : Set G) := hker
    rw [hset, Set.mem_mul] at hmem
    obtain ⟨w, hw, r, hr, hwr⟩ := hmem
    have hwC : w ∈ C₃ := mem_inf.mpr ⟨hQF hw, mem_centralizer_iff.mpr fun r' hr' =>
      (mem_centralizer_iff.mp (hR₃Q hr') w hw).symm⟩
    refine ⟨(c' : G) * w, mul_mem hc' hwC, r, hr, ?_⟩
    have e : (c'⁻¹ : G) * f = w * r := by
      rw [hwr]
      rfl
    calc f = (c' : G) * ((c'⁻¹ : G) * f) := by group
      _ = (c' : G) * w * r := by rw [e, mul_assoc]
  have : Group.IsSolvable ↥R₃ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (AS76b.odd_card_oddCoreIn C₁)
  have hle := Sec3SHat.le_of_perfect F_perfect inf_le_left hFC₃ hR₃F hdec
  intro r hr
  exact mem_centralizer_iff.mpr fun f hf => (mem_centralizer_iff.mp (hle hf).2 r hr).symm

theorem U_le_SHat (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) :
    (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) ≤ sec3SHat (Q₀ ⊔ Q) Zs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_inf_right _ hQF)
    (fun c hc => mem_normalizer_inf (H.F_le_N hc.1) (le_normalizer hc.2)) ?_
  exact (IsPGroup.of_card (n := 9) H.card).to_le inf_le_left

theorem exists_mul_of_ρF_eq_one (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q)
    {c : ↥(sec3F (Q₀ ⊔ Q))} (hcZ : (c : G) ∈ centralizer (Zs : Set G)) (hc : H.ρF c = 1) :
    ∃ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), ∃ r ∈ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
      centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)), (c : G) = u * r := by
  set R₃ := AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))
    with hR₃
  have hR₃Q : R₃ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    (AS76b.oddCoreIn_le _).trans inf_le_right
  have hQ₁R : Q₀ ⊔ Q ≤ normalizer (R₃ : Set G) := fun w hw =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hR₃Q hr) w hw).symm)
  have hker : c ∈ H.ρF.ker := hc
  rw [H.ker_ρF hQF, mem_subgroupOf] at hker
  have hmem : (c : G) ∈ (((Q₀ ⊔ Q) ⊔ R₃ : Subgroup G) : Set G) := hker
  rw [coe_mul_of_left_le_normalizer_right _ _ hQ₁R, Set.mem_mul] at hmem
  obtain ⟨w, hw, r, hr, hwr⟩ := hmem
  refine ⟨w, mem_inf.mpr ⟨hw, ?_⟩, r, hr, hwr.symm⟩
  have hrZ : r ∈ centralizer (Zs : Set G) :=
    Subgroup.centralizer_le (hZQ.trans H.Q_le) (hR₃Q hr)
  have e : w = (c : G) * r⁻¹ := by rw [← hwr]; group
  rw [e]
  exact mul_mem hcZ (inv_mem hrZ)

theorem mem_U_of_mem_SHat (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q)
    {s : ↥(sec3F (Q₀ ⊔ Q))} (hs : (s : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs) (h1 : H.ρF s = 1) :
    (s : G) ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC := CFSG.LieType.BorelTits.pCoreOf_le 2 (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
  have hS2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
  obtain ⟨u, hu, r, hr, hur⟩ := H.exists_mul_of_ρF_eq_one hQF hZQ (hSC hs).2 h1
  have hrS : r ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
    have e : r = u⁻¹ * s := by rw [hur]; group
    rw [e]
    exact mul_mem (inv_mem (H.U_le_SHat hQF hu)) hs
  have hr1 : r = 1 := by
    have h : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ⊓
        sec3SHat (Q₀ ⊔ Q) Zs = ⊥ := AS76b.oddCoreIn_inf_eq_bot hS2
    have hmem : r ∈ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
        centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ⊓ sec3SHat (Q₀ ⊔ Q) Zs :=
      mem_inf.mpr ⟨hr, hrS⟩
    rw [h] at hmem
    exact hmem
  rw [hur, hr1, mul_one]
  exact hu

theorem ρF_mem_pointRadical (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) {s : ↥(sec3F (Q₀ ⊔ Q))} (hs : (s : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    H.ρF s ∈ pointRadical H.xsub.q (H.xsub.cl z₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hC
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hS
  have hSC : S ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hCS : C ≤ normalizer (S : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  obtain ⟨b, hb⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero H.xsub.q_nondegenerate
    (H.cl_ne_zero hZQ hz₂ hz₂z)
  have hab : polar H.xsub.q (H.xsub.cl z₂) b = 1 :=
    CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero hb
  have hle := AS81.PointIrr.le_pointRadical_of_isPGroup H.xsub.q_nondegenerate
    (by rw [H.finrank_Qt]) hab (P := (S.subgroupOf (sec3F (Q₀ ⊔ Q))).map H.ρF)
    ((hS2.comap_subtype (K := sec3F (Q₀ ⊔ Q))).map H.ρF)
    (by rintro _ ⟨f, -, rfl⟩; exact (H.xsub.ρ _).2)
    (by rintro _ ⟨f, hf, rfl⟩; exact H.ρG_cl_z₂ hZQ hz₂ (hSC (mem_subgroupOf.mp hf)).2)
    (by
      rintro w hw _ ⟨f, hf, rfl⟩
      obtain ⟨f₀, hf₀⟩ := H.exists_F_of_omega hΩ hw.1
      have hwa : w (H.xsub.cl z₂) = H.xsub.cl z₂ := hw.2 _ (Submodule.subset_span (by simp))
      obtain ⟨f', hf'C, hf'⟩ := H.exists_mem_centralizer_of_apply hQF hZQ hz₂ hz₂z f₀
        (by rw [hf₀]; exact hwa)
      refine ⟨f' * f * f'⁻¹, ?_, ?_⟩
      · exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hCS (mem_inf.mpr ⟨f'.2, hf'C⟩)) f).mp
          (mem_subgroupOf.mp hf))
      · rw [map_mul, map_mul, map_inv, hf', hf₀])
  exact hle ⟨s, mem_subgroupOf.mpr hs, rfl⟩

theorem commutator_mem_Zs_of_mem_U
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) {s u : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) : s * u * s⁻¹ * u⁻¹ ∈ Zs := by
  have hsF : s ∈ sec3F (Q₀ ⊔ Q) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) hs).1
  have ht := H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z (s := ⟨s, hsF⟩) hs
  have huQ : u ∈ H.xsub.Q₁ := hu.1
  have hu' := hu
  rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z] at hu'
  have hpol : polar H.xsub.q (H.xsub.cl z₂) (H.xsub.cl u) = 0 :=
    (mem_perp.mp hu'.2) _ (Submodule.mem_span_singleton_self _)
  have h1 := ht.2.2.1 (H.xsub.cl u) hpol
  have hsN := H.F_le_N hsF
  have hsu : s * u * s⁻¹ ∈ H.xsub.Q₁ := H.xsub.conj_mem hsN huQ
  rw [H.Zs_eq_clPre hZQ hz₂ hz₂z]
  refine ⟨mul_mem hsu (inv_mem huQ), ?_⟩
  have e : H.xsub.cl (s * u * s⁻¹ * u⁻¹) =
      H.ρF ⟨s, hsF⟩ (H.xsub.cl u) - H.xsub.cl u := by
    rw [H.xsub.cl_mul hsu (inv_mem huQ), H.xsub.cl_inv huQ,
      show H.ρF ⟨s, hsF⟩ (H.xsub.cl u) = H.xsub.cl (s * u * s⁻¹) from H.ρG_cl _ huQ,
      sub_eq_add_neg, ZModModule.neg_eq_self]
  rw [e]
  exact h1

theorem exists_mem_SHat_of_mem_pointRadical
    (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z)
    {t : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt} (ht : t ∈ pointRadical H.xsub.q (H.xsub.cl z₂)) :
    ∃ s : ↥(sec3F (Q₀ ⊔ Q)), (s : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧ H.ρF s = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Fs := sec3F (Q₀ ⊔ Q) with hFs
  set C := Fs ⊓ centralizer (Zs : Set G) with hC
  set R₃ := AS76b.oddCoreIn (Fs ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) with hR₃
  set a := H.xsub.cl z₂ with ha
  have ha0 : a ≠ 0 := H.cl_ne_zero hZQ hz₂ hz₂z
  have haq : H.xsub.q a = 0 := H.q_cl_eq_zero hZQ hz₂
  have hR₃F : R₃ ≤ Fs := (AS76b.oddCoreIn_le _).trans inf_le_left
  have hR₃Q : R₃ ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    (AS76b.oddCoreIn_le _).trans inf_le_right
  have hR₃Z : R₃ ≤ centralizer (Zs : Set G) := fun r hr =>
    Subgroup.centralizer_le (hZQ.trans H.Q_le) (hR₃Q hr)
  have hρR : ∀ r (hr : r ∈ R₃), H.ρF ⟨r, hR₃F hr⟩ = 1 := fun r hr =>
    (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem_centralizer (hR₃Q hr))
  set Ph : Subgroup G := ((pointRadical H.xsub.q a).comap H.ρF).map Fs.subtype ⊓
    centralizer (Zs : Set G) with hPh
  have hmemP : ∀ {c : G} (hc : c ∈ Fs), c ∈ centralizer (Zs : Set G) →
      H.ρF ⟨c, hc⟩ ∈ pointRadical H.xsub.q a → c ∈ Ph := fun hc hcZ hct =>
    mem_inf.mpr ⟨⟨⟨_, hc⟩, hct, rfl⟩, hcZ⟩
  have hPhmem : ∀ {c : G}, c ∈ Ph → ∃ hc : c ∈ Fs, H.ρF ⟨c, hc⟩ ∈ pointRadical H.xsub.q a ∧
      c ∈ centralizer (Zs : Set G) := by
    rintro c ⟨⟨f, hf, rfl⟩, hcZ⟩
    exact ⟨f.2, hf, hcZ⟩
  have hPhC : Ph ≤ C := fun c hc => by
    obtain ⟨hcF, -, hcZ⟩ := hPhmem hc
    exact mem_inf.mpr ⟨hcF, hcZ⟩
  have hCPh : C ≤ normalizer (Ph : Set G) := by
    intro c hc
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hpF, hpt, hpZ⟩ := hPhmem hp
    have hcF : c ∈ Fs := hc.1
    have hcZ : c ∈ centralizer (Zs : Set G) := hc.2
    show c * p * c⁻¹ ∈ Ph
    have hcp : c * p * c⁻¹ ∈ Fs := mul_mem (mul_mem hcF hpF) (inv_mem hcF)
    refine hmemP hcp (mul_mem (mul_mem hcZ hpZ) (inv_mem hcZ)) ?_
    have e : H.ρF ⟨c * p * c⁻¹, hcp⟩ =
        H.ρF ⟨c, hcF⟩ * H.ρF ⟨p, hpF⟩ * (H.ρF ⟨c, hcF⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact Sec3SHat.conj_mem_pointRadical (H.xsub.ρ _).2 (H.ρG_cl_z₂ hZQ hz₂ hcZ) hpt
  have hpow : ∀ c ∈ Ph, c ^ (2 ^ 10) ∈ R₃ := by
    intro c hc
    obtain ⟨hcF, hct, hcZ⟩ := hPhmem hc
    have hc2F : c * c ∈ Fs := mul_mem hcF hcF
    have h1 : H.ρF ⟨c * c, hc2F⟩ = 1 := by
      have e : (⟨c * c, hc2F⟩ : ↥Fs) = ⟨c, hcF⟩ * ⟨c, hcF⟩ := rfl
      rw [e, map_mul]
      exact Sec3SHat.mul_self_of_mem_pointRadical H.xsub.q_nondegenerate ha0 haq hct
    obtain ⟨u, hu, r, hr, hur⟩ := H.exists_mul_of_ρF_eq_one hQF hZQ
      (c := ⟨c * c, hc2F⟩) (mul_mem hcZ hcZ) h1
    have hu9 : u ^ (2 ^ 9) = 1 := by
      have h := pow_card_eq_one' (G := ↥(Q₀ ⊔ Q)) (x := ⟨u, hu.1⟩)
      rw [H.card] at h
      exact congrArg Subtype.val h
    have hcomm : Commute u r := mem_centralizer_iff.mp (hR₃Q hr) u hu.1
    have e : c ^ (2 ^ 10) = (c * c) ^ (2 ^ 9) := by
      rw [← pow_two, ← pow_mul]
      norm_num
    rw [e, show c * c = u * r from hur, hcomm.mul_pow, hu9, one_mul]
    exact pow_mem hr _
  set R' : Subgroup ↥Ph := R₃.subgroupOf Ph with hR'
  have hR₃Ph : R₃ ≤ Ph := fun r hr =>
    hmemP (hR₃F hr) (hR₃Z hr) (by rw [hρR r hr]; exact one_mem _)
  have hR'c : R' ≤ center ↥Ph := by
    intro r hr
    rw [mem_subgroupOf] at hr
    refine mem_center_iff.mpr fun p => Subtype.ext ?_
    exact mem_centralizer_iff.mp (hRc hr) p (hPhC p.2).1
  have hR'n : R'.Normal := ⟨fun r hr p => by
    rw [mem_center_iff.mp (hR'c hr) p, mul_inv_cancel_right]
    exact hr⟩
  have hquot : IsPGroup 2 (↥Ph ⧸ R') := by
    intro w
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective R' w
    refine ⟨10, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf,
      Subgroup.coe_pow]
    exact hpow p p.2
  have : Group.IsNilpotent (↥Ph ⧸ R') := hquot.isNilpotent
  have : Group.IsNilpotent ↥Ph := Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' R')
    (by rw [QuotientGroup.ker_mk']; exact hR'c)
  let T : Sylow 2 ↥Ph := default
  have hTn : (T : Subgroup ↥Ph).Normal := inferInstance
  have hTc : (T : Subgroup ↥Ph).Characteristic := Sylow.characteristic_of_normal T hTn
  have hTS : (T : Subgroup ↥Ph).map Ph.subtype ≤ sec3SHat (Q₀ ⊔ Q) Zs :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((map_subtype_le _).trans hPhC)
      (fun c hc => CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (T : Subgroup ↥Ph) (hCPh hc)) (T.isPGroup'.map _)
  have hTall : ∀ p : ↥Ph, ∀ n : ℕ, p ^ 2 ^ n = 1 → p ∈ (T : Subgroup ↥Ph) := by
    intro p n hn
    obtain ⟨T', hT'⟩ := (AS76b.isPGroup_zpowers_of_pow_eq_one hn).exists_le_sylow
    have : Unique (Sylow 2 ↥Ph) := Sylow.unique_of_normal T hTn
    rw [Subsingleton.elim T' T] at hT'
    exact hT' (mem_zpowers p)
  obtain ⟨f₀, hf₀⟩ := H.exists_F_of_omega hΩ
    (CFSG.LargeExtraspecial.S2.pointRadical_le_omegaGroup H.xsub.q_nondegenerate ha0 haq ht)
  obtain ⟨c, hcZ, hc⟩ := H.exists_mem_centralizer_of_apply hQF hZQ hz₂ hz₂z f₀
    (by rw [hf₀]; exact ht.2.1)
  rw [hf₀] at hc
  have hcP : (c : G) ∈ Ph := hmemP c.2 hcZ (by rw [hc]; exact ht)
  set m := Nat.card ↥R₃ with hm
  have hcop : Nat.Coprime (2 ^ 10) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (AS76b.odd_card_oddCoreIn _))
  have hbez : ((2 ^ 10 : ℕ) : ℤ) * Nat.gcdA (2 ^ 10) m + (m : ℤ) * Nat.gcdB (2 ^ 10) m = 1 := by
    have h := Nat.gcd_eq_gcd_ab (2 ^ 10) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  set α := Nat.gcdA (2 ^ 10) m with hα
  set β := Nat.gcdB (2 ^ 10) m with hβ
  set e : ↥Fs := c ^ ((m : ℤ) * β) with he
  have hc2 : ((c ^ (2 ^ 10 : ℕ) : ↥Fs) : G) ∈ R₃ := by
    rw [Subgroup.coe_pow]
    exact hpow _ hcP
  have hdec : c = (c ^ (2 ^ 10 : ℕ)) ^ α * e := by
    rw [he, ← zpow_natCast, ← zpow_mul, ← zpow_add, hbez, zpow_one]
  have hρα : H.ρF ((c ^ (2 ^ 10 : ℕ)) ^ α) = 1 := by
    have hmem : (((c ^ (2 ^ 10 : ℕ)) ^ α : ↥Fs) : G) ∈ R₃ := by
      rw [Subgroup.coe_zpow]
      exact zpow_mem hc2 _
    exact hρR _ hmem
  have hρe : H.ρF e = t := by
    have h1 : H.ρF c = H.ρF ((c ^ (2 ^ 10 : ℕ)) ^ α) * H.ρF e := by
      rw [← map_mul, ← hdec]
    rw [hρα, one_mul, hc] at h1
    exact h1.symm
  have he2 : e ^ (2 ^ 10 : ℕ) = 1 := by
    have h1 : e ^ (2 ^ 10 : ℕ) = ((c ^ (2 ^ 10 : ℕ)) ^ m) ^ β := by
      simp only [he, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    have h2 : (c ^ (2 ^ 10 : ℕ)) ^ m = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact congrArg Subtype.val (pow_card_eq_one' (G := ↥R₃) (x := ⟨_, hc2⟩))
    rw [h1, h2, one_zpow]
  have heP : (e : G) ∈ Ph := by
    rw [he, Subgroup.coe_zpow]
    exact zpow_mem hcP _
  have heT : (⟨e, heP⟩ : ↥Ph) ∈ (T : Subgroup ↥Ph) := hTall _ 10 (Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg Subtype.val he2))
  exact ⟨e, hTS ⟨_, heT, rfl⟩, hρe⟩

theorem card_SHat (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q))
    (hRc : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (sec3F (Q₀ ⊔ Q) : Set G))
    (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    Nat.card ↥(sec3SHat (Q₀ ⊔ Q) Zs) = 2 ^ 14 := by
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hS
  have hSF : S ≤ sec3F (Q₀ ⊔ Q) := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  let ψ : ↥S →* (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) := H.ρF.comp (Subgroup.inclusion hSF)
  have hrange : ψ.range = pointRadical H.xsub.q (H.xsub.cl z₂) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z (s := Subgroup.inclusion hSF s) s.2
    · intro t ht
      obtain ⟨s, hsS, hst⟩ := H.exists_mem_SHat_of_mem_pointRadical hΩ hQF hRc hZQ hz₂ hz₂z ht
      exact ⟨⟨s, hsS⟩, hst⟩
  have hker : ψ.ker = ((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact H.mem_U_of_mem_SHat hQF hZQ (s := Subgroup.inclusion hSF s) s.2 h
    · intro h
      exact (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem h.1)
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrange, hker, card_pointRadical H.xsub.q_nondegenerate
    (H.cl_ne_zero hZQ hz₂ hz₂z) (H.q_cl_eq_zero hZQ hz₂), H.finrank_Qt] at h1
  rw [← h1, Nat.card_congr (subgroupOfEquivOfLe (H.U_le_SHat hQF)).toEquiv,
    H.card_U hZQ hz₂ hz₂z]
  norm_num

theorem commutator_SHat_le (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) :
    ⁅sec3SHat (Q₀ ⊔ Q) Zs, sec3SHat (Q₀ ⊔ Q) Zs⁆ ≤ Zs := by
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hS
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  have hSC : S ≤ sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSU : ⁅S, U'⁆ ≤ Zs := (Subgroup.commutator_le).mpr fun s hs u hu => by
    rw [commutatorElement_def]
    exact H.commutator_mem_Zs_of_mem_U hΩ hQF hZQ hz₂ hz₂z hs hu
  have hZS : ⁅Zs, S⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro w hw
    exact mem_centralizer_iff.mpr fun s hs => (mem_centralizer_iff.mp (hSC hs).2 w hw).symm
  have h1 : ⁅⁅S, U'⁆, S⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hSU le_rfl).trans hZS.le)
  have h2 : ⁅⁅U', S⁆, S⁆ = ⊥ := by rw [commutator_comm U' S]; exact h1
  have h3 : ⁅⁅S, S⁆, U'⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have hSSU : ⁅S, S⁆ ≤ U' := (Subgroup.commutator_le).mpr fun s hs t ht => by
    have hsF := (hSC hs).1
    have htF := (hSC ht).1
    have hcF : ⁅s, t⁆ ∈ sec3F (Q₀ ⊔ Q) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hsF htF) (inv_mem hsF)) (inv_mem htF)
    have hcS : ⁅s, t⁆ ∈ S := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hs ht) (inv_mem hs)) (inv_mem ht)
    refine H.mem_U_of_mem_SHat hQF hZQ (s := ⟨_, hcF⟩) hcS ?_
    have e : (⟨⁅s, t⁆, hcF⟩ : ↥(sec3F (Q₀ ⊔ Q))) =
        ⁅(⟨s, hsF⟩ : ↥(sec3F (Q₀ ⊔ Q))), ⟨t, htF⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Sec3SHat.comm_of_mem_pointRadical H.xsub.q_nondegenerate (H.cl_ne_zero hZQ hz₂ hz₂z)
      (H.q_cl_eq_zero hZQ hz₂) (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z hs)
      (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z ht)
  rw [← H.centerIn_U hZQ hz₂ hz₂z]
  intro c hc
  exact ⟨hSSU hc, (commutator_eq_bot_iff_le_centralizer.mp h3) hc⟩

theorem mul_self_mem_Zs (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) : s * s ∈ Zs := by
  have hSC : sec3SHat (Q₀ ⊔ Q) Zs ≤ sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hsF := (hSC hs).1
  have hssF : s * s ∈ sec3F (Q₀ ⊔ Q) := mul_mem hsF hsF
  have h1 : H.ρF ⟨s * s, hssF⟩ = 1 := by
    have e : (⟨s * s, hssF⟩ : ↥(sec3F (Q₀ ⊔ Q))) = ⟨s, hsF⟩ * ⟨s, hsF⟩ := rfl
    rw [e, map_mul]
    exact Sec3SHat.mul_self_of_mem_pointRadical H.xsub.q_nondegenerate
      (H.cl_ne_zero hZQ hz₂ hz₂z) (H.q_cl_eq_zero hZQ hz₂)
      (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z (s := ⟨s, hsF⟩) hs)
  have hssU := H.mem_U_of_mem_SHat hQF hZQ (s := ⟨s * s, hssF⟩) (mul_mem hs hs) h1
  rw [← H.centerIn_U hZQ hz₂ hz₂z]
  refine ⟨hssU, mem_centralizer_iff.mpr fun u hu => ?_⟩
  set c := s * u * s⁻¹ * u⁻¹ with hcdef
  have hcZ : c ∈ Zs := H.commutator_mem_Zs_of_mem_U hΩ hQF hZQ hz₂ hz₂z hs hu
  have h2 : s * u * s⁻¹ = c * u := by rw [hcdef]; group
  have hcs : c * s = s * c := mem_centralizer_iff.mp (hSC hs).2 c hcZ
  have hcc : c * c = 1 := by
    have h := H.sq_eq_one_of_mem_Zs hcZ
    rwa [pow_two] at h
  have h3 : (s * s) * u * (s * s)⁻¹ = u := by
    calc (s * s) * u * (s * s)⁻¹ = s * (s * u * s⁻¹) * s⁻¹ := by group
      _ = s * (c * u) * s⁻¹ := by rw [h2]
      _ = s * c * s⁻¹ * (s * u * s⁻¹) := by group
      _ = c * (c * u) := by rw [← hcs, mul_inv_cancel_right, h2]
      _ = u := by rw [← mul_assoc, hcc, one_mul]
  calc u * (s * s) = ((s * s) * u * (s * s)⁻¹) * (s * s) := by rw [h3]
    _ = (s * s) * u := by group

theorem centerIn_SHat (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
    (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q) {z₂ : G} (hz₂ : z₂ ∈ Zs)
    (hz₂z : z₂ ∉ zpowers z) : centerIn (sec3SHat (Q₀ ⊔ Q) Zs) = Zs := by
  have hSC : sec3SHat (Q₀ ⊔ Q) Zs ≤ sec3F (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hUS := H.U_le_SHat hQF
  have hZU : Zs ≤ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
    intro s hs
    have h : s ∈ centerIn ((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) := by
      rw [H.centerIn_U hZQ hz₂ hz₂z]
      exact hs
    exact h.1
  have ha0 := H.cl_ne_zero hZQ hz₂ hz₂z
  have haq := H.q_cl_eq_zero hZQ hz₂
  apply le_antisymm
  · rintro s ⟨hs, hsc⟩
    have hsF := (hSC hs).1
    obtain ⟨w, haw, hEw, happ⟩ := CFSG.LargeExtraspecial.pointRadical_apply_of_polar_eq_zero
      H.xsub.q_nondegenerate ha0 haq (H.ρF_mem_pointRadical hΩ hQF hZQ hz₂ hz₂z (s := ⟨s, hsF⟩) hs)
    have hw : w ∈ (ZMod 2) ∙ H.xsub.cl z₂ := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal H.xsub.q_nondegenerate
        (CFSG.LargeExtraspecial.OrthoF2.isRefl_polarBilin H.xsub.q) ((ZMod 2) ∙ H.xsub.cl z₂),
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      have hva : polar H.xsub.q (H.xsub.cl z₂) v = 0 :=
        CFSG.LargeExtraspecial.OrthoF2.mem_orthogonal_span_singleton_iff.mp hv
      obtain ⟨u, huQ, rfl⟩ := H.xsub.exists_cl v
      have huU : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
        rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z]
        refine ⟨huQ, mem_perp.mpr fun y hy => ?_⟩
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [polar_smul_left, hva, smul_zero]
      have hsu : s * u * s⁻¹ = u := by
        rw [← mem_centralizer_iff.mp hsc u (hUS huU), mul_inv_cancel_right]
      have h1 := happ _ hva
      rw [show H.ρF ⟨s, hsF⟩ (H.xsub.cl u) = H.xsub.cl (s * u * s⁻¹) from H.ρG_cl _ huQ, hsu,
        left_eq_add, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · rw [polarBilin_apply_apply, h1]
      · exact absurd h1 ha0
    have h1 : H.ρF ⟨s, hsF⟩ = 1 := by
      rw [hEw]
      exact (CFSG.LargeExtraspecial.eichler_eq_one_iff H.xsub.q_nondegenerate ha0 haq haw).mpr hw
    have hsU := H.mem_U_of_mem_SHat hQF hZQ (s := ⟨s, hsF⟩) hs h1
    rw [← H.centerIn_U hZQ hz₂ hz₂z]
    exact ⟨hsU, Subgroup.centralizer_le hUS hsc⟩
  · intro s hs
    refine ⟨hUS (hZU hs), mem_centralizer_iff.mpr fun t ht => ?_⟩
    exact (mem_centralizer_iff.mp (hSC ht).2 s hs).symm

end Sec38Hyp

end CFSG.ComponentClassification.AS81
