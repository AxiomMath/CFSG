module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5ActG
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitE8Generation
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085
public import Certificates.Certificate3085Base
public import Certificates.Certificate3170
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8052
public import Certificates.Certificate9310
public import Certificates.Certificate9314

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem twoPart_eq_of_quotient_equiv {A B : Subgroup G}
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) : twoPart A = twoPart B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : ∀ X : Subgroup G, (Nat.card X).factorization 2 =
      (Nat.card (X ⧸ pPrimeCore 2 X)).factorization 2 := by
    intro X
    have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 X) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 X),
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  rw [twoPart, twoPart, hf A, hf B, Nat.card_congr e.toEquiv]

omit [Finite G] in
theorem mem_centralizer_bot (x : G) : x ∈ centralizer ((⊥ : Subgroup G) : Set G) :=
  mem_centralizer_iff.mpr fun g hg => by
    rw [show g = 1 from mem_bot.mp hg, one_mul, mul_one]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem footeF_z : footeF L₀ z = L := eq_footeF h.sec4.huniq h.zL h.memF

theorem inf_footeF_eq {u : G} (huQ : u ∈ Q) (hu2 : orderOf u = 2)
    (huS : ∀ s ∈ S, s * u = u * s) : S ⊓ footeF L₀ u = S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := h.sec4
  have hu := h.repoint huQ hu2 huS
  have huC : u ∈ coreActionKernel L := h.Q_le huQ
  obtain ⟨hfix, hLu, -⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hu2 huC
  have hRLu : S ⊓ L ≤ footeF L₀ u := by
    intro r hr
    rw [← hfix, footeFixed]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_S) ⟨r, (mem_inf.mp hr).1⟩
    refine subset_closure ⟨mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp hr).2, ?_⟩), k, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (huS r (mem_inf.mp hr).1)
    · rwa [Subgroup.orderOf_mk] at hk
  have hLu' : IsTwoComponentAt u (footeFixed L u) := hfix ▸ hLu
  obtain ⟨φ, -, -⟩ := exists_quotient_mulEquiv_footeFixed h.zL hu2 huC hLu'
  have htwo : twoPart L = twoPart (footeF L₀ u) := by
    rw [← hfix]
    exact twoPart_eq_of_quotient_equiv φ
  refine (eq_of_le_of_card_ge (le_inf inf_le_left hRLu) ?_).symm
  rw [hu.R_sylow.card_eq, h.R_sylow.card_eq]
  exact htwo.symm.le

theorem hasDihedralSylowTwo_quotient :
    GorensteinWalter.HasDihedralSylowTwo (L ⧸ pPrimeCore 2 L) := by
  obtain ⟨-, ⟨e⟩⟩ := h.quotient_simple
  exact OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e
    (hasDihedralSylowTwo_of_footeFamilyType h.sec4.footeFamilyType)

theorem quotient_nonabelian : ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a :=
  exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent h.zL.2.1 h.zL.2.2)

theorem exists_dihedral_R : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥L →* L ⧸ pPrimeCore 2 L := QuotientGroup.mk' (pPrimeCore 2 L) with hψ
  obtain ⟨P, hP⟩ := h.R_sylow.exists_sylow_eq_subgroupOf
  obtain ⟨m, hm, ⟨e⟩⟩ := h.hasDihedralSylowTwo_quotient
    (P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 L)))
  have hinj : Function.Injective (ψ.comp (P : Subgroup L).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hψ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn] at hx
    have hxR : ((x : L) : G) ∈ S ⊓ L := by
      have h1 : (x : L) ∈ (S ⊓ L).subgroupOf L := hP ▸ x.2
      exact mem_subgroupOf.mp h1
    have h1 := eq_one_of_mem_of_odd h.R_sylow.isPGroup (odd_card_oddCoreIn L) hxR hx
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hrange : (ψ.comp (P : Subgroup L).subtype).range =
      ((P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 L)) : Sylow 2 _) :
        Subgroup (L ⧸ pPrimeCore 2 L)) := by
    rw [MonoidHom.range_comp, range_subtype, Sylow.coe_mapSurjective]
  refine ⟨m, hm, ⟨?_⟩⟩
  refine ((subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).symm.trans
    (MulEquiv.subgroupCongr hP.symm)).trans ?_
  exact ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans e

theorem isDihedralTwoGroup_R : AschbacherTheorem3.IsDihedralTwoGroup (S ⊓ L) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h.exists_dihedral_R
  exact ⟨m + 1, by omega, ⟨e⟩⟩

theorem center_R (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {c : G} (hc : c ∈ S ⊓ L)
    (hcZ : ∀ r ∈ S ⊓ L, c * r = r * c) : c = 1 ∨ c = t := by
  obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
  obtain ⟨c₀, -, hc₀⟩ := exists_center_of_dihedral e hna
  have ht1 : t ≠ 1 := fun h1 => by
    have h2 := h.t2
    rw [h1, orderOf_one] at h2
    omega
  rcases hc₀ t h.tR (fun r hr => (h.tZ r (mem_inf.mp hr).1).symm) with h1 | h1
  · exact absurd h1 ht1
  rcases hc₀ c hc hcZ with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (h2.trans h1.symm)

theorem exists_conj_t {r : G} (hr : r ∈ S ⊓ L) (hr2 : orderOf r = 2) :
    ∃ k ∈ L, k⁻¹ * r * k = t := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := h.quotient_simple.1
  obtain ⟨k, hkL, -, hk⟩ := exists_conj_of_involutions (W := ⊥) h.quotient_nonabelian
    h.hasDihedralSylowTwo_quotient IsPGroup.of_bot bot_le (mem_inf.mp hr).2 h.tL hr2 h.t2
    (mem_centralizer_bot r) (mem_centralizer_bot t)
  exact ⟨k, hkL, hk⟩

variable {𝕊 : Type} [Group 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)

abbrev Rbar : Sylow 2 𝕊 := sylowImage ε h.R_sylow

theorem mem_Rbar_iff {ρ : 𝕊} :
    ρ ∈ (h.Rbar ε : Subgroup 𝕊) ↔ ∃ r : ↥L, (r : G) ∈ S ⊓ L ∧ psi L ε r = ρ :=
  mem_sylowImage ε h.R_sylow

theorem psi_mem_Rbar {r : G} (hr : r ∈ S ⊓ L) :
    psi L ε ⟨r, (mem_inf.mp hr).2⟩ ∈ (h.Rbar ε : Subgroup 𝕊) :=
  (h.mem_Rbar_iff ε).mpr ⟨_, hr, rfl⟩

include ε in
theorem center_eq_bot : center 𝕊 = ⊥ := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := h.quotient_simple.1
  have hZ : center (L ⧸ pPrimeCore 2 L) = ⊥ := center_eq_bot_of_isSimpleGroup h.quotient_nonabelian
  rw [eq_bot_iff]
  intro c hc
  have h1 : ε.symm c ∈ center (L ⧸ pPrimeCore 2 L) := by
    rw [mem_center_iff] at hc ⊢
    intro g
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc (ε g)]
  rw [hZ, mem_bot] at h1
  rw [mem_bot]
  simpa using congrArg ε h1

theorem actG_eq_one_iff_mem_Q {s : G} (hs : s ∈ S) : actG L ε s = 1 ↔ s ∈ Q := by
  rw [actG_eq_one_iff ε (h.S_le hs)]
  constructor
  · intro hc
    rw [← h.inf_coreActionKernel]
    exact mem_inf.mpr ⟨hs, hc⟩
  · exact fun hq => h.Q_le hq

theorem actG_fix_iff {s : G} (hs : s ∈ S) :
    (∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε s ρ = ρ) ↔ ∀ r ∈ S ⊓ L, s * r = r * s := by
  have hsN := h.S_le hs
  constructor
  · intro hfix r hr
    have h1 := hfix _ (h.psi_mem_Rbar ε hr)
    rw [actG_psi ε hsN, psi_eq_iff] at h1
    have hmem : (s * r * s⁻¹)⁻¹ * r ∈ S ⊓ L :=
      mul_mem (inv_mem (h.conj_mem_R hs hr)) hr
    have h2 := eq_one_of_mem_of_odd h.R_sylow.isPGroup (odd_card_oddCoreIn L) hmem h1
    rw [inv_mul_eq_one] at h2
    calc s * r = (s * r * s⁻¹) * s := by group
      _ = r * s := by rw [h2]
  · intro hcomm ρ hρ
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    rw [actG_psi ε hsN]
    congr 1
    apply Subtype.ext
    change s * (r : G) * s⁻¹ = r
    rw [hcomm r hr]
    group

theorem actG_map_Rbar {s : G} (hs : s ∈ S) :
    (h.Rbar ε : Subgroup 𝕊).map (actG L ε s).toMonoidHom = h.Rbar ε := by
  have hsN := h.S_le hs
  ext ρ
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ'
    rw [MulEquiv.coe_toMonoidHom, actG_psi ε hsN]
    exact h.psi_mem_Rbar ε (h.conj_mem_R hs hr)
  · intro hρ
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    have hr' : s⁻¹ * (r : G) * s ∈ S ⊓ L := by
      have h1 := h.conj_mem_R (inv_mem hs) hr
      rwa [inv_inv] at h1
    refine ⟨_, h.psi_mem_Rbar ε hr', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, actG_psi ε hsN]
    congr 1
    apply Subtype.ext
    change s * (s⁻¹ * (r : G) * s) * s⁻¹ = r
    group

theorem exists_R_of_inner {s : G} (hs : s ∈ S) (hinn : actG L ε s ∈ innAut5 𝕊) :
    ∃ r ∈ S ⊓ L, actG L ε s = actG L ε r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := hinn
  have hZ := h.center_eq_bot ε
  have hinj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ center 𝕊 := by
      rw [mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut 𝕊 => φ g) hab
      simp only [MulAut.conj_apply] at h2
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = b⁻¹ * a * g := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  set P := (actImage L ε S).comap (MulAut.conj : 𝕊 →* MulAut 𝕊) with hPdef
  have hP2 : IsPGroup 2 P := (isPGroup_actImage ε h.isPGroup_S).comap_of_injective _ hinj
  have hRP : (h.Rbar ε : Subgroup 𝕊) ≤ P := by
    intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    rw [hPdef, mem_comap, ← actG_of_mem_self ε r.2]
    exact actG_mem_actImage ε h.S_le (mem_inf.mp hr).1
  have hPeq : P = h.Rbar ε := (h.Rbar ε).is_maximal' hP2 hRP
  have hcP : c ∈ P := by
    rw [hPdef, mem_comap, hc]
    exact actG_mem_actImage ε h.S_le hs
  rw [hPeq] at hcP
  obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hcP
  refine ⟨r, hr, ?_⟩
  rw [← hc, actG_of_mem_self ε r.2]

theorem exists_mul_of_inner {s : G} (hs : s ∈ S) (hinn : actG L ε s ∈ innAut5 𝕊) :
    ∃ q ∈ Q, ∃ r ∈ S ⊓ L, s = q * r := by
  obtain ⟨r, hr, hsr⟩ := h.exists_R_of_inner ε hs hinn
  have hrS := (mem_inf.mp hr).1
  have hq : s * r⁻¹ ∈ Q := by
    rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hs (inv_mem hrS)),
      actG_mul ε (h.S_le hs) (h.S_le (inv_mem hrS)), actG_inv ε (h.S_le hrS), hsr,
      mul_inv_cancel]
  exact ⟨s * r⁻¹, hq, r, hr, by group⟩

end Sec5

end CFSG.ComponentClassification.Foote5
