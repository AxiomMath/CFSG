module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L]

section Model

variable (D : LangDatum τ L) {Fr : L →+* L}

theorem torus_eq_twistedTorus (hΦ : D.Φ = Units.map (entrywiseHom Fr)) :
    D.torus = twistedTorusOf D.n (Units.map (entrywiseHom Fr)) := by
  show twistedTorusOf D.n D.Φ = _
  rw [hΦ]

theorem NFix_le_model (hΦ : D.Φ = Units.map (entrywiseHom Fr)) : NFix D.n Fr ≤ D.model := by
  intro y hy
  refine ⟨monomialSubgroup_le_adjointGroup' hy.1, ?_⟩
  have hf : negPhi Fr D.n y = y := hy.2
  rw [negPhi_apply] at hf
  change D.n * D.Φ y * D.n⁻¹ = y
  rw [hΦ]
  exact hf

theorem Γ_le_model' : D.Γ ≤ D.model := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem model_conj_mem_Γ {y g : ModGL τ L} (hy : y ∈ D.model) (hg : g ∈ D.Γ) :
    y * g * y⁻¹ ∈ D.Γ := by
  have hgM : g ∈ D.model := Γ_le_model' D hg
  have h := (commutator_subgroupOf_normal D.model).conj_mem ⟨g, hgM⟩
    (Subgroup.mem_subgroupOf.2 hg) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem commutator_mem_Γ {y₁ y₂ : ModGL τ L} (h₁ : y₁ ∈ D.model) (h₂ : y₂ ∈ D.model) :
    ⁅y₁, y₂⁆ ∈ D.Γ :=
  Subgroup.commutator_mem_commutator h₁ h₂

end Model

section Normalize

variable [IsAlgClosed L] (D : LangDatum τ L) {Fr : L →+* L} {p : ℕ} [Fact p.Prime]

theorem NFix_conj_mem_sylow (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {y : ModGL τ L}
    (hy : y ∈ NFix D.n Fr) {s : ModGL τ L} (hs : s ∈ (S₀ : Subgroup D.Γ).map D.Γ.subtype) :
    y * s * y⁻¹ ∈ (S₀ : Subgroup D.Γ).map D.Γ.subtype := by
  obtain ⟨s', hs'S, rfl⟩ := hs
  have hyM : y ∈ D.model := NFix_le_model D hΦ hy
  have hs'T : (s' : ModGL τ L) ∈ D.torus := Subgroup.mem_subgroupOf.1 (hS₀ hs'S)
  have hzT : y * (s' : ModGL τ L) * y⁻¹ ∈ D.torus := by
    rw [torus_eq_twistedTorus D hΦ] at hs'T ⊢
    exact NFix_conj_mem_twistedTorusOf hy hs'T
  have hzΓ : y * (s' : ModGL τ L) * y⁻¹ ∈ D.Γ := model_conj_mem_Γ D hyM s'.2
  set z : D.Γ := ⟨y * (s' : ModGL τ L) * y⁻¹, hzΓ⟩ with hz
  obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨s', hs'S⟩
  have hs'k : (s' : ModGL τ L) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using congrArg Subtype.val this
  have hzk : z ^ p ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hz]
    rw [conj_pow, hs'k]
    simp
  have hcomm : ∀ t ∈ (S₀ : Subgroup D.Γ), t * z = z * t := by
    intro t ht
    have htT : (t : ModGL τ L) ∈ D.torus := Subgroup.mem_subgroupOf.1 (hS₀ ht)
    apply Subtype.ext
    exact torusGroup_mul_comm htT.1 hzT.1
  exact ⟨z, mem_sylow_of_commute S₀ hzk hcomm, rfl⟩

theorem NFix_mem_normalizer (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {y : ModGL τ L}
    (hy : y ∈ NFix D.n Fr) :
    y ∈ Subgroup.normalizer (((S₀ : Subgroup D.Γ).map D.Γ.subtype : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => NFix_conj_mem_sylow D hΦ S₀ hS₀ hy hx, fun hx => ?_⟩
  have h := NFix_conj_mem_sylow D hΦ S₀ hS₀ ((NFix D.n Fr).inv_mem hy) hx
  simpa [mul_assoc] using h

end Normalize

section Engine

variable [IsAlgClosed L] (D : LangDatum τ L) {Fr : L →+* L} {q : ℕ} {p : ℕ} [Fact p.Prime]

theorem exists_nfix_lift (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {w : WeylGroup τ}
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) {a : WeylGroup τ}
    (ha : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ))) :
    ∃ y : NFix D.n Fr, NFixToWeyl D.n Fr y = a := by
  have hr := NFixToWeyl_range_eq_centralizer (L := L) Fr w hq hFr
  rw [← hn] at hr
  have : a ∈ (NFixToWeyl D.n Fr).range := by rw [hr]; exact ha
  exact this

theorem nfix_fpf_of_weyl (y : NFix D.n Fr) (v : WeylGroup τ) (hy : NFixToWeyl D.n Fr y = v)
    {S : Subgroup (ModGL τ L)} (hST : S ≤ D.torus)
    (hfpf : ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈ D.torus → rootDiagUnit τ β ^ p = 1 →
      weylTuple v β = β → rootDiagUnit τ β = 1) :
    ∀ x ∈ S, x ^ p = 1 → (y : ModGL τ L) * x * (y : ModGL τ L)⁻¹ = x → x = 1 := by
  intro x hxS hxp hxy
  have hxT : x ∈ D.torus := hST hxS
  obtain ⟨β, hβ⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT.1
  rw [hβ] at hxT hxp hxy ⊢
  rw [NFix_conj_rootDiagUnit y β, hy] at hxy
  exact hfpf β hxT hxp (rootDiagUnit_injective hxy)

theorem nfixToWeyl_dc (ya yb yc yd : NFix D.n Fr) :
    NFixToWeyl D.n Fr ⁅⁅ya, yb⁆, ⁅yc, yd⁆⁆ =
      ⁅⁅NFixToWeyl D.n Fr ya, NFixToWeyl D.n Fr yb⁆,
        ⁅NFixToWeyl D.n Fr yc, NFixToWeyl D.n Fr yd⁆⁆ := by
  simp only [map_commutatorElement]

theorem normalizerMovesLines_of_nfix_dc (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {a b c d : WeylGroup τ}
    (ha : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb : b ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc : c ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd : d ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈ D.torus → rootDiagUnit τ β ^ p = 1 →
      weylTuple ⁅⁅a, b⁆, ⁅c, d⁆⁆ β = β → rootDiagUnit τ β = 1) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  obtain ⟨ya, hya⟩ := exists_nfix_lift D hq hFr hn ha
  obtain ⟨yb, hyb⟩ := exists_nfix_lift D hq hFr hn hb
  obtain ⟨yc, hyc⟩ := exists_nfix_lift D hq hFr hn hc
  obtain ⟨yd, hyd⟩ := exists_nfix_lift D hq hFr hn hd
  intro A hAS hA
  set S : Subgroup (ModGL τ L) := (S₀ : Subgroup D.Γ).map D.Γ.subtype with hSdef
  have hSΓ : S ≤ D.Γ := Subgroup.map_subtype_le _
  have hST : S ≤ D.torus := by
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hS₀ hs)
  have hN : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ Subgroup.normalizer (S : Set (ModGL τ L)) :=
    fun y => NFix_mem_normalizer D hΦ S₀ hS₀ y.2
  have hM : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ D.model := fun y => NFix_le_model D hΦ y.2
  have hfp := nfix_fpf_of_weyl D ⁅⁅ya, yb⁆, ⁅yc, yd⁆⁆ ⁅⁅a, b⁆, ⁅c, d⁆⁆
    (by rw [nfixToWeyl_dc, hya, hyb, hyc, hyd]) hST hfpf
  have hAS' : A.map D.Γ.subtype ≤ S := Subgroup.map_mono hAS
  have hA' : Nat.card (A.map D.Γ.subtype) = p := by
    rw [Subgroup.card_map_of_injective D.Γ.subtype_injective, hA]
  obtain ⟨n, hnΓ, hnN, hmove⟩ := exists_dc_moves_line (Γ := D.Γ) (S := S) hSΓ hAS' hA'
    (hN ya) (hN yb) (hN yc) (hN yd)
    (commutator_mem_Γ D (hM ya) (hM yb)) (commutator_mem_Γ D (hM yc) (hM yd)) hfp
  exact exists_mem_normalizer_move_of_ambient hnΓ hnN hmove

theorem nfix_fpf_of_weyl2 (y₁ y₂ : NFix D.n Fr) (v₁ v₂ : WeylGroup τ)
    (hy₁ : NFixToWeyl D.n Fr y₁ = v₁) (hy₂ : NFixToWeyl D.n Fr y₂ = v₂)
    {S : Subgroup (ModGL τ L)} (hST : S ≤ D.torus)
    (hfpf : ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈ D.torus → rootDiagUnit τ β ^ p = 1 →
      weylTuple v₁ β = β → weylTuple v₂ β = β → rootDiagUnit τ β = 1) :
    ∀ x ∈ S, x ^ p = 1 → (y₁ : ModGL τ L) * x * (y₁ : ModGL τ L)⁻¹ = x →
      (y₂ : ModGL τ L) * x * (y₂ : ModGL τ L)⁻¹ = x → x = 1 := by
  intro x hxS hxp hx₁ hx₂
  have hxT : x ∈ D.torus := hST hxS
  obtain ⟨β, hβ⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT.1
  rw [hβ] at hxT hxp hx₁ hx₂ ⊢
  rw [NFix_conj_rootDiagUnit y₁ β, hy₁] at hx₁
  rw [NFix_conj_rootDiagUnit y₂ β, hy₂] at hx₂
  exact hfpf β hxT hxp (rootDiagUnit_injective hx₁) (rootDiagUnit_injective hx₂)

theorem normalizerMovesLines_of_nfix_dc2 (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ)
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : WeylGroup τ}
    (ha₁ : a₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb₁ : b₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc₁ : c₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd₁ : d₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (ha₂ : a₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb₂ : b₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd₂ : d₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈ D.torus → rootDiagUnit τ β ^ p = 1 →
      weylTuple ⁅⁅a₁, b₁⁆, ⁅c₁, d₁⁆⁆ β = β → weylTuple ⁅⁅a₂, b₂⁆, ⁅c₂, d₂⁆⁆ β = β →
        rootDiagUnit τ β = 1) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  obtain ⟨ya₁, hya₁⟩ := exists_nfix_lift D hq hFr hn ha₁
  obtain ⟨yb₁, hyb₁⟩ := exists_nfix_lift D hq hFr hn hb₁
  obtain ⟨yc₁, hyc₁⟩ := exists_nfix_lift D hq hFr hn hc₁
  obtain ⟨yd₁, hyd₁⟩ := exists_nfix_lift D hq hFr hn hd₁
  obtain ⟨ya₂, hya₂⟩ := exists_nfix_lift D hq hFr hn ha₂
  obtain ⟨yb₂, hyb₂⟩ := exists_nfix_lift D hq hFr hn hb₂
  obtain ⟨yc₂, hyc₂⟩ := exists_nfix_lift D hq hFr hn hc₂
  obtain ⟨yd₂, hyd₂⟩ := exists_nfix_lift D hq hFr hn hd₂
  intro A hAS hA
  set S : Subgroup (ModGL τ L) := (S₀ : Subgroup D.Γ).map D.Γ.subtype with hSdef
  have hSΓ : S ≤ D.Γ := Subgroup.map_subtype_le _
  have hST : S ≤ D.torus := by
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hS₀ hs)
  have hN : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ Subgroup.normalizer (S : Set (ModGL τ L)) :=
    fun y => NFix_mem_normalizer D hΦ S₀ hS₀ y.2
  have hM : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ D.model := fun y => NFix_le_model D hΦ y.2
  have hfp := nfix_fpf_of_weyl2 D ⁅⁅ya₁, yb₁⁆, ⁅yc₁, yd₁⁆⁆ ⁅⁅ya₂, yb₂⁆, ⁅yc₂, yd₂⁆⁆
    ⁅⁅a₁, b₁⁆, ⁅c₁, d₁⁆⁆ ⁅⁅a₂, b₂⁆, ⁅c₂, d₂⁆⁆
    (by rw [nfixToWeyl_dc, hya₁, hyb₁, hyc₁, hyd₁]) (by rw [nfixToWeyl_dc, hya₂, hyb₂, hyc₂, hyd₂])
    hST hfpf
  have hAS' : A.map D.Γ.subtype ≤ S := Subgroup.map_mono hAS
  have hA' : Nat.card (A.map D.Γ.subtype) = p := by
    rw [Subgroup.card_map_of_injective D.Γ.subtype_injective, hA]
  obtain ⟨n, hnΓ, hnN, hmove⟩ := exists_dc2_moves_line (Γ := D.Γ) (S := S) hSΓ hAS' hA'
    (hN ya₁) (hN yb₁) (hN yc₁) (hN yd₁) (hN ya₂) (hN yb₂) (hN yc₂) (hN yd₂)
    (commutator_mem_Γ D (hM ya₁) (hM yb₁)) (commutator_mem_Γ D (hM yc₁) (hM yd₁))
    (commutator_mem_Γ D (hM ya₂) (hM yb₂)) (commutator_mem_Γ D (hM yc₂) (hM yd₂)) hfp
  exact exists_mem_normalizer_move_of_ambient hnΓ hnN hmove

theorem normalizerMovesLines_of_nfix_c (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) (hMΓ : D.model ≤ D.Γ) {w : WeylGroup τ}
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) {a b : WeylGroup τ}
    (ha : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb : b ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈ D.torus → rootDiagUnit τ β ^ p = 1 →
      weylTuple ⁅a, b⁆ β = β → rootDiagUnit τ β = 1) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) := by
  obtain ⟨ya, hya⟩ := exists_nfix_lift D hq hFr hn ha
  obtain ⟨yb, hyb⟩ := exists_nfix_lift D hq hFr hn hb
  intro A hAS hA
  set S : Subgroup (ModGL τ L) := (S₀ : Subgroup D.Γ).map D.Γ.subtype with hSdef
  have hST : S ≤ D.torus := by
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hS₀ hs)
  have hN : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ Subgroup.normalizer (S : Set (ModGL τ L)) :=
    fun y => NFix_mem_normalizer D hΦ S₀ hS₀ y.2
  have hM : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ D.Γ := fun y => hMΓ (NFix_le_model D hΦ y.2)
  have hfp := nfix_fpf_of_weyl D ⁅ya, yb⁆ ⁅a, b⁆ (by simp only [map_commutatorElement, hya, hyb])
    hST hfpf
  have hAS' : A.map D.Γ.subtype ≤ S := Subgroup.map_mono hAS
  have hA' : Nat.card (A.map D.Γ.subtype) = p := by
    rw [Subgroup.card_map_of_injective D.Γ.subtype_injective, hA]
  obtain ⟨n, hnΓ, hnN, hmove⟩ := exists_c_moves_line (Γ := D.Γ) (S := S) hAS' hA'
    (hN ya) (hN yb) (hM ya) (hM yb) hfp
  exact exists_mem_normalizer_move_of_ambient hnΓ hnN hmove

end Engine

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
