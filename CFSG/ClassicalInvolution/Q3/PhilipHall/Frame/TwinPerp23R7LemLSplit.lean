module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E64Pres
public import Certificates.Certificate255001
public import Certificates.Certificate393003
public import Certificates.Certificate550841
public import Certificates.Certificate550871
public import Certificates.Certificate550872
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2ConjE64
import CFSG.ClassicalInvolution.Q3.Q3CPSix67
import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Q3.TL3T35
import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
import CFSG.ClassicalInvolution.Asc77.AscSixBasic
import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
import CFSG.ClassicalInvolution.Asc77.AscE187B2a
import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI
import CFSG.ClassicalInvolution.AschTight.Hall196Idx
import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusE6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Y
public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7S

local notation "𝕂" k:max => AE.memBar (E64P.memSet k) (E64P.memSet_card k) (E64P.memB k)

section Lift

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_le_isPGroup {N : Subgroup H} [N.Normal] {A₁ A₂ : Subgroup H}
    (hA₁ : IsPGroup 2 A₁) (hA₂ : IsPGroup 2 A₂) {T : Subgroup (H ⧸ N)} (hT : IsPGroup 2 T)
    (h₁ : A₁.map (QuotientGroup.mk' N) ≤ T) (h₂ : A₂.map (QuotientGroup.mk' N) ≤ T) :
    ∃ m ∈ N, ∃ P : Subgroup H, IsPGroup 2 P ∧ A₁ ≤ P ∧ conjSub m A₂ ≤ P := by
  have hA₁T : A₁ ≤ T.comap (QuotientGroup.mk' N) := fun a ha => h₁ ⟨a, ha, rfl⟩
  have hA₂T : A₂ ≤ T.comap (QuotientGroup.mk' N) := fun a ha => h₂ ⟨a, ha, rfl⟩
  obtain ⟨P, hP, hA₁P⟩ := IsSylow2In.exists_ge hA₁ hA₁T
  have hmap := Hall196.isSylow2In_map_hom (QuotientGroup.mk' N) hP
  have hTmap : (T.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = T :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) T
  rw [hTmap] at hmap
  have hPT : T = P.map (QuotientGroup.mk' N) := hmap.2.2 T le_rfl hT hmap.1
  obtain ⟨c, hcT, hA₂c⟩ := exists_conj_of_isSylow2In hP hA₂ hA₂T
  have hc : QuotientGroup.mk' N c ∈ P.map (QuotientGroup.mk' N) := by
    rw [← hPT]
    exact hcT
  obtain ⟨p, hpP, hpc⟩ := hc
  have hn : c * p⁻¹ ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hpc, mul_inv_cancel]
  refine ⟨(c * p⁻¹)⁻¹, N.inv_mem hn, P, hP.2.1, hA₁P, ?_⟩
  rw [conjSub_le_iff, inv_inv]
  have e : conjSub c P = conjSub (c * p⁻¹) P := by
    rw [conjSub_mul, conjSub_eq_self_of_mem (P.inv_mem hpP)]
  rw [← e]
  exact hA₂c

end Lift

section Sec

variable {G : Type} [Group G] [Finite G]

theorem card_secImage {X A : Subgroup G} (hAX : A ≤ X) (hA2 : IsPGroup 2 A) :
    Nat.card (secImage X A) = Nat.card A := by
  have hinj : Function.Injective ((F7I.piC X).comp (A.subgroupOf X).subtype) := by
    intro x y h
    exact Subtype.ext (F7I.piC_inj hA2 x.2 y.2 h)
  have hr : ((F7I.piC X).comp (A.subgroupOf X).subtype).range = secImage X A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]

theorem eq_secImage_of_map_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {X : Subgroup G}
    {Q : Type} [Group Q] (φ : SecQuot X →* Q) (hker : φ.ker ≤ Subgroup.center (SecQuot X))
    {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ RSet Ω) (hR₂ : R₂ ∈ RSet Ω) (hR₁X : R₁ ≤ X)
    (hR₂X : R₂ ≤ X) (hinj : ∀ x ∈ secImage X R₁, ∀ y ∈ secImage X R₁, φ x = φ y → x = y)
    (heq : (secImage X R₁).map φ = (secImage X R₂).map φ) :
    secImage X R₁ = secImage X R₂ := by
  have hcf : classicalInvolutionOddCore (SecQuot X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
  have hK2 : IsPGroup 2 φ.ker := (TL4.Vtx.isPGroup_center_of_oddFree hcf).to_le hker
  have hR₁2 : IsPGroup 2 R₁ := F7C.isPGroup_of_mem_RSet hR₁
  have hA₁ : IsPGroup 2 (R₁.subgroupOf X) := hR₁2.comap_subtype
  have hA₂ : IsPGroup 2 (R₂.subgroupOf X) := (F7C.isPGroup_of_mem_RSet hR₂).comap_subtype
  have hL₁2 : IsPGroup 2 (secImage X R₁) := hA₁.map _
  have hL₂T : secImage X R₂ ≤ secImage X R₁ ⊔ φ.ker := by
    intro y hy
    have hφy : φ y ∈ (secImage X R₁).map φ := by
      rw [heq]
      exact ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hφy
    have hk : x⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have e : y = x * (x⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hk)
  have hT2 : IsPGroup 2 (secImage X R₁ ⊔ φ.ker : Subgroup (SecQuot X)) :=
    IsPGroup.to_sup_of_normal_right' hL₁2 hK2 fun x _ => by
      rw [Subgroup.normalizer_eq_top]
      trivial
  obtain ⟨m, hm, P, hP2, hA₁P, hA₂P⟩ :=
    exists_conj_le_isPGroup (N := classicalInvolutionOddCore ↥X) hA₁ hA₂ hT2 le_sup_left hL₂T
  have hR₂'sub : (conjSub (m : G) R₂).subgroupOf X = conjSub m (R₂.subgroupOf X) :=
    (conjSub_subgroupOf X m R₂).symm
  have hR₂'X : conjSub (m : G) R₂ ≤ X := by
    have h := conjSub_mono (n := (m : G)) hR₂X
    rwa [conjSub_eq_self_of_mem m.2] at h
  have hR₂'R : conjSub (m : G) R₂ ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR₂ _
  have hP'2 : IsPGroup 2 (P.map X.subtype) := hP2.map _
  have hR₁P : R₁ ≤ P.map X.subtype := fun r hr =>
    ⟨⟨r, hR₁X hr⟩, hA₁P (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hR₂'P : conjSub (m : G) R₂ ≤ P.map X.subtype := by
    intro r hr
    refine ⟨⟨r, hR₂'X hr⟩, ?_, rfl⟩
    rw [← hR₂'sub] at hA₂P
    exact hA₂P (Subgroup.mem_subgroupOf.mpr hr)
  have hL₂' : secImage X (conjSub (m : G) R₂) = secImage X R₂ := by
    show ((conjSub (m : G) R₂).subgroupOf X).map _ = (R₂.subgroupOf X).map _
    rw [hR₂'sub]
    exact OddQuot.map_conjSub_of_mem hm _
  obtain ⟨S, hS⟩ := hP'2.exists_le_sylow
  by_cases hRR : R₁ = conjSub (m : G) R₂
  · rw [← hL₂', ← hRR]
  · exfalso
    have hc := Q3CP.l67Gen G Ω hΩ S R₁ hR₁ _ hR₂'R (hR₁P.trans hS) (hR₂'P.trans hS) hRR
    obtain ⟨a, ha, b, hb, hab⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₁).exists_not_commute
    have hxa : F7I.piC X ⟨a, hR₁X ha⟩ ∈ secImage X R₁ := F7I.mem_map_piC.mpr ⟨_, ha, rfl⟩
    have hxb : F7I.piC X ⟨b, hR₁X hb⟩ ∈ secImage X R₁ := F7I.mem_map_piC.mpr ⟨_, hb, rfl⟩
    have hφb : φ (F7I.piC X ⟨b, hR₁X hb⟩) ∈ (secImage X (conjSub (m : G) R₂)).map φ := by
      rw [hL₂', ← heq]
      exact ⟨_, hxb, rfl⟩
    obtain ⟨y, hy, hyb⟩ := hφb
    obtain ⟨c, hcR, rfl⟩ := F7I.mem_map_piC.mp hy
    have hcomm : F7I.piC X ⟨a, hR₁X ha⟩ * F7I.piC X c = F7I.piC X c * F7I.piC X ⟨a, hR₁X ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc a ha _ hcR)
    apply hab
    have h1 : F7I.piC X ⟨a, hR₁X ha⟩ * F7I.piC X ⟨b, hR₁X hb⟩ =
        F7I.piC X ⟨b, hR₁X hb⟩ * F7I.piC X ⟨a, hR₁X ha⟩ := by
      refine hinj _ ((secImage X R₁).mul_mem hxa hxb) _ ((secImage X R₁).mul_mem hxb hxa) ?_
      rw [map_mul, map_mul, ← hyb, ← map_mul φ (F7I.piC X ⟨a, hR₁X ha⟩) (F7I.piC X c), hcomm,
        map_mul]
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (F7I.piC_inj hR₁2 (R₁.mul_mem ha hb) (R₁.mul_mem hb ha) h1)

end Sec

section Univ

variable {Q : Type} [Group Q] [Finite Q] {ψ : Q →* AE.AEQ 7}

theorem injOn_of_map_eq_memBar {L : Subgroup Q} (h8 : Nat.card L = 8) {α : Finset (Fin 7)}
    {h : α.card = 4} {b : Bool} (hlab : L.map ψ = AE.memBar α h b) {x y : Q} (hx : x ∈ L)
    (hy : y ∈ L) (hxy : ψ x = ψ y) : x = y := by
  let f : ↥L → ↥(AE.memBar α h b) := fun l => ⟨ψ l, by rw [← hlab]; exact ⟨l, l.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    rw [← hlab] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    exact ⟨⟨l, hl⟩, rfl⟩
  have hcard : Nat.card ↥L ≤ Nat.card ↥(AE.memBar α h b) := by
    rw [AE.natCard_memBar (by norm_num), h8]
  have hinj := (hf.bijective_of_nat_card_le hcard).1
  exact congrArg Subtype.val (@hinj ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext hxy))

theorem map_eq_zBar {L : Subgroup Q} (h8 : Nat.card L = 8) {α : Finset (Fin 7)}
    {h : α.card = 4} {b : Bool} (hlab : L.map ψ = AE.memBar α h b) {z : Q} (hz : z ∈ L)
    (hz1 : z ≠ 1) (hzz : z * z = 1) : ψ z = AE.zBar α h := by
  have hmem : ψ z ∈ AE.memBar α h b := by
    rw [← hlab]
    exact ⟨z, hz, rfl⟩
  have hsq : ψ z * ψ z = 1 := by rw [← map_mul, hzz, map_one]
  rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hmem hsq with h1 | h1
  · exact absurd (injOn_of_map_eq_memBar h8 hlab hz L.one_mem (h1.trans (map_one ψ).symm)) hz1
  · exact h1

theorem map_conjSub (L : Subgroup Q) (q : Q) :
    (conjSub q L).map ψ = conjSub (ψ q) (L.map ψ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem conjSub_memBar_eq {w : AE.AEQ 7} {α β : Finset (Fin 7)} {h : α.card = 4}
    {h' : β.card = 4} {b c : Bool}
    (hle : ∀ x ∈ AE.memBar α h b, w * x * w⁻¹ ∈ AE.memBar β h' c) :
    conjSub w (AE.memBar α h b) = AE.memBar β h' c := by
  have hle' : conjSub w (AE.memBar α h b) ≤ AE.memBar β h' c := by
    rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  refine Subgroup.eq_of_le_of_card_ge hle' (le_of_eq ?_)
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj w).injective,
    AE.natCard_memBar (by norm_num), AE.natCard_memBar (by norm_num)]

theorem mkQ_mem_e64Sub {g : AE.Wr 7} (hg : g ∈ AE.aeSubOver AE.l32) : AE.mkQ 7 g ∈ AE.e64Sub :=
  ⟨g, hg, rfl⟩

theorem twin_of_pair {P : Set (Subgroup Q)} (hrange : ψ.range = AE.e64Sub)
    (h8 : ∀ L ∈ P, Nat.card L = 8)
    (hlab : ∀ L ∈ P, ∃ α ∈ AE.e64Sets, ∃ (h : α.card = 4) (b : Bool), L.map ψ = AE.memBar α h b)
    (huniq : ∀ L₁ ∈ P, ∀ L₂ ∈ P, L₁.map ψ = L₂.map ψ → L₁ = L₂)
    (hconj : ∀ L ∈ P, ∀ q : Q, conjSub q L ∈ P) {L₁ L₂ : Subgroup Q} (h₁ : L₁ ∈ P)
    (h₂ : L₂ ∈ P) (hcomm : Commutes L₁ L₂) {z : Q} (hz₁ : z ∈ L₁) (hz₂ : z ∈ L₂) (hz1 : z ≠ 1)
    (hzz : z * z = 1) {α : Finset (Fin 7)} (hα : α ∈ AE.e64Sets) (h : α.card = 4)
    {M₁ M₂ : Subgroup Q} (hM₁ : M₁ ∈ P) (hM₂ : M₂ ∈ P) (hl₁ : M₁.map ψ = AE.memBar α h true)
    (hl₂ : M₂.map ψ = AE.memBar α h false) : ∃ y ∈ M₁ ⊓ M₂, ψ y = AE.zBar α h := by
  have hcommI : ∀ {A B : Subgroup Q}, Commutes A B →
      ∀ x ∈ A.map ψ, ∀ y ∈ B.map ψ, x * y = y * x := by
    rintro A B hAB _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAB a ha b hb]
  obtain ⟨α₀, hα₀, h₀, b₀, hl₀⟩ := hlab L₁ h₁
  obtain ⟨g₁, hg₁, hc₁⟩ := TwinThinPf.member_conj α₀ hα₀ h₀ b₀
  obtain ⟨g₂, hg₂, hc₂⟩ := TwinThinPf.member_conj α hα h true
  have he₁ := conjSub_memBar_eq hc₁
  have he₂ := conjSub_memBar_eq hc₂
  have hw : conjSub (AE.mkQ 7 g₂ * (AE.mkQ 7 g₁)⁻¹) (AE.memBar α₀ h₀ b₀) =
      AE.memBar α h true := by
    rw [conjSub_mul, ← he₁, ← conjSub_mul (AE.mkQ 7 g₁)⁻¹, inv_mul_cancel, conjSub_one, he₂]
  have hwr : AE.mkQ 7 g₂ * (AE.mkQ 7 g₁)⁻¹ ∈ ψ.range := by
    rw [hrange]
    exact AE.e64Sub.mul_mem (mkQ_mem_e64Sub hg₂) (AE.e64Sub.inv_mem (mkQ_mem_e64Sub hg₁))
  obtain ⟨q, hq⟩ := hwr
  have hN₁ : (conjSub q L₁).map ψ = AE.memBar α h true := by
    rw [map_conjSub, hq, hl₀, hw]
  obtain ⟨β, -, h', c, hlc⟩ := hlab _ (hconj L₂ h₂ q)
  have hcq : Commutes (conjSub q L₁) (conjSub q L₂) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show q * x * q⁻¹ * (q * y * q⁻¹) = q * y * q⁻¹ * (q * x * q⁻¹)
    calc q * x * q⁻¹ * (q * y * q⁻¹) = q * (x * y) * q⁻¹ := by group
      _ = q * (y * x) * q⁻¹ := by rw [hcomm x hx y hy]
      _ = q * y * q⁻¹ * (q * x * q⁻¹) := by group
  have hcomm' := hcommI hcq
  rw [hN₁, hlc] at hcomm'
  obtain ⟨rfl, hc⟩ := LL1.twin_of_commute hcomm'
  have hcf : c = false := by
    cases c
    · rfl
    · exact absurd rfl hc
  subst hcf
  have hM₁N : M₁ = conjSub q L₁ := huniq M₁ hM₁ _ (hconj L₁ h₁ q) (hl₁.trans hN₁.symm)
  have hM₂N : M₂ = conjSub q L₂ := huniq M₂ hM₂ _ (hconj L₂ h₂ q) (hl₂.trans hlc.symm)
  have hzq₁ : q * z * q⁻¹ ∈ M₁ := by
    rw [hM₁N]
    exact conj_mem_conjSub hz₁
  have hzq₂ : q * z * q⁻¹ ∈ M₂ := by
    rw [hM₂N]
    exact conj_mem_conjSub hz₂
  refine ⟨q * z * q⁻¹, ⟨hzq₁, hzq₂⟩, map_eq_zBar (h8 M₁ hM₁) hl₁ hzq₁ ?_ ?_⟩
  · rwa [Ne, conj_eq_one_iff]
  · calc q * z * q⁻¹ * (q * z * q⁻¹) = q * (z * z) * q⁻¹ := by group
      _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]

end Univ

section Model

theorem memBar_congr {α β : Finset (Fin 7)} (hαβ : α = β) {hα : α.card = 4} {hβ : β.card = 4}
    {b : Bool} : AE.memBar α hα b = AE.memBar β hβ b := by
  subst hαβ
  rfl

theorem zBar_congr {α β : Finset (Fin 7)} (hαβ : α = β) {hα : α.card = 4} {hβ : β.card = 4} :
    AE.zBar α hα = AE.zBar β hβ := by
  subst hαβ
  rfl

theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

theorem comm_of_mem_closure_pair {M : Type} [Group M] {a b : M} (hab : a * b = b * a) {u v : M}
    (hu : u ∈ Subgroup.closure {a, b}) (hv : v ∈ Subgroup.closure {a, b}) : u * v = v * u := by
  have hs : ({a, b} : Set M).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have h := Subgroup.closure_le_centralizer_centralizer ({a, b} : Set M)
  exact Set.centralizer_centralizer_comm_of_comm hs _ (h hu) _ (h hv)

theorem sq_eq_zBar {α : Finset (Fin 7)} {h : α.card = 4} {b : Bool} {y : AE.AEQ 7}
    (hy : y ∈ AE.memBar α h b) (h4 : y ^ 4 = 1) (h2 : y ^ 2 ≠ 1) : y ^ 2 = AE.zBar α h := by
  have hsq : y ^ 2 * y ^ 2 = 1 := by
    rw [← pow_add]
    exact h4
  rcases AE.eq_of_mem_memBar_mul_self (by norm_num) ((AE.memBar α h b).pow_mem hy 2) hsq with
    h1 | h1
  · exact absurd h1 h2
  · exact h1

theorem modelGen_pow_four (g : Fin 28) : E64P.modelGen g ^ 4 = 1 := by
  rw [← E64P.orderOf_modelGen g]
  exact pow_orderOf_eq_one _

theorem modelGen_sq_ne (g : Fin 28) : E64P.modelGen g ^ 2 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by rw [E64P.orderOf_modelGen]; norm_num)

theorem modelGen_gIdx_mem {k l : ℕ} (hk : k < 14) (hl : l < 2) :
    E64P.modelGen (E64P.gIdx k l) ∈ 𝕂 ⟨k, hk⟩ := by
  have e : E64P.memOf (E64P.gIdx k l) = ⟨k, hk⟩ := E64P.memOf_gIdx ⟨k, hk⟩ hl
  have h := E64P.modelGen_mem_memBar (E64P.gIdx k l)
  rwa [e] at h

theorem modelGen_sq {k l : ℕ} (hk : k < 14) (hl : l < 2) :
    E64P.modelGen (E64P.gIdx k l) ^ 2 = AE.zBar (E64P.memSet ⟨k, hk⟩) (E64P.memSet_card _) :=
  sq_eq_zBar (modelGen_gIdx_mem hk hl) (modelGen_pow_four _) (modelGen_sq_ne _)

theorem word_mem {k : ℕ} (hk : k < 14) {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    (w.map fun l => E64P.modelGen (E64P.gIdx k l)).prod ∈ 𝕂 ⟨k, hk⟩ := by
  refine list_prod_mem fun y hy => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
  exact modelGen_gIdx_mem hk (hw l hl)

theorem memIdx_inj : ∀ i j : Fin 14, E64P.memSet i = E64P.memSet j →
    E64P.memB i = E64P.memB j → i = j := by
  decide +kernel

theorem memIdx_surj {α : Finset (Fin 7)} (hα : α ∈ AE.e64Sets) (b : Bool) :
    ∃ k : Fin 14, E64P.memSet k = α ∧ E64P.memB k = b := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  have key : ∀ ℓ ∈ AE.fanoLines, ∀ b : Bool,
      ∃ k : Fin 14, E64P.memSet k = ℓᶜ ∧ E64P.memB k = b := by
    decide +kernel
  exact key ℓ hℓ b

theorem twin_idx {ℓ : ℕ} (h₁ : 2 * ℓ < 14) (h₂ : 2 * ℓ + 1 < 14) :
    E64P.memSet ⟨2 * ℓ, h₁⟩ = E64P.memSet ⟨2 * ℓ + 1, h₂⟩ ∧ E64P.memB ⟨2 * ℓ, h₁⟩ = true ∧
      E64P.memB ⟨2 * ℓ + 1, h₂⟩ = false := by
  refine ⟨?_, ?_, ?_⟩
  · show (AE.fanoLines.getD (2 * ℓ / 2) ∅)ᶜ = (AE.fanoLines.getD ((2 * ℓ + 1) / 2) ∅)ᶜ
    rw [show 2 * ℓ / 2 = ℓ by omega, show (2 * ℓ + 1) / 2 = ℓ by omega]
  · show (2 * ℓ % 2 == 0) = true
    rw [show 2 * ℓ % 2 = 0 by omega]
    rfl
  · show ((2 * ℓ + 1) % 2 == 0) = false
    rw [show (2 * ℓ + 1) % 2 = 1 by omega]
    rfl


theorem conjRow_bounds {g k c k' : ℕ} {w : List ℕ} (hd : (g, k, c, k', w) ∈ E64P.conjRows) :
    g < 28 ∧ k < 14 ∧ c < 2 ∧ k' < 14 ∧ ∀ l ∈ w, l < 2 := by
  have h := E64P.rowsCheck_holds
  simp only [E64P.rowsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨i, hi, hid⟩ := List.getElem_of_mem hd
  have hi' : i < 784 := h.1 ▸ hi
  have hrow := h.2 i hi'
  rw [List.getElem?_eq_getElem hi, hid] at hrow
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hrow
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hrow
  exact ⟨by omega, by omega, by omega, h4, h5⟩

theorem model_q8 {k : ℕ} (hk : k < 14) :
    E64P.modelGen (E64P.gIdx k 1) * E64P.modelGen (E64P.gIdx k 0) *
      (E64P.modelGen (E64P.gIdx k 1))⁻¹ = (E64P.modelGen (E64P.gIdx k 0))⁻¹ := by
  have hr : [(E64P.gIdx k 1, true), (E64P.gIdx k 0, true), (E64P.gIdx k 1, false),
      (E64P.gIdx k 0, true)] ∈ E64P.e64MemberRels := by
    unfold E64P.e64MemberRels
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨k, List.mem_range.mpr hk, ?_⟩))
    simp [E64P.q8Rels]
  have h := E64P.lift_modelGen_rel hr
  simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false, mul_one] at h
  calc _ = E64P.modelGen (E64P.gIdx k 1) * (E64P.modelGen (E64P.gIdx k 0) *
        ((E64P.modelGen (E64P.gIdx k 1))⁻¹ * E64P.modelGen (E64P.gIdx k 0))) *
          (E64P.modelGen (E64P.gIdx k 0))⁻¹ := by group
    _ = _ := by rw [h, one_mul]

theorem conjSub_modelGen_pair {g k k₀ k₁ : ℕ} {w₀ w₁ : List ℕ}
    (h₀ : (g, k, 0, k₀, w₀) ∈ E64P.conjRows) (h₁ : (g, k, 1, k₁, w₁) ∈ E64P.conjRows)
    (hk : k < 14) (hk₀ : k₀ < 14) (hk₁ : k₁ < 14) (hw₀ : ∀ l ∈ w₀, l < 2)
    (hw₁ : ∀ l ∈ w₁, l < 2) :
    k₀ = k₁ ∧ conjSub (E64P.modelGen (Fin.ofNat 28 g)) (𝕂 ⟨k, hk⟩) = 𝕂 ⟨k₀, hk₀⟩ := by
  obtain ⟨G, hG⟩ : ∃ G, G = E64P.modelGen (Fin.ofNat 28 g) := ⟨_, rfl⟩
  rw [← hG]
  have e₀ := E64P.model_conj h₀
  have e₁ := E64P.model_conj h₁
  dsimp only at e₀ e₁
  have hy₀ : G * E64P.modelGen (E64P.gIdx k 0) * G⁻¹ ∈ 𝕂 ⟨k₀, hk₀⟩ := by
    rw [hG, e₀]
    exact word_mem hk₀ hw₀
  have hy₁ : G * E64P.modelGen (E64P.gIdx k 1) * G⁻¹ ∈ 𝕂 ⟨k₁, hk₁⟩ := by
    rw [hG, e₁]
    exact word_mem hk₁ hw₁
  have hsq : ∀ {c k' : ℕ} (hc : c < 2) (hk' : k' < 14),
      G * E64P.modelGen (E64P.gIdx k c) * G⁻¹ ∈ 𝕂 ⟨k', hk'⟩ →
        G * AE.zBar (E64P.memSet ⟨k, hk⟩) (E64P.memSet_card _) * G⁻¹ =
          AE.zBar (E64P.memSet ⟨k', hk'⟩) (E64P.memSet_card _) := by
    intro c k' hc hk' hy
    have h4 : (G * E64P.modelGen (E64P.gIdx k c) * G⁻¹) ^ 4 = 1 := by
      rw [conj_pow, modelGen_pow_four, mul_one, mul_inv_cancel]
    have h2 : (G * E64P.modelGen (E64P.gIdx k c) * G⁻¹) ^ 2 ≠ 1 := by
      rw [conj_pow, Ne, conj_eq_one_iff]
      exact modelGen_sq_ne _
    rw [← sq_eq_zBar hy h4 h2, conj_pow, modelGen_sq hk hc]
  have hz := (hsq (by norm_num) hk₀ hy₀).symm.trans (hsq (by norm_num) hk₁ hy₁)
  have hset : E64P.memSet ⟨k₀, hk₀⟩ = E64P.memSet ⟨k₁, hk₁⟩ := AE.eq_of_zBar_eq (by norm_num) hz
  have hb : E64P.memB ⟨k₀, hk₀⟩ = E64P.memB ⟨k₁, hk₁⟩ := by
    by_contra hne
    have hy₁' : G * E64P.modelGen (E64P.gIdx k 1) * G⁻¹ ∈
        AE.memBar (E64P.memSet ⟨k₀, hk₀⟩) (E64P.memSet_card _) (!E64P.memB ⟨k₀, hk₀⟩) := by
      rw [← bool_eq_not_of_ne hne,
        memBar_congr hset (hα := E64P.memSet_card _) (hβ := E64P.memSet_card _)]
      exact hy₁
    have hcomm := TC.Thin.memBar_twin_comm _ _ _ _ hy₀ _ hy₁'
    have hab : E64P.modelGen (E64P.gIdx k 0) * E64P.modelGen (E64P.gIdx k 1) =
        E64P.modelGen (E64P.gIdx k 1) * E64P.modelGen (E64P.gIdx k 0) := by
      calc _ = G⁻¹ * ((G * E64P.modelGen (E64P.gIdx k 0) * G⁻¹) *
            (G * E64P.modelGen (E64P.gIdx k 1) * G⁻¹)) * G := by group
        _ = G⁻¹ * ((G * E64P.modelGen (E64P.gIdx k 1) * G⁻¹) *
            (G * E64P.modelGen (E64P.gIdx k 0) * G⁻¹)) * G := by rw [hcomm]
        _ = _ := by group
    obtain ⟨a, ha, a', ha', hne'⟩ := AE.exists_not_comm_memBar (by norm_num)
      (E64P.memSet ⟨k, hk⟩) (E64P.memSet_card _) (E64P.memB ⟨k, hk⟩)
    rw [← E64P.closure_modelGen_pair ⟨k, hk⟩] at ha ha'
    exact hne' (comm_of_mem_closure_pair hab ha ha')
  have hkk : k₀ = k₁ := congrArg Fin.val (memIdx_inj _ _ hset hb)
  subst hkk
  refine ⟨rfl, ?_⟩
  have hle : conjSub G (𝕂 ⟨k, hk⟩) ≤ 𝕂 ⟨k₀, hk₀⟩ := by
    rw [← E64P.closure_modelGen_pair ⟨k, hk⟩, conjSub, MonoidHom.map_closure, Set.image_pair,
      Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hy₀
    · exact hy₁
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj G).injective,
    AE.natCard_memBar (by norm_num), AE.natCard_memBar (by norm_num)]

theorem conjSub_modelGen {g k c k' : ℕ} {w : List ℕ} (hd : (g, k, c, k', w) ∈ E64P.conjRows)
    (hk : k < 14) (hk' : k' < 14) :
    conjSub (E64P.modelGen (Fin.ofNat 28 g)) (𝕂 ⟨k, hk⟩) = 𝕂 ⟨k', hk'⟩ := by
  obtain ⟨hg, -, hc, -, hw⟩ := conjRow_bounds hd
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · obtain ⟨k₁, w₁, h₁, hk₁, hw₁⟩ := E64P.exists_conjRow hg hk (by norm_num : 1 < 2)
    exact (conjSub_modelGen_pair hd h₁ hk hk' hk₁ hw hw₁).2
  · obtain ⟨k₀, w₀, h₀, hk₀, hw₀⟩ := E64P.exists_conjRow hg hk (by norm_num : 0 < 2)
    obtain ⟨rfl, h⟩ := conjSub_modelGen_pair h₀ hd hk hk₀ hk' hw₀ hw
    exact h

end Model

section Pres

variable
  {Q : Type} [Group Q] [Finite Q] {ψ : Q →* AE.AEQ 7}

theorem injective_of_members {P : Set (Subgroup Q)} (hspan : (⨆ L ∈ P, L) = ⊤)
    (hrange : ψ.range = AE.e64Sub) (h8 : ∀ L ∈ P, Nat.card L = 8)
    (hlab : ∀ L ∈ P, ∃ α ∈ AE.e64Sets, ∃ (h : α.card = 4) (b : Bool), L.map ψ = AE.memBar α h b)
    (hsurj : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ P,
      L.map ψ = AE.memBar α h b)
    (huniq : ∀ L₁ ∈ P, ∀ L₂ ∈ P, L₁.map ψ = L₂.map ψ → L₁ = L₂)
    (hconj : ∀ L ∈ P, ∀ q : Q, conjSub q L ∈ P)
    (htwin : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4), ∀ M₁ ∈ P, ∀ M₂ ∈ P,
      M₁.map ψ = AE.memBar α h true → M₂.map ψ = AE.memBar α h false →
        ∃ y ∈ M₁ ⊓ M₂, ψ y = AE.zBar α h) :
    Function.Injective ψ := by
  have hL : ∀ k : Fin 14, ∃ L ∈ P, L.map ψ = 𝕂 k := fun k =>
    hsurj _ (E64P.memSet_mem k) (E64P.memSet_card k) (E64P.memB k)
  choose L hLP hLψ using hL
  have hinjL : ∀ (k : Fin 14) {u v : Q}, u ∈ L k → v ∈ L k → ψ u = ψ v → u = v := by
    intro k u v hu hv huv
    exact injOn_of_map_eq_memBar (h8 _ (hLP k)) (hLψ k) hu hv huv
  have hx : ∀ g : Fin 28, ∃ y ∈ L (E64P.memOf g), ψ y = E64P.modelGen g := by
    intro g
    have h := E64P.modelGen_mem_memBar g
    rw [← hLψ] at h
    obtain ⟨y, hy, hyg⟩ := h
    exact ⟨y, hy, hyg⟩
  choose x hxL hxψ using hx
  have hxk : ∀ {k : ℕ} (hk : k < 14) {l : ℕ}, l < 2 → x (E64P.gIdx k l) ∈ L ⟨k, hk⟩ := by
    intro k hk l hl
    have e : E64P.memOf (E64P.gIdx k l) = ⟨k, hk⟩ := E64P.memOf_gIdx ⟨k, hk⟩ hl
    have h := hxL (E64P.gIdx k l)
    rwa [e] at h
  have hψw : ∀ (k : ℕ) (w : List ℕ), ψ (w.map fun l => x (E64P.gIdx k l)).prod =
      (w.map fun l => E64P.modelGen (E64P.gIdx k l)).prod := by
    intro k w
    induction w with
    | nil => simp
    | cons l w ih => simp [ih, hxψ]
  have hq : ∀ k < 14, x (E64P.gIdx k 0) ^ 4 = 1 ∧
      x (E64P.gIdx k 0) ^ 2 = x (E64P.gIdx k 1) ^ 2 ∧
        x (E64P.gIdx k 1) * x (E64P.gIdx k 0) * (x (E64P.gIdx k 1))⁻¹ =
          (x (E64P.gIdx k 0))⁻¹ := by
    intro k hk
    have h0 := hxk hk (l := 0) (by norm_num)
    have h1 := hxk hk (l := 1) (by norm_num)
    refine ⟨hinjL _ ((L _).pow_mem h0 4) (L _).one_mem ?_,
      hinjL _ ((L _).pow_mem h0 2) ((L _).pow_mem h1 2) ?_,
      hinjL _ ((L _).mul_mem ((L _).mul_mem h1 h0) ((L _).inv_mem h1)) ((L _).inv_mem h0) ?_⟩
    · rw [map_pow, hxψ, map_one, modelGen_pow_four]
    · rw [map_pow, map_pow, hxψ, hxψ, modelGen_sq (l := 0) hk (by norm_num),
        modelGen_sq (l := 1) hk (by norm_num)]
    · rw [map_mul, map_mul, map_inv, map_inv, hxψ, hxψ]
      exact model_q8 hk
  have hc : ∀ d ∈ E64P.conjRows, x (Fin.ofNat 28 d.1) * x (E64P.gIdx d.2.1 d.2.2.1) *
      (x (Fin.ofNat 28 d.1))⁻¹ = (d.2.2.2.2.map fun l => x (E64P.gIdx d.2.2.2.1 l)).prod := by
    rintro ⟨g, k, c, k', w⟩ hd
    obtain ⟨-, hk, hc, hk', hw⟩ := conjRow_bounds hd
    dsimp only
    have hN : conjSub (x (Fin.ofNat 28 g)) (L ⟨k, hk⟩) = L ⟨k', hk'⟩ := by
      refine huniq _ (hconj _ (hLP _) _) _ (hLP _) ?_
      rw [map_conjSub, hxψ, hLψ, hLψ]
      exact conjSub_modelGen hd hk hk'
    have ha : x (Fin.ofNat 28 g) * x (E64P.gIdx k c) * (x (Fin.ofNat 28 g))⁻¹ ∈ L ⟨k', hk'⟩ := by
      rw [← hN]
      exact conj_mem_conjSub (hxk hk hc)
    have hb : (w.map fun l => x (E64P.gIdx k' l)).prod ∈ L ⟨k', hk'⟩ := by
      refine list_prod_mem fun y hy => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
      exact hxk hk' (hw l hl)
    refine hinjL _ ha hb ?_
    have hm := E64P.model_conj hd
    dsimp only at hm
    rw [map_mul, map_mul, map_inv, hxψ, hxψ, hψw, hm]
  have ht : ∀ ℓ < 7, x (E64P.gIdx (2 * ℓ) 0) ^ 2 = x (E64P.gIdx (2 * ℓ + 1) 0) ^ 2 := by
    intro ℓ hℓ
    have hk₁ : 2 * ℓ < 14 := by omega
    have hk₂ : 2 * ℓ + 1 < 14 := by omega
    obtain ⟨hset, hb₁, hb₂⟩ := twin_idx hk₁ hk₂
    have hl₁ : (L ⟨2 * ℓ, hk₁⟩).map ψ =
        AE.memBar (E64P.memSet ⟨2 * ℓ, hk₁⟩) (E64P.memSet_card _) true := by
      rw [hLψ, hb₁]
    have hl₂ : (L ⟨2 * ℓ + 1, hk₂⟩).map ψ =
        AE.memBar (E64P.memSet ⟨2 * ℓ, hk₁⟩) (E64P.memSet_card _) false := by
      rw [hLψ, hb₂]
      exact memBar_congr hset.symm
    obtain ⟨z, ⟨hz₁, hz₂⟩, hz⟩ :=
      htwin _ (E64P.memSet_mem _) (E64P.memSet_card _) _ (hLP _) _ (hLP _) hl₁ hl₂
    have e₁ : x (E64P.gIdx (2 * ℓ) 0) ^ 2 = z := by
      refine hinjL _ ((L _).pow_mem (hxk hk₁ (l := 0) (by norm_num)) 2) hz₁ ?_
      rw [map_pow, hxψ, hz, modelGen_sq (l := 0) hk₁ (by norm_num)]
    have e₂ : x (E64P.gIdx (2 * ℓ + 1) 0) ^ 2 = z := by
      refine hinjL _ ((L _).pow_mem (hxk hk₂ (l := 0) (by norm_num)) 2) hz₂ ?_
      rw [map_pow, hxψ, hz, modelGen_sq (l := 0) hk₂ (by norm_num)]
      exact zBar_congr hset.symm
    rw [e₁, e₂]
  have hrels := E64P.rels_of hq hc ht
  have hmemC : ∀ k : Fin 14, L k ≤ Subgroup.closure (Set.range x) := by
    intro k l hl
    have hsub : Subgroup.closure {x (E64P.gIdx k.val 0), x (E64P.gIdx k.val 1)} ≤ L k := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hxk k.isLt (l := 0) (by norm_num)
      · exact hxk k.isLt (l := 1) (by norm_num)
    have hψl : ψ l ∈ (Subgroup.closure {x (E64P.gIdx k.val 0), x (E64P.gIdx k.val 1)}).map ψ := by
      rw [MonoidHom.map_closure, Set.image_pair, hxψ, hxψ, E64P.closure_modelGen_pair k,
        ← hLψ k]
      exact ⟨l, hl, rfl⟩
    obtain ⟨c, hc, hcl⟩ := hψl
    rw [← hinjL k (hsub hc) hl hcl]
    exact Subgroup.closure_mono (by rintro _ (rfl | rfl) <;> exact ⟨_, rfl⟩) hc
  have htop : Subgroup.closure (Set.range x) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨α, hα, h, b, hMψ⟩ := hlab M hM
    obtain ⟨k, hk₁, hk₂⟩ := memIdx_surj hα b
    have hMk : M = L k := huniq M hM (L k) (hLP k) (by
      rw [hMψ, hLψ k, hk₂]
      exact memBar_congr hk₁.symm)
    rw [hMk]
    exact hmemC k
  have hcardQ : Nat.card Q ≤ Nat.card ψ.range := by
    have h1 := E64P.card_closure_le_of_rels x hrels
    rw [htop, Subgroup.card_top] at h1
    rw [hrange]
    exact h1.trans E64Ker.le_card_e64Sub
  have hbij := ψ.rangeRestrict_surjective.bijective_of_nat_card_le hcardQ
  exact MonoidHom.rangeRestrict_injective_iff.mp hbij.1

end Pres

end F7S

section Conj

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}

theorem p23SecFamV_conj (hΩ : HypOmegaGen (Om R)) {V : Subgroup Y}
    {L : Subgroup (SecQuot (rLayerSub (Om R) V))} (hL : L ∈ p23SecFamV R V)
    (q : SecQuot (rLayerSub (Om R) V)) : conjSub q L ∈ p23SecFamV R V := by
  obtain ⟨R', hR', hR'V, rfl⟩ := hL
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨conjSub (c : Y) R', Q3CL.Thompson.conjSub_mem_RSet hΩ hR' _, ?_, ?_⟩
  · have hc : (c : Y) ∈ Subgroup.centralizer (V : Set Y) := F7C.rLayerSub_le_centralizer V c.2
    have h := conjSub_mono (n := (c : Y)) hR'V
    rwa [conjSub_eq_self_of_mem hc] at h
  · exact F7I.conjSub_map_piC c

end Conj


section S1

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23SecFamV_card (hc : P23Cfg n Y R S t K' W u e g) {V : Subgroup Y}
    {L : Subgroup (SecQuot (rLayerSub (Om R) V))} (hL : L ∈ p23SecFamV R V) : Nat.card L = 8 := by
  have hC := CoreData.of_S hc.std.perp.core
  obtain ⟨R₁, hR₁, hR₁V, rfl⟩ := hL
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR₁
  rw [F7S.card_secImage (F7C.le_rLayerSub hR₁ hR₁V) (F7C.isPGroup_of_mem_RSet hR₁)]
  exact (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8 J hJ R₁ hRJ

theorem p23SecFamV_eq_of_map_eq (hc : P23Cfg n Y R S t K' W u e g) {V : Subgroup Y}
    (hspan : TC.Thin.pSpan (p23SecFamV R V) = ⊤)
    (I : TC.Thin.AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub)
    {L₁ L₂ : Subgroup (SecQuot (rLayerSub (Om R) V))} (h₁ : L₁ ∈ p23SecFamV R V)
    (h₂ : L₂ ∈ p23SecFamV R V)
    (he : (L₁.subgroupOf (TC.Thin.pSpan (p23SecFamV R V))).map I.φ =
      (L₂.subgroupOf (TC.Thin.pSpan (p23SecFamV R V))).map I.φ) : L₁ = L₂ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hmemP : ∀ x : SecQuot (rLayerSub (Om R) V), x ∈ TC.Thin.pSpan (p23SecFamV R V) :=
    fun x => by
      rw [hspan]
      exact Subgroup.mem_top x
  let ι : SecQuot (rLayerSub (Om R) V) →* ↥(TC.Thin.pSpan (p23SecFamV R V)) :=
    { toFun := fun x => ⟨x, hmemP x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hker : (I.φ.comp ι).ker ≤ Subgroup.center (SecQuot (rLayerSub (Om R) V)) := by
    intro x hx
    have hk := I.ker_le hx
    exact Subgroup.mem_center_iff.mpr fun y =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hk (ι y))
  have hlab : ∀ L : Subgroup (SecQuot (rLayerSub (Om R) V)),
      L.map (I.φ.comp ι) = (L.subgroupOf (TC.Thin.pSpan (p23SecFamV R V))).map I.φ := by
    intro L
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
  have hP₁ := h₁
  obtain ⟨R₁, hR₁, hR₁V, rfl⟩ := h₁
  obtain ⟨R₂, hR₂, hR₂V, rfl⟩ := h₂
  have hR₁Y : R₁ ≤ rLayerSub (Om R) V := F7C.le_rLayerSub hR₁ hR₁V
  refine F7S.eq_secImage_of_map_eq hΩ (I.φ.comp ι) hker hR₁ hR₂ hR₁Y
    (F7C.le_rLayerSub hR₂ hR₂V) ?_ (by rw [hlab, hlab]; exact he)
  intro x hx y hy hxy
  obtain ⟨α, -, hα, b, hlabI⟩ := I.label _ hP₁
  exact TC.Thin.phi_injOn I.φ (by norm_num) hP₁ (p23SecFamV_card hc hP₁) hlabI hx hy hxy

end S1

section S3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_phi_injective (hc : P23Cfg n Y R S t K' W u e g) {Z : Subgroup Y}
    (hZ : P23ZData t u e Z) {V : Subgroup Y} (hVZ : V ≤ Z)
    (hspan : TC.Thin.pSpan (p23SecFamV R V) = ⊤)
    (I : TC.Thin.AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub) :
    Function.Injective I.φ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hmemP : ∀ x : SecQuot (rLayerSub (Om R) V), x ∈ TC.Thin.pSpan (p23SecFamV R V) :=
    fun x => by
      rw [hspan]
      exact Subgroup.mem_top x
  let ι : SecQuot (rLayerSub (Om R) V) →* ↥(TC.Thin.pSpan (p23SecFamV R V)) :=
    { toFun := fun x => ⟨x, hmemP x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hlab : ∀ L : Subgroup (SecQuot (rLayerSub (Om R) V)),
      L.map (I.φ.comp ι) = (L.subgroupOf (TC.Thin.pSpan (p23SecFamV R V))).map I.φ := by
    intro L
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
  have hrange : (I.φ.comp ι).range = AE.e64Sub := by
    refine Eq.trans ?_ I.range_eq
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ι x, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, rfl⟩
  have h8 : ∀ L ∈ p23SecFamV R V, Nat.card L = 8 := fun L hL => p23SecFamV_card hc hL
  have hlab' : ∀ L ∈ p23SecFamV R V, ∃ α ∈ AE.e64Sets, ∃ (h : α.card = 4) (b : Bool),
      L.map (I.φ.comp ι) = AE.memBar α h b := by
    intro L hL
    obtain ⟨α, hα, h, b, hl⟩ := I.label L hL
    exact ⟨α, hα, h, b, (hlab L).trans hl⟩
  have hsurj : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ p23SecFamV R V,
      L.map (I.φ.comp ι) = AE.memBar α h b := by
    intro α hα h b
    obtain ⟨L, hL, hl⟩ := I.label_surj α hα h b
    exact ⟨L, hL, (hlab L).trans hl⟩
  have huniq : ∀ L₁ ∈ p23SecFamV R V, ∀ L₂ ∈ p23SecFamV R V,
      L₁.map (I.φ.comp ι) = L₂.map (I.φ.comp ι) → L₁ = L₂ := fun L₁ h₁ L₂ h₂ he =>
    p23SecFamV_eq_of_map_eq hc hspan I h₁ h₂ (by rw [← hlab, ← hlab]; exact he)
  have hconj : ∀ L ∈ p23SecFamV R V, ∀ q, conjSub q L ∈ p23SecFamV R V :=
    fun L hL q => p23SecFamV_conj hΩ hL q
  obtain ⟨R₁, R₁', hR₁, hR₁', hcomm, hzR₁, hzR₁'⟩ := LL1.exists_cent_twin_sylows hc hZ
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hcV : ∀ {L : Subgroup Y}, (∀ z ∈ Z, ∀ r ∈ L, z * r = r * z) →
      L ≤ Subgroup.centralizer (V : Set Y) := fun hL' r hr =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hL' v (hVZ hv) r hr
  have hR₁R : R₁ ∈ RSet (Om R) := mem_RSet_of_isSylow2In hK hR₁
  have hR₁'R : R₁' ∈ RSet (Om R) := mem_RSet_of_isSylow2In hK' hR₁'
  have hR₁X : R₁ ≤ rLayerSub (Om R) V := F7C.le_rLayerSub hR₁R (hcV hzR₁)
  have hP₁ : secImage (rLayerSub (Om R) V) R₁ ∈ p23SecFamV R V := ⟨R₁, hR₁R, hcV hzR₁, rfl⟩
  have hP₂ : secImage (rLayerSub (Om R) V) R₁' ∈ p23SecFamV R V := ⟨R₁', hR₁'R, hcV hzR₁', rfl⟩
  have hc8 := (CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC).card8
  have htR₁ : t ∈ R₁ :=
    Asc77.mem_of_two_dvd_card hz hR₁.1 (by rw [hc8 _ hK R₁ hR₁]; norm_num)
  have htR₁' : t ∈ R₁' :=
    Asc77.mem_of_two_dvd_card hz' hR₁'.1 (by rw [hc8 _ hK' R₁' hR₁']; norm_num)
  obtain ⟨tb, htb⟩ : ∃ tb, tb = F7I.piC (rLayerSub (Om R) V) ⟨t, hR₁X htR₁⟩ := ⟨_, rfl⟩
  have htb₁ : tb ∈ secImage (rLayerSub (Om R) V) R₁ := F7I.mem_map_piC.mpr ⟨_, htR₁, htb.symm⟩
  have htb₂ : tb ∈ secImage (rLayerSub (Om R) V) R₁' := F7I.mem_map_piC.mpr ⟨_, htR₁', htb.symm⟩
  have htb1 : tb ≠ 1 := by
    intro h1
    rw [htb, ← map_one (F7I.piC (rLayerSub (Om R) V))] at h1
    exact hz.ne_one (congrArg Subtype.val
      (F7I.piC_inj (F7C.isPGroup_of_mem_RSet hR₁R) htR₁ R₁.one_mem h1))
  have htbb : tb * tb = 1 := by
    rw [htb, ← map_mul, ← map_one (F7I.piC (rLayerSub (Om R) V))]
    congr 1
    exact Subtype.ext hz.sq
  have hcommL : Commutes (secImage (rLayerSub (Om R) V) R₁)
      (secImage (rLayerSub (Om R) V) R₁') := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := F7I.mem_map_piC.mp hx
    obtain ⟨y', hy', rfl⟩ := F7I.mem_map_piC.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ hx' _ hy')
  have htwin : ∀ α ∈ AE.e64Sets, ∀ (h : α.card = 4), ∀ M₁ ∈ p23SecFamV R V,
      ∀ M₂ ∈ p23SecFamV R V, M₁.map (I.φ.comp ι) = AE.memBar α h true →
        M₂.map (I.φ.comp ι) = AE.memBar α h false →
          ∃ y ∈ M₁ ⊓ M₂, (I.φ.comp ι) y = AE.zBar α h :=
    fun α hα h M₁ hM₁ M₂ hM₂ hl₁ hl₂ => F7S.twin_of_pair hrange h8 hlab' huniq hconj hP₁ hP₂
      hcommL htb₁ htb₂ htb1 htbb hα h hM₁ hM₂ hl₁ hl₂
  have hψ := F7S.injective_of_members hspan hrange h8 hlab' hsurj huniq hconj htwin
  intro a b hab
  exact Subtype.ext (hψ (show (I.φ.comp ι) a.1 = (I.φ.comp ι) b.1 from hab))

theorem p23E7LemL_of_lemLId (hL : P23E7LemLId n) : P23E7LemL n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZu Z hZ V hVZ hV1 f₁ hf₁ f₂ hf₂ hne h₁ h₂
  obtain ⟨hgen, ⟨I⟩, ha⟩ :=
    hL hcit hP Y R S t K' W u e g hc hno hE hZu Z hZ V hVZ hV1 f₁ hf₁ f₂ hf₂ hne h₁ h₂
  refine ⟨hgen, I, fun x _ hx => p23_phi_injective hc hZ hVZ hgen I ?_, ha⟩
  rw [hx, map_one]

end S3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
