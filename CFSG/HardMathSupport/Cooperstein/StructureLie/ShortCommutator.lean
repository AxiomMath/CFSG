module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommPair
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommConfig
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub)
open CFSG.QuasithinUnique
open Subgroup
open scoped commutatorElement Pointwise

@[expose] def commKer' {G : Type*} [Group G] (M W₁ W₂ : Subgroup G)
    (hW₂ : M ≤ normalizer (W₂ : Set G)) : Subgroup G where
  carrier := {g | g ∈ M ∧ ∀ w ∈ W₁, ⁅w, g⁆ ∈ W₂}
  one_mem' := ⟨M.one_mem, fun w _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun w hw => ?_⟩
    have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact W₂.mul_mem (ha' w hw) (TransvIrr.conj_mem_of_le_normalizer hW₂ ha (hb' w hw))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun w hw => ?_⟩
    have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact TransvIrr.conj_mem_of_le_normalizer hW₂ (M.inv_mem ha) (W₂.inv_mem (ha' w hw))

namespace ShortComm

namespace DihData

variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G} {s s' z z' l : G}

theorem not_central (h : DihData V s s' z z') (hz1 : z ≠ 1) (hperf : ⁅L, L⁆ = L)
    (hLV : L ≤ normalizer (V : Set G)) (hlL : l ∈ L) (hz'l : z' = l⁻¹ * z * l)
    (hcen : ∀ l₂ ∈ L, ∀ v ∈ V, s * s' * (l₂ * v * l₂⁻¹) * (s * s')⁻¹ =
      l₂ * (s * s' * v * (s * s')⁻¹) * l₂⁻¹) : False := by
  classical
  have hzz' : z * z' = z' * z := h.zz'_comm
  set E₀ : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers z' with hE₀
  have hzE : z ∈ E₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hz'E : z' ∈ E₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z')
  have hInE : ∀ e, InE z z' e → e ∈ E₀ := by
    intro e he
    obtain he | he | he | he : e = 1 ∨ e = z ∨ e = z' ∨ e = z * z' := he
    all_goals rw [he]
    · exact E₀.one_mem
    · exact hzE
    · exact hz'E
    · exact E₀.mul_mem hzE hz'E
  have hconjV : ∀ l₂ ∈ L, ∀ v ∈ V, l₂ * v * l₂⁻¹ ∈ V := fun l₂ hl₂ v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLV hl₂) v).mp hv
  have hkey : ∀ l₂ ∈ L, ∀ v ∈ V, l₂ * (v⁻¹ * (s * s' * v * (s * s')⁻¹)) * l₂⁻¹ =
      (l₂ * v * l₂⁻¹)⁻¹ * (s * s' * (l₂ * v * l₂⁻¹) * (s * s')⁻¹) := by
    intro l₂ hl₂ v hv
    rw [hcen l₂ hl₂ v hv]
    group
  have hz_eq : z = z'⁻¹ * (s * s' * z' * (s * s')⁻¹) := by
    rw [h.u_z']
    have : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right h.z'_sq
    rw [this]
    calc z = (z' * z') * z := by rw [h.z'_sq, one_mul]
      _ = z' * (z' * z) := by rw [mul_assoc]
      _ = z' * (z * z') := by rw [hzz']
  have hz'_eq : z' = (z * z')⁻¹ * (s * s' * (z * z') * (s * s')⁻¹) := by
    rw [h.u_zz']
    have h1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
    have h2 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right h.z'_sq
    rw [mul_inv_rev, h1, h2]
    calc z' = z' * (z * z) := by rw [h.z_sq, mul_one]
      _ = z' * z * z := by rw [mul_assoc]
  have hnz : ∀ l₂ ∈ L, l₂ * z * l₂⁻¹ ∈ E₀ := by
    intro l₂ hl₂
    have e : l₂ * z * l₂⁻¹ = (l₂ * z' * l₂⁻¹)⁻¹ * (s * s' * (l₂ * z' * l₂⁻¹) * (s * s')⁻¹) := by
      rw [← hkey l₂ hl₂ z' h.hz', ← hz_eq]
    rw [e]
    exact hInE _ (h.commutator_mem_E (hconjV l₂ hl₂ z' h.hz'))
  have hnz' : ∀ l₂ ∈ L, l₂ * z' * l₂⁻¹ ∈ E₀ := by
    intro l₂ hl₂
    have hzz'V : z * z' ∈ V := V.mul_mem h.hz h.hz'
    have e : l₂ * z' * l₂⁻¹ = (l₂ * (z * z') * l₂⁻¹)⁻¹ *
        (s * s' * (l₂ * (z * z') * l₂⁻¹) * (s * s')⁻¹) := by
      rw [← hkey l₂ hl₂ (z * z') hzz'V, ← hz'_eq]
    rw [e]
    exact hInE _ (h.commutator_mem_E (hconjV l₂ hl₂ (z * z') hzz'V))
  have hN : L ≤ normalizer (E₀ : Set G) := by
    intro g hg
    have hle : E₀ ≤ E₀.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact hnz g hg
      · rw [Subgroup.zpowers_le]; exact hnz' g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hle hx, fun hx => ?_⟩
    have hle' : E₀ ≤ E₀.comap (MulAut.conj g⁻¹).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact hnz g⁻¹ (L.inv_mem hg)
      · rw [Subgroup.zpowers_le]; exact hnz' g⁻¹ (L.inv_mem hg)
    have h2 : g⁻¹ * (g * x * g⁻¹) * g ∈ E₀ := by simpa using hle' hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h2
  have hcard : Nat.card E₀ ≤ 4 := by
    have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers z' : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (Subgroup.zpowers z' : Set G))
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute z' z from hzz'.symm) m).eq
    have hmulset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers z)
      (Subgroup.zpowers z') hnorm
    have h1 := Set.natCard_mul_le (s := (Subgroup.zpowers z : Set G))
      (t := (Subgroup.zpowers z' : Set G))
    have h2 : Nat.card E₀ = Nat.card ↥((Subgroup.zpowers z : Set G) * (Subgroup.zpowers z' : Set G)) := by
      rw [← hmulset]; rfl
    have hz2 : Nat.card (Subgroup.zpowers z) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.z_sq))
    have hz'2 : Nat.card (Subgroup.zpowers z') ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.z'_sq))
    rw [h2]
    calc _ ≤ Nat.card ↥(Subgroup.zpowers z) * Nat.card ↥(Subgroup.zpowers z') := h1
      _ ≤ 2 * 2 := Nat.mul_le_mul hz2 hz'2
  have hcentr := centralizes_of_perfect_of_card_le_four hperf hN hcard
  have hzc := hcentr l⁻¹ (L.inv_mem hlL) z hzE
  have hz'z : z' = z := by rw [hz'l]; simpa using hzc
  apply hz1
  have h3 := h.sz'
  rw [hz'z, h.sz] at h3
  calc z = z * z := h3
    _ = 1 := h.z_sq

end DihData

end ShortComm

theorem commutator_pCore_le_blockV {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (ht : TransvectionData S L) :
    ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L := by
  obtain ⟨s, hsS, hgen, hsn, hZ⟩ := ht
  have hset := TransvIrr.setting_of hX hA hL hsS hgen hsn hZ
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hV2 : ∀ v ∈ blockV S L, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  obtain ⟨z, hzZ, hz1, l, hlL, hl1, hl2⟩ := TransvIrr.exists_pair_of_setting hset hV2 hsn
    (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen hX hA hL hTM hMT hCT hx hxn)
  have hMV : L ⊔ S ≤ normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  have hQS : pCoreOf 2 (L ⊔ S) ≤ S := twoCore_sup_le hA hL hSL
  have hQC : pCoreOf 2 (L ⊔ S) ≤ centralizer (blockV S L : Set G) := fun x hx =>
    CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx
  have hVQ : blockV S L ≤ pCoreOf 2 (L ⊔ S) := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hVel : CFSG.Open.IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ S)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (L ⊔ S)
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hMQ : L ⊔ S ≤ normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hCnorm : L ⊔ S ≤ normalizer (((L ⊔ S) ⊓ centralizer (blockV S L : Set G) : Subgroup G) :
      Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer_blockV S L hg⟩
  have hCleN : (L ⊔ S) ⊓ centralizer (blockV S L : Set G) ≤ normalizer (S : Set G) :=
    inf_centralizer_blockV_le_normalizer hA hL hSL
  have hSC : S ⊓ centralizer (blockV S L : Set G) ≤ pCoreOf 2 (L ⊔ S) :=
    inf_centralizer_blockV_le_twoCore hA hL hSL
  have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hsS
  have hlM : l ∈ L ⊔ S := Subgroup.mem_sup_left hlL
  have hsC : s ∉ centralizer (blockV S L : Set G) := fun h =>
    hsn (Subgroup.mem_sup_right ⟨hsM, h⟩)
  have hs2 : ∀ v ∈ blockV S L, s * s * v * (s * s)⁻¹ = v := fun v hv => by
    calc s * s * v * (s * s)⁻¹ = s * (s * v * s⁻¹) * s⁻¹ := by group
      _ = v := hset.s_sq hv
  have hs2C : s * s ∈ centralizer (blockV S L : Set G) := by
    rw [mem_centralizer_iff]
    intro v hv
    have := hs2 v hv
    have h2 : s * s * v = v * (s * s) := by
      rw [mul_inv_eq_iff_eq_mul] at this; exact this
    exact h2.symm
  have hs2Q : s * s ∈ pCoreOf 2 (L ⊔ S) := hSC ⟨S.mul_mem hsS hsS, hs2C⟩
  set M : Subgroup G := L ⊔ S with hMdef
  set V : Subgroup G := blockV S L with hVdef
  set Q : Subgroup G := pCoreOf 2 M with hQdef
  set C : Subgroup G := M ⊓ centralizer (V : Set G) with hCdef
  have hzV : z ∈ V := hset.comm_le_V le_rfl (zpowers_le.mpr hset.mem) hzZ
  have hz2 : z * z = 1 := hV2 z hzV
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hl'M : l⁻¹ ∈ M := M.inv_mem hlM
  have hconjV : ∀ v ∈ V, ∀ g ∈ M, g * v * g⁻¹ ∈ V := fun v hv g hg => hset.conjV hg hv
  set z' : G := l⁻¹ * z * l with hz'def
  have hz'V : z' ∈ V := by
    have := hconjV z hzV l⁻¹ hl'M
    simpa using this
  have hsz : s * z * s⁻¹ = z := hset.s_fix_Z hzZ
  have hscomm1 : ∀ v ∈ V, ⁅v, s⁆ = 1 → s * v * s⁻¹ = v := by
    intro v hv hc
    have := commutatorElement_eq_one_iff_mul_comm.mp hc
    calc s * v * s⁻¹ = v * s * s⁻¹ := by rw [this]
      _ = v := by group
  have hscomm2 : ∀ v ∈ V, ⁅v, s⁆ ≠ 1 → s * v * s⁻¹ = v * z := by
    intro v hv hc
    have heq : ⁅v, s⁆ = z := hset.Z_eq_of_ne_one (hset.mem_Z hv) hzZ hc hz1
    have hw : s * v * s⁻¹ = ⁅v, s⁆⁻¹ * v := by simp only [commutatorElement_def]; group
    rw [hw, heq, hzinv]
    exact hset.comm z hzV v hv
  have hscase : ∀ v ∈ V, s * v * s⁻¹ = v ∨ s * v * s⁻¹ = v * z := by
    intro v hv
    by_cases hc : ⁅v, s⁆ = 1
    · exact Or.inl (hscomm1 v hv hc)
    · exact Or.inr (hscomm2 v hv hc)
  have hs'case : ∀ v ∈ V, (l⁻¹ * s * l) * v * (l⁻¹ * s * l)⁻¹ = v ∨
      (l⁻¹ * s * l) * v * (l⁻¹ * s * l)⁻¹ = v * z' := by
    intro v hv
    have hv1 : l * v * l⁻¹ ∈ V := hconjV v hv l hlM
    have e : (l⁻¹ * s * l) * v * (l⁻¹ * s * l)⁻¹ = l⁻¹ * (s * (l * v * l⁻¹) * s⁻¹) * l := by group
    rw [e]
    rcases hscase _ hv1 with h1 | h1
    · left; rw [h1]; group
    · right; rw [h1, hz'def]; group
  have hsz' : s * z' * s⁻¹ = z' * z := by
    have h1 : ⁅z', s⁆ ≠ 1 := hl1
    rw [hscomm2 z' hz'V h1]
  have hs'z' : (l⁻¹ * s * l) * z' * (l⁻¹ * s * l)⁻¹ = z' := by
    have e : (l⁻¹ * s * l) * z' * (l⁻¹ * s * l)⁻¹ = l⁻¹ * (s * z * s⁻¹) * l := by
      rw [hz'def]; group
    rw [e, hsz]
  have hs'z : (l⁻¹ * s * l) * z * (l⁻¹ * s * l)⁻¹ = z * z' := by
    have hzl : l * z * l⁻¹ ∈ V := hconjV z hzV l hlM
    have h2 : ⁅l * z * l⁻¹, s⁆ ≠ 1 := hl2
    have e : (l⁻¹ * s * l) * z * (l⁻¹ * s * l)⁻¹ = l⁻¹ * (s * (l * z * l⁻¹) * s⁻¹) * l := by group
    rw [e, hscomm2 _ hzl h2]
    have e2 : l⁻¹ * (l * z * l⁻¹ * z) * l = z * z' := by
      rw [hz'def]; group
    rw [e2]
  have hdih : ShortComm.DihData V s (l⁻¹ * s * l) z z' :=
    ⟨hzV, hz'V, hset.comm, hV2, hscase, hs'case, hsz, hs'z', hsz', hs'z⟩
  set s' : G := l⁻¹ * s * l with hs'def
  set u : G := s * s' with hudef
  have hs'M : s' ∈ M := M.mul_mem (M.mul_mem hl'M hsM) hlM
  have huM : u ∈ M := M.mul_mem hsM hs'M
  have hu3 : ∀ v ∈ V, u ^ 3 * v * (u ^ 3)⁻¹ = v := fun v hv => hdih.u_cube hv
  have hu3C : u ^ 3 ∈ C := by
    refine ⟨M.pow_mem huM 3, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := hu3 v hv
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have huC : u ∉ centralizer (V : Set G) := by
    intro h
    apply hdih.u_ne hz1
    have := mem_centralizer_iff.mp h z' hz'V
    calc u * z' * u⁻¹ = z' * u * u⁻¹ := by rw [← this]
      _ = z' := by group
  have hSM : S ≤ M := le_sup_right
  have hQM : Q ≤ M := hQS.trans hSM
  have hSgen : S ≤ zpowers s ⊔ Q := by
    intro y hy
    have hy' : y ∈ C ⊔ zpowers s := by rw [sup_comm]; exact hgen hy
    have hsN : zpowers s ≤ normalizer (C : Set G) := zpowers_le.mpr (hCnorm hsM)
    obtain ⟨c, hc, t, ht, rfl⟩ :=
      CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer (N := C) (K := zpowers s) hsN hy'
    have htS : t ∈ S := zpowers_le.mpr hsS ht
    have hcS : c ∈ S := by simpa using S.mul_mem hy (S.inv_mem htS)
    have hcQ : c ∈ Q := hSC ⟨hcS, hc.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcQ) (Subgroup.mem_sup_left ht)
  have hcgs : ∀ C' : Subgroup G, C' ≤ S → C' ≠ ⊥ → (C'.subgroupOf S).Characteristic →
      ∀ y ∈ M, y ∈ normalizer (C' : Set G) → y ∈ normalizer (S : Set G) := by
    intro C' hCS hC1 hchar y hy hyN
    have hcgsM : CFSG.Quasithin.cgsIn M S = M ⊓ normalizer (S : Set G) :=
      cgsIn_eq_of_le hA (sup_le hL.le hA.twoRadical.1)
    have hle : M ⊓ normalizer (C' : Set G) ≤ CFSG.Quasithin.cgsIn M S :=
      le_iSup_of_le C' (le_iSup_of_le hCS (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))
    rw [hcgsM] at hle
    exact (hle ⟨hy, hyN⟩).2
  have hQn : (Q.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ
  let mq : ↥M →* ↥M ⧸ Q.subgroupOf M := QuotientGroup.mk' (Q.subgroupOf M)
  have mq_eq_one : ∀ y : ↥M, mq y = 1 ↔ (y : G) ∈ Q := by
    intro y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let sM : ↥M := ⟨s, hsM⟩
  let uM : ↥M := ⟨u, huM⟩
  have hs'2Q : s' * s' ∈ Q := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hMQ hl'M) (s * s)).mp hs2Q
    have e : l⁻¹ * (s * s) * l⁻¹⁻¹ = s' * s' := by rw [hs'def]; group
    rwa [e] at h1
  have hinv : s * u * s⁻¹ * u ∈ Q := by
    have e : s * u * s⁻¹ * u = (s * s) * (s' * s') := by rw [hudef]; group
    rw [e]; exact Q.mul_mem hs2Q hs'2Q
  have hcomm_s : ∀ c ∈ C, s * c * s⁻¹ * c⁻¹ ∈ Q := by
    intro c hc
    have hcS : c ∈ normalizer (S : Set G) := hCleN hc
    have h1 : c * s⁻¹ * c⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hcS s⁻¹).mp (S.inv_mem hsS)
    have h2 : s * c * s⁻¹ * c⁻¹ ∈ S := by
      have := S.mul_mem hsS h1
      have e : s * (c * s⁻¹ * c⁻¹) = s * c * s⁻¹ * c⁻¹ := by group
      rwa [e] at this
    have h3 : s * c * s⁻¹ * c⁻¹ ∈ C :=
      C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCnorm hsM) c).mp hc) (C.inv_mem hc)
    exact hSC ⟨h2, h3.2⟩
  have hσ : mq sM * mq uM * (mq sM)⁻¹ * mq uM = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, mq_eq_one]; exact hinv
  have hσ1 : mq sM * mq uM * (mq sM)⁻¹ = (mq uM)⁻¹ := eq_inv_of_mul_eq_one_left hσ
  have hu6 : u ^ 6 ∈ Q := by
    have hc3 := hcomm_s (u ^ 3) hu3C
    have hσc : mq sM * mq uM ^ 3 * (mq sM)⁻¹ * (mq uM ^ 3)⁻¹ = 1 := by
      rw [← map_pow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, mq_eq_one]
      exact hc3
    have h4 : mq sM * mq uM ^ 3 * (mq sM)⁻¹ = mq uM ^ 3 := mul_inv_eq_one.mp hσc
    have h5 : (mq sM * mq uM * (mq sM)⁻¹) ^ 3 = mq uM ^ 3 := by rw [conj_pow]; exact h4
    rw [hσ1] at h5
    have h6 : mq uM ^ 6 = 1 := by
      calc mq uM ^ 6 = mq uM ^ 3 * mq uM ^ 3 := by group
        _ = mq uM ^ 3 * (mq uM)⁻¹ ^ 3 := by rw [h5]
        _ = 1 := by group
    rw [← map_pow, mq_eq_one] at h6
    exact h6
  have hx3 : (u ^ 4) ^ 3 ∈ Q := by
    have e : (u ^ 4) ^ 3 = u ^ 6 * u ^ 6 := by group
    rw [e]; exact Q.mul_mem hu6 hu6
  have hsx : s * u ^ 4 * s⁻¹ * u ^ 4 ∈ Q := by
    have h1 : mq sM * mq uM ^ 4 * (mq sM)⁻¹ * mq uM ^ 4 = 1 := by
      calc mq sM * mq uM ^ 4 * (mq sM)⁻¹ * mq uM ^ 4
          = (mq sM * mq uM * (mq sM)⁻¹) ^ 4 * mq uM ^ 4 := by rw [conj_pow]
        _ = (mq uM)⁻¹ ^ 4 * mq uM ^ 4 := by rw [hσ1]
        _ = 1 := by group
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_mul, mq_eq_one] at h1
    exact h1
  have hxC : u ^ 4 ∉ centralizer (V : Set G) := by
    intro h
    apply huC
    have h3 : u ^ 3 ∈ centralizer (V : Set G) := hu3C.2
    have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ h3)
    have e : u ^ 4 * (u ^ 3)⁻¹ = u := by group
    rwa [e] at this
  obtain ⟨k, hk⟩ := ShortComm.exists_baumann_commutator hQ2 hS2 hMQ hMV hQS hSM hVQ hVel hQC hsS
    hs2Q hSgen hsC (M.pow_mem huM 4) hx3 hsx hxC hcgs
  have hTn : M ≤ normalizer ((commKer' M Q V hMV : Subgroup G) : Set G) := by
    apply TransvIrr.le_normalizer_of_conj_mem
    rintro m hm g ⟨hg, hg'⟩
    refine ⟨M.mul_mem (M.mul_mem hm hg) (M.inv_mem hm), fun w hw => ?_⟩
    have e : ⁅w, m * g * m⁻¹⁆ = m * ⁅m⁻¹ * w * m⁻¹⁻¹, g⁆ * m⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hg' (m⁻¹ * w * m⁻¹⁻¹) (TransvIrr.conj_mem_of_le_normalizer hMQ (M.inv_mem hm) hw)
    exact TransvIrr.conj_mem_of_le_normalizer hMV hm this
  set T : Subgroup G := commKer' M Q V hMV with hTdef
  have hTM : T ≤ M := fun g hg => hg.1
  have hyT : (u ^ 4) ^ 2 ^ k ∈ T := ⟨M.pow_mem (M.pow_mem huM 4) _, hk⟩
  have hLP : L ≤ T ⊔ Q := by
    have hXM : M ≤ X := sup_le hL.le hA.twoRadical.1
    have hOQM : pCoreOf 2 X ≤ M := hA.twoCore_le.trans le_sup_right
    have hOQ : pCoreOf 2 X ≤ Q :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hOQM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hOQM).mpr
          (hXM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
    set P₀ : Subgroup G := T ⊔ Q with hP₀def
    have hP₀n : M ≤ normalizer (P₀ : Set G) := fun g hg =>
      inf_normalizer_le_normalizer_sup _ _ ⟨hTn hg, hMQ hg⟩
    have hLM : L ≤ M := hset.le
    let hbar := barMHomSub (X := X) (L := L) hL.le
    have hq := hL.component.2.2
    have hP₀Ln : (((P₀ ⊓ L).subgroupOf L)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ P₀ ⊓ L := hn
      show ((g * n * g⁻¹ : ↥L) : G) ∈ P₀ ⊓ L
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hP₀n (hLM g.2)) (n : G)).mp hn'.1
      · exact L.mul_mem (L.mul_mem g.2 hn'.2) (L.inv_mem g.2)
    have hN₁ : (((P₀ ⊓ L).subgroupOf L).map hbar).Normal :=
      hP₀Ln.map hbar (barMHomSub_surjective hL.le)
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      hq.1 hq.2 _ hN₁ with hc | htop
    · exfalso
      set y : G := (u ^ 4) ^ 2 ^ k with hydef
      have hyM : y ∈ M := M.pow_mem (M.pow_mem huM 4) _
      have hsL1 : s * l⁻¹ * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hSL hsS) l⁻¹).mp (L.inv_mem hlL)
      have hss : (s * s) * l * (s * s)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hSL (S.mul_mem hsS hsS)) l).mp hlL
      have hu_eq : u = ((s * l⁻¹ * s⁻¹) * ((s * s) * l * (s * s)⁻¹)) * (s * s) := by
        rw [hudef, hs'def]; group
      have huLQ : u ∈ L ⊔ Q := by
        rw [hu_eq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.mul_mem hsL1 hss))
          (Subgroup.mem_sup_right hs2Q)
      have hyLQ : y ∈ L ⊔ Q := Subgroup.pow_mem _ (Subgroup.pow_mem _ huLQ 4) _
      obtain ⟨ℓ, hℓL, q₁, hq₁, hyℓ⟩ :=
        CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer (N := L) (K := Q) (hQS.trans hSL) hyLQ
      have hℓM : ℓ ∈ M := hset.le hℓL
      have hℓP : ℓ ∈ P₀ := by
        have e : ℓ = y * q₁⁻¹ := by rw [hyℓ]; group
        rw [e]
        exact P₀.mul_mem (Subgroup.mem_sup_left hyT) (Subgroup.mem_sup_right (Q.inv_mem hq₁))
      have hcen := hc ⟨⟨ℓ, hℓL⟩, Subgroup.mem_subgroupOf.mpr ⟨hℓP, hℓL⟩, rfl⟩
      have hcomm : ∀ l₂ ∈ L, ℓ * l₂ * ℓ⁻¹ * l₂⁻¹ ∈ Q := by
        intro l₂ hl₂
        have h1 := Subgroup.mem_center_iff.mp hcen (hbar ⟨l₂, hl₂⟩)
        have h2 : hbar (⟨ℓ, hℓL⟩ * ⟨l₂, hl₂⟩ * ⟨ℓ, hℓL⟩⁻¹ * ⟨l₂, hl₂⟩⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
          group
        have h3 : (⟨ℓ, hℓL⟩ * ⟨l₂, hl₂⟩ * ⟨ℓ, hℓL⟩⁻¹ * ⟨l₂, hl₂⟩⁻¹ : ↥L) ∈ hbar.ker := h2
        rw [ker_barMHomSub hL.le, Subgroup.mem_subgroupOf] at h3
        exact hOQ h3
      have hLV : L ≤ normalizer (V : Set G) := hset.le.trans hMV
      have hconjV' : ∀ v ∈ V, ∀ g ∈ M, g * v * g⁻¹ ∈ V := hconjV
      have hcentV : ∀ l₂ ∈ L, ∀ v ∈ V, ℓ * (l₂ * v * l₂⁻¹) * ℓ⁻¹ = l₂ * (ℓ * v * ℓ⁻¹) * l₂⁻¹ := by
        intro l₂ hl₂ v hv
        have hcC : ℓ * l₂ * ℓ⁻¹ * l₂⁻¹ ∈ centralizer (V : Set G) := hQC (hcomm l₂ hl₂)
        have hW : l₂ * (ℓ * v * ℓ⁻¹) * l₂⁻¹ ∈ V :=
          hconjV' _ (hconjV' v hv ℓ hℓM) l₂ (hset.le hl₂)
        have hc1 := Subgroup.mem_centralizer_iff.mp hcC _ hW
        calc ℓ * (l₂ * v * l₂⁻¹) * ℓ⁻¹
            = (ℓ * l₂ * ℓ⁻¹ * l₂⁻¹) * (l₂ * (ℓ * v * ℓ⁻¹) * l₂⁻¹) * (ℓ * l₂ * ℓ⁻¹ * l₂⁻¹)⁻¹ := by
              group
          _ = l₂ * (ℓ * v * ℓ⁻¹) * l₂⁻¹ := by
              rw [← hc1]; group
      have hyV : ∀ v ∈ V, y * v * y⁻¹ = ℓ * v * ℓ⁻¹ := by
        intro v hv
        have hq1 := Subgroup.mem_centralizer_iff.mp (hQC hq₁) v hv
        have e : ℓ * v * ℓ⁻¹ = y * (q₁⁻¹ * v * q₁) * y⁻¹ := by
          have e1 : ℓ = y * q₁⁻¹ := by rw [hyℓ]; group
          rw [e1]; group
        have e2 : q₁⁻¹ * v * q₁ = v := by
          calc q₁⁻¹ * v * q₁ = q₁⁻¹ * (v * q₁) := by group
            _ = q₁⁻¹ * (q₁ * v) := by rw [hq1]
            _ = v := by group
        rw [e, e2]
      have hycent : ∀ l₂ ∈ L, ∀ v ∈ V, y * (l₂ * v * l₂⁻¹) * y⁻¹ = l₂ * (y * v * y⁻¹) * l₂⁻¹ := by
        intro l₂ hl₂ v hv
        rw [hyV _ (hconjV' v hv l₂ (hset.le hl₂)), hyV v hv]
        exact hcentV l₂ hl₂ v hv
      let ρ := Setup.rho V M hMV
      let uM : ↥M := ⟨u, huM⟩
      let yM : ↥M := ⟨y, hyM⟩
      have hu3ρ : ρ uM ^ 3 = 1 := by
        rw [← map_pow]
        exact (Setup.rho_eq_one_iff hMV _).mpr hu3C.2
      have hyρ : ρ yM = ρ uM ^ (4 * 2 ^ k) := by
        have : yM = uM ^ (4 * 2 ^ k) := Subtype.ext (by simp [yM, uM, hydef, pow_mul])
        rw [this, map_pow]
      have hmod : 4 * 2 ^ k * 2 ^ k % 3 = 1 := by
        have : 4 * 2 ^ k * 2 ^ k = 4 ^ (k + 1) := by
          rw [mul_assoc, ← mul_pow, show (2 : ℕ) * 2 = 4 by norm_num, ← pow_succ']
        rw [this, Nat.pow_mod]
        simp
      have huρ : ρ uM = ρ yM ^ (2 ^ k) := by
        rw [hyρ, ← pow_mul, pow_eq_pow_mod _ hu3ρ, hmod, pow_one]
      have hcenu : ∀ l₂ ∈ L, ∀ v ∈ V, u * (l₂ * v * l₂⁻¹) * u⁻¹ = l₂ * (u * v * u⁻¹) * l₂⁻¹ := by
        intro l₂ hl₂ v hv
        have hcy : Commute (ρ yM) (ρ ⟨l₂, hset.le hl₂⟩) := by
          show ρ yM * ρ ⟨l₂, hset.le hl₂⟩ = ρ ⟨l₂, hset.le hl₂⟩ * ρ yM
          ext w
          show (((ρ yM) ((ρ ⟨l₂, hset.le hl₂⟩) w) : ↥V) : G) =
            (((ρ ⟨l₂, hset.le hl₂⟩) ((ρ yM) w) : ↥V) : G)
          rw [Setup.rho_apply_coe, Setup.rho_apply_coe, Setup.rho_apply_coe, Setup.rho_apply_coe]
          exact hycent l₂ hl₂ w w.2
        have hcu : Commute (ρ uM) (ρ ⟨l₂, hset.le hl₂⟩) := by
          rw [huρ]; exact hcy.pow_left _
        have h5 := congrArg (fun f : MulAut V => ((f ⟨v, hv⟩ : V) : G)) hcu.eq
        simp only [MulAut.mul_apply] at h5
        exact h5
      exact hdih.not_central hz1 hL.perfect hLV hlL hz'def hcenu
    · intro l₂ hl₂
      have hmem : hbar ⟨l₂, hl₂⟩ ∈ ((P₀ ⊓ L).subgroupOf L).map hbar := by
        rw [htop]; trivial
      obtain ⟨p, hp, hpe⟩ := hmem
      have hker : p⁻¹ * ⟨l₂, hl₂⟩ ∈ hbar.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpe, inv_mul_cancel]
      rw [ker_barMHomSub hL.le, Subgroup.mem_subgroupOf] at hker
      have hpP : (p : G) ∈ P₀ := (Subgroup.mem_subgroupOf.mp hp).1
      have h1 : (p : G)⁻¹ * l₂ ∈ Q := hOQ hker
      have e : l₂ = (p : G) * ((p : G)⁻¹ * l₂) := by group
      rw [e]
      exact P₀.mul_mem hpP (Subgroup.mem_sup_right h1)
  have hLT : L ≤ T := by
    have hTn' : (T.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr hTn
    let ψ : ↥M →* ↥M ⧸ T.subgroupOf M := QuotientGroup.mk' (T.subgroupOf M)
    have hLm : ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hset.le, hL.perfect]
    have hQ2' : IsPGroup 2 ((Q.subgroupOf M).map ψ) :=
      (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).map ψ
    have hPle : (L.subgroupOf M).map ψ ≤ (Q.subgroupOf M).map ψ := by
      rintro _ ⟨l₂, hl₂, rfl⟩
      have hl₂' : (l₂ : G) ∈ T ⊔ Q := hLP (Subgroup.mem_subgroupOf.mp hl₂)
      obtain ⟨t, ht, q, hq, hlt⟩ :=
        CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer (N := T) (K := Q)
          (hQM.trans hTn) hl₂'
      refine ⟨⟨q, hQM hq⟩, Subgroup.mem_subgroupOf.mpr hq, ?_⟩
      have h1 : l₂ = ⟨t, hTM ht⟩ * ⟨q, hQM hq⟩ := Subtype.ext hlt
      have h2 : ψ ⟨t, hTM ht⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr ht
      rw [h1, map_mul, h2, one_mul]
    have hPperf : ⁅(L.subgroupOf M).map ψ, (L.subgroupOf M).map ψ⁆ = (L.subgroupOf M).map ψ := by
      rw [← Subgroup.map_commutator, hLm]
    have hPbot := ShortComm.eq_bot_of_perfect_of_isPGroup hPperf (hQ2'.to_le hPle)
    intro l₂ hl₂
    have h1 : ψ ⟨l₂, hset.le hl₂⟩ ∈ (L.subgroupOf M).map ψ :=
      ⟨⟨l₂, hset.le hl₂⟩, Subgroup.mem_subgroupOf.mpr hl₂, rfl⟩
    rw [hPbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  refine Subgroup.commutator_le.mpr fun q hq l₂ hl₂ => ?_
  exact (hLT hl₂).2 q hq

end CFSG.HardMathSupport.Cooperstein.StructureLie
