module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import Certificates.Data.A5GL42Norm

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open Certificates.A5GL42 (Mat4 Vec4 GroupFacts FixZero)
open scoped commutatorElement Matrix

section Pre

variable {G : Type} [Group G] [Finite G]

theorem mem_pCore_iff_pCoreOf {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := by
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

theorem a5Pre_self {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L)
    (he : IsElemAbelian 2 (pCoreOf 2 L)) (h16 : Nat.card (pCoreOf 2 L) = 16) :
    A5Pre L L (pCoreOf 2 L) ⊥ := by
  have hQnorm : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf L)
  have hcomm : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (he.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm1 : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
  refine ⟨le_rfl, Subgroup.le_normalizer, hQnorm, ?_, ⟨bot_le, ?_, ?_⟩, ?_, ?_, hq, ?_⟩
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl; simp
    · intro hx
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx]; group
  · exact Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [Subgroup.mem_bot]; exact hcomm1 a ha b hb
  · exact fun e he' => by rw [Subgroup.mem_bot]; exact he.2 e he'
  · rw [Subgroup.relIndex_bot_left]; exact h16
  · exact fun q hq' e he' => by rw [Subgroup.mem_bot]; exact hcomm1 q hq' e he'
  · by_contra hcon
    push Not at hcon
    have hLQ : L ≤ pCoreOf 2 L := by
      intro l hl
      apply hc
      refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun e he' => ?_⟩
      have h1 := hcon l hl e he'
      rw [Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
    have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [Nat.card_congr e.toEquiv]; exact CFSG.QuasithinUnique.A5.Delta5.a5_card
    have htop : CFSG.Open.pCore 2 ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact (mem_pCore_iff_pCoreOf x).mpr (hLQ x.2)
    have h1 : Nat.card (oTwoQuot ↥L) = 1 := by
      show Nat.card (↥L ⧸ CFSG.Open.pCore 2 ↥L) = 1
      rw [htop]
      exact Subgroup.index_top
    omega

theorem iso_models {L : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L) (he : IsElemAbelian 2 (pCoreOf 2 L))
    (h16 : Nat.card (pCoreOf 2 L) = 16) :
    (NatSec L ⊥ (pCoreOf 2 L) ∧
        Nonempty (A5Model L L (pCoreOf 2 L) ⊥ Certificates.A5GL42.HN)) ∨
      (¬ NatSec L ⊥ (pCoreOf 2 L) ∧
        Nonempty (A5Model L L (pCoreOf 2 L) ⊥ Certificates.A5GL42.HO)) :=
  (a5Pre_self hq hc he h16).exists_model'

end Pre

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {H : Finset Mat4}

theorem blockU_eq_pCoreOf (hF : Certificates.A5GL42.Facts) (hH : GroupFacts H)
    (h : A5Pre L L (pCoreOf 2 L) ⊥) (M : A5Model L L (pCoreOf 2 L) ⊥ H) :
    blockU L = pCoreOf 2 L := by
  have hle : blockU L ≤ pCoreOf 2 L :=
    Subgroup.commutator_le.mpr fun q hq l hl => ElemFrame.comm_right_mem h.norm_E hl hq
  have hLX : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQ : (pCoreOf 2 L).map (MulAut.conj g).toMonoidHom = pCoreOf 2 L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.norm_E hg)
    have hL : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.norm_L hg)
    show ⁅pCoreOf 2 L, L⁆.map (MulAut.conj g).toMonoidHom = ⁅pCoreOf 2 L, L⁆
    rw [Subgroup.map_commutator, hQ, hL]
  rcases M.eq_or_eq_of_normalizes hF hH h (X := blockU L) bot_le hle hLX with hb | hq
  · exfalso
    obtain ⟨l, hl, e, he, hne⟩ := h.nontriv
    apply hne
    rw [Subgroup.mem_bot]
    have h1 : ⁅e, l⁆ ∈ blockU L := Subgroup.commutator_mem_commutator he hl
    rw [hb, Subgroup.mem_bot] at h1
    rw [← commutatorElement_inv, h1, inv_one]
  · exact hq

theorem blockZ_eq_bot (hfix : FixZero H) (M : A5Model L L (pCoreOf 2 L) ⊥ H)
    (hU : blockU L = pCoreOf 2 L) : blockZ L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have hxQ : x ∈ pCoreOf 2 L := hU ▸ hxU
  let e : ↥(pCoreOf 2 L) := ⟨x, hxQ⟩
  have hfixv : ∀ m ∈ H, m *ᵥ Multiplicative.toAdd (M.F.φ e) = Multiplicative.toAdd (M.F.φ e) := by
    intro m hm
    obtain ⟨l, hlL, hlm⟩ := M.surjL m hm
    have hcl : (l : G) * x = x * (l : G) := Subgroup.mem_centralizer_iff.mp hxC (l : G) hlL
    have := M.F.act l e e (by
      show x = (l : G) * x * (l : G)⁻¹
      rw [hcl]; group)
    rw [← hlm]
    exact this
  have h0 := hfix _ hfixv
  have : M.F.φ e = 1 := by
    apply Multiplicative.toAdd.injective
    rw [h0, toAdd_one]
  have := (M.F.ker e).mp this
  rwa [Subgroup.mem_bot] at this

structure Rep4 (T : Type*) [Group T] (H : Finset Mat4) where
  rho : T →* GL (Fin 4) (ZMod 2)
  inj : Function.Injective rho
  mem : ∀ t, glMat (rho t) ∈ H
  surj : ∀ m ∈ H, ∃ t, glMat (rho t) = m

theorem recog_exists (hF : Certificates.A5GL42.Facts) (hH : GroupFacts H) (hfix : FixZero H)
    (h : A5Pre L L (pCoreOf 2 L) ⊥) (M : A5Model L L (pCoreOf 2 L) ⊥ H)
    {T Mod : Type*} [Group T] [AddCommGroup Mod] (R : Rep4 T H) (ψ : Vec4 →+ Mod)
    (hψ : Function.Injective ψ) (act : T → Mod → Mod)
    (hact : ∀ t v, ψ (glMat (R.rho t) *ᵥ v) = act t (ψ v)) :
    ∃ (α : ↥L →* T) (β : ↥(blockU L) →* Multiplicative Mod),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ Function.Injective β ∧
      β.ker = (blockZ L).subgroupOf (blockU L) ∧
      (∀ X : Mod, (∃ u, Multiplicative.toAdd (β u) = X) ↔ ∃ v : Vec4, ψ v = X) ∧
      ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) = act (α ℓ) (Multiplicative.toAdd (β u)) := by
  have hU := blockU_eq_pCoreOf hF hH h M
  have hZ := blockZ_eq_bot hfix M hU
  have hrange : ∀ l : ↥L, M.F.M l ∈ R.rho.range := by
    intro l
    obtain ⟨t, ht⟩ := R.surj _ (M.imgL l l.2)
    exact ⟨t, Units.ext ht⟩
  let α : ↥L →* T :=
    ((MonoidHom.ofInjective R.inj).symm : R.rho.range ≃* T).toMonoidHom.comp
      (M.F.M.codRestrict R.rho.range hrange)
  have hα : ∀ l : ↥L, R.rho (α l) = M.F.M l := by
    intro l
    have := (MonoidHom.ofInjective R.inj).apply_symm_apply ⟨M.F.M l, hrange l⟩
    exact congrArg Subtype.val this
  let e1 : ↥(blockU L) ≃* ↥(pCoreOf 2 L) := MulEquiv.subgroupCongr hU
  let β : ↥(blockU L) →* Multiplicative Mod :=
    (AddMonoidHom.toMultiplicative ψ).comp (M.F.φ.comp e1.toMonoidHom)
  have hβ : ∀ u : ↥(blockU L), Multiplicative.toAdd (β u) =
      ψ (Multiplicative.toAdd (M.F.φ (e1 u))) := fun u => rfl
  have hφinj : Function.Injective M.F.φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    have := (M.F.ker e).mp he
    rw [Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : ψ (Multiplicative.toAdd (M.F.φ (e1 u))) = ψ (Multiplicative.toAdd (M.F.φ (e1 v))) := by
      rw [← hβ, ← hβ, huv]
    have h2 := hψ h1
    exact e1.injective (hφinj (Multiplicative.toAdd.injective h2))
  refine ⟨α, β, ?_, ?_, hβinj, ?_, ?_, ?_⟩
  ·
    intro t
    obtain ⟨l, -, hl⟩ := M.surjL _ (R.mem t)
    refine ⟨l, R.inj ?_⟩
    rw [hα l]
    exact Units.ext hl
  ·
    ext l
    rw [MonoidHom.mem_ker, mem_pCore_iff_pCoreOf, ← M.kerL l l.2, ← hα l]
    constructor
    · intro h1; rw [h1, map_one]
    · intro h1; exact R.inj (by rw [h1, map_one])
  ·
    rw [hZ, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
    exact hβinj
  ·
    intro X
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, (hβ u).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨e, he⟩ := M.F.surj (Multiplicative.ofAdd v)
      refine ⟨e1.symm e, ?_⟩
      rw [hβ]
      simp [he]
  ·
    intro ℓ u v huv
    have hact' := M.F.act ℓ (e1 u) (e1 v) (by
      show (v : G) = (ℓ : G) * (u : G) * (ℓ : G)⁻¹
      exact huv)
    rw [hβ, hβ, ← hact', ← hα ℓ]
    exact hact _ _

end Model

end CFSG.GH74.QTGen4.DSGen4

