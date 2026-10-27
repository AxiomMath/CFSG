module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatContract
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDefs

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Transport

variable {H G : Type*} [Group H] [Group G] (f : H →* G) (hf : Function.Injective f)

omit [Group G] in
theorem ker_comp_symm' {A B T : Type*} [Group A] [Group B] [Group T] (ε : A ≃* B) (g : A →* T) :
    (g.comp ε.symm.toMonoidHom).ker = g.ker.map ε.toMonoidHom := by
  ext y
  constructor
  · intro hy
    exact ⟨ε.symm y, hy, ε.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    change g (ε.symm (ε x)) = 1
    rw [ε.symm_apply_apply]
    exact hx

include hf

theorem map_subgroupOf_of_coe' {X : Subgroup H} {X' : Subgroup G} (e : X ≃* X')
    (he : ∀ x : X, (e x : G) = f x) (L : Subgroup H) :
    (L.subgroupOf X).map e.toMonoidHom = (L.map f).subgroupOf X' := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, (he x).symm⟩
  · rintro ⟨g, hg, hgy⟩
    refine ⟨e.symm y, Subgroup.mem_subgroupOf.mpr ?_, e.apply_symm_apply y⟩
    have h1 : f (e.symm y : H) = (y : G) := by rw [← he, e.apply_symm_apply]
    rw [hf (h1.trans hgy.symm)]
    exact hg

theorem exists_blockU_mulEquiv' (L : Subgroup H) :
    ∃ e : blockU L ≃* blockU (L.map f), ∀ u : blockU L, (e u : G) = f u :=
  ⟨((blockU L).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (blockU_map_injective f hf L).symm), fun _ => rfl⟩

theorem exists_typeWitness_map' {L : Subgroup H} {T M : Type*} [Group T] [Group M]
    (R : T → M → M → Prop)
    (h : ∃ α : L →* T, Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
      ∃ β : blockU L →* M, Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
        ∀ (ℓ : L) (u v : blockU L), (v : H) = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v)) :
    ∃ α : L.map f →* T, Function.Surjective α ∧
      α.ker = CFSG.pCore 2 (L.map f) ∧
      ∃ β : blockU (L.map f) →* M, Function.Surjective β ∧
        β.ker = (blockZ (L.map f)).subgroupOf (blockU (L.map f)) ∧
        ∀ (ℓ : L.map f) (u v : blockU (L.map f)),
          (v : G) = ℓ * u * ℓ⁻¹ → R (α ℓ) (β u) (β v) := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  obtain ⟨e, he⟩ := exists_blockU_mulEquiv' f hf L
  set ε := L.equivMapOfInjective f hf
  refine ⟨α.comp ε.symm.toMonoidHom, hαs.comp ε.symm.surjective, ?_,
    β.comp e.symm.toMonoidHom, hβs.comp e.symm.surjective, ?_, fun ℓ u v huv => ?_⟩
  · rw [ker_comp_symm', hαk, CFSG.pCore_map_iso]
  · rw [ker_comp_symm', hβk, map_subgroupOf_of_coe' f hf e he, blockZ_map_injective f hf]
  · have hv : f (e.symm v : H) = v := by rw [← he, e.apply_symm_apply]
    have hu : f (e.symm u : H) = u := by rw [← he, e.apply_symm_apply]
    have hl : f (ε.symm ℓ : H) = ℓ := by
      change ((ε (ε.symm ℓ) : L.map f) : G) = ℓ
      rw [ε.apply_symm_apply]
    refine hR (ε.symm ℓ) (e.symm u) (e.symm v) (hf ?_)
    rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, hv, hu, hl, huv, Subgroup.coe_inv]

theorem IsLin2Type.map_of_injective {L : Subgroup H} {n : ℕ} (h : IsLin2Type L n) :
    IsLin2Type (L.map f) n := by
  obtain ⟨F, _, _, hF, hw⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF, exists_typeWitness_map' f hf
    (fun (t : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Multiplicative (Fin 2 → F)) =>
      Multiplicative.toAdd y = (t : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x))
    hw⟩

theorem IsAltType.map_of_injective {L : Subgroup H} {m : ℕ} (h : IsAltType L m) :
    IsAltType (L.map f) m :=
  exists_typeWitness_map' f hf
    (fun (t : alternatingGroup (Fin m)) (x y : Multiplicative (evenWeight m)) =>
      ∀ i : Fin m, ((Multiplicative.toAdd y : evenWeight m) : Fin m → ZMod 2) i =
        ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2)
          ((t : Equiv.Perm (Fin m))⁻¹ i)) h

theorem IsChi0Block.map_of_injective {X L : Subgroup H} (h : IsChi0Block X L) :
    IsChi0Block (X.map f) (L.map f) := by
  obtain ⟨⟨hs, hLX, hsub⟩, ht⟩ := h
  refine ⟨⟨IsShort2.map_of_injective f hf hs, Subgroup.map_mono hLX,
    isSubnormal_map_injective f hf hsub⟩, ?_⟩
  rcases ht with ⟨n, hn, hl⟩ | ha | ha
  · exact Or.inl ⟨n, hn, IsLin2Type.map_of_injective f hf hl⟩
  · exact Or.inr (Or.inl (IsAltType.map_of_injective f hf ha))
  · exact Or.inr (Or.inr (IsAltType.map_of_injective f hf ha))

end Transport

section Commutators

variable {G : Type} [Group G]

theorem modComm_autOn {B V : Subgroup G} (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    modComm V (autOn B V) = ⁅B, V⁆ := by
  unfold modComm
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, v, rfl⟩
    obtain ⟨g', hg'B, rfl⟩ := mem_autOn_iff.1 ha
    refine ⟨g', hg'B, v, v.2, ?_⟩
    rw [coe_conjAct_apply]
    simp only [commutatorElement_def]
  · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    refine ⟨conjAct V ⟨g₁, hB hg₁⟩, mem_autOn_iff.2 ⟨⟨g₁, hB hg₁⟩, hg₁, rfl⟩, ⟨g₂, hg₂⟩, ?_⟩
    rw [coe_conjAct_apply]
    simp only [commutatorElement_def]

theorem commutator_le_of_normalizes {B V : Subgroup G} (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    ⁅B, V⁆ ≤ V := by
  rw [Subgroup.commutator_comm]
  exact Campbell.commutator_le_left_of_normalizes hB

theorem commutator_commutator_eq {B V : Subgroup G} (hB : B ≤ Subgroup.normalizer (V : Set G))
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hperf : ⁅autOn B V, autOn B V⁆ = autOn B V) :
    ⁅B, ⁅B, V⁆⁆ = ⁅B, V⁆ := by
  set N : Subgroup G := ⁅B, ⁅B, V⁆⁆ with hN
  have hBV : ⁅B, V⁆ ≤ V := commutator_le_of_normalizes hB
  have hnormBV : B ≤ Subgroup.normalizer ((⁅B, V⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left B V
  have hNle : N ≤ ⁅B, V⁆ := by
    rw [hN, Subgroup.commutator_comm]
    exact Campbell.commutator_le_left_of_normalizes hnormBV
  have hNB : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N := fun b hb n hn =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator_left B (⁅B, V⁆ : Subgroup G) hb) n).mp hn
  have hNV : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ = n := by
    intro v hv n hn
    rw [hV v hv n (hBV (hNle hn)), mul_inv_cancel_right]
  have hHW : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ v ∈ V, ⁅⁅b₁, b₂⁆, v⁆ ∈ N := by
    intro x hx y hy z hz
    have e : ⁅⁅x, y⁆, z⁆ = ((x * z) * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * (x * z)⁻¹ *
        ((x * y) * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * (x * y)⁻¹))⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hp1 : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
      refine Subgroup.commutator_mem_commutator hy ?_
      rw [← commutatorElement_inv]
      exact (⁅B, V⁆).inv_mem (Subgroup.commutator_mem_commutator (B.inv_mem hx) (V.inv_mem hz))
    have hp2 : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N :=
      Subgroup.commutator_mem_commutator (B.inv_mem hx)
        (Subgroup.commutator_mem_commutator (B.inv_mem hy) hz)
    rw [e]
    refine N.inv_mem (N.mul_mem ?_ ?_)
    · have : (x * z) * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * (x * z)⁻¹ =
          x * (z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹) * x⁻¹ := by group
      rw [this, hNV z hz _ (N.inv_mem hp1)]
      exact hNB x hx _ (N.inv_mem hp1)
    · exact hNB (x * y) (B.mul_mem hx hy) _ (N.inv_mem hp2)
  let T : Subgroup G :=
    { carrier := {c | c ∈ B ∧ ∀ v ∈ V, ⁅c, v⁆ ∈ N}
      one_mem' := ⟨B.one_mem, fun v _ => by simp⟩
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩
        refine ⟨B.mul_mem hc₁ hc₂, fun v hv => ?_⟩
        have e : ⁅c₁ * c₂, v⁆ = c₁ * ⁅c₂, v⁆ * c₁⁻¹ * ⁅c₁, v⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem (hNB c₁ hc₁ _ (h₂ v hv)) (h₁ v hv)
      inv_mem' := by
        rintro c ⟨hc, h⟩
        refine ⟨B.inv_mem hc, fun v hv => ?_⟩
        have e : ⁅c⁻¹, v⁆ = c⁻¹ * ⁅c, v⁆⁻¹ * c := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := hNB c⁻¹ (B.inv_mem hc) _ (N.inv_mem (h v hv))
        simpa using this }
  have hT : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ ≤ T.subgroupOf B := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact ⟨(⁅x, y⁆ : ↥B).2, fun v hv => hHW x x.2 y y.2 v hv⟩
  have hBV' : ⁅B, V⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro b hb v hv
    set ρ : ↥B →* MulAut V := rho V B hB with hρ
    have h1 : ρ ⟨b, hb⟩ ∈ Subgroup.map ρ ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hρ, range_rho hB, hperf]
      exact (mem_autOn_self_iff hB).2 ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨c, hc, hcb⟩ := h1
    have h2 : ⁅(c : G), v⁆ ∈ N := (hT hc).2 v hv
    have h3 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hcb
    simp only [hρ, rho_apply_coe] at h3
    have : ⁅b, v⁆ = ⁅(c : G), v⁆ := by
      simp only [commutatorElement_def]
      rw [h3]
    rw [this]
    exact h2
  exact le_antisymm hNle hBV'

end Commutators

section Chi0Ext

variable {H : Type*} [Group H] [Finite H] {k : Type} [Field k] [Finite k] [CharP k 2]
  {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem natural_chi0_block_ext (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card k = 2 ^ n)
    (hGb : baumannOvergroup R = ⊤) :
    IsChi0Block (⊤ : Subgroup H) (oddOrderSubgroup (⊤ : Subgroup H)) ∧
      (1 < n → IsLin2Type (oddOrderSubgroup (⊤ : Subgroup H)) n) ∧
      (n = 1 → IsAltType (oddOrderSubgroup (⊤ : Subgroup H)) 3 ∧
        Nonempty (↥(oddOrderSubgroup (⊤ : Subgroup H)) ≃* alternatingGroup (Fin 4)) ∧
        Nat.card (↥(oddOrderSubgroup (⊤ : Subgroup H)) ⧸
          CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H))) = 3) ∧
      ⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ =
        ⁅V, oddOrderSubgroup (⊤ : Subgroup H)⁆ ∧
      blockU (oddOrderSubgroup (⊤ : Subgroup H)) =
        ⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ ∧
      (⊤ : Subgroup H) ⊓ Subgroup.centralizer
        ((⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ : Subgroup H) : Set H) =
        blockQ (⊤ : Subgroup H) ∧
      Nat.card ↥(⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ : Subgroup H) =
        Nat.card ↥((⁅blockQ (⊤ : Subgroup H), oddOrderSubgroup (⊤ : Subgroup H)⁆ : Subgroup H) ⊓
          Subgroup.centralizer ((⊤ : Subgroup H) : Set H)) * Nat.card k ^ 2 := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set Gb : Subgroup H := baumannOvergroup R with hGbdef
  obtain ⟨h1, h3, hρG, hVmod, -, hQK, hVE, βo, hβs, hβk, hβe⟩ :=
    h.actual_Campbell_natural_minimal_parabolic_output hchar hnc hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, hKodd, -⟩ :=
    h.actual_Baumann_whole_center_natural_module hchar hnc hJ
  have hmem := h.rho_mem_baumannOvergroup hJ
  have hLG : L ≤ Gb := le_sup_left
  have hVG : V ≤ Gb := by rw [hGb]; exact le_top
  have hQmap : blockQ Gb = (CFSG.pCore 2 ↥Gb).map Gb.subtype := blockQ_eq_map Gb
  have hKodd' : (Kodd ↥Gb).map Gb.subtype = L := hKodd
  have hUmap : (⁅blockQ Gb, L⁆ : Subgroup H) = (⁅CFSG.pCore 2 ↥Gb, Kodd ↥Gb⁆).map Gb.subtype := by
    rw [hQmap, ← hKodd', Subgroup.map_commutator]
  have hcentral : (⁅blockQ Gb, L⁆ : Subgroup H) ≤
      Subgroup.centralizer ((blockQ Gb : Subgroup H) : Set H) := by
    rw [hUmap, hQK]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [hQmap] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hxE := hVE hx
    have := (mem_centerTorsion_iff.mp hxE).2.1 p hp
    exact congrArg Subtype.val this
  have hsetup : NaturalOvergroupSetup Gb L :=
    { charTwo := h3
      le := hLG
      normal := inferInstance
      noPQ := hasNoTwoQuotient_oddOrderSubgroup ⊤
      two_quot := fun x _ => exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) trivial
      central := hcentral }
  let ρ₀ : ↥Gb →* Matrix.SpecialLinearGroup (Fin 2) k := h.actualRho hJ
  let W : Subgroup ↥Gb := ⁅CFSG.pCore 2 ↥Gb, Kodd ↥Gb⁆
  let eU : ↥(⁅blockQ Gb, L⁆ : Subgroup H) ≃* ↥W :=
    (MulEquiv.subgroupCongr hUmap).trans (W.equivMapOfInjective Gb.subtype Gb.subtype_injective).symm
  have heU : ∀ u : ↥(⁅blockQ Gb, L⁆ : Subgroup H), (((eU u : ↥W) : ↥Gb) : H) = (u : H) := by
    intro u
    have h3' := (W.equivMapOfInjective Gb.subtype Gb.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hUmap u)
    have h4' := congrArg (fun z : ↥(W.map Gb.subtype) => (z : H)) h3'
    rw [Subgroup.coe_equivMapOfInjective_apply] at h4'
    exact h4'
  let β' : ↥(⁅blockQ Gb, L⁆ : Subgroup H) →* Multiplicative (Fin 2 → k) := βo.comp eU.toMonoidHom
  have hmod : NaturalOvergroupModule Gb L Gb ρ₀ β' :=
    { KD := hLG
      DX := le_rfl
      ρ_surj := restrictSL_surjective ρ Gb hmem hρG
      β_surj := hβs.comp eU.surjective
      β_ker := by
        ext u
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        show βo (eU u) = 1 ↔ _
        have hkerβ : βo (eU u) = 1 ↔ (eU u) ∈ (W ⊓ Subgroup.center ↥Gb).subgroupOf W := by
          rw [← hβk]; exact MonoidHom.mem_ker.symm
        rw [hkerβ, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨u.2, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have := Subgroup.mem_center_iff.mp hx.2 ⟨g, hg⟩
          have h5 := congrArg Subtype.val this
          rw [← heU u]
          exact h5
        · intro hx
          refine Subgroup.mem_inf.mpr ⟨(eU u).2, Subgroup.mem_center_iff.mpr fun g => ?_⟩
          apply Subtype.ext
          have := Subgroup.mem_centralizer_iff.mp hx.2 (g : H) g.2
          show (g : H) * ((eU u : ↥W) : ↥Gb) = ((eU u : ↥W) : ↥Gb) * (g : H)
          rw [heU u]
          exact this
      β_equiv := by
        intro d u u' hu'
        have := hβe d (eU u) (eU u') (Subtype.ext (by
          show (((eU u' : ↥W) : ↥Gb) : H) = (d : H) * (((eU u : ↥W) : ↥Gb) : H) * (d : H)⁻¹
          rw [heU u', heU u]; exact hu'))
        exact this }
  obtain ⟨-, hcentU, -, -, hshort, hchi, hUK, -, -, hLin, hAlt⟩ :=
    natural_overgroup_recognizes_actual_chi0_block hn hcard hsetup hmod
  have hsubn : (L.subgroupOf (⊤ : Subgroup H)).IsSubnormal := by
    have : (L.subgroupOf (⊤ : Subgroup H)).Normal := inferInstance
    exact this.isSubnormal
  have hE : (⁅blockQ Gb, L⁆ : Subgroup H) = ⁅V, L⁆ := by
    rw [hUmap, hQK, hVmod, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVG, hKodd']
  have hcardU : Nat.card ↥(⁅blockQ Gb, L⁆ : Subgroup H) =
      Nat.card ↥((⁅blockQ Gb, L⁆ : Subgroup H) ⊓ Subgroup.centralizer (Gb : Set H)) *
        Nat.card k ^ 2 := by
    have h1 := β'.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective β' hmod.β_surj,
      Subgroup.card_top, hmod.β_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : (⁅blockQ Gb, L⁆ : Subgroup H) ⊓ Subgroup.centralizer (Gb : Set H) ≤
          ⁅blockQ Gb, L⁆)).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → k) ≃ (Fin 2 → k))] at h1
    rw [← h1]
    simp [Nat.card_fun]
  rw [hGb] at hE hUK hcentU hcardU
  exact ⟨⟨⟨hshort, le_top, hsubn⟩, hchi.2⟩, fun hn1 => (hLin hn1).2, fun hn1 => by
    obtain ⟨hcard3, hA4, hA⟩ := hAlt hn1
    exact ⟨hA, hA4, hcard3⟩, hE, hUK, hcentU, hcardU⟩

end Chi0Ext

end CFSG.QuasithinUnique.Setup.Lift.Piece
