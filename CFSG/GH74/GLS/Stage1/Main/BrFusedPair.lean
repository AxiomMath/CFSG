module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedModel
public import CFSG.GH74.GLS.Stage1.Main.BrFusedTrans

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Pair

variable {G : Type} [Group G] {z : G} {S : Subgroup G} {ε : Bool} {Gs : Type} [Group Gs] [Finite Gs]
  {p f : ℕ} (C : FusedCtx z S ε Gs p f)

omit [Finite Gs] in
theorem FusedCtx.pull_inf (K K' : Subgroup Gs) : C.pull (K ⊓ K') = C.pull K ⊓ C.pull K' := by
  unfold FusedCtx.pull
  have h : (K ⊓ K').subgroupOf C.X = K.subgroupOf C.X ⊓ K'.subgroupOf C.X := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [h, Subgroup.map_inf _ _ _ C.emb_injective]

omit [Finite Gs] in
theorem FusedCtx.pull_injective {K K' : Subgroup Gs} (hK : K ≤ C.X) (hK' : K' ≤ C.X)
    (h : C.pull K = C.pull K') : K = K' := by
  unfold FusedCtx.pull at h
  have h1 := Subgroup.map_injective C.emb_injective h
  have h2 := Subgroup.subgroupOf_inj.1 h1
  rwa [inf_eq_left.2 hK, inf_eq_left.2 hK'] at h2

omit [Finite Gs] in
theorem FusedCtx.card_pull {K : Subgroup Gs} (hK : K ≤ C.X) : Nat.card ↥(C.pull K) = Nat.card ↥K := by
  unfold FusedCtx.pull
  rw [Subgroup.card_map_of_injective C.emb_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

noncomputable def FusedCtx.pullEquiv {K : Subgroup Gs} (hK : K ≤ C.X) : ↥K ≃* ↥(C.pull K) :=
  (Subgroup.subgroupOfEquivOfLe hK).symm.trans
    (Subgroup.equivMapOfInjective (K.subgroupOf C.X) C.emb C.emb_injective)

omit [Finite Gs] in
theorem FusedCtx.comm_pull {K K' : Subgroup Gs} (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) :
    ∀ a ∈ C.pull K, ∀ b ∈ C.pull K', a * b = b * a := by
  rintro _ ⟨a', ha', rfl⟩ _ ⟨b', hb', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm _ ha' _ hb')

theorem FusedCtx.comps [Finite G] (hSp : IsPGroup 2 ↥(barOf z S)) :
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {C.pull C.E₁, C.pull C.E₂} := by
  have hc := C.comps_X
  have hE₁c : IsComponent (C.E₁.subgroupOf C.X) := by
    have : C.E₁.subgroupOf C.X ∈ {K : Subgroup ↥C.X | IsComponent K} := by
      rw [hc]; exact Or.inl rfl
    exact this
  have hE₂c : IsComponent (C.E₂.subgroupOf C.X) := by
    have : C.E₂.subgroupOf C.X ∈ {K : Subgroup ↥C.X | IsComponent K} := by
      rw [hc]; exact Or.inr rfl
    exact this
  have hLY : layer (CentralizerBar z) ≤ Stage1.Thm3.Sec8.layerSBar z S := by
    rw [layerSBar_eq_sup]; exact le_sup_left
  ext K
  constructor
  · intro hK
    have hKΓ : K ≤ Stage1.Thm3.Sec8.layerSBar z S := (le_sSup hK).trans hLY
    have hK' : IsComponent (K.subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)) :=
      ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hKΓ)).2 hK.1, hK.2.subgroupOf⟩
    have hK'' := isComponent_map_of_isComponent C.Ψ hK'
    have hmem : (K.subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)).map C.Ψ.toMonoidHom ∈
        ({C.E₁.subgroupOf C.X, C.E₂.subgroupOf C.X} : Set (Subgroup ↥C.X)) := by
      rw [← hc]; exact hK''
    have key : ∀ E' : Subgroup ↥C.X,
        (K.subgroupOf (Stage1.Thm3.Sec8.layerSBar z S)).map C.Ψ.toMonoidHom = E' →
        K = (E'.map C.Ψ.symm.toMonoidHom).map (Stage1.Thm3.Sec8.layerSBar z S).subtype := by
      intro E' h
      rw [← h, Subgroup.map_map, Subgroup.map_map]
      have : ((Stage1.Thm3.Sec8.layerSBar z S).subtype.comp C.Ψ.symm.toMonoidHom).comp
          C.Ψ.toMonoidHom = (Stage1.Thm3.Sec8.layerSBar z S).subtype := by
        ext x
        simp
      rw [this, Subgroup.map_subgroupOf_eq_of_le hKΓ]
    rcases hmem with h | h
    · left
      rw [C.pull_eq_map]
      exact key _ h
    · right
      rw [C.pull_eq_map]
      exact key _ h
  · rintro (rfl | rfl)
    · exact C.pull_isComponent hSp le_sup_left hE₁c
    · exact C.pull_isComponent hSp le_sup_right hE₂c

omit [Finite Gs] in
theorem FusedCtx.pull_conj (x : ↥C.X) (K : Subgroup Gs) :
    (C.pull K).map (MulAut.conj (C.emb x)).toMonoidHom =
      C.pull (K.map (MulAut.conj (x : Gs)).toMonoidHom) := by
  unfold FusedCtx.pull
  rw [Subgroup.map_map]
  have h1 : (MulAut.conj (C.emb x)).toMonoidHom.comp C.emb =
      C.emb.comp (MulAut.conj x).toMonoidHom := by
    ext a
    simp [map_mul, map_inv]
  have h2 : (K.subgroupOf C.X).map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (x : Gs)).toMonoidHom).subgroupOf C.X := by
    ext a
    simp only [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    rfl
  rw [h1, ← Subgroup.map_map, h2]

omit [Finite Gs] in
theorem map_conj_conj_of_sq {t : Gs} (ht : t * t = 1) (H : Subgroup Gs) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id Gs := by
    ext a
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    show t * (t * a * t⁻¹) * t⁻¹ = a
    rw [hinv]
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [ht]; group
  rw [this, Subgroup.map_id]

theorem FusedCtx.swap_exists [Finite G] (hcen : Cen2 G z S) :
    ∃ s ∈ S, Swaps z s (C.pull C.E₁) (C.pull C.E₂) := by
  obtain ⟨σ, hσ⟩ := C.exists_sigma' hcen
  have hs := C.pkg.data.syl
  obtain ⟨s, hs'⟩ := σ.surjective ⟨C.t₁, hs.t_mem⟩
  obtain ⟨hsC, hy, hval, -⟩ := hσ s
  have hxt : ((C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩ : ↥C.X) : Gs) = C.t₁ := by
    rw [← hval, hs']
  have hemb : C.emb (C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩) = toBar z ⟨s, hsC⟩ := by
    show ((C.Ψ.symm (C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩) : ↥(Stage1.Thm3.Sec8.layerSBar z S)) :
      CentralizerBar z) = _
    rw [MulEquiv.symm_apply_apply]
  have ht2 : C.t₁ * C.t₁ = 1 := by
    obtain ⟨c, hc'⟩ := isConj_iff.1 hs.t_conj
    have h1 := MulEquiv.orderOf_eq (MulAut.conj c) C.z₁
    rw [MulAut.conj_apply, hc'] at h1
    have : orderOf C.t₁ = 2 := by rw [h1]; exact hs.z_inv
    have := pow_orderOf_eq_one C.t₁
    rwa [‹orderOf C.t₁ = 2›, pow_two] at this
  have hinv : C.t₁⁻¹ = C.t₁ := inv_eq_of_mul_eq_one_right ht2
  refine ⟨(s : G), s.2, hsC, ?_, ?_⟩
  · show (C.pull C.E₁).map (MulAut.conj (toBar z ⟨s, hsC⟩)⁻¹).toMonoidHom = C.pull C.E₂
    rw [← hemb, ← map_inv, C.pull_conj]
    have : ((C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩)⁻¹ : ↥C.X).1 = C.t₁ := by
      rw [Subgroup.coe_inv, hxt, hinv]
    rw [this, hs.t_swap]
  · show (C.pull C.E₂).map (MulAut.conj (toBar z ⟨s, hsC⟩)⁻¹).toMonoidHom = C.pull C.E₁
    rw [← hemb, ← map_inv, C.pull_conj]
    have : ((C.Ψ ⟨toBar z ⟨s, hsC⟩, hy⟩)⁻¹ : ↥C.X).1 = C.t₁ := by
      rw [Subgroup.coe_inv, hxt, hinv]
    rw [this, ← hs.t_swap, map_conj_conj_of_sq ht2]

include C in
theorem FusedCtx.centralizer_le [Finite G] (hcen : Cen2 G z S) :
    ∀ γ : CentralizerBar z, (∀ l ∈ LBar z, l * γ = γ * l) → γ ∈ LBar z := by
  rw [C.LBar_eq_pull hcen, ← C.layer_eq_pull (isSylowOf_barOf hcen.sylow).isPGroup]
  exact C.centralizer_layer_le hcen

end Pair

section Stage2

theorem pairBridgeF_of_leaf (hfus : FusedModelLeaf) : PairBridgeF := by
  intro G _ _ z S ε hcen hE hbase
  obtain ⟨hone, Gs, iG, fG, p, f, hp, hp2, hm, hS, hC⟩ := id hE
  obtain ⟨C⟩ := fused_ctx_of hfus hcen hp hp2 hm hS hC
  have hq5 : 5 ≤ p ^ f := by
    rcases hm with ⟨-, h8, -⟩ | ⟨-, h8, h3, -⟩ <;> omega
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcomp := C.pkg.data.comps
  have hSp : IsPGroup 2 ↥(barOf z S) := (isSylowOf_barOf hcen.sylow).isPGroup
  have hLB : LBar z = C.pull C.E₁ ⊔ C.pull C.E₂ := by
    rw [C.LBar_eq_pull hcen, C.pull_sup C.E₁_le_X C.E₂_le_X]
  have hlayer : layer (CentralizerBar z) = C.pull C.E₁ ⊔ C.pull C.E₂ := by
    show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
    rw [C.comps hSp, sSup_pair]
  refine ⟨p ^ f, C.pull C.E₁, C.pull C.E₂, ⟨hbase, hodd, by omega,
    fun h => hcomp.ne (C.pull_injective C.E₁_le_X C.E₂_le_X h), ⟨hLB.symm,
      C.comm_pull (fun a ha b hb => hcomp.comm a ha b hb), ?_⟩,
    ModelLUT.hasSL2Model_of_equiv (C.pullEquiv C.E₁_le_X) hcomp.sl₁,
    ModelLUT.hasSL2Model_of_equiv (C.pullEquiv C.E₂_le_X) hcomp.sl₂, C.comps hSp, ?_, C.swap_exists hcen⟩, ?_⟩
  · rw [← C.pull_inf, C.card_pull (inf_le_left.trans C.E₁_le_X), hcomp.inf_eq, Nat.card_zpowers,
      C.pkg.data.syl.z_inv]
  · show fittingSubgroup (CentralizerBar z) ⊔ layer (CentralizerBar z) = LBar z
    have hF : fittingSubgroup (CentralizerBar z) ≤ LBar z := by
      intro f' hf
      apply C.centralizer_le hcen
      intro a ha
      have hal : a ∈ layer (CentralizerBar z) := by rw [hlayer, ← hLB]; exact ha
      have hm' : ⁅f', a⁆ ∈ ⁅fittingSubgroup (CentralizerBar z), layer (CentralizerBar z)⁆ :=
        Subgroup.commutator_mem_commutator hf hal
      rw [CFSG.LocalCores.fitting_layer_commute] at hm'
      have h1 : ⁅f', a⁆ = 1 := by simpa using hm'
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    rw [hlayer, ← hLB]
    exact sup_eq_right.2 hF
  · refine ⟨hE, Gs, iG, fG, p, f, hp, hp2, rfl, ?_, hS, hC⟩
    rcases hm with ⟨h1, -, hL⟩ | ⟨h1, -, -, hL⟩
    · exact Or.inl ⟨h1, hL⟩
    · exact Or.inr ⟨h1, hL⟩

end Stage2

theorem pairBridgeF_thm : PairBridgeF := pairBridgeF_of_leaf fusedModelLeaf

end CFSG.GH74.GLS.Stage1.Main
