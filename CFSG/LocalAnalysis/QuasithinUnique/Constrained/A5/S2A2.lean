module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Fin2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Phi

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

section Sylow

variable {L' : Subgroup G}

theorem card_im_of_sylow (P : A5Pi L') {K : Subgroup G} (hK : IsSylowTwoOf K L') :
    Nat.card (P.im K) = 4 := by
  have hKL : K ≤ L' := hK.1
  have hK' : IsPGroup 2 (K.subgroupOf L') :=
    hK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm
  let Sy : Sylow 2 ↥L' := hK'.toSylow hK.2.2
  have h1 := sylow_card_alt_five (Sy.mapSurjective P.hα)
  have h2 : ((Sy.mapSurjective P.hα : Sylow 2 (alternatingGroup (Fin 5))) :
      Subgroup (alternatingGroup (Fin 5))) = (K.subgroupOf L').map P.α := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : P.im K = ((K.subgroupOf L').map P.α).map (alternatingGroup (Fin 5)).subtype := by
    ext σ
    rw [P.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨P.α ⟨y, hKL hyK⟩, ⟨⟨y, hKL hyK⟩, Subgroup.mem_subgroupOf.2 hyK, rfl⟩, ?_⟩
      rw [P.hπα (y : G) (hKL hyK)]
      rfl
    · rintro ⟨a, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨⟨l, Subgroup.le_normalizer l.2⟩, Subgroup.mem_subgroupOf.1 hl, ?_⟩
      rw [P.hπα (l : G) l.2]
      rfl
  rw [h3, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective, ← h2]
  exact h1

end Sylow

section Bf

variable {L' : Subgroup G}

omit [Finite G] in
theorem bf_inv_eq (D : PiData L') {u : G} (hu : u ∈ blockU L') : D.bf u⁻¹ = D.bf u := by
  have h1 := D.bf_mul hu (inv_mem hu)
  rw [mul_inv_cancel, D.bf_one] at h1
  have : D.bf u⁻¹ = -D.bf u := eq_neg_of_add_eq_zero_right h1.symm
  rw [this]
  exact neg_eq_of_add_eq_zero_right (ew_add_self _)

end Bf

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem isSylow_S_L₂ : IsSylowTwoOf (S ⊓ cj t L) (cj t L) :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal c.data.cs.sylow c.data.cs₂.block.1.2.1
    c.data.cs₂.block.1.2.2

theorem S_L₂_le_SI : S ⊓ cj t L ≤ s2SI S L :=
  le_inf inf_le_left (inf_le_right.trans c.data.L₂_le_normalizer)

theorem E_le_im_SI {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) :
    Estd ≤ P₂.im (s2SI S L) :=
  hE ▸ P₂.im_mono c.R_le_SI

theorem im_SI_fix {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) :
    ∀ σ ∈ P₂.im (s2SI S L), σ 4 = 4 :=
  fix4_of_two_group (im_two P₂.toPiData c.isPGroup_SI) (c.E_le_im_SI hE)

theorem im_V {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) :
    P₂.im (S ⊓ cj t L) = Vstd := by
  have hle : P₂.im (S ⊓ cj t L) ≤ P₂.im (s2SI S L) := P₂.im_mono c.S_L₂_le_SI
  refine V_eq_Vstd ?_ (fun σ hσ => c.im_SI_fix hE σ (hle hσ)) ?_
    (card_im_of_sylow P₂ c.isSylow_S_L₂)
  · exact fun σ hσ => im_two P₂.toPiData (c.isPGroup_S.to_le inf_le_left) σ hσ
  · intro σ hσ
    obtain ⟨y, hy, rfl⟩ := (P₂.mem_im).1 hσ
    have hyL : (y : G) ∈ cj t L := hy.2
    rw [P₂.hπα (y : G) hyL]
    exact Equiv.Perm.mem_alternatingGroup.1 (P₂.α ⟨y, hyL⟩).2

theorem D_le_im_SI {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) :
    ∀ τ ∈ Dset, τ ∈ P₂.im (s2SI S L) := by
  refine Dset_le_of (c.E_le_im_SI hE) ?_
  rw [← c.im_V hE]
  exact P₂.im_mono c.S_L₂_le_SI

theorem bf_cases {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) {u : G}
    (hu : u ∈ blockU (cj t L)) (hC : u ∈ Subgroup.centralizer (s2SI S L : Set G)) :
    P₂.bf u = 0 ∨ P₂.bf u = zv := by
  apply fix_of_D
  intro σ hσ
  obtain ⟨s, hs, rfl⟩ := (P₂.mem_im_pf c.SI_le_normalizer₂).1 (c.D_le_im_SI hE σ hσ)
  have hcomm : s * u = u * s := Subgroup.mem_centralizer_iff.1 hC s hs
  exact (P₂.comm_iff (c.SI_le_normalizer₂ hs) hu).1 hcomm

theorem exists_u₀ {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) :
    ∃ u₀ ∈ blockU (cj t L), u₀ ≠ 1 ∧ P₂.bf u₀ = zv ∧ u₀ ∈ s2Phi S L := by
  obtain ⟨w, hw⟩ := zv_comm
  obtain ⟨u', hu', hbu'⟩ := P₂.bf_surj w
  have hIN := c.I_le_normalizer₂
  have hτ₁ : swap (0 : Fin 5) 1 ∈ P₂.im (s2I S L) := hI ▸ swap01_mem
  have hτ₂ : swap (2 : Fin 5) 3 ∈ P₂.im (s2I S L) := hI ▸ swap23_mem
  obtain ⟨r₁, hr₁, hpr₁⟩ := (P₂.mem_im_pf hIN).1 hτ₁
  obtain ⟨r₂, hr₂, hpr₂⟩ := (P₂.mem_im_pf hIN).1 hτ₂
  have hu'I : u' ∈ s2I S L := c.U₂_le_I hu'
  have key : ∀ r ∈ s2I S L, ∃ c₀ ∈ blockU (cj t L), c₀ ∈ frattiniOf (s2I S L) ∧
      P₂.bf c₀ = vact (P₂.pf r) w + w := by
    intro r hr
    have hrN := hIN hr
    have h1 : r * u' * r⁻¹ ∈ blockU (cj t L) := PiData.conj_mem_U hrN hu'
    refine ⟨r * u' * r⁻¹ * u'⁻¹, mul_mem h1 (inv_mem hu'), ?_, ?_⟩
    · exact commutator_le_frattiniOf c.isPGroup_I (Subgroup.commutator_mem_commutator hr hu'I)
    · rw [P₂.bf_mul h1 (inv_mem hu'), P₂.bf_conj hrN hu', bf_inv_eq P₂.toPiData hu', hbu']
  obtain ⟨c₁, hc₁, hc₁Φ, hbc₁⟩ := key r₁ hr₁
  obtain ⟨c₂, hc₂, hc₂Φ, hbc₂⟩ := key r₂ hr₂
  rw [hpr₁] at hbc₁
  rw [hpr₂] at hbc₂
  have hbu₀ : P₂.bf (c₁ * c₂) = zv := by rw [P₂.bf_mul hc₁ hc₂, hbc₁, hbc₂, hw]
  refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, ?_, hbu₀, ?_⟩
  · intro h1
    rw [h1, P₂.bf_one] at hbu₀
    exact zv_ne_zero hbu₀.symm
  · refine ⟨mul_mem hc₁Φ hc₂Φ, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have hsN : s ∈ Subgroup.normalizer (cj t L : Set G) := c.SI_le_normalizer₂ hs
    have hs4 : P₂.pf s 4 = 4 :=
      c.im_SI_fix hE _ (pf_mem_im P₂.toPiData c.SI_le_normalizer₂ hs)
    rw [P₂.comm_iff hsN (mul_mem hc₁ hc₂), hbu₀]
    exact vact_zv hs4

end Ctx

end CFSG.QuasithinUnique.A5.S2
