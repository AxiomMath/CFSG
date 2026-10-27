module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivBar
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Sec2Quot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open LinearFlag CFSG.LieType.Chevalley Matrix

section SL2

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem center_SL2_eq_bot_of_charTwo [CharP k 2] : center (SL2 k) = ⊥ := by
  rw [eq_bot_iff]
  intro B hB
  obtain ⟨c, hc, hcB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hB
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcB, hc1]
  simp [Matrix.one_apply]

theorem card_SL2_of_card_four (hk : Nat.card k = 4) : Nat.card (SL2 k) = 60 := by
  let _ := Fintype.ofFinite k
  have hq : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card, hk]
  rw [Matrix.card_SL_field, hq]
  decide

theorem isSimpleGroup_SL2_of_card_four (hk : Nat.card k = 4) : IsSimpleGroup (SL2 k) := by
  have : CharP k 2 := charP_two_of_card hk
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) k) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let e : SL2 k ≃* ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center (SL2 k)))
      ⟨(injective_iff_map_eq_one _).mpr fun t ht => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          center_SL2_eq_bot_of_charTwo] at ht
        exact (mem_bot.mp ht),
      QuotientGroup.mk'_surjective _⟩
  exact e.isSimpleGroup

end SL2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_top_of_commutator_eq {H : Subgroup G} (h : ⁅H, H⁆ = H) :
    commutator ↥H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, h]

section Wsec

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
  (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
  (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) (hW : IsElemAbelian 2 (sec2W A E y))

include h11 hE16 hF hL hodd hyA hyE hyU hy3 hW

theorem exists_sl2_of_nbar : ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
    ∃ ψ : ↥(nbar (sec2W A E y) (sec2L A E)) →* SL2 k, Function.Surjective ψ ∧
      ψ.ker = center ↥(nbar (sec2W A E y) (sec2L A E)) ∧
      Odd (Nat.card (center ↥(nbar (sec2W A E y) (sec2L A E)))) := by
  set W := sec2W A E y with hWdef
  set L := sec2L A E with hLdef
  set M := nbar W L with hMdef
  have hLN : L ≤ normalizer (W : Set G) :=
    sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have hLA : L ≤ A := (sec2L_le A E).trans inf_le_left
  have hLW := sec2L_inf_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3
  have hUL : E ⊓ A ≤ L := (inf_le_inf_right A le_sup_left).trans (sup_inf_le_sec2L hF hL hodd)
  have hLU : L ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := (sec2L_le A E).trans inf_le_right
  let f : ↥L →* ↥M := ((QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))).comp
    (inclusion hLN)).codRestrict M fun l => mk_mem_nbar l.2 (hLN l.2)
  have hf_apply : ∀ l : ↥L, ((f l : ↥M) : _) =
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨l, hLN l.2⟩ := fun _ => rfl
  have hf : Function.Surjective f := by
    rintro ⟨q, m, hm, rfl⟩
    exact ⟨⟨m, mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  have hf1 : ∀ l : ↥L, f l = 1 ↔ (l : G) ∈ W := fun l => by
    rw [← Subtype.coe_inj, hf_apply, OneMemClass.coe_one, mk_eq_one_iff]
  obtain ⟨c, φ, hφs, hφk, hφU, -, -⟩ := exists_cover_projRad_zero_one hF hL hodd
  have hk := c.card_k
  have hφL := map_sec2L hF hodd hk hφs hφk hφU
  let φL : ↥L →* ↥(normalizer (projRad c.k 0 : Set (projectiveSL 3 c.k))) :=
    (φ.comp (inclusion hLA)).codRestrict _ fun l => by
      rw [← hφL]
      exact ⟨inclusion hLA l, mem_subgroupOf.mpr l.2, rfl⟩
  let gL : ↥L →* SL2 c.k := (Sec2Aut.leviHom hk).comp φL
  have hgL : Function.Surjective gL := by
    intro B
    have hB : (⟨proj 3 c.k (leviOne c.k B), leviOne_mem_normalizer B⟩ :
        ↥(normalizer (projRad c.k 0 : Set (projectiveSL 3 c.k)))).1 ∈
        ((L.subgroupOf A).map φ) := by
      rw [hφL]
      exact leviOne_mem_normalizer B
    obtain ⟨a, ha, hab⟩ := hB
    refine ⟨⟨a, mem_subgroupOf.mp ha⟩, ?_⟩
    have : φL ⟨a, mem_subgroupOf.mp ha⟩ =
        ⟨proj 3 c.k (leviOne c.k B), leviOne_mem_normalizer B⟩ := Subtype.ext hab
    change Sec2Aut.leviHom hk (φL ⟨a, mem_subgroupOf.mp ha⟩) = B
    rw [this, Sec2Aut.leviHom_leviOne]
  have hgL1 : ∀ l : ↥L, gL l = 1 ↔ φ (inclusion hLA l) ∈ projRad c.k 0 := fun l =>
    Sec2Aut.leviHom_eq_one_iff hk (φL l)
  have hker : f.ker ≤ gL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker, hf1] at hl
    rw [MonoidHom.mem_ker, hgL1, ← hφU]
    have hlU : (l : G) ∈ E ⊓ A := hLW ▸ ⟨l.2, hl⟩
    exact ⟨inclusion hLA l, mem_subgroupOf.mpr hlU, rfl⟩
  let ψ : ↥M →* SL2 c.k :=
    f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨gL, hker⟩
  have hψf : ∀ l : ↥L, ψ (f l) = gL l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hψs : Function.Surjective ψ := fun B => by
    obtain ⟨l, hl⟩ := hgL B
    exact ⟨f l, by rw [hψf, hl]⟩
  set Zc : Subgroup G := (center ↥A).map A.subtype with hZc
  have hkerZ : ψ.ker ≤ (Zc.subgroupOf L).map f := by
    intro x hx
    obtain ⟨l, rfl⟩ := hf x
    rw [MonoidHom.mem_ker, hψf, hgL1, ← hφU] at hx
    obtain ⟨u, hu, hul⟩ := hx
    have hu' : (u : G) ∈ E ⊓ A := mem_subgroupOf.mp hu
    have hz : u⁻¹ * inclusion hLA l ∈ center ↥A := by
      rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hul, inv_mul_cancel]
    refine ⟨⟨(u : G)⁻¹ * l, L.mul_mem (L.inv_mem (hUL hu')) l.2⟩,
      mem_subgroupOf.mpr ⟨_, hz, rfl⟩, ?_⟩
    obtain ⟨-, hUW, -⟩ := sec2W_facts h11 hE16 hF hL hodd hyA hyE hyU hy3
    have hfu : f ⟨u, hUL hu'⟩ = 1 := (hf1 _).mpr (hUW hu')
    rw [show (⟨(u : G)⁻¹ * l, L.mul_mem (L.inv_mem (hUL hu')) l.2⟩ : ↥L) =
      (⟨u, hUL hu'⟩ : ↥L)⁻¹ * l from rfl, map_mul, map_inv, hfu, inv_one, one_mul]
  have hZcent : (Zc.subgroupOf L).map f ≤ center ↥M := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_center_iff]
    intro x
    obtain ⟨l, rfl⟩ := hf x
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨a, ha, hza⟩ := mem_subgroupOf.mp hz
    have h := congrArg Subtype.val (mem_center_iff.mp ha ⟨l, hLA l.2⟩)
    apply Subtype.ext
    change (l : G) * z = z * l
    rw [← hza]
    exact h
  have hcentK : center ↥M ≤ ψ.ker := by
    intro z hz
    have : CharP c.k 2 := charP_two_of_card hk
    have hψz : ψ z ∈ center (SL2 c.k) := by
      rw [mem_center_iff]
      intro B
      obtain ⟨x, rfl⟩ := hψs B
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz x]
    rw [center_SL2_eq_bot_of_charTwo, mem_bot] at hψz
    exact hψz
  have hkerc : ψ.ker = center ↥M :=
    le_antisymm (hkerZ.trans hZcent) hcentK
  refine ⟨c.k, inferInstance, inferInstance, hk, ψ, hψs, hkerc, ?_⟩
  have hceq : center ↥M = (Zc.subgroupOf L).map f :=
    le_antisymm (hkerc ▸ hkerZ) hZcent
  rw [hceq]
  refine hodd.of_dvd_nat ((card_map_dvd _ _).trans ?_)
  have h1 : Nat.card (Zc.subgroupOf L) = Nat.card (Zc ⊓ L : Subgroup G) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective L.subtype_injective]
  rw [h1]
  refine (card_dvd_of_le inf_le_left).trans ?_
  rw [hZc, card_map_of_injective A.subtype_injective]

omit h11 hE16 hL hodd hyA hyE hyU hy3
  hW in
theorem commutator_nbar_sec2L (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) (hLN : sec2L A E ≤ normalizer (sec2W A E y : Set G)) :
    ⁅nbar (sec2W A E y) (sec2L A E), nbar (sec2W A E y) (sec2L A E)⁆ =
      nbar (sec2W A E y) (sec2L A E) := by
  rw [nbar, ← map_commutator, ← commutator_subgroupOf_eq hLN, commutator_sec2L hF hL hodd]

theorem isQuasisimple_nbar_sec2L : Open.IsQuasisimple ↥(nbar (sec2W A E y) (sec2L A E)) := by
  obtain ⟨k, _, _, hk, ψ, hψs, hψk, -⟩ :=
    exists_sl2_of_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have := isSimpleGroup_SL2_of_card_four hk
  refine ⟨commutator_eq_top_of_commutator_eq (commutator_nbar_sec2L hF hL hodd
    (sec2L_le_normalizer_sec2W h11 hE16 hF hL hodd hyA hyE hyU hy3 hW)), ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).isSimpleGroup

theorem nonempty_rankTwoQuot_nbar_equiv :
    Nonempty (rankTwoQuot (nbar (sec2W A E y) (sec2L A E)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨k, _, _, hk, ψ, hψs, hψk, -⟩ :=
    exists_sl2_of_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  have := isSimpleGroup_SL2_of_card_four hk
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_SL2_of_card_four hk)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans e⟩

theorem odd_card_center_nbar : Odd (Nat.card (center ↥(nbar (sec2W A E y) (sec2L A E)))) := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := exists_sl2_of_nbar h11 hE16 hF hL hodd hyA hyE hyU hy3 hW
  exact h

end Wsec

end CFSG.ComponentClassification.AS81
