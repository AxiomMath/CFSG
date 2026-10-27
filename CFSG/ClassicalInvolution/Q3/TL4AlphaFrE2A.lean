module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2A

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem isSylow2In_self {L : Subgroup Y} (hL : IsPGroup 2 ↥L) : IsSylow2In L L :=
  ⟨le_rfl, hL, fun _ hVL _ hLV => le_antisymm hVL hLV⟩

theorem commutes_of_le (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    {L M : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hne : L ≠ M) {Q : Subgroup Y}
    (hQ : IsPGroup 2 ↥Q) (hLQ : L ≤ Q) (hMQ : M ≤ Q) : Commutes L M := by
  have h2 := E2D.isPGroup_mem hd hc hO2
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  exact Q3CP.l67Gen Y _ hd.hypOmegaGen P L
    (mem_RSet_of_isSylow2In hL (isSylow2In_self (h2 L hL))) M
    (mem_RSet_of_isSylow2In hM (isSylow2In_self (h2 M hM))) (hLQ.trans hP) (hMQ.trans hP) hne

theorem commutes_of_mem_omegaNbr (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {K B : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K) : Commutes K B := by
  have h2 := E2D.isPGroup_mem hd hc hO2
  obtain ⟨hBΔ, hne, T, hT, hTB, hTN⟩ := hB
  have hTsyl : IsSylow2In T B := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hd.hypOmegaGen hBΔ hT hTB
  have hTeq : B = T := hTsyl.2.2 B le_rfl (h2 B hBΔ) hTsyl.1
  have hBN : B ≤ Subgroup.normalizer (K : Set Y) := by
    rw [hTeq]
    exact hTN
  have hsup : IsPGroup 2 ↥(B ⊔ K) := (h2 B hBΔ).to_sup_of_normal_right' (h2 K hK) hBN
  exact commutes_of_le hd hc hO2 hK hBΔ (Ne.symm hne) hsup le_sup_right le_sup_left

theorem mul_mem_center_of_zBar_eq (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {L M : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) {α β : Finset (Fin m)} {h : α.card = 4}
    {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' b')
    (he : AE.zBar α h = AE.zBar β h') {u w : Y} (hu : IsUniqueInvolution L u)
    (hw : IsUniqueInvolution M w) : u * w ∈ Subgroup.center Y := by
  have h8 : ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nat.card ↥J = 8 := fun J hJ =>
    (E2D.card_mem hd hc hO2 J hJ).trans (by norm_num)
  have hk : (⟨u, le_pSpan hL hu.mem⟩ * ⟨w, le_pSpan hM hw.mem⟩ :
      ↥(pSpan (CoreAssembly.conjClass (tightCore R)))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, TC.Thin.phi_map_eq_zBar φ hm hL (h8 L hL) hlab hu,
      TC.Thin.phi_map_eq_zBar φ hm hM (h8 M hM) hlab' hw, he]
    exact AE.zBar_mul_self β h'
  have hz := hker hk
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  have hy : y ∈ pSpan (CoreAssembly.conjClass (tightCore R)) := by
    rw [E2D.pSpan_eq_top hc]
    exact Subgroup.mem_top y
  exact congrArg Subtype.val (hz ⟨y, hy⟩)

theorem eq_or_disjoint_of_commutes (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    {L M : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hcomm : Commutes L M)
    {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b b' : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' b')
    {u : Y} (hu : IsUniqueInvolution L u) : α = β ∨ Disjoint α β := by
  by_cases hab : α = β
  · exact Or.inl hab
  right
  have h8 : Nat.card ↥L = 8 := (E2D.card_mem hd hc hO2 L hL).trans (by norm_num)
  refine AE.disjoint_of_zBar_comm (h := h) (h' := h') hab (c := b') fun y hy => ?_
  rw [← hlab'] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  rw [← TC.Thin.phi_map_eq_zBar φ hm hL h8 hlab hu, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact hcomm u hu.mem y' (Subgroup.mem_subgroupOf.mp hy')

theorem eight_le_of_disjoint {m : ℕ} {α β : Finset (Fin m)} (h : α.card = 4)
    (h' : β.card = 4) (hd : Disjoint α β) : 8 ≤ m := by
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_univ (α ∪ β)
  rw [Fintype.card_fin] at h2
  omega

theorem eq_compl_of_disjoint {α β : Finset (Fin 8)} (h : α.card = 4) (h' : β.card = 4)
    (hd : Disjoint α β) : β = αᶜ := by
  have hsub : β ⊆ αᶜ := fun x hx =>
    Finset.mem_compl.mpr fun hxa => Finset.disjoint_left.mp hd hxa hx
  have hc : αᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, h]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hc, h'])

theorem mul_mem_center_of_labels (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≤ 8)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {B : Subgroup Y} (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hlabK : ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool),
      ((tightCore R).subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
        AE.memBar α h b)
    (hlabB : ∃ (β : Finset (Fin m)) (h' : β.card = 4) (b' : Bool),
      (B.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar β h' b')
    {v : Y} (hv : IsUniqueInvolution B v) : t * v ∈ Subgroup.center Y := by
  obtain ⟨α, h, b, hlab⟩ := hlabK
  obtain ⟨β, h', b', hlab'⟩ := hlabB
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  have hcomm := commutes_of_mem_omegaNbr hd hc hO2 hK hB
  have ht := hd.isUniqueInvolution_core
  rcases eq_or_disjoint_of_commutes hd hc hO2 hm φ hK hcomm hlab hlab' ht with hab | hdisj
  · subst hab
    exact mul_mem_center_of_zBar_eq hd hc hO2 hm φ hker hK hB.1 hlab hlab' rfl ht hv
  · have h8 := eight_le_of_disjoint h h' hdisj
    obtain rfl : m = 8 := by omega
    obtain rfl := eq_compl_of_disjoint h h' hdisj
    exact mul_mem_center_of_zBar_eq hd hc hO2 hm φ hker hK hB.1 hlab hlab'
      (AE.zBar_compl α h h') ht hv

theorem mul_mem_center_of_aeIdent (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≤ 8)
    (I : AEIdent (CoreAssembly.conjClass (tightCore R)) m) {B : Subgroup Y}
    (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {v : Y}
    (hv : IsUniqueInvolution B v) : t * v ∈ Subgroup.center Y :=
  mul_mem_center_of_labels hd hc hO2 hm hm8 I.φ I.ker_le hB
    (I.label _ (CoreAssembly.mem_conjClass_self _)) (I.label B hB.1) hv

theorem mul_mem_center_of_aeIdentOn (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≤ 8) {𝒜 : Set (Finset (Fin m))}
    {H : Subgroup (AE.AEQ m)} (I : AEIdentOn (CoreAssembly.conjClass (tightCore R)) m 𝒜 H)
    {B : Subgroup Y} (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {v : Y} (hv : IsUniqueInvolution B v) : t * v ∈ Subgroup.center Y := by
  obtain ⟨α, -, h, b, hlab⟩ := I.label _ (CoreAssembly.mem_conjClass_self _)
  obtain ⟨β, -, h', b', hlab'⟩ := I.label B hB.1
  exact mul_mem_center_of_labels hd hc hO2 hm hm8 I.φ I.ker_le hB ⟨α, h, b, hlab⟩
    ⟨β, h', b', hlab'⟩ hv

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2A
