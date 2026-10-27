module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEndY
import CFSG.ClassicalInvolution.Q3.TL3T60
import CFSG.ClassicalInvolution.Q3.TL3T61
import CFSG.ClassicalInvolution.Q3.Sec13StarAE5
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T50

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace CaseBU

variable {K : Subgroup G} {P₁ P₂ : Set (Subgroup G)} {g u h e : G} {T : Subgroup G}

private theorem endAE_K_mem (c : CaseBU Ω K P₁ P₂ g u h e T) : K ∈ Ω := by
  have hmem : conjSub g K ∈ dComp Ω K := by
    rw [c.dcomp]
    exact Or.inr c.gP
  have hne : conjSub g K ≠ K := fun heq => Set.disjoint_left.mp c.disj c.hK (heq ▸ c.gP)
  unfold dComp at hmem
  have hJΩ : conjSub g K ∈ Ω := by
    rcases Relation.ReflTransGen.cases_tail hmem with h1 | ⟨M, -, hM⟩
    · exact absurd h1 hne
    · exact hM.1
  have hK' := c.hyp.thmD.hyp.conjInvariant g⁻¹ _ hJΩ
  rwa [conjSub_inv_conjSub] at hK'

private theorem endAE_mem_Omega₁ (c : CaseBU Ω K P₁ P₂ g u h e T) {L : Subgroup G} (hL : L ∈ P₁) :
    L ∈ Ω := by
  by_cases hLK : L = K
  · rw [hLK]
    exact endAE_K_mem c
  · have hmem : L ∈ dComp Ω K := by
      rw [c.dcomp]
      exact Or.inl hL
    unfold dComp at hmem
    rcases Relation.ReflTransGen.cases_tail hmem with h1 | ⟨M, -, hM⟩
    · exact absurd h1 hLK
    · exact hM.1

private theorem endAE_mem_Omega (c : CaseBU Ω K P₁ P₂ g u h e T) {L : Subgroup G} (hL : L ∈ P₂) :
    L ∈ Ω := by
  have hmem : L ∈ dComp Ω K := by
    rw [c.dcomp]
    exact Or.inr hL
  unfold dComp at hmem
  rcases Relation.ReflTransGen.cases_tail hmem with h' | ⟨M, -, hM⟩
  · subst h'
    exact absurd hL (Set.disjoint_left.mp c.disj c.hK)
  · exact hM.1

private theorem endAE_conj_sub (c : CaseBU Ω K P₁ P₂ g u h e T) :
    conjSub g '' P₁ ⊆ P₂ := by
  rintro _ ⟨L, hL, rfl⟩
  exact (c.swap _).mpr (by rw [conjSub_inv_conjSub]; exact hL)

private theorem endAE_sub_centMembers (c : CaseBU Ω K P₁ P₂ g u h e T) :
    P₂ ⊆ Generic.centMembers Ω u :=
  fun L hL => ⟨endAE_mem_Omega c hL, c.P₂_u L hL⟩

private theorem endAE_conj_injective (g : G) :
    Function.Injective (conjSub g : Subgroup G → Subgroup G) := by
  intro L L' hLL'
  calc L = conjSub g⁻¹ (conjSub g L) := (conjSub_inv_conjSub g L).symm
    _ = conjSub g⁻¹ (conjSub g L') := by rw [hLL']
    _ = L' := conjSub_inv_conjSub g L'

private theorem endAE_disjoint_four {m : ℕ} (hm : 8 ≤ m) :
    ∃ (α β : Finset (Fin m)) (hα : α.card = 4) (hβ : β.card = 4), Disjoint α β := by
  let ι₁ : Fin 4 ↪ Fin m := Fin.castLEEmb (by omega)
  let ι₂ : Fin 4 ↪ Fin m :=
    ⟨fun i => ⟨i.val + 4, by omega⟩, fun a b hab => by
      apply Fin.ext
      have := congrArg Fin.val hab
      simp only [Fin.mk.injEq] at this
      omega⟩
  refine ⟨Finset.univ.map ι₁, Finset.univ.map ι₂, by simp, by simp, ?_⟩
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hy
  have h1 : (ι₁ i).val = i.val := rfl
  have h2 : (ι₂ j).val = j.val + 4 := rfl
  have h3 := congrArg Fin.val hj
  have := i.isLt
  omega

private theorem endAE_memBar_ne {m : ℕ} (hm : 5 ≤ m) {α β : Finset (Fin m)} {hα : α.card = 4}
    {hβ : β.card = 4} (hd : Disjoint α β) (b c : Bool) :
    AE.memBar α hα b ≠ AE.memBar β hβ c := by
  intro he
  obtain ⟨x, hx, x', hx', hne⟩ := AE.exists_not_comm_memBar hm α hα b
  have hx'' : x' ∈ AE.memBar β hβ c := by
    rw [← he]
    exact hx'
  exact hne (AE.comm_memBar_of_disjoint hd b c x hx x' hx'')

private theorem endAE_comm_labels (hS : StarHyp Ω) {m : ℕ} (hm : 5 ≤ m)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (h8 : ∀ L ∈ P, Nat.card L = 8) (J : AEIdent P m) {L L' : Subgroup G} (hL : L ∈ P)
    (hL' : L' ∈ P) {α β : Finset (Fin m)} {hα : α.card = 4} {hβ : β.card = 4}
    (hd : Disjoint α β) {b c : Bool}
    (hLα : (L.subgroupOf (pSpan P)).map J.φ = AE.memBar α hα b)
    (hL'β : (L'.subgroupOf (pSpan P)).map J.φ = AE.memBar β hβ c) :
    ∀ l' ∈ L', ∀ l ∈ L, l' * l = l * l' := by
  intro l' hl' l hl
  have hmem : J.φ ⟨l', le_pSpan hL' hl'⟩ ∈ AE.memBar β hβ c := by
    rw [← hL'β]
    exact J.mem_map hL' hl'
  have hg : ∀ y ∈ (L.subgroupOf (pSpan P)).map J.φ,
      J.φ ⟨l', le_pSpan hL' hl'⟩ * y = y * J.φ ⟨l', le_pSpan hL' hl'⟩ := by
    intro y hy
    rw [hLα] at hy
    exact (AE.comm_memBar_of_disjoint hd b c y hy _ hmem).symm
  have hinj : ∀ L₁ ∈ P, ∀ L₂ ∈ P,
      (L₁.subgroupOf (pSpan P)).map J.φ = (L₂.subgroupOf (pSpan P)).map J.φ → L₁ = L₂ :=
    fun L₁ hL₁ L₂ hL₂ he => StarHyp.aeIdent_map_injective hS hPΩ J hL₁ hL₂ he
  exact AEIdent.comm_member J hm h8 hconj hinj hL ⟨l', le_pSpan hL' hl'⟩ hg l hl

private theorem endAE_false_five (c : CaseBU Ω K P₁ P₂ g u h e T) (I : AEIdent P₁ 5)
    (J : AEIdent (Generic.centMembers Ω u) 5) : False := by
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun _ hL => hL.1
  have hP₁Ω : P₁ ⊆ Ω := fun L hL => endAE_mem_Omega₁ c hL
  have hinjP : ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
      (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map J.φ =
        (L'.subgroupOf (pSpan (Generic.centMembers Ω u))).map J.φ → L = L' :=
    fun L hL L' hL' he => c.hyp.toStarHyp.aeIdent_map_injective hPΩ J hL hL' he
  have hinjP₁ : ∀ L ∈ P₁, ∀ L' ∈ P₁,
      (L.subgroupOf (pSpan P₁)).map I.φ = (L'.subgroupOf (pSpan P₁)).map I.φ → L = L' :=
    fun L hL L' hL' he => c.hyp.toStarHyp.aeIdent_map_injective hP₁Ω I hL hL' he
  have hdec : (Finset.univ : Finset (Fin 5)).card.choose 4 * 2 = 10 := by decide
  have hP10 : (Generic.centMembers Ω u).ncard ≤ 10 := by
    have h := J.ncard_over_le hinjP Finset.univ
    rw [J.over_univ, hdec] at h
    exact h
  have hP₁10 : P₁.ncard = 10 := by
    have h := I.ncard_over (le_refl 5) (by norm_num) hinjP₁ Finset.univ
    rw [I.over_univ, hdec] at h
    exact h
  have hF10 : (conjSub g '' P₁).ncard = 10 := by
    rw [Set.ncard_image_of_injective _ (endAE_conj_injective g), hP₁10]
  have hTF : T ∉ conjSub g '' P₁ := fun hT => c.T_not (Or.inr (endAE_conj_sub c hT))
  have hsub : insert T (conjSub g '' P₁) ⊆ Generic.centMembers Ω u :=
    Set.insert_subset_iff.mpr
      ⟨c.T_mem, fun L hL => endAE_sub_centMembers c (endAE_conj_sub c hL)⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hTF (Set.toFinite _), hF10] at hle
  omega

private theorem endAE_false_ge_eight (c : CaseBU Ω K P₁ P₂ g u h e T) (I : AEIdent P₁ 5)
    (hI : I.φ.ker = ⊥) {m : ℕ} (hm : 8 ≤ m) (J : AEIdent (Generic.centMembers Ω u) m) :
    False := by
  have hm5 : 5 ≤ m := by omega
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun _ hL => hL.1
  have hconj : ∀ L ∈ Generic.centMembers Ω u, ∀ x ∈ pSpan (Generic.centMembers Ω u),
      conjSub x L ∈ Generic.centMembers Ω u :=
    fun L hL x hx => c.hyp.toStarHyp.conjSub_mem_centMembers hL hx
  have h8 : ∀ L ∈ Generic.centMembers Ω u, Nat.card L = 8 :=
    fun L hL => c.hyp.card_eq_eight (hPΩ hL)
  obtain ⟨α, β, hα, hβ, hd⟩ := endAE_disjoint_four hm
  obtain ⟨L₁, hL₁, h₁⟩ := J.label_surj α hα true
  obtain ⟨L₂, hL₂, h₂⟩ := J.label_surj β hβ true
  obtain ⟨L₃, hL₃, h₃⟩ := J.label_surj β hβ false
  have h12 : L₁ ≠ L₂ := fun hEq =>
    endAE_memBar_ne hm5 (hα := hα) (hβ := hβ) hd true true (by rw [← h₁, ← h₂, hEq])
  have h13 : L₁ ≠ L₃ := fun hEq =>
    endAE_memBar_ne hm5 (hα := hα) (hβ := hβ) hd true false (by rw [← h₁, ← h₃, hEq])
  have h23 : L₂ ≠ L₃ := fun hEq =>
    AE.memBar_true_ne_false hm5 β hβ (by rw [← h₂, ← h₃, hEq])
  have hc2 := endAE_comm_labels c.hyp.toStarHyp hm5 hPΩ hconj h8 J hL₁ hL₂ hd h₁ h₂
  have hc3 := endAE_comm_labels c.hyp.toStarHyp hm5 hPΩ hconj h8 J hL₁ hL₃ hd h₁ h₃
  have hKP : ∀ L' : Subgroup G, L' ∈ Generic.centMembers Ω u → L' ≠ L₁ →
      (∀ x ∈ L', ∀ l ∈ L₁, x * l = l * x) → L' ∈ KPerp Ω L₁ := by
    intro L' hL' hne hcomm
    unfold KPerp
    rw [Set.mem_insert_iff]
    refine Or.inr ?_
    unfold omegaNbr
    refine ⟨hPΩ hL', hne, L', ?_, le_rfl, ?_⟩
    · exact TC.mem_RSet_of_isPGroup (hPΩ hL')
        (IsPGroup.of_card (n := 3) (by rw [h8 L' hL']; norm_num))
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        have e := hcomm x hx n hn
        show x * n * x⁻¹ ∈ L₁
        rw [e, mul_inv_cancel_right]
        exact hn
      · intro hn
        have e := hcomm x hx (x * n * x⁻¹) hn
        have hn' : n = x * n * x⁻¹ := by
          calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
            _ = x⁻¹ * ((x * n * x⁻¹) * x) := by group
            _ = x⁻¹ * (x * (x * n * x⁻¹)) := by rw [e]
            _ = x * n * x⁻¹ := by group
        rw [hn']
        exact hn
  have hgt : 2 < (KPerp Ω L₁ ∩ Generic.centMembers Ω u).ncard :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mpr
      ⟨L₁, L₂, L₃, ⟨Set.mem_insert L₁ _, hL₁⟩, ⟨hKP L₂ hL₂ h12.symm hc2, hL₂⟩,
        ⟨hKP L₃ hL₃ h13.symm hc3, hL₃⟩, h12, h13, h23⟩
  rw [ncard_kPerp c I hI L₁ hL₁] at hgt
  omega

theorem exists_aeIdent (c : CaseBU Ω K P₁ P₂ g u h e T) (I : AEIdent P₁ 5) (hI : I.φ.ker = ⊥) :
    ∃ m : ℕ, (m = 6 ∨ m = 7) ∧ Nonempty (AEIdent (Generic.centMembers Ω u) m) := by
  have hF₂ : conjSub g '' P₁ ⊆ P₂ := endAE_conj_sub c
  have hFΩ : conjSub g '' P₁ ⊆ Ω := fun L hL => endAE_mem_Omega c (hF₂ hL)
  have hFP : conjSub g '' P₁ ⊆ Generic.centMembers Ω u :=
    fun L hL => endAE_sub_centMembers c (hF₂ hL)
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun _ hL => hL.1
  have hP₁Ω : P₁ ⊆ Ω := fun L hL => endAE_mem_Omega₁ c hL
  have hFspan : pSpan (conjSub g '' P₁) ≤ pSpan (Generic.centMembers Ω u) :=
    pSpan_le fun L hL => le_pSpan (hFP hL)
  have hconjmem : ∀ y ∈ pSpan P₁, g * y * g⁻¹ ∈ pSpan (Generic.centMembers Ω u) := by
    intro y hy
    have hcl : (pSpan P₁).map (MulAut.conj g : G →* G) ≤ pSpan (Generic.centMembers Ω u) := by
      rw [← pSpan_image_conjSub]
      exact hFspan
    exact hcl (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  have hk₁ : IsPGroup 2 I.φ.ker := by
    rw [hI]
    exact IsPGroup.of_card (n := 0) (by simp)
  have h5 : ∃ x ∈ pSpan (Generic.centMembers Ω u), x ^ 5 = 1 ∧
      ∃ w ∈ pSpan (Generic.centMembers Ω u), x * w ≠ w * x := by
    obtain ⟨x₁, hx₁, w₁, hw₁⟩ := AEIdent.exists_pow_five_not_comm I le_rfl hk₁
    have hx5 : (x₁ : G) ^ 5 = 1 := by rw [← Subgroup.coe_pow, hx₁, Subgroup.coe_one]
    refine ⟨g * (x₁ : G) * g⁻¹, hconjmem _ x₁.2, ?_, g * (w₁ : G) * g⁻¹, hconjmem _ w₁.2, ?_⟩
    · rw [conj_pow, hx5, mul_one, mul_inv_cancel]
    · intro hc
      apply hw₁
      apply Subtype.ext
      show (x₁ : G) * w₁ = w₁ * x₁
      have e1 : ∀ a b : G, g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ :=
        fun a b => by group
      rw [e1, e1] at hc
      exact mul_left_cancel (mul_right_cancel hc)
  have hK₂ : conjSub g K ∈ conjSub g '' P₁ := ⟨K, c.hK, rfl⟩
  have h3 : ∃ L ∈ Generic.centMembers Ω u, ∃ y ∈ pSpan (Generic.centMembers Ω u),
      y ^ 3 = 1 ∧ conjSub y L = L ∧ ¬ ∀ l ∈ L, y * l = l * y := by
    have h2Ω : ∀ L ∈ Ω, IsPGroup 2 L := fun L hL =>
      IsPGroup.of_card (n := 3) (by rw [c.hyp.card_eq_eight hL]; norm_num)
    obtain ⟨y₁, hy₁, hyK, hync⟩ := AEIdent.exists_pow_three_norm c.hyp.thmD.hyp h2Ω hP₁Ω
      c.inv (le_refl 5) I hk₁ c.hK
    have hy3 : (y₁ : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy₁, Subgroup.coe_one]
    refine ⟨conjSub g K, hFP hK₂, g * (y₁ : G) * g⁻¹, hconjmem _ y₁.2, ?_, ?_, ?_⟩
    · rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    · rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hyK]
    · intro hall
      apply hync
      intro l hl
      have hc := hall _ (conj_mem_conjSub hl)
      have e2 : g * ((y₁ : G) * l) * g⁻¹ = g * (l * (y₁ : G)) * g⁻¹ := by
        calc g * ((y₁ : G) * l) * g⁻¹ = g * (y₁ : G) * g⁻¹ * (g * l * g⁻¹) := by group
          _ = (g * l * g⁻¹) * (g * (y₁ : G) * g⁻¹) := hc
          _ = g * (l * (y₁ : G)) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e2)
  have hns : ∃ L ∈ Generic.centMembers Ω u, ∃ L' ∈ Generic.centMembers Ω u, L ≠ L' :=
    ⟨conjSub g K, hFP hK₂, T, c.T_mem,
      fun heq => c.T_not (Or.inr (by rw [← heq]; exact c.gP))⟩
  have hlt : Nat.card (pSpan (Generic.centMembers Ω u)) < Nat.card G :=
    c.hyp.toStarHyp.card_pSpan_centMembers_lt c.u_ne
  obtain ⟨m, hm5, ⟨J⟩⟩ := exists_aeIdent_span c.hyp.thmD c.hyp.below
    (fun L hL => c.hyp.card_eq_eight hL) hPΩ hlt (oneClass c I hI)
    (fun L hL x hx => c.hyp.toStarHyp.conjSub_mem_centMembers hL hx) hns h5 h3
  rcases (by omega : m = 5 ∨ m = 6 ∨ m = 7 ∨ 8 ≤ m) with rfl | rfl | rfl | hm8
  · exact (endAE_false_five c I J).elim
  · exact ⟨6, Or.inl rfl, ⟨J⟩⟩
  · exact ⟨7, Or.inr rfl, ⟨J⟩⟩
  · exact (endAE_false_ge_eight c I hI hm8 J).elim

end CaseBU

end CFSG.ClassicalInvolution.Q3.Sec13
