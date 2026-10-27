module

public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.LieType.HighestRoot.CentChevalleyToral
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem commute_of_mem_sup {A B : Subgroup G} {x : G} (hA : ∀ y ∈ A, Commute x y)
    (hB : ∀ y ∈ B, Commute x y) {y : G} (hy : y ∈ A ⊔ B) : Commute x y := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hA y hy).eq.symm)
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hB y hy).eq.symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

variable [Finite G]

theorem eq_or_eq_of_le_sup_of_isPerfect {J L₀ L : Subgroup G} (hJq : CFSG.IsQuasisimple J)
    (hL₀q : CFSG.IsQuasisimple L₀) (hLp : Group.IsPerfect L)
    (hLc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) (hcJ : Nat.card L ≤ Nat.card J)
    (hcL₀ : Nat.card L ≤ Nat.card L₀) (hcomm : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a)
    (hLS : L ≤ J ⊔ L₀) (hJ : J ≤ Subgroup.normalizer (L : Set G))
    (hL₀ : L₀ ≤ Subgroup.normalizer (L : Set G)) : L = J ∨ L = L₀ := by
  have hNJ : J ⊔ L₀ ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer fun b hb =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
        (hcomm a ha b hb))
  have hNL₀ : J ⊔ L₀ ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le (fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)) Subgroup.le_normalizer
  have key : ∀ {A B : Subgroup G}, CFSG.IsQuasisimple A → Nat.card L ≤ Nat.card A →
      A ≤ Subgroup.normalizer (L : Set G) → L ≤ Subgroup.normalizer (A : Set G) →
      (∀ c ∈ A, (∀ a ∈ A, c * a = a * c) → ∀ l ∈ L, c * l = l * c) →
      L = A ∨ ∀ l ∈ L, ∀ a ∈ A, l * a = a * l := by
    intro A B hAq hcA hA hLA hZA
    have hcomL : ⁅L, A⁆ ≤ L ⊓ A := by
      rw [Subgroup.commutator_le]
      intro l hl a ha
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.1 (hA ha) l⁻¹).1 (inv_mem hl)
        have e : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact mul_mem hl h
      · have h := (Subgroup.mem_normalizer_iff.1 (hLA hl) a).1 ha
        rw [commutatorElement_def]
        exact mul_mem h (inv_mem ha)
    have hnorm : ((L ⊓ A).subgroupOf A).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (hA g.2) n).1 hn.1
      · simpa using mul_mem (mul_mem g.2 hn.2) (inv_mem g.2)
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hAq
      hnorm.isSubnormal with htop | hZ
    · left
      have hAL : A ≤ L := fun a ha => by
        have : (⟨a, ha⟩ : A) ∈ (L ⊓ A).subgroupOf A := htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).1
      exact (Subgroup.eq_of_le_of_card_ge hAL hcA).symm
    · right
      have hcen : ⁅L, A⁆ ≤ Subgroup.centralizer (L : Set G) := by
        intro c hc
        have hc' := hcomL hc
        have hcZ : (⟨c, hc'.2⟩ : A) ∈ Subgroup.center A :=
          hZ (Subgroup.mem_subgroupOf.2 hc')
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        refine (hZA c hc'.2 (fun a ha => ?_) l hl).symm
        have := Subgroup.mem_center_iff.1 hcZ ⟨a, ha⟩
        exact (congrArg Subtype.val this).symm
      have h1 : ⁅⁅L, A⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcen
      have h2 : ⁅⁅A, L⁆, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm A L]
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rw [commutator_self_eq_of_isPerfect hLp, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
      intro l hl a ha
      exact (Subgroup.mem_centralizer_iff.1 (h3 hl) a ha).symm
  have hZJ : ∀ c ∈ J, (∀ a ∈ J, c * a = a * c) → ∀ l ∈ L, c * l = l * c := fun c hc hcJ l hl =>
    (commute_of_mem_sup (fun y hy => (hcJ y hy)) (fun y hy => hcomm c hc y hy) (hLS hl)).eq
  have hZL₀ : ∀ c ∈ L₀, (∀ a ∈ L₀, c * a = a * c) → ∀ l ∈ L, c * l = l * c :=
    fun c hc hcL l hl =>
      (commute_of_mem_sup (fun y hy => (hcomm y hy c hc).symm) (fun y hy => hcL y hy)
        (hLS hl)).eq
  rcases key (B := L₀) hJq hcJ hJ ((hLS.trans hNJ)) hZJ with h | hLJ
  · exact Or.inl h
  rcases key (B := J) hL₀q hcL₀ hL₀ ((hLS.trans hNL₀)) hZL₀ with h | hLL₀
  · exact Or.inr h
  exfalso
  obtain ⟨x, hx, y, hy, hxy⟩ := hLc
  exact hxy (commute_of_mem_sup (fun a ha => (hLJ x hx a ha : Commute x a))
    (fun b hb => (hLL₀ x hx b hb : Commute x b)) (hLS hy)).eq

end Abstract

section Roots

abbrev g2l : Fin (Tag.rank .G2) := ⟨0, by decide⟩

abbrev g2s : Fin (Tag.rank .G2) := ⟨1, by decide⟩

abbrev g2e0 : Fin (Tag.rank .G2) → ℤ := Pi.single g2l 1

abbrev g2δ : Fin (Tag.rank .G2) → ℤ := ![1, 2]

abbrev g2w0 : Fin (Tag.rank .G2) → ℤ := ![-1, -3]

theorem isRoot_g2δ : IsRoot .G2 g2δ :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)).2 ⟨8, by decide, by decide⟩

theorem g2_kernel_check : ∀ k < (Tag.rootCertificate .G2).roots.length,
    corootPair .G2 g2l ((Tag.rootCertificate .G2).root k) % 2 = 0 →
      (Tag.rootCertificate .G2).root k = g2e0 ∨ (Tag.rootCertificate .G2).root k = -g2e0 ∨
        (Tag.rootCertificate .G2).root k = g2δ ∨ (Tag.rootCertificate .G2).root k = -g2δ := by
  decide

theorem iform_g2e0 : iform g2e0 g2e0 = 6 := by decide

theorem g2δ_l : g2δ g2l = 1 := rfl

theorem g2δ_s : g2δ g2s = 2 := rfl

theorem g2e0_l : g2e0 g2l = 1 := by decide

theorem g2e0_s : g2e0 g2s = 0 := by decide

theorem iform_g2δ : iform g2δ g2δ = 2 := by decide

variable {K : Type} [Field K]

theorem g2_mem_kernel_iff
    (hK : ringChar K ≠ 2) (α : Fin (Tag.rank .G2) → ℤ) :
    α ∈ rootCharKernel (signTuple .G2 K g2l) ↔ α = g2e0 ∨ α = -g2e0 ∨ α = g2δ ∨ α = -g2δ := by
  rw [mem_rootCharKernel_signTuple hK]
  constructor
  · rintro ⟨hα, hev⟩
    obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)).1 hα
    exact g2_kernel_check k hk (Int.even_iff.1 hev)
  · have hev : ∀ v : Fin (Tag.rank .G2) → ℤ, corootPair .G2 g2l v % 2 = 0 →
        Even (∑ j, Tag.cartan .G2 g2l j * v j) := fun v h => Int.even_iff.2 h
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨isRoot_single _ _, hev _ (by decide)⟩
    · exact ⟨IsRoot.neg (isRoot_single _ _), hev _ (by decide)⟩
    · exact ⟨isRoot_g2δ, hev _ (by decide)⟩
    · exact ⟨IsRoot.neg isRoot_g2δ, hev _ (by decide)⟩

theorem g2_mem_kernel_of_isRoot
    {α β : Fin (Tag.rank .G2) → ℤ}
    (hα : α ∈ rootCharKernel (signTuple .G2 K g2l)) (hβ : β ∈ rootCharKernel (signTuple .G2 K g2l))
    {x y : ℕ} (h : IsRoot .G2 (x • α + y • β)) :
    x • α + y • β ∈ rootCharKernel (signTuple .G2 K g2l) := by
  refine ⟨h, ?_⟩
  rw [rootChar_add, ← natCast_zsmul, ← natCast_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul,
    CFSG.LieType.Chevalley.rootChar_zsmul, hα.2, hβ.2, one_zpow, one_zpow, mul_one]

theorem g2_not_isRoot_comb
    (hK : ringChar K ≠ 2) {α β : Fin (Tag.rank .G2) → ℤ}
    (h : ((α = g2δ ∨ α = -g2δ) ∧ (β = g2e0 ∨ β = -g2e0)) ∨
      ((α = g2e0 ∨ α = -g2e0) ∧ (β = g2δ ∨ β = -g2δ)))
    {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : ¬ IsRoot .G2 (x • α + y • β) := by
  intro hr
  have hαk : α ∈ rootCharKernel (signTuple .G2 K g2l) := by
    rw [g2_mem_kernel_iff hK]
    rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> simp [h]
  have hβk : β ∈ rootCharKernel (signTuple .G2 K g2l) := by
    rw [g2_mem_kernel_iff hK]
    rcases h with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> simp [h]
  have hk := (g2_mem_kernel_iff hK _).1 (g2_mem_kernel_of_isRoot hαk hβk hr)
  have c0 : ∀ {v w : Fin (Tag.rank .G2) → ℤ}, v = w → v g2l = w g2l := fun h => h ▸ rfl
  have c1 : ∀ {v w : Fin (Tag.rank .G2) → ℤ}, v = w → v g2s = w g2s := fun h => h ▸ rfl
  rcases h with ⟨hα | hα, hβ | hβ⟩ | ⟨hα | hα, hβ | hβ⟩ <;> subst hα hβ <;>
    rcases hk with hk | hk | hk | hk <;>
    · have h0 := c0 hk
      have h1 := c1 hk
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply] at h0 h1
      simp only [nsmul_eq_mul, mul_neg, g2δ_l, g2δ_s, g2e0_l, g2e0_s] at h0 h1
      omega

end Roots

section Centralizer

variable {K : Type} [Field K]

theorem g2_commute_root
    (hK : ringChar K ≠ 2) {α β : Fin (Tag.rank .G2) → ℤ}
    (h : ((α = g2δ ∨ α = -g2δ) ∧ (β = g2e0 ∨ β = -g2e0)) ∨
      ((α = g2e0 ∨ α = -g2e0) ∧ (β = g2δ ∨ β = -g2δ)))
    {x y : ModGL .G2 K} (hx : x ∈ rootSubgroup .G2 K α) (hy : y ∈ rootSubgroup .G2 K β) :
    Commute x y := by
  have hroot : ∀ v, v = g2e0 ∨ v = -g2e0 ∨ v = g2δ ∨ v = -g2δ → IsRoot .G2 v := by
    rintro v (rfl | rfl | rfl | rfl)
    exacts [isRoot_single _ _, IsRoot.neg (isRoot_single _ _), isRoot_g2δ,
      IsRoot.neg isRoot_g2δ]
  have hα : IsRoot .G2 α := hroot α (by rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> simp [h])
  have hβ : IsRoot .G2 β := hroot β (by rcases h with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> simp [h])
  have hne : α ≠ β ∧ α ≠ -β := by
    rcases h with ⟨hα' | hα', hβ' | hβ'⟩ | ⟨hα' | hα', hβ' | hβ'⟩ <;> subst hα' hβ' <;>
      exact ⟨by decide, by decide⟩
  exact commute_of_forall_not_isRoot hα hβ hne.1 hne.2
    (fun x y hx hy => g2_not_isRoot_comb hK h hx hy) hx hy

theorem g2_smul_eq_or_eq_neg
    (hK : ringChar K ≠ 2) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : γ = g2e0 ∨ γ = g2δ) {w : WeylGroup .G2}
    (hw : w ∈ rootCharStabilizer (signTuple .G2 K g2l)) : w • γ = γ ∨ w • γ = -γ := by
  have hγk : γ ∈ rootCharKernel (signTuple .G2 K g2l) := by
    rw [g2_mem_kernel_iff hK]
    rcases hγ with rfl | rfl <;> simp
  have hwk : w • γ ∈ rootCharKernel (signTuple .G2 K g2l) :=
    ⟨IsRoot.smul hγk.1 w, by rw [hw γ]; exact hγk.2⟩
  have hlen : iform (w • γ) (w • γ) = iform γ γ := iform_smul w γ γ
  rcases (g2_mem_kernel_iff hK _).1 hwk with h | h | h | h <;> rw [h] at hlen ⊢ <;>
    rcases hγ with rfl | rfl
  · exact Or.inl rfl
  · rw [iform_g2e0, iform_g2δ] at hlen; omega
  · exact Or.inr rfl
  · rw [iform_neg_neg, iform_g2e0, iform_g2δ] at hlen; omega
  · rw [iform_g2e0, iform_g2δ] at hlen; omega
  · exact Or.inl rfl
  · rw [iform_neg_neg, iform_g2e0, iform_g2δ] at hlen; omega
  · exact Or.inr rfl

theorem g2_toralCentralizer_le_normalizer
    (hK : ringChar K ≠ 2) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : γ = g2e0 ∨ γ = g2δ) :
    toralCentralizer .G2 K (signTuple .G2 K g2l) ≤ Subgroup.normalizer
      ((rootSubgroup .G2 K γ ⊔ rootSubgroup .G2 K (-γ) : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)) := by
  have hγr : IsRoot .G2 γ := by
    rcases hγ with rfl | rfl
    exacts [isRoot_single _ _, isRoot_g2δ]
  refine toralCentralizer_le_normalizer_pair hγr (fun α hα hne hne' x hx => ?_)
    (fun w hw => g2_smul_eq_or_eq_neg hK hγ hw)
  have hα' := (g2_mem_kernel_iff hK α).1 hα
  have hcase : ((α = g2δ ∨ α = -g2δ) ∧ (γ = g2e0 ∨ γ = -g2e0)) ∨
      ((α = g2e0 ∨ α = -g2e0) ∧ (γ = g2δ ∨ γ = -g2δ)) := by
    rcases hγ with rfl | rfl
    · rcases hα' with h | h | h | h
      · exact absurd h hne
      · exact absurd h hne'
      · exact Or.inl ⟨Or.inl h, Or.inl rfl⟩
      · exact Or.inl ⟨Or.inr h, Or.inl rfl⟩
    · rcases hα' with h | h | h | h
      · exact Or.inr ⟨Or.inl h, Or.inl rfl⟩
      · exact Or.inr ⟨Or.inr h, Or.inl rfl⟩
      · exact absurd h hne
      · exact absurd h hne'
  have hcase' : ((α = g2δ ∨ α = -g2δ) ∧ (-γ = g2e0 ∨ -γ = -g2e0)) ∨
      ((α = g2e0 ∨ α = -g2e0) ∧ (-γ = g2δ ∨ -γ = -g2δ)) := by
    rcases hcase with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> subst h2 <;> simp [h1]
  exact ⟨fun y hy => g2_commute_root hK hcase hx hy, fun y hy => g2_commute_root hK hcase' hx hy⟩

theorem g2_commute
    (hK : ringChar K ≠ 2) {x y : ModGL .G2 K}
    (hx : x ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0))
    (hy : y ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) : Commute x y := by
  have hδ : ∀ {β : Fin (Tag.rank .G2) → ℤ}, (β = g2δ ∨ β = -g2δ) →
      ∀ u ∈ rootSubgroup .G2 K β, Commute x u := fun {β} hβ u hu =>
    (commute_of_mem_sup (fun v hv => g2_commute_root hK (Or.inl ⟨hβ, Or.inl rfl⟩) hu hv)
      (fun v hv => g2_commute_root hK (Or.inl ⟨hβ, Or.inr rfl⟩) hu hv) hx).symm
  exact commute_of_mem_sup (hδ (Or.inl rfl)) (hδ (Or.inr rfl)) hy

theorem g2_rootSpan_kernel
    (hK : ringChar K ≠ 2) :
    rootSpan .G2 K (rootCharKernel (signTuple .G2 K g2l)) =
      (rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)) ⊔
        (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)) := by
  have hS : rootCharKernel (signTuple .G2 K g2l) = {g2e0, -g2e0, g2δ, -g2δ} := by
    ext α
    rw [g2_mem_kernel_iff hK]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hS, rootSpan, iSup_insert, iSup_insert, iSup_insert, iSup_singleton]
  simp only [sup_assoc]

theorem g2_w_smul :
    (simple .G2 g2s * simple .G2 g2l) • (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ) = g2δ := by
  rw [mul_smul, simple_smul, simple_smul]
  decide

theorem g2_w_smul_e0 :
    (simple .G2 g2s * simple .G2 g2l) • (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ) = g2w0 := by
  rw [mul_smul, simple_smul, simple_smul]
  decide

theorem g2_rootChar_w
    {K : Type} [Field K] (v : Fin (Tag.rank .G2) → ℤ) :
    rootChar (signTuple .G2 K g2l) ((simple .G2 g2s * simple .G2 g2l) • v) =
      rootChar (signTuple .G2 K g2s) v := by
  set w := simple .G2 g2s * simple .G2 g2l
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin (Tag.rank .G2) → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin (Tag.rank .G2) → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, CFSG.LieType.Chevalley.rootChar_sum]
  conv_rhs => rw [hv, CFSG.LieType.Chevalley.rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [CFSG.LieType.Chevalley.rootChar_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul]
  congr 1
  rw [rootChar_signTuple, rootChar_signTuple]
  fin_cases i
  · have h1 : ∑ j, Tag.cartan .G2 g2l j *
        (w • (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ)) j = 1 := by
      rw [g2_w_smul_e0]
      decide
    have h2 : ∑ j, Tag.cartan .G2 g2s j * (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ) j = -3 := by
      decide
    change (-1 : Kˣ) ^ (∑ j, Tag.cartan .G2 g2l j *
        (w • (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ)) j) =
      (-1 : Kˣ) ^ (∑ j, Tag.cartan .G2 g2s j * (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ) j)
    rw [h1, h2, (show Odd (1 : ℤ) by decide).neg_one_zpow,
      (show Odd (-3 : ℤ) by decide).neg_one_zpow]
  · have h1 : ∑ j, Tag.cartan .G2 g2l j *
        (w • (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ)) j = 0 := by
      rw [g2_w_smul]
      decide
    have h2 : ∑ j, Tag.cartan .G2 g2s j * (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ) j = 2 := by
      decide
    change (-1 : Kˣ) ^ (∑ j, Tag.cartan .G2 g2l j *
        (w • (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ)) j) =
      (-1 : Kˣ) ^ (∑ j, Tag.cartan .G2 g2s j * (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ) j)
    rw [h1, h2, (show Even (0 : ℤ) by decide).neg_one_zpow,
      (show Even (2 : ℤ) by decide).neg_one_zpow]

theorem g2_rootDiagUnit_mem_short
    (hK : ringChar K ≠ 2) :
    rootDiagUnit .G2 (signTuple .G2 K g2l) ∈
      rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_rootSubgroup_sup hK g2_w_smul
  have hconj : rootDiagUnit .G2 (signTuple .G2 K g2l) =
      canonicalRep (coxeterSystem .G2) K (simple .G2 g2s * simple .G2 g2l) *
        rootDiagUnit .G2 (signTuple .G2 K g2s) *
          (canonicalRep (coxeterSystem .G2) K (simple .G2 g2s * simple .G2 g2l))⁻¹ := by
    rw [rootDiagUnit_eq_conj_canonicalRep_iff]
    exact g2_rootChar_w
  rw [hconj, ← torusElt_neg_one_eq, ← simpleRootSL2_HSL, ← neg_one_eq_HSL_neg_one, ← he]
  exact (e (-1)).2

end Centralizer

section SLTwo

variable {K : Type} [Field K]

theorem eq_one_or_orderOf_eq_two_of_mem_center {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    A = 1 ∨ orderOf A = 2 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  by_cases h1 : A = 1
  · exact Or.inl h1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine Or.inr (orderOf_eq_prime ?_ h1)
    ext i j
    simp only [Fintype.card_fin] at hr
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrA, ← map_mul, ← pow_two, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]

variable {G : Type*} [Group G]

theorem coe_eq_one_or_eq_of_mem_center (hK : ringChar K ≠ 2) {A : Subgroup G}
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) {t : G} (ht : t ∈ A) (ht2 : orderOf t = 2)
    {x : A} (hx : x ∈ Subgroup.center A) : (x : G) = 1 ∨ (x : G) = t := by
  have hcen : eA x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g, rfl⟩ := eA.surjective g
    rw [← map_mul, ← map_mul, hx g]
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rcases eq_one_or_orderOf_eq_two_of_mem_center hcen with h | h
  · exact Or.inl (by rw [eA.map_eq_one_iff.1 h]; rfl)
  · right
    have hx2 := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 _).1 h
    have ht2' : orderOf (eA ⟨t, ht⟩) = 2 := by
      have := orderOf_injective eA.toMonoidHom eA.injective ⟨t, ht⟩
      simp only [MulEquiv.coe_toMonoidHom] at this
      rw [this, Subgroup.orderOf_mk]
      exact ht2
    have ht' := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 _).1 ht2'
    exact congrArg Subtype.val (eA.injective (hx2.trans ht'.symm))

theorem exists_not_commute_sl2 : ∃ x y : Matrix.SpecialLinearGroup (Fin 2) K, x * y ≠ y * x := by
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.sl2Upper K 1,
    CFSG.LocalAnalysis.ComponentInitial.sl2Lower K 1, fun h => ?_⟩
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [CFSG.LocalAnalysis.ComponentInitial.sl2Upper,
    CFSG.LocalAnalysis.ComponentInitial.sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] at h1

theorem isPerfect_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Group.IsPerfect B) : Group.IsPerfect A := by
  refine ⟨?_⟩
  have h := congrArg (Subgroup.map e.symm.toMonoidHom) hB.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  rw [commutator_def]
  exact h

end SLTwo

section Unique

variable {K : Type} [Field K]

theorem g2_rootDiagUnit_mem_long
    (hK : ringChar K ≠ 2) :
    rootDiagUnit .G2 (signTuple .G2 K g2l) ∈
        rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) ∧
      orderOf (rootDiagUnit .G2 (signTuple .G2 K g2l)) = 2 := by
  rw [← torusElt_neg_one_eq, ← simpleRootSL2_HSL, ← neg_one_eq_HSL_neg_one]
  refine ⟨?_, ?_⟩
  · rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
    exact ⟨_, rfl⟩
  · rw [orderOf_injective _ (simpleRootSL2_injective hK g2l)]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K (Ring.two_ne_zero hK)

variable [Finite K]

theorem g2_eq_or_eq
    (hK : ringChar K ≠ 2) {L : Subgroup (ModGL .G2 K)}
    (hLX : L ≤ toralCentralizer .G2 K (signTuple .G2 K g2l))
    (hLN : rootSpan .G2 K (rootCharKernel (signTuple .G2 K g2l)) ≤
      Subgroup.normalizer (L : Set (ModGL .G2 K)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    L = rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) ∨
      L = rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) := by
  have : Finite (ModGL .G2 K) := finite_modGL
  have ha : ∀ i, signTuple .G2 K g2l i = 1 ∨ signTuple .G2 K g2l i = -1 := by
    intro i
    rcases Int.even_or_odd (Tag.cartan .G2 g2l i) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  set J := rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0) with hJdef
  set L₀ := rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) with hL₀def
  have hJS : rootSpan .G2 K (rootCharKernel (signTuple .G2 K g2l)) = J ⊔ L₀ :=
    g2_rootSpan_kernel hK
  obtain ⟨-, ⟨eJ⟩, -, hfinJ⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 K hK
    (isRoot_single .G2 g2l)
  obtain ⟨-, ⟨eL₀⟩, -, hfinL₀⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 K hK isRoot_g2δ
  have hcomm : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a := fun a ha b hb => (g2_commute hK ha hb).eq
  have hJN : J ≤ Subgroup.normalizer (L : Set (ModGL .G2 K)) :=
    le_sup_left.trans (hJS ▸ hLN)
  have hL₀N : L₀ ≤ Subgroup.normalizer (L : Set (ModGL .G2 K)) :=
    le_sup_right.trans (hJS ▸ hLN)
  obtain ⟨hzJ, hz2⟩ := g2_rootDiagUnit_mem_long (K := K) hK
  have hzL₀ := g2_rootDiagUnit_mem_short (K := K) hK
  have hq : Nat.card K = 3 ∨ 5 ≤ Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    have hodd := FiniteField.odd_card_of_char_ne_two hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [Nat.card_eq_fintype_card] at h1 ⊢
    omega
  rcases hq with h3 | h5
  ·
    have hLS : L ≤ J ⊔ L₀ := hJS ▸ le_rootSpan_of_closure_eq_top h3 hK ha hLX
      (closure_orderOf_three_eq_top_of_mulEquiv h3 eL)
    refine eq_or_eq_of_le_sup h3 eJ.symm eL₀.symm eL hcomm ?_ ?_ ?_ hLS hJN hL₀N
    ·
      have hsub : ((J ⊓ L₀ : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) ⊆
          {1, rootDiagUnit .G2 (signTuple .G2 K g2l)} := by
        intro x hx
        have hxZ : (⟨x, hx.1⟩ : J) ∈ Subgroup.center J := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hcomm _ g.2 _ hx.2)
        rcases coe_eq_one_or_eq_of_mem_center hK eJ.symm hzJ hz2 hxZ with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc Nat.card (J ⊓ L₀ : Subgroup (ModGL .G2 K))
          = Nat.card ((J ⊓ L₀ : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := rfl
        _ ≤ Nat.card ({1, rootDiagUnit .G2 (signTuple .G2 K g2l)} : Set (ModGL .G2 K)) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
            rw [Nat.card_coe_set_eq]
            exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    · intro x hx
      rcases coe_eq_one_or_eq_of_mem_center hK eJ.symm hzJ hz2 hx with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact hzL₀
    · intro x hx
      rcases coe_eq_one_or_eq_of_mem_center hK eL₀.symm hzL₀ hz2 hx with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact hzJ
  ·
    have hperf : Group.IsPerfect L := isPerfect_of_mulEquiv eL
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl
        (Or.inr (by omega)) (Or.inr (by omega)))
    have hLS : L ≤ J ⊔ L₀ := hJS ▸ le_rootSpan_of_isPerfect hK ha hLX hperf
    have hJq := ((@hfinJ inferInstance).2 h5).1
    have hL₀q := ((@hfinL₀ inferInstance).2 h5).1
    obtain ⟨x, y, hxy⟩ := exists_not_commute_sl2 (K := K)
    have hLc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x :=
      ⟨eL.symm x, (eL.symm x).2, eL.symm y, (eL.symm y).2, fun h => hxy (by
        have h' : eL.symm x * eL.symm y = eL.symm y * eL.symm x := Subtype.ext h
        rw [← map_mul, ← map_mul] at h'
        exact eL.symm.injective h')⟩
    have hcard : ∀ {A : Subgroup (ModGL .G2 K)},
        (Matrix.SpecialLinearGroup (Fin 2) K ≃* A) → Nat.card L ≤ Nat.card A := fun {A} eA =>
      (Nat.card_congr (eL.trans eA).toEquiv).le
    exact eq_or_eq_of_le_sup_of_isPerfect hJq hL₀q hperf hLc (hcard eJ) (hcard eL₀) hcomm hLS
      hJN hL₀N

end Unique

end CFSG.LieType.HighestRoot
