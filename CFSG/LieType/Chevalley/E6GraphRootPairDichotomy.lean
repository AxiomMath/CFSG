module

public import CFSG.LieType.Chevalley.E6GraphRootPairHeisenberg
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRootPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi

section Conj

variable {G : Type*} [Group G]

theorem map_conj_mul (a b : G) (H : Subgroup G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
    Function.comp_apply]
  group

theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

theorem map_conj_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  · refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    simpa using this

theorem map_conj_of_forall {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ = x) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ fun x hx => ⟨x, hx, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h x hx]⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h y hy]
  exact hy

end Conj

section Core

variable {E : Type} [Field E] {F₀ : Type} [Field F₀]

theorem thetaRootGroup_le_rootSubgroup
    (ι : F₀ →+* E) :
    thetaRootGroup ι ≤ rootSubgroup TwistTag.E6.tag E e6HighestRoot :=
  (Subgroup.closure_le _).2 fun _ ⟨c, hc⟩ => mem_rootSubgroup.2 ⟨ι c, hc⟩

theorem isPGroup_thetaRootGroup
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) :
    IsPGroup 2 ↥(thetaRootGroup ι) := fun x =>
  ⟨1, Subtype.ext (by
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    exact rootSubgroup_mul_self h2 (thetaRootGroup_le_rootSubgroup ι x.2))⟩

theorem map_conj_canonicalRep_thetaRootGroup
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    (w : WeylGroup TwistTag.E6.tag) :
    (thetaRootGroup ι).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) E w)).toMonoidHom =
      Subgroup.closure
        (Set.range fun c : F₀ => pinnedX TwistTag.E6.tag E (w • e6HighestRoot) (ι c)) := by
  rw [thetaRootGroup, MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext c
  simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 w isRoot_e6HighestRoot (ι c)

theorem sup_map_conj_dichotomy
    (h2 : (2 : E) = 0) (ι : F₀ →+* E) (w : WeylGroup TwistTag.E6.tag)
    {b₁ b₂ : ModGL TwistTag.E6.tag E}
    (hb₁ : b₁ ∈ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)))
    (hb₂ : b₂ ∈ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E))) :
    IsPGroup 2 ↥(thetaRootGroup ι ⊔ (thetaRootGroup ι).map (MulAut.conj
        (b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b₂)).toMonoidHom) ∨
      thetaRootGroup ι ⊔ (thetaRootGroup ι).map (MulAut.conj
          (b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b₂)).toMonoidHom =
        (thetaRankOneGroup ι).map (MulAut.conj b₁).toMonoidHom := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) E w with hn
  have e : thetaRootGroup ι ⊔ (thetaRootGroup ι).map (MulAut.conj (b₁ * n * b₂)).toMonoidHom =
      (thetaRootGroup ι ⊔ (thetaRootGroup ι).map (MulAut.conj n).toMonoidHom).map
        (MulAut.conj b₁).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_of_mem_normalizer hb₁, map_conj_mul, map_conj_mul,
      map_conj_of_mem_normalizer hb₂]
  rw [e, map_conj_canonicalRep_thetaRootGroup h2 ι w]
  by_cases hθ : w • e6HighestRoot = e6HighestRoot
  · left
    rw [hθ, ← thetaRootGroup, sup_idem]
    exact (isPGroup_thetaRootGroup h2 ι).map _
  by_cases hθ' : w • e6HighestRoot = -e6HighestRoot
  · right
    rw [hθ', ← thetaNegRootGroup]
    rfl
  left
  refine IsPGroup.map (IsPGroup.to_le (isPGroup_rootSubgroup_sup h2
    (IsRoot.smul isRoot_e6HighestRoot w) hθ hθ') (sup_le_sup
      (thetaRootGroup_le_rootSubgroup ι) ((Subgroup.closure_le _).2 ?_))) _
  rintro _ ⟨c, rfl⟩
  exact mem_rootSubgroup.2 ⟨_, rfl⟩

end Core

section General

variable {E : Type} [Field E] {F₀ : Type} [Field F₀]

theorem conj_pair_dichotomy
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {G B : Subgroup (ModGL TwistTag.E6.tag E)} (hBG : B ≤ G)
    (hBN : B ≤ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)))
    (hG : ∀ g ∈ G, ∃ b₁ ∈ B, ∃ w : WeylGroup TwistTag.E6.tag, ∃ b₂ ∈ B,
      g = b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b₂)
    {g₁ g₂ : ModGL TwistTag.E6.tag E} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) :
    IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        (thetaRootGroup ι).map (MulAut.conj g₂).toMonoidHom) ∨
      ∃ g ∈ G, (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
          (thetaRootGroup ι).map (MulAut.conj g₂).toMonoidHom =
        (thetaRankOneGroup ι).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨b₁, hb₁, w, b₂, hb₂, he⟩ := hG _ (mul_mem (inv_mem hg₁) hg₂)
  have e : (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
      (thetaRootGroup ι).map (MulAut.conj g₂).toMonoidHom =
      (thetaRootGroup ι ⊔ (thetaRootGroup ι).map (MulAut.conj
        (b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b₂)).toMonoidHom).map
          (MulAut.conj g₁).toMonoidHom := by
    rw [Subgroup.map_sup, ← he, ← map_conj_mul, mul_inv_cancel_left]
  rw [e]
  rcases sup_map_conj_dichotomy h2 ι w (hBN hb₁) (hBN hb₂) with h | h
  · exact Or.inl (h.map _)
  · refine Or.inr ⟨g₁ * b₁, mul_mem hg₁ (hBG hb₁), ?_⟩
    rw [h, map_conj_mul]

theorem mem_or_of_mem_sup_zpowers {G : Subgroup (ModGL TwistTag.E6.tag E)}
    {P : ModGL TwistTag.E6.tag E} (hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G) (hPP : P * P = 1)
    {j : ModGL TwistTag.E6.tag E} (hj : j ∈ G ⊔ Subgroup.zpowers P) :
    j ∈ G ∨ ∃ a ∈ G, j = a * P := by
  have hPinv : P⁻¹ = P := (eq_inv_of_mul_eq_one_left hPP).symm
  let S : Subgroup (ModGL TwistTag.E6.tag E) :=
    { carrier := {x | x ∈ G ∨ ∃ a ∈ G, x = a * P}
      mul_mem' := by
        rintro _ _ (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr ⟨_ * b, mul_mem hx hb, by group⟩
        · refine Or.inr ⟨a * (P * _ * P⁻¹), mul_mem ha (hPG _ hy), ?_⟩
          group
        · refine Or.inl ?_
          have : a * P * (b * P) = a * (P * b * P⁻¹) := by
            rw [hPinv]
            group
          rw [this]
          exact mul_mem ha (hPG b hb)
      one_mem' := Or.inl (one_mem _)
      inv_mem' := by
        rintro _ (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨P * a⁻¹ * P⁻¹, hPG _ (inv_mem ha), ?_⟩
          rw [hPinv]
          calc (a * P)⁻¹ = P⁻¹ * a⁻¹ := by group
            _ = P * a⁻¹ * P * P := by rw [hPinv, mul_assoc (P * a⁻¹), hPP, mul_one] }
  have hle : G ⊔ Subgroup.zpowers P ≤ S :=
    sup_le (fun g hg => Or.inl hg) ((Subgroup.zpowers_le).2 (Or.inr ⟨1, one_mem _, by group⟩))
  exact hle hj

theorem involution_consequence
    (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {G B : Subgroup (ModGL TwistTag.E6.tag E)} (hBG : B ≤ G)
    (hBN : B ≤ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)))
    (hG : ∀ g ∈ G, ∃ b₁ ∈ B, ∃ w : WeylGroup TwistTag.E6.tag, ∃ b₂ ∈ B,
      g = b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b₂)
    {P : ModGL TwistTag.E6.tag E} (hPG : ∀ g ∈ G, P * g * P⁻¹ ∈ G)
    (hPR : ∀ r ∈ thetaRootGroup ι, P * r * P⁻¹ = r) (hPP : P * P = 1)
    {g₁ : ModGL TwistTag.E6.tag E} (hg₁ : g₁ ∈ G) {j : ModGL TwistTag.E6.tag E}
    (hj : j ∈ G ⊔ Subgroup.zpowers P) (hjj : j * j = 1)
    (hnot : ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
      ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom)) :
    (∃ g ∈ G, (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      (thetaRankOneGroup ι).map (MulAut.conj g).toMonoidHom) ∧
    ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
          (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom ∧
    ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom ≠
      (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ∧
    (((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
        (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom := by
  set R₁ := (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom with hR₁
  have hjj' : (R₁.map (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom = R₁ := by
    rw [← map_conj_mul, hjj, map_conj_one]
  have hR₂ : ∃ g₂ ∈ G, R₁.map (MulAut.conj j).toMonoidHom =
      (thetaRootGroup ι).map (MulAut.conj g₂).toMonoidHom := by
    rcases mem_or_of_mem_sup_zpowers hPG hPP hj with hjG | ⟨a, ha, rfl⟩
    · exact ⟨j * g₁, mul_mem hjG hg₁, by rw [hR₁, ← map_conj_mul]⟩
    · refine ⟨a * (P * g₁ * P⁻¹), mul_mem ha (hPG g₁ hg₁), ?_⟩
      rw [hR₁, ← map_conj_mul, show a * P * g₁ = a * (P * g₁ * P⁻¹) * P by group,
        map_conj_mul _ P, map_conj_of_forall hPR]
  obtain ⟨g₂, hg₂, he₂⟩ := hR₂
  refine ⟨?_, ?_, fun h => ?_, hjj'⟩
  · rcases conj_pair_dichotomy h2 ι hBG hBN hG hg₁ hg₂ with h | h
    · rw [← he₂] at h
      exact absurd h hnot
    · rwa [← he₂] at h
  · rw [Subgroup.map_sup, hjj', sup_comm]
  · apply hnot
    rw [h, sup_idem, hR₁]
    exact (isPGroup_thetaRootGroup h2 ι).map _

end General

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_root_pair_dichotomy
    (f : ℕ) (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ g₁ ∈ adjointGroup TwistTag.E6.tag k, ∀ g₂ ∈ adjointGroup TwistTag.E6.tag k,
        IsPGroup 2 ↥((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₂).toMonoidHom) ∨
        ∃ g ∈ adjointGroup TwistTag.E6.tag k,
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
              (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₂).toMonoidHom =
            (thetaRankOneGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom) ∧
    (∀ g₁ ∈ adjointGroup TwistTag.E6.tag k,
      ∀ j ∈ adjointGroup TwistTag.E6.tag k ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 k),
        j * j = 1 →
        ¬ IsPGroup 2 ↥((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
          ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom) →
        (∃ g ∈ adjointGroup TwistTag.E6.tag k,
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
              ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
                (MulAut.conj j).toMonoidHom =
            (thetaRankOneGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom) ∧
        ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
            ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
              (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ⊔
            ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
              (MulAut.conj j).toMonoidHom ∧
        ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom ≠
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom ∧
        (((thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
          (thetaRootGroup (RingHom.id k)).map (MulAut.conj g₁).toMonoidHom) ∧
    (∀ g₁ ∈ graphFixedRootGroup TwistTag.E6 K σ, ∀ g₂ ∈ graphFixedRootGroup TwistTag.E6 K σ,
        IsPGroup 2 ↥((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₂).toMonoidHom) ∨
        ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
              (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₂).toMonoidHom =
            (thetaRankOneGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom) ∧
    (∀ g₁ ∈ graphFixedRootGroup TwistTag.E6 K σ,
      ∀ j ∈ graphFixedRootGroup TwistTag.E6 K σ ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 K),
        j * j = 1 →
        ¬ IsPGroup 2 ↥((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
          ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom) →
        (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
              ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
                (MulAut.conj j).toMonoidHom =
            (thetaRankOneGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom) ∧
        ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
            ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
              (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ⊔
            ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
              (MulAut.conj j).toMonoidHom ∧
        ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom ≠
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom ∧
        (((thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
          (thetaRootGroup (algebraMap k K)).map (MulAut.conj g₁).toMonoidHom) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  obtain ⟨hNO, hNT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨hNR, -, -, -, -, -, -, -, -, -, -, hPR⟩ := hNO
  obtain ⟨hNR', -, -, -, -, -, -, -, -, -, -, hPR'⟩ := hNT
  have hBN : borelGroup TwistTag.E6.tag k ≤
      Subgroup.normalizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) :=
    fun b hb => by
      have : b ∈ parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k :=
        Subgroup.mem_inf.2 ⟨borelGroup_le_parabolicSubgroup setA hb, borelGroup_le_adjointGroup' hb⟩
      rw [← hNR] at this
      exact (Subgroup.mem_inf.1 this).1
  have hG : ∀ g ∈ adjointGroup TwistTag.E6.tag k, ∃ b₁ ∈ borelGroup TwistTag.E6.tag k,
      ∃ w : WeylGroup TwistTag.E6.tag, ∃ b₂ ∈ borelGroup TwistTag.E6.tag k,
        g = b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) k w * b₂ := by
    intro g hg
    have hg' : g ∈ (adjointGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) := hg
    rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', he⟩ := mem_bruhatCell.1 hw
    exact ⟨b, hb, w, b', hb', he.symm⟩
  have hPP := diagramMap_E6_mul_self (K := k)
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩ with hσEdef
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hB1 : graphFixedRootBorel TwistTag.E6 K σ ≤ borelGroup TwistTag.E6.tag K :=
    inf_le_left.trans inf_le_left
  have hBN' : graphFixedRootBorel TwistTag.E6 K σ ≤
      Subgroup.normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) :=
    fun b hb => by
      have : b ∈ parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ :=
        Subgroup.mem_inf.2 ⟨borelGroup_le_parabolicSubgroup setA (hB1 hb),
          graphFixedRootBorel_le _ _ _ hb⟩
      rw [← hNR'] at this
      exact (Subgroup.mem_inf.1 this).1
  have hG' : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      ∃ b₁ ∈ graphFixedRootBorel TwistTag.E6 K σ, ∃ w : WeylGroup TwistTag.E6.tag,
        ∃ b₂ ∈ graphFixedRootBorel TwistTag.E6 K σ,
          g = b₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * b₂ := by
    intro g hg
    obtain ⟨-, -, -, -, -, -, -, -, -, hU, -⟩ := fixed_root_Bruhat_decomposition TwistTag.E6 K σE
    rw [hσE] at hU
    have hg' : g ∈ (graphFixedRootGroup TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) := hg
    rw [hU] at hg'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    obtain ⟨b, hb, b', hb', he⟩ := mem_graphFixedRootBruhatCell.1 hw
    exact ⟨b, hb, w, b', hb', he.symm⟩
  have hPG' : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ := fun g hg => by
    rw [← map_conj_diagramMap_graphFixedRootGroup σE hσE hσσ]
    exact ⟨g, hg, rfl⟩
  have hPP' := diagramMap_E6_mul_self (K := K)
  refine ⟨fun g₁ hg₁ g₂ hg₂ => conj_pair_dichotomy hk2 (RingHom.id k)
      borelGroup_le_adjointGroup' hBN hG hg₁ hg₂,
    fun g₁ hg₁ j hj hjj hnot => involution_consequence hk2 (RingHom.id k)
      borelGroup_le_adjointGroup' hBN hG (fun g hg => diagramMap_conj_mem_adjointGroup' hg) hPR
      hPP hg₁ hj hjj hnot,
    fun g₁ hg₁ g₂ hg₂ => conj_pair_dichotomy hK2 (algebraMap k K)
      (graphFixedRootBorel_le _ _ _) hBN' hG' hg₁ hg₂,
    fun g₁ hg₁ j hj hjj hnot => involution_consequence hK2 (algebraMap k K)
      (graphFixedRootBorel_le _ _ _) hBN' hG' hPG' hPR' hPP' hg₁ hj hjj hnot⟩

end CFSG.LieType.Chevalley.E6GraphRootPair
