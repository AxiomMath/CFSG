module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElementAux1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace MElt

variable {τ : Tag} {K : Type} [Field K]

theorem exists_M_of_Uneg_conj {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (h3 : 3 ≤ Nat.card K) (hXH : X₁ ⊔ X₂ ≤ H)
    {q : ModGL τ K} (hq : q ∈ Qθ τ K) (hBH : conjSub q (Heis.Uneg τ K) ≤ H)
    (hBX : ¬ conjSub q (Heis.Uneg τ K) ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  classical
  have hs := heisCoord_spec τ K
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  have hUnegX : Heis.Uneg τ K ≤ X₁ ⊔ X₂ := hb.Uneg_le.trans hX₁X
  have hUθX : Uθ τ K ≤ X₁ ⊔ X₂ := hb.Uθ_le.trans hX₁X
  have hUθH : Uθ τ K ≤ H := hUθX.trans hXH
  have hq' : heisCoord τ K q ∈ VS (X₁ ⊔ X₂) ⊔ VM (X₁ ⊔ X₂) := by
    rw [hco.sup_eq_top]
    exact fun β hβ => hs.support q hq β hβ
  obtain ⟨uS, huS, m, hm, hsum⟩ := Submodule.mem_sup.1 hq'
  obtain ⟨s, hsR, hsc⟩ := exists_mem_Rθ_of_mem_VS hb huS
  have hsX : s ∈ X₁ ⊔ X₂ := hsR.1
  have hsQ : s ∈ Qθ τ K := hsR.2
  obtain ⟨v, hv⟩ : ∃ v : ModGL τ K, v = s⁻¹ * q := ⟨_, rfl⟩
  have hvQ : v ∈ Qθ τ K := by
    rw [hv]
    exact mul_mem (inv_mem hsQ) hq
  have hvc : heisCoord τ K v = m := by
    rw [hv, hs.mul _ (inv_mem hsQ) _ hq, heisCoord_inv hsQ, hsc, ← hsum]
    abel
  have hB'eq : conjSub v (Heis.Uneg τ K) = conjSub s⁻¹ (conjSub q (Heis.Uneg τ K)) := by
    rw [hv, conjSub_mul]
  have hB'H : conjSub v (Heis.Uneg τ K) ≤ H := by
    rw [hB'eq]
    exact conjSub_le_of_mem_of_le (inv_mem (hXH hsX)) hBH
  have hm0 : m ≠ 0 := by
    intro h0
    apply hBX
    have hvU : v ∈ Uθ τ K := (hs.eq_zero_iff v hvQ).1 (by rw [hvc, h0])
    have hB'X : conjSub v (Heis.Uneg τ K) ≤ X₁ ⊔ X₂ :=
      conjSub_le_of_mem_of_le (hUθX hvU) hUnegX
    have e : conjSub q (Heis.Uneg τ K) = conjSub s (conjSub v (Heis.Uneg τ K)) := by
      rw [hB'eq]
      exact (conjSub_conjSub_inv s _).symm
    rw [e]
    exact conjSub_le_of_mem_of_le hsX hB'X
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_three_le h3
  obtain ⟨h, hhS, -, hh⟩ := exists_scalarTorus τ K hc0
  have hhX₁ : h ∈ X₁ := sup_le hb.Uθ_le hb.Uneg_le hhS
  have hhH : h ∈ H := hXH (hX₁X hhX₁)
  have hconjh : v * h * v⁻¹ ∈ H := by
    have hle : conjSub v (Uθ τ K ⊔ Heis.Uneg τ K) ≤ H := by
      have e : conjSub v (Uθ τ K ⊔ Heis.Uneg τ K) =
          conjSub v (Uθ τ K) ⊔ conjSub v (Heis.Uneg τ K) := Subgroup.map_sup _ _ _
      rw [e]
      refine sup_le ?_ hB'H
      rw [conjSub_Uθ_of_mem_Pθ (Qθ_le_Pθ τ K hvQ)]
      exact hUθH
    refine hle (mem_conjSub_iff.2 ?_)
    rw [show v⁻¹ * (v * h * v⁻¹) * v = h by group]
    exact hhS
  have hg₁H : (v * h * v⁻¹) * h⁻¹ ∈ H := mul_mem hconjh (inv_mem hhH)
  have hhv : h * v⁻¹ * h⁻¹ ∈ Qθ τ K := (hh _ (inv_mem hvQ)).1
  have hsplit : (v * h * v⁻¹) * h⁻¹ = v * (h * v⁻¹ * h⁻¹) := by group
  have hg₁Q : (v * h * v⁻¹) * h⁻¹ ∈ Qθ τ K := by
    rw [hsplit]
    exact mul_mem hvQ hhv
  have hg₁c : heisCoord τ K ((v * h * v⁻¹) * h⁻¹) = (1 - c) • m := by
    rw [hsplit, hs.mul _ hvQ _ hhv, (hh _ (inv_mem hvQ)).2, heisCoord_inv hvQ, hvc, sub_smul,
      one_smul, smul_neg]
    abel
  refine ⟨_, hg₁H, hg₁Q, fun hSg => ?_⟩
  rw [hg₁c] at hSg
  have hmem : (1 - c) • m ∈ VS (X₁ ⊔ X₂) ⊓ VM (X₁ ⊔ X₂) :=
    ⟨hSg, (VM (X₁ ⊔ X₂)).smul_mem _ hm⟩
  rw [hco.inf_eq_bot, Submodule.mem_bot] at hmem
  rcases smul_eq_zero.1 hmem with h0 | h0
  · exact hc1 (sub_eq_zero.1 h0).symm
  · exact hm0 h0

theorem exists_M_of_special {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (hXH : X₁ ⊔ X₂ ≤ H)
    {p : ModGL τ K} (hpP : p ∈ Pθ τ K) {β : Fin τ.rank → ℤ}
    (hw : ∃ w : WeylGroup τ, β = w • highRoot τ) (hneg : β (iθ τ) = -1)
    (hBH : conjSub p (rootSubgroup τ K β) ≤ H)
    (hBX : ¬ conjSub p (rootSubgroup τ K β) ≤ X₁ ⊔ X₂) :
    (∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂)) ∨
      ∀ a ∈ Uθ τ K, ∀ b ∈ conjSub p (rootSubgroup τ K β), a * b = b * a := by
  classical
  obtain ⟨hβ, hlong, w', hw', hD1, hγD⟩ := exists_special_data hw hneg
  obtain ⟨C₀, hC₀⟩ := commutator_special (K := K) hβ hlong hneg
  have hUθH : Uθ τ K ≤ H := hb.Uθ_le.trans (le_sup_left.trans hXH)
  have hpG : p ∈ adjointGroup τ K := Pθ_le_adjointGroup τ K hpP
  by_cases hC0 : C₀ = 0
  · right
    intro a ha b hb'
    have hcomm : ∀ s t : K, Commute (pinnedX τ K (highRoot τ) s) (pinnedX τ K β t) := by
      intro s t
      have h1 := hC₀ s t
      rw [hC0, zero_mul, zero_mul, pinnedX_zero, ← pinnedX_neg τ K (highRoot τ) s,
        ← pinnedX_neg τ K β t] at h1
      exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h1)
    have ha' : p⁻¹ * a * p ∈ Uθ τ K := mem_conjSub_iff.1 (by rwa [conjSub_Uθ_of_mem_Pθ hpP])
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 ha'
    obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hb')
    have hc := (hcomm s t).eq
    rw [hs, ht] at hc
    calc a * b = p * ((p⁻¹ * a * p) * (p⁻¹ * b * p)) * p⁻¹ := by group
      _ = p * ((p⁻¹ * b * p) * (p⁻¹ * a * p)) * p⁻¹ := by rw [hc]
      _ = b * a := by group
  · left
    have hCH : conjSub p (rootSubgroup τ K (highRoot τ + β)) ≤ H := by
      intro x hx
      obtain ⟨e, he⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hx)
      have hxe : x = p * pinnedX τ K (highRoot τ + β) e * p⁻¹ := by rw [he]; group
      have h1 := hC₀ 1 (e / C₀)
      have e1 : C₀ * 1 * (e / C₀) = e := by field_simp
      rw [e1] at h1
      have hmemU : ∀ s : K, p * pinnedX τ K (highRoot τ) s * p⁻¹ ∈ H := by
        intro s
        have h' : p * pinnedX τ K (highRoot τ) s * p⁻¹ ∈ conjSub p (Uθ τ K) :=
          mem_conjSub_iff.2 (by
            rw [show p⁻¹ * (p * pinnedX τ K (highRoot τ) s * p⁻¹) * p =
              pinnedX τ K (highRoot τ) s by group]
            exact mem_rootSubgroup.2 ⟨s, rfl⟩)
        rw [conjSub_Uθ_of_mem_Pθ hpP] at h'
        exact hUθH h'
      have hmemB : ∀ t : K, p * pinnedX τ K β t * p⁻¹ ∈ H := by
        intro t
        apply hBH
        exact mem_conjSub_iff.2 (by
          rw [show p⁻¹ * (p * pinnedX τ K β t * p⁻¹) * p = pinnedX τ K β t by group]
          exact mem_rootSubgroup.2 ⟨t, rfl⟩)
      rw [hxe, ← h1]
      have e2 : p * (pinnedX τ K (highRoot τ) 1 * pinnedX τ K β (e / C₀) *
          pinnedX τ K (highRoot τ) (-1) * pinnedX τ K β (-(e / C₀))) * p⁻¹ =
          (p * pinnedX τ K (highRoot τ) 1 * p⁻¹) * (p * pinnedX τ K β (e / C₀) * p⁻¹) *
          (p * pinnedX τ K (highRoot τ) (-1) * p⁻¹) * (p * pinnedX τ K β (-(e / C₀)) * p⁻¹) := by
        group
      rw [e2]
      exact mul_mem (mul_mem (mul_mem (hmemU 1) (hmemB _)) (hmemU _)) (hmemB _)
    have hCQ : conjSub p (rootSubgroup τ K (highRoot τ + β)) ≤ Qθ τ K :=
      conjSub_le_Qθ hpP (rootSubgroup_le_Qθ_of_mem_Deg1 hγD)
    by_cases hM : ∃ c ∈ conjSub p (rootSubgroup τ K (highRoot τ + β)),
        heisCoord τ K c ∉ VS (X₁ ⊔ X₂)
    · obtain ⟨c, hc, hcS⟩ := hM
      exact ⟨c, hCH hc, hCQ hc, hcS⟩
    · push Not at hM
      set n' := canonicalRep (coxeterSystem τ) K w' with hn'
      have hn'U : conjSub n' (Uθ τ K) = rootSubgroup τ K (highRoot τ + β) := by
        rw [← hw']
        exact conjSub_canonicalRep_rootSubgroup w' (isRoot_highRoot τ)
      have hCn : conjSub (p * n') (Uθ τ K) =
          conjSub p (rootSubgroup τ K (highRoot τ + β)) := by
        rw [conjSub_mul, hn'U]
      have hn'G : n' ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w'
      obtain ⟨x, hxX₁, hCx⟩ := hp (p * n') (mul_mem hpG hn'G) (by
        rw [hCn]
        exact fun c hc => ⟨hco.inj c (hCQ hc) (hM c hc), hCQ hc⟩)
      rw [hCn] at hCx
      have hy : conjSub (x⁻¹ * p) (rootSubgroup τ K (highRoot τ + β)) = Uθ τ K := by
        rw [conjSub_mul, hCx, conjSub_inv_conjSub]
      have hyn : (x⁻¹ * p) * n' ∈ Pθ τ K := by
        have hG : (x⁻¹ * p) * n' ∈ adjointGroup τ K :=
          mul_mem (mul_mem (inv_mem (hb.le₁ hxX₁)) hpG) hn'G
        refine normalizer_Uθ_le_Pθ τ K hG (mem_normalizer_of_conjSub_eq ?_)
        rw [conjSub_mul, hn'U, hy]
      have hrβ : conjSub n' (rootSubgroup τ K (w'⁻¹ • β)) = rootSubgroup τ K β := by
        rw [hn', conjSub_canonicalRep_rootSubgroup w' (IsRoot.smul hβ _), smul_inv_smul]
      have hB''eq : conjSub x⁻¹ (conjSub p (rootSubgroup τ K β)) =
          conjSub ((x⁻¹ * p) * n') (rootSubgroup τ K (w'⁻¹ • β)) := by
        rw [conjSub_mul (x⁻¹ * p) n', hrβ, conjSub_mul]
      have hxX : x ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_left hxX₁
      have hxH : x⁻¹ ∈ H := inv_mem (hXH hxX)
      refine exists_M_of_le_Qθ (B := conjSub x⁻¹ (conjSub p (rootSubgroup τ K β))) hco
        (conjSub_le_of_mem_of_le hxH hBH) ?_ ?_
      · rw [hB''eq]
        exact conjSub_le_Qθ hyn (rootSubgroup_le_Qθ_of_mem_Deg1 hD1)
      · intro hle
        apply hBX
        have e : conjSub p (rootSubgroup τ K β) =
            conjSub x (conjSub x⁻¹ (conjSub p (rootSubgroup τ K β))) :=
          (conjSub_conjSub_inv x _).symm
        rw [e]
        exact conjSub_le_of_mem_of_le hxX hle

theorem core_commute {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (h3 : 3 ≤ Nat.card K)
    (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H)
    (hno : ∀ m ∈ H, m ∈ Qθ τ K → heisCoord τ K m ∈ VS (X₁ ⊔ X₂))
    {g : ModGL τ K} (hgH : g ∈ H) (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∀ a ∈ Uθ τ K, ∀ b ∈ conjSub g (Uθ τ K), a * b = b * a := by
  classical
  have hUθX : Uθ τ K ≤ X₁ ⊔ X₂ := hb.Uθ_le.trans le_sup_left
  have hUθH : Uθ τ K ≤ H := hUθX.trans hXH
  obtain ⟨p, hpP, β, hβ, hw, hnf⟩ := exists_normalForm τ K (hHG hgH)
  have hBH : conjSub p (rootSubgroup τ K β) ≤ H := by
    rw [← hnf]
    exact conjSub_le_of_mem_of_le hgH hUθH
  rw [hnf] at hgX ⊢
  have noM : ¬ ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
    rintro ⟨m, hm, hmQ, hmS⟩
    exact hmS (hno m hm hmQ)
  rcases deg_cases hβ with hd | hd | hd | hd | hd
  · exfalso
    have hβθ : β = highRoot τ := CoordAux.eq_highRoot_of_two_le hβ (by omega)
    apply hgX
    rw [hβθ]
    show conjSub p (Uθ τ K) ≤ _
    rw [conjSub_Uθ_of_mem_Pθ hpP]
    exact hUθX
  · exfalso
    apply noM
    exact exists_M_of_le_Qθ hco hBH
      (conjSub_le_Qθ hpP (rootSubgroup_le_Qθ_of_mem_Deg1 (CoordAux.mem_Deg1.2 ⟨hβ, hd⟩))) hgX
  · exact commute_Uθ_conjSub_of_deg_zero hpP hβ hd
  · rcases exists_M_of_special hb hco hp hXH hpP hw hd hBH hgX with h | h
    · exact absurd h noM
    · exact h
  · exfalso
    apply noM
    have hβ' := eq_neg_highRoot_of_deg_neg_two hβ hd
    subst hβ'
    obtain ⟨q, hq, hpq⟩ := exists_conjSub_Pθ_Uneg τ K hpP
    refine exists_M_of_Uneg_conj hb hco h3 hXH hq ?_ ?_
    · rw [← hpq]
      exact hBH
    · rw [← hpq]
      exact hgX

theorem pinnedX_pow (α : Fin τ.rank → ℤ) (c : K) (n : ℕ) :
    pinnedX τ K α c ^ n = pinnedX τ K α ((n : K) * c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← pinnedX_add]
    congr 1
    push_cast
    ring

end MElt

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
