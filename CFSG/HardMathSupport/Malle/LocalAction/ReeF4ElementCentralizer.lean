module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerPlane

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Generic

variable {G : Type*} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [← h a ha b hb] }
  have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

theorem card_sup_of_commute_of_inf_eq_bot {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective (fun p => ⟨p.1.1 * p.2.1, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h1 : a * b = a' * b' := congrArg Subtype.val hab
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hAB, Subgroup.mem_bot] at h3
    have h4 : a = a' := by
      have := congrArg (fun y => a' * y) h3
      simpa using this
    subst h4
    have h5 : b = b' := mul_left_cancel h1
    subst h5
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

end Generic


section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_centralizer_decomp (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (P : Sylow 5 (ReeTag.F4.reeGamma K 2)) (E : Subgroup (ReeTag.F4.reeGamma K 2))
    (hEP : E ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2))) (hE : CFSG.Open.IsElemAbelian 5 E)
    (x : ReeTag.F4.reeGamma K 2) (hxE : x ∈ E) (hx1 : x ≠ 1) :
    ∃ A S : Subgroup (ReeTag.F4.reeGamma K 2),
      A ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2)) ∧ Nat.card A = 25 ∧ IsCyclic A ∧
      (∀ a ∈ A, ∀ s ∈ S, a * s = s * a) ∧ A ⊓ S = ⊥ ∧
      A ⊔ S = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) ∧
      Nat.card S = 32537600 ∧ Nonempty (S ≃* suzukiGroup 2 K) ∧
      Nat.card ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S : Subgroup _) = 25 ∧
      (P : Subgroup (ReeTag.F4.reeGamma K 2)) = A ⊔ ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S) ∧
      x ∈ A := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨F⟩ := plane25_nonempty hK
  have hT₀card : Nat.card F.Ψ.range = 625 := card_range_plane25 F
  obtain ⟨P₁⟩ : Nonempty (Sylow 5 (ReeTag.F4.reeGamma K 2)) := inferInstance
  have hfac : 5 ^ (Nat.card (ReeTag.F4.reeGamma K 2)).factorization 5 = 625 := by
    rw [← Sylow.card_eq_multiplicity P₁]
    exact card_sylow_five hK P₁
  let P₀ : Sylow 5 (ReeTag.F4.reeGamma K 2) := Sylow.ofCard F.Ψ.range (by rw [hfac, hT₀card])
  have hP₀ : (P₀ : Subgroup (ReeTag.F4.reeGamma K 2)) = F.Ψ.range := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ReeTag.F4.reeGamma K 2) P₀ P
  have hmem := mem_sylow_iff_conj hg
  have hxP : x ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)) := hEP hxE
  have hx5 : x ^ 5 = 1 := hE.2 x hxE
  have hx'P₀ : g⁻¹ * x * g ∈ F.Ψ.range := by
    rw [← hP₀]
    exact (hmem x).1 hxP
  obtain ⟨z, hz⟩ := hx'P₀
  have hz5 : z ^ 5 = 1 := by
    apply F.Ψinj
    rw [map_pow, hz, map_one]
    have h := congrArg (MulAut.conj g⁻¹) hx5
    rw [map_pow, map_one] at h
    simpa [MulAut.conj_apply] using h
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hx1
    rw [map_one] at hz
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, ← hz]
    group
  obtain ⟨A', Sg', hA'le, hA'c, hA'cyc, hcomm', hinf', hsup', hxA', hSz'⟩ :=
    plane_decomp hK F z hz5 hz1
  let c : ReeTag.F4.reeGamma K 2 →* ReeTag.F4.reeGamma K 2 := (MulAut.conj g).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hcapp : ∀ y, c y = g * y * g⁻¹ := fun y => by simp [c, MulAut.conj_apply]
  set A : Subgroup (ReeTag.F4.reeGamma K 2) := A'.map c with hA
  set S : Subgroup (ReeTag.F4.reeGamma K 2) := Sg'.map c with hS
  have hAP : A ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hmem, hcapp]
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this, hP₀]
    exact hA'le hy
  have hcardA : Nat.card A = 25 := by
    rw [hA, Subgroup.card_map_of_injective hcinj, hA'c]
  have hcycA : IsCyclic A := by
    have e := A'.equivMapOfInjective c hcinj
    have : IsCyclic A' := hA'cyc
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hcommAS : ∀ a ∈ A, ∀ s ∈ S, a * s = s * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' a ha s hs]
  have hinfAS : A ⊓ S = ⊥ := by
    rw [hA, hS, ← Subgroup.map_inf_eq _ _ c hcinj, hinf', Subgroup.map_bot]
  have hcent : Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) =
      (Subgroup.centralizer ({g⁻¹ * x * g} : Set (ReeTag.F4.reeGamma K 2))).map c := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨g⁻¹ * y * g, ?_, by rw [hcapp]; group⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Eq.symm ?_
      calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
        _ = g⁻¹ * (y * x) * g := by rw [h]
        _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hw
      rw [hcapp]
      refine Eq.symm ?_
      calc x * (g * w * g⁻¹) = g * (g⁻¹ * x * g * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * x * g)) * g⁻¹ := by rw [hw]
        _ = g * w * g⁻¹ * x := by group
  have hsupAS : A ⊔ S = Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K 2)) := by
    rw [hcent, hA, hS, ← Subgroup.map_sup, ← hz, hsup']
  obtain ⟨eSz'⟩ := hSz'
  have eSz : S ≃* suzukiGroup 2 K := (Sg'.equivMapOfInjective c hcinj).symm.trans eSz'
  have hcardS : Nat.card S = 32537600 := by
    rw [Nat.card_congr eSz.toEquiv, suzuki_order hK]
    norm_num
  have hxA : x ∈ A := by
    refine ⟨g⁻¹ * x * g, ?_, by rw [hcapp]; group⟩
    rw [← hz]
    exact hxA'
  obtain ⟨eP⟩ := sylowShape_five hK (P : Subgroup (ReeTag.F4.reeGamma K 2)) P.isPGroup'
    P.not_dvd_index
  have hPcomm : ∀ p ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)),
      ∀ q ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)), p * q = q * p := by
    intro p hp q hq
    have := mul_comm (eP ⟨p, hp⟩) (eP ⟨q, hq⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (eP.injective this)
  have hPcard : Nat.card (P : Subgroup (ReeTag.F4.reeGamma K 2)) = 625 := card_sylow_five hK P
  have hPsup : (P : Subgroup (ReeTag.F4.reeGamma K 2)) =
      A ⊔ ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S) := by
    apply le_antisymm
    · intro p hp
      have hpC : p ∈ A ⊔ S := by
        rw [hsupAS, Subgroup.mem_centralizer_singleton_iff]
        exact (hPcomm x hxP p hp).symm
      obtain ⟨a, ha, s, hs, rfl⟩ := mem_sup_of_commute hcommAS hpC
      have hsP : s ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)) := by
        have : s = a⁻¹ * (a * s) := by group
        rw [this]
        exact mul_mem (inv_mem (hAP ha)) hp
      exact Subgroup.mul_mem_sup ha ⟨hsP, hs⟩
    · exact sup_le hAP inf_le_left
  have hcommAPS : ∀ a ∈ A, ∀ b ∈ (P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S, a * b = b * a :=
    fun a ha b hb => hcommAS a ha b hb.2
  have hinfAPS : A ⊓ ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S) = ⊥ := by
    rw [eq_bot_iff, ← hinfAS]
    exact inf_le_inf_left _ inf_le_right
  have hcardPS : Nat.card ((P : Subgroup (ReeTag.F4.reeGamma K 2)) ⊓ S : Subgroup _) = 25 := by
    have h := card_sup_of_commute_of_inf_eq_bot hcommAPS hinfAPS
    rw [← hPsup, hPcard, hcardA] at h
    omega
  exact ⟨A, S, hAP, hcardA, hcycA, hcommAS, hinfAS, hsupAS, hcardS, ⟨eSz⟩, hcardPS, hPsup, hxA⟩

end Main

end CFSG.HardMathSupport.Malle.LocalAction
