module

public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.LargeExtraspecial.DWSm77Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem card_centralizer_L0_le {g v : G}
    (huv : g * S.z * g⁻¹ * v ≠ v * (g * S.z * g⁻¹)) :
    Nat.card (S.L0 g ⊓ centralizer ({v} : Set G) : Subgroup G) ≤ 2 ^ S.width := by
  set T := S.conjBy g with hT
  set C := S.L0 g ⊓ centralizer ({v} : Set G) with hC
  have hCQ : C ≤ T.QG := fun c hc => S.L0_le_Qa g hc.1
  have huC : T.z ∉ C := fun h => huv (mem_centralizer_singleton_iff.mp h.2)
  have hcomm : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ * c₂ = c₂ * c₁ := by
    intro c₁ h₁ c₂ h₂
    rcases T.commutator_eq_one_or_z (hCQ h₁) (hCQ h₂) with h | h
    · calc c₁ * c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by group
        _ = c₂ * c₁ := by rw [h, one_mul]
    · exact absurd (h ▸ C.mul_mem (C.mul_mem (C.mul_mem h₁ h₂) (C.inv_mem h₁)) (C.inv_mem h₂))
        huC
  set U := T.clSub C with hU
  have hUdim : finrank (ZMod 2) U ≤ S.width := by
    rw [← S.width_conjBy g]
    refine finrank_le_width_of_isotropic T fun a ha b hb => ?_
    obtain ⟨x, hx, hxQ, rfl⟩ := T.mem_clSub_iff.mp ha
    obtain ⟨y, hy, hyQ, rfl⟩ := T.mem_clSub_iff.mp hb
    exact (T.polar_cl_eq_zero_iff hxQ hyQ).mpr (hcomm x hx y hy)
  have hinj : Function.Injective
      (fun c : C => (⟨T.cl c, T.cl_mem_clSub c.2 (hCQ c.2)⟩ : U)) := by
    intro c₁ c₂ h
    have h' : T.cl c₁ = T.cl c₂ := congrArg Subtype.val h
    rcases (T.cl_eq_cl_iff (hCQ c₁.2) (hCQ c₂.2)).mp h' with e | e
    · exact Subtype.ext e.symm
    · exfalso
      apply huC
      have e' : T.z = (c₁ : G)⁻¹ * c₂ := by rw [e]; group
      rw [e']
      exact C.mul_mem (C.inv_mem c₁.2) c₂.2
  calc Nat.card C ≤ Nat.card U := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ finrank (ZMod 2) U := T.card_submodule U
    _ ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hUdim

theorem card_le_finrank_add_one_of_polar_eq_one (X : Submodule (ZMod 2) S.Qt) (T : Finset S.Qt)
    (hTX : ∀ v ∈ T, v ∈ X) (hT : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → polar S.q v w = 1) :
    T.card ≤ finrank (ZMod 2) X + 1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · simp
  set T' := T.erase s₀ with hT'
  let Φ : S.Qt →ₗ[ZMod 2] (T' → ZMod 2) :=
    LinearMap.pi fun t : T' => S.q.polarBilin.flip (t : S.Qt)
  have hΦ : ∀ v (t : T'), Φ v t = polar S.q v t := fun v t => by
    simp [Φ, polarBilin_apply_apply]
  let f : T' → X := fun t =>
    ⟨s₀ + t, X.add_mem (hTX s₀ hs₀) (hTX t (Finset.mem_of_mem_erase t.2))⟩
  have hcomp : ⇑(Φ ∘ₗ X.subtype) ∘ f = Pi.basisFun (ZMod 2) T' := by
    funext t t'
    have ht := Finset.mem_erase.mp t.2
    have ht' := Finset.mem_erase.mp t'.2
    simp only [Function.comp_apply, LinearMap.coe_comp, Submodule.coe_subtype, hΦ, f,
      polar_add_left, Pi.basisFun_apply]
    rw [hT s₀ hs₀ t' ht'.2 (Ne.symm ht'.1)]
    by_cases htt : t = t'
    · subst htt
      rw [CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero, Pi.single_eq_same, add_zero]
    · have hne : (t : S.Qt) ≠ t' := fun h => htt (Subtype.ext h)
      rw [hT t ht.2 t' ht'.2 hne, Pi.single_eq_of_ne (Ne.symm htt)]
      decide
  have hli : LinearIndependent (ZMod 2) f := by
    apply LinearIndependent.of_comp (Φ ∘ₗ X.subtype)
    rw [hcomp]
    exact (Pi.basisFun (ZMod 2) T').linearIndependent
  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, hT', Finset.card_erase_of_mem hs₀] at h1
  omega

theorem two_pow_width_le_of_polar_eq_one {g v : G} (hu : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hvQ : v ∈ S.QG)
    (huv : g * S.z * g⁻¹ * v ≠ v * (g * S.z * g⁻¹)) (X : Submodule (ZMod 2) S.Qt)
    (hvX : ∀ d ∈ S.L0 g, S.cl (d * v * d⁻¹) ∈ X)
    (hP : ∀ d₁ ∈ S.L0 g, ∀ d₂ ∈ S.L0 g, S.cl (d₁ * v * d₁⁻¹) ≠ S.cl (d₂ * v * d₂⁻¹) →
      polar S.q (S.cl (d₁ * v * d₁⁻¹)) (S.cl (d₂ * v * d₂⁻¹)) = 1) :
    2 ^ S.width ≤ 2 * (finrank (ZMod 2) X + 1) := by
  classical
  set L := S.L0 g with hLdef
  set C := L ⊓ centralizer ({v} : Set G) with hCdef
  have : Fintype L := Fintype.ofFinite L
  have : Fintype C := Fintype.ofFinite C
  set φ : L → G := fun d => (d : G) * v * (d : G)⁻¹ with hφ
  set O : Finset G := Finset.univ.image φ with hO
  set T : Finset S.Qt := O.image S.cl with hT
  have hL := S.card_L0 hu hne
  have hC := card_centralizer_L0_le S huv
  have h1 : (Finset.univ : Finset L).card ≤ Nat.card C * O.card := by
    refine Finset.card_le_mul_card_image (f := φ) Finset.univ (Nat.card C) fun w hw => ?_
    obtain ⟨d₀, -, hd₀⟩ := Finset.mem_image.mp hw
    have hmap : ∀ d ∈ ({a ∈ Finset.univ | φ a = w} : Finset L), (d₀ : G)⁻¹ * d ∈ C := by
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      refine ⟨L.mul_mem (L.inv_mem d₀.2) d.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have e : (d : G) * v * (d : G)⁻¹ = (d₀ : G) * v * (d₀ : G)⁻¹ := hd'.trans hd₀.symm
      calc (d₀ : G)⁻¹ * d * v = (d₀ : G)⁻¹ * ((d : G) * v * (d : G)⁻¹) * d := by group
        _ = (d₀ : G)⁻¹ * ((d₀ : G) * v * (d₀ : G)⁻¹) * d := by rw [e]
        _ = v * ((d₀ : G)⁻¹ * d) := by group
    calc ({a ∈ Finset.univ | φ a = w} : Finset L).card ≤ (Finset.univ : Finset C).card := by
          refine Finset.card_le_card_of_injOn
            (fun d => if h : (d₀ : G)⁻¹ * d ∈ C then (⟨_, h⟩ : C) else 1)
            (fun d _ => Finset.mem_coe.mpr (Finset.mem_univ _)) fun d₁ hd₁ d₂ hd₂ h => ?_
          simp only [dite_eq_left (hmap d₁ hd₁), dite_eq_left (hmap d₂ hd₂)] at h
          exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
      _ = Nat.card C := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hOQ : ∀ w ∈ O, w ∈ S.QG := by
    intro w hw
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hw
    exact S.conj_mem_QG (S.L0_le_M g d.2) hvQ
  have h2 : O.card ≤ 2 * T.card := by
    refine Finset.card_le_mul_card_image O 2 fun t ht => ?_
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp ht
    calc ({w ∈ O | S.cl w = S.cl w₀} : Finset G).card ≤ ({w₀, w₀ * S.z} : Finset G).card := by
          refine Finset.card_le_card fun w hw => ?_
          have hw' := Finset.mem_filter.mp hw
          rcases (S.cl_eq_cl_iff (hOQ w₀ hw₀) (hOQ w hw'.1)).mp hw'.2.symm with e | e
          · simp [e]
          · simp [e]
      _ ≤ 2 := Finset.card_le_two
  have h3 : T.card ≤ finrank (ZMod 2) X + 1 := by
    refine card_le_finrank_add_one_of_polar_eq_one S X T (fun w hw => ?_) fun a ha b hb hab => ?_
    · obtain ⟨w₁, hw₁, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hw₁
      exact hvX d d.2
    · obtain ⟨w₁, hw₁, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨w₂, hw₂, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨d₁, -, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨d₂, -, rfl⟩ := Finset.mem_image.mp hw₂
      exact hP d₁ d₁.2 d₂ d₂.2 hab
  rw [Finset.card_univ, Fintype.card_eq_nat_card, hL] at h1
  have hbound : 2 ^ S.width * 2 ^ S.width ≤
      2 ^ S.width * (2 * (finrank (ZMod 2) X + 1)) := by
    calc 2 ^ S.width * 2 ^ S.width = 2 ^ (2 * S.width) := by rw [← pow_add, two_mul]
      _ ≤ Nat.card C * O.card := h1
      _ ≤ 2 ^ S.width * (2 * T.card) := Nat.mul_le_mul hC h2
      _ ≤ 2 ^ S.width * (2 * (finrank (ZMod 2) X + 1)) := by
        apply Nat.mul_le_mul_left
        omega
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

theorem false_of_polar_eq_one_of_four_le (hn : 4 ≤ S.width) {g v : G}
    (hu : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hvQ : v ∈ S.QG)
    (huv : g * S.z * g⁻¹ * v ≠ v * (g * S.z * g⁻¹)) (X : Submodule (ZMod 2) S.Qt)
    (hX : finrank (ZMod 2) X + 2 ≤ 2 * S.width)
    (hvX : ∀ d ∈ S.L0 g, S.cl (d * v * d⁻¹) ∈ X)
    (hP : ∀ d₁ ∈ S.L0 g, ∀ d₂ ∈ S.L0 g, S.cl (d₁ * v * d₁⁻¹) ≠ S.cl (d₂ * v * d₂⁻¹) →
      polar S.q (S.cl (d₁ * v * d₁⁻¹)) (S.cl (d₂ * v * d₂⁻¹)) = 1) : False := by
  have h := two_pow_width_le_of_polar_eq_one S hu hne hvQ huv X hvX hP
  have key : ∀ m : ℕ, 4 * (m + 4) < 2 ^ (m + 4) + 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ]
      omega
  have h4 := key (S.width - 4)
  rw [show S.width - 4 + 4 = S.width by omega] at h4
  omega

end Sm77

end CFSG.LargeExtraspecial.DW
