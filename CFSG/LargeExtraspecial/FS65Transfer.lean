module

public import CFSG.LargeExtraspecial.AS35CS64Basic
public import CFSG.RankThree.Literature.FSmithInvolution

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

namespace FS65

variable {H : Type*} [Group H] {Q : Subgroup H} [Finite Q] (hQ : IsExtraspecialPGroup 2 Q)
  (hQn : Q.Normal) [Module (ZMod 2) (Additive (Abelianization Q))]

theorem exists_smith_subgroup_of_involution {z₀ : H} (hz₀ : ∀ g : H, g * z₀ = z₀ * g)
    (hz₀1 : z₀ ≠ 1) (hz₀Q : z₀ ∈ Q) (hCQ : centralizer (Q : Set H) ≤ Q)
    (h3 : 3 ≤ Module.finrank (ZMod 2) (Additive (Abelianization Q)))
    {v : Additive (Abelianization Q)} (hv : extraspecialQuadForm hQ v = 1) {a : H}
    (ha : ∀ u, conjLinEquiv hQn a u = u + polar (extraspecialQuadForm hQ) u v • v)
    (haa : a * a = 1) :
    ∃ F : Subgroup H, a ∈ F ∧ z₀ ∈ F ∧ IsPGroup 2 F ∧
      (∀ j : H, (∀ f ∈ F, j * f = f * j) → j = 1 ∨ j = z₀) ∧
      (∀ f ∈ F, f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀) ∧ (∃ e ∈ F, e * a * e⁻¹ = a * z₀) ∧
      (∃ c₁ ∈ F, ∃ c₂ ∈ F, c₁ * a = a * c₁ ∧ c₂ * a = a * c₂ ∧ ⁅c₁, c₂⁆ = z₀) := by
  obtain ⟨d, rfl⟩ := exists_ofMul_of v
  have had := conjAut_eq_of_sq hQ hQn hz₀ hz₀1 hz₀Q hv ha (Or.inl haa)
  have hd0 : Additive.ofMul (Abelianization.of d) ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hzz : z₀ * z₀ = 1 := sq_eq_one_of_central hQ hz₀ hz₀Q
  have hzinv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hzz
  have hadH : a * (d : H) * a⁻¹ = d * z₀ := by
    have := congrArg Subtype.val had
    rwa [conjAut_apply] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hadH' : a⁻¹ * (d : H) * a = d * z₀ := by
    calc a⁻¹ * (d : H) * a = a * d * a⁻¹ := by rw [hainv]
      _ = d * z₀ := hadH
  set D : Subgroup H := Q ⊓ centralizer {(d : H)} with hDdef
  have hmemD : ∀ y : Q, y * d = d * y → (y : H) ∈ D := fun y hy =>
    mem_inf.mpr ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy)⟩
  set F : Subgroup H := D ⊔ zpowers a with hFdef
  have hDF : D ≤ F := le_sup_left
  have haF : a ∈ F := mem_sup_right (mem_zpowers a)
  have hz₀F : z₀ ∈ F :=
    hDF (mem_inf.mpr ⟨hz₀Q, mem_centralizer_singleton_iff.mpr (hz₀ d).symm⟩)
  refine ⟨F, haF, hz₀F, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hza : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa))
    have : Q.Normal := hQn
    exact (hQ.1.to_sup_of_normal_left hza).to_le (sup_le_sup_right inf_le_left _)
  ·
    intro j hj
    have hja : j * a = a * j := hj a haF
    have hjD : ∀ y : Q, y * d = d * y → j * y = y * j := fun y hy => hj y (hDF (hmemD y hy))
    have hρj : conjLinEquiv hQn j = 1 ∨
        conjLinEquiv hQn j = reflect (extraspecialQuadForm hQ) (Additive.ofMul
          (Abelianization.of d)) := by
      refine eq_one_or_eq_reflect_of_fix (extraspecialQuadForm_nondegenerate hQ) hv
        (conjLinEquiv_mem hQ hQn j) fun u hu => ?_
      obtain ⟨y, rfl⟩ := exists_ofMul_of u
      have hy : y * d = d * y := (polar_extraspecialQuadForm_eq_zero_iff hQ y d).mp hu
      rw [conjLinEquiv_apply, show conjAut hQn j y = y from
        Subtype.ext (by rw [conjAut_apply, hjD y hy, mul_inv_cancel_right])]
    rcases hρj with h1 | h1
    · have hjQ : j ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ (Subtype.ext h1)
      have hs : ∀ y : Q, y * d = d * y → (⟨j, hjQ⟩ : Q) * y = y * ⟨j, hjQ⟩ :=
        fun y hy => Subtype.ext (hjD y hy)
      rcases mem_center_or_of_forall_commute hQ hs with h | h
      · exact (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp h
      · exfalso
        have hμ : j * (d : H)⁻¹ = 1 ∨ j * (d : H)⁻¹ = z₀ :=
          (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp h
        have hμc : ∀ g : H, g * (j * (d : H)⁻¹) = (j * (d : H)⁻¹) * g := by
          intro g
          rcases hμ with h | h <;> rw [h]
          · group
          · exact hz₀ g
        have key : a * j * a⁻¹ = j * z₀ := by
          calc a * j * a⁻¹ = a * ((j * (d : H)⁻¹) * d) * a⁻¹ := by group
            _ = (a * (j * (d : H)⁻¹)) * d * a⁻¹ := by group
            _ = ((j * (d : H)⁻¹) * a) * d * a⁻¹ := by rw [hμc a]
            _ = (j * (d : H)⁻¹) * (a * d * a⁻¹) := by group
            _ = (j * (d : H)⁻¹) * (d * z₀) := by rw [hadH]
            _ = j * z₀ := by group
        have : a * j * a⁻¹ = j := by rw [← hja, mul_inv_cancel_right]
        rw [this] at key
        exact hz₀1 (by simpa using key.symm)
    · exfalso
      have hja' : conjLinEquiv hQn (j * a⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, ← eq_reflect_of_apply hv ha, mul_inv_cancel]
      have hqQ : j * a⁻¹ ∈ Q := mem_of_extraspecialConjOrth_eq_one hQ hQn hCQ (Subtype.ext hja')
      have hqa : a * (j * a⁻¹) * a⁻¹ = j * a⁻¹ := by
        calc a * (j * a⁻¹) * a⁻¹ = (a * j) * a⁻¹ * a⁻¹ := by group
          _ = (j * a) * a⁻¹ * a⁻¹ := by rw [hja]
          _ = j * a⁻¹ := by group
      have hfixq : conjLinEquiv hQn a (Additive.ofMul (Abelianization.of (⟨_, hqQ⟩ : Q))) =
          Additive.ofMul (Abelianization.of (⟨_, hqQ⟩ : Q)) := by
        rw [conjLinEquiv_apply, show conjAut hQn a ⟨_, hqQ⟩ = ⟨_, hqQ⟩ from
          Subtype.ext (by rw [conjAut_apply]; exact hqa)]
      rw [ha] at hfixq
      have hpol : polar (extraspecialQuadForm hQ) (Additive.ofMul (Abelianization.of
          (⟨_, hqQ⟩ : Q))) (Additive.ofMul (Abelianization.of d)) = 0 := by
        rcases zmod2_eq_zero_or_eq_one (polar (extraspecialQuadForm hQ) (Additive.ofMul
          (Abelianization.of (⟨_, hqQ⟩ : Q))) (Additive.ofMul (Abelianization.of d))) with h | h
        · exact h
        · exfalso
          rw [h, one_smul, add_eq_left] at hfixq
          exact hd0 hfixq
      have hqd := congrArg Subtype.val ((polar_extraspecialQuadForm_eq_zero_iff hQ _ d).mp hpol)
      change j * a⁻¹ * (d : H) = d * (j * a⁻¹) at hqd
      have hjd : j * (d : H) = d * j := hjD d rfl
      have key : (j * a⁻¹) * (d : H) * (j * a⁻¹)⁻¹ = d * z₀ := by
        calc (j * a⁻¹) * (d : H) * (j * a⁻¹)⁻¹ = j * (a⁻¹ * d * a) * j⁻¹ := by group
          _ = j * (d * z₀) * j⁻¹ := by rw [hadH']
          _ = (j * d) * z₀ * j⁻¹ := by group
          _ = (d * j) * z₀ * j⁻¹ := by rw [hjd]
          _ = d * (j * z₀) * j⁻¹ := by group
          _ = d * (z₀ * j) * j⁻¹ := by rw [hz₀ j]
          _ = d * z₀ := by group
      rw [hqd, mul_inv_cancel_right] at key
      exact hz₀1 (by simpa using key.symm)
  ·
    have hconjz : ∀ f : H, f * (a * z₀) * f⁻¹ = f * a * f⁻¹ * z₀ := fun f => by
      calc f * (a * z₀) * f⁻¹ = f * a * (z₀ * f⁻¹) := by group
        _ = f * a * (f⁻¹ * z₀) := by rw [← hz₀ f⁻¹]
        _ = f * a * f⁻¹ * z₀ := by group
    let S : Subgroup H :=
      { carrier := {f | f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀}
        mul_mem' := by
          intro f g hf hg
          simp only [Set.mem_ofPred_eq] at hf hg ⊢
          have e : f * g * a * (f * g)⁻¹ = f * (g * a * g⁻¹) * f⁻¹ := by group
          rw [e]
          rcases hg with hg | hg <;> rw [hg]
          · exact hf
          · rw [hconjz]
            rcases hf with hf | hf <;> rw [hf]
            · exact Or.inr rfl
            · left
              rw [mul_assoc, hzz, mul_one]
        one_mem' := Or.inl (by group)
        inv_mem' := by
          intro f hf
          simp only [Set.mem_ofPred_eq, inv_inv] at hf ⊢
          rcases hf with hf | hf
          · left
            calc f⁻¹ * a * f = f⁻¹ * (f * a * f⁻¹) * f := by rw [hf]
              _ = a := by group
          · right
            have h1 : f⁻¹ * a * f * z₀ = a := by
              calc f⁻¹ * a * f * z₀ = f⁻¹ * a * (f * z₀) := by group
                _ = f⁻¹ * a * (z₀ * f) := by rw [hz₀ f]
                _ = f⁻¹ * (a * z₀) * f := by group
                _ = f⁻¹ * (f * a * f⁻¹) * f := by rw [hf]
                _ = a := by group
            calc f⁻¹ * a * f = f⁻¹ * a * f * (z₀ * z₀) := by rw [hzz, mul_one]
              _ = (f⁻¹ * a * f * z₀) * z₀ := by group
              _ = a * z₀ := by rw [h1] }
    have hDS : D ≤ S := by
      intro f hf
      obtain ⟨hfQ, hfd⟩ := mem_inf.mp hf
      have hy : (⟨f, hfQ⟩ : Q) * d = d * ⟨f, hfQ⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.mp hfd)
      have hc := conjAut_mul_inv_mem_center hQ hQn ha hy
      have hc' : a * f * a⁻¹ * f⁻¹ = 1 ∨ a * f * a⁻¹ * f⁻¹ = z₀ := by
        have := (mem_center_iff_coe hQ hz₀ hz₀1 hz₀Q).mp hc
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply] using this
      have e : f * a * f⁻¹ = (a * f * a⁻¹ * f⁻¹)⁻¹ * a := by group
      change f * a * f⁻¹ = a ∨ f * a * f⁻¹ = a * z₀
      rw [e]
      rcases hc' with h | h <;> rw [h]
      · left
        group
      · right
        rw [hzinv, hz₀ a]
    have hFS : F ≤ S := sup_le hDS ((zpowers_le (G := H)).mpr (Or.inl (by group)))
    exact fun f hf => hFS hf
  ·
    refine ⟨d, hDF (hmemD d rfl), ?_⟩
    calc (d : H) * a * (d : H)⁻¹ = (a * d * a⁻¹ * (d : H)⁻¹)⁻¹ * a := by group
      _ = ((d : H) * z₀ * (d : H)⁻¹)⁻¹ * a := by rw [hadH]
      _ = z₀⁻¹ * a := by rw [hz₀ d, mul_inv_cancel_right]
      _ = a * z₀ := by rw [hzinv, hz₀ a]
  ·
    obtain ⟨c₁, c₂, hc₁d, hc₂d, hc₁a, hc₂a, hc⟩ :=
      exists_fixed_commutator hQ hQn hz₀ hz₀1 hz₀Q h3 hv ha had
    have hcomm : ∀ c : Q, conjAut hQn a c = c → (c : H) * a = a * c := fun c hc => by
      have := congrArg Subtype.val hc
      rw [conjAut_apply] at this
      calc (c : H) * a = a * c * a⁻¹ * a := by rw [this]
        _ = a * c := by group
    exact ⟨c₁, hDF (hmemD c₁ hc₁d), c₂, hDF (hmemD c₂ hc₂d), hcomm c₁ hc₁a, hcomm c₂ hc₂a, hc⟩

end FS65

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_commutator_eq_z (hn : 1 ≤ S.width) :
    ∃ c₁ ∈ S.QG, ∃ c₂ ∈ S.QG, c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = S.z := by
  by_contra h
  push Not at h
  have hcomm : ∀ x ∈ S.QG, ∀ y ∈ S.QG, x * y = y * x := by
    intro x hx y hy
    rcases S.commutator_eq_one_or_z hx hy with h1 | h1
    · calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h1, one_mul]
    · exact absurd h1 (h x hx y hy)
  have h1 := S.card_le_of_commute le_rfl hcomm
  rw [S.card_QG_eq_card_Q, S.card_Q_eq] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

theorem conj_z_mem_commutator (hn : 1 ≤ S.width) (g : G) :
    g * S.z * g⁻¹ ∈ _root_.commutator G := by
  obtain ⟨c₁, -, c₂, -, hc⟩ := S.exists_commutator_eq_z hn
  have hz : S.z ∈ _root_.commutator G := by
    rw [← hc, commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top c₁) (mem_top c₂)
  exact (commutator_normal ⊤ ⊤).conj_mem _ hz g

theorem not_forall_eq_transvection_of_mem_commutator (hn : 2 ≤ S.width) (m : S.M)
    (hmm : m * m = 1) (hmG : (m : G) ∈ _root_.commutator G) (v : S.Qt) (hv : S.q v = 1) :
    ¬ ∀ u : S.Qt, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + polar S.q u v • v := by
  classical
  intro hm
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hz₀ : ∀ k : S.M, k * S.zM = S.zM * k := fun k =>
    Subtype.ext (mem_centralizer_singleton_iff.mp k.2)
  have hz₀1 : S.zM ≠ 1 := fun h => S.z_ne_one (congrArg Subtype.val h)
  have hdim : finrank (ZMod 2) S.Qt = 2 * S.width := S.finrank_Qt_eq_two_mul_width
  obtain ⟨F, hmF, hz₀F, hF2, hCF, hFm, he, hc⟩ :=
    FS65.exists_smith_subgroup_of_involution S.extraspecial S.normal hz₀ hz₀1 S.zM_mem_Q
      S.centralizer_le (hdim ▸ (by omega : 3 ≤ 2 * S.width)) hv hm hmm
  let ϕ : S.M →* Multiplicative (ZMod 2) := (dicksonHom S.q S.q_nondegenerate).comp S.ρ
  have hV : ϕ.transfer (m : G) = 1 := Abelianization.commutator_subset_ker ϕ.transfer hmG
  have hϕm : ϕ m ≠ 1 := by
    have hρm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = reflect S.q v := eq_reflect_of_apply hv hm
    change dicksonHom S.q S.q_nondegenerate (S.ρ m) ≠ 1
    rw [dicksonHom_apply, hρm, finrank_commSpace_reflect S.q_nondegenerate hv, Nat.cast_one, Ne,
      ofAdd_eq_one]
    exact one_ne_zero
  refine smith_transfer ϕ S.z_ne_one S.z_mul_z (F := F.map S.M.subtype) (a := (m : G))
    (map_subtype_le F) (hF2.map _) ?_ (mem_map_of_mem _ hmF) (congrArg Subtype.val hmm) hϕm
    hV ?_ ?_ ?_
  · intro c hc
    have hcz : c * S.z = S.z * c := hc S.z (mem_map_of_mem _ hz₀F)
    have hcM : c ∈ S.M := mem_centralizer_singleton_iff.mpr hcz
    rcases hCF ⟨c, hcM⟩ (fun f hf => Subtype.ext (hc f (mem_map_of_mem _ hf))) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro f ⟨f', hf', rfl⟩
    rcases hFm f' hf' with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · obtain ⟨e, heF, he⟩ := he
    exact ⟨e, mem_map_of_mem _ heF, congrArg Subtype.val he⟩
  · obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, h3⟩ := hc
    exact ⟨c₁, mem_map_of_mem _ hc₁, c₂, mem_map_of_mem _ hc₂, congrArg Subtype.val h1,
      congrArg Subtype.val h2, congrArg Subtype.val h3⟩

theorem not_forall_eq_transvection_of_conj (hn : 2 ≤ S.width) {g : G} (m : S.M)
    (hgm : g * S.z * g⁻¹ = m) (v : S.Qt) (hv : S.q v = 1) :
    ¬ ∀ u : S.Qt, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u + polar S.q u v • v := by
  have hmm : m * m = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← hgm]
    exact S.conj_mul_self g)
  have hmG : (m : G) ∈ _root_.commutator G := by
    rw [← hgm]
    exact S.conj_z_mem_commutator (by omega) g
  exact S.not_forall_eq_transvection_of_mem_commutator hn m hmm hmG v hv

theorem two_le_finrank_commSpace_of_conj (hn : 2 ≤ S.width) {g : G} {x : S.M}
    (hgx : g * S.z * g⁻¹ = x) (hx : x ∉ S.Q) :
    2 ≤ finrank (ZMod 2) (commSpace ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra! hlt
  have h1 : ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h =>
    hx (S.mem_Q_of_ρ_eq_one (Subtype.ext h))
  have hsum := finrank_commSpace_add_finrank_fixSpace ((S.ρ x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rcases eq_one_or_eq_transvection_of_finrank_fixSpace S.q_nondegenerate (S.ρ x).2
      (by omega) with h | ⟨c, hc, hxc, -, -⟩
  · exact h1 h
  · exact S.not_forall_eq_transvection_of_conj hn x hgx c hc hxc

end Setting

end CFSG.LargeExtraspecial
