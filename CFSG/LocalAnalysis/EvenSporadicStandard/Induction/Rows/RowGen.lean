module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Link

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem exists_involution_of_isPGroup {H : Type} [Group H] {T : Subgroup H} (hT : IsPGroup 2 T)
    (hne : T ≠ ⊥) : ∃ t ∈ T, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) g
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have hord : orderOf ((g : T) : H) = 2 ^ k := by rw [Subgroup.orderOf_coe, hk]
  refine ⟨((g : T) : H) ^ (orderOf ((g : T) : H) / 2), Subgroup.pow_mem T g.2 _, ?_⟩
  exact orderOf_pow_orderOf_div (by rw [hord]; exact pow_ne_zero _ (by norm_num))
    (by rw [hord]; exact dvd_pow_self 2 hk0)

theorem eq_top_of_allInner {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hN : FStarSimple N)
    (hin : AllInner ↥N) : N = ⊤ := by
  have hNn : N.Normal := hN.normal
  rw [eq_top_iff]
  intro y _
  obtain ⟨c, hc⟩ := hin (MulAut.conjNormal y)
  have hcen : (c : Y)⁻¹ * y ∈ centralizer (N : Set Y) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun α : MulAut ↥N => ((α ⟨n, hn⟩ : ↥N) : Y)) hc
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      at h1
    calc n * ((c : Y)⁻¹ * y) = (c : Y)⁻¹ * ((c : Y) * n * (c : Y)⁻¹) * y := by group
      _ = (c : Y)⁻¹ * (y * n * y⁻¹) * y := by rw [h1]
      _ = ((c : Y)⁻¹ * y) * n := by group
  have h2 : (c : Y)⁻¹ * y ∈ N := hN.centralizer_le hcen
  have h3 : y = (c : Y) * ((c : Y)⁻¹ * y) := by group
  rw [h3]
  exact mul_mem c.2 h2

theorem eq_top_of_perfect_of_index_le_two {G : Type} [Group G] [Finite G]
    (hG : Group.IsPerfect G) {N : Subgroup G} (hidx : N.index ≤ 2) : N = ⊤ := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
  · exact Subgroup.index_eq_one.1 h1
  · have : N.Normal := Subgroup.normal_of_index_eq_two h2
    have hperf : Group.IsPerfect ↥(⊤ : Subgroup G) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := G)).symm.surjective
    exact eq_top_iff.2 (le_of_perfect_of_index_le_two hidx hperf)

theorem exists_involution_of_link {G : Type} [Group G] [Finite G] {L K₁ T : Subgroup G} {s : G}
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁) (hne : K₁ ≠ L)
    (hin : AllInner ↥L) (hZ : center ↥L = ⊥) :
    ∃ l : G, l ∈ L ∧ orderOf l = 2 ∧ ∀ k ∈ K₁, k * l = l * k := by
  obtain ⟨hsN, hKL, hs2, hsK, hsL⟩ :=
    link5b_setup hq hne hdata.L_comp hdata.s_sq hdata.K_comp hdata.incl.1 hdata.link
  let σ : MulAut ↥L := L.normalizerMonoidHom ⟨s, hsN⟩
  have hσ : ∀ x : ↥L, ((σ x : ↥L) : G) = s * x * s⁻¹ := fun x => rfl
  have hker : ∀ g : normalizer (L : Set G), L.normalizerMonoidHom g = 1 ↔
      (g : G) ∈ centralizer (L : Set G) := fun g => by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf]
  have hσσ : σ * σ = 1 := by
    have h1 : σ * σ = L.normalizerMonoidHom (⟨s, hsN⟩ * ⟨s, hsN⟩) := (map_mul _ _ _).symm
    rw [h1, hker]
    show s * s ∈ centralizer (L : Set G)
    rwa [← pow_two]
  obtain ⟨c, hc⟩ := hin σ
  have hcc : c * c = 1 := by
    apply mul_self_eq_one_of_conj_mul_self hZ
    rw [← hc]
    exact hσσ
  have hc1 : c ≠ 1 := by
    rintro rfl
    have : σ = 1 := by rw [hc]; exact map_one _
    exact hsL ((hker ⟨s, hsN⟩).1 this)
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← Subgroup.coe_mul, hcc]
      rfl
    · intro h
      exact hc1 (Subtype.ext h)
  · intro k hk
    have hkL : k ∈ L := hKL hk
    have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨k, hkL⟩ : ↥L) : G)) hc
    simp only [hσ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 : k * s = s * k := mem_centralizer_iff.1 hsK k hk
    have h3 : s * k * s⁻¹ = k := by rw [← h2]; group
    rw [h3] at h1
    calc k * (c : G) = ((c : G) * k * (c : G)⁻¹) * (c : G) := by rw [← h1]
      _ = (c : G) * k := by group

theorem isSolvable_centralizer_of_cover {K₂ B : Type*} [Group K₂] [Group B] (π : K₂ →* B)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center K₂) (k : K₂)
    (hsol : Group.IsSolvable ↥(centralizer ({k} : Set K₂))) :
    Group.IsSolvable ↥(centralizer ({π k} : Set B)) := by
  let Ct : Subgroup K₂ := (centralizer ({π k} : Set B)).comap π
  have hmem : ∀ x : ↥Ct, (x : K₂) * k * (x : K₂)⁻¹ * k⁻¹ ∈ center K₂ := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker]
    have hx : π k * π x = π x * π k := by
      have := x.2
      simp only [Ct, mem_comap, mem_centralizer_singleton_iff] at this
      exact this.symm
    calc π ((x : K₂) * k * (x : K₂)⁻¹ * k⁻¹)
        = (π x * π k) * (π x)⁻¹ * (π k)⁻¹ := by simp only [map_mul, map_inv]
      _ = (π k * π x) * (π x)⁻¹ * (π k)⁻¹ := by rw [hx]
      _ = 1 := by group
  let δ : ↥Ct →* ↥(center K₂) :=
    { toFun := fun x => ⟨(x : K₂) * k * (x : K₂)⁻¹ * k⁻¹, hmem x⟩
      map_one' := by
        ext
        simp
      map_mul' := fun x y => by
        ext
        have h1 := mem_center_iff.1 (hmem y) (x : K₂)
        have h2 := mem_center_iff.1 (hmem y) ((x : K₂) * k * (x : K₂)⁻¹ * k⁻¹)
        show ((x : K₂) * (y : K₂)) * k * ((x : K₂) * (y : K₂))⁻¹ * k⁻¹ =
          ((x : K₂) * k * (x : K₂)⁻¹ * k⁻¹) * ((y : K₂) * k * (y : K₂)⁻¹ * k⁻¹)
        calc ((x : K₂) * (y : K₂)) * k * ((x : K₂) * (y : K₂))⁻¹ * k⁻¹
            = ((x : K₂) * ((y : K₂) * k * (y : K₂)⁻¹ * k⁻¹) * (x : K₂)⁻¹) *
                ((x : K₂) * k * (x : K₂)⁻¹ * k⁻¹) := by group
          _ = ((y : K₂) * k * (y : K₂)⁻¹ * k⁻¹) * ((x : K₂) * k * (x : K₂)⁻¹ * k⁻¹) := by
              rw [h1]
              group
          _ = _ := h2.symm }
  have hkerδ : Group.IsSolvable ↥δ.ker := by
    let ι : ↥δ.ker →* ↥(centralizer ({k} : Set K₂)) :=
      { toFun := fun x => ⟨((x : ↥Ct) : K₂), by
          have h := congrArg (fun z : ↥(center K₂) => (z : K₂)) (MonoidHom.mem_ker.1 x.2)
          simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h
          rw [mem_centralizer_singleton_iff]
          calc ((x : ↥Ct) : K₂) * k = (((x : ↥Ct) : K₂) * k * ((x : ↥Ct) : K₂)⁻¹ * k⁻¹) * k *
                ((x : ↥Ct) : K₂) := by group
            _ = k * ((x : ↥Ct) : K₂) := by rw [h]; group⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := ι) (fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(centralizer ({k} : Set K₂)) => (z : K₂)) h)
  have hCt : Group.IsSolvable ↥Ct :=
    Group.isSolvable_of_ker_le_range δ.ker.subtype δ (by
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩)
  let q : ↥Ct →* ↥(centralizer ({π k} : Set B)) :=
    (π.comp Ct.subtype).codRestrict (centralizer ({π k} : Set B)) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hπ (y : B)
    exact ⟨⟨x, by simp only [Ct, mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  exact Group.isSolvable_of_surjective hq

end CFSG.EvenSporadicStandard.Induction.Hyp
