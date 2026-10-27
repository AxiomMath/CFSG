module

public import CFSG.GH74.AS16.E2.OuterModel
public import CFSG.GH74.AS16.E2.Outer2

public section

namespace CFSG.GH74.AS16.E2

open Subgroup

section Lift

variable {G : Type*} [Group G] {L : Subgroup G}

theorem act_pow' {x : G} (hx : x ∈ normalizer (L : Set G)) (n : ℕ) :
    (L.normalizerMonoidHom ⟨x, hx⟩) ^ n =
      L.normalizerMonoidHom ⟨x ^ n, (normalizer (L : Set G)).pow_mem hx n⟩ := by
  rw [← map_pow]
  congr 1

theorem act_inv' {x : G} (hx : x ∈ normalizer (L : Set G)) :
    (L.normalizerMonoidHom ⟨x, hx⟩)⁻¹ =
      L.normalizerMonoidHom ⟨x⁻¹, (normalizer (L : Set G)).inv_mem hx⟩ := by
  rw [← map_inv]
  rfl

theorem act_fix_iff {x : G} (hx : x ∈ normalizer (L : Set G)) (c : ↥L) :
    L.normalizerMonoidHom ⟨x, hx⟩ c = c ↔ x * (c : G) = (c : G) * x := by
  constructor
  · intro h
    have h2 : x * (c : G) * x⁻¹ = (c : G) := congrArg Subtype.val h
    calc x * (c : G) = (x * (c : G) * x⁻¹) * x := by group
      _ = (c : G) * x := by rw [h2]
  · intro h
    apply Subtype.ext
    show x * (c : G) * x⁻¹ = (c : G)
    calc x * (c : G) * x⁻¹ = ((c : G) * x) * x⁻¹ := by rw [h]
      _ = (c : G) := by group

theorem inv_mul_mem_centralizer_of_act_eq {x y : G} (hx : x ∈ normalizer (L : Set G))
    (hy : y ∈ normalizer (L : Set G))
    (h : L.normalizerMonoidHom ⟨y, hy⟩ = L.normalizerMonoidHom ⟨x, hx⟩) :
    x⁻¹ * y ∈ centralizer (L : Set G) := by
  have hxy : x⁻¹ * y ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hx) hy
  have h1 : L.normalizerMonoidHom ⟨x⁻¹ * y, hxy⟩ = 1 := by
    rw [act_mul ((normalizer (L : Set G)).inv_mem hx) hy hxy, ← act_inv' hx, h, inv_mul_cancel]
  exact (act_eq_one_iff hxy).1 h1

theorem act_eq_of_inv_mul_mem {x y : G} (hx : x ∈ normalizer (L : Set G))
    (hy : y ∈ normalizer (L : Set G)) (h : x⁻¹ * y ∈ centralizer (L : Set G)) :
    L.normalizerMonoidHom ⟨y, hy⟩ = L.normalizerMonoidHom ⟨x, hx⟩ := by
  have hxy : x⁻¹ * y ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hx) hy
  have h1 := (act_eq_one_iff hxy).2 h
  rw [act_mul ((normalizer (L : Set G)).inv_mem hx) hy hxy, ← act_inv' hx] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem OuterSub.of_table (hT : OuterTable ↥L) : OuterSub L where
  outer_cent3 := by
    intro r hr hr2 hrout y hy hfix
    have hτ2 : (L.normalizerMonoidHom ⟨r, hr⟩) ^ 2 = 1 := by
      rw [act_pow']
      have h1 : (⟨r ^ 2, (normalizer (L : Set G)).pow_mem hr 2⟩ : normalizer (L : Set G)) = 1 :=
        Subtype.ext hr2
      rw [h1, map_one]
    have hτi : ¬ IsInn (L.normalizerMonoidHom ⟨r, hr⟩) := fun h => hrout ((act_isInn_iff hr).1 h)
    have key := hT.outer_cent3 _ hτ2 hτi (L.normalizerMonoidHom ⟨y, hy⟩) (by
      intro c hc3 hτc
      have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
      have h1 := (act_fix_iff hr c).1 hτc
      exact (act_fix_iff hy c).2 (hfix c c.2 hc3' h1.symm))
    rcases key with h | h
    · exact Or.inl ((act_eq_one_iff hy).1 h)
    · exact Or.inr (inv_mul_mem_centralizer_of_act_eq hr hy h)
  bang := by
    intro r hr hr2 hrout
    have hτ2 : (L.normalizerMonoidHom ⟨r, hr⟩) ^ 2 = 1 := by
      rw [act_pow']
      have h1 : (⟨r ^ 2, (normalizer (L : Set G)).pow_mem hr 2⟩ : normalizer (L : Set G)) = 1 :=
        Subtype.ext hr2
      rw [h1, map_one]
    have hτi : ¬ IsInn (L.normalizerMonoidHom ⟨r, hr⟩) := fun h => hrout ((act_isInn_iff hr).1 h)
    obtain ⟨l, c₁, c₂, hc₁, hc₂, hc₁τ, hc₂τ, hw2, hw1, hlτ⟩ := hT.bang _ hτ2 hτi
    have hr1 : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hr2)
    refine ⟨(l : G), l.2, (c₁ : G), c₁.2, (c₂ : G), c₂.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hc₁
    · rw [Subgroup.orderOf_coe]
      exact hc₂
    · exact ((act_fix_iff hr c₁).1 hc₁τ).symm
    · exact ((act_fix_iff hr c₂).1 hc₂τ).symm
    · have := congrArg Subtype.val hw2
      simpa using this
    · intro h
      apply hw1
      exact Subtype.ext (by simpa using h)
    · have h2 : r * (l : G) * r⁻¹ * (l : G)⁻¹ = (c₁ : G) * (c₂ : G) := congrArg Subtype.val hlτ
      rw [hr1] at h2 ⊢
      exact h2
  inner_sq := by
    intro v hv hv2 y hy hfix
    have hv' : orderOf (⟨v, hv⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
    have hvN : v ∈ normalizer (L : Set G) := Subgroup.le_normalizer hv
    have y2N : y ^ 2 ∈ normalizer (L : Set G) := (normalizer (L : Set G)).pow_mem hy 2
    have key := hT.inner_sq ⟨v, hv⟩ hv' (L.normalizerMonoidHom ⟨y, hy⟩) (by
      intro c hc3 hcv
      have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
      have h1 : (c : G) * v = v * (c : G) := congrArg Subtype.val hcv
      exact (act_fix_iff hy c).2 (hfix c c.2 hc3' h1))
    have hsq : (L.normalizerMonoidHom ⟨y, hy⟩) ^ 2 = L.normalizerMonoidHom ⟨y ^ 2, y2N⟩ :=
      act_pow' hy 2
    have hconj : MulAut.conj (⟨v, hv⟩ : ↥L) = L.normalizerMonoidHom ⟨v, hvN⟩ :=
      (act_conj hv).symm
    refine ⟨?_, ?_⟩
    · rcases key.1 with h | h
      · left
        rw [hsq] at h
        exact (act_eq_one_iff y2N).1 h
      · right
        rw [hsq, hconj] at h
        exact inv_mul_mem_centralizer_of_act_eq hvN y2N h
    · intro hinn hy2
      have hinn' : IsInn (L.normalizerMonoidHom ⟨y, hy⟩) := (act_isInn_iff hy).2 hinn
      have hψ2 : (L.normalizerMonoidHom ⟨y, hy⟩) ^ 2 = 1 := by
        rw [hsq]
        exact (act_eq_one_iff y2N).2 hy2
      rcases key.2 hinn' hψ2 with h | h
      · exact Or.inl ((act_eq_one_iff hy).1 h)
      · right
        rw [hconj] at h
        exact inv_mul_mem_centralizer_of_act_eq hvN hy h

theorem OuterSylow.of_table {Q : Subgroup G} (hQL : Q ≤ L)
    (hT : OuterSylowTable ↥L (Q.subgroupOf L)) : OuterSylow L Q where
  exists_s := by
    obtain ⟨s, hsQ, hs1, hs2, hsc, hsu, hcent, a, b, ha3, hb3, has, hbs, hab⟩ := hT.exists_s
    have hsQ' : (s : G) ∈ Q := hsQ
    refine ⟨(s : G), hsQ', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => hs1 (Subtype.ext h)
    · have := congrArg Subtype.val hs2
      simpa using this
    · intro q hq
      have := congrArg Subtype.val (hsc ⟨q, hQL hq⟩ hq)
      exact this
    · intro a₀ ha₀ hac ha2
      have h1 := hsu ⟨a₀, hQL ha₀⟩ ha₀ (fun q' hq' => Subtype.ext (hac q' hq')) (Subtype.ext (by
        simpa using ha2))
      rcases h1 with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · intro y hy hyc
      have hfix : ∀ q ∈ Q.subgroupOf L, L.normalizerMonoidHom ⟨y, hy⟩ q = q := by
        intro q hq
        exact (act_fix_iff hy q).2 (hyc q hq)
      obtain ⟨a₀, ha₀Q, ha₀c, ha₀⟩ := hcent _ hfix
      refine ⟨(a₀ : G), ha₀Q, ?_, ?_⟩
      · intro q hq
        have := congrArg Subtype.val (ha₀c ⟨q, hQL hq⟩ hq)
        exact this
      · have hN : (a₀ : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer a₀.2
        have : L.normalizerMonoidHom ⟨y, hy⟩ = L.normalizerMonoidHom ⟨(a₀ : G), hN⟩ := by
          rw [ha₀]
          exact (act_conj a₀.2).symm
        exact inv_mul_mem_centralizer_of_act_eq hN hy this
    · refine ⟨(a : G), a.2, (b : G), b.2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe]
        exact ha3
      · rw [Subgroup.orderOf_coe]
        exact hb3
      · exact congrArg Subtype.val has
      · exact congrArg Subtype.val hbs
      · have := congrArg Subtype.val hab
        simpa using this
  sq := by
    intro y hy hyi hyQ v hvQ hv2 hfix hvy q hq
    have hvL : v ∈ L := hQL hvQ
    have hvN : v ∈ normalizer (L : Set G) := Subgroup.le_normalizer hvL
    have y2N : y ^ 2 ∈ normalizer (L : Set G) := (normalizer (L : Set G)).pow_mem hy 2
    have hψQ : ∀ q' ∈ Q.subgroupOf L, L.normalizerMonoidHom ⟨y, hy⟩ q' ∈ Q.subgroupOf L := by
      intro q' hq'
      exact hyQ _ hq'
    have hv' : orderOf (⟨v, hvL⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
    have hsq : (L.normalizerMonoidHom ⟨y, hy⟩) ^ 2 = L.normalizerMonoidHom ⟨y ^ 2, y2N⟩ :=
      act_pow' hy 2
    have hsq' : L.normalizerMonoidHom ⟨y ^ 2, y2N⟩ = L.normalizerMonoidHom ⟨v, hvN⟩ :=
      act_eq_of_inv_mul_mem hvN y2N hvy
    have key := hT.sq _ (fun h => hyi ((act_isInn_iff hy).1 h)) hψQ ⟨v, hvL⟩ hvQ hv' (by
      intro c hc3 hcv
      have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
      have h1 : (c : G) * v = v * (c : G) := congrArg Subtype.val hcv
      exact (act_fix_iff hy c).2 (hfix c c.2 hc3' h1)) (by
      rw [hsq, hsq', act_conj hvL]) ⟨q, hQL hq⟩ hq
    exact congrArg Subtype.val key
  conj4 := by
    intro a haQ ha4 hfix
    have haL : a ∈ L := hQL haQ
    have ha4' : orderOf (⟨a, haL⟩ : ↥L) = 4 := by rw [← Subgroup.orderOf_coe]; exact ha4
    obtain ⟨k, hkQ, hkc⟩ := hT.conj4 ⟨a, haL⟩ haQ ha4' (by
      intro c hc3 hca
      have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
      have h1 : (c : G) * a ^ 2 = a ^ 2 * (c : G) := congrArg Subtype.val hca
      exact Subtype.ext (hfix c c.2 hc3' h1))
    refine ⟨(k : G), k.2, hkQ, fun y hy => ?_⟩
    exact congrArg Subtype.val (hkc ⟨y, hQL hy⟩ hy)

@[expose] def OuterCyc (L : Subgroup G) : Prop :=
  ∀ R : Subgroup G, R ≤ normalizer (L : Set G) → R ⊓ centralizer (L : Set G) = ⊥ →
    ∀ v ∈ L, orderOf v = 2 → (∀ ρ ∈ R, ∀ c ∈ L, orderOf c = 3 → c * v = v * c → ρ * c = c * ρ) →
      IsCyclic ↥R

theorem OuterCyc.of_table (hT : OuterCycTable ↥L) : OuterCyc L := by
  intro R hRN hRD v hv hv2 hfix
  have hv' : orderOf (⟨v, hv⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
  obtain ⟨φ, hφ⟩ := hT.cyc ⟨v, hv⟩ hv'
  let f : ↥R →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hf : ∀ ρ : ↥R, f ρ = L.normalizerMonoidHom ⟨(ρ : G), hRN ρ.2⟩ := fun ρ => rfl
  have hmem : ∀ ρ : ↥R, f ρ ∈ Subgroup.zpowers φ := by
    intro ρ
    apply hφ
    intro c hc3 hcv
    have hc3' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc3
    have h1 : (c : G) * v = v * (c : G) := congrArg Subtype.val hcv
    rw [hf]
    exact (act_fix_iff _ c).2 (hfix ρ ρ.2 c c.2 hc3' h1)
  have hinj : Function.Injective (f.codRestrict (Subgroup.zpowers φ) hmem) := by
    intro a b hab
    have h1 : f a = f b := congrArg Subtype.val hab
    have h2 : f (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : ((a⁻¹ * b : ↥R) : G) ∈ centralizer (L : Set G) := by
      have := (act_eq_one_iff (hRN (a⁻¹ * b).2)).1 (by rw [← hf]; exact h2)
      exact this
    have h4 : ((a⁻¹ * b : ↥R) : G) ∈ R ⊓ centralizer (L : Set G) := ⟨(a⁻¹ * b).2, h3⟩
    rw [hRD, Subgroup.mem_bot] at h4
    have h5 : a⁻¹ * b = 1 := Subtype.ext h4
    exact (inv_mul_eq_one.1 h5)
  exact isCyclic_of_injective _ hinj

end Lift

end CFSG.GH74.AS16.E2
