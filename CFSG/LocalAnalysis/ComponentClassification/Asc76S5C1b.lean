module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1a

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_inf_centralizer' {A R T : Subgroup G} {g : G}
    (hK : TightlyEmbedded (centralizer (A : Set G)))
    (hg : g ∉ normalizer (centralizer (A : Set G) : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓
      normalizer (centralizer (A : Set G) : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hTR : T ≤ normalizer (R : Set G)) {u : G}
    (hu : u ∈ T) (huAK : u ∈ A ⊔ centralizer (A : Set G)) :
    ∃ a ∈ A, ∃ r ∈ R ⊓ centralizer (T : Set G), u = a * r := by
  by_cases hu1 : u = 1
  · exact ⟨1, one_mem _, 1, one_mem _, by rw [hu1, mul_one]⟩
  obtain ⟨m, hm⟩ := hT.isPGroup ⟨u, hu⟩
  have hm' : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨a, ha, r, hr, hur⟩ := exists_mul_of_mem_sup_centralizer hR huAK (hTR hu) hm'
  refine ⟨a, ha, r, ?_, hur⟩
  rw [← inf_centralizer_singleton_eq hK hg hT hR hTR hu hu1]
  refine ⟨hr, ?_⟩
  show r ∈ centralizer ({u} : Set G)
  rw [mem_centralizer_singleton_iff, hur]
  have hc : Commute a r := commute_of_mem_centralizer ha (hR.le hr)
  rw [← mul_assoc, ← hc.eq]

omit [Finite G] in
theorem card_omegaOne_eq_of_mulEquiv {C T : Subgroup G} (hC : IsMulCommutative C)
    (hT : IsMulCommutative T) (e : C ≃* T) : Nat.card (omegaOne C) = Nat.card (omegaOne T) := by
  have hsq : ∀ {X Y : Subgroup G} (f : X ≃* Y) (x : X), ((x : G) ^ 2 = 1) → ((f x : G) ^ 2 = 1) :=
    by
    intro X Y f x hx
    have h1 : x ^ 2 = 1 := Subtype.ext (by simpa using hx)
    have h2 : f x ^ 2 = 1 := by rw [← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2
  refine Nat.card_congr
    { toFun := fun x => ⟨e ⟨x, ((mem_omegaOne_iff hC).mp x.2).1⟩, (mem_omegaOne_iff hT).mpr
        ⟨(e _).2, hsq e _ ((mem_omegaOne_iff hC).mp x.2).2⟩⟩
      invFun := fun y => ⟨e.symm ⟨y, ((mem_omegaOne_iff hT).mp y.2).1⟩, (mem_omegaOne_iff hC).mpr
        ⟨(e.symm _).2, hsq e.symm _ ((mem_omegaOne_iff hT).mp y.2).2⟩⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

omit [Finite G] in
theorem isMulCommutative_of_mulEquiv' {X Y : Subgroup G} (e : X ≃* Y) (hY : IsMulCommutative Y) :
    IsMulCommutative X :=
  ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, hY.is_comm.comm])⟩⟩

theorem Overlap.exists_sq {A R T : Subgroup G} {g : G} (h : Overlap A R g T)
    (hTc : IsMulCommutative T) (hUAK : omegaOne T ≤ A ⊔ centralizer (A : Set G))
    {r : G} (hr : r ∈ R) (hrC : r ∉ R ⊓ centralizer (T : Set G))
    (hrinv : ∀ x ∈ R ⊓ centralizer (T : Set G), r * x * r⁻¹ = x⁻¹) :
    ∀ x ∈ R ⊓ centralizer (T : Set G), x ^ 2 = 1 →
      ∃ y ∈ R ⊓ centralizer (T : Set G), x = y ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set C := R ⊓ centralizer (T : Set G) with hCdef
  obtain ⟨e⟩ := h.mulEquiv
  have hCc : IsMulCommutative C := isMulCommutative_of_mulEquiv' e hTc
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hCc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAK : A ≤ centralizer (K : Set G) := le_centralizer_iff.mp le_rfl
  have hRK : R ≤ K := h.sylowR.le
  have hCR : C ≤ R := inf_le_left
  have hrep : ∀ u : omegaOne T, ∃ s : C, (u : G) * (s : G)⁻¹ ∈ A := by
    intro u
    obtain ⟨a, ha, s, hs, hus⟩ := exists_mul_mem_inf_centralizer' h.tight h.not_mem_K h.sylowK
      h.sylowR h.normalizesR (omegaOne_le T u.2) (hUAK u.2)
    exact ⟨⟨s, hs⟩, by rw [hus, mul_inv_cancel_right]; exact ha⟩
  choose ρ hρ using hrep
  have hu2 : ∀ u : omegaOne T, (u : G) ^ 2 = 1 := fun u => ((mem_omegaOne_iff hTc).mp u.2).2
  have hdecomp : ∀ u : omegaOne T, (u : G) = ((u : G) * (ρ u : G)⁻¹) * (ρ u : G) := fun u => by
    group
  have hcAρ : ∀ u : omegaOne T, ∀ a ∈ A, Commute a (ρ u : G) := fun u a ha =>
    commute_of_mem_centralizer ha (hRK (hCR (ρ u).2))
  have hTU : ∃ u₀ : omegaOne T, (u₀ : G) ≠ 1 := by
    have h4 := h.ne_bot
    have h2T : 2 ∣ Nat.card T := (even_card_of_isPGroup h.sylow.isPGroup h4).two_dvd
    obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2T
    rw [Subgroup.orderOf_mk] at hx2
    refine ⟨⟨x, mem_omegaOne hx (by rw [← hx2]; exact pow_orderOf_eq_one x)⟩, fun hx1 => ?_⟩
    change x = 1 at hx1
    rw [hx1, orderOf_one] at hx2
    norm_num at hx2
  obtain ⟨u₀, hu₀⟩ := hTU
  have hZC : ∀ z ∈ R, z ∈ centralizer (K : Set G) → z ∈ C := by
    intro z hzR hzK
    have hu₀T : (u₀ : G) ∈ T := omegaOne_le T u₀.2
    rw [hCdef, ← inf_centralizer_singleton_eq h.tight h.not_mem_K h.sylowK h.sylowR
      h.normalizesR hu₀T hu₀]
    refine ⟨hzR, ?_⟩
    show z ∈ centralizer ({(u₀ : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    have ha := hρ u₀
    have h1 : Commute ((u₀ : G) * (ρ u₀ : G)⁻¹) z := commute_of_mem_centralizer ha (hRK hzR)
    have h2 : Commute (ρ u₀ : G) z :=
      (mem_centralizer_iff.mp hzK _ (hRK (hCR (ρ u₀).2)))
    rw [hdecomp u₀]
    exact ((h1.mul_left h2).eq).symm
  have hZ2 : ∀ z ∈ R, z ∈ centralizer (K : Set G) → z ^ 2 = 1 := by
    intro z hzR hzK
    have h1 := hrinv z (hZC z hzR hzK)
    have h2 : r * z * r⁻¹ = z := by
      have := mem_centralizer_iff.mp hzK r (hRK hr)
      rw [this]
      group
    rw [h2] at h1
    rw [sq]
    nth_rw 2 [h1]
    exact mul_inv_cancel z
  have hρK : ∀ u : omegaOne T, (ρ u : G) ^ 2 ∈ centralizer (K : Set G) := by
    intro u
    have ha := hρ u
    have h1 : ((u : G) * (ρ u : G)⁻¹) ^ 2 * (ρ u : G) ^ 2 = 1 := by
      rw [← (hcAρ u _ ha).mul_pow, ← hdecomp u, hu2 u]
    have h2 : (ρ u : G) ^ 2 = (((u : G) * (ρ u : G)⁻¹) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact hAK (A.inv_mem (A.pow_mem ha 2))
  have hρR : ∀ u : omegaOne T, (ρ u : G) ^ 2 ∈ R := fun u => R.pow_mem (hCR (ρ u).2) 2
  have hρZ2 : ∀ u : omegaOne T, ((ρ u : G) ^ 2) ^ 2 = 1 := fun u => hZ2 _ (hρR u) (hρK u)
  have hρ1 : ∀ u : omegaOne T, (ρ u : G) ^ 2 = 1 → (u : G) = 1 := by
    intro u hsq
    by_contra hu1
    apply hrC
    have huT : (u : G) ∈ T := omegaOne_le T u.2
    rw [hCdef, ← inf_centralizer_singleton_eq h.tight h.not_mem_K h.sylowK h.sylowR
      h.normalizesR huT hu1]
    refine ⟨hr, ?_⟩
    show r ∈ centralizer ({(u : G)} : Set G)
    rw [mem_centralizer_singleton_iff]
    set s : G := (ρ u : G) with hs
    have hsC : s ∈ C := (ρ u).2
    have hinv' : r * s⁻¹ * r⁻¹ = s := by rw [hrinv _ (C.inv_mem hsC), inv_inv]
    have hsr : s * r * s⁻¹ = r := by
      calc s * r * s⁻¹ = s * (r * s⁻¹ * r⁻¹) * r := by group
        _ = s * s * r := by rw [hinv']
        _ = s ^ 2 * r := by rw [sq]
        _ = r := by rw [hsq, one_mul]
    set a : G := (u : G) * s⁻¹ with ha
    have haA : a ∈ A := hρ u
    have hca : Commute a (s * r * s⁻¹) :=
      commute_of_mem_centralizer haA (K.mul_mem (K.mul_mem (hRK (hCR hsC)) (hRK hr))
        (K.inv_mem (hRK (hCR hsC))))
    rw [hsr] at hca
    have hu : (u : G) = a * s := by rw [ha]; group
    rw [hu]
    calc r * (a * s) = a * r * s := by rw [← mul_assoc, hca.eq]
      _ = a * (s * r * s⁻¹) * s := by rw [hsr]
      _ = a * s * r := by group
  have hmul : ∀ u v : omegaOne T, (ρ (u * v) : G) ^ 2 = (ρ u : G) ^ 2 * (ρ v : G) ^ 2 := by
    intro u v
    have haA : (u : G) * (ρ u : G)⁻¹ ∈ A := hρ u
    have hbA : (v : G) * (ρ v : G)⁻¹ ∈ A := hρ v
    have hcA : ((u * v : omegaOne T) : G) * (ρ (u * v) : G)⁻¹ ∈ A := hρ (u * v)
    have hc : Commute (ρ u : G) ((v : G) * (ρ v : G)⁻¹) := (hcAρ u _ hbA).symm
    have key : ((u * v : omegaOne T) : G) =
        ((u : G) * (ρ u : G)⁻¹) * ((v : G) * (ρ v : G)⁻¹) * ((ρ u : G) * (ρ v : G)) := by
      calc ((u * v : omegaOne T) : G)
          = ((u : G) * (ρ u : G)⁻¹) * ((ρ u : G) * ((v : G) * (ρ v : G)⁻¹)) * (ρ v : G) := by
            rw [coe_mul]; group
        _ = ((u : G) * (ρ u : G)⁻¹) * (((v : G) * (ρ v : G)⁻¹) * (ρ u : G)) * (ρ v : G) := by
            rw [hc.eq]
        _ = _ := by group
    set z := (ρ u : G) * (ρ v : G) * (ρ (u * v) : G)⁻¹ with hz
    have hzR : z ∈ R := R.mul_mem (R.mul_mem (hCR (ρ u).2) (hCR (ρ v).2))
      (R.inv_mem (hCR (ρ (u * v)).2))
    have hzA : z ∈ A := by
      have h3 : z = (((u : G) * (ρ u : G)⁻¹) * ((v : G) * (ρ v : G)⁻¹))⁻¹ *
          (((u * v : omegaOne T) : G) * (ρ (u * v) : G)⁻¹) := by
        rw [hz, key]
        group
      rw [h3]
      exact A.mul_mem (A.inv_mem (A.mul_mem haA hbA)) hcA
    have hzK : z ∈ centralizer (K : Set G) := hAK hzA
    have hzC : z ∈ C := hZC z hzR hzK
    have hz2 : z ^ 2 = 1 := hZ2 z hzR hzK
    have hρuv : (ρ (u * v) : G) = z⁻¹ * ((ρ u : G) * (ρ v : G)) := by rw [hz]; group
    have hc1 : Commute z⁻¹ ((ρ u : G) * (ρ v : G)) :=
      hcomm _ (C.inv_mem hzC) _ (C.mul_mem (ρ u).2 (ρ v).2)
    have hc2 : Commute (ρ u : G) (ρ v : G) := hcomm _ (ρ u).2 _ (ρ v).2
    rw [hρuv, hc1.mul_pow, hc2.mul_pow, inv_pow, hz2, inv_one, one_mul]
  let f : omegaOne T → omegaOne C := fun u =>
    ⟨(ρ u : G) ^ 2, (mem_omegaOne_iff hCc).mpr ⟨C.pow_mem (ρ u).2 2, hρZ2 u⟩⟩
  have hfinj : Function.Injective f := by
    intro u v huv
    have h1 : (ρ u : G) ^ 2 = (ρ v : G) ^ 2 := congrArg Subtype.val huv
    have h2 : (ρ (u * v) : G) ^ 2 = 1 := by
      rw [hmul, ← h1, ← sq, ← pow_mul, show 2 * 2 = 2 * 2 from rfl, pow_mul, hρZ2 u]
    have h3 := hρ1 (u * v) h2
    have h4 : (u : G) * v = 1 := h3
    have h5 : (v : G) = (u : G)⁻¹ := eq_inv_of_mul_eq_one_right h4
    have h6 : (u : G)⁻¹ = u := by
      have := hu2 u
      rw [sq] at this
      exact inv_eq_of_mul_eq_one_right this
    exact Subtype.ext (by rw [h5, h6])
  have hcard : Nat.card (omegaOne T) = Nat.card (omegaOne C) :=
    (card_omegaOne_eq_of_mulEquiv hCc hTc e).symm
  have hfbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  intro x hx hx2
  obtain ⟨u, hu⟩ := hfbij.2 ⟨x, (mem_omegaOne_iff hCc).mpr ⟨hx, hx2⟩⟩
  exact ⟨ρ u, (ρ u).2, (congrArg Subtype.val hu).symm⟩

end CFSG.ComponentClassification.Asc76.Sec5
