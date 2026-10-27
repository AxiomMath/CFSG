module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD13
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NF

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng : Subgroup G} [(hz.z4iSub Ng).Normal]

theorem z4j_bound (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    S4B.ZJBound (S4B.z4iπ (hz.z4iSub Ng) hz.z4iT) := by
  intro P hPc hP
  have hN' : Odd (Nat.card (hz.z4iSub Ng)) := by
    rw [hz.z4i_card_sub hN.le_NQ]; exact hN.odd
  have hker : Odd (Nat.card (S4B.z4iπ (hz.z4iSub Ng)).ker) := by
    rw [S4B.z4iπ_ker]; exact hN'
  have ht2 : hz.z4iT * hz.z4iT = 1 := Subtype.ext hz.t_mul_self
  have ht1 : hz.z4iT ≠ 1 := fun h => hz.t_ne_one (congrArg Subtype.val h)
  have hord : orderOf hz.z4iT = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hA2 : IsPGroup 2 ↥(zpowers hz.z4iT) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hcent : centralizer ((zpowers hz.z4iT : Subgroup ↥(ctxNQ t tau x₁ x₂ rho)) :
      Set ↥(ctxNQ t tau x₁ x₂ rho)) =
      centralizer ({hz.z4iT} : Set ↥(ctxNQ t tau x₁ x₂ rho)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hPc' : P ≤ centralizer (((zpowers hz.z4iT).map (S4B.z4iπ (hz.z4iSub Ng)) :
      Subgroup (↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng)) :
      Set (↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng)) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hPc
  obtain ⟨P', hP'2, hP'map, hP'c, -⟩ :=
    S4B.z4i_lift_two_cent (S4B.z4iπ (hz.z4iSub Ng)) (S4B.z4iπ_surjective _) hker hA2 hP hPc'
  have hP'c' : P' ≤ centralizer ({hz.z4iT} : Set ↥(ctxNQ t tau x₁ x₂ rho)) :=
    hcent ▸ hP'c
  have hbound := (hz.z4iPartD (Ng := Ng) (V' := ⊥)).bound P' hP'2 hP'c'
  calc Nat.card P = Nat.card (P'.map (S4B.z4iπ (hz.z4iSub Ng))) := by rw [hP'map]
    _ = Nat.card P' := S4B.z4i_card_map _ hN' hP'2
    _ ≤ 128 := hbound

theorem z4j_no_abelian (hN : Z4IOdd t tau x₁ x₂ rho Ng) :
    S4B.ZJNoAb (S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam * S4B.z4iπ (hz.z4iSub Ng) hz.z4iT) := by
  intro A hA2 hAab hσA hw
  obtain ⟨w, hwA, hw8⟩ := hw
  have hN' : Odd (Nat.card (hz.z4iSub Ng)) := by
    rw [hz.z4i_card_sub hN.le_NQ]; exact hN.odd
  have hker : Odd (Nat.card (S4B.z4iπ (hz.z4iSub Ng)).ker) := by
    rw [S4B.z4iπ_ker]; exact hN'
  have hbot : (⊥ : Subgroup ↥(ctxNQ t tau x₁ x₂ rho)).map (S4B.z4iπ (hz.z4iSub Ng)) ≤ A := by
    rw [Subgroup.map_bot]; exact bot_le
  obtain ⟨A', hA'2, -, hA'map, hinj⟩ :=
    S4B.z4i_lift_two_ge (S4B.z4iπ (hz.z4iSub Ng)) (S4B.z4iπ_surjective _) hker
      (A := ⊥) IsPGroup.of_bot hA2 hbot
  have ha2G : (lam * t) * (lam * t) = 1 := hz.sigma_sq
  have ha2 : (hz.z4iLam * hz.z4iT) * (hz.z4iLam * hz.z4iT) = 1 := Subtype.ext ha2G
  have ha1G : lam * t ≠ 1 := by
    obtain ⟨h₀, hh₀⟩ := hz.sigma_conj_t
    intro h
    apply hz.t_ne_one
    calc t = h₀⁻¹ * (h₀ * t * h₀⁻¹) * h₀ := by group
      _ = h₀⁻¹ * (lam * t) * h₀ := by rw [hh₀]
      _ = 1 := by rw [h]; group
  have ha1 : (hz.z4iLam * hz.z4iT) ≠ 1 := fun h => ha1G (congrArg Subtype.val h)
  have hσmem : (S4B.z4iπ (hz.z4iSub Ng)) (hz.z4iLam * hz.z4iT) ∈ A := by
    rw [map_mul]; exact hσA
  obtain ⟨s', hs'A, hs'eq⟩ := Subgroup.mem_map.mp (hA'map ▸ hσmem)
  have hs'2 : s' * s' = 1 := by
    have h1 : (S4B.z4iπ (hz.z4iSub Ng)) (s' * s') = (S4B.z4iπ (hz.z4iSub Ng)) 1 := by
      rw [map_mul, map_one, hs'eq, ← map_mul, ha2, map_one]
    exact S4B.z4iπ_injOn _ hN' hA'2 (A'.mul_mem hs'A hs'A) (one_mem _) h1
  have hs'1 : s' ≠ 1 := by
    intro h
    have hπ1 : (S4B.z4iπ (hz.z4iSub Ng)) (hz.z4iLam * hz.z4iT) = 1 := by
      rw [← hs'eq, h, map_one]
    exact S4B.z4i_map_ne_one _ hN' ha2 ha1 hπ1
  obtain ⟨g, hg⟩ := S4B.z4i_exists_conj_of_map_eq _ hN' hs'2 hs'1 ha2 hs'eq
  obtain ⟨h₀, hh₀⟩ := hz.sigma_conj_t
  have hs'G : (s' : G) = ((g : G) * h₀) * t * ((g : G) * h₀)⁻¹ := by
    have h1 : (s' : G) = (g : G) * (lam * t) * (g : G)⁻¹ := by
      calc (s' : G) =
            ((g * (hz.z4iLam * hz.z4iT) * g⁻¹ : ↥(ctxNQ t tau x₁ x₂ rho)) : G) :=
            congrArg Subtype.val hg
        _ = (g : G) * (lam * t) * (g : G)⁻¹ := by rfl
    calc (s' : G) = (g : G) * (lam * t) * (g : G)⁻¹ := h1
      _ = ((g : G) * h₀) * t * ((g : G) * h₀)⁻¹ := by rw [← hh₀]; group
  let A'' : Subgroup G := A'.map (ctxNQ t tau x₁ x₂ rho).subtype
  have hA''2 : IsPGroup 2 A'' := hA'2.map (ctxNQ t tau x₁ x₂ rho).subtype
  have hab' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    have hxA : (S4B.z4iπ (hz.z4iSub Ng)) x ∈ A := by
      rw [← hA'map]; exact Subgroup.mem_map_of_mem _ hx
    have hyA : (S4B.z4iπ (hz.z4iSub Ng)) y ∈ A := by
      rw [← hA'map]; exact Subgroup.mem_map_of_mem _ hy
    have hcomm := hAab ((S4B.z4iπ (hz.z4iSub Ng)) x) hxA ((S4B.z4iπ (hz.z4iSub Ng)) y) hyA
    have hπ : (S4B.z4iπ (hz.z4iSub Ng)) (x * y) = (S4B.z4iπ (hz.z4iSub Ng)) (y * x) := by
      rw [map_mul, map_mul]; exact hcomm
    exact S4B.z4iπ_injOn _ hN' hA'2 (A'.mul_mem hx hy) (A'.mul_mem hy hx) hπ
  have hA''ab : IsMulCommutative ↥A'' := IsMulCommutative.of_comm fun x y => by
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    refine Subtype.ext ?_
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hax, ← hby]
    exact congrArg Subtype.val (hab' a ha b hb)
  obtain ⟨w', hw'A, hw'eq⟩ := Subgroup.mem_map.mp (hA'map ▸ hwA)
  have hw''mem : (w' : G) ∈ A'' := Subgroup.mem_map.mpr ⟨w', hw'A, rfl⟩
  have hw''8 : orderOf (w' : G) = 8 := by
    calc orderOf (w' : G) = orderOf w' := Subgroup.orderOf_coe w'
      _ = orderOf (⟨w', hw'A⟩ : ↥A') := Subgroup.orderOf_coe (⟨w', hw'A⟩ : ↥A')
      _ = orderOf ((S4B.z4iπ (hz.z4iSub Ng)) w') :=
          (orderOf_injective ((S4B.z4iπ (hz.z4iSub Ng)).comp A'.subtype) hinj
            ⟨w', hw'A⟩).symm
      _ = orderOf w := by rw [hw'eq]
      _ = 8 := hw8
  have hA''cent : A'' ≤ centralizer ({((g : G) * h₀) * t * ((g : G) * h₀)⁻¹} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hs'G]
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    rw [← hax]
    exact congrArg Subtype.val (hab' a ha s' hs'A)
  have hbound := S4B.c17_card_abelian_ord_eight_le hz.toCtx10 ((g : G) * h₀)
    hA''cent hA''ab hA''2 hw''mem hw''8
  calc Nat.card A = Nat.card A' := by rw [← hA'map]; exact S4B.z4i_card_map _ hN' hA'2
    _ = Nat.card A'' := (Subgroup.card_map_of_injective
        (ctxNQ t tau x₁ x₂ rho).subtype_injective).symm
    _ ≤ 16 := hbound

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
