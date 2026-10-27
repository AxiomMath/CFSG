module

public import CFSG.CGT.T75P.RankOne81
public import CFSG.CGT.T75Q.CentU

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem Std81.centralizer_eq (s : Std81 T T₁) :
    Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) =
      Subgroup.centralizer (ugen T : Set G) :=
  centralizer_hSub_eq_centralizer_ugen s.h1 s.h62 s.h63 s.h66 s.hc s.hnat chain3 (le_refl 3)

theorem Std81.two_dvd (s : Std81 T T₁) : 2 ∣ Nat.card T :=
  two_dvd_card_of_ctx s.hc (by norm_num)

theorem Std81.hN_gen (s : Std81 T T₁) : ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T) := by
  have : Finite G := s.finite
  exact hN_ugen s.hc.hy.pair.wc s.hc.hS s.two_dvd

theorem Std81.T₁_le_ugen (s : Std81 T T₁) : T₁ ≤ ugen T := by
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1⟩ := exists_ne_one_mem_normIn s.hc
  obtain ⟨hℓD, hℓN, -⟩ := mem_normD_of_mem_normIn s.hc hℓ₀ hℓ₀1
  have hℓΓ : ℓ₀ ∈ gammaD T := normD_subset_gammaD hWC s.two_dvd ⟨hℓD, hℓN⟩
  obtain ⟨x₀, -, hx₀⟩ := s.hc.sec3.conj
  have hT₁ab : IsElemAbelian 2 T₁ := hx₀ ▸ isElemAbelian_conjSubgroup hWC.1 x₀
  have hℓT₁ : ℓ₀ ∈ T₁ := (mem_normIn.1 hℓ₀).1
  intro t₁ ht₁
  by_cases ht1 : t₁ = 1
  · rw [ht1]
    exact Subgroup.one_mem _
  · have hmem : t₁ ∈ conjSubgroup x₀ T := hx₀ ▸ ht₁
    have htD : t₁ ∈ classD T := mem_classD_of_mem_conjSubgroup hmem ht1
    have hcomm : t₁ * ℓ₀ = ℓ₀ * t₁ := elemAbelian_mul_comm hT₁ab ht₁ hℓT₁
    exact gammaD_subset_ugen (gammaD_closed hℓΓ htD hcomm)

theorem Std81.Uc_le_ugen (s : Std81 T T₁) : Uc T T₁ ≤ ugen T :=
  sup_le (hSub_le_ugen s.hc (by norm_num)) s.T₁_le_ugen

theorem center_eq_bot_of_simple [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

@[expose] def Yc (T : Subgroup G) (c : G) : Subgroup G :=
  Subgroup.closure {d | d ∈ classD T ∧ c * d = d * c}

theorem Yc_le_centralizer (T : Subgroup G) (c : G) :
    Yc T c ≤ Subgroup.centralizer ({c} : Set G) := by
  rw [Yc, Subgroup.closure_le]
  intro e he
  exact Subgroup.mem_centralizer_singleton_iff.2 he.2.symm

theorem Yc_comm {T : Subgroup G} {c y : G} (hy : y ∈ Yc T c) : c * y = y * c :=
  (Subgroup.mem_centralizer_singleton_iff.1 (Yc_le_centralizer T c hy)).symm

theorem subset_Yc {T : Subgroup G} {c d : G} (hd : d ∈ classD T) (hcd : c * d = d * c) :
    d ∈ Yc T c :=
  Subgroup.subset_closure ⟨hd, hcd⟩

theorem Yc_conj_le (g c : G) : Yc T (g * c * g⁻¹) ≤ conjSubgroup g (Yc T c) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro d ⟨hd, hcd⟩
  apply mem_conjSubgroup.2
  apply subset_Yc (classD_conj hd g)
  have h1 : g * c * g⁻¹ * d = d * (g * c * g⁻¹) := hcd
  calc c * (g⁻¹ * d * g) = g⁻¹ * (g * c * g⁻¹ * d) * g := by group
    _ = g⁻¹ * (d * (g * c * g⁻¹)) * g := by rw [h1]
    _ = (g⁻¹ * d * g) * c := by group

structure GoodY (T Y : Subgroup G) : Prop where
  ne_top : Y ≠ ⊤
  ugen_le : ugen T ≤ Y
  gen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G))

theorem Std81.ugen_le_Yc (s : Std81 T T₁) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) : ugen T ≤ Yc T c := by
  refine Subgroup.closure_mono (fun d hd => ⟨hd.1, ?_⟩)
  exact gammaD_le_centralizer s.h1 s.h62 s.h63 s.h66 s.hc s.hnat chain3 (le_refl 3) hcC d hd

theorem Std81.closed_Yc (s : Std81 T T₁) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) {d : G} (hd : d ∈ classD T)
    (hdY : d ∈ Yc T c) {x : G} (hx : x ∈ classD T) (hxd : x * d = d * x) : x ∈ Yc T c :=
  subset_Yc hx (closed_CD81 s (fun _ hu => s.hC1 hcC hu) hd (Yc_comm hdY) hx hxd)

theorem Std81.goodY_Yc [IsSimpleGroup G] (s : Std81 T T₁) {c : G}
    (hcC : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hc1 : c ≠ 1) :
    GoodY T (Yc T c) := by
  refine ⟨?_, s.ugen_le_Yc hcC, ?_⟩
  · intro htop
    have hcen : c ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Yc_comm (htop ▸ Subgroup.mem_top g)).symm
    rw [center_eq_bot_of_simple s.hc.hy.nonab, Subgroup.mem_bot] at hcen
    exact hc1 hcen
  · refine (Subgroup.closure_le _).2 ?_
    intro d hd
    exact Subgroup.subset_closure ⟨hd.1, subset_Yc hd.1 hd.2⟩

end CFSG.CGT.T75P
