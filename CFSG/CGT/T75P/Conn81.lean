module

public import CFSG.CGT.T75P.RankOne81
public import CFSG.CGT.T75Q.CentU

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def ClD (T : Subgroup G) (m : G) : Prop :=
  ∀ d ∈ classD T, m * d = d * m → ∀ x ∈ classD T, x * d = d * x → m * x = x * m

theorem ClD.comm_of_conn {m d₀ δ : G} (hm : ClD T m) (hd₀ : m * d₀ = d₀ * m)
    (h : Relation.ReflTransGen (CommD T) d₀ δ) : m * δ = δ * m := by
  induction h with
  | refl => exact hd₀
  | tail _ hbc ih => exact hm _ hbc.1 ih _ hbc.2.1 hbc.2.2.symm

theorem Std81.clD_of_conj (s : Std81 T T₁) {c g m : G}
    (hc : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) (hm : m = g * c * g⁻¹) :
    ClD T m :=
  fun _ hd hmd _ hx hxd => closed_CD81_conj s (fun _ hu => s.hC1 hc hu) hm hd hmd hx hxd

theorem gammaD_conn (hT : IsElemAbelian 2 T) {t₀ δ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    (hδ : δ ∈ gammaD T) : Relation.ReflTransGen (CommD T) t₀ δ := by
  obtain ⟨-, t, ht, ht1, hp⟩ := hδ
  have h1 : Relation.ReflTransGen (CommD T) t₀ t :=
    Relation.ReflTransGen.single ⟨mem_classD_of_mem ht₀ ht₀1, mem_classD_of_mem ht ht1,
      elemAbelian_mul_comm hT ht₀ ht⟩
  exact h1.trans hp

theorem Std81.comm_conj_ugen (s : Std81 T T₁) {m d y t₀ : G} (hm : ClD T m)
    (hmd : m * d = d * m) (hdy : d = y * t₀ * y⁻¹) (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) :
    ∀ u ∈ ugen T, m * (y * u * y⁻¹) = (y * u * y⁻¹) * m := by
  have hWC := s.hc.hy.pair.wc
  have hle : ugen T ≤ Subgroup.centralizer ({y⁻¹ * m * y} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    intro δ hδ
    have hpath := reflTransGen_conj (gammaD_conn hWC.1 ht₀ ht₀1 hδ) y
    rw [← hdy] at hpath
    have h1 := hm.comm_of_conn hmd hpath
    apply Subgroup.mem_centralizer_singleton_iff.2
    calc δ * (y⁻¹ * m * y) = y⁻¹ * ((y * δ * y⁻¹) * m) * y := by group
      _ = y⁻¹ * (m * (y * δ * y⁻¹)) * y := by rw [← h1]
      _ = (y⁻¹ * m * y) * δ := by group
  intro u hu
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
  calc m * (y * u * y⁻¹) = y * ((y⁻¹ * m * y) * u) * y⁻¹ := by group
    _ = y * (u * (y⁻¹ * m * y)) * y⁻¹ := by rw [← h2]
    _ = (y * u * y⁻¹) * m := by group

theorem Std81.conjC_of_comm (s : Std81 T T₁) {g h m x : G}
    (hm : g⁻¹ * m * g ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G))
    (hmx : m * x = x * m) (hh : h⁻¹ * x * h ∈ T) (hh1 : h⁻¹ * x * h ≠ 1) :
    h⁻¹ * m * h ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
  have hcl : ClD T m := s.clD_of_conj (g := g) hm (by group)
  have hxh : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  have h1 := s.comm_conj_ugen hcl hmx hxh hh hh1
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h2 := h1 u (hSub_le_ugen s.hc (by norm_num) hu)
  calc u * (h⁻¹ * m * h) = h⁻¹ * ((h * u * h⁻¹) * m) * h := by group
    _ = h⁻¹ * (m * (h * u * h⁻¹)) * h := by rw [← h2]
    _ = (h⁻¹ * m * h) * u := by group

end CFSG.CGT.T75P
