module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mem_normalizer_closure_pair_of_conj_mem {g : G}
    (ht : g * t * g⁻¹ ∈ closure ({t, tau} : Set G))
    (htau : g * tau * g⁻¹ ∈ closure ({t, tau} : Set G)) :
    g ∈ normalizer ((closure ({t, tau} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure, closure_le]
    rintro x hx
    rw [Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · simpa [MulAut.conj_apply] using ht
    · simpa [MulAut.conj_apply] using htau
  · exact le_of_eq (Subgroup.card_map_of_injective (K := closure ({t, tau} : Set G))
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).symm

private lemma conj_tau_mem_closure_of {g u : G} (hu : u = tau ∨ u = t * tau)
    (ht2 : t * t = 1) (hgu : g * u * g⁻¹ = t)
    (hgt : g * t * g⁻¹ ∈ closure ({t, tau} : Set G)) :
    g * tau * g⁻¹ ∈ closure ({t, tau} : Set G) := by
  rcases hu with hu1 | hu2
  · rw [hu1] at hgu
    rw [hgu]
    exact Subgroup.subset_closure (by simp)
  · have htau : tau = t * u := by
      rw [hu2, ← mul_assoc, ht2, one_mul]
    have hgtau_eq : g * tau * g⁻¹ = g * (t * u) * g⁻¹ := by rw [htau]
    rw [hgtau_eq]
    have hsplit : g * (t * u) * g⁻¹ = (g * t * g⁻¹) * (g * u * g⁻¹) := by group
    rw [hsplit, hgu]
    exact Subgroup.mul_mem _ hgt (Subgroup.subset_closure (by simp))

theorem card_centralizer_t_tau (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    Nat.card (centralizer ((closure {t, tau} : Subgroup G) : Set G)) = 96 := by
  obtain ⟨hcent, _hE4, hcardV, hinf, hcomm⟩ := centralizer_t_tau_of h h43 h44
  have hcardQ : Nat.card (closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Subgroup G) = 24 := by
    obtain ⟨e⟩ := h.perm_four
    have he : Nat.card ↥(L ⊓ centralizer ({tau} : Set G)) = 24 := by
      rw [Nat.card_congr e.toEquiv]
      rw [Nat.card_perm, Nat.card_fin]
      norm_num
    rw [← h.cent_L_tau]
    exact he
  rw [hcent, card_sup_of_commute hcomm hinf, hcardV, hcardQ]

theorem no_conj_pair_tz (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {u : G} (hu : u = tau ∨ u = t * tau) :
    ¬ ∃ g : G, g * t * g⁻¹ = t * (x₁ * x₂) ^ 2 ∧ g * u * g⁻¹ = t := by
  rintro ⟨g, hgt, hgu⟩
  set V : Subgroup G := closure {t, tau} with hV
  set W : Subgroup G := closure {t, (x₁ * x₂) ^ 2} with hW
  have htu_eq : closure ({t, u} : Set G) = closure ({t, tau} : Set G) := by
    rcases hu with hu1 | hu2
    · rw [hu1]
    · rw [hu2]
      apply le_antisymm
      · rw [closure_le]
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
      · rw [closure_le]
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx1 | hx2
        · rw [hx1]
          exact Subgroup.subset_closure (by simp)
        · rw [hx2]
          have htau : tau = t * (t * tau) := by
            rw [← mul_assoc, t_mul_self h.hyp, one_mul]
          have hmem : t * (t * tau) ∈ closure ({t, t * tau} : Set G) :=
            Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
          rwa [← htau] at hmem
  have hmap : V.map (MulAut.conj g).toMonoidHom = W := by
    rw [hV, hW, ← htu_eq, MonoidHom.map_closure, Set.image_pair]
    have hft : (MulAut.conj g).toMonoidHom t = t * (x₁ * x₂) ^ 2 := by
      simpa [MulAut.conj_apply] using hgt
    have hfu : (MulAut.conj g).toMonoidHom u = t := by
      simpa [MulAut.conj_apply] using hgu
    rw [hft, hfu]
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
    · rw [closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · have hz : (x₁ * x₂) ^ 2 = t * (t * (x₁ * x₂) ^ 2) := by
          rw [← mul_assoc, t_mul_self h.hyp, one_mul]
        have hmem : t * (t * (x₁ * x₂) ^ 2) ∈
            closure ({t * (x₁ * x₂) ^ 2, t} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        rwa [← hz] at hmem
  have hcardV : Nat.card (centralizer (V : Set G)) = 96 := by
    rw [hV]
    exact card_centralizer_t_tau h h43 h44
  have hcardW : Nat.card (centralizer (W : Set G)) = 96 := by
    have hle1 : (centralizer (V : Set G)).map (MulAut.conj g).toMonoidHom ≤
        centralizer (W : Set G) := by
      have hle := Subgroup.map_centralizer_le_centralizer_image (V : Set G)
        (MulAut.conj g).toMonoidHom
      rw [← Subgroup.coe_map, hmap] at hle
      exact hle
    have hcard1 : Nat.card (centralizer (V : Set G)) ≤ Nat.card (centralizer (W : Set G)) := by
      have hle := Subgroup.card_le_of_le hle1
      rwa [Subgroup.card_map_of_injective (K := centralizer (V : Set G))
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective] at hle
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    have hmap_inv : W.map (MulAut.conj g⁻¹).toMonoidHom = V := by
      rw [← hmap, Subgroup.map_map, hcomp, Subgroup.map_id]
    have hle2 : (centralizer (W : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        centralizer (V : Set G) := by
      have hle := Subgroup.map_centralizer_le_centralizer_image (W : Set G)
        (MulAut.conj g⁻¹).toMonoidHom
      rw [← Subgroup.coe_map, hmap_inv] at hle
      exact hle
    have hcard2 : Nat.card (centralizer (W : Set G)) ≤ Nat.card (centralizer (V : Set G)) := by
      have hle := Subgroup.card_le_of_le hle2
      rwa [Subgroup.card_map_of_injective (K := centralizer (W : Set G))
        (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective] at hle
    have : Nat.card (centralizer (W : Set G)) = Nat.card (centralizer (V : Set G)) :=
      le_antisymm hcard2 hcard1
    rw [this, hcardV]
  have hSle : S ≤ centralizer (W : Set G) := by
    apply (Subgroup.le_centralizer_iff).mpr
    intro x hx
    rw [hW] at hx
    exact (Subgroup.mem_inf.mp (h.center_ge hx)).2
  have hle : Nat.card S ≤ Nat.card (centralizer (W : Set G)) := Subgroup.card_le_of_le hSle
  rw [card_S_of h h43, hcardW] at hle
  norm_num at hle

theorem exists_normalizer_V_of_conj (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {u : G} (hu : u = tau ∨ u = t * tau)
    (hg : ∃ g : G, g * u * g⁻¹ = t) :
    ∃ g : G, g * u * g⁻¹ = t ∧ g ∈ normalizer ((closure {t, tau} : Subgroup G) : Set G) := by
  obtain ⟨g₀, hg₀⟩ := hg
  have htau_comm_t : tau * t = t * tau :=
    mem_invCent_iff.mp (h.toCtx0.le_invCent h.tau_mem)
  have htu_comm : t * u = u * t := by
    rcases hu with hu1 | hu2
    · rw [hu1]
      exact htau_comm_t.symm
    · rw [hu2, mul_assoc, htau_comm_t]
  have ht'mem : g₀ * t * g₀⁻¹ ∈ invCent t := by
    rw [mem_invCent_iff]
    calc (g₀ * t * g₀⁻¹) * t
        = (g₀ * t * g₀⁻¹) * (g₀ * u * g₀⁻¹) := by rw [hg₀]
      _ = g₀ * (t * u) * g₀⁻¹ := by group
      _ = g₀ * (u * t) * g₀⁻¹ := by rw [htu_comm]
      _ = (g₀ * u * g₀⁻¹) * (g₀ * t * g₀⁻¹) := by group
      _ = t * (g₀ * t * g₀⁻¹) := by rw [hg₀]
  have ht'sq : (g₀ * t * g₀⁻¹) * (g₀ * t * g₀⁻¹) = 1 := by
    calc (g₀ * t * g₀⁻¹) * (g₀ * t * g₀⁻¹)
        = g₀ * (t * t) * g₀⁻¹ := by group
      _ = g₀ * 1 * g₀⁻¹ := by rw [t_mul_self h.hyp]
      _ = 1 := by group
  have ht'ne : g₀ * t * g₀⁻¹ ≠ 1 := by
    intro h1
    apply t_ne_one h.hyp
    calc t = g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ := by group
      _ = g₀⁻¹ * 1 * g₀ := by rw [h1]
      _ = 1 := by group
  obtain ⟨k, hk, hkw⟩ :=
    (five_classes_of h h43 h44).1 (g₀ * t * g₀⁻¹) ht'mem ht'sq ht'ne
  have hk_t : k * t = t * k := mem_invCent_iff.mp hk
  set g₁ : G := k * g₀ with hg₁
  have hg₁t : g₁ * t * g₁⁻¹ = k * (g₀ * t * g₀⁻¹) * k⁻¹ := by
    rw [hg₁]
    group
  have hg₁u : g₁ * u * g₁⁻¹ = t := by
    rw [hg₁]
    calc (k * g₀) * u * (k * g₀)⁻¹ = k * (g₀ * u * g₀⁻¹) * k⁻¹ := by group
      _ = k * t * k⁻¹ := by rw [hg₀]
      _ = t := by rw [hk_t]; group
  rcases hkw with hw | hw | hw | hw | hw
  ·
    rw [hw] at hg₁t
    exfalso
    have hut : u = t := by
      calc u = g₁⁻¹ * (g₁ * u * g₁⁻¹) * g₁ := by group
        _ = g₁⁻¹ * (g₁ * t * g₁⁻¹) * g₁ := by rw [hg₁u, hg₁t]
        _ = t := by group
    rcases hu with hu1 | hu2
    · rw [hu1] at hut
      exact h.tau_not_mem (by rw [hut]; exact Subgroup.mem_sup_left h.hyp.mem_twoCore)
    · rw [hu2] at hut
      have htau1 : tau = 1 := by
        calc tau = t * (t * tau) := by rw [← mul_assoc, t_mul_self h.hyp, one_mul]
          _ = t * t := by rw [hut]
          _ = 1 := t_mul_self h.hyp
      exact h.tau_not_mem (by rw [htau1]; exact Subgroup.one_mem _)
  ·
    rw [hw] at hg₁t
    exfalso
    exact not_conj_z_of_ctx h ⟨g₁, hg₁t⟩
  ·
    rw [hw] at hg₁t
    refine ⟨g₁, hg₁u, ?_⟩
    apply mem_normalizer_closure_pair_of_conj_mem
    · rw [hg₁t]; exact Subgroup.subset_closure (by simp)
    · exact conj_tau_mem_closure_of hu (t_mul_self h.hyp) hg₁u
        (by rw [hg₁t]; exact Subgroup.subset_closure (by simp))
  ·
    rw [hw] at hg₁t
    exfalso
    exact no_conj_pair_tz h h43 h44 hu ⟨g₁, hg₁t, hg₁u⟩
  ·
    rw [hw] at hg₁t
    refine ⟨g₁, hg₁u, ?_⟩
    apply mem_normalizer_closure_pair_of_conj_mem
    · rw [hg₁t]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · have hconjt : g₁ * t * g₁⁻¹ ∈ closure ({t, tau} : Set G) := by
        rw [hg₁t]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact conj_tau_mem_closure_of hu (t_mul_self h.hyp) hg₁u hconjt

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
