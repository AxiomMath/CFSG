module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiAltCore
public import CFSG.GroupTheory.SylowIntersectionControl.GomiComponents
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.SylowIntersectionControl.GomiProductSylow
import CFSG.GroupTheory.SylowIntersectionControl.GomiAltComponent
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentClauses
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentIsolated
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentSection

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {G : Type} [Group G] {n : ℕ}

private theorem inf_centralizer_eq_bot_of_mulEquiv_alt {A : Subgroup G} (hn : 4 ≤ n)
    (e : A ≃* alternatingGroup (Fin n)) : A ⊓ centralizer (A : Set G) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hc : e ⟨x, hx.1⟩ ∈ center (alternatingGroup (Fin n)) := mem_center_iff.mpr fun b => by
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (mem_centralizer_iff.mp hx.2 a a.2))
  rw [alternatingGroup.center_eq_bot (by simpa using hn), mem_bot,
    MulEquiv.map_eq_one_iff] at hc
  exact (mem_bot).mpr (congrArg Subtype.val hc)

private theorem isGomiThreeCycle_map_conj {A : Subgroup G} (e : A ≃* alternatingGroup (Fin n))
    {z : G} (hz : z ∈ A)
    (h3 : ((e ⟨z, hz⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle) (g : G) :
    IsGomiThreeCycle n (A.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
  have hmem : g * z * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨z, hz, rfl⟩
  set φ := A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨hmem, φ.symm.trans e, ?_⟩
  have h : φ.symm ⟨g * z * g⁻¹, hmem⟩ = ⟨z, hz⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  rw [MulEquiv.trans_apply, h]
  exact h3

private theorem exists_isGomiThreeCycle {L : Subgroup G} (hn : 3 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) :
    ∃ x : Subgroup G → G, ∀ g : G, IsGomiThreeCycle n (L.map (MulAut.conj g).toMonoidHom)
      (x (L.map (MulAut.conj g).toMonoidHom)) := by
  classical
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) *
      Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨2, by omega⟩ : Fin n)).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  set a := e.symm ⟨_, h3.mem_alternatingGroup⟩
  have hex (g : G) : ∃ y, IsGomiThreeCycle n (L.map (MulAut.conj g).toMonoidHom) y :=
    ⟨_, isGomiThreeCycle_map_conj e a.2 (by simpa [a] using h3) g⟩
  exact ⟨fun B => if h : ∃ y, IsGomiThreeCycle n B y then h.choose else 1, fun g => by
    dsimp only
    rw [dif_pos (hex g)]
    exact (hex g).choose_spec⟩

private def IsGomiFact23Subgroup (L H M : Subgroup G) (n : ℕ) : Prop :=
  M ≠ ⊤ ∧ Odd M.index ∧
    (∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ∧
      (K.subgroupOf (normalizer (H : Set G))).IsSubnormal ∧ 2 ∣ H.relIndex K ∧ K ≤ M) ∧
    (Even n → CharTwo M) ∧
    (n % 4 = 3 → ∃ x : Subgroup G → G,
      (∀ g : G, IsGomiThreeCycle n (L.map (MulAut.conj g).toMonoidHom)
        (x (L.map (MulAut.conj g).toMonoidHom))) ∧
      twoResidual (M ⊓ centralizer (pCoreOf 2 M : Set G)) ≤
        closure (Set.range fun g : G => x (L.map (MulAut.conj g).toMonoidHom)))

private theorem map_conj_mem_range (L : Subgroup G) (g : G) {J : Subgroup G}
    (hJ : J ∈ Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom) :
    J.map (MulAut.conj g).toMonoidHom ∈
      Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k, rfl⟩ := hJ
  exact ⟨g * k, (map_conj_map_conj L k g).symm⟩

private theorem exists_map_conj_eq (L : Subgroup G) (g₀ : G) {B : Subgroup G}
    (hB : B ∈ Set.range fun k : G => L.map (MulAut.conj k).toMonoidHom) :
    ∃ g : G, (L.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
  obtain ⟨k, rfl⟩ := hB
  exact ⟨k * g₀⁻¹, by rw [map_conj_map_conj, inv_mul_cancel_right]⟩

section Cases

variable [Finite G]

private theorem exists_of_isSylowTwoOf {L : Subgroup G} (hL : GomiHyp21 L) (hn : 7 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) {H : Subgroup G} (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hJ : IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    ∃ M : Subgroup G, IsGomiFact23Subgroup L H M n := by
  have hN := isDirectProduct_conj hL.commute (inf_centralizer_eq_bot_of_mulEquiv_alt (by omega) e)
  have hA : ∀ A ∈ Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom,
      Nonempty (A ≃* alternatingGroup (Fin n)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
      e⟩
  obtain ⟨hc, h2⟩ := charTwo_normalizer_of_isSylowTwoOf hL.isPGroup_quotient hJ
    (inf_centralizer_le_of_isSylowTwoOf (by omega) hN hA hJ)
  obtain ⟨x, hx⟩ := exists_isGomiThreeCycle (by omega) e
  have hL1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext y
    simp
  refine ⟨_, normalizer_ne_top_of_isSylowTwoOf (by omega) hN ⟨1, hL1⟩ e hJ,
    odd_index_normalizer_of_isSylowTwoOf hJ,
    hiso.exists_le_of_sq_mem hH fun a ha _ => normalizer_le_normalizer_inf_of_normal ha,
    fun _ => hc, fun _ => ⟨x, hx, ?_⟩⟩
  rw [twoResidual_eq_bot_of_isPGroup h2]
  exact bot_le

private theorem charTwo_of_components {S : Set (Subgroup G)} {N M A Q : Subgroup G} [N.Normal]
    (hGN : IsPGroup 2 (G ⧸ N)) (hN : IsDirectProduct S N)
    (hMN : M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B})
    (hMB : ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
      M ⊓ B = Q.map (MulAut.conj g).toMonoidHom)
    (hQ : CharTwo Q) : CharTwo M := by
  rw [charTwo_iff_twoResidual_eq_bot] at hQ ⊢
  refine eq_bot_iff.mpr ((twoResidual_inf_centralizer_le_inf hGN M).trans
    ((twoResidual_inf_centralizer_le_sSup hN hMN (T := fun _ => ⊥) fun B hB => ?_).trans
      (sSup_le ?_)))
  · obtain ⟨g, -, hg⟩ := hMB B hB
    rw [hg, twoResidual_inf_centralizer_map (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hQ, Subgroup.map_bot]
  · rintro _ ⟨B, -, rfl⟩
    exact le_rfl

private theorem exists_threeCycles_of_components {L N M A Q : Subgroup G} [N.Normal]
    (hGN : IsPGroup 2 (G ⧸ N))
    (hN : IsDirectProduct (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom) N)
    (hMN : M ⊓ N = sSup {Y | ∃ B ∈ Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom,
      Y = M ⊓ B})
    (hMB : ∀ B ∈ Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom, ∃ g : G,
      A.map (MulAut.conj g).toMonoidHom = B ∧ M ⊓ B = Q.map (MulAut.conj g).toMonoidHom)
    (e : A ≃* alternatingGroup (Fin n)) {z : G} (hz : z ∈ A)
    (h3 : ((e ⟨z, hz⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle)
    (hQz : twoResidual (Q ⊓ centralizer (pCoreOf 2 Q : Set G)) ≤ zpowers z) :
    ∃ x : Subgroup G → G,
      (∀ g : G, IsGomiThreeCycle n (L.map (MulAut.conj g).toMonoidHom)
        (x (L.map (MulAut.conj g).toMonoidHom))) ∧
      twoResidual (M ⊓ centralizer (pCoreOf 2 M : Set G)) ≤
        closure (Set.range fun g : G => x (L.map (MulAut.conj g).toMonoidHom)) := by
  classical
  choose c hcA hcM using hMB
  obtain ⟨x, hx⟩ : ∃ x : Subgroup G → G, ∀ B (hB : B ∈ Set.range fun g : G =>
      L.map (MulAut.conj g).toMonoidHom), x B = c B hB * z * (c B hB)⁻¹ :=
    ⟨fun B => if hB : _ then c B hB * z * (c B hB)⁻¹ else 1, fun B hB => dif_pos hB⟩
  refine ⟨x, fun g => ?_, (twoResidual_inf_centralizer_le_inf hGN M).trans
    ((twoResidual_inf_centralizer_le_sSup hN hMN (T := fun B => zpowers (x B))
      fun B hB => ?_).trans (sSup_le ?_))⟩
  · have h := isGomiThreeCycle_map_conj e hz h3 (c _ ⟨g, rfl⟩)
    rw [hcA _ ⟨g, rfl⟩] at h
    rwa [hx _ ⟨g, rfl⟩]
  · rw [hcM B hB, twoResidual_inf_centralizer_map (f := (MulAut.conj (c B hB)).toMonoidHom)
      (MulAut.conj _).injective, hx B hB]
    exact (map_mono hQz).trans (MonoidHom.map_zpowers _ _).le
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact zpowers_le.mpr (subset_closure ⟨g, rfl⟩)

private theorem exists_of_component (hAlt : GomiAltCore) {L : Subgroup G} (hL : GomiHyp21 L)
    (hn : 7 ≤ n) (hn' : ∀ m : ℕ, n ≠ 2 ^ m + 1) (e : L ≃* alternatingGroup (Fin n))
    {H : Subgroup G} (hH : IsPGroup 2 H) (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hJ : ¬ IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G))) :
    ∃ M : Subgroup G, IsGomiFact23Subgroup L H M n := by
  have hN := isDirectProduct_conj hL.commute (inf_centralizer_eq_bot_of_mulEquiv_alt (by omega) e)
  have hSG := fun g J hJ => map_conj_mem_range L g (J := J) hJ
  obtain ⟨_, ⟨g₀, rfl⟩, hKA⟩ := exists_two_dvd_relIndex_of_not_isSylowTwoOf hN hH hJ
  set eA :=
    (L.equivMapOfInjective (MulAut.conj g₀).toMonoidHom (MulAut.conj g₀).injective).symm.trans e
  obtain ⟨Q, hQA, hQne, hQN, hTQ, hIQ, hDQ, hc, h3⟩ := exists_inf_of_gomiAltCore hAlt hn hn' eA
    inf_le_right (hH.to_le inf_le_left)
    (hiso.normalizer_inf_sup_of_component hN hSG hH ⟨g₀, rfl⟩ hKA)
    (hiso.sup_inf_centralizer_le_of_component hN hSG hH ⟨g₀, rfl⟩ hKA
      (inf_centralizer_eq_bot_of_mulEquiv_alt (by omega) eA))
  obtain ⟨M, hMo, hHM, hMA, hMne, hMN, hMB⟩ := exists_odd_index_inf_eq hN hSG ⟨g₀, rfl⟩
    (fun B hB => exists_map_conj_eq L g₀ hB) hL.isPGroup_quotient hH hQA hQN hTQ hIQ
  refine ⟨M, hMne hQne, hMo, hiso.exists_le_of_sq_mem hH fun a ha ha2 =>
    hiso.mem_of_component hN hSG hH ⟨g₀, rfl⟩ hKA hHM (fun d hd hd2 =>
      (hMA.ge (hDQ d hd ⟨hd2, pow_mem (le_normalizer hd.1) 2⟩)).1) ha ha2,
    fun he => charTwo_of_components hL.isPGroup_quotient hN hMN hMB (hc he), fun h4 => ?_⟩
  obtain ⟨z, hz, hz3, hzQ⟩ := h3 h4
  exact exists_threeCycles_of_components hL.isPGroup_quotient hN hMN hMB eA hz hz3 hzQ

end Cases

theorem gomiFact23_of_gomiAltCore (hAlt : GomiAltCore) : GomiFact23 := by
  intro G _ _ L n hL hn ⟨e⟩ H _ hH hiso
  have key (hn' : ∀ m : ℕ, n ≠ 2 ^ m + 1) : ∃ M : Subgroup G, IsGomiFact23Subgroup L H M n :=
    (em (IsSylowTwoOf (H ⊓ normalClosure (L : Set G)) (normalClosure (L : Set G)))).elim
      (exists_of_isSylowTwoOf hL hn e hH hiso) (exists_of_component hAlt hL hn hn' e hH hiso)
  have hev (he : Even n) (m : ℕ) : n ≠ 2 ^ m + 1 := by
    obtain ⟨k, hk⟩ := he
    rcases m with _ | m
    · omega
    · rw [pow_succ]
      omega
  have h43 (h4 : n % 4 = 3) (m : ℕ) : n ≠ 2 ^ m + 1 := by
    rcases m with _ | _ | m
    · omega
    · omega
    · rw [pow_succ, pow_succ]
      omega
  refine ⟨fun hn' => ?_, fun he => ?_, fun h4 => ?_⟩
  · obtain ⟨M, h1, h2, h3, -, -⟩ := key hn'
    exact ⟨M, h1, h2, h3⟩
  · obtain ⟨M, h1, h2, h3, h5, -⟩ := key (hev he)
    exact ⟨M, h1, h2, h3, h5 he⟩
  · obtain ⟨M, h1, h2, h3, -, h6⟩ := key (h43 h4)
    exact ⟨M, h1, h2, h3, h6 h4⟩

end CFSG.GroupTheory

end
