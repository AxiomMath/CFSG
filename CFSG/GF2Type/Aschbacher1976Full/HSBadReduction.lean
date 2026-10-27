module

public import CFSG.GF2Type.Aschbacher1976Full.HSBadLocal2
public import CFSG.GF2Type.Aschbacher1976Full.HSBadCrux
public import CFSG.GroupTheory.TransferOrderFourStmt

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour CFSG.GroupTheory.TransferOrderFour Subgroup
open scoped IsMulCommutative

theorem hsPartBad_of_crux (hTC : TransferCoreStmt) (hC : BadCruxStmt) : HSPartBad := by
  intro G _ _ z hset hti ⟨T, hTH, hcard⟩
  have hset' := hset
  obtain ⟨⟨hsimple, hna, hz, hsymp⟩, hZ4⟩ := hset'
  haveI := hsimple
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨k, hkZ, hkord, hgen, hk2⟩ := Width.exists_gen_Z hD hz
  have hF2 : IsPGroup 2 (Fz z) := hsymp.1
  have c : BL.Ctx z 2 Z A T := ⟨hD, hz, hF2, hTH⟩
  have hZk : Z = zpowers k := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr hkZ)
    obtain ⟨i, rfl⟩ := hgen x hx
    exact zpow_mem_zpowers k i
  have hZF : ZF z = zpowers k := c.ZF_self.trans hZk
  have s : Bad.Setup z Z A T k := ⟨c, hti, hZk, hk2⟩
  refine hC hset hti T hTH hcard k hZF ?_
  let N₀ : Subgroup ↥(T : Subgroup G) :=
    commutator ↥(T : Subgroup G) ⊔
      closure {x : ↥(T : Subgroup G) | IsConj z (x : G) ∧ (x : G) * k = k * (x : G)}
  have hcomm : commutator ↥(T : Subgroup G) ≤ N₀ := le_sup_left
  haveI : N₀.Normal := Subgroup.Normal.of_commutator_le _ hcomm
  haveI : IsMulCommutative (↥(T : Subgroup G) ⧸ N₀) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let ψ : ↥(T : Subgroup G) →* ↥(T : Subgroup G) ⧸ N₀ := QuotientGroup.mk' N₀
  have hψ : Bad.KillsS (T : Subgroup G) z k ψ := by
    intro u hu huz huk
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_sup_right (subset_closure (show (⟨u, hu⟩ : ↥(T : Subgroup G)) ∈ _ from
        ⟨huz, huk⟩)))
  have hnorm : centralizer ({k ^ 2} : Set G) ≤ normalizer (zpowers k : Set G) := by
    have h := Width.normalizer_centerAt hD hz hF2
    rw [show centerAt z = zpowers k from hZF] at h
    rw [hk2, h]
  have hTH' : (T : Subgroup G) ≤ centralizer ({k ^ 2} : Set G) := by rw [hk2]; exact hTH
  have hodd : Odd ((T : Subgroup G).relIndex (centralizer ({k ^ 2} : Set G))) := by
    rw [hk2]; exact Bad.odd_relIndex c
  have hkT : k ∈ (T : Subgroup G) := c.Z_le_T hkZ
  have hC1 : ∀ (u : G) (hu : u ∈ (T : Subgroup G)), IsConj (k ^ 2) u →
      ψ ⟨u, hu⟩ = 1 ∨ 4 ∣ Nat.card
        (MulAction.orbit (ConjAct (T : Subgroup G)) (⟨u, hu⟩ : (T : Subgroup G))) := by
    intro u hu huz
    rw [hk2] at huz
    by_cases huk : u * k = k * u
    · exact Or.inl (hψ u hu huz huk)
    · exact Or.inr (Bad.four_dvd_card_orbit_of_ne c hti hZk hu huz huk)
  obtain ⟨cc, hcc, hcc1, hEven⟩ := s.exists_c hcard hψ
  have key := hTC hkord hnorm T.isPGroup' hTH' hodd hkT ψ hC1 cc hcc hcc1 hEven
  have h1 := eq_one_of_isSimpleGroup hna ψ.transfer k
  rw [key] at h1
  have hmem : (⟨k, hkT⟩ : ↥(T : Subgroup G)) ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h1
  have hle : N₀ ≤ Subgroup.comap (T : Subgroup G).subtype
      (⁅(T : Subgroup G), (T : Subgroup G)⁆ ⊔
        closure {u : G | u ∈ (T : Subgroup G) ∧ IsConj z u ∧ u * k = k * u}) := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
      exact le_sup_left
    · refine (closure_le _).mpr fun x hx => ?_
      exact Subgroup.mem_sup_right (subset_closure ⟨x.2, hx.1, hx.2⟩)
  exact hle hmem

end CFSG.GF2Type.Aschbacher1976Full.HS
